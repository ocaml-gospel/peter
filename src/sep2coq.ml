open Gospel_checker
open Sast
open Id_uast
open Ident
open Tast
open Coq
open Formula
open Coq_driver
module M = Map.Make (String)

let is_stdlib = ref false
let to_triple s = "_" ^ s ^ "_spec"

let ty_map =
  List.fold_left (fun m (k, v) -> M.add k v m) M.empty type_mapping_list

let id_map =
  List.fold_left (fun m (k, v) -> M.add k v m) M.empty id_mapping_list

let is_ignore x = List.mem x ignore_list

let id_mapper = function
  | "prefix -" -> "neg"
  | "infix +" -> "plus"
  | "infix -" -> "minus"
  | "infix *" -> "mult"
  | "infix /" -> "div"
  | "infix >" -> "gt"
  | "infix >=" -> "ge"
  | "infix <>" -> "neq"
  | "infix <->" -> "iff"
  | "infix <" -> "lt"
  | "infix <=" -> "le"
  | "infix =" -> "eq"
  | "infix ++" -> "app"
  | "infix ->" -> "impl"
  | "infix ||" -> "orb"
  | "infix &&" -> "andb"
  | "mixfix [_]" -> "seq_get"
  | "mixfix [_.._]" -> "seq_sub"
  | "mixfix [_..]" -> "seq_sub_l"
  | "mixfix [.._]" -> "seq_sub_r"
  | "mixfix [->]" -> "map_set"
  | "mixfix {}" -> "set_create"
  | s -> s

let coq_keywords = [ "mod"; "Set"; "Alias" ]
let inhab = Coq_var "Inhab"
let enc = Coq_var "Enc"
let valid_coq_id s = if List.mem s coq_keywords then "_" ^ s else id_mapper s

let qual_var qual id =
  List.fold_left
    (fun acc x -> valid_coq_id x ^ "." ^ acc)
    (valid_coq_id id) qual

let stdlib_sym id =
  match id.id_str with "prop" -> "Prop" | "integer" -> "Z" | _ -> id.id_str

let rec qid_to_string = function
  | Qid id ->
      let id =
        if Ident.is_stdlib id || Ident.is_primitive id then stdlib_sym id
        else id.id_str
      in
      valid_coq_id id
  | Qdot (q, id) -> qid_to_string q ^ "." ^ id.id_str

let var_of_ty t =
  let rec var_of_ty t =
    match t with
    | PTtyapp (v, l) ->
        coq_apps (coq_var (qid_to_string v.app_qid)) (List.map var_of_ty l)
    | PTarrow (t1, t2) -> coq_impl (var_of_ty t1) (var_of_ty t2)
    | PTtyvar tv -> Coq_var (String.capitalize_ascii tv.id_str)
    | PTtuple l -> coq_prods (List.map var_of_ty l)
  in
  var_of_ty t

let coq_id id = qid_to_string id
let gen_args vs = tv vs.ts_id.id_str (var_of_ty vs.ts_ty) false
let gen_spec_args = function None -> coq_tt_tv | Some arg -> gen_args arg

let coq_const c =
  match c with
  | Parse_uast.Pconst_integer (v, None) -> coq_int (int_of_string v)
  | _ -> assert false

let to_inh = ( ^ ) "Ih_"

let gen_poly is_pure poly_vars =
  let types =
    List.map
      (fun v -> tv (String.capitalize_ascii v.id_str) Coq_type true)
      poly_vars
  in
  let f v =
    let nm = String.capitalize_ascii v.var_name in
    let inhab = (to_inh nm, coq_app inhab (coq_var nm)) in
    let enc = ("Enc_" ^ nm, coq_app enc (coq_var nm)) in
    let param = if is_pure then [ inhab ] else [ inhab; enc ] in
    List.map (fun (n, c) -> tv n c true) param
  in
  let type_properties = List.concat_map f types in
  types @ type_properties

let is_infix v =
  String.starts_with ~prefix:"infix" v.id_str && v.id_str <> "infix ++"

let get_infix t =
  match t.t_node with
  | Tvar (Qid v) | Ttyapply (Qid v, _) ->
      List.nth (String.split_on_char ' ' v.id_str) 1
  | _ -> assert false

let rec collect_tvars_pty tbl = function
  | PTtyvar v -> IdTable.replace tbl v.id_tag v
  | PTtyapp (_, l) | PTtuple l -> List.iter (collect_tvars_pty tbl) l
  | PTarrow (t1, t2) ->
      collect_tvars_pty tbl t1;
      collect_tvars_pty tbl t2

let collect_tvars tbl ts = collect_tvars_pty tbl ts.ts_ty

let rec only_uses_named tbl = function
  | PTtyvar v -> IdTable.mem tbl v.id_tag
  | PTtyapp (_, l) | PTtuple l -> List.for_all (only_uses_named tbl) l
  | PTarrow (t1, t2) -> only_uses_named tbl t1 || only_uses_named tbl t2

let only_uses_named tbl = List.for_all (only_uses_named tbl)

let is_infix_term tbl t =
  match t.t_node with
  | Tvar (Qid v) -> is_infix v
  | Ttyapply (Qid v, l) -> is_infix v && only_uses_named tbl l
  | _ -> false

let rec coq_term tvar_tbl t =
  let coq_term = coq_term tvar_tbl in
  match t.t_node with
  | Tvar v -> Coq_var (coq_id v)
  | Tconst c -> coq_const c
  | Tapply (f, arg1) -> (
      match f.t_node with
      | Tapply (f, arg2) when is_infix_term tvar_tbl f ->
          let f = get_infix f in
          let l = coq_term arg2 in
          let r = coq_term arg1 in
          if f = "->" then Coq_impl (l, r) else Coq_infix (l, f, r)
      | _ ->
          let e1 = coq_term f in
          let e2 = coq_term arg1 in
          coq_app e1 e2)
  | Ttyapply (q, ptys) ->
      let e1 = coq_var_at (qid_to_string q) in
      if only_uses_named tvar_tbl ptys then Coq_var (coq_id q)
      else
        let () = List.iter (collect_tvars_pty tvar_tbl) ptys in
        let l = List.map var_of_ty ptys in
        let l =
          List.concat_map
            (function
              | Coq_var v -> [ Coq_var v; Coq_var (to_inh v) ]
              | _ -> assert false)
            l
        in
        coq_apps e1 l
  | Tfield (t, q) ->
      let t = coq_term t in
      coq_record_proj t (qid_to_string q)
  | Tif (g, th, el) ->
      let gc = coq_term g in
      let thc = coq_term th in
      let elc = coq_term el in
      coq_if_prop gc thc elc
  | Tquant (q, ids, t) ->
      let f = match q with Tforall -> coq_foralls | Texists -> coq_exists in
      let () = List.iter (collect_tvars tvar_tbl) ids in
      let ids = List.map gen_args ids in
      f ids (coq_term t)
  | Tlambda (vl, t, _) ->
      let () = List.iter (collect_tvars tvar_tbl) vl in
      coq_funs (List.map gen_args vl) (coq_term t)
  | Tlet (vs, t1, t2) ->
      let vs = List.map (fun x -> coq_var x.ts_id.id_str) vs in
      Coq_lettuple (vs, coq_term t1, coq_term t2)
  | Told t -> coq_term t
  | Ttrue -> coq_prop_true
  | Tfalse -> coq_prop_false
  | Ttuple l -> coq_tuple (List.map coq_term l)
  | Trecord l -> coq_record (List.map (fun (x, t) -> (coq_id x, coq_term t)) l)
  | Tattr (_, t) -> coq_term t
  | Tscope _ | Tcast _ -> assert false

let cfml_term tbl t =
  let rec cfml_term = function
    | Logical t -> hpure (coq_term tbl t)
    | Lift (sym, l) ->
        let loc = List.hd l in
        let rep = List.nth l (List.length l - 1) in
        hdata (coq_term tbl loc)
          (coq_app (coq_var sym.ps_name.id_str) (coq_term tbl rep))
    | Wand (l, r) ->
        hwand (hstars (List.map cfml_term l)) (hstars (List.map cfml_term r))
    | Quant (q, vs, t) ->
        let f = match q with Tforall -> hforalls | Texists -> hexistss in
        let args = List.map (fun x -> (x.ts_id.id_str, var_of_ty x.ts_ty)) vs in
        let t = hstars (List.map cfml_term t) in
        f args t
  in
  cfml_term t

let gen_tbl tvars =
  let tbl = IdTable.create 100 in
  let () = List.iter (collect_tvars tbl) tvars in
  tbl

let gen_spec triple =
  let tbl = gen_tbl triple.triple_vars in
  let poly = gen_poly false triple.triple_poly in
  let args = List.map gen_spec_args triple.triple_args in
  let all_vars = List.map gen_args triple.triple_vars in
  let mk_condition tl = hstars (List.map (cfml_term tbl) tl) in
  let pre = mk_condition triple.triple_pre in
  let rets_typ =
    match triple.triple_rets with
    | [] -> coq_typ_unit
    | rets ->
        let f =
          Option.fold ~none:coq_typ_unit ~some:(fun v -> var_of_ty v.ts_ty)
        in
        coq_typ_tuple (List.map f rets)
  in

  let res_name = ref "_res_" in
  let mk_post (vl, tl) =
    let post = mk_condition tl in
    let term =
      List.fold_right
        (fun v acc -> hexists v.ts_id.id_str (var_of_ty v.ts_ty) acc)
        vl post
    in
    match triple.triple_rets with
    | [] -> term
    | [ Some x ] ->
        res_name := x.ts_id.id_str;
        term
    | [ None ] ->
        res_name := "_";
        term
    | rets ->
        let nms =
          List.map
            (function None -> Coq_wild | Some x -> Coq_var x.ts_id.id_str)
            rets
        in
        Coq_lettuple (nms, coq_var !res_name, term)
  in

  let post =
    coq_fun (tv !res_name rets_typ false) (mk_post triple.triple_post)
  in

  let f = "_" ^ triple.triple_name.id_str in
  let coq_triple = coq_spec f args pre post in
  let triple_vars = coq_foralls all_vars coq_triple in
  coq_foralls poly triple_vars

let mk_enc s = "_Enc_" ^ s

let rec sep_def d =
  match d.d_node with
  | Type tdef ->
      let ty =
        coq_impls (List.map (fun _ -> Coq_type) tdef.type_args) Coq_type
      in
      let nm = tdef.type_name.id_str in
      let poly = List.map (fun x -> tv x.id_str Coq_type true) tdef.type_args in
      let ty_decl = tv nm ty false in
      let inhab_param =
        tv ("__Inhab_" ^ nm) (coq_app inhab (coq_var nm)) false
      in
      let enc_param =
        if tdef.type_ocaml then
          [
            Coqtop_instance
              (tv ("__Enc_" ^ nm) (coq_app enc (coq_var nm)) false, None, false);
          ]
        else []
      in
      let def =
        match tdef.type_def with
        | Abstract -> Coqtop_param ty_decl
        | Alias t ->
            let t = var_of_ty t in
            let poly =
              List.map
                (fun x -> tv (String.capitalize_ascii x.id_str) Coq_type false)
                tdef.type_args
            in
            Coqtop_fundef (false, [ (tdef.type_name.id_str, poly, Coq_type, t) ])
        | Record r ->
            Coqtop_record
              {
                coqind_name = nm;
                coqind_constructor_name = "_mk_" ^ nm;
                coqind_targs = poly;
                coqind_ret = coq_typ_type;
                coqind_branches =
                  List.map
                    (fun (s, t) -> tv s.Ident.id_str (var_of_ty t) false)
                    r;
              }
      in
      [ def; Coqtop_instance (inhab_param, None, false) ] @ enc_param
  | Pred pred ->
      let args = List.rev pred.pred_args in
      let poly = gen_poly false pred.pred_poly in
      let types = List.map (fun v -> var_of_ty v.ts_ty) args in
      let t = coq_impls types hprop in
      let with_poly = coq_foralls poly t in
      [ Coqtop_param (tv (valid_coq_id pred.pred_name.id_str) with_poly false) ]
  | Triple triple ->
      let fun_def =
        tv ("_" ^ triple.triple_name.id_str) Formula.func_type false
      in
      let fun_triple = gen_spec triple in
      let triple_name = to_triple triple.triple_name.id_str in
      coqtop_params [ fun_def; tv triple_name fun_triple false ]
  | Val v ->
      let fun_def = tv ("_" ^ v.vname.id_str) Formula.func_type false in
      coqtop_params [ fun_def ]
  | Function f -> (
      if !is_stdlib && (is_infix f.fun_name || f.fun_name.id_str = "not") then
        []
      else
        let name = valid_coq_id f.fun_name.id_str in
        let args = f.fun_params in
        let ret = f.fun_ret in
        let ret_coq = var_of_ty ret in
        let args_coq =
          List.map
            (fun arg -> tv arg.ts_id.id_str (var_of_ty arg.ts_ty) false)
            args
        in
        let tbl = gen_tbl f.fun_params in
        let def = Option.map (coq_term tbl) f.fun_def in
        let poly_types = gen_poly true f.fun_tvars in
        match def with
        | Some d ->
            let coq_def = (name, poly_types @ args_coq, ret_coq, d) in
            if f.fun_rec then [ coqtop_fixdef coq_def ]
            else [ coqtop_fundef coq_def ]
        | None ->
            let t =
              coq_impls (List.map (fun x -> x.var_type) args_coq) ret_coq
            in
            let poly_args = coq_foralls poly_types t in
            coqtop_params [ tv name poly_args false ])
  | Axiom a ->
      let is_pure =
        match a.sax_term with [ Logical _ ] -> true | _ -> false
      in
      let tbl = gen_tbl [] in
      let t =
        match a.sax_term with
        | [ Logical t ] -> coq_term tbl t
        | t ->
            let t = hstars (List.map (cfml_term tbl) t) in
            himpl hempty t
      in
      let poly_vars = gen_poly is_pure a.sax_tvars in
      [ Coqtop_axiom (tv a.sax_name.id_str (coq_foralls poly_vars t) false) ]
  | Module (nm, l) ->
      let statements = List.concat_map sep_def l in
      let nm_var = valid_coq_id nm.id_str in
      let m = Coqtop_module (nm_var, [], Mod_cast_free, Mod_def_declare) in
      (m :: statements) @ [ Coqtop_end nm_var ]
  | Import l -> [ Coqtop_import (List.map valid_coq_id l) ]

let sep_defs ~stdlib file =
  let () = is_stdlib := stdlib in
  let cfml = List.map (fun s -> "CFML." ^ s) in
  let imports =
    [ Coqtop_set_implicit_args ]
    @ (if !is_stdlib then []
       else
         [
           Coqtop_require_import [ "Gospelstdlib_verified" ];
           Coqtop_import [ "Gospelstdlib" ];
         ])
    @ [
        Coqtop_require
          [
            "Coq.ZArith.BinInt";
            "TLC.LibLogic";
            "TLC.LibRelation";
            "TLC.LibInt";
            "TLC.LibListZ";
          ];
        Coqtop_require_import
          (cfml
             [
               "SepBase";
               "SepLifted";
               "WPLib";
               "WPLifted";
               "WPRecord";
               "WPArray";
               "WPBuiltin";
             ]);
        (*coqtop_require_unless no_mystd_include*)
        Coqtop_require
          (cfml [ "Stdlib.Array_ml"; "Stdlib.List_ml"; "Stdlib.Sys_ml" ]);
        Coqtop_require_import
          [ "Coq.ZArith.BinIntDef"; "CFML.Semantics"; "CFML.WPHeader" ];
        Coqtop_custom "Delimit Scope Z_scope with Z."
        (*Coqtop_custom "Existing Instance WPHeader.Enc_any | 99."*);
      ]
  in
  let tops = List.concat_map sep_def file.Gospel.fdefs in
  let top =
    if !is_stdlib then
      (Coqtop_module_type ("Stdlib", [], Mod_def_declare) :: tops)
      @ [ Coqtop_end "Stdlib" ]
    else tops
  in
  imports @ top

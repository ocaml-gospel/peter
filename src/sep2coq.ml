open Gospel_checker
open Sast
open Id_uast
open Ident
open Tast
open Coq
open Formula
open Coq_driver
module M = Map.Make (String)

type decls = {
  abstract : Coq.coqtops;
  concrete : Coq.coqtops;
  obligations : Coq.coqtops;
}

let empty_decls = { abstract = []; concrete = []; obligations = [] }
let is_stdlib = ref false
let to_triple s = "_" ^ s ^ "_spec"

let ty_map =
  List.fold_left (fun m (k, v) -> M.add k v m) M.empty type_mapping_list

let id_map =
  List.fold_left (fun m (k, v) -> M.add k v m) M.empty id_mapping_list

let is_ignore x = List.mem x ignore_list
let backend = Print_coq.backend

let unicode_mapper = function
  | "∈" -> "belongs"
  | "∉" -> "neg_belongs"
  | "⋅" -> "multiplicity"
  | "∪" -> "union"
  | "∩" -> "inter"
  | "⊂" -> "subset"
  | "∖" -> "diff"
  | "++" -> "app"
  | "∅" | "[]" -> "empty"
  | s -> s

let id_mapper = function
  | "-" -> "neg"
  | "+" -> "plus"
  | "*" -> "mult"
  | "/" -> "div"
  | ">" -> "gt"
  | ">=" -> "ge"
  | "<>" -> "neq"
  | "<->" -> "iff"
  | "<" -> "lt"
  | "<=" -> "le"
  | "=" -> "eq"
  | "->" -> "impl"
  | "||" -> "orb"
  | "&&" -> "andb"
  | "[_]" -> "seq_get"
  | "[_.._]" -> "seq_sub"
  | "[_..]" -> "seq_sub_l"
  | "[.._]" -> "seq_sub_r"
  | "[->]" -> "map_set"
  | "{}" -> "set_create"
  | "{:_:}" -> "singleton_set"
  | s -> unicode_mapper s

let coq_keywords = [ "mod"; "Set"; "Alias" ]

let inhab () =
  match !backend with CFML -> Coq_var "Inhab" | Iris -> Coq_var "Inhabited"

let enc = Coq_var "Enc"
let valid_coq_id s = if List.mem s coq_keywords then "_" ^ s else id_mapper s

let stdlib_sym id =
  match id.id_str with
  | "prop" -> "Prop"
  | "integer" -> "Z"
  | "char" -> "ascii"
  | _ -> unicode_mapper id.id_str

let rec qid_to_string =
  let valid_string id =
    if Ident.is_stdlib id || Ident.is_primitive id then stdlib_sym id
    else valid_coq_id id.id_str
  in
  function
  | Qid id -> valid_string id
  | Qdot (q, id) -> qid_to_string q ^ "." ^ valid_string id

let var_of_ty t =
  let rec var_of_ty = function
    | PTtyapp (v, l) ->
        coq_apps (coq_var (qid_to_string v.app_qid)) (List.map var_of_ty l)
    | PTarrow (t1, t2) -> coq_impl (var_of_ty t1) (var_of_ty t2)
    | PTtyvar tv -> Coq_var (String.capitalize_ascii tv.id_str)
    | PTtuple l -> coq_prods (List.map var_of_ty l)
  in
  var_of_ty t

let coq_id id = qid_to_string id

let rec is_predicate = function
  | PTarrow (_, t) -> is_predicate t
  | PTtyapp ({ app_qid = Qid v; _ }, []) -> Ident.equal v Structure.prop_id
  | _ -> false

let to_dec = ( ^ ) "Dec_"

let gen_args vs =
  let v = tv vs.ts_id.id_str (var_of_ty vs.ts_ty) false in
  v

let gen_args_pat p =
  match p.pat_desc with Pid vs -> gen_args vs | _ -> assert false

let let_pat p =
  match p.pat_desc with
  | Pwild -> []
  | Pid ts -> [ coq_var ts.ts_id.id_str ]
  | Ptuple ts ->
      List.map
        (fun x ->
          match x.pat_desc with
          | Pid id -> coq_var id.ts_id.id_str
          | _ -> assert false)
        ts
  | _ -> assert false

let gen_spec_args = function
  | Sast.Unit -> (
      match !backend with
      | CFML -> coq_tt_tv
      | Iris -> tv "#()" coq_typ_unit false)
  | Wildcard -> assert false (* TODO *)
  | Ghost ts -> gen_args ts
  | Value v -> gen_args v.arg_ocaml

let coq_const c =
  match c with
  | Parse_uast.Pconst_integer (v, None) -> coq_int (int_of_string v)
  | _ -> assert false

let to_inh = ( ^ ) "Ih_"
let to_enc = ( ^ ) "Enc_"
let to_eq_dec = ( ^ ) "Eq_"

let gen_poly is_pure poly_vars =
  let types =
    List.map
      (fun v -> tv (String.capitalize_ascii v.id_str) Coq_type true)
      poly_vars
  in
  let type_properties v =
    let nm = String.capitalize_ascii v.var_name in
    let inhab = (to_inh nm, coq_app (inhab ()) (coq_var nm)) in
    let enc = (to_enc nm, coq_app enc (coq_var nm)) in
    let param =
      if is_pure || !backend <> CFML then [ inhab ] else [ inhab; enc ]
    in
    List.map (fun (n, c) -> tv n c true) param
  in
  let properties = List.concat_map type_properties types in
  types @ properties

let fixity_mapper v =
  match v.id_fixity with
  | Normal -> v.id_str
  | Prefix -> if v.id_str = "-" then "minus" else assert false
  | Infix | Mixfix | Let -> id_mapper v.id_str

let is_infix v = match v.id_fixity with Infix -> true | _ -> false

let get_infix t =
  match t.t_node with
  | Tvar (Qid v) | Ttyapply (Qid v, _) -> v.id_str
  | _ -> assert false

let rec collect_tvars_pty tbl = function
  | PTtyvar v -> IdTable.replace tbl v.id_tag v
  | PTtyapp (_, l) | PTtuple l -> List.iter (collect_tvars_pty tbl) l
  | PTarrow (t1, t2) ->
      collect_tvars_pty tbl t1;
      collect_tvars_pty tbl t2

let collect_tvars tbl ts = collect_tvars_pty tbl ts.ts_ty

let rec collect_tvars_pat tbl p =
  match p.pat_desc with
  | Pwild -> ()
  | Pid ts -> collect_tvars tbl ts
  | Ptuple l -> List.iter (collect_tvars_pat tbl) l
  | Pcast (p, ty) ->
      collect_tvars_pat tbl p;
      collect_tvars_pty tbl ty

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
      let s = qid_to_string q in
      let e1 = coq_var_at s in
      if only_uses_named tvar_tbl ptys then Coq_var (coq_id q)
      else
        let () = List.iter (collect_tvars_pty tvar_tbl) ptys in
        let l = List.map var_of_ty ptys in
        let l =
          List.concat_map
            (function
              | Coq_var v when !Print_coq.backend = Iris ->
                  [ Coq_var v; Coq_var (to_eq_dec v); Coq_var (to_inh v) ]
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
  | Tset (v, p) -> coq_set v.ts_id.id_str (coq_term p)
  | Tquant (q, ids, t) ->
      let f = match q with Tforall -> coq_foralls | Texists -> coq_exists in
      let () = List.iter (collect_tvars tvar_tbl) ids in
      let ids = List.map gen_args ids in
      f ids (coq_term t)
  | Tlambda (vl, t, _) ->
      let () = List.iter (collect_tvars_pat tvar_tbl) vl in
      coq_funs (List.map gen_args_pat vl) (coq_term t)
  | Tlet (pat, t1, t2) ->
      let pat = let_pat pat in
      Coq_lettuple (pat, coq_term t1, coq_term t2)
  | Told t -> coq_term t
  | Ttrue -> coq_bool_true
  | Tfalse -> coq_bool_false
  | TTrue -> coq_prop_true
  | TFalse -> coq_prop_false
  | Ttuple l -> coq_tuple (List.map coq_term l)
  | Trecord l -> coq_record (List.map (fun (x, t) -> (coq_id x, coq_term t)) l)
  | Tattr (_, t) -> coq_term t
  | Tscope _ | Tcast _ -> assert false

let cfml_term tbl t =
  let rec cfml_term = function
    | Logical t -> hpure (coq_term tbl t)
    | Lift (sym, arg1, arg2) ->
        let loc = arg1 in
        let rep = arg2 in
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

let loc_ty =
  let loc_id = Ident.mk_id ~loc:Location.none "loc" in
  let loc_app =
    {
      app_qid = Qid loc_id;
      app_alias = None;
      app_model = None;
      app_mut = false;
    }
  in
  PTtyapp (loc_app, [])

let val_ty =
  let loc_id = Ident.mk_id ~loc:Location.none "val" in
  let loc_app =
    {
      app_qid = Qid loc_id;
      app_alias = None;
      app_model = None;
      app_mut = false;
    }
  in
  PTtyapp (loc_app, [])

let triple_val_to_ts = function
  | Sast.Unit | Wildcard -> []
  | Ghost ts -> [ ts ]
  | Value v ->
      let ocaml =
        match !backend with
        | CFML ->
            if v.is_loc then { v.arg_ocaml with ts_ty = loc_ty }
            else v.arg_ocaml
        | Iris -> { v.arg_ocaml with ts_ty = val_ty }
      in
      [ ocaml; v.arg_model ]

let gen_spec triple =
  let all_ts = List.concat_map triple_val_to_ts triple.triple_args in
  let tbl = gen_tbl all_ts in
  let poly = gen_poly false triple.triple_poly in
  let args = List.map gen_spec_args triple.triple_args in
  let all_vars = List.map gen_args all_ts in
  let mk_condition tl = hstars (List.map (cfml_term tbl) tl) in
  let pre = mk_condition triple.triple_pre in
  let ex, posts = triple.triple_post in
  let post = mk_condition posts in
  let post_ex =
    List.fold_right
      (fun v acc -> hexists v.ts_id.id_str (var_of_ty v.ts_ty) acc)
      ex post
  in

  let ret_vars =
    match triple.triple_rets with
    | [] -> [ Coq.Unit ]
    | rets ->
        let f = function
          | Sast.Unit -> Coq.Unit
          | Wildcard -> Coq.Wildcard
          | Ghost _ -> assert false
          | Value v ->
              let nm = v.arg_ocaml.ts_id.id_str in
              Coq.Var nm
        in
        List.map f rets
  in

  let f = "_" ^ triple.triple_name.id_str in
  let coq_triple = coq_spec f args pre ret_vars post_ex in
  let triple_vars = coq_foralls all_vars coq_triple in
  coq_foralls poly triple_vars

let mk_enc s = "_Enc_" ^ s
let val_var = Coq_var "val"

let tdef tdef =
  let ty = coq_impls (List.map (fun _ -> Coq_type) tdef.type_args) Coq_type in
  let nm = tdef.type_name.id_str in
  let poly =
    List.map
      (fun x -> tv (String.capitalize_ascii x.id_str) Coq_type false)
      tdef.type_args
  in
  let ty_decl = tv nm ty false in
  let enc_param =
    if tdef.type_ocaml && !backend = CFML then
      [
        Coqtop_instance
          (tv ("__Enc_" ^ nm) (coq_app enc (coq_var nm)) false, None, false);
      ]
    else []
  in
  match !backend with
  | Iris -> empty_decls
  | CFML -> (
      match tdef.type_def with
      | Abstract ->
          let def = Coqtop_param ty_decl in
          { empty_decls with abstract = def :: enc_param }
      | Alias t ->
          let t = var_of_ty t in
          let poly =
            List.map
              (fun x -> tv (String.capitalize_ascii x.id_str) Coq_type false)
              tdef.type_args
          in
          let def =
            Coqtop_fundef (false, [ (tdef.type_name.id_str, poly, Coq_type, t) ])
          in
          { empty_decls with abstract = enc_param; concrete = [ def ] }
      | Record r ->
          let def =
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
          { empty_decls with abstract = enc_param; concrete = [ def ] })

let rec combine x acc =
  let defs = sep_def x in
  {
    abstract = defs.abstract @ acc.abstract;
    concrete = defs.concrete @ acc.concrete;
    obligations = defs.obligations @ acc.obligations;
  }

and sep_def d =
  match d.d_node with
  | Type t -> tdef t
  | Pred pred ->
      let args = List.rev pred.pred_args in
      let poly = gen_poly false pred.pred_poly in
      let types =
        List.mapi
          (fun i v ->
            if !backend = Iris && i = 1 then var_of_ty val_ty
            else var_of_ty v.ts_ty)
          args
      in
      let t = coq_impls types (hprop ()) in
      let with_poly = coq_foralls poly t in
      let param = tv (valid_coq_id pred.pred_name.id_str) with_poly false in
      { empty_decls with abstract = coqtop_params [ param ] }
  | Triple triple ->
      let val_nm = triple.triple_name.id_str in
      let fun_def = tv ("_" ^ val_nm) val_var false in
      let fun_triple = gen_spec triple in
      let triple_name = to_triple triple.triple_name.id_str in
      let params =
        coqtop_params [ tv triple_name (Coq_var triple_name) false ]
      in
      let def = [ coqtop_def_untyped triple_name fun_triple ] in
      {
        abstract = coqtop_params [ fun_def ];
        concrete = def;
        obligations = params;
      }
  | Val v ->
      let fun_def = tv ("_" ^ v.vname.id_str) Formula.func_type false in
      { empty_decls with abstract = coqtop_params [ fun_def ] }
  | Function f -> (
      if !is_stdlib && (is_infix f.fun_name || f.fun_name.id_str = "not") then
        empty_decls
      else
        let name = valid_coq_id f.fun_name.id_str in
        let args = f.fun_params in
        let ret = f.fun_ret in
        let ret_coq = var_of_ty ret in
        let args_coq = List.map gen_args args in
        let tbl = gen_tbl f.fun_params in
        let def = Option.map (coq_term tbl) f.fun_def in
        let poly_types = gen_poly true f.fun_tvars in
        match def with
        | Some d ->
            let coq_def = (name, poly_types @ args_coq, ret_coq, d) in
            if f.fun_rec then
              { empty_decls with concrete = [ coqtop_fixdef coq_def ] }
            else { empty_decls with concrete = [ coqtop_fundef coq_def ] }
        | None ->
            let poly_args = coq_foralls (poly_types @ args_coq) ret_coq in
            {
              empty_decls with
              abstract = coqtop_params [ tv name poly_args false ];
            })
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
      let t = coq_foralls poly_vars t in
      let def = coqtop_fundef (a.sax_name.id_str, [], Coq_wild, t) in
      let ax =
        Coqtop_axiom (tv a.sax_name.id_str (Coq_var a.sax_name.id_str) false)
      in
      { empty_decls with concrete = [ def ]; obligations = [ ax ] }
  | Module (nm, l) ->
      let statements = List.fold_right combine l empty_decls in
      let nm_var = valid_coq_id nm.id_str in
      let m = Coqtop_module (nm_var, [], Mod_cast_free, Mod_def_declare) in
      let end_mod = [ Coqtop_end nm_var ] in
      {
        abstract = (m :: statements.abstract) @ end_mod;
        concrete = (m :: statements.concrete) @ end_mod;
        obligations = (m :: statements.obligations) @ end_mod;
      }
  | Import l ->
      let l = [ Coqtop_import [ qid_to_string l ] ] in
      { abstract = l; concrete = l; obligations = l }

let import_stdlib () =
  match !backend with
  | CFML ->
      [
        Coqtop_custom "Set Warnings \"-deprecated\".";
        Coqtop_custom "Set Warnings \"-default\".";
        Coqtop_custom "Set Warnings \"-syntax\".";
        Coqtop_require_import
          [
            "Stdlib.ZArith.BinInt";
            "TLC.LibLogic";
            "TLC.LibRelation";
            "TLC.LibInt";
            "TLC.LibListZ";
          ];
      ]
  | Iris -> [ Coqtop_require_import [ "Stdlib.ZArith.BinInt"; "stdpp.base" ] ]

let import_gospelstdlib stdlib =
  if stdlib then import_stdlib ()
  else
    (match !backend with
    | CFML -> Coqtop_require_import [ "Stdlib_tlc.gospelstdlib_verified_tlc" ]
    | Iris ->
        Coqtop_require_import [ "Stdlib_stdpp.gospelstdlib_verified_stdpp" ])
    :: [ Coqtop_import [ "Stdlib" ] ]

let import_sep_semantics stdlib =
  if stdlib then []
  else
    let cfml = List.map (fun s -> "CFML." ^ s) in
    let l =
      match !backend with
      | CFML ->
          cfml
            [
              "SepBase";
              "SepLifted";
              "WPLib";
              "WPLifted";
              "WPRecord";
              "WPArray";
              "WPBuiltin";
              "CFML.Semantics";
              "CFML.WPHeader";
            ]
      | Iris ->
          [
            "iris.proofmode.proofmode";
            "iris.heap_lang.proofmode";
            "iris.heap_lang.notation";
            "iris.prelude.options";
          ]
    in
    [ Coqtop_require_import l ]

let sep_defs ~stdlib ~sep_logic file =
  let () = is_stdlib := stdlib in
  let () = Print_coq.backend := sep_logic in
  let imports =
    [ Coqtop_set_implicit_args ]
    @ import_gospelstdlib stdlib
    @ [
        Coqtop_require_import
          [
            "Stdlib.Floats.Floats";
            "Stdlib.ZArith.BinIntDef";
            "Stdlib.Strings.Ascii";
          ];
      ]
    @ import_sep_semantics stdlib
    @
    match !backend with
    | Iris -> [ Coqtop_custom "Local Open Scope Z_scope." ]
    | CFML ->
        [
          Coqtop_custom "Local Open Scope Z_scope.";
          Coqtop_custom "Local Open Scope comp_scope.";
        ]
  in
  let abs, specs, specs_typ, obl = ("Abs", "Defs", "D", "Obligations") in
  let acc =
    {
      abstract = [ Coqtop_end abs ];
      concrete = [];
      obligations = [ Coqtop_end obl ];
    }
  in
  let defs = List.fold_right combine file.Gospel.fdefs acc in
  let abs_mod =
    Coqtop_module_type (abs, [], Mod_def_declare) :: defs.abstract
  in
  let abs_arg = "S" in
  let concrete_args = [ ([ abs_arg ], Mod_typ_var abs) ] in
  let abs_imp = Coqtop_import [ abs_arg ] in
  let concrete_typ =
    Coqtop_module_type (specs_typ, concrete_args, Mod_def_declare)
    :: abs_imp :: defs.concrete
    @ [ Coqtop_end specs_typ ]
  in
  let concrete =
    Coqtop_module (specs, concrete_args, Mod_cast_free, Mod_def_declare)
    :: abs_imp :: defs.concrete
    @ [ Coqtop_end specs ]
  in
  let conc_arg = "C" in
  let obl_args =
    concrete_args @ [ ([ conc_arg ], Mod_typ_app [ specs_typ; abs_arg ]) ]
  in
  let imp = [ Coqtop_import [ conc_arg ]; abs_imp ] in
  let obligations =
    (Coqtop_module_type (obl, obl_args, Mod_def_declare) :: imp)
    @ defs.obligations
  in
  let tops = abs_mod @ concrete_typ @ concrete @ obligations in
  let top =
    if !is_stdlib then Coqtop_param (tv "set" (coq_impl_types 1) false) :: tops
    else tops
  in
  imports @ top

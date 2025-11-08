open Gospel_checker
open Sast
open Id_uast
open Ident
open Tast
open Rocq
module M = Map.Make (String)

type decls = {
  declarations : Rocq.rocqtops;
  (* These contain concrete Gospel definitions as well as the
       signatures of abstract definitions *)
  obligations : Rocq.rocqtops;
      (* These contain the definitions the user must provide in
           order to prove the statements in the Gospel file.  These
           definitions can depend on the definitions in the
           [declarations] field. *)
}
(** The declarations Peter will generate. *)

module type Sep_to_rocq = sig
  val ocaml_to_ts : tsymbol -> tsymbol
  val ocaml_record : (Ident.t * Id_uast.pty) list -> decls
  val prelude : rocqtops
end

module type P = sig
  val sep_defs : stdlib:bool -> Sast.definition list Gospel.file -> rocqtop list
end

module Peter (M : Sep_to_rocq) : P = struct
  open M

  let empty_decls = { declarations = []; obligations = [] }

  (** This flag notes if we are translating a Gospel file that only contains
      logical definitions. *)
  let is_logical = ref true

  let to_triple s = "_" ^ s ^ "_spec"

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

  let rocq_keywords = [ "mod"; "Set"; "Alias" ]

  let valid_rocq_id s =
    if List.mem s rocq_keywords then "_" ^ s else id_mapper s

  let stdlib_sym id =
    match id.id_str with
    | "prop" -> "Prop"
    | "integer" -> "Z"
    | "char" -> "ascii"
    | _ -> unicode_mapper id.id_str

  let rec qid_to_string =
    let valid_string id =
      if Ident.is_stdlib id || Ident.is_primitive id then stdlib_sym id
      else valid_rocq_id id.id_str
    in
    function
    | Qid id -> valid_string id
    | Qdot (q, id) -> qid_to_string q ^ "." ^ valid_string id

  let rocq_ty t =
    let rec rocq_ty = function
      | PTtyapp (v, l) ->
          rocq_apps (rocq_var (qid_to_string v.app_qid)) (List.map rocq_ty l)
      | PTarrow (t1, t2) -> rocq_impl (rocq_ty t1) (rocq_ty t2)
      | PTtyvar tv -> Rocq_var (to_tvar tv)
      | PTtuple l -> rocq_prods (List.map rocq_ty l)
    in
    rocq_ty t

  let rocq_id id = qid_to_string id
  let rocq_tv vs = tv vs.ts_id.id_str (rocq_ty vs.ts_ty)

  let gen_args_pat p =
    match p.pat_desc with Pid vs -> rocq_tv vs | _ -> assert false

  let let_pat p =
    match p.pat_desc with
    | Pwild -> []
    | Pid ts -> [ rocq_var ts.ts_id.id_str ]
    | Ptuple ts ->
        List.map
          (fun x ->
            match x.pat_desc with
            | Pid id -> rocq_var id.ts_id.id_str
            | _ -> assert false)
          ts
    | _ -> assert false

  let spec_arg = function
    | Sast.Unit -> Some Unit
    | Wildcard -> Some Wildcard
    | Ghost _ -> None
    | Value v -> Some (Var v.arg_ocaml.ts_id.id_str)

  let spec_args = List.filter_map spec_arg

  let rocq_const c =
    match c with
    | Parse_uast.Pconst_integer (v, None) -> rocq_int (int_of_string v)
    | _ -> assert false

  let gen_poly ~ocaml poly_vars =
    let typ = if ocaml then ocaml_type else gospel_type in
    let types = List.map (fun v -> tv (to_tvar v) typ) poly_vars in
    types

  let fixity_mapper v =
    match v.id_fixity with
    | Normal -> v.id_str
    | Prefix -> if v.id_str = "-" then "minus" else assert false
    | Infix | Mixfix -> id_mapper v.id_str

  let is_infix v = match v.id_fixity with Infix -> true | _ -> false

  let get_infix t =
    match t.t_node with Tvar (Qid v, _) -> v.id_str | _ -> assert false

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
    | Tvar (Qid v, l) -> is_infix v && only_uses_named tbl l
    | _ -> false

  let rec rocq_term tvar_tbl t =
    let rocq_term = rocq_term tvar_tbl in
    match t.t_node with
    | Tvar (q, ptys) ->
        let s = qid_to_string q in
        let e1 = rocq_var_at s in
        if only_uses_named tvar_tbl ptys then Rocq_var (rocq_id q)
        else
          let () = List.iter (collect_tvars_pty tvar_tbl) ptys in
          let l = List.map rocq_ty ptys in
          rocq_apps e1 l
    | Tconst c -> rocq_const c
    | Tapply (f, arg1) -> (
        match f.t_node with
        | Tapply (f, arg2) when is_infix_term tvar_tbl f ->
            let f = get_infix f in
            let l = rocq_term arg2 in
            let r = rocq_term arg1 in
            Rocq_infix (l, f, r)
        | _ ->
            let e1 = rocq_term f in
            let e2 = rocq_term arg1 in
            rocq_app e1 e2)
    | Tfield (t, q) ->
        let t = rocq_term t in
        rocq_record_proj t (qid_to_string q)
    | Tif (g, th, el) ->
        let gc = rocq_term g in
        let thc = rocq_term th in
        let elc = rocq_term el in
        rocq_if_prop gc thc elc
    | Tset (v, p) -> rocq_set v.ts_id.id_str (rocq_term p)
    | Tquant (q, ids, t) ->
        let f =
          match q with Tforall -> rocq_foralls | Texists -> rocq_exists
        in
        let () = List.iter (collect_tvars tvar_tbl) ids in
        let ids = List.map rocq_tv ids in
        f ids (rocq_term t)
    | Tlambda (vl, t, _) ->
        let () = List.iter (collect_tvars_pat tvar_tbl) vl in
        rocq_funs (List.map gen_args_pat vl) (rocq_term t)
    | Tlet (pat, t1, t2) ->
        let pat = let_pat pat in
        Rocq_lettuple (pat, rocq_term t1, rocq_term t2)
    | Told t -> rocq_term t
    | Ttrue -> rocq_bool_true
    | Tfalse -> rocq_bool_false
    | TTrue -> rocq_prop_true
    | TFalse -> rocq_prop_false
    | Ttuple l -> rocq_tuple (List.map rocq_term l)
    | Trecord l ->
        rocq_record (List.map (fun (x, t) -> (rocq_id x, rocq_term t)) l)
    | Tattr (_, t) -> rocq_term t
    | Tscope _ | Tcast _ -> assert false

  let gen_tbl tvars =
    let tbl = IdTable.create 100 in
    let () = List.iter (collect_tvars tbl) tvars in
    tbl

  let loc_ty =
    let loc_id = Ident.mk_id ~loc:Location.none "loc" in
    let loc_app = { app_qid = Qid loc_id; app_alias = None; app_mut = false } in
    PTtyapp (loc_app, [])

  let triple_val_to_ts = function
    | Sast.Unit | Wildcard -> []
    | Ghost ts -> [ ts ]
    | Value v ->
        let ocaml = ocaml_to_ts v.arg_ocaml in
        [ ocaml; v.arg_model ]

  let sep_term tbl t =
    let rec sep_term = function
      | Logical t -> Rocq_pure (rocq_term tbl t)
      | Lift (sym, arg1, arg2) ->
          let ocaml = rocq_term tbl arg1 in
          let model = rocq_term tbl arg2 in
          Rocq_lift (sym.ps_name.id_str, ocaml, model)
      | Quant (q, vs, t) ->
          let q = match q with Tforall -> Forall | Texists -> Exists in
          let args =
            List.map (fun x -> tv x.ts_id.id_str (rocq_ty x.ts_ty)) vs
          in
          let t = List.map sep_term t in
          Rocq_hquant (q, args, t)
      | Wand _ -> assert false
    in
    sep_term t

  let sep_terms tbl = List.map (sep_term tbl)

  let triple_rets l =
    match l with [] -> [ Rocq.Unit ] | rets -> spec_args rets

  let gen_spec triple =
    let all_ts = List.concat_map triple_val_to_ts triple.triple_args in
    let tbl = gen_tbl all_ts in
    let poly = gen_poly ~ocaml:true triple.triple_poly in
    let args = spec_args triple.triple_args in
    let all_vars = List.map rocq_tv all_ts in
    let pre = sep_terms tbl triple.triple_pre in
    let ex, posts = triple.triple_post in
    let post = sep_terms tbl posts in
    let vars = List.map rocq_tv ex in
    let post = rocq_hexists vars post in
    let ret_vars = triple_rets triple.triple_rets in
    let f = "_" ^ triple.triple_name.id_str in
    rocq_spec f (poly @ all_vars) pre args ret_vars post

  let val_var = Rocq_var "val"
  let class_name v = "__" ^ v ^ "_sig"
  let inst_name v = "__" ^ v ^ "_inst"

  let tdef tdef =
    let tname = tdef.type_name.id_str in
    match tdef.type_def with
    | Abstract ->
        let class_name = class_name tname in
        let inst_name = inst_name tname in
        let typ = rocq_forall_types ~ocaml:false tdef.type_args in
        let c = tclass class_name tname typ in
        let inst = tinst inst_name class_name in
        { declarations = [ c ]; obligations = [ inst ] }
    | Alias t ->
        let t = rocq_ty t in
        let tvars = rocq_types ~ocaml:false tdef.type_args in
        let def =
          rocqtop_def false tname [] (assert false) tvars (typ ~ocaml:false) t
        in
        { empty_decls with declarations = [ def ] }
    | Record r ->
        if tdef.type_ocaml then assert false
        else
          let tvars = rocq_types ~ocaml:false tdef.type_args in
          let def =
            Rocqtop_record
              {
                rocqind_name = tname;
                rocqind_constructor_name = "_mk_" ^ tname;
                rocqind_targs = tvars;
                rocqind_ret = gospel_type;
                rocqind_branches =
                  List.map (fun (s, t) -> tv s.Ident.id_str (rocq_ty t)) r;
              }
          in
          { empty_decls with declarations = [ def ] }

  let rec combine x acc =
    let defs = sep_def x in
    {
      declarations = defs.declarations @ acc.declarations;
      obligations = defs.obligations @ acc.obligations;
    }

  and sep_def d =
    match d.d_node with
    | Type t -> tdef t
    | Pred pred ->
        let args = List.rev pred.pred_args in
        let poly = gen_poly ~ocaml:false pred.pred_poly in
        let types =
          List.mapi
            (fun i v ->
              if !backend = Iris && i = 1 then rocq_ty val_ty
              else rocq_ty v.ts_ty)
            args
        in
        let t = rocq_impls types (hprop ()) in
        let with_poly = rocq_foralls poly t in
        let param = tv (valid_rocq_id pred.pred_name.id_str) with_poly false in
        { empty_decls with abstract = rocqtop_params [ param ] }
    | Triple triple ->
        let val_nm = triple.triple_name.id_str in
        let fun_def = tv ("_" ^ val_nm) val_var false in
        let fun_triple = gen_spec triple in
        let triple_name = to_triple triple.triple_name.id_str in
        let params =
          rocqtop_params [ tv triple_name (Rocq_var triple_name) false ]
        in
        let def = [ rocqtop_def_untyped triple_name fun_triple ] in
        {
          abstract = rocqtop_params [ fun_def ];
          concrete = def;
          obligations = params;
        }
    | Val v ->
        let fun_def = tv ("_" ^ v.vname.id_str) Formula.func_type false in
        { empty_decls with abstract = rocqtop_params [ fun_def ] }
    | Function f -> (
        if !is_logical && (is_infix f.fun_name || f.fun_name.id_str = "not")
        then empty_decls
        else
          let name = valid_rocq_id f.fun_name.id_str in
          let args = f.fun_params in
          let ret = f.fun_ret in
          let ret_rocq = rocq_ty ret in
          let args_rocq = List.map gen_args args in
          let tbl = gen_tbl f.fun_params in
          let def = Option.map (rocq_term tbl) f.fun_def in
          let poly_types = gen_poly ~ocaml:false f.fun_tvars in
          match def with
          | Some d ->
              let rocq_def = (name, poly_types @ args_rocq, ret_rocq, d) in
              if f.fun_rec then
                { empty_decls with concrete = [ rocqtop_fixdef rocq_def ] }
              else { empty_decls with concrete = [ rocqtop_fundef rocq_def ] }
          | None ->
              let poly_args = rocq_foralls (poly_types @ args_rocq) ret_rocq in
              {
                empty_decls with
                abstract = rocqtop_params [ tv name poly_args false ];
              })
    | Axiom a ->
        let is_pure =
          match a.sax_term with [ Logical _ ] -> true | _ -> false
        in
        let tbl = gen_tbl [] in
        let t =
          match a.sax_term with
          | [ Logical t ] -> rocq_term tbl t
          | t ->
              let t = hstars (List.map (cfml_term tbl) t) in
              himpl hempty t
        in
        let poly_vars = gen_poly ~ocaml:is_pure a.sax_tvars in
        let t = rocq_foralls poly_vars t in
        let def = rocqtop_fundef (a.sax_name.id_str, [], Rocq_wild, t) in
        let ax =
          Rocqtop_axiom
            (tv a.sax_name.id_str (Rocq_var a.sax_name.id_str) false)
        in
        { empty_decls with concrete = [ def ]; obligations = [ ax ] }
    | Module (nm, l) ->
        let statements = List.fold_right combine l empty_decls in
        let nm_var = valid_rocq_id nm.id_str in
        let m = Rocqtop_module (nm_var, [], Mod_cast_free, Mod_def_declare) in
        let end_mod = [ Rocqtop_end nm_var ] in
        {
          abstract = (m :: statements.abstract) @ end_mod;
          concrete = (m :: statements.concrete) @ end_mod;
          obligations = (m :: statements.obligations) @ end_mod;
        }
    | Import l ->
        let l = [ Rocqtop_import [ qid_to_string l ] ] in
        { abstract = l; concrete = l; obligations = l }

  let import_stdlib () =
    match !backend with
    | CFML ->
        [
          Rocqtop_custom "Set Warnings \"-deprecated\".";
          Rocqtop_custom "Set Warnings \"-default\".";
          Rocqtop_custom "Set Warnings \"-syntax\".";
          Rocqtop_require_import
            [
              "Stdlib.ZArith.BinInt";
              "TLC.LibLogic";
              "TLC.LibRelation";
              "TLC.LibInt";
              "TLC.LibListZ";
            ];
        ]
    | Iris ->
        [ Rocqtop_require_import [ "Stdlib.ZArith.BinInt"; "stdpp.base" ] ]

  let import_gospelstdlib stdlib =
    if stdlib then import_stdlib ()
    else
      (match !backend with
      | CFML ->
          Rocqtop_require_import [ "Stdlib_tlc.gospelstdlib_verified_tlc" ]
      | Iris ->
          Rocqtop_require_import [ "Stdlib_stdpp.gospelstdlib_verified_stdpp" ])
      :: [ Rocqtop_import [ "Stdlib" ] ]

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
      [ Rocqtop_require_import l ]

  let sep_defs ~stdlib file =
    let () = is_logical := stdlib in
    let () = Print_rocq.backend := sep_logic in
    let imports =
      [ Rocqtop_set_implicit_args ]
      @ import_gospelstdlib stdlib
      @ [
          Rocqtop_require_import
            [
              "Stdlib.Floats.Floats";
              "Stdlib.ZArith.BinIntDef";
              "Stdlib.Strings.Ascii";
            ];
        ]
      @ import_sep_semantics stdlib
      @
      match !backend with
      | Iris -> [ Rocqtop_custom "Local Open Scope Z_scope." ]
      | CFML ->
          [
            Rocqtop_custom "Local Open Scope Z_scope.";
            Rocqtop_custom "Local Open Scope comp_scope.";
          ]
    in
    let abs, specs, specs_typ, obl = ("Abs", "Defs", "D", "Obligations") in
    let acc =
      {
        abstract = [ Rocqtop_end abs ];
        concrete = [];
        obligations = [ Rocqtop_end obl ];
      }
    in
    let defs = List.fold_right combine file.Gospel.fdefs acc in
    let abs_mod =
      Rocqtop_module_type (abs, [], Mod_def_declare) :: defs.abstract
    in
    let abs_arg = "S" in
    let concrete_args = [ ([ abs_arg ], Mod_typ_var abs) ] in
    let abs_imp = Rocqtop_import [ abs_arg ] in
    let concrete_typ =
      Rocqtop_module_type (specs_typ, concrete_args, Mod_def_declare)
      :: abs_imp :: defs.concrete
      @ [ Rocqtop_end specs_typ ]
    in
    let concrete =
      Rocqtop_module (specs, concrete_args, Mod_cast_free, Mod_def_declare)
      :: abs_imp :: defs.concrete
      @ [ Rocqtop_end specs ]
    in
    let conc_arg = "C" in
    let obl_args =
      concrete_args @ [ ([ conc_arg ], Mod_typ_app [ specs_typ; abs_arg ]) ]
    in
    let imp = [ Rocqtop_import [ conc_arg ]; abs_imp ] in
    let obligations =
      (Rocqtop_module_type (obl, obl_args, Mod_def_declare) :: imp)
      @ defs.obligations
    in
    let tops = abs_mod @ concrete_typ @ concrete @ obligations in
    let top =
      if !is_logical then
        Rocqtop_param (tv "set" (rocq_impl_types 1) false) :: tops
      else tops
    in
    imports @ top
end

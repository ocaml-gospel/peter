open Gospel_checker
open Sast
open Id_uast
open Ident
open Tast
open Rocq
module M = Map.Make (String)

let sig_tbl : (string * string list) list IdTable.t = IdTable.create 100
let () = IdTable.add sig_tbl Constants.set_id.id_tag [ ("_set_sig", []) ]

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

(** Helper functions to generate names. *)

let class_name v = "_" ^ v ^ "_sig"
let inst_name v = "_" ^ v ^ "_inst"
let stmt_name v = "_" ^ v ^ "_stmt"
let to_ocaml v = "_" ^ v ^ "_prog"

(** Names for the generated modules. *)

let decl_mod = "Declarations"
let obl_mod = "Obligations"

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

let rocq_keywords = [ "mod"; "Set"; "Alias" ]

let id_mapper = function
  | "-" -> "minus"
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
  | s when List.mem s rocq_keywords -> "_" ^ s
  | s -> unicode_mapper s

let stdlib_sym id =
  match id.id_str with
  | "prop" -> "Prop"
  | "integer" -> "Z"
  | "char" -> "ascii"
  | _ -> id_mapper id.id_str

(** Function definitions that should not be present in any standard library
    implementation. *)
let inline = function
  | "+" | "-" | "*" | "/" | ">" | ">=" | "<" | "<=" | "->" | "||" | "&&" | "="
  | "<>" | "<->" | "not" | "/\\" | "\\/" ->
      true
  | _ -> false

(** This flag notes if we are translating the Gospel standard library. *)
let is_stdlib = ref false

let stdlib_skip nm = !is_stdlib && inline nm.id_str
let is_internal id = !is_stdlib || Ident.is_stdlib id || Ident.is_primitive id

let valid_string id =
  if is_internal id then if inline id.id_str then id.id_str else stdlib_sym id
  else id_mapper id.id_str

let rec qid_to_string = function
  | Qid id -> valid_string id
  | Qdot (q, id) -> qid_to_string q ^ "." ^ valid_string id

let remove_dups l =
  let rec remove_dups visited = function
    | [] -> []
    | x :: t ->
        if List.mem x visited then remove_dups visited t
        else x :: remove_dups (x :: visited) t
  in
  remove_dups [] l

let rec mk_relative absolute_path current_path =
  match (absolute_path, current_path) with
  | [], _ -> ""
  | absolute_path, [] -> String.concat "." absolute_path
  | x :: t1, y :: t2 ->
      if x = y then mk_relative t1 t2 else String.concat "." absolute_path

let mk_insts_path curr_path =
  List.map (fun (x, path) ->
      let rel = mk_relative path curr_path in
      rel ^ (if rel <> "" then "." else "") ^ x)

let update_deps deps q =
  let id = Uast_utils.leaf q in
  match IdTable.find_opt sig_tbl id.id_tag with
  | None -> ()
  | Some s ->
      deps := !deps @ s;
      deps := remove_dups !deps

let rocq_ty deps t =
  let rec rocq_ty = function
    | PTtyapp (v, l) ->
        update_deps deps v.app_qid;
        rocq_apps (rocq_var (qid_to_string v.app_qid)) (List.map rocq_ty l)
    | PTarrow (t1, t2) -> rocq_impl (rocq_ty t1) (rocq_ty t2)
    | PTtyvar tv -> Rocq_var (to_tvar tv)
    | PTtuple l -> rocq_prods (List.map rocq_ty l)
  in
  rocq_ty t

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

let only_uses_named tbl (_, pty) =
  let rec only_uses_named tbl pty =
    match pty with
    | PTtyvar v -> IdTable.mem tbl v.id_tag
    | PTtyapp (_, l) | PTtuple l -> List.for_all (only_uses_named tbl) l
    | PTarrow (t1, t2) -> only_uses_named tbl t1 || only_uses_named tbl t2
  in
  only_uses_named tbl pty

let only_uses_named tbl = List.for_all (only_uses_named tbl)
let is_infix v = match v.id_fixity with Infix -> true | _ -> false

let is_infix_term tbl t =
  match t.t_node with
  | Tvar (Qid v, l) -> is_internal v && inline v.id_str && only_uses_named tbl l
  | _ -> false

let rocq_const c =
  match c with
  | Parse_uast.Pconst_integer (v, None) -> rocq_int (int_of_string v)
  | _ -> assert false

let get_infix t =
  match t.t_node with Tvar (Qid v, _) -> v.id_str | _ -> assert false

let rocq_tv deps vs = tv vs.ts_id.id_str (rocq_ty deps vs.ts_ty)
let rocq_id id = qid_to_string id

let gen_args_pat deps p =
  match p.pat_desc with Pid vs -> rocq_tv deps vs | _ -> assert false

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

let rec rocq_term path deps tvar_tbl t =
  let rocq_term = rocq_term path deps tvar_tbl in
  match t.t_node with
  | Tvar (q, ptys) ->
      update_deps deps q;
      let s = qid_to_string q in
      if only_uses_named tvar_tbl ptys then Rocq_var (rocq_id q)
      else
        let () =
          List.iter (fun (_, pty) -> collect_tvars_pty tvar_tbl pty) ptys
        in
        let l =
          List.map (fun (x, pty) -> rocq_implicit x (rocq_ty deps pty)) ptys
        in
        rocq_apps (Rocq_var s) l
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
      let f = match q with Tforall -> rocq_foralls | Texists -> rocq_exists in
      let () = List.iter (collect_tvars tvar_tbl) ids in
      let ids = List.map (rocq_tv deps) ids in
      f ids (rocq_term t)
  | Tlambda (vl, t, _) ->
      let () = List.iter (collect_tvars_pat tvar_tbl) vl in
      rocq_funs (List.map (gen_args_pat deps) vl) (rocq_term t)
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

module type Sep_to_rocq = sig
  val inhab : var -> var
  val ocaml_tdef : type_decl -> decls
  val import_sl : rocqtops

  val pred_typ :
    string list -> (string * string list) list ref -> Tast.lens_info -> rocq

  val import_stdlib : gospelstdlib:bool -> rocqtops
  val decl_args : (string * string) list
end

module Sep_to_iris : Sep_to_rocq = struct
  let inhab v = "Inhabited " ^ v

  let ocaml_tdef def =
    let tvars = tv_tvars def.type_args in
    {
      declarations =
        [ rocqtop_def false def.type_name.id_str [] [] tvars typ rocq_val ];
      obligations = [];
    }

  let import_stdpp =
    [ Rocqtop_require_import [ "Stdlib.ZArith.BinInt"; "stdpp.base" ] ]

  let import_stdpp_impl =
    [ Rocqtop_require_import [ "Stdlib_stdpp.iris_core" ] ]

  let import_sl =
    [
      Rocqtop_require_import
        [
          "iris.proofmode.proofmode";
          "iris.heap_lang.proofmode";
          "iris.heap_lang.notation";
          "iris.prelude.options";
        ];
    ]

  let pred_typ path deps lens =
    let i_prop = rocq_var "iProp" in
    let model_ty = rocq_ty deps lens.lmodel in
    let ty = rocq_impls [ rocq_ty deps lens.locaml; model_ty ] i_prop in
    let l = mk_insts_path path !deps in
    rocq_insts l ty

  let import_stdlib ~gospelstdlib =
    (if gospelstdlib then import_stdpp else import_stdpp_impl)
    @ [ Rocqtop_custom "Local Open Scope Z_scope" ]

  let decl_args = [ ("Heap", "H") ]
end

module Sep_to_CFML : Sep_to_rocq = struct
  let inhab v = "Inhab " ^ v
  let ocaml_tdef _ = assert false

  let import_tlc =
    [
      Rocqtop_custom "Set Warnings \"-deprecated\"";
      Rocqtop_custom "Set Warnings \"-default\"";
      Rocqtop_custom "Set Warnings \"-syntax\"";
      Rocqtop_require_import [ "TLC.LibCore" ];
    ]

  let import_tlc_impl =
    [
      Rocqtop_require_import
        [
          "Stdlib_tlc.gospelstdlib_verified_tlc";
          "Stdlib_tlc.gospelstdlib_mli_tlc";
        ];
    ]

  let import_sl =
    [
      Rocqtop_require_import
        [
          "CFML.SepBase";
          "CFML.SepLifted";
          "CFML.WPLib";
          "CFML.WPLifted";
          "CFML.WPRecord";
          "CFML.WPArray";
          "CFML.WPBuiltin";
          "CFML.Semantics";
          "CFML.WPHeader";
        ];
    ]

  let pred_typ _ _ _ = assert false

  let import_stdlib ~gospelstdlib =
    (if gospelstdlib then import_tlc else import_tlc_impl)
    @ [ Rocqtop_custom "Local Open Scope comp_scope" ]

  let decl_args = []
end

module type P = sig
  val sep_defs : stdlib:bool -> Sast.definition list Gospel.file -> rocqtop list
end

module Make (M : Sep_to_rocq) : P = struct
  open M

  let empty_decls = { declarations = []; obligations = [] }
  let to_triple s = { s with id_str = s.id_str ^ "_spec" }

  let spec_arg deps = function
    | Sast.Unit -> Some Unit
    | Wildcard -> Some Wildcard
    | Ghost _ -> None
    | Value v ->
        let var =
          tv v.arg_ocaml.ts_id.id_str (rocq_ty deps v.arg_ocaml.ts_ty)
        in
        Some (Var var)

  let spec_args deps = List.filter_map (spec_arg deps)

  let gen_tbl tvars =
    let tbl = IdTable.create 100 in
    let () = List.iter (collect_tvars tbl) tvars in
    tbl

  let triple_val_to_ts = function
    | Sast.Unit | Wildcard -> []
    | Ghost ts -> [ ts ]
    | Value v -> [ v.arg_ocaml; v.arg_model ]

  let sep_term path deps tbl t =
    let rec sep_term = function
      | Logical t -> Rocq_pure (rocq_term path deps tbl t)
      | Lift (sym, arg1, arg2) ->
          let ocaml = rocq_term path deps tbl arg1 in
          let model = rocq_term path deps tbl arg2 in
          let () = update_deps deps (Qid sym.ps_name) in
          Rocq_lift (sym.ps_name.id_str, ocaml, model)
      | Quant (q, vs, t) ->
          let q = match q with Tforall -> Forall | Texists -> Exists in
          let args =
            List.map (fun x -> tv x.ts_id.id_str (rocq_ty deps x.ts_ty)) vs
          in
          let t = List.map sep_term t in
          Rocq_hquant (q, args, t)
      | Wand _ -> assert false
    in
    sep_term t

  let sep_terms path deps tbl = List.map (sep_term path deps tbl)

  let triple_rets deps l =
    match l with [] -> [ Rocq.Unit ] | rets -> spec_args deps rets

  let inhabs l = List.map inhab l

  let gen_spec deps path triple =
    let all_ts = List.concat_map triple_val_to_ts triple.triple_args in
    let tbl = gen_tbl all_ts in
    let poly = tvars triple.triple_poly in
    let args = spec_args deps triple.triple_args in
    let inhabs = inhabs poly in
    let all_vars = List.map (rocq_tv deps) all_ts in
    let pre = sep_terms path deps tbl triple.triple_pre in
    let ex, posts = triple.triple_post in
    let post = sep_terms path deps tbl posts in
    let vars = List.map (rocq_tv deps) ex in
    let post = rocq_hexists vars post in
    let ret_vars = triple_rets deps triple.triple_rets in
    let f = triple.triple_name.id_str in
    let deps = mk_insts_path path !deps in
    let all_vars = List.map inst (deps @ inhabs) @ all_vars in
    rocq_foralls all_vars (rocq_spec f poly pre args ret_vars post)

  let abstract id nm path deps tvars rocq =
    let class_name = class_name nm in
    let inst_name = inst_name nm in
    let underscores = List.fold_left (fun acc _ -> acc ^ " _") "" deps in
    let dep_name = class_name ^ underscores in
    let () = IdTable.add sig_tbl id (deps @ [ (dep_name, path) ]) in
    let tvars = List.map to_tvar tvars in
    let deps = mk_insts_path path deps in
    let c = tclass class_name deps tvars nm rocq in
    let inst = tinst inst_name class_name in
    { declarations = [ c ]; obligations = [ inst ] }

  let abstract_id nm path deps tvars rocq =
    abstract nm.id_tag nm.id_str path deps tvars rocq

  let tdef path tdef =
    if tdef.type_ocaml then ocaml_tdef tdef
    else
      let tname = tdef.type_name.id_str in
      match tdef.type_def with
      | Abstract ->
          let typ = rocq_forall_types tdef.type_args in
          abstract_id tdef.type_name path [] [] typ
      | Alias t ->
          let deps = ref [] in
          let t = rocq_ty deps t in
          let tvars = tv_tvars tdef.type_args in
          let () = IdTable.add sig_tbl tdef.type_name.id_tag !deps in
          let deps = mk_insts_path path !deps in
          let def = rocqtop_def false tname [] deps tvars typ t in
          { empty_decls with declarations = [ def ] }
      | Record r ->
          let tvars = tv_tvars tdef.type_args in
          let deps = ref [] in
          let branches =
            List.map (fun (s, t) -> tv s.Ident.id_str (rocq_ty deps t)) r
          in
          let def =
            Rocqtop_record
              {
                rocqind_name = tname;
                rocqind_constructor_name = "_mk_" ^ tname;
                rocqind_targs = tvars;
                rocqind_ret = typ;
                rocqind_branches = branches;
              }
          in
          { empty_decls with declarations = [ def ] }

  let combine defs acc =
    {
      declarations = defs.declarations @ acc.declarations;
      obligations = defs.obligations @ acc.obligations;
    }

  let rec sep_def path d =
    match d.d_node with
    | Type t -> tdef path t
    | Pred pred ->
        let deps = ref [] in
        let typ = pred_typ path deps pred in
        let nm = pred.lid in
        abstract_id nm path !deps pred.lvars typ
    | Triple triple ->
        let deps = ref [] in
        let fun_triple = gen_spec deps path triple in
        let triple_name = to_triple triple.triple_name in
        deps := (class_name triple.triple_name.id_str, []) :: !deps;
        abstract_id triple_name path !deps triple.triple_poly fun_triple
    | Val v ->
        let deps = ref [] in
        abstract_id v.vname path !deps [] rocq_val
    | Function f -> (
        if stdlib_skip f.fun_name then empty_decls
        else
          let name = id_mapper f.fun_name.id_str in
          let args = f.fun_params in
          let ret = f.fun_ret in
          let tvars = tvars f.fun_tvars in
          let deps = ref [] in
          let ret_rocq = rocq_ty deps ret in
          let args_rocq = List.map (rocq_tv deps) args in
          let tbl = gen_tbl args in
          let def = Option.map (rocq_term path deps tbl) f.fun_def in
          match def with
          | Some d ->
              let insts = mk_insts_path path !deps in
              let def =
                rocqtop_def f.fun_rec name tvars insts args_rocq ret_rocq d
              in
              { empty_decls with declarations = [ def ] }
          | None ->
              let typ =
                List.fold_right
                  (fun x acc -> rocq_impl x.var_type acc)
                  args_rocq ret_rocq
              in
              let typ = rocq_insts (inhabs tvars) typ in
              abstract f.fun_name.id_tag name path !deps f.fun_tvars typ)
    | Axiom a ->
        let tbl = gen_tbl [] in
        let deps = ref [] in
        let t =
          match a.sax_term with
          | [ Logical t ] -> rocq_term path deps tbl t
          | _ -> assert false
        in
        let t = rocq_insts (inhabs (tvars a.sax_tvars)) t in
        abstract_id a.sax_name path !deps a.sax_tvars t
    | Module (nm, l) ->
        let nm_var = id_mapper nm.id_str in
        let statements = sep_defs (nm_var :: path) l in

        let import = import [ decl_mod ^ "." ^ nm_var ] in
        let declarations = [ rocq_module nm_var [] statements.declarations ] in
        let obligations =
          [ rocq_module nm_var [] (import :: statements.obligations) ]
        in
        { declarations; obligations }
    | Import l ->
        let l = [ Rocqtop_import [ qid_to_string l ] ] in
        { declarations = l; obligations = l }

  and sep_defs path l =
    match l with
    | [] -> empty_decls
    | x :: t ->
        let s = sep_def path x in
        let l = sep_defs path t in
        combine s l

  let import_gospelstdlib stdlib =
    import_stdlib ~gospelstdlib:stdlib
    @ if stdlib then [] else [ Rocqtop_import [ "Proofs"; "Declarations" ] ]

  let import_sep_semantics stdlib = if stdlib then [] else import_sl

  let sep_defs ~stdlib file =
    let () = is_stdlib := stdlib in
    let imports =
      import_gospelstdlib stdlib
      @ [
          Rocqtop_require_import
            [
              "Stdlib.Floats.Floats";
              "Stdlib.ZArith.BinIntDef";
              "Stdlib.Strings.Ascii";
            ];
        ]
      @ import_sep_semantics stdlib
    in
    let defs = sep_defs [] file.Gospel.fdefs in
    let extra_decl, extra_obl =
      if stdlib then
        let set_decl =
          tclass "_set_sig" [] [] "set" (rocq_forall_types [ Ident.mk_id "A" ])
        in
        let set_obl = tinst "_set_inst" "_set_sig" in
        ([ set_decl ], [ set_obl ])
      else
        let open Gospel_checker.Utils.Fmt in
        let mod_nms = List.map fst M.decl_args in
        let extra_obl =
          if M.decl_args = [] then []
          else
            [
              Rocqtop_custom
                (Format.asprintf "Module %s := %s%a" decl_mod decl_mod
                   (list ~sep:sp ~first:sp string)
                   mod_nms);
            ]
        in
        let extra_decl = [ import mod_nms ] in
        (extra_decl, extra_obl)
    in

    let decl_args = List.map (fun (v, t) -> tv v (Rocq_var t)) M.decl_args in
    let decls =
      rocq_module decl_mod decl_args (extra_decl @ defs.declarations)
    in
    let obls =
      mod_type obl_mod decl_args
        ((extra_obl @ [ Rocqtop_import [ decl_mod ] ]) @ defs.obligations)
    in
    let tops = [ decls; obls ] in
    imports @ tops
end

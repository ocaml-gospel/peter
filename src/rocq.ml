let list_make n v = List.init n (fun _ -> v)

(** This file contains facilities for representing Coq expressions. Most of the
    core language is supported. A subset of the top-level declarations are
    supported. *)

(*#########################################################################*)
(* ** Syntax of Rocq expressions *)

(** Rocq variables and paths *)

type quant = Exists | Forall
type var = string
type vars = var list
type spec_var = Var of var | Wildcard | Unit
type rocq_path = Rocqp_var of var | Rocqp_dot of rocq_path * string

type typed_var = { var_name : var; var_type : rocq }
and typed_vars = typed_var list

(** Rocq expressions *)

and rocq =
  | OCaml_type
  | Gospel_type
  | Rocq_var of var
  | Rocq_int of int
  | Rocq_string of string
  | Rocq_app of rocq * rocq
  | Rocq_lettuple of rocqs * rocq * rocq
  | Rocq_quant of quant * typed_var list * rocq
  | Rocq_fun of typed_var * rocq
  | Rocq_set of var * rocq
  | Rocq_infix of rocq * var * rocq
  | Rocq_tuple of rocqs
  | Rocq_record of (var * rocq) list
  | Rocq_proj of var * rocq
  | Rocq_if of rocq * rocq * rocq
  | Rocq_match of rocq * (rocq * rocq) list

and rocqs = rocq list

type rocq_sep =
  | Rocq_pure of rocq
  | Rocq_hempty
  | Rocq_lift of var * rocq * rocq
  | Rocq_hquant of quant * typed_vars * rocq_seps

and rocq_seps = rocq_sep list

let tv var_name var_type = { var_name; var_type }

(** Toplevel declarations *)

type instance = { inst_nm : var; inst_class : var }

type definition = {
  def_rec : bool;
  def_nm : var;
  def_tvars : var list;
  def_insts : rocq list;
  def_args : typed_var list;
  def_return : rocq;
  def_body : rocq;
}

type param = { param_nm : var; param_ret : rocq }

type spec = {
  spec_nm : var;
  spec_forall : typed_vars;
  spec_pre : rocq_seps;
  spec_args : spec_var list;
  spec_ret : spec_var list;
  spec_post : rocq_seps;
}

let rocq_spec spec_nm spec_forall spec_pre spec_args spec_ret spec_post =
  { spec_nm; spec_forall; spec_pre; spec_args; spec_ret; spec_post }

type kind = Obligation | Statement
type tclass = { cname : var; cproj : var; crocq : rocq }

type rocqtop =
  | Rocqtop_def of definition
  | Rocqtop_param of param
  | Rocqtop_axiom of param
  | Rocqtop_instance of instance
  | Rocqtop_record of rocqind
  | Rocqtop_import of vars
  | Rocqtop_class of tclass
  | Rocqtop_require_import of vars
  | Rocqtop_module of var * rocqtop list
  | Rocqtop_module_type of var * var * rocqtop list
  | Rocqtop_module_type_include of var
  | Rocqtop_custom of string
  | Rocqtop_section of var
  | Rocqtop_context of typed_vars
  | Rocqtop_htop of kind * htop

and rocqind = {
  rocqind_name : var;
  rocqind_constructor_name : var;
  rocqind_targs : typed_vars;
  rocqind_ret : rocq;
  rocqind_branches : typed_vars;
}

and rocqtops = rocqtop list

and htop =
  | Rocqtop_spec of spec
  | Rocqtop_hpred of spec
  | Rocqtop_encoder of var * rocq

let tclass cname cproj crocq = Rocqtop_class { cname; cproj; crocq }
let tinst inst_nm inst_class = Rocqtop_instance { inst_nm; inst_class }

(** Inductive definitions *)

(*#########################################################################*)
(* ** Smart constructors for toplevel definitions *)

let rocqtop_def def_rec def_nm def_tvars def_insts def_args def_return def_body
    =
  Rocqtop_def
    { def_rec; def_nm; def_tvars; def_insts; def_args; def_return; def_body }

let rocqtop_param param_nm param_ret = Rocqtop_param { param_nm; param_ret }
let instance inst_nm inst_class = Rocqtop_instance { inst_nm; inst_class }

(*#########################################################################*)
(* ** Smart constructors for variables *)

(** Identifier [x] *)

let rocq_wild = Rocq_var "_"
let rocq_var x = Rocq_var x

(** List of identifiers [x1 x2 .. xn] *)

let rocq_vars xs = List.map rocq_var xs

(** Identifier [@x] *)

let rocq_var_at x = rocq_var ("@" ^ x)

(** Identifier [@c], where [c] is a [Rocq_var] *)

let rocq_at c =
  match c with
  | Rocq_var x -> Rocq_var ("@" ^ x)
  | _ -> failwith "rocq_at applied to a non-variable"

(*#########################################################################*)
(* ** Smart constructors for applications *)

(** Application [c1 c2] *)

let rocq_app c1 c2 = Rocq_app (c1, c2)

(** Application [c c1 c2 ... cn] *)

let rocq_apps c args = List.fold_left rocq_app c args

(** Application [c0 c1 c2] *)

let rocq_app_2 c0 c1 c2 = rocq_apps c0 [ c1; c2 ]
let rocq_infix c1 op c2 = Rocq_infix (c1, op, c2)

(** Application [x c] *)

let rocq_app_var x c = rocq_app (rocq_var x) c

(** Application [x c1 c2 .. cn] *)

let rocq_apps_var x args = rocq_apps (rocq_var x) args

(** Application [@x c1 c2 .. cn] *)

let rocq_apps_var_at x args = rocq_apps (rocq_var_at x) args

(** Application [x x1 x2 .. xn] *)

let rocq_apps_vars x xs = rocq_apps (rocq_var x) (rocq_vars xs)

(** Applications of an at-identifier to arguments [@x c1 .. cn] *)

let rocq_app_var_at x args =
  if args = [] then Rocq_var x else rocq_apps (rocq_var_at x) args

(*#########################################################################*)
(* ** Smart constructors for base types *)

let typ_prop = Rocq_var "Prop"
let ocaml_type = OCaml_type
let gospel_type = Gospel_type
let typ ~ocaml = if ocaml then ocaml_type else gospel_type
let typ_unit = Rocq_var "unit"
let typ_bool = Rocq_var "bool"
let typ_int = Rocq_var "Z"
let typ_nat = Rocq_var "nat"
let rocq_set v p = Rocq_set (v, p)
(*#########################################################################*)
(* ** Helper functions *)

(** List of types [(A1:Type)::(A2::Type)::...::(AN:Type)::nil] *)

let to_tvar v = String.capitalize_ascii v.Gospel_checker.Ident.id_str

let rocq_types ~ocaml names =
  List.map (fun v -> tv (to_tvar v) (typ ~ocaml)) names

(*#########################################################################*)
(* ** Smart constructors for structure *)

(** Function [fun (x:t) => c] where [arg] is the pair [(x,t)] *)

(** Function [fun (x1:T1) .. (xn:Tn) => c] *)
let rocq_fun arg c = Rocq_fun (arg, c)

(** Recursive function [fix f (x1:T1) .. (xn:Tn) : Tr => c] represented as
    [Rocq_fix f n Tr body] where [body] is the representation of
    [fun (x1:T1) .. (xn:Tn) => c]. *)
let rocq_funs args c = List.fold_right rocq_fun args c

(* Matching [match v with p1 => c1 | .. | pn => cn *)

let rocq_match carg branches = Rocq_match (carg, branches)

(** Function [fun (x1:Type) .. (xn:Type) => c] *)

let rocq_fun_types ocaml names c = rocq_funs (rocq_types ~ocaml names) c

(** Conditionals *)

let rocq_if_bool c0 c1 c2 = Rocq_if (c0, c1, c2)
let rocq_if_prop c0 c1 c2 = Rocq_if (Rocq_app (Rocq_var "classicT", c0), c1, c2)
(* TODO: set the path to TLC? *)

(** Let binding [let (x:T) := t1 in t2] TODO let rocq_foralls args c =
    List.fold_right (fun ci acc -> Rocq_forall (ci, acc)) args c *)

(*#########################################################################*)
(* ** Smart constructors for quantifiers *)

(** Existential [exists (x1:T1) .. (xn:Tn), c] *)

let rocq_exists args c =
  match args with [] -> c | _ -> Rocq_quant (Exists, args, c)

(** Universal [forall (x1:T1) .. (xn:Tn), c] *)

let rocq_foralls args c =
  match args with [] -> c | _ -> Rocq_quant (Forall, args, c)

(** Universal [forall (x1:Type) .. (xn:Type), c] *)

let rocq_hexists l s =
  match l with [] -> s | _ -> [ Rocq_hquant (Exists, l, s) ]

let rocq_forall_types ~ocaml names =
  rocq_foralls (rocq_types ~ocaml names) (typ ~ocaml)

(** Implication [c1 -> c2] *)

let rocq_impl c1 c2 = Rocq_infix (c1, "->", c2)

(** Implication [c1 -> c2 -> .. -> cn -> c] *)

let rocq_impls cs c = List.fold_right (fun ci acc -> rocq_impl ci acc) cs c

(** Predicate type [A->Prop] *)

let rocq_pred c = rocq_impl c typ_prop

(** N-ary predicate [c1 -> c2 -> .. -> cn -> Prop] *)

let rocq_preds cs = rocq_impls cs typ_prop

(*#########################################################################*)
(* ** Smart constructors for compound types *)

(** Product type [(c1 * c2)%type] *)

let rocq_prod c1 c2 =
  rocq_apps (Rocq_var "Corelib.Init.Datatypes.prod") [ c1; c2 ]

(** Product type [(c1 * c2 * .. * cN)%type], or [unit] if the list is empty *)

let rocq_prods cs =
  match cs with
  | [] -> typ_unit
  | [ c ] -> c
  | c0 :: cs' -> List.fold_left (fun acc c -> rocq_prod acc c) c0 cs'

let rocq_typ_tuple = rocq_prods

(** Implication [Type -> Type -> .. -> Type] *)

let rocq_impl_types ~ocaml n =
  rocq_impls (list_make n (typ ~ocaml)) (typ ~ocaml)

(*#########################################################################*)
(* ** Smart constructors for constants *)

let rocq_prop_false = Rocq_var "False"
let rocq_prop_true = Rocq_var "True"
let tt_tv = tv "tt" typ_unit
let tt = rocq_var "tt"
let rocq_bool_false = Rocq_var "false"
let rocq_bool_true = Rocq_var "true"
let rocq_int n = Rocq_int n
let rocq_string s = Rocq_string s

(** List [c1 :: c2 :: .. :: cN :: nil], with constructors optionally annotated
    with a type *)

let rocq_nil ?(typ : rocq option) () =
  let f = "Rocq.Lists.List.nil" in
  (* TODO: factorize this code pattern with "rocq_none", etc. *)
  match typ with
  | None -> rocq_apps_var f []
  | Some t -> rocq_apps_var_at f [ t ]

let rocq_cons ?(typ : rocq option) c1 c2 =
  let f = "Rocq.Lists.List.cons" in
  (* TODO: factorize this code pattern with "rocq_none", etc. *)
  match typ with
  | None -> rocq_apps_var f [ c1; c2 ]
  | Some t -> rocq_apps_var_at f [ t; c1; c2 ]

let rocq_list ?(typ : rocq option) cs =
  let cnil = rocq_nil ?typ () in
  let ccons = rocq_cons ?typ in
  List.fold_right ccons cs cnil

(** Pair [(c1,c2)], with optional type arguments *)

let rocq_pair ?(typ : (rocq * rocq) option) c1 c2 =
  let f = "Rocq.Init.Datatypes.pair" in
  match typ with
  | None -> rocq_apps_var f [ c1; c2 ]
  | Some (t1, t2) -> rocq_apps_var_at f [ t1; t2; c1; c2 ]

(** Tuple [(c1,c2,..,cn)], with optional type arguments; tt if the list empty;
    c1 if the list is singleton *)

let rocq_tuple cs = Rocq_tuple cs

(** Record [{ f1 := c1; ...; fn := cn }] *)

let rocq_record (fcs : (var * rocq) list) = Rocq_record fcs

(** Record projection [c.f], actually printed as [(f c)] in print_rocq ---the
    two are equivalent. *)

let rocq_record_proj (c : rocq) (field : var) = Rocq_proj (field, c)

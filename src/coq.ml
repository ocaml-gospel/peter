let list_make n v = List.init n (fun _ -> v)

(** This file contains facilities for representing Coq expressions. Most of the
    core language is supported. A subset of the top-level declarations are
    supported. *)

(*#########################################################################*)
(* ** Syntax of Coq expressions *)

(** Coq variables and paths *)

type quant = Exists | Forall | Hexists | Hforall
type var = string
type vars = var list
type spec_var = Var of var | Wildcard | Unit
type coq_path = Coqp_var of var | Coqp_dot of coq_path * string

type typed_var = { var_name : var; var_type : coq }
and typed_vars = typed_var list

(** Coq expressions *)

and coq =
  | Coq_var of var
  | Coq_int of int
  | Coq_string of string
  | Coq_app of coq * coq
  | Coq_impl of coq * coq
  | Coq_lettuple of coqs * coq * coq
  | Coq_quant of quant * typed_var list * coq
  | Coq_fun of typed_var * coq
  | Coq_set of var * coq
  | Coq_infix of coq * var * coq
  | Coq_tuple of coqs
  | Coq_record of (var * coq) list
  | Coq_proj of var * coq
  | Coq_if of coq * coq * coq
  | Coq_match of coq * (coq * coq) list
  | Coq_sep of sep

and coqs = coq list

and sep =
  | Coq_pure of coq
  | Coq_hempty
  | Coq_spec of var * typed_vars * coq * spec_var list * coq

let tv var_name var_type = { var_name; var_type }

(** Toplevel declarations *)

type instance = { inst_nm : var; inst_typ : coq }

type definition = {
  def_rec : bool;
  def_nm : var;
  def_tvars : var list;
  def_insts : coq list;
  def_args : typed_var list;
  def_return : coq;
  def_body : coq;
}

type param = { param_nm : var; param_vars : typed_var list; param_ret : coq }

type coqtop =
  | Coqtop_def of definition
    (* Coqtop_fundef(isrecursive, [(fun_name,typed_args,ret_type,body)])
       the list has more than one item for a mutually-recursive definition *)
  | Coqtop_param of param
  | Coqtop_axiom of param
  | Coqtop_instance of instance
  | Coqtop_record of coqind
  | Coqtop_import of vars
  | Coqtop_require_import of vars
  | Coqtop_module of var * coqtop list
  | Coqtop_module_type of var * var * coqtop list
  | Coqtop_module_type_include of var
  | Coqtop_end of var
  | Coqtop_custom of string
  | Coqtop_section of var
  | Coqtop_context of typed_vars
  | Coqtop_encoder of var * coq

and coqtops = coqtop list

(** Inductive definitions *)

and coqind = {
  coqind_name : var;
  coqind_constructor_name : var;
  coqind_targs : typed_vars;
  coqind_ret : coq;
  coqind_branches : typed_vars;
}

(*#########################################################################*)
(* ** Smart constructors for toplevel definitions *)

let coqtop_def def_rec def_nm def_tvars def_insts def_args def_return def_body =
  Coqtop_def
    { def_rec; def_nm; def_tvars; def_insts; def_args; def_return; def_body }

let coqtop_param param_nm param_vars param_ret =
  Coqtop_param { param_nm; param_vars; param_ret }

let instance inst_nm inst_typ = Coqtop_instance { inst_nm; inst_typ }

(*#########################################################################*)
(* ** Smart constructors for variables *)

(** Identifier [x] *)

let coq_wild = Coq_var "_"
let coq_var x = Coq_var x

(** List of identifiers [x1 x2 .. xn] *)

let coq_vars xs = List.map coq_var xs

(** Identifier [@x] *)

let coq_var_at x = coq_var ("@" ^ x)

(** Identifier [@c], where [c] is a [Coq_var] *)

let coq_at c =
  match c with
  | Coq_var x -> Coq_var ("@" ^ x)
  | _ -> failwith "coq_at applied to a non-variable"

(*#########################################################################*)
(* ** Smart constructors for applications *)

(** Application [c1 c2] *)

let coq_app c1 c2 = Coq_app (c1, c2)

(** Application [c c1 c2 ... cn] *)

let coq_apps c args = List.fold_left coq_app c args

(** Application [c0 c1 c2] *)

let coq_app_2 c0 c1 c2 = coq_apps c0 [ c1; c2 ]
let coq_infix c1 op c2 = Coq_infix (c1, op, c2)

(** Application [x c] *)

let coq_app_var x c = coq_app (coq_var x) c

(** Application [x c1 c2 .. cn] *)

let coq_apps_var x args = coq_apps (coq_var x) args

(** Application [@x c1 c2 .. cn] *)

let coq_apps_var_at x args = coq_apps (coq_var_at x) args

(** Application [x x1 x2 .. xn] *)

let coq_apps_vars x xs = coq_apps (coq_var x) (coq_vars xs)

(** Applications of an at-identifier to arguments [@x c1 .. cn] *)

let coq_app_var_at x args =
  if args = [] then Coq_var x else coq_apps (coq_var_at x) args

(*#########################################################################*)
(* ** Smart constructors for base types *)

let typ_prop = Coq_var "Prop"
let typ_type = Coq_var "Type"
let typ_unit = Coq_var "unit"
let typ_bool = Coq_var "bool"
let typ_int = Coq_var "Z"
let typ_nat = Coq_var "nat"
let coq_set v p = Coq_set (v, p)
(*#########################################################################*)
(* ** Helper functions *)

(** List of types [(A1:Type)::(A2::Type)::...::(AN:Type)::nil] *)

let coq_types names = List.map (fun n -> tv n typ_type) names

(*#########################################################################*)
(* ** Smart constructors for structure *)

(** Function [fun (x:t) => c] where [arg] is the pair [(x,t)] *)

(** Function [fun (x1:T1) .. (xn:Tn) => c] *)
let coq_fun arg c = Coq_fun (arg, c)

(** Recursive function [fix f (x1:T1) .. (xn:Tn) : Tr => c] represented as
    [Coq_fix f n Tr body] where [body] is the representation of
    [fun (x1:T1) .. (xn:Tn) => c]. *)
let coq_funs args c = List.fold_right coq_fun args c

(* Matching [match v with p1 => c1 | .. | pn => cn *)

let coq_match carg branches = Coq_match (carg, branches)

(** Function [fun (x1:Type) .. (xn:Type) => c] *)

let coq_fun_types names c = coq_funs (coq_types names) c

(** Conditionals *)

let coq_if_bool c0 c1 c2 = Coq_if (c0, c1, c2)
let coq_if_prop c0 c1 c2 = Coq_if (Coq_app (Coq_var "classicT", c0), c1, c2)
(* TODO: set the path to TLC? *)

(** Let binding [let (x:T) := t1 in t2] TODO let coq_foralls args c =
    List.fold_right (fun ci acc -> Coq_forall (ci, acc)) args c *)

(*#########################################################################*)
(* ** Smart constructors for quantifiers *)

(** Existential [exists (x1:T1) .. (xn:Tn), c] *)

let coq_exists xcs c2 = Coq_quant (Exists, xcs, c2)

(** Universal [forall (x1:T1) .. (xn:Tn), c] *)

let coq_foralls args c = Coq_quant (Forall, args, c)

(** Universal [forall (x1:Type) .. (xn:Type), c] *)

let coq_forall_types names c = coq_foralls (coq_types names) c

(** Implication [c1 -> c2] *)

let coq_impl c1 c2 = Coq_impl (c1, c2)

(** Implication [c1 -> c2 -> .. -> cn -> c] *)

let coq_impls cs c = List.fold_right (fun ci acc -> Coq_impl (ci, acc)) cs c

(** Predicate type [A->Prop] *)

let coq_pred c = coq_impl c typ_prop

(** N-ary predicate [c1 -> c2 -> .. -> cn -> Prop] *)

let coq_preds cs = coq_impls cs typ_prop
let coq_spec f tv pre rets post = Coq_sep (Coq_spec (f, tv, pre, rets, post))

(*#########################################################################*)
(* ** Smart constructors for compound types *)

(** Product type [(c1 * c2)%type] *)

let coq_prod c1 c2 = coq_apps (Coq_var "Corelib.Init.Datatypes.prod") [ c1; c2 ]

(** Product type [(c1 * c2 * .. * cN)%type], or [unit] if the list is empty *)

let coq_prods cs =
  match cs with
  | [] -> typ_unit
  | [ c ] -> c
  | c0 :: cs' -> List.fold_left (fun acc c -> coq_prod acc c) c0 cs'

let coq_typ_tuple = coq_prods

(** Implication [Type -> Type -> .. -> Type] *)

let coq_impl_types n = coq_impls (list_make n typ_type) typ_type

(*#########################################################################*)
(* ** Smart constructors for constants *)

let coq_prop_false = Coq_var "False"
let coq_prop_true = Coq_var "True"
let tt_tv = tv "tt" typ_unit
let tt = coq_var "tt"
let coq_bool_false = Coq_var "false"
let coq_bool_true = Coq_var "true"
let coq_int n = Coq_int n
let coq_string s = Coq_string s

(** List [c1 :: c2 :: .. :: cN :: nil], with constructors optionally annotated
    with a type *)

let coq_nil ?(typ : coq option) () =
  let f = "Coq.Lists.List.nil" in
  (* TODO: factorize this code pattern with "coq_none", etc. *)
  match typ with
  | None -> coq_apps_var f []
  | Some t -> coq_apps_var_at f [ t ]

let coq_cons ?(typ : coq option) c1 c2 =
  let f = "Coq.Lists.List.cons" in
  (* TODO: factorize this code pattern with "coq_none", etc. *)
  match typ with
  | None -> coq_apps_var f [ c1; c2 ]
  | Some t -> coq_apps_var_at f [ t; c1; c2 ]

let coq_list ?(typ : coq option) cs =
  let cnil = coq_nil ?typ () in
  let ccons = coq_cons ?typ in
  List.fold_right ccons cs cnil

(** Pair [(c1,c2)], with optional type arguments *)

let coq_pair ?(typ : (coq * coq) option) c1 c2 =
  let f = "Coq.Init.Datatypes.pair" in
  match typ with
  | None -> coq_apps_var f [ c1; c2 ]
  | Some (t1, t2) -> coq_apps_var_at f [ t1; t2; c1; c2 ]

(** Tuple [(c1,c2,..,cn)], with optional type arguments; tt if the list empty;
    c1 if the list is singleton *)

let coq_tuple cs = Coq_tuple cs

(** Record [{ f1 := c1; ...; fn := cn }] *)

let coq_record (fcs : (var * coq) list) = Coq_record fcs

(** Record projection [c.f], actually printed as [(f c)] in print_coq ---the two
    are equivalent. *)

let coq_record_proj (c : coq) (field : var) = Coq_proj (field, c)

(** Option constructors *)

let coq_none ?(typ : coq option) () =
  let f = "Coq.Init.Datatypes.None" in
  match typ with None -> coq_apps_var f [] | Some t -> coq_apps_var_at f [ t ]

let coq_some ?(typ : coq option) c =
  let f = "Coq.Init.Datatypes.Some" in
  match typ with
  | None -> coq_apps_var f [ c ]
  | Some t -> coq_apps_var_at f [ t; c ]

let coq_option ?(typ : coq option) copt =
  match copt with None -> coq_none ?typ () | Some c -> coq_some ?typ c

(*#########################################################################*)
(* ** Smart constructors for logical operators *)

let coq_not =
  (* propositional negation *)
  coq_var "Coq.Init.Logic.not"

let coq_eq = coq_var "Coq.Init.Logic.eq"
let coq_app_eq c1 c2 = coq_app_2 coq_eq c1 c2
let coq_app_neq c1 c2 = coq_app coq_not (coq_app_eq c1 c2)
let coq_disj = coq_var "Coq.Init.Logic.or"
let coq_app_disj c1 c2 = coq_app_2 coq_disj c1 c2

(* Iterated disjunction [c1 \/ c2 \/ .. \/ cn] or [False] if empty list of args *)

let coq_app_disjs cs =
  match List.rev cs with
  | [] -> coq_prop_false
  | c :: cs -> List.fold_left (fun acc ci -> coq_app_disj ci acc) c cs

let coq_conj = coq_var "Coq.Init.Logic.and"
let coq_app_conj c1 c2 = coq_app_2 coq_conj c1 c2

(* Iterated conjunction [c1 /\ c2 /\ .. /\ cn] or [True] if empty list of args *)

let coq_app_conjs cs =
  match List.rev cs with
  | [] -> coq_prop_true
  | c :: cs -> List.fold_left (fun acc ci -> coq_app_conj ci acc) c cs

let coq_neg =
  (* boolean negation *)
  coq_var "TLC.LibBool.neg"

let coq_app_neg c = coq_app coq_neg c

(*#########################################################################*)
(* ** Smart constructors for arithmetic operations *)

(* Nat operators *)

let coq_nat_succ = coq_var "Coq.Init.Datatypes.S"
let coq_nat_add = coq_var "Coq.Init.Nat.add"
let coq_nat_sub = coq_var "Coq.Init.Nat.sub"
let coq_nat_lt = coq_var "Coq.Init.Peano.lt"
let coq_nat_le = coq_var "Coq.Init.Peano.le"
let coq_nat_gt = coq_var "Coq.Init.Peano.gt"
let coq_nat_ge = coq_var "Coq.Init.Peano.ge"

(* Z operators *)

let coq_le c1 c2 = coq_apps (Coq_var "TLC.LibOrder.le") [ c1; c2 ]
let coq_ge c1 c2 = coq_apps (Coq_var "TLC.LibOrder.ge") [ c1; c2 ]
let coq_lt c1 c2 = coq_apps (Coq_var "TLC.LibOrder.lt") [ c1; c2 ]
let coq_gt c1 c2 = coq_apps (Coq_var "TLC.LibOrder.gt") [ c1; c2 ]
let coq_plus c1 c2 = coq_apps (Coq_var "Coq.ZArith.BinInt.Zplus") [ c1; c2 ]
let coq_minus c1 c2 = coq_apps (Coq_var "Coq.ZArith.BinInt.Zminus") [ c1; c2 ]

(*#########################################################################*)
(* ** Smart constructors for the [Semantics] file *)
(* TODO: move to some other file? *)

let pat_type = "pat"
let trm_type = "trm"
let val_type = "val"
let val_constr = "val_constr"

(*#########################################################################*)
(* ** Inversion functions *)
(* TODO: where is it used? *)

let rec coq_apps_inv c =
  (* LATER could reimplement using an accumulator *)
  match c with
  | Coq_app (c1, c2) ->
      let c0, cs = coq_apps_inv c1 in
      (c0, cs @ [ c2 ])
  | _ -> (c, [])

let rec coq_funs_inv c =
  (* LATER could reimplement using an accumulator *)
  match c with
  | Coq_fun (arg1, c2) ->
      let args, body = coq_funs_inv c2 in
      (arg1 :: args, body)
  | _ -> ([], c)

(*#########################################################################*)
(* ** Representation of labels (notation of the form "'x" := `1`0`1`0) *)
(* TODO: DEPRECATED? *)
(** --

    type label = string

    let var_bits_of_int n = let rec repr n = if n < 2 then [] else (1+(n mod
    2))::(repr (n/2)) in List.rev (0::(repr n))

    let string_of_var_bits vb = show_listp (fun b -> string_of_int b) "`" vb

    let value_variable n = string_of_var_bits (var_bits_of_int n)

    let coq_tag (tag : string) ?args ?label (term : coq) = let args = match args
    with | None -> [] | Some args -> args in Coq_tag ("CFML.CFPrint." ^ tag,
    args, label, term) (* TODO DEPRECATED *) *)

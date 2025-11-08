open PPrint
open Rocq

type backend = Iris | CFML

let backend = ref CFML

(* These functions could move to [PPrint]. *)

let sprintf format = Printf.ksprintf arbitrary_string format

let run (print : Buffer.t -> 'a -> unit) (x : 'a) : string =
  let b = Buffer.create 1024 in
  print b x;
  Buffer.contents b

(* -------------------------------------------------------------------------- *)

(* Global parameters. *)

let indentation = 2
let width = ref 80

(* -------------------------------------------------------------------------- *)

(* Various fixed elements. *)

let arrow = string "->"
let doublearrow = string "=>"
let colonequals = string ":="
let spacecolon = string " :"
let spacecolonequals = string ":="
let hardline2 = hardline ^^ hardline

(* -------------------------------------------------------------------------- *)

(* Applications. *)

let app d1 d2 =
  (* The following definition would reject a large argument on a line of
     its own, indented: *)
  (* group (d1 ^^ nest indentation (break 1 ^^ d2)) *)
  (* However, that would be redundant with the fact that large arguments
     are usually parenthesized, and we already break lines and indent
     within the parentheses. So, the following suffices: *)
  group (d1 ^^ space ^^ d2)

let apps ds =
  match ds with [] -> assert false | d :: ds -> List.fold_left app d ds

(* -------------------------------------------------------------------------- *)

(* A block with indentation. *)

let block n opening contents closing =
  group (opening ^^ nest n contents ^^ closing)

let block = block indentation

(* -------------------------------------------------------------------------- *)

(* Parentheses with indentation. *)

(* We allow breaking a parenthesized thing into several lines by leaving the
   opening and closing parentheses alone on a line and indenting the content. *)

let parens d = block lparen (break 0 ^^ d) (break 0 ^^ rparen)

(* Braces with spacing and indentation. *)

let braces d = block lbrace (break 1 ^^ d) (break 1 ^^ rbrace)

(* Coq-record braces {| ... |} with spacing and indentation. *)

let record_braces d = block (string "{|") (break 1 ^^ d) (break 1 ^^ string "|}")

(* Brackets with spacing and indentation. *)

let brackets d = block lbracket (break 1 ^^ d) (break 1 ^^ rbracket)
let corners d = block (string "⌜") (break 1 ^^ d) (break 1 ^^ string "⌝")

(* -------------------------------------------------------------------------- *)

(* Field assignement : [f := t]. *)

(* Raw. *)

let field (x, t) = block (x ^^ spacecolonequals) (space ^^ t) empty

(* A list of field value declarations, separated with semicolons. *)

let fields_value fts = separate_map (semi ^^ break 1) field fts

(* Record definition : {| f1 := t1; ... |} *)

let record_value fts = record_braces (fields_value fts)

(* -------------------------------------------------------------------------- *)

(* Tuples. *)

let tuple expr es = parens (separate_map (comma ^^ break 1) expr es)

(* -------------------------------------------------------------------------- *)

(* FOR FUTURE USE
      Labels (part of [Coq_tag]).

   let label = function
     | None ->
         string "_"
     | Some l ->
         parens (
           string "Label_create" ^/^ squote ^^ string l
         )
*)

(* -------------------------------------------------------------------------- *)

(* Bindings, or annotations: [x : t]. *)

let binding x t = block (x ^^ spacecolon) (space ^^ t) empty

(* -------------------------------------------------------------------------- *)

(* Expressions. *)

let rec expr0 = function
  | OCaml_type | Gospel_type -> string "Type"
  | Rocq_var s -> string s
  | Rocq_int n -> string (string_of_int n)
  | Rocq_string s -> dquotes (string s)
  | Rocq_tuple es -> tuple expr es
  | Rocq_set (v, t) -> (
      match !backend with
      | Iris ->
          lbrace ^^ space ^^ string v ^^ space ^^ bar ^^ space ^^ expr1 t
          ^^ rbrace
      | CFML -> parens (string "fun " ^^ string v ^^ string "=>" ^^ expr0 t))
  | Rocq_record fes ->
      record_value (List.map (fun (f, e) -> (string f, expr e)) fes)
  | Rocq_proj (f, e1) ->
      (* less well supported:  expr e1 ^^ dot ^^ string f *)
      parens (app (string f) (expr e1))
  | ( Rocq_app _ | Rocq_lettuple _ | Rocq_quant _ | Rocq_fun _ | Rocq_if _
    | Rocq_match _ | Rocq_infix _ ) as e ->
      parens (expr e)

and spec_vars_cfml l =
  let spec_var v =
    string (match v with Unit | Wildcard -> "_" | Var v -> v)
  in
  parens (separate_map comma spec_var l) ^^ space ^^ equals ^^ space

and cfml_post rets post =
  match rets with
  | [ Unit ] -> string "POSTUNIT" ^^ expr0 post
  | [ Var x ] ->
      string "POST"
      ^^ parens (string "fun" ^^ space ^^ string x ^^ doublearrow ^^ expr0 post)
  | l ->
      let ret_name = "_rets_" in
      string "POST"
      ^^ parens
           (string "fun" ^^ space ^^ string ret_name ^^ doublearrow
           ^^ parens (spec_vars_cfml l)
           ^^ string ret_name ^^ string "in" ^^ expr0 post)

(* and sep_expr_cfml = function *)
(*   | Rocq_pure e -> backslash ^^ brackets (expr e) *)
(*   | Rocq_hempty -> backslash ^^ lbracket ^^ rbracket *)
(* | Rocq_spec (f, args, pre, rets, post) -> *)
(*     string "SPEC" *)
(*     ^^ parens *)
(*          (string f ^^ space *)
(*          ^^ separate_map (string " ") (fun x -> string x.var_name) args) *)
(*     ^^ break 0 ^^ string "PRE" ^^ expr pre ^^ break 0 ^^ cfml_post rets post *)

and iris_rets rets =
  let vars =
    List.mapi
      (fun i -> function
        | Var x -> x | Wildcard -> "_x" ^ string_of_int i | Unit -> "#()")
      rets
  in
  let comma_if_cons =
    if List.for_all (( = ) "#()") vars then empty else comma ^^ space
  in
  let ret = match vars with [ x ] -> string x | _ -> tuple string vars in
  let vars = List.filter (( <> ) "#()") vars in
  separate_map space string vars
  ^^ comma_if_cons ^^ string "RET " ^^ ret ^^ semi ^^ space

(* and sep_expr_iris = function *)
(*   | Rocq_pure e -> corners (expr e) *)
(*   | Rocq_hempty -> string "True" *)
(* | Rocq_spec (f, args, pre, rets, post) -> *)
(*     let triple b = b ^^ b ^^ b in *)
(*     triple lbrace ^^ space ^^ expr pre ^^ space ^^ triple rbrace ^^ break 0 *)
(*     ^^ string f ^^ space *)
(*     ^^ separate_map (string " ") (fun x -> string x.var_name) args *)
(*     ^^ break 0 ^^ triple lbrace ^^ space ^^ iris_rets rets ^^ expr post *)
(*     ^^ space ^^ triple rbrace *)

and expr1 = function
  | Rocq_app (e1, e2) -> app (expr1 e1) (expr0 e2)
  | Rocq_infix (e1, v, e2) -> expr0 e1 ^^ space ^^ string v ^^ space ^^ expr0 e2
  | e -> expr0 e

and expr2 = function
  | Rocq_lettuple (es, e1, e2) ->
      block
        (string "let '" ^^ tuple expr es ^^ space ^^ colonequals)
        (break 1 ^^ expr e1)
        (break 1 ^^ string "in")
      ^/^ expr2 e2
  | Rocq_quant (q, vars, e2) ->
      let quant = match q with Forall -> "forall" | Exists -> "exists" in
      let args tv =
        block
          (string quant ^^ space ^^ string tv.var_name ^^ spacecolon)
          (break 1 ^^ expr tv.var_type)
          (break 1)
      in
      concat_map args vars ^^ comma ^^ expr2 e2
  | Rocq_fun (var, e2) ->
      block
        (string "fun" ^^ space ^^ lbracket ^^ string var.var_name ^^ spacecolon)
        (break 1 ^^ expr var.var_type)
        (break 1 ^^ doublearrow)
      ^/^ expr2 e2
  | Rocq_if (e0, e1, e2) ->
      block
        (string "if" ^^ space ^^ expr e0 ^^ space ^^ string "then")
        (break 1 ^^ expr e1 ^^ break 1)
        (string "else" ^^ break 1 ^^ expr e2)
  | Rocq_match (carg, branches) ->
      let mk_branch (c1, c2) =
        group
          (string "|" ^^ space ^^ expr c1 ^^ space ^^ doublearrow ^^ space
         ^^ expr c2)
        ^^ hardline
      in
      block
        (string "match" ^^ space ^^ expr carg ^^ space ^^ string "with"
       ^^ hardline)
        (concat_map mk_branch branches)
        (string "end")
  | e -> expr1 e

and expr e = expr2 e

(* -------------------------------------------------------------------------- *)

(* Typed variables: [x : t]. *)

(* Raw. *)

and var { var_name = x; var_type = t; _ } = binding (string x) (expr t)

(* With parentheses and with a leading space. *)

and pvar xt =
  let v = var xt in
  space ^^ parens v

and pvars xts = group (concat_map pvar xts)

(* A list of field type declarations, separated with semicolons. *)

let fields_type xts = separate_map (semi ^^ break 1) var xts

(* -------------------------------------------------------------------------- *)

(* Tools for toplevel elements. *)

(* A definition, without a leading keyword, but with a leading space.
   [ x : d1 :=]. *)

let definition x d1 =
  block (space ^^ x ^^ spacecolon) (break 1 ^^ d1) (break 1 ^^ colonequals)

(* A parameter, without a leading keyword, but with a leading space.
   [ x : d1.]. *)

let parameter nm ret =
  block (space ^^ string nm ^^ spacecolon) (break 1 ^^ expr1 ret) empty

(* The right-hand side of a record declaration. [ Foo {| ... |}]. *)

let record_rhs r =
  space
  ^^ string r.rocqind_constructor_name
  ^^ space
  ^^ braces (fields_type r.rocqind_branches)

(* The right-hand side of a sum declaration. [| x1 : T1 | x2 : T2 ...]. *)

let sum_rhs r =
  concat_map
    (fun xt -> hardline ^^ block (string "| ") (var xt) empty)
    r.rocqind_branches

(* The left-hand side of a record or sum declaration. [ foo params : T := rhs]. *)

let inductive_lhs rhs r =
  definition
    (string r.rocqind_name ^^ pvars r.rocqind_targs)
    (expr r.rocqind_ret)
  ^^ rhs r

(* An implicit argument specification. *)

(* DEPRECATED
   let deprecated_implicit (x, i) =
     match i with
     | Rocqi_maximal ->
         brackets (string x)
     | Rocqi_implicit ->
         string x
     | Rocqi_explicit ->
         sprintf "(* %s *)" x
*)

let tvars _ = assert false

(* -------------------------------------------------------------------------- *)

(* Toplevel elements. *)

let rec top_internal = function
  | Rocqtop_def instance ->
      let first_keyword =
        if instance.def_rec then "Fixpoint" else "Definition"
      in

      let keyword = first_keyword in
      string keyword ^^ space ^^ string instance.def_nm ^^ space
      ^^ tvars instance.def_tvars ^^ spacecolon ^^ space
      ^^ expr instance.def_return ^^ colonequals ^^ break 1
      ^^ expr instance.def_body
  | Rocqtop_param param ->
      string "Parameter" ^^ parameter param.param_nm param.param_ret
  | Rocqtop_axiom param ->
      string "Axiom" ^^ parameter param.param_nm param.param_ret
  | Rocqtop_instance instance ->
      string "Global Declare Instance"
      ^^ string instance.inst_nm ^^ spacecolon ^^ string instance.inst_class
  | Rocqtop_record r -> string "Record" ^^ inductive_lhs record_rhs r ^^ dot
  | Rocqtop_import xs -> string "Import " ^^ flow_map space string xs ^^ dot
  | Rocqtop_require_import xs ->
      string "Require Import " ^^ flow_map space string xs ^^ dot
  | Rocqtop_module (x, defs) ->
      string "Module" ^^ space ^^ string x ^^ dot ^^ hardline ^^ tops defs
      ^^ string "End" ^^ string x
  | Rocqtop_module_type (x, bs, d) ->
      string "Module Type" ^^ space ^^ string x ^^ spacecolon ^^ space
      ^^ string bs ^^ dot ^^ hardline ^^ tops d ^^ string "End" ^^ string x
  | Rocqtop_module_type_include x -> sprintf "Include Type %s." x
  | Rocqtop_custom x -> sprintf "%s" x
  | Rocqtop_section x -> sprintf "Section %s." x
  | Rocqtop_context xs -> sprintf "Context" ^^ space ^^ pvars xs ^^ dot
  | Rocqtop_class _ -> assert false
  | Rocqtop_htop _ -> assert false

and top t = group (top_internal t)

and tops ts =
  let first = ref true in
  concat_map
    (fun t ->
      (if !first then (
         first := true;
         empty)
       else hardline2)
      ^^ top t ^^ dot)
    ts

(* -------------------------------------------------------------------------- *)

(* The main entry point translates a list of toplevel elements to a string. *)

let tops ts : string = run (PPrint.ToBuffer.pretty 0.9 !width) (tops ts)

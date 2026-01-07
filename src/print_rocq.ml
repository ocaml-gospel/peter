open PPrint
open Rocq

module type S = sig
  val print_spec : Rocq.spec -> document
  val print_set : var -> rocq -> document
  val print : rocqtops -> var
end

let run (print : Buffer.t -> 'a -> unit) (x : 'a) : string =
  let b = Buffer.create 1024 in
  print b x;
  Buffer.contents b

let indentation = 2
let nest d = nest indentation d

let separate_map ?(first = break 1) ?(last = break 1) ?(sep = break 1) f l =
  match l with [] -> empty | _ -> group (first ^^ separate_map sep f l ^^ last)

(* -------------------------------------------------------------------------- *)

(* Global parameters. *)

let width = 80

(* -------------------------------------------------------------------------- *)

(* Various fixed elements. *)

let arrow = string " ->" ^^ break 1
let doublearrow = string "=>"
let colonequals = string " :="
let spacecolon = string " : "
let spacecolonbr = string " :" ^^ break 1
let hardline2 = hardline ^^ hardline
let semi = string ";" ^^ break 1

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

(* -------------------------------------------------------------------------- *)

(* A block with indentation. *)

(* -------------------------------------------------------------------------- *)

(* Parentheses with indentation. *)

(* We allow breaking a parenthesized thing into several lines by leaving the
   opening and closing parentheses alone on a line and indenting the content. *)

let parens d = lparen ^^ d ^^ rparen

(* Coq-record braces {| ... |} with spacing and indentation. *)

let record_braces d = string "{|" ^^ break 1 ^^ d ^^ break 1 ^^ string "|}"

(* Brackets with spacing and indentation. *)

let corners d = string "⌜" ^^ break 1 ^^ d ^^ break 1 ^^ string "⌝"
let commabr = comma ^^ break 1

(* -------------------------------------------------------------------------- *)

(* Field assignement : [f := t]. *)

(* Raw. *)

let field (x, t) = x ^^ colonequals ^^ t

(* A list of field value declarations, separated with semicolons. *)

let fields_value = separate_map ~sep:(semi ^^ break 1) field

(* Record definition : {| f1 := t1; ... |} *)

let record_value fts = record_braces (fields_value fts)

(* -------------------------------------------------------------------------- *)

(* Tuples. *)

let tuple expr es = parens (separate_map ~sep:(comma ^^ break 1) expr es)

(* -------------------------------------------------------------------------- *)

let forall_tvars tvars =
  separate_map
    (fun x -> braces (string x))
    ~first:(string "forall ") ~last:commabr tvars

module Printer (Sep_printer : S) = struct
  (* These functions could move to [PPrint]. *)

  (* -------------------------------------------------------------------------- *)

  (* Expressions. *)

  let rec expr0 = function
    | OCaml_type | Gospel_type -> string "Type"
    | Rocq_var s -> string s
    | Rocq_int n -> string (string_of_int n)
    | Rocq_string s -> dquotes (string s)
    | Rocq_tuple es -> tuple expr es
    | Rocq_set (v, t) -> Sep_printer.print_set v t
    | Rocq_record fes ->
        record_value (List.map (fun (f, e) -> (string f, expr e)) fes)
    | Rocq_proj (f, e1) -> parens (app (string f) (expr e1))
    | Rocq_implicit (v, arg) ->
        parens (string v ^^ colonequals ^^ space ^^ expr arg)
    | ( Rocq_app _ | Rocq_lettuple _ | Rocq_quant _ | Rocq_fun _ | Rocq_if _
      | Rocq_match _ | Rocq_infix _ | Rocq_spec _ ) as e ->
        parens (expr e)

  (* and spec_vars_cfml l = *)
  (*   let spec_var v = *)
  (*     string (match v with Unit | Wildcard -> "_" | Var v -> v) *)
  (*   in *)
  (*   parens (con comma spec_var l) ^^ space ^^ equals ^^ space *)

  (* and cfml_post rets post = *)
  (*   match rets with *)
  (*   | [ Unit ] -> string "POSTUNIT" ^^ expr0 post *)
  (*   | [ Var x ] -> *)
  (*       string "POST" *)
  (*       ^^ parens (string "fun" ^^ space ^^ string x ^^ doublearrow ^^ expr0 post) *)
  (*   | l -> *)
  (*       let ret_name = "_rets_" in *)
  (*       string "POST" *)
  (*       ^^ parens *)
  (*            (string "fun" ^^ space ^^ string ret_name ^^ doublearrow *)
  (*            ^^ parens (spec_vars_cfml l) *)
  (*            ^^ string ret_name ^^ string "in" ^^ expr0 post) *)

  (* and sep_expr_cfml = function *)
  (*   | Rocq_pure e -> backslash ^^ brackets (expr e) *)
  (*   | Rocq_hempty -> backslash ^^ lbracket ^^ rbracket *)
  (* | Rocq_spec (f, args, pre, rets, post) -> *)
  (*     string "SPEC" *)
  (*     ^^ parens *)
  (*          (string f ^^ space *)
  (*          ^^ separate_map (string " ") (fun x -> string x.var_name) args) *)
  (*     ^^ break 0 ^^ string "PRE" ^^ expr pre ^^ break 0 ^^ cfml_post rets post *)

  and expr1 = function
    | Rocq_app (e1, e2) -> app (expr1 e1) (expr0 e2)
    | Rocq_infix (e1, "->", Rocq_infix (e2, "->", e3)) ->
        expr0 e1 ^^ arrow ^^ expr0 e2 ^^ arrow ^^ expr1 e3
    | Rocq_infix (e1, v, e2) ->
        expr0 e1 ^^ break 1 ^^ string v ^^ break 1 ^^ expr0 e2
    | e -> expr0 e

  and quant_vars quant vars d = (string quant ^^ tvars ~last:commabr vars) ^^ d

  and expr2 = function
    | Rocq_lettuple (es, e1, e2) ->
        (string "let '" ^^ tuple expr es ^^ space ^^ colonequals)
        ^^ break 1 ^^ expr e1 ^^ break 1 ^^ string "in" ^/^ expr e2
    | Rocq_quant (q, vars, e2) ->
        let quant = match q with Forall -> "forall" | Exists -> "exists" in
        quant_vars quant vars (expr e2)
    | Rocq_fun (var, e2) ->
        string "fun" ^^ space ^^ tvar var ^^ break 1 ^^ doublearrow ^/^ expr e2
    | Rocq_if (e0, e1, e2) ->
        string "if" ^^ space ^^ expr e0 ^^ space ^^ string "then" ^^ break 1
        ^^ expr e1 ^^ break 1 ^^ string "else" ^^ break 1 ^^ expr e2
    | Rocq_match (carg, branches) ->
        let mk_branch (c1, c2) =
          group
            (string "|" ^^ space ^^ expr c1 ^^ space ^^ doublearrow ^^ space
           ^^ expr c2)
          ^^ hardline
        in

        string "match" ^^ space ^^ expr carg ^^ space ^^ string "with"
        ^^ hardline
        ^^ concat_map mk_branch branches
        ^^ string "end"
    | Rocq_spec spec -> Sep_printer.print_spec spec
    | e -> expr1 e

  and expr e = group (expr2 e)

  (* Typed variables: [x : t]. *)

  (* Raw. *)

  and binding x t = parens (x ^^ spacecolon ^^ t)

  and tvar v =
    match v.var_name with
    | Some x -> binding (string x) (expr v.var_type)
    | None -> string "`" ^^ braces (expr v.var_type)

  and tvars ?(last = space) l = separate_map ~last tvar l

  (* -------------------------------------------------------------------------- *)

  (* Tools for toplevel elements. *)

  (* A parameter, without a leading keyword, but with a leading space.
   [ x : d1.]. *)

  let parameter nm ret = space ^^ string nm ^^ spacecolon ^^ expr1 ret

  (* The left-hand side of a record or sum declaration. [ foo params : T := rhs]. *)

  (* Bindings, or annotations: [x : t]. *)

  let bindings ~first = separate_map ~first tvar

  let fields =
    separate_map ~sep:semi ~first:empty ~last:empty (fun (v, t) ->
        string v ^^ spacecolonbr ^^ expr t)

  let record r =
    (string r.rname ^^ bindings ~first:space r.rvars)
    ^^ expr typ ^^ colonequals ^^ space
    ^^ nest (lbrace ^^ break 1 ^^ fields r.rfields)
    ^^ break 1 ^^ rbrace

  let type_var v = lbrace ^^ string v ^^ rbrace
  let type_vars = separate_map ~first:empty type_var

  (* -------------------------------------------------------------------------- *)

  (* Top level elements. *)

  let inst x = string "`" ^^ braces (string "@" ^^ string x)
  let insts = separate_map ~first:empty inst

  let rocq_class c =
    string "Class " ^^ string c.cname ^^ space ^^ insts c.cdeps ^^ colonequals
    ^^ space ^^ lbrace
    ^^ group
         (nest
            (break 1 ^^ string c.cproj
            ^^ nest (spacecolonbr ^^ forall_tvars c.ctvars ^^ expr c.crocq))
         ^^ break 1 ^^ rbrace)

  let deps xs = nest (separate_map ~last:empty string xs)
  let import xs = string "Import" ^^ deps xs

  let rec top = function
    | Rocqtop_def def ->
        let keyword = if def.def_rec then "Fixpoint" else "Definition" in
        string keyword ^^ space ^^ string def.def_nm ^^ space
        ^^ type_vars def.def_tvars ^^ insts def.def_insts
        ^^ bindings ~first:empty def.def_args
        ^^ colon ^^ space ^^ expr def.def_return ^^ colonequals
        ^^ group (nest (break 1 ^^ expr def.def_body))
    | Rocqtop_param param ->
        string "Parameter" ^^ parameter param.param_nm param.param_ret
    | Rocqtop_instance instance ->
        string "Global Declare Instance "
        ^^ string instance.inst_nm ^^ spacecolon ^^ string instance.inst_class
    | Rocqtop_record r -> string "Record " ^^ record r
    | Rocqtop_import xs -> import xs
    | Rocqtop_require xs -> string "Require" ^^ deps xs
    | Rocqtop_require_import xs -> string "Require " ^^ import xs
    | Rocqtop_module (x, args, defs) -> print_module "Module" x args defs
    | Rocqtop_module_type (x, args, d) -> print_module "Module Type" x args d
    | Rocqtop_module_type_include x -> string "Include Type %s." ^^ string x
    | Rocqtop_custom x -> string x
    | Rocqtop_section x -> string "Section " ^^ string x
    | Rocqtop_context xs -> string "Context" ^^ space ^^ tvars xs
    | Rocqtop_class c -> rocq_class c
    | Rocqtop_notation (nm, e) ->
        string "Notation " ^^ string nm ^^ colonequals ^^ break 1
        ^^ parens (expr e)
        ^^ string " (only parsing)"

  and print_module prefix x args defs =
    string prefix ^^ space ^^ string x
    ^^ separate_map ~sep:space tvar args
    ^^ dot ^^ hardline
    ^^ nest (tops defs)
    ^^ hardline ^^ string "End " ^^ string x

  and tops ?(first = hardline) ?(last = hardline) ts : document =
    separate_map (fun t -> top t ^^ dot) ~sep:hardline2 ~first ~last ts

  (* -------------------------------------------------------------------------- *)

  (* The main entry point translates a list of toplevel elements to a string. *)

  let print ts : string =
    run (PPrint.ToBuffer.pretty 0.9 width) (tops ~first:empty ~last:empty ts)
end

module rec Iris : S = struct
  module Printer = Printer (Iris)
  include Printer

  let print_set v t =
    lbrace ^^ space ^^ string v ^^ space ^^ bar ^^ space ^^ expr1 t ^^ rbrace

  let spec_var named = function
    | Var x ->
        named := true;
        tvar x
    | Wildcard -> assert false
    | Unit -> string "#()"

  let spec_var_opt = function
    | Var x -> Some (tvar x)
    | Wildcard -> assert false
    | Unit -> None

  let iris_rets rets =
    let named = ref false in
    let vars = List.map (spec_var named) rets in
    let ex = List.filter_map spec_var_opt rets in
    let comma_if_cons = if !named then comma ^^ space else empty in
    let ret = match vars with [ x ] -> x | _ -> tuple (fun x -> x) vars in
    separate_map (fun x -> x) ex
    ^^ comma_if_cons ^^ string "RET " ^^ ret ^^ semi ^^ space

  let empty = string "True"

  let rec sep_expr = function
    | Rocq_pure e -> corners (expr e)
    | Rocq_hempty -> empty
    | Rocq_lift (v, e1, e2) ->
        group (string v ^^ break 1 ^^ expr0 e1 ^^ break 1 ^^ expr0 e2)
    | Rocq_hquant (q, vars, seps) ->
        let q = match q with Forall -> "∀" | Exists -> "∃" in
        quant_vars q vars (sep_exprs seps)

  and sep_exprs = function l -> separate_map ~sep:(string "∗") sep_expr l

  let print_spec spec =
    let triple b = b ^^ b ^^ b in
    triple lbrace ^^ space ^^ sep_exprs spec.spec_pre ^^ space ^^ triple rbrace
    ^^ break 1 ^^ string spec.spec_nm ^^ space
    ^^ separate_map (fun x -> spec_var (ref true) x) spec.spec_args
    ^^ break 0 ^^ triple lbrace ^^ space ^^ iris_rets spec.spec_ret
    ^^ sep_exprs spec.spec_post ^^ space ^^ triple rbrace
end

module rec CFML : S = struct
  module Printer = Printer (CFML)
  include Printer

  let spec_vars l =
    let spec_var v =
      string
        (match v with Unit | Wildcard -> "_" | Var v -> Option.get v.var_name)
    in
    separate_map spec_var l

  let rec sep_expr = function
    | Rocq_pure e -> backslash ^^ brackets (expr e)
    | Rocq_hempty -> backslash ^^ lbracket ^^ rbracket
    | Rocq_lift (v, e1, e2) ->
        expr e1 ^^ space ^^ string "~> " ^^ string v ^^ space ^^ expr e2
    | Rocq_hquant (q, v, e) ->
        let q = match q with Forall -> "∀" | Exists -> "∃" in
        quant_vars q v (sep_exprs e)

  and sep_exprs l = separate_map ~sep:(string "\\*") sep_expr l

  let cfml_post rets post =
    let post = sep_exprs post in
    match rets with
    | [ Unit ] -> string "POSTUNIT" ^^ post
    | [ Var x ] ->
        string "POST"
        ^^ parens
             (string "fun" ^^ space
             ^^ string (Option.get x.var_name)
             ^^ doublearrow ^^ post)
    | l ->
        let ret_name = "_rets_" in
        string "POST"
        ^^ parens
             (string "fun" ^^ space ^^ string ret_name ^^ doublearrow
             ^^ parens (spec_vars l)
             ^^ string ret_name ^^ string "in" ^^ post)

  let print_spec spec =
    string "SPEC"
    ^^ parens (string spec.spec_nm ^^ space ^^ spec_vars spec.spec_args)
    ^^ break 0 ^^ string "PRE" ^^ sep_exprs spec.spec_pre ^^ break 0
    ^^ cfml_post spec.spec_ret spec.spec_post

  let print_set v t =
    parens (string "fun " ^^ string v ^^ string "=>" ^^ expr0 t)
end

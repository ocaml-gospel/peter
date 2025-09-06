(*@ open Sequence *)

type t
(*@ mutable model : integer Sequence.t *)

val create : unit -> t
(*@ q = create ()
    produces q
    ensures q = []
*)

val push : t -> int -> unit
(*@ () = push q x
    modifies q
    ensures q = cons x (old q)
*)

val clear : t -> unit
(*@ () = clear q
    consumes q
    produces q
    ensures q = [] *)

val copy : t -> t
(*@ q2 = copy q1
    preserves q1
    produces q2
    ensures q2 = q1
*)

val is_empty : t -> bool
(*@ b = is_empty q
    preserves q
    ensures b <-> q = [] *)

val length : t -> int
(*@ l = length q
    preserves q
    ensures Sequence.length q = l *)

val transfer : t -> t -> unit
(*@ () = transfer q1 q2
    consumes q1
    consumes q2

    produces q1
    produces q2

    ensures q1 = []
    ensures q2 = old (q2 ++ q1) *)

(* missing : pop, take, iter, fold, to_seq, add_seq, of_seq *)

(* predicate is_eq (A : type)
(* this predicate does not hold for unwoned mutable structures and functions*)

val st_eq : 'a -> 'a -> bool
(* b = st_eq x y
    requires is_eq 'a
    ensures b <-> x = y
 *)

(* predicate unowned (A : type) *)



(*
{ R x Mx * R y My * [unowned R] } ph_eq x y {[x = y]}

val ph_eq : 'a -> 'a -> bool
(* b = st_eq x y
    requires addressable 'a
    ensures b <-> &x = &y
 *)

{ [is_loc x && is_loc y] } ph_eq x y {[x = y]}

 predicates over types, type classes *)
(* increase clarity in spatial specs
   adressable vs unowned *)
 *)

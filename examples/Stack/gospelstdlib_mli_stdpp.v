Set Implicit Arguments.

Require Import Stdlib.ZArith.BinInt stdpp.base.

Require Import Stdlib.ZArith.BinIntDef.

Local Open Scope Z_scope.

Module Type Stdlib.

Parameter set : Type -> Type.

Parameter sequence : Type -> Type.

Parameter bag : Type -> Type.

Parameter option : Type -> Type.

Parameter Some :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  option A.

Parameter None :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  option A.

Definition map  (A : Type) (B : Type) : Type:= A -> B.

Parameter succ : forall x : Z, Z.

Parameter pred : forall x : Z, Z.

Parameter neg : forall x : Z, Z.

Parameter _mod : forall x : Z, forall y : Z, Z.

Parameter pow : forall x : Z, forall y : Z, Z.

Parameter abs : forall x : Z, Z.

Parameter min : forall x : Z, forall y : Z, Z.

Parameter max : forall x : Z, forall y : Z, Z.

Parameter app :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall s' : sequence A,
  sequence A.

Parameter seq_get :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall i : Z,
  A.

Parameter seq_sub :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall i1 : Z,
  forall i2 : Z,
  sequence A.

Parameter seq_sub_l :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall i : Z,
  sequence A.

Parameter seq_sub_r :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall i : Z,
  sequence A.

Parameter monoid :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : A -> A -> A,
  forall neutral : A,
  Prop.

Axiom monoid_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : A -> A -> A,
  forall neutral : A,
  (
    (monoid f neutral) <-> (
      (
        (
          forall x : A,
          ((((f neutral x) = (f x neutral))) /\ (((f x neutral) = x)))
        ) /\ (
          forall x : A,
          forall y : A,
          forall z : A,
          ((f x (f y z)) = (f (f x y) z))
        )
      )
    )
  ).

Parameter comm_monoid :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : A -> A -> A,
  forall neutral : A,
  Prop.

Axiom comm_monoid_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : A -> A -> A,
  forall neutral : A,
  (
    (comm_monoid f neutral) <-> (
      (
        (monoid f neutral) /\ (forall x : A, forall y : A, ((f x y) = (f y x)))
      )
    )
  ).

Module Sequence.

Definition t  (A : Type) : Type:= sequence A.

Parameter length :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : t A,
  Z.

Parameter in_range :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : t A,
  forall i : Z,
  Prop.

Axiom in_range_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall i : Z,
  ((in_range s i) <-> ((((0 <= i)) /\ ((i < (length s)))))).

Axiom length_nonneg :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  (0 <= (length s)).

Axiom subseq_l :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall i : Z,
  in_range s i -> ((seq_sub_l s i) = (seq_sub s i (length s))).

Axiom subseq_r :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall i : Z,
  in_range s i -> ((seq_sub_r s i) = (seq_sub s 0 i)).

Axiom subseq :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall i : Z,
  forall i1 : Z,
  forall i2 : Z,
  (
    ((0 <= i1)) /\ ((((i1 <= i)) /\ ((((i < i2)) /\ ((i2 <= (length s)))))))
  ) ->
  ((seq_get s i) = (seq_get (seq_sub s i1 i2) ((i - i1)))).

Axiom subseq_len :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall i1 : Z,
  forall i2 : Z,
  (((0 <= i1)) /\ ((((i1 <= i2)) /\ ((i2 < (length s)))))) ->
  ((length (seq_sub s i1 i2)) = ((i2 - i1))).

Parameter empty :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  t A.

Axiom empty_length :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  ((@length A Eq_A Ih_A empty) = 0).

Parameter init :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall n : Z,
  forall f : Z -> A,
  t A.

Axiom init_length :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall n : Z,
  forall f : Z -> A,
  (n >= 0) -> ((length (init n f)) = n).

Axiom init_elems :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall n : Z,
  forall f : Z -> A,
  forall i : Z,
  (((0 <= i)) /\ ((i < n))) -> ((seq_get (init n f) i) = (f i)).

Parameter singleton :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  t A.

Axiom singleton_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall f : Z -> A,
  ((f 0) = x) -> ((singleton x) = (init 1 f)).

Parameter cons :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : t A,
  t A.

Axiom cons_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : sequence A,
  ((cons x s) = (app (singleton x) s)).

Parameter snoc :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : t A,
  forall x : A,
  t A.

Axiom snoc_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall x : A,
  ((snoc s x) = (app s (singleton x))).

Parameter hd :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : t A,
  A.

Axiom hd_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  ((hd s) = (seq_get s 0)).

Parameter tl :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : t A,
  t A.

Axiom tl_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  ((tl s) = (seq_sub_l s 1)).

Parameter append :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s1 : t A,
  forall s2 : t A,
  t A.

Axiom append_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s1 : sequence A,
  forall s2 : sequence A,
  ((append s1 s2) = (app s1 s2)).

Axiom append_length :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall s' : sequence A,
  ((length (app s s')) = (((length s) + (length s')))).

Axiom append_elems_left :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall s' : sequence A,
  forall i : Z,
  in_range s i -> ((seq_get (app s s') i) = (seq_get s i)).

Axiom append_elems_right :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall s' : sequence A,
  forall i : Z,
  ((((length s) <= i)) /\ ((i < (((length s) + (length s')))))) ->
  ((seq_get (app s s') i) = (seq_get s' ((i - (length s))))).

Parameter multiplicity :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : t A,
  Z.

Axiom mult_empty :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  ((multiplicity x empty) = 0).

Axiom mult_cons :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall x : A,
  (((1 + (multiplicity x s))) = (multiplicity x (cons x s))).

Axiom mult_cons_neutral :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall x1 : A,
  forall x2 : A,
  (x1 <> x2) -> ((multiplicity x1 s) = (multiplicity x1 (cons x2 s))).

Axiom mult_length :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : sequence A,
  (((0 <= (multiplicity x s))) /\ (((multiplicity x s) <= (length s)))).

Parameter belongs :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : t A,
  Prop.

Parameter mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : t A,
  Prop.

Axiom mem_fun_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : sequence A,
  ((belongs x s) <-> (mem x s)).

Axiom mem_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall x : A,
  ((belongs x s) <-> (((multiplicity x s) > 0))).

Parameter neg_belongs :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : t A,
  Prop.

Axiom nmem_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall x : A,
  ((neg_belongs x s) <-> (not (belongs x s))).

Parameter Forall :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall p : A -> Prop,
  forall {Dec_p : forall x0 : _, Decision (p x0)},
  forall s : sequence A,
  Prop.

Axiom forall_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall p : A -> Prop,
  forall {Dec_p : forall x0 : _, Decision (p x0)},
  forall s : sequence A,
  ((Forall p s) <-> (forall x : A, belongs x s -> p x)).

Parameter Exists :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall p : A -> Prop,
  forall {Dec_p : forall x0 : _, Decision (p x0)},
  forall s : sequence A,
  Prop.

Axiom exists_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall p : A -> Prop,
  forall {Dec_p : forall x0 : _, Decision (p x0)},
  forall s : sequence A,
  ((Exists p s) <-> (exists x : A, ((belongs x s) /\ (p x)))).

Parameter map :
  forall {A : Type},
  forall {B : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall f : A -> B,
  forall s : t A,
  t B.

Axiom map_elems :
  forall {B : Type},
  forall {A : Type},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall i : Z,
  forall f : B -> A,
  forall s : sequence B,
  in_range s i -> ((seq_get (map f s) i) = (f (seq_get s i))).

Axiom map_length :
  forall {B : Type},
  forall {A : Type},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : B -> A,
  forall s : sequence B,
  ((length (map f s)) = (length s)).

Parameter filter :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : A -> Prop,
  forall {Dec_f : forall x0 : _, Decision (f x0)},
  forall s : t A,
  t A.

Axiom filter_elems :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : A -> Prop,
  forall {Dec_f : forall x0 : _, Decision (f x0)},
  forall s : sequence A,
  forall x : A,
  belongs x s -> f x -> belongs x (filter f s).

Parameter filter_map :
  forall {A : Type},
  forall {B : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall f : A -> option B,
  forall s : t A,
  t B.

Axiom filter_map_elems :
  forall {B : Type},
  forall {A : Type},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : B -> option A,
  forall s : sequence B,
  forall y : A,
  (
    (exists x : B, ((((f x) = (Some y))) /\ (belongs x s))) <-> (
      belongs y (filter_map f s)
    )
  ).

Parameter get :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : t A,
  forall i : Z,
  A.

Axiom get_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall i : Z,
  ((get s i) = (seq_get s i)).

Parameter set :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : t A,
  forall i : Z,
  forall x : A,
  t A.

Axiom set_elem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall i : Z,
  forall x : A,
  in_range s i -> ((seq_get (set s i x) i) = x).

Axiom set_elem_other :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall i1 : Z,
  forall i2 : Z,
  forall x : A,
  (i1 <> i2) ->
  in_range s i1 ->
  in_range s i2 -> ((seq_get (set s i1 x) i2) = (seq_get s i2)).

Parameter rev :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : t A,
  t A.

Axiom rev_length :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  ((length s) = (length (rev s))).

Axiom rev_elems :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall i : Z,
  forall s : sequence A,
  in_range s i ->
  ((seq_get (rev s) i) = (seq_get s (((((length s) - 1)) - i)))).

Axiom extensionality :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s1 : sequence A,
  forall s2 : sequence A,
  ((length s1) = (length s2)) ->
  (forall i : Z, in_range s1 i -> ((seq_get s1 i) = (seq_get s2 i))) ->
  (s1 = s2).

Parameter fold_left :
  forall {A : Type},
  forall {B : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall f : A -> B -> A,
  forall acc : A,
  forall s : t B,
  A.

Axiom fold_left_empty :
  forall {B : Type},
  forall {A : Type},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : A -> B -> A,
  forall acc : A,
  ((fold_left f acc empty) = acc).

Axiom fold_left_cons :
  forall {B : Type},
  forall {A : Type},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : A -> B -> A,
  forall acc : A,
  forall x : B,
  forall l : sequence B,
  ((fold_left f acc (cons x l)) = (fold_left f (f acc x) l)).

Parameter fold_right :
  forall {A : Type},
  forall {B : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall f : A -> B -> B,
  forall s : t A,
  forall acc : B,
  B.

Axiom fold_right_empty :
  forall {B : Type},
  forall {A : Type},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall acc : A,
  forall f : B -> A -> A,
  ((fold_right f empty acc) = acc).

Axiom fold_right_cons :
  forall {B : Type},
  forall {A : Type},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall acc : A,
  forall f : B -> A -> A,
  forall x : B,
  forall l : sequence B,
  ((fold_right f (cons x l) acc) = (f x (fold_right f l acc))).

Parameter permut :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s1 : t A,
  forall s2 : t A,
  Prop.

Axiom permut_mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s1 : sequence A,
  forall s2 : sequence A,
  permut s1 s2 -> (forall x : A, ((belongs x s1) <-> (belongs x s2))).

Parameter permut_sub :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s1 : t A,
  forall s2 : t A,
  forall i : Z,
  forall j : Z,
  Prop.

Axiom permut_sub_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s1 : sequence A,
  forall s2 : sequence A,
  forall i : Z,
  forall j : Z,
  permut (seq_sub s1 i j) (seq_sub s2 i j) ->
  ((seq_sub_r s1 i) = (seq_sub_r s2 i)) ->
  ((seq_sub_l s1 j) = (seq_sub_l s2 j)) -> permut_sub s1 s2 i j.

End Sequence.

Module Bag.

Definition t  (A : Type) : Type:= bag A.

Parameter multiplicity :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall b : t A,
  Z.

Axiom well_formed :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : bag A,
  forall x : A,
  ((multiplicity x b) >= 0).

Parameter empty :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  t A.

Axiom empty_mult :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  ((multiplicity x empty) = 0).

Parameter init :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : A -> Z,
  t A.

Axiom init_axiom :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : A -> Z,
  forall x : A,
  ((max 0 (f x)) = (multiplicity x (init f))).

Parameter belongs :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall b : t A,
  Prop.

Parameter mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : t A,
  Prop.

Axiom mem_fun_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : bag A,
  ((belongs x s) <-> (mem x s)).

Parameter neg_belongs :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : t A,
  Prop.

Axiom nmem_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : bag A,
  forall x : A,
  ((neg_belongs x s) <-> (not (belongs x s))).

Axiom mem_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall b : bag A,
  ((belongs x b) <-> (((multiplicity x b) > 0))).

Parameter add :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall b : t A,
  t A.

Axiom add_mult_x :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : bag A,
  forall x : A,
  ((multiplicity x (add x b)) = ((1 + (multiplicity x b)))).

Axiom add_mult_neg_x :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall y : A,
  forall b : bag A,
  (x <> y) -> ((multiplicity y (add x b)) = (multiplicity y b)).

Parameter singleton_set :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  t A.

Parameter singleton :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  t A.

Axiom singleton_fun_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  ((singleton_set x) = (singleton x)).

Axiom singleton_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  ((singleton_set x) = (add x empty)).

Parameter remove :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall b : t A,
  t A.

Axiom remove_mult_x :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : bag A,
  forall x : A,
  ((multiplicity x (remove x b)) = (max 0 (((multiplicity x b) - 1)))).

Axiom remove_mult_neg_x :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall y : A,
  forall b : bag A,
  (x <> y) -> ((multiplicity y (remove x b)) = (multiplicity y b)).

Parameter union :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : t A,
  forall b' : t A,
  t A.

Axiom union_all :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : bag A,
  forall b' : bag A,
  forall x : A,
  (
    (max (multiplicity x b) (multiplicity x b')) = (
      multiplicity x (union b b')
    )
  ).

Parameter sum :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : t A,
  forall b' : t A,
  t A.

Axiom sum_all :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : bag A,
  forall b' : bag A,
  forall x : A,
  (
    (((multiplicity x b) + (multiplicity x b'))) = (
      multiplicity x (sum b b')
    )
  ).

Parameter inter :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : t A,
  forall b' : t A,
  t A.

Axiom inter_all :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : bag A,
  forall b' : bag A,
  forall x : A,
  (
    (min (multiplicity x b) (multiplicity x b')) = (
      multiplicity x (inter b b')
    )
  ).

Parameter disjoint :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : t A,
  forall b' : t A,
  Prop.

Axiom disjoint_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : bag A,
  forall b' : bag A,
  ((disjoint b b') <-> (forall x : A, belongs x b -> neg_belongs x b')).

Parameter diff :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : t A,
  forall b' : t A,
  t A.

Axiom diff_all :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : bag A,
  forall b' : bag A,
  forall x : A,
  (
    (max 0 (((multiplicity x b) - (multiplicity x b')))) = (
      multiplicity x (diff b b')
    )
  ).

Parameter subset :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : t A,
  forall b' : t A,
  Prop.

Axiom subset_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : bag A,
  forall b' : bag A,
  (
    (subset b b') <-> (
      forall x : A,
      ((multiplicity x b) <= (multiplicity x b'))
    )
  ).

Parameter filter :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : A -> Prop,
  forall {Dec_f : forall x0 : _, Decision (f x0)},
  forall b : t A,
  t A.

Axiom filter_mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : bag A,
  forall x : A,
  forall f : A -> Prop,
  forall {Dec_f : forall x0 : _, Decision (f x0)},
  f x -> ((multiplicity x (filter f b)) = (multiplicity x b)).

Axiom filter_mem_neg :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : bag A,
  forall x : A,
  forall f : A -> Prop,
  forall {Dec_f : forall x0 : _, Decision (f x0)},
  not (f x) -> ((multiplicity x (filter f b)) = 0).

Parameter cardinal :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : t A,
  Z.

Parameter finite :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : t A,
  Prop.

Axiom finite_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : bag A,
  (
    (finite b) <-> (
      exists s : sequence A,
      forall x : A,
      belongs x b -> Sequence.belongs x s
    )
  ).

Axiom card_nonneg :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b : bag A,
  ((cardinal b) >= 0).

Axiom card_empty :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  ((@cardinal A Eq_A Ih_A empty) = 0).

Axiom card_singleton :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  ((cardinal (singleton_set x)) = 1).

Axiom card_union :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall b1 : bag A,
  forall b2 : bag A,
  finite b1 ->
  finite b2 ->
  ((cardinal (union b1 b2)) = (((cardinal b1) + (cardinal b2)))).

Axiom card_add :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall b : bag A,
  finite b -> ((cardinal (add x b)) = (((cardinal b) + 1))).

Axiom card_map :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : A -> Prop,
  forall {Dec_f : forall x0 : _, Decision (f x0)},
  forall b : bag A,
  finite b -> ((cardinal (filter f b)) <= (cardinal b)).

Parameter of_seq :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : Sequence.t A,
  t A.

Axiom of_seq_multiplicity :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall x : A,
  ((Sequence.multiplicity x s) = (multiplicity x (of_seq s))).

End Bag.

Module _Set.

Definition t  (A : Type) : Type:= set A.

Parameter empty :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  t A.

Parameter belongs :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : t A,
  Prop.

Parameter neg_belongs :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : t A,
  Prop.

Parameter mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : t A,
  Prop.

Axiom mem_fun_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : set A,
  ((belongs x s) <-> (mem x s)).

Axiom nmem_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall x : A,
  ((not (belongs x s)) <-> (neg_belongs x s)).

Axiom empty_mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  neg_belongs x empty.

Parameter add :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : t A,
  t A.

Axiom add_mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall x : A,
  belongs x (add x s).

Axiom add_mem_neq :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall x : A,
  forall y : A,
  (x <> y) -> ((belongs x s) <-> (belongs x (add y s))).

Parameter singleton_set :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  t A.

Parameter singleton :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  t A.

Axiom singleton_fun_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  ((singleton_set x) = (singleton x)).

Axiom singleton_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  ((singleton_set x) = (add x empty)).

Parameter remove :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall s : t A,
  t A.

Axiom remove_mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall x : A,
  neg_belongs x (remove x s).

Axiom remove_mem_neq :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall x : A,
  forall y : A,
  (x <> y) -> ((belongs x s) <-> (belongs x (remove y s))).

Parameter union :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : t A,
  forall s' : t A,
  t A.

Axiom union_mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall s' : set A,
  forall x : A,
  ((belongs x s) \/ (belongs x s')) -> belongs x (union s s').

Axiom union_mem_neg :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall s' : set A,
  forall x : A,
  neg_belongs x s -> neg_belongs x s' -> neg_belongs x (union s s').

Parameter inter :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : t A,
  forall s' : t A,
  t A.

Axiom inter_mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall s' : set A,
  forall x : A,
  belongs x s -> belongs x s' -> belongs x (inter s s').

Axiom inter_mem_neq :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall s' : set A,
  forall x : A,
  not (((belongs x s) \/ (belongs x s'))) -> neg_belongs x (inter s s').

Parameter disjoint :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : t A,
  forall s' : t A,
  Prop.

Axiom disjoint_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall s' : set A,
  ((disjoint s s') <-> (((inter s s') = empty))).

Parameter diff :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : t A,
  forall s' : t A,
  t A.

Axiom diff_mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall s' : set A,
  forall x : A,
  belongs x s' -> neg_belongs x (diff s s').

Axiom diff_mem_fst :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall s' : set A,
  forall x : A,
  neg_belongs x s' -> ((belongs x s) <-> (belongs x (diff s s'))).

Parameter subset :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : t A,
  forall s' : t A,
  Prop.

Axiom subset_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall s' : set A,
  ((subset s s') <-> (forall x : A, belongs x s -> belongs x s')).

Parameter map :
  forall {A : Type},
  forall {B : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall f : A -> B,
  forall s : t A,
  t B.

Axiom set_map :
  forall {A : Type},
  forall {B : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall f : B -> A,
  forall s : set B,
  forall x : A,
  (
    (belongs x (map f s)) <-> (
      exists y : B,
      ((((f y) = x)) /\ (belongs y s))
    )
  ).

Parameter partition :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : A -> Prop,
  forall {Dec_f : forall x0 : _, Decision (f x0)},
  forall s : t A,
  Corelib.Init.Datatypes.prod (t A) (t A).

Axiom partition_l_mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : A -> Prop,
  forall {Dec_f : forall x0 : _, Decision (f x0)},
  forall s : set A,
  forall x : A,
  forall p1 : set A,
  forall p2 : set A,
  belongs x s -> f x -> ((partition f s) = (p1, p2)) -> belongs x p1.

Axiom partition_r_mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall f : A -> Prop,
  forall {Dec_f : forall x0 : _, Decision (f x0)},
  forall s : set A,
  forall x : A,
  forall p1 : set A,
  forall p2 : set A,
  belongs x s -> not (f x) -> ((partition f s) = (p1, p2)) -> belongs x p2.

Parameter cardinal :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : t A,
  Z.

Parameter finite :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : t A,
  Prop.

Axiom finite_def :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  (
    (finite s) <-> (
      exists seq : sequence A,
      forall x : A,
      belongs x s -> Sequence.belongs x seq
    )
  ).

Axiom cardinal_nonneg :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  ((cardinal s) >= 0).

Axiom cardinal_empty :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  ((@cardinal A Eq_A Ih_A empty) = 0).

Axiom cardinal_remove_mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall x : A,
  finite s ->
  belongs x s -> ((cardinal (remove x s)) = (((cardinal s) - 1))).

Axiom cardinal_remove_not_mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall x : A,
  finite s -> neg_belongs x s -> ((cardinal (remove x s)) = (cardinal s)).

Axiom cardinal_add :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall x : A,
  finite s ->
  neg_belongs x s -> ((cardinal (add x s)) = (((cardinal s) + 1))).

Axiom cardinal_add_mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  forall x : A,
  finite s -> belongs x s -> ((cardinal (add x s)) = (cardinal s)).

Parameter of_seq :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : Sequence.t A,
  t A.

Axiom of_seq_mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : sequence A,
  forall x : A,
  ((belongs x (of_seq s)) <-> (Sequence.belongs x s)).

Parameter to_seq :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : t A,
  Sequence.t A.

Axiom to_seq_mem :
  forall {A : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall s : set A,
  finite s ->
  (
    forall x : A,
    ((belongs x s) <-> (((Sequence.multiplicity x (to_seq s)) = 1)))
  ).

Parameter fold :
  forall {A : Type},
  forall {B : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall f : A -> B,
  forall m : B -> B -> B,
  forall s : t A,
  forall acc : B,
  B.

Axiom fold_def :
  forall {A : Type},
  forall {B : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall f : A -> B,
  forall m : B -> B -> B,
  forall s : set A,
  forall acc : B,
  finite s ->
  comm_monoid m acc ->
  (
    (fold f m s acc) = (
      Sequence.fold_right (fun x : A => fun acc : B => m (f x) acc) (to_seq s) acc
    )
  ).

End _Set.

Parameter map_set :
  forall {A : Type},
  forall {B : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall f : A -> B,
  forall x : A,
  forall y : B,
  A -> B.

Axiom map_set_def :
  forall {A : Type},
  forall {B : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall f : A -> B,
  forall x : A,
  forall y : B,
  ((map_set f x y x) = y).

Axiom map_set_def_neq :
  forall {A : Type},
  forall {B : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall f : A -> B,
  forall x : A,
  forall y : B,
  forall z : A,
  (x <> z) -> ((map_set f x y z) = (f z)).

Module Map.

Definition t  (A : Type) (B : Type) : Type:= map A B.

Parameter domain :
  forall {A : Type},
  forall {B : Type},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall default : B,
  forall m : t A B,
  _Set.t A.

Axiom domain_mem :
  forall {B : Type},
  forall {A : Type},
  forall {Eq_B : EqDecision B},
  forall {Ih_B : Inhabited B},
  forall {Eq_A : EqDecision A},
  forall {Ih_A : Inhabited A},
  forall x : A,
  forall m : A -> B,
  forall default : B,
  ((m x) <> default) -> _Set.belongs x (domain default m).

End Map.

End Stdlib.



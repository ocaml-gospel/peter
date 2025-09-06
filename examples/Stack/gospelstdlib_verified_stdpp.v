Set Implicit Arguments.

Require Stdlib.ZArith.BinInt stdpp.base.

Require Stdlib.ZArith.BinInt.
Require Import Stdlib.ZArith.BinIntDef.
Require Import stdpp.decidable stdpp.list stdpp.gmap stdpp.propset stdpp.option.

Local Open Scope Z_scope.
From Stdlib Require Import BinInt.

Require gospelstdlib_mli_stdpp.

Module Stdlib : gospelstdlib_mli_stdpp.Stdlib.

  Definition sequence A := list A.

  Definition bag A := A -> nat.
  Definition set A := @propset A.
  Definition option A := option A.
  Definition Some A `{EqDecision A} `{Inhabited A} (x : A) := Some x.
  Definition None A `{EqDecision A} `{Inhabited A} := @None A.

  Definition map A B := A -> B.

  Parameter succ : Z -> Z.

  Parameter pred : Z -> Z.

  Parameter neg : Z -> Z.

  Parameter _mod : Z -> Z -> Z.

  Parameter pow : Z -> Z -> Z.

  Parameter abs : Z -> Z.

  Definition min : Z -> Z -> Z := Z.min.

  Definition max : Z -> Z -> Z := Z.max.

  Definition app {A} `{EqDecision A} `{Inhabited A} (s1 : sequence A) (s2 : sequence A) := s1 ++ s2.

  Definition seq_get {A} `{EqDecision A} `{Inhabited A} (s : sequence A) (i : Z) : A :=
    s !!! (Z.to_nat i).

  Definition takeZ {A} (i : Z) (s : sequence A) :=
    take (Z.to_nat i) s.

  Definition dropZ {A} (i : Z) (s : sequence A) := drop (Z.to_nat i) s.

  Definition seq_sub {A} `{EqDecision A} `{Inhabited A} (s : sequence A) (i1 : Z) (i2 : Z) : sequence A :=
    takeZ (i2 - i1) (dropZ i1 s).

  Definition seq_sub_l {A} `{EqDecision A} `{Inhabited A} (s : sequence A) (i : Z) : sequence A :=
    seq_sub s i (Z.of_nat (length s)).

  Definition seq_sub_r {A} `{EqDecision A} `{Inhabited A} (s : sequence A) (i : Z) : sequence A:=
    seq_sub s (0)%Z i.

  Definition neutral_l {A} (f : A -> A -> A) n := forall x, f n x = x.
  Definition neutral_r {A} (f : A -> A -> A) n := forall x, f x n = x.

  Definition monoid {A : Type} `{EqDecision A} `{Inhabited A} (f : A -> A -> A) (neutral : A) :=
    Assoc eq f /\ neutral_l f neutral /\ neutral_r f neutral.

  Lemma monoid_def :
    forall {A : Type},
    forall `{EqDecision A} `{Inhabited A},
    forall f : A -> A -> A,
    forall neutral : A,
      (
        monoid f neutral <-> (
                             (forall x : A,
                                 ((f neutral x = f x neutral) /\ (f x neutral = x))) /\ forall x : A,
                             forall y : A,
                             forall z : A,
                               (f x (f y z) = f (f x y) z)
                           )
      ).
  Proof.
    intros A Ih f neutral.
    unfold monoid, neutral_l, neutral_r.
    split.
    - intros (H1 & H2 & H3). repeat split; try rewrite H2; auto.
    - intros [H1 H2].
      repeat split.
      1: auto.
      all: intros; specialize H1 with x; destruct H1 as [H1 H3]; try rewrite H1; auto.
  Qed.

  Definition comm_monoid {A} `{EqDecision A} `{Inhabited A} (f : A -> A -> A) (n : A) : Prop :=
    monoid f n /\ Comm eq f.

  Lemma comm_monoid_def :
    forall {A : Type},
    forall `{EqDecision A} `{Inhabited A},
    forall f : A -> A -> A,
    forall neutral : A,
      (
        comm_monoid f neutral <-> (
                                  monoid f neutral /\ forall x : A,
                                  forall y : A,
                                    (f x y = f y x)
                                )
      ).
  Proof.
    auto.
  Qed.

  Module Sequence.

    Definition t (A : Type) : Type := sequence A.

    Definition length {A} `{EqDecision A} `{Inhabited A} (s : t A) : Z :=
      Z.of_nat (length s).

    Lemma length_takeZ :
      forall A `{EqDecision A} `{Inhabited A} (s : sequence A) i,
        0 <= i <= length s ->
        length (takeZ i s) = i.
    Proof.
      intros.
      unfold takeZ, length in *.
      rewrite length_take. lia.
    Qed.

    Lemma lookup_takeZ_lt :
      forall A `{EqDecision A} `{Inhabited A} (s : sequence A) l i,
        0 <= i < l ->
        seq_get (takeZ l s) i = seq_get s i.
    Proof.
      intros.
      unfold length, takeZ.
      unfold seq_get.
      rewrite lookup_total_take_lt; auto with lia.
    Qed.

    Lemma lookup_dropZ_lt :
      forall A `{EqDecision A} `{Inhabited A} (s : sequence A) l i,
        0 <= i ->
        0 <= l ->
        seq_get (dropZ l s) i = seq_get s (l + i).
    Proof.
      intros.
      unfold length, dropZ, seq_get.
      rewrite lookup_total_drop.
      rewrite Z2Nat.inj_add; auto with lia.
    Qed.

    Lemma length_dropZ :
      forall A `{EqDecision A} `{Inhabited A} (s : sequence A) i,
        0 <= i <= length s ->
        length (dropZ i s) = length s - i.
    Proof.
      intros.
      unfold dropZ, length, length in *.
      rewrite length_drop. lia.
    Qed.

    Definition in_range {A} `{EqDecision A} `{Inhabited A} (s : t A) (i : Z) :=
      0 <= i < length s.

    Lemma in_range_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
      forall i : Z,
        (in_range s i <-> (((0)%Z <= i) /\ (i < length s))).
    Proof.
      auto.
    Qed.

    Lemma length_nonneg :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
        ((0)%Z <= length s).
    Proof.
      unfold length. unfold length. intros.
      lia.
    Qed.

    Lemma subseq_l :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
      forall i : Z,
        in_range s i -> (seq_sub_l s i = seq_sub s i (length s)).
    Proof.
      auto.
    Qed.

    Lemma subseq_r :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
      forall i : Z,
        in_range s i -> (seq_sub_r s i = seq_sub s (0)%Z i).
    Proof.
      auto.
    Qed.

    Lemma subseq :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
      forall i : Z,
      forall i1 : Z,
      forall i2 : Z,
        (((0)%Z <= i1) /\ ((i1 <= i) /\ ((i < i2) /\ (i2 <= length s)))) ->
        (seq_get s i = seq_get (seq_sub s i1 i2) ((i - i1))).
    Proof.
      intros A Ih Eq s i i1 i2 H.
      unfold length, seq_sub.
      rewrite lookup_takeZ_lt. 2: lia.
      rewrite lookup_dropZ_lt. 2, 3: lia.
      f_equal. lia.
    Qed.

    Lemma subseq_len :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
      forall i1 : Z,
      forall i2 : Z,
        (((0)%Z <= i1) /\ ((i1 <= i2) /\ (i2 < length s))) ->
        (length (seq_sub s i1 i2) = (i2 - i1)).
    Proof.
      intros.
      unfold seq_sub.
      rewrite length_takeZ. 1: lia.
      rewrite length_dropZ; lia.
    Qed.

    Lemma lengthZ_app :
      forall {A} `{EqDecision A} `{Inhabited A} (l1 : sequence A) l2,
        length (l1 ++ l2) = length l1 + length l2.
    Proof.
      intros.
      unfold length.
      rewrite length_app.
      lia.
    Qed.

    Definition empty {A} `{EqDecision A} `{Inhabited A} := @nil A.

    Lemma empty_length :
      forall {A : Type},
      forall {Eq: EqDecision A} `{Ih : Inhabited A},
        (@length A Eq Ih empty = (0)%Z).
    Proof.
      auto.
    Qed.

    Fixpoint init_aux {A} (n : nat) (f : Z -> A) : sequence A :=
      match n with
      |O => nil
      |S n' => (init_aux n' f) ++ [f (Z.of_nat n')] end.

    Definition init {A} `{EqDecision A} `{Inhabited A} (n : Z) (f : Z -> A) : sequence A :=
      if decide (n < 0) then nil else
        init_aux (Z.to_nat n) f.

    Lemma init_aux_length :
      forall {A} `{EqDecision A} `{Inhabited A} n (f : Z -> A),
        Datatypes.length (init_aux n f) = n.
    Proof.
      intros. intros.
      induction n as [|n' Ih].
      + auto.
      + simpl. rewrite length_app. rewrite Ih.
        unfold length. simpl.
        lia.
    Qed.

    Lemma init_aux_lengthZ :
      forall A `{EqDecision A} `{Inhabited A} n (f : Z -> A),
        length (init_aux n f) = Z.of_nat n.
    Proof.
      intros. unfold length. rewrite init_aux_length. auto.
    Qed.

    Lemma init_length :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall n : Z,
      forall f : Z -> A,
        (n >= (0)%Z) -> (length (init n f) = n).
    Proof.
      intros.
      unfold init.
      rewrite decide_False. 2: lia.
      rewrite init_aux_lengthZ. lia.
    Qed.

    Lemma lookup_total_app_lZ :
      forall {A} `{EqDecision A} `{Inhabited A} (s1 : sequence A) (s2 : sequence A) i,
        0 <= i < length s1 ->
        seq_get (s1 ++ s2) i = seq_get s1 i.
    Proof.
      intros.
      unfold seq_get, length in *.
      rewrite lookup_total_app_l; auto with lia.
    Qed.

    Lemma lookup_total_app_rZ :
      forall {A} `{EqDecision A} `{Inhabited A} (s1 : sequence A) (s2 : sequence A) i,
        length s1 <= i < length s1 + length s2 ->
        seq_get (s1 ++ s2) i = seq_get s2 (i - length s1).
    Proof.
      intros.
      unfold seq_get, length in *.
      rewrite lookup_total_app_r. 2: lia.
      f_equal.
      rewrite Z2Nat.inj_sub; lia.
    Qed.

    Lemma init_i :
      forall {A} (n : nat) (i : Z) (f : Z -> A),
      forall `{EqDecision A} `{Inhabited A},
        0 <= i ->
        i < Z.of_nat n ->
        seq_get (init_aux n f) i = f i.
    Proof.
      intros A n i f Eq Inh H1 H2.
      induction n as [|n' Ih].
      - lia.
      - simpl.
        destruct (decide (i < Z.of_nat n')).
        + rewrite lookup_total_app_lZ.
          2: unfold length; rewrite init_aux_length; lia.
          auto.
        +
          cut (i = Z.of_nat n'). 2: lia.
          intros P.
          rewrite lookup_total_app_rZ; unfold length; rewrite init_aux_length. 2: simpl; lia.
          subst.
          rewrite Z.sub_diag.
          auto.
    Qed.

    Lemma init_elems :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall n : Z,
      forall f : Z -> A,
      forall i : Z,
        (((0)%Z <= i) /\ (i < n)) -> (seq_get (init n f) i = f i).
    Proof.
      intros.
      unfold init.
      rewrite decide_False. 2: lia.
      apply init_i; lia.
    Qed.

    Definition singleton {A} `{EqDecision A} `{Inhabited A} (x : A) := [x].

    Lemma singleton_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall x : A,
      forall f : Z -> A,
        (f (0)%Z = x) -> (singleton x = init (1)%Z f).
    Proof.
      intros A Eq Ih x f H.
      rewrite <- H. auto.
    Qed.

    Definition cons {A} `{EqDecision A} `{Inhabited A} (x : A) s := x :: s.

    Definition cons_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall x : A,
      forall s : sequence A,
        (cons x s = app (singleton x) s).
    Proof.
      list_simplifier. auto.
    Qed.

    Definition snoc {A} `{EqDecision A} `{Inhabited A} s (x : A) := s ++ [x].

    Lemma snoc_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
      forall x : A,
        (snoc s x = app s (singleton x)).
    Proof.
      auto.
    Qed.

    Definition hd {A} `{EqDecision A} `{Inhabited A} (s : sequence A) := s !!! 0%nat.

    Definition hd_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
        (hd s = seq_get s (0)%Z).
    Proof.
      auto.
    Qed.

    Definition tl {A} `{EqDecision A} `{Inhabited A} (s : sequence A) := seq_sub_l s (1)%Z.

    Lemma tl_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
        (tl s = seq_sub_l s (1)%Z).
    Proof.
      auto.
    Qed.

    Definition append {A} `{EqDecision A} `{Inhabited A} (s1 : sequence A) s2 := s1 ++ s2.

    Lemma append_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s1 : sequence A,
      forall s2 : sequence A,
        (append s1 s2 = app s1 s2).
    Proof.
      auto.
    Qed.

    Lemma append_length :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
      forall s' : sequence A,
        (length (app s s') = (length s + length s')).
    Proof.
      intros.
      unfold app.
      rewrite lengthZ_app. auto.
    Qed.

    Lemma append_elems_left :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
      forall s' : sequence A,
      forall i : Z,
        in_range s i -> (seq_get (app s s') i = seq_get s i).
    Proof.
      intros.
      unfold app.
      rewrite lookup_total_app_lZ; auto.
    Qed.

    Lemma append_elems_right :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
      forall s' : sequence A,
      forall i : Z,
        ((length s <= i) /\ (i < (length s + length s'))) ->
        (seq_get (app s s') i = seq_get s' ((i - length s))).
    Proof.
      intros.
      unfold app. rewrite lookup_total_app_rZ; auto.
    Qed.

    Lemma EM : ¬ (exists P, P /\ ¬ P).
    Proof.
      intros H.
      destruct H as [P H].
      destruct H.
      apply H0.
      apply H.
    Qed.

    Definition multiplicity {A} `{EqDecision A} `{Inhabited A} x (s : sequence A) :=
      length (filter (λ y, x = y) s).

    Lemma mult_empty :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall x : A,
        (multiplicity x empty = (0)%Z).
    Proof.
      unfold multiplicity, empty.
      intros.
      rewrite filter_nil.
      apply empty_length.
    Qed.

    Lemma lengthZ_cons :
      forall A `{EqDecision A} `{Inhabited A} s (x :  A),
        length (x :: s) = 1 + length s.
    Proof.
      intros.
      unfold length.
      simpl. lia.
    Qed.

    Lemma mult_cons :
      forall {A : Type},
      forall {E : EqDecision A},
      forall `{Inhabited A},
      forall s : sequence A,
      forall x : A,
        (((1)%Z + multiplicity x s) = multiplicity x (cons x s)).
    Proof.
      unfold multiplicity, cons.
      intros A I E s x.
      rewrite filter_cons.
      rewrite decide_True. 2: auto.
      rewrite lengthZ_cons. auto.
    Qed.

    Lemma mult_cons_neutral :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
      forall x1 : A,
      forall x2 : A,
        (x1 <> x2) -> (multiplicity x1 s = multiplicity x1 (cons x2 s)).
    Proof.
      intros.
      unfold multiplicity, cons.
      rewrite filter_cons.
      rewrite decide_False; auto.
    Qed.

    Lemma lengthZ_filter :
      forall {A} `{EqDecision A} `{Inhabited A} (s : sequence A) P `{forall x, Decision (P x)},
        length (filter P s) <= length s.
    Proof.
      intros.
      unfold length.
      rewrite <- Nat2Z.inj_le.
      apply length_filter.
    Qed.

    Lemma mult_length :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall x : A,
      forall s : sequence A,
        (((0)%Z <= multiplicity x s) /\ (multiplicity x s <= length s)).
    Proof.
      intros. unfold multiplicity.
      split.
      - unfold length. lia.
      - apply lengthZ_filter.
    Qed.

    Definition mem {A} `{EqDecision A} `{Inhabited A} (x : A) (s : sequence A) :=
      x ∈ s.

    Definition belongs {A} `{EqDecision A} `{Inhabited A} (x : A) s := mem x s.

    Lemma mem_fun_def :
      forall {A : Type},
      forall {Eq_A : EqDecision A},
      forall {Ih_A : Inhabited A},
      forall x : A,
      forall s : sequence A,
        ((belongs x s) <-> (mem x s)).
    Proof.
      tauto.
    Qed.

    Definition neg_belongs {A} `{EqDecision A} `{Inhabited A} (x : A) s := not (belongs x s).

    Lemma nmem_def :
      forall {A : Type},
      forall {Eq_A : EqDecision A},
      forall {Ih_A : Inhabited A},
      forall s : sequence A,
      forall x : A,
        ((neg_belongs x s) <-> (not (belongs x s))).
    Proof.
      unfold neg_belongs. tauto.
    Qed.

    Lemma mem_def :
      forall {A : Type},
      forall `{EqDecision A},
      forall `{Inhabited A},
      forall s : sequence A,
      forall x : A,
        (mem x s <-> (multiplicity x s > (0)%Z)).
    Proof.
      intros A I E s x.
      unfold mem.
      unfold multiplicity.
      split; intros H.
      - induction s as [|y t Ih].
        + apply not_elem_of_nil in H. tauto.
        + rewrite filter_cons.
          destruct (decide (x = y)).
          * rewrite lengthZ_cons.
            unfold length. lia.
          * apply Ih.
            rewrite elem_of_cons in H.
            destruct H.
            1: contradiction.
            auto.
      - induction s as [|y t Ih].
        + rewrite filter_nil in H.
          rewrite @empty_length with (A:=A) in H.
          lia.
        + rewrite filter_cons in H.
          destruct (decide (x = y)); rewrite elem_of_cons; auto.
    Qed.

    Definition Forall {A} `{EqDecision A} `{Inhabited A} (P : A -> Prop) `{forall x, Decision (P x)} (s : sequence A) :=
      Forall P s.

    Lemma forall_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall p : A -> Prop,
      forall `{forall x, Decision (p x)},
      forall s : sequence A,
        (Forall p s <-> forall x : A, mem x s -> p x).
    Proof.
      intros.
      unfold Forall, mem.
      apply list.Forall_forall.
    Qed.

    Definition Exists {A} `{EqDecision A} `{Inhabited A} (P : A -> Prop) `{forall x, Decision (P x)} (s : sequence A) :=
      Exists P s.

    Lemma exists_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall p : A -> Prop,
      forall `{forall x, Decision (p x)},
      forall s : sequence A,
        (Exists p s <-> exists x : A, (mem x s /\ p x)).
    Proof.
      intros.
      unfold Exists.
      apply list.Exists_exists.
    Qed.

    Definition map {A} {B} `{EqDecision A} `{Inhabited A} `{EqDecision B} `{Inhabited B} := @List.map A B.

    Lemma empty_lengthZ :
      forall A `{Eq : EqDecision A} `{Ih : Inhabited A},
        @length A Eq Ih (@nil A) = 0.
    Proof.
      intros.
      unfold length.
      rewrite list.length_nil.
      auto.
    Qed.

    Lemma cons_lengthZ :
      forall A `{EqDecision A} `{Inhabited A} s (x : A),
        length (x :: s) = 1 + length s.
    Proof.
      intros.
      unfold length.
      rewrite list.length_cons. lia.
    Qed.

    Lemma cons_seq_get :
      forall A `{EqDecision A} `{Inhabited A} s (x : A) i,
        0 < i ->
        seq_get (x :: s) i = seq_get s (i - 1).
    Proof.
      intros.
      unfold seq_get.
      rewrite lookup_total_cons_ne_0.
      1: f_equal. all: lia.
    Qed.

    Lemma map_elems :
      forall {B : Type},
      forall {A : Type},
      forall `{EqDecision B} `{Inhabited B},
      forall `{EqDecision A} `{Inhabited A},
      forall i : Z,
      forall f : B -> A,
      forall s : sequence B,
        in_range s i -> (seq_get (map f s) i = f (seq_get s i)).
    Proof.
      unfold in_range.
      intros B A Eq_B Ih_B Eq_A Ih_A i f s.
      generalize dependent i.
      induction s as [|h t Ih]; intros i H.
      - rewrite (@empty_lengthZ B Eq_B Ih_B) in H. lia.
      - rewrite cons_lengthZ in H.
        simpl.
        destruct (decide (i = 0)) as [E | E].
        + rewrite E.
          unfold seq_get. auto.
        + repeat (rewrite cons_seq_get; try lia).
          apply Ih. lia.
    Qed.

    Lemma map_length :
      forall {B : Type},
      forall {A : Type},
      forall {Eq_B : EqDecision B},
      forall {Ih_B : Inhabited B},
      forall {Eq_A : EqDecision A},
      forall {Ih_A : Inhabited A},
      forall f : B -> A,
      forall s : sequence B,
        ((length (map f s)) = (length s)).
    Proof.
      intros.
      unfold length, map.
      by rewrite length_map.
    Qed.

    Definition filter A `{EqDecision A} `{Inhabited A}
      (P : A -> Prop) `{D : forall x, Decision (P x)} s :=
      list_filter P D s.

    Lemma filter_elems :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall f : A -> Prop,
      forall `{forall x, Decision (f x)},
      forall s : sequence A,
      forall x : A,
        mem x s -> f x -> mem x (filter f s).
    Proof.
      intros.
      unfold mem, filter.
      apply list_elem_of_filter.
      auto.
    Qed.

    Definition filter_map {A} {B} `{EqDecision A} `{Inhabited A} `{EqDecision B} `{Inhabited B} (f : A -> option B) s :=
      map
        (λ x, match f x with |Datatypes.Some x' => x' |Datatypes.None => inhabitant end)
        (filter (λ x, f x <> Datatypes.None) s).

    Lemma map_mem :
      forall {A} `{EqDecision A} `{Inhabited A} {B} `{EqDecision B} `{Inhabited B} (s : sequence A) (f : A -> B) (x : A),
        x ∈ s -> f x ∈ map f s.
    Proof.
      intros A B EqA EqB IhA IhB s f x.
      generalize dependent x. induction s as [|h t Ih]; intros x H1.
      + apply not_elem_of_nil in H1. tauto.
      + simpl. apply elem_of_cons.
        destruct (decide (x = h)) as [E | E].
        * left. f_equal. auto.
        * right. apply elem_of_cons in H1.
          destruct H1. 1: tauto.
          auto.
    Qed.

    Lemma filter_map_elems :
      forall {B : Type},
      forall {A : Type},
      forall `{EqDecision B},
      forall {Ih_B : Inhabited B},
      forall `{EqDecision A} `{Inhabited A},
      forall f : B -> option A,
      forall s : sequence B,
      forall y : A,
        ((exists x : B, ((f x = Some y) /\ mem x s)) <-> mem y (filter_map f s)).
    Proof.
      intros B a IB IA EqA EqB f s y.
      unfold mem, filter_map.
      remember (λ x0 : B,
                   match f x0 with
                   | Datatypes.Some x' => x'
                   | Datatypes.None => inhabitant
                   end) as f' eqn:E.
      split.
      - intros [x [H1 H2]].
        cut (y = f' (x)). 2: subst; rewrite H1; auto.
        intros H.
        rewrite H.
        apply map_mem.
        unfold filter.
        apply list_elem_of_filter.
        rewrite H1. split; auto.
      - intros H1.
        induction s as [|h t Ih].
        + apply not_elem_of_nil in H1. tauto.
        + simpl in H1.
          destruct (decide (f h ≠ Datatypes.None)).
          * simpl in H1.
            apply elem_of_cons in H1.
            destruct H1 as [H1 | H1].
            { exists h.
              split.
              - subst. destruct (f h). 1: auto. tauto.
              - apply elem_of_cons. auto. }
            { apply Ih in H1 as [x [H1 H2]]. exists x.
              split. 2: apply elem_of_cons. all: auto. }
          * apply Ih in H1 as [x [H1 H2]]. exists x.
            split. 2: apply elem_of_cons. all: auto.
    Qed.

    Definition get {A} `{EqDecision A} `{Inhabited A} s i : A := seq_get s i.

    Lemma get_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
      forall i : Z,
        (get s i = seq_get s i).
    Proof.
      auto.
    Qed.

    Fixpoint set_aux {A} (s : sequence A) (n : nat) (x : A) : sequence A :=
      match s, n with
      |nil, _ => inhabitant
      |_ :: t, O => x :: t
      |e :: t, S n' => e :: set_aux t n' x
      end.

    Definition set {A} `{EqDecision A} `{Inhabited A} (s : sequence A) (n : Z) (x : A) : sequence A :=
      if decide (n < 0) then inhabitant else set_aux s (Z.to_nat n) x.

    Lemma set_elem_nat :
      forall {A} `{EqDecision A} `{Inhabited A} (x : A) i s,
        (i < List.length s)%nat -> (set_aux s i x) !!! i = x.
    Proof.
      intros A I x.
      induction i as [|n Ih]; intros s H1; destruct s as [|h t]. 2: auto. 1, 2: rewrite length_nil in H1; lia.
      simpl. apply Ih. simpl in H1.
      lia.
    Qed.

    Lemma set_elem :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
      forall i : Z,
      forall x : A,
        in_range s i -> (seq_get (set s i x) i = x).
    Proof.
      unfold set, in_range.
      intros A E I s i x H1.
      rewrite decide_False. 2: lia.
      apply set_elem_nat. unfold length in H1. lia.
    Qed.

    Lemma set_elem_other_nat :
      forall {A} `{EqDecision A} `{Inhabited A} (x : A) s i1 i2,
        i1 <> i2 ->
        (i1 < List.length s)%nat ->
        (i2 < List.length s)%nat ->
        (set_aux s i1 x) !!! i2 = s !!! i2.
    Proof.
      intros A E I x s.
      induction s as [|h t Ih]; intros i1 i2 H1 H2.
      - rewrite length_nil in H2. lia.
      - intros H3. destruct i1 as [| i1]; destruct i2 as [| i2].
        2, 3: auto.
        * contradiction.
        * simpl in H2, H3.
          apply Ih.
          2, 3: lia.
          auto.
    Qed.

    Lemma set_elem_other :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
      forall i1 : Z,
      forall i2 : Z,
      forall x : A,
        (i1 <> i2) ->
        in_range s i1 ->
        in_range s i2 -> (seq_get (set s i1 x) i2 = seq_get s i2).
    Proof.
      unfold seq_get, in_range, set.
      intros A E Ih s i1 i2 x H1 H2 H3.
      rewrite decide_False. 2: lia.
      unfold length in *.
      apply set_elem_other_nat; lia.
    Qed.

    Definition rev {A} `{EqDecision A} `{Inhabited A} := @reverse A.

    Lemma rev_length :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
        (length s = length (rev s)).
    Proof.
      intros.
      unfold rev, length.
      rewrite length_reverse.
      auto.
    Qed.

    Lemma rev_elems :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall i : Z,
      forall s : sequence A,
        in_range s i ->
        (seq_get (rev s) i = seq_get s (((length s - (1)%Z) - i))).
    Proof.
      unfold in_range, seq_get, rev, length.
      intros A E I i s H1.
      apply Some_inj.
      rewrite <- list_lookup_lookup_total_lt. 2: rewrite length_reverse; lia.
      rewrite <- list_lookup_lookup_total_lt. 2: lia.
      rewrite Z2Nat.inj_sub. 2: lia.
      rewrite Z2Nat.inj_sub. 2: lia.
      rewrite Nat2Z.id.
      cut ((Datatypes.length s - Z.to_nat 1 - Z.to_nat i)%nat = (Datatypes.length s - S (Z.to_nat i))%nat). 2: lia.
      intros. subst. rewrite H.
      apply reverse_lookup. lia.
    Qed.

    Lemma seq_get_cons2 :
      forall {A} `{EqDecision A} `{Inhabited A} s i (x : A),
        0 <= i < length s ->
        seq_get s i = seq_get (x :: s) (i + 1).
    Proof.
      unfold seq_get, in_range.
      intros.
      rewrite lookup_total_cons_ne_0. 2: lia.
      f_equal. lia.
    Qed.

    Lemma extensionality :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s1 : sequence A,
      forall s2 : sequence A,
        (length s1 = length s2) ->
        (forall i : Z, in_range s1 i -> (seq_get s1 i = seq_get s2 i)) ->
        (s1 = s2).
    Proof.
      intros A E I s1.
      induction s1 as [|h s1 Ih]; intros s2 H1.
      - rewrite (@empty_lengthZ A E I) in H1.
        symmetry.
        apply length_zero_iff_nil.
        unfold length in H1. lia.
      - intros H2.
        destruct s2 as [|h' s2].
        + rewrite (@empty_lengthZ A E I) in H1.
          rewrite cons_lengthZ in H1.
          cut (0 <= length s1). 2: apply length_nonneg.
          intros. lia.
        + cut (h = h').
          * intros H3.
            subst.
            f_equal.
            repeat (rewrite cons_lengthZ in H1).
            apply Ih. 1: lia.
            intros i H3.
            unfold in_range in *.
            rewrite seq_get_cons2 with s1 i h'. 2: auto.
            rewrite seq_get_cons2 with s2 i h'. 2: lia.
            apply H2.
            rewrite lengthZ_cons. lia.
          * specialize H2 with 0.
            unfold seq_get in H2.
            apply H2. unfold in_range. rewrite lengthZ_cons.
            cut (0 <= length s1). 2: apply length_nonneg.
            lia.
    Qed.

    Definition fold_left A B `{EqDecision A} `{Inhabited A} `{EqDecision B} `{Inhabited B} (f : A -> B -> A) (x : A) (s : sequence B) : A  :=
      fold_left f s x.

    Lemma fold_left_empty :
      forall {B : Type},
      forall {A : Type},
      forall `{EqDecision B} {Ih_B : Inhabited B},
      forall `{EqDecision A} `{Inhabited A},
      forall f : A -> B -> A,
      forall acc : A,
        (fold_left f acc empty = acc).
    Proof.
      auto.
    Qed.

    Lemma fold_left_cons :
      forall {B : Type},
      forall {A : Type},
      forall `{EqDecision B} {Ih_B : Inhabited B},
      forall `{EqDecision A} `{Inhabited A},
      forall f : A -> B -> A,
      forall acc : A,
      forall x : B,
      forall l : sequence B,
        (fold_left f acc (cons x l) = fold_left f (f acc x) l).
    Proof.
      auto.
    Qed.

    Definition fold_right {A : Type} {B : Type} `{EqDecision A} `{Inhabited A} `{EqDecision B} `{Inhabited B}
      (f : A -> B -> B) (s : t A) (x : B) : B := fold_right f x s.

    Lemma fold_right_empty :
      forall {B : Type},
      forall {A : Type},
      forall `{EqDecision B} `{Inhabited B},
      forall `{EqDecision A} `{Inhabited A},
      forall acc : A,
      forall f : B -> A -> A,
        (fold_right f empty acc = acc).
    Proof.
      auto.
    Qed.

    Lemma fold_right_cons :
      forall {B : Type},
      forall {A : Type},
      forall `{EqDecision B} `{Inhabited B},
      forall `{EqDecision A} `{Inhabited A},
      forall acc : A,
      forall f : B -> A -> A,
      forall x : B,
      forall l : sequence B,
        (fold_right f (cons x l) acc = f x (fold_right f l acc)).
    Proof.
      auto.
    Qed.

    Definition permut {A} `{EqDecision A} `{Inhabited A} (s1 : sequence A) (s2 : sequence A) :=
      (forall x : A, (mem x s1) <-> (mem x s2)).

    Lemma permut_mem :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s1 : sequence A,
      forall s2 : sequence A,
        permut s1 s2 ->
        (forall x : A, (mem x s1) <-> (mem x s2)).
    Proof.
      tauto.
    Qed.

    Definition permut_sub {A} `{EqDecision A} `{Inhabited A}
      (s1 : sequence A) (s2 : sequence A) (i : Z) (j : Z) :=
      permut (seq_sub s1 i j) (seq_sub s2 i j) /\
        (seq_sub_r s1 i) = (seq_sub_r s2 i) /\
        (seq_sub_l s1 j) = (seq_sub_l s2 j).

    Lemma permut_sub_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s1 : sequence A,
      forall s2 : sequence A,
      forall i : Z,
      forall j : Z,
        permut (seq_sub s1 i j) (seq_sub s2 i j) ->
        (seq_sub_r s1 i = seq_sub_r s2 i) ->
        (seq_sub_l s1 j = seq_sub_l s2 j) -> permut_sub s1 s2 i j.
    Proof.
      unfold permut_sub. tauto.
    Qed.

  End Sequence.

  Module Bag.

    Definition t := bag.

    Definition multiplicity {A} `{EqDecision A} `{Inhabited A} (x : A) (b : bag A) := Z.of_nat (b x).

    Lemma well_formed :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall b : bag A,
      forall x : A,
        (multiplicity x b >= (0)%Z).
    Proof.
      unfold multiplicity. lia.
    Qed.

    Definition empty {A} `{EqDecision A} `{Inhabited A} := λ (_ : A), 0%nat.

    Lemma empty_mult :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall x : A,
        (multiplicity x empty = (0)%Z).
    Proof.
      auto.
    Qed.

    Definition init {A} `{EqDecision A} `{Inhabited A} (f : A -> Z) := λ x, Z.to_nat (f x).

    Lemma init_axiom :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall f : A -> Z,
      forall x : A,
        (max (0)%Z (f x) = multiplicity x (init f)).
    Proof.
      unfold multiplicity, init, max. lia.
    Qed.

    Definition mem {A} `{EqDecision A} `{Inhabited A} (x : A) b := multiplicity x b > 0.

    Definition belongs {A} `{EqDecision A} `{Inhabited A} (x : A) s := mem x s.

    Lemma mem_fun_def :
      forall {A : Type},
      forall {Eq_A : EqDecision A},
      forall {Ih_A : Inhabited A},
      forall x : A,
      forall s : bag A,
        ((belongs x s) <-> (mem x s)).
    Proof.
      tauto.
    Qed.

    Definition neg_belongs {A} `{EqDecision A} `{Inhabited A} (x : A) s := not (belongs x s).

    Lemma nmem_def :
      forall {A : Type},
      forall {Eq_A : EqDecision A},
      forall {Ih_A : Inhabited A},
      forall s : bag A,
      forall x : A,
        ((neg_belongs x s) <-> (not (belongs x s))).
    Proof.
      unfold neg_belongs. tauto.
    Qed.

    Lemma mem_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall x : A,
      forall b : bag A,
        (mem x b <-> (multiplicity x b > (0)%Z)).
    Proof.
      tauto.
    Qed.

    Definition add {A} `{EqDecision A} `{Inhabited A} (x : A) b := (λ y, if decide (x = y) then b y + 1 else  b y)%nat.

    Lemma add_mult_x :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall b : bag A,
      forall x : A,
        (multiplicity x (add x b) = ((1)%Z + multiplicity x b)).
    Proof.
      intros.
      unfold multiplicity, add.
      rewrite decide_True.
      + lia.
      + auto.
    Qed.

    Lemma add_mult_neg_x :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall x : A,
      forall y : A,
      forall b : bag A,
        (x <> y) -> (multiplicity y (add x b) = multiplicity y b).
    Proof.
      intros.
      unfold multiplicity, add.
      rewrite decide_False; auto.
    Qed.

    Definition singleton {A} `{EqDecision A} `{Inhabited A} (x : A) := λ y, if decide (x = y) then 1%nat else 0%nat.

    Definition singleton_set {A} `{EqDecision A} `{Inhabited A} (x : A) := singleton x.

    Lemma singleton_fun_def :
      forall {A : Type},
      forall {Eq_A : EqDecision A},
      forall {Ih_A : Inhabited A},
      forall x : A,
        ((singleton_set x) = (singleton x)).
    Proof.
      tauto.
    Qed.

    Definition singleton_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall x : A,
        (singleton x = add x empty).
    Proof.
      auto.
    Qed.

    Definition remove {A} `{EqDecision A} `{Inhabited A} (x : A) (s : bag A) :=
      λ y, if decide (x = y) then (s y - 1)%nat else s y.

    Lemma remove_mult_x :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall b : bag A,
      forall x : A,
        (multiplicity x (remove x b) = max (0)%Z ((multiplicity x b - (1)%Z))).
    Proof.
      intros.
      unfold multiplicity, remove, max.
      rewrite decide_True. lia. auto.
    Qed.

    Lemma remove_mult_neg_x :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall x : A,
      forall y : A,
      forall b : bag A,
        (x <> y) -> (multiplicity y (remove x b) = multiplicity y b).
    Proof.
      intros.
      unfold multiplicity, remove, max.
      rewrite decide_False. lia. auto.
    Qed.

    Definition union {A} `{EqDecision A} `{Inhabited A} (b1 : bag A) b2 := λ y, (Nat.max (b1 y) (b2 y))%nat.

    Lemma union_all :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall b : bag A,
      forall b' : bag A,
      forall x : A,
        (
          max (multiplicity x b) (multiplicity x b') = multiplicity x (union b b')
        ).
    Proof.
      unfold max, multiplicity, union.
      lia.
    Qed.

    Definition sum {A} `{EqDecision A} `{Inhabited A} (b1 : bag A) b2 := λ y, (b1 y + b2 y)%nat.

    Lemma sum_all :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall b : bag A,
      forall b' : bag A,
      forall x : A,
        ((multiplicity x b + multiplicity x b') = multiplicity x (sum b b')).
    Proof.
      unfold multiplicity, sum. lia.
    Qed.

    Definition inter {A} `{EqDecision A} `{Inhabited A} (b1 : bag A) b2 := λ y, (b1 y `min` b2 y)%nat.

    Lemma inter_all :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall b : bag A,
      forall b' : bag A,
      forall x : A,
        (
          min (multiplicity x b) (multiplicity x b') = multiplicity x (inter b b')
        ).
    Proof.
      unfold multiplicity, inter.
      unfold min.
      lia.
    Qed.

    Definition disjoint {A} `{EqDecision A} `{Inhabited A} (b1 : bag A) b2 := forall x, mem x b1 -> ~ mem x b2.

    Lemma disjoint_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall b : bag A,
      forall b' : bag A,
        (disjoint b b' <-> forall x : A, mem x b -> not (mem x b')).
    Proof.
      auto.
    Qed.

    Definition diff {A} `{EqDecision A} `{Inhabited A} (b1 : bag A) (b2 : bag A) := λ y, (b1 y - b2 y)%nat.

    Lemma diff_all :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall b : bag A,
      forall b' : bag A,
      forall x : A,
        (
          max (0)%Z ((multiplicity x b - multiplicity x b')) = multiplicity x (
                                                                   diff b b'
                                                                 )
        ).
    Proof.
      unfold max, multiplicity, diff.
      lia.
    Qed.

    Definition subset {A} `{EqDecision A} `{Inhabited A} (b1 : bag A) (b2 : bag A) :=
      forall x, (b1 x <= b2 x)%nat.

    Lemma subset_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall b : bag A,
      forall b' : bag A,
        (subset b b' <-> forall x : A, (multiplicity x b <= multiplicity x b')).
    Proof.
      intros A E I b b'.
      unfold multiplicity, subset.
      split; intros H x; specialize H with x; lia.
    Qed.

    Definition filter {A} `{EqDecision A} `{Inhabited A} (P : A -> Prop) `{forall x, Decision (P x)} (b1 : bag A) :=
      λ x, if decide (P x) then b1 x else 0%nat.

    Lemma filter_mem :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall b : bag A,
      forall x : A,
      forall f : A -> Prop,
      forall `{forall x, Decision (f x)},
        f x -> (multiplicity x (filter f b) = multiplicity x b).
    Proof.
      intros.
      unfold filter.
      unfold multiplicity.
      rewrite decide_True; auto.
    Qed.

    Lemma filter_mem_neg :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall b : bag A,
      forall x : A,
      forall f : A -> Prop,
      forall `{forall x, Decision (f x)},
        not (f x) -> (multiplicity x (filter f b) = (0)%Z).
    Proof.
      intros.
      unfold multiplicity, filter.
      rewrite decide_False; auto.
    Qed.

    Parameter cardinal :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
        t A -> Z.

    Parameter finite :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
        t A -> Prop.

    Axiom finite_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall b : bag A,
        (
          finite b <-> exists s : sequence A,
          forall x : A,
            mem x b -> Sequence.mem x s
        ).

    Axiom card_nonneg :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall b : bag A,
        (cardinal b >= (0)%Z).

    Axiom card_empty :
      forall {A : Type},
      forall {E: EqDecision A} {I:Inhabited A},
        (@cardinal A E I empty = (0)%Z).

    Axiom card_singleton :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall x : A,
        (cardinal (singleton x) = (1)%Z).

    Axiom card_union :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall b1 : bag A,
      forall b2 : bag A,
        finite b1 ->
        finite b2 -> (cardinal (union b1 b2) = (cardinal b1 + cardinal b2)).

    Axiom card_add :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall x : A,
      forall b : bag A,
        finite b -> (cardinal (add x b) = (cardinal b + (1)%Z)).

    Axiom card_map :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall f : A -> Prop,
      forall `{forall x, Decision (f x)},
      forall b : bag A,
        finite b -> (cardinal (filter f b) <= cardinal b).

    Parameter of_seq :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
        Sequence.t A -> t A.

    Axiom of_seq_multiplicity :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
      forall x : A,
        (Sequence.multiplicity x s = multiplicity x (of_seq s)).
  End Bag.

  Module _Set.

    Definition t := set.

    Definition empty {A} `{EqDecision A} `{Inhabited A} : set A := ∅.

    Definition mem {A} `{EqDecision A} `{Inhabited A} (x : A) (s : set A) :=
      x ∈ s.

    Definition belongs {A} `{EqDecision A} `{Inhabited A} (x : A) s := mem x s.

    Lemma mem_fun_def :
      forall {A : Type},
      forall {Eq_A : EqDecision A},
      forall {Ih_A : Inhabited A},
      forall x : A,
      forall s : set A,
        ((belongs x s) <-> (mem x s)).
    Proof.
      tauto.
    Qed.

    Definition neg_belongs {A} `{EqDecision A} `{Inhabited A} (x : A) s := not (belongs x s).

    Lemma nmem_def :
      forall {A : Type},
      forall {Eq_A : EqDecision A},
      forall {Ih_A : Inhabited A},
      forall s : set A,
      forall x : A,
        ((neg_belongs x s) <-> (not (belongs x s))).
    Proof.
      unfold neg_belongs. tauto.
    Qed.

    Lemma empty_mem :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall x : A,
        not (mem x empty).
    Proof.
      intros.
      unfold empty. unfold mem.
      apply not_elem_of_empty.
    Qed.

    Definition add {A} `{EqDecision A} `{Inhabited A} (x : A) (s : set A) := {[ x ]} ∪ s.

    Lemma add_mem :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
      forall x : A,
        mem x (add x s).
    Proof.
      intros.
      unfold mem, add.
      apply elem_of_union_l.
      by apply elem_of_singleton.
    Qed.

    Lemma add_mem_neq :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
      forall x : A,
      forall y : A,
        (x <> y) -> (mem x s <-> mem x (add y s)).
    Proof.
      intros A I s x y H1.
      unfold mem, add.
      split.
      + intros. by apply elem_of_union_r.
      + intros H2. inversion H2 as [H3 | H3].
        * by apply elem_of_singleton in H3.
        * auto.
    Qed.


    Definition singleton {A} `{EqDecision A} `{Inhabited A} (x : A) : set A := add x empty.

    Definition singleton_set {A} `{EqDecision A} `{Inhabited A} (x : A) := singleton x.

    Lemma singleton_def :
      ∀ (A : Type) (Eq_A : EqDecision A) (Ih_A : Inhabited A) (x : A),
        singleton_set x = add x empty.
    Proof.
      unfold singleton_set, singleton, add, empty.
      tauto.
    Qed.

    Lemma singleton_fun_def :
      forall {A : Type},
      forall {Eq_A : EqDecision A},
      forall {Ih_A : Inhabited A},
      forall x : A,
        ((singleton_set x) = (singleton x)).
    Proof.
      tauto.
    Qed.

    Definition remove {A} `{EqDecision A} `{Inhabited A} (x : A) (s : set A) : set A := s ∖ {[ x ]}.

    Lemma remove_mem :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
      forall x : A,
        not (mem x (remove x s)).
    Proof.
      unfold mem, remove.
      intros A E I s x H1.
      apply elem_of_difference in H1 as [_ H1].
      apply H1. by apply elem_of_singleton.
    Qed.

    Lemma remove_mem_neq :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
      forall x : A,
      forall y : A,
        (x <> y) -> (mem x s <-> mem x (remove y s)).
    Proof.
      unfold mem, remove.
      intros.
      split; intros H1.
      + apply elem_of_difference. split; auto.
      + by apply elem_of_difference in H1 as [H1 _].
    Qed.


    Definition union {A} `{EqDecision A} `{Inhabited A} (s1 : set A) s2 := s1 ∪ s2.

    Lemma union_mem :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
      forall s' : set A,
      forall x : A,
        (mem x s \/ mem x s') -> mem x (union s s').
    Proof.
      auto.
    Qed.

    Lemma union_mem_neg :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
      forall s' : set A,
      forall x : A,
        not (mem x s) -> not (mem x s') -> not (mem x (union s s')).
    Proof.
      unfold mem, union.
      intros.
      apply not_elem_of_union. auto.
    Qed.

    Definition inter {A} `{EqDecision A} `{Inhabited A} (s1 : set A) s2 := s1 ∩ s2.

    Lemma inter_mem :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
      forall s' : set A,
      forall x : A,
        mem x s -> mem x s' -> mem x (inter s s').
    Proof.
      unfold mem, inter.
      intros.
      apply elem_of_intersection. auto.
    Qed.

    Lemma inter_mem_neq :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
      forall s' : set A,
      forall x : A,
        not ((mem x s \/ mem x s')) -> not (mem x (inter s s')).
    Proof.
      unfold mem, inter.
      intros A E I s s' x H1 H2.
      apply elem_of_intersection in H2. tauto.
    Qed.

    Definition disjoint {A} `{EqDecision A} `{Inhabited A} (s1 : set A) (s2 : set A) := s1 ∩ s2 = ∅.

    Lemma disjoint_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
      forall s' : set A,
        (disjoint s s' <-> (inter s s' = empty)).
    Proof.
      auto.
    Qed.

    Definition diff {A} `{EqDecision A} `{Inhabited A} (s1 : set A) s2 := s1 ∖ s2.

    Lemma diff_mem :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
      forall s' : set A,
      forall x : A,
        mem x s' -> not (mem x (diff s s')).
    Proof.
      unfold mem, diff.
      intros A E Ih s1 s2 x H1 H2.
      by apply elem_of_difference in H2 as [_ H2].
    Qed.

    Lemma diff_mem_fst :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
      forall s' : set A,
      forall x : A,
        not (mem x s') -> (mem x s <-> mem x (diff s s')).
    Proof.
      unfold mem, diff.
      intros A I s1 s2 x H1.
      split; intros H2.
      + by apply elem_of_difference.
      + by apply elem_of_difference in H2 as [H2 _].
    Qed.

    Definition subset {A} `{EqDecision A} `{Inhabited A} (s1 : set A) (s2 : set A) :=
      forall x, mem x s1 -> mem x s2.

    Definition subset_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
      forall s' : set A,
        (subset s s' <-> forall x : A, mem x s -> mem x s').
    Proof.
      auto.
    Qed.

    Definition map {A} {B} `{EqDecision A} `{Inhabited A} `{EqDecision B} `{Inhabited B} (f : A -> B) (s : set A) :=
      {[x | ∃ y, (f y) = x /\ y ∈ s]}.

    Definition set_map :
      forall {A : Type},
      forall {B : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall `{EqDecision B} `{Inhabited B},
      forall f : B -> A,
      forall s : set B,
      forall x : A,
        (mem x (map f s) <-> exists y : B, ((f y = x) /\ mem y s)).
    Proof.
      unfold mem, map.
      intros.
      split.
      + intros H1. by apply -> (@elem_of_PropSet A) in H1.
      + intros. by apply (@elem_of_PropSet A).
    Qed.

    Definition partition {A} `{EqDecision A} `{Inhabited A} (P : A -> Prop) `{forall x, Decision (P x)} (s : set A) :=
      ({[x | x ∈ s /\ P x]}, {[x | x ∈ s /\ ~ P x]}).

    Lemma partition_l_mem :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall f : A -> Prop,
      forall `{forall x, Decision (f x)},
      forall s : set A,
      forall x : A,
      forall p1 : set A,
      forall p2 : set A,
        mem x s -> f x -> (partition f s = (p1, p2)) -> mem x p1.
    Proof.
      unfold mem, partition.
      intros A E I f D s x p1 p2 H1 H2 H3.
      injection H3.
      intros.
      subst.
      by apply elem_of_PropSet.
    Qed.

    Lemma partition_r_mem :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall f : A -> Prop,
      forall `{forall x, Decision (f x)},
      forall s : set A,
      forall x : A,
      forall p1 : set A,
      forall p2 : set A,
        mem x s -> not (f x) -> (partition f s = (p1, p2)) -> mem x p2.
    Proof.
      unfold mem, partition.
      intros A E I f D s x p1 p2 H1 H2 H3.
      injection H3.
      intros.
      subst.
      apply elem_of_PropSet. auto.
    Qed.

    Parameter cardinal :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
        t A -> Z.

    Parameter finite :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
        t A -> Prop.

    Axiom finite_def :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
        (
          finite s <-> exists seq : sequence A,
          forall x : A,
            mem x s -> Sequence.mem x seq
        ).

    Axiom cardinal_nonneg :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
        (cardinal s >= (0)%Z).

    Axiom cardinal_empty :
      forall {A : Type},
      forall {E : EqDecision A} {I: Inhabited A},
        (@cardinal A E I empty = (0)%Z).

    Axiom cardinal_remove_mem :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
      forall x : A,
        finite s -> mem x s -> (cardinal (remove x s) = (cardinal s - (1)%Z)).

    Axiom cardinal_remove_not_mem :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
      forall x : A,
        finite s -> not (mem x s) -> (cardinal (remove x s) = cardinal s).

    Axiom cardinal_add :
      ∀ (A : Type) (Eq_A : EqDecision A) (Ih_A : Inhabited A) (s : set A) (x : A),
        _Set.finite s
        → _Set.neg_belongs x s
        → _Set.cardinal (_Set.add x s) = _Set.cardinal s + 1.

    Axiom cardinal_add_mem :
      forall {A : Type},
      forall {Eq_A : EqDecision A},
      forall {Ih_A : Inhabited A},
      forall s : set A,
      forall x : A,
        finite s -> belongs x s -> ((cardinal (add x s)) = (cardinal s)).

    Definition of_seq {A} `{EqDecision A} `{Inhabited A} (s : list A) : set A := {[x | Sequence.mem x s]}.

    Lemma of_seq_mem :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : sequence A,
      forall x : A,
        (mem x (of_seq s) <-> Sequence.mem x s).
    Proof.
      auto.
    Qed.

    Parameter to_seq :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
        t A -> Sequence.t A.

    Axiom to_seq_mem :
      forall {A : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall s : set A,
        finite s ->
        (
          forall x : A,
            (mem x s <-> (Sequence.multiplicity x (to_seq s) = (1)%Z))
        ).

    Parameter fold :
      forall {A : Type},
      forall {B : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall `{EqDecision B} `{Inhabited B},
        (A -> B) -> (B -> B -> B) -> t A -> B -> B.

    Axiom fold_def :
      forall {A : Type},
      forall {B : Type},
      forall `{EqDecision A} `{Inhabited A},
      forall `{EqDecision B} `{Inhabited B},
      forall f : A -> B,
      forall m : B -> B -> B,
      forall s : set A,
      forall acc : B,
        finite s ->
        comm_monoid m acc ->
        (
          fold f m s acc = Sequence.fold_right (
                               fun x : A =>
                               fun acc : B =>
                                 m (f x) acc
                             ) (to_seq s) acc
        ).

  End _Set.

  Definition map_set {A} {B} `{EqDecision A} `{Inhabited A} `{EqDecision B} `{Inhabited B} (f : A -> B) x y :=
    λ z, if (decide (x = z)) then y else f z.

  Lemma map_set_def :
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
  Proof.
    intros.
    unfold map_set.
    by rewrite decide_True.
  Qed.

  Lemma map_set_def_neq :
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
  Proof.
    intros.
    unfold map_set.
    by rewrite decide_False.
  Qed.

  Module Map.

    Definition t  (A : Type) (B : Type) : Type:= map A B.

    Definition domain {A} {B} `{EqDecision A} `{Inhabited A} `{EqDecision B} `{Inhabited B} (x : B) (m : map A B) :=
      {[y | m y <> x]}.

    Lemma domain_mem :
      forall {B : Type},
      forall {A : Type},
      forall `{EqDecision B} `{Inhabited B},
      forall `{EqDecision A} `{Inhabited A},
      forall x : A,
      forall m : A -> B,
      forall default : B,
        (m x <> default) -> _Set.mem x (domain default m).
    Proof.
      auto.
    Qed.

  End Map.
End Stdlib.

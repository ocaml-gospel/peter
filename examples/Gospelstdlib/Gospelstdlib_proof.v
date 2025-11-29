Require Import Gospelstdlib_mli.

Require Stdlib.ZArith.BinInt stdpp.base.

Require Stdlib.ZArith.BinInt.
Require Import Stdlib.ZArith.BinIntDef.
Require Import stdpp.decidable stdpp.list stdpp.gmap stdpp.propset stdpp.option stdpp.base.

Global Declare Instance _DECIDABLE : forall P, stdpp.base.Decision P.

Local Open Scope Z_scope.
From Stdlib Require Import BinInt.

Module Proofs : Gospelstdlib_mli.Obligations.

  Import Declarations.

  Global Instance _set_inst : _set_sig :=
    { set := fun A => propset A }.

  Global Instance _bag_inst : _bag_sig :=
    { bag := fun A => A -> nat }.

  Global Instance _sequence_inst : _sequence_sig :=
    { sequence := fun A => list A }.

  Global Instance _option_inst : _option_sig :=
    { option := fun A => Datatypes.option A }.

  Global Instance _Some_inst : _Some_sig :=
    { Some := fun A _ x => Datatypes.Some x }.

  Global Instance _None_inst : _None_sig :=
    { None := fun A _ => @Datatypes.None A }.

  Global Instance _succ_inst : _succ_sig :=
    { succ := Z.succ }.

  Global Instance _pred_inst : _pred_sig :=
    { pred := Z.pred }.

  Global Instance __mod_inst : __mod_sig :=
    { _mod := Z.modulo }.

  Global Instance _pow_inst : _pow_sig :=
    { pow := Z.pow }.

  Global Instance _abs_inst : _abs_sig :=
    { abs := Z.abs }.

  Global Instance _min_inst : _min_sig :=
    { min := Z.min }.

  Global Instance _max_inst : _max_sig :=
    { max := Z.max }.

  Global Instance _app_inst : _app_sig :=
    { app := fun A _ s1 s2 => s1 ++ s2 }.

  Global Instance _seq_get_inst : _seq_get_sig :=
    { seq_get := fun A _ (s : list A) i => s !!! Z.to_nat i }.

  Definition takeZ {A} (i : Z) (s : sequence A) :=
    take (Z.to_nat i) s.

  Definition dropZ {A} (i : Z) (s : sequence A) := drop (Z.to_nat i) s.

  Global Instance _seq_sub_inst : _seq_sub_sig :=
    { seq_sub := fun A _ s i1 i2 => takeZ (i2 - i1) (dropZ i1 s) }.

  Global Instance _seq_sub_l_inst : _seq_sub_l_sig :=
    { seq_sub_l := fun A _ s i => seq_sub s i (Z.of_nat (length s)) }.

  Global Instance _seq_sub_r_inst : _seq_sub_r_sig :=
    { seq_sub_r := fun A _ s i => seq_sub s 0 i }.

  Definition neutral_l {A} (f : A -> A -> A) n := forall x, f n x = x.
  Definition neutral_r {A} (f : A -> A -> A) n := forall x, f x n = x.

  Global Instance _monoid_inst : _monoid_sig :=
    { monoid :=
        fun A _ f neutral =>
          Assoc eq f /\ neutral_l f neutral /\ neutral_r f neutral
    }.

  #[refine] Global Instance _monoid_def_inst : _monoid_def_sig := { }.
  Proof.
    simpl.
    intros A Ih f neutral.
    unfold neutral_l, neutral_r.
    split.
    - intros (H1 & H2 & H3). repeat split; try rewrite H2; auto.
    - intros [H1 H2].
      repeat split.
      1: auto.
      all: intros; specialize H1 with x; destruct H1 as [H1 H3]; try rewrite H1; auto.
  Qed.

  Global Instance _comm_monoid_inst : _comm_monoid_sig :=
    { comm_monoid := fun A _ f n => monoid f n /\ Comm eq f }.

  #[refine] Global Instance _comm_monoid_def_inst : _comm_monoid_def_sig := { }.
  Proof.
    auto.
  Qed.

  Module Sequence.

    Import Sequence.

    Definition lengthZ {A} s := Z.of_nat (@List.length A s).

    Global Instance _length_inst : _length_sig :=
      { length := fun A _ s => @lengthZ A s }.

    Lemma length_takeZ :
      forall A (s : sequence A) i,
        0 <= i <= lengthZ s ->
        lengthZ (takeZ i s) = i.
    Proof.
      simpl.
      intros.
      unfold takeZ, lengthZ in *.
      rewrite length_take. lia.
    Qed.

    Lemma lookup_takeZ_lt :
      forall A `{Inhabited A} (s : sequence A) l i,
        0 <= i < l ->
        (takeZ l s) !!! Z.to_nat i = s !!! Z.to_nat i.
    Proof.
      simpl in *.
      intros.
      unfold takeZ.
      rewrite lookup_total_take_lt; auto with lia.
    Qed.

    Lemma lookup_dropZ_lt :
      forall A `{Inhabited A} (s : sequence A) l i,
        0 <= i ->
        0 <= l ->
        (dropZ l s) !!! Z.to_nat i = s !!! Z.to_nat (l + i).
    Proof.
      simpl in *.
      intros.
      unfold length, dropZ, seq_get.
      rewrite lookup_total_drop.
      rewrite Z2Nat.inj_add; auto with lia.
    Qed.

    Lemma length_dropZ :
      forall A (s : sequence A) i,
        0 <= i <= lengthZ s ->
        lengthZ (dropZ i s) = lengthZ s - i.
    Proof.
      simpl in *.
      intros.
      unfold dropZ, lengthZ in *.
      rewrite length_drop. lia.
    Qed.

    Global Instance _in_range_inst : _in_range_sig :=
      { in_range := fun A _ s i => 0 <= i < length s }.

    #[refine] Global Instance _in_range_def_inst : _in_range_def_sig := { }.
    Proof.
      auto.
    Qed.

    #[refine] Global Instance _length_nonneg_inst : _length_nonneg_sig := { }.
    Proof.
      simpl. unfold lengthZ. lia.
    Qed.

    #[refine] Global Instance _subseq_l_inst : _subseq_l_sig := { }.
    Proof.
      auto.
    Qed.

    #[refine] Global Instance _subseq_r_inst : _subseq_r_sig := { }.
    Proof.
      auto.
    Qed.

    #[refine] Global Instance _subseq_inst : _subseq_sig := { }.
    Proof.
      intros A Ih s i i1 i2 H.
      simpl.
      rewrite lookup_takeZ_lt. 2: lia.
      rewrite lookup_dropZ_lt. 2, 3: lia.
      f_equal. lia.
    Qed.

    #[refine] Global Instance _subseq_len_inst : _subseq_len_sig := { }.
    Proof.
      simpl.
      intros.
      unfold seq_sub.
      rewrite length_takeZ. 1: lia.
      rewrite length_dropZ; lia.
    Qed.

    Lemma lengthZ_app :
      forall {A} (l1 : sequence A) l2,
        lengthZ (l1 ++ l2) = lengthZ l1 + lengthZ l2.
    Proof.
      intros.
      unfold lengthZ.
      rewrite length_app.
      lia.
    Qed.

    Global Instance _empty_inst : _empty_sig :=
      { empty := fun A _ => @nil A }.

    #[refine] Global Instance _empty_length_inst : _empty_length_sig := { }.
    Proof.
      auto.
    Qed.

    Fixpoint init_aux {A} (n : nat) (f : Z -> A) : sequence A :=
      match n with
      |O => nil
      |S n' => (init_aux n' f) ++ [f (Z.of_nat n')] end.

    Global Instance _init_inst : _init_sig :=
      { init :=
          fun A _ n f =>
            if decide (n < 0) then
              nil
            else
              init_aux (Z.to_nat n) f }.

    Lemma init_aux_length :
      forall {A} n (f : Z -> A),
        Datatypes.length (init_aux n f) = n.
    Proof.
      intros.
      induction n as [|n' Ih].
      + auto.
      + simpl. rewrite length_app. rewrite Ih.
        unfold length. simpl.
        lia.
    Qed.

    Lemma init_aux_lengthZ :
      forall A n (f : Z -> A),
        lengthZ (init_aux n f) = Z.of_nat n.
    Proof.
      simpl. intros. unfold lengthZ.
      rewrite init_aux_length. auto.
    Qed.

    #[refine] Global Instance _init_length_inst : _init_length_sig := { }.
    Proof.
      simpl.
      intros.
      rewrite decide_False. 2: lia.
      rewrite init_aux_lengthZ. lia.
    Qed.

    Lemma lookup_total_app_lZ :
      forall {A} `{Inhabited A} (s1 : sequence A) (s2 : sequence A) i,
        0 <= i < lengthZ s1 ->
        (s1 ++ s2) !!! Z.to_nat i = s1 !!! Z.to_nat i.
    Proof.
      intros.
      unfold lengthZ in *.
      rewrite lookup_total_app_l; auto with lia.
    Qed.

    Lemma lookup_total_app_rZ :
      forall {A} `{Inhabited A} (s1 : sequence A) (s2 : sequence A) i,
        lengthZ s1 <= i < lengthZ s1 + lengthZ s2 ->
        (s1 ++ s2) !!! Z.to_nat i = s2 !!! Z.to_nat (i - lengthZ s1).
    Proof.
      simpl.
      intros.
      unfold seq_get, lengthZ in *.
      rewrite lookup_total_app_r. 2: lia.
      f_equal.
      rewrite Z2Nat.inj_sub; lia.
    Qed.

    Lemma init_i :
      forall {A} (n : nat) (i : Z) (f : Z -> A),
      forall `{Inhabited A},
        0 <= i ->
        i < Z.of_nat n ->
        (init_aux n f) !!! Z.to_nat i = f i.
    Proof.
      intros A n i f Inh H1 H2.
      induction n as [|n' Ih].
      - lia.
      - simpl.
        destruct (decide (i < Z.of_nat n')).
        + rewrite lookup_total_app_lZ.
          2: unfold lengthZ; rewrite init_aux_length; lia.
          auto.
        +
          cut (i = Z.of_nat n'). 2: lia.
          intros P.
          rewrite lookup_total_app_rZ; unfold lengthZ;
            rewrite init_aux_length. 2: simpl; lia.
          subst.
          rewrite Z.sub_diag.
          auto.
    Qed.

    #[refine] Global Instance _init_elems_inst : _init_elems_sig := { }.
    Proof.
      simpl.
      intros.
      rewrite decide_False. 2: lia.
      apply init_i; lia.
    Qed.

    Global Instance _singleton_inst : _singleton_sig :=
      { singleton := fun A _ x => [x] }.

    #[refine] Global Instance _singleton_def_inst : _singleton_def_sig := { }.
    Proof.
      intros A Ih x f H.
      rewrite <- H.
      simpl. rewrite decide_False.
      auto. lia.
    Qed.

    Global Instance _cons_inst : _cons_sig :=
      { cons := fun A _ x t =>  x :: t}.

    #[refine] Global Instance _cons_def_inst : _cons_def_sig := { }.
    Proof.
      list_simplifier. auto.
    Qed.

    Global Instance _snoc_inst : _snoc_sig :=
      { snoc := fun A _ s x => s ++ [x] }.

    #[refine] Global Instance _snoc_def_inst : _snoc_def_sig := { }.
    Proof.
      auto.
    Qed.

    Global Instance _hd_inst : _hd_sig :=
      { hd := fun A _ s => s !!! 0%nat }.

    #[refine] Global Instance _hd_def_inst : _hd_def_sig := { }.
    Proof.
      auto.
    Qed.

    Global Instance _tl_inst : _tl_sig :=
      { tl := fun A _ s => List.tl s }.

    #[refine] Global Instance _tl_def_inst : _tl_def_sig := { }.
    Proof.
      simpl.
      intros.
      subst. auto.
    Qed.

    Global Instance _append_inst : _append_sig :=
      { append := fun A _ s1 s2 => s1 ++ s2 }.


    #[refine] Global Instance _append_def_inst : _append_def_sig := { }.
    Proof.
      auto.
    Qed.

    #[refine] Global Instance _append_length_inst : _append_length_sig := { }.
    Proof.
      simpl.
      intros.
      by rewrite lengthZ_app.
    Qed.

    #[refine] Global Instance _append_elems_left_inst : _append_elems_left_sig := { }.
    Proof.
      simpl.
      intros.
      rewrite lookup_total_app_lZ; auto.
    Qed.

    #[refine] Global Instance _append_elems_right_inst : _append_elems_right_sig := { }.
    Proof.
      intros.
      simpl. rewrite lookup_total_app_rZ; auto.
    Qed.

    Global Instance _multiplicity_inst : _multiplicity_sig :=
      { multiplicity :=
          fun A _ x s => length (base.filter (λ y, x = y) s) }.

    #[refine] Global Instance _mult_empty_inst : _mult_empty_sig := { }.
    Proof.
      simpl.
      intros.
      rewrite filter_nil.
      unfold lengthZ.
      auto.
    Qed.

    Lemma lengthZ_cons :
      forall A s (x :  A),
        lengthZ (x :: s) = 1 + lengthZ s.
    Proof.
      intros.
      unfold lengthZ.
      simpl. lia.
    Qed.

    #[refine] Global Instance _mult_cons_inst : _mult_cons_sig := { }.
    Proof.
      simpl.
      intros.
      rewrite filter_cons.
      rewrite decide_True. 2: auto.
      rewrite lengthZ_cons. auto.
    Qed.

    #[refine] Global Instance _mult_cons_neutral_inst : _mult_cons_neutral_sig := { }.
    Proof.
      simpl.
      intros.
      rewrite filter_cons.
      rewrite decide_False; auto.
    Qed.

    Lemma lengthZ_filter :
      forall {A} `{Inhabited A} (s : sequence A) P,
        length (base.filter P s) <= length s.
    Proof.
      simpl.
      intros.
      unfold lengthZ.
      rewrite <- Nat2Z.inj_le.
      apply length_filter.
    Qed.

    #[refine] Global Instance _mult_length_inst : _mult_length_sig := { }.
    Proof.
      simpl. intros.
      split.
      - unfold lengthZ. lia.
      - apply lengthZ_filter.
    Qed.

    Global Instance _mem_inst : _mem_sig :=
      { mem := fun A _ x s => x ∈ s }.

    Global Instance _belongs_inst : _belongs_sig :=
      { belongs := fun A _ x s => x ∈ s }.

    #[refine] Global Instance _mem_fun_def_inst : _mem_fun_def_sig := { }.
    Proof.
      tauto.
    Qed.

    Global Instance _neg_belongs_inst : _neg_belongs_sig :=
      { neg_belongs := fun A _ x s => x ∉ s }.

    #[refine] Global Instance _nmem_def_inst : _nmem_def_sig := { }.
    Proof.
      simpl. tauto.
    Qed.

    #[refine] Global Instance _mem_def_inst : _mem_def_sig := { }.
    Proof.
      simpl.
      intros A I s x.
      split; intros H.
      - induction s as [|y t Ih].
        + apply not_elem_of_nil in H. tauto.
        + rewrite filter_cons.
          destruct (decide (x = y)).
          * rewrite lengthZ_cons.
            unfold lengthZ. lia.
          * apply Ih.
            rewrite elem_of_cons in H.
            destruct H.
            1: contradiction.
            auto.
      - induction s as [|y t Ih].
        + rewrite filter_nil in H.
          unfold lengthZ in H.
          rewrite length_nil in H. lia.
        + rewrite filter_cons in H.
          destruct (decide (x = y)); rewrite elem_of_cons; auto.
    Qed.

    Global Instance _Forall_inst : _Forall_sig :=
      { Forall := fun A _ P s => List.Forall P s }.

    #[refine] Global Instance _forall_def_inst : _forall_def_sig := { }.
    Proof.
      intros.
      unfold Forall, mem.
      apply list.Forall_forall.
    Qed.

    Global Instance _Exists_inst : _Exists_sig :=
      { Exists := fun A _ P s => List.Exists P s }.

    #[refine] Global Instance _exists_def_inst : _exists_def_sig := { }.
    Proof.
      simpl.
      intros.
      apply list.Exists_exists.
    Qed.

    Global Instance _map_inst : _map_sig :=
      { map := fun A B _ _ f s => List.map f s }.

    Lemma empty_lengthZ :
      forall {A}, lengthZ (@nil A) = 0.
    Proof.
      intros.
      unfold lengthZ.
      rewrite list.length_nil.
      auto.
    Qed.

    Lemma cons_lengthZ :
      forall {A} s (x : A),
        lengthZ (x :: s) = 1 + lengthZ s.
    Proof.
      intros.
      unfold lengthZ.
      rewrite list.length_cons. lia.
    Qed.

    Lemma cons_seq_get :
      forall A `{Inhabited A} s (x : A) i,
        0 < i ->
        (x :: s) !!! Z.to_nat i = s !!! Z.to_nat (i - 1).
    Proof.
      intros.
      rewrite lookup_total_cons_ne_0.
      1: f_equal. all: lia.
    Qed.

    #[refine] Global Instance _map_elems_inst : _map_elems_sig := { }.
    Proof.
      simpl.
      intros A B Ih_A Ih_B i f s.
      generalize dependent i.
      induction s as [|h t Ih]; intros i H.
      - rewrite (@empty_lengthZ A) in H. lia.
      - rewrite cons_lengthZ in H.
        simpl.
        destruct (decide (i = 0)) as [E | E].
        + rewrite E.
          unfold seq_get. auto.
        + repeat (rewrite cons_seq_get; try lia).
          apply Ih. lia.
    Qed.

    #[refine] Global Instance _map_length_inst : _map_length_sig := { }.
    Proof.
      simpl. intros.
      unfold lengthZ. by rewrite length_map.
    Qed.

    Global Instance _filter_inst : _filter_sig :=
      { filter :=
          fun A _ P s =>
            let D := (fun x => _DECIDABLE (P x)) in
            list_filter P D s }.

    #[refine] Global Instance _filter_elems_inst : _filter_elems_sig := { }.
    Proof.
      intros.
      apply list_elem_of_filter.
      auto.
    Qed.


    Global Instance _filter_map_inst : _filter_map_sig :=
      { filter_map :=
          fun A B _ _ f s =>
          List.map
            (λ x, match f x with
                  |Datatypes.Some x' => x'
                  |Datatypes.None => inhabitant end)
            (filter (λ x, f x <> Datatypes.None) s)
      }.

    Lemma map_mem :
      forall {A} `{Inhabited A} {B} `{Inhabited B} (s : sequence A) (f : A -> B) (x : A),
        x ∈ s -> f x ∈ map f s.
    Proof.
      intros A B IhA IhB s f x.
      generalize dependent x. induction s as [|h t Ih]; intros x H1.
      + apply not_elem_of_nil in H1. tauto.
      + simpl. apply elem_of_cons.
        destruct (decide (x = h)) as [E | E].
        * left. f_equal. auto.
        * right. apply elem_of_cons in H1.
          destruct H1. 1: tauto.
          auto.
    Qed.

    #[refine] Global Instance _filter_map_elems_inst : _filter_map_elems_sig := { }.
    Proof.
      simpl.
      intros A B IhA IhB f s y.
      remember (λ x0 : A,
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

    Global Instance _get_inst : _get_sig :=
      { get := fun A _ => seq_get }.

    #[refine] Global Instance _get_def_inst : _get_def_sig := { }.
    Proof.
      auto.
    Qed.

    Fixpoint set_aux {A} (s : sequence A) (n : nat) (x : A) : sequence A :=
      match s, n with
      |nil, _ => inhabitant
      |_ :: t, O => x :: t
      |e :: t, S n' => e :: set_aux t n' x
      end.

    Global Instance _set_inst : _set_sig :=
      { set := fun A _ s n x => if decide (n < 0) then inhabitant else set_aux s (Z.to_nat n) x }.

    Lemma set_elem_nat :
      forall {A} `{Inhabited A} (x : A) i s,
        (i < List.length s)%nat -> (set_aux s i x) !!! i = x.
    Proof.
      intros A I x.
      induction i as [|n Ih]; intros s H1; destruct s as [|h t]. 2: auto. 1, 2: rewrite length_nil in H1; lia.
      simpl. apply Ih. simpl in H1.
      lia.
    Qed.

    #[refine] Global Instance _set_elem_inst : _set_elem_sig := { }.
    Proof.
      simpl.
      intros A I s i x H1.
      rewrite decide_False. 2: lia.
      apply set_elem_nat. unfold lengthZ in H1. lia.
    Qed.

    Lemma set_elem_other_nat :
      forall {A} `{Inhabited A} (x : A) s i1 i2,
        i1 <> i2 ->
        (i1 < List.length s)%nat ->
        (i2 < List.length s)%nat ->
        (set_aux s i1 x) !!! i2 = s !!! i2.
    Proof.
      intros A I x s.
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

    #[refine] Global Instance _set_elem_other_inst : _set_elem_other_sig := { }.
    Proof.
      simpl.
      intros A Ih s i1 i2 x H1 H2 H3.
      rewrite decide_False. 2: lia.
      unfold lengthZ in *.
      apply set_elem_other_nat; lia.
    Qed.

    Global Instance _rev_inst : _rev_sig :=
      { rev := fun A _ s => reverse s }.

    #[refine] Global Instance _rev_length_inst : _rev_length_sig := { }.
    Proof.
      simpl.
      intros.
      unfold lengthZ. rewrite length_reverse.
      auto.
    Qed.

    #[refine] Global Instance _rev_elems_inst : _rev_elems_sig := { }.
    Proof.
      simpl.
      unfold lengthZ.
      intros A I i s H1.
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
      forall {A} `{Inhabited A} s i (x : A),
        0 <= i < lengthZ s ->
        s !!! Z.to_nat i = (x :: s) !!! Z.to_nat (i + 1).
    Proof.
      simpl.
      intros.
      rewrite lookup_total_cons_ne_0. 2: lia.
      f_equal. lia.
    Qed.

    #[refine] Global Instance _extensionality_inst : _extensionality_sig := { }.
    Proof.
      simpl.
      intros A IhA s1.
      induction s1 as [|h s1 Ih]; intros s2 H1.
      - rewrite (@empty_lengthZ A) in H1.
        symmetry.
        apply length_zero_iff_nil.
        unfold lengthZ in H1. lia.
      - intros H2.
        destruct s2 as [|h' s2].
        + rewrite (@empty_lengthZ A) in H1.
          rewrite cons_lengthZ in H1.
          cut (0 <= lengthZ s1). 2: unfold lengthZ in H1; lia.
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
            intros H3. simpl in H3.
            lia.
    Qed.

    Global Instance _fold_left_inst : _fold_left_sig :=
      { fold_left :=
          fun A B _ _ f acc s =>
            List.fold_left f s acc }.

    #[refine] Global Instance _fold_left_empty_inst : _fold_left_empty_sig := { }.
    Proof.
      auto.
    Qed.

    #[refine] Global Instance _fold_left_cons_inst : _fold_left_cons_sig := { }.
    Proof.
      auto.
    Qed.

    Global Instance _fold_right_inst : _fold_right_sig :=
      { fold_right := fun A B _ _ f s acc => List.fold_right f acc s }.

    #[refine] Global Instance _fold_right_empty_inst : _fold_right_empty_sig := { }.
    Proof.
      auto.
    Qed.

    #[refine] Global Instance _fold_right_cons_inst : _fold_right_cons_sig := { }.
    Proof.
      auto.
    Qed.

    Global Instance _permut_inst : _permut_sig :=
      { permut :=
          fun A _ s1 s2 =>
            (forall x, (mem x s1) <-> (mem x s2)) }.

    #[refine] Global Instance _permut_mem_inst : _permut_mem_sig := { }.
    Proof.
      tauto.
    Qed.

    Global Instance _permut_sub_inst : _permut_sub_sig :=
      { permut_sub :=
          fun A _ s1 s2 i j =>
            permut (seq_sub s1 i j) (seq_sub s2 i j) /\
              (seq_sub_r s1 i) = (seq_sub_r s2 i) /\
              (seq_sub_l s1 j) = (seq_sub_l s2 j) }.

    #[refine] Global Instance _permut_sub_def_inst : _permut_sub_def_sig := { }.
    Proof.
      simpl. tauto.
    Qed.

    End Sequence.

  Module Bag.

    Import Bag.

    Global Instance _multiplicity_inst : _multiplicity_sig :=
      { multiplicity := fun A _ x b => Z.of_nat (b x) }.

    #[refine] Global Instance _well_formed_inst : _well_formed_sig := { }.
    Proof.
      simpl. lia.
    Qed.

    Global Instance _empty_inst : _empty_sig :=
      { empty := fun A _ _ => 0%nat }.

    #[refine] Global Instance _empty_mult_inst : _empty_mult_sig := { }.
    Proof.
      auto.
    Qed.

    Global Instance _init_inst : _init_sig :=
      { init := fun A _ f x => Z.to_nat (f x) }.

    #[refine] Global Instance _init_axiom_inst : _init_axiom_sig := { }.
    Proof.
      simpl. lia.
    Qed.

    Global Instance _mem_inst : _mem_sig :=
      { mem := fun A _ x b => multiplicity x b > 0 }.

    Global Instance _belongs_inst : _belongs_sig :=
      { belongs := fun A _ => mem }.

    #[refine] Global Instance _mem_fun_def_inst : _mem_fun_def_sig := { }.
    Proof.
      tauto.
    Qed.

    Global Instance _neg_belongs_inst : _neg_belongs_sig :=
      { neg_belongs := fun A _ x b => not (belongs x b) }.

    #[refine] Global Instance _nmem_def_inst : _nmem_def_sig := { }.
    Proof.
      simpl. tauto.
    Qed.

    #[refine] Global Instance _mem_def_inst : _mem_def_sig := { }.
    Proof.
      tauto.
    Qed.

    Global Instance _add_inst : _add_sig :=
      { add :=
          fun A _ x b =>
            (λ y, if decide (x = y) then b y + 1 else  b y)%nat }.

    #[refine] Global Instance _add_mult_x_inst : _add_mult_x_sig := { }.
    Proof.
      simpl.
      intros.
      rewrite decide_True.
      + lia.
      + auto.
    Qed.

    #[refine] Global Instance _add_mult_neg_x_inst : _add_mult_neg_x_sig := { }.
    Proof.
      simpl.
      intros.
      rewrite decide_False; auto.
    Qed.

    Global Instance _singleton_inst : _singleton_sig :=
      { singleton :=
          fun A _ x =>
          fun y => if decide (x = y) then 1%nat else 0%nat }.

    Global Instance _singleton_set_inst : _singleton_set_sig :=
      { singleton_set := fun A _ => singleton }.

    #[refine] Global Instance _singleton_fun_def_inst : _singleton_fun_def_sig := { }.
    Proof.
      tauto.
    Qed.

    #[refine] Global Instance _singleton_def_inst : _singleton_def_sig := { }.
    Proof.
      auto.
    Qed.

    Global Instance _remove_inst : _remove_sig :=
      { remove :=
          fun A _ x b =>
            λ y, if decide (x = y) then (b y - 1)%nat else b y }.

    #[refine] Global Instance _remove_mult_x_inst : _remove_mult_x_sig := { }.
    Proof.
      simpl.
      intros.
      rewrite decide_True. lia. auto.
    Qed.

    #[refine] Global Instance _remove_mult_neg_x_inst : _remove_mult_neg_x_sig := { }.
    Proof.
      simpl.
      intros.
      rewrite decide_False. lia. auto.
    Qed.

    Global Instance _union_inst : _union_sig :=
      { union := fun A _ b1 b2 y => (Nat.max (b1 y) (b2 y))%nat }.

    #[refine] Global Instance _union_all_inst : _union_all_sig := { }.
    Proof.
      simpl.
      lia.
    Qed.

    Global Instance _sum_inst : _sum_sig :=
      { sum := fun A _ b1 b2 => λ y, (b1 y + b2 y)%nat }.

    #[refine] Global Instance _sum_all_inst : _sum_all_sig := { }.
    Proof.
      simpl. lia.
    Qed.

    Global Instance _inter_inst : _inter_sig :=
      { inter := fun A _ b1 b2 => λ y, (b1 y `min` b2 y)%nat }.

    #[refine] Global Instance _inter_all_inst : _inter_all_sig := { }.
    Proof.
      simpl. lia.
    Qed.

    Global Instance _disjoint_inst : _disjoint_sig :=
      { disjoint := fun A _ b1 b2 => forall x, mem x b1 -> ~ mem x b2 }.

    #[refine] Global Instance _disjoint_def_inst : _disjoint_def_sig := { }.
    Proof.
      auto.
    Qed.

    Global Instance _diff_inst : _diff_sig :=
      { diff := fun A _ b1 b2 => λ y, (b1 y - b2 y)%nat }.

    #[refine] Global Instance _diff_all_inst : _diff_all_sig := { }.
    Proof.
      simpl. lia.
    Qed.

    Global Instance _subset_inst : _subset_sig :=
      { subset := fun A _ b1 b2 => forall x, (b1 x <= b2 x)%nat }.

    #[refine] Global Instance _subset_def_inst : _subset_def_sig := { }.
    Proof.
      simpl.
      intros A I b b'.
      split; intros H x; specialize H with x; lia.
    Qed.

    Global Instance _filter_inst : _filter_sig :=
      { filter := fun A _ P b => λ x, if decide (P x) then b x else 0%nat }.

    #[refine] Global Instance _filter_mem_inst : _filter_mem_sig := { }.
    Proof.
      simpl.
      intros.
      rewrite decide_True; auto.
    Qed.

    #[refine] Global Instance _filter_mem_neg_inst : _filter_mem_neg_sig := { }.
    Proof.
      simpl.
      intros.
      rewrite decide_False; auto.
    Qed.

    Global Declare Instance _cardinal_inst : _cardinal_sig.
    Global Declare Instance _finite_inst : _finite_sig.
    Global Declare Instance _finite_def_inst : _finite_def_sig.
    Global Declare Instance _card_nonneg_inst : _card_nonneg_sig.
    Global Declare Instance _card_empty_inst : _card_empty_sig.
    Global Declare Instance _card_singleton_inst : _card_singleton_sig.
    Global Declare Instance _card_union_inst : _card_union_sig.
    Global Declare Instance _card_add_inst : _card_add_sig.
    Global Declare Instance _card_map_inst : _card_map_sig.
    Global Declare Instance _of_seq_inst : _of_seq_sig.
    Global Declare Instance _of_seq_multiplicity_inst : _of_seq_multiplicity_sig.

  End Bag.

  Module _Set.

    Import _Set.

    Global Instance _empty_inst : _empty_sig :=
      { empty := fun A _ => ∅ }.

    Global Instance _mem_inst : _mem_sig :=
      { mem := fun A _ x s => x ∈ s }.

    Global Instance _belongs_inst : _belongs_sig :=
      { belongs := fun A _ x s => mem x s }.

    #[refine] Global Instance _mem_fun_def_inst : _mem_fun_def_sig := { }.
    Proof.
      tauto.
    Qed.

    Global Instance _neg_belongs_inst : _neg_belongs_sig :=
      { neg_belongs := fun A _ x s => not (belongs x s) }.

    #[refine] Global Instance _nmem_def_inst : _nmem_def_sig := { }.
    Proof.
      simpl. tauto.
    Qed.

    #[refine] Global Instance _empty_mem_inst : _empty_mem_sig := { }.
    Proof.
      simpl.
      intros. apply not_elem_of_empty.
    Qed.

    Global Instance _add_inst : _add_sig :=
      { add := fun A _ x s => {[ x ]} ∪ s }.

    #[refine] Global Instance _add_mem_inst : _add_mem_sig := { }.
    Proof.
      simpl.
      intros.
      apply elem_of_union_l.
      by apply elem_of_singleton.
    Qed.

    #[refine] Global Instance _add_mem_neq_inst : _add_mem_neq_sig := { }.
    Proof.
      intros A I s x y H1.
      unfold mem, add.
      split.
      + intros. by apply elem_of_union_r.
      + intros H2. inversion H2 as [H3 | H3].
        * by apply elem_of_singleton in H3.
        * auto.
    Qed.

    Global Instance _singleton_inst : _singleton_sig :=
      { singleton := fun A _ x => add x empty }.

    Global Instance _singleton_set_inst : _singleton_set_sig :=
      { singleton_set := fun A _ x => singleton x }.

    #[refine] Global Instance _singleton_def_inst : _singleton_def_sig := { }.
    Proof.
      simpl. tauto.
    Qed.

    #[refine] Global Instance _singleton_fun_def_inst : _singleton_fun_def_sig := { }.
    Proof.
      tauto.
    Qed.

    Global Instance _remove_inst : _remove_sig :=
      { remove := fun A _ x s => s ∖ {[x]} }.

    #[refine] Global Instance _remove_mem_inst : _remove_mem_sig := { }.
    Proof.
      simpl.
      intros A I s x H1.
      apply elem_of_difference in H1 as [_ H1].
      apply H1. by apply elem_of_singleton.
    Qed.

    #[refine] Global Instance _remove_mem_neq_inst : _remove_mem_neq_sig := { }.
    Proof.
      simpl.
      intros.
      split; intros H1.
      + apply elem_of_difference. split; auto.
      + by apply elem_of_difference in H1 as [H1 _].
    Qed.

    Global Instance _union_inst : _union_sig :=
      { union := fun A _ s1 s2 => s1 ∪ s2 }.

    #[refine] Global Instance _union_mem_inst : _union_mem_sig := { }.
    Proof.
      auto.
    Qed.

    #[refine] Global Instance _union_mem_neg_inst : _union_mem_neg_sig := { }.
    Proof.
      simpl. intros. apply not_elem_of_union. auto.
    Qed.

    Global Instance _inter_inst : _inter_sig :=
      { inter := fun A _ s1 s2 => s1 ∩ s2 }.

    #[refine] Global Instance _inter_mem_inst : _inter_mem_sig := { }.
    Proof.
      simpl. intros. apply elem_of_intersection. auto.
    Qed.

    #[refine] Global Instance _inter_mem_neq_inst : _inter_mem_neq_sig := { }.
    Proof.
      simpl.
      intros A I s s' x H1 H2.
      apply elem_of_intersection in H2. tauto.
    Qed.

    Global Instance _disjoint_inst : _disjoint_sig :=
      { disjoint := fun A _ s1 s2 => s1 ∩ s2 = ∅ }.

    #[refine] Global Instance _disjoint_def_inst : _disjoint_def_sig := { }.
    Proof.
      auto.
    Qed.

    Global Instance _diff_inst : _diff_sig :=
      { diff := fun A _ s1 s2 => s1 ∖ s2 }.

    #[refine] Global Instance _diff_mem_inst : _diff_mem_sig := { }.
    Proof.
      simpl.
      intros A Ih s1 s2 x H1 H2.
      by apply elem_of_difference in H2 as [_ H2].
    Qed.

    #[refine] Global Instance _diff_mem_fst_inst : _diff_mem_fst_sig := { }.
    Proof.
      simpl.
      intros A I s1 s2 x H1.
      split; intros H2.
      + by apply elem_of_difference.
      + by apply elem_of_difference in H2 as [H2 _].
    Qed.

    Global Instance _subset_inst : _subset_sig :=
      { subset := fun A _ s1 s2 => forall x, mem x s1 -> mem x s2 }.

    #[refine] Global Instance _subset_def_inst : _subset_def_sig := { }.
    Proof.
      auto.
    Qed.

    Global Instance _map_inst : _map_sig :=
      { map := fun A B _ _ f s => {[x | ∃ y, (f y) = x /\ y ∈ s]} }.

    #[refine] Global Instance _set_map_inst : _set_map_sig := { }.
    Proof.
      intros.
      split.
      + intros H1. by apply -> (@elem_of_PropSet A) in H1.
      + intros. by apply (@elem_of_PropSet A).
    Qed.

    Global Instance _partition_inst : _partition_sig :=
      { partition :=
          fun A _ P s =>
            ({[x | x ∈ s /\ P x]}, {[x | x ∈ s /\ ~ P x]}) }.

    #[refine] Global Instance _partition_l_mem_inst : _partition_l_mem_sig := { }.
    Proof.
      simpl.
      intros A I f s x p1 p2 H1 H2 H3.
      injection H3.
      intros.
      subst.
      by apply elem_of_PropSet.
    Qed.

    #[refine] Global Instance _partition_r_mem_inst : _partition_r_mem_sig := { }.
    Proof.
      simpl.
      intros A I f s x p1 p2 H1 H2 H3.
      injection H3.
      intros.
      subst.
      by apply elem_of_PropSet.
    Qed.

    Global Declare Instance _cardinal_inst : _cardinal_sig.
    Global Declare Instance _finite_inst : _finite_sig.
    Global Declare Instance _finite_def_inst : _finite_def_sig.
    Global Declare Instance _cardinal_nonneg_inst : _cardinal_nonneg_sig.
    Global Declare Instance _cardinal_empty_inst : _cardinal_empty_sig.
    Global Declare Instance _cardinal_remove_mem_inst : _cardinal_remove_mem_sig.
    Global Declare Instance _cardinal_remove_not_mem_inst : _cardinal_remove_not_mem_sig.
    Global Declare Instance _cardinal_add_inst : _cardinal_add_sig.
    Global Declare Instance _cardinal_add_mem_inst : _cardinal_add_mem_sig.

    Global Instance _of_seq_inst : _of_seq_sig :=
      { of_seq := fun A _ s => {[x | Sequence.mem x s]} }.

    #[refine] Global Instance _of_seq_mem_inst : _of_seq_mem_sig := { }.
    Proof.
      auto.
    Qed.

    Global Declare Instance _to_seq_inst : _to_seq_sig.
    Global Declare Instance _to_seq_mem_inst : _to_seq_mem_sig.
    Global Declare Instance _fold_inst : _fold_sig.
    Global Declare Instance _fold_def_inst : _fold_def_sig.
    End _Set.

  Global Instance _map_set_inst : _map_set_sig :=
    { map_set :=
        fun A B _ _ f x y =>
          λ z, if (decide (x = z)) then y else f z }.

  #[refine] Global Instance _map_set_def_inst : _map_set_def_sig := { }.
  Proof.
    simpl.
    intros.
    by rewrite decide_True.
  Qed.

  #[refine] Global Instance _map_set_def_neq_inst : _map_set_def_neq_sig := { }.
  Proof.
    simpl.
    intros.
    by rewrite decide_False.
  Qed.

  Module Map.
    Import Map.

    Global Instance _domain_inst : _domain_sig :=
      { domain := fun A B _ _ x m => {[y | m y <> x]} }.

    #[refine] Global Instance _domain_mem_inst : _domain_mem_sig := { }.
    Proof.
      auto.
    Qed.
  End Map.

End Proofs.

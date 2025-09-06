Set Implicit Arguments.

Require Import gospelstdlib_verified_stdpp.

Import Stdlib.

Require Import iris.proofmode.proofmode iris.heap_lang.proofmode iris.heap_lang.notation iris.prelude.options.

Section spec.

  Context `{!heapGS Σ}. Notation iProp := (iProp Σ).

  Require Import Stdlib.ZArith.BinIntDef.

  Local Open Scope Z_scope.

  Import Sequence.

  Parameter T : Sequence.t Z -> val -> iProp.

  Parameter _create : val.

  Parameter _create_spec :
    {{{True}}}
      _create #()
      {{{_prog_q, RET _prog_q; (T empty _prog_q)}}}.

  Parameter _push : val.

  Parameter _push_spec :
    forall _prog_q : val,
    forall q : Sequence.t Z,
    forall _prog_x : val,
    forall x : Z,
      {{{(T q _prog_q)}}}
        _push _prog_q _prog_x
        {{{RET #(); T (cons x q) _prog_q}}}.

  Parameter _clear : val.

  Definition _clear_spec :=
    forall _prog_q : val,
    forall q : Sequence.t Z,
      {{{(T q _prog_q)}}}
        _clear _prog_q
        {{{RET #(); T empty _prog_q}}}.

  Parameter clear_spec_proof : _clear_spec.

  Parameter _copy : val.

  Parameter _copy_spec :
    forall _prog_q1 : val,
    forall q1 : Sequence.t Z,
      {{{(T q1 _prog_q1)}}}
        _copy _prog_q1
        {{{
            _prog_q2, RET _prog_q2; ((T q1 _prog_q1) ∗ (((T q1 _prog_q2))))
        }}}.

  Parameter _is_empty : val.

  Parameter _is_empty_spec :
    forall _prog_q : val,
    forall q : Sequence.t Z,
      {{{(T q _prog_q)}}}
        _is_empty _prog_q
      {{{b : b, RET b; ⌜True⌝ }}}.

  Parameter _length : val.

  Parameter _length_spec :
    forall _prog_q : val,
    forall q : Sequence.t Z,
      {{{(T q _prog_q)}}}
        _length _prog_q q
        {{{(
                fun _prog_l : val =>
                  ((T q _prog_q) ∗ ⌜ (((Sequence.length q) = l)) ⌝)
        )}}}.

  Parameter _transfer : val.

  Parameter _transfer_spec :
    forall _prog_q1 : val,
    forall q1 : Sequence.t Z,
    forall _prog_q2 : val,
    forall q2 : Sequence.t Z,
      {{{(((T q1 _prog_q1) ∗ (T q2 _prog_q2)))}}}
        _transfer _prog_q1 q1 _prog_q2 q2
        {{{(fun _ : unit => ((T empty _prog_q1) ∗ (T (app q2 q1) _prog_q2)))}}}.

End spec.

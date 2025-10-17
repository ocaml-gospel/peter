Set Implicit Arguments.

Require Import Stdlib.ZArith.BinIntDef.

Require Import iris.proofmode.proofmode iris.heap_lang.proofmode iris.heap_lang.notation iris.prelude.options.

Require Import Stdlib_stdpp.gospelstdlib_verified_stdpp.

Import Stdlib.

Section spec.

Context `{!heapGS Σ}. Notation iProp := (iProp Σ).

Local Open Scope Z_scope.

Import Sequence.

Parameter T : sequence Z -> val -> iProp.
Parameter _create : val.

Parameter _create_spec :
  {{{ True }}}
  _create #()
  {{{ __q, RET __q; T empty __q }}}.

Parameter _push : val.

Parameter _push_spec :
  forall __q : val,
  forall q : sequence Z,
  forall __x : val,
  forall x : Z,
  {{{ (T q __q) ∗ (Int x __x) }}}
  _push __q __x
  {{{ RET #(); (T (cons x q) __q) ∗ (Int x __x) }}}.

Parameter _clear : val.

Parameter _clear_spec :
  forall __q : val,
  forall q : sequence Z,
  {{{ T q __q }}}
  _clear __q
  {{{ RET #(); T empty __q }}}.

Parameter _copy : val.

Parameter _copy_spec :
  forall __q1 : val,
  forall q1 : sequence Z,
  {{{ T q1 __q1 }}}
  _copy __q1
  {{{ __q2, RET __q2; (T q1 __q1) ∗ (T q1 __q2) }}}.

Parameter _is_empty : val.
Parameter _is_empty_spec :
  forall __q : val,
  forall q : sequence Z,
  {{{ T q __q }}}
  _is_empty __q
  {{{ __b, RET __b; (T q __q) ∗ (Bool (q = empty) __b) }}}.

Parameter _length : val.

Parameter _length_spec :
  forall __q : val,
  forall q : sequence Z,
  {{{ T q __q }}}
  _length __q
  {{{ __l, RET __l; (T q __q) ∗ (Int (Sequence.length q) __l) }}}.

Parameter _transfer : val.

Parameter _transfer_spec :
  forall __q1 : val,
  forall q1 : sequence Z,
  forall __q2 : val,
  forall q2 : sequence Z,
  {{{ (T q1 __q1) ∗ (T q2 __q2) }}}
  _transfer __q1 __q2
  {{{ RET #(); (T empty __q1) ∗ (T (app q2 q1) __q2) }}}.

End spec.

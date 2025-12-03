Require Import Stdlib_stdpp.iris_core.

Local Open Scope Z_scope.

Import Proofs Declarations.

Require Import Stdlib.Floats.Floats Stdlib.ZArith.BinIntDef Stdlib.Strings.Ascii.

Require Import iris.proofmode.proofmode iris.heap_lang.proofmode iris.heap_lang.notation iris.prelude.options.

Parameter Σ : gFunctors.

Notation iProp := (iProp Σ).

Module Declarations.

  Import Bag.

  Class _Priority_sig := {
    Priority : val -> Z -> iProp
  }.

  Class _T_sig := {
    T : forall { A }, val -> (bag (val * Z)) -> iProp
  }.

  Class _create_sig := {
    create : val
  }.

  Class _create_spec_sig := {
    create_spec : forall { A }, forall `{ Inhabited A }, {{{
    True
     }}}
    _create  #()
    {{{  __q , RET __q;  ∃ (q :bag (val * Z)),  T __q q   }}}
  }.

  Class _add_sig := {
    add : val
  }.

  Class _add_spec_sig := {
    add_spec : forall { A }, forall
    `{ Inhabited A }
    (__q :t A)
    (q :bag (val * Z))
    (__x :A)
    (x :val)
    (__i :priority)
    (i :Z),
    {{{  T __q q∗Val __x x∗Priority __i i  }}}
    _add  __q __x __i
    {{{ RET #();
    ∃ (_q' :bag (val * Z)),
    T __q _q'∗Val __x x∗Priority __i i

     }}}
  }.

  Definition is_min  {A} (x :A) (i :Z) (q :bag (A * Z)) : Prop :=
  (belongs ( x, i ) q) /\ (forall (j :Z) (y :A), (j < i) -> (neg_belongs (
    y,
    j
    ) q)).

  Class _extract_sig := {
    extract : val
  }.

  Class _extract_spec_sig := {
    extract_spec : forall { A }, forall
    `{ Inhabited A }
    (__q :t A)
    (q :bag (val * Z)),
    {{{  T __q q  }}}
    _extract  __q
    {{{  __x , RET __x;
    ∃ (_q' :bag (val * Z)) (x :option val),
    T __q _q'∗Option __x x

     }}}
  }.

  Class _is_empty_sig := {
    is_empty : val
  }.

  Class _is_empty_spec_sig := {
    is_empty_spec : forall { A }, forall
    `{ Inhabited A }
    (__q :t A)
    (q :bag (val * Z)),
    {{{  T __q q  }}}
    _is_empty  __q
    {{{  __b , RET __b;
    ∃ (b :Prop),  T __q q∗Bool __b b
     }}}
  }.

  Class _cardinal_sig := {
    cardinal : val
  }.

  Class _cardinal_spec_sig := {
    cardinal_spec : forall { A }, forall
    `{ Inhabited A }
    (__q :t A)
    (q :bag (val * Z)),
    {{{  T __q q  }}}
    _cardinal  __q
    {{{  __n , RET __n;  ∃ (n :Z),  T __q q∗Int __n n   }}}
  }.

  Class _reset_sig := {
    reset : val
  }.

  Class _reset_spec_sig := {
    reset_spec : forall { A }, forall
    `{ Inhabited A }
    (__q :t A)
    (q :bag (val * Z)),
    {{{  T __q q  }}}
    _reset  __q
    {{{ RET #();  ∃ (_q' :bag (val * Z)),  T __q _q'   }}}
  }.

End Declarations.

Module Type Obligations.

Import Declarations.

Import Bag.

Global Declare Instance _Priority_inst :_Priority_sig.

Global Declare Instance _T_inst :_T_sig.

Global Declare Instance _create_inst :_create_sig.

Global Declare Instance _create_spec_inst :_create_spec_sig.

Global Declare Instance _add_inst :_add_sig.

Global Declare Instance _add_spec_inst :_add_spec_sig.

Global Declare Instance _extract_inst :_extract_sig.

Global Declare Instance _extract_spec_inst :_extract_spec_sig.

Global Declare Instance _is_empty_inst :_is_empty_sig.

Global Declare Instance _is_empty_spec_inst :_is_empty_spec_sig.

Global Declare Instance _cardinal_inst :_cardinal_sig.

Global Declare Instance _cardinal_spec_inst :_cardinal_spec_sig.

Global Declare Instance _reset_inst :_reset_sig.

Global Declare Instance _reset_spec_inst :_reset_spec_sig.

End Obligations.
Require Import Stdlib_stdpp.gospelstdlib_verified_stdpp Stdlib_stdpp.gospelstdlib_mli_stdpp.

Local Open Scope Z_scope.

Import Proofs Declarations.

Require Import Stdlib.Floats.Floats Stdlib.ZArith.BinIntDef Stdlib.Strings.Ascii.

Require Import iris.proofmode.proofmode iris.heap_lang.proofmode iris.heap_lang.notation iris.prelude.options.

Module Type wow.
  Parameter Σ : gFunctors.
End wow.

Module Declarations.

  Import Bag.
  Parameter Σ : gFunctors.
  Notation iProp := (iProp Σ).

  Class _T_sig := {
    T : forall { A }, val ->
    (bag (Corelib.Init.Datatypes.prod A Z)) ->
    iProp
  }.

  Class _create_sig := {
      _create : val
    }.

  Class _create_spec_sig := {
    create_spec : forall { A }, forall `{ Inhabited A }, {{{  True }}}
    _create  #()
    {{{  __q , RET __q;
    ∃ (q :bag (Corelib.Init.Datatypes.prod A Z)),
    T __q q

     }}}
  }.

End Declarations.

Module Type Obligations.

Import Declarations.

Import Bag.

Global Declare Instance _T_inst :_T_sig.

Global Declare Instance _create_spec_inst :_create_spec_sig.

End Obligations.

Require Import Stdlib_stdpp.iris_core.

Local Open Scope Z_scope.

Import Proofs Declarations.

Require Import Stdlib.Floats.Floats Stdlib.ZArith.BinIntDef Stdlib.Strings.Ascii.

Require Import iris.proofmode.proofmode iris.heap_lang.proofmode iris.heap_lang.notation iris.prelude.options.

Module Declarations (Heap :H) .

  Import Heap.

  Import Bag.

  Definition priority : Type :=
  val.

  Class _Priority_sig := {
    Priority : priority -> Z -> iProp
  }.

  Definition t (A :Type) : Type :=
  val.

  Class _T_sig := {
    T : forall { A }, (t A) ->
    (bag (Corelib.Init.Datatypes.prod val Z)) ->
    iProp
  }.

  Class _create_sig := {
    create : val
  }.

  Class _create_spec_sig `{ @_create_sig } `{ @_T_sig } := {
    create_spec : forall { A }, forall
    `{ _T_sig }
    `{ Inhabited A },
    {{{ True }}}
    create  #()
    {{{  (__q :t A) , RET (__q :t A);
    ∃ (q :bag (Corelib.Init.Datatypes.prod val Z)),
    T __q q

     }}}
  }.

End Declarations.

Module Type Obligations (Heap :H) .

  Module Declarations := Declarations
Heap.

  Import Declarations.

  Import Bag.

  Global Declare Instance _Priority_inst :_Priority_sig.

  Global Declare Instance _T_inst :_T_sig.

  Global Declare Instance _create_inst :_create_sig.

  Global Declare Instance _create_spec_inst :_create_spec_sig.

End Obligations.
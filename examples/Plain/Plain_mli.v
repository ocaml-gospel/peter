Require Import Gospel.iris.base.

Local Open Scope Z_scope.

Require Import Stdlib.Floats.Floats Stdlib.ZArith.BinIntDef Stdlib.Strings.Ascii.

Require Import iris.proofmode.proofmode iris.heap_lang.proofmode iris.heap_lang.notation iris.prelude.options.

Module Declarations (Heap :H) .

  Import Heap.

  Module Primitives := Primitives Heap.
  Import Primitives.

  Import Bag.

  Definition priority'' : Type :=
  val.

  Class _Priority_sig := {
    Priority : priority'' -> integer -> iProp
  }.

  Definition t'' (A :Type) : Type :=
  val.

  Class _T_sig := {
    T : forall { A }, (t'' A) ->
    (bag (val * integer)) ->
    iProp
  }.

  Class _create_sig := {
    create : val
  }.

  Class _create_spec_sig `{ @_create_sig } `{ @_T_sig } := {
    create_spec : forall { A }, forall
    `{ _T_sig }
    `{ Inhabited A },
    {{{  True  }}}
    create  #()
    {{{  (q'' :t'' A) , RET (q'' :t'' A);
      ∃ (q :bag (val * integer)),  T q'' q   }}}
  }.

  Class _add_sig := {
    add : val
  }.

  Class _add_spec_sig
  `{ @_add_sig }
  `{ @_T_sig }
  `{ @_Priority_sig } := {
    add_spec : forall { A }, forall
    `{ _T_sig }
    `{ _Priority_sig }
    `{ Inhabited A }
    (q'' :t A)
    (q :bag (val * integer))
    (x'' :A)
    (x :val)
    (i'' :priority)
    (i :integer),
    {{{  T q'' q∗Val x'' x∗Priority i'' i  }}}
    add  (q'' :t A) (x'' :A) (i'' :priority)
    {{{ RET #();

    ∃ (_q' :bag (val * integer)),
    T q'' _q'∗Val x'' x∗Priority i'' i

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

  Global Declare Instance _add_inst :_add_sig.

  Global Declare Instance _add_spec_inst :_add_spec_sig.

End Obligations.

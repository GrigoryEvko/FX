import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap

/-! # SwapChain — the closure normalized to single-swap chains (FREE-6b)

`AtomicTraceEquiv` is a symmetric-transitive-congruence CLOSURE — inducting over it
directly strands the invariance theorem at the `consCongr` arm (knowing two tails share a
normal form says nothing about the consed lists).  This file normalizes the closure to
CHAINS of single steps so downstream theorems only ever reason about ONE adjacent swap at
ONE position:

  * `OneAdjacentSwap` — one adjacent transposition, in either direction, at any depth
    (symmetric by construction: the two head arms mirror each other);
  * `OneAdjacentSwapChain` — the reflexive-transitive chain, with `trans` / `symm` /
    `consCongr` all ADMISSIBLE (chains append, reverse, and map under a head cons);
  * `oneAdjacentSwapChain_iff_atomicTraceEquiv` — ★ the closure identification: the
    chain relation IS the atomic trace equivalence.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## One swap, anywhere, either direction -/

/-- One adjacent atom transposition, in either direction, at any depth. -/
inductive OneAdjacentSwap (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} :
    List (SpineAtom signature overallSource overallTarget) →
    List (SpineAtom signature overallSource overallTarget) → Prop where
  /-- The swap at the head, along the constructor direction. -/
  | here {firstList secondList : List (SpineAtom signature overallSource overallTarget)} :
      SpineAtomSwap signature firstList secondList →
      OneAdjacentSwap signature firstList secondList
  /-- The swap at the head, against the constructor direction. -/
  | hereReversed {firstList secondList :
      List (SpineAtom signature overallSource overallTarget)} :
      SpineAtomSwap signature secondList firstList →
      OneAdjacentSwap signature firstList secondList
  /-- The swap sits deeper (an untouched head atom passes through). -/
  | deeper (atom : SpineAtom signature overallSource overallTarget)
      {firstList secondList : List (SpineAtom signature overallSource overallTarget)} :
      OneAdjacentSwap signature firstList secondList →
      OneAdjacentSwap signature (atom :: firstList) (atom :: secondList)

/-- One adjacent swap is symmetric by construction. -/
theorem OneAdjacentSwap.symm {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (oneSwap : OneAdjacentSwap signature firstList secondList) :
    OneAdjacentSwap signature secondList firstList := by
  induction oneSwap with
  | here swapStep => exact OneAdjacentSwap.hereReversed swapStep
  | hereReversed swapStep => exact OneAdjacentSwap.here swapStep
  | deeper atom _ innerHypothesis => exact OneAdjacentSwap.deeper atom innerHypothesis

/-- One adjacent swap includes into the atomic closure. -/
theorem OneAdjacentSwap.toAtomicTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (oneSwap : OneAdjacentSwap signature firstList secondList) :
    AtomicTraceEquiv signature firstList secondList := by
  induction oneSwap with
  | here swapStep => exact AtomicTraceEquiv.ofSwap swapStep
  | hereReversed swapStep => exact AtomicTraceEquiv.symm (AtomicTraceEquiv.ofSwap swapStep)
  | deeper atom _ innerHypothesis => exact AtomicTraceEquiv.consCongr atom innerHypothesis

/-! ## The chain -/

/-- The reflexive-transitive chain of single adjacent swaps. -/
inductive OneAdjacentSwapChain (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} :
    List (SpineAtom signature overallSource overallTarget) →
    List (SpineAtom signature overallSource overallTarget) → Prop where
  /-- The empty chain. -/
  | refl (spineList : List (SpineAtom signature overallSource overallTarget)) :
      OneAdjacentSwapChain signature spineList spineList
  /-- Advance by one swap, then continue. -/
  | advance {firstList midList secondList :
      List (SpineAtom signature overallSource overallTarget)} :
      OneAdjacentSwap signature firstList midList →
      OneAdjacentSwapChain signature midList secondList →
      OneAdjacentSwapChain signature firstList secondList

/-- A one-step chain. -/
theorem OneAdjacentSwapChain.single {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (oneSwap : OneAdjacentSwap signature firstList secondList) :
    OneAdjacentSwapChain signature firstList secondList :=
  OneAdjacentSwapChain.advance oneSwap (OneAdjacentSwapChain.refl secondList)

/-- Chains append. -/
theorem OneAdjacentSwapChain.trans {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList thirdList :
      List (SpineAtom signature overallSource overallTarget)}
    (firstChain : OneAdjacentSwapChain signature firstList secondList)
    (secondChain : OneAdjacentSwapChain signature secondList thirdList) :
    OneAdjacentSwapChain signature firstList thirdList := by
  induction firstChain with
  | refl _ => exact secondChain
  | advance headSwap _ innerHypothesis =>
      exact OneAdjacentSwapChain.advance headSwap (innerHypothesis secondChain)

/-- Chains reverse (each step is symmetric, appended in reverse order). -/
theorem OneAdjacentSwapChain.symm {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (chain : OneAdjacentSwapChain signature firstList secondList) :
    OneAdjacentSwapChain signature secondList firstList := by
  induction chain with
  | refl spineList => exact OneAdjacentSwapChain.refl spineList
  | advance headSwap _ innerHypothesis =>
      exact innerHypothesis.trans (OneAdjacentSwapChain.single headSwap.symm)

/-- Chains map under a head cons (every step moves deeper). -/
theorem OneAdjacentSwapChain.consCongr {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atom : SpineAtom signature overallSource overallTarget)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (chain : OneAdjacentSwapChain signature firstList secondList) :
    OneAdjacentSwapChain signature (atom :: firstList) (atom :: secondList) := by
  induction chain with
  | refl spineList => exact OneAdjacentSwapChain.refl (atom :: spineList)
  | advance headSwap _ innerHypothesis =>
      exact OneAdjacentSwapChain.advance (OneAdjacentSwap.deeper atom headSwap)
        innerHypothesis

/-! ## The closure identification -/

/-- Chains include into the atomic closure. -/
theorem OneAdjacentSwapChain.toAtomicTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (chain : OneAdjacentSwapChain signature firstList secondList) :
    AtomicTraceEquiv signature firstList secondList := by
  induction chain with
  | refl spineList => exact AtomicTraceEquiv.refl spineList
  | advance headSwap _ innerHypothesis =>
      exact AtomicTraceEquiv.trans headSwap.toAtomicTraceEquiv innerHypothesis

/-- The atomic closure flattens into a chain — every closure operator is admissible for
chains, so the induction goes arm by arm. -/
theorem AtomicTraceEquiv.toOneAdjacentSwapChain {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv signature firstList secondList) :
    OneAdjacentSwapChain signature firstList secondList := by
  induction traceEquiv with
  | ofSwap swapStep =>
      exact OneAdjacentSwapChain.single (OneAdjacentSwap.here swapStep)
  | refl spineList => exact OneAdjacentSwapChain.refl spineList
  | symm _ innerHypothesis => exact innerHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis
  | consCongr atom _ innerHypothesis =>
      exact OneAdjacentSwapChain.consCongr atom innerHypothesis

/-- ★ **The closure identification**: single-swap chains ARE the atomic trace
equivalence.  Downstream, per-single-swap invariance plus chain induction replaces
reasoning about the raw closure (whose `consCongr` arm strands normal-form
inductions). -/
theorem oneAdjacentSwapChain_iff_atomicTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (firstList secondList : List (SpineAtom signature overallSource overallTarget)) :
    OneAdjacentSwapChain signature firstList secondList
      ↔ AtomicTraceEquiv signature firstList secondList :=
  ⟨OneAdjacentSwapChain.toAtomicTraceEquiv, AtomicTraceEquiv.toOneAdjacentSwapChain⟩

end FX1Poly.Polygraph

import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupSpine

/-! # AllCupAritySwapTransport — the pure-cup regime transports along the atomic swap DIRECTLY

The cup-interchange base case reorders one pure-cup spine into another by disjoint-atom
transpositions and must stay pure cup throughout.  The shipped route
(`allCupArity_preservedOfAtomicTraceEquiv`) proved this by DETOURING through the `Nat` cap
count (`AllCupArity ↔ capAtomCount = 0` via `allCupArity_ofCapAtomCountZero`), which drags in
the walking-adjunction classifier `adjunctionSpineAtom_isCupOrCap` — pinning the whole leg to
one signature.

This brick eliminates the classifier: it transports `AllCupArity` DIRECTLY through the atomic
swap, signature-generic, by matching the swap constructor and inverting the two head arities.
The atomic swap (`SpineAtomSwap.swap`) transposes two adjacent atoms KEEPING each atom's
generator — only the whisker contexts re-thread — so each atom's `generatorDom` / `generatorCod`
is carried unchanged; the two cup-arity witnesses merely commute past one another.  The head
`AllCupArity.cons` fields therefore slot into the swapped positions by `rfl`.

  * `allCupArity_ofAtomicSwap` / `allCupArity_ofAtomicSwap_rev` — one swap transports the
    pure-cup witness forward / backward (double `cases` on the two-atom prefix).
  * `allCupArity_atomicConsCongr` — a shared head atom passes a transport through the tail.
  * ★ `allCupArity_iff_ofAtomicTraceEquiv` — the BICONDITIONAL closure over the whole atomic
    equivalence.  A biconditional motive is FORCED: the one-directional induction fails on the
    `symm` arm (the IH is the converse of what is needed).

Empirically de-risked FIRST at the faithful Init-only toy (`scratchpad/probe.lean`, machine-
checked): the double-`cases` transport is axiom-clean and the boundary defeq fires; the count
detour (Route A) leaks `propext + Quot.sound` via the `Bool ==` extraction.

Raw Lean 4 + Init; STRUCTURAL (`cases` + induction on the closure), signature-generic; per-
declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **One swap transports the pure-cup witness forward.**  The swap transposes the two head
atoms keeping their generators, so the left atom's cup-arity witnesses `(hasCupDomLeft,
hasCupCodLeft)` and the right atom's `(hasCupDomRight, hasCupCodRight)` are exactly what the
swapped positions demand — `generatorDom` / `generatorCod` are read off the (unchanged)
generator, so the fits are `rfl`. -/
theorem allCupArity_ofAtomicSwap {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (swapStep : SpineAtomSwap signature firstList secondList)
    (firstPureCup : AllCupArity firstList) : AllCupArity secondList := by
  cases swapStep with
  | swap generatorLeft generatorRight leftAcc inertPath rightAcc rest =>
      cases firstPureCup with
      | cons hasCupDomLeft hasCupCodLeft restAfterLeft =>
          cases restAfterLeft with
          | cons hasCupDomRight hasCupCodRight restRemaining =>
              exact AllCupArity.cons hasCupDomRight hasCupCodRight
                (AllCupArity.cons hasCupDomLeft hasCupCodLeft restRemaining)

/-- **One swap transports the pure-cup witness backward** — the mirror of
`allCupArity_ofAtomicSwap`, inverting the swapped-side witness onto the original ordering. -/
theorem allCupArity_ofAtomicSwap_rev {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (swapStep : SpineAtomSwap signature firstList secondList)
    (secondPureCup : AllCupArity secondList) : AllCupArity firstList := by
  cases swapStep with
  | swap generatorLeft generatorRight leftAcc inertPath rightAcc rest =>
      cases secondPureCup with
      | cons hasCupDomRight hasCupCodRight restAfterRight =>
          cases restAfterRight with
          | cons hasCupDomLeft hasCupCodLeft restRemaining =>
              exact AllCupArity.cons hasCupDomLeft hasCupCodLeft
                (AllCupArity.cons hasCupDomRight hasCupCodRight restRemaining)

/-- **A shared head atom passes a tail transport through.**  Peel the head cup witness, apply
the tail transport, and rebuild the same head — the head-cons congruence for the pure-cup
predicate. -/
theorem allCupArity_atomicConsCongr {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atom : SpineAtom signature overallSource overallTarget)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (transportTail : AllCupArity firstList → AllCupArity secondList) :
    AllCupArity (atom :: firstList) → AllCupArity (atom :: secondList) := by
  intro consPureCup
  cases consPureCup with
  | cons hasCupDom hasCupCod restPureCup =>
      exact AllCupArity.cons hasCupDom hasCupCod (transportTail restPureCup)

/-- ★ **The pure-cup regime transports along the whole atomic equivalence, both directions.**
Structural induction on the atomic closure.  A BICONDITIONAL motive is FORCED: the one-
directional `AllCupArity firstList → AllCupArity secondList` induction cannot close the `symm`
arm, whose induction hypothesis is the converse implication.  Each swap uses
`allCupArity_ofAtomicSwap` / `_rev`; reflexivity is `id`; symmetry flips the pair; transitivity
composes forward-then-forward and backward-then-backward; the head-congruence threads through
`allCupArity_atomicConsCongr`.  Signature-generic — the walking-adjunction classifier is gone. -/
theorem allCupArity_iff_ofAtomicTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (atomicEquiv : AtomicTraceEquiv signature firstList secondList) :
    (AllCupArity firstList → AllCupArity secondList)
      ∧ (AllCupArity secondList → AllCupArity firstList) := by
  induction atomicEquiv with
  | ofSwap swapStep =>
      exact ⟨allCupArity_ofAtomicSwap swapStep, allCupArity_ofAtomicSwap_rev swapStep⟩
  | refl spineList => exact ⟨id, id⟩
  | symm _ innerHypothesis => exact ⟨innerHypothesis.2, innerHypothesis.1⟩
  | trans _ _ innerFirst innerSecond =>
      exact ⟨fun firstPureCup => innerSecond.1 (innerFirst.1 firstPureCup),
        fun thirdPureCup => innerFirst.2 (innerSecond.2 thirdPureCup)⟩
  | consCongr atom _ innerHypothesis =>
      exact ⟨allCupArity_atomicConsCongr atom innerHypothesis.1,
        allCupArity_atomicConsCongr atom innerHypothesis.2⟩

/-! ## Honesty marker -/

/-- **Honesty marker — the pure-cup regime transports along the atomic swap DIRECTLY, classifier-
free.**  `allCupArity_iff_ofAtomicTraceEquiv`: two spine lists related by `AtomicTraceEquiv`
transport `AllCupArity` in both directions, proved by matching the swap constructor and inverting
the two head arities — no cap-count detour, no `adjunctionSpineAtom_isCupOrCap`, signature-generic.
This is the Route-B keystone that lets `allCupArity_preservedOfAtomicTraceEquiv` (and the pure-cup
peel it feeds) drop the walking-adjunction classifier.  What this marker does NOT claim: any
matching-model content — this is purely the arity-multiset transport.  `= true`. -/
def fxMode_hasAllCupAritySwapTransport : Bool := true

end FX1Poly.Polygraph

import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCapSpine

/-! # WalkingString/StringAllCapAritySwapTransport — the pure-CAP regime transports along the atomic swap
DIRECTLY (FC-3 r22, B2 P4)

The cap-head discharge needs `AllCapArity` to travel across an `AtomicTraceEquiv` so the matched remainder inherits
pure-cap from the source spine.  This is the exact dual of `WalkingAdjunction/AllCupAritySwapTransport`'s
`allCupArity_iff_ofAtomicTraceEquiv`, for `AllCapArity` instead of `AllCupArity` — the same classifier-FREE,
signature-GENERIC transport (no `Nat` cup/cap count detour, no `adjunctionSpineAtom_isCupOrCap`, so it runs at any
signature including the adjoint triple).  The atomic swap (`SpineAtomSwap.swap`) transposes two adjacent atoms
KEEPING each atom's generator — only the whisker contexts re-thread — so each atom's `generatorDom` / `generatorCod`
is carried unchanged and the two cap-arity witnesses merely commute past one another; the head `AllCapArity.cons`
fields slot into the swapped positions by `rfl`.

  * `allCapArity_ofAtomicSwap` / `allCapArity_ofAtomicSwap_rev` — one swap transports the pure-cap witness forward /
    backward (double `cases` on the two-atom prefix);
  * `allCapArity_atomicConsCongr` — a shared head atom passes a transport through the tail;
  * ★ `allCapArity_iff_ofAtomicTraceEquiv` — the BICONDITIONAL closure over the whole atomic equivalence (the
    biconditional motive is FORCED: the one-directional induction fails on the `symm` arm);
  * `allCapArity_preservedOfAtomicTraceEquiv` — the forward extraction (`.1`), the direction the cap-head discharge
    consumes to inherit pure-cap on the matched remainder.

Raw Lean 4 + Init; STRUCTURAL (`cases` + induction on the closure), signature-generic; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **One swap transports the pure-cap witness forward.**  The swap transposes the two head atoms keeping their
generators, so the left atom's cap-arity witnesses `(hasCapDomLeft, hasCapCodLeft)` and the right atom's
`(hasCapDomRight, hasCapCodRight)` are exactly what the swapped positions demand — `generatorDom` / `generatorCod`
are read off the (unchanged) generator, so the fits are `rfl`. -/
theorem allCapArity_ofAtomicSwap {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (swapStep : SpineAtomSwap signature firstList secondList)
    (firstPureCap : AllCapArity firstList) : AllCapArity secondList := by
  cases swapStep with
  | swap generatorLeft generatorRight leftAcc inertPath rightAcc rest =>
      cases firstPureCap with
      | cons hasCapDomLeft hasCapCodLeft restAfterLeft =>
          cases restAfterLeft with
          | cons hasCapDomRight hasCapCodRight restRemaining =>
              exact AllCapArity.cons hasCapDomRight hasCapCodRight
                (AllCapArity.cons hasCapDomLeft hasCapCodLeft restRemaining)

/-- **One swap transports the pure-cap witness backward** — the mirror of `allCapArity_ofAtomicSwap`, inverting
the swapped-side witness onto the original ordering. -/
theorem allCapArity_ofAtomicSwap_rev {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (swapStep : SpineAtomSwap signature firstList secondList)
    (secondPureCap : AllCapArity secondList) : AllCapArity firstList := by
  cases swapStep with
  | swap generatorLeft generatorRight leftAcc inertPath rightAcc rest =>
      cases secondPureCap with
      | cons hasCapDomRight hasCapCodRight restAfterRight =>
          cases restAfterRight with
          | cons hasCapDomLeft hasCapCodLeft restRemaining =>
              exact AllCapArity.cons hasCapDomLeft hasCapCodLeft
                (AllCapArity.cons hasCapDomRight hasCapCodRight restRemaining)

/-- **A shared head atom passes a tail transport through.**  Peel the head cap witness, apply the tail transport,
and rebuild the same head — the head-cons congruence for the pure-cap predicate. -/
theorem allCapArity_atomicConsCongr {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (atom : SpineAtom signature overallSource overallTarget)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (transportTail : AllCapArity firstList → AllCapArity secondList) :
    AllCapArity (atom :: firstList) → AllCapArity (atom :: secondList) := by
  intro consPureCap
  cases consPureCap with
  | cons hasCapDom hasCapCod restPureCap =>
      exact AllCapArity.cons hasCapDom hasCapCod (transportTail restPureCap)

/-- ★ **The pure-cap regime transports along the whole atomic equivalence, both directions.**  Structural
induction on the atomic closure.  A BICONDITIONAL motive is FORCED: the one-directional
`AllCapArity firstList → AllCapArity secondList` induction cannot close the `symm` arm, whose induction hypothesis
is the converse implication.  Each swap uses `allCapArity_ofAtomicSwap` / `_rev`; reflexivity is `id`; symmetry
flips the pair; transitivity composes forward-then-forward and backward-then-backward; the head-congruence threads
through `allCapArity_atomicConsCongr`.  Signature-generic — the exact dual of the cup transport, classifier-free. -/
theorem allCapArity_iff_ofAtomicTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (atomicEquiv : AtomicTraceEquiv signature firstList secondList) :
    (AllCapArity firstList → AllCapArity secondList)
      ∧ (AllCapArity secondList → AllCapArity firstList) := by
  induction atomicEquiv with
  | ofSwap swapStep =>
      exact ⟨allCapArity_ofAtomicSwap swapStep, allCapArity_ofAtomicSwap_rev swapStep⟩
  | refl spineList => exact ⟨id, id⟩
  | symm _ innerHypothesis => exact ⟨innerHypothesis.2, innerHypothesis.1⟩
  | trans _ _ innerFirst innerSecond =>
      exact ⟨fun firstPureCap => innerSecond.1 (innerFirst.1 firstPureCap),
        fun thirdPureCap => innerFirst.2 (innerSecond.2 thirdPureCap)⟩
  | consCongr atom _ innerHypothesis =>
      exact ⟨allCapArity_atomicConsCongr atom innerHypothesis.1,
        allCapArity_atomicConsCongr atom innerHypothesis.2⟩

/-- ★ **The forward pure-cap transport.**  Two spine lists related by `AtomicTraceEquiv` carry `AllCapArity`
forward — the extraction the cap-head discharge consumes so the matched remainder (the target of the bubble
equivalence) inherits pure-cap from the source spine.  The `.1` of the biconditional. -/
theorem allCapArity_preservedOfAtomicTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (atomicEquiv : AtomicTraceEquiv signature firstList secondList)
    (firstPureCap : AllCapArity firstList) : AllCapArity secondList :=
  (allCapArity_iff_ofAtomicTraceEquiv atomicEquiv).1 firstPureCap

/-! ## Honesty marker -/

/-- **Honesty marker — the pure-cap regime transports along the atomic swap DIRECTLY, classifier-free (FC-3 r22,
B2 P4).**  `allCapArity_iff_ofAtomicTraceEquiv`: two spine lists related by `AtomicTraceEquiv` transport
`AllCapArity` in both directions, proved by matching the swap constructor and inverting the two head arities — no
cup-count detour, no classifier, signature-generic.  The exact dual of the cup Route-B keystone
`allCupArity_iff_ofAtomicTraceEquiv`.  `allCapArity_preservedOfAtomicTraceEquiv` is the forward extraction the
cap-head discharge feeds the bubble equivalence into so the matched remainder inherits pure-cap.  What this marker
does NOT claim: any matching-model content — this is purely the arity-multiset transport.  `= true`. -/
def fxMode_hasAllCapAritySwapTransport : Bool := true

end FX1Poly.Polygraph

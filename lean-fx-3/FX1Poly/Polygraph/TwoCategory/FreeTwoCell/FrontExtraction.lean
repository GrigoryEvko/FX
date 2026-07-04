import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SwapRecognizer

/-! # FrontExtraction — the certified front-extraction enumeration (FREE-6b)

The trace normal form is computed by REPEATED MINIMAL EXTRACTION — the classical
lexicographic-normal-form algorithm for trace monoids (least letter of the initial
alphabet first, then recurse).  NOTE the honest algorithmic finding: the two naive
strategies both fail on the same configuration.  With atoms a ⊥ b, b ⊥ c but a, c
dependent and priority a < b < c, the word `cab` is a LOCAL minimum (the adjacent pair
(c, a) is dependent, so no oriented step and no insertion step fires) yet the class
minimum is `bca` — greedy oriented rewriting is not confluent AND naive insertion sort is
trapped at the same point.  Only whole-list extraction sees that `b` commutes past BOTH
`c` and `a`.

This file ships the extraction data layer:

  * `AtomicTraceEquiv.lengthEq` — trace-equivalent spines have equal length (the recursion
    fuel for the normal-form function);
  * `FrontExtraction` — one certified extraction: the atom pulled to the very front by a
    chain of adjacent swaps, the once-mutated remainder behind it, and the
    trace-equivalence certificate riding in the value (the self-certifying discipline);
  * `frontExtractions` — the complete enumeration: the head extracts trivially; every
    extraction from the tail lifts past the head exactly when `recognizeAdjacentSwap`
    certifies the adjacent swap (the candidate mutates by the context shift crossing the
    head, the head joins the remainder mutated once).

The normal-form legs (the minimal-selection function, its correctness, and the
swap-invariance / uniqueness theorem) consume this enumeration downstream.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Length invariance -/

/-- Trace-equivalent spines have equal length: each adjacent swap preserves length and the
closure operators transport it. -/
theorem AtomicTraceEquiv.lengthEq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv signature firstList secondList) :
    firstList.length = secondList.length := by
  induction traceEquiv with
  | ofSwap swapStep => cases swapStep; rfl
  | refl spineList => rfl
  | symm _ innerHypothesis => exact innerHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis
  | consCongr atom _ innerHypothesis =>
      exact congrArg (fun tailLength => tailLength + 1) innerHypothesis

/-! ## The certified extraction -/

/-- **One certified front extraction** from `originalList`: `frontAtom` pulled to the very
front by a chain of adjacent swaps, the mutated `remainder` behind it, and the
trace-equivalence certificate.  The certificate rides in the value, so the normal-form
legs consume it directly — no companion soundness lemma. -/
structure FrontExtraction {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    (originalList : List (SpineAtom signature overallSource overallTarget)) where
  /-- The atom standing at the very front after the extraction. -/
  frontAtom : SpineAtom signature overallSource overallTarget
  /-- The rest of the spine behind the extracted atom (each crossed atom mutated once). -/
  remainder : List (SpineAtom signature overallSource overallTarget)
  /-- The extraction is a chain of adjacent swaps. -/
  isTraceEquivalent : AtomicTraceEquiv signature (frontAtom :: remainder) originalList

/-- The remainder is one atom shorter than the original list — the normal-form
function's fuel arithmetic. -/
theorem FrontExtraction.lengthEq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {originalList : List (SpineAtom signature overallSource overallTarget)}
    (extraction : FrontExtraction originalList) :
    extraction.remainder.length + 1 = originalList.length :=
  extraction.isTraceEquivalent.lengthEq

/-! ## The enumeration -/

/-- ★ **Enumerate every certified front extraction**: the head extracts trivially (the
reflexivity certificate); every extraction from the tail lifts past the head exactly when
the recognizer certifies the adjacent swap — the lifted candidate is the swap's
`firstAfterSwap` (the candidate mutated by crossing the head) and the head joins the
remainder as `secondAfterSwap` (mutated once).  The lifted certificate is the swap
prepended to the tail certificate under the head-cons congruence. -/
def frontExtractions {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    {overallSource overallTarget : signature.graph.Mode} :
    (spineList : List (SpineAtom signature overallSource overallTarget)) →
    List (FrontExtraction spineList)
  | [] => []
  | atom :: rest =>
      ⟨atom, rest, AtomicTraceEquiv.refl (atom :: rest)⟩ ::
      (frontExtractions modeDecEq modalityDecEq rest).filterMap
        (fun tailExtraction =>
          match recognizeAdjacentSwap modeDecEq modalityDecEq atom
              tailExtraction.frontAtom with
          | .inl witness =>
              some ⟨witness.firstAfterSwap,
                witness.secondAfterSwap :: tailExtraction.remainder,
                AtomicTraceEquiv.trans
                  (AtomicTraceEquiv.symm (AtomicTraceEquiv.ofSwap
                    (witness.toSwap tailExtraction.remainder)))
                  (AtomicTraceEquiv.consCongr atom tailExtraction.isTraceEquivalent)⟩
          | .inr _ => none)

end FX1Poly.Polygraph

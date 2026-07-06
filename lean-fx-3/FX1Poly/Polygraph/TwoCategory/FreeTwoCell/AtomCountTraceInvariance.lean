import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.GodementIndependence

/-! # AtomCountTraceInvariance — the cup/cap atom counts are trace-equivalence invariants

`cupAtomCount` / `capAtomCount` count the atoms whose GENERATOR carries the cup arity (`0 ⇒ 2`) or
the cap arity (`2 ⇒ 0`).  The atomic swap (`SpineAtomSwap.swap`) transposes two adjacent atoms
KEEPING each atom's generator — only the whisker contexts re-thread — so each atom's
`generatorDom` / `generatorCod` (hence its cup/cap indicator) is carried unchanged; the two
indicators merely commute past one another.  So both counts survive the whole closure:

  * `cupAtomCount_eq_of_atomicTraceEquiv` / `capAtomCount_eq_of_atomicTraceEquiv` — an
    `AtomicTraceEquiv` of two spine lists forces equal cup / cap atom counts.

This is the multiset-level invariant behind the arc structure's `cupCount` / `capCount` legs: the
total cup and cap tallies are the same on any two trace-equivalent spines, no matter how the atoms
are permuted.

Raw Lean 4 + Init; structural induction on the closure; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The cup-atom count is a trace-equivalence invariant.**  Induction on the atomic closure: the
single swap keeps both generators (only the whisker contexts re-thread), so the two atoms' cup
indicators are unchanged and commute past one another (`Nat.add_left_comm`); reflexivity/symmetry/
transitivity/head-congruence carry through structurally. -/
theorem cupAtomCount_eq_of_atomicTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (atomicEquiv : AtomicTraceEquiv signature firstList secondList) :
    cupAtomCount firstList = cupAtomCount secondList := by
  induction atomicEquiv with
  | ofSwap swapStep =>
      cases swapStep with
      | swap generatorLeft generatorRight leftAcc inertPath rightAcc rest =>
          dsimp only [cupAtomCount]
          exact Nat.add_left_comm _ _ _
  | refl spineList => rfl
  | symm _ innerHypothesis => exact innerHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis
  | consCongr atom _ innerHypothesis =>
      dsimp only [cupAtomCount]
      rw [innerHypothesis]

/-- ★ **The cap-atom count is a trace-equivalence invariant** — the dual of
`cupAtomCount_eq_of_atomicTraceEquiv`, same swap-keeps-the-generators argument on the cap indicator. -/
theorem capAtomCount_eq_of_atomicTraceEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (atomicEquiv : AtomicTraceEquiv signature firstList secondList) :
    capAtomCount firstList = capAtomCount secondList := by
  induction atomicEquiv with
  | ofSwap swapStep =>
      cases swapStep with
      | swap generatorLeft generatorRight leftAcc inertPath rightAcc rest =>
          dsimp only [capAtomCount]
          exact Nat.add_left_comm _ _ _
  | refl spineList => rfl
  | symm _ innerHypothesis => exact innerHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis
  | consCongr atom _ innerHypothesis =>
      dsimp only [capAtomCount]
      rw [innerHypothesis]

/-! ## Honesty marker -/

/-- **Honesty marker — the cup/cap atom counts are trace-equivalence invariants.**
`cupAtomCount_eq_of_atomicTraceEquiv` / `capAtomCount_eq_of_atomicTraceEquiv`: two spine lists
related by `AtomicTraceEquiv` carry equal cup and cap atom counts — the swap keeps each atom's
generator, so its cup/cap indicator is unchanged and the two merely commute.  This is the
multiset-level invariant behind the arc structure's total `cupCount` / `capCount`.  What this marker
does NOT claim: the per-port INTERNAL counts (`internalCupCounts` / `internalCapCounts`), which the
leg-join can still scramble — those are the genuine orbit residual.  `= true`. -/
def fxMode_hasAtomCountTraceInvariance : Bool := true

end FX1Poly.Polygraph

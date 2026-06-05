import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasType
import FX1Poly.Core.StepStarConfluence

/-! # FX1Poly/Typed/RawStepNotStronglyNormalizing
    — the honest NEGATIVE counterpart to SN-043: the RAW β-reduction is NOT strongly normalizing (SN-140 L1)

SN-043 (`HasTypeDescPi Γ t T → IsStronglyNormalizing t`, OB-5 `#794`) proves every WELL-TYPED term is strongly
normalizing.  That theorem is only non-vacuous if the typing restriction is genuinely LOAD-BEARING — i.e. if the
RAW (untyped) `Step` relation is NOT itself strongly normalizing.  This file proves exactly that, exhibiting the
classic diverging combinator and confirming `Step` has an infinite reduction sequence on a (well-scoped but
ill-typed) raw cell.

This is the five-layer-defense L1 (§27.3) honesty pin for the kernel's own foundations: the memory finding "raw
β+ι SN is FALSE" / `StepStar.HasStrongNormalization` is an UNPROVED-because-FALSE global claim, now committed as
a POSITIVE theorem (`rawStep_notStronglyNormalizing`) so no future development silently assumes global raw SN.
It is the negative witness that makes SN-043 meaningful: SN is a CONSEQUENCE OF TYPING, never a property of the
raw substrate.

  * `selfApplicatorCell` — `λx. x x` (the self-applicator), a well-scoped raw cell.
  * `divergentOmegaCell` — `Ω = (λx. x x)(λx. x x)`, Church's diverging combinator.
  * `divergentOmega_stepsToSelf` — `Step Ω Ω`: the single β-redex fires and `subst0` returns `Ω` itself, so the
    cell reduces to itself in one step (by `Step.beta`; the substitution computes definitionally).
  * `notAccessibleOfSelfLoop` — a general well-foundedness fact: an element related to itself is not
    `Acc`-accessible (an infinite descending chain `a ⤳ a ⤳ …` cannot be well-founded).
  * `divergentOmega_notStronglyNormalizing` — `¬ IsStronglyNormalizing Ω`: since `IsStronglyNormalizing` is
    `Acc StepSuccessor` and `StepSuccessor Ω Ω` holds (the self-step), `notAccessibleOfSelfLoop` refutes it.
  * `rawStep_notStronglyNormalizing` — the headline: `¬ HasStrongNormalization`.  The raw `Step` relation does
    NOT strongly normalize at every scope; `Ω` is the counterexample.

## Zero-axiom verification

`divergentOmega_stepsToSelf` is `Step.beta` (the `subst0` of the self-applicator into its own body is
definitionally `Ω`); `notAccessibleOfSelfLoop` is structural induction on the `Acc` witness (the `Acc.rec`
recursor, propext-free for this constant-ish motive); the rest are direct compositions.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (verified by `#print axioms` in scratch before
landing).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation FX1Poly.Core.StepStar

/-- **The self-applicator `λx. x x`** at scope 0 — a well-scoped raw cell (it is NOT well-typed: no type can be
both a function's domain and the type of that function applied to itself). -/
def selfApplicatorCell : RawTerm 0 :=
  lamCell (appCell (variableCell ⟨0, Nat.succ_pos 0⟩) (variableCell ⟨0, Nat.succ_pos 0⟩))

/-- **Church's diverging combinator `Ω = (λx. x x)(λx. x x)`** at scope 0. -/
def divergentOmegaCell : RawTerm 0 :=
  appCell selfApplicatorCell selfApplicatorCell

/-- **`Ω` β-steps to itself.**  The single β-redex `(λx. x x)(λx. x x)` fires; substituting the self-applicator
for the bound variable in the body `x x` returns `(λx. x x)(λx. x x) = Ω`, so `Step Ω Ω`.  The substitution
computes definitionally, so this is `Step.beta` directly. -/
theorem divergentOmega_stepsToSelf : Step divergentOmegaCell divergentOmegaCell :=
  Step.beta

/-- **A self-related element is not accessible.**  If `relation element element` holds, `element` cannot be
`Acc relation`-accessible: the would-be accessibility witness yields, by induction, the same demand on
`element` again — the infinite descending chain `element ⤳ element ⤳ …` no well-founded order admits.  The
general well-foundedness fact the divergence proof consumes. -/
theorem notAccessibleOfSelfLoop {carrier : Type} {relation : carrier → carrier → Prop} :
    ∀ element : carrier, Acc relation element → ¬ relation element element := by
  intro element accessible
  induction accessible with
  | intro current _currentStep inductiveHypothesis =>
      intro selfLoop
      exact inductiveHypothesis current selfLoop selfLoop

/-- **`Ω` is not strongly normalizing.**  `IsStronglyNormalizing` is `Acc StepSuccessor`, and `StepSuccessor Ω Ω`
is exactly the self-step `Step Ω Ω` (`StepSuccessor later earlier := Step earlier later`), so
`notAccessibleOfSelfLoop` refutes accessibility.  The concrete divergence witness. -/
theorem divergentOmega_notStronglyNormalizing : ¬ IsStronglyNormalizing divergentOmegaCell :=
  fun stronglyNormalizing =>
    notAccessibleOfSelfLoop divergentOmegaCell stronglyNormalizing divergentOmega_stepsToSelf

/-- **The raw `Step` relation does NOT have global strong normalization.**  The honest negative counterpart to
SN-043: well-typed terms are strongly normalizing, but the RAW substrate is not — `Ω` diverges.  This confirms
the typing restriction in SN-043 is load-bearing and that `HasStrongNormalization` (global raw SN) is FALSE, not
merely unproved.  §27.3 five-layer-defense L1. -/
theorem rawStep_notStronglyNormalizing : ¬ HasStrongNormalization :=
  fun globalStrongNormalization =>
    divergentOmega_notStronglyNormalizing (globalStrongNormalization divergentOmegaCell)

end FX1Poly.Typed

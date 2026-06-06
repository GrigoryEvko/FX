import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Core.StepStarConfluence
import FX1Poly.Core.StepInversion
import FX1Poly.Core.RawTermNF

/-! # FX1Poly/Typed/RawStepNotStronglyNormalizing
    — the honest NEGATIVE counterpart to SN-for-well-typed: the RAW β-reduction is NOT strongly normalizing

Strong normalization for well-typed terms (`HasTypeDescPi Γ t T → IsStronglyNormalizing t`) proves every
WELL-TYPED term is strongly normalizing.  That theorem is only non-vacuous if the typing restriction is
genuinely LOAD-BEARING — i.e. if the
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

The second half sharpens "not SN" into "no normal form" — `Ω` does not merely fail the accessibility predicate,
it never reaches a `Step`-normal term along its (unique) reduction path:

  * `selfApplicator_isStepNormalForm` — `λx. x x` is itself a normal form: its body is a variable applied to a
    variable, a neutral with no redex.  Decided structurally (`by decide`, axiom-free).
  * `divergentOmega_reductIsSelf` — `Ω`'s ONLY one-step reduct is `Ω`.  `Step.from_app` inversion gives three
    shapes: β (returns `Ω`, the body being `x x`), a function-step, or an argument-step — the latter two refuted
    because the self-applicator is normal.
  * `divergentOmega_starReductIsSelf` — `Ω`'s ONLY `StepStar`-reduct is `Ω`.  Chain induction (both endpoints
    generalized, the start-is-`Ω` fact carried as an equation): each `trans` step lands back at `Ω`.
  * `divergentOmega_noNormalForm` — `Ω` has NO normal form: every reachable term equals `Ω`, and `Ω` is a redex,
    so nothing reachable is `Step`-normal.  This is the exact obstruction a weak-normalization proof faces on raw
    terms (and overcomes only via the typing restriction): a closed, well-scoped, ill-typed term whose every
    reduction path diverges.

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

/-- **The self-applicator `λx. x x` is a `Step`-normal form.**  Its body `x x` is a variable applied to a
variable — a neutral application with no redex anywhere — so no `Step` fires.  Decided structurally
(`by decide`, no `Decidable`-instance axiom leak).  The fact the `Ω`-reduct inversion consumes to refute the two
congruence shapes of `Step.from_app`. -/
theorem selfApplicator_isStepNormalForm : RawTerm.isStepNormalForm selfApplicatorCell := by decide

/-- **`Ω`'s only one-step reduct is `Ω`.**  `Step.from_app` inverts a step out of the application
`(λx. x x)(λx. x x)` into three shapes: a β-contraction, a step inside the function, or a step inside the
argument.  The β-shape's contractum is `subst0 (x x) (λx. x x) = Ω` (the body forced to `x x` by injecting the
function equation).  Both congruence shapes are impossible because the self-applicator is a normal form
(`selfApplicator_isStepNormalForm` ⋈ `isStepNormalForm_blocks_step`).  So the reduct is uniquely `Ω`. -/
theorem divergentOmega_reductIsSelf :
    ∀ reduct : RawTerm 0, Step divergentOmegaCell reduct → reduct = divergentOmegaCell := by
  intro reduct step
  rcases Step.from_app step with
      ⟨body, functionEq, reductEq⟩ | ⟨functionAfter, reductEq, functionStep⟩
      | ⟨argumentAfter, reductEq, argumentStep⟩
  · -- β-shape: functionEq forces the lambda body to be `x x`, so the contractum is Ω.
    rw [show selfApplicatorCell
          = (.mkGen .gen_lam () (.childCons
              (appCell (variableCell ⟨0, Nat.succ_pos 0⟩) (variableCell ⟨0, Nat.succ_pos 0⟩))
              .childNil) : RawTerm 0) from rfl] at functionEq
    injection functionEq with _scopeEq _genEq _payloadEq childrenSpineEq
    injection childrenSpineEq with _shiftEq _arityEq _restShiftsEq bodyEq _tailEq
    subst reductEq
    subst bodyEq
    rfl
  · exact absurd functionStep
      (RawTerm.isStepNormalForm_blocks_step selfApplicator_isStepNormalForm functionAfter)
  · exact absurd argumentStep
      (RawTerm.isStepNormalForm_blocks_step selfApplicator_isStepNormalForm argumentAfter)

/-- **`Ω`'s only `StepStar`-reduct is `Ω`.**  Induction on the reduction chain with BOTH endpoints generalized
and the start-is-`Ω` fact carried as an explicit equation (the standard fixed-start `StepStar`-induction shape —
the bare `induction` motive cannot abstract the constant first index).  The reflexive case is immediate; each
`trans` step lands back at `Ω` by `divergentOmega_reductIsSelf`, so the tail chain restarts at `Ω` and the
inductive hypothesis closes it. -/
theorem divergentOmega_starReductIsSelf (reached : RawTerm 0)
    (chain : StepStar divergentOmegaCell reached) : reached = divergentOmegaCell := by
  suffices generalized :
      ∀ start finish : RawTerm 0, StepStar start finish →
        start = divergentOmegaCell → finish = divergentOmegaCell from
    generalized divergentOmegaCell reached chain rfl
  intro start finish startChain
  induction startChain with
  | refl => exact fun startEq => startEq
  | trans headStep _restChain tailInductiveHypothesis =>
      intro firstEq
      subst firstEq
      exact tailInductiveHypothesis (divergentOmega_reductIsSelf _ headStep)

/-- **`Ω` has NO normal form.**  Every term reachable from `Ω` equals `Ω` (`divergentOmega_starReductIsSelf`),
and `Ω` is itself a redex (`divergentOmega_stepsToSelf`), so no reachable term is `Step`-normal: the unique
reduction path `Ω ⤳ Ω ⤳ …` never halts.  The sharpest divergence statement — not merely "`Ω` is not SN" but
"`Ω` never reaches a normal form by ANY reduction."  Precisely the obstruction a raw weak-normalization proof
cannot clear, and the reason SN/WN (SN-043) need the typing restriction: this term is closed and well-scoped yet
ill-typed.  §27.3 five-layer-defense L1. -/
theorem divergentOmega_noNormalForm (reached : RawTerm 0)
    (chain : StepStar divergentOmegaCell reached) : ¬ RawTerm.isStepNormalForm reached := by
  have reachedEq : reached = divergentOmegaCell := divergentOmega_starReductIsSelf reached chain
  subst reachedEq
  exact fun normalForm =>
    RawTerm.isStepNormalForm_blocks_step normalForm divergentOmegaCell divergentOmega_stepsToSelf

end FX1Poly.Typed

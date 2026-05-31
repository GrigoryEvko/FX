import FX1Poly.Core.DependentArrowReducibilityCandidate
import FX1Poly.Core.StratifiedReducibleTypeConvInvariance
import FX1Poly.Core.StratifiedReducibleTypeNeutral

/-! # Foundation/PolyCell/Core/StratifiedReducibleTypeReducibilityCandidate
    — every candidate the stratified reducibility relation assigns is a Girard reducibility candidate

The stratified port of `ReducibleType.isReducibilityCandidate`, plus the dependent-arrow CR it delegates
to.  This closes the CR-soundness of the whole Tarski-universe relation: at every POSITIVE fuel level, the
candidate `ReducibleTypeStep`/`ReducibleTypeAt` assigns to a type code satisfies all three Girard CR
conditions.  It is the precondition the fundamental theorem's term cases consume (variable inhabitation,
elimination SN-descent, neutral-expansion).

## The four arms

  * `whnfExpand` — inherits its contractum's candidate-hood (the induction hypothesis), the candidate is
    literally the same.
  * `neutral` — the strong-normalization candidate (`isStronglyNormalizing_isReducibilityCandidate`).
  * `piType` — the DEPENDENT function-space candidate; a CR by `isDependentArrowReducibleStep_isReducibilityCandidate`
    below (the stratified arrow CR), fed variable 0 as the domain inhabitant CR1 needs.
  * `universeCode` — the Tarski universe candidate, a CR by `universeCandidateIsReducibilityCandidate` over
    the type-level interface (forward-step + neutral-inclusion).

## The dependent-arrow CR (`isDependentArrowReducibleStep_isReducibilityCandidate`)

A VERBATIM port of `isDependentArrowReducible_isReducibilityCandidate` — every line generic over the
candidate algebra except the single conversion-invariance bridge in CR3's argument-reduction case, where
`ReducibleType.convTransfer` becomes `ReducibleTypeStep.convTransfer`.  That bridge carries membership
across the convertible reduced codomain codes `subst0 codomainCode argumentFocus ~ subst0 codomainCode
argumentAfter`.  The `IsDependentArrowReducible` predicate itself is reused unchanged (it is purely
candidate-shaped — no reducibility relation in its definition).

## The level wrapper is stated at `predLevel + 1` (the bottom is genuinely degenerate)

`ReducibleTypeAt.isReducibilityCandidate` is at `predLevel + 1`, NOT all levels: at level `0` the universe
candidate is `universeReducibilityPredicate (fun _ _ => False)` = the EMPTY predicate (`SN ∧ ∃c, False`),
which FAILS CR3 (a variable is neutral with no reducts, so CR3's premise holds vacuously, but the empty
conclusion is `False`).  At every positive level the lower relation is `ReducibleTypeAt predLevel`, whose
forward-step and neutral-inclusion legs ARE discharged (`forwardStep` / `reducibleOfNeutral`), so the
result holds with no hypotheses.  Real type interpretations always sit at a level at least the
universe-nesting depth, so the level-0 degeneracy is never invoked.

## Zero-axiom verification

`induction reducible` with four `exact`s; the arrow CR is the Girard candidate construction with
`convTransfer` bridging CR3's dependence; the level wrapper discharges the universe interface by
`forwardStep` / `reducibleOfNeutral`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **The dependent arrow construction is a reducibility candidate (stratified).**  The verbatim port of
`isDependentArrowReducible_isReducibilityCandidate`: every CR condition is generic over the candidate
algebra, save CR3's argument-reduction case where `ReducibleTypeStep.convTransfer` carries membership across
the convertible reduced codomain codes.  Given a domain candidate, a family of codomain candidates each a
reducibility candidate, the `ReducibleTypeStep` witnesses interpreting them (supplying conversion-
invariance), and an inhabited domain, the dependent function space satisfies CR1/CR2/CR3. -/
theorem isDependentArrowReducibleStep_isReducibilityCandidate {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    {domainPredicate : RawTerm scope → Prop}
    {codomainCandidate : RawTerm scope → (RawTerm scope → Prop)}
    {codomainCode : RawTerm (scope + 1)}
    (domainCandidate : IsReducibilityCandidate domainPredicate)
    (codomainCandidateHood : ∀ argument : RawTerm scope, domainPredicate argument →
      IsReducibilityCandidate (codomainCandidate argument))
    (codomainReducible : ∀ argument : RawTerm scope, domainPredicate argument →
      ReducibleTypeStep lowerReducible (RawTerm.subst0 codomainCode argument)
        (codomainCandidate argument))
    (reducibleWitness : RawTerm scope)
    (witnessReducible : domainPredicate reducibleWitness) :
    IsReducibilityCandidate (IsDependentArrowReducible domainPredicate codomainCandidate) := by
  refine ⟨?stronglyNormalizing, ?closedUnderStep, ?neutralExpansion⟩
  case stronglyNormalizing =>
    intro function functionArrowReducible
    have applicationReducible :
        codomainCandidate reducibleWitness
          (.mkGen .gen_app ()
            (.childCons function (.childCons reducibleWitness .childNil))) :=
      functionArrowReducible reducibleWitness witnessReducible
    exact appHead_isStronglyNormalizing_of_app
      ((codomainCandidateHood reducibleWitness witnessReducible).stronglyNormalizing
        applicationReducible)
  case closedUnderStep =>
    intro function functionAfter functionArrowReducible functionStep argument argumentReducible
    have applicationStep :
        Step
          (.mkGen .gen_app () (.childCons function (.childCons argument .childNil)))
          (.mkGen .gen_app () (.childCons functionAfter (.childCons argument .childNil))) :=
      Step.cong .gen_app ()
        (StepChildren.here
          (.childCons argument .childNil : RawTermChildren [0] scope)
          functionStep)
    exact (codomainCandidateHood argument argumentReducible).closedUnderStep
      (functionArrowReducible argument argumentReducible) applicationStep
  case neutralExpansion =>
    intro function functionIsNeutral reductsArrowReducible
    suffices general :
        ∀ {currentArgument : RawTerm scope}, Acc StepSuccessor currentArgument →
          domainPredicate currentArgument →
            codomainCandidate currentArgument
              (.mkGen .gen_app ()
                (.childCons function (.childCons currentArgument .childNil))) from
      fun argument argumentReducible =>
        general (domainCandidate.stronglyNormalizing argumentReducible) argumentReducible
    intro currentArgument argumentAccessible
    induction argumentAccessible with
    | intro argumentFocus _argumentPredecessors argumentInductiveHypothesis =>
        intro argumentFocusReducible
        refine (codomainCandidateHood argumentFocus argumentFocusReducible).neutralExpansion
          (IsNeutral.app functionIsNeutral) ?_
        intro reduct reductionStep
        rcases Step.from_app reductionStep with
          ⟨_body, functionEqualsLam, _targetEq⟩ |
          ⟨functionAfter, reductEquals, functionStep⟩ |
          ⟨argumentAfter, reductEquals, argumentStep⟩
        · exact (IsNeutral.not_lam (functionEqualsLam ▸ functionIsNeutral)).elim
        · rw [reductEquals]
          exact reductsArrowReducible functionAfter functionStep
            argumentFocus argumentFocusReducible
        · rw [reductEquals]
          have argumentAfterReducible :=
            domainCandidate.closedUnderStep argumentFocusReducible argumentStep
          exact ReducibleTypeStep.convTransfer
            (codomainReducible argumentAfter argumentAfterReducible)
            (codomainReducible argumentFocus argumentFocusReducible)
            ⟨_, StepStar.refl _, Step.subst0Argument codomainCode argumentStep⟩
            (argumentInductiveHypothesis argumentAfter argumentStep argumentAfterReducible)

/-- **Every stratified-reducibility candidate is a Girard reducibility candidate** (parametric).  By
induction on the `ReducibleTypeStep` derivation: `whnfExpand` reuses the induction hypothesis, `neutral` is
the strong-normalization candidate, `piType` is the dependent function-space candidate (domain inhabitant =
variable 0), and `universeCode` is the Tarski candidate via the type-level interface (`lowerForwardStep` +
`lowerNeutralInclusion`).  Stated at `scope + 1` so the arrow CR1 has variable 0 available as the uniform
domain inhabitant. -/
theorem ReducibleTypeStep.isReducibilityCandidate {scope : Nat}
    {lowerReducible : RawTerm (scope + 1) → (RawTerm (scope + 1) → Prop) → Prop}
    (lowerForwardStep : ∀ {typeCode reduct : RawTerm (scope + 1)} {candidate : RawTerm (scope + 1) → Prop},
      lowerReducible typeCode candidate → Step typeCode reduct → lowerReducible reduct candidate)
    (lowerNeutralInclusion : ∀ {typeCode : RawTerm (scope + 1)}, IsNeutral typeCode →
      (∀ reduct : RawTerm (scope + 1), Step typeCode reduct →
        ∃ candidate : RawTerm (scope + 1) → Prop, lowerReducible reduct candidate) →
      ∃ candidate : RawTerm (scope + 1) → Prop, lowerReducible typeCode candidate)
    {typeCode : RawTerm (scope + 1)} {candidate : RawTerm (scope + 1) → Prop}
    (reducible : ReducibleTypeStep lowerReducible typeCode candidate) :
    IsReducibilityCandidate candidate := by
  induction reducible with
  | whnfExpand _weakHeadStep _reductReducible reductInductiveHypothesis =>
      exact reductInductiveHypothesis
  | neutral _noWeakHeadStep _notPiType _notUniverse =>
      exact isStronglyNormalizing_isReducibilityCandidate
  | piType codomainCandidate _domainReducible codomainReducible
      domainInductiveHypothesis codomainInductiveHypothesis =>
      exact isDependentArrowReducibleStep_isReducibilityCandidate
        domainInductiveHypothesis codomainInductiveHypothesis codomainReducible
        (.mkGen .gen_var ⟨0, Nat.succ_pos scope⟩ .childNil)
        (domainInductiveHypothesis.containsVariable ⟨0, Nat.succ_pos scope⟩)
  | universeCode _levelExpr _flag =>
      exact ReducibleTypeStep.universeCandidateIsReducibilityCandidate
        lowerForwardStep lowerNeutralInclusion

/-- **Every level-indexed reducibility candidate is a Girard reducibility candidate** (unconditional, at
every positive fuel level).  `ReducibleTypeStep.isReducibilityCandidate` with both interface legs discharged
for `ReducibleTypeAt predLevel`: the forward leg by `forwardStep`, the neutral leg by `reducibleOfNeutral`.
Stated at `predLevel + 1` because the level-0 universe candidate is the empty predicate (not a CR); every
positive level has a genuine lower relation. -/
theorem ReducibleTypeAt.isReducibilityCandidate {scope : Nat} {predLevel : Nat}
    {typeCode : RawTerm (scope + 1)} {candidate : RawTerm (scope + 1) → Prop}
    (reducible : ReducibleTypeAt (predLevel + 1) typeCode candidate) :
    IsReducibilityCandidate candidate := by
  refine ReducibleTypeStep.isReducibilityCandidate ?lowerForwardStep ?lowerNeutralInclusion reducible
  · exact fun reducibleLower step => ReducibleTypeAt.forwardStep reducibleLower step
  · exact fun neutral _reductsReducible => ReducibleTypeAt.reducibleOfNeutral neutral

end FX1Poly.Core

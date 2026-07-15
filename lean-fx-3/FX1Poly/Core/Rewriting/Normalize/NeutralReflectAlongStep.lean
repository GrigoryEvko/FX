import FX1Poly.Core.Rewriting.Normalize.WeakHeadNormalPreservation
import FX1Poly.Core.Substrate.Neutral.NeutralTerm

/-! # FX1Poly/Core/NeutralReflectAlongStep
    — neutrality reflects backward across an arbitrary single step (the dual of `WeakHeadStep.reflectAlongStep`)

`WeakHeadStep.reflectAlongStep` reflects a weak-head redex BACKWARD across a single step: if `subject`
steps to `reduct` and `reduct` has a weak-head step, then `subject` already had one (a single reduction
never CREATES a weak-head redex).  This brick supplies the COMPLEMENTARY reflection for the OTHER
weak-head-normal-form shape — neutrality: if `subject` steps to a NEUTRAL `reduct`, then `subject` is
EITHER neutral itself OR has a weak-head step.

The two together are the dispatch the data-eliminator fundamental-theorem rows need over the
head-expansion-closed `dataTaitCandidate`.  A `dataTaitCandidate`-member scrutinee is strongly normalizing
and every reachable normal form is a value or neutral (`dataTaitCandidate`'s second projection), but the
ELIMINATOR's reducibility argument must peel the scrutinee's WEAK-HEAD reductions one at a time (the only
reductions a general result candidate absorbs backward, via its `headExpand` interface) and, when the
scrutinee is weak-head normal, classify it as a value (fire ι) or a neutral (place the stuck eliminator
cell by CR3).  This file is the neutral half of that classification: it turns "the scrutinee reaches a
neutral normal form" into "the scrutinee has a weak-head step (keep peeling) or is itself neutral (stop)".

## The proof shape

`IsNeutral.reflectAlongStep` is by INDUCTION ON the neutral derivation `IsNeutral reductTerm` (mirroring
`WeakHeadStep.reflectAlongStep`'s induction on the weak-head step).  In each arm the arbitrary
`Step subjectTerm reductTerm` is inverted by the packaging inversion
`Step.weakHeadOrSpineStepIntoCell` (the generator / payload / children pinning discharged once,
upstream):

  * **weak-head disjunct** — `subjectTerm` already has a weak-head step; emit it.  Identical across
    all twelve arms.

  * **spine-step disjunct** — `subjectTerm = mkGen G payload sourceChildren` with
    `StepChildren sourceChildren <reduct spine>`; case the `StepChildren` against the concrete reduct
    spine by WHICH child stepped:
      - a NON-principal child stepped (motive / branch / base case) — the principal child is unchanged, so
        the subject is still neutral at the same head (`IsNeutral.<former>` with the stored premise);
      - the PRINCIPAL child stepped — recurse with the induction hypothesis, which returns a weak-head step
        on the principal subterm (lift it via the matching `WeakHeadStep.scrutinee*` / `appCongruence`) or
        the principal subterm's own neutrality (re-wrap with `IsNeutral.<former>`).

The childless atomic `var` arm refutes the impossible cong-into-leaf spine by `cases childStep`.

## Zero-axiom verification

`induction` on `IsNeutral` then the `Step.weakHeadOrSpineStepIntoCell` packaging inversion + `cases` on
`StepChildren` against a pinned-concrete reduct spine; impossible cong-into-leaf spines closed by
`cases`.  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core
open FX1Poly.Tier0.Syntax

/-- **Neutrality reflects backward across an arbitrary single step.**  If `subjectTerm` reduces to
`reductTerm` and `reductTerm` is neutral, then `subjectTerm` is EITHER neutral itself OR has a weak-head
step.  The dual of `WeakHeadStep.reflectAlongStep`: a single reduction cannot turn a non-neutral
weak-head-normal form into a neutral without exposing a weak-head redex on the source.

Induction on `IsNeutral reductTerm`; each arbitrary `Step subjectTerm reductTerm` is inverted by the
packaging inversion `Step.weakHeadOrSpineStepIntoCell`.  The weak-head disjunct yields the source
weak-head step; the spine-step disjunct cases the `StepChildren` — a stepped non-principal child keeps
the subject neutral at the same head, a stepped principal child recurses through the induction
hypothesis (lifting either its weak-head step or its neutrality).

Zero-axiom: no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`. -/
theorem IsNeutral.reflectAlongStep {scope : Nat} :
    ∀ {reductTerm : RawTerm scope}, IsNeutral reductTerm →
      ∀ {subjectTerm : RawTerm scope}, Step subjectTerm reductTerm →
        (∃ subjectReduct : RawTerm scope, WeakHeadStep subjectTerm subjectReduct) ∨
          IsNeutral subjectTerm := by
  intro reductTerm neutral
  induction neutral with
  | var index =>
      intro subjectTerm step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨_sourceChildren, _subjectEquation, childStep⟩
      · exact Or.inl ⟨subjectReduct, weakHeadOnSubject⟩
      · cases childStep
  | app headIsNeutral headInductiveHypothesis =>
      intro subjectTerm step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact Or.inl ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest functionStep =>
            rcases headInductiveHypothesis functionStep with
              ⟨_functionWhReduct, weakHeadOnFunction⟩ | functionReductNeutral
            · exact Or.inl ⟨_, WeakHeadStep.appCongruence weakHeadOnFunction⟩
            · exact Or.inr (IsNeutral.app functionReductNeutral)
        | there _head tailStep =>
            cases tailStep with
            | here _rest _argumentStep =>
                exact Or.inr (IsNeutral.app headIsNeutral)
            | there _head2 emptyStep => cases emptyStep
  | pathApp functionIsNeutral functionInductiveHypothesis =>
      intro subjectTerm step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact Or.inl ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest functionStep =>
            rcases functionInductiveHypothesis functionStep with
              ⟨_functionWhReduct, weakHeadOnFunction⟩ | functionReductNeutral
            · exact Or.inl ⟨_, WeakHeadStep.pathAppCongruence weakHeadOnFunction⟩
            · exact Or.inr (IsNeutral.pathApp functionReductNeutral)
        | there _head tailStep =>
            cases tailStep with
            | here _rest _argumentStep =>
                exact Or.inr (IsNeutral.pathApp functionIsNeutral)
            | there _head2 emptyStep => cases emptyStep
  | fst argumentIsNeutral argumentInductiveHypothesis =>
      intro subjectTerm step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact Or.inl ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest argumentStep =>
            rcases argumentInductiveHypothesis argumentStep with
              ⟨_argumentWhReduct, weakHeadOnArgument⟩ | argumentReductNeutral
            · exact Or.inl ⟨_, WeakHeadStep.scrutineeFst weakHeadOnArgument⟩
            · exact Or.inr (IsNeutral.fst argumentReductNeutral)
        | there _head tailStep => cases tailStep
  | snd argumentIsNeutral argumentInductiveHypothesis =>
      intro subjectTerm step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact Or.inl ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest argumentStep =>
            rcases argumentInductiveHypothesis argumentStep with
              ⟨_argumentWhReduct, weakHeadOnArgument⟩ | argumentReductNeutral
            · exact Or.inl ⟨_, WeakHeadStep.scrutineeSnd weakHeadOnArgument⟩
            · exact Or.inr (IsNeutral.snd argumentReductNeutral)
        | there _head tailStep => cases tailStep
  | boolElim scrutineeIsNeutral scrutineeInductiveHypothesis =>
      intro subjectTerm step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact Or.inl ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep => exact Or.inr (IsNeutral.boolElim scrutineeIsNeutral)
        | there _head tailStep =>
            cases tailStep with
            | here _rest _thenStep => exact Or.inr (IsNeutral.boolElim scrutineeIsNeutral)
            | there _head2 restStep =>
                cases restStep with
                | here _rest _elseStep => exact Or.inr (IsNeutral.boolElim scrutineeIsNeutral)
                | there _head3 scrutineeTailStep =>
                    cases scrutineeTailStep with
                    | here _rest scrutineeStep =>
                        rcases scrutineeInductiveHypothesis scrutineeStep with
                          ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩ | scrutineeReductNeutral
                        · exact Or.inl ⟨_, WeakHeadStep.scrutineeBoolElim weakHeadOnScrutinee⟩
                        · exact Or.inr (IsNeutral.boolElim scrutineeReductNeutral)
                    | there _head4 emptyStep => cases emptyStep
  | natElim scrutineeIsNeutral scrutineeInductiveHypothesis =>
      intro subjectTerm step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact Or.inl ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep => exact Or.inr (IsNeutral.natElim scrutineeIsNeutral)
        | there _head tailStep =>
            cases tailStep with
            | here _rest _zeroStep => exact Or.inr (IsNeutral.natElim scrutineeIsNeutral)
            | there _head2 restStep =>
                cases restStep with
                | here _rest _succStep => exact Or.inr (IsNeutral.natElim scrutineeIsNeutral)
                | there _head3 scrutineeTailStep =>
                    cases scrutineeTailStep with
                    | here _rest scrutineeStep =>
                        rcases scrutineeInductiveHypothesis scrutineeStep with
                          ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩ | scrutineeReductNeutral
                        · exact Or.inl ⟨_, WeakHeadStep.scrutineeNatElim weakHeadOnScrutinee⟩
                        · exact Or.inr (IsNeutral.natElim scrutineeReductNeutral)
                    | there _head4 emptyStep => cases emptyStep
  | natRec scrutineeIsNeutral scrutineeInductiveHypothesis =>
      intro subjectTerm step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact Or.inl ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep => exact Or.inr (IsNeutral.natRec scrutineeIsNeutral)
        | there _head tailStep =>
            cases tailStep with
            | here _rest _zeroStep => exact Or.inr (IsNeutral.natRec scrutineeIsNeutral)
            | there _head2 restStep =>
                cases restStep with
                | here _rest _succStep => exact Or.inr (IsNeutral.natRec scrutineeIsNeutral)
                | there _head3 scrutineeTailStep =>
                    cases scrutineeTailStep with
                    | here _rest scrutineeStep =>
                        rcases scrutineeInductiveHypothesis scrutineeStep with
                          ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩ | scrutineeReductNeutral
                        · exact Or.inl ⟨_, WeakHeadStep.scrutineeNatRec weakHeadOnScrutinee⟩
                        · exact Or.inr (IsNeutral.natRec scrutineeReductNeutral)
                    | there _head4 emptyStep => cases emptyStep
  | listElim scrutineeIsNeutral scrutineeInductiveHypothesis =>
      intro subjectTerm step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact Or.inl ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep => exact Or.inr (IsNeutral.listElim scrutineeIsNeutral)
        | there _head tailStep =>
            cases tailStep with
            | here _rest _nilStep => exact Or.inr (IsNeutral.listElim scrutineeIsNeutral)
            | there _head2 restStep =>
                cases restStep with
                | here _rest _consStep => exact Or.inr (IsNeutral.listElim scrutineeIsNeutral)
                | there _head3 scrutineeTailStep =>
                    cases scrutineeTailStep with
                    | here _rest scrutineeStep =>
                        rcases scrutineeInductiveHypothesis scrutineeStep with
                          ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩ | scrutineeReductNeutral
                        · exact Or.inl ⟨_, WeakHeadStep.scrutineeListElim weakHeadOnScrutinee⟩
                        · exact Or.inr (IsNeutral.listElim scrutineeReductNeutral)
                    | there _head4 emptyStep => cases emptyStep
  | optionMatch scrutineeIsNeutral scrutineeInductiveHypothesis =>
      intro subjectTerm step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact Or.inl ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep => exact Or.inr (IsNeutral.optionMatch scrutineeIsNeutral)
        | there _head tailStep =>
            cases tailStep with
            | here _rest _noneStep => exact Or.inr (IsNeutral.optionMatch scrutineeIsNeutral)
            | there _head2 restStep =>
                cases restStep with
                | here _rest _someStep => exact Or.inr (IsNeutral.optionMatch scrutineeIsNeutral)
                | there _head3 scrutineeTailStep =>
                    cases scrutineeTailStep with
                    | here _rest scrutineeStep =>
                        rcases scrutineeInductiveHypothesis scrutineeStep with
                          ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩ | scrutineeReductNeutral
                        · exact Or.inl ⟨_, WeakHeadStep.scrutineeOptionMatch weakHeadOnScrutinee⟩
                        · exact Or.inr (IsNeutral.optionMatch scrutineeReductNeutral)
                    | there _head4 emptyStep => cases emptyStep
  | eitherMatch scrutineeIsNeutral scrutineeInductiveHypothesis =>
      intro subjectTerm step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact Or.inl ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep => exact Or.inr (IsNeutral.eitherMatch scrutineeIsNeutral)
        | there _head tailStep =>
            cases tailStep with
            | here _rest _leftStep => exact Or.inr (IsNeutral.eitherMatch scrutineeIsNeutral)
            | there _head2 restStep =>
                cases restStep with
                | here _rest _rightStep => exact Or.inr (IsNeutral.eitherMatch scrutineeIsNeutral)
                | there _head3 scrutineeTailStep =>
                    cases scrutineeTailStep with
                    | here _rest scrutineeStep =>
                        rcases scrutineeInductiveHypothesis scrutineeStep with
                          ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩ | scrutineeReductNeutral
                        · exact Or.inl ⟨_, WeakHeadStep.scrutineeEitherMatch weakHeadOnScrutinee⟩
                        · exact Or.inr (IsNeutral.eitherMatch scrutineeReductNeutral)
                    | there _head4 emptyStep => cases emptyStep
  | idJ witnessIsNeutral witnessInductiveHypothesis =>
      intro subjectTerm step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact Or.inl ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep => exact Or.inr (IsNeutral.idJ witnessIsNeutral)
        | there _head tailStep =>
            cases tailStep with
            | here _rest _baseStep => exact Or.inr (IsNeutral.idJ witnessIsNeutral)
            | there _head2 restStep =>
                cases restStep with
                | here _rest witnessStep =>
                    rcases witnessInductiveHypothesis witnessStep with
                      ⟨_witnessWhReduct, weakHeadOnWitness⟩ | witnessReductNeutral
                    · exact Or.inl ⟨_, WeakHeadStep.scrutineeIdJ weakHeadOnWitness⟩
                    · exact Or.inr (IsNeutral.idJ witnessReductNeutral)
                | there _head3 emptyStep => cases emptyStep
  | idStrictRec witnessIsNeutral witnessInductiveHypothesis =>
      intro subjectTerm step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact Or.inl ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep => exact Or.inr (IsNeutral.idStrictRec witnessIsNeutral)
        | there _head tailStep =>
            cases tailStep with
            | here _rest _baseStep => exact Or.inr (IsNeutral.idStrictRec witnessIsNeutral)
            | there _head2 restStep =>
                cases restStep with
                | here _rest witnessStep =>
                    rcases witnessInductiveHypothesis witnessStep with
                      ⟨_witnessWhReduct, weakHeadOnWitness⟩ | witnessReductNeutral
                    · exact Or.inl ⟨_, WeakHeadStep.scrutineeIdStrictRec weakHeadOnWitness⟩
                    · exact Or.inr (IsNeutral.idStrictRec witnessReductNeutral)
                | there _head3 emptyStep => cases emptyStep

/-- **Neutrality reflects backward across a whole reduction.**  If `subjectTerm` reduces (in any number of
steps) to a NEUTRAL `reductTerm`, then `subjectTerm` is EITHER neutral itself OR has a weak-head step.  The
`StepStar` closure of `IsNeutral.reflectAlongStep`: induction on the reduction, with a weak-head step on
the intermediate pulled back by `WeakHeadStep.reflectAlongStep` and an intermediate neutrality pulled back
by `IsNeutral.reflectAlongStep`. -/
theorem IsNeutral.reflectAlongStepStar {scope : Nat} {subjectTerm reductTerm : RawTerm scope}
    (reduction : StepStar subjectTerm reductTerm) (reductIsNeutral : IsNeutral reductTerm) :
    (∃ subjectReduct : RawTerm scope, WeakHeadStep subjectTerm subjectReduct) ∨
      IsNeutral subjectTerm := by
  induction reduction with
  | refl _ => exact Or.inr reductIsNeutral
  | trans firstStep _restReduction restInductiveHypothesis =>
      rcases restInductiveHypothesis reductIsNeutral with
        ⟨_midWhReduct, weakHeadOnMid⟩ | midNeutral
      · exact Or.inl (WeakHeadStep.reflectAlongStep weakHeadOnMid firstStep)
      · exact IsNeutral.reflectAlongStep midNeutral firstStep

end FX1Poly.Core

import FX1Poly.Core.Metatheory.Reducibility.Types.ReducibleTypeForwardClosure

/-! # Foundation/PolyCell/Core/WeakHeadNormalPreservation
    — weak-head-normal forms are preserved under arbitrary single-step reduction

The conversion-invariance of the dependent reducibility relation (`ReducibleType`) factors, in its
`neutral` arm, through a single structural fact about the COMPLETE weak-head reduction `WeakHeadStep`
(β + root-ι + scrutinee-congruence): a term that is weak-head NORMAL stays weak-head normal as it
reduces.  `ReducibleTypeForwardClosure` already keeps the root generator stable along such a step
(`Step.rootGenerator_eq_of_weakHeadNormal`); this brick supplies the COMPLEMENTARY half — the
weak-head-normality itself is stable — completing the `neutral` classification's invariance and, with it,
the UNCONDITIONAL (not fragment-restricted) conversion-invariance the `neutral` arm needs.

The engine is `reflectAlongStep`: a step BACKWARD across the weak-head step.  If `subjectType` steps to
some `reductType` and `reductType` has a weak-head step, then `subjectType` ALREADY had a weak-head step.
Contrapositive: a weak-head-normal `subjectType` (no wh-step) forces its reduct to be weak-head normal too
(`weakHeadNormalPreservedByStep`) — a step can never CREATE a weak-head redex out of a normal form.

## The proof shape

The whole induction dispatches through ONE packaging inversion,
`Step.weakHeadOrSpineStepIntoCell`: a step whose REDUCT is a concrete cell either exposes a weak-head
step on the SOURCE directly, or the source is a cell with the SAME generator and payload whose spine
steps to the reduct's spine.  It is `Step.weakHeadStep_or_cong` with the generator / payload / children
pinning (`congrArg RawTerm.rootGenerator` + `injection`) discharged ONCE instead of once per arm.

`reflectAlongStep` is then by INDUCTION ON the weak-head step `WeakHeadStep reductType weakHeadReduct`
(the second-to-first argument), each arm consuming the packaging inversion TWICE:

  * on the SUBJECT against the concrete redex/eliminator cell — the weak-head disjunct is the answer
    verbatim; the spine-step disjunct splits by WHICH child stepped:
      - a NON-scrutinee child (branch / argument / base case) stepped — the scrutinee is unchanged, so
        the subject is still a redex (`beta` / `rootIota` / the native `… rfl` firings) at the same head,
        or still weak-head reduces at the unchanged scrutinee (`scrutinee*` arms, `appCongruence`);
      - the SCRUTINEE child stepped — recurse with the induction hypothesis (`appCongruence` /
        `scrutinee*`), or, for `rootIota` and the native rows, consume the packaging inversion AGAIN
  * on the SCRUTINEE against its constructor cell — a genuine wh-step on the scrutinee lifts through the
    scrutinee-congruence constructor; a spine step INTO the constructor means the scrutinee already IS
    that constructor (same head, same payload), so the ι redex re-forms (nullary constructors refute the
    impossible spine step into an empty spine by `cases`).

Phase-Z places the scrutinee LAST in every eliminator: child 3 for `boolElim` / `natElim` / `natRec` /
`listElim` / `optionMatch` / `eitherMatch` whose spines lead with `motive`, child 2 for
`idJ`/`idStrictRec` whose spine is `(motive, baseCase, witness)`, child 0 for `fst`/`snd`/`ungel`.  The
corollary `weakHeadNormalPreservedByStep` is the four-line contrapositive.

## Zero-axiom verification

`Step.weakHeadOrSpineStepIntoCell` is `Step.weakHeadStep_or_cong` + generator pinning via
`congrArg RawTerm.rootGenerator` + `injection` (the propext-clean route the whole `Step`-inversion
family uses); `reflectAlongStep` is `induction` on `WeakHeadStep` consuming it, with impossible
spine-steps into leaf spines closed by `cases`.  No `axiom`, `sorry`, `admit`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Verified per declaration:
`#print axioms Step.weakHeadOrSpineStepIntoCell`, `#print axioms WeakHeadStep.reflectAlongStep` and
`#print axioms WeakHeadStep.weakHeadNormalPreservedByStep` each report "does not depend on any axioms".
-/

namespace FX1Poly.Core
open FX1Poly.Tier0.Syntax

/-- **Inversion of a step INTO a concrete cell.**  When the REDUCT of an arbitrary step is a concrete
cell `.mkGen targetGenerator targetPayload targetChildren`, either the SOURCE already has a weak-head
step, or the source is a cell with the SAME generator and payload whose spine steps to the target
spine.  This is `Step.weakHeadStep_or_cong` with the generator / payload / children pinning
(`congrArg RawTerm.rootGenerator` + `injection`) discharged ONCE — every arm of `reflectAlongStep`
consumes it twice: on the subject against the concrete redex, and on the scrutinee against its
constructor. -/
theorem Step.weakHeadOrSpineStepIntoCell {scope : Nat}
    {targetGenerator : Generator} {targetPayload : targetGenerator.payload scope}
    {targetChildren : RawTermChildren targetGenerator.binderShifts scope}
    {subjectType : RawTerm scope}
    (step : Step subjectType (.mkGen targetGenerator targetPayload targetChildren)) :
    (∃ subjectReduct : RawTerm scope, WeakHeadStep subjectType subjectReduct) ∨
    (∃ sourceChildren : RawTermChildren targetGenerator.binderShifts scope,
      subjectType = .mkGen targetGenerator targetPayload sourceChildren ∧
      StepChildren sourceChildren targetChildren) := by
  rcases Step.weakHeadStep_or_cong step with
    ⟨subjectReduct, weakHeadOnSubject⟩
    | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
  · exact Or.inl ⟨subjectReduct, weakHeadOnSubject⟩
  · have generatorEquation : targetGenerator = generator :=
      congrArg RawTerm.rootGenerator reductEquation
    subst generatorEquation
    injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
    subst payloadEquation
    subst childrenAfterEquation
    exact Or.inr ⟨children, subjectEquation, childStep⟩

/-- **A weak-head step reflects backward across an arbitrary single step.**  If `subjectType` reduces to
`reductType` and `reductType` has a weak-head step, then `subjectType` ALREADY has a weak-head step — a
single reduction can never CREATE a weak-head redex where the source had none.

Induction on the weak-head step; each arm consumes the packaging inversion
`Step.weakHeadOrSpineStepIntoCell` on the subject against the concrete redex (the weak-head disjunct is
the answer verbatim; the spine-step disjunct splits by which child stepped — a stepped scrutinee
recurses through the induction hypothesis or consumes the inversion again against the scrutinee's
constructor, a stepped branch / argument / base case leaves the redex intact at the same head).

Zero-axiom: `#print axioms WeakHeadStep.reflectAlongStep` reports "does not depend on any axioms". -/
theorem WeakHeadStep.reflectAlongStep {scope : Nat} :
    ∀ {reductType weakHeadReduct : RawTerm scope}, WeakHeadStep reductType weakHeadReduct →
      ∀ {subjectType : RawTerm scope}, Step subjectType reductType →
        ∃ subjectReduct : RawTerm scope, WeakHeadStep subjectType subjectReduct := by
  intro reductType weakHeadReduct weakHeadStep
  induction weakHeadStep with
  | @beta body argument =>
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here rest functionStep =>
            rcases Step.weakHeadOrSpineStepIntoCell functionStep with
              ⟨_functionWhReduct, weakHeadOnFunction⟩
              | ⟨innerChildren, functionEquation, _innerChildStep⟩
            · exact ⟨_, WeakHeadStep.appCongruence weakHeadOnFunction⟩
            · subst functionEquation
              match innerChildren with
              | .childCons _innerDomain (.childCons _innerBody .childNil) =>
                  exact ⟨_, WeakHeadStep.beta⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest _argumentStep =>
                exact ⟨_, WeakHeadStep.beta⟩
            | there _head2 emptyStep => cases emptyStep
  | @appCongruence function functionReduct argument _storedWeakHead inductiveHypothesis =>
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest functionStep =>
            obtain ⟨_headReduct, weakHeadOnHead⟩ := inductiveHypothesis functionStep
            exact ⟨_, WeakHeadStep.appCongruence weakHeadOnHead⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest _argumentStep =>
                exact ⟨_, WeakHeadStep.appCongruence _storedWeakHead⟩
            | there _head2 emptyStep => cases emptyStep
  | @rootIota _innerTerm _innerReduct iotaStep =>
      intro subjectType step
      cases iotaStep with
      | @iotaBoolTrue motive thenBranch elseBranch =>
          -- Phase-Z spine: (motive, then, else, scrutinee=boolTrue).  A step in motive / then /
          -- else leaves the scrutinee a constructor, so the subject is still a boolTrue redex
          -- (`rootIota IotaHeadStep.iotaBoolTrue`).  A step in the LAST child (scrutinee) is
          -- decided by a nested `weakHeadOrSpineStepIntoCell`: a genuine wh-step lifts via
          -- `scrutineeBoolElim`, a spine step into `boolTrue`'s empty spine is impossible.
          rcases Step.weakHeadOrSpineStepIntoCell step with
            ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · subst subjectEquation
            cases childStep with
            | here _rest _motiveStep =>
                exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaBoolTrue⟩
            | there _head tailStep =>
                cases tailStep with
                | here _rest _thenStep =>
                    exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaBoolTrue⟩
                | there _head2 restStep =>
                    cases restStep with
                    | here _rest _elseStep =>
                        exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaBoolTrue⟩
                    | there _head3 scrutineeTailStep =>
                        cases scrutineeTailStep with
                        | here _rest scrutineeStep =>
                            rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨_innerChildren, _scrutineeEquation, innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeBoolElim weakHeadOnScrutinee⟩
                            · cases innerChildStep
                        | there _head4 emptyStep => cases emptyStep
      | @iotaBoolFalse motive thenBranch elseBranch =>
          -- Symmetric to iotaBoolTrue.
          rcases Step.weakHeadOrSpineStepIntoCell step with
            ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · subst subjectEquation
            cases childStep with
            | here _rest _motiveStep =>
                exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaBoolFalse⟩
            | there _head tailStep =>
                cases tailStep with
                | here _rest _thenStep =>
                    exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaBoolFalse⟩
                | there _head2 restStep =>
                    cases restStep with
                    | here _rest _elseStep =>
                        exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaBoolFalse⟩
                    | there _head3 scrutineeTailStep =>
                        cases scrutineeTailStep with
                        | here _rest scrutineeStep =>
                            rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨_innerChildren, _scrutineeEquation, innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeBoolElim weakHeadOnScrutinee⟩
                            · cases innerChildStep
                        | there _head4 emptyStep => cases emptyStep
      | @iotaFstPair firstValue secondValue =>
          -- 1-child spine: the scrutinee IS child 0.  A scrutinee wh-step lifts via `scrutineeFst`;
          -- a spine step into the `pair` keeps it a pair, so the redex re-forms.
          rcases Step.weakHeadOrSpineStepIntoCell step with
            ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · subst subjectEquation
            cases childStep with
            | here _rest scrutineeStep =>
                rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                  ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                  | ⟨innerChildren, scrutineeEquation, _innerChildStep⟩
                · exact ⟨_, WeakHeadStep.scrutineeFst weakHeadOnScrutinee⟩
                · subst scrutineeEquation
                  match innerChildren with
                  | .childCons _innerFirst (.childCons _innerSecond .childNil) =>
                      exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaFstPair⟩
            | there _head tailStep => cases tailStep
      | @iotaSndPair firstValue secondValue =>
          rcases Step.weakHeadOrSpineStepIntoCell step with
            ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · subst subjectEquation
            cases childStep with
            | here _rest scrutineeStep =>
                rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                  ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                  | ⟨innerChildren, scrutineeEquation, _innerChildStep⟩
                · exact ⟨_, WeakHeadStep.scrutineeSnd weakHeadOnScrutinee⟩
                · subst scrutineeEquation
                  match innerChildren with
                  | .childCons _innerFirst (.childCons _innerSecond .childNil) =>
                      exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaSndPair⟩
            | there _head tailStep => cases tailStep
      | @iotaNatElimZero motive zeroBranch succBranch =>
          rcases Step.weakHeadOrSpineStepIntoCell step with
            ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · subst subjectEquation
            cases childStep with
            | here _rest _motiveStep =>
                exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatElimZero⟩
            | there _head tailStep =>
                cases tailStep with
                | here _rest _zeroStep =>
                    exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatElimZero⟩
                | there _head2 restStep =>
                    cases restStep with
                    | here _rest _succStep =>
                        exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatElimZero⟩
                    | there _head3 scrutineeTailStep =>
                        cases scrutineeTailStep with
                        | here _rest scrutineeStep =>
                            rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨_innerChildren, _scrutineeEquation, innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeNatElim weakHeadOnScrutinee⟩
                            · cases innerChildStep
                        | there _head4 emptyStep => cases emptyStep
      | @iotaNatRecZero motive zeroBranch succBranch =>
          rcases Step.weakHeadOrSpineStepIntoCell step with
            ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · subst subjectEquation
            cases childStep with
            | here _rest _motiveStep =>
                exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatRecZero⟩
            | there _head tailStep =>
                cases tailStep with
                | here _rest _zeroStep =>
                    exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatRecZero⟩
                | there _head2 restStep =>
                    cases restStep with
                    | here _rest _succStep =>
                        exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatRecZero⟩
                    | there _head3 scrutineeTailStep =>
                        cases scrutineeTailStep with
                        | here _rest scrutineeStep =>
                            rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨_innerChildren, _scrutineeEquation, innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeNatRec weakHeadOnScrutinee⟩
                            · cases innerChildStep
                        | there _head4 emptyStep => cases emptyStep
      | @iotaListElimNil motive nilBranch consBranch =>
          rcases Step.weakHeadOrSpineStepIntoCell step with
            ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · subst subjectEquation
            cases childStep with
            | here _rest _motiveStep =>
                exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaListElimNil⟩
            | there _head tailStep =>
                cases tailStep with
                | here _rest _nilStep =>
                    exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaListElimNil⟩
                | there _head2 restStep =>
                    cases restStep with
                    | here _rest _consStep =>
                        exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaListElimNil⟩
                    | there _head3 scrutineeTailStep =>
                        cases scrutineeTailStep with
                        | here _rest scrutineeStep =>
                            rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨_innerChildren, _scrutineeEquation, innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeListElim weakHeadOnScrutinee⟩
                            · cases innerChildStep
                        | there _head4 emptyStep => cases emptyStep
      | @iotaOptionMatchNone motive noneBranch someBranch =>
          rcases Step.weakHeadOrSpineStepIntoCell step with
            ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · subst subjectEquation
            cases childStep with
            | here _rest _motiveStep =>
                exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaOptionMatchNone⟩
            | there _head tailStep =>
                cases tailStep with
                | here _rest _noneStep =>
                    exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaOptionMatchNone⟩
                | there _head2 restStep =>
                    cases restStep with
                    | here _rest _someStep =>
                        exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaOptionMatchNone⟩
                    | there _head3 scrutineeTailStep =>
                        cases scrutineeTailStep with
                        | here _rest scrutineeStep =>
                            rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨_innerChildren, _scrutineeEquation, innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeOptionMatch weakHeadOnScrutinee⟩
                            · cases innerChildStep
                        | there _head4 emptyStep => cases emptyStep
      | @iotaOptionMatchSome motive value noneBranch someBranch =>
          -- Payload-bearing scrutinee (`optionSome value`): a spine step into the scrutinee keeps it
          -- an `optionSome`, so the redex re-forms on the stepped payload.
          rcases Step.weakHeadOrSpineStepIntoCell step with
            ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · subst subjectEquation
            cases childStep with
            | here _rest _motiveStep =>
                exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaOptionMatchSome⟩
            | there _head tailStep =>
                cases tailStep with
                | here _rest _noneStep =>
                    exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaOptionMatchSome⟩
                | there _head2 restStep =>
                    cases restStep with
                    | here _rest _someStep =>
                        exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaOptionMatchSome⟩
                    | there _head3 scrutineeTailStep =>
                        cases scrutineeTailStep with
                        | here _rest scrutineeStep =>
                            rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerChildren, scrutineeEquation, _innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeOptionMatch weakHeadOnScrutinee⟩
                            · subst scrutineeEquation
                              match innerChildren with
                              | .childCons _innerValue .childNil =>
                                  exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaOptionMatchSome⟩
                        | there _head4 emptyStep => cases emptyStep
      | @iotaEitherMatchInl motive value leftBranch rightBranch =>
          rcases Step.weakHeadOrSpineStepIntoCell step with
            ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · subst subjectEquation
            cases childStep with
            | here _rest _motiveStep =>
                exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaEitherMatchInl⟩
            | there _head tailStep =>
                cases tailStep with
                | here _rest _leftStep =>
                    exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaEitherMatchInl⟩
                | there _head2 restStep =>
                    cases restStep with
                    | here _rest _rightStep =>
                        exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaEitherMatchInl⟩
                    | there _head3 scrutineeTailStep =>
                        cases scrutineeTailStep with
                        | here _rest scrutineeStep =>
                            rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerChildren, scrutineeEquation, _innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeEitherMatch weakHeadOnScrutinee⟩
                            · subst scrutineeEquation
                              match innerChildren with
                              | .childCons _innerValue .childNil =>
                                  exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaEitherMatchInl⟩
                        | there _head4 emptyStep => cases emptyStep
      | @iotaEitherMatchInr motive value leftBranch rightBranch =>
          rcases Step.weakHeadOrSpineStepIntoCell step with
            ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · subst subjectEquation
            cases childStep with
            | here _rest _motiveStep =>
                exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaEitherMatchInr⟩
            | there _head tailStep =>
                cases tailStep with
                | here _rest _leftStep =>
                    exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaEitherMatchInr⟩
                | there _head2 restStep =>
                    cases restStep with
                    | here _rest _rightStep =>
                        exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaEitherMatchInr⟩
                    | there _head3 scrutineeTailStep =>
                        cases scrutineeTailStep with
                        | here _rest scrutineeStep =>
                            rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerChildren, scrutineeEquation, _innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeEitherMatch weakHeadOnScrutinee⟩
                            · subst scrutineeEquation
                              match innerChildren with
                              | .childCons _innerValue .childNil =>
                                  exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaEitherMatchInr⟩
                        | there _head4 emptyStep => cases emptyStep
      | @iotaNatElimSucc motive predecessor zeroBranch succBranch =>
          rcases Step.weakHeadOrSpineStepIntoCell step with
            ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · subst subjectEquation
            cases childStep with
            | here _rest _motiveStep =>
                exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatElimSucc⟩
            | there _head tailStep =>
                cases tailStep with
                | here _rest _zeroStep =>
                    exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatElimSucc⟩
                | there _head2 restStep =>
                    cases restStep with
                    | here _rest _succStep =>
                        exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatElimSucc⟩
                    | there _head3 scrutineeTailStep =>
                        cases scrutineeTailStep with
                        | here _rest scrutineeStep =>
                            rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerChildren, scrutineeEquation, _innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeNatElim weakHeadOnScrutinee⟩
                            · subst scrutineeEquation
                              match innerChildren with
                              | .childCons _innerPredecessor .childNil =>
                                  exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatElimSucc⟩
                        | there _head4 emptyStep => cases emptyStep
      | @iotaNatRecSucc motive predecessor zeroBranch succBranch =>
          rcases Step.weakHeadOrSpineStepIntoCell step with
            ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · subst subjectEquation
            cases childStep with
            | here _rest _motiveStep =>
                exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatRecSucc⟩
            | there _head tailStep =>
                cases tailStep with
                | here _rest _zeroStep =>
                    exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatRecSucc⟩
                | there _head2 restStep =>
                    cases restStep with
                    | here _rest _succStep =>
                        exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatRecSucc⟩
                    | there _head3 scrutineeTailStep =>
                        cases scrutineeTailStep with
                        | here _rest scrutineeStep =>
                            rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerChildren, scrutineeEquation, _innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeNatRec weakHeadOnScrutinee⟩
                            · subst scrutineeEquation
                              match innerChildren with
                              | .childCons _innerPredecessor .childNil =>
                                  exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatRecSucc⟩
                        | there _head4 emptyStep => cases emptyStep
      | @iotaListElimCons motive headVal tailVal nilBranch consBranch =>
          rcases Step.weakHeadOrSpineStepIntoCell step with
            ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · subst subjectEquation
            cases childStep with
            | here _rest _motiveStep =>
                exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaListElimCons⟩
            | there _head tailStep =>
                cases tailStep with
                | here _rest _nilStep =>
                    exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaListElimCons⟩
                | there _head2 restStep =>
                    cases restStep with
                    | here _rest _consStep =>
                        exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaListElimCons⟩
                    | there _head3 scrutineeTailStep =>
                        cases scrutineeTailStep with
                        | here _rest scrutineeStep =>
                            rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerChildren, scrutineeEquation, _innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeListElim weakHeadOnScrutinee⟩
                            · subst scrutineeEquation
                              match innerChildren with
                              | .childCons _innerHead (.childCons _innerTail .childNil) =>
                                  exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaListElimCons⟩
                        | there _head4 emptyStep => cases emptyStep
      | @iotaIdJRefl motive baseCase rawWitness =>
          -- Phase-Z spine: (motive, baseCase, witness=refl rawWitness) — the scrutinee is child 2.
          rcases Step.weakHeadOrSpineStepIntoCell step with
            ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · subst subjectEquation
            cases childStep with
            | here _rest _motiveStep =>
                exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaIdJRefl⟩
            | there _head tailStep =>
                cases tailStep with
                | here _rest _baseStep =>
                    exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaIdJRefl⟩
                | there _head2 restStep =>
                    cases restStep with
                    | here _rest scrutineeStep =>
                        rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                          ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                          | ⟨innerChildren, scrutineeEquation, _innerChildStep⟩
                        · exact ⟨_, WeakHeadStep.scrutineeIdJ weakHeadOnScrutinee⟩
                        · subst scrutineeEquation
                          match innerChildren with
                          | .childCons _innerWitness .childNil =>
                              exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaIdJRefl⟩
                    | there _head3 emptyStep => cases emptyStep
      | @iotaIdStrictRecRefl motive baseCase rawWitness =>
          -- Symmetric to the idJ arm.
          rcases Step.weakHeadOrSpineStepIntoCell step with
            ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · subst subjectEquation
            cases childStep with
            | here _rest _motiveStep =>
                exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaIdStrictRecRefl⟩
            | there _head tailStep =>
                cases tailStep with
                | here _rest _baseStep =>
                    exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaIdStrictRecRefl⟩
                | there _head2 restStep =>
                    cases restStep with
                    | here _rest scrutineeStep =>
                        rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                          ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                          | ⟨innerChildren, scrutineeEquation, _innerChildStep⟩
                        · exact ⟨_, WeakHeadStep.scrutineeIdStrictRec weakHeadOnScrutinee⟩
                        · subst scrutineeEquation
                          match innerChildren with
                          | .childCons _innerWitness .childNil =>
                              exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaIdStrictRecRefl⟩
                    | there _head3 emptyStep => cases emptyStep
  | @scrutineeBoolElim motive scrutinee scrutineeReduct thenBranch elseBranch
      _storedWeakHead inductiveHypothesis =>
      -- Phase-Z spine: (motive, then, else, scrutinee).  A step in motive / then / else leaves the
      -- scrutinee still reducible (`scrutineeBoolElim _storedWeakHead`); a scrutinee step recurses
      -- through the induction hypothesis.
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep =>
            exact ⟨_, WeakHeadStep.scrutineeBoolElim _storedWeakHead⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest _thenStep =>
                exact ⟨_, WeakHeadStep.scrutineeBoolElim _storedWeakHead⟩
            | there _head2 restStep =>
                cases restStep with
                | here _rest _elseStep =>
                    exact ⟨_, WeakHeadStep.scrutineeBoolElim _storedWeakHead⟩
                | there _head3 scrutineeTailStep =>
                    cases scrutineeTailStep with
                    | here _rest scrutineeStep =>
                        obtain ⟨_scrutineeReduct2, weakHeadOnScrutinee⟩ :=
                          inductiveHypothesis scrutineeStep
                        exact ⟨_, WeakHeadStep.scrutineeBoolElim weakHeadOnScrutinee⟩
                    | there _head4 emptyStep => cases emptyStep
  | @scrutineeFst scrutinee scrutineeReduct _storedWeakHead inductiveHypothesis =>
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest scrutineeStep =>
            obtain ⟨_scrutineeReduct2, weakHeadOnScrutinee⟩ := inductiveHypothesis scrutineeStep
            exact ⟨_, WeakHeadStep.scrutineeFst weakHeadOnScrutinee⟩
        | there _head tailStep => cases tailStep
  | @scrutineeSnd scrutinee scrutineeReduct _storedWeakHead inductiveHypothesis =>
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest scrutineeStep =>
            obtain ⟨_scrutineeReduct2, weakHeadOnScrutinee⟩ := inductiveHypothesis scrutineeStep
            exact ⟨_, WeakHeadStep.scrutineeSnd weakHeadOnScrutinee⟩
        | there _head tailStep => cases tailStep
  | @scrutineeNatElim motive scrutinee scrutineeReduct zeroBranch succBranch
      _storedWeakHead inductiveHypothesis =>
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep =>
            exact ⟨_, WeakHeadStep.scrutineeNatElim _storedWeakHead⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest _zeroStep =>
                exact ⟨_, WeakHeadStep.scrutineeNatElim _storedWeakHead⟩
            | there _head2 restStep =>
                cases restStep with
                | here _rest _succStep =>
                    exact ⟨_, WeakHeadStep.scrutineeNatElim _storedWeakHead⟩
                | there _head3 scrutineeTailStep =>
                    cases scrutineeTailStep with
                    | here _rest scrutineeStep =>
                        obtain ⟨_scrutineeReduct2, weakHeadOnScrutinee⟩ :=
                          inductiveHypothesis scrutineeStep
                        exact ⟨_, WeakHeadStep.scrutineeNatElim weakHeadOnScrutinee⟩
                    | there _head4 emptyStep => cases emptyStep
  | @scrutineeNatRec motive scrutinee scrutineeReduct zeroBranch succBranch
      _storedWeakHead inductiveHypothesis =>
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep =>
            exact ⟨_, WeakHeadStep.scrutineeNatRec _storedWeakHead⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest _zeroStep =>
                exact ⟨_, WeakHeadStep.scrutineeNatRec _storedWeakHead⟩
            | there _head2 restStep =>
                cases restStep with
                | here _rest _succStep =>
                    exact ⟨_, WeakHeadStep.scrutineeNatRec _storedWeakHead⟩
                | there _head3 scrutineeTailStep =>
                    cases scrutineeTailStep with
                    | here _rest scrutineeStep =>
                        obtain ⟨_scrutineeReduct2, weakHeadOnScrutinee⟩ :=
                          inductiveHypothesis scrutineeStep
                        exact ⟨_, WeakHeadStep.scrutineeNatRec weakHeadOnScrutinee⟩
                    | there _head4 emptyStep => cases emptyStep
  | @scrutineeListElim motive scrutinee scrutineeReduct nilBranch consBranch
      _storedWeakHead inductiveHypothesis =>
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep =>
            exact ⟨_, WeakHeadStep.scrutineeListElim _storedWeakHead⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest _nilStep =>
                exact ⟨_, WeakHeadStep.scrutineeListElim _storedWeakHead⟩
            | there _head2 restStep =>
                cases restStep with
                | here _rest _consStep =>
                    exact ⟨_, WeakHeadStep.scrutineeListElim _storedWeakHead⟩
                | there _head3 scrutineeTailStep =>
                    cases scrutineeTailStep with
                    | here _rest scrutineeStep =>
                        obtain ⟨_scrutineeReduct2, weakHeadOnScrutinee⟩ :=
                          inductiveHypothesis scrutineeStep
                        exact ⟨_, WeakHeadStep.scrutineeListElim weakHeadOnScrutinee⟩
                    | there _head4 emptyStep => cases emptyStep
  | @scrutineeOptionMatch motive scrutinee scrutineeReduct noneBranch someBranch
      _storedWeakHead inductiveHypothesis =>
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep =>
            exact ⟨_, WeakHeadStep.scrutineeOptionMatch _storedWeakHead⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest _noneStep =>
                exact ⟨_, WeakHeadStep.scrutineeOptionMatch _storedWeakHead⟩
            | there _head2 restStep =>
                cases restStep with
                | here _rest _someStep =>
                    exact ⟨_, WeakHeadStep.scrutineeOptionMatch _storedWeakHead⟩
                | there _head3 scrutineeTailStep =>
                    cases scrutineeTailStep with
                    | here _rest scrutineeStep =>
                        obtain ⟨_scrutineeReduct2, weakHeadOnScrutinee⟩ :=
                          inductiveHypothesis scrutineeStep
                        exact ⟨_, WeakHeadStep.scrutineeOptionMatch weakHeadOnScrutinee⟩
                    | there _head4 emptyStep => cases emptyStep
  | @scrutineeEitherMatch motive scrutinee scrutineeReduct leftBranch rightBranch
      _storedWeakHead inductiveHypothesis =>
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep =>
            exact ⟨_, WeakHeadStep.scrutineeEitherMatch _storedWeakHead⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest _leftStep =>
                exact ⟨_, WeakHeadStep.scrutineeEitherMatch _storedWeakHead⟩
            | there _head2 restStep =>
                cases restStep with
                | here _rest _rightStep =>
                    exact ⟨_, WeakHeadStep.scrutineeEitherMatch _storedWeakHead⟩
                | there _head3 scrutineeTailStep =>
                    cases scrutineeTailStep with
                    | here _rest scrutineeStep =>
                        obtain ⟨_scrutineeReduct2, weakHeadOnScrutinee⟩ :=
                          inductiveHypothesis scrutineeStep
                        exact ⟨_, WeakHeadStep.scrutineeEitherMatch weakHeadOnScrutinee⟩
                    | there _head4 emptyStep => cases emptyStep
  | @scrutineeIdJ motive baseCase scrutinee scrutineeReduct _storedWeakHead inductiveHypothesis =>
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep =>
            exact ⟨_, WeakHeadStep.scrutineeIdJ _storedWeakHead⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest _baseStep =>
                exact ⟨_, WeakHeadStep.scrutineeIdJ _storedWeakHead⟩
            | there _head2 restStep =>
                cases restStep with
                | here _rest scrutineeStep =>
                    obtain ⟨_scrutineeReduct2, weakHeadOnScrutinee⟩ := inductiveHypothesis scrutineeStep
                    exact ⟨_, WeakHeadStep.scrutineeIdJ weakHeadOnScrutinee⟩
                | there _head3 emptyStep => cases emptyStep
  | @scrutineeIdStrictRec motive baseCase scrutinee scrutineeReduct _storedWeakHead inductiveHypothesis =>
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep =>
            exact ⟨_, WeakHeadStep.scrutineeIdStrictRec _storedWeakHead⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest _baseStep =>
                exact ⟨_, WeakHeadStep.scrutineeIdStrictRec _storedWeakHead⟩
            | there _head2 restStep =>
                cases restStep with
                | here _rest scrutineeStep =>
                    obtain ⟨_scrutineeReduct2, weakHeadOnScrutinee⟩ := inductiveHypothesis scrutineeStep
                    exact ⟨_, WeakHeadStep.scrutineeIdStrictRec weakHeadOnScrutinee⟩
                | there _head3 emptyStep => cases emptyStep
  | @pathBeta spine reduct fires =>
      -- Canonical-table endpoint-β: the redex `pathApp(pathLam(body), arg)` is the REDUCT of `step`.
      -- Pin the spine to a path-λ (via the firing's primary-head test), then mirror the `beta` arm — a
      -- function-slot wh-step lifts via `pathAppCongruence`; a function-slot spine step that re-forms
      -- the path-λ, or an argument-slot step, leaves a `pathBeta` redex (`pathBeta rfl`).
      obtain ⟨functionChild, argumentChild, spineShape⟩ :
          ∃ functionChild argumentChild,
            spine = .childCons functionChild (.childCons argumentChild .childNil) := by
        cases spine with
        | childCons functionChild restSpine =>
            cases restSpine with
            | childCons argumentChild nilTail => cases nilTail; exact ⟨_, _, rfl⟩
      subst spineShape
      obtain ⟨_pathBody, functionIsPathLam⟩ :
          ∃ pathBody : RawTerm (scope + 1),
            functionChild = .mkGen .gen_pathLam () (.childCons pathBody .childNil) := by
        cases functionChild with
        | mkGen functionGenerator functionPayload functionChildren =>
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases functionPayload
            cases functionChildren with
            | childCons pathBody pathNil => cases pathNil; exact ⟨pathBody, rfl⟩
      subst functionIsPathLam
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest functionStep =>
            rcases Step.weakHeadOrSpineStepIntoCell functionStep with
              ⟨_functionWhReduct, weakHeadOnFunction⟩
              | ⟨innerChildren, functionEquation, _innerChildStep⟩
            · exact ⟨_, WeakHeadStep.pathAppCongruence weakHeadOnFunction⟩
            · subst functionEquation
              match innerChildren with
              | .childCons _innerBody .childNil =>
                  exact ⟨_, WeakHeadStep.pathBeta rfl⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest _argumentStep =>
                exact ⟨_, WeakHeadStep.pathBeta rfl⟩
            | there _head2 emptyStep => cases emptyStep
  | @quotRecMk spine reduct fires =>
      -- Quotient lift: pin the slot-2 scrutinee to `quotMk` (via the firing's primary-head test), then
      -- a kernel/respects-slot step keeps the redex (`quotRecMk rfl`); a scrutinee-slot wh-step lifts
      -- via `scrutineeQuotRec`, a scrutinee spine step that re-forms `quotMk` keeps the redex.
      obtain ⟨kernelFn, respectsRel, scrutinee, spineShape⟩ :
          ∃ kernelFn respectsRel scrutinee,
            spine =
              .childCons kernelFn (.childCons respectsRel (.childCons scrutinee .childNil)) := by
        cases spine with
        | childCons kernelFn restSpine =>
            cases restSpine with
            | childCons respectsRel restSpine2 =>
                cases restSpine2 with
                | childCons scrutinee nilTail => cases nilTail; exact ⟨_, _, _, rfl⟩
      subst spineShape
      obtain ⟨_value, scrutineeIsMk⟩ :
          ∃ value : RawTerm scope,
            scrutinee = .mkGen .gen_quotMk () (.childCons value .childNil) := by
        cases scrutinee with
        | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineePayload
            cases scrutineeChildren with
            | childCons value valueNil => cases valueNil; exact ⟨value, rfl⟩
      subst scrutineeIsMk
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _kernelStep =>
            exact ⟨_, WeakHeadStep.quotRecMk rfl⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest _respectsStep =>
                exact ⟨_, WeakHeadStep.quotRecMk rfl⟩
            | there _head2 restStep =>
                cases restStep with
                | here _rest scrutineeStep =>
                    rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                      ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                      | ⟨innerChildren, scrutineeEquation, _innerChildStep⟩
                    · exact ⟨_, WeakHeadStep.scrutineeQuotRec weakHeadOnScrutinee⟩
                    · subst scrutineeEquation
                      match innerChildren with
                      | .childCons _innerValue .childNil =>
                          exact ⟨_, WeakHeadStep.quotRecMk rfl⟩
                | there _head3 emptyStep => cases emptyStep
  | @quotElimMk spine reduct fires =>
      -- Dependent quotient eliminator: slot-2 scrutinee `quotMk`; symmetric to `quotRecMk`.
      obtain ⟨depMotive, depKernel, scrutinee, spineShape⟩ :
          ∃ depMotive depKernel scrutinee,
            spine =
              .childCons depMotive (.childCons depKernel (.childCons scrutinee .childNil)) := by
        cases spine with
        | childCons depMotive restSpine =>
            cases restSpine with
            | childCons depKernel restSpine2 =>
                cases restSpine2 with
                | childCons scrutinee nilTail => cases nilTail; exact ⟨_, _, _, rfl⟩
      subst spineShape
      obtain ⟨_value, scrutineeIsMk⟩ :
          ∃ value : RawTerm scope,
            scrutinee = .mkGen .gen_quotMk () (.childCons value .childNil) := by
        cases scrutinee with
        | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineePayload
            cases scrutineeChildren with
            | childCons value valueNil => cases valueNil; exact ⟨value, rfl⟩
      subst scrutineeIsMk
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep =>
            exact ⟨_, WeakHeadStep.quotElimMk rfl⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest _kernelStep =>
                exact ⟨_, WeakHeadStep.quotElimMk rfl⟩
            | there _head2 restStep =>
                cases restStep with
                | here _rest scrutineeStep =>
                    rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                      ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                      | ⟨innerChildren, scrutineeEquation, _innerChildStep⟩
                    · exact ⟨_, WeakHeadStep.scrutineeQuotElim weakHeadOnScrutinee⟩
                    · subst scrutineeEquation
                      match innerChildren with
                      | .childCons _innerValue .childNil =>
                          exact ⟨_, WeakHeadStep.quotElimMk rfl⟩
                | there _head3 emptyStep => cases emptyStep
  | @truncRecIntro truncationLevel spine reduct fires =>
      -- Truncation recursor: slot-1 scrutinee `truncIntro` (its own level is irrelevant to firing).
      obtain ⟨kernelFn, scrutinee, spineShape⟩ :
          ∃ kernelFn scrutinee,
            spine = .childCons kernelFn (.childCons scrutinee .childNil) := by
        cases spine with
        | childCons kernelFn restSpine =>
            cases restSpine with
            | childCons scrutinee nilTail => cases nilTail; exact ⟨_, _, rfl⟩
      subst spineShape
      obtain ⟨_scrutineeLevel, _value, scrutineeIsIntro⟩ :
          ∃ scrutineeLevel value,
            scrutinee = .mkGen .gen_truncIntro scrutineeLevel (.childCons value .childNil) := by
        cases scrutinee with
        | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineeChildren with
            | childCons value valueNil => cases valueNil; exact ⟨scrutineePayload, value, rfl⟩
      subst scrutineeIsIntro
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _kernelStep =>
            exact ⟨_, WeakHeadStep.truncRecIntro rfl⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest scrutineeStep =>
                rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
                  ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                  | ⟨innerChildren, scrutineeEquation, _innerChildStep⟩
                · exact ⟨_, WeakHeadStep.scrutineeTruncRec weakHeadOnScrutinee⟩
                · subst scrutineeEquation
                  match innerChildren with
                  | .childCons _innerValue .childNil =>
                      exact ⟨_, WeakHeadStep.truncRecIntro rfl⟩
            | there _head2 emptyStep => cases emptyStep
  | @pathAppCongruence function functionReduct argument storedWeakHead inductiveHypothesis =>
      -- Native weak-head congruence at slot 0 of `pathApp` — twin of `appCongruence`.
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest functionStep =>
            obtain ⟨_functionReduct2, weakHeadOnFunction⟩ := inductiveHypothesis functionStep
            exact ⟨_, WeakHeadStep.pathAppCongruence weakHeadOnFunction⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest _argumentStep =>
                exact ⟨_, WeakHeadStep.pathAppCongruence storedWeakHead⟩
            | there _head2 emptyStep => cases emptyStep
  | @scrutineeQuotRec kernelFn respectsRel scrutinee scrutineeReduct
      storedWeakHead inductiveHypothesis =>
      -- Native weak-head congruence at slot 2 of `quotRec` — twin of the data scrutinee arms.
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _kernelStep =>
            exact ⟨_, WeakHeadStep.scrutineeQuotRec storedWeakHead⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest _respectsStep =>
                exact ⟨_, WeakHeadStep.scrutineeQuotRec storedWeakHead⟩
            | there _head2 restStep =>
                cases restStep with
                | here _rest scrutineeStep =>
                    obtain ⟨_scrutineeReduct2, weakHeadOnScrutinee⟩ :=
                      inductiveHypothesis scrutineeStep
                    exact ⟨_, WeakHeadStep.scrutineeQuotRec weakHeadOnScrutinee⟩
                | there _head3 emptyStep => cases emptyStep
  | @scrutineeQuotElim depMotive depKernel scrutinee scrutineeReduct
      storedWeakHead inductiveHypothesis =>
      -- Native weak-head congruence at slot 2 of `quotElim`.
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _motiveStep =>
            exact ⟨_, WeakHeadStep.scrutineeQuotElim storedWeakHead⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest _kernelStep =>
                exact ⟨_, WeakHeadStep.scrutineeQuotElim storedWeakHead⟩
            | there _head2 restStep =>
                cases restStep with
                | here _rest scrutineeStep =>
                    obtain ⟨_scrutineeReduct2, weakHeadOnScrutinee⟩ :=
                      inductiveHypothesis scrutineeStep
                    exact ⟨_, WeakHeadStep.scrutineeQuotElim weakHeadOnScrutinee⟩
                | there _head3 emptyStep => cases emptyStep
  | @scrutineeTruncRec truncationLevel kernelFn scrutinee scrutineeReduct
      storedWeakHead inductiveHypothesis =>
      -- Native weak-head congruence at slot 1 of `truncRec` (level in payload).
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest _kernelStep =>
            exact ⟨_, WeakHeadStep.scrutineeTruncRec storedWeakHead⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest scrutineeStep =>
                obtain ⟨_scrutineeReduct2, weakHeadOnScrutinee⟩ :=
                  inductiveHypothesis scrutineeStep
                exact ⟨_, WeakHeadStep.scrutineeTruncRec weakHeadOnScrutinee⟩
            | there _head2 emptyStep => cases emptyStep
  | @gelBeta spine reduct fires =>
      -- gel-β: pin the slot-0 scrutinee to `gel` (via the firing's primary-head test); a scrutinee-slot
      -- wh-step lifts via `scrutineeUngel`, a scrutinee spine step that re-forms `gel` keeps the redex.
      obtain ⟨scrutinee, spineShape⟩ :
          ∃ scrutinee, spine = .childCons scrutinee .childNil := by
        cases spine with
        | childCons scrutinee nilTail => cases nilTail; exact ⟨_, rfl⟩
      subst spineShape
      obtain ⟨_leftComponent, _rightComponent, _witness, scrutineeIsGel⟩ :
          ∃ leftComponent rightComponent witness : RawTerm scope,
            scrutinee = .mkGen .gen_gel ()
              (.childCons leftComponent
                (.childCons rightComponent (.childCons witness .childNil))) := by
        cases scrutinee with
        | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
            have isHead := IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
            subst isHead
            cases scrutineePayload
            cases scrutineeChildren with
            | childCons leftComponent rest =>
                cases rest with
                | childCons rightComponent rest2 =>
                    cases rest2 with
                    | childCons witness witnessNil =>
                        cases witnessNil
                        exact ⟨leftComponent, rightComponent, witness, rfl⟩
      subst scrutineeIsGel
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest scrutineeStep =>
            rcases Step.weakHeadOrSpineStepIntoCell scrutineeStep with
              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
              | ⟨innerChildren, scrutineeEquation, _innerChildStep⟩
            · exact ⟨_, WeakHeadStep.scrutineeUngel weakHeadOnScrutinee⟩
            · subst scrutineeEquation
              match innerChildren with
              | .childCons _innerLeft (.childCons _innerRight (.childCons _innerWitness .childNil)) =>
                  exact ⟨_, WeakHeadStep.gelBeta rfl⟩
        | there _head emptyStep => cases emptyStep
  | @scrutineeUngel scrutinee scrutineeReduct _storedWeakHead inductiveHypothesis =>
      intro subjectType step
      rcases Step.weakHeadOrSpineStepIntoCell step with
        ⟨subjectReduct, weakHeadOnSubject⟩ | ⟨sourceChildren, subjectEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · subst subjectEquation
        cases childStep with
        | here _rest scrutineeStep =>
            obtain ⟨_scrutineeReduct2, weakHeadOnScrutinee⟩ := inductiveHypothesis scrutineeStep
            exact ⟨_, WeakHeadStep.scrutineeUngel weakHeadOnScrutinee⟩
        | there _head tailStep => cases tailStep

/-- **Weak-head-normality is preserved under reduction.**  If `subjectType` is weak-head NORMAL (no
weak-head step) and reduces to `reductType`, then `reductType` is weak-head normal too — a reduction never
CREATES a weak-head redex out of a normal form.  The contrapositive of `reflectAlongStep`: any weak-head
step on the reduct would reflect back to one on the (normal) subject.  This is the `neutral` arm's
stability half — composed with `Step.rootGenerator_eq_of_weakHeadNormal` (root-generator stability), it
keeps the whole `neutral` classification invariant under reduction. -/
theorem WeakHeadStep.weakHeadNormalPreservedByStep {scope : Nat}
    {subjectType reductType : RawTerm scope}
    (weakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep subjectType reduct)
    (step : Step subjectType reductType) :
    ∀ reduct : RawTerm scope, ¬ WeakHeadStep reductType reduct :=
  fun _reduct weakHeadOnReduct =>
    let ⟨_subjectReduct, weakHeadOnSubject⟩ := WeakHeadStep.reflectAlongStep weakHeadOnReduct step
    weakHeadNormal _ weakHeadOnSubject

end FX1Poly.Core

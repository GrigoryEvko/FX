import FX1Poly.Core.ReducibleTypeForwardClosure

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

`reflectAlongStep` is by INDUCTION ON the weak-head step `WeakHeadStep reductType weakHeadReduct` (the
SECOND-to-first argument), not on the arbitrary `Step` and not by well-founded recursion.  In each
weak-head-step constructor case the arbitrary `Step subjectType <concreteReduct>` is inverted by
`Step.weakHeadStep_or_cong`:

  * **root reduction (`Or.inl`)** — the arbitrary step exposed a weak-head step on `subjectType` directly;
    `subjectType` already has a wh-step.  IDENTICAL across all thirteen constructor cases.

  * **congruence (`Or.inr`)** — `subjectType = mkGen G payload children`, `<concreteReduct> =
    mkGen G payload childrenAfter`, with `StepChildren children childrenAfter`.  Pinning `G` (via
    `congrArg RawTerm.rootGenerator`), the payload, and the concrete reduct children FIRST, then casing
    the `StepChildren` against the now-concrete target, splits cleanly by WHICH child stepped:
      - a SCRUTINEE child stepped — recurse with the induction hypothesis (`appCongruence`/`scrutinee*`)
        or, for `rootIota`, decide via a nested `Step.weakHeadStep_or_cong` whether the scrutinee is now a
        constructor (re-form the ι redex) or genuinely reducible (lift the scrutinee's wh-step);
      - a NON-scrutinee child (branch / argument / base case) stepped — the scrutinee is unchanged, so the
        subject is still a redex (`beta` / `rootIota`) at the same head.

The `beta`/`appCongruence` cases use a nested `Step.weakHeadStep_or_cong` on the function child to decide
β-redex-vs-`appCongruence`; the sixteen `rootIota` sub-cases are the bulk, one per ι rule, uniform up to
the scrutinee's child position (Phase-Z places it LAST in every eliminator: child 3 for `boolElim` /
`natElim` / `natRec` / `listElim` / `optionMatch` / `eitherMatch` whose spines lead with `motive`, child 2
for `idJ`/`idStrictRec` whose spine is `(motive, baseCase, witness)`, child 0 for `fst`/`snd`) and arity
(nullary constructors refute the impossible cong-into-leaf spine by `cases`).  The corollary
`weakHeadNormalPreservedByStep` is the four-line contrapositive.

## Zero-axiom verification

`induction` on `WeakHeadStep` then `Step.weakHeadStep_or_cong` inversion + `cases` on `StepChildren`
against a pinned-concrete target (the propext-clean route the whole `Step`-inversion family uses);
generator pinning via `congrArg RawTerm.rootGenerator`; impossible cong-into-leaf spines closed by `cases`.
No `axiom`, `sorry`, `admit`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Verified
per declaration: `#print axioms WeakHeadStep.reflectAlongStep` and
`#print axioms WeakHeadStep.weakHeadNormalPreservedByStep` each report "does not depend on any axioms".
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **A weak-head step reflects backward across an arbitrary single step.**  If `subjectType` reduces to
`reductType` and `reductType` has a weak-head step, then `subjectType` ALREADY has a weak-head step — a
single reduction can never CREATE a weak-head redex where the source had none.

Induction on the weak-head step; each arbitrary `Step subjectType reductType` is inverted by
`Step.weakHeadStep_or_cong`.  The root-reduction disjunct yields the source weak-head step verbatim; the
congruence disjunct pins the generator (`congrArg RawTerm.rootGenerator`), payload, and reduct children,
then cases the `StepChildren` against the now-concrete target — a stepped scrutinee recurses through the
induction hypothesis (or, in `rootIota`, a nested `Step.weakHeadStep_or_cong` re-forms the ι redex or
lifts the scrutinee's wh-step), a stepped branch / argument / base case leaves the redex intact at the
same head (`beta` / `rootIota`).

Zero-axiom: `#print axioms WeakHeadStep.reflectAlongStep` reports "does not depend on any axioms". -/
theorem WeakHeadStep.reflectAlongStep {scope : Nat} :
    ∀ {reductType weakHeadReduct : RawTerm scope}, WeakHeadStep reductType weakHeadReduct →
      ∀ {subjectType : RawTerm scope}, Step subjectType reductType →
        ∃ subjectReduct : RawTerm scope, WeakHeadStep subjectType subjectReduct := by
  intro reductType weakHeadReduct weakHeadStep
  induction weakHeadStep with
  | @beta body argument =>
      intro subjectType step
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_app = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
        cases childStep with
        | here rest functionStep =>
            rcases Step.weakHeadStep_or_cong functionStep with
              ⟨_functionWhReduct, weakHeadOnFunction⟩
              | ⟨innerGenerator, innerPayload, innerChildren, _innerAfter,
                  functionEquation, lamEquation, _innerChildStep⟩
            · exact ⟨_, WeakHeadStep.appCongruence weakHeadOnFunction⟩
            · have innerGeneratorEquation : Generator.gen_lam = innerGenerator :=
                congrArg RawTerm.rootGenerator lamEquation
              subst innerGeneratorEquation
              subst functionEquation
              injection lamEquation with _innerScopeEq _innerGenEq innerPayloadEquation _innerChildrenEq
              subst innerPayloadEquation
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
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_app = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
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
          -- decided by a nested `weakHeadStep_or_cong`: a genuine wh-step lifts via
          -- `scrutineeBoolElim`, a cong into `boolTrue`'s empty spine is impossible.
          rcases Step.weakHeadStep_or_cong step with
            ⟨subjectReduct, weakHeadOnSubject⟩
            | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · have generatorEquation : Generator.gen_boolElim = generator :=
              congrArg RawTerm.rootGenerator reductEquation
            subst generatorEquation
            subst subjectEquation
            injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
            subst payloadEquation
            subst childrenAfterEquation
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
                            rcases Step.weakHeadStep_or_cong scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerGenerator, _innerPayload, _innerChildren, innerAfter,
                                  _scrutineeEquation, ctorEquation, innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeBoolElim weakHeadOnScrutinee⟩
                            · have innerGeneratorEquation : Generator.gen_boolTrue = innerGenerator :=
                                congrArg RawTerm.rootGenerator ctorEquation
                              subst innerGeneratorEquation
                              injection ctorEquation with
                                _innerScopeEq _innerGenEq _innerPayloadEq innerAfterEquation
                              subst innerAfterEquation
                              cases innerChildStep
                        | there _head4 emptyStep => cases emptyStep
      | @iotaBoolFalse motive thenBranch elseBranch =>
          -- Phase-Z spine: (motive, then, else, scrutinee=boolFalse).  Symmetric to iotaBoolTrue.
          rcases Step.weakHeadStep_or_cong step with
            ⟨subjectReduct, weakHeadOnSubject⟩
            | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · have generatorEquation : Generator.gen_boolElim = generator :=
              congrArg RawTerm.rootGenerator reductEquation
            subst generatorEquation
            subst subjectEquation
            injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
            subst payloadEquation
            subst childrenAfterEquation
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
                            rcases Step.weakHeadStep_or_cong scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerGenerator, _innerPayload, _innerChildren, innerAfter,
                                  _scrutineeEquation, ctorEquation, innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeBoolElim weakHeadOnScrutinee⟩
                            · have innerGeneratorEquation : Generator.gen_boolFalse = innerGenerator :=
                                congrArg RawTerm.rootGenerator ctorEquation
                              subst innerGeneratorEquation
                              injection ctorEquation with
                                _innerScopeEq _innerGenEq _innerPayloadEq innerAfterEquation
                              subst innerAfterEquation
                              cases innerChildStep
                        | there _head4 emptyStep => cases emptyStep
      | @iotaFstPair firstValue secondValue =>
          rcases Step.weakHeadStep_or_cong step with
            ⟨subjectReduct, weakHeadOnSubject⟩
            | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · have generatorEquation : Generator.gen_fst = generator :=
              congrArg RawTerm.rootGenerator reductEquation
            subst generatorEquation
            subst subjectEquation
            injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
            subst payloadEquation
            subst childrenAfterEquation
            cases childStep with
            | here _rest scrutineeStep =>
                rcases Step.weakHeadStep_or_cong scrutineeStep with
                  ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                  | ⟨innerGenerator, innerPayload, innerChildren, _innerAfter,
                      scrutineeEquation, ctorEquation, _innerChildStep⟩
                · exact ⟨_, WeakHeadStep.scrutineeFst weakHeadOnScrutinee⟩
                · have innerGeneratorEquation : Generator.gen_pair = innerGenerator :=
                    congrArg RawTerm.rootGenerator ctorEquation
                  subst innerGeneratorEquation
                  subst scrutineeEquation
                  match innerPayload, innerChildren with
                  | (), .childCons _innerFirst (.childCons _innerSecond .childNil) =>
                      exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaFstPair⟩
            | there _head tailStep => cases tailStep
      | @iotaSndPair firstValue secondValue =>
          rcases Step.weakHeadStep_or_cong step with
            ⟨subjectReduct, weakHeadOnSubject⟩
            | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · have generatorEquation : Generator.gen_snd = generator :=
              congrArg RawTerm.rootGenerator reductEquation
            subst generatorEquation
            subst subjectEquation
            injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
            subst payloadEquation
            subst childrenAfterEquation
            cases childStep with
            | here _rest scrutineeStep =>
                rcases Step.weakHeadStep_or_cong scrutineeStep with
                  ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                  | ⟨innerGenerator, innerPayload, innerChildren, _innerAfter,
                      scrutineeEquation, ctorEquation, _innerChildStep⟩
                · exact ⟨_, WeakHeadStep.scrutineeSnd weakHeadOnScrutinee⟩
                · have innerGeneratorEquation : Generator.gen_pair = innerGenerator :=
                    congrArg RawTerm.rootGenerator ctorEquation
                  subst innerGeneratorEquation
                  subst scrutineeEquation
                  match innerPayload, innerChildren with
                  | (), .childCons _innerFirst (.childCons _innerSecond .childNil) =>
                      exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaSndPair⟩
            | there _head tailStep => cases tailStep
      | @iotaNatElimZero motive zeroBranch succBranch =>
          -- Phase-Z spine: (motive, zero, succ, scrutinee=natZero).  A step in motive / zero /
          -- succ leaves the scrutinee a constructor, so the subject is still a natZero redex
          -- (`rootIota IotaHeadStep.iotaNatElimZero`).  A step in the LAST child (scrutinee) is
          -- decided by a nested `weakHeadStep_or_cong`: a genuine wh-step lifts via
          -- `scrutineeNatElim`, a cong into `natZero`'s empty spine is impossible.
          rcases Step.weakHeadStep_or_cong step with
            ⟨subjectReduct, weakHeadOnSubject⟩
            | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · have generatorEquation : Generator.gen_natElim = generator :=
              congrArg RawTerm.rootGenerator reductEquation
            subst generatorEquation
            subst subjectEquation
            injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
            subst payloadEquation
            subst childrenAfterEquation
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
                            rcases Step.weakHeadStep_or_cong scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerGenerator, _innerPayload, _innerChildren, innerAfter,
                                  _scrutineeEquation, ctorEquation, innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeNatElim weakHeadOnScrutinee⟩
                            · have innerGeneratorEquation : Generator.gen_natZero = innerGenerator :=
                                congrArg RawTerm.rootGenerator ctorEquation
                              subst innerGeneratorEquation
                              injection ctorEquation with
                                _innerScopeEq _innerGenEq _innerPayloadEq innerAfterEquation
                              subst innerAfterEquation
                              cases innerChildStep
                        | there _head4 emptyStep => cases emptyStep
      | @iotaNatRecZero motive zeroBranch succBranch =>
          rcases Step.weakHeadStep_or_cong step with
            ⟨subjectReduct, weakHeadOnSubject⟩
            | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · have generatorEquation : Generator.gen_natRec = generator :=
              congrArg RawTerm.rootGenerator reductEquation
            subst generatorEquation
            subst subjectEquation
            injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
            subst payloadEquation
            subst childrenAfterEquation
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
                            rcases Step.weakHeadStep_or_cong scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerGenerator, _innerPayload, _innerChildren, innerAfter,
                                  _scrutineeEquation, ctorEquation, innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeNatRec weakHeadOnScrutinee⟩
                            · have innerGeneratorEquation : Generator.gen_natZero = innerGenerator :=
                                congrArg RawTerm.rootGenerator ctorEquation
                              subst innerGeneratorEquation
                              injection ctorEquation with
                                _innerScopeEq _innerGenEq _innerPayloadEq innerAfterEquation
                              subst innerAfterEquation
                              cases innerChildStep
                        | there _head4 emptyStep => cases emptyStep
      | @iotaListElimNil motive nilBranch consBranch =>
          -- Phase-Z spine: (motive, nil, cons, scrutinee=listNil).  A step in motive / nil /
          -- cons leaves the scrutinee a constructor, so the subject is still a listNil redex
          -- (`rootIota IotaHeadStep.iotaListElimNil`).  A step in the LAST child (scrutinee) is
          -- decided by a nested `weakHeadStep_or_cong`: a genuine wh-step lifts via
          -- `scrutineeListElim`, a cong into `listNil`'s empty spine is impossible.
          rcases Step.weakHeadStep_or_cong step with
            ⟨subjectReduct, weakHeadOnSubject⟩
            | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · have generatorEquation : Generator.gen_listElim = generator :=
              congrArg RawTerm.rootGenerator reductEquation
            subst generatorEquation
            subst subjectEquation
            injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
            subst payloadEquation
            subst childrenAfterEquation
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
                            rcases Step.weakHeadStep_or_cong scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerGenerator, _innerPayload, _innerChildren, innerAfter,
                                  _scrutineeEquation, ctorEquation, innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeListElim weakHeadOnScrutinee⟩
                            · have innerGeneratorEquation : Generator.gen_listNil = innerGenerator :=
                                congrArg RawTerm.rootGenerator ctorEquation
                              subst innerGeneratorEquation
                              injection ctorEquation with
                                _innerScopeEq _innerGenEq _innerPayloadEq innerAfterEquation
                              subst innerAfterEquation
                              cases innerChildStep
                        | there _head4 emptyStep => cases emptyStep
      | @iotaOptionMatchNone motive noneBranch someBranch =>
          -- Phase-Z spine: (motive, none, some, scrutinee=optionNone).  A step in motive / none /
          -- some leaves the scrutinee a constructor, so the subject is still an optionNone redex
          -- (`rootIota IotaHeadStep.iotaOptionMatchNone`).  A step in the LAST child (scrutinee) is
          -- decided by a nested `weakHeadStep_or_cong`: a genuine wh-step lifts via
          -- `scrutineeOptionMatch`, a cong into `optionNone`'s empty spine is impossible.
          rcases Step.weakHeadStep_or_cong step with
            ⟨subjectReduct, weakHeadOnSubject⟩
            | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · have generatorEquation : Generator.gen_optionMatch = generator :=
              congrArg RawTerm.rootGenerator reductEquation
            subst generatorEquation
            subst subjectEquation
            injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
            subst payloadEquation
            subst childrenAfterEquation
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
                            rcases Step.weakHeadStep_or_cong scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerGenerator, _innerPayload, _innerChildren, innerAfter,
                                  _scrutineeEquation, ctorEquation, innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeOptionMatch weakHeadOnScrutinee⟩
                            · have innerGeneratorEquation : Generator.gen_optionNone = innerGenerator :=
                                congrArg RawTerm.rootGenerator ctorEquation
                              subst innerGeneratorEquation
                              injection ctorEquation with
                                _innerScopeEq _innerGenEq _innerPayloadEq innerAfterEquation
                              subst innerAfterEquation
                              cases innerChildStep
                        | there _head4 emptyStep => cases emptyStep
      | @iotaOptionMatchSome motive value noneBranch someBranch =>
          -- Phase-Z spine: (motive, none, some, scrutinee=optionSome value).  A step in motive /
          -- none / some leaves the scrutinee a constructor, so the subject is still an optionSome
          -- redex (`rootIota IotaHeadStep.iotaOptionMatchSome`).  A step in the LAST child
          -- (scrutinee) is decided by a nested `weakHeadStep_or_cong`: a genuine wh-step lifts via
          -- `scrutineeOptionMatch`, a cong into an `optionSome` scrutinee leaves it a constructor.
          rcases Step.weakHeadStep_or_cong step with
            ⟨subjectReduct, weakHeadOnSubject⟩
            | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · have generatorEquation : Generator.gen_optionMatch = generator :=
              congrArg RawTerm.rootGenerator reductEquation
            subst generatorEquation
            subst subjectEquation
            injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
            subst payloadEquation
            subst childrenAfterEquation
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
                            rcases Step.weakHeadStep_or_cong scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerGenerator, innerPayload, innerChildren, _innerAfter,
                                  scrutineeEquation, ctorEquation, _innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeOptionMatch weakHeadOnScrutinee⟩
                            · have innerGeneratorEquation : Generator.gen_optionSome = innerGenerator :=
                                congrArg RawTerm.rootGenerator ctorEquation
                              subst innerGeneratorEquation
                              subst scrutineeEquation
                              match innerPayload, innerChildren with
                              | (), .childCons _innerValue .childNil =>
                                  exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaOptionMatchSome⟩
                        | there _head4 emptyStep => cases emptyStep
      | @iotaEitherMatchInl motive value leftBranch rightBranch =>
          -- Phase-Z spine: (motive, left, right, scrutinee=eitherInl value).  A step in motive /
          -- left / right leaves the scrutinee a constructor, so the subject is still an eitherInl
          -- redex (`rootIota IotaHeadStep.iotaEitherMatchInl`).  A step in the LAST child
          -- (scrutinee) is decided by a nested `weakHeadStep_or_cong`: a genuine wh-step lifts via
          -- `scrutineeEitherMatch`, a cong into an `eitherInl` scrutinee leaves it a constructor.
          rcases Step.weakHeadStep_or_cong step with
            ⟨subjectReduct, weakHeadOnSubject⟩
            | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · have generatorEquation : Generator.gen_eitherMatch = generator :=
              congrArg RawTerm.rootGenerator reductEquation
            subst generatorEquation
            subst subjectEquation
            injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
            subst payloadEquation
            subst childrenAfterEquation
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
                            rcases Step.weakHeadStep_or_cong scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerGenerator, innerPayload, innerChildren, _innerAfter,
                                  scrutineeEquation, ctorEquation, _innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeEitherMatch weakHeadOnScrutinee⟩
                            · have innerGeneratorEquation : Generator.gen_eitherInl = innerGenerator :=
                                congrArg RawTerm.rootGenerator ctorEquation
                              subst innerGeneratorEquation
                              subst scrutineeEquation
                              match innerPayload, innerChildren with
                              | (), .childCons _innerValue .childNil =>
                                  exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaEitherMatchInl⟩
                        | there _head4 emptyStep => cases emptyStep
      | @iotaEitherMatchInr motive value leftBranch rightBranch =>
          -- Phase-Z spine: (motive, left, right, scrutinee=eitherInr value).  Symmetric to
          -- `iotaEitherMatchInl`; a step in motive / left / right keeps the eitherInr redex, a
          -- scrutinee wh-step lifts via `scrutineeEitherMatch`, a cong keeps it a constructor.
          rcases Step.weakHeadStep_or_cong step with
            ⟨subjectReduct, weakHeadOnSubject⟩
            | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · have generatorEquation : Generator.gen_eitherMatch = generator :=
              congrArg RawTerm.rootGenerator reductEquation
            subst generatorEquation
            subst subjectEquation
            injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
            subst payloadEquation
            subst childrenAfterEquation
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
                            rcases Step.weakHeadStep_or_cong scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerGenerator, innerPayload, innerChildren, _innerAfter,
                                  scrutineeEquation, ctorEquation, _innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeEitherMatch weakHeadOnScrutinee⟩
                            · have innerGeneratorEquation : Generator.gen_eitherInr = innerGenerator :=
                                congrArg RawTerm.rootGenerator ctorEquation
                              subst innerGeneratorEquation
                              subst scrutineeEquation
                              match innerPayload, innerChildren with
                              | (), .childCons _innerValue .childNil =>
                                  exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaEitherMatchInr⟩
                        | there _head4 emptyStep => cases emptyStep
      | @iotaNatElimSucc motive predecessor zeroBranch succBranch =>
          -- Phase-Z spine: (motive, zero, succ, scrutinee=natSucc predecessor).  A step in motive /
          -- zero / succ leaves the scrutinee a constructor, so the subject is still a natSucc redex
          -- (`rootIota IotaHeadStep.iotaNatElimSucc`).  A step in the LAST child (scrutinee) is
          -- decided by a nested `weakHeadStep_or_cong`: a genuine wh-step lifts via
          -- `scrutineeNatElim`, a cong into a `natSucc` scrutinee leaves it a constructor.
          rcases Step.weakHeadStep_or_cong step with
            ⟨subjectReduct, weakHeadOnSubject⟩
            | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · have generatorEquation : Generator.gen_natElim = generator :=
              congrArg RawTerm.rootGenerator reductEquation
            subst generatorEquation
            subst subjectEquation
            injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
            subst payloadEquation
            subst childrenAfterEquation
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
                            rcases Step.weakHeadStep_or_cong scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerGenerator, innerPayload, innerChildren, _innerAfter,
                                  scrutineeEquation, ctorEquation, _innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeNatElim weakHeadOnScrutinee⟩
                            · have innerGeneratorEquation : Generator.gen_natSucc = innerGenerator :=
                                congrArg RawTerm.rootGenerator ctorEquation
                              subst innerGeneratorEquation
                              subst scrutineeEquation
                              match innerPayload, innerChildren with
                              | (), .childCons _innerPredecessor .childNil =>
                                  exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatElimSucc⟩
                        | there _head4 emptyStep => cases emptyStep
      | @iotaNatRecSucc motive predecessor zeroBranch succBranch =>
          rcases Step.weakHeadStep_or_cong step with
            ⟨subjectReduct, weakHeadOnSubject⟩
            | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · have generatorEquation : Generator.gen_natRec = generator :=
              congrArg RawTerm.rootGenerator reductEquation
            subst generatorEquation
            subst subjectEquation
            injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
            subst payloadEquation
            subst childrenAfterEquation
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
                            rcases Step.weakHeadStep_or_cong scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerGenerator, innerPayload, innerChildren, _innerAfter,
                                  scrutineeEquation, ctorEquation, _innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeNatRec weakHeadOnScrutinee⟩
                            · have innerGeneratorEquation : Generator.gen_natSucc = innerGenerator :=
                                congrArg RawTerm.rootGenerator ctorEquation
                              subst innerGeneratorEquation
                              subst scrutineeEquation
                              match innerPayload, innerChildren with
                              | (), .childCons _innerPredecessor .childNil =>
                                  exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaNatRecSucc⟩
                        | there _head4 emptyStep => cases emptyStep
      | @iotaListElimCons motive headVal tailVal nilBranch consBranch =>
          -- Phase-Z spine: (motive, nil, cons, scrutinee=listCons).  A step in motive / nil /
          -- cons leaves the scrutinee a constructor, so the subject is still a listCons redex
          -- (`rootIota IotaHeadStep.iotaListElimCons`).  A step in the LAST child (scrutinee) is
          -- decided by a nested `weakHeadStep_or_cong`: a genuine wh-step lifts via
          -- `scrutineeListElim`, a cong into a `listCons` scrutinee leaves it a constructor.
          rcases Step.weakHeadStep_or_cong step with
            ⟨subjectReduct, weakHeadOnSubject⟩
            | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · have generatorEquation : Generator.gen_listElim = generator :=
              congrArg RawTerm.rootGenerator reductEquation
            subst generatorEquation
            subst subjectEquation
            injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
            subst payloadEquation
            subst childrenAfterEquation
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
                            rcases Step.weakHeadStep_or_cong scrutineeStep with
                              ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                              | ⟨innerGenerator, innerPayload, innerChildren, _innerAfter,
                                  scrutineeEquation, ctorEquation, _innerChildStep⟩
                            · exact ⟨_, WeakHeadStep.scrutineeListElim weakHeadOnScrutinee⟩
                            · have innerGeneratorEquation : Generator.gen_listCons = innerGenerator :=
                                congrArg RawTerm.rootGenerator ctorEquation
                              subst innerGeneratorEquation
                              subst scrutineeEquation
                              match innerPayload, innerChildren with
                              | (), .childCons _innerHead (.childCons _innerTail .childNil) =>
                                  exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaListElimCons⟩
                        | there _head4 emptyStep => cases emptyStep
      | @iotaIdJRefl motive baseCase rawWitness =>
          -- Phase-Z spine: (motive, baseCase, witness=refl rawWitness).  A step in motive / base
          -- leaves the witness a `refl` constructor, so the subject is still an idJ-on-refl redex
          -- (`rootIota IotaHeadStep.iotaIdJRefl`).  A step in the LAST child (witness) is decided by
          -- a nested `weakHeadStep_or_cong`: a genuine wh-step lifts via `scrutineeIdJ`, a cong into
          -- `refl`'s spine leaves it a constructor.
          rcases Step.weakHeadStep_or_cong step with
            ⟨subjectReduct, weakHeadOnSubject⟩
            | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · have generatorEquation : Generator.gen_idJ = generator :=
              congrArg RawTerm.rootGenerator reductEquation
            subst generatorEquation
            subst subjectEquation
            injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
            subst payloadEquation
            subst childrenAfterEquation
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
                        rcases Step.weakHeadStep_or_cong scrutineeStep with
                          ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                          | ⟨innerGenerator, innerPayload, innerChildren, _innerAfter,
                              scrutineeEquation, ctorEquation, _innerChildStep⟩
                        · exact ⟨_, WeakHeadStep.scrutineeIdJ weakHeadOnScrutinee⟩
                        · have innerGeneratorEquation : Generator.gen_refl = innerGenerator :=
                            congrArg RawTerm.rootGenerator ctorEquation
                          subst innerGeneratorEquation
                          subst scrutineeEquation
                          match innerPayload, innerChildren with
                          | (), .childCons _innerWitness .childNil =>
                              exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaIdJRefl⟩
                    | there _head3 emptyStep => cases emptyStep
      | @iotaIdStrictRecRefl motive baseCase rawWitness =>
          -- Phase-Z spine: (motive, baseCase, witness=refl rawWitness).  Symmetric to the idJ arm.
          rcases Step.weakHeadStep_or_cong step with
            ⟨subjectReduct, weakHeadOnSubject⟩
            | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
          · exact ⟨subjectReduct, weakHeadOnSubject⟩
          · have generatorEquation : Generator.gen_idStrictRec = generator :=
              congrArg RawTerm.rootGenerator reductEquation
            subst generatorEquation
            subst subjectEquation
            injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
            subst payloadEquation
            subst childrenAfterEquation
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
                        rcases Step.weakHeadStep_or_cong scrutineeStep with
                          ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                          | ⟨innerGenerator, innerPayload, innerChildren, _innerAfter,
                              scrutineeEquation, ctorEquation, _innerChildStep⟩
                        · exact ⟨_, WeakHeadStep.scrutineeIdStrictRec weakHeadOnScrutinee⟩
                        · have innerGeneratorEquation : Generator.gen_refl = innerGenerator :=
                            congrArg RawTerm.rootGenerator ctorEquation
                          subst innerGeneratorEquation
                          subst scrutineeEquation
                          match innerPayload, innerChildren with
                          | (), .childCons _innerWitness .childNil =>
                              exact ⟨_, WeakHeadStep.rootIota IotaHeadStep.iotaIdStrictRecRefl⟩
                    | there _head3 emptyStep => cases emptyStep
  | @scrutineeBoolElim motive scrutinee scrutineeReduct thenBranch elseBranch
      _storedWeakHead inductiveHypothesis =>
      -- Phase-Z spine: (motive, then, else, scrutinee).  The WeakHeadStep reduces the LAST child.
      -- A step in motive / then / else leaves the scrutinee still reducible, so the subject still
      -- weak-head reduces there (`scrutineeBoolElim _storedWeakHead`).  A step in the scrutinee
      -- (deepest child) recurses through the induction hypothesis.
      intro subjectType step
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_boolElim = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
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
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_fst = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
        cases childStep with
        | here _rest scrutineeStep =>
            obtain ⟨_scrutineeReduct2, weakHeadOnScrutinee⟩ := inductiveHypothesis scrutineeStep
            exact ⟨_, WeakHeadStep.scrutineeFst weakHeadOnScrutinee⟩
        | there _head tailStep => cases tailStep
  | @scrutineeSnd scrutinee scrutineeReduct _storedWeakHead inductiveHypothesis =>
      intro subjectType step
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_snd = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
        cases childStep with
        | here _rest scrutineeStep =>
            obtain ⟨_scrutineeReduct2, weakHeadOnScrutinee⟩ := inductiveHypothesis scrutineeStep
            exact ⟨_, WeakHeadStep.scrutineeSnd weakHeadOnScrutinee⟩
        | there _head tailStep => cases tailStep
  | @scrutineeNatElim motive scrutinee scrutineeReduct zeroBranch succBranch
      _storedWeakHead inductiveHypothesis =>
      -- Phase-Z spine: (motive, zero, succ, scrutinee).  The WeakHeadStep reduces the LAST child.
      -- A step in motive / zero / succ leaves the scrutinee still reducible, so the subject still
      -- weak-head reduces there (`scrutineeNatElim _storedWeakHead`).  A step in the scrutinee
      -- (deepest child) recurses through the induction hypothesis.
      intro subjectType step
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_natElim = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
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
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_natRec = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
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
      -- Phase-Z spine: (motive, nil, cons, scrutinee).  The WeakHeadStep reduces the LAST child.
      -- A step in motive / nil / cons leaves the scrutinee still reducible, so the subject still
      -- weak-head reduces there (`scrutineeListElim _storedWeakHead`).  A step in the scrutinee
      -- (deepest child) recurses through the induction hypothesis.
      intro subjectType step
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_listElim = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
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
      -- Phase-Z spine: (motive, none, some, scrutinee).  The WeakHeadStep reduces the LAST child.
      -- A step in motive / none / some leaves the scrutinee still reducible, so the subject still
      -- weak-head reduces there (`scrutineeOptionMatch _storedWeakHead`).  A step in the scrutinee
      -- (deepest child) recurses through the induction hypothesis.
      intro subjectType step
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_optionMatch = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
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
      -- Phase-Z spine: (motive, left, right, scrutinee).  The WeakHeadStep reduces the LAST child.
      -- A step in motive / left / right leaves the scrutinee still reducible, so the subject still
      -- weak-head reduces there (`scrutineeEitherMatch _storedWeakHead`).  A step in the scrutinee
      -- (deepest child) recurses through the induction hypothesis.
      intro subjectType step
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_eitherMatch = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
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
      -- Phase-Z spine: (motive, baseCase, witness=scrutinee).  The WeakHeadStep reduces the LAST
      -- child.  A step in motive / base leaves the witness still reducible, so the subject still
      -- weak-head reduces there (`scrutineeIdJ _storedWeakHead`).  A step in the witness (deepest
      -- child) recurses through the induction hypothesis.
      intro subjectType step
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_idJ = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
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
      -- Phase-Z spine: (motive, baseCase, witness=scrutinee).  Symmetric to the idJ scrutinee arm.
      intro subjectType step
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_idStrictRec = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
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
      -- Pin the spine to a path-λ (via `pathBetaRowFiringDecompose`), then mirror the `beta` arm — a
      -- function-slot wh-step lifts via `pathAppCongruence`; a function-slot cong that re-forms the
      -- path-λ, or an argument-slot step, leaves a `pathBeta` redex (`pathBeta rfl`).
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
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_pathApp = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
        cases childStep with
        | here _rest functionStep =>
            rcases Step.weakHeadStep_or_cong functionStep with
              ⟨_functionWhReduct, weakHeadOnFunction⟩
              | ⟨innerGenerator, innerPayload, innerChildren, _innerAfter,
                  functionEquation, pathLamEquation, _innerChildStep⟩
            · exact ⟨_, WeakHeadStep.pathAppCongruence weakHeadOnFunction⟩
            · have innerGeneratorEquation : Generator.gen_pathLam = innerGenerator :=
                congrArg RawTerm.rootGenerator pathLamEquation
              subst innerGeneratorEquation
              subst functionEquation
              injection pathLamEquation with
                _innerScopeEq _innerGenEq innerPayloadEquation _innerChildrenEq
              subst innerPayloadEquation
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
      -- via `scrutineeQuotRec`, a scrutinee cong that re-forms `quotMk` keeps the redex.
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
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_quotRec = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
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
                    rcases Step.weakHeadStep_or_cong scrutineeStep with
                      ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                      | ⟨innerGenerator, innerPayload, innerChildren, _innerAfter,
                          scrutineeEquation, quotMkEquation, _innerChildStep⟩
                    · exact ⟨_, WeakHeadStep.scrutineeQuotRec weakHeadOnScrutinee⟩
                    · have innerGeneratorEquation : Generator.gen_quotMk = innerGenerator :=
                        congrArg RawTerm.rootGenerator quotMkEquation
                      subst innerGeneratorEquation
                      subst scrutineeEquation
                      injection quotMkEquation with
                        _innerScopeEq _innerGenEq innerPayloadEquation _innerChildrenEq
                      subst innerPayloadEquation
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
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_quotElim = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
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
                    rcases Step.weakHeadStep_or_cong scrutineeStep with
                      ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                      | ⟨innerGenerator, innerPayload, innerChildren, _innerAfter,
                          scrutineeEquation, quotMkEquation, _innerChildStep⟩
                    · exact ⟨_, WeakHeadStep.scrutineeQuotElim weakHeadOnScrutinee⟩
                    · have innerGeneratorEquation : Generator.gen_quotMk = innerGenerator :=
                        congrArg RawTerm.rootGenerator quotMkEquation
                      subst innerGeneratorEquation
                      subst scrutineeEquation
                      injection quotMkEquation with
                        _innerScopeEq _innerGenEq innerPayloadEquation _innerChildrenEq
                      subst innerPayloadEquation
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
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_truncRec = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
        cases childStep with
        | here _rest _kernelStep =>
            exact ⟨_, WeakHeadStep.truncRecIntro rfl⟩
        | there _head tailStep =>
            cases tailStep with
            | here _rest scrutineeStep =>
                rcases Step.weakHeadStep_or_cong scrutineeStep with
                  ⟨_scrutineeWhReduct, weakHeadOnScrutinee⟩
                  | ⟨innerGenerator, innerPayload, innerChildren, _innerAfter,
                      scrutineeEquation, truncIntroEquation, _innerChildStep⟩
                · exact ⟨_, WeakHeadStep.scrutineeTruncRec weakHeadOnScrutinee⟩
                · have innerGeneratorEquation : Generator.gen_truncIntro = innerGenerator :=
                    congrArg RawTerm.rootGenerator truncIntroEquation
                  subst innerGeneratorEquation
                  subst scrutineeEquation
                  injection truncIntroEquation with
                    _innerScopeEq _innerGenEq _innerPayloadEquation _innerChildrenEq
                  match innerChildren with
                  | .childCons _innerValue .childNil =>
                      exact ⟨_, WeakHeadStep.truncRecIntro rfl⟩
            | there _head2 emptyStep => cases emptyStep
  | @pathAppCongruence function functionReduct argument storedWeakHead inductiveHypothesis =>
      -- Native weak-head congruence at slot 0 of `pathApp` — twin of `appCongruence`.
      intro subjectType step
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_pathApp = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
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
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_quotRec = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
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
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_quotElim = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
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
      rcases Step.weakHeadStep_or_cong step with
        ⟨subjectReduct, weakHeadOnSubject⟩
        | ⟨generator, payload, children, childrenAfter, subjectEquation, reductEquation, childStep⟩
      · exact ⟨subjectReduct, weakHeadOnSubject⟩
      · have generatorEquation : Generator.gen_truncRec = generator :=
          congrArg RawTerm.rootGenerator reductEquation
        subst generatorEquation
        subst subjectEquation
        injection reductEquation with _scopeEquation _genEquation payloadEquation childrenAfterEquation
        subst payloadEquation
        subst childrenAfterEquation
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

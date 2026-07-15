import FX1Poly.Core.Rewriting.Reduction.Head.IotaHeadStep
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStep
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadRowCommuteEngine
import FX1Poly.Core.Rewriting.Normalize.WeakHeadStepNormalForms
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStepDeterministic
import FX1Poly.Core.Rewriting.Reduction.Head.HeadStep
import FX1Poly.Core.Rewriting.Reduction.Step.StepInversion
import FX1Poly.Core.Rewriting.RuleTables.StepOver.StepTable
import FX1Poly.Core.Rewriting.Reduction.Step.StepSubst
import FX1Poly.Core.Rewriting.Reduction.Step.StepStar
import FX1Poly.Core.Rewriting.RuleTables.Tables.TableParallelStability
import FX1Poly.Core.Rewriting.Confluence.StepStarConfluenceViaTable
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableOrthogonality

/-! # Foundation/PolyCell/Core/WeakHeadStepCommute
    — the complete weak-head reduction commutes with arbitrary single-step reduction

`HeadStepCommute2` proved the β-only weak-head step (`HeadStep`) commutes with an arbitrary `Step`.
`ReducibleType` now dispatches on the COMPLETE weak-head reduction `WeakHeadStep` (β + root-ι +
scrutinee-congruence), so conversion-invariance needs the commutation diamond for `WeakHeadStep`:

```
        WeakHeadStep         Step
  term ──────────► reduct ,  term ──────────► other
```

Either the arbitrary step contracted the very weak-head redex (`other = reduct`), or the redex SURVIVES
— `other` weak-head steps to some `otherReduct` and the two contracta re-converge by a `StepStar` chain
(`reduct ↠ otherReduct`).  The chain (not a single step) is essential: a β-redex argument or an
eliminator branch can occur MORE THAN ONCE in the contractum.  For the Phase-Z substituting succ-iota
`natElim m z s (natSucc p) ↝ s[var 0 := natElim m z s p, var 1 := p]` the predecessor `p` and the
succ-branch `s` each occur twice (once in the recursive call substituted for `var 0`, plus the singleton
slot / the substitution body), so replaying one source step replays it once per occurrence — the chain is
assembled via `RawTerm.subst_pointwise_stepStar` over the consed substitution (plus `StepStar.subst` for
the succ body).

The diamond is assembled in two lemmas:

  * `IotaHeadStep.commuteWithStep` — the root-ι half: sixteen one-line cases (one per ι rule), each
    consuming its row's subsumption pin from the table-generic row-commute engine
    (`WeakHeadRowCommuteEngine`): the row REFIRES on the stepped spine by the IOTA-T6 parallel
    firing-stability, the refire converts back to `IotaHeadStep` through the shipped
    `<row>FiringToIotaHead` inversion, and the catch-up chain is the parallel reduct's `StepStar`
    collapse.

  * `WeakHeadStep.commuteWithStep` — the full relation, by induction on the `WeakHeadStep` derivation.  β
    and `appCongruence` mirror `HeadStep.commuteWithStep` (the β-redex / function-spine cases, with
    `Step.subst0Body`/`Step.subst0Argument` replaying argument reduction across the substitution); the
    `rootIota` case delegates to `IotaHeadStep.commuteWithStep` and re-wraps with `.rootIota`; each of the
    ten `scrutineeCong` cases inverts the arbitrary step with the eliminator's `Step.from_<elim>`, refutes
    the ι disjuncts via the `WeakHeadStep.not_from_<ctor>` normal-form lemmas (a reducible scrutinee is
    not yet a constructor), applies the induction hypothesis to a scrutinee step, and lifts a branch step
    by `StepStar.congAt`.

## Zero-axiom verification

The generic lifter `StepStar.congAt` is induction on the `StepStar` chain.  `IotaHeadStep.commuteWithStep`
is `cases` on the ι rule then one subsumption pin per row (the table-generic row-commute engine, itself
zero-axiom).  `WeakHeadStep.commuteWithStep` is induction reusing the shipped `Step.from_<elim>`
inversions and `WeakHeadStep.not_from_<ctor>` refutes.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Swept per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Axis.Syntax

/-- **One-hole-context chain lift.**  Replay a `StepStar` chain inside a single-hole context, given that
the context lifts ONE `Step` through its hole.  The general substrate the eliminator-child congruences
(scrutinee / branch positions) are built from: instantiate `oneHoleContext` with the eliminator wrapped
around its stepping child and `liftStepThroughHole` with the uniform `Step.cong` at that child. -/
theorem StepStar.congAt {scope : Nat} {subjectStart subjectEnd : RawTerm scope}
    (oneHoleContext : RawTerm scope → RawTerm scope)
    (liftStepThroughHole : ∀ {filledStart filledEnd : RawTerm scope},
      Step filledStart filledEnd → Step (oneHoleContext filledStart) (oneHoleContext filledEnd))
    (innerChain : StepStar subjectStart subjectEnd) :
    StepStar (oneHoleContext subjectStart) (oneHoleContext subjectEnd) := by
  induction innerChain with
  | refl _ => exact StepStar.refl _
  | trans headStep _restChain restCongruence =>
      exact StepStar.trans (liftStepThroughHole headStep) restCongruence

/-- **The natElim/natRec succ-iota cons-substitution replays piece-wise `StepStar`.**

The Phase-Z succ-iota contractum is `subst (cons recursiveCall (singleton predecessor)) succBranch`.
When a child of the redex steps, the recursive call and/or the predecessor step, so the consed
substitution steps pointwise: this lemma assembles the `PointwiseStepStar` between the original and the
stepped consed substitution.  Composed with `RawTerm.subst_pointwise_stepStar succBranch` it yields the
contractum catch-up chain the local-confluence diamond needs.

Position 0 carries the recursive-call chain; position 1 carries the predecessor chain (through the
singleton's position-0 slot); positions `k + 2` are the unchanged shifted variables (`refl`). -/
theorem RawTermSubst.natSuccElim_cons_pointwiseStepStar {scope : Nat}
    {recursiveCall recursiveCallReduct : RawTerm scope}
    {predecessor predecessorReduct : RawTerm scope}
    (recChain : StepStar recursiveCall recursiveCallReduct)
    (predChain : StepStar predecessor predecessorReduct) :
    RawTermSubst.PointwiseStepStar
      (RawTermSubst.cons recursiveCall (RawTermSubst.singleton predecessor))
      (RawTermSubst.cons recursiveCallReduct (RawTermSubst.singleton predecessorReduct)) := by
  intro position
  match position with
  | ⟨0, _⟩ => exact recChain
  | ⟨1, _⟩ => exact predChain
  | ⟨_priorValue + 2, _⟩ => exact StepStar.refl _

/-- **Root-iota reduction commutes with arbitrary single-step reduction.**  Given a root-ι step
`term ↝ᵢ reduct` and any step `term ↝ other`, either the arbitrary step contracted the same ι redex
(`other = reduct`), or the redex survives — `other` ι-reduces to some `otherReduct` and `reduct` catches
up by a `StepStar` chain (`reduct ↠ otherReduct`).  Sixteen one-line arms, each consuming its row's
subsumption pin from the table-generic row-commute engine
(`WeakHeadRowCommuteEngine.rowFiringCommuteWithStepToIotaHead`). -/
theorem IotaHeadStep.commuteWithStep {scope : Nat} {term reduct : RawTerm scope}
    (iotaStep : IotaHeadStep term reduct) :
    ∀ (other : RawTerm scope), Step term other →
      other = reduct ∨
        ∃ otherReduct : RawTerm scope, IotaHeadStep other otherReduct ∧ StepStar reduct otherReduct := by
  cases iotaStep with
  | iotaBoolTrue => exact fun _other step => boolTrueRedexCommuteWithStep step
  | iotaBoolFalse => exact fun _other step => boolFalseRedexCommuteWithStep step
  | iotaFstPair => exact fun _other step => fstPairRedexCommuteWithStep step
  | iotaSndPair => exact fun _other step => sndPairRedexCommuteWithStep step
  | iotaNatElimZero => exact fun _other step => natElimZeroRedexCommuteWithStep step
  | iotaNatRecZero => exact fun _other step => natRecZeroRedexCommuteWithStep step
  | iotaListElimNil => exact fun _other step => listElimNilRedexCommuteWithStep step
  | iotaOptionMatchNone => exact fun _other step => optionMatchNoneRedexCommuteWithStep step
  | iotaOptionMatchSome => exact fun _other step => optionMatchSomeRedexCommuteWithStep step
  | iotaEitherMatchInl => exact fun _other step => eitherMatchInlRedexCommuteWithStep step
  | iotaEitherMatchInr => exact fun _other step => eitherMatchInrRedexCommuteWithStep step
  | iotaNatElimSucc => exact fun _other step => natElimSuccRedexCommuteWithStep step
  | iotaNatRecSucc => exact fun _other step => natRecSuccRedexCommuteWithStep step
  | iotaListElimCons => exact fun _other step => listElimConsRedexCommuteWithStep step
  | iotaIdJRefl => exact fun _other step => idJReflRedexCommuteWithStep step
  | iotaIdStrictRecRefl => exact fun _other step => idStrictRecReflRedexCommuteWithStep step

/-- **A table-native row firing commutes with arbitrary single-step reduction.**  The four table-native
weak-head rows (endpoint-β, the two quotient eliminators, the truncation recursor) carry their reduct as a
firing equation rather than a structured constructor, so their commutation is the row-commute keystone
(`rowFiringCommuteWithStepRefire`) with the survive branch's refire equation converted to a weak-head step
by the 21-arm row dispatch `canonicalRootFiringToWeakHeadStep`. -/
theorem nativeRowCommuteWithStep {scope : Nat} {rule : IotaRuleDesc}
    (isRow : rule ∈ iotaRuleTable)
    {elimPayload : rule.elimGenerator.payload scope}
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct)
    {other : RawTerm scope}
    (step : Step (.mkGen rule.elimGenerator elimPayload spine) other) :
    other = reduct ∨ ∃ otherReduct : RawTerm scope,
      WeakHeadStep other otherReduct ∧ StepStar reduct otherReduct := by
  rcases rowFiringCommuteWithStepRefire isRow step fires with
    otherIsReduct | ⟨spineAfter, refireReduct, otherShape, refires, catchUpChain⟩
  · exact Or.inl otherIsReduct
  · subst otherShape
    exact Or.inr ⟨refireReduct,
      canonicalRootFiringToWeakHeadStep isRow elimPayload refires, catchUpChain⟩

/-- **The complete weak-head reduction commutes with arbitrary single-step reduction.**  Given a weak-head
step `term ↝ʰ reduct` and any step `term ↝ other`, either the arbitrary step contracted the same weak-head
redex (`other = reduct`), or the redex survives — `other` weak-head steps to some `otherReduct` and
`reduct` catches up by a `StepStar` chain.  Induction on the `WeakHeadStep` derivation: `beta`/
`appCongruence` mirror `HeadStep.commuteWithStep` (β-redex argument/body substitution replays via
`Step.subst0Body`/`Step.subst0Argument`); `rootIota` delegates to `IotaHeadStep.commuteWithStep`; each
`scrutineeCong` case inverts by the eliminator's `Step.from_<elim>`, refutes the ι disjuncts via the
`WeakHeadStep.not_from_<ctor>` normal-form lemmas (a reducible scrutinee is not yet a constructor), recurses
on a scrutinee step, and lifts a branch step by `StepStar.congAt`. -/
theorem WeakHeadStep.commuteWithStep {scope : Nat} {term reduct : RawTerm scope}
    (weakHeadStep : WeakHeadStep term reduct) :
    ∀ (other : RawTerm scope), Step term other →
      other = reduct ∨
        ∃ otherReduct : RawTerm scope, WeakHeadStep other otherReduct ∧ StepStar reduct otherReduct := by
  induction weakHeadStep with
  | @beta domainAnn body argument =>
      intro other step
      cases Step.weakHeadOrChildCong step with
      | inl innerWeakHeadStep =>
          cases innerWeakHeadStep with
          | beta => exact Or.inl rfl
          | appCongruence functionStep =>
              exact absurd functionStep WeakHeadStep.not_from_lam
          | rootIota iotaHead => cases iotaHead
      | inr congShape =>
          obtain ⟨childrenAfter, targetEq, childStep⟩ := congShape
          subst targetEq
          cases childStep with
          | here _rest functionStep =>
              rcases Step.from_lam functionStep with
                ⟨domainAfter, functionEquation, _domainStep⟩ |
                ⟨bodyAfter, functionEquation, bodyStep⟩
              · subst functionEquation
                exact Or.inr ⟨_, WeakHeadStep.beta, StepStar.refl _⟩
              · subst functionEquation
                exact Or.inr ⟨_, WeakHeadStep.beta, Step.subst0Body argument bodyStep⟩
          | there _head tailStep =>
              cases tailStep with
              | here _rest argumentStep =>
                  exact Or.inr ⟨_, WeakHeadStep.beta, Step.subst0Argument body argumentStep⟩
              | there _head2 emptyStep => cases emptyStep
  | @appCongruence function functionReduct argument functionWeakHeadStep functionInductiveHypothesis =>
      intro other step
      rcases Step.from_app step with
        ⟨_betaDomainAnn, betaBody, functionEquation, _targetEquation⟩
        | ⟨functionAfter, targetEquation, functionStep⟩
        | ⟨argumentAfter, targetEquation, argumentStep⟩
      · rw [functionEquation] at functionWeakHeadStep
        exact absurd functionWeakHeadStep WeakHeadStep.not_from_lam
      · subst targetEquation
        rcases functionInductiveHypothesis _ functionStep with
          functionAfterEquation | ⟨functionReduct2, weakHeadStep2, starChain⟩
        · subst functionAfterEquation
          exact Or.inl rfl
        · exact Or.inr
            ⟨_, WeakHeadStep.appCongruence weakHeadStep2, StepStar.appFunction starChain⟩
      · subst targetEquation
        exact Or.inr
          ⟨_, WeakHeadStep.appCongruence functionWeakHeadStep,
            StepStar.appArgument functionReduct (StepStar.single argumentStep)⟩
  | @rootIota _innerTerm _innerReduct iotaStep =>
      intro other step
      rcases iotaStep.commuteWithStep other step with equation | ⟨otherReduct, iotaOther, starChain⟩
      · exact Or.inl equation
      · exact Or.inr ⟨otherReduct, WeakHeadStep.rootIota iotaOther, starChain⟩
  | @scrutineeBoolElim motive scrutinee scrutineeReduct thenBranch elseBranch
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      -- Phase-Z spine: (motive, then, else, scrutinee).  The WeakHeadStep reduces the LAST
      -- child (scrutinee).  `Step.from_boolElim` is a six-way disjunction in the order
      -- iotaTrue / iotaFalse / cong-motive / cong-then / cong-else / cong-scrutinee.  The two
      -- iota disjuncts are refuted (a reducible scrutinee is not yet a constructor); motive,
      -- then, and else steps leave the scrutinee reducible, so `other` still weak-head reduces
      -- there and `reduct` catches up by a single congruence at the stepped child; a scrutinee
      -- step recurses through the induction hypothesis.
      intro other step
      rcases Step.from_boolElim step with
        ⟨scrutEq, _⟩ | ⟨scrutEq, _⟩
        | ⟨_motiveAfter, otherEq, motiveStep⟩
        | ⟨_thenAfter, otherEq, thenStep⟩
        | ⟨_elseAfter, otherEq, elseStep⟩
        | ⟨_scrutAfter, otherEq, scrutStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_boolTrue
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_boolFalse
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeBoolElim scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_boolElim () (.here _ motiveStep))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeBoolElim scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_boolElim () (.there _ (.here _ thenStep)))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeBoolElim scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_boolElim () (.there _ (.there _ (.here _ elseStep))))⟩
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ scrutStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeBoolElim weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_boolElim ()
                (.childCons motive
                  (.childCons thenBranch (.childCons elseBranch (.childCons hole .childNil)))))
              (fun childStep' =>
                Step.cong .gen_boolElim ()
                  (.there _ (.there _ (.there _ (.here _ childStep'))))) starChain⟩
  | @scrutineeFst scrutinee scrutineeReduct scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      intro other step
      rcases Step.from_fst step with
        ⟨_firstValue, _secondValue, scrutEq, _⟩ | ⟨_scrutAfter, otherEq, scrutStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_pair
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ scrutStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeFst weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_fst () (.childCons hole .childNil))
              (fun childStep' => Step.cong .gen_fst () (.here _ childStep')) starChain⟩
  | @scrutineeSnd scrutinee scrutineeReduct scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      intro other step
      rcases Step.from_snd step with
        ⟨_firstValue, _secondValue, scrutEq, _⟩ | ⟨_scrutAfter, otherEq, scrutStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_pair
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ scrutStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeSnd weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_snd () (.childCons hole .childNil))
              (fun childStep' => Step.cong .gen_snd () (.here _ childStep')) starChain⟩
  | @scrutineeNatElim motive scrutinee scrutineeReduct zeroBranch succBranch
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      -- Phase-Z spine: (motive, zero, succ, scrutinee).  The WeakHeadStep reduces the LAST
      -- child (scrutinee).  `Step.from_natElim` is a six-way disjunction in the order
      -- iotaZero / iotaSucc / cong-motive / cong-zero / cong-succ / cong-scrutinee.  The two
      -- iota disjuncts are refuted (a reducible scrutinee is not yet a constructor); motive,
      -- zero, and succ steps leave the scrutinee reducible, so `other` still weak-head reduces
      -- there and `reduct` catches up by a single congruence at the stepped child (the succ
      -- branch lives at scope + 2); a scrutinee step recurses through the induction hypothesis.
      intro other step
      rcases Step.from_natElim step with
        ⟨scrutEq, _⟩ | ⟨_pred, scrutEq, _⟩
        | ⟨_motiveAfter, otherEq, motiveStep⟩
        | ⟨_zeroAfter, otherEq, zeroStep⟩
        | ⟨_succAfter, otherEq, succStep⟩
        | ⟨_scrutAfter, otherEq, scrutStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_natZero
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_natSucc
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeNatElim scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_natElim () (.here _ motiveStep))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeNatElim scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_natElim () (.there _ (.here _ zeroStep)))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeNatElim scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_natElim () (.there _ (.there _ (.here _ succStep))))⟩
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ scrutStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeNatElim weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_natElim ()
                (.childCons motive
                  (.childCons zeroBranch (.childCons succBranch (.childCons hole .childNil)))))
              (fun childStep' =>
                Step.cong .gen_natElim ()
                  (.there _ (.there _ (.there _ (.here _ childStep'))))) starChain⟩
  | @scrutineeNatRec motive scrutinee scrutineeReduct zeroBranch succBranch
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      intro other step
      rcases Step.from_natRec step with
        ⟨scrutEq, _⟩ | ⟨_pred, scrutEq, _⟩
        | ⟨_motiveAfter, otherEq, motiveStep⟩
        | ⟨_zeroAfter, otherEq, zeroStep⟩
        | ⟨_succAfter, otherEq, succStep⟩
        | ⟨_scrutAfter, otherEq, scrutStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_natZero
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_natSucc
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeNatRec scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_natRec () (.here _ motiveStep))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeNatRec scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_natRec () (.there _ (.here _ zeroStep)))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeNatRec scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_natRec () (.there _ (.there _ (.here _ succStep))))⟩
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ scrutStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeNatRec weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_natRec ()
                (.childCons motive
                  (.childCons zeroBranch (.childCons succBranch (.childCons hole .childNil)))))
              (fun childStep' =>
                Step.cong .gen_natRec ()
                  (.there _ (.there _ (.there _ (.here _ childStep'))))) starChain⟩
  | @scrutineeListElim motive scrutinee scrutineeReduct nilBranch consBranch
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      -- Phase-Z spine: (motive, nil, cons, scrutinee).  The WeakHeadStep reduces the LAST
      -- child (scrutinee).  `Step.from_listElim` is a six-way disjunction in the order
      -- iotaNil / iotaCons / cong-motive / cong-nil / cong-cons / cong-scrutinee.  The two
      -- iota disjuncts are refuted (a reducible scrutinee is not yet a constructor); motive,
      -- nil, and cons steps leave the scrutinee reducible, so `other` still weak-head reduces
      -- there and `reduct` catches up by a single congruence at the stepped child; a scrutinee
      -- step recurses through the induction hypothesis.
      intro other step
      rcases Step.from_listElim step with
        ⟨scrutEq, _⟩ | ⟨_headVal, _tailVal, scrutEq, _⟩
        | ⟨_motiveAfter, otherEq, motiveStep⟩
        | ⟨_nilAfter, otherEq, nilStep⟩
        | ⟨_consAfter, otherEq, consStep⟩
        | ⟨_scrutAfter, otherEq, scrutStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_listNil
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_listCons
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeListElim scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_listElim () (.here _ motiveStep))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeListElim scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_listElim () (.there _ (.here _ nilStep)))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeListElim scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_listElim () (.there _ (.there _ (.here _ consStep))))⟩
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ scrutStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeListElim weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_listElim ()
                (.childCons motive
                  (.childCons nilBranch (.childCons consBranch (.childCons hole .childNil)))))
              (fun childStep' =>
                Step.cong .gen_listElim ()
                  (.there _ (.there _ (.there _ (.here _ childStep'))))) starChain⟩
  | @scrutineeOptionMatch motive scrutinee scrutineeReduct noneBranch someBranch
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      -- Phase-Z spine: (motive, none, some, scrutinee).  The WeakHeadStep reduces the LAST
      -- child (scrutinee).  `Step.from_optionMatch` is a six-way disjunction in the order
      -- iotaNone / iotaSome / cong-motive / cong-none / cong-some / cong-scrutinee.  The two
      -- iota disjuncts are refuted (a reducible scrutinee is not yet a constructor); motive,
      -- none, and some steps leave the scrutinee reducible, so `other` still weak-head reduces
      -- there and `reduct` catches up by a single congruence at the stepped child; a scrutinee
      -- step recurses through the induction hypothesis.
      intro other step
      rcases Step.from_optionMatch step with
        ⟨scrutEq, _⟩ | ⟨_value, scrutEq, _⟩
        | ⟨_motiveAfter, otherEq, motiveStep⟩
        | ⟨_noneAfter, otherEq, noneStep⟩
        | ⟨_someAfter, otherEq, someStep⟩
        | ⟨_scrutAfter, otherEq, scrutStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_optionNone
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_optionSome
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeOptionMatch scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_optionMatch () (.here _ motiveStep))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeOptionMatch scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_optionMatch () (.there _ (.here _ noneStep)))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeOptionMatch scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_optionMatch () (.there _ (.there _ (.here _ someStep))))⟩
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ scrutStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeOptionMatch weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_optionMatch ()
                (.childCons motive
                  (.childCons noneBranch (.childCons someBranch (.childCons hole .childNil)))))
              (fun childStep' =>
                Step.cong .gen_optionMatch ()
                  (.there _ (.there _ (.there _ (.here _ childStep'))))) starChain⟩
  | @scrutineeEitherMatch motive scrutinee scrutineeReduct leftBranch rightBranch
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      -- Phase-Z spine: (motive, left, right, scrutinee).  The WeakHeadStep reduces the LAST
      -- child (scrutinee).  `Step.from_eitherMatch` is a six-way disjunction in the order
      -- iotaInl / iotaInr / cong-motive / cong-left / cong-right / cong-scrutinee.  The two
      -- iota disjuncts are refuted (a reducible scrutinee is not yet a constructor); motive,
      -- left, and right steps leave the scrutinee reducible, so `other` still weak-head reduces
      -- there and `reduct` catches up by a single congruence at the stepped child; a scrutinee
      -- step recurses through the induction hypothesis.
      intro other step
      rcases Step.from_eitherMatch step with
        ⟨_value, scrutEq, _⟩ | ⟨_value, scrutEq, _⟩
        | ⟨_motiveAfter, otherEq, motiveStep⟩
        | ⟨_leftAfter, otherEq, leftStep⟩
        | ⟨_rightAfter, otherEq, rightStep⟩
        | ⟨_scrutAfter, otherEq, scrutStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_eitherInl
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_eitherInr
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeEitherMatch scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_eitherMatch () (.here _ motiveStep))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeEitherMatch scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_eitherMatch () (.there _ (.here _ leftStep)))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeEitherMatch scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_eitherMatch () (.there _ (.there _ (.here _ rightStep))))⟩
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ scrutStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeEitherMatch weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_eitherMatch ()
                (.childCons motive
                  (.childCons leftBranch (.childCons rightBranch (.childCons hole .childNil)))))
              (fun childStep' =>
                Step.cong .gen_eitherMatch ()
                  (.there _ (.there _ (.there _ (.here _ childStep'))))) starChain⟩
  | @scrutineeIdJ motive baseCase scrutinee scrutineeReduct
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      -- Phase-Z spine: (motive, baseCase, witness=scrutinee).  The WeakHeadStep reduces the LAST
      -- child (the witness scrutinee).  `Step.from_idJ` is a four-way disjunction in the order
      -- iotaRefl / cong-motive / cong-base / cong-witness.  The iota disjunct is refuted (a
      -- reducible witness is not yet `refl`); motive and base steps leave the witness reducible,
      -- so `other` still weak-head reduces there and `reduct` catches up by a single congruence at
      -- the stepped child; a witness step recurses through the induction hypothesis.
      intro other step
      rcases Step.from_idJ step with
        ⟨_rawWitness, scrutEq, _⟩
        | ⟨_motiveAfter, otherEq, motiveStep⟩
        | ⟨_baseAfter, otherEq, baseStep⟩
        | ⟨_witnessAfter, otherEq, witnessStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_refl
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeIdJ scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_idJ () (.here _ motiveStep))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeIdJ scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_idJ () (.there _ (.here _ baseStep)))⟩
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ witnessStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeIdJ weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_idJ ()
                (.childCons motive (.childCons baseCase (.childCons hole .childNil))))
              (fun childStep' =>
                Step.cong .gen_idJ () (.there _ (.there _ (.here _ childStep')))) starChain⟩
  | @scrutineeIdStrictRec motive baseCase scrutinee scrutineeReduct
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      -- Phase-Z spine: (motive, baseCase, witness=scrutinee).  Symmetric to the idJ scrutinee
      -- arm; `Step.from_idStrictRec` is the same four-way disjunction.
      intro other step
      rcases Step.from_idStrictRec step with
        ⟨_rawWitness, scrutEq, _⟩
        | ⟨_motiveAfter, otherEq, motiveStep⟩
        | ⟨_baseAfter, otherEq, baseStep⟩
        | ⟨_witnessAfter, otherEq, witnessStep⟩
      · rw [scrutEq] at scrutineeWeakHeadStep
        exact absurd scrutineeWeakHeadStep WeakHeadStep.not_from_refl
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeIdStrictRec scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_idStrictRec () (.here _ motiveStep))⟩
      · subst otherEq
        exact Or.inr ⟨_, WeakHeadStep.scrutineeIdStrictRec scrutineeWeakHeadStep,
          StepStar.single
            (Step.cong .gen_idStrictRec () (.there _ (.here _ baseStep)))⟩
      · subst otherEq
        rcases scrutineeInductiveHypothesis _ witnessStep with
          scrutAfterEquation | ⟨_scrutReduct2, weakHeadStep2, starChain⟩
        · subst scrutAfterEquation; exact Or.inl rfl
        · exact Or.inr ⟨_, WeakHeadStep.scrutineeIdStrictRec weakHeadStep2,
            StepStar.congAt
              (fun hole => .mkGen .gen_idStrictRec ()
                (.childCons motive (.childCons baseCase (.childCons hole .childNil))))
              (fun childStep' =>
                Step.cong .gen_idStrictRec () (.there _ (.there _ (.here _ childStep')))) starChain⟩
  | @pathBeta spine _reduct fires =>
      intro other step
      exact nativeRowCommuteWithStep pathBetaIotaRow_memTable fires step
  | @quotRecMk spine _reduct fires =>
      intro other step
      exact nativeRowCommuteWithStep quotRecMkIotaRow_memTable fires step
  | @quotElimMk spine _reduct fires =>
      intro other step
      exact nativeRowCommuteWithStep quotElimMkIotaRow_memTable fires step
  | @truncRecIntro truncationLevel spine _reduct fires =>
      intro other step
      exact nativeRowCommuteWithStep truncRecIntroIotaRow_memTable fires step
  | @pathAppCongruence function functionReduct argument functionWeakHeadStep
      functionInductiveHypothesis =>
      intro other step
      cases Step.weakHeadOrChildCong step with
      | inl innerWeakHeadStep =>
          cases innerWeakHeadStep with
          | pathBeta fires => exact (pathBetaFunctionNoStep fires functionWeakHeadStep).elim
          | pathAppCongruence functionStep2 =>
              rw [WeakHeadStep.deterministic functionWeakHeadStep functionStep2]
              exact Or.inl rfl
          | rootIota iotaHead => cases iotaHead
      | inr congShape =>
          obtain ⟨childrenAfter, targetEq, childStep⟩ := congShape
          subst targetEq
          cases childStep with
          | here _rest functionStep =>
              rcases functionInductiveHypothesis _ functionStep with
                functionAfterEquation | ⟨_functionReduct2, weakHeadStep2, starChain⟩
              · subst functionAfterEquation; exact Or.inl rfl
              · exact Or.inr ⟨_, WeakHeadStep.pathAppCongruence weakHeadStep2,
                  StepStar.congAt
                    (fun hole => .mkGen .gen_pathApp ()
                      (.childCons hole (.childCons argument .childNil)))
                    (fun childStep' => Step.cong .gen_pathApp () (.here _ childStep')) starChain⟩
          | there _head tailStep =>
              cases tailStep with
              | here _rest argumentStep =>
                  exact Or.inr ⟨_, WeakHeadStep.pathAppCongruence functionWeakHeadStep,
                    StepStar.single
                      (Step.cong .gen_pathApp () (.there _ (.here _ argumentStep)))⟩
              | there _head2 emptyStep => cases emptyStep
  | @scrutineeQuotRec kernelFn respectsRel scrutinee scrutineeReduct
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      intro other step
      cases Step.weakHeadOrChildCong step with
      | inl innerWeakHeadStep =>
          cases innerWeakHeadStep with
          | quotRecMk fires => exact (quotRecScrutineeNoStep fires scrutineeWeakHeadStep).elim
          | scrutineeQuotRec scrutineeStep2 =>
              rw [WeakHeadStep.deterministic scrutineeWeakHeadStep scrutineeStep2]
              exact Or.inl rfl
          | rootIota iotaHead => cases iotaHead
      | inr congShape =>
          obtain ⟨childrenAfter, targetEq, childStep⟩ := congShape
          subst targetEq
          cases childStep with
          | here _rest kernelFnStep =>
              exact Or.inr ⟨_, WeakHeadStep.scrutineeQuotRec scrutineeWeakHeadStep,
                StepStar.single (Step.cong .gen_quotRec () (.here _ kernelFnStep))⟩
          | there _head tailStep =>
              cases tailStep with
              | here _rest respectsRelStep =>
                  exact Or.inr ⟨_, WeakHeadStep.scrutineeQuotRec scrutineeWeakHeadStep,
                    StepStar.single
                      (Step.cong .gen_quotRec () (.there _ (.here _ respectsRelStep)))⟩
              | there _head2 tailStep2 =>
                  cases tailStep2 with
                  | here _rest scrutineeStep =>
                      rcases scrutineeInductiveHypothesis _ scrutineeStep with
                        scrutineeAfterEquation | ⟨_scrutineeReduct2, weakHeadStep2, starChain⟩
                      · subst scrutineeAfterEquation; exact Or.inl rfl
                      · exact Or.inr ⟨_, WeakHeadStep.scrutineeQuotRec weakHeadStep2,
                          StepStar.congAt
                            (fun hole => .mkGen .gen_quotRec ()
                              (.childCons kernelFn
                                (.childCons respectsRel (.childCons hole .childNil))))
                            (fun childStep' =>
                              Step.cong .gen_quotRec ()
                                (.there _ (.there _ (.here _ childStep')))) starChain⟩
                  | there _head3 emptyStep => cases emptyStep
  | @scrutineeQuotElim depMotive depKernel scrutinee scrutineeReduct
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      intro other step
      cases Step.weakHeadOrChildCong step with
      | inl innerWeakHeadStep =>
          cases innerWeakHeadStep with
          | quotElimMk fires => exact (quotElimScrutineeNoStep fires scrutineeWeakHeadStep).elim
          | scrutineeQuotElim scrutineeStep2 =>
              rw [WeakHeadStep.deterministic scrutineeWeakHeadStep scrutineeStep2]
              exact Or.inl rfl
          | rootIota iotaHead => cases iotaHead
      | inr congShape =>
          obtain ⟨childrenAfter, targetEq, childStep⟩ := congShape
          subst targetEq
          cases childStep with
          | here _rest depMotiveStep =>
              exact Or.inr ⟨_, WeakHeadStep.scrutineeQuotElim scrutineeWeakHeadStep,
                StepStar.single (Step.cong .gen_quotElim () (.here _ depMotiveStep))⟩
          | there _head tailStep =>
              cases tailStep with
              | here _rest depKernelStep =>
                  exact Or.inr ⟨_, WeakHeadStep.scrutineeQuotElim scrutineeWeakHeadStep,
                    StepStar.single
                      (Step.cong .gen_quotElim () (.there _ (.here _ depKernelStep)))⟩
              | there _head2 tailStep2 =>
                  cases tailStep2 with
                  | here _rest scrutineeStep =>
                      rcases scrutineeInductiveHypothesis _ scrutineeStep with
                        scrutineeAfterEquation | ⟨_scrutineeReduct2, weakHeadStep2, starChain⟩
                      · subst scrutineeAfterEquation; exact Or.inl rfl
                      · exact Or.inr ⟨_, WeakHeadStep.scrutineeQuotElim weakHeadStep2,
                          StepStar.congAt
                            (fun hole => .mkGen .gen_quotElim ()
                              (.childCons depMotive
                                (.childCons depKernel (.childCons hole .childNil))))
                            (fun childStep' =>
                              Step.cong .gen_quotElim ()
                                (.there _ (.there _ (.here _ childStep')))) starChain⟩
                  | there _head3 emptyStep => cases emptyStep
  | @scrutineeTruncRec truncationLevel kernelFn scrutinee scrutineeReduct
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      intro other step
      cases Step.weakHeadOrChildCong step with
      | inl innerWeakHeadStep =>
          cases innerWeakHeadStep with
          | truncRecIntro fires => exact (truncRecScrutineeNoStep fires scrutineeWeakHeadStep).elim
          | scrutineeTruncRec scrutineeStep2 =>
              rw [WeakHeadStep.deterministic scrutineeWeakHeadStep scrutineeStep2]
              exact Or.inl rfl
          | rootIota iotaHead => cases iotaHead
      | inr congShape =>
          obtain ⟨childrenAfter, targetEq, childStep⟩ := congShape
          subst targetEq
          cases childStep with
          | here _rest kernelFnStep =>
              exact Or.inr ⟨_, WeakHeadStep.scrutineeTruncRec scrutineeWeakHeadStep,
                StepStar.single (Step.cong .gen_truncRec truncationLevel (.here _ kernelFnStep))⟩
          | there _head tailStep =>
              cases tailStep with
              | here _rest scrutineeStep =>
                  rcases scrutineeInductiveHypothesis _ scrutineeStep with
                    scrutineeAfterEquation | ⟨_scrutineeReduct2, weakHeadStep2, starChain⟩
                  · subst scrutineeAfterEquation; exact Or.inl rfl
                  · exact Or.inr ⟨_, WeakHeadStep.scrutineeTruncRec weakHeadStep2,
                      StepStar.congAt
                        (fun hole => .mkGen .gen_truncRec truncationLevel
                          (.childCons kernelFn (.childCons hole .childNil)))
                        (fun childStep' =>
                          Step.cong .gen_truncRec truncationLevel
                            (.there _ (.here _ childStep'))) starChain⟩
              | there _head2 emptyStep => cases emptyStep
  | @gelBeta spine _reduct fires =>
      intro other step
      exact nativeRowCommuteWithStep gelBetaIotaRow_memTable fires step
  | @scrutineeUngel scrutinee scrutineeReduct
      scrutineeWeakHeadStep scrutineeInductiveHypothesis =>
      intro other step
      cases Step.weakHeadOrChildCong step with
      | inl innerWeakHeadStep =>
          cases innerWeakHeadStep with
          | gelBeta fires => exact (gelBetaScrutineeNoStep fires scrutineeWeakHeadStep).elim
          | scrutineeUngel scrutineeStep2 =>
              rw [WeakHeadStep.deterministic scrutineeWeakHeadStep scrutineeStep2]
              exact Or.inl rfl
          | rootIota iotaHead => cases iotaHead
      | inr congShape =>
          obtain ⟨childrenAfter, targetEq, childStep⟩ := congShape
          subst targetEq
          cases childStep with
          | here _rest scrutineeStep =>
              rcases scrutineeInductiveHypothesis _ scrutineeStep with
                scrutineeAfterEquation | ⟨_scrutineeReduct2, weakHeadStep2, starChain⟩
              · subst scrutineeAfterEquation; exact Or.inl rfl
              · exact Or.inr ⟨_, WeakHeadStep.scrutineeUngel weakHeadStep2,
                  StepStar.congAt
                    (fun hole => .mkGen .gen_ungel () (.childCons hole .childNil))
                    (fun childStep' => Step.cong .gen_ungel () (.here _ childStep')) starChain⟩
          | there _head emptyStep => cases emptyStep

/-- **★ Weak-head postponement along a whole reduction (standardization-lite).**  A single weak-head step
`startTerm ↝ʰ weakHeadReduct` commutes past an ENTIRE `StepStar` chain `startTerm ↝* target`: either the
weak-head reduct catches up to `target` (`StepStar weakHeadReduct target`), or `target` still exposes a
weak-head redex `target ↝ʰ targetReduct` that the reduct catches (`StepStar weakHeadReduct targetReduct`).
Front-peeling induction on the chain (`StepStar` is left-extension), discharging each step by the local
commutation `WeakHeadStep.commuteWithStep` and threading the catch-up by `StepStar.trans_compose`.  This is
the building block for "the weak-head reduct reaches every weak-head-normal target" — the residue-transport
lemma the carrier-aware bridge candidate's head-expansion closure consumes. -/
theorem weakHeadStepCommutesAlongStepStar {scope : Nat} {startTerm target : RawTerm scope}
    (startToTarget : StepStar startTerm target) :
    ∀ weakHeadReduct : RawTerm scope, WeakHeadStep startTerm weakHeadReduct →
      StepStar weakHeadReduct target ∨
        ∃ targetReduct : RawTerm scope,
          WeakHeadStep target targetReduct ∧ StepStar weakHeadReduct targetReduct := by
  induction startToTarget with
  | refl term =>
      intro weakHeadReduct weakHeadStep
      exact Or.inr ⟨weakHeadReduct, weakHeadStep, StepStar.refl weakHeadReduct⟩
  | trans firstStep restChain restInductiveHypothesis =>
      intro weakHeadReduct weakHeadStep
      cases weakHeadStep.commuteWithStep _ firstStep with
      | inl intermediateEqWeakHeadReduct =>
          subst intermediateEqWeakHeadReduct
          exact Or.inl restChain
      | inr survives =>
          obtain ⟨intermediateReduct, intermediateWeakHead, weakHeadReductToIntermediate⟩ := survives
          cases restInductiveHypothesis intermediateReduct intermediateWeakHead with
          | inl intermediateReductToTarget =>
              exact Or.inl
                (StepStar.trans_compose weakHeadReductToIntermediate intermediateReductToTarget)
          | inr targetSurvives =>
              obtain ⟨targetReduct, targetWeakHead, intermediateReductToTargetReduct⟩ := targetSurvives
              exact Or.inr ⟨targetReduct, targetWeakHead,
                StepStar.trans_compose weakHeadReductToIntermediate intermediateReductToTargetReduct⟩

/-- **★ The weak-head reduct reaches every weak-head-NORMAL target.**  When the chain's endpoint `target`
heads no weak-head redex (`targetWeakHeadNormal` — e.g. a constructor value like `pathLamValueCell body`),
the residual `∃` disjunct of `weakHeadStepCommutesAlongStepStar` is impossible, so the weak-head reduct
reaches the EXACT `target`.  This closes the body-reduction gap in the bridge candidate's head-expansion:
the endpoint-β contractum reaches precisely the `pathLam body` the redex reaches, so the residue transports
to the literal body with no reformulation. -/
theorem weakHeadReductReachesWeakHeadNormalForm {scope : Nat}
    {startTerm weakHeadReduct target : RawTerm scope}
    (weakHeadStep : WeakHeadStep startTerm weakHeadReduct)
    (startToTarget : StepStar startTerm target)
    (targetWeakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep target reduct) :
    StepStar weakHeadReduct target := by
  cases weakHeadStepCommutesAlongStepStar startToTarget weakHeadReduct weakHeadStep with
  | inl reduces => exact reduces
  | inr survives =>
      obtain ⟨targetReduct, targetWeakHead, _⟩ := survives
      exact absurd targetWeakHead (targetWeakHeadNormal targetReduct)

end FX1Poly.Core

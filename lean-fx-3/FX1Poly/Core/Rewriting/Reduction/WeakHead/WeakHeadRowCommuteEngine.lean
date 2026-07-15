import FX1Poly.Core.Rewriting.Reduction.Head.IotaHeadStep
import FX1Poly.Core.Rewriting.Reduction.WeakHead.WeakHeadStepDeterministic
import FX1Poly.Core.Rewriting.RuleTables.StepOver.StepTable
import FX1Poly.Core.Rewriting.Reduction.Step.StepStar
import FX1Poly.Core.Rewriting.RuleTables.Tables.TableParallelStability
import FX1Poly.Core.Rewriting.Confluence.StepStarConfluenceViaTable
import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaTableOrthogonality

/-! # Foundation/PolyCell/Core/WeakHeadRowCommuteEngine
    — ONE table-generic commute engine for every canonical-row root firing

Every per-row "root redex commutes with an arbitrary `Step`" argument in the repo used to be a bespoke
proof pile: invert the arbitrary step by hand, walk the `here`/`there` spine, and hand-assemble the
catch-up chain for the specific contractum shape (app-chains via `StepStar.appFunction`/`appArgument`,
the substituting succ-iotas via pointwise-substitution chains).  This file replaces the PROOFS (never
the statements) with one engine over the table row:

  * `rowFiringCommuteWithStepRefire` — the keystone.  A canonical `iotaRuleTable` row firing at the
    root commutes with an arbitrary `Step`, with the survive branch exposing the REFIRE data: the
    stepped spine, the shape equation `other = .mkGen rule.elimGenerator elimPayload spineAfter`, the
    refire equation `rule.firesOn? elimPayload spineAfter = some refireReduct`, and the `StepStar`
    catch-up chain.  The root/cong dichotomy is `Step.weakHeadOrChildCong`; a root firing is settled
    by weak-head determinism; a child congruence refires by the IOTA-T6 parallel firing-stability
    (`IotaRuleDesc.firesOn?_parStable`) whose parallel reduct collapses to a `StepStar` chain.
    Consumers convert the refire equation to whatever head-step shape they need (per-row
    `<row>FiringToIotaHead` inversions, `canonicalRootFiringToWeakHeadStep`, …).

  * `rowFiringCommuteWithStepToIotaHead` — the `IotaHeadStep`-shaped packaging: given the row's
    firing-to-`IotaHeadStep` inversion, the survive branch delivers `IotaHeadStep other refireReduct`
    directly — the exact disjunction shape `IotaHeadStep.commuteWithStep`'s sixteen arms conclude.

  * The sixteen per-row SUBSUMPTION PINS (`boolTrueRedexCommuteWithStep` …
    `idStrictRecReflRedexCommuteWithStep`) — one named theorem per bespoke-heritage iota row, each
    stating the EXACT per-arm commute statement on the literal redex/contractum shapes of
    `IotaHeadStep`'s constructors and proved by the engine with a definitionally-computing
    `fires := rfl` pin (the same defeq route the derived `Step.iota*` rules ride).  These certify
    that the generic engine re-derives every bespoke arm verbatim; `IotaHeadStep.commuteWithStep`'s
    arms consume them.

## Zero-axiom verification

`rowFiringCommuteWithStepRefire` is `Step.weakHeadOrChildCong` + `WeakHeadStep.deterministic` on the
root branch and `firesOn?_parStable` + `ReflTransClosure.toStepStar` on the cong branch — all shipped
zero-axiom.  The pins are direct applications with `rfl` firing equations.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration by
`#audit_namespace FX1Poly.Core` plus the dedicated audit twin. -/

namespace FX1Poly.Core
open FX1Poly.Axis.Syntax

/-- **★ THE ROW-COMMUTE KEYSTONE: a canonical row firing commutes with an arbitrary step, refire
exposed.**  Given a row of the canonical table firing at the root (`fires`) and any step out of the
same redex, either the arbitrary step contracted the very root redex (`other = reduct`, by weak-head
determinism through `canonicalRootFiringToWeakHeadStep`), or the redex SURVIVES: the step was a child
congruence, the row REFIRES on the stepped spine (IOTA-T6 parallel firing-stability), and the original
reduct catches up to the refired reduct by a `StepStar` chain.  The survive branch exposes the full
refire data — spine shape, refire equation, catch-up chain — so each consumer can convert the refire
into its own head-step currency. -/
theorem rowFiringCommuteWithStepRefire {scope : Nat} {rule : IotaRuleDesc}
    (isRow : rule ∈ iotaRuleTable)
    {elimPayload : rule.elimGenerator.payload scope}
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {other : RawTerm scope}
    (step : Step (.mkGen rule.elimGenerator elimPayload spine) other)
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct) :
    other = reduct ∨
      ∃ spineAfter : RawTermChildren rule.elimGenerator.binderShifts scope,
        ∃ refireReduct : RawTerm scope,
          other = .mkGen rule.elimGenerator elimPayload spineAfter ∧
          rule.firesOn? elimPayload spineAfter = some refireReduct ∧
          StepStar reduct refireReduct := by
  cases Step.weakHeadOrChildCong step with
  | inl otherWeakHead =>
      have ourWeakHead : WeakHeadStep (.mkGen rule.elimGenerator elimPayload spine) reduct :=
        canonicalRootFiringToWeakHeadStep isRow elimPayload fires
      exact Or.inl (WeakHeadStep.deterministic ourWeakHead otherWeakHead).symm
  | inr congShape =>
      obtain ⟨spineAfter, otherShape, childStep⟩ := congShape
      have spinePar : ParStepOverTableChildren iotaRuleTable spine spineAfter :=
        StepOverTableChildren.toParStepOverTableChildren
          (StepChildren.toTableStepChildren childStep)
      obtain ⟨refireReduct, refires, reductPar⟩ :=
        rule.firesOn?_parStable iotaRuleTable_isScopeUniform
          (iotaRuleTable_isWf.scrutineeHeadsAreRigid isRow) elimPayload spinePar fires
      exact Or.inr ⟨spineAfter, refireReduct, otherShape, refires,
        ReflTransClosure.toStepStar reductPar.toStepClosure⟩

/-- **The `IotaHeadStep`-shaped packaging of the row-commute keystone.**  Feed the engine the row's
firing-to-`IotaHeadStep` inversion (one of the shipped `<row>FiringToIotaHead` lemmas) and the survive
branch delivers `IotaHeadStep other refireReduct` — the exact disjunction each arm of
`IotaHeadStep.commuteWithStep` concludes. -/
theorem rowFiringCommuteWithStepToIotaHead {scope : Nat} {rule : IotaRuleDesc}
    (isRow : rule ∈ iotaRuleTable)
    {elimPayload : rule.elimGenerator.payload scope}
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {other : RawTerm scope}
    (step : Step (.mkGen rule.elimGenerator elimPayload spine) other)
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct)
    (invertFiringToIotaHead :
      ∀ {spineAfter : RawTermChildren rule.elimGenerator.binderShifts scope}
        {refireReduct : RawTerm scope},
        rule.firesOn? elimPayload spineAfter = some refireReduct →
        IotaHeadStep (.mkGen rule.elimGenerator elimPayload spineAfter) refireReduct) :
    other = reduct ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧ StepStar reduct otherReduct := by
  rcases rowFiringCommuteWithStepRefire isRow step fires with
    otherIsReduct | ⟨spineAfter, refireReduct, otherShape, refires, catchUpChain⟩
  · exact Or.inl otherIsReduct
  · subst otherShape
    exact Or.inr ⟨refireReduct, invertFiringToIotaHead refires, catchUpChain⟩

/-! ## The sixteen per-row subsumption pins

One named theorem per bespoke-heritage iota row, each the EXACT statement of the corresponding
`IotaHeadStep.commuteWithStep` arm (literal redex and contractum copied from `IotaHeadStep`'s
constructors), proved by the generic engine + the row's membership pin + a definitionally-computing
`fires := rfl` + the row's shipped firing inversion.  These are the machine certificates that the
generic engine SUBSUMES every bespoke per-arm proof pile. -/

/-- Arm pin: `boolElim … boolTrue` commute — the `IotaHeadStep.iotaBoolTrue` arm's exact statement. -/
theorem boolTrueRedexCommuteWithStep {scope : Nat}
    {motive : RawTerm (scope + 1)} {thenBranch elseBranch : RawTerm scope}
    {other : RawTerm scope}
    (step : Step
      (.mkGen .gen_boolElim ()
        (.childCons motive
          (.childCons thenBranch
            (.childCons elseBranch
              (.childCons (.mkGen .gen_boolTrue () .childNil) .childNil)))))
      other) :
    other = thenBranch ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧ StepStar thenBranch otherReduct :=
  rowFiringCommuteWithStepToIotaHead boolTrueIotaRow_memTable step rfl
    (fun refires => boolTrueRowFiringToIotaHead _ refires)

/-- Arm pin: `boolElim … boolFalse` commute — the `IotaHeadStep.iotaBoolFalse` arm's exact statement. -/
theorem boolFalseRedexCommuteWithStep {scope : Nat}
    {motive : RawTerm (scope + 1)} {thenBranch elseBranch : RawTerm scope}
    {other : RawTerm scope}
    (step : Step
      (.mkGen .gen_boolElim ()
        (.childCons motive
          (.childCons thenBranch
            (.childCons elseBranch
              (.childCons (.mkGen .gen_boolFalse () .childNil) .childNil)))))
      other) :
    other = elseBranch ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧ StepStar elseBranch otherReduct :=
  rowFiringCommuteWithStepToIotaHead boolFalseIotaRow_memTable step rfl
    (fun refires => boolFalseRowFiringToIotaHead _ refires)

/-- Arm pin: `fst (pair …)` commute — the `IotaHeadStep.iotaFstPair` arm's exact statement. -/
theorem fstPairRedexCommuteWithStep {scope : Nat}
    {firstValue secondValue : RawTerm scope}
    {other : RawTerm scope}
    (step : Step
      (.mkGen .gen_fst ()
        (.childCons
          (.mkGen .gen_pair ()
            (.childCons firstValue (.childCons secondValue .childNil)))
          .childNil))
      other) :
    other = firstValue ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧ StepStar firstValue otherReduct :=
  rowFiringCommuteWithStepToIotaHead fstPairIotaRow_memTable step rfl
    (fun refires => fstPairRowFiringToIotaHead _ refires)

/-- Arm pin: `snd (pair …)` commute — the `IotaHeadStep.iotaSndPair` arm's exact statement. -/
theorem sndPairRedexCommuteWithStep {scope : Nat}
    {firstValue secondValue : RawTerm scope}
    {other : RawTerm scope}
    (step : Step
      (.mkGen .gen_snd ()
        (.childCons
          (.mkGen .gen_pair ()
            (.childCons firstValue (.childCons secondValue .childNil)))
          .childNil))
      other) :
    other = secondValue ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧ StepStar secondValue otherReduct :=
  rowFiringCommuteWithStepToIotaHead sndPairIotaRow_memTable step rfl
    (fun refires => sndPairRowFiringToIotaHead _ refires)

/-- Arm pin: `natElim … natZero` commute — the `IotaHeadStep.iotaNatElimZero` arm's exact statement. -/
theorem natElimZeroRedexCommuteWithStep {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    {other : RawTerm scope}
    (step : Step
      (.mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons (.mkGen .gen_natZero () .childNil) .childNil)))))
      other) :
    other = zeroBranch ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧ StepStar zeroBranch otherReduct :=
  rowFiringCommuteWithStepToIotaHead natElimZeroIotaRow_memTable step rfl
    (fun refires => natElimZeroRowFiringToIotaHead _ refires)

/-- Arm pin: `natRec … natZero` commute — the `IotaHeadStep.iotaNatRecZero` arm's exact statement. -/
theorem natRecZeroRedexCommuteWithStep {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    {other : RawTerm scope}
    (step : Step
      (.mkGen .gen_natRec ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons (.mkGen .gen_natZero () .childNil) .childNil)))))
      other) :
    other = zeroBranch ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧ StepStar zeroBranch otherReduct :=
  rowFiringCommuteWithStepToIotaHead natRecZeroIotaRow_memTable step rfl
    (fun refires => natRecZeroRowFiringToIotaHead _ refires)

/-- Arm pin: `listElim … listNil` commute — the `IotaHeadStep.iotaListElimNil` arm's exact statement. -/
theorem listElimNilRedexCommuteWithStep {scope : Nat}
    {motive : RawTerm (scope + 1)} {nilBranch consBranch : RawTerm scope}
    {other : RawTerm scope}
    (step : Step
      (.mkGen .gen_listElim ()
        (.childCons motive
          (.childCons nilBranch
            (.childCons consBranch
              (.childCons (.mkGen .gen_listNil () .childNil) .childNil)))))
      other) :
    other = nilBranch ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧ StepStar nilBranch otherReduct :=
  rowFiringCommuteWithStepToIotaHead listElimNilIotaRow_memTable step rfl
    (fun refires => listElimNilRowFiringToIotaHead _ refires)

/-- Arm pin: `optionMatch … optionNone` commute — the `IotaHeadStep.iotaOptionMatchNone` arm's exact
statement. -/
theorem optionMatchNoneRedexCommuteWithStep {scope : Nat}
    {motive : RawTerm (scope + 1)} {noneBranch someBranch : RawTerm scope}
    {other : RawTerm scope}
    (step : Step
      (.mkGen .gen_optionMatch ()
        (.childCons motive
          (.childCons noneBranch
            (.childCons someBranch
              (.childCons (.mkGen .gen_optionNone () .childNil) .childNil)))))
      other) :
    other = noneBranch ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧ StepStar noneBranch otherReduct :=
  rowFiringCommuteWithStepToIotaHead optionMatchNoneIotaRow_memTable step rfl
    (fun refires => optionMatchNoneRowFiringToIotaHead _ refires)

/-- Arm pin: `optionMatch … (optionSome value)` commute — the `IotaHeadStep.iotaOptionMatchSome`
arm's exact statement (the contractum is the 1-arg app-chain). -/
theorem optionMatchSomeRedexCommuteWithStep {scope : Nat}
    {motive : RawTerm (scope + 1)} {value noneBranch someBranch : RawTerm scope}
    {other : RawTerm scope}
    (step : Step
      (.mkGen .gen_optionMatch ()
        (.childCons motive
          (.childCons noneBranch
            (.childCons someBranch
              (.childCons (.mkGen .gen_optionSome () (.childCons value .childNil))
                .childNil)))))
      other) :
    other = .mkGen .gen_app () (.childCons someBranch (.childCons value .childNil)) ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧
          StepStar
            (.mkGen .gen_app () (.childCons someBranch (.childCons value .childNil)))
            otherReduct :=
  rowFiringCommuteWithStepToIotaHead optionMatchSomeIotaRow_memTable step rfl
    (fun refires => optionMatchSomeRowFiringToIotaHead _ refires)

/-- Arm pin: `eitherMatch … (eitherInl value)` commute — the `IotaHeadStep.iotaEitherMatchInl`
arm's exact statement (the contractum is the 1-arg app-chain). -/
theorem eitherMatchInlRedexCommuteWithStep {scope : Nat}
    {motive : RawTerm (scope + 1)} {value leftBranch rightBranch : RawTerm scope}
    {other : RawTerm scope}
    (step : Step
      (.mkGen .gen_eitherMatch ()
        (.childCons motive
          (.childCons leftBranch
            (.childCons rightBranch
              (.childCons (.mkGen .gen_eitherInl () (.childCons value .childNil))
                .childNil)))))
      other) :
    other = .mkGen .gen_app () (.childCons leftBranch (.childCons value .childNil)) ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧
          StepStar
            (.mkGen .gen_app () (.childCons leftBranch (.childCons value .childNil)))
            otherReduct :=
  rowFiringCommuteWithStepToIotaHead eitherMatchInlIotaRow_memTable step rfl
    (fun refires => eitherMatchInlRowFiringToIotaHead _ refires)

/-- Arm pin: `eitherMatch … (eitherInr value)` commute — the `IotaHeadStep.iotaEitherMatchInr`
arm's exact statement (the contractum is the 1-arg app-chain). -/
theorem eitherMatchInrRedexCommuteWithStep {scope : Nat}
    {motive : RawTerm (scope + 1)} {value leftBranch rightBranch : RawTerm scope}
    {other : RawTerm scope}
    (step : Step
      (.mkGen .gen_eitherMatch ()
        (.childCons motive
          (.childCons leftBranch
            (.childCons rightBranch
              (.childCons (.mkGen .gen_eitherInr () (.childCons value .childNil))
                .childNil)))))
      other) :
    other = .mkGen .gen_app () (.childCons rightBranch (.childCons value .childNil)) ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧
          StepStar
            (.mkGen .gen_app () (.childCons rightBranch (.childCons value .childNil)))
            otherReduct :=
  rowFiringCommuteWithStepToIotaHead eitherMatchInrIotaRow_memTable step rfl
    (fun refires => eitherMatchInrRowFiringToIotaHead _ refires)

/-- Arm pin: `natElim … (natSucc predecessor)` commute — the `IotaHeadStep.iotaNatElimSucc` arm's
exact statement (the contractum is the two-binder substituting succ-branch). -/
theorem natElimSuccRedexCommuteWithStep {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {predecessor zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    {other : RawTerm scope}
    (step : Step
      (.mkGen .gen_natElim ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons
                (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
                .childNil)))))
      other) :
    other =
        RawTerm.subst
          (RawTermSubst.cons
            (.mkGen .gen_natElim ()
              (.childCons motive
                (.childCons zeroBranch
                  (.childCons succBranch
                    (.childCons predecessor .childNil)))))
            (RawTermSubst.singleton predecessor))
          succBranch ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧
          StepStar
            (RawTerm.subst
              (RawTermSubst.cons
                (.mkGen .gen_natElim ()
                  (.childCons motive
                    (.childCons zeroBranch
                      (.childCons succBranch
                        (.childCons predecessor .childNil)))))
                (RawTermSubst.singleton predecessor))
              succBranch)
            otherReduct :=
  rowFiringCommuteWithStepToIotaHead natElimSuccIotaRow_memTable step rfl
    (fun refires => natElimSuccRowFiringToIotaHead _ refires)

/-- Arm pin: `natRec … (natSucc predecessor)` commute — the `IotaHeadStep.iotaNatRecSucc` arm's
exact statement (the contractum is the two-binder substituting succ-branch). -/
theorem natRecSuccRedexCommuteWithStep {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {predecessor zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    {other : RawTerm scope}
    (step : Step
      (.mkGen .gen_natRec ()
        (.childCons motive
          (.childCons zeroBranch
            (.childCons succBranch
              (.childCons
                (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
                .childNil)))))
      other) :
    other =
        RawTerm.subst
          (RawTermSubst.cons
            (.mkGen .gen_natRec ()
              (.childCons motive
                (.childCons zeroBranch
                  (.childCons succBranch
                    (.childCons predecessor .childNil)))))
            (RawTermSubst.singleton predecessor))
          succBranch ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧
          StepStar
            (RawTerm.subst
              (RawTermSubst.cons
                (.mkGen .gen_natRec ()
                  (.childCons motive
                    (.childCons zeroBranch
                      (.childCons succBranch
                        (.childCons predecessor .childNil)))))
                (RawTermSubst.singleton predecessor))
              succBranch)
            otherReduct :=
  rowFiringCommuteWithStepToIotaHead natRecSuccIotaRow_memTable step rfl
    (fun refires => natRecSuccRowFiringToIotaHead _ refires)

/-- Arm pin: `listElim … (listCons headVal tailVal)` commute — the `IotaHeadStep.iotaListElimCons`
arm's exact statement (the contractum is the 3-arg app-chain with the recursive call). -/
theorem listElimConsRedexCommuteWithStep {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {headVal tailVal nilBranch consBranch : RawTerm scope}
    {other : RawTerm scope}
    (step : Step
      (.mkGen .gen_listElim ()
        (.childCons motive
          (.childCons nilBranch
            (.childCons consBranch
              (.childCons
                (.mkGen .gen_listCons ()
                  (.childCons headVal (.childCons tailVal .childNil)))
                .childNil)))))
      other) :
    other =
        .mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_app ()
                  (.childCons consBranch (.childCons headVal .childNil)))
                (.childCons tailVal .childNil)))
            (.childCons
              (.mkGen .gen_listElim ()
                (.childCons motive
                  (.childCons nilBranch
                    (.childCons consBranch (.childCons tailVal .childNil)))))
              .childNil)) ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧
          StepStar
            (.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_app ()
                  (.childCons
                    (.mkGen .gen_app ()
                      (.childCons consBranch (.childCons headVal .childNil)))
                    (.childCons tailVal .childNil)))
                (.childCons
                  (.mkGen .gen_listElim ()
                    (.childCons motive
                      (.childCons nilBranch
                        (.childCons consBranch (.childCons tailVal .childNil)))))
                  .childNil)))
            otherReduct :=
  rowFiringCommuteWithStepToIotaHead listElimConsIotaRow_memTable step rfl
    (fun refires => listElimConsRowFiringToIotaHead _ refires)

/-- Arm pin: `idJ … (refl rawWitness)` commute — the `IotaHeadStep.iotaIdJRefl` arm's exact
statement. -/
theorem idJReflRedexCommuteWithStep {scope : Nat}
    {motive : RawTerm (scope + 2)} {baseCase rawWitness : RawTerm scope}
    {other : RawTerm scope}
    (step : Step
      (.mkGen .gen_idJ ()
        (.childCons motive
          (.childCons baseCase
            (.childCons (.mkGen .gen_refl () (.childCons rawWitness .childNil)) .childNil))))
      other) :
    other = baseCase ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧ StepStar baseCase otherReduct :=
  rowFiringCommuteWithStepToIotaHead idJReflIotaRow_memTable step rfl
    (fun refires => idJReflRowFiringToIotaHead _ refires)

/-- Arm pin: `idStrictRec … (refl rawWitness)` commute — the `IotaHeadStep.iotaIdStrictRecRefl`
arm's exact statement. -/
theorem idStrictRecReflRedexCommuteWithStep {scope : Nat}
    {motive : RawTerm (scope + 2)} {baseCase rawWitness : RawTerm scope}
    {other : RawTerm scope}
    (step : Step
      (.mkGen .gen_idStrictRec ()
        (.childCons motive
          (.childCons baseCase
            (.childCons (.mkGen .gen_refl () (.childCons rawWitness .childNil)) .childNil))))
      other) :
    other = baseCase ∨
      ∃ otherReduct : RawTerm scope,
        IotaHeadStep other otherReduct ∧ StepStar baseCase otherReduct :=
  rowFiringCommuteWithStepToIotaHead idStrictRecReflIotaRow_memTable step rfl
    (fun refires => idStrictRecReflRowFiringToIotaHead _ refires)

end FX1Poly.Core

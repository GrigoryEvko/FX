import FX1Poly.Core.StratifiedReducibleType
import FX1Poly.Core.ReducibleTypeForwardStepStar
import FX1Poly.Core.ConvNormalForm
import FX1Poly.Core.StrongNormalizationLeaves

/-! # Foundation/PolyCell/Core/StratifiedReducibleTypeForwardClosure
    — forward closure of the STRATIFIED (Tarski-universe) reducibility relation under reduction

`ReducibleType.forwardStepStar` ships forward closure for the pure-SN relation; this file ports it to the
stratified step-functor `ReducibleTypeStep lowerReducible` from `StratifiedReducibleType`, adding the case
for the new `universeCode` arm.  The statement is the same keystone of conversion-invariance: a reducible
type stays reducible at the SAME candidate along any `StepStar`.

The three non-universe arms reuse the existing reduction machinery verbatim (now over the stratified
constructors):

  * `whnfExpand` — `ReducibleTypeStep.whnfExpandClosure` (the weak-head commutation diamond), a direct
    port of `ReducibleType.whnfExpandClosure`.
  * `neutral` — `WeakHeadStep.weakHeadNormalRootStableAlongStepStar`, a NEW reusable helper that returns
    weak-head-normality preservation AND root-generator EQUALITY (strictly more than the piTyCode-specialized
    `ReducibleType.neutralPreservedAlongStepStar`), so BOTH the `notPiType` and the new `notUniverse` guards
    are re-derived from one root equation.
  * `piType` — `StepStar.piTyCode_decompose` + `StepStar.subst0Body`, identical to the pure-SN proof.

The `universeCode` arm is the easy one: a universe code `mkGen gen_universeCode (levelExpr, flag) childNil`
is a STEP normal form (no children to congruence-step, no redex root — `noStep_universeCode`), so any
`StepStar` out of it is reflexive (`StepStar.eq_of_noStep`) and the universe code rebuilds itself.

## Zero-axiom verification

Induction on the reducibility derivation (per arm) and on the `StepStar` chain (for `whnfExpandClosure` and
the root-stability helper); the universe arm is `eq_of_noStep` + `subst` + the `universeCode` constructor.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept per declaration
by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **Weak-head-normal root stability along `StepStar`.**  A weak-head-NORMAL term stays weak-head-normal
under any multi-step reduction, AND its root generator is preserved.  Weak-head-normality descends
step-by-step (`WeakHeadStep.weakHeadNormalPreservedByStep`) and the root generator is fixed by each step
out of a normal form (`Step.rootGenerator_eq_of_weakHeadNormal`), composed along the chain.  Returning the
root EQUALITY (not a single `≠`-guard) lets a caller re-derive every root-disequality guard at once — the
engine of the stratified `neutral` arm, which carries both `notPiType` and `notUniverse`. -/
theorem WeakHeadStep.weakHeadNormalRootStableAlongStepStar {scope : Nat} :
    ∀ {startType finalType : RawTerm scope}, StepStar startType finalType →
      (∀ reduct : RawTerm scope, ¬ WeakHeadStep startType reduct) →
      (∀ reduct : RawTerm scope, ¬ WeakHeadStep finalType reduct) ∧
        finalType.rootGenerator = startType.rootGenerator := by
  intro startType finalType chain
  induction chain with
  | refl _ => intro noWeakHeadStep; exact ⟨noWeakHeadStep, rfl⟩
  | trans firstStep _restChain restStable =>
      intro noWeakHeadStep
      have intermediateNoWeakHeadStep :=
        WeakHeadStep.weakHeadNormalPreservedByStep noWeakHeadStep firstStep
      have rootEquation := Step.rootGenerator_eq_of_weakHeadNormal noWeakHeadStep firstStep
      obtain ⟨finalNoWeakHeadStep, finalRootEquation⟩ := restStable intermediateNoWeakHeadStep
      exact ⟨finalNoWeakHeadStep, finalRootEquation.trans rootEquation⟩

/-- **Forward closure of a stratified `whnfExpand` code along `StepStar`.**  The stratified port of
`ReducibleType.whnfExpandClosure`: a `whnfExpand`-typed code (weak-head reduct reducible at `candidate`,
every further reduct reducible) stays reducible at `candidate` along ANY `StepStar`.  Each leading step is
commuted past the weak-head redex by `WeakHeadStep.commuteWithStep`; the surviving-redex branch recurses on
the tail with the catch-up chain threaded into a refreshed closure. -/
theorem ReducibleTypeStep.whnfExpandClosure {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    {candidate : RawTerm scope → Prop} :
    ∀ {firstType finalType : RawTerm scope}, StepStar firstType finalType →
      ∀ {weakHeadReduct : RawTerm scope}, WeakHeadStep firstType weakHeadReduct →
        ReducibleTypeStep lowerReducible weakHeadReduct candidate →
        (∀ furtherReduct : RawTerm scope, StepStar weakHeadReduct furtherReduct →
          ReducibleTypeStep lowerReducible furtherReduct candidate) →
        ReducibleTypeStep lowerReducible finalType candidate := by
  intro firstType finalType chain
  induction chain with
  | refl _ =>
      intro weakHeadReduct weakHeadStep reductReducible _laterClosure
      exact ReducibleTypeStep.whnfExpand weakHeadStep reductReducible
  | trans firstStep _restChain restClosure =>
      intro weakHeadReduct weakHeadStep reductReducible laterClosure
      rcases weakHeadStep.commuteWithStep _ firstStep with
        midEquation | ⟨_laterReduct, laterWeakHeadStep, catchUpChain⟩
      · subst midEquation
        exact laterClosure _ _restChain
      · exact restClosure laterWeakHeadStep (laterClosure _ catchUpChain)
          (fun furtherReduct furtherChain =>
            laterClosure furtherReduct (StepStar.trans_compose catchUpChain furtherChain))

/-- **Forward closure of the stratified reducibility relation under multi-step reduction.**  A stratified
reducible type stays reducible at the SAME candidate along any `StepStar` — the keystone of
conversion-invariance for the Tarski-universe relation.  Induction on the derivation dispatches by arm:
`whnfExpand` pushes the chain past the weak-head redex (`whnfExpandClosure`); `neutral` re-derives both
root guards from the root equality (`weakHeadNormalRootStableAlongStepStar`); `piType` decomposes the
Π-code reduction (`StepStar.piTyCode_decompose` / `StepStar.subst0Body`) and rebuilds; `universeCode` is a
step normal form (`noStep_universeCode`) so the chain is reflexive (`StepStar.eq_of_noStep`) and the code
rebuilds itself. -/
theorem ReducibleTypeStep.forwardStepStar {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    {candidate : RawTerm scope → Prop} {typeCode : RawTerm scope}
    (reducible : ReducibleTypeStep lowerReducible typeCode candidate) :
    ∀ {finalType : RawTerm scope}, StepStar typeCode finalType →
      ReducibleTypeStep lowerReducible finalType candidate := by
  induction reducible with
  | whnfExpand weakHeadStep reductReducible reductInductiveHypothesis =>
      intro finalType chain
      exact ReducibleTypeStep.whnfExpandClosure chain weakHeadStep reductReducible
        (fun _furtherReduct furtherChain => reductInductiveHypothesis furtherChain)
  | neutral noWeakHeadStep notPiType notUniverse =>
      intro finalType chain
      obtain ⟨finalNoWeakHeadStep, rootEquation⟩ :=
        WeakHeadStep.weakHeadNormalRootStableAlongStepStar chain noWeakHeadStep
      exact ReducibleTypeStep.neutral finalNoWeakHeadStep
        (fun rootIsPiType => notPiType (rootEquation.symm.trans rootIsPiType))
        (fun rootIsUniverse => notUniverse (rootEquation.symm.trans rootIsUniverse))
  | piType codomainCandidate _domainReducible _codomainReducible
      domainInductiveHypothesis codomainInductiveHypothesis =>
      intro finalType chain
      obtain ⟨_updatedDomain, _updatedCodomain, finalEquation, domainChain, codomainChain⟩ :=
        StepStar.piTyCode_decompose chain
      subst finalEquation
      exact ReducibleTypeStep.piType codomainCandidate (domainInductiveHypothesis domainChain)
        (fun argument domainMember =>
          codomainInductiveHypothesis argument domainMember
            (StepStar.subst0Body argument codomainChain))
  | universeCode levelExpr flag =>
      intro finalType chain
      have finalEquation :=
        StepStar.eq_of_noStep (fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step)
          chain
      subst finalEquation
      exact ReducibleTypeStep.universeCode levelExpr flag

/-- **Forward closure of the level-indexed relation.**  `ReducibleTypeStep.forwardStepStar` specialized
through the `Nat` recursion of `ReducibleTypeAt` (level `0` over the empty lower relation, level `n+1` over
`ReducibleTypeAt n`); both cases are the step-functor closure by defeq.  The explicit
`ReducibleTypeStep.forwardStepStar` (not dot-notation) avoids a self-recursive resolution to
`ReducibleTypeAt.forwardStepStar`. -/
theorem ReducibleTypeAt.forwardStepStar {scope : Nat} {level : Nat}
    {candidate : RawTerm scope → Prop} {typeCode finalType : RawTerm scope}
    (reducible : ReducibleTypeAt level typeCode candidate)
    (chain : StepStar typeCode finalType) :
    ReducibleTypeAt level finalType candidate := by
  cases level with
  | zero => exact ReducibleTypeStep.forwardStepStar reducible chain
  | succ predLevel => exact ReducibleTypeStep.forwardStepStar reducible chain

end FX1Poly.Core

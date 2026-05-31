import FX1Poly.Core.ReducibleType
import FX1Poly.Core.WeakHeadStepCommute

/-! # Foundation/PolyCell/Core/ReducibleTypeForwardStepStar
    — forward closure of the dependent reducibility relation under multi-step reduction (whnfExpand arm)

Conversion-invariance of `ReducibleType` factors through FORWARD CLOSURE along `StepStar`:
`ReducibleType firstType candidate → StepStar firstType finalType → ReducibleType finalType candidate`.
The relation has three arms (`whnfExpand` / `neutral` / `piType`), and the full closure proof dispatches
the chain differently per arm.  This file ships the `whnfExpand` arm — the one that needs the commutation
diamond — as a standalone, reusable theorem; the `neutral` arm (needs weak-head-normality preservation,
`WeakHeadNormalPreservation`) and the `piType` arm (`StepStar.piTyCode_decompose` +
`StepStar.subst0Body`, `ReducibleTypeForwardClosure`) assemble on top of it into the master
`forwardStepStar`.

`ReducibleType.whnfExpandClosure`: a `whnfExpand`-typed code (one with a weak-head reduct `weakHeadReduct`
reducible at `candidate`, and whose every further reduct is also reducible — the induction hypothesis a
`whnfExpand` sub-derivation supplies) stays reducible at `candidate` along ANY `StepStar`.  The proof
pushes each leading step past the weak-head redex with `WeakHeadStep.commuteWithStep`: if the step IS the
weak-head contraction the chain continues from the reduct (closed by the stored further-reduct closure);
otherwise the weak-head redex survives (`other` weak-head steps to `laterReduct`, `weakHeadReduct ↠
laterReduct`), and the tail chain replays from `laterReduct` with a freshly-composed closure
(`closure ∘ trans_compose catchUpChain`).

## Zero-axiom verification

Induction on the `StepStar` chain; the leading step is commuted by `WeakHeadStep.commuteWithStep`, the
catch-up chains composed by `StepStar.trans_compose`, the base case rebuilt by the `ReducibleType.whnfExpand`
constructor.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Swept
per declaration by `#audit_namespace FX1Poly.Core`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation

/-- **Forward closure of a `whnfExpand` code along `StepStar`.**  Given a weak-head step
`firstType ↝ʰ weakHeadReduct` with `weakHeadReduct` reducible at `candidate` and every further reduct of
`weakHeadReduct` reducible at `candidate` (the `whnfExpand` sub-derivation's induction hypothesis), any
`StepStar firstType finalType` lands `finalType` reducible at `candidate`.  Each leading step is commuted
past the weak-head redex; the surviving-redex branch recurses on the tail chain with the catch-up chain
threaded into a refreshed closure. -/
theorem ReducibleType.whnfExpandClosure {scope : Nat} {candidate : RawTerm scope → Prop} :
    ∀ {firstType finalType : RawTerm scope}, StepStar firstType finalType →
      ∀ {weakHeadReduct : RawTerm scope}, WeakHeadStep firstType weakHeadReduct →
        ReducibleType weakHeadReduct candidate →
        (∀ furtherReduct : RawTerm scope, StepStar weakHeadReduct furtherReduct →
          ReducibleType furtherReduct candidate) →
        ReducibleType finalType candidate := by
  intro firstType finalType chain
  induction chain with
  | refl _ =>
      intro weakHeadReduct weakHeadStep reductReducible _laterClosure
      exact ReducibleType.whnfExpand weakHeadStep reductReducible
  | trans firstStep _restChain restClosure =>
      intro weakHeadReduct weakHeadStep reductReducible laterClosure
      rcases weakHeadStep.commuteWithStep _ firstStep with
        midEquation | ⟨_laterReduct, laterWeakHeadStep, catchUpChain⟩
      · subst midEquation
        exact laterClosure _ _restChain
      · exact restClosure laterWeakHeadStep (laterClosure _ catchUpChain)
          (fun furtherReduct furtherChain =>
            laterClosure furtherReduct (StepStar.trans_compose catchUpChain furtherChain))

end FX1Poly.Core

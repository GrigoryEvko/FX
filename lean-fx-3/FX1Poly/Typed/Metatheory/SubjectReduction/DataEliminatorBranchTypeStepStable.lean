import FX1Poly.Typed.Metatheory.SubjectReduction.StepStarCellCongruence
import FX1Poly.Typed.Cell.OptionMatchDependentSomeBranchType
import FX1Poly.Typed.Cell.EitherMatchDependentBranchType
import FX1Poly.Typed.Cell.IdJDependentMotiveType

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/DataEliminatorBranchTypeStepStable
    — SR-DSL-4: option / either dependent branch types REDUCE when the motive steps (the classifier StepStar drift)

The context-fixed obligation driver (`premisesHoldUnderObligationsDrift`) needs, per obligation, the classifier's
`StepStar` drift.  For `optionMatch` / `eitherMatch`, the dependent branch obligations live at the AMBIENT context
(their branch TYPE is a `piTyCode` function type — the binder is inside the type, not in the obligation's context),
so when the motive steps only the CLASSIFIER drifts, and these eliminators fit the context-fixed driver directly.

This file ships those classifier drifts — the DIRECTED (`StepStar`) twins of the shipped formedness lemmas
(`optionMatchDependentSomeBranchType_formedUnderMotiveStep` etc.).  Each is the formedness lemma's proof with
`Step.subst` ↝ `StepStar.subst` and `piCodeFormedUnderCodomainStep` ↝ `StepStar.piTyCode_cong`: the branch type is
`piTyCodeCell <elementType> (<codomain> motive)`, the codomain is a single motive substitution, so the type reduces
in its codomain leg while the element-type domain stays fixed.

## Zero-axiom

`StepStar.piTyCode_cong` (shipped) over `StepStar.subst` (substitution stability of `StepStar`).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax

/-- **The `optionMatch` some-branch type reduces when the motive reduces.**  `optionMatchDependentSomeBranchType
motive valueType = piTyCodeCell valueType (optionMatchDependentSomeBranchCodomain motive)`, the codomain a single
`subst` of the motive, so the type `StepStar`-reduces in its codomain (domain `valueType` fixed).  The directed
twin of `optionMatchDependentSomeBranchType_formedUnderMotiveStep`. -/
theorem optionMatchDependentSomeBranchType_stepStable {scope : Nat}
    {motive motiveAfter : RawTerm (scope + 1)} {valueType : RawTerm scope}
    (motiveChain : StepStar motive motiveAfter) :
    StepStar (optionMatchDependentSomeBranchType motive valueType)
             (optionMatchDependentSomeBranchType motiveAfter valueType) := by
  unfold optionMatchDependentSomeBranchType
  refine StepStar.piTyCode_cong (StepStar.refl valueType) ?_
  unfold optionMatchDependentSomeBranchCodomain
  exact StepStar.subst _ motiveChain

/-- **The `eitherMatch` inl-branch type reduces when the motive reduces** — the inl twin of
`optionMatchDependentSomeBranchType_stepStable` at the inl re-basing. -/
theorem eitherMatchDependentInlBranchType_stepStable {scope : Nat}
    {motive motiveAfter : RawTerm (scope + 1)} {leftType : RawTerm scope}
    (motiveChain : StepStar motive motiveAfter) :
    StepStar (eitherMatchDependentInlBranchType motive leftType)
             (eitherMatchDependentInlBranchType motiveAfter leftType) := by
  unfold eitherMatchDependentInlBranchType
  refine StepStar.piTyCode_cong (StepStar.refl leftType) ?_
  unfold eitherMatchDependentInlBranchCodomain
  exact StepStar.subst _ motiveChain

/-- **The `eitherMatch` inr-branch type reduces when the motive reduces** — the inr twin. -/
theorem eitherMatchDependentInrBranchType_stepStable {scope : Nat}
    {motive motiveAfter : RawTerm (scope + 1)} {rightType : RawTerm scope}
    (motiveChain : StepStar motive motiveAfter) :
    StepStar (eitherMatchDependentInrBranchType motive rightType)
             (eitherMatchDependentInrBranchType motiveAfter rightType) := by
  unfold eitherMatchDependentInrBranchType
  refine StepStar.piTyCode_cong (StepStar.refl rightType) ?_
  unfold eitherMatchDependentInrBranchCodomain
  exact StepStar.subst _ motiveChain

/-- **The `idJ` motive instantiation reduces when the motive (body) reduces.**  `idJMotiveAt motive point path =
substPair motive path point = subst (pair path point) motive` (`substPair` is `@[reducible]` over `subst`), so a
motive `StepStar` lifts directly by the substitution body-congruence `StepStar.subst` at the fixed pair
substitution.  `idJ`'s base-case obligation classifier is `idJMotiveAt motive leftEndpoint (reflCell leftEndpoint)`
at the AMBIENT context, so when the motive steps only the CLASSIFIER drifts — `idJ` is context-fixed (its motive
obligation's context head `idJMotiveSecondBinderType typeCode left` is motive-INDEPENDENT). -/
theorem idJMotiveAt_bodyStepStable {scope : Nat} {motive motiveAfter : RawTerm (scope + 2)}
    (point path : RawTerm scope) (motiveChain : StepStar motive motiveAfter) :
    StepStar (idJMotiveAt motive point path) (idJMotiveAt motiveAfter point path) := by
  unfold idJMotiveAt
  exact StepStar.subst (RawTermSubst.pair path point) motiveChain

end FX1Poly.Typed

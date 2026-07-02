import FX1Poly.Typed.Engine.Union.HasTypeUnionInversion
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiDataHeadUntyped

/-! # FX1Poly/Typed/Metatheory/HostAdmissibility/NativeUnionInversionCoverage — the native-union inversion coverage gate

Relocated out of `HasTypeUnionInversion` (B0-b) so the `Union/` core no longer imports the grown engine.  This
gate records the first-elimination inversion deliverables; its `grownRejectsPathLamHead` field is the one
grown-engine statement (`HasTypeDescPi` types no pathLam head), inhabited by the relocated
`HasTypeDescPi.pathLamCellHasNoTyping` (now homed in the grown corpus `HasTypeDescPiDataHeadUntyped`).  The
five native fields cite the `invertAt*Head` / affine-rejection lemmas that stay in `HasTypeUnionInversion`.

## Zero-axiom

Structure fields inhabited by the shipped inversions + the grown pathLam refutation.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/Typed/Metatheory/HostAdmissibility/NativeUnionInversionCoverage.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-- **The NATIVE-37 inversion coverage record.**  Each field is a distinct live property of the first
eliminations over the native union: the host pathLam-head refutation, the four per-head inversions, and the
union-wide affine rejection.  An inhabitant certifies the inversion substrate is exercised (constructed, not just
declared). -/
structure NativeUnionInversionCoverage (profile : PolyProfile) : Prop where
  /-- The grown engine types no pathLam-headed subject. -/
  grownRejectsPathLamHead : ∀ {scope : Nat} {context : TypingContext profile scope}
    {body : RawTerm (scope + 1)} {classifier : RawTerm scope},
    HasTypeDescPi profile context (pathLamCell body) classifier → False
  /-- The pathLam-head inversion holds (native-only: the graded pathLam-row premises directly — the former
  grown disjunct is dropped, redundant by `iff_nativeOnly`), Conv-modulo: the conv arm reclassifies, so the
  pinned classifier is convertible to the actual one. -/
  pathLamInversion : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} {body : RawTerm (scope + 1)},
    HasTypeUnion profile context subject classifier →
    subject = pathLamCell body →
    ∃ (carrierCode pinnedClassifier : RawTerm scope),
      pinnedClassifier = bridgeTypeCell carrierCode
        (RawTerm.subst0 body intervalZeroCell) (RawTerm.subst0 body intervalOneCell) ∧
      gradedBinderChecks UsageGrade.one body ∧
      HasTypeUnion profile (context.lockCons intervalTypeCell) body
        (RawTerm.weaken carrierCode) ∧
      Conv pinnedClassifier classifier
  /-- The natElim-head inversion holds (the single recursive-eliminator survivor). -/
  natElimInversion : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} {motive : RawTerm (scope + 1)}
    {zeroBranch : RawTerm scope} {stepBranch : RawTerm (scope + 2)} {scrutinee : RawTerm scope},
    HasTypeUnion profile context subject classifier →
    subject = natElimCell motive zeroBranch stepBranch scrutinee →
    HasTypeUnion profile context scrutinee natTypeCell ∧
    HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell) ∧
    Conv (RawTerm.subst0 motive scrutinee) classifier
  /-- The natSucc-head inversion holds (EXACT since the NATIVE-42 embedding-arm deletion),
  Conv-modulo: the conv arm reclassifies, so the pinned `Nat` classifier is convertible to the
  actual one. -/
  natSuccInversion : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope} {child : RawTerm scope},
    HasTypeUnion profile context subject classifier →
    subject = natSuccCell child →
    Conv natTypeCell classifier ∧ HasTypeUnion profile context child natTypeCell
  /-- The union rejects the affine double-use path abstraction at every classifier and context. -/
  affineDoubleUseRejected : ∀ {scope : Nat} (context : TypingContext profile scope)
    (classifier : RawTerm scope),
    ¬ HasTypeUnion profile context
        (pathLamCell (doubleDimensionUseBody scope)) classifier
  /-- Every union-typed pathLam body uses the dimension binder at most once (the affine-honesty pin,
  union-side — the FORCED grade, successor of the retired `HasTypeDescBridge.pathLamSubjectIsAffine`). -/
  pathLamBodyAffine : ∀ {scope : Nat} {context : TypingContext profile scope}
    {body : RawTerm (scope + 1)} {classifier : RawTerm scope},
    HasTypeUnion profile context (pathLamCell body) classifier →
    RawTerm.occurrenceCountAt body ⟨0, Nat.succ_pos scope⟩ ≤ 1

/-- **★ The NATIVE-37 inversion coverage gate** — inhabited by the shipped declarations, so the exercised
inversion-substrate property set can NOT silently shrink. -/
theorem nativeUnionInversionCoverageWitness {profile : PolyProfile} :
    NativeUnionInversionCoverage profile where
  grownRejectsPathLamHead := fun typed => typed.pathLamCellHasNoTyping
  pathLamInversion := fun derivation subjectShape => derivation.invertAtPathLamHead subjectShape
  natElimInversion := fun derivation subjectShape => derivation.invertAtNatElimHead subjectShape
  natSuccInversion := fun derivation subjectShape => derivation.invertAtNatSuccHead subjectShape
  affineDoubleUseRejected := fun context classifier =>
    HasTypeUnion.unionRejectsAffineDoubleUse context classifier
  pathLamBodyAffine := fun derivation => derivation.pathLamSubjectIsAffine

end FX1Poly.Typed

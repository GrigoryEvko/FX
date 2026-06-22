import FX1Poly.Core.Metatheory.Canonicity.ReflCanonicalFormsCandidate
import FX1Poly.Core.Eliminators.Core.DependentDataEliminatorMemberSkeleton
import FX1Poly.Core.Eliminators.Core.DataTaitFocusTrichotomy
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.IdentityEliminatorStrongNormalization
import FX1Poly.Core.Rewriting.Reduction.Head.IotaHeadStep

/-! # FX1Poly/Core/IdentityEliminatorGeneralCandidateMember
    — dependent `idJ` / `idStrictRec` over a `dataTaitCandidate` scrutinee land in the motive candidate (identity)

The identity-eliminator companions to `optionMatchDependentReducibleMember`: the native bounded data-eliminator FT
rows need `idJ` (path induction / J) and `idStrictRec` to land in an ARBITRARY reducibility candidate (the
dependent motive's instantiated output type), with the scrutinee arriving as a member of the head-expansion-closed
`dataTaitCandidate isReflValue`.

The identity type has the single unary constructor `refl witness` (the reflected point), and its eliminators
contract to the BASE CASE DIRECTLY on `refl` (`idJ motive baseCase (refl w) ↝ baseCase`) — no branch application,
no substitution into the base.  So the members take no branch-SN or application-SN premise — only the cell's spine
SN (`idJ_isStronglyNormalizing_of_strongly_normalizing_base`, which needs the motive and base SN) and a single
conditioned base-membership premise (the base case is a result member WHEN the scrutinee reaches a `refl`).  The
motive binds two variables (the path endpoint and the path), so it lives at `scope + 2`; the Core member is
agnostic to this — it threads the motive untouched.  There is one constructor (`refl`), so the trichotomy's
value-head set is the singleton `gen_refl`.  As with option/either, a `refl(redex)` focus is a candidate member
whose witness is a redex — not a value, not neutral, not weak-head reducible — so the trichotomy concludes the
CONSTRUCTOR-HEAD relaxation `isReflConstructorHead` (head `refl`, witness arbitrary), recovered by
`isReflConstructorHead_ofValueHead`.

This is the fifth dependent data-eliminator general-candidate family (after `bool`, `option`, `either`,
pair-projection), the first with a DIRECT base-case contractum.  `idJ` and `idStrictRec` are identical bar the
generator and share every refl helper — the J and the strict identity recursor.

## Zero-axiom verification

`isReflConstructorHead_ofValueHead` mirrors `isOptionConstructorHead_ofValueHead`'s head-recovery idiom (match the
cell, `change` the singleton root equation, `subst`), collapsing the `Unit` payload and the unary witness GADT
(`[0]`).  The members drive the shared skeleton with the identity spine lemmas
(`idJ` / `idStrictRec_isStronglyNormalizing_of_strongly_normalizing_base`, `WeakHeadStep.scrutineeIdJ` / `…IdStrictRec`,
`IsNeutral.idJ` / `…idStrictRec`) and fire `iotaIdJRefl` / `iotaIdStrictRecRefl`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated by the `FX1Poly.Core` namespace
sweep in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- **The refl value-head generator predicate.**  The sole identity data constructor. -/
def isReflValueHead (generator : Generator) : Prop :=
  generator = .gen_refl

/-- **The refl constructor-head predicate.**  A term is identity-constructor-headed when it is `reflCell witness`
with the witness ARBITRARY (no normality side-condition — unlike `isReflValue`).  This is the predicate the
dependent-eliminator value dispatch fires the ι on (the ι fires on `refl(anything)`) and the trichotomy concludes;
`isReflValue ⊆ isReflConstructorHead`. -/
def isReflConstructorHead {scope : Nat} (term : RawTerm scope) : Prop :=
  ∃ witness : RawTerm scope, term = reflCell witness

/-- **A refl value is identity-constructor-headed.**  Drops the witness-normality side-condition of `isReflValue`
— the easy inclusion the trichotomy's candidate-side bridge composes with. -/
theorem isReflConstructorHead_ofIsReflValue {scope : Nat} {term : RawTerm scope}
    (valueIsRefl : isReflValue term) : isReflConstructorHead term := by
  obtain ⟨witness, valueEq, _witnessNormal⟩ := valueIsRefl
  exact ⟨witness, valueEq⟩

/-- **A refl value's root generator is the refl value head.**  The candidate-side trichotomy bridge: a normal
identity value's root is `gen_refl`. -/
theorem isReflValueHead_ofIsReflValue {scope : Nat} {term : RawTerm scope}
    (valueIsRefl : isReflValue term) : isReflValueHead term.rootGenerator := by
  obtain ⟨_witness, valueEq, _witnessNormal⟩ := valueIsRefl
  exact congrArg RawTerm.rootGenerator valueEq

/-- **★ Root-generator reconstruction for refl.**  A term whose root generator is the identity constructor IS
identity-constructor-headed — `reflCell witness` structurally.  The conclusion-side trichotomy bridge, recovering
the focus's constructor shape from `reachesValueHead`'s root-generator output.  Mirrors
`isOptionConstructorHead_ofValueHead`'s head-recovery (match the cell, `change`+`subst` the root equation), then
collapses the `Unit` payload and the unary witness GADT (`[0]`). -/
theorem isReflConstructorHead_ofValueHead {scope : Nat} {term : RawTerm scope}
    (rootIsRefl : isReflValueHead term.rootGenerator) : isReflConstructorHead term := by
  match term, rootIsRefl with
  | .mkGen generator payload children, rootIsRefl =>
      change generator = .gen_refl at rootIsRefl
      subst rootIsRefl
      match payload, children with
      | (), .childCons witness .childNil => exact ⟨witness, rfl⟩

/-- **★ Dependent `idJ` reducibility: the cell lands in the candidate of the motive at the scrutinee.**  The
path-induction companion to `optionMatchDependentReducibleMember`.  The scrutinee arrives as a member of the
head-expansion-closed `dataTaitCandidate isReflValue`; the BASE CASE is a result member WHEN the scrutinee reaches
`refl witness` (the conditioning the bounded row discharges from the motive's reducibility).  J contracts to the
base case directly on `refl`, so there is no branch application; the spine SN needs the motive (at `scope + 2`) and
base SN.  Drives the shared `dependentDataEliminatorMemberFromValueDispatch`: the per-focus classifier is
`dataTaitFocusTrichotomyOfValueHead` at refl's singleton constructor-head set; the value handler fires `iotaIdJRefl`
and transports the conditioned base case. -/
theorem idJDependentReducibleMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (memberOfStronglyNormalizingNeutral :
      ∀ {neutralTerm : RawTerm scope},
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidate neutralTerm)
    {motive : RawTerm (scope + 2)} {scrutinee baseCase : RawTerm scope}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (baseCaseStronglyNormalizing : IsStronglyNormalizing baseCase)
    (scrutineeMember : dataTaitCandidate isReflValue scrutinee)
    (baseCaseMemberIfReachesRefl : ∀ witness : RawTerm scope,
        StepStar scrutinee (reflCell witness) → resultCandidate baseCase) :
    resultCandidate
      (.mkGen .gen_idJ ()
        (.childCons motive (.childCons baseCase (.childCons scrutinee .childNil)))) :=
  dependentDataEliminatorMemberFromValueDispatch
    (isValue := isReflConstructorHead)
    (scrutineeCandidate := dataTaitCandidate isReflValue)
    (elimSpine := fun focus =>
      .mkGen .gen_idJ () (.childCons motive (.childCons baseCase (.childCons focus .childNil))))
    (focusTrichotomy := fun focusMember =>
      dataTaitFocusTrichotomyOfValueHead
        (valueHead := isReflValueHead) (candidateValue := isReflValue)
        (conclusionValue := isReflConstructorHead)
        (fun valueIsRefl => isReflValueHead_ofIsReflValue valueIsRefl)
        (fun rootIsRefl => isReflConstructorHead_ofValueHead rootIsRefl)
        focusMember)
    (candidateStronglyNormalizing := fun focusMember => focusMember.stronglyNormalizing)
    (candidateClosedUnderStep := fun focusMember step => focusMember.closedUnderStep step)
    (spineStronglyNormalizing := fun focusStronglyNormalizing =>
      idJ_isStronglyNormalizing_of_strongly_normalizing_base motiveStronglyNormalizing
        baseCaseStronglyNormalizing focusStronglyNormalizing)
    (spineScrutineeCongruence := fun focusWeakHead => WeakHeadStep.scrutineeIdJ focusWeakHead)
    (spineNeutral := fun focusNeutral => IsNeutral.idJ focusNeutral)
    (headExpand := headExpand)
    (memberOfStronglyNormalizingNeutral := memberOfStronglyNormalizingNeutral)
    (valueHandler := fun focusIsConstructorHead reaches cellStronglyNormalizing => by
      obtain ⟨witness, focusIsRefl⟩ := focusIsConstructorHead
      subst focusIsRefl
      exact headExpand IotaHeadStep.iotaIdJRefl.toWeakHeadStep
        (baseCaseMemberIfReachesRefl witness reaches) cellStronglyNormalizing)
    (scrutineeMember := scrutineeMember)

/-- **★ Dependent `idStrictRec` reducibility: the cell lands in the candidate of the motive at the scrutinee.**
Identical to `idJDependentReducibleMember` bar the generator: the strict identity recursor's spine SN is
`idStrictRec_isStronglyNormalizing_of_strongly_normalizing_base`, the congruence `WeakHeadStep.scrutineeIdStrictRec`,
the neutrality `IsNeutral.idStrictRec`, and the value handler fires `iotaIdStrictRecRefl`.  Shares every refl helper
with `idJ` — the J and the strict recursor of the identity type. -/
theorem idStrictRecDependentReducibleMember {scope : Nat}
    (resultCandidate : RawTerm scope → Prop)
    (headExpand : ∀ {redexTerm contractum : RawTerm scope},
        WeakHeadStep redexTerm contractum → resultCandidate contractum →
        IsStronglyNormalizing redexTerm → resultCandidate redexTerm)
    (memberOfStronglyNormalizingNeutral :
      ∀ {neutralTerm : RawTerm scope},
        IsStronglyNormalizing neutralTerm → IsNeutral neutralTerm → resultCandidate neutralTerm)
    {motive : RawTerm (scope + 2)} {scrutinee baseCase : RawTerm scope}
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (baseCaseStronglyNormalizing : IsStronglyNormalizing baseCase)
    (scrutineeMember : dataTaitCandidate isReflValue scrutinee)
    (baseCaseMemberIfReachesRefl : ∀ witness : RawTerm scope,
        StepStar scrutinee (reflCell witness) → resultCandidate baseCase) :
    resultCandidate
      (.mkGen .gen_idStrictRec ()
        (.childCons motive (.childCons baseCase (.childCons scrutinee .childNil)))) :=
  dependentDataEliminatorMemberFromValueDispatch
    (isValue := isReflConstructorHead)
    (scrutineeCandidate := dataTaitCandidate isReflValue)
    (elimSpine := fun focus =>
      .mkGen .gen_idStrictRec () (.childCons motive (.childCons baseCase (.childCons focus .childNil))))
    (focusTrichotomy := fun focusMember =>
      dataTaitFocusTrichotomyOfValueHead
        (valueHead := isReflValueHead) (candidateValue := isReflValue)
        (conclusionValue := isReflConstructorHead)
        (fun valueIsRefl => isReflValueHead_ofIsReflValue valueIsRefl)
        (fun rootIsRefl => isReflConstructorHead_ofValueHead rootIsRefl)
        focusMember)
    (candidateStronglyNormalizing := fun focusMember => focusMember.stronglyNormalizing)
    (candidateClosedUnderStep := fun focusMember step => focusMember.closedUnderStep step)
    (spineStronglyNormalizing := fun focusStronglyNormalizing =>
      idStrictRec_isStronglyNormalizing_of_strongly_normalizing_base motiveStronglyNormalizing
        baseCaseStronglyNormalizing focusStronglyNormalizing)
    (spineScrutineeCongruence := fun focusWeakHead => WeakHeadStep.scrutineeIdStrictRec focusWeakHead)
    (spineNeutral := fun focusNeutral => IsNeutral.idStrictRec focusNeutral)
    (headExpand := headExpand)
    (memberOfStronglyNormalizingNeutral := memberOfStronglyNormalizingNeutral)
    (valueHandler := fun focusIsConstructorHead reaches cellStronglyNormalizing => by
      obtain ⟨witness, focusIsRefl⟩ := focusIsConstructorHead
      subst focusIsRefl
      exact headExpand IotaHeadStep.iotaIdStrictRecRefl.toWeakHeadStep
        (baseCaseMemberIfReachesRefl witness reaches) cellStronglyNormalizing)
    (scrutineeMember := scrutineeMember)

end FX1Poly.Core

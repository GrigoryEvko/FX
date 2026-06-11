import FX1Poly.Typed.KernelBinaryParametricity

/-! # FX1Poly/Typed/KernelBinaryMemberSN
    — ★ BINARY CR1: every related member pair is a pair of strongly normalizing terms (OP1-K2)

The CR1 shadow of the INHABITATION WALL, closed BY CONSTRUCTION.  The unary CR1 ("members of
a reducible type are SN") was proven via neutral inhabitation (OB-1: apply the member's Π
candidate at the variable-0 neutral).  Binary neutral-pair inhabitation is FALSE (the wall,
rung 64), so binary CR1 cannot be proven that way — and with the ORIGINAL naked `piType`
member candidate it was simply FALSE: over an uninhabited domain relation the Π candidate's
∀-quantification is vacuous, so non-SN pairs like `(Omega, Omega)` qualified.  The candidate
strengthening (this campaign rung: per-side `IsStronglyNormalizing` conjuncts baked into the
`piType` member candidate, the standard binary-logical-relations construction) makes every
arm's candidate carry or imply its members' SN:

  * `neutral` — the SN-product candidate, literally;
  * `piType` — the NEW conjuncts (the strengthening);
  * `universeCode` — `binaryUniverseDenotePredicate`'s leading SN conjuncts (before the
    below-family decode, so no level gate is needed);
  * `dataEmpty` / `dataFlat` — the unary Tait candidates' own SN
    (`emptyTaitCandidate.stronglyNormalizing` / `dataTaitCandidate.stronglyNormalizing`);
  * `whnfExpand*` / `ofPointwiseIff` — recursion (+ the pointwise transport).

Consequence for the FT assembly: brick 2's `binaryFundamentalPiIntroArm` premise
`domainArgumentsSN` is now DISCHARGEABLE for every domain shape — no wall premise needed for
argument SN.  Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- ★ **Binary CR1 at the step functor** (parametric in `lowerAt`): every member pair of every
candidate the binary relation assigns is a pair of strongly normalizing terms — one 8-arm
induction, each arm reading the SN content its candidate carries by construction. -/
theorem BinaryReducibleTypeStepBounded.memberPairStronglyNormalizing {scope : Nat}
    {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    {leftCode rightCode : RawTerm scope} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation) :
    ∀ {leftMember rightMember : RawTerm scope}, relation leftMember rightMember →
      IsStronglyNormalizing leftMember ∧ IsStronglyNormalizing rightMember := by
  induction related with
  | whnfExpandLeft _weakHeadStep _reductRelated reductIH =>
      exact reductIH
  | whnfExpandRight _weakHeadStep _reductRelated reductIH =>
      exact reductIH
  | neutral _ _ _ _ _ _ _ _ _ _ =>
      intro _leftMember _rightMember membership
      exact membership
  | piType _codomainRelation _domainsRelated _codomainsRelated _domainIH _codomainIH =>
      intro _leftMember _rightMember membership
      exact ⟨membership.1, membership.2.1⟩
  | universeCode _levelExpr _flag _belowBound =>
      intro _leftMember _rightMember membership
      exact ⟨membership.1, membership.2.1⟩
  | dataEmpty =>
      intro _leftMember _rightMember membership
      exact ⟨membership.1.stronglyNormalizing, membership.2.stronglyNormalizing⟩
  | dataFlat _flatPinned _headsAgree =>
      intro _leftMember _rightMember membership
      exact ⟨membership.1.stronglyNormalizing, membership.2.1.stronglyNormalizing⟩
  | ofPointwiseIff _innerRelated pointwiseIff innerIH =>
      intro leftMember rightMember membership
      exact innerIH ((pointwiseIff leftMember rightMember).mpr membership)

/-- ★ **Binary CR1 (member-pair level)**: every binary-reducible member pair is SN on both
sides — the brick that discharges the piIntro arm's `domainArgumentsSN` premise at assembly,
for EVERY domain shape. -/
theorem binaryMemberPairStronglyNormalizingAtBounded {scope : Nat} {env : Nat → Nat}
    {bound : Nat} {leftType rightType leftMember rightMember : RawTerm scope}
    (memberPair : IsBinaryReducibleMemberPairAtBounded env bound leftType rightType
      leftMember rightMember) :
    IsStronglyNormalizing leftMember ∧ IsStronglyNormalizing rightMember := by
  obtain ⟨relation, typesRelated, membersInRelation⟩ := memberPair
  exact typesRelated.memberPairStronglyNormalizing membersInRelation

end FX1Poly.Typed

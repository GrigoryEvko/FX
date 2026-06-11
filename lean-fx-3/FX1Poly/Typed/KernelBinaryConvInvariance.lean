import FX1Poly.Typed.KernelBinaryPiIntro

/-! # FX1Poly/Typed/KernelBinaryConvInvariance
    — binary forward closure + Conv-invariance: convertible pairs share their candidate (OP1-K2 brick 3)

The conv-arm substrate of the binary fundamental theorem.  The unary conv transfer rode the
forget bridge ("a fact about candidates"); the binary machinery is once more DIRECT, but the
payoff is the same load-bearing fact: **the binary candidate is an invariant of the Conv-class
PAIR** — convertible type pairs have pointwise-equivalent binary candidates, so member pairs
transport along conversions of their types.

  * `whnfExpandClosureLeft` / `Right` — multi-step weak-head-expansion closure on one side
    (the `commuteWithStep` race between the chain and the peeled weak-head step, per side).
  * ★ `forwardStepStarLeft` / `Right` — forward closure: a related pair stays related at the
    SAME candidate when either side reduces (neutral and flat arms ride
    `weakHeadNormalRootStableAlongStepStar`; the Π arm decomposes the chain into child chains
    and pushes the codomain chain through `subst0`), plus the `forwardStepStarPair` corollary
    and single-step forms.
  * ★ `binaryConvCandidateIff` — **binary Conv-invariance**: two related pairs whose
    components are componentwise convertible have pointwise-equivalent candidates (join at
    the common reducts, forward both derivations, align by brick-1 determinism).
  * ★ `IsBinaryReducibleMemberPairAtBounded.convTransport` (+ the closing-substitution form
    `convMemberPairUnderClosingSubstitutionBounded` via `Conv.subst`) — the member-pair
    transport every conv FT arm consumes.

Honest scope: the FT-shaped conv arm additionally needs the binary universe-membership
extraction (type-pair reducibility out of a binary universe member + the gate extraction);
that rides with the assembly brick, which threads it from the universeFormation IHs.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-! ## One-sided multi-step weak-head-expansion closure -/

/-- Multi-step weak-head-expansion closure on the LEFT (port of `whnfExpandClosure`): the
race between a left chain and a peeled left weak-head step, resolved by
`WeakHeadStep.commuteWithStep`. -/
theorem BinaryReducibleTypeStepBounded.whnfExpandClosureLeft {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    {rightCode : RawTerm scope} {relation : BinaryCandidate scope} :
    ∀ {firstLeft finalLeft : RawTerm scope}, StepStar firstLeft finalLeft →
      ∀ {leftWeakHeadReduct : RawTerm scope}, WeakHeadStep firstLeft leftWeakHeadReduct →
        BinaryReducibleTypeStepBounded env lowerAt bound leftWeakHeadReduct rightCode relation →
        (∀ furtherReduct : RawTerm scope, StepStar leftWeakHeadReduct furtherReduct →
          BinaryReducibleTypeStepBounded env lowerAt bound furtherReduct rightCode relation) →
        BinaryReducibleTypeStepBounded env lowerAt bound finalLeft rightCode relation := by
  intro firstLeft finalLeft chain
  induction chain with
  | refl _ =>
      intro leftWeakHeadReduct weakHeadStep reductRelated _laterClosure
      exact BinaryReducibleTypeStepBounded.whnfExpandLeft weakHeadStep reductRelated
  | trans firstStep _restChain restClosure =>
      intro leftWeakHeadReduct weakHeadStep reductRelated laterClosure
      rcases weakHeadStep.commuteWithStep _ firstStep with
        midEquation | ⟨_laterReduct, laterWeakHeadStep, catchUpChain⟩
      · subst midEquation
        exact laterClosure _ _restChain
      · exact restClosure laterWeakHeadStep (laterClosure _ catchUpChain)
          (fun furtherReduct furtherChain =>
            laterClosure furtherReduct (StepStar.trans_compose catchUpChain furtherChain))

/-- Multi-step weak-head-expansion closure on the RIGHT (mirror). -/
theorem BinaryReducibleTypeStepBounded.whnfExpandClosureRight {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    {leftCode : RawTerm scope} {relation : BinaryCandidate scope} :
    ∀ {firstRight finalRight : RawTerm scope}, StepStar firstRight finalRight →
      ∀ {rightWeakHeadReduct : RawTerm scope}, WeakHeadStep firstRight rightWeakHeadReduct →
        BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightWeakHeadReduct relation →
        (∀ furtherReduct : RawTerm scope, StepStar rightWeakHeadReduct furtherReduct →
          BinaryReducibleTypeStepBounded env lowerAt bound leftCode furtherReduct relation) →
        BinaryReducibleTypeStepBounded env lowerAt bound leftCode finalRight relation := by
  intro firstRight finalRight chain
  induction chain with
  | refl _ =>
      intro rightWeakHeadReduct weakHeadStep reductRelated _laterClosure
      exact BinaryReducibleTypeStepBounded.whnfExpandRight weakHeadStep reductRelated
  | trans firstStep _restChain restClosure =>
      intro rightWeakHeadReduct weakHeadStep reductRelated laterClosure
      rcases weakHeadStep.commuteWithStep _ firstStep with
        midEquation | ⟨_laterReduct, laterWeakHeadStep, catchUpChain⟩
      · subst midEquation
        exact laterClosure _ _restChain
      · exact restClosure laterWeakHeadStep (laterClosure _ catchUpChain)
          (fun furtherReduct furtherChain =>
            laterClosure furtherReduct (StepStar.trans_compose catchUpChain furtherChain))

/-! ## ★ One-sided forward closure (same candidate) -/

/-- ★ **Forward closure on the LEFT**: a related pair stays related at the SAME binary
candidate when the left code reduces (port of `forwardStepStar`: neutral and flat arms ride
root-stability; the Π arm decomposes the chain into child chains, pushing the codomain chain
through `subst0`; universe/empty codes are step-rigid). -/
theorem BinaryReducibleTypeStepBounded.forwardStepStarLeft {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    {leftCode rightCode : RawTerm scope} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation) :
    ∀ {finalLeft : RawTerm scope}, StepStar leftCode finalLeft →
      BinaryReducibleTypeStepBounded env lowerAt bound finalLeft rightCode relation := by
  induction related with
  | whnfExpandLeft weakHeadStep reductRelated reductIH =>
      intro finalLeft chain
      exact BinaryReducibleTypeStepBounded.whnfExpandClosureLeft chain weakHeadStep
        reductRelated (fun _furtherReduct furtherChain => reductIH furtherChain)
  | whnfExpandRight weakHeadStep _reductRelated reductIH =>
      intro finalLeft chain
      exact BinaryReducibleTypeStepBounded.whnfExpandRight weakHeadStep (reductIH chain)
  | neutral noStepLeft noStepRight notPiLeft notUniverseLeft notEmptyLeft notFlatLeft
      notPiRight notUniverseRight notEmptyRight notFlatRight =>
      intro finalLeft chain
      obtain ⟨finalNoStep, rootEquation⟩ :=
        WeakHeadStep.weakHeadNormalRootStableAlongStepStar chain noStepLeft
      exact BinaryReducibleTypeStepBounded.neutral finalNoStep noStepRight
        (fun rootIsPi => notPiLeft (rootEquation.symm.trans rootIsPi))
        (fun rootIsUniverse => notUniverseLeft (rootEquation.symm.trans rootIsUniverse))
        (fun rootIsEmpty => notEmptyLeft (rootEquation.symm.trans rootIsEmpty))
        ((congrArg Generator.isFlatDataCode rootEquation).trans notFlatLeft)
        notPiRight notUniverseRight notEmptyRight notFlatRight
  | piType codomainRelation _domainsRelated _codomainsRelated domainIH codomainIH =>
      intro finalLeft chain
      obtain ⟨_updatedDomain, _updatedCodomain, finalEquation, domainChain, codomainChain⟩ :=
        StepStar.piTyCode_decompose chain
      subst finalEquation
      exact BinaryReducibleTypeStepBounded.piType codomainRelation (domainIH domainChain)
        (fun leftArgument rightArgument argumentsRelated =>
          codomainIH leftArgument rightArgument argumentsRelated
            (StepStar.subst0Body leftArgument codomainChain))
  | universeCode levelExpr flag belowBound =>
      intro finalLeft chain
      have finalEquation :=
        StepStar.eq_of_noStep
          (fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step) chain
      subst finalEquation
      exact BinaryReducibleTypeStepBounded.universeCode levelExpr flag belowBound
  | dataEmpty =>
      intro finalLeft chain
      have finalEquation :=
        StepStar.eq_of_noStep (fun reduct step => emptyTypeCell_noStep reduct step) chain
      subst finalEquation
      exact BinaryReducibleTypeStepBounded.dataEmpty
  | @dataFlat leftCode rightCode flatPinned headsAgree =>
      intro finalLeft chain
      obtain ⟨_finalNoStep, rootEquation⟩ :=
        WeakHeadStep.weakHeadNormalRootStableAlongStepStar chain
          (noWeakHeadStep_of_isFlatDataCode flatPinned)
      have finalRelated := BinaryReducibleTypeStepBounded.dataFlat (env := env)
        (lowerAt := lowerAt) (bound := bound) (rightCode := rightCode)
        ((congrArg Generator.isFlatDataCode rootEquation).trans flatPinned)
        (headsAgree.trans rootEquation.symm)
      rw [rootEquation] at finalRelated
      exact finalRelated
  | ofPointwiseIff _innerRelated pointwiseIff innerIH =>
      intro finalLeft chain
      exact (innerIH chain).ofPointwiseIff pointwiseIff

/-- ★ **Forward closure on the RIGHT** (mirror). -/
theorem BinaryReducibleTypeStepBounded.forwardStepStarRight {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    {leftCode rightCode : RawTerm scope} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation) :
    ∀ {finalRight : RawTerm scope}, StepStar rightCode finalRight →
      BinaryReducibleTypeStepBounded env lowerAt bound leftCode finalRight relation := by
  induction related with
  | whnfExpandLeft weakHeadStep _reductRelated reductIH =>
      intro finalRight chain
      exact BinaryReducibleTypeStepBounded.whnfExpandLeft weakHeadStep (reductIH chain)
  | whnfExpandRight weakHeadStep reductRelated reductIH =>
      intro finalRight chain
      exact BinaryReducibleTypeStepBounded.whnfExpandClosureRight chain weakHeadStep
        reductRelated (fun _furtherReduct furtherChain => reductIH furtherChain)
  | neutral noStepLeft noStepRight notPiLeft notUniverseLeft notEmptyLeft notFlatLeft
      notPiRight notUniverseRight notEmptyRight notFlatRight =>
      intro finalRight chain
      obtain ⟨finalNoStep, rootEquation⟩ :=
        WeakHeadStep.weakHeadNormalRootStableAlongStepStar chain noStepRight
      exact BinaryReducibleTypeStepBounded.neutral noStepLeft finalNoStep
        notPiLeft notUniverseLeft notEmptyLeft notFlatLeft
        (fun rootIsPi => notPiRight (rootEquation.symm.trans rootIsPi))
        (fun rootIsUniverse => notUniverseRight (rootEquation.symm.trans rootIsUniverse))
        (fun rootIsEmpty => notEmptyRight (rootEquation.symm.trans rootIsEmpty))
        ((congrArg Generator.isFlatDataCode rootEquation).trans notFlatRight)
  | piType codomainRelation _domainsRelated _codomainsRelated domainIH codomainIH =>
      intro finalRight chain
      obtain ⟨_updatedDomain, _updatedCodomain, finalEquation, domainChain, codomainChain⟩ :=
        StepStar.piTyCode_decompose chain
      subst finalEquation
      exact BinaryReducibleTypeStepBounded.piType codomainRelation (domainIH domainChain)
        (fun leftArgument rightArgument argumentsRelated =>
          codomainIH leftArgument rightArgument argumentsRelated
            (StepStar.subst0Body rightArgument codomainChain))
  | universeCode levelExpr flag belowBound =>
      intro finalRight chain
      have finalEquation :=
        StepStar.eq_of_noStep
          (fun _reduct step => StepStar.noStep_universeCode (levelExpr, flag) step) chain
      subst finalEquation
      exact BinaryReducibleTypeStepBounded.universeCode levelExpr flag belowBound
  | dataEmpty =>
      intro finalRight chain
      have finalEquation :=
        StepStar.eq_of_noStep (fun reduct step => emptyTypeCell_noStep reduct step) chain
      subst finalEquation
      exact BinaryReducibleTypeStepBounded.dataEmpty
  | @dataFlat leftCode rightCode flatPinned headsAgree =>
      intro finalRight chain
      obtain ⟨_finalNoStep, rootEquation⟩ :=
        WeakHeadStep.weakHeadNormalRootStableAlongStepStar chain
          (noWeakHeadStep_of_isFlatDataCode (headsAgree ▸ flatPinned))
      exact BinaryReducibleTypeStepBounded.dataFlat flatPinned
        (rootEquation.trans headsAgree)
  | ofPointwiseIff _innerRelated pointwiseIff innerIH =>
      intro finalRight chain
      exact (innerIH chain).ofPointwiseIff pointwiseIff

/-- Forward closure on BOTH sides — the pair corollary. -/
theorem BinaryReducibleTypeStepBounded.forwardStepStarPair {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    {leftCode rightCode finalLeft finalRight : RawTerm scope}
    {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation)
    (leftChain : StepStar leftCode finalLeft) (rightChain : StepStar rightCode finalRight) :
    BinaryReducibleTypeStepBounded env lowerAt bound finalLeft finalRight relation :=
  (related.forwardStepStarLeft leftChain).forwardStepStarRight rightChain

/-! ## ★ Binary Conv-invariance: the candidate is an invariant of the Conv-class pair -/

/-- ★ **Binary Conv-invariance**: two related pairs whose components are componentwise
convertible have pointwise-equivalent binary candidates — join at the common reducts, forward
both derivations there (same candidates), and align by determinism (brick 1).  The
load-bearing fact behind the conv FT arm: the binary candidate depends only on the Conv-class
PAIR of the type codes. -/
theorem binaryConvCandidateIff {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {leftCode rightCode leftCodePrimed rightCodePrimed : RawTerm scope}
    {relation relationPrimed : BinaryCandidate scope}
    (related : BinaryReducibleTypeAtBounded env bound leftCode rightCode relation)
    (relatedPrimed : BinaryReducibleTypeAtBounded env bound
      leftCodePrimed rightCodePrimed relationPrimed)
    (leftConverts : Conv leftCode leftCodePrimed)
    (rightConverts : Conv rightCode rightCodePrimed) :
    BinaryPointwiseIff relation relationPrimed := by
  obtain ⟨leftCommon, leftChain, leftPrimedChain⟩ := leftConverts
  obtain ⟨rightCommon, rightChain, rightPrimedChain⟩ := rightConverts
  exact BinaryReducibleTypeAtBounded.deterministic
    (related.forwardStepStarPair leftChain rightChain)
    (relatedPrimed.forwardStepStarPair leftPrimedChain rightPrimedChain)

/-- ★ **Member-pair transport along Conv**: a member pair of a related type pair is a member
pair of any componentwise-CONVERTIBLE related type pair — the conv FT arm's engine. -/
theorem IsBinaryReducibleMemberPairAtBounded.convTransport {scope : Nat} {env : Nat → Nat}
    {bound : Nat} {leftCode rightCode leftCodePrimed rightCodePrimed : RawTerm scope}
    {leftMember rightMember : RawTerm scope}
    (memberPair : IsBinaryReducibleMemberPairAtBounded env bound leftCode rightCode
      leftMember rightMember)
    (primedPairRelated : IsBinaryReducibleTypePairAtBounded env bound
      leftCodePrimed rightCodePrimed)
    (leftConverts : Conv leftCode leftCodePrimed)
    (rightConverts : Conv rightCode rightCodePrimed) :
    IsBinaryReducibleMemberPairAtBounded env bound leftCodePrimed rightCodePrimed
      leftMember rightMember := by
  obtain ⟨relation, related, membersInRelation⟩ := memberPair
  obtain ⟨relationPrimed, relatedPrimed⟩ := primedPairRelated
  exact ⟨relationPrimed, relatedPrimed,
    (binaryConvCandidateIff related relatedPrimed leftConverts rightConverts
      leftMember rightMember).mp membersInRelation⟩

/-- The member-pair Conv transport under a closing-substitution pair (the FT shape): a single
source-level `Conv subjectClassifier reclassifier` pushes through BOTH substitutions via
`Conv.subst`. -/
theorem convMemberPairUnderClosingSubstitutionBounded {scope targetScope : Nat}
    (env : Nat → Nat) (bound : Nat)
    {subjectClassifier reclassifier subject : RawTerm scope}
    {leftSubstitution rightSubstitution : RawTermSubst scope targetScope}
    (memberPair : IsBinaryReducibleMemberPairAtBounded env bound
      (RawTerm.subst leftSubstitution subjectClassifier)
      (RawTerm.subst rightSubstitution subjectClassifier)
      (RawTerm.subst leftSubstitution subject) (RawTerm.subst rightSubstitution subject))
    (reclassifierPairRelated : IsBinaryReducibleTypePairAtBounded env bound
      (RawTerm.subst leftSubstitution reclassifier)
      (RawTerm.subst rightSubstitution reclassifier))
    (converts : Conv subjectClassifier reclassifier) :
    IsBinaryReducibleMemberPairAtBounded env bound
      (RawTerm.subst leftSubstitution reclassifier)
      (RawTerm.subst rightSubstitution reclassifier)
      (RawTerm.subst leftSubstitution subject) (RawTerm.subst rightSubstitution subject) :=
  memberPair.convTransport reclassifierPairRelated
    (Conv.subst leftSubstitution converts) (Conv.subst rightSubstitution converts)

end FX1Poly.Typed

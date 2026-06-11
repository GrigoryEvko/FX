import FX1Poly.Typed.KernelBinaryParametricity
import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Core.RawTermSubst0Commute

/-! # FX1Poly/Typed/KernelBinaryPiElim
    — binary determinism + the Π-ELIMINATION pair arm + the binary FT motive (OP1-K2 brick 1)

The first OP1-K2 brick over the K1 relation: everything the binary fundamental theorem's
APPLICATION case needs, mirroring the unary `DenoteKeyedBoundedPiElimArm` chain — with the one
structural novelty the unary did not have: the unary `deterministic` transferred through the
bounded-to-denote forget bridge, but the binary relation has NO denote twin, so determinism is
a DIRECT double induction here, built on per-shape candidate-identification lemmas exactly like
the denote original.

  * `candidateAtWhnfReductLeft` / `Right` — one-sided weak-head factoring: a derivation whose
    left (right) code weak-head-steps re-derives at the reduct with the SAME candidate.  The
    novelty vs the unary: the OPPOSITE side's expansions commute past the factoring (re-wrap).
  * `binaryCandidateIffStronglyNormalizingPair` / `binaryCandidateIffUniverse` /
    `binaryCandidateIffEmptyCandidate` / `binaryCandidateIffFlatCandidate` — the per-shape
    candidate identifications (the determinism leaves), each keyed on BOTH indices.
  * `candidatePiPairShape` / `piTypePairInversion` — the Π-PAIR inversion: a derivation at two
    `gen_piTyCode`-rooted codes came through the `piType` arm; recovers the domain relation,
    the related-argument-indexed codomain family, and the application-form `BinaryPointwiseIff`.
  * ★ `BinaryReducibleTypeStepBounded.deterministic` — the binary relation is FUNCTIONAL: two
    derivations at the same PAIR have pointwise-equivalent binary candidates.  The alignment
    every elimination arm needs.
  * ★ `applicationMemberPairAtBounded` + the closing-substitution form — the Π-ELIMINATION
    member arm: a related function pair applied to a related argument pair is a related pair
    at the substituted dependent codomains (both sides commute by `subst0_subst_commute`).
  * ★ `BinaryFundamentalConclusionAtBounded` — THE binary fundamental-theorem motive: related
    closing-substitution pairs take the subject's two closures to a related member pair at the
    classifier's two closures.
  * `binaryFundamentalVarArm` / ★ `binaryFundamentalPiElimArm` — the var and application FT
    arms in motive form (the leaf is the environment lookup; the application arm composes the
    member arm with both sub-conclusions).

Honest scope (the K2 brick split): the piIntro (binder) arm needs the binary env cons + the
two-sided β-expansion closure; the conv arm needs binary Conv-invariance; the former arms need
the binary telescope — all later K2 bricks.  This brick is the complete ELIMINATION leg.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-! ## One-sided weak-head factoring -/

/-- **Left weak-head peel**: a binary derivation whose LEFT code weak-head-steps re-derives at
the left reduct with the SAME candidate.  Right-side expansions commute past the peel (re-wrap
in the `whnfExpandRight` arm); the remaining arms' left indices are weak-head-normal. -/
theorem BinaryReducibleTypeStepBounded.candidateAtWhnfReductLeft {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    {leftCode rightCode : RawTerm scope} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation) :
    ∀ {leftReduct : RawTerm scope}, WeakHeadStep leftCode leftReduct →
      BinaryReducibleTypeStepBounded env lowerAt bound leftReduct rightCode relation := by
  induction related with
  | whnfExpandLeft weakHeadStep0 reductRelated0 _ =>
      intro leftReduct weakHeadStep
      have reductEquation := WeakHeadStep.deterministic weakHeadStep0 weakHeadStep
      subst reductEquation
      exact reductRelated0
  | whnfExpandRight rightStep _innerRelated ih =>
      intro leftReduct weakHeadStep
      exact BinaryReducibleTypeStepBounded.whnfExpandRight rightStep (ih weakHeadStep)
  | neutral noStepLeft _ _ _ _ _ _ _ _ _ =>
      intro leftReduct weakHeadStep
      exact absurd weakHeadStep (noStepLeft leftReduct)
  | piType _ _ _ _ _ =>
      intro leftReduct weakHeadStep
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep
  | universeCode _ _ _ =>
      intro leftReduct weakHeadStep
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep
  | dataEmpty =>
      intro leftReduct weakHeadStep
      exact absurd weakHeadStep (emptyTypeCell_noWeakHeadStep leftReduct)
  | dataFlat flatPinned _headsAgree =>
      intro leftReduct weakHeadStep
      exact absurd weakHeadStep (noWeakHeadStep_of_isFlatDataCode flatPinned leftReduct)
  | ofPointwiseIff _innerRelated pointwiseIff ih =>
      intro leftReduct weakHeadStep
      exact .ofPointwiseIff (ih weakHeadStep) pointwiseIff

/-- **Right weak-head peel** — the mirror of `candidateAtWhnfReductLeft`.  The `dataFlat` arm
routes the head agreement through to the right side. -/
theorem BinaryReducibleTypeStepBounded.candidateAtWhnfReductRight {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    {leftCode rightCode : RawTerm scope} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation) :
    ∀ {rightReduct : RawTerm scope}, WeakHeadStep rightCode rightReduct →
      BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightReduct relation := by
  induction related with
  | whnfExpandLeft leftStep _innerRelated ih =>
      intro rightReduct weakHeadStep
      exact BinaryReducibleTypeStepBounded.whnfExpandLeft leftStep (ih weakHeadStep)
  | whnfExpandRight weakHeadStep0 reductRelated0 _ =>
      intro rightReduct weakHeadStep
      have reductEquation := WeakHeadStep.deterministic weakHeadStep0 weakHeadStep
      subst reductEquation
      exact reductRelated0
  | neutral _ noStepRight _ _ _ _ _ _ _ _ =>
      intro rightReduct weakHeadStep
      exact absurd weakHeadStep (noStepRight rightReduct)
  | piType _ _ _ _ _ =>
      intro rightReduct weakHeadStep
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep
  | universeCode _ _ _ =>
      intro rightReduct weakHeadStep
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep
  | dataEmpty =>
      intro rightReduct weakHeadStep
      exact absurd weakHeadStep (emptyTypeCell_noWeakHeadStep rightReduct)
  | dataFlat flatPinned headsAgree =>
      intro rightReduct weakHeadStep
      have rightFlat : _ := headsAgree ▸ flatPinned
      exact absurd weakHeadStep (noWeakHeadStep_of_isFlatDataCode rightFlat rightReduct)
  | ofPointwiseIff _innerRelated pointwiseIff ih =>
      intro rightReduct weakHeadStep
      exact .ofPointwiseIff (ih weakHeadStep) pointwiseIff

/-! ## Per-shape candidate identifications (the determinism leaves) -/

/-- A weak-head-normal pair whose heads pass all eight gates has the SN-product candidate. -/
theorem BinaryReducibleTypeStepBounded.binaryCandidateIffStronglyNormalizingPair {scope : Nat}
    {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    {leftCode rightCode : RawTerm scope} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation) :
    (∀ reduct : RawTerm scope, ¬ WeakHeadStep leftCode reduct) →
    (∀ reduct : RawTerm scope, ¬ WeakHeadStep rightCode reduct) →
    leftCode.rootGenerator ≠ Generator.gen_piTyCode →
    leftCode.rootGenerator ≠ Generator.gen_universeCode →
    leftCode.rootGenerator ≠ Generator.gen_emptyCode →
    leftCode.rootGenerator.isFlatDataCode = false →
    rightCode.rootGenerator ≠ Generator.gen_piTyCode →
    rightCode.rootGenerator ≠ Generator.gen_universeCode →
    rightCode.rootGenerator ≠ Generator.gen_emptyCode →
    rightCode.rootGenerator.isFlatDataCode = false →
    BinaryPointwiseIff relation
      (fun leftTerm rightTerm =>
        IsStronglyNormalizing leftTerm ∧ IsStronglyNormalizing rightTerm) := by
  induction related with
  | whnfExpandLeft weakHeadStep0 _ _ =>
      intro noStepLeft _ _ _ _ _ _ _ _ _
      exact absurd weakHeadStep0 (noStepLeft _)
  | whnfExpandRight weakHeadStep0 _ _ =>
      intro _ noStepRight _ _ _ _ _ _ _ _
      exact absurd weakHeadStep0 (noStepRight _)
  | neutral _ _ _ _ _ _ _ _ _ _ =>
      intro _ _ _ _ _ _ _ _ _ _
      exact fun _ _ => Iff.rfl
  | piType _ _ _ _ _ =>
      intro _ _ notPiLeft _ _ _ _ _ _ _
      exact absurd rfl notPiLeft
  | universeCode _ _ _ =>
      intro _ _ _ notUniverseLeft _ _ _ _ _ _
      exact absurd rfl notUniverseLeft
  | dataEmpty =>
      intro _ _ _ _ notEmptyLeft _ _ _ _ _
      exact absurd rfl notEmptyLeft
  | dataFlat flatPinned _headsAgree =>
      intro _ _ _ _ _ notFlatLeft _ _ _ _
      exact nomatch notFlatLeft.symm.trans flatPinned
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro noStepLeft noStepRight notPiLeft notUniverseLeft notEmptyLeft notFlatLeft
        notPiRight notUniverseRight notEmptyRight notFlatRight
      intro leftTerm rightTerm
      exact (pointwiseIff leftTerm rightTerm).symm.trans
        (innerHypothesis noStepLeft noStepRight notPiLeft notUniverseLeft notEmptyLeft
          notFlatLeft notPiRight notUniverseRight notEmptyRight notFlatRight leftTerm rightTerm)

/-- A pair of universe codes has the binary universe candidate at the LEFT code's level (the
arms pin equal payloads, so the left equation suffices to align the level). -/
theorem BinaryReducibleTypeStepBounded.binaryCandidateIffUniverse {scope : Nat}
    {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    {leftCode rightCode : RawTerm scope} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation) :
    ∀ {levelExpr levelExprRight : LevelExpr} {flag flagRight : UniverseFlag},
      leftCode = (.mkGen .gen_universeCode (levelExpr, flag) .childNil) →
      rightCode = (.mkGen .gen_universeCode (levelExprRight, flagRight) .childNil) →
      BinaryPointwiseIff relation (binaryUniverseDenotePredicate env lowerAt levelExpr) := by
  induction related with
  | whnfExpandLeft weakHeadStep0 _ _ =>
      intro _ _ _ _ leftEq _rightEq; subst leftEq
      cases weakHeadStep0 with | rootIota iotaStep => cases iotaStep
  | whnfExpandRight weakHeadStep0 _ _ =>
      intro _ _ _ _ _leftEq rightEq; subst rightEq
      cases weakHeadStep0 with | rootIota iotaStep => cases iotaStep
  | neutral _ _ _ notUniverseLeft _ _ _ _ _ _ =>
      intro _ _ _ _ leftEq _rightEq; subst leftEq
      exact absurd rfl notUniverseLeft
  | piType _ _ _ _ _ =>
      intro _ _ _ _ leftEq _rightEq
      have rootMismatch : Generator.gen_piTyCode = Generator.gen_universeCode :=
        congrArg RawTerm.rootGenerator leftEq
      exact absurd rootMismatch (by decide)
  | universeCode armLevelExpr armFlag _belowBound =>
      intro _ _ _ _ leftEq _rightEq
      obtain ⟨levelEq, _flagEq⟩ := universeCodeCell_inj leftEq
      subst levelEq
      exact fun _ _ => Iff.rfl
  | dataEmpty =>
      intro _ _ _ _ leftEq _rightEq
      have rootMismatch : Generator.gen_emptyCode = Generator.gen_universeCode :=
        congrArg RawTerm.rootGenerator leftEq
      exact absurd rootMismatch (by decide)
  | dataFlat flatPinned _headsAgree =>
      intro _ _ _ _ leftEq _rightEq
      rw [leftEq] at flatPinned
      exact nomatch flatPinned
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro _ _ _ _ leftEq rightEq leftTerm rightTerm
      exact (pointwiseIff leftTerm rightTerm).symm.trans
        (innerHypothesis leftEq rightEq leftTerm rightTerm)

/-- A pair of empty-type codes has the binary empty candidate. -/
theorem BinaryReducibleTypeStepBounded.binaryCandidateIffEmptyCandidate {scope : Nat}
    {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    {leftCode rightCode : RawTerm scope} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation) :
    leftCode = emptyTypeCell (scope := scope) → rightCode = emptyTypeCell (scope := scope) →
    BinaryPointwiseIff relation binaryEmptyCandidate := by
  induction related with
  | whnfExpandLeft weakHeadStep0 _ _ =>
      intro leftEq _rightEq; subst leftEq
      exact absurd weakHeadStep0 (emptyTypeCell_noWeakHeadStep _)
  | whnfExpandRight weakHeadStep0 _ _ =>
      intro _leftEq rightEq; subst rightEq
      exact absurd weakHeadStep0 (emptyTypeCell_noWeakHeadStep _)
  | neutral _ _ _ _ notEmptyLeft _ _ _ _ _ =>
      intro leftEq _rightEq; subst leftEq
      exact absurd
        (rfl : (emptyTypeCell (scope := scope)).rootGenerator = Generator.gen_emptyCode)
        notEmptyLeft
  | piType _ _ _ _ _ =>
      intro leftEq _rightEq
      have rootMismatch : Generator.gen_piTyCode = Generator.gen_emptyCode :=
        congrArg RawTerm.rootGenerator leftEq
      exact absurd rootMismatch (by decide)
  | universeCode _ _ _ =>
      intro leftEq _rightEq
      have rootMismatch : Generator.gen_universeCode = Generator.gen_emptyCode :=
        congrArg RawTerm.rootGenerator leftEq
      exact absurd rootMismatch (by decide)
  | dataEmpty =>
      intro _leftEq _rightEq
      exact fun _ _ => Iff.rfl
  | dataFlat flatPinned _headsAgree =>
      intro leftEq _rightEq
      rw [leftEq] at flatPinned
      exact nomatch flatPinned
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro leftEq rightEq leftTerm rightTerm
      exact (pointwiseIff leftTerm rightTerm).symm.trans
        (innerHypothesis leftEq rightEq leftTerm rightTerm)

/-- A pair of same-headed flat data codes has the pinned same-value binary data candidate at
the LEFT code's value predicate. -/
theorem BinaryReducibleTypeStepBounded.binaryCandidateIffFlatCandidate {scope : Nat}
    {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    {leftCode rightCode : RawTerm scope} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation) :
    leftCode.rootGenerator.isFlatDataCode = true →
    rightCode.rootGenerator.isFlatDataCode = true →
    BinaryPointwiseIff relation
      (binaryDataCandidate (flatCodeValuePredicate leftCode.rootGenerator)) := by
  induction related with
  | whnfExpandLeft weakHeadStep0 _ _ =>
      intro flatLeft _flatRight
      exact absurd weakHeadStep0 (noWeakHeadStep_of_isFlatDataCode flatLeft _)
  | whnfExpandRight weakHeadStep0 _ _ =>
      intro _flatLeft flatRight
      exact absurd weakHeadStep0 (noWeakHeadStep_of_isFlatDataCode flatRight _)
  | neutral _ _ _ _ _ notFlatLeft _ _ _ _ =>
      intro flatLeft _flatRight
      exact nomatch notFlatLeft.symm.trans flatLeft
  | piType _ _ _ _ _ =>
      intro flatLeft _flatRight
      exact nomatch flatLeft
  | universeCode _ _ _ =>
      intro flatLeft _flatRight
      exact nomatch flatLeft
  | dataEmpty =>
      intro flatLeft _flatRight
      exact nomatch flatLeft
  | dataFlat _flatPinned _headsAgree =>
      intro _flatLeft _flatRight
      exact fun _ _ => Iff.rfl
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro flatLeft flatRight leftTerm rightTerm
      exact (pointwiseIff leftTerm rightTerm).symm.trans
        (innerHypothesis flatLeft flatRight leftTerm rightTerm)

/-! ## The Π-pair inversion -/

/-- **Π-pair shape inversion**: a derivation at two `gen_piTyCode`-rooted codes came through
the `piType` arm; recovers the domain relation, the related-argument-indexed codomain family,
and the application-form `BinaryPointwiseIff`. -/
theorem BinaryReducibleTypeStepBounded.candidatePiPairShape {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    {leftCode rightCode : RawTerm scope} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation) :
    ∀ {leftDomain rightDomain : RawTerm scope}
      {leftCodomain rightCodomain : RawTerm (scope + 1)},
      leftCode
        = (.mkGen .gen_piTyCode () (.childCons leftDomain (.childCons leftCodomain .childNil))) →
      rightCode
        = (.mkGen .gen_piTyCode () (.childCons rightDomain (.childCons rightCodomain .childNil))) →
      ∃ (leftDomainCandidate rightDomainCandidate : RawTerm scope → Prop)
        (domainRelation : BinaryCandidate scope)
        (codomainRelation : RawTerm scope → RawTerm scope → BinaryCandidate scope),
        ReducibleTypeAtBounded env bound leftDomain leftDomainCandidate ∧
        ReducibleTypeAtBounded env bound rightDomain rightDomainCandidate ∧
        BinaryReducibleTypeStepBounded env lowerAt bound leftDomain rightDomain domainRelation ∧
        (∀ leftArgument rightArgument : RawTerm scope,
          leftDomainCandidate leftArgument → rightDomainCandidate rightArgument →
          domainRelation leftArgument rightArgument →
          BinaryReducibleTypeStepBounded env lowerAt bound
            (RawTerm.subst0 leftCodomain leftArgument)
            (RawTerm.subst0 rightCodomain rightArgument)
            (codomainRelation leftArgument rightArgument)) ∧
        BinaryPointwiseIff relation
          (fun leftFunction rightFunction =>
            IsStronglyNormalizing leftFunction ∧ IsStronglyNormalizing rightFunction ∧
              ∀ leftArgument rightArgument : RawTerm scope,
                leftDomainCandidate leftArgument → rightDomainCandidate rightArgument →
                domainRelation leftArgument rightArgument →
                codomainRelation leftArgument rightArgument
                  (.mkGen .gen_app ()
                    (.childCons leftFunction (.childCons leftArgument .childNil)))
                  (.mkGen .gen_app ()
                    (.childCons rightFunction (.childCons rightArgument .childNil)))) := by
  induction related with
  | whnfExpandLeft weakHeadStep0 _ _ =>
      intro _ _ _ _ leftEq _rightEq; subst leftEq
      cases weakHeadStep0 with | rootIota iotaStep => cases iotaStep
  | whnfExpandRight weakHeadStep0 _ _ =>
      intro _ _ _ _ _leftEq rightEq; subst rightEq
      cases weakHeadStep0 with | rootIota iotaStep => cases iotaStep
  | neutral _ _ notPiLeft _ _ _ _ _ _ _ =>
      intro _ _ _ _ leftEq _rightEq; subst leftEq
      exact absurd rfl notPiLeft
  | piType codomainRelation leftDomainUnary rightDomainUnary domainsRelated codomainsRelated
      _ _ =>
      intro _ _ _ _ leftEq rightEq
      cases leftEq; cases rightEq
      exact ⟨_, _, _, codomainRelation, leftDomainUnary, rightDomainUnary, domainsRelated,
        codomainsRelated, fun _ _ => Iff.rfl⟩
  | universeCode _ _ _ =>
      intro _ _ _ _ leftEq _rightEq
      have rootMismatch : Generator.gen_universeCode = Generator.gen_piTyCode :=
        congrArg RawTerm.rootGenerator leftEq
      exact absurd rootMismatch (by decide)
  | dataEmpty =>
      intro _ _ _ _ leftEq _rightEq
      have rootMismatch : Generator.gen_emptyCode = Generator.gen_piTyCode :=
        congrArg RawTerm.rootGenerator leftEq
      exact absurd rootMismatch (by decide)
  | dataFlat flatPinned _headsAgree =>
      intro _ _ _ _ leftEq _rightEq
      rw [leftEq] at flatPinned
      exact nomatch flatPinned
  | ofPointwiseIff _ pointwiseIff innerHypothesis =>
      intro _ _ _ _ leftEq rightEq
      obtain ⟨leftDomainCandidate, rightDomainCandidate, domainRelation, codomainRelation,
        leftDomainUnary, rightDomainUnary, domainsRelated, codomainsRelated, pwi⟩ :=
        innerHypothesis leftEq rightEq
      exact ⟨leftDomainCandidate, rightDomainCandidate, domainRelation, codomainRelation,
        leftDomainUnary, rightDomainUnary, domainsRelated, codomainsRelated,
        fun leftTerm rightTerm =>
          (pointwiseIff leftTerm rightTerm).symm.trans (pwi leftTerm rightTerm)⟩

/-- **Π-pair inversion (family level).** -/
theorem BinaryReducibleTypeAtBounded.piTypePairInversion {scope : Nat} {env : Nat → Nat}
    {bound : Nat} {leftDomain rightDomain : RawTerm scope}
    {leftCodomain rightCodomain : RawTerm (scope + 1)} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeAtBounded env bound
      (.mkGen .gen_piTyCode () (.childCons leftDomain (.childCons leftCodomain .childNil)))
      (.mkGen .gen_piTyCode () (.childCons rightDomain (.childCons rightCodomain .childNil)))
      relation) :
    ∃ (leftDomainCandidate rightDomainCandidate : RawTerm scope → Prop)
      (domainRelation : BinaryCandidate scope)
      (codomainRelation : RawTerm scope → RawTerm scope → BinaryCandidate scope),
      ReducibleTypeAtBounded env bound leftDomain leftDomainCandidate ∧
      ReducibleTypeAtBounded env bound rightDomain rightDomainCandidate ∧
      BinaryReducibleTypeAtBounded env bound leftDomain rightDomain domainRelation ∧
      (∀ leftArgument rightArgument : RawTerm scope,
        leftDomainCandidate leftArgument → rightDomainCandidate rightArgument →
        domainRelation leftArgument rightArgument →
        BinaryReducibleTypeAtBounded env bound
          (RawTerm.subst0 leftCodomain leftArgument)
          (RawTerm.subst0 rightCodomain rightArgument)
          (codomainRelation leftArgument rightArgument)) ∧
      BinaryPointwiseIff relation
        (fun leftFunction rightFunction =>
          IsStronglyNormalizing leftFunction ∧ IsStronglyNormalizing rightFunction ∧
            ∀ leftArgument rightArgument : RawTerm scope,
              leftDomainCandidate leftArgument → rightDomainCandidate rightArgument →
              domainRelation leftArgument rightArgument →
              codomainRelation leftArgument rightArgument
                (.mkGen .gen_app ()
                  (.childCons leftFunction (.childCons leftArgument .childNil)))
                (.mkGen .gen_app ()
                  (.childCons rightFunction (.childCons rightArgument .childNil)))) :=
  related.candidatePiPairShape rfl rfl

/-! ## ★ Binary determinism (direct double induction — no denote bridge exists) -/

/-- ★ **The binary relation is functional**: two derivations at the same PAIR of type codes
have pointwise-equivalent binary candidates.  Induction on the first derivation; each arm
identifies the second derivation's candidate through the matching per-shape lemma (the
one-sided peels handle the expansion arms; the unary's forget-bridge transfer is unavailable
because the binary relation has no denote twin). -/
theorem BinaryReducibleTypeStepBounded.deterministic {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    {leftCode rightCode : RawTerm scope} {relation1 : BinaryCandidate scope}
    (related1 : BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation1) :
    ∀ {relation2 : BinaryCandidate scope},
      BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation2 →
      BinaryPointwiseIff relation1 relation2 := by
  induction related1 with
  | whnfExpandLeft weakHeadStep1 _reductRelated1 reductIH =>
      intro relation2 related2
      exact reductIH (related2.candidateAtWhnfReductLeft weakHeadStep1)
  | whnfExpandRight weakHeadStep1 _reductRelated1 reductIH =>
      intro relation2 related2
      exact reductIH (related2.candidateAtWhnfReductRight weakHeadStep1)
  | neutral noStepLeft noStepRight notPiLeft notUniverseLeft notEmptyLeft notFlatLeft
      notPiRight notUniverseRight notEmptyRight notFlatRight =>
      intro relation2 related2 leftTerm rightTerm
      exact (related2.binaryCandidateIffStronglyNormalizingPair noStepLeft noStepRight
        notPiLeft notUniverseLeft notEmptyLeft notFlatLeft
        notPiRight notUniverseRight notEmptyRight notFlatRight leftTerm rightTerm).symm
  | piType codomainRelation1 leftDomainUnary1 rightDomainUnary1 _domainsRelated1
      _codomainsRelated1 domainIH codomainIH =>
      intro relation2 related2
      obtain ⟨leftDomainCandidate2, rightDomainCandidate2, domainRelation2, codomainRelation2,
        leftDomainUnary2, rightDomainUnary2, domainsRelated2, codomainsRelated2, pwi2⟩ :=
        related2.candidatePiPairShape rfl rfl
      have leftUnaryAgree :=
        ReducibleTypeAtBounded.deterministic leftDomainUnary1 leftDomainUnary2
      have rightUnaryAgree :=
        ReducibleTypeAtBounded.deterministic rightDomainUnary1 rightDomainUnary2
      refine fun leftFunction rightFunction =>
        Iff.trans ?_ (pwi2 leftFunction rightFunction).symm
      constructor
      · intro membership1
        refine ⟨membership1.1, membership1.2.1, ?_⟩
        intro leftArgument rightArgument leftGuard2 rightGuard2 domain2Arguments
        have leftGuard1 := (leftUnaryAgree leftArgument).mpr leftGuard2
        have rightGuard1 := (rightUnaryAgree rightArgument).mpr rightGuard2
        have domain1Arguments :=
          (domainIH domainsRelated2 leftArgument rightArgument).mpr domain2Arguments
        have codomainEquivalence :=
          codomainIH leftArgument rightArgument leftGuard1 rightGuard1 domain1Arguments
            (codomainsRelated2 leftArgument rightArgument leftGuard2 rightGuard2
              domain2Arguments)
        exact (codomainEquivalence _ _).mp
          (membership1.2.2 leftArgument rightArgument leftGuard1 rightGuard1 domain1Arguments)
      · intro membership2
        refine ⟨membership2.1, membership2.2.1, ?_⟩
        intro leftArgument rightArgument leftGuard1 rightGuard1 domain1Arguments
        have leftGuard2 := (leftUnaryAgree leftArgument).mp leftGuard1
        have rightGuard2 := (rightUnaryAgree rightArgument).mp rightGuard1
        have domain2Arguments :=
          (domainIH domainsRelated2 leftArgument rightArgument).mp domain1Arguments
        have codomainEquivalence :=
          codomainIH leftArgument rightArgument leftGuard1 rightGuard1 domain1Arguments
            (codomainsRelated2 leftArgument rightArgument leftGuard2 rightGuard2
              domain2Arguments)
        exact (codomainEquivalence _ _).mpr
          (membership2.2.2 leftArgument rightArgument leftGuard2 rightGuard2 domain2Arguments)
  | universeCode _levelExpr1 _flag1 _belowBound1 =>
      intro relation2 related2 leftTerm rightTerm
      exact (related2.binaryCandidateIffUniverse rfl rfl leftTerm rightTerm).symm
  | dataEmpty =>
      intro relation2 related2 leftTerm rightTerm
      exact (related2.binaryCandidateIffEmptyCandidate rfl rfl leftTerm rightTerm).symm
  | dataFlat flatPinned1 headsAgree1 =>
      intro relation2 related2 leftTerm rightTerm
      exact (related2.binaryCandidateIffFlatCandidate flatPinned1
        (headsAgree1 ▸ flatPinned1) leftTerm rightTerm).symm
  | ofPointwiseIff _innerRelated1 pointwiseIff1 innerIH1 =>
      intro relation2 related2 leftTerm rightTerm
      exact (pointwiseIff1 leftTerm rightTerm).symm.trans
        (innerIH1 related2 leftTerm rightTerm)

/-- Family-level binary determinism. -/
theorem BinaryReducibleTypeAtBounded.deterministic {scope : Nat} {env : Nat → Nat} {bound : Nat}
    {leftCode rightCode : RawTerm scope} {relation1 relation2 : BinaryCandidate scope}
    (related1 : BinaryReducibleTypeAtBounded env bound leftCode rightCode relation1)
    (related2 : BinaryReducibleTypeAtBounded env bound leftCode rightCode relation2) :
    BinaryPointwiseIff relation1 relation2 :=
  BinaryReducibleTypeStepBounded.deterministic related1 related2

/-! ## ★ The Π-elimination pair arm -/

/-- ★ **The binary Π-elimination member arm**: a related function pair at a related Π pair,
applied to a related argument pair at the domains, is a related pair at the substituted
dependent codomains.  The Π-pair inversion supplies the relational-arrow form; binary
determinism aligns the argument pair's witnessed relation with the inverted domain relation. -/
theorem applicationMemberPairAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {leftDomain rightDomain : RawTerm scope}
    {leftCodomain rightCodomain : RawTerm (scope + 1)}
    {leftFunction rightFunction leftArgument rightArgument : RawTerm scope}
    (functionMemberPair : IsBinaryReducibleMemberPairAtBounded env bound
      (.mkGen .gen_piTyCode () (.childCons leftDomain (.childCons leftCodomain .childNil)))
      (.mkGen .gen_piTyCode () (.childCons rightDomain (.childCons rightCodomain .childNil)))
      leftFunction rightFunction)
    (argumentMemberPair : IsBinaryReducibleMemberPairAtBounded env bound
      leftDomain rightDomain leftArgument rightArgument)
    (leftArgumentUnaryMember : IsReducibleMemberAtBounded env bound leftDomain leftArgument)
    (rightArgumentUnaryMember :
      IsReducibleMemberAtBounded env bound rightDomain rightArgument) :
    IsBinaryReducibleMemberPairAtBounded env bound
      (RawTerm.subst0 leftCodomain leftArgument) (RawTerm.subst0 rightCodomain rightArgument)
      (.mkGen .gen_app () (.childCons leftFunction (.childCons leftArgument .childNil)))
      (.mkGen .gen_app () (.childCons rightFunction (.childCons rightArgument .childNil))) := by
  obtain ⟨_piRelation, piPairRelated, functionsInPi⟩ := functionMemberPair
  obtain ⟨leftDomainCandidate, rightDomainCandidate, domainRelation, codomainRelation,
    leftDomainUnary, rightDomainUnary, domainsRelated, codomainsRelated, piRelationIff⟩ :=
    piPairRelated.piTypePairInversion
  have functionsApply := (piRelationIff leftFunction rightFunction).mp functionsInPi
  obtain ⟨argumentRelation, argumentTypesRelated, argumentsInRelation⟩ := argumentMemberPair
  have argumentsInDomain : domainRelation leftArgument rightArgument :=
    (BinaryReducibleTypeAtBounded.deterministic argumentTypesRelated domainsRelated
      leftArgument rightArgument).mp argumentsInRelation
  obtain ⟨leftUnaryCandidate, leftUnaryReducible, leftArgumentInUnary⟩ :=
    leftArgumentUnaryMember
  obtain ⟨rightUnaryCandidate, rightUnaryReducible, rightArgumentInUnary⟩ :=
    rightArgumentUnaryMember
  have leftGuard : leftDomainCandidate leftArgument :=
    (ReducibleTypeAtBounded.deterministic leftUnaryReducible leftDomainUnary leftArgument).mp
      leftArgumentInUnary
  have rightGuard : rightDomainCandidate rightArgument :=
    (ReducibleTypeAtBounded.deterministic rightUnaryReducible rightDomainUnary
      rightArgument).mp rightArgumentInUnary
  exact ⟨codomainRelation leftArgument rightArgument,
    codomainsRelated leftArgument rightArgument leftGuard rightGuard argumentsInDomain,
    functionsApply.2.2 leftArgument rightArgument leftGuard rightGuard argumentsInDomain⟩

/-- The Π-elimination pair arm under a closing-substitution pair (the FT shape): both sides'
dependent result types commute by `subst0_subst_commute`, and `subst` distributes over the app
and Π cells definitionally. -/
theorem applicationMemberPairUnderClosingSubstitutionBounded {scope targetScope : Nat}
    (env : Nat → Nat) (bound : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {functionTerm argumentTerm : RawTerm scope}
    {leftSubstitution rightSubstitution : RawTermSubst scope targetScope}
    (functionMemberPair : IsBinaryReducibleMemberPairAtBounded env bound
      (RawTerm.subst leftSubstitution
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
      (RawTerm.subst rightSubstitution
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
      (RawTerm.subst leftSubstitution functionTerm)
      (RawTerm.subst rightSubstitution functionTerm))
    (argumentMemberPair : IsBinaryReducibleMemberPairAtBounded env bound
      (RawTerm.subst leftSubstitution domainCode) (RawTerm.subst rightSubstitution domainCode)
      (RawTerm.subst leftSubstitution argumentTerm)
      (RawTerm.subst rightSubstitution argumentTerm))
    (leftArgumentUnaryMember : IsReducibleMemberAtBounded env bound
      (RawTerm.subst leftSubstitution domainCode) (RawTerm.subst leftSubstitution argumentTerm))
    (rightArgumentUnaryMember : IsReducibleMemberAtBounded env bound
      (RawTerm.subst rightSubstitution domainCode)
      (RawTerm.subst rightSubstitution argumentTerm)) :
    IsBinaryReducibleMemberPairAtBounded env bound
      (RawTerm.subst leftSubstitution (RawTerm.subst0 codomainCode argumentTerm))
      (RawTerm.subst rightSubstitution (RawTerm.subst0 codomainCode argumentTerm))
      (RawTerm.subst leftSubstitution
        (.mkGen .gen_app () (.childCons functionTerm (.childCons argumentTerm .childNil))))
      (RawTerm.subst rightSubstitution
        (.mkGen .gen_app () (.childCons functionTerm (.childCons argumentTerm .childNil)))) := by
  rw [RawTerm.subst0_subst_commute codomainCode argumentTerm leftSubstitution,
    RawTerm.subst0_subst_commute codomainCode argumentTerm rightSubstitution]
  exact applicationMemberPairAtBounded env bound functionMemberPair argumentMemberPair
    leftArgumentUnaryMember rightArgumentUnaryMember

/-! ## ★ The binary fundamental-theorem motive + the var and piElim arms -/

/-- ★ **THE binary fundamental-theorem motive**: every binary-related closing-substitution pair
takes the subject's two closures to a binary-reducible member pair at the classifier's two
closures — the conclusion shape of every OP1-K2 FT arm (the binary twin of
`FundamentalConclusionAtBounded`). -/
def BinaryFundamentalConclusionAtBounded {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    (subject classifier : RawTerm scope) : Prop :=
  ∀ {targetScope : Nat}
    (leftSubstitution rightSubstitution : RawTermSubst scope targetScope),
    BinaryReducibleEnvAtBounded env bound context leftSubstitution rightSubstitution →
    IsBinaryReducibleMemberPairAtBounded env bound
      (RawTerm.subst leftSubstitution classifier) (RawTerm.subst rightSubstitution classifier)
      (RawTerm.subst leftSubstitution subject) (RawTerm.subst rightSubstitution subject)

/-- **The binary FT var arm**: a variable satisfies the binary fundamental conclusion at its
looked-up type — the environment lookup IS the arm (`subst` on a variable cell is the
substitution's image definitionally). -/
theorem binaryFundamentalVarArm {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (bound : Nat) (context : TypingContext profile scope) (index : Fin scope) :
    BinaryFundamentalConclusionAtBounded env bound context
      (variableCell index) (context.lookup index) :=
  fun _leftSubstitution _rightSubstitution envRelated => envRelated index

/-- ★ **The binary FT piElim (application) arm**: from the binary fundamental conclusions of
the function (at the Π classifier) and the argument (at the domain), the application satisfies
the binary fundamental conclusion at the substituted dependent codomain — one composition of
the closing-substitution member arm with both sub-conclusions. -/
theorem binaryFundamentalPiElimArm {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (bound : Nat) (context : TypingContext profile scope)
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (functionConclusion : BinaryFundamentalConclusionAtBounded env bound context functionTerm
      (piTyCodeCell domainCode codomainCode))
    (argumentConclusion : BinaryFundamentalConclusionAtBounded env bound context argument
      domainCode)
    (argumentUnaryMembers : ∀ {targetScope : Nat}
      (leftSubstitution rightSubstitution : RawTermSubst scope targetScope),
      BinaryReducibleEnvAtBounded env bound context leftSubstitution rightSubstitution →
      IsReducibleMemberAtBounded env bound (RawTerm.subst leftSubstitution domainCode)
          (RawTerm.subst leftSubstitution argument) ∧
        IsReducibleMemberAtBounded env bound (RawTerm.subst rightSubstitution domainCode)
          (RawTerm.subst rightSubstitution argument)) :
    BinaryFundamentalConclusionAtBounded env bound context (appCell functionTerm argument)
      (RawTerm.subst0 codomainCode argument) := by
  intro _targetScope leftSubstitution rightSubstitution envRelated
  exact applicationMemberPairUnderClosingSubstitutionBounded env bound
    (functionConclusion leftSubstitution rightSubstitution envRelated)
    (argumentConclusion leftSubstitution rightSubstitution envRelated)
    (argumentUnaryMembers leftSubstitution rightSubstitution envRelated).1
    (argumentUnaryMembers leftSubstitution rightSubstitution envRelated).2

end FX1Poly.Typed

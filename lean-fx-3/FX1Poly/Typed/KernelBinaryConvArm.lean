import FX1Poly.Typed.KernelBinaryConvInvariance

/-! # FX1Poly/Typed/KernelBinaryConvArm
    — binary universe-membership extraction + the conv and universeFormation FT arms (OP1-K2 brick 4)

The two remaining LEAF-FAMILY arms of the binary fundamental theorem, completing everything
except the former/telescope arms and the assembly:

  * `belowBoundOfUniverseCodePairShape` / `binaryUniverseCodeReducibleAtBounded_belowBound` —
    the GATE extraction: a binary-related pair of universe codes carries its `belowBound`
    (the left payload aligned by `universeCodeCell_inj`; the right equation rules out the
    right expansion arm).
  * `binaryUniverseMemberReducibleAsTypePairAtDecodedLevel` +
    ★ `binaryReducibleTypePairFromUniverseMemberBounded` — the A2-bridge, doubled: a member
    PAIR of a binary universe pair is itself a binary-related TYPE pair at the ambient bound
    (identify the candidate by brick-1's `binaryCandidateIffUniverse`, decode through the
    below-family coherence, lift by K1 cumulativity).
  * ★ `binaryFundamentalConvArm` — the conv FT arm: the reclassifier's universe membership
    yields its type-pair reducibility; brick-3's `convMemberPairUnderClosingSubstitution`
    transports the subject's member pair (substitution leaves universe codes fixed, so the
    extraction applies definitionally — no rewriting).
  * `binaryUniverseMembershipBounded_levelIrrelevant` +
    `binaryUniverseFormationMemberPairAtBounded` + ★ `binaryFundamentalUniverseFormationArm`
    — the universeFormation FT arm in MEMBER form (completing K1's type-level form):
    `(Type@e, Type@e)` is a related member pair of `(Type@(lsucc e), Type@(lsucc e))` under
    every substitution pair, the level-irrelevant candidate decoding at `denote (lsucc e)`.

With var (brick 1), piElim (brick 1), piIntro (brick 2), conv and universeFormation (this
brick), all NON-FORMER arms of the binary FT are shipped.  Remaining: the former/telescope
arms (genFormationPi) and the budget-dispatched assembly.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-! ## The gate extraction -/

/-- A binary-related pair of universe codes carries its bound gate (the LEFT payload is the
keyed one, aligned via `universeCodeCell_inj`; the right equation rules out the right
expansion arm). -/
theorem BinaryReducibleTypeStepBounded.belowBoundOfUniverseCodePairShape {scope : Nat}
    {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    {leftCode rightCode : RawTerm scope} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation) :
    ∀ {levelExpr levelExprRight : LevelExpr} {flag flagRight : UniverseFlag},
      leftCode = universeCodeCell levelExpr flag →
      rightCode = universeCodeCell levelExprRight flagRight →
      LevelExpr.denote levelExpr env < bound := by
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
  | universeCode armLevelExpr armFlag belowBound =>
      intro _ _ _ _ leftEq _rightEq
      obtain ⟨levelEq, _flagEq⟩ := universeCodeCell_inj leftEq
      exact levelEq ▸ belowBound
  | dataEmpty =>
      intro _ _ _ _ leftEq _rightEq
      have rootMismatch : Generator.gen_emptyCode = Generator.gen_universeCode :=
        congrArg RawTerm.rootGenerator leftEq
      exact absurd rootMismatch (by decide)
  | dataFlat flatPinned _headsAgree =>
      intro _ _ _ _ leftEq _rightEq
      rw [leftEq] at flatPinned
      exact nomatch flatPinned
  | ofPointwiseIff _ _pointwiseIff innerHypothesis =>
      intro _ _ _ _ leftEq rightEq
      exact innerHypothesis leftEq rightEq

/-- Gate extraction at the diagonal (the FT shape). -/
theorem binaryUniverseCodeReducibleAtBounded_belowBound {scope : Nat} {env : Nat → Nat}
    {bound : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag}
    {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeAtBounded env bound
      (universeCodeCell levelExpr flag : RawTerm scope) (universeCodeCell levelExpr flag)
      relation) :
    LevelExpr.denote levelExpr env < bound :=
  related.belowBoundOfUniverseCodePairShape rfl rfl

/-! ## ★ The A2-bridge, doubled: universe member pairs are related type pairs -/

/-- A member pair of a binary universe pair is binary-related AS TYPES at the decoded level:
identify the witnessed candidate with the binary universe candidate (brick 1), then decode
the below-family conjunct through coherence. -/
theorem binaryUniverseMemberReducibleAsTypePairAtDecodedLevel {scope : Nat} {env : Nat → Nat}
    {bound : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag}
    {leftCode rightCode : RawTerm scope}
    (memberPair : IsBinaryReducibleMemberPairAtBounded env bound
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr flag) leftCode rightCode)
    (belowBound : LevelExpr.denote levelExpr env < bound) :
    IsBinaryReducibleTypePairAtBounded env (LevelExpr.denote levelExpr env)
      leftCode rightCode := by
  obtain ⟨relation, universePairRelated, membersInRelation⟩ := memberPair
  have membersInUniverse :=
    (universePairRelated.binaryCandidateIffUniverse rfl rfl leftCode rightCode).mp
      membersInRelation
  obtain ⟨_leftSN, _rightSN, lowerRelation, lowerRelated⟩ := membersInUniverse
  rw [binaryDenoteBelowFamilyBounded_eq_reducible env bound
    (LevelExpr.denote levelExpr env) belowBound] at lowerRelated
  exact ⟨lowerRelation, lowerRelated⟩

/-- ★ **The binary A2-bridge**: a member pair of a binary universe pair is a binary-related
TYPE pair at the AMBIENT bound (decode, then lift by cumulativity). -/
theorem binaryReducibleTypePairFromUniverseMemberBounded {scope : Nat} {env : Nat → Nat}
    {bound : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag}
    {leftCode rightCode : RawTerm scope}
    (memberPair : IsBinaryReducibleMemberPairAtBounded env bound
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr flag) leftCode rightCode)
    (belowBound : LevelExpr.denote levelExpr env < bound) :
    IsBinaryReducibleTypePairAtBounded env bound leftCode rightCode :=
  isBinaryReducibleTypePair_cumulative
    (binaryUniverseMemberReducibleAsTypePairAtDecodedLevel memberPair belowBound)
    (Nat.le_of_lt belowBound)

/-! ## ★ The conv FT arm -/

/-- ★ **The binary `conv` fundamental-theorem arm**: from the subject's conclusion at its
classifier and the reclassifier's conclusion at a universe (the typing rule's premise shape),
the subject satisfies the conclusion at the reclassifier.  The reclassifier's universe
membership yields the gate and its type-pair reducibility (substitution leaves universe codes
fixed definitionally — the extraction applies without rewriting); brick-3's Conv transport
finishes. -/
theorem binaryFundamentalConvArm {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (bound : Nat) (context : TypingContext profile scope)
    {subject subjectClassifier reclassifier : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (subjectConclusion : BinaryFundamentalConclusionAtBounded env bound context subject
      subjectClassifier)
    (reclassifierConclusion : BinaryFundamentalConclusionAtBounded env bound context
      reclassifier (universeCodeCell levelExpr flag))
    (converts : Conv subjectClassifier reclassifier) :
    BinaryFundamentalConclusionAtBounded env bound context subject reclassifier := by
  intro _targetScope leftSubstitution rightSubstitution envRelated
  have reclassifierMemberPair : IsBinaryReducibleMemberPairAtBounded env bound
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr flag)
      (RawTerm.subst leftSubstitution reclassifier)
      (RawTerm.subst rightSubstitution reclassifier) :=
    reclassifierConclusion leftSubstitution rightSubstitution envRelated
  have belowBound : LevelExpr.denote levelExpr env < bound := by
    obtain ⟨_relation, universePairRelated, _membersIn⟩ := reclassifierMemberPair
    exact binaryUniverseCodeReducibleAtBounded_belowBound universePairRelated
  exact convMemberPairUnderClosingSubstitutionBounded env bound
    (subjectConclusion leftSubstitution rightSubstitution envRelated)
    (binaryReducibleTypePairFromUniverseMemberBounded reclassifierMemberPair belowBound)
    converts

/-! ## ★ The universeFormation FT arm (member form) -/

/-- The binary universe candidate is LEVEL-IRRELEVANT below the bound: the universe pair is
binary-related with the candidate that decodes at the level directly (the below-family
collapses through coherence) — the binary twin of `universeMembershipBounded_levelIrrelevant`. -/
theorem binaryUniverseMembershipBounded_levelIrrelevant {scope : Nat} (env : Nat → Nat)
    (bound : Nat) (levelExpr : LevelExpr) (flag : UniverseFlag)
    (belowBound : LevelExpr.denote levelExpr env < bound) :
    BinaryReducibleTypeAtBounded (scope := scope) env bound
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (fun leftMember rightMember =>
        IsStronglyNormalizing leftMember ∧ IsStronglyNormalizing rightMember ∧
          IsBinaryReducibleTypePairAtBounded env (LevelExpr.denote levelExpr env)
            leftMember rightMember) := by
  have key : binaryDenoteBelowFamilyBounded (scope := scope) env bound
      (LevelExpr.denote levelExpr env)
      = BinaryReducibleTypeAtBounded env (LevelExpr.denote levelExpr env) :=
    binaryDenoteBelowFamilyBounded_eq_reducible env bound
      (LevelExpr.denote levelExpr env) belowBound
  refine BinaryReducibleTypeStepBounded.ofPointwiseIff
    (BinaryReducibleTypeStepBounded.universeCode levelExpr flag belowBound)
    (fun leftMember rightMember => ?_)
  show (IsStronglyNormalizing leftMember ∧ IsStronglyNormalizing rightMember ∧
        ∃ relation : BinaryCandidate scope,
          binaryDenoteBelowFamilyBounded env bound (LevelExpr.denote levelExpr env)
            leftMember rightMember relation)
    ↔ (IsStronglyNormalizing leftMember ∧ IsStronglyNormalizing rightMember ∧
        IsBinaryReducibleTypePairAtBounded env (LevelExpr.denote levelExpr env)
          leftMember rightMember)
  rw [key]
  exact Iff.rfl

/-- The binary universeFormation member pair: `(Type@e, Type@e)` is a related member pair of
`(Type@(lsucc e), Type@(lsucc e))` — the member side of no-Type-in-Type, doubled. -/
theorem binaryUniverseFormationMemberPairAtBounded {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) (bound : Nat)
    (belowBound : LevelExpr.denote (LevelExpr.lsucc levelExpr) env < bound) :
    IsBinaryReducibleMemberPairAtBounded (scope := scope) env bound
      (.mkGen .gen_universeCode (LevelExpr.lsucc levelExpr, flag) .childNil)
      (.mkGen .gen_universeCode (LevelExpr.lsucc levelExpr, flag) .childNil)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) :=
  ⟨fun leftMember rightMember =>
      IsStronglyNormalizing leftMember ∧ IsStronglyNormalizing rightMember ∧
        IsBinaryReducibleTypePairAtBounded env
          (LevelExpr.denote (LevelExpr.lsucc levelExpr) env) leftMember rightMember,
   binaryUniverseMembershipBounded_levelIrrelevant env bound
     (LevelExpr.lsucc levelExpr) flag belowBound,
   isStronglyNormalizing_of_noStep (fun _target => noStep_universeCode (levelExpr, flag)),
   isStronglyNormalizing_of_noStep (fun _target => noStep_universeCode (levelExpr, flag)),
   ⟨binaryUniverseDenotePredicate env
       (binaryDenoteBelowFamilyBounded env (LevelExpr.denote (LevelExpr.lsucc levelExpr) env))
       levelExpr,
     BinaryReducibleTypeStepBounded.universeCode levelExpr flag
       (denote_lt_lsucc levelExpr env)⟩⟩

/-- ★ **The binary `universeFormation` fundamental-theorem arm**: under every related
substitution pair, the two (fixed) closures of `Type@levelExpr` form a related member pair of
the two closures of `Type@(lsucc levelExpr)` — substitution leaves the closed universe codes
fixed definitionally. -/
theorem binaryFundamentalUniverseFormationFTArm {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (belowBound : LevelExpr.denote (LevelExpr.lsucc levelExpr) env < bound) :
    BinaryFundamentalConclusionAtBounded env bound context
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr.lsucc flag) := by
  intro _targetScope _leftSubstitution _rightSubstitution _envRelated
  exact binaryUniverseFormationMemberPairAtBounded env levelExpr flag bound belowBound

end FX1Poly.Typed

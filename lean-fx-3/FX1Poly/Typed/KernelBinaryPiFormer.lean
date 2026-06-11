import FX1Poly.Typed.KernelBinaryTelescope
import FX1Poly.Typed.FormerOutputLevelBounds
import FX1Poly.Typed.CellSubstitution
import FX1Poly.Core.StrongNormalizationConstructors

/-! # FX1Poly/Typed/KernelBinaryPiFormer
    — the PREMISE-ISOLATED binary Π-former FT arm (OP1-K2 brick 5b)

The binary twin of `fundamentalGenFormationPiFromTelescopeAtBoundedSucc`, restructured around
the INHABITATION WALL recorded in `KernelBinaryTelescope`: the unary arm extracted the
codomain's level gate and the open-codomain SN by firing the telescope's codomain clause at
the variable-0 neutral inhabitant, and binary neutral-pair inhabitation is FALSE (a diagonal
neutral pair recursing through a Π candidate produces non-diagonal application pairs that the
same-value data candidate refuses).  So this arm takes exactly those two facts as premises —

  * `outputBelowBound` — the former's decoded output level sits below the budget (a fixed
    level-arithmetic fact, substitution-independent), from which BOTH component gates fall out
    by `denote_*_le_lmaxAll_pair` + `Nat.lt_of_le_of_lt`; and
  * `codomainOpenSNPair` — per related substitution pair, the once-lifted codomain closures
    are strongly normalizing on each side (the unary FT discharges this at assembly time:
    parametricity presupposes the unary normalization layer)

— while everything the binary relation CAN deliver internally is extracted here: the domain
SN pair comes out of the binary universe candidate's own SN conjuncts
(`binaryStronglyNormalizingPairOfUniverseMemberAtBounded`, new in this module), the component
type-pair reducibilities come from brick 4's decode + brick 1's cumulativity, and brick 5a's
`binaryPiReducibleFromComponentsAtBounded` + `binaryUniverseMembershipIntroAtBounded` close
the member pair.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **The binary universe candidate's SN conjuncts, extracted**: a member pair of a binary
universe pair is a pair of strongly normalizing terms — keyed on both indices through
`binaryCandidateIffUniverse`, gate-free (the SN conjuncts sit BEFORE the below-family decode,
so no `belowBound` is needed).  The binary twin of
`stronglyNormalizing_of_universeMemberAtBounded`, delivering both sides at once. -/
theorem binaryStronglyNormalizingPairOfUniverseMemberAtBounded {scope : Nat} {env : Nat → Nat}
    {bound : Nat} {levelExpr : LevelExpr} {flag : UniverseFlag}
    {leftMember rightMember : RawTerm scope}
    (memberPair : IsBinaryReducibleMemberPairAtBounded env bound
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr flag)
      leftMember rightMember) :
    IsStronglyNormalizing leftMember ∧ IsStronglyNormalizing rightMember := by
  obtain ⟨relation, universePairRelated, membersInRelation⟩ := memberPair
  have membersInUniverse :=
    (universePairRelated.binaryCandidateIffUniverse rfl rfl leftMember rightMember).mp
      membersInRelation
  exact ⟨membersInUniverse.1, membersInUniverse.2.1⟩

/-- ★ **The PER-SUBSTITUTION-PAIR binary Π-former member pair** — the composition core the
premise-isolated FT arm and the conjoined master assembly both consume: from the per-pair
binary telescope at the output level, the output gate, the open-codomain SN pair, and the two
UNARY domain reducibilities at the output level (the design-(f) fields), the two closures of
`piTyCodeCell domain codomain` are a related member pair of the output universe pair. -/
theorem binaryPiFormerMemberPairUnderSubstAtBounded {scope targetScope : Nat}
    (env : Nat → Nat) (bound : Nat)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (leftSubstitution rightSubstitution : RawTermSubst scope targetScope)
    (outputBelowBound :
      LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env < bound)
    (codomainLeftOpenSN :
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift leftSubstitution) codomain))
    (codomainRightOpenSN :
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift rightSubstitution) codomain))
    (leftDomainUnaryReducible : IsReducibleTypeAtBounded env
      (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
      (RawTerm.subst leftSubstitution domain))
    (rightDomainUnaryReducible : IsReducibleTypeAtBounded env
      (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
      (RawTerm.subst rightSubstitution domain))
    (telescopePair : BinaryTelescopeReducibleAtBounded env bound
      (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env) flag 0 2
      leftSubstitution rightSubstitution [domainLevel, codomainLevel]
      (.childCons domain (.childCons codomain .childNil))) :
    IsBinaryReducibleMemberPairAtBounded env bound
      (RawTerm.subst leftSubstitution
        (universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag))
      (RawTerm.subst rightSubstitution
        (universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag))
      (RawTerm.subst leftSubstitution (piTyCodeCell domain codomain))
      (RawTerm.subst rightSubstitution (piTyCodeCell domain codomain)) := by
  obtain ⟨leftDomainCandidateAtOutput, leftDomainUnaryAtOutput⟩ := leftDomainUnaryReducible
  obtain ⟨rightDomainCandidateAtOutput, rightDomainUnaryAtOutput⟩ := rightDomainUnaryReducible
  obtain ⟨domainMemberPair, codomainMemberPairFn⟩ := telescopePair.twoChildMembers
  have domainBelowOutput := denote_domainLevel_le_lmaxAll_pair domainLevel codomainLevel env
  have codomainBelowOutput := denote_codomainLevel_le_lmaxAll_pair domainLevel codomainLevel env
  have domainBelowBound : LevelExpr.denote domainLevel env < bound :=
    Nat.lt_of_le_of_lt domainBelowOutput outputBelowBound
  have codomainBelowBound : LevelExpr.denote codomainLevel env < bound :=
    Nat.lt_of_le_of_lt codomainBelowOutput outputBelowBound
  obtain ⟨domainLeftSN, domainRightSN⟩ :=
    binaryStronglyNormalizingPairOfUniverseMemberAtBounded domainMemberPair
  have piLeftSN :
      IsStronglyNormalizing
        (RawTerm.subst leftSubstitution (piTyCodeCell domain codomain)) := by
    rw [subst_piTyCodeCell]
    exact piTyCode_isStronglyNormalizing_of_domain_codomain domainLeftSN codomainLeftOpenSN
  have piRightSN :
      IsStronglyNormalizing
        (RawTerm.subst rightSubstitution (piTyCodeCell domain codomain)) := by
    rw [subst_piTyCodeCell]
    exact piTyCode_isStronglyNormalizing_of_domain_codomain domainRightSN codomainRightOpenSN
  have domainPairAtOutput :
      IsBinaryReducibleTypePairAtBounded env
        (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
        (RawTerm.subst leftSubstitution domain) (RawTerm.subst rightSubstitution domain) :=
    isBinaryReducibleTypePair_cumulative
      (binaryUniverseMemberReducibleAsTypePairAtDecodedLevel domainMemberPair domainBelowBound)
      domainBelowOutput
  have codomainPairAtOutput :
      ∀ leftArgument rightArgument : RawTerm targetScope,
        IsReducibleMemberAtBounded env
          (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
          (RawTerm.subst leftSubstitution domain) leftArgument →
        IsReducibleMemberAtBounded env
          (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
          (RawTerm.subst rightSubstitution domain) rightArgument →
        IsBinaryReducibleMemberPairAtBounded env
          (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
          (RawTerm.subst leftSubstitution domain) (RawTerm.subst rightSubstitution domain)
          leftArgument rightArgument →
        IsBinaryReducibleTypePairAtBounded env
          (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
          (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift leftSubstitution) codomain)
            leftArgument)
          (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift rightSubstitution) codomain)
            rightArgument) :=
    fun leftArgument rightArgument leftUnaryMember rightUnaryMember argumentsMember =>
      isBinaryReducibleTypePair_cumulative
        (binaryUniverseMemberReducibleAsTypePairAtDecodedLevel
          (codomainMemberPairFn leftArgument rightArgument leftUnaryMember rightUnaryMember
            argumentsMember)
          codomainBelowBound)
        codomainBelowOutput
  have piPairRelated :
      IsBinaryReducibleTypePairAtBounded env
        (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
        (RawTerm.subst leftSubstitution (piTyCodeCell domain codomain))
        (RawTerm.subst rightSubstitution (piTyCodeCell domain codomain)) := by
    rw [subst_piTyCodeCell, subst_piTyCodeCell]
    exact binaryPiReducibleFromComponentsAtBounded env
      (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
      leftDomainUnaryAtOutput rightDomainUnaryAtOutput
      domainPairAtOutput
      (fun leftArgument rightArgument leftGuard rightGuard argumentsMember =>
        codomainPairAtOutput leftArgument rightArgument
          ⟨leftDomainCandidateAtOutput, leftDomainUnaryAtOutput, leftGuard⟩
          ⟨rightDomainCandidateAtOutput, rightDomainUnaryAtOutput, rightGuard⟩
          argumentsMember)
  rw [subst_universeCodeCell, subst_universeCodeCell]
  exact binaryUniverseMembershipIntroAtBounded env (lmaxAll [domainLevel, codomainLevel]) flag
    bound outputBelowBound piLeftSN piRightSN piPairRelated

/-- ★ **The premise-isolated binary Π-former FT arm** — the env-quantified wrapper over the
per-pair composition core: the wall premises (`outputBelowBound` / `codomainOpenSNPair` /
`domainUnaryPair`) and the telescope arrive as per-related-substitution-pair suppliers; the
conjoined master assembly discharges them from the shipped UNARY fundamental theorem. -/
theorem binaryFundamentalGenFormationPiArm {profile : PolyProfile} {scope : Nat}
    (env : Nat → Nat) (bound : Nat) (context : TypingContext profile scope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)}
    (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
    (outputBelowBound :
      LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env < bound)
    (codomainOpenSNPair : ∀ {targetScope : Nat}
      (leftSubstitution rightSubstitution : RawTermSubst scope targetScope),
      BinaryReducibleEnvAtBounded env bound context leftSubstitution rightSubstitution →
      IsStronglyNormalizing
          (RawTerm.subst (RawTermSubst.lift leftSubstitution) codomain) ∧
        IsStronglyNormalizing
          (RawTerm.subst (RawTermSubst.lift rightSubstitution) codomain))
    (domainUnaryPair : ∀ {targetScope : Nat}
      (leftSubstitution rightSubstitution : RawTermSubst scope targetScope),
      BinaryReducibleEnvAtBounded env bound context leftSubstitution rightSubstitution →
      IsReducibleTypeAtBounded env
          (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
          (RawTerm.subst leftSubstitution domain) ∧
        IsReducibleTypeAtBounded env
          (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
          (RawTerm.subst rightSubstitution domain))
    (telescope : ∀ {targetScope : Nat}
      (leftSubstitution rightSubstitution : RawTermSubst scope targetScope),
      BinaryReducibleEnvAtBounded env bound context leftSubstitution rightSubstitution →
      BinaryTelescopeReducibleAtBounded env bound
        (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env) flag 0 2
        leftSubstitution rightSubstitution [domainLevel, codomainLevel]
        (.childCons domain (.childCons codomain .childNil))) :
    BinaryFundamentalConclusionAtBounded env bound context
      (piTyCodeCell domain codomain)
      (universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag) :=
  fun leftSubstitution rightSubstitution envRelated =>
    binaryPiFormerMemberPairUnderSubstAtBounded env bound domainLevel codomainLevel flag
      leftSubstitution rightSubstitution outputBelowBound
      (codomainOpenSNPair leftSubstitution rightSubstitution envRelated).1
      (codomainOpenSNPair leftSubstitution rightSubstitution envRelated).2
      (domainUnaryPair leftSubstitution rightSubstitution envRelated).1
      (domainUnaryPair leftSubstitution rightSubstitution envRelated).2
      (telescope leftSubstitution rightSubstitution envRelated)

end FX1Poly.Typed

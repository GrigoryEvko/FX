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

/-- ★ **The premise-isolated binary Π-former FT arm.**  From the binary formation telescope
(children related member pairs of their universe pairs under every related closing-substitution
pair, at the former's decoded output level), the output gate, and the per-substitution open
codomain SN pair, the former `piTyCodeCell domain codomain` satisfies the binary fundamental
conclusion at `Type@(lmaxAll [domainLevel, codomainLevel])`.

The two premises beyond the telescope are exactly the var-0-inhabitant extractions the
INHABITATION WALL forbids reproducing binarily; the assembly discharges them from the budget
and the shipped UNARY fundamental theorem. -/
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
    (telescope : ∀ {targetScope : Nat}
      (leftSubstitution rightSubstitution : RawTermSubst scope targetScope),
      BinaryReducibleEnvAtBounded env bound context leftSubstitution rightSubstitution →
      BinaryTelescopeReducibleAtBounded env bound
        (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env) flag 0 2
        leftSubstitution rightSubstitution [domainLevel, codomainLevel]
        (.childCons domain (.childCons codomain .childNil))) :
    BinaryFundamentalConclusionAtBounded env bound context
      (piTyCodeCell domain codomain)
      (universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag) := by
  intro _targetScope leftSubstitution rightSubstitution envRelated
  obtain ⟨domainMemberPair, codomainMemberPairFn⟩ :=
    (telescope leftSubstitution rightSubstitution envRelated).twoChildMembers
  have domainBelowOutput := denote_domainLevel_le_lmaxAll_pair domainLevel codomainLevel env
  have codomainBelowOutput := denote_codomainLevel_le_lmaxAll_pair domainLevel codomainLevel env
  have domainBelowBound : LevelExpr.denote domainLevel env < bound :=
    Nat.lt_of_le_of_lt domainBelowOutput outputBelowBound
  have codomainBelowBound : LevelExpr.denote codomainLevel env < bound :=
    Nat.lt_of_le_of_lt codomainBelowOutput outputBelowBound
  obtain ⟨domainLeftSN, domainRightSN⟩ :=
    binaryStronglyNormalizingPairOfUniverseMemberAtBounded domainMemberPair
  obtain ⟨codomainLeftSN, codomainRightSN⟩ :=
    codomainOpenSNPair leftSubstitution rightSubstitution envRelated
  have piLeftSN :
      IsStronglyNormalizing
        (RawTerm.subst leftSubstitution (piTyCodeCell domain codomain)) := by
    rw [subst_piTyCodeCell]
    exact piTyCode_isStronglyNormalizing_of_domain_codomain domainLeftSN codomainLeftSN
  have piRightSN :
      IsStronglyNormalizing
        (RawTerm.subst rightSubstitution (piTyCodeCell domain codomain)) := by
    rw [subst_piTyCodeCell]
    exact piTyCode_isStronglyNormalizing_of_domain_codomain domainRightSN codomainRightSN
  have domainPairAtOutput :
      IsBinaryReducibleTypePairAtBounded env
        (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
        (RawTerm.subst leftSubstitution domain) (RawTerm.subst rightSubstitution domain) :=
    isBinaryReducibleTypePair_cumulative
      (binaryUniverseMemberReducibleAsTypePairAtDecodedLevel domainMemberPair domainBelowBound)
      domainBelowOutput
  have codomainPairAtOutput :
      ∀ leftArgument rightArgument : RawTerm _targetScope,
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
    fun leftArgument rightArgument argumentsMember =>
      isBinaryReducibleTypePair_cumulative
        (binaryUniverseMemberReducibleAsTypePairAtDecodedLevel
          (codomainMemberPairFn leftArgument rightArgument argumentsMember)
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
      domainPairAtOutput codomainPairAtOutput
  rw [subst_universeCodeCell, subst_universeCodeCell]
  exact binaryUniverseMembershipIntroAtBounded env (lmaxAll [domainLevel, codomainLevel]) flag
    bound outputBelowBound piLeftSN piRightSN piPairRelated

end FX1Poly.Typed

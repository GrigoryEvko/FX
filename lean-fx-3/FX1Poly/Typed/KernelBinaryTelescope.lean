import FX1Poly.Typed.KernelBinaryConvArm
import FX1Poly.Typed.DenoteKeyedBoundedTelescopeReducible

/-! # FX1Poly/Typed/KernelBinaryTelescope
    — the binary formation telescope + universe intro + Π-pair reducibility (OP1-K2 brick 5a)

The former-arm substrate of the binary fundamental theorem: the telescope motive interpreting
a former's child premises over a PAIR of closing substitutions, its projections, and the two
composition lemmas the Π-former arm assembles from.

  * `BinaryTelescopeReducibleAtBounded` — the pair-substitution telescope: each child pair is
    a related member pair of its universe pair, and the rest fires at RELATED argument pairs
    (the binary twin of `TelescopeReducibleAtBounded`, same propext-clean recursion shape).
  * `nil` / `twoChildMembers` / `oneChildMember` — the constructors/projections the Π/Σ and
    data-former arms consume (`subst_cons_eq_subst0_lift` reshapes the codomain on each side).
  * `binaryUniverseMembershipIntroAtBounded` — the INTRO inverse of brick 4's extraction:
    gate + SN pair + decoded-level type-pair reducibility ⟹ member pair of the universe pair
    (one anonymous constructor over brick 4's level-irrelevant candidate).
  * ★ `binaryPiReducibleFromComponentsAtBounded` — related domains + related codomain
    families ⟹ the Π PAIR is binary-related as types, with both candidates pinned to the
    canonical member-pair predicate (brick 2's choice-free engine).

## ⚠ The INHABITATION WALL (a genuine binary-LR finding, recorded honestly)

The unary Π-former arm extracted the codomain's level gate and the open-codomain SN by firing
the telescope's codomain clause at the VARIABLE-0 NEUTRAL INHABITANT (`OB-1`: a neutral is a
member of every reducible type).  The binary twin of that inhabitation is FALSE: a diagonal
neutral pair `(x, x)` is NOT a member pair of every related type pair — at a Π pair the
recursion produces NON-diagonal neutral application pairs `(app x aL, app x aR)`, and at the
same-value data candidate (`binaryDataCandidate` = data-Tait × data-Tait × Conv) such a pair
would need `Conv (app x aL) (app x aR)`, which fails for non-convertible arguments.  This is
the standard binary-logical-relations phenomenon (binary relations do not admit neutral
inhabitation; parametricity presupposes the unary normalization layer for proof-irrelevant
facts).  Consequence: the binary Π-former arm (next brick) is PREMISE-ISOLATING — it takes the
codomain gate and the component SN facts as explicit per-substitution premises, to be
discharged at assembly time from the budget and the shipped UNARY fundamental theorem rather
than from binary inhabitation.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The binary formation telescope**: over a PAIR of closing substitutions, each child pair
is a related member pair of its universe pair, and the remaining telescope fires at every
RELATED argument pair of the (substituted) head pair — the binary twin of
`TelescopeReducibleAtBounded`, with the same structural recursion shape. -/
def BinaryTelescopeReducibleAtBounded {baseScope targetScope : Nat} (env : Nat → Nat)
    (bound argLevel : Nat) (flag : UniverseFlag) :
    (currentDepth : Nat) → (count : Nat) →
    RawTermSubst (baseScope + currentDepth) targetScope →
    RawTermSubst (baseScope + currentDepth) targetScope →
    List LevelExpr →
    RawTermChildren (consecutiveShifts currentDepth count) baseScope → Prop
  | _, 0, _, _, _, _ => True
  | _, _ + 1, _, _, [], _ => True
  | currentDepth, _ + 1, leftSubstitution, rightSubstitution, headLevel :: restLevels,
      .childCons head tail =>
      IsBinaryReducibleMemberPairAtBounded env bound
        (universeCodeCell headLevel flag) (universeCodeCell headLevel flag)
        (RawTerm.subst leftSubstitution head) (RawTerm.subst rightSubstitution head) ∧
      (∀ leftArgument rightArgument : RawTerm targetScope,
        IsBinaryReducibleMemberPairAtBounded env argLevel
          (RawTerm.subst leftSubstitution head) (RawTerm.subst rightSubstitution head)
          leftArgument rightArgument →
        BinaryTelescopeReducibleAtBounded env bound argLevel flag (currentDepth + 1) _
          (RawTermSubst.cons leftArgument leftSubstitution)
          (RawTermSubst.cons rightArgument rightSubstitution) restLevels tail)

/-- The empty binary telescope is reducible vacuously. -/
theorem BinaryTelescopeReducibleAtBounded.nil {baseScope targetScope : Nat} (env : Nat → Nat)
    (bound argLevel : Nat) (flag : UniverseFlag) (currentDepth : Nat)
    (leftSubstitution rightSubstitution : RawTermSubst (baseScope + currentDepth) targetScope)
    (children : RawTermChildren (consecutiveShifts currentDepth 0) baseScope) :
    BinaryTelescopeReducibleAtBounded env bound argLevel flag currentDepth 0
      leftSubstitution rightSubstitution [] children :=
  True.intro

/-- **Project the two-child Π/Σ binary telescope** into the domain member pair and the
per-related-argument-pair codomain member pair (the codomain reshaped by
`subst_cons_eq_subst0_lift` on each side). -/
theorem BinaryTelescopeReducibleAtBounded.twoChildMembers {baseScope targetScope : Nat}
    {env : Nat → Nat} {bound argLevel : Nat} {flag : UniverseFlag}
    {leftSubstitution rightSubstitution : RawTermSubst baseScope targetScope}
    {domainLevel codomainLevel : LevelExpr}
    {domain : RawTerm baseScope} {codomain : RawTerm (baseScope + 1)}
    (telescope : BinaryTelescopeReducibleAtBounded env bound argLevel flag 0 2
      leftSubstitution rightSubstitution [domainLevel, codomainLevel]
      (.childCons domain (.childCons codomain .childNil))) :
    IsBinaryReducibleMemberPairAtBounded env bound
      (universeCodeCell domainLevel flag) (universeCodeCell domainLevel flag)
      (RawTerm.subst leftSubstitution domain) (RawTerm.subst rightSubstitution domain) ∧
    (∀ leftArgument rightArgument : RawTerm targetScope,
      IsBinaryReducibleMemberPairAtBounded env argLevel
        (RawTerm.subst leftSubstitution domain) (RawTerm.subst rightSubstitution domain)
        leftArgument rightArgument →
      IsBinaryReducibleMemberPairAtBounded env bound
        (universeCodeCell codomainLevel flag) (universeCodeCell codomainLevel flag)
        (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift leftSubstitution) codomain)
          leftArgument)
        (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift rightSubstitution) codomain)
          rightArgument)) :=
  ⟨telescope.1,
   fun leftArgument rightArgument argumentsMember => by
     have codomainMemberPair := (telescope.2 leftArgument rightArgument argumentsMember).1
     rwa [RawTerm.subst_cons_eq_subst0_lift codomain leftArgument leftSubstitution,
       RawTerm.subst_cons_eq_subst0_lift codomain rightArgument rightSubstitution]
       at codomainMemberPair⟩

/-- **Project the one-child data-former binary telescope** into the element member pair (a
pure projection — the data former is non-dependent). -/
theorem BinaryTelescopeReducibleAtBounded.oneChildMember {baseScope targetScope : Nat}
    {env : Nat → Nat} {bound argLevel : Nat} {flag : UniverseFlag}
    {leftSubstitution rightSubstitution : RawTermSubst baseScope targetScope}
    {elementLevel : LevelExpr} {element : RawTerm baseScope}
    (telescope : BinaryTelescopeReducibleAtBounded env bound argLevel flag 0 1
      leftSubstitution rightSubstitution [elementLevel] (.childCons element .childNil)) :
    IsBinaryReducibleMemberPairAtBounded env bound
      (universeCodeCell elementLevel flag) (universeCodeCell elementLevel flag)
      (RawTerm.subst leftSubstitution element) (RawTerm.subst rightSubstitution element) :=
  telescope.1

/-! ## The universe-membership INTRO (the inverse of brick 4's extraction) -/

/-- **Binary universe-membership intro**: a pair of SN type codes that is binary-related AS
TYPES at the decoded level is a related member pair of the universe pair (below the bound) —
one anonymous constructor over brick 4's level-irrelevant candidate. -/
theorem binaryUniverseMembershipIntroAtBounded {scope : Nat} (env : Nat → Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) (bound : Nat)
    {leftCode rightCode : RawTerm scope}
    (belowBound : LevelExpr.denote levelExpr env < bound)
    (leftSN : IsStronglyNormalizing leftCode) (rightSN : IsStronglyNormalizing rightCode)
    (decodedPairRelated : IsBinaryReducibleTypePairAtBounded env
      (LevelExpr.denote levelExpr env) leftCode rightCode) :
    IsBinaryReducibleMemberPairAtBounded env bound
      (universeCodeCell levelExpr flag) (universeCodeCell levelExpr flag)
      leftCode rightCode :=
  ⟨fun leftMember rightMember =>
      IsStronglyNormalizing leftMember ∧ IsStronglyNormalizing rightMember ∧
        IsBinaryReducibleTypePairAtBounded env (LevelExpr.denote levelExpr env)
          leftMember rightMember,
   binaryUniverseMembershipBounded_levelIrrelevant env bound levelExpr flag belowBound,
   leftSN, rightSN, decodedPairRelated⟩

/-! ## ★ Π-pair reducibility from components -/

/-- ★ **The Π PAIR is binary-related as types from related components** — both candidates
pinned to the canonical member-pair predicate (brick 2's choice-free engine): the domain pair
related, and the codomain pair related at every CANONICAL related argument pair. -/
theorem binaryPiReducibleFromComponentsAtBounded {scope : Nat} (env : Nat → Nat) (lvl : Nat)
    {leftDomain rightDomain : RawTerm scope} {leftCodomain rightCodomain : RawTerm (scope + 1)}
    (domainsRelated : IsBinaryReducibleTypePairAtBounded env lvl leftDomain rightDomain)
    (codomainsRelated : ∀ leftArgument rightArgument : RawTerm scope,
      IsBinaryReducibleMemberPairAtBounded env lvl leftDomain rightDomain
        leftArgument rightArgument →
      IsBinaryReducibleTypePairAtBounded env lvl
        (RawTerm.subst0 leftCodomain leftArgument)
        (RawTerm.subst0 rightCodomain rightArgument)) :
    IsBinaryReducibleTypePairAtBounded env lvl
      (.mkGen .gen_piTyCode () (.childCons leftDomain (.childCons leftCodomain .childNil)))
      (.mkGen .gen_piTyCode ()
        (.childCons rightDomain (.childCons rightCodomain .childNil))) :=
  ⟨_, BinaryReducibleTypeStepBounded.piType
    (fun leftArgument rightArgument leftTerm rightTerm =>
      IsBinaryReducibleMemberPairAtBounded env lvl
        (RawTerm.subst0 leftCodomain leftArgument)
        (RawTerm.subst0 rightCodomain rightArgument) leftTerm rightTerm)
    domainsRelated.reducibleMemberPairCandidate
    (fun leftArgument rightArgument argumentsMember =>
      (codomainsRelated leftArgument rightArgument
        argumentsMember).reducibleMemberPairCandidate)⟩

end FX1Poly.Typed

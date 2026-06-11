import FX1Poly.Typed.KernelBinaryPiFormer
import FX1Poly.Typed.KernelBinaryMemberSN
import FX1Poly.Typed.BoundedFormationArityDispatch

/-! # FX1Poly/Typed/KernelBinaryGenericFormer
    — the binary GENERIC former membership + supplier + the premise-isolated Σ arm (OP1-K2)

The non-Π half of the binary FT's former coverage, mirroring the unary
`BoundedFormationArityDispatch` with the wall discipline:

  * `binaryDataFormationUnderSubstAtBounded` — the table-generic membership: any former with
    a formation row other than Π is, under a closing-substitution PAIR, a binary-reducible
    member pair of its output universe pair, given the output gate and both sides' substituted
    children SN.  The pair's relatedness-as-types is the binary `neutral` arm over the SAME
    table-generic root gates as the unary, applied once per side (subst preserves the root, so
    both cells share the generator's gates) — no SN enters the relatedness at all; SN feeds
    only the universe candidate's conjuncts through the membership intro.
  * `BinaryTelescopeReducibleAtBounded.foldChildrenNormalizingAndOutputBelow` — the supplier
    for arity ≤ 1 (every non-Π/Σ cumulative formation row): ONE binary telescope application
    yields both sides' fold-children SN and the output gate, WALL-FREE — the 1-child member
    pair's SN comes from the binary universe candidate's own conjuncts
    (`binaryStronglyNormalizingPairOfUniverseMemberAtBounded`) and its gate from the pair
    extraction.  The unary's 2-child case is deliberately ABSENT: it used the variable-0
    neutral inhabitant, which the wall forbids — the only 2-child non-Π row is Σ, which gets
    its own premise-isolated arm below.
  * `binaryFundamentalGenFormationSigmaArm` — the Σ-former FT arm, premise-isolated exactly
    like the Π arm (brick 5b): `outputBelowBound` + `codomainOpenSNPair` arrive as premises
    (the wall's extractions), the domain SN pair extracts from the binary universe candidate,
    and the Σ PAIR is related-as-types via the binary `neutral` arm at the concrete
    `gen_sigmaTyCode` row (Σ codes are weak-head normal non-Π/universe/empty/flat heads — in
    this model Σ formers take the SN-product candidate, exactly as in the unary relation).

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Binary non-Π formation membership under a closing-substitution pair, at a SYMBOLIC
generator.**  The binary twin of `dataFormationUnderSubstAtBounded`: substitution distributes
on each side (`subst_nonVar_reduces`), each substituted cell is SN from its children
(`formerCellStronglyNormalizingOfChildren`), and the PAIR is related-as-types by the binary
`neutral` arm over the table-generic root gates applied per side.  One arm for the whole
non-Π binary formation family. -/
theorem binaryDataFormationUnderSubstAtBounded {scope targetScope : Nat}
    {env : Nat → Nat} {bound : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope} {rule : TypingRuleDesc}
    (outputLevel : LevelExpr) (outputFlag : UniverseFlag)
    (leftSubstitution rightSubstitution : RawTermSubst scope targetScope)
    (isFormation : typingRuleDescOf generator = some rule)
    (isNotPiFormer : generator ≠ .gen_piTyCode)
    (belowBound : LevelExpr.denote outputLevel env < bound)
    (leftChildrenNormalizing :
      (foldChildren GenAlgebra.canonical leftSubstitution children).allStronglyNormalizing)
    (rightChildrenNormalizing :
      (foldChildren GenAlgebra.canonical rightSubstitution children).allStronglyNormalizing) :
    IsBinaryReducibleMemberPairAtBounded env bound
      (RawTerm.subst leftSubstitution (universeCodeCell outputLevel outputFlag))
      (RawTerm.subst rightSubstitution (universeCodeCell outputLevel outputFlag))
      (RawTerm.subst leftSubstitution (.mkGen generator payload children))
      (RawTerm.subst rightSubstitution (.mkGen generator payload children)) := by
  rw [subst_universeCodeCell, subst_universeCodeCell,
    RawTerm.subst_nonVar_reduces leftSubstitution (formationRowIsNotVariable isFormation)
      payload children,
    RawTerm.subst_nonVar_reduces rightSubstitution (formationRowIsNotVariable isFormation)
      payload children]
  exact binaryUniverseMembershipIntroAtBounded env outputLevel outputFlag bound belowBound
    (formerCellStronglyNormalizingOfChildren isFormation leftChildrenNormalizing)
    (formerCellStronglyNormalizingOfChildren isFormation rightChildrenNormalizing)
    ⟨fun leftTerm rightTerm =>
        IsStronglyNormalizing leftTerm ∧ IsStronglyNormalizing rightTerm,
      BinaryReducibleTypeStepBounded.neutral
        (formationGenerator_noWeakHeadStep isFormation)
        (formationGenerator_noWeakHeadStep isFormation)
        isNotPiFormer
        (formationRowIsNotUniverse isFormation)
        (formationRowIsNotEmpty isFormation)
        (formationRowIsNotFlat isFormation)
        isNotPiFormer
        (formationRowIsNotUniverse isFormation)
        (formationRowIsNotEmpty isFormation)
        (formationRowIsNotFlat isFormation)⟩

/-- **Binary telescope at the bound ⟹ both folds all-SN AND output gate, arity ≤ 1** — the
wall-free supplier for every non-Π/Σ cumulative formation row.  The 1-child member pair's SN
comes from the binary universe candidate's own conjuncts; its gate from the pair extraction;
the nullary gate from the explicit premise.  The 2-child case is deliberately absent (the
unary discharged it at the variable-0 neutral inhabitant — forbidden by the wall; Σ, the only
2-child non-Π row, has its own premise-isolated arm). -/
theorem BinaryTelescopeReducibleAtBounded.foldChildrenNormalizingAndOutputBelow
    {baseScope targetScope : Nat} {env : Nat → Nat} {bound : Nat} {flag : UniverseFlag}
    {binderShifts : List Nat}
    {children : RawTermChildren binderShifts baseScope}
    {leftSubstitution rightSubstitution : RawTermSubst baseScope targetScope}
    {levels : List LevelExpr}
    (shapeEq : binderShifts = consecutiveShifts 0 levels.length)
    (arityBound : levels.length ≤ 1)
    (nullaryBelowBound : levels = [] → 0 < bound)
    (telescope : BinaryTelescopeReducibleAtBounded env bound bound flag 0 levels.length
      leftSubstitution rightSubstitution levels (shapeEq ▸ children)) :
    (foldChildren GenAlgebra.canonical leftSubstitution children).allStronglyNormalizing ∧
      (foldChildren GenAlgebra.canonical rightSubstitution children).allStronglyNormalizing ∧
      LevelExpr.denote (lmaxAll levels) env < bound := by
  subst shapeEq
  match levels, children, telescope with
  | [], .childNil, _telescope =>
      exact ⟨True.intro, True.intro, nullaryBelowBound rfl⟩
  | [elementLevel], .childCons elementCode .childNil, telescope =>
      have elementMemberPair := telescope.oneChildMember
      have elementBelowBound : LevelExpr.denote elementLevel env < bound := by
        obtain ⟨_elementCandidate, elementCandidateReducible, _elementIn⟩ := elementMemberPair
        exact binaryUniverseCodeReducibleAtBounded_belowBound elementCandidateReducible
      obtain ⟨elementLeftSN, elementRightSN⟩ :=
        binaryStronglyNormalizingPairOfUniverseMemberAtBounded elementMemberPair
      exact ⟨⟨elementLeftSN, True.intro⟩, ⟨elementRightSN, True.intro⟩, elementBelowBound⟩
  | _ :: _ :: _, _children, _telescope =>
      exact nomatch Nat.le_of_succ_le_succ arityBound

/-- ★ **The premise-isolated binary Σ-former FT arm.**  Same premise discipline as the Π arm
(brick 5b): the output gate and the open-codomain SN pair arrive as premises (the wall's
forbidden extractions), the domain SN pair extracts from the binary universe candidate, and
the Σ PAIR is related-as-types via the binary `neutral` arm at the concrete `gen_sigmaTyCode`
row — no component reducibility enters (Σ formers take the SN-product candidate in this
model, exactly as in the unary relation). -/
theorem binaryFundamentalGenFormationSigmaArm {profile : PolyProfile} {scope : Nat}
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
      (sigmaTyCodeCell domain codomain)
      (universeCodeCell (lmaxAll [domainLevel, codomainLevel]) flag) := by
  obtain ⟨sigmaRule, sigmaRow⟩ :
      ∃ rule, typingRuleDescOf Generator.gen_sigmaTyCode = some rule := ⟨_, rfl⟩
  intro _targetScope leftSubstitution rightSubstitution envRelated
  obtain ⟨domainMemberPair, _codomainMemberPairFn⟩ :=
    (telescope leftSubstitution rightSubstitution envRelated).twoChildMembers
  obtain ⟨domainLeftSN, domainRightSN⟩ :=
    binaryStronglyNormalizingPairOfUniverseMemberAtBounded domainMemberPair
  obtain ⟨codomainLeftSN, codomainRightSN⟩ :=
    codomainOpenSNPair leftSubstitution rightSubstitution envRelated
  have sigmaLeftSN :
      IsStronglyNormalizing
        (RawTerm.subst leftSubstitution (sigmaTyCodeCell domain codomain)) := by
    rw [subst_sigmaTyCodeCell]
    exact sigmaTyCode_isStronglyNormalizing_of_domain_codomain domainLeftSN codomainLeftSN
  have sigmaRightSN :
      IsStronglyNormalizing
        (RawTerm.subst rightSubstitution (sigmaTyCodeCell domain codomain)) := by
    rw [subst_sigmaTyCodeCell]
    exact sigmaTyCode_isStronglyNormalizing_of_domain_codomain domainRightSN codomainRightSN
  have sigmaPairRelated :
      IsBinaryReducibleTypePairAtBounded env
        (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env)
        (RawTerm.subst leftSubstitution (sigmaTyCodeCell domain codomain))
        (RawTerm.subst rightSubstitution (sigmaTyCodeCell domain codomain)) := by
    rw [subst_sigmaTyCodeCell, subst_sigmaTyCodeCell]
    exact ⟨fun leftTerm rightTerm =>
        IsStronglyNormalizing leftTerm ∧ IsStronglyNormalizing rightTerm,
      BinaryReducibleTypeStepBounded.neutral
        (formationGenerator_noWeakHeadStep sigmaRow)
        (formationGenerator_noWeakHeadStep sigmaRow)
        (fun rootIsPi => nomatch rootIsPi)
        (formationRowIsNotUniverse sigmaRow)
        (formationRowIsNotEmpty sigmaRow)
        (formationRowIsNotFlat sigmaRow)
        (fun rootIsPi => nomatch rootIsPi)
        (formationRowIsNotUniverse sigmaRow)
        (formationRowIsNotEmpty sigmaRow)
        (formationRowIsNotFlat sigmaRow)⟩
  rw [subst_universeCodeCell, subst_universeCodeCell]
  exact binaryUniverseMembershipIntroAtBounded env (lmaxAll [domainLevel, codomainLevel]) flag
    bound outputBelowBound sigmaLeftSN sigmaRightSN sigmaPairRelated

end FX1Poly.Typed

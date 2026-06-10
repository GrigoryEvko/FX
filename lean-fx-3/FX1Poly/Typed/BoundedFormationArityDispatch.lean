import FX1Poly.Typed.DenoteKeyedBoundedTelescopeProjection
import FX1Poly.Typed.DenoteKeyedBoundedFormerEngine
import FX1Poly.Typed.BoundedDomainInhabitant
import FX1Poly.Typed.BoundedCodomainOpenSN
import FX1Poly.Typed.DenoteKeyedBoundedAssemblyBridge
import FX1Poly.Typed.FormerOutputLevelBounds
import FX1Poly.Typed.GenericDataFormationUnderSubst
import FX1Poly.Typed.FormationTableShapeFacts

/-! # FX1Poly/Typed/BoundedFormationArityDispatch
   — the BOUNDED twin of the by_cases-free dispatch chain (GTL-06, bounded half)

The three bounded dispatch files (`BoundedFormationDispatch` / `BoundedGrownDispatch` /
`BoundedGrownFundamental`) each enumerate the non-Π formation rows in a five-deep `by_cases`
chain feeding per-former bounded membership theorems.  This module supplies the two
table-generic pieces that collapse those chains to ONE generic branch:

  * `TelescopeReducibleAtBounded.foldChildrenNormalizingAndOutputBelow` — the bounded
    arity-dispatch supplier.  From a SINGLE telescope application at `argLevel = bound`
    (no double-apply dance: the non-Π formers classify by the `neutral` arm, which needs
    only SN and the level gates, never a per-argument codomain telescope), it produces
    BOTH the substituted-spine strong normalization in the `foldChildren` spelling AND
    the output-level bound `denote (lmaxAll levels) env < bound` — the gate extraction
    (`universeCodeReducibleAtBounded_belowBound`) per child, joined by `levelMax_lt`.
    The shape equation is over a FREE `binderShifts` index so `subst` eliminates the
    index cast, exactly as in the unbounded supplier.
  * `IsReducibleMemberAtBounded.dataFormationUnderSubstAtBounded` — the symbolic-generator
    bounded membership arm: any former carrying a formation row other than Π is, under a
    closing substitution, a bound-reducible member of its output universe, given the output
    bound and the substituted-children SN.  Substitution distributes by
    `subst_nonVar_reduces`; cell SN is the generic N-child accessibility assembly; the
    reducibility-as-type is the `neutral` arm over the four table-generic root gates
    (`formationGenerator_noWeakHeadStep`, not-Π, `formationRowIsNotUniverse`,
    `formationRowIsNotEmpty`, `formationRowIsNotFlat`).

## Zero-axiom verification

`subst` + `match` + gate extraction + the shipped bounded membership intro
(`universeMembershipIntroAtBounded`); no induction, no `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTypedReducibilityCandidates.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **Bounded telescope at the bound ⟹ fold-children all-SN AND output level below bound, by
arity dispatch.**  Over a FREE `binderShifts` pinned to the consecutive-shifts shape, ONE
application of the bounded telescope relation at `argLevel = bound` yields both halves the
generic bounded membership arm consumes — for every arity the formation table admits.  The
nullary output bound cannot come from children (there are none); it arrives as the explicit
`nullaryBelowBound` gate, which dispatch sites read off the derivation budget. -/
theorem TelescopeReducibleAtBounded.foldChildrenNormalizingAndOutputBelow
    {baseScope targetScope : Nat} {env : Nat → Nat} {bound : Nat} {flag : UniverseFlag}
    {binderShifts : List Nat}
    {children : RawTermChildren binderShifts baseScope}
    {substitution : RawTermSubst baseScope (targetScope + 1)}
    {levels : List LevelExpr}
    (shapeEq : binderShifts = consecutiveShifts 0 levels.length)
    (arityBound : levels.length ≤ 2)
    (nullaryBelowBound : levels = [] → 0 < bound)
    (telescope : TelescopeReducibleAtBounded env bound bound flag 0 levels.length
      substitution levels (shapeEq ▸ children)) :
    RawTermChildren.allStronglyNormalizing
        (foldChildren GenAlgebra.canonical substitution children) ∧
      LevelExpr.denote (lmaxAll levels) env < bound := by
  subst shapeEq
  match levels, children, telescope with
  | [], .childNil, _telescope =>
      exact ⟨True.intro, nullaryBelowBound rfl⟩
  | [elementLevel], .childCons elementCode .childNil, telescope =>
      have elementMember := telescope.oneChildMember
      have elementBelowBound : LevelExpr.denote elementLevel env < bound := by
        obtain ⟨_elementCandidate, elementCandidateReducible, _elementIn⟩ := elementMember
        exact universeCodeReducibleAtBounded_belowBound elementCandidateReducible
      exact ⟨⟨stronglyNormalizing_of_universeMemberAtBounded env bound elementLevel flag _
          elementBelowBound elementMember, True.intro⟩,
        elementBelowBound⟩
  | [domainLevel, codomainLevel],
      .childCons domainCode (.childCons codomainCode .childNil), telescope =>
      obtain ⟨domainMember, codomainMemberFn⟩ := telescope.twoChildMembers
      have domainBelowBound : LevelExpr.denote domainLevel env < bound := by
        obtain ⟨_domainCandidate, domainCandidateReducible, _domainIn⟩ := domainMember
        exact universeCodeReducibleAtBounded_belowBound domainCandidateReducible
      have variableZeroMember := variableZeroMemberOfBoundedUniverseMember domainMember
        domainBelowBound (Nat.le_of_lt domainBelowBound)
      have codomainMember := codomainMemberFn _ variableZeroMember
      have codomainBelowBound : LevelExpr.denote codomainLevel env < bound := by
        obtain ⟨_codomainCandidate, codomainCandidateReducible, _codomainIn⟩ := codomainMember
        exact universeCodeReducibleAtBounded_belowBound codomainCandidateReducible
      exact ⟨⟨stronglyNormalizing_of_universeMemberAtBounded env bound domainLevel flag _
          domainBelowBound domainMember,
        codomainOpenStronglyNormalizing_ofBoundedFilledMember codomainMember, True.intro⟩,
        levelMax_lt domainBelowBound codomainBelowBound⟩
  | _ :: _ :: _ :: _, _children, _telescope =>
      exact nomatch Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ arityBound)

/-- **Bounded non-Π formation membership under a closing substitution, at a SYMBOLIC
generator.**  The bounded twin of `dataFormationUnderSubst`: any former with a formation row
other than Π is, under a closing substitution, a bound-reducible member of its output
universe, given the output-level bound and SN of its substituted children.  Substitution
distributes (`subst_nonVar_reduces`; not-variable by table-miss), cell SN is the generic
N-child accessibility assembly, and the cell's reducibility-as-type at the output level is
the `neutral` arm over the table-generic root gates (no weak-head step, not Π, not the
universe, not the empty code, not a flat code).  One arm for the whole non-Π bounded
formation family — every future data-former row absorbs with zero new lines. -/
theorem IsReducibleMemberAtBounded.dataFormationUnderSubstAtBounded {scope targetScope : Nat}
    {env : Nat → Nat} {bound : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {children : RawTermChildren generator.binderShifts scope} {rule : TypingRuleDesc}
    (outputLevel : LevelExpr) (outputFlag : UniverseFlag)
    (substitution : RawTermSubst scope targetScope)
    (isFormation : typingRuleDescOf generator = some rule)
    (isNotPiFormer : generator ≠ .gen_piTyCode)
    (belowBound : LevelExpr.denote outputLevel env < bound)
    (substitutedChildrenNormalizing :
      (foldChildren GenAlgebra.canonical substitution children).allStronglyNormalizing) :
    IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution (universeCodeCell outputLevel outputFlag))
      (RawTerm.subst substitution (.mkGen generator payload children)) := by
  rw [subst_universeCodeCell,
    RawTerm.subst_nonVar_reduces substitution (formationRowIsNotVariable isFormation)
      payload children]
  exact universeMembershipIntroAtBounded env outputLevel outputFlag bound _ belowBound
    (formerCellStronglyNormalizingOfChildren isFormation substitutedChildrenNormalizing)
    ⟨IsStronglyNormalizing,
      ReducibleTypeStepBounded.neutral
        (formationGenerator_noWeakHeadStep isFormation)
        isNotPiFormer
        (formationRowIsNotUniverse isFormation)
        (formationRowIsNotEmpty isFormation)
        (formationRowIsNotFlat isFormation)⟩

end FX1Poly.Typed

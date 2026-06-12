import FX1Poly.Core.TableParallelReduction
import FX1Poly.Core.StepTableEquivariance
import FX1Poly.Core.RawTermSubst0Commute
import FX1Poly.Core.RawTermSubstPair

/-! # FX1Poly/Core/TableParallelSubstitution — IOTA-T6: parallel equivariance engines

The substitution/renaming closure of the table-driven parallel
reduction, mirroring the bespoke `ParStepSubstRename` +
`ParStepSubstPointwise` pair — but where the bespoke files needed
eighteen per-constructor arms each, the table relation needs ONE redex
arm routed through the IOTA-T2 firing naturality
(`scrutineesFire_subst` / `firesOn?_subst`).  Every future row inherits
all of this from its scope-uniformity certificate.

Layering (each step feeds the next):

  1. `ParStepOverTable.subst` — one fixed substitution applied to both
     sides (the redex arm refires by T2; the variable congruence is
     reflexivity).
  2. `ParStepOverTable.rename` / `.weaken` — corollaries through the
     rename-as-subst factoring and the weakening-as-subst spelling.
  3. The DEPTH engines the template interpreter uses
     (`weakenBy`, `weakenBodyUnderOneBinderBy`,
     `weakenBodyUnderTwoBindersBy`, spine `weakenSpineBy`) preserve
     parallel steps — induction on the depth over 2.
  4. `RawTermSubst.PointwiseParStepOverTable` + binder lifts — two
     substitutions related entrywise, the relation `substPointwise`
     threads.
  5. `ParStepOverTable.substPointwise` — the DIAGONAL lemma: vary the
     substitution AND the term simultaneously (a single parallel step
     is not transitive, so this cannot be composed from two one-sided
     applications).
  6. `subst0_diagonal` / `substPair_diagonal` — the instantiations the
     stability lemma's `substOneInto…` / `substPairInto…` /
     `motiveInstantiated…` template arms fire with.

## Zero-axiom verification

Mutual structural recursion on derivations, the T2 firing-naturality
bricks, defeq `show`-ascriptions through the fold reductions, and
`Nat`-match index helpers.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated per
declaration in `FX1PolyAudit/AuditTableParallelReduction.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## One fixed substitution, both sides -/

mutual

/-- **The parallel table relation is closed under substitution** (one
fixed substitution on both sides) — for any table whose rows are
scope-uniform.  The redex arm refires through the T2 firing naturality
on BOTH the source pattern and the reduced-spine firing; the variable
congruence collapses to reflexivity of the substituted entry. -/
theorem ParStepOverTable.subst {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform) :
    {scope targetScope : Nat} →
    (sigma : RawTermSubst scope targetScope) →
    {source target : RawTerm scope} →
    ParStepOverTable table source target →
    ParStepOverTable table (RawTerm.subst sigma source)
      (RawTerm.subst sigma target)
  | scope, targetScope, sigma, _, _,
      .tableRedex isRow elimPayload spinePar sourceFires fires => by
      rw [RawTerm.subst_nonVar_reduces sigma
        (tableIsUniform _ isRow).isNotVarHead elimPayload _]
      exact .tableRedex isRow _
        (ParStepOverTableChildren.subst tableIsUniform sigma spinePar)
        (IotaRuleDesc.scrutineesFire_subst _ sigma _ _
          (tableIsUniform _ isRow).scrutineesAreUniform sourceFires)
        (IotaRuleDesc.firesOn?_subst _ sigma (tableIsUniform _ isRow)
          elimPayload fires)
  | scope, targetScope, sigma, _, _, .cong gen payload childrenPar => by
      by_cases isVarGen : gen = .gen_var
      case pos =>
        subst isVarGen
        cases childrenPar
        show ParStepOverTable _ (sigma payload) (sigma payload)
        exact ParStepOverTable.refl _
      case neg =>
        rw [RawTerm.subst_nonVar_reduces sigma isVarGen payload _,
          RawTerm.subst_nonVar_reduces sigma isVarGen payload _]
        exact .cong gen _
          (ParStepOverTableChildren.subst tableIsUniform sigma childrenPar)

/-- Spine companion: each pointwise position substitutes at the fold
engine's per-shift lift — the alignment is definitional. -/
theorem ParStepOverTableChildren.subst {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform) :
    {parentScope parentTargetScope : Nat} →
    (sigma : RawTermSubst parentScope parentTargetScope) →
    {binderShifts : List Nat} →
    {children children' : RawTermChildren binderShifts parentScope} →
    ParStepOverTableChildren table children children' →
    ParStepOverTableChildren table (RawTermChildren.subst sigma children)
      (RawTermChildren.subst sigma children')
  | _, _, _, _, _, _, .nil => .nil
  | parentScope, _, sigma, _, _, _,
      @ParStepOverTableChildren.cons _ _ headShift _ _ _ _ _
        headPar tailPar =>
      .cons
        (ParStepOverTable.subst tableIsUniform
          (iterateLiftRaw sigma headShift) headPar)
        (ParStepOverTableChildren.subst tableIsUniform sigma tailPar)

end

/-! ## Rename and weaken corollaries -/

/-- Rename closure through the rename-as-subst factoring. -/
theorem ParStepOverTable.rename {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform)
    {scope targetScope : Nat}
    (someRenaming : RawRenaming scope targetScope)
    {source target : RawTerm scope}
    (parStep : ParStepOverTable table source target) :
    ParStepOverTable table (RawTerm.rename someRenaming source)
      (RawTerm.rename someRenaming target) := by
  rw [RawTerm.rename_eq_subst_ofRenaming someRenaming source,
    RawTerm.rename_eq_subst_ofRenaming someRenaming target]
  exact ParStepOverTable.subst tableIsUniform
    (RawTermSubst.ofRenaming someRenaming) parStep

/-- Spine rename closure through the children rename-as-subst
factoring. -/
theorem ParStepOverTableChildren.rename {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform)
    {parentScope parentTargetScope : Nat}
    (someRenaming : RawRenaming parentScope parentTargetScope)
    {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (childrenPar : ParStepOverTableChildren table children children') :
    ParStepOverTableChildren table
      (RawTermChildren.rename someRenaming children)
      (RawTermChildren.rename someRenaming children') := by
  rw [RawTermChildren.rename_eq_subst_ofRenaming someRenaming children,
    RawTermChildren.rename_eq_subst_ofRenaming someRenaming children']
  exact ParStepOverTableChildren.subst tableIsUniform
    (RawTermSubst.ofRenaming someRenaming) childrenPar

/-- The parallel table relation is stable under the weakening renaming
(`RawTerm.weaken` is definitionally `rename RawRenaming.weaken`). -/
theorem ParStepOverTable.weaken {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform)
    {scope : Nat} {source target : RawTerm scope}
    (parStep : ParStepOverTable table source target) :
    ParStepOverTable table (RawTerm.weaken source)
      (RawTerm.weaken target) :=
  ParStepOverTable.rename tableIsUniform RawRenaming.weaken parStep

/-! ## The interpreter's depth-weakening engines preserve parallel steps -/

/-- `weakenBy` preserves parallel steps — induction on the depth,
one `weaken` per layer. -/
theorem ParStepOverTable.weakenBy {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform)
    {scope : Nat} :
    (depth : Nat) → {source target : RawTerm scope} →
    ParStepOverTable table source target →
    ParStepOverTable table (RawTerm.weakenBy depth source)
      (RawTerm.weakenBy depth target)
  | 0, _, _, parStep => parStep
  | innerDepth + 1, _, _, parStep =>
      ParStepOverTable.weaken tableIsUniform
        (ParStepOverTable.weakenBy tableIsUniform innerDepth parStep)

/-- `weakenBodyUnderOneBinderBy` preserves parallel steps — each layer
is a rename at the one-binder lift of weakening. -/
theorem ParStepOverTable.weakenBodyUnderOneBinderBy
    {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform)
    {scope : Nat} :
    (depth : Nat) → {body body' : RawTerm (scope + 1)} →
    ParStepOverTable table body body' →
    ParStepOverTable table
      (RawTerm.weakenBodyUnderOneBinderBy depth body)
      (RawTerm.weakenBodyUnderOneBinderBy depth body')
  | 0, _, _, parStep => parStep
  | innerDepth + 1, _, _, parStep =>
      ParStepOverTable.rename tableIsUniform
        (RawRenaming.lift RawRenaming.weaken)
        (ParStepOverTable.weakenBodyUnderOneBinderBy tableIsUniform
          innerDepth parStep)

/-- `weakenBodyUnderTwoBindersBy` preserves parallel steps — each layer
is a rename at the two-binder lift of weakening. -/
theorem ParStepOverTable.weakenBodyUnderTwoBindersBy
    {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform)
    {scope : Nat} :
    (depth : Nat) → {body body' : RawTerm (scope + 2)} →
    ParStepOverTable table body body' →
    ParStepOverTable table
      (RawTerm.weakenBodyUnderTwoBindersBy depth body)
      (RawTerm.weakenBodyUnderTwoBindersBy depth body')
  | 0, _, _, parStep => parStep
  | innerDepth + 1, _, _, parStep =>
      ParStepOverTable.rename tableIsUniform
        (RawRenaming.lift (RawRenaming.lift RawRenaming.weaken))
        (ParStepOverTable.weakenBodyUnderTwoBindersBy tableIsUniform
          innerDepth parStep)

/-- Spine `weakenSpineBy` preserves pointwise parallel steps — each
layer is a spine rename at the weakening renaming. -/
theorem ParStepOverTableChildren.weakenSpineBy {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform)
    {binderShifts : List Nat} {scope : Nat} :
    (depth : Nat) →
    {children children' : RawTermChildren binderShifts scope} →
    ParStepOverTableChildren table children children' →
    ParStepOverTableChildren table
      (RawTermChildren.weakenSpineBy depth children)
      (RawTermChildren.weakenSpineBy depth children')
  | 0, _, _, childrenPar => childrenPar
  | innerDepth + 1, _, _, childrenPar =>
      ParStepOverTableChildren.rename tableIsUniform RawRenaming.weaken
        (ParStepOverTableChildren.weakenSpineBy tableIsUniform innerDepth
          childrenPar)

/-! ## Pointwise-related substitutions -/

/-- Two substitutions related entrywise by the parallel table
relation. -/
def RawTermSubst.PointwiseParStepOverTable (table : List IotaRuleDesc)
    {sourceScope targetScope : Nat}
    (first second : RawTermSubst sourceScope targetScope) : Prop :=
  ∀ position, ParStepOverTable table (first position) (second position)

/-- Lifting through one binder preserves pointwise relatedness: the
fresh variable is reflexive, the weakened tail steps by `weaken`. -/
theorem RawTermSubst.lift_pointwiseParStepOverTable
    {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform)
    {sourceScope targetScope : Nat}
    {first second : RawTermSubst sourceScope targetScope}
    (relatedness : RawTermSubst.PointwiseParStepOverTable table
      first second) :
    RawTermSubst.PointwiseParStepOverTable table first.lift second.lift := by
  intro position
  match position with
  | ⟨0, _⟩ => exact ParStepOverTable.refl _
  | ⟨priorPositionValue + 1, positionBound⟩ =>
      show ParStepOverTable table
        (RawTerm.weaken
          (first ⟨priorPositionValue, Nat.lt_of_succ_lt_succ positionBound⟩))
        (RawTerm.weaken
          (second ⟨priorPositionValue, Nat.lt_of_succ_lt_succ positionBound⟩))
      exact ParStepOverTable.weaken tableIsUniform
        (relatedness
          ⟨priorPositionValue, Nat.lt_of_succ_lt_succ positionBound⟩)

/-- Iterated binder lift preserves pointwise relatedness. -/
theorem RawTermSubst.iterateLift_pointwiseParStepOverTable
    {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform)
    {sourceScope targetScope : Nat}
    {first second : RawTermSubst sourceScope targetScope}
    (relatedness : RawTermSubst.PointwiseParStepOverTable table
      first second) :
    (binderDepth : Nat) →
    RawTermSubst.PointwiseParStepOverTable table
      (iterateLiftRaw first binderDepth) (iterateLiftRaw second binderDepth)
  | 0 => relatedness
  | priorDepth + 1 =>
      RawTermSubst.lift_pointwiseParStepOverTable tableIsUniform
        (RawTermSubst.iterateLift_pointwiseParStepOverTable tableIsUniform
          relatedness priorDepth)

/-! ## The diagonal substitution lemma -/

mutual

/-- **Diagonal parallel substitution over the table**: pointwise-related
substitutions applied across a parallel step yield a parallel step —
varying BOTH the substitution and the term.  The redex arm refires by
T2 firing naturality at the source-side substitution (the pattern) and
the target-side substitution (the reduced-spine firing); the variable
congruence is exactly the pointwise hypothesis at the variable's
index. -/
theorem ParStepOverTable.substPointwise {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform) :
    {scope targetScope : Nat} → {source target : RawTerm scope} →
    ParStepOverTable table source target →
    {sigma tau : RawTermSubst scope targetScope} →
    RawTermSubst.PointwiseParStepOverTable table sigma tau →
    ParStepOverTable table (RawTerm.subst sigma source)
      (RawTerm.subst tau target)
  | scope, targetScope, _, _,
      .tableRedex isRow elimPayload spinePar sourceFires fires,
      sigma, tau, pointwiseRelated => by
      rw [RawTerm.subst_nonVar_reduces sigma
        (tableIsUniform _ isRow).isNotVarHead elimPayload _]
      exact .tableRedex isRow _
        (ParStepOverTableChildren.substPointwise tableIsUniform spinePar
          pointwiseRelated)
        (IotaRuleDesc.scrutineesFire_subst _ sigma _ _
          (tableIsUniform _ isRow).scrutineesAreUniform sourceFires)
        (IotaRuleDesc.firesOn?_subst _ tau (tableIsUniform _ isRow)
          elimPayload fires)
  | scope, targetScope, _, _, .cong gen payload childrenPar,
      sigma, tau, pointwiseRelated => by
      by_cases isVarGen : gen = .gen_var
      case pos =>
        subst isVarGen
        cases childrenPar
        show ParStepOverTable _ (sigma payload) (tau payload)
        exact pointwiseRelated payload
      case neg =>
        rw [RawTerm.subst_nonVar_reduces sigma isVarGen payload _,
          RawTerm.subst_nonVar_reduces tau isVarGen payload _]
        exact .cong gen _
          (ParStepOverTableChildren.substPointwise tableIsUniform
            childrenPar pointwiseRelated)

/-- Spine companion of the diagonal lemma: each position iterate-lifts
both substitutions by its binder shift. -/
theorem ParStepOverTableChildren.substPointwise {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform) :
    {parentScope parentTargetScope : Nat} → {binderShifts : List Nat} →
    {children children' : RawTermChildren binderShifts parentScope} →
    ParStepOverTableChildren table children children' →
    {sigma tau : RawTermSubst parentScope parentTargetScope} →
    RawTermSubst.PointwiseParStepOverTable table sigma tau →
    ParStepOverTableChildren table (RawTermChildren.subst sigma children)
      (RawTermChildren.subst tau children')
  | _, _, _, _, _, .nil, _, _, _ => .nil
  | parentScope, _, _, _, _,
      @ParStepOverTableChildren.cons _ _ headShift _ _ _ _ _
        headPar tailPar, _sigma, _tau, pointwiseRelated =>
      .cons
        (ParStepOverTable.substPointwise tableIsUniform headPar
          (RawTermSubst.iterateLift_pointwiseParStepOverTable tableIsUniform
            pointwiseRelated headShift))
        (ParStepOverTableChildren.substPointwise tableIsUniform tailPar
          pointwiseRelated)

end

/-! ## The `subst0` / `substPair` diagonals (the template-arm engines) -/

/-- The `singleton` substitutions of two related arguments are pointwise
related: position 0 carries the argument step, higher positions are
identical. -/
theorem RawTermSubst.singleton_pointwiseParStepOverTable
    {table : List IotaRuleDesc} {scope : Nat} {arg arg' : RawTerm scope}
    (argPar : ParStepOverTable table arg arg') :
    RawTermSubst.PointwiseParStepOverTable table
      (RawTermSubst.singleton arg) (RawTermSubst.singleton arg') := by
  intro position
  match position with
  | ⟨0, _⟩ => exact argPar
  | ⟨_ + 1, _⟩ => exact ParStepOverTable.refl _

/-- The `cons` extension of pointwise-related substitutions by related
heads is pointwise related. -/
theorem RawTermSubst.cons_pointwiseParStepOverTable
    {table : List IotaRuleDesc} {scope targetScope : Nat}
    {headTerm headTerm' : RawTerm targetScope}
    {tailSubst tailSubst' : RawTermSubst scope targetScope}
    (headPar : ParStepOverTable table headTerm headTerm')
    (tailRelatedness : RawTermSubst.PointwiseParStepOverTable table
      tailSubst tailSubst') :
    RawTermSubst.PointwiseParStepOverTable table
      (RawTermSubst.cons headTerm tailSubst)
      (RawTermSubst.cons headTerm' tailSubst') := by
  intro position
  match position with
  | ⟨0, _⟩ => exact headPar
  | ⟨priorPositionValue + 1, positionBound⟩ =>
      exact tailRelatedness
        ⟨priorPositionValue, Nat.lt_of_succ_lt_succ positionBound⟩

/-- The `pair` substitutions of related inner/outer arguments are
pointwise related. -/
theorem RawTermSubst.pair_pointwiseParStepOverTable
    {table : List IotaRuleDesc} {scope : Nat}
    {innerArg innerArg' outerArg outerArg' : RawTerm scope}
    (innerPar : ParStepOverTable table innerArg innerArg')
    (outerPar : ParStepOverTable table outerArg outerArg') :
    RawTermSubst.PointwiseParStepOverTable table
      (RawTermSubst.pair innerArg outerArg)
      (RawTermSubst.pair innerArg' outerArg') :=
  RawTermSubst.cons_pointwiseParStepOverTable innerPar
    (RawTermSubst.singleton_pointwiseParStepOverTable outerPar)

/-- **The one-binder diagonal**: substituting a parallel-reduced
argument into a parallel-reduced body parallel-reduces — the engine for
the `substOneInto…` and `motiveInstantiatedWith` template arms. -/
theorem ParStepOverTable.subst0_diagonal {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform)
    {scope : Nat} {body body' : RawTerm (scope + 1)}
    {arg arg' : RawTerm scope}
    (bodyPar : ParStepOverTable table body body')
    (argPar : ParStepOverTable table arg arg') :
    ParStepOverTable table (RawTerm.subst0 body arg)
      (RawTerm.subst0 body' arg') :=
  ParStepOverTable.substPointwise tableIsUniform bodyPar
    (RawTermSubst.singleton_pointwiseParStepOverTable argPar)

/-- **The two-binder diagonal**: the engine for the `substPairInto…`
and `motiveInstantiatedWithPair` template arms. -/
theorem ParStepOverTable.substPair_diagonal {table : List IotaRuleDesc}
    (tableIsUniform : ∀ rule, rule ∈ table → rule.IsScopeUniform)
    {scope : Nat} {body body' : RawTerm (scope + 2)}
    {innerArg innerArg' outerArg outerArg' : RawTerm scope}
    (bodyPar : ParStepOverTable table body body')
    (innerPar : ParStepOverTable table innerArg innerArg')
    (outerPar : ParStepOverTable table outerArg outerArg') :
    ParStepOverTable table (RawTerm.substPair body innerArg outerArg)
      (RawTerm.substPair body' innerArg' outerArg') :=
  ParStepOverTable.substPointwise tableIsUniform bodyPar
    (RawTermSubst.pair_pointwiseParStepOverTable innerPar outerPar)

end FX1Poly.Core

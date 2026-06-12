import FX1Poly.Core.IotaRuleTable
import FX1Poly.Core.RawTermSubst0Commute
import FX1Poly.Core.RawTermSubstLiftWeaken
import FX1Poly.Core.StructuralInductionPrimitives
import FX1Poly.Core.StepRename

/-! # FX1Poly/Core/IotaTableEquivarianceSubstrate — IOTA-T2 substrate

The commutation bricks for the GENERIC template-interpreter
equivariance (`interpretTemplate?` commutes with substitution by ONE
induction over `ReductTemplate` — the theorem that replaces the
seventeen per-rule substitution arms at the canonicality flip).  Each
brick relates one interpreter ingredient to its image under a
substitution `sigma`, with binder depth handled by the fold engine's
own `iterateLiftRaw` (no bespoke lift-iterate):

  * the shift-erased VIEW (`ScopedChild.substView`,
    `toScopedChildren_subst`, `listEntryAt?_map`) — slot lookup on a
    substituted spine is the substituted lookup;
  * the per-shift PROJECTIONS (`atShiftZero?/One?/Two?_substView`) —
    projecting after substitution is substituting (under 0/1/2 lifts)
    after projecting;
  * the DEPTH WEAKENINGS (`weakenBy_subst`,
    `weakenBodyUnderOneBinderBy_subst`,
    `weakenBodyUnderTwoBindersBy_subst`) — weakening under template
    binders is natural in the substitution, via the under-binder
    naturality squares (`subst_liftLift_renameLiftWeaken` and its
    two-binder twin, both by the
    `rename_subst_commute`/`subst_rename_commute`/pointwise recipe);
  * slot REPLACEMENT (`replaceChildAt?_subst`) — the reassembly
    primitive is natural in the substitution.

The spine-level `weakenSpineBy` naturality (the `reassembledReplacing`
arm's remaining brick) and the payload scope-uniformity certificates
land with the main induction.

## Zero-axiom verification

Structural inductions, the shipped commute/compose/pointwise fold
machinery, and `rfl` pins.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated per
declaration in `FX1PolyAudit/AuditIotaTableEquivariance.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## The fold engine's lift-iterate, pinned on substitutions -/

/-- `iterateLiftRaw` at depth 0 is the substitution itself. -/
theorem iterateLiftRawSubst_zero {scope targetScope : Nat}
    (sigma : RawTermSubst scope targetScope) :
    iterateLiftRaw sigma 0 = sigma := rfl

/-- `iterateLiftRaw` peels one `RawTermSubst.lift` per depth step. -/
theorem iterateLiftRawSubst_succ {scope targetScope : Nat}
    (sigma : RawTermSubst scope targetScope) (depth : Nat) :
    iterateLiftRaw sigma (depth + 1) =
      RawTermSubst.lift (iterateLiftRaw sigma depth) := rfl

/-! ## The shift-erased view under substitution -/

/-- Substitute a scoped child: the child term substitutes under its own
binder shift (the fold engine's `iterateLiftRaw`). -/
def ScopedChild.substView {scope targetScope : Nat}
    (sigma : RawTermSubst scope targetScope) :
    ScopedChild scope → ScopedChild targetScope
  | ⟨binderShift, childTerm⟩ =>
      ⟨binderShift, RawTerm.subst (iterateLiftRaw sigma binderShift) childTerm⟩

/-- Positional lookup commutes with `List.map`. -/
theorem listEntryAt?_map {entryType resultType : Type}
    (transform : entryType → resultType) :
    (entries : List entryType) → (position : Nat) →
    listEntryAt? (entries.map transform) position =
      (listEntryAt? entries position).map transform
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: restEntries, position + 1 =>
      listEntryAt?_map transform restEntries position

/-- The shift-erased view of a substituted spine is the per-child
substituted view. -/
theorem RawTermChildren.toScopedChildren_subst
    {parentSourceScope parentTargetScope : Nat}
    (sigma : RawTermSubst parentSourceScope parentTargetScope) :
    {binderShifts : List Nat} →
    (children : RawTermChildren binderShifts parentSourceScope) →
    (RawTermChildren.subst sigma children).toScopedChildren =
      children.toScopedChildren.map (ScopedChild.substView sigma)
  | _, .childNil => rfl
  | _, .childCons childHead childTail =>
      congrArg (List.cons _)
        (RawTermChildren.toScopedChildren_subst sigma childTail)

namespace ScopedChild

/-- Shift-0 projection commutes with the substituted view. -/
theorem atShiftZero?_substView {scope targetScope : Nat}
    (sigma : RawTermSubst scope targetScope) :
    (child : ScopedChild scope) →
    (child.substView sigma).atShiftZero? =
      child.atShiftZero?.map (RawTerm.subst sigma)
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => rfl

/-- Shift-1 projection commutes with the substituted view (one lift). -/
theorem atShiftOne?_substView {scope targetScope : Nat}
    (sigma : RawTermSubst scope targetScope) :
    (child : ScopedChild scope) →
    (child.substView sigma).atShiftOne? =
      child.atShiftOne?.map (RawTerm.subst (RawTermSubst.lift sigma))
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨_ + 2, _⟩ => rfl

/-- Shift-2 projection commutes with the substituted view (two lifts). -/
theorem atShiftTwo?_substView {scope targetScope : Nat}
    (sigma : RawTermSubst scope targetScope) :
    (child : ScopedChild scope) →
    (child.substView sigma).atShiftTwo? =
      child.atShiftTwo?.map
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift sigma)))
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨_ + 3, _⟩ => rfl

end ScopedChild

/-! ## Depth-weakening naturality -/

/-- Weakening under `depth` template binders is natural in the
substitution: substituting at the lifted depth after weakening is
weakening after substituting. -/
theorem RawTerm.weakenBy_subst {scope targetScope : Nat}
    (sigma : RawTermSubst scope targetScope) :
    (depth : Nat) → (term : RawTerm scope) →
    RawTerm.subst (iterateLiftRaw sigma depth) (RawTerm.weakenBy depth term) =
      RawTerm.weakenBy depth (RawTerm.subst sigma term)
  | 0, _ => rfl
  | innerDepth + 1, term => by
      dsimp only [RawTerm.weakenBy]
      rw [iterateLiftRawSubst_succ]
      rw [RawTerm.subst_lift_weaken]
      rw [RawTerm.weakenBy_subst sigma innerDepth term]

/-- The under-ONE-binder naturality square: substituting under two
lifts after inserting a fresh middle binder is inserting after
substituting under one lift.  The `rename_subst_commute` /
`subst_rename_commute` / `subst_pointwise` recipe. -/
theorem RawTerm.subst_liftLift_renameLiftWeaken {scope targetScope : Nat}
    (tau : RawTermSubst scope targetScope) (body : RawTerm (scope + 1)) :
    RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift tau))
        (RawTerm.rename (RawRenaming.lift RawRenaming.weaken) body) =
      RawTerm.rename (RawRenaming.lift RawRenaming.weaken)
        (RawTerm.subst (RawTermSubst.lift tau) body) := by
  rw [RawTerm.rename_subst_commute, RawTerm.subst_rename_commute]
  apply RawTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨priorPosition + 1, _⟩ =>
      show RawTerm.weaken (RawTerm.weaken _) =
        RawTerm.rename (RawRenaming.lift RawRenaming.weaken)
          (RawTerm.weaken _)
      rw [RawTerm.rename_lift_weaken, ← RawTerm.weaken_eq_rename]

/-- The under-TWO-binder naturality square (the `substPair` /
two-binder-motive leg). -/
theorem RawTerm.subst_liftLiftLift_renameLiftLiftWeaken
    {scope targetScope : Nat}
    (tau : RawTermSubst scope targetScope) (body : RawTerm (scope + 2)) :
    RawTerm.subst
        (RawTermSubst.lift (RawTermSubst.lift (RawTermSubst.lift tau)))
        (RawTerm.rename
          (RawRenaming.lift (RawRenaming.lift RawRenaming.weaken)) body) =
      RawTerm.rename
        (RawRenaming.lift (RawRenaming.lift RawRenaming.weaken))
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift tau)) body) := by
  rw [RawTerm.rename_subst_commute, RawTerm.subst_rename_commute]
  apply RawTerm.subst_pointwise
  intro position
  match position with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨priorPosition + 2, _⟩ =>
      show RawTerm.weaken (RawTerm.weaken (RawTerm.weaken _)) =
        RawTerm.rename
          (RawRenaming.lift (RawRenaming.lift RawRenaming.weaken))
          (RawTerm.weaken (RawTerm.weaken _))
      rw [RawTerm.rename_lift_weaken, RawTerm.rename_lift_weaken,
        ← RawTerm.weaken_eq_rename]

/-- One-binder body weakening under `depth` template binders is natural
in the substitution (the motive / `subst0`-body leg). -/
theorem RawTerm.weakenBodyUnderOneBinderBy_subst {scope targetScope : Nat}
    (sigma : RawTermSubst scope targetScope) :
    (depth : Nat) → (body : RawTerm (scope + 1)) →
    RawTerm.subst (RawTermSubst.lift (iterateLiftRaw sigma depth))
        (RawTerm.weakenBodyUnderOneBinderBy depth body) =
      RawTerm.weakenBodyUnderOneBinderBy depth
        (RawTerm.subst (RawTermSubst.lift sigma) body)
  | 0, _ => rfl
  | innerDepth + 1, body => by
      dsimp only [RawTerm.weakenBodyUnderOneBinderBy]
      rw [iterateLiftRawSubst_succ]
      rw [RawTerm.subst_liftLift_renameLiftWeaken]
      rw [RawTerm.weakenBodyUnderOneBinderBy_subst sigma innerDepth body]

/-- Two-binder body weakening under `depth` template binders is natural
in the substitution (the `idJ`-motive / `substPair`-body leg). -/
theorem RawTerm.weakenBodyUnderTwoBindersBy_subst {scope targetScope : Nat}
    (sigma : RawTermSubst scope targetScope) :
    (depth : Nat) → (body : RawTerm (scope + 2)) →
    RawTerm.subst
        (RawTermSubst.lift (RawTermSubst.lift (iterateLiftRaw sigma depth)))
        (RawTerm.weakenBodyUnderTwoBindersBy depth body) =
      RawTerm.weakenBodyUnderTwoBindersBy depth
        (RawTerm.subst (RawTermSubst.lift (RawTermSubst.lift sigma)) body)
  | 0, _ => rfl
  | innerDepth + 1, body => by
      dsimp only [RawTerm.weakenBodyUnderTwoBindersBy]
      rw [iterateLiftRawSubst_succ]
      rw [RawTerm.subst_liftLiftLift_renameLiftLiftWeaken]
      rw [RawTerm.weakenBodyUnderTwoBindersBy_subst sigma innerDepth body]

/-! ## Slot replacement under substitution -/

/-- Slot replacement is natural in the substitution: replacing then
substituting is substituting then replacing with the substituted
replacement. -/
theorem RawTermChildren.replaceChildAt?_subst
    {parentSourceScope parentTargetScope : Nat}
    (sigma : RawTermSubst parentSourceScope parentTargetScope) :
    {binderShifts : List Nat} →
    (children : RawTermChildren binderShifts parentSourceScope) →
    (slot : Nat) → (replacement : RawTerm parentSourceScope) →
    (children.replaceChildAt? slot replacement).map
        (RawTermChildren.subst sigma) =
      (RawTermChildren.subst sigma children).replaceChildAt? slot
        (RawTerm.subst sigma replacement)
  | _, .childNil, _, _ => rfl
  | _, .childCons (shift := 0) childHead childTail, 0, replacement => rfl
  | _, .childCons (shift := _ + 1) childHead childTail, 0, replacement => rfl
  | _, .childCons childHead childTail, slot + 1, replacement => by
      show ((childTail.replaceChildAt? slot replacement).map
          (RawTermChildren.childCons childHead ·)).map
            (RawTermChildren.subst sigma)
        = ((RawTermChildren.subst sigma childTail).replaceChildAt? slot
            (RawTerm.subst sigma replacement)).map
          (RawTermChildren.childCons
            (RawTerm.subst (iterateLiftRaw sigma _) childHead) ·)
      rw [← RawTermChildren.replaceChildAt?_subst sigma childTail
        slot replacement]
      cases childTail.replaceChildAt? slot replacement with
      | none => rfl
      | some replacedTail => rfl

end FX1Poly.Core

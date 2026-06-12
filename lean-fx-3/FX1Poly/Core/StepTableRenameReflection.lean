import FX1Poly.Core.StepTableEquivariance
import FX1Poly.Core.StructuralInductionPrimitives
import FX1Poly.Core.RawTermChildrenUnique

/-! # FX1Poly/Core/StepTableRenameReflection — the pattern test REFLECTS under renaming

`StepTableEquivariance` ships the FORWARD direction: a fired row refires on
the substituted spine.  The bespoke `Step.reflectRename` (the 753-line
per-iota eliminator dispatch) needs the BACKWARD direction: a row that fires
on the RENAMED spine already fired on the original.  This holds for renaming
(not general substitution!) because a renaming preserves the head generator
of every cell — a variable stays a variable, a constructor keeps its
constructor — so the slot pattern test answers the same question on both
sides, conditional on the same scope-uniformity certificates the forward
direction uses.

This file lands the dispatcher layer of that reflection:

  * `scrutineeSlotLookup_rename` — the shift-0 slot lookup on a renamed
    spine is the renamed original lookup (the rename-as-subst bridge
    composed with the substituted-view projection bricks);
  * `IotaRuleDesc.scrutineeSpecFires_reflectRename` — ONE spec's pattern
    test reflects: the renamed slot's pinned head forces the original
    slot's head (renaming preserves heads), and the guard answers the
    same by its scope-uniformity clause;
  * `IotaRuleDesc.scrutineesFire_reflectRename` — the spec-list
    conjunction reflects, spec by spec.

The follow-on bricks (`interpretTarget?` isSome-reflection, the assembled
`StepOverTable.reflectRename`) consume these to replace the bespoke
eliminator with ONE table-generic proof.

## Zero-axiom verification

Firing inversion via the shipped `scrutineeSpecFires_extractsHead`,
defeq-ascription through the matcher/dite reductions, the substrate's
view/projection naturality bricks, and structural recursion over the spec
list.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Gated per declaration in
`FX1PolyAudit/AuditIotaTableEquivariance.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## The renamed slot lookup -/

/-- The shift-0 scrutinee lookup on a RENAMED spine is the renamed
original lookup: rename is subst at the variable injection, the
substituted view maps positionally, and the shift-0 projection commutes
with the view (the binder shift is preserved, and at shift 0 the
iterated lift is the substitution itself). -/
theorem scrutineeSlotLookup_rename {scope targetScope : Nat}
    (rho : RawRenaming scope targetScope)
    {binderShifts : List Nat}
    (spine : RawTermChildren binderShifts scope) (slot : Nat) :
    (scopedChildAt? (RawTermChildren.rename rho spine).toScopedChildren
        slot).bind ScopedChild.atShiftZero?
      = ((scopedChildAt? spine.toScopedChildren slot).bind
          ScopedChild.atShiftZero?).map (RawTerm.rename rho) := by
  rw [RawTermChildren.rename_eq_subst_ofRenaming rho spine,
    RawTermChildren.toScopedChildren_subst
      (RawTermSubst.ofRenaming rho) spine]
  dsimp only [scopedChildAt?]
  rw [listEntryAt?_map]
  cases originSlot : listEntryAt? spine.toScopedChildren slot with
  | none => rfl
  | some scrutineeChild =>
      rw [optionSomeMap, optionSomeBindExplicit, optionSomeBindExplicit,
        ScopedChild.atShiftZero?_substView]
      cases originShiftZero : scrutineeChild.atShiftZero? with
      | none => rfl
      | some scrutineeTerm =>
          rw [optionSomeMap, optionSomeMap,
            RawTerm.rename_eq_subst_ofRenaming rho scrutineeTerm]

/-! ## Spec-level reflection -/

/-- ONE scrutinee spec's pattern test REFLECTS under renaming: the
renamed slot's pinned head forces the original slot's head (a renaming
keeps a variable a variable and a constructor its constructor), and the
guard (if any) answers the same by its scope-uniformity clause. -/
theorem IotaRuleDesc.scrutineeSpecFires_reflectRename (rule : IotaRuleDesc)
    {scope targetScope : Nat} (rho : RawRenaming scope targetScope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope)
    {spec : ScrutineeSpec} (specIsUniform : spec.IsScopeUniform)
    (renamedFires :
      rule.scrutineeSpecFires (RawTermChildren.rename rho spine) spec
        = true) :
    rule.scrutineeSpecFires spine spec = true := by
  obtain ⟨isNotVarSpecHead, guardIsUniform⟩ := specIsUniform
  cases childLookup : (scopedChildAt? spine.toScopedChildren
      spec.slot).bind ScopedChild.atShiftZero? with
  | none =>
      exfalso
      dsimp only [IotaRuleDesc.scrutineeSpecFires] at renamedFires
      rw [scrutineeSlotLookup_rename rho spine spec.slot, childLookup]
        at renamedFires
      exact Bool.noConfusion renamedFires
  | some scrutineeCell =>
    cases scrutineeCell with
    | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
      by_cases isVarHead : scrutineeGenerator = .gen_var
      · -- a var-headed slot renames to a var-headed slot, whose pinned
        -- head would have to BE the declared head — contradicting the
        -- spec's non-var certificate
        exfalso
        subst isVarHead
        have childrenAreNil : scrutineeChildren = .childNil :=
          RawTermChildren.eq_childNil scrutineeChildren
        subst childrenAreNil
        have renamedVarLookup :
            (scopedChildAt?
                (RawTermChildren.rename rho spine).toScopedChildren
                spec.slot).bind ScopedChild.atShiftZero?
            = some (.mkGen .gen_var (rho scrutineePayload) .childNil) := by
          rw [scrutineeSlotLookup_rename rho spine spec.slot, childLookup,
            optionSomeMap]
          rfl
        exact isNotVarSpecHead
          (rule.scrutineeSpecFires_extractsHead renamedFires
            renamedVarLookup).symm
      · -- a non-var head survives the rename intact; the renamed firing
        -- pins it to the declared head, so the ORIGINAL slot already
        -- matches — and the guard answers the same by uniformity
        have renamedLookup :
            (scopedChildAt?
                (RawTermChildren.rename rho spine).toScopedChildren
                spec.slot).bind ScopedChild.atShiftZero?
            = some (.mkGen scrutineeGenerator
                (Generator.payload_scope_invariant_of_not_var
                  isVarHead scope targetScope ▸ scrutineePayload)
                (foldChildren GenAlgebra.canonical rho
                  scrutineeChildren)) := by
          rw [scrutineeSlotLookup_rename rho spine spec.slot, childLookup,
            optionSomeMap,
            RawTerm.rename_nonVar_reduces rho isVarHead scrutineePayload
              scrutineeChildren]
        have isDeclaredHead : scrutineeGenerator = spec.head :=
          rule.scrutineeSpecFires_extractsHead renamedFires renamedLookup
        subst isDeclaredHead
        -- the RENAMED guard verdict, with the matcher/dite/Eq.rec
        -- reductions collapsed by defeq ascription
        have renamedGuardPasses :
            (match spec.payloadGuard? with
              | none => true
              | some payloadGuard =>
                  payloadGuard targetScope
                    (Generator.payload_scope_invariant_of_not_var
                      isVarHead scope targetScope ▸ scrutineePayload))
            = true := by
          have renamedDite :
              (if isHead : spec.head = spec.head then
                (match spec.payloadGuard? with
                  | none => true
                  | some payloadGuard =>
                      payloadGuard targetScope
                        (Eq.rec (motive := fun matchedHead _ =>
                            matchedHead.payload targetScope)
                          (cast (Generator.payload_scope_invariant_of_not_var
                            isVarHead scope targetScope) scrutineePayload)
                          isHead))
              else false) = true := by
            dsimp only [IotaRuleDesc.scrutineeSpecFires] at renamedFires
            rw [renamedLookup] at renamedFires
            exact renamedFires
          rw [dif_pos rfl] at renamedDite
          exact renamedDite
        -- refire on the ORIGINAL spine
        dsimp only [IotaRuleDesc.scrutineeSpecFires]
        rw [childLookup]
        show (if isHead : spec.head = spec.head then
            (match spec.payloadGuard? with
              | none => true
              | some payloadGuard =>
                  payloadGuard scope
                    (Eq.rec (motive := fun matchedHead _ =>
                        matchedHead.payload scope)
                      scrutineePayload isHead))
          else false) = true
        rw [dif_pos rfl]
        cases guardShape : spec.payloadGuard? with
        | none => rfl
        | some payloadGuard =>
            have guardCommutes :
                ∀ (guardSourceScope guardTargetScope : Nat)
                  (isNotVar : spec.head ≠ .gen_var)
                  (matchedPayload : spec.head.payload guardSourceScope),
                  payloadGuard guardTargetScope
                    (cast (Generator.payload_scope_invariant_of_not_var
                      isNotVar guardSourceScope guardTargetScope)
                      matchedPayload)
                  = payloadGuard guardSourceScope matchedPayload := by
              rw [guardShape] at guardIsUniform
              exact guardIsUniform
            have guardPassedAtTarget :
                payloadGuard targetScope
                  (cast (Generator.payload_scope_invariant_of_not_var
                    isVarHead scope targetScope) scrutineePayload)
                = true := by
              rw [guardShape] at renamedGuardPasses
              exact renamedGuardPasses
            exact (guardCommutes scope targetScope isVarHead
              scrutineePayload).symm.trans guardPassedAtTarget

/-- The full pattern test reflects under renaming, spec by spec. -/
theorem IotaRuleDesc.scrutineesFire_reflectRename (rule : IotaRuleDesc)
    {scope targetScope : Nat} (rho : RawRenaming scope targetScope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    (specs : List ScrutineeSpec) →
    ScrutineeSpecsAreScopeUniform specs →
    rule.scrutineesFire (RawTermChildren.rename rho spine) specs = true →
    rule.scrutineesFire spine specs = true
  | [], _, _ => rfl
  | spec :: restSpecs, specsAreUniform, allFire => by
      obtain ⟨specIsUniform, restAreUniform⟩ := specsAreUniform
      dsimp only [IotaRuleDesc.scrutineesFire] at allFire ⊢
      obtain ⟨specFires, restFire⟩ := andEqTrueSplit allFire
      rw [rule.scrutineeSpecFires_reflectRename rho spine specIsUniform
          specFires,
        rule.scrutineesFire_reflectRename rho spine restSpecs
          restAreUniform restFire]
      rfl

end FX1Poly.Core

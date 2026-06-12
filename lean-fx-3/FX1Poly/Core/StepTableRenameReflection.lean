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

/-! ## Stage EQUATIONS at the rename instantiation

The forward equivariance lemmas are found-IMPLICATIONS because a general
substitution can turn a failing head test into a passing one (a variable
maps to an arbitrary cell).  A RENAMING cannot: variables stay variables,
so every interpreter stage satisfies a total `Option.map` EQUATION — the
two-sided form that yields both the forward transport and the backward
reflection in one statement.  These equations feed the interpreter
isSome-reflection (the `reflectRename` assembly's missing leg). -/

/-- Rename on a variable cell is the renamed-position variable cell
(definitional — the fold's variable arm). -/
theorem RawTerm.rename_var_reduces {scope targetScope : Nat}
    (rho : RawRenaming scope targetScope) (varPosition : Fin scope) :
    RawTerm.rename rho (.mkGen .gen_var varPosition .childNil)
      = .mkGen .gen_var (rho varPosition) .childNil := rfl

/-- The shift-erased children view of a renamed cell is the
substituted-at-the-injection view of the original cell's children: a
variable has no children on either side, and a non-variable keeps its
children spine (renamed), which views positionally. -/
theorem RawTerm.scopedChildrenView_rename {scope targetScope : Nat}
    (rho : RawRenaming scope targetScope) :
    (sourceTerm : RawTerm scope) →
    (RawTerm.rename rho sourceTerm).scopedChildrenView
      = sourceTerm.scopedChildrenView.map
          (ScopedChild.substView (RawTermSubst.ofRenaming rho))
  | .mkGen someGenerator somePayload someChildren => by
      by_cases isVarGen : someGenerator = .gen_var
      · subst isVarGen
        have childrenAreNil : someChildren = .childNil :=
          RawTermChildren.eq_childNil someChildren
        subst childrenAreNil
        rfl
      · rw [RawTerm.rename_nonVar_reduces rho isVarGen somePayload
          someChildren]
        dsimp only [RawTerm.scopedChildrenView]
        rw [show foldChildren GenAlgebra.canonical rho someChildren
            = RawTermChildren.rename rho someChildren from rfl,
          RawTermChildren.rename_eq_subst_ofRenaming rho someChildren,
          RawTermChildren.toScopedChildren_subst
            (RawTermSubst.ofRenaming rho) someChildren]

/-- The derived scrutinee on a renamed spine is the renamed derived
scrutinee — total equation form. -/
theorem IotaRuleDesc.scrutineeTermAt?_rename (rule : IotaRuleDesc)
    {scope targetScope : Nat} (rho : RawRenaming scope targetScope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope)
    (scrutineeIndex : Nat) :
    rule.scrutineeTermAt? scrutineeIndex (RawTermChildren.rename rho spine)
      = (rule.scrutineeTermAt? scrutineeIndex spine).map
          (RawTerm.rename rho) := by
  dsimp only [IotaRuleDesc.scrutineeTermAt?]
  cases specLookup : rule.scrutineeSpecAt? scrutineeIndex with
  | none => rfl
  | some spec =>
      rw [optionSomeBindExplicit, optionSomeBindExplicit]
      exact scrutineeSlotLookup_rename rho spine spec.slot

/-- The derived scrutinee-children view on a renamed spine is the
substituted-at-the-injection view of the original — total equation
form. -/
theorem IotaRuleDesc.scrutineeChildrenAt?_rename (rule : IotaRuleDesc)
    {scope targetScope : Nat} (rho : RawRenaming scope targetScope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope)
    (scrutineeIndex : Nat) :
    rule.scrutineeChildrenAt? scrutineeIndex
        (RawTermChildren.rename rho spine)
      = (rule.scrutineeChildrenAt? scrutineeIndex spine).map
          (List.map (ScopedChild.substView (RawTermSubst.ofRenaming rho))) := by
  dsimp only [IotaRuleDesc.scrutineeChildrenAt?]
  rw [rule.scrutineeTermAt?_rename rho spine scrutineeIndex]
  cases termLookup : rule.scrutineeTermAt? scrutineeIndex spine with
  | none => rfl
  | some scrutineeTerm =>
      rw [optionSomeMap, optionSomeMap, optionSomeMap, optionSomeMap,
        RawTerm.scopedChildrenView_rename rho scrutineeTerm]

/-- The reassembly payload transport satisfies the total cast-map
equation: both sides take the non-variable branch, and the two cast
chains over the payload type square agree definitionally. -/
theorem IotaRuleDesc.elimPayloadAtDepth?_rename (rule : IotaRuleDesc)
    {scope targetScope : Nat}
    (isNotVarHead : rule.elimGenerator ≠ .gen_var)
    (elimPayload : rule.elimGenerator.payload scope) (depth : Nat) :
    rule.elimPayloadAtDepth? depth
        (cast (Generator.payload_scope_invariant_of_not_var isNotVarHead
          scope targetScope) elimPayload)
      = (rule.elimPayloadAtDepth? depth elimPayload).map
          (cast (Generator.payload_scope_invariant_of_not_var isNotVarHead
            (scope + depth) (targetScope + depth))) := by
  dsimp only [IotaRuleDesc.elimPayloadAtDepth?]
  rw [dif_neg isNotVarHead, dif_neg isNotVarHead, optionSomeMap]
  exact congrArg some (castCompose
    (Generator.payload_scope_invariant_of_not_var isNotVarHead
      scope targetScope)
    (Generator.payload_scope_invariant_of_not_var isNotVarHead
      targetScope (targetScope + depth))
    (Generator.payload_scope_invariant_of_not_var isNotVarHead
      scope (scope + depth))
    (Generator.payload_scope_invariant_of_not_var isNotVarHead
      (scope + depth) (targetScope + depth))
    elimPayload)

/-- A `builtGen` payload source satisfies the total cast-map equation
on a renamed spine — GIVEN its scope-uniformity certificate.  A
constant family is scope-uniform by its clause; a scrutinee transform
reads the SAME head on both sides (renaming preserves heads — the
variable case fails the head test on both sides since the declared
source head is non-variable), and the transform commutes with the
payload transport by its clause. -/
theorem IotaRuleDesc.resolvePayloadSource?_rename (rule : IotaRuleDesc)
    {scope targetScope : Nat} (rho : RawRenaming scope targetScope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope)
    (depth : Nat) {builtHead : Generator}
    (payloadSource : PayloadSource builtHead)
    (isUniform : payloadSource.IsScopeUniform) :
    ∃ (isNotVarBuilt : builtHead ≠ .gen_var),
      rule.resolvePayloadSource? (RawTermChildren.rename rho spine) depth
          payloadSource
        = (rule.resolvePayloadSource? spine depth payloadSource).map
            (cast (Generator.payload_scope_invariant_of_not_var
              isNotVarBuilt (scope + depth) (targetScope + depth))) := by
  cases payloadSource with
  | constantFamily payloadFamily =>
      obtain ⟨isNotVarBuilt, familyUniform⟩ := isUniform
      refine ⟨isNotVarBuilt, ?_⟩
      dsimp only [IotaRuleDesc.resolvePayloadSource?]
      rw [optionSomeMap]
      exact congrArg some
        (familyUniform (scope + depth) (targetScope + depth)
          isNotVarBuilt).symm
  | transformedFromScrutinee scrutineeIndex sourceHead payloadTransform =>
      obtain ⟨isNotVarBuilt, isNotVarSource, transformUniform⟩ := isUniform
      refine ⟨isNotVarBuilt, ?_⟩
      dsimp only [IotaRuleDesc.resolvePayloadSource?]
      rw [rule.scrutineeTermAt?_rename rho spine scrutineeIndex]
      cases termLookup : rule.scrutineeTermAt? scrutineeIndex spine with
      | none => rfl
      | some scrutineeTerm =>
        cases scrutineeTerm with
        | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
          by_cases isVarGen : scrutineeGenerator = .gen_var
          · subst isVarGen
            have childrenAreNil : scrutineeChildren = .childNil :=
              RawTermChildren.eq_childNil scrutineeChildren
            subst childrenAreNil
            rw [optionSomeMap, RawTerm.rename_var_reduces rho
                scrutineePayload,
              optionSomeBindMonadic, optionSomeBindMonadic]
            dsimp only
            rw [dif_neg (fun isVarSource =>
                isNotVarSource isVarSource.symm),
              dif_neg (fun isVarSource => isNotVarSource isVarSource.symm)]
            rfl
          · rw [optionSomeMap,
              RawTerm.rename_nonVar_reduces rho isVarGen scrutineePayload
                scrutineeChildren,
              optionSomeBindMonadic, optionSomeBindMonadic]
            dsimp only
            by_cases isHead : scrutineeGenerator = sourceHead
            · subst isHead
              rw [dif_pos rfl, dif_pos rfl, optionSomeMap]
              exact congrArg some
                (transformUniform scope (scope + depth) targetScope
                  (targetScope + depth) isNotVarSource isNotVarBuilt
                  scrutineePayload).symm
            · rw [dif_neg isHead, dif_neg isHead]
              rfl

/-- The raw slot lookup on a renamed spine is the substituted-view map
of the original lookup — the un-composed sibling of
`scrutineeSlotLookup_rename` (no shift-0 projection), feeding the
template arms that project at shift 1 or 2. -/
theorem scopedChildAt?_rename {scope targetScope : Nat}
    (rho : RawRenaming scope targetScope)
    {binderShifts : List Nat}
    (spine : RawTermChildren binderShifts scope) (slot : Nat) :
    scopedChildAt? (RawTermChildren.rename rho spine).toScopedChildren slot
      = (scopedChildAt? spine.toScopedChildren slot).map
          (ScopedChild.substView (RawTermSubst.ofRenaming rho)) := by
  rw [RawTermChildren.rename_eq_subst_ofRenaming rho spine,
    RawTermChildren.toScopedChildren_subst
      (RawTermSubst.ofRenaming rho) spine]
  dsimp only [scopedChildAt?]
  rw [listEntryAt?_map]

/-! ## Interpreter NONE-preservation under renaming

The shipped forward walk (`interpretTemplate?_subst`) transports a
SUCCESSFUL interpretation; reflection additionally needs that a FAILING
interpretation stays failing on the renamed spine — together they give
the total map-equation.  Failure is a shape question (a missing slot, a
wrong binder shift, a wrong head, an out-of-range template binder), and
renaming preserves every shape the interpreter inspects.  Recursive
sub-template links that DID interpret are advanced with the forward
theorem at the variable-injection substitution. -/

mutual

/-- A failing template interpretation stays failing on the renamed
spine — the none leg of the interpreter's rename equation. -/
theorem IotaRuleDesc.interpretTemplate?_rename_none (rule : IotaRuleDesc)
    {scope targetScope : Nat} (rho : RawRenaming scope targetScope)
    (isNotVarHead : rule.elimGenerator ≠ .gen_var)
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    (depth : Nat) → (template : ReductTemplate) →
    template.HasScopeUniformPayloads →
    rule.interpretTemplate? elimPayload spine depth template = none →
    rule.interpretTemplate?
        (cast (Generator.payload_scope_invariant_of_not_var isNotVarHead
          scope targetScope) elimPayload)
        (RawTermChildren.rename rho spine) depth template
      = none
  | depth, .boundVarAt binderIndex, _, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      by_cases isBound : binderIndex < depth
      · rw [dif_pos isBound] at interpreted
        injection interpreted
      · rw [dif_neg isBound]
  | depth, .spineChildAt slot, _, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      rw [scopedChildAt?_rename rho spine slot]
      cases lookupShape : scopedChildAt? spine.toScopedChildren slot with
      | none => rfl
      | some spineChild =>
          rw [optionSomeMap, optionSomeBindMonadic,
            ScopedChild.atShiftZero?_substView]
          rw [lookupShape, optionSomeBindMonadic] at interpreted
          cases projShape : spineChild.atShiftZero? with
          | none => rfl
          | some childTerm =>
              rw [projShape, optionSomeBindMonadic] at interpreted
              injection interpreted
  | depth, .scrutineeChildAt scrutineeIndex slot, _, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      rw [rule.scrutineeChildrenAt?_rename rho spine scrutineeIndex]
      cases childrenShape :
          rule.scrutineeChildrenAt? scrutineeIndex spine with
      | none => rfl
      | some childrenView =>
          rw [optionSomeMap, optionSomeBindMonadic]
          rw [childrenShape, optionSomeBindMonadic] at interpreted
          dsimp only [scopedChildAt?] at interpreted ⊢
          rw [listEntryAt?_map]
          cases childShape : listEntryAt? childrenView slot with
          | none => rfl
          | some scrutineeChild =>
              rw [optionSomeMap, optionSomeBindMonadic,
                ScopedChild.atShiftZero?_substView]
              rw [childShape, optionSomeBindMonadic] at interpreted
              cases projShape : scrutineeChild.atShiftZero? with
              | none => rfl
              | some childTerm =>
                  rw [projShape, optionSomeBindMonadic] at interpreted
                  injection interpreted
  | depth, .theScrutineeAt scrutineeIndex, _, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      rw [rule.scrutineeTermAt?_rename rho spine scrutineeIndex]
      cases termShape : rule.scrutineeTermAt? scrutineeIndex spine with
      | none => rfl
      | some scrutineeTerm =>
          rw [termShape, optionSomeBindMonadic] at interpreted
          injection interpreted
  | depth, .motiveInstantiatedWith argTemplate, argUniform,
      interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      cases motiveShape : rule.motiveSlot? with
      | none => rfl
      | some motiveSlot =>
          rw [optionSomeBindMonadic]
          rw [motiveShape, optionSomeBindMonadic] at interpreted
          cases argShape : rule.interpretTemplate? elimPayload spine depth
              argTemplate with
          | none =>
              rw [rule.interpretTemplate?_rename_none rho isNotVarHead
                elimPayload spine depth argTemplate argUniform argShape]
              rfl
          | some argTerm =>
              have renamedArg := rule.interpretTemplate?_subst
                (RawTermSubst.ofRenaming rho) isNotVarHead elimPayload
                spine depth argTemplate argUniform argShape
              rw [← RawTermChildren.rename_eq_subst_ofRenaming rho spine]
                at renamedArg
              rw [renamedArg, optionSomeBindMonadic]
              rw [argShape, optionSomeBindMonadic] at interpreted
              rw [scopedChildAt?_rename rho spine motiveSlot]
              cases motiveChildShape :
                  scopedChildAt? spine.toScopedChildren motiveSlot with
              | none => rfl
              | some motiveChild =>
                  rw [optionSomeMap, optionSomeBindMonadic,
                    ScopedChild.atShiftOne?_substView]
                  rw [motiveChildShape, optionSomeBindMonadic]
                    at interpreted
                  cases projShape : motiveChild.atShiftOne? with
                  | none => rfl
                  | some motiveBody =>
                      rw [projShape, optionSomeBindMonadic] at interpreted
                      injection interpreted
  | depth, .motiveInstantiatedWithPair innerTemplate outerTemplate,
      isUniform, interpreted => by
      obtain ⟨innerUniform, outerUniform⟩ := isUniform
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      cases motiveShape : rule.motiveSlot? with
      | none => rfl
      | some motiveSlot =>
          rw [optionSomeBindMonadic]
          rw [motiveShape, optionSomeBindMonadic] at interpreted
          cases innerShape : rule.interpretTemplate? elimPayload spine depth
              innerTemplate with
          | none =>
              rw [rule.interpretTemplate?_rename_none rho isNotVarHead
                elimPayload spine depth innerTemplate innerUniform
                innerShape]
              rfl
          | some innerTerm =>
              have renamedInner := rule.interpretTemplate?_subst
                (RawTermSubst.ofRenaming rho) isNotVarHead elimPayload
                spine depth innerTemplate innerUniform innerShape
              rw [← RawTermChildren.rename_eq_subst_ofRenaming rho spine]
                at renamedInner
              rw [renamedInner, optionSomeBindMonadic]
              rw [innerShape, optionSomeBindMonadic] at interpreted
              cases outerShape : rule.interpretTemplate? elimPayload spine
                  depth outerTemplate with
              | none =>
                  rw [rule.interpretTemplate?_rename_none rho isNotVarHead
                    elimPayload spine depth outerTemplate outerUniform
                    outerShape]
                  rfl
              | some outerTerm =>
                  have renamedOuter := rule.interpretTemplate?_subst
                    (RawTermSubst.ofRenaming rho) isNotVarHead elimPayload
                    spine depth outerTemplate outerUniform outerShape
                  rw [← RawTermChildren.rename_eq_subst_ofRenaming rho
                    spine] at renamedOuter
                  rw [renamedOuter, optionSomeBindMonadic]
                  rw [outerShape, optionSomeBindMonadic] at interpreted
                  rw [scopedChildAt?_rename rho spine motiveSlot]
                  cases motiveChildShape :
                      scopedChildAt? spine.toScopedChildren motiveSlot with
                  | none => rfl
                  | some motiveChild =>
                      rw [optionSomeMap, optionSomeBindMonadic,
                        ScopedChild.atShiftTwo?_substView]
                      rw [motiveChildShape, optionSomeBindMonadic]
                        at interpreted
                      cases projShape : motiveChild.atShiftTwo? with
                      | none => rfl
                      | some motiveBody =>
                          rw [projShape, optionSomeBindMonadic]
                            at interpreted
                          injection interpreted
  | depth, .builtGen builtHead payloadSource childTemplates, isUniform,
      interpreted => by
      obtain ⟨sourceUniform, childrenUniform⟩ := isUniform
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨isNotVarBuilt, resolveEq⟩ :=
        rule.resolvePayloadSource?_rename rho spine depth payloadSource
          sourceUniform
      rw [resolveEq]
      cases resolveShape :
          rule.resolvePayloadSource? spine depth payloadSource with
      | none => rfl
      | some builtPayload =>
          rw [optionSomeMap, optionSomeBindMonadic]
          rw [resolveShape, optionSomeBindMonadic] at interpreted
          cases childrenShape : rule.interpretBuiltChildren? elimPayload
              spine depth builtHead.binderShifts childTemplates with
          | none =>
              rw [rule.interpretBuiltChildren?_rename_none rho isNotVarHead
                elimPayload spine depth builtHead.binderShifts
                childTemplates childrenUniform childrenShape]
              rfl
          | some builtChildren =>
              rw [childrenShape, optionSomeBindMonadic] at interpreted
              injection interpreted
  | depth, .reassembledReplacing replacements, replacementsUniform,
      interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      rw [rule.elimPayloadAtDepth?_rename isNotVarHead elimPayload depth]
      cases payloadShape : rule.elimPayloadAtDepth? depth elimPayload with
      | none => rfl
      | some payloadAtDepth =>
          rw [optionSomeMap, optionSomeBindMonadic]
          rw [payloadShape, optionSomeBindMonadic] at interpreted
          rw [RawTermChildren.rename_eq_subst_ofRenaming rho spine,
            ← RawTermChildren.weakenSpineBy_subst
              (RawTermSubst.ofRenaming rho) depth spine,
            ← RawTermChildren.rename_eq_subst_ofRenaming rho spine]
          cases replacedShape : rule.interpretReplacements? elimPayload
              spine depth replacements
              (RawTermChildren.weakenSpineBy depth spine) with
          | none =>
              rw [rule.interpretReplacements?_rename_none rho isNotVarHead
                elimPayload spine depth replacements replacementsUniform
                (RawTermChildren.weakenSpineBy depth spine) replacedShape]
              rfl
          | some replacedSpine =>
              rw [replacedShape, optionSomeBindMonadic] at interpreted
              injection interpreted
  | depth, .substOneIntoSpineChild bodySlot argTemplate, argUniform,
      interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      cases argShape : rule.interpretTemplate? elimPayload spine depth
          argTemplate with
      | none =>
          rw [rule.interpretTemplate?_rename_none rho isNotVarHead
            elimPayload spine depth argTemplate argUniform argShape]
          rfl
      | some argTerm =>
          have renamedArg := rule.interpretTemplate?_subst
            (RawTermSubst.ofRenaming rho) isNotVarHead elimPayload spine
            depth argTemplate argUniform argShape
          rw [← RawTermChildren.rename_eq_subst_ofRenaming rho spine]
            at renamedArg
          rw [renamedArg, optionSomeBindMonadic]
          rw [argShape, optionSomeBindMonadic] at interpreted
          rw [scopedChildAt?_rename rho spine bodySlot]
          cases bodyChildShape :
              scopedChildAt? spine.toScopedChildren bodySlot with
          | none => rfl
          | some bodyChild =>
              rw [optionSomeMap, optionSomeBindMonadic,
                ScopedChild.atShiftOne?_substView]
              rw [bodyChildShape, optionSomeBindMonadic] at interpreted
              cases projShape : bodyChild.atShiftOne? with
              | none => rfl
              | some bodyTerm =>
                  rw [projShape, optionSomeBindMonadic] at interpreted
                  injection interpreted
  | depth, .substOneIntoScrutineeChild scrutineeIndex bodySlot argTemplate,
      argUniform, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      cases argShape : rule.interpretTemplate? elimPayload spine depth
          argTemplate with
      | none =>
          rw [rule.interpretTemplate?_rename_none rho isNotVarHead
            elimPayload spine depth argTemplate argUniform argShape]
          rfl
      | some argTerm =>
          have renamedArg := rule.interpretTemplate?_subst
            (RawTermSubst.ofRenaming rho) isNotVarHead elimPayload spine
            depth argTemplate argUniform argShape
          rw [← RawTermChildren.rename_eq_subst_ofRenaming rho spine]
            at renamedArg
          rw [renamedArg, optionSomeBindMonadic]
          rw [argShape, optionSomeBindMonadic] at interpreted
          rw [rule.scrutineeChildrenAt?_rename rho spine scrutineeIndex]
          cases childrenShape :
              rule.scrutineeChildrenAt? scrutineeIndex spine with
          | none => rfl
          | some childrenView =>
              rw [optionSomeMap, optionSomeBindMonadic]
              rw [childrenShape, optionSomeBindMonadic] at interpreted
              dsimp only [scopedChildAt?] at interpreted ⊢
              rw [listEntryAt?_map]
              cases childShape : listEntryAt? childrenView bodySlot with
              | none => rfl
              | some bodyChild =>
                  rw [optionSomeMap, optionSomeBindMonadic,
                    ScopedChild.atShiftOne?_substView]
                  rw [childShape, optionSomeBindMonadic] at interpreted
                  cases projShape : bodyChild.atShiftOne? with
                  | none => rfl
                  | some bodyTerm =>
                      rw [projShape, optionSomeBindMonadic] at interpreted
                      injection interpreted
  | depth, .substPairIntoSpineChild bodySlot innerTemplate outerTemplate,
      isUniform, interpreted => by
      obtain ⟨innerUniform, outerUniform⟩ := isUniform
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      cases innerShape : rule.interpretTemplate? elimPayload spine depth
          innerTemplate with
      | none =>
          rw [rule.interpretTemplate?_rename_none rho isNotVarHead
            elimPayload spine depth innerTemplate innerUniform innerShape]
          rfl
      | some innerTerm =>
          have renamedInner := rule.interpretTemplate?_subst
            (RawTermSubst.ofRenaming rho) isNotVarHead elimPayload spine
            depth innerTemplate innerUniform innerShape
          rw [← RawTermChildren.rename_eq_subst_ofRenaming rho spine]
            at renamedInner
          rw [renamedInner, optionSomeBindMonadic]
          rw [innerShape, optionSomeBindMonadic] at interpreted
          cases outerShape : rule.interpretTemplate? elimPayload spine
              depth outerTemplate with
          | none =>
              rw [rule.interpretTemplate?_rename_none rho isNotVarHead
                elimPayload spine depth outerTemplate outerUniform
                outerShape]
              rfl
          | some outerTerm =>
              have renamedOuter := rule.interpretTemplate?_subst
                (RawTermSubst.ofRenaming rho) isNotVarHead elimPayload
                spine depth outerTemplate outerUniform outerShape
              rw [← RawTermChildren.rename_eq_subst_ofRenaming rho spine]
                at renamedOuter
              rw [renamedOuter, optionSomeBindMonadic]
              rw [outerShape, optionSomeBindMonadic] at interpreted
              rw [scopedChildAt?_rename rho spine bodySlot]
              cases bodyChildShape :
                  scopedChildAt? spine.toScopedChildren bodySlot with
              | none => rfl
              | some bodyChild =>
                  rw [optionSomeMap, optionSomeBindMonadic,
                    ScopedChild.atShiftTwo?_substView]
                  rw [bodyChildShape, optionSomeBindMonadic] at interpreted
                  cases projShape : bodyChild.atShiftTwo? with
                  | none => rfl
                  | some bodyTerm =>
                      rw [projShape, optionSomeBindMonadic] at interpreted
                      injection interpreted
  | depth, .substPairIntoScrutineeChild scrutineeIndex bodySlot
      innerTemplate outerTemplate, isUniform, interpreted => by
      obtain ⟨innerUniform, outerUniform⟩ := isUniform
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      cases innerShape : rule.interpretTemplate? elimPayload spine depth
          innerTemplate with
      | none =>
          rw [rule.interpretTemplate?_rename_none rho isNotVarHead
            elimPayload spine depth innerTemplate innerUniform innerShape]
          rfl
      | some innerTerm =>
          have renamedInner := rule.interpretTemplate?_subst
            (RawTermSubst.ofRenaming rho) isNotVarHead elimPayload spine
            depth innerTemplate innerUniform innerShape
          rw [← RawTermChildren.rename_eq_subst_ofRenaming rho spine]
            at renamedInner
          rw [renamedInner, optionSomeBindMonadic]
          rw [innerShape, optionSomeBindMonadic] at interpreted
          cases outerShape : rule.interpretTemplate? elimPayload spine
              depth outerTemplate with
          | none =>
              rw [rule.interpretTemplate?_rename_none rho isNotVarHead
                elimPayload spine depth outerTemplate outerUniform
                outerShape]
              rfl
          | some outerTerm =>
              have renamedOuter := rule.interpretTemplate?_subst
                (RawTermSubst.ofRenaming rho) isNotVarHead elimPayload
                spine depth outerTemplate outerUniform outerShape
              rw [← RawTermChildren.rename_eq_subst_ofRenaming rho spine]
                at renamedOuter
              rw [renamedOuter, optionSomeBindMonadic]
              rw [outerShape, optionSomeBindMonadic] at interpreted
              rw [rule.scrutineeChildrenAt?_rename rho spine scrutineeIndex]
              cases childrenShape :
                  rule.scrutineeChildrenAt? scrutineeIndex spine with
              | none => rfl
              | some childrenView =>
                  rw [optionSomeMap, optionSomeBindMonadic]
                  rw [childrenShape, optionSomeBindMonadic] at interpreted
                  dsimp only [scopedChildAt?] at interpreted ⊢
                  rw [listEntryAt?_map]
                  cases childShape : listEntryAt? childrenView bodySlot with
                  | none => rfl
                  | some bodyChild =>
                      rw [optionSomeMap, optionSomeBindMonadic,
                        ScopedChild.atShiftTwo?_substView]
                      rw [childShape, optionSomeBindMonadic] at interpreted
                      cases projShape : bodyChild.atShiftTwo? with
                      | none => rfl
                      | some bodyTerm =>
                          rw [projShape, optionSomeBindMonadic]
                            at interpreted
                          injection interpreted

/-- Spine companion: failing `builtGen` children assembly stays failing
on the renamed spine. -/
theorem IotaRuleDesc.interpretBuiltChildren?_rename_none
    (rule : IotaRuleDesc) {scope targetScope : Nat}
    (rho : RawRenaming scope targetScope)
    (isNotVarHead : rule.elimGenerator ≠ .gen_var)
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    (depth : Nat) → (childShifts : List Nat) →
    (childTemplates : ReductTemplateSpine) →
    childTemplates.HasScopeUniformPayloads →
    rule.interpretBuiltChildren? elimPayload spine depth childShifts
        childTemplates
      = none →
    rule.interpretBuiltChildren?
        (cast (Generator.payload_scope_invariant_of_not_var isNotVarHead
          scope targetScope) elimPayload)
        (RawTermChildren.rename rho spine) depth childShifts childTemplates
      = none
  | depth, [], .spineNil, _, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted
      injection interpreted
  | _, [], .spineCons _ _, _, _ => rfl
  | _, _ :: _, .spineNil, _, _ => rfl
  | depth, 0 :: restShifts, .spineCons childTemplate restTemplates,
      isUniform, interpreted => by
      obtain ⟨childUniform, restUniform⟩ := isUniform
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted ⊢
      cases childShape : rule.interpretTemplate? elimPayload spine depth
          childTemplate with
      | none =>
          rw [rule.interpretTemplate?_rename_none rho isNotVarHead
            elimPayload spine depth childTemplate childUniform childShape]
          rfl
      | some childTerm =>
          have renamedChild := rule.interpretTemplate?_subst
            (RawTermSubst.ofRenaming rho) isNotVarHead elimPayload spine
            depth childTemplate childUniform childShape
          rw [← RawTermChildren.rename_eq_subst_ofRenaming rho spine]
            at renamedChild
          rw [renamedChild, optionSomeBindMonadic]
          rw [childShape, optionSomeBindMonadic] at interpreted
          cases restShape : rule.interpretBuiltChildren? elimPayload spine
              depth restShifts restTemplates with
          | none =>
              rw [rule.interpretBuiltChildren?_rename_none rho isNotVarHead
                elimPayload spine depth restShifts restTemplates
                restUniform restShape]
              rfl
          | some restChildren =>
              rw [restShape, optionSomeBindMonadic] at interpreted
              injection interpreted
  | depth, 1 :: restShifts, .spineCons childTemplate restTemplates,
      isUniform, interpreted => by
      obtain ⟨childUniform, restUniform⟩ := isUniform
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted ⊢
      cases childShape : rule.interpretTemplate? elimPayload spine
          (depth + 1) childTemplate with
      | none =>
          rw [rule.interpretTemplate?_rename_none rho isNotVarHead
            elimPayload spine (depth + 1) childTemplate childUniform
            childShape]
          rfl
      | some childTerm =>
          have renamedChild := rule.interpretTemplate?_subst
            (RawTermSubst.ofRenaming rho) isNotVarHead elimPayload spine
            (depth + 1) childTemplate childUniform childShape
          rw [← RawTermChildren.rename_eq_subst_ofRenaming rho spine]
            at renamedChild
          rw [renamedChild, optionSomeBindMonadic]
          rw [childShape, optionSomeBindMonadic] at interpreted
          cases restShape : rule.interpretBuiltChildren? elimPayload spine
              depth restShifts restTemplates with
          | none =>
              rw [rule.interpretBuiltChildren?_rename_none rho isNotVarHead
                elimPayload spine depth restShifts restTemplates
                restUniform restShape]
              rfl
          | some restChildren =>
              rw [restShape, optionSomeBindMonadic] at interpreted
              injection interpreted
  | depth, 2 :: restShifts, .spineCons childTemplate restTemplates,
      isUniform, interpreted => by
      obtain ⟨childUniform, restUniform⟩ := isUniform
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted ⊢
      cases childShape : rule.interpretTemplate? elimPayload spine
          (depth + 2) childTemplate with
      | none =>
          rw [rule.interpretTemplate?_rename_none rho isNotVarHead
            elimPayload spine (depth + 2) childTemplate childUniform
            childShape]
          rfl
      | some childTerm =>
          have renamedChild := rule.interpretTemplate?_subst
            (RawTermSubst.ofRenaming rho) isNotVarHead elimPayload spine
            (depth + 2) childTemplate childUniform childShape
          rw [← RawTermChildren.rename_eq_subst_ofRenaming rho spine]
            at renamedChild
          rw [renamedChild, optionSomeBindMonadic]
          rw [childShape, optionSomeBindMonadic] at interpreted
          cases restShape : rule.interpretBuiltChildren? elimPayload spine
              depth restShifts restTemplates with
          | none =>
              rw [rule.interpretBuiltChildren?_rename_none rho isNotVarHead
                elimPayload spine depth restShifts restTemplates
                restUniform restShape]
              rfl
          | some restChildren =>
              rw [restShape, optionSomeBindMonadic] at interpreted
              injection interpreted
  | _, (_ + 3) :: _, .spineCons _ _, _, _ => rfl

/-- Replacements companion: a failing reassembly fold stays failing on
the renamed spine (with the reassembly argument transported along the
depth-lifted variable injection). -/
theorem IotaRuleDesc.interpretReplacements?_rename_none
    (rule : IotaRuleDesc) {scope targetScope : Nat}
    (rho : RawRenaming scope targetScope)
    (isNotVarHead : rule.elimGenerator ≠ .gen_var)
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    (depth : Nat) → (replacements : SpineReplacements) →
    replacements.HasScopeUniformPayloads →
    (reassemblySpine :
      RawTermChildren rule.elimGenerator.binderShifts (scope + depth)) →
    rule.interpretReplacements? elimPayload spine depth replacements
        reassemblySpine
      = none →
    rule.interpretReplacements?
        (cast (Generator.payload_scope_invariant_of_not_var isNotVarHead
          scope targetScope) elimPayload)
        (RawTermChildren.rename rho spine) depth replacements
        (RawTermChildren.subst
          (iterateLiftRaw (RawTermSubst.ofRenaming rho) depth)
          reassemblySpine)
      = none
  | depth, .replaceNil, _, reassemblySpine, interpreted => by
      dsimp only [IotaRuleDesc.interpretReplacements?] at interpreted
      injection interpreted
  | depth, .replaceCons slot replacementTemplate restReplacements,
      isUniform, reassemblySpine, interpreted => by
      obtain ⟨replacementUniform, restUniform⟩ := isUniform
      dsimp only [IotaRuleDesc.interpretReplacements?] at interpreted ⊢
      cases replacementShape : rule.interpretTemplate? elimPayload spine
          depth replacementTemplate with
      | none =>
          rw [rule.interpretTemplate?_rename_none rho isNotVarHead
            elimPayload spine depth replacementTemplate replacementUniform
            replacementShape]
          rfl
      | some replacement =>
          have renamedReplacement := rule.interpretTemplate?_subst
            (RawTermSubst.ofRenaming rho) isNotVarHead elimPayload spine
            depth replacementTemplate replacementUniform replacementShape
          rw [← RawTermChildren.rename_eq_subst_ofRenaming rho spine]
            at renamedReplacement
          rw [renamedReplacement, optionSomeBindMonadic]
          rw [replacementShape, optionSomeBindMonadic] at interpreted
          rw [← RawTermChildren.replaceChildAt?_subst
            (iterateLiftRaw (RawTermSubst.ofRenaming rho) depth)
            reassemblySpine slot replacement]
          cases replaceShape :
              reassemblySpine.replaceChildAt? slot replacement with
          | none => rfl
          | some replacedOnce =>
              rw [optionSomeMap, optionSomeBindMonadic]
              rw [replaceShape, optionSomeBindMonadic] at interpreted
              exact rule.interpretReplacements?_rename_none rho
                isNotVarHead elimPayload spine depth restReplacements
                restUniform replacedOnce interpreted

end

/-! ## The headline EQUATIONS: interpreter and firing dispatcher -/

/-- ★ **The interpreter's total rename equation**: template
interpretation on the renamed spine IS the depth-lifted
variable-injection substitution of the original interpretation — the
none and some legs in one two-sided statement (none by the
none-preservation walk, some by the shipped forward transport). -/
theorem IotaRuleDesc.interpretTemplate?_rename (rule : IotaRuleDesc)
    {scope targetScope : Nat} (rho : RawRenaming scope targetScope)
    (isNotVarHead : rule.elimGenerator ≠ .gen_var)
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope)
    (depth : Nat) (template : ReductTemplate)
    (isUniform : template.HasScopeUniformPayloads) :
    rule.interpretTemplate?
        (cast (Generator.payload_scope_invariant_of_not_var isNotVarHead
          scope targetScope) elimPayload)
        (RawTermChildren.rename rho spine) depth template
      = (rule.interpretTemplate? elimPayload spine depth template).map
          (RawTerm.subst
            (iterateLiftRaw (RawTermSubst.ofRenaming rho) depth)) := by
  cases originShape : rule.interpretTemplate? elimPayload spine depth
      template with
  | none =>
      rw [rule.interpretTemplate?_rename_none rho isNotVarHead elimPayload
        spine depth template isUniform originShape]
      rfl
  | some result =>
      have renamed := rule.interpretTemplate?_subst
        (RawTermSubst.ofRenaming rho) isNotVarHead elimPayload spine depth
        template isUniform originShape
      rw [← RawTermChildren.rename_eq_subst_ofRenaming rho spine] at renamed
      rw [renamed]
      rfl

/-- ★ **Row-level rename equation**: a row's reduct interpretation on
the renamed spine is the renamed reduct interpretation — at depth 0 the
lifted injection collapses to the renaming itself. -/
theorem IotaRuleDesc.interpretTarget?_rename (rule : IotaRuleDesc)
    {scope targetScope : Nat} (rho : RawRenaming scope targetScope)
    (isNotVarHead : rule.elimGenerator ≠ .gen_var)
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope)
    (isUniform : rule.target.HasScopeUniformPayloads) :
    rule.interpretTarget?
        (cast (Generator.payload_scope_invariant_of_not_var isNotVarHead
          scope targetScope) elimPayload)
        (RawTermChildren.rename rho spine)
      = (rule.interpretTarget? elimPayload spine).map
          (RawTerm.rename rho) := by
  dsimp only [IotaRuleDesc.interpretTarget?]
  cases originShape : rule.interpretTemplate? elimPayload spine 0
      rule.target with
  | none =>
      rw [rule.interpretTemplate?_rename_none rho isNotVarHead elimPayload
        spine 0 rule.target isUniform originShape]
      rfl
  | some result =>
      have renamed := rule.interpretTemplate?_subst
        (RawTermSubst.ofRenaming rho) isNotVarHead elimPayload spine 0
        rule.target isUniform originShape
      rw [← RawTermChildren.rename_eq_subst_ofRenaming rho spine] at renamed
      rw [renamed, optionSomeMap]
      exact congrArg some
        (RawTerm.rename_eq_subst_ofRenaming rho result).symm

/-- ★ **Firing-dispatcher rename equation**: a row fires on the renamed
spine exactly as it fires on the original, producing the renamed reduct
— the two-sided form whose none leg is the reflection the bespoke
`Step.reflectRename` eliminator dispatch encodes per rule. -/
theorem IotaRuleDesc.firesOn?_rename (rule : IotaRuleDesc)
    {scope targetScope : Nat} (rho : RawRenaming scope targetScope)
    (isUniform : rule.IsScopeUniform)
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    rule.firesOn?
        (cast (Generator.payload_scope_invariant_of_not_var
          isUniform.isNotVarHead scope targetScope) elimPayload)
        (RawTermChildren.rename rho spine)
      = (rule.firesOn? elimPayload spine).map (RawTerm.rename rho) := by
  dsimp only [IotaRuleDesc.firesOn?]
  cases originFires : rule.scrutineesFire spine rule.scrutinees with
  | false =>
      have renamedNotFire :
          rule.scrutineesFire (RawTermChildren.rename rho spine)
            rule.scrutinees = false := by
        cases renamedShape : rule.scrutineesFire
            (RawTermChildren.rename rho spine) rule.scrutinees with
        | false => rfl
        | true =>
            have originFire := rule.scrutineesFire_reflectRename rho spine
              rule.scrutinees isUniform.scrutineesAreUniform renamedShape
            rw [originFires] at originFire
            exact Bool.noConfusion originFire
      rw [renamedNotFire]
      rfl
  | true =>
      have renamedFires := rule.scrutineesFire_subst
        (RawTermSubst.ofRenaming rho) spine rule.scrutinees
        isUniform.scrutineesAreUniform originFires
      rw [← RawTermChildren.rename_eq_subst_ofRenaming rho spine]
        at renamedFires
      rw [if_pos renamedFires, if_pos (rfl : (true : Bool) = true)]
      exact rule.interpretTarget?_rename rho isUniform.isNotVarHead
        elimPayload spine isUniform.targetIsUniform

end FX1Poly.Core

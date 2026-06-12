import FX1Poly.Core.IotaRuleTable
import FX1Poly.Core.RawTermSubst0Commute
import FX1Poly.Core.RawTermSubstLiftWeaken
import FX1Poly.Core.StructuralInductionPrimitives

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
  | _, .childCons _ childTail =>
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

/-! ## Spine weakening naturality (the reassembly arm's brick) -/

/-- The children-spine lift-weaken naturality — the spine twin of
`RawTerm.subst_lift_weaken`, by the same
`rename_subst_commute`/`subst_rename_commute`/pointwise recipe. -/
theorem RawTermChildren.subst_lift_weaken
    {parentSourceScope parentTargetScope : Nat}
    (sigma : RawTermSubst parentSourceScope parentTargetScope)
    {binderShifts : List Nat}
    (children : RawTermChildren binderShifts parentSourceScope) :
    RawTermChildren.subst (RawTermSubst.lift sigma)
        (RawTermChildren.weaken children)
      = RawTermChildren.weaken (RawTermChildren.subst sigma children) := by
  rw [RawTermChildren.weaken_eq_rename children,
    RawTermChildren.weaken_eq_rename (RawTermChildren.subst sigma children)]
  rw [RawTermChildren.rename_subst_commute RawRenaming.weaken
    (RawTermSubst.lift sigma) children]
  rw [RawTermChildren.subst_rename_commute sigma RawRenaming.weaken children]
  apply RawTermChildren.subst_pointwise
  intro position
  cases position with
  | mk positionValue positionBound => rfl

/-- Weakening a spine under `depth` template binders is natural in the
substitution. -/
theorem RawTermChildren.weakenSpineBy_subst
    {parentSourceScope parentTargetScope : Nat}
    (sigma : RawTermSubst parentSourceScope parentTargetScope)
    {binderShifts : List Nat} :
    (depth : Nat) →
    (children : RawTermChildren binderShifts parentSourceScope) →
    RawTermChildren.subst (iterateLiftRaw sigma depth)
        (RawTermChildren.weakenSpineBy depth children)
      = RawTermChildren.weakenSpineBy depth
        (RawTermChildren.subst sigma children)
  | 0, _ => rfl
  | innerDepth + 1, children => by
      dsimp only [RawTermChildren.weakenSpineBy]
      rw [iterateLiftRawSubst_succ]
      rw [RawTermChildren.subst_lift_weaken]
      rw [RawTermChildren.weakenSpineBy_subst sigma innerDepth children]

/-! ## The template-binder fixpoint (the `boundVarAt` arm's brick) -/

/-- A lifted substitution FIXES template-binder indices: positions below
the lift depth map to themselves. -/
theorem iterateLiftRawSubst_fixesTemplateBinder {scope targetScope : Nat}
    (sigma : RawTermSubst scope targetScope) :
    (depth : Nat) → (binderIndex : Nat) →
    (isTemplateBound : binderIndex < depth) →
    (sourceBound : binderIndex < scope + depth) →
    (targetBound : binderIndex < targetScope + depth) →
    iterateLiftRaw sigma depth ⟨binderIndex, sourceBound⟩ =
      .mkGen .gen_var ⟨binderIndex, targetBound⟩ .childNil
  | 0, _, isTemplateBound, _, _ =>
      absurd isTemplateBound (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, _ => rfl
  | innerDepth + 1, binderIndex + 1, isTemplateBound, sourceBound,
      targetBound => by
      show RawTerm.weaken
          (iterateLiftRaw sigma innerDepth ⟨binderIndex, _⟩) = _
      rw [iterateLiftRawSubst_fixesTemplateBinder sigma innerDepth binderIndex
        (Nat.lt_of_succ_lt_succ isTemplateBound)
        (Nat.lt_of_succ_lt_succ sourceBound)
        (Nat.lt_of_succ_lt_succ targetBound)]
      rfl

/-! ## Option-bind extraction (the do-chain splitter) -/

/-- Split a successful `Option.bind`: the first stage succeeded and its
value continues to the result. -/
theorem optionBindEqSome {valueType resultType : Type}
    {optionValue : Option valueType}
    {continuation : valueType → Option resultType} {result : resultType}
    (bound : optionValue.bind continuation = some result) :
    ∃ value, optionValue = some value ∧ continuation value = some result :=
  match optionValue, bound with
  | some value, bound => ⟨value, rfl, bound⟩
  | none, bound => by injection bound

/-! ## Payload scope-uniformity certificates

A `builtGen` payload SOURCE must be scope-uniform for the interpreter to
commute with substitution: a constant family whose value genuinely
varied with the scope would interpret differently on the two sides.
Every shipped row satisfies the certificate definitionally; it is the
first ingredient of the IOTA-T5 `WfIotaTable` discipline. -/

/-- Scope uniformity of a payload source: the built head is not the
variable generator (so built cells substitute structurally), and the
supplied payload data commutes with the scope-invariance transport. -/
def PayloadSource.IsScopeUniform {builtHead : Generator} :
    PayloadSource builtHead → Prop
  | .constantFamily payloadFamily =>
      builtHead ≠ .gen_var ∧
        ∀ (sourceScope targetScope : Nat) (isNotVar : builtHead ≠ .gen_var),
          cast (Generator.payload_scope_invariant_of_not_var isNotVar
              sourceScope targetScope)
            (payloadFamily sourceScope) = payloadFamily targetScope
  | .transformedFromScrutinee _ sourceHead payloadTransform =>
      builtHead ≠ .gen_var ∧ sourceHead ≠ .gen_var ∧
        ∀ (sourceScopeA targetScopeA sourceScopeB targetScopeB : Nat)
          (isNotVarSource : sourceHead ≠ .gen_var)
          (isNotVarBuilt : builtHead ≠ .gen_var)
          (matchedPayload : sourceHead.payload sourceScopeA),
          cast (Generator.payload_scope_invariant_of_not_var isNotVarBuilt
              targetScopeA targetScopeB)
            (payloadTransform sourceScopeA targetScopeA matchedPayload) =
            payloadTransform sourceScopeB targetScopeB
              (cast (Generator.payload_scope_invariant_of_not_var
                  isNotVarSource sourceScopeA sourceScopeB)
                matchedPayload)

mutual

/-- Every `builtGen` payload source anywhere in the template is
scope-uniform. -/
def ReductTemplate.HasScopeUniformPayloads : ReductTemplate → Prop
  | .boundVarAt _ => True
  | .spineChildAt _ => True
  | .scrutineeChildAt _ _ => True
  | .theScrutineeAt _ => True
  | .motiveInstantiatedWith argTemplate =>
      argTemplate.HasScopeUniformPayloads
  | .motiveInstantiatedWithPair innerTemplate outerTemplate =>
      innerTemplate.HasScopeUniformPayloads ∧
        outerTemplate.HasScopeUniformPayloads
  | .builtGen _ payloadSource childTemplates =>
      payloadSource.IsScopeUniform ∧
        childTemplates.HasScopeUniformPayloads
  | .reassembledReplacing replacements =>
      replacements.HasScopeUniformPayloads
  | .substOneIntoSpineChild _ argTemplate =>
      argTemplate.HasScopeUniformPayloads
  | .substOneIntoScrutineeChild _ _ argTemplate =>
      argTemplate.HasScopeUniformPayloads
  | .substPairIntoSpineChild _ innerTemplate outerTemplate =>
      innerTemplate.HasScopeUniformPayloads ∧
        outerTemplate.HasScopeUniformPayloads
  | .substPairIntoScrutineeChild _ _ innerTemplate outerTemplate =>
      innerTemplate.HasScopeUniformPayloads ∧
        outerTemplate.HasScopeUniformPayloads

/-- Spine-wise conjunction of payload scope-uniformity. -/
def ReductTemplateSpine.HasScopeUniformPayloads :
    ReductTemplateSpine → Prop
  | .spineNil => True
  | .spineCons childTemplate restTemplates =>
      childTemplate.HasScopeUniformPayloads ∧
        restTemplates.HasScopeUniformPayloads

/-- Replacement-wise conjunction of payload scope-uniformity. -/
def SpineReplacements.HasScopeUniformPayloads :
    SpineReplacements → Prop
  | .replaceNil => True
  | .replaceCons _ replacementTemplate restReplacements =>
      replacementTemplate.HasScopeUniformPayloads ∧
        restReplacements.HasScopeUniformPayloads

end

/-- Scope uniformity of ONE scrutinee spec: the declared head is not
the variable generator (a matched scrutinee then substitutes
structurally, KEEPING its head), and the optional payload guard
commutes with the scope-invariance transport — so the firing
dispatcher answers the same question on the substituted spine.  A
guard reading scope-VARYING content would fire differently on the two
sides; this clause is the honest boundary for guarded rows. -/
def ScrutineeSpec.IsScopeUniform (spec : ScrutineeSpec) : Prop :=
  spec.head ≠ .gen_var ∧
    match spec.payloadGuard? with
    | none => True
    | some payloadGuard =>
        ∀ (sourceScope targetScope : Nat)
          (isNotVarHead : spec.head ≠ .gen_var)
          (matchedPayload : spec.head.payload sourceScope),
          payloadGuard targetScope
            (cast (Generator.payload_scope_invariant_of_not_var
              isNotVarHead sourceScope targetScope) matchedPayload)
          = payloadGuard sourceScope matchedPayload

/-- Spec-list conjunction of scrutinee scope-uniformity. -/
def ScrutineeSpecsAreScopeUniform : List ScrutineeSpec → Prop
  | [] => True
  | spec :: restSpecs =>
      spec.IsScopeUniform ∧ ScrutineeSpecsAreScopeUniform restSpecs

/-- A singleton guard-free spec with a concrete constructor head is
scope-uniform — the shape every kernel row uses. -/
theorem singletonUnguardedSpec_isScopeUniform {slot : Nat}
    {head : Generator} (isNotVarHead : head ≠ .gen_var) :
    ScrutineeSpecsAreScopeUniform [{ slot := slot, head := head }] :=
  ⟨⟨isNotVarHead, ⟨⟩⟩, ⟨⟩⟩

/-- The row-level equivariance certificate: the eliminator head is not
the variable generator (variable-headed "rules" cannot substitute
structurally), the reduct's payload sources are scope-uniform, and
every scrutinee spec is scope-uniform (non-var head, guard commutes
with the payload transport).  The generic interpreter-substitution
commutation AND the firing-dispatcher naturality are CONDITIONAL on
this certificate — the honest boundary the table discipline
surfaces. -/
structure IotaRuleDesc.IsScopeUniform (rule : IotaRuleDesc) : Prop where
  isNotVarHead : rule.elimGenerator ≠ .gen_var
  targetIsUniform : rule.target.HasScopeUniformPayloads
  scrutineesAreUniform : ScrutineeSpecsAreScopeUniform rule.scrutinees

/-- The constant-unit application payload source (the app-chain rows'
shared source) is scope-uniform. -/
theorem PayloadSource.unitConstantApp_isScopeUniform :
    (PayloadSource.constantFamily (builtHead := .gen_app)
      fun _ => ()).IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra, fun _ _ _ => rfl⟩

/-! ## The 18 row certificates -/

theorem betaIotaRow_isScopeUniform : betaIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra, ⟨⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem boolTrueIotaRow_isScopeUniform : boolTrueIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra, ⟨⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem boolFalseIotaRow_isScopeUniform : boolFalseIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra, ⟨⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem fstPairIotaRow_isScopeUniform : fstPairIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra, ⟨⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem sndPairIotaRow_isScopeUniform : sndPairIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra, ⟨⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem natElimZeroIotaRow_isScopeUniform :
    natElimZeroIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra, ⟨⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem natRecZeroIotaRow_isScopeUniform :
    natRecZeroIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra, ⟨⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem natElimSuccIotaRow_isScopeUniform :
    natElimSuccIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra, ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟩⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem natRecSuccIotaRow_isScopeUniform :
    natRecSuccIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra, ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟩⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem listElimNilIotaRow_isScopeUniform :
    listElimNilIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra, ⟨⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem listElimConsIotaRow_isScopeUniform :
    listElimConsIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra,
    ⟨PayloadSource.unitConstantApp_isScopeUniform,
      ⟨PayloadSource.unitConstantApp_isScopeUniform,
        ⟨PayloadSource.unitConstantApp_isScopeUniform, ⟨⟩, ⟨⟩, ⟨⟩⟩,
        ⟨⟩, ⟨⟩⟩,
      ⟨⟨⟩, ⟨⟩⟩, ⟨⟩⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem optionMatchNoneIotaRow_isScopeUniform :
    optionMatchNoneIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra, ⟨⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem optionMatchSomeIotaRow_isScopeUniform :
    optionMatchSomeIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra,
    ⟨PayloadSource.unitConstantApp_isScopeUniform, ⟨⟩, ⟨⟩, ⟨⟩⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem eitherMatchInlIotaRow_isScopeUniform :
    eitherMatchInlIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra,
    ⟨PayloadSource.unitConstantApp_isScopeUniform, ⟨⟩, ⟨⟩, ⟨⟩⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem eitherMatchInrIotaRow_isScopeUniform :
    eitherMatchInrIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra,
    ⟨PayloadSource.unitConstantApp_isScopeUniform, ⟨⟩, ⟨⟩, ⟨⟩⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem idJReflIotaRow_isScopeUniform : idJReflIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra, ⟨⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem idStrictRecReflIotaRow_isScopeUniform :
    idStrictRecReflIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra, ⟨⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem pathBetaIotaRow_isScopeUniform : pathBetaIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra, ⟨⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem quotRecMkIotaRow_isScopeUniform :
    quotRecMkIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra,
    ⟨PayloadSource.unitConstantApp_isScopeUniform, ⟨⟩, ⟨⟩, ⟨⟩⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem quotElimMkIotaRow_isScopeUniform :
    quotElimMkIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra,
    ⟨PayloadSource.unitConstantApp_isScopeUniform, ⟨⟩, ⟨⟩, ⟨⟩⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩
theorem truncRecIntroIotaRow_isScopeUniform :
    truncRecIntroIotaRow.IsScopeUniform :=
  ⟨fun contra => Generator.noConfusion contra,
    ⟨PayloadSource.unitConstantApp_isScopeUniform, ⟨⟩, ⟨⟩, ⟨⟩⟩,
    singletonUnguardedSpec_isScopeUniform
      (fun contra => Generator.noConfusion contra)⟩

end FX1Poly.Core

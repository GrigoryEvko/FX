import FX1Poly.Core.TableParallelSubstitution
import FX1Poly.Core.IotaTableOrthogonality
import FX1Poly.Core.IotaTableEquivariance

/-! # FX1Poly/Core/TableParallelStabilitySubstrate — IOTA-T6: orthogonality bricks for parallel stability

The substrate the generic parallel-stability induction consumes: when an
eliminator spine reduces POINTWISE in parallel, every datum the template
interpreter reads from it survives, related or identical:

  * slot lookups stay at the same binder shift and relate by the
    parallel relation (`lookupAtShiftZero/One/TwoRelated`);
  * a parallel step out of a cell whose head is no table row's
    eliminator is a CONGRUENCE (`invertAtRigidHead`) — the orthogonality
    payoff: scrutinee heads are constructors, constructors are not
    eliminators (`WfIotaTable.scrutineeHeadsAreRigid`), so a firing
    pattern can never be DESTROYED by parallel reduction of the spine;
  * therefore the firing test is preserved
    (`scrutineeSpecFires_parPreserved` / `scrutineesFire_parPreserved`),
    derived scrutinees relate with their structure exposed
    (`scrutineeCellExtraction_parRelated`), payload reads are IDENTICAL
    (`resolvePayloadSource?_parPreserved` — congruence preserves the
    matched payload on the nose), and slot replacement relates
    (`replaceChildAt?_parRelated`).

## Zero-axiom verification

Structural walks over the pointwise relation with `Nat`-matches on
binder shifts, the freed-subject inversion recipe (head extraction via
a `congrArg` match-lambda BEFORE injection, so the dependent payload
equality is homogeneous), and the T5 head-pinning bricks.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Gated per declaration in
`FX1PolyAudit/AuditTableParallelStability.lean`. -/

namespace FX1Poly.Core

/-! ## List membership bricks -/

/-- A successful positional lookup is a membership witness. -/
theorem listEntryAt?_mem {entryType : Type} :
    (entries : List entryType) → (position : Nat) →
    {entry : entryType} → listEntryAt? entries position = some entry →
    entry ∈ entries
  | [], _, _, lookupEq => nomatch lookupEq
  | headEntry :: _, 0, _, lookupEq => by
      obtain rfl := Option.some.inj lookupEq
      exact .head _
  | _ :: restEntries, position + 1, _, lookupEq =>
      .tail _ (listEntryAt?_mem restEntries position lookupEq)

/-- A row's eliminator is an elim root of its table. -/
theorem tableElimRoots_memOfRow :
    {table : List IotaRuleDesc} → {rule : IotaRuleDesc} → rule ∈ table →
    rule.elimGenerator ∈ tableElimRoots table
  | _, _, .head _ => .head _
  | _, _, .tail _ isInRest => .tail _ (tableElimRoots_memOfRow isInRest)

/-- A passing list pattern test passes for each member spec. -/
theorem IotaRuleDesc.scrutineesFire_memberFires (rule : IotaRuleDesc)
    {scope : Nat}
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope} :
    (specs : List ScrutineeSpec) →
    rule.scrutineesFire spine specs = true →
    {spec : ScrutineeSpec} → spec ∈ specs →
    rule.scrutineeSpecFires spine spec = true
  | [], _, _, isMember => by cases isMember
  | _ :: restSpecs, allFire, spec, isMember => by
      dsimp only [IotaRuleDesc.scrutineesFire] at allFire
      obtain ⟨headFires, restFire⟩ := andEqTrueSplit allFire
      cases isMember with
      | head => exact headFires
      | tail _ isInRest =>
          exact rule.scrutineesFire_memberFires restSpecs restFire isInRest

/-- **Scrutinee heads are rigid**: in a well-formed table, no declared
scrutinee head of any row is any row's eliminator — extracted from the
`allElimRootsAvoidScrutineeHeads` checker. -/
theorem WfIotaTable.scrutineeHeadsAreRigid {table : List IotaRuleDesc}
    (tableIsWf : WfIotaTable table) {rule : IotaRuleDesc}
    (isRow : rule ∈ table) :
    ∀ spec, spec ∈ rule.scrutinees →
    ∀ other, other ∈ table → spec.head ≠ other.elimGenerator := by
  intro spec specIsMember other otherIsRow
  have rowChecks :=
    listForall_mem table tableIsWf.elimRootsAvoidHeads isRow
  dsimp only [elimRootsAvoidScrutineeHeads] at rowChecks
  have specChecks := listForall_mem rule.scrutinees rowChecks specIsMember
  have verdict := listForall_mem (tableElimRoots table) specChecks
    (tableElimRoots_memOfRow otherIsRow)
  by_cases isRoot : spec.head = other.elimGenerator
  · rw [if_pos isRoot] at verdict
    exact Bool.noConfusion verdict
  · exact isRoot

/-! ## Pointwise lookup relatedness -/

/-- A shift-0 slot read survives pointwise parallel reduction: the
reduced spine's slot holds a parallel reduct of the original read. -/
theorem ParStepOverTableChildren.lookupAtShiftZeroRelated
    {table : List IotaRuleDesc} :
    {binderShifts : List Nat} → {scope : Nat} →
    {children children' : RawTermChildren binderShifts scope} →
    ParStepOverTableChildren table children children' →
    (slot : Nat) → {sourceTerm : RawTerm scope} →
    (scopedChildAt? children.toScopedChildren slot).bind
        ScopedChild.atShiftZero?
      = some sourceTerm →
    ∃ targetTerm : RawTerm scope,
      (scopedChildAt? children'.toScopedChildren slot).bind
          ScopedChild.atShiftZero?
        = some targetTerm
      ∧ ParStepOverTable table sourceTerm targetTerm
  | _, _, _, _, .nil, _, _, lookupEq => nomatch lookupEq
  | _, _, _, _,
      @ParStepOverTableChildren.cons _ _ headShift _ _ _ _ _
        headPar _tailPar, 0, _, lookupEq => by
      cases headShift with
      | zero =>
          obtain rfl := Option.some.inj lookupEq
          exact ⟨_, rfl, headPar⟩
      | succ _ => exact nomatch lookupEq
  | _, _, _, _, .cons _headPar tailPar, slot + 1, _, lookupEq =>
      ParStepOverTableChildren.lookupAtShiftZeroRelated tailPar slot lookupEq

/-- A shift-1 slot read survives pointwise parallel reduction (the
one-binder bodies: motives, λ bodies). -/
theorem ParStepOverTableChildren.lookupAtShiftOneRelated
    {table : List IotaRuleDesc} :
    {binderShifts : List Nat} → {scope : Nat} →
    {children children' : RawTermChildren binderShifts scope} →
    ParStepOverTableChildren table children children' →
    (slot : Nat) → {sourceBody : RawTerm (scope + 1)} →
    (scopedChildAt? children.toScopedChildren slot).bind
        ScopedChild.atShiftOne?
      = some sourceBody →
    ∃ targetBody : RawTerm (scope + 1),
      (scopedChildAt? children'.toScopedChildren slot).bind
          ScopedChild.atShiftOne?
        = some targetBody
      ∧ ParStepOverTable table sourceBody targetBody
  | _, _, _, _, .nil, _, _, lookupEq => nomatch lookupEq
  | _, _, _, _,
      @ParStepOverTableChildren.cons _ _ headShift _ _ _ _ _
        headPar _tailPar, 0, _, lookupEq => by
      cases headShift with
      | zero => exact nomatch lookupEq
      | succ priorShift =>
          cases priorShift with
          | zero =>
              obtain rfl := Option.some.inj lookupEq
              exact ⟨_, rfl, headPar⟩
          | succ _ => exact nomatch lookupEq
  | _, _, _, _, .cons _headPar tailPar, slot + 1, _, lookupEq =>
      ParStepOverTableChildren.lookupAtShiftOneRelated tailPar slot lookupEq

/-- A shift-2 slot read survives pointwise parallel reduction (the
two-binder bodies: `idJ` motives, Nat-recursor step cases). -/
theorem ParStepOverTableChildren.lookupAtShiftTwoRelated
    {table : List IotaRuleDesc} :
    {binderShifts : List Nat} → {scope : Nat} →
    {children children' : RawTermChildren binderShifts scope} →
    ParStepOverTableChildren table children children' →
    (slot : Nat) → {sourceBody : RawTerm (scope + 2)} →
    (scopedChildAt? children.toScopedChildren slot).bind
        ScopedChild.atShiftTwo?
      = some sourceBody →
    ∃ targetBody : RawTerm (scope + 2),
      (scopedChildAt? children'.toScopedChildren slot).bind
          ScopedChild.atShiftTwo?
        = some targetBody
      ∧ ParStepOverTable table sourceBody targetBody
  | _, _, _, _, .nil, _, _, lookupEq => nomatch lookupEq
  | _, _, _, _,
      @ParStepOverTableChildren.cons _ _ headShift _ _ _ _ _
        headPar _tailPar, 0, _, lookupEq => by
      cases headShift with
      | zero => exact nomatch lookupEq
      | succ priorShift =>
          cases priorShift with
          | zero => exact nomatch lookupEq
          | succ priorPriorShift =>
              cases priorPriorShift with
              | zero =>
                  obtain rfl := Option.some.inj lookupEq
                  exact ⟨_, rfl, headPar⟩
              | succ _ => exact nomatch lookupEq
  | _, _, _, _, .cons _headPar tailPar, slot + 1, _, lookupEq =>
      ParStepOverTableChildren.lookupAtShiftTwoRelated tailPar slot lookupEq

/-! ## Congruence inversion at rigid heads -/

/-- **A parallel step out of a rigid-headed cell is a congruence.**
When the cell's head is no table row's eliminator, the redex arm cannot
apply, so the step preserves the head and the payload and reduces the
children pointwise.  Freed-subject form: the source shape is a separate
equation, so the derivation cases stay index-clean. -/
theorem ParStepOverTable.invertAtRigidHead {table : List IotaRuleDesc}
    {scope : Nat} {source target : RawTerm scope}
    (parStep : ParStepOverTable table source target)
    {gen : Generator} {payload : gen.payload scope}
    {children : RawTermChildren gen.binderShifts scope}
    (sourceShape : source = .mkGen gen payload children)
    (isRigidHead : ∀ rule, rule ∈ table → gen ≠ rule.elimGenerator) :
    ∃ children', target = .mkGen gen payload children'
      ∧ ParStepOverTableChildren table children children' := by
  cases parStep with
  | tableRedex isRow elimPayload spinePar sourceFires fires =>
      exfalso
      have headsAgree := congrArg
        (fun cell => match cell with
          | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
        sourceShape
      exact isRigidHead _ isRow headsAgree.symm
  | cong congGen congPayload childrenPar =>
      have headsAgree : congGen = gen := congrArg
        (fun cell => match cell with
          | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
        sourceShape
      subst headsAgree
      injection sourceShape with _scopeRefl _genRefl payloadEq childrenEq
      subst payloadEq
      subst childrenEq
      exact ⟨_, rfl, childrenPar⟩

/-! ## Derived-scrutinee relatedness -/

/-- The derived scrutinee read survives pointwise parallel reduction
(no head structure needed — the `theScrutineeAt` consumer). -/
theorem IotaRuleDesc.scrutineeTermAt?_parRelated (rule : IotaRuleDesc)
    {table : List IotaRuleDesc} {scope : Nat}
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spinePar : ParStepOverTableChildren table spine spine')
    (scrutineeIndex : Nat) {scrutineeTerm : RawTerm scope}
    (termEq : rule.scrutineeTermAt? scrutineeIndex spine
      = some scrutineeTerm) :
    ∃ scrutineeTerm',
      rule.scrutineeTermAt? scrutineeIndex spine' = some scrutineeTerm'
      ∧ ParStepOverTable table scrutineeTerm scrutineeTerm' := by
  dsimp only [IotaRuleDesc.scrutineeTermAt?] at termEq ⊢
  obtain ⟨spec, specEq, lookupEq⟩ := optionBindEqSome termEq
  obtain ⟨targetTerm, lookupRelatedEq, relatedPar⟩ :=
    spinePar.lookupAtShiftZeroRelated spec.slot lookupEq
  rw [specEq, optionSomeBindExplicit]
  exact ⟨targetTerm, lookupRelatedEq, relatedPar⟩

/-- **The structured scrutinee extraction**: under the firing hypothesis
and head rigidity, the derived scrutinee is a CELL of the declared
head, the reduced spine's scrutinee is a cell of the SAME head with the
SAME payload, and the two cells' children relate pointwise — the brick
every scrutinee-projecting template arm and the payload reader fire
with. -/
theorem IotaRuleDesc.scrutineeCellExtraction_parRelated
    (rule : IotaRuleDesc) {table : List IotaRuleDesc} {scope : Nat}
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spinePar : ParStepOverTableChildren table spine spine')
    (allFire : rule.scrutineesFire spine rule.scrutinees = true)
    (scrutineeHeadsAreRigid : ∀ spec, spec ∈ rule.scrutinees →
      ∀ other, other ∈ table → spec.head ≠ other.elimGenerator)
    (scrutineeIndex : Nat) {scrutineeTerm : RawTerm scope}
    (termEq : rule.scrutineeTermAt? scrutineeIndex spine
      = some scrutineeTerm) :
    ∃ (spec : ScrutineeSpec) (matchedPayload : spec.head.payload scope)
      (matchedChildren matchedChildren' :
        RawTermChildren spec.head.binderShifts scope),
      rule.scrutineeSpecAt? scrutineeIndex = some spec
      ∧ scrutineeTerm = .mkGen spec.head matchedPayload matchedChildren
      ∧ rule.scrutineeTermAt? scrutineeIndex spine'
          = some (.mkGen spec.head matchedPayload matchedChildren')
      ∧ ParStepOverTableChildren table matchedChildren matchedChildren' := by
  have termEqStructure := termEq
  dsimp only [IotaRuleDesc.scrutineeTermAt?] at termEqStructure
  obtain ⟨spec, specEq, lookupEq⟩ := optionBindEqSome termEqStructure
  have specIsMember : spec ∈ rule.scrutinees :=
    listEntryAt?_mem rule.scrutinees scrutineeIndex specEq
  have specFires : rule.scrutineeSpecFires spine spec = true :=
    rule.scrutineesFire_memberFires rule.scrutinees allFire specIsMember
  obtain ⟨matchedPayload, matchedChildren, slotHoldsHead⟩ :=
    rule.scrutineeSpecFires_slotHoldsHead specFires
  have scrutineeIsCell :
      scrutineeTerm
        = .mkGen spec.head matchedPayload matchedChildren :=
    Option.some.inj (lookupEq.symm.trans slotHoldsHead)
  obtain ⟨targetTerm, lookupRelatedEq, relatedPar⟩ :=
    spinePar.lookupAtShiftZeroRelated spec.slot slotHoldsHead
  obtain ⟨matchedChildren', targetIsCell, matchedChildrenPar⟩ :=
    relatedPar.invertAtRigidHead rfl
      (fun other otherIsRow =>
        scrutineeHeadsAreRigid spec specIsMember other otherIsRow)
  refine ⟨spec, matchedPayload, matchedChildren, matchedChildren',
    specEq, scrutineeIsCell, ?_, matchedChildrenPar⟩
  dsimp only [IotaRuleDesc.scrutineeTermAt?]
  rw [specEq, optionSomeBindExplicit, lookupRelatedEq, targetIsCell]

/-! ## Firing preservation -/

/-- ONE spec's pattern test survives pointwise parallel reduction of
the spine: the slot's head cell can only step by congruence (head
rigidity), so the head AND the payload persist and the guard answers
identically. -/
theorem IotaRuleDesc.scrutineeSpecFires_parPreserved (rule : IotaRuleDesc)
    {table : List IotaRuleDesc} {scope : Nat}
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spinePar : ParStepOverTableChildren table spine spine')
    {spec : ScrutineeSpec}
    (specIsRigid : ∀ other, other ∈ table →
      spec.head ≠ other.elimGenerator)
    (specFires : rule.scrutineeSpecFires spine spec = true) :
    rule.scrutineeSpecFires spine' spec = true := by
  obtain ⟨matchedPayload, matchedChildren, slotHoldsHead⟩ :=
    rule.scrutineeSpecFires_slotHoldsHead specFires
  -- the ORIGINAL guard verdict, with the dite collapsed
  have guardPasses :
      (match spec.payloadGuard? with
        | none => true
        | some payloadGuard => payloadGuard scope matchedPayload)
      = true := by
    have specFiresDite :
        (if isHead : spec.head = spec.head then
          (match spec.payloadGuard? with
            | none => true
            | some payloadGuard =>
                payloadGuard scope
                  (Eq.rec (motive := fun matchedHead _ =>
                      matchedHead.payload scope)
                    matchedPayload isHead))
        else false) = true := by
      dsimp only [IotaRuleDesc.scrutineeSpecFires] at specFires
      rw [slotHoldsHead] at specFires
      exact specFires
    rw [dif_pos rfl] at specFiresDite
    exact specFiresDite
  -- the reduced slot holds the same head with the same payload
  obtain ⟨targetTerm, lookupRelatedEq, relatedPar⟩ :=
    spinePar.lookupAtShiftZeroRelated spec.slot slotHoldsHead
  obtain ⟨matchedChildren', targetIsCell, _matchedChildrenPar⟩ :=
    relatedPar.invertAtRigidHead rfl specIsRigid
  -- refire on the reduced spine
  dsimp only [IotaRuleDesc.scrutineeSpecFires]
  rw [lookupRelatedEq, targetIsCell]
  show (if isHead : spec.head = spec.head then
      (match spec.payloadGuard? with
        | none => true
        | some payloadGuard =>
            payloadGuard scope
              (Eq.rec (motive := fun matchedHead _ =>
                  matchedHead.payload scope)
                matchedPayload isHead))
    else false) = true
  rw [dif_pos rfl]
  exact guardPasses

/-- The full pattern test survives pointwise parallel reduction, spec
by spec. -/
theorem IotaRuleDesc.scrutineesFire_parPreserved (rule : IotaRuleDesc)
    {table : List IotaRuleDesc} {scope : Nat}
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spinePar : ParStepOverTableChildren table spine spine') :
    (specs : List ScrutineeSpec) →
    (∀ spec, spec ∈ specs → ∀ other, other ∈ table →
      spec.head ≠ other.elimGenerator) →
    rule.scrutineesFire spine specs = true →
    rule.scrutineesFire spine' specs = true
  | [], _, _ => rfl
  | spec :: restSpecs, specsAreRigid, allFire => by
      dsimp only [IotaRuleDesc.scrutineesFire] at allFire ⊢
      obtain ⟨specFires, restFire⟩ := andEqTrueSplit allFire
      rw [rule.scrutineeSpecFires_parPreserved spinePar
          (fun other otherIsRow =>
            specsAreRigid spec (.head _) other otherIsRow) specFires,
        rule.scrutineesFire_parPreserved spinePar restSpecs
          (fun innerSpec isInRest other otherIsRow =>
            specsAreRigid innerSpec (.tail _ isInRest) other otherIsRow)
          restFire]
      rfl

/-! ## Payload reads are identical across the reduction -/

/-- A `builtGen` payload source resolves to the SAME payload on the
reduced spine: a constant family never reads the spine, and a scrutinee
transform reads the matched payload, which congruence preserves on the
nose. -/
theorem IotaRuleDesc.resolvePayloadSource?_parPreserved
    (rule : IotaRuleDesc) {table : List IotaRuleDesc} {scope : Nat}
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spinePar : ParStepOverTableChildren table spine spine')
    (allFire : rule.scrutineesFire spine rule.scrutinees = true)
    (scrutineeHeadsAreRigid : ∀ spec, spec ∈ rule.scrutinees →
      ∀ other, other ∈ table → spec.head ≠ other.elimGenerator)
    (depth : Nat) {builtHead : Generator}
    (payloadSource : PayloadSource builtHead)
    {builtPayload : builtHead.payload (scope + depth)}
    (resolved : rule.resolvePayloadSource? spine depth payloadSource
      = some builtPayload) :
    rule.resolvePayloadSource? spine' depth payloadSource
      = some builtPayload := by
  cases payloadSource with
  | constantFamily payloadFamily => exact resolved
  | transformedFromScrutinee scrutineeIndex sourceHead payloadTransform =>
      dsimp only [IotaRuleDesc.resolvePayloadSource?] at resolved ⊢
      obtain ⟨scrutineeTerm, termEq, matchEq⟩ := optionBindEqSome resolved
      obtain ⟨spec, matchedPayload, matchedChildren, matchedChildren',
          _specEq, scrutineeIsCell, termRelatedEq, _matchedChildrenPar⟩ :=
        rule.scrutineeCellExtraction_parRelated spinePar allFire
          scrutineeHeadsAreRigid scrutineeIndex termEq
      subst scrutineeIsCell
      rw [termRelatedEq, optionSomeBindMonadic]
      exact matchEq

/-! ## Slot replacement relatedness -/

/-- Replacing a slot of pointwise-related spines with related
replacements yields pointwise-related spines. -/
theorem RawTermChildren.replaceChildAt?_parRelated
    {table : List IotaRuleDesc} :
    {binderShifts : List Nat} → {scope : Nat} →
    {children children' : RawTermChildren binderShifts scope} →
    ParStepOverTableChildren table children children' →
    (slot : Nat) → {replacement replacement' : RawTerm scope} →
    ParStepOverTable table replacement replacement' →
    {replaced : RawTermChildren binderShifts scope} →
    children.replaceChildAt? slot replacement = some replaced →
    ∃ replaced', children'.replaceChildAt? slot replacement' = some replaced'
      ∧ ParStepOverTableChildren table replaced replaced'
  | _, _, _, _, .nil, _, _, _, _, _, replaceEq => nomatch replaceEq
  | _, _, _, _,
      @ParStepOverTableChildren.cons _ _ headShift _ _ _ _ _
        _headPar tailPar, 0, _, _, replacementPar, _, replaceEq => by
      cases headShift with
      | zero =>
          obtain rfl := Option.some.inj replaceEq
          exact ⟨_, rfl, .cons replacementPar tailPar⟩
      | succ _ => exact nomatch replaceEq
  | _, _, _, _, .cons headPar tailPar, slot + 1, _, _,
      replacementPar, _, replaceEq => by
      dsimp only [RawTermChildren.replaceChildAt?] at replaceEq ⊢
      obtain ⟨replacedTail, replaceTailEq, mapEq⟩ :=
        optionMapEqSome replaceEq
      obtain ⟨replacedTail', replaceTailRelatedEq, replacedTailPar⟩ :=
        RawTermChildren.replaceChildAt?_parRelated tailPar slot
          replacementPar replaceTailEq
      rw [replaceTailRelatedEq, optionSomeMap]
      exact ⟨_, rfl, mapEq ▸ .cons headPar replacedTailPar⟩

end FX1Poly.Core

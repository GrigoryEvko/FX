import FX1Poly.Core.EtaSpinePointwise
import FX1Poly.Core.IotaTableEquivariance
import FX1Poly.Core.TableParallelStabilitySubstrate

/-! # EtaStabilitySubstrate — ETA-T5 increment 4.3a: the pointwise-star
spine relation and the stability bricks

The template-interpreter stability induction relates spines POINTWISE
BY ETA-STAR (replacement chains and interpreted sub-results are stars,
not single steps).  This file ships the relation and every brick the
induction consumes:

  * `EtaChildrenPointwiseStar` with reflexivity, the embeddings from
    the single-step relations, sequentialization into
    `StepEtaOverTableChildrenStar`, and renaming / spine-weakening
    transport;
  * `StepEtaOverTableStar.weakenByLift` — stars lift through iterated
    weakening;
  * the shift-0/1/2 composed-read lookup bricks (star-valued);
  * `ScrutineeCellsEtaRelated` — the SUPPLIED scrutinee hypothesis:
    each derived scrutinee cell keeps its head and payload and its
    children relate pointwise-by-star.  Supplied, never derived: eta
    intro roots ARE scrutinee heads, so no rigidity certificate can
    invert an eta step at a scrutinee cell (the duality case is
    excluded by the consumer's case split, not here);
  * the structured scrutinee extraction, the payload-read
    preservation, and the slot-replacement brick.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaStabilitySubstrate.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation (RawRenaming)

/-! ## The pointwise-star spine relation -/

/-- Every spine position relates by an eta star. -/
inductive EtaChildrenPointwiseStar (etaTable : List EtaRuleDesc) :
    {parentScope : Nat} → {binderShifts : List Nat} →
    RawTermChildren binderShifts parentScope →
    RawTermChildren binderShifts parentScope → Prop where
  | nil {parentScope : Nat} :
      EtaChildrenPointwiseStar etaTable
        (RawTermChildren.childNil (scope := parentScope))
        RawTermChildren.childNil
  | cons {parentScope headShift : Nat} {restShifts : List Nat}
      {head head' : RawTerm (parentScope + headShift)}
      (headStar : StepEtaOverTableStar etaTable head head')
      {rest rest' : RawTermChildren restShifts parentScope}
      (tailRelated : EtaChildrenPointwiseStar etaTable rest rest') :
      EtaChildrenPointwiseStar etaTable
        (RawTermChildren.childCons head rest)
        (RawTermChildren.childCons head' rest')

/-- Pointwise-star is reflexive. -/
theorem EtaChildrenPointwiseStar.refl {etaTable : List EtaRuleDesc}
    {parentScope : Nat} :
    {binderShifts : List Nat} →
    (children : RawTermChildren binderShifts parentScope) →
    EtaChildrenPointwiseStar etaTable children children
  | _, .childNil => .nil
  | _, .childCons _head rest =>
      .cons (.refl _) (EtaChildrenPointwiseStar.refl rest)

/-- The refl-or-step relation embeds. -/
theorem EtaChildrenPointwiseStar.ofPointwise
    {etaTable : List EtaRuleDesc} {parentScope : Nat} :
    {binderShifts : List Nat} →
    {children children' : RawTermChildren binderShifts parentScope} →
    EtaChildrenPointwise etaTable children children' →
    EtaChildrenPointwiseStar etaTable children children'
  | _, _, _, .nil => .nil
  | _, _, _, .consEqual _head tailRelated =>
      .cons (.refl _)
        (EtaChildrenPointwiseStar.ofPointwise tailRelated)
  | _, _, _, .consStep headStep tailRelated =>
      .cons (StepEtaOverTableStar.single headStep)
        (EtaChildrenPointwiseStar.ofPointwise tailRelated)

/-- A one-position spine step embeds. -/
theorem EtaChildrenPointwiseStar.ofChildrenStep
    {etaTable : List EtaRuleDesc} {parentScope : Nat}
    {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (childrenStep : StepEtaOverTableChildren etaTable children children') :
    EtaChildrenPointwiseStar etaTable children children' :=
  EtaChildrenPointwiseStar.ofPointwise
    (EtaChildrenPointwise.ofChildrenStep childrenStep)

/-- Sequentialize: per-position stars compose into one spine star. -/
theorem EtaChildrenPointwiseStar.toSequentialStar
    {etaTable : List EtaRuleDesc} {parentScope : Nat} :
    {binderShifts : List Nat} →
    {children children' : RawTermChildren binderShifts parentScope} →
    EtaChildrenPointwiseStar etaTable children children' →
    StepEtaOverTableChildrenStar etaTable children children'
  | _, _, _, .nil => .refl _
  | _, _, _, @EtaChildrenPointwiseStar.cons _ _ _ _ _ head' headStar
      rest _rest' tailRelated =>
      StepEtaOverTableChildrenStar.concat
        (StepEtaOverTableChildrenStar.hereLift rest headStar)
        (StepEtaOverTableChildrenStar.thereLift head'
          (EtaChildrenPointwiseStar.toSequentialStar tailRelated))

/-! ## Renaming and weakening transport -/

/-- Pointwise-star transports along a spine renaming (per-position
lifted renamings). -/
theorem EtaChildrenPointwiseStar.rename {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    {parentScope parentTargetScope : Nat}
    (someRenaming : RawRenaming parentScope parentTargetScope) :
    {binderShifts : List Nat} →
    {children children' : RawTermChildren binderShifts parentScope} →
    EtaChildrenPointwiseStar etaTable children children' →
    EtaChildrenPointwiseStar etaTable
      (RawTermChildren.rename someRenaming children)
      (RawTermChildren.rename someRenaming children')
  | _, _, _, .nil => .nil
  | _, _, _, @EtaChildrenPointwiseStar.cons _ _ headShift _ _ _
      headStar _ _ tailRelated =>
      .cons
        (StepEtaOverTableStar.rename rowsAreScopeSafe
          (iterateLiftRaw someRenaming headShift) headStar)
        (EtaChildrenPointwiseStar.rename rowsAreScopeSafe someRenaming
          tailRelated)

/-- Pointwise-star transports along `weakenSpineBy`. -/
theorem EtaChildrenPointwiseStar.weakenSpineBy
    {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    {parentScope : Nat} {binderShifts : List Nat} :
    (depth : Nat) →
    {children children' : RawTermChildren binderShifts parentScope} →
    EtaChildrenPointwiseStar etaTable children children' →
    EtaChildrenPointwiseStar etaTable
      (RawTermChildren.weakenSpineBy depth children)
      (RawTermChildren.weakenSpineBy depth children')
  | 0, _, _, spineRelated => spineRelated
  | depth + 1, _, _, spineRelated =>
      EtaChildrenPointwiseStar.rename rowsAreScopeSafe RawRenaming.weaken
        (EtaChildrenPointwiseStar.weakenSpineBy rowsAreScopeSafe depth
          spineRelated)

/-- Stars lift through iterated weakening. -/
theorem StepEtaOverTableStar.weakenByLift {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    {scope : Nat} :
    (depth : Nat) → {source target : RawTerm scope} →
    StepEtaOverTableStar etaTable source target →
    StepEtaOverTableStar etaTable (RawTerm.weakenBy depth source)
      (RawTerm.weakenBy depth target)
  | 0, _, _, etaStar => etaStar
  | depth + 1, _, _, etaStar =>
      StepEtaOverTableStar.weaken rowsAreScopeSafe
        (StepEtaOverTableStar.weakenByLift rowsAreScopeSafe depth etaStar)

/-! ## The composed-read lookup bricks -/

/-- A shift-0 composed read across a pointwise-star spine. -/
theorem EtaChildrenPointwiseStar.lookupAtShiftZeroRelated
    {etaTable : List EtaRuleDesc} :
    {binderShifts : List Nat} → {scope : Nat} →
    {children children' : RawTermChildren binderShifts scope} →
    EtaChildrenPointwiseStar etaTable children children' →
    (slot : Nat) → {sourceTerm : RawTerm scope} →
    (scopedChildAt? children.toScopedChildren slot).bind
        ScopedChild.atShiftZero?
      = some sourceTerm →
    ∃ targetTerm : RawTerm scope,
      (scopedChildAt? children'.toScopedChildren slot).bind
          ScopedChild.atShiftZero?
        = some targetTerm
      ∧ StepEtaOverTableStar etaTable sourceTerm targetTerm
  | _, _, _, _, .nil, _, _, lookupEq => nomatch lookupEq
  | _, _, _, _,
      @EtaChildrenPointwiseStar.cons _ _ headShift _ _ _ headStar _ _
        _tailRelated, 0, _, lookupEq => by
      cases headShift with
      | zero =>
          obtain rfl := Option.some.inj lookupEq
          exact ⟨_, rfl, headStar⟩
      | succ _ => exact nomatch lookupEq
  | _, _, _, _, .cons _headStar tailRelated, slot + 1, _, lookupEq =>
      EtaChildrenPointwiseStar.lookupAtShiftZeroRelated tailRelated slot
        lookupEq

/-- A shift-1 composed read across a pointwise-star spine. -/
theorem EtaChildrenPointwiseStar.lookupAtShiftOneRelated
    {etaTable : List EtaRuleDesc} :
    {binderShifts : List Nat} → {scope : Nat} →
    {children children' : RawTermChildren binderShifts scope} →
    EtaChildrenPointwiseStar etaTable children children' →
    (slot : Nat) → {sourceBody : RawTerm (scope + 1)} →
    (scopedChildAt? children.toScopedChildren slot).bind
        ScopedChild.atShiftOne?
      = some sourceBody →
    ∃ targetBody : RawTerm (scope + 1),
      (scopedChildAt? children'.toScopedChildren slot).bind
          ScopedChild.atShiftOne?
        = some targetBody
      ∧ StepEtaOverTableStar etaTable sourceBody targetBody
  | _, _, _, _, .nil, _, _, lookupEq => nomatch lookupEq
  | _, _, _, _,
      @EtaChildrenPointwiseStar.cons _ _ headShift _ _ _ headStar _ _
        _tailRelated, 0, _, lookupEq => by
      cases headShift with
      | zero => exact nomatch lookupEq
      | succ priorShift =>
          cases priorShift with
          | zero =>
              obtain rfl := Option.some.inj lookupEq
              exact ⟨_, rfl, headStar⟩
          | succ _ => exact nomatch lookupEq
  | _, _, _, _, .cons _headStar tailRelated, slot + 1, _, lookupEq =>
      EtaChildrenPointwiseStar.lookupAtShiftOneRelated tailRelated slot
        lookupEq

/-- A shift-2 composed read across a pointwise-star spine. -/
theorem EtaChildrenPointwiseStar.lookupAtShiftTwoRelated
    {etaTable : List EtaRuleDesc} :
    {binderShifts : List Nat} → {scope : Nat} →
    {children children' : RawTermChildren binderShifts scope} →
    EtaChildrenPointwiseStar etaTable children children' →
    (slot : Nat) → {sourceBody : RawTerm (scope + 2)} →
    (scopedChildAt? children.toScopedChildren slot).bind
        ScopedChild.atShiftTwo?
      = some sourceBody →
    ∃ targetBody : RawTerm (scope + 2),
      (scopedChildAt? children'.toScopedChildren slot).bind
          ScopedChild.atShiftTwo?
        = some targetBody
      ∧ StepEtaOverTableStar etaTable sourceBody targetBody
  | _, _, _, _, .nil, _, _, lookupEq => nomatch lookupEq
  | _, _, _, _,
      @EtaChildrenPointwiseStar.cons _ _ headShift _ _ _ headStar _ _
        _tailRelated, 0, _, lookupEq => by
      cases headShift with
      | zero => exact nomatch lookupEq
      | succ priorShift =>
          cases priorShift with
          | zero => exact nomatch lookupEq
          | succ priorPriorShift =>
              cases priorPriorShift with
              | zero =>
                  obtain rfl := Option.some.inj lookupEq
                  exact ⟨_, rfl, headStar⟩
              | succ _ => exact nomatch lookupEq
  | _, _, _, _, .cons _headStar tailRelated, slot + 1, _, lookupEq =>
      EtaChildrenPointwiseStar.lookupAtShiftTwoRelated tailRelated slot
        lookupEq

/-! ## The supplied scrutinee hypothesis -/

/-- **The scrutinee-cell hypothesis**: every derived scrutinee cell of
the source spine reappears on the related spine with the SAME head and
payload and pointwise-star-related children.  SUPPLIED by the
quasi-commutation's case split (equal reads in the non-scrutinee case;
a cong inversion in the scrutinee-cong case) — never derived from a
rigidity certificate, because eta intro roots ARE scrutinee heads. -/
def ScrutineeCellsEtaRelated (rule : IotaRuleDesc)
    (etaTable : List EtaRuleDesc) {scope : Nat}
    (spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope) :
    Prop :=
  ∀ (scrutineeIndex : Nat) {spec : ScrutineeSpec},
    rule.scrutineeSpecAt? scrutineeIndex = some spec →
    ∀ {matchedPayload : spec.head.payload scope}
      {matchedChildren : RawTermChildren spec.head.binderShifts scope},
    rule.scrutineeTermAt? scrutineeIndex spine
      = some (.mkGen spec.head matchedPayload matchedChildren) →
    ∃ matchedChildren',
      rule.scrutineeTermAt? scrutineeIndex spine'
        = some (.mkGen spec.head matchedPayload matchedChildren')
      ∧ EtaChildrenPointwiseStar etaTable matchedChildren
          matchedChildren'

/-- The plain derived-scrutinee read across a pointwise-star spine (no
head structure — the `theScrutineeAt` consumer). -/
theorem IotaRuleDesc.scrutineeTermAt?_etaRelated (rule : IotaRuleDesc)
    {etaTable : List EtaRuleDesc} {scope : Nat}
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spineRelated : EtaChildrenPointwiseStar etaTable spine spine')
    (scrutineeIndex : Nat) {scrutineeTerm : RawTerm scope}
    (termEq : rule.scrutineeTermAt? scrutineeIndex spine
      = some scrutineeTerm) :
    ∃ scrutineeTerm',
      rule.scrutineeTermAt? scrutineeIndex spine' = some scrutineeTerm'
      ∧ StepEtaOverTableStar etaTable scrutineeTerm scrutineeTerm' := by
  dsimp only [IotaRuleDesc.scrutineeTermAt?] at termEq ⊢
  obtain ⟨spec, specEq, lookupEq⟩ := optionBindEqSome termEq
  obtain ⟨targetTerm, lookupRelatedEq, relatedStar⟩ :=
    spineRelated.lookupAtShiftZeroRelated spec.slot lookupEq
  rw [specEq, optionSomeBindExplicit]
  exact ⟨targetTerm, lookupRelatedEq, relatedStar⟩

/-- **The structured scrutinee extraction**: under the source firing
and the supplied cell hypothesis, the derived scrutinee is a cell of
the declared head, the related spine's scrutinee keeps the head and
payload, and the children relate pointwise-by-star. -/
theorem IotaRuleDesc.scrutineeCellExtraction_etaRelated
    (rule : IotaRuleDesc) {etaTable : List EtaRuleDesc} {scope : Nat}
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (allFire : rule.scrutineesFire spine rule.scrutinees = true)
    (cellsRelated : ScrutineeCellsEtaRelated rule etaTable spine spine')
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
      ∧ EtaChildrenPointwiseStar etaTable matchedChildren
          matchedChildren' := by
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
      scrutineeTerm = .mkGen spec.head matchedPayload matchedChildren :=
    Option.some.inj (lookupEq.symm.trans slotHoldsHead)
  have sourceCellRead :
      rule.scrutineeTermAt? scrutineeIndex spine
        = some (.mkGen spec.head matchedPayload matchedChildren) :=
    termEq.trans (congrArg some scrutineeIsCell)
  obtain ⟨matchedChildren', targetCellRead, matchedChildrenRelated⟩ :=
    cellsRelated scrutineeIndex specEq sourceCellRead
  exact ⟨spec, matchedPayload, matchedChildren, matchedChildren',
    specEq, scrutineeIsCell, targetCellRead, matchedChildrenRelated⟩

/-! ## Payload reads are identical across the relation -/

/-- A `builtGen` payload source resolves to the SAME payload on the
related spine: a constant family never reads the spine, and a
scrutinee transform reads the matched payload, which the supplied cell
hypothesis preserves on the nose. -/
theorem IotaRuleDesc.resolvePayloadSource?_etaPreserved
    (rule : IotaRuleDesc) {etaTable : List EtaRuleDesc} {scope : Nat}
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (allFire : rule.scrutineesFire spine rule.scrutinees = true)
    (cellsRelated : ScrutineeCellsEtaRelated rule etaTable spine spine')
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
          _specEq, scrutineeIsCell, termRelatedEq, _matchedChildrenRel⟩ :=
        rule.scrutineeCellExtraction_etaRelated allFire cellsRelated
          scrutineeIndex termEq
      subst scrutineeIsCell
      rw [termRelatedEq, optionSomeBindMonadic]
      exact matchEq

/-! ## Slot replacement -/

/-- Replacing a slot of pointwise-star spines with star-related
replacements yields pointwise-star spines. -/
theorem RawTermChildren.replaceChildAt?_etaRelated
    {etaTable : List EtaRuleDesc} :
    {binderShifts : List Nat} → {scope : Nat} →
    {children children' : RawTermChildren binderShifts scope} →
    EtaChildrenPointwiseStar etaTable children children' →
    (slot : Nat) → {replacement replacement' : RawTerm scope} →
    StepEtaOverTableStar etaTable replacement replacement' →
    {replaced : RawTermChildren binderShifts scope} →
    children.replaceChildAt? slot replacement = some replaced →
    ∃ replaced',
      children'.replaceChildAt? slot replacement' = some replaced'
      ∧ EtaChildrenPointwiseStar etaTable replaced replaced'
  | _, _, _, _, .nil, _, _, _, _, _, replaceEq => nomatch replaceEq
  | _, _, _, _,
      @EtaChildrenPointwiseStar.cons _ _ headShift _ _ _ _headStar _ _
        tailRelated, 0, _, _, replacementStar, _, replaceEq => by
      cases headShift with
      | zero =>
          obtain rfl := Option.some.inj replaceEq
          exact ⟨_, rfl, .cons replacementStar tailRelated⟩
      | succ _ => exact nomatch replaceEq
  | _, _, _, _, .cons headStar tailRelated, slot + 1, _, _,
      replacementStar, _, replaceEq => by
      dsimp only [RawTermChildren.replaceChildAt?] at replaceEq ⊢
      obtain ⟨replacedTail, replaceTailEq, mapEq⟩ :=
        optionMapEqSome replaceEq
      obtain ⟨replacedTail', replaceTailRelatedEq, replacedTailRelated⟩ :=
        RawTermChildren.replaceChildAt?_etaRelated tailRelated slot
          replacementStar replaceTailEq
      rw [replaceTailRelatedEq, optionSomeMap]
      exact ⟨_, rfl, mapEq ▸ .cons headStar replacedTailRelated⟩

end FX1Poly.Core

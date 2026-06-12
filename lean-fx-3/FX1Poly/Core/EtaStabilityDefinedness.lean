import FX1Poly.Core.EtaTableStability

/-! # EtaStabilityDefinedness — ETA-T5 increment 4.4a: interpretation
success transfers BACKWARD across the eta relation

The quasi-commutation's cong-then-redex case holds a firing on the
POST-eta spine and must fire the row on the PRE-eta spine.  The
pattern match transfers by the per-case head/payload analysis; what
remains is interpretation SUCCESS — and success depends only on the
spine's READ SHAPE: the binder shifts (shared by both spines — same
indexed type) and the scrutinee cells' heads and payloads (shared by
the supplied `ScrutineeCellsEtaRelated` hypothesis).  So a successful
interpretation on the related spine yields SOME successful
interpretation on the source spine; the shipped FORWARD stability then
relates the two results by eta star.

The bricks are shape equi-definedness: composed slot reads and slot
replacements succeed uniformly across any two spines of the same
indexed type.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaStabilityDefinedness.lean`. -/

namespace FX1Poly.Core

/-! ## Shape equi-definedness of the composed reads -/

/-- A successful shift-0 composed read transfers to ANY spine of the
same indexed type. -/
theorem composedReadAtShiftZero_equiDefined {scope : Nat} :
    {binderShifts : List Nat} →
    (children otherChildren : RawTermChildren binderShifts scope) →
    (slot : Nat) → {found : RawTerm scope} →
    (scopedChildAt? children.toScopedChildren slot).bind
        ScopedChild.atShiftZero?
      = some found →
    ∃ other : RawTerm scope,
      (scopedChildAt? otherChildren.toScopedChildren slot).bind
          ScopedChild.atShiftZero?
        = some other
  | _, .childNil, .childNil, _, _, lookupEq => nomatch lookupEq
  | headShift :: _, .childCons _head _rest,
      .childCons otherHead _otherRest, 0, _, lookupEq => by
      cases headShift with
      | zero => exact ⟨otherHead, rfl⟩
      | succ _ => exact nomatch lookupEq
  | _ :: _, .childCons _head rest, .childCons _otherHead otherRest,
      slot + 1, _, lookupEq =>
      composedReadAtShiftZero_equiDefined rest otherRest slot lookupEq

/-- A successful shift-1 composed read transfers to ANY spine of the
same indexed type. -/
theorem composedReadAtShiftOne_equiDefined {scope : Nat} :
    {binderShifts : List Nat} →
    (children otherChildren : RawTermChildren binderShifts scope) →
    (slot : Nat) → {found : RawTerm (scope + 1)} →
    (scopedChildAt? children.toScopedChildren slot).bind
        ScopedChild.atShiftOne?
      = some found →
    ∃ other : RawTerm (scope + 1),
      (scopedChildAt? otherChildren.toScopedChildren slot).bind
          ScopedChild.atShiftOne?
        = some other
  | _, .childNil, .childNil, _, _, lookupEq => nomatch lookupEq
  | headShift :: _, .childCons _head _rest,
      .childCons otherHead _otherRest, 0, _, lookupEq => by
      cases headShift with
      | zero => exact nomatch lookupEq
      | succ priorShift =>
          cases priorShift with
          | zero => exact ⟨otherHead, rfl⟩
          | succ _ => exact nomatch lookupEq
  | _ :: _, .childCons _head rest, .childCons _otherHead otherRest,
      slot + 1, _, lookupEq =>
      composedReadAtShiftOne_equiDefined rest otherRest slot lookupEq

/-- A successful shift-2 composed read transfers to ANY spine of the
same indexed type. -/
theorem composedReadAtShiftTwo_equiDefined {scope : Nat} :
    {binderShifts : List Nat} →
    (children otherChildren : RawTermChildren binderShifts scope) →
    (slot : Nat) → {found : RawTerm (scope + 2)} →
    (scopedChildAt? children.toScopedChildren slot).bind
        ScopedChild.atShiftTwo?
      = some found →
    ∃ other : RawTerm (scope + 2),
      (scopedChildAt? otherChildren.toScopedChildren slot).bind
          ScopedChild.atShiftTwo?
        = some other
  | _, .childNil, .childNil, _, _, lookupEq => nomatch lookupEq
  | headShift :: _, .childCons _head _rest,
      .childCons otherHead _otherRest, 0, _, lookupEq => by
      cases headShift with
      | zero => exact nomatch lookupEq
      | succ priorShift =>
          cases priorShift with
          | zero => exact nomatch lookupEq
          | succ priorPriorShift =>
              cases priorPriorShift with
              | zero => exact ⟨otherHead, rfl⟩
              | succ _ => exact nomatch lookupEq
  | _ :: _, .childCons _head rest, .childCons _otherHead otherRest,
      slot + 1, _, lookupEq =>
      composedReadAtShiftTwo_equiDefined rest otherRest slot lookupEq

/-- A successful slot replacement transfers to ANY spine of the same
indexed type (with any replacement value). -/
theorem replaceChildAt?_equiDefined {scope : Nat} :
    {binderShifts : List Nat} →
    (children otherChildren : RawTermChildren binderShifts scope) →
    (slot : Nat) → {replacement : RawTerm scope} →
    {replaced : RawTermChildren binderShifts scope} →
    children.replaceChildAt? slot replacement = some replaced →
    (otherReplacement : RawTerm scope) →
    ∃ otherReplaced,
      otherChildren.replaceChildAt? slot otherReplacement
        = some otherReplaced
  | _, .childNil, .childNil, _, _, _, replaceEq, _ => nomatch replaceEq
  | headShift :: _, .childCons _head _rest,
      .childCons _otherHead otherRest, 0, _, _, replaceEq,
      otherReplacement => by
      cases headShift with
      | zero => exact ⟨.childCons otherReplacement otherRest, rfl⟩
      | succ _ => exact nomatch replaceEq
  | _ :: _, .childCons _head rest, .childCons otherHead otherRest,
      slot + 1, _, _, replaceEq, otherReplacement => by
      dsimp only [RawTermChildren.replaceChildAt?] at replaceEq ⊢
      obtain ⟨replacedTail, replaceTailEq, _mapEq⟩ :=
        optionMapEqSome replaceEq
      obtain ⟨otherReplacedTail, otherReplaceTailEq⟩ :=
        replaceChildAt?_equiDefined rest otherRest slot replaceTailEq
          otherReplacement
      rw [otherReplaceTailEq, optionSomeMap]
      exact ⟨_, rfl⟩

/-! ## The scrutinee-read pin (source side) -/

/-- Under the source firing, the derived scrutinee read at any declared
index succeeds with the pinned head/payload cell. -/
theorem IotaRuleDesc.scrutineeTermAt?_ofFiring (rule : IotaRuleDesc)
    {scope : Nat}
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    (allFire : rule.scrutineesFire spine rule.scrutinees = true)
    {scrutineeIndex : Nat} {spec : ScrutineeSpec}
    (specEq : rule.scrutineeSpecAt? scrutineeIndex = some spec) :
    ∃ (matchedPayload : spec.head.payload scope)
      (matchedChildren : RawTermChildren spec.head.binderShifts scope),
      rule.scrutineeTermAt? scrutineeIndex spine
        = some (.mkGen spec.head matchedPayload matchedChildren) := by
  have specIsMember : spec ∈ rule.scrutinees :=
    listEntryAt?_mem rule.scrutinees scrutineeIndex specEq
  have specFires : rule.scrutineeSpecFires spine spec = true :=
    rule.scrutineesFire_memberFires rule.scrutinees allFire specIsMember
  obtain ⟨matchedPayload, matchedChildren, slotHoldsHead⟩ :=
    rule.scrutineeSpecFires_slotHoldsHead specFires
  refine ⟨matchedPayload, matchedChildren, ?_⟩
  dsimp only [IotaRuleDesc.scrutineeTermAt?]
  rw [specEq, optionSomeBindExplicit]
  exact slotHoldsHead

/-! ## The definedness mutual -/

mutual

/-- ★ **Backward success transfer**: a successful interpretation on the
RELATED spine yields some successful interpretation on the SOURCE spine
— success depends only on the shared binder shifts and the scrutinee
heads/payloads the supplied hypothesis preserves. -/
theorem IotaRuleDesc.interpretTemplate?_definedTransfer
    (rule : IotaRuleDesc) {etaTable : List EtaRuleDesc}
    {scope : Nat} (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (allFire : rule.scrutineesFire spine rule.scrutinees = true)
    (cellsRelated : ScrutineeCellsEtaRelated rule etaTable spine spine') :
    (depth : Nat) → (template : ReductTemplate) →
    {result' : RawTerm (scope + depth)} →
    rule.interpretTemplate? elimPayload spine' depth template
      = some result' →
    ∃ result,
      rule.interpretTemplate? elimPayload spine depth template
        = some result
  | depth, .boundVarAt binderIndex, result', interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      by_cases isBound : binderIndex < depth
      · rw [dif_pos isBound]
        exact ⟨_, rfl⟩
      · rw [dif_neg isBound] at interpreted
        injection interpreted
  | depth, .spineChildAt slot, result', interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨spineChild', lookupEq', restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨childTerm', projEq', _someEq⟩ := optionBindEqSome restEq
      have composedLookup' :
          (scopedChildAt? spine'.toScopedChildren slot).bind
              ScopedChild.atShiftZero?
            = some childTerm' := by
        rw [lookupEq', optionSomeBindExplicit]
        exact projEq'
      obtain ⟨childTerm, composedLookup⟩ :=
        composedReadAtShiftZero_equiDefined spine' spine slot
          composedLookup'
      obtain ⟨spineChild, lookupEq, projEq⟩ :=
        optionBindEqSome composedLookup
      refine ⟨RawTerm.weakenBy depth childTerm, ?_⟩
      rw [lookupEq, optionSomeBindMonadic, projEq, optionSomeBindMonadic]
  | depth, .scrutineeChildAt scrutineeIndex slot, result',
      interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨childrenView', childrenEq', restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨scrutineeChild', childEq', restEq2⟩ :=
        optionBindEqSome restEq
      obtain ⟨childTerm', projEq', _someEq⟩ := optionBindEqSome restEq2
      dsimp only [IotaRuleDesc.scrutineeChildrenAt?] at childrenEq' ⊢
      obtain ⟨scrutineeTerm', termEq', viewEq'⟩ :=
        optionMapEqSome childrenEq'
      -- pin the source-side cell, relate, identify the walked cell
      have specEq : ∃ spec, rule.scrutineeSpecAt? scrutineeIndex
          = some spec := by
        dsimp only [IotaRuleDesc.scrutineeTermAt?] at termEq'
        obtain ⟨spec, specEq, _⟩ := optionBindEqSome termEq'
        exact ⟨spec, specEq⟩
      obtain ⟨spec, specEq⟩ := specEq
      obtain ⟨matchedPayload, matchedChildren, sourceCellRead⟩ :=
        rule.scrutineeTermAt?_ofFiring allFire specEq
      obtain ⟨matchedChildren', targetCellRead, _matchedChildrenRel⟩ :=
        cellsRelated scrutineeIndex specEq sourceCellRead
      have walkedIsCell :
          scrutineeTerm'
            = .mkGen spec.head matchedPayload matchedChildren' :=
        Option.some.inj (termEq'.symm.trans targetCellRead)
      subst walkedIsCell
      -- the inner read transfers by shape
      have composedInner' :
          (scopedChildAt? matchedChildren'.toScopedChildren slot).bind
              ScopedChild.atShiftZero?
            = some childTerm' := by
        rw [show matchedChildren'.toScopedChildren = childrenView'
            from viewEq', childEq', optionSomeBindExplicit]
        exact projEq'
      obtain ⟨childTerm, composedInner⟩ :=
        composedReadAtShiftZero_equiDefined matchedChildren'
          matchedChildren slot composedInner'
      obtain ⟨scrutineeChild, childEq, projEq⟩ :=
        optionBindEqSome composedInner
      refine ⟨RawTerm.weakenBy depth childTerm, ?_⟩
      rw [sourceCellRead, optionSomeMap, optionSomeBindMonadic]
      show ((scopedChildAt? matchedChildren.toScopedChildren slot)
          >>= fun scrutineeChild =>
            scrutineeChild.atShiftZero? >>= fun innerChildTerm =>
              some (RawTerm.weakenBy depth innerChildTerm))
        = some (RawTerm.weakenBy depth childTerm)
      rw [childEq, optionSomeBindMonadic, projEq, optionSomeBindMonadic]
  | depth, .theScrutineeAt scrutineeIndex, result', interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨scrutineeTerm', termEq', _someEq⟩ :=
        optionBindEqSome interpreted
      have specEq : ∃ spec, rule.scrutineeSpecAt? scrutineeIndex
          = some spec := by
        dsimp only [IotaRuleDesc.scrutineeTermAt?] at termEq'
        obtain ⟨spec, specEq, _⟩ := optionBindEqSome termEq'
        exact ⟨spec, specEq⟩
      obtain ⟨spec, specEq⟩ := specEq
      obtain ⟨matchedPayload, matchedChildren, sourceCellRead⟩ :=
        rule.scrutineeTermAt?_ofFiring allFire specEq
      refine ⟨RawTerm.weakenBy depth
        (.mkGen spec.head matchedPayload matchedChildren), ?_⟩
      rw [sourceCellRead, optionSomeBindMonadic]
  | depth, .motiveInstantiatedWith argTemplate, result', interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨motiveSlot, slotEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨argTerm', argEq', restEq2⟩ := optionBindEqSome restEq
      obtain ⟨motiveChild', lookupEq', restEq3⟩ :=
        optionBindEqSome restEq2
      obtain ⟨motiveBody', projEq', _someEq⟩ := optionBindEqSome restEq3
      obtain ⟨argTerm, argEq⟩ :=
        rule.interpretTemplate?_definedTransfer elimPayload allFire
          cellsRelated depth argTemplate argEq'
      have composedLookup' :
          (scopedChildAt? spine'.toScopedChildren motiveSlot).bind
              ScopedChild.atShiftOne?
            = some motiveBody' := by
        rw [lookupEq', optionSomeBindExplicit]
        exact projEq'
      obtain ⟨motiveBody, composedLookup⟩ :=
        composedReadAtShiftOne_equiDefined spine' spine motiveSlot
          composedLookup'
      obtain ⟨motiveChild, lookupEq, projEq⟩ :=
        optionBindEqSome composedLookup
      refine ⟨RawTerm.subst0
        (RawTerm.weakenBodyUnderOneBinderBy depth motiveBody) argTerm,
        ?_⟩
      rw [slotEq, optionSomeBindMonadic, argEq, optionSomeBindMonadic,
        lookupEq, optionSomeBindMonadic, projEq, optionSomeBindMonadic]
  | depth, .motiveInstantiatedWithPair innerTemplate outerTemplate,
      result', interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨motiveSlot, slotEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨innerTerm', innerEq', restEq2⟩ := optionBindEqSome restEq
      obtain ⟨outerTerm', outerEq', restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨motiveChild', lookupEq', restEq4⟩ :=
        optionBindEqSome restEq3
      obtain ⟨motiveBody', projEq', _someEq⟩ := optionBindEqSome restEq4
      obtain ⟨innerTerm, innerEq⟩ :=
        rule.interpretTemplate?_definedTransfer elimPayload allFire
          cellsRelated depth innerTemplate innerEq'
      obtain ⟨outerTerm, outerEq⟩ :=
        rule.interpretTemplate?_definedTransfer elimPayload allFire
          cellsRelated depth outerTemplate outerEq'
      have composedLookup' :
          (scopedChildAt? spine'.toScopedChildren motiveSlot).bind
              ScopedChild.atShiftTwo?
            = some motiveBody' := by
        rw [lookupEq', optionSomeBindExplicit]
        exact projEq'
      obtain ⟨motiveBody, composedLookup⟩ :=
        composedReadAtShiftTwo_equiDefined spine' spine motiveSlot
          composedLookup'
      obtain ⟨motiveChild, lookupEq, projEq⟩ :=
        optionBindEqSome composedLookup
      refine ⟨RawTerm.substPair
        (RawTerm.weakenBodyUnderTwoBindersBy depth motiveBody)
        innerTerm outerTerm, ?_⟩
      rw [slotEq, optionSomeBindMonadic, innerEq, optionSomeBindMonadic,
        outerEq, optionSomeBindMonadic, lookupEq, optionSomeBindMonadic,
        projEq, optionSomeBindMonadic]
  | depth, .builtGen builtHead payloadSource childTemplates, result',
      interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨builtPayload, payloadEq', restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨builtChildren', childrenEq', _someEq⟩ :=
        optionBindEqSome restEq
      have payloadEq :=
        rule.resolvePayloadSource?_definedTransfer elimPayload allFire
          cellsRelated depth payloadSource payloadEq'
      obtain ⟨sourcePayload, payloadSourceEq⟩ := payloadEq
      obtain ⟨builtChildren, childrenEq⟩ :=
        rule.interpretBuiltChildren?_definedTransfer elimPayload allFire
          cellsRelated depth builtHead.binderShifts childTemplates
          childrenEq'
      refine ⟨.mkGen builtHead sourcePayload builtChildren, ?_⟩
      rw [payloadSourceEq, optionSomeBindMonadic, childrenEq,
        optionSomeBindMonadic]
  | depth, .reassembledReplacing replacements, result', interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨payloadAtDepth, payloadEq, restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨replacedSpine', replacedEq', _someEq⟩ :=
        optionBindEqSome restEq
      obtain ⟨replacedSpine, replacedEq⟩ :=
        rule.interpretReplacements?_definedTransfer elimPayload allFire
          cellsRelated depth replacements
          (RawTermChildren.weakenSpineBy depth spine') replacedEq'
          (RawTermChildren.weakenSpineBy depth spine)
      refine ⟨.mkGen rule.elimGenerator payloadAtDepth replacedSpine, ?_⟩
      rw [payloadEq, optionSomeBindMonadic, replacedEq,
        optionSomeBindMonadic]
  | depth, .substOneIntoSpineChild bodySlot argTemplate, result',
      interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨argTerm', argEq', restEq⟩ := optionBindEqSome interpreted
      obtain ⟨bodyChild', lookupEq', restEq2⟩ := optionBindEqSome restEq
      obtain ⟨bodyTerm', projEq', _someEq⟩ := optionBindEqSome restEq2
      obtain ⟨argTerm, argEq⟩ :=
        rule.interpretTemplate?_definedTransfer elimPayload allFire
          cellsRelated depth argTemplate argEq'
      have composedLookup' :
          (scopedChildAt? spine'.toScopedChildren bodySlot).bind
              ScopedChild.atShiftOne?
            = some bodyTerm' := by
        rw [lookupEq', optionSomeBindExplicit]
        exact projEq'
      obtain ⟨bodyTerm, composedLookup⟩ :=
        composedReadAtShiftOne_equiDefined spine' spine bodySlot
          composedLookup'
      obtain ⟨bodyChild, lookupEq, projEq⟩ :=
        optionBindEqSome composedLookup
      refine ⟨RawTerm.subst0
        (RawTerm.weakenBodyUnderOneBinderBy depth bodyTerm) argTerm, ?_⟩
      rw [argEq, optionSomeBindMonadic, lookupEq, optionSomeBindMonadic,
        projEq, optionSomeBindMonadic]
  | depth, .substOneIntoScrutineeChild scrutineeIndex bodySlot
      argTemplate, result', interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨argTerm', argEq', restEq⟩ := optionBindEqSome interpreted
      obtain ⟨childrenView', childrenEq', restEq2⟩ :=
        optionBindEqSome restEq
      obtain ⟨bodyChild', childEq', restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨bodyTerm', projEq', _someEq⟩ := optionBindEqSome restEq3
      obtain ⟨argTerm, argEq⟩ :=
        rule.interpretTemplate?_definedTransfer elimPayload allFire
          cellsRelated depth argTemplate argEq'
      dsimp only [IotaRuleDesc.scrutineeChildrenAt?] at childrenEq' ⊢
      obtain ⟨scrutineeTerm', termEq', viewEq'⟩ :=
        optionMapEqSome childrenEq'
      have specEq : ∃ spec, rule.scrutineeSpecAt? scrutineeIndex
          = some spec := by
        dsimp only [IotaRuleDesc.scrutineeTermAt?] at termEq'
        obtain ⟨spec, specEq, _⟩ := optionBindEqSome termEq'
        exact ⟨spec, specEq⟩
      obtain ⟨spec, specEq⟩ := specEq
      obtain ⟨matchedPayload, matchedChildren, sourceCellRead⟩ :=
        rule.scrutineeTermAt?_ofFiring allFire specEq
      obtain ⟨matchedChildren', targetCellRead, _matchedChildrenRel⟩ :=
        cellsRelated scrutineeIndex specEq sourceCellRead
      have walkedIsCell :
          scrutineeTerm'
            = .mkGen spec.head matchedPayload matchedChildren' :=
        Option.some.inj (termEq'.symm.trans targetCellRead)
      subst walkedIsCell
      have composedInner' :
          (scopedChildAt? matchedChildren'.toScopedChildren
              bodySlot).bind
              ScopedChild.atShiftOne?
            = some bodyTerm' := by
        rw [show matchedChildren'.toScopedChildren = childrenView'
            from viewEq', childEq', optionSomeBindExplicit]
        exact projEq'
      obtain ⟨bodyTerm, composedInner⟩ :=
        composedReadAtShiftOne_equiDefined matchedChildren'
          matchedChildren bodySlot composedInner'
      obtain ⟨bodyChild, childEq, projEq⟩ :=
        optionBindEqSome composedInner
      refine ⟨RawTerm.subst0
        (RawTerm.weakenBodyUnderOneBinderBy depth bodyTerm) argTerm, ?_⟩
      rw [argEq, optionSomeBindMonadic, sourceCellRead, optionSomeMap,
        optionSomeBindMonadic]
      show ((scopedChildAt? matchedChildren.toScopedChildren bodySlot)
          >>= fun bodyChild =>
            bodyChild.atShiftOne? >>= fun innerBodyTerm =>
              some (RawTerm.subst0
                (RawTerm.weakenBodyUnderOneBinderBy depth innerBodyTerm)
                argTerm))
        = some (RawTerm.subst0
            (RawTerm.weakenBodyUnderOneBinderBy depth bodyTerm) argTerm)
      rw [childEq, optionSomeBindMonadic, projEq, optionSomeBindMonadic]
  | depth, .substPairIntoSpineChild bodySlot innerTemplate
      outerTemplate, result', interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨innerTerm', innerEq', restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨outerTerm', outerEq', restEq2⟩ := optionBindEqSome restEq
      obtain ⟨bodyChild', lookupEq', restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨bodyTerm', projEq', _someEq⟩ := optionBindEqSome restEq3
      obtain ⟨innerTerm, innerEq⟩ :=
        rule.interpretTemplate?_definedTransfer elimPayload allFire
          cellsRelated depth innerTemplate innerEq'
      obtain ⟨outerTerm, outerEq⟩ :=
        rule.interpretTemplate?_definedTransfer elimPayload allFire
          cellsRelated depth outerTemplate outerEq'
      have composedLookup' :
          (scopedChildAt? spine'.toScopedChildren bodySlot).bind
              ScopedChild.atShiftTwo?
            = some bodyTerm' := by
        rw [lookupEq', optionSomeBindExplicit]
        exact projEq'
      obtain ⟨bodyTerm, composedLookup⟩ :=
        composedReadAtShiftTwo_equiDefined spine' spine bodySlot
          composedLookup'
      obtain ⟨bodyChild, lookupEq, projEq⟩ :=
        optionBindEqSome composedLookup
      refine ⟨RawTerm.substPair
        (RawTerm.weakenBodyUnderTwoBindersBy depth bodyTerm)
        innerTerm outerTerm, ?_⟩
      rw [innerEq, optionSomeBindMonadic, outerEq, optionSomeBindMonadic,
        lookupEq, optionSomeBindMonadic, projEq, optionSomeBindMonadic]
  | depth, .substPairIntoScrutineeChild scrutineeIndex bodySlot
      innerTemplate outerTemplate, result', interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨innerTerm', innerEq', restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨outerTerm', outerEq', restEq2⟩ := optionBindEqSome restEq
      obtain ⟨childrenView', childrenEq', restEq3⟩ :=
        optionBindEqSome restEq2
      obtain ⟨bodyChild', childEq', restEq4⟩ := optionBindEqSome restEq3
      obtain ⟨bodyTerm', projEq', _someEq⟩ := optionBindEqSome restEq4
      obtain ⟨innerTerm, innerEq⟩ :=
        rule.interpretTemplate?_definedTransfer elimPayload allFire
          cellsRelated depth innerTemplate innerEq'
      obtain ⟨outerTerm, outerEq⟩ :=
        rule.interpretTemplate?_definedTransfer elimPayload allFire
          cellsRelated depth outerTemplate outerEq'
      dsimp only [IotaRuleDesc.scrutineeChildrenAt?] at childrenEq' ⊢
      obtain ⟨scrutineeTerm', termEq', viewEq'⟩ :=
        optionMapEqSome childrenEq'
      have specEq : ∃ spec, rule.scrutineeSpecAt? scrutineeIndex
          = some spec := by
        dsimp only [IotaRuleDesc.scrutineeTermAt?] at termEq'
        obtain ⟨spec, specEq, _⟩ := optionBindEqSome termEq'
        exact ⟨spec, specEq⟩
      obtain ⟨spec, specEq⟩ := specEq
      obtain ⟨matchedPayload, matchedChildren, sourceCellRead⟩ :=
        rule.scrutineeTermAt?_ofFiring allFire specEq
      obtain ⟨matchedChildren', targetCellRead, _matchedChildrenRel⟩ :=
        cellsRelated scrutineeIndex specEq sourceCellRead
      have walkedIsCell :
          scrutineeTerm'
            = .mkGen spec.head matchedPayload matchedChildren' :=
        Option.some.inj (termEq'.symm.trans targetCellRead)
      subst walkedIsCell
      have composedInner' :
          (scopedChildAt? matchedChildren'.toScopedChildren
              bodySlot).bind
              ScopedChild.atShiftTwo?
            = some bodyTerm' := by
        rw [show matchedChildren'.toScopedChildren = childrenView'
            from viewEq', childEq', optionSomeBindExplicit]
        exact projEq'
      obtain ⟨bodyTerm, composedInner⟩ :=
        composedReadAtShiftTwo_equiDefined matchedChildren'
          matchedChildren bodySlot composedInner'
      obtain ⟨bodyChild, childEq, projEq⟩ :=
        optionBindEqSome composedInner
      refine ⟨RawTerm.substPair
        (RawTerm.weakenBodyUnderTwoBindersBy depth bodyTerm)
        innerTerm outerTerm, ?_⟩
      rw [innerEq, optionSomeBindMonadic, outerEq, optionSomeBindMonadic,
        sourceCellRead, optionSomeMap, optionSomeBindMonadic]
      show ((scopedChildAt? matchedChildren.toScopedChildren bodySlot)
          >>= fun bodyChild =>
            bodyChild.atShiftTwo? >>= fun innerBodyTerm =>
              some (RawTerm.substPair
                (RawTerm.weakenBodyUnderTwoBindersBy depth innerBodyTerm)
                innerTerm outerTerm))
        = some (RawTerm.substPair
            (RawTerm.weakenBodyUnderTwoBindersBy depth bodyTerm)
            innerTerm outerTerm)
      rw [childEq, optionSomeBindMonadic, projEq, optionSomeBindMonadic]

/-- Payload-source companion: resolution success transfers backward
(the matched payload is shared, so the resolved payload is shared
too). -/
theorem IotaRuleDesc.resolvePayloadSource?_definedTransfer
    (rule : IotaRuleDesc) {etaTable : List EtaRuleDesc}
    {scope : Nat} (_elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (allFire : rule.scrutineesFire spine rule.scrutinees = true)
    (cellsRelated : ScrutineeCellsEtaRelated rule etaTable spine spine') :
    (depth : Nat) → {builtHead : Generator} →
    (payloadSource : PayloadSource builtHead) →
    {builtPayload : builtHead.payload (scope + depth)} →
    rule.resolvePayloadSource? spine' depth payloadSource
      = some builtPayload →
    ∃ sourcePayload,
      rule.resolvePayloadSource? spine depth payloadSource
        = some sourcePayload
  | depth, _, .constantFamily payloadFamily, _, _resolved =>
      ⟨payloadFamily (scope + depth), rfl⟩
  | depth, _,
      .transformedFromScrutinee scrutineeIndex sourceHead
        payloadTransform, builtPayload, resolved => by
      dsimp only [IotaRuleDesc.resolvePayloadSource?] at resolved ⊢
      obtain ⟨scrutineeTerm', termEq', matchEq'⟩ :=
        optionBindEqSome resolved
      have specEq : ∃ spec, rule.scrutineeSpecAt? scrutineeIndex
          = some spec := by
        dsimp only [IotaRuleDesc.scrutineeTermAt?] at termEq'
        obtain ⟨spec, specEq, _⟩ := optionBindEqSome termEq'
        exact ⟨spec, specEq⟩
      obtain ⟨spec, specEq⟩ := specEq
      obtain ⟨matchedPayload, matchedChildren, sourceCellRead⟩ :=
        rule.scrutineeTermAt?_ofFiring allFire specEq
      obtain ⟨matchedChildren', targetCellRead, _matchedChildrenRel⟩ :=
        cellsRelated scrutineeIndex specEq sourceCellRead
      have walkedIsCell :
          scrutineeTerm'
            = .mkGen spec.head matchedPayload matchedChildren' :=
        Option.some.inj (termEq'.symm.trans targetCellRead)
      subst walkedIsCell
      refine ⟨builtPayload, ?_⟩
      rw [sourceCellRead, optionSomeBindMonadic]
      exact matchEq'

/-- Built-children companion. -/
theorem IotaRuleDesc.interpretBuiltChildren?_definedTransfer
    (rule : IotaRuleDesc) {etaTable : List EtaRuleDesc}
    {scope : Nat} (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (allFire : rule.scrutineesFire spine rule.scrutinees = true)
    (cellsRelated : ScrutineeCellsEtaRelated rule etaTable spine spine') :
    (depth : Nat) → (childShifts : List Nat) →
    (childTemplates : ReductTemplateSpine) →
    {builtChildren' : RawTermChildren childShifts (scope + depth)} →
    rule.interpretBuiltChildren? elimPayload spine' depth childShifts
        childTemplates
      = some builtChildren' →
    ∃ builtChildren,
      rule.interpretBuiltChildren? elimPayload spine depth childShifts
          childTemplates
        = some builtChildren
  | depth, [], .spineNil, _, _interpreted => ⟨.childNil, rfl⟩
  | _, [], .spineCons _ _, _, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted
      injection interpreted
  | _, _ :: _, .spineNil, _, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted
      injection interpreted
  | depth, 0 :: restShifts, .spineCons childTemplate restTemplates, _,
      interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted ⊢
      obtain ⟨childTerm', childEq', restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨restChildren', restChildrenEq', _someEq⟩ :=
        optionBindEqSome restEq
      obtain ⟨childTerm, childEq⟩ :=
        rule.interpretTemplate?_definedTransfer elimPayload allFire
          cellsRelated depth childTemplate childEq'
      obtain ⟨restChildren, restChildrenEq⟩ :=
        rule.interpretBuiltChildren?_definedTransfer elimPayload allFire
          cellsRelated depth restShifts restTemplates restChildrenEq'
      refine ⟨.childCons childTerm restChildren, ?_⟩
      rw [childEq, optionSomeBindMonadic, restChildrenEq,
        optionSomeBindMonadic]
  | depth, 1 :: restShifts, .spineCons childTemplate restTemplates, _,
      interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted ⊢
      obtain ⟨childTerm', childEq', restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨restChildren', restChildrenEq', _someEq⟩ :=
        optionBindEqSome restEq
      obtain ⟨childTerm, childEq⟩ :=
        rule.interpretTemplate?_definedTransfer elimPayload allFire
          cellsRelated (depth + 1) childTemplate childEq'
      obtain ⟨restChildren, restChildrenEq⟩ :=
        rule.interpretBuiltChildren?_definedTransfer elimPayload allFire
          cellsRelated depth restShifts restTemplates restChildrenEq'
      refine ⟨.childCons childTerm restChildren, ?_⟩
      rw [childEq, optionSomeBindMonadic, restChildrenEq,
        optionSomeBindMonadic]
  | depth, 2 :: restShifts, .spineCons childTemplate restTemplates, _,
      interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted ⊢
      obtain ⟨childTerm', childEq', restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨restChildren', restChildrenEq', _someEq⟩ :=
        optionBindEqSome restEq
      obtain ⟨childTerm, childEq⟩ :=
        rule.interpretTemplate?_definedTransfer elimPayload allFire
          cellsRelated (depth + 2) childTemplate childEq'
      obtain ⟨restChildren, restChildrenEq⟩ :=
        rule.interpretBuiltChildren?_definedTransfer elimPayload allFire
          cellsRelated depth restShifts restTemplates restChildrenEq'
      refine ⟨.childCons childTerm restChildren, ?_⟩
      rw [childEq, optionSomeBindMonadic, restChildrenEq,
        optionSomeBindMonadic]
  | _, (_ + 3) :: _, .spineCons _ _, _, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted
      injection interpreted

/-- Replacements companion: the reassembly fold's success transfers
backward across any same-typed reassembly spine. -/
theorem IotaRuleDesc.interpretReplacements?_definedTransfer
    (rule : IotaRuleDesc) {etaTable : List EtaRuleDesc}
    {scope : Nat} (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (allFire : rule.scrutineesFire spine rule.scrutinees = true)
    (cellsRelated : ScrutineeCellsEtaRelated rule etaTable spine spine') :
    (depth : Nat) → (replacements : SpineReplacements) →
    (reassemblySpine' :
      RawTermChildren rule.elimGenerator.binderShifts (scope + depth)) →
    {replacedSpine' :
      RawTermChildren rule.elimGenerator.binderShifts (scope + depth)} →
    rule.interpretReplacements? elimPayload spine' depth replacements
        reassemblySpine'
      = some replacedSpine' →
    (reassemblySpine :
      RawTermChildren rule.elimGenerator.binderShifts (scope + depth)) →
    ∃ replacedSpine,
      rule.interpretReplacements? elimPayload spine depth replacements
          reassemblySpine
        = some replacedSpine
  | depth, .replaceNil, _, _, _interpreted, reassemblySpine =>
      ⟨reassemblySpine, rfl⟩
  | depth, .replaceCons slot replacementTemplate restReplacements,
      reassemblySpine', replacedSpine', interpreted, reassemblySpine => by
      dsimp only [IotaRuleDesc.interpretReplacements?] at interpreted ⊢
      obtain ⟨replacement', replacementEq', restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨replacedOnce', replaceAtEq', restEq2⟩ :=
        optionBindEqSome restEq
      obtain ⟨replacement, replacementEq⟩ :=
        rule.interpretTemplate?_definedTransfer elimPayload allFire
          cellsRelated depth replacementTemplate replacementEq'
      obtain ⟨replacedOnce, replaceAtEq⟩ :=
        replaceChildAt?_equiDefined reassemblySpine' reassemblySpine slot
          replaceAtEq' replacement
      obtain ⟨replacedSpine, restRelatedEq⟩ :=
        rule.interpretReplacements?_definedTransfer elimPayload allFire
          cellsRelated depth restReplacements replacedOnce' restEq2
          replacedOnce
      refine ⟨replacedSpine, ?_⟩
      rw [replacementEq, optionSomeBindMonadic, replaceAtEq,
        optionSomeBindMonadic]
      exact restRelatedEq

end

/-- Row-level backward definedness: a successful reduct interpretation
on the related spine yields one on the source spine. -/
theorem IotaRuleDesc.interpretTarget?_definedTransfer
    (rule : IotaRuleDesc) {etaTable : List EtaRuleDesc}
    {scope : Nat} (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (allFire : rule.scrutineesFire spine rule.scrutinees = true)
    (cellsRelated : ScrutineeCellsEtaRelated rule etaTable spine spine')
    {result' : RawTerm scope}
    (interpreted :
      rule.interpretTarget? elimPayload spine' = some result') :
    ∃ result, rule.interpretTarget? elimPayload spine = some result :=
  rule.interpretTemplate?_definedTransfer elimPayload allFire
    cellsRelated 0 rule.target interpreted

/-- ★ **Backward firing**: a row fired on the related spine fires on
the source spine too (the source pattern match supplied per-case), with
an eta-star from the source reduct to the related reduct — the
definedness transfer composed with the forward stability. -/
theorem IotaRuleDesc.firesOn?_etaReflected (rule : IotaRuleDesc)
    {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ etaRule, etaRule ∈ etaTable →
      etaRule.IsScopeSafe)
    {scope : Nat} (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spineRelated : EtaChildrenPointwiseStar etaTable spine spine')
    (allFire : rule.scrutineesFire spine rule.scrutinees = true)
    (cellsRelated : ScrutineeCellsEtaRelated rule etaTable spine spine')
    {reduct' : RawTerm scope}
    (fires' : rule.firesOn? elimPayload spine' = some reduct') :
    ∃ reduct, rule.firesOn? elimPayload spine = some reduct
      ∧ StepEtaOverTableStar etaTable reduct reduct' := by
  have targetFires := rule.firesOn?_some_scrutineesFire fires'
  have interpreted' : rule.interpretTarget? elimPayload spine'
      = some reduct' := by
    dsimp only [IotaRuleDesc.firesOn?] at fires'
    rw [if_pos targetFires] at fires'
    exact fires'
  obtain ⟨reduct, interpreted⟩ :=
    rule.interpretTarget?_definedTransfer elimPayload allFire
      cellsRelated interpreted'
  obtain ⟨reductForward, interpretedForward, reductStar⟩ :=
    rule.interpretTarget?_etaStable rowsAreScopeSafe elimPayload
      spineRelated allFire cellsRelated interpreted
  have reductsAgree : reductForward = reduct' :=
    Option.some.inj (interpretedForward.symm.trans interpreted')
  subst reductsAgree
  refine ⟨reduct, ?_, reductStar⟩
  dsimp only [IotaRuleDesc.firesOn?]
  rw [if_pos allFire]
  exact interpreted

end FX1Poly.Core

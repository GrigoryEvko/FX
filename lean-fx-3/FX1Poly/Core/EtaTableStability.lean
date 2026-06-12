import FX1Poly.Core.EtaStabilitySubstrate

/-! # EtaTableStability — ETA-T5 increment 4.3b: the ONE eta-stability
induction over the template interpreter

THE generic eta-stability theorem: when an eliminator spine relates
pointwise by eta star (and the row's pattern matches the source, and
the scrutinee cells relate head-and-payload-preservingly — the
SUPPLIED hypothesis), the template interpreter still succeeds on the
related spine, and the two interpretations relate by ETA STAR — the
star absorbs the copy fan-out of duplicating templates.

This is the eta twin of `TableParallelStability`, proved by the same
ONE mutual induction over `ReductTemplate` / `ReductTemplateSpine` /
`SpineReplacements`:

  * spine and scrutinee reads relate by the substrate's lookup bricks;
  * `weakenBy` / `weakenBodyUnder…By` transport stars by the renaming
    closure;
  * `subst0` / `substPair` nodes glue with the star diagonals
    (argument fan-out + per-step substitution closure);
  * `builtGen` and `reassembledReplacing` rebuild by congruence
    (`congLift` of the sequentialized pointwise-star).

The firing-level corollary takes the TARGET-side pattern match as a
hypothesis: eta steps at scrutinee slots can change heads (the
duality), so refiring is the consumer's per-case obligation, never a
rigidity corollary.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaTableStability.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation (RawRenaming)

/-! ## Body-weakening transports and the full pair diagonal -/

/-- Stars transport through `weakenBodyUnderOneBinderBy`. -/
theorem StepEtaOverTableStar.weakenBodyUnderOneBinderBy
    {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    {scope : Nat} :
    (depth : Nat) → {body body' : RawTerm (scope + 1)} →
    StepEtaOverTableStar etaTable body body' →
    StepEtaOverTableStar etaTable
      (RawTerm.weakenBodyUnderOneBinderBy depth body)
      (RawTerm.weakenBodyUnderOneBinderBy depth body')
  | 0, _, _, bodyStar => bodyStar
  | depth + 1, _, _, bodyStar =>
      StepEtaOverTableStar.rename rowsAreScopeSafe
        (RawRenaming.lift RawRenaming.weaken)
        (StepEtaOverTableStar.weakenBodyUnderOneBinderBy rowsAreScopeSafe
          depth bodyStar)

/-- Stars transport through `weakenBodyUnderTwoBindersBy`. -/
theorem StepEtaOverTableStar.weakenBodyUnderTwoBindersBy
    {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    {scope : Nat} :
    (depth : Nat) → {body body' : RawTerm (scope + 2)} →
    StepEtaOverTableStar etaTable body body' →
    StepEtaOverTableStar etaTable
      (RawTerm.weakenBodyUnderTwoBindersBy depth body)
      (RawTerm.weakenBodyUnderTwoBindersBy depth body')
  | 0, _, _, bodyStar => bodyStar
  | depth + 1, _, _, bodyStar =>
      StepEtaOverTableStar.rename rowsAreScopeSafe
        (RawRenaming.lift (RawRenaming.lift RawRenaming.weaken))
        (StepEtaOverTableStar.weakenBodyUnderTwoBindersBy
          rowsAreScopeSafe depth bodyStar)

/-- **The full two-binder diagonal**: body stars and argument stars
glue into one star on the pair substitution. -/
theorem StepEtaOverTableStar.substPair_diagonal
    {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ rule, rule ∈ etaTable → rule.IsScopeSafe)
    {scope : Nat} {body body' : RawTerm (scope + 2)}
    {innerArg innerArg' outerArg outerArg' : RawTerm scope}
    (bodyStar : StepEtaOverTableStar etaTable body body')
    (innerStar : StepEtaOverTableStar etaTable innerArg innerArg')
    (outerStar : StepEtaOverTableStar etaTable outerArg outerArg') :
    StepEtaOverTableStar etaTable
      (RawTerm.substPair body innerArg outerArg)
      (RawTerm.substPair body' innerArg' outerArg') := by
  refine StepEtaOverTableStar.concat
    (StepEtaOverTableStar.substPair_argDiagonal rowsAreScopeSafe body
      innerStar outerStar) ?_
  induction bodyStar with
  | refl => exact .refl _
  | head firstStep _restStar ih =>
      exact .head
        (StepEtaOverTable.subst rowsAreScopeSafe
          (RawTermSubst.pair innerArg' outerArg') firstStep) ih

/-! ## The mutual stability induction -/

mutual

/-- ★ **The generic interpreter eta-stability theorem**: a successful
interpretation transports to the pointwise-star-related spine with an
eta-star-related result.  ONE induction for every rule, every depth,
every future row — conditional on the rows' scope-safety (the eta
equivariance engines), the source pattern match, and the SUPPLIED
scrutinee-cell hypothesis. -/
theorem IotaRuleDesc.interpretTemplate?_etaStable (rule : IotaRuleDesc)
    {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ etaRule, etaRule ∈ etaTable →
      etaRule.IsScopeSafe)
    {scope : Nat} (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spineRelated : EtaChildrenPointwiseStar etaTable spine spine')
    (allFire : rule.scrutineesFire spine rule.scrutinees = true)
    (cellsRelated : ScrutineeCellsEtaRelated rule etaTable spine spine') :
    (depth : Nat) → (template : ReductTemplate) →
    {result : RawTerm (scope + depth)} →
    rule.interpretTemplate? elimPayload spine depth template = some result →
    ∃ result',
      rule.interpretTemplate? elimPayload spine' depth template
        = some result'
      ∧ StepEtaOverTableStar etaTable result result'
  | depth, .boundVarAt binderIndex, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      by_cases isBound : binderIndex < depth
      · rw [dif_pos isBound] at interpreted ⊢
        obtain rfl := Option.some.inj interpreted
        exact ⟨_, rfl, .refl _⟩
      · rw [dif_neg isBound] at interpreted
        injection interpreted
  | depth, .spineChildAt slot, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨spineChild, lookupEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨childTerm, projEq, someEq⟩ := optionBindEqSome restEq
      obtain rfl := Option.some.inj someEq
      have composedLookup :
          (scopedChildAt? spine.toScopedChildren slot).bind
              ScopedChild.atShiftZero?
            = some childTerm := by
        rw [lookupEq, optionSomeBindExplicit]
        exact projEq
      obtain ⟨childTerm', composedLookupRelated, childStar⟩ :=
        spineRelated.lookupAtShiftZeroRelated slot composedLookup
      obtain ⟨spineChild', lookupRelatedEq, projRelatedEq⟩ :=
        optionBindEqSome composedLookupRelated
      refine ⟨RawTerm.weakenBy depth childTerm', ?_, ?_⟩
      · rw [lookupRelatedEq, optionSomeBindMonadic, projRelatedEq,
          optionSomeBindMonadic]
      · exact StepEtaOverTableStar.weakenByLift rowsAreScopeSafe depth
          childStar
  | depth, .scrutineeChildAt scrutineeIndex slot, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨childrenView, childrenEq, restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨scrutineeChild, childEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨childTerm, projEq, someEq⟩ := optionBindEqSome restEq2
      obtain rfl := Option.some.inj someEq
      dsimp only [IotaRuleDesc.scrutineeChildrenAt?] at childrenEq ⊢
      obtain ⟨scrutineeTerm, termEq, viewEq⟩ := optionMapEqSome childrenEq
      obtain ⟨spec, matchedPayload, matchedChildren, matchedChildren',
          _specEq, scrutineeIsCell, termRelatedEq, matchedChildrenRel⟩ :=
        rule.scrutineeCellExtraction_etaRelated allFire cellsRelated
          scrutineeIndex termEq
      subst scrutineeIsCell
      have composedLookup :
          (scopedChildAt? matchedChildren.toScopedChildren slot).bind
              ScopedChild.atShiftZero?
            = some childTerm := by
        rw [show matchedChildren.toScopedChildren = childrenView
            from viewEq, childEq, optionSomeBindExplicit]
        exact projEq
      obtain ⟨childTerm', composedLookupRelated, childStar⟩ :=
        matchedChildrenRel.lookupAtShiftZeroRelated slot composedLookup
      obtain ⟨scrutineeChild', lookupRelatedEq, projRelatedEq⟩ :=
        optionBindEqSome composedLookupRelated
      refine ⟨RawTerm.weakenBy depth childTerm', ?_, ?_⟩
      · rw [termRelatedEq, optionSomeMap, optionSomeBindMonadic]
        show ((scopedChildAt? matchedChildren'.toScopedChildren slot)
            >>= fun scrutineeChild =>
              scrutineeChild.atShiftZero? >>= fun innerChildTerm =>
                some (RawTerm.weakenBy depth innerChildTerm))
          = some (RawTerm.weakenBy depth childTerm')
        rw [lookupRelatedEq, optionSomeBindMonadic, projRelatedEq,
          optionSomeBindMonadic]
      · exact StepEtaOverTableStar.weakenByLift rowsAreScopeSafe depth
          childStar
  | depth, .theScrutineeAt scrutineeIndex, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨scrutineeTerm, termEq, someEq⟩ := optionBindEqSome interpreted
      obtain rfl := Option.some.inj someEq
      obtain ⟨scrutineeTerm', termRelatedEq, scrutineeStar⟩ :=
        rule.scrutineeTermAt?_etaRelated spineRelated scrutineeIndex
          termEq
      refine ⟨RawTerm.weakenBy depth scrutineeTerm', ?_, ?_⟩
      · rw [termRelatedEq, optionSomeBindMonadic]
      · exact StepEtaOverTableStar.weakenByLift rowsAreScopeSafe depth
          scrutineeStar
  | depth, .motiveInstantiatedWith argTemplate, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨motiveSlot, slotEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨argTerm, argEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨motiveChild, lookupEq, restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨motiveBody, projEq, someEq⟩ := optionBindEqSome restEq3
      obtain rfl := Option.some.inj someEq
      obtain ⟨argTerm', argRelatedEq, argStar⟩ :=
        rule.interpretTemplate?_etaStable rowsAreScopeSafe elimPayload
          spineRelated allFire cellsRelated depth argTemplate argEq
      have composedLookup :
          (scopedChildAt? spine.toScopedChildren motiveSlot).bind
              ScopedChild.atShiftOne?
            = some motiveBody := by
        rw [lookupEq, optionSomeBindExplicit]
        exact projEq
      obtain ⟨motiveBody', composedLookupRelated, bodyStar⟩ :=
        spineRelated.lookupAtShiftOneRelated motiveSlot composedLookup
      obtain ⟨motiveChild', lookupRelatedEq, projRelatedEq⟩ :=
        optionBindEqSome composedLookupRelated
      refine ⟨RawTerm.subst0
        (RawTerm.weakenBodyUnderOneBinderBy depth motiveBody') argTerm',
        ?_, ?_⟩
      · rw [slotEq, optionSomeBindMonadic, argRelatedEq,
          optionSomeBindMonadic, lookupRelatedEq, optionSomeBindMonadic,
          projRelatedEq, optionSomeBindMonadic]
      · exact StepEtaOverTableStar.subst0_diagonal rowsAreScopeSafe
          (StepEtaOverTableStar.weakenBodyUnderOneBinderBy
            rowsAreScopeSafe depth bodyStar)
          argStar
  | depth, .motiveInstantiatedWithPair innerTemplate outerTemplate,
      result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨motiveSlot, slotEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨innerTerm, innerEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨outerTerm, outerEq, restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨motiveChild, lookupEq, restEq4⟩ := optionBindEqSome restEq3
      obtain ⟨motiveBody, projEq, someEq⟩ := optionBindEqSome restEq4
      obtain rfl := Option.some.inj someEq
      obtain ⟨innerTerm', innerRelatedEq, innerStar⟩ :=
        rule.interpretTemplate?_etaStable rowsAreScopeSafe elimPayload
          spineRelated allFire cellsRelated depth innerTemplate innerEq
      obtain ⟨outerTerm', outerRelatedEq, outerStar⟩ :=
        rule.interpretTemplate?_etaStable rowsAreScopeSafe elimPayload
          spineRelated allFire cellsRelated depth outerTemplate outerEq
      have composedLookup :
          (scopedChildAt? spine.toScopedChildren motiveSlot).bind
              ScopedChild.atShiftTwo?
            = some motiveBody := by
        rw [lookupEq, optionSomeBindExplicit]
        exact projEq
      obtain ⟨motiveBody', composedLookupRelated, bodyStar⟩ :=
        spineRelated.lookupAtShiftTwoRelated motiveSlot composedLookup
      obtain ⟨motiveChild', lookupRelatedEq, projRelatedEq⟩ :=
        optionBindEqSome composedLookupRelated
      refine ⟨RawTerm.substPair
        (RawTerm.weakenBodyUnderTwoBindersBy depth motiveBody')
        innerTerm' outerTerm', ?_, ?_⟩
      · rw [slotEq, optionSomeBindMonadic, innerRelatedEq,
          optionSomeBindMonadic, outerRelatedEq, optionSomeBindMonadic,
          lookupRelatedEq, optionSomeBindMonadic, projRelatedEq,
          optionSomeBindMonadic]
      · exact StepEtaOverTableStar.substPair_diagonal rowsAreScopeSafe
          (StepEtaOverTableStar.weakenBodyUnderTwoBindersBy
            rowsAreScopeSafe depth bodyStar)
          innerStar outerStar
  | depth, .builtGen builtHead payloadSource childTemplates, result,
      interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨builtPayload, payloadEq, restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨builtChildren, childrenEq, someEq⟩ := optionBindEqSome restEq
      obtain rfl := Option.some.inj someEq
      have payloadRelatedEq :=
        rule.resolvePayloadSource?_etaPreserved allFire cellsRelated
          depth payloadSource payloadEq
      obtain ⟨builtChildren', childrenRelatedEq, builtChildrenRel⟩ :=
        rule.interpretBuiltChildren?_etaStable rowsAreScopeSafe
          elimPayload spineRelated allFire cellsRelated
          depth builtHead.binderShifts childTemplates childrenEq
      refine ⟨.mkGen builtHead builtPayload builtChildren', ?_, ?_⟩
      · rw [payloadRelatedEq, optionSomeBindMonadic, childrenRelatedEq,
          optionSomeBindMonadic]
      · exact StepEtaOverTableStar.congLift builtHead builtPayload
          builtChildrenRel.toSequentialStar
  | depth, .reassembledReplacing replacements, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨payloadAtDepth, payloadEq, restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨replacedSpine, replacedEq, someEq⟩ := optionBindEqSome restEq
      obtain rfl := Option.some.inj someEq
      obtain ⟨replacedSpine', replacedRelatedEq, replacedRel⟩ :=
        rule.interpretReplacements?_etaStable rowsAreScopeSafe
          elimPayload spineRelated allFire cellsRelated
          depth replacements
          (EtaChildrenPointwiseStar.weakenSpineBy rowsAreScopeSafe depth
            spineRelated)
          replacedEq
      refine ⟨.mkGen rule.elimGenerator payloadAtDepth replacedSpine',
        ?_, ?_⟩
      · rw [payloadEq, optionSomeBindMonadic, replacedRelatedEq,
          optionSomeBindMonadic]
      · exact StepEtaOverTableStar.congLift rule.elimGenerator
          payloadAtDepth replacedRel.toSequentialStar
  | depth, .substOneIntoSpineChild bodySlot argTemplate, result,
      interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨argTerm, argEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨bodyChild, lookupEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨bodyTerm, projEq, someEq⟩ := optionBindEqSome restEq2
      obtain rfl := Option.some.inj someEq
      obtain ⟨argTerm', argRelatedEq, argStar⟩ :=
        rule.interpretTemplate?_etaStable rowsAreScopeSafe elimPayload
          spineRelated allFire cellsRelated depth argTemplate argEq
      have composedLookup :
          (scopedChildAt? spine.toScopedChildren bodySlot).bind
              ScopedChild.atShiftOne?
            = some bodyTerm := by
        rw [lookupEq, optionSomeBindExplicit]
        exact projEq
      obtain ⟨bodyTerm', composedLookupRelated, bodyStar⟩ :=
        spineRelated.lookupAtShiftOneRelated bodySlot composedLookup
      obtain ⟨bodyChild', lookupRelatedEq, projRelatedEq⟩ :=
        optionBindEqSome composedLookupRelated
      refine ⟨RawTerm.subst0
        (RawTerm.weakenBodyUnderOneBinderBy depth bodyTerm') argTerm',
        ?_, ?_⟩
      · rw [argRelatedEq, optionSomeBindMonadic, lookupRelatedEq,
          optionSomeBindMonadic, projRelatedEq, optionSomeBindMonadic]
      · exact StepEtaOverTableStar.subst0_diagonal rowsAreScopeSafe
          (StepEtaOverTableStar.weakenBodyUnderOneBinderBy
            rowsAreScopeSafe depth bodyStar)
          argStar
  | depth, .substOneIntoScrutineeChild scrutineeIndex bodySlot argTemplate,
      result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨argTerm, argEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨childrenView, childrenEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨bodyChild, childEq, restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨bodyTerm, projEq, someEq⟩ := optionBindEqSome restEq3
      obtain rfl := Option.some.inj someEq
      obtain ⟨argTerm', argRelatedEq, argStar⟩ :=
        rule.interpretTemplate?_etaStable rowsAreScopeSafe elimPayload
          spineRelated allFire cellsRelated depth argTemplate argEq
      dsimp only [IotaRuleDesc.scrutineeChildrenAt?] at childrenEq ⊢
      obtain ⟨scrutineeTerm, termEq, viewEq⟩ := optionMapEqSome childrenEq
      obtain ⟨spec, matchedPayload, matchedChildren, matchedChildren',
          _specEq, scrutineeIsCell, termRelatedEq, matchedChildrenRel⟩ :=
        rule.scrutineeCellExtraction_etaRelated allFire cellsRelated
          scrutineeIndex termEq
      subst scrutineeIsCell
      have composedLookup :
          (scopedChildAt? matchedChildren.toScopedChildren bodySlot).bind
              ScopedChild.atShiftOne?
            = some bodyTerm := by
        rw [show matchedChildren.toScopedChildren = childrenView
            from viewEq, childEq, optionSomeBindExplicit]
        exact projEq
      obtain ⟨bodyTerm', composedLookupRelated, bodyStar⟩ :=
        matchedChildrenRel.lookupAtShiftOneRelated bodySlot composedLookup
      obtain ⟨bodyChild', lookupRelatedEq, projRelatedEq⟩ :=
        optionBindEqSome composedLookupRelated
      refine ⟨RawTerm.subst0
        (RawTerm.weakenBodyUnderOneBinderBy depth bodyTerm') argTerm',
        ?_, ?_⟩
      · rw [argRelatedEq, optionSomeBindMonadic, termRelatedEq,
          optionSomeMap, optionSomeBindMonadic]
        show ((scopedChildAt? matchedChildren'.toScopedChildren bodySlot)
            >>= fun bodyChild =>
              bodyChild.atShiftOne? >>= fun innerBodyTerm =>
                some (RawTerm.subst0
                  (RawTerm.weakenBodyUnderOneBinderBy depth innerBodyTerm)
                  argTerm'))
          = some (RawTerm.subst0
              (RawTerm.weakenBodyUnderOneBinderBy depth bodyTerm')
              argTerm')
        rw [lookupRelatedEq, optionSomeBindMonadic, projRelatedEq,
          optionSomeBindMonadic]
      · exact StepEtaOverTableStar.subst0_diagonal rowsAreScopeSafe
          (StepEtaOverTableStar.weakenBodyUnderOneBinderBy
            rowsAreScopeSafe depth bodyStar)
          argStar
  | depth, .substPairIntoSpineChild bodySlot innerTemplate outerTemplate,
      result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨innerTerm, innerEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨outerTerm, outerEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨bodyChild, lookupEq, restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨bodyTerm, projEq, someEq⟩ := optionBindEqSome restEq3
      obtain rfl := Option.some.inj someEq
      obtain ⟨innerTerm', innerRelatedEq, innerStar⟩ :=
        rule.interpretTemplate?_etaStable rowsAreScopeSafe elimPayload
          spineRelated allFire cellsRelated depth innerTemplate innerEq
      obtain ⟨outerTerm', outerRelatedEq, outerStar⟩ :=
        rule.interpretTemplate?_etaStable rowsAreScopeSafe elimPayload
          spineRelated allFire cellsRelated depth outerTemplate outerEq
      have composedLookup :
          (scopedChildAt? spine.toScopedChildren bodySlot).bind
              ScopedChild.atShiftTwo?
            = some bodyTerm := by
        rw [lookupEq, optionSomeBindExplicit]
        exact projEq
      obtain ⟨bodyTerm', composedLookupRelated, bodyStar⟩ :=
        spineRelated.lookupAtShiftTwoRelated bodySlot composedLookup
      obtain ⟨bodyChild', lookupRelatedEq, projRelatedEq⟩ :=
        optionBindEqSome composedLookupRelated
      refine ⟨RawTerm.substPair
        (RawTerm.weakenBodyUnderTwoBindersBy depth bodyTerm')
        innerTerm' outerTerm', ?_, ?_⟩
      · rw [innerRelatedEq, optionSomeBindMonadic, outerRelatedEq,
          optionSomeBindMonadic, lookupRelatedEq, optionSomeBindMonadic,
          projRelatedEq, optionSomeBindMonadic]
      · exact StepEtaOverTableStar.substPair_diagonal rowsAreScopeSafe
          (StepEtaOverTableStar.weakenBodyUnderTwoBindersBy
            rowsAreScopeSafe depth bodyStar)
          innerStar outerStar
  | depth, .substPairIntoScrutineeChild scrutineeIndex bodySlot
      innerTemplate outerTemplate, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨innerTerm, innerEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨outerTerm, outerEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨childrenView, childrenEq, restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨bodyChild, childEq, restEq4⟩ := optionBindEqSome restEq3
      obtain ⟨bodyTerm, projEq, someEq⟩ := optionBindEqSome restEq4
      obtain rfl := Option.some.inj someEq
      obtain ⟨innerTerm', innerRelatedEq, innerStar⟩ :=
        rule.interpretTemplate?_etaStable rowsAreScopeSafe elimPayload
          spineRelated allFire cellsRelated depth innerTemplate innerEq
      obtain ⟨outerTerm', outerRelatedEq, outerStar⟩ :=
        rule.interpretTemplate?_etaStable rowsAreScopeSafe elimPayload
          spineRelated allFire cellsRelated depth outerTemplate outerEq
      dsimp only [IotaRuleDesc.scrutineeChildrenAt?] at childrenEq ⊢
      obtain ⟨scrutineeTerm, termEq, viewEq⟩ := optionMapEqSome childrenEq
      obtain ⟨spec, matchedPayload, matchedChildren, matchedChildren',
          _specEq, scrutineeIsCell, termRelatedEq, matchedChildrenRel⟩ :=
        rule.scrutineeCellExtraction_etaRelated allFire cellsRelated
          scrutineeIndex termEq
      subst scrutineeIsCell
      have composedLookup :
          (scopedChildAt? matchedChildren.toScopedChildren bodySlot).bind
              ScopedChild.atShiftTwo?
            = some bodyTerm := by
        rw [show matchedChildren.toScopedChildren = childrenView
            from viewEq, childEq, optionSomeBindExplicit]
        exact projEq
      obtain ⟨bodyTerm', composedLookupRelated, bodyStar⟩ :=
        matchedChildrenRel.lookupAtShiftTwoRelated bodySlot composedLookup
      obtain ⟨bodyChild', lookupRelatedEq, projRelatedEq⟩ :=
        optionBindEqSome composedLookupRelated
      refine ⟨RawTerm.substPair
        (RawTerm.weakenBodyUnderTwoBindersBy depth bodyTerm')
        innerTerm' outerTerm', ?_, ?_⟩
      · rw [innerRelatedEq, optionSomeBindMonadic, outerRelatedEq,
          optionSomeBindMonadic, termRelatedEq, optionSomeMap,
          optionSomeBindMonadic]
        show ((scopedChildAt? matchedChildren'.toScopedChildren bodySlot)
            >>= fun bodyChild =>
              bodyChild.atShiftTwo? >>= fun innerBodyTerm =>
                some (RawTerm.substPair
                  (RawTerm.weakenBodyUnderTwoBindersBy depth innerBodyTerm)
                  innerTerm' outerTerm'))
          = some (RawTerm.substPair
              (RawTerm.weakenBodyUnderTwoBindersBy depth bodyTerm')
              innerTerm' outerTerm')
        rw [lookupRelatedEq, optionSomeBindMonadic, projRelatedEq,
          optionSomeBindMonadic]
      · exact StepEtaOverTableStar.substPair_diagonal rowsAreScopeSafe
          (StepEtaOverTableStar.weakenBodyUnderTwoBindersBy
            rowsAreScopeSafe depth bodyStar)
          innerStar outerStar

/-- Spine companion: `builtGen` children assembly transports — each
shift arm interprets at its own depth and the assembled spines relate
pointwise-by-star. -/
theorem IotaRuleDesc.interpretBuiltChildren?_etaStable
    (rule : IotaRuleDesc) {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ etaRule, etaRule ∈ etaTable →
      etaRule.IsScopeSafe)
    {scope : Nat} (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spineRelated : EtaChildrenPointwiseStar etaTable spine spine')
    (allFire : rule.scrutineesFire spine rule.scrutinees = true)
    (cellsRelated : ScrutineeCellsEtaRelated rule etaTable spine spine') :
    (depth : Nat) → (childShifts : List Nat) →
    (childTemplates : ReductTemplateSpine) →
    {builtChildren : RawTermChildren childShifts (scope + depth)} →
    rule.interpretBuiltChildren? elimPayload spine depth childShifts
        childTemplates
      = some builtChildren →
    ∃ builtChildren',
      rule.interpretBuiltChildren? elimPayload spine' depth childShifts
          childTemplates
        = some builtChildren'
      ∧ EtaChildrenPointwiseStar etaTable builtChildren builtChildren'
  | depth, [], .spineNil, builtChildren, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted ⊢
      obtain rfl := Option.some.inj interpreted
      exact ⟨.childNil, rfl, .nil⟩
  | _, [], .spineCons _ _, _, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted
      injection interpreted
  | _, _ :: _, .spineNil, _, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted
      injection interpreted
  | depth, 0 :: restShifts, .spineCons childTemplate restTemplates,
      builtChildren, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted ⊢
      obtain ⟨childTerm, childEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨restChildren, restChildrenEq, someEq⟩ :=
        optionBindEqSome restEq
      obtain rfl := Option.some.inj someEq
      obtain ⟨childTerm', childRelatedEq, childStar⟩ :=
        rule.interpretTemplate?_etaStable rowsAreScopeSafe elimPayload
          spineRelated allFire cellsRelated depth childTemplate childEq
      obtain ⟨restChildren', restRelatedEq, restRel⟩ :=
        rule.interpretBuiltChildren?_etaStable rowsAreScopeSafe
          elimPayload spineRelated allFire cellsRelated
          depth restShifts restTemplates restChildrenEq
      refine ⟨.childCons childTerm' restChildren', ?_, ?_⟩
      · rw [childRelatedEq, optionSomeBindMonadic, restRelatedEq,
          optionSomeBindMonadic]
      · refine EtaChildrenPointwiseStar.cons ?_ restRel
        exact childStar
  | depth, 1 :: restShifts, .spineCons childTemplate restTemplates,
      builtChildren, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted ⊢
      obtain ⟨childTerm, childEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨restChildren, restChildrenEq, someEq⟩ :=
        optionBindEqSome restEq
      obtain rfl := Option.some.inj someEq
      obtain ⟨childTerm', childRelatedEq, childStar⟩ :=
        rule.interpretTemplate?_etaStable rowsAreScopeSafe elimPayload
          spineRelated allFire cellsRelated (depth + 1) childTemplate
          childEq
      obtain ⟨restChildren', restRelatedEq, restRel⟩ :=
        rule.interpretBuiltChildren?_etaStable rowsAreScopeSafe
          elimPayload spineRelated allFire cellsRelated
          depth restShifts restTemplates restChildrenEq
      refine ⟨.childCons childTerm' restChildren', ?_, ?_⟩
      · rw [childRelatedEq, optionSomeBindMonadic, restRelatedEq,
          optionSomeBindMonadic]
      · refine EtaChildrenPointwiseStar.cons ?_ restRel
        exact childStar
  | depth, 2 :: restShifts, .spineCons childTemplate restTemplates,
      builtChildren, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted ⊢
      obtain ⟨childTerm, childEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨restChildren, restChildrenEq, someEq⟩ :=
        optionBindEqSome restEq
      obtain rfl := Option.some.inj someEq
      obtain ⟨childTerm', childRelatedEq, childStar⟩ :=
        rule.interpretTemplate?_etaStable rowsAreScopeSafe elimPayload
          spineRelated allFire cellsRelated (depth + 2) childTemplate
          childEq
      obtain ⟨restChildren', restRelatedEq, restRel⟩ :=
        rule.interpretBuiltChildren?_etaStable rowsAreScopeSafe
          elimPayload spineRelated allFire cellsRelated
          depth restShifts restTemplates restChildrenEq
      refine ⟨.childCons childTerm' restChildren', ?_, ?_⟩
      · rw [childRelatedEq, optionSomeBindMonadic, restRelatedEq,
          optionSomeBindMonadic]
      · refine EtaChildrenPointwiseStar.cons ?_ restRel
        exact childStar
  | _, (_ + 3) :: _, .spineCons _ _, _, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted
      injection interpreted

/-- Replacements companion: the reassembly fold transports across
pointwise-star-related reassembly spines. -/
theorem IotaRuleDesc.interpretReplacements?_etaStable
    (rule : IotaRuleDesc) {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ etaRule, etaRule ∈ etaTable →
      etaRule.IsScopeSafe)
    {scope : Nat} (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spineRelated : EtaChildrenPointwiseStar etaTable spine spine')
    (allFire : rule.scrutineesFire spine rule.scrutinees = true)
    (cellsRelated : ScrutineeCellsEtaRelated rule etaTable spine spine') :
    (depth : Nat) → (replacements : SpineReplacements) →
    {reassemblySpine reassemblySpine' :
      RawTermChildren rule.elimGenerator.binderShifts (scope + depth)} →
    EtaChildrenPointwiseStar etaTable reassemblySpine reassemblySpine' →
    {replacedSpine :
      RawTermChildren rule.elimGenerator.binderShifts (scope + depth)} →
    rule.interpretReplacements? elimPayload spine depth replacements
        reassemblySpine
      = some replacedSpine →
    ∃ replacedSpine',
      rule.interpretReplacements? elimPayload spine' depth replacements
          reassemblySpine'
        = some replacedSpine'
      ∧ EtaChildrenPointwiseStar etaTable replacedSpine replacedSpine'
  | depth, .replaceNil, _, _, reassemblyRel, replacedSpine,
      interpreted => by
      dsimp only [IotaRuleDesc.interpretReplacements?] at interpreted ⊢
      obtain rfl := Option.some.inj interpreted
      exact ⟨_, rfl, reassemblyRel⟩
  | depth, .replaceCons slot replacementTemplate restReplacements, _, _,
      reassemblyRel, replacedSpine, interpreted => by
      dsimp only [IotaRuleDesc.interpretReplacements?] at interpreted ⊢
      obtain ⟨replacement, replacementEq, restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨replacedOnce, replaceAtEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨replacement', replacementRelatedEq, replacementStar⟩ :=
        rule.interpretTemplate?_etaStable rowsAreScopeSafe elimPayload
          spineRelated allFire cellsRelated depth replacementTemplate
          replacementEq
      obtain ⟨replacedOnce', replaceAtRelatedEq, replacedOnceRel⟩ :=
        RawTermChildren.replaceChildAt?_etaRelated reassemblyRel slot
          replacementStar replaceAtEq
      obtain ⟨replacedSpine', restRelatedEq, replacedSpineRel⟩ :=
        rule.interpretReplacements?_etaStable rowsAreScopeSafe
          elimPayload spineRelated allFire cellsRelated
          depth restReplacements replacedOnceRel restEq2
      refine ⟨replacedSpine', ?_, replacedSpineRel⟩
      rw [replacementRelatedEq, optionSomeBindMonadic, replaceAtRelatedEq,
        optionSomeBindMonadic]
      exact restRelatedEq

end

/-! ## The depth-0 and firing-level corollaries -/

/-- Row-level eta stability: a row's reduct interpretation transports
to a pointwise-star-related spine with an eta-star-related reduct. -/
theorem IotaRuleDesc.interpretTarget?_etaStable (rule : IotaRuleDesc)
    {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ etaRule, etaRule ∈ etaTable →
      etaRule.IsScopeSafe)
    {scope : Nat} (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spineRelated : EtaChildrenPointwiseStar etaTable spine spine')
    (allFire : rule.scrutineesFire spine rule.scrutinees = true)
    (cellsRelated : ScrutineeCellsEtaRelated rule etaTable spine spine')
    {result : RawTerm scope}
    (interpreted : rule.interpretTarget? elimPayload spine = some result) :
    ∃ result', rule.interpretTarget? elimPayload spine' = some result'
      ∧ StepEtaOverTableStar etaTable result result' :=
  rule.interpretTemplate?_etaStable rowsAreScopeSafe elimPayload
    spineRelated allFire cellsRelated 0 rule.target interpreted

/-- ★ **Firing-level eta stability**: a fired row refires on a
pointwise-star-related spine — provided the TARGET-side pattern also
matches (the consumer's per-case obligation; eta can change scrutinee
heads, so this is never a rigidity corollary) — with an
eta-star-related reduct. -/
theorem IotaRuleDesc.firesOn?_etaStable (rule : IotaRuleDesc)
    {etaTable : List EtaRuleDesc}
    (rowsAreScopeSafe : ∀ etaRule, etaRule ∈ etaTable →
      etaRule.IsScopeSafe)
    {scope : Nat} (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spineRelated : EtaChildrenPointwiseStar etaTable spine spine')
    (cellsRelated : ScrutineeCellsEtaRelated rule etaTable spine spine')
    (targetFires : rule.scrutineesFire spine' rule.scrutinees = true)
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct) :
    ∃ reduct', rule.firesOn? elimPayload spine' = some reduct'
      ∧ StepEtaOverTableStar etaTable reduct reduct' := by
  have allFire := rule.firesOn?_some_scrutineesFire fires
  dsimp only [IotaRuleDesc.firesOn?] at fires ⊢
  rw [if_pos allFire] at fires
  rw [if_pos targetFires]
  exact rule.interpretTarget?_etaStable rowsAreScopeSafe elimPayload
    spineRelated allFire cellsRelated fires

end FX1Poly.Core

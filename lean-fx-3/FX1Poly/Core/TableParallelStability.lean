import FX1Poly.Core.TableParallelStabilitySubstrate

/-! # FX1Poly/Core/TableParallelStability — IOTA-T6: the ONE parallel-stability induction

THE generic parallel-stability theorem: when an eliminator spine
reduces POINTWISE in parallel (and the row's pattern matches the
source), the template interpreter still succeeds on the reduced spine,
and the two interpretations are related by ONE parallel step —
`interpretTemplate? spine = some result` transports to
`interpretTemplate? spine' = some result'` with `result ⇒∥ result'`.

This is the table twin of the Takahashi substitution lemma, proved by
ONE mutual induction over `ReductTemplate` / `ReductTemplateSpine` /
`SpineReplacements` — the theorem the triangle's root-vs-cong and
root-vs-root cases both fire with, for every current and future row:

  * spine and scrutinee reads relate by the substrate's lookup bricks
    (the scrutinee's structure survives by head rigidity);
  * `weakenBy` / `weakenBodyUnder…By` transport relations by the
    equivariance depth engines;
  * `subst0` / `substPair` nodes glue with the DIAGONAL substitution
    lemma (`subst0_diagonal` / `substPair_diagonal`);
  * `builtGen` and `reassembledReplacing` rebuild by CONGRUENCE — the
    payload reads are identical across the reduction, so the rebuilt
    cells share payloads and only children move.

Corollaries: `interpretTarget?_parStable` (depth 0) and the packaged
★ `firesOn?_parStable` — a fired row REFIRES on a pointwise-reduced
spine with a parallel-related reduct.

## Zero-axiom verification

Mutual structural induction mirroring the IOTA-T2 equivariance
induction, `dsimp only` arm unfolding, the substrate bricks, and the
equivariance engines.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Gated per declaration in
`FX1PolyAudit/AuditTableParallelStability.lean`. -/

namespace FX1Poly.Core

mutual

/-- ★ **The generic interpreter parallel-stability theorem** (the
some-direction): a successful interpretation transports to the
pointwise-reduced spine with a parallel-related result.  ONE induction
for every rule, every depth, every future row — conditional on the
table's scope-uniformity certificates (the equivariance engines), the
row's scrutinee-head rigidity (the orthogonality certificate), and the
source pattern match. -/
theorem IotaRuleDesc.interpretTemplate?_parStable (rule : IotaRuleDesc)
    {table : List IotaRuleDesc}
    (tableIsUniform : ∀ anyRule, anyRule ∈ table → anyRule.IsScopeUniform)
    (scrutineeHeadsAreRigid : ∀ spec, spec ∈ rule.scrutinees →
      ∀ other, other ∈ table → spec.head ≠ other.elimGenerator)
    {scope : Nat} (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spinePar : ParStepOverTableChildren table spine spine')
    (allFire : rule.scrutineesFire spine rule.scrutinees = true) :
    (depth : Nat) → (template : ReductTemplate) →
    {result : RawTerm (scope + depth)} →
    rule.interpretTemplate? elimPayload spine depth template = some result →
    ∃ result',
      rule.interpretTemplate? elimPayload spine' depth template
        = some result'
      ∧ ParStepOverTable table result result'
  | depth, .boundVarAt binderIndex, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      by_cases isBound : binderIndex < depth
      · rw [dif_pos isBound] at interpreted ⊢
        obtain rfl := Option.some.inj interpreted
        exact ⟨_, rfl, ParStepOverTable.refl _⟩
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
      obtain ⟨childTerm', composedLookupRelated, childPar⟩ :=
        spinePar.lookupAtShiftZeroRelated slot composedLookup
      obtain ⟨spineChild', lookupRelatedEq, projRelatedEq⟩ :=
        optionBindEqSome composedLookupRelated
      refine ⟨RawTerm.weakenBy depth childTerm', ?_, ?_⟩
      · rw [lookupRelatedEq, optionSomeBindMonadic, projRelatedEq,
          optionSomeBindMonadic]
      · exact ParStepOverTable.weakenBy tableIsUniform depth childPar
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
          _specEq, scrutineeIsCell, termRelatedEq, matchedChildrenPar⟩ :=
        rule.scrutineeCellExtraction_parRelated spinePar allFire
          scrutineeHeadsAreRigid scrutineeIndex termEq
      subst scrutineeIsCell
      have composedLookup :
          (scopedChildAt? matchedChildren.toScopedChildren slot).bind
              ScopedChild.atShiftZero?
            = some childTerm := by
        rw [show matchedChildren.toScopedChildren = childrenView
            from viewEq, childEq, optionSomeBindExplicit]
        exact projEq
      obtain ⟨childTerm', composedLookupRelated, childPar⟩ :=
        matchedChildrenPar.lookupAtShiftZeroRelated slot composedLookup
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
      · exact ParStepOverTable.weakenBy tableIsUniform depth childPar
  | depth, .theScrutineeAt scrutineeIndex, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨scrutineeTerm, termEq, someEq⟩ := optionBindEqSome interpreted
      obtain rfl := Option.some.inj someEq
      obtain ⟨scrutineeTerm', termRelatedEq, scrutineePar⟩ :=
        rule.scrutineeTermAt?_parRelated spinePar scrutineeIndex termEq
      refine ⟨RawTerm.weakenBy depth scrutineeTerm', ?_, ?_⟩
      · rw [termRelatedEq, optionSomeBindMonadic]
      · exact ParStepOverTable.weakenBy tableIsUniform depth scrutineePar
  | depth, .motiveInstantiatedWith argTemplate, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨motiveSlot, slotEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨argTerm, argEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨motiveChild, lookupEq, restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨motiveBody, projEq, someEq⟩ := optionBindEqSome restEq3
      obtain rfl := Option.some.inj someEq
      obtain ⟨argTerm', argRelatedEq, argPar⟩ :=
        rule.interpretTemplate?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth argTemplate argEq
      have composedLookup :
          (scopedChildAt? spine.toScopedChildren motiveSlot).bind
              ScopedChild.atShiftOne?
            = some motiveBody := by
        rw [lookupEq, optionSomeBindExplicit]
        exact projEq
      obtain ⟨motiveBody', composedLookupRelated, bodyPar⟩ :=
        spinePar.lookupAtShiftOneRelated motiveSlot composedLookup
      obtain ⟨motiveChild', lookupRelatedEq, projRelatedEq⟩ :=
        optionBindEqSome composedLookupRelated
      refine ⟨RawTerm.subst0
        (RawTerm.weakenBodyUnderOneBinderBy depth motiveBody') argTerm',
        ?_, ?_⟩
      · rw [slotEq, optionSomeBindMonadic, argRelatedEq,
          optionSomeBindMonadic, lookupRelatedEq, optionSomeBindMonadic,
          projRelatedEq, optionSomeBindMonadic]
      · exact ParStepOverTable.subst0_diagonal tableIsUniform
          (ParStepOverTable.weakenBodyUnderOneBinderBy tableIsUniform
            depth bodyPar)
          argPar
  | depth, .motiveInstantiatedWithPair innerTemplate outerTemplate,
      result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨motiveSlot, slotEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨innerTerm, innerEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨outerTerm, outerEq, restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨motiveChild, lookupEq, restEq4⟩ := optionBindEqSome restEq3
      obtain ⟨motiveBody, projEq, someEq⟩ := optionBindEqSome restEq4
      obtain rfl := Option.some.inj someEq
      obtain ⟨innerTerm', innerRelatedEq, innerPar⟩ :=
        rule.interpretTemplate?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth innerTemplate innerEq
      obtain ⟨outerTerm', outerRelatedEq, outerPar⟩ :=
        rule.interpretTemplate?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth outerTemplate outerEq
      have composedLookup :
          (scopedChildAt? spine.toScopedChildren motiveSlot).bind
              ScopedChild.atShiftTwo?
            = some motiveBody := by
        rw [lookupEq, optionSomeBindExplicit]
        exact projEq
      obtain ⟨motiveBody', composedLookupRelated, bodyPar⟩ :=
        spinePar.lookupAtShiftTwoRelated motiveSlot composedLookup
      obtain ⟨motiveChild', lookupRelatedEq, projRelatedEq⟩ :=
        optionBindEqSome composedLookupRelated
      refine ⟨RawTerm.substPair
        (RawTerm.weakenBodyUnderTwoBindersBy depth motiveBody')
        innerTerm' outerTerm', ?_, ?_⟩
      · rw [slotEq, optionSomeBindMonadic, innerRelatedEq,
          optionSomeBindMonadic, outerRelatedEq, optionSomeBindMonadic,
          lookupRelatedEq, optionSomeBindMonadic, projRelatedEq,
          optionSomeBindMonadic]
      · exact ParStepOverTable.substPair_diagonal tableIsUniform
          (ParStepOverTable.weakenBodyUnderTwoBindersBy tableIsUniform
            depth bodyPar)
          innerPar outerPar
  | depth, .builtGen builtHead payloadSource childTemplates, result,
      interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨builtPayload, payloadEq, restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨builtChildren, childrenEq, someEq⟩ := optionBindEqSome restEq
      obtain rfl := Option.some.inj someEq
      have payloadRelatedEq :=
        rule.resolvePayloadSource?_parPreserved spinePar allFire
          scrutineeHeadsAreRigid depth payloadSource payloadEq
      obtain ⟨builtChildren', childrenRelatedEq, builtChildrenPar⟩ :=
        rule.interpretBuiltChildren?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth builtHead.binderShifts childTemplates childrenEq
      refine ⟨.mkGen builtHead builtPayload builtChildren', ?_, ?_⟩
      · rw [payloadRelatedEq, optionSomeBindMonadic, childrenRelatedEq,
          optionSomeBindMonadic]
      · exact ParStepOverTable.cong builtHead builtPayload builtChildrenPar
  | depth, .reassembledReplacing replacements, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨payloadAtDepth, payloadEq, restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨replacedSpine, replacedEq, someEq⟩ := optionBindEqSome restEq
      obtain rfl := Option.some.inj someEq
      obtain ⟨replacedSpine', replacedRelatedEq, replacedPar⟩ :=
        rule.interpretReplacements?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth replacements
          (ParStepOverTableChildren.weakenSpineBy tableIsUniform depth
            spinePar)
          replacedEq
      refine ⟨.mkGen rule.elimGenerator payloadAtDepth replacedSpine',
        ?_, ?_⟩
      · rw [payloadEq, optionSomeBindMonadic, replacedRelatedEq,
          optionSomeBindMonadic]
      · exact ParStepOverTable.cong rule.elimGenerator payloadAtDepth
          replacedPar
  | depth, .substOneIntoSpineChild bodySlot argTemplate, result,
      interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨argTerm, argEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨bodyChild, lookupEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨bodyTerm, projEq, someEq⟩ := optionBindEqSome restEq2
      obtain rfl := Option.some.inj someEq
      obtain ⟨argTerm', argRelatedEq, argPar⟩ :=
        rule.interpretTemplate?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth argTemplate argEq
      have composedLookup :
          (scopedChildAt? spine.toScopedChildren bodySlot).bind
              ScopedChild.atShiftOne?
            = some bodyTerm := by
        rw [lookupEq, optionSomeBindExplicit]
        exact projEq
      obtain ⟨bodyTerm', composedLookupRelated, bodyPar⟩ :=
        spinePar.lookupAtShiftOneRelated bodySlot composedLookup
      obtain ⟨bodyChild', lookupRelatedEq, projRelatedEq⟩ :=
        optionBindEqSome composedLookupRelated
      refine ⟨RawTerm.subst0
        (RawTerm.weakenBodyUnderOneBinderBy depth bodyTerm') argTerm',
        ?_, ?_⟩
      · rw [argRelatedEq, optionSomeBindMonadic, lookupRelatedEq,
          optionSomeBindMonadic, projRelatedEq, optionSomeBindMonadic]
      · exact ParStepOverTable.subst0_diagonal tableIsUniform
          (ParStepOverTable.weakenBodyUnderOneBinderBy tableIsUniform
            depth bodyPar)
          argPar
  | depth, .substOneIntoScrutineeChild scrutineeIndex bodySlot argTemplate,
      result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨argTerm, argEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨childrenView, childrenEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨bodyChild, childEq, restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨bodyTerm, projEq, someEq⟩ := optionBindEqSome restEq3
      obtain rfl := Option.some.inj someEq
      obtain ⟨argTerm', argRelatedEq, argPar⟩ :=
        rule.interpretTemplate?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth argTemplate argEq
      dsimp only [IotaRuleDesc.scrutineeChildrenAt?] at childrenEq ⊢
      obtain ⟨scrutineeTerm, termEq, viewEq⟩ := optionMapEqSome childrenEq
      obtain ⟨spec, matchedPayload, matchedChildren, matchedChildren',
          _specEq, scrutineeIsCell, termRelatedEq, matchedChildrenPar⟩ :=
        rule.scrutineeCellExtraction_parRelated spinePar allFire
          scrutineeHeadsAreRigid scrutineeIndex termEq
      subst scrutineeIsCell
      have composedLookup :
          (scopedChildAt? matchedChildren.toScopedChildren bodySlot).bind
              ScopedChild.atShiftOne?
            = some bodyTerm := by
        rw [show matchedChildren.toScopedChildren = childrenView
            from viewEq, childEq, optionSomeBindExplicit]
        exact projEq
      obtain ⟨bodyTerm', composedLookupRelated, bodyPar⟩ :=
        matchedChildrenPar.lookupAtShiftOneRelated bodySlot composedLookup
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
              (RawTerm.weakenBodyUnderOneBinderBy depth bodyTerm') argTerm')
        rw [lookupRelatedEq, optionSomeBindMonadic, projRelatedEq,
          optionSomeBindMonadic]
      · exact ParStepOverTable.subst0_diagonal tableIsUniform
          (ParStepOverTable.weakenBodyUnderOneBinderBy tableIsUniform
            depth bodyPar)
          argPar
  | depth, .substPairIntoSpineChild bodySlot innerTemplate outerTemplate,
      result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨innerTerm, innerEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨outerTerm, outerEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨bodyChild, lookupEq, restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨bodyTerm, projEq, someEq⟩ := optionBindEqSome restEq3
      obtain rfl := Option.some.inj someEq
      obtain ⟨innerTerm', innerRelatedEq, innerPar⟩ :=
        rule.interpretTemplate?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth innerTemplate innerEq
      obtain ⟨outerTerm', outerRelatedEq, outerPar⟩ :=
        rule.interpretTemplate?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth outerTemplate outerEq
      have composedLookup :
          (scopedChildAt? spine.toScopedChildren bodySlot).bind
              ScopedChild.atShiftTwo?
            = some bodyTerm := by
        rw [lookupEq, optionSomeBindExplicit]
        exact projEq
      obtain ⟨bodyTerm', composedLookupRelated, bodyPar⟩ :=
        spinePar.lookupAtShiftTwoRelated bodySlot composedLookup
      obtain ⟨bodyChild', lookupRelatedEq, projRelatedEq⟩ :=
        optionBindEqSome composedLookupRelated
      refine ⟨RawTerm.substPair
        (RawTerm.weakenBodyUnderTwoBindersBy depth bodyTerm')
        innerTerm' outerTerm', ?_, ?_⟩
      · rw [innerRelatedEq, optionSomeBindMonadic, outerRelatedEq,
          optionSomeBindMonadic, lookupRelatedEq, optionSomeBindMonadic,
          projRelatedEq, optionSomeBindMonadic]
      · exact ParStepOverTable.substPair_diagonal tableIsUniform
          (ParStepOverTable.weakenBodyUnderTwoBindersBy tableIsUniform
            depth bodyPar)
          innerPar outerPar
  | depth, .substPairIntoScrutineeChild scrutineeIndex bodySlot
      innerTemplate outerTemplate, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨innerTerm, innerEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨outerTerm, outerEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨childrenView, childrenEq, restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨bodyChild, childEq, restEq4⟩ := optionBindEqSome restEq3
      obtain ⟨bodyTerm, projEq, someEq⟩ := optionBindEqSome restEq4
      obtain rfl := Option.some.inj someEq
      obtain ⟨innerTerm', innerRelatedEq, innerPar⟩ :=
        rule.interpretTemplate?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth innerTemplate innerEq
      obtain ⟨outerTerm', outerRelatedEq, outerPar⟩ :=
        rule.interpretTemplate?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth outerTemplate outerEq
      dsimp only [IotaRuleDesc.scrutineeChildrenAt?] at childrenEq ⊢
      obtain ⟨scrutineeTerm, termEq, viewEq⟩ := optionMapEqSome childrenEq
      obtain ⟨spec, matchedPayload, matchedChildren, matchedChildren',
          _specEq, scrutineeIsCell, termRelatedEq, matchedChildrenPar⟩ :=
        rule.scrutineeCellExtraction_parRelated spinePar allFire
          scrutineeHeadsAreRigid scrutineeIndex termEq
      subst scrutineeIsCell
      have composedLookup :
          (scopedChildAt? matchedChildren.toScopedChildren bodySlot).bind
              ScopedChild.atShiftTwo?
            = some bodyTerm := by
        rw [show matchedChildren.toScopedChildren = childrenView
            from viewEq, childEq, optionSomeBindExplicit]
        exact projEq
      obtain ⟨bodyTerm', composedLookupRelated, bodyPar⟩ :=
        matchedChildrenPar.lookupAtShiftTwoRelated bodySlot composedLookup
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
      · exact ParStepOverTable.substPair_diagonal tableIsUniform
          (ParStepOverTable.weakenBodyUnderTwoBindersBy tableIsUniform
            depth bodyPar)
          innerPar outerPar

/-- Spine companion: `builtGen` children assembly transports — each
shift arm interprets at its own depth and the assembled spines relate
pointwise. -/
theorem IotaRuleDesc.interpretBuiltChildren?_parStable (rule : IotaRuleDesc)
    {table : List IotaRuleDesc}
    (tableIsUniform : ∀ anyRule, anyRule ∈ table → anyRule.IsScopeUniform)
    (scrutineeHeadsAreRigid : ∀ spec, spec ∈ rule.scrutinees →
      ∀ other, other ∈ table → spec.head ≠ other.elimGenerator)
    {scope : Nat} (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spinePar : ParStepOverTableChildren table spine spine')
    (allFire : rule.scrutineesFire spine rule.scrutinees = true) :
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
      ∧ ParStepOverTableChildren table builtChildren builtChildren'
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
      obtain ⟨childTerm', childRelatedEq, childPar⟩ :=
        rule.interpretTemplate?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth childTemplate childEq
      obtain ⟨restChildren', restRelatedEq, restPar⟩ :=
        rule.interpretBuiltChildren?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth restShifts restTemplates restChildrenEq
      refine ⟨.childCons childTerm' restChildren', ?_, ?_⟩
      · rw [childRelatedEq, optionSomeBindMonadic, restRelatedEq,
          optionSomeBindMonadic]
      · exact .cons childPar restPar
  | depth, 1 :: restShifts, .spineCons childTemplate restTemplates,
      builtChildren, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted ⊢
      obtain ⟨childTerm, childEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨restChildren, restChildrenEq, someEq⟩ :=
        optionBindEqSome restEq
      obtain rfl := Option.some.inj someEq
      obtain ⟨childTerm', childRelatedEq, childPar⟩ :=
        rule.interpretTemplate?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          (depth + 1) childTemplate childEq
      obtain ⟨restChildren', restRelatedEq, restPar⟩ :=
        rule.interpretBuiltChildren?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth restShifts restTemplates restChildrenEq
      refine ⟨.childCons childTerm' restChildren', ?_, ?_⟩
      · rw [childRelatedEq, optionSomeBindMonadic, restRelatedEq,
          optionSomeBindMonadic]
      · exact .cons childPar restPar
  | depth, 2 :: restShifts, .spineCons childTemplate restTemplates,
      builtChildren, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted ⊢
      obtain ⟨childTerm, childEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨restChildren, restChildrenEq, someEq⟩ :=
        optionBindEqSome restEq
      obtain rfl := Option.some.inj someEq
      obtain ⟨childTerm', childRelatedEq, childPar⟩ :=
        rule.interpretTemplate?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          (depth + 2) childTemplate childEq
      obtain ⟨restChildren', restRelatedEq, restPar⟩ :=
        rule.interpretBuiltChildren?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth restShifts restTemplates restChildrenEq
      refine ⟨.childCons childTerm' restChildren', ?_, ?_⟩
      · rw [childRelatedEq, optionSomeBindMonadic, restRelatedEq,
          optionSomeBindMonadic]
      · exact .cons childPar restPar
  | _, (_ + 3) :: _, .spineCons _ _, _, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted
      injection interpreted

/-- Replacements companion: the reassembly fold transports across
pointwise-related reassembly spines. -/
theorem IotaRuleDesc.interpretReplacements?_parStable (rule : IotaRuleDesc)
    {table : List IotaRuleDesc}
    (tableIsUniform : ∀ anyRule, anyRule ∈ table → anyRule.IsScopeUniform)
    (scrutineeHeadsAreRigid : ∀ spec, spec ∈ rule.scrutinees →
      ∀ other, other ∈ table → spec.head ≠ other.elimGenerator)
    {scope : Nat} (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spinePar : ParStepOverTableChildren table spine spine')
    (allFire : rule.scrutineesFire spine rule.scrutinees = true) :
    (depth : Nat) → (replacements : SpineReplacements) →
    {reassemblySpine reassemblySpine' :
      RawTermChildren rule.elimGenerator.binderShifts (scope + depth)} →
    ParStepOverTableChildren table reassemblySpine reassemblySpine' →
    {replacedSpine :
      RawTermChildren rule.elimGenerator.binderShifts (scope + depth)} →
    rule.interpretReplacements? elimPayload spine depth replacements
        reassemblySpine
      = some replacedSpine →
    ∃ replacedSpine',
      rule.interpretReplacements? elimPayload spine' depth replacements
          reassemblySpine'
        = some replacedSpine'
      ∧ ParStepOverTableChildren table replacedSpine replacedSpine'
  | depth, .replaceNil, _, _, reassemblyPar, replacedSpine, interpreted => by
      dsimp only [IotaRuleDesc.interpretReplacements?] at interpreted ⊢
      obtain rfl := Option.some.inj interpreted
      exact ⟨_, rfl, reassemblyPar⟩
  | depth, .replaceCons slot replacementTemplate restReplacements, _, _,
      reassemblyPar, replacedSpine, interpreted => by
      dsimp only [IotaRuleDesc.interpretReplacements?] at interpreted ⊢
      obtain ⟨replacement, replacementEq, restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨replacedOnce, replaceAtEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨replacement', replacementRelatedEq, replacementPar⟩ :=
        rule.interpretTemplate?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth replacementTemplate replacementEq
      obtain ⟨replacedOnce', replaceAtRelatedEq, replacedOncePar⟩ :=
        RawTermChildren.replaceChildAt?_parRelated reassemblyPar slot
          replacementPar replaceAtEq
      obtain ⟨replacedSpine', restRelatedEq, replacedSpinePar⟩ :=
        rule.interpretReplacements?_parStable tableIsUniform
          scrutineeHeadsAreRigid elimPayload spinePar allFire
          depth restReplacements replacedOncePar restEq2
      refine ⟨replacedSpine', ?_, replacedSpinePar⟩
      rw [replacementRelatedEq, optionSomeBindMonadic, replaceAtRelatedEq,
        optionSomeBindMonadic]
      exact restRelatedEq

end

/-! ## The depth-0 and firing-level corollaries -/

/-- Row-level parallel stability: a row's reduct interpretation
transports to a pointwise-reduced spine with a parallel-related
reduct. -/
theorem IotaRuleDesc.interpretTarget?_parStable (rule : IotaRuleDesc)
    {table : List IotaRuleDesc}
    (tableIsUniform : ∀ anyRule, anyRule ∈ table → anyRule.IsScopeUniform)
    (scrutineeHeadsAreRigid : ∀ spec, spec ∈ rule.scrutinees →
      ∀ other, other ∈ table → spec.head ≠ other.elimGenerator)
    {scope : Nat} (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spinePar : ParStepOverTableChildren table spine spine')
    (allFire : rule.scrutineesFire spine rule.scrutinees = true)
    {result : RawTerm scope}
    (interpreted : rule.interpretTarget? elimPayload spine = some result) :
    ∃ result', rule.interpretTarget? elimPayload spine' = some result'
      ∧ ParStepOverTable table result result' :=
  rule.interpretTemplate?_parStable tableIsUniform scrutineeHeadsAreRigid
    elimPayload spinePar allFire 0 rule.target interpreted

/-- ★ **Firing-level parallel stability**: a fired row REFIRES on a
pointwise-reduced spine, producing a parallel-related reduct — the
single lemma the Takahashi triangle's root cases consume. -/
theorem IotaRuleDesc.firesOn?_parStable (rule : IotaRuleDesc)
    {table : List IotaRuleDesc}
    (tableIsUniform : ∀ anyRule, anyRule ∈ table → anyRule.IsScopeUniform)
    (scrutineeHeadsAreRigid : ∀ spec, spec ∈ rule.scrutinees →
      ∀ other, other ∈ table → spec.head ≠ other.elimGenerator)
    {scope : Nat} (elimPayload : rule.elimGenerator.payload scope)
    {spine spine' : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spinePar : ParStepOverTableChildren table spine spine')
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct) :
    ∃ reduct', rule.firesOn? elimPayload spine' = some reduct'
      ∧ ParStepOverTable table reduct reduct' := by
  have allFire := rule.firesOn?_some_scrutineesFire fires
  have allFireOnReduced := rule.scrutineesFire_parPreserved spinePar
    rule.scrutinees scrutineeHeadsAreRigid allFire
  dsimp only [IotaRuleDesc.firesOn?] at fires ⊢
  rw [if_pos allFire] at fires
  rw [if_pos allFireOnReduced]
  exact rule.interpretTarget?_parStable tableIsUniform
    scrutineeHeadsAreRigid elimPayload spinePar allFire fires

end FX1Poly.Core

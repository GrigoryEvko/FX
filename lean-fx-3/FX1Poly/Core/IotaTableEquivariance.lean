import FX1Poly.Core.IotaTableEquivarianceSubstrate

/-! # FX1Poly/Core/IotaTableEquivariance — IOTA-T2: the ONE template induction

THE generic equivariance theorem: the template interpreter commutes
with substitution, proved by ONE mutual induction over
`ReductTemplate`/`ReductTemplateSpine`/`SpineReplacements` — the
theorem that replaces the seventeen per-rule substitution arms
(`StepSubst`'s per-ι cases) at the canonicality flip, and that every
FUTURE row inherits with zero new proofs.

`interpretTemplate?_subst` (the some-direction): if a template
interprets on a spine, it interprets on the SUBSTITUTED spine to the
substituted result (at the depth-lifted substitution).  CONDITIONAL on
the row's scope-uniformity certificate
(`HasScopeUniformPayloads` / `IsScopeUniform`, all 21 rows pinned in
the substrate) and on the eliminator head not being the variable
generator — the two honest boundaries the table discipline surfaces.

The direction is deliberately one-way: a VARIABLE-headed scrutinee
child access fails on the original spine (variables have no children)
but could succeed after substitution replaces the variable — so only
original success transports.  That is exactly what table subject
reduction, parallel stability, and the Takahashi triangle consume.

Corollary: `interpretTarget?_subst` (depth 0).  The `firesOn?` and
`StepOverTable.subst` relation-level corollaries land next (they add
the head-test transport on top).

## Zero-axiom verification

Mutual structural induction, the substrate commutation bricks, `dsimp
only` arm unfolding (never `unfold` — the mutual eqn-lemma trap), and
`cast` reasoning only through `castCompose` (proved by `cases` on type
equalities + definitional proof irrelevance).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated
per declaration in `FX1PolyAudit/AuditIotaTableEquivariance.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Option plumbing pins -/

/-- Monadic bind on a `some` reduces (the do-chain spelling). -/
theorem optionSomeBindMonadic {valueType resultType : Type} (value : valueType)
    (continuation : valueType → Option resultType) :
    (some value >>= continuation) = continuation value := rfl

/-- Explicit `Option.bind` on a `some` reduces (the helper spelling). -/
theorem optionSomeBindExplicit {valueType resultType : Type} (value : valueType)
    (continuation : valueType → Option resultType) :
    (some value).bind continuation = continuation value := rfl

/-- `Option.map` on a `some` reduces. -/
theorem optionSomeMap {valueType resultType : Type} (value : valueType)
    (transform : valueType → resultType) :
    (some value).map transform = some (transform value) := rfl

/-- Split a successful `Option.map`. -/
theorem optionMapEqSome {valueType resultType : Type}
    {optionValue : Option valueType} {transform : valueType → resultType}
    {result : resultType}
    (mapped : optionValue.map transform = some result) :
    ∃ value, optionValue = some value ∧ transform value = result :=
  match optionValue, mapped with
  | some value, mapped => ⟨value, rfl, Option.some.inj mapped⟩
  | none, mapped => by injection mapped

/-- Two cast-chains over the same type square agree (definitional proof
irrelevance after collapsing the intermediate types). -/
theorem castCompose {typeA typeB typeC typeD : Type}
    (viaB1 : typeA = typeB) (viaB2 : typeB = typeD)
    (viaC1 : typeA = typeC) (viaC2 : typeC = typeD) (value : typeA) :
    cast viaB2 (cast viaB1 value) = cast viaC2 (cast viaC1 value) := by
  cases viaB1
  cases viaC1
  rfl

/-! ## Scrutinee derivation under substitution -/

/-- The derived scrutinee commutes with substitution: whatever term the
declared slot holds, the substituted spine's slot holds its
substitution. -/
theorem IotaRuleDesc.scrutineeTermAt?_subst (rule : IotaRuleDesc)
    {scope targetScope : Nat} (sigma : RawTermSubst scope targetScope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope)
    (scrutineeIndex : Nat) {scrutineeTerm : RawTerm scope}
    (found : rule.scrutineeTermAt? scrutineeIndex spine = some scrutineeTerm) :
    rule.scrutineeTermAt? scrutineeIndex (RawTermChildren.subst sigma spine)
      = some (RawTerm.subst sigma scrutineeTerm) := by
  dsimp only [IotaRuleDesc.scrutineeTermAt?, scopedChildAt?] at found ⊢
  obtain ⟨spec, specEq, restEq⟩ := optionBindEqSome found
  obtain ⟨scrutineeChild, lookupEq, projEq⟩ := optionBindEqSome restEq
  rw [specEq, optionSomeBindExplicit]
  rw [RawTermChildren.toScopedChildren_subst sigma spine, listEntryAt?_map,
    lookupEq, optionSomeMap, optionSomeBindExplicit]
  rw [ScopedChild.atShiftZero?_substView, projEq, optionSomeMap]

/-- The scrutinee-CHILD lookup commutes with substitution.  Bundles the
variable-headed contradiction: a successful child lookup on the
ORIGINAL spine forces the scrutinee to be a non-variable cell (variables
have no children), so the substituted scrutinee decomposes
structurally. -/
theorem IotaRuleDesc.scrutineeChildLookup_subst (rule : IotaRuleDesc)
    {scope targetScope : Nat} (sigma : RawTermSubst scope targetScope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope)
    (scrutineeIndex slot : Nat)
    {scrutineeChildrenView : List (ScopedChild scope)}
    (childrenFound : rule.scrutineeChildrenAt? scrutineeIndex spine
      = some scrutineeChildrenView)
    {scrutineeChild : ScopedChild scope}
    (childFound : scopedChildAt? scrutineeChildrenView slot
      = some scrutineeChild) :
    rule.scrutineeChildrenAt? scrutineeIndex
        (RawTermChildren.subst sigma spine)
      = some (scrutineeChildrenView.map (ScopedChild.substView sigma))
    ∧ scopedChildAt? (scrutineeChildrenView.map (ScopedChild.substView sigma))
        slot
      = some (scrutineeChild.substView sigma) := by
  dsimp only [IotaRuleDesc.scrutineeChildrenAt?] at childrenFound ⊢
  obtain ⟨scrutineeTerm, termEq, viewEq⟩ := optionMapEqSome childrenFound
  cases scrutineeTerm with
  | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
    by_cases isVar : scrutineeGenerator = .gen_var
    · exfalso
      subst isVar
      cases scrutineeChildren
      rw [← viewEq] at childFound
      dsimp only [RawTerm.scopedChildrenView,
        RawTermChildren.toScopedChildren, scopedChildAt?,
        listEntryAt?] at childFound
      injection childFound
    · constructor
      · rw [rule.scrutineeTermAt?_subst sigma spine scrutineeIndex termEq]
        rw [RawTerm.subst_nonVar_reduces sigma isVar
          scrutineePayload scrutineeChildren]
        rw [optionSomeMap]
        dsimp only [RawTerm.scopedChildrenView]
        rw [show foldChildren GenAlgebra.canonical sigma scrutineeChildren
            = RawTermChildren.subst sigma scrutineeChildren from rfl]
        rw [RawTermChildren.toScopedChildren_subst sigma scrutineeChildren]
        rw [show scrutineeChildren.toScopedChildren = scrutineeChildrenView
          from viewEq]
      · dsimp only [scopedChildAt?] at childFound ⊢
        rw [listEntryAt?_map, childFound, optionSomeMap]

/-- The reassembly payload transport commutes with substitution (cast
chains over the payload type square agree). -/
theorem IotaRuleDesc.elimPayloadAtDepth?_subst (rule : IotaRuleDesc)
    {scope targetScope : Nat}
    (isNotVarHead : rule.elimGenerator ≠ .gen_var)
    (elimPayload : rule.elimGenerator.payload scope) (depth : Nat)
    {payloadAtDepth : rule.elimGenerator.payload (scope + depth)}
    (resolved : rule.elimPayloadAtDepth? depth elimPayload
      = some payloadAtDepth) :
    rule.elimPayloadAtDepth? depth
        (cast (Generator.payload_scope_invariant_of_not_var isNotVarHead
          scope targetScope) elimPayload)
      = some (cast (Generator.payload_scope_invariant_of_not_var isNotVarHead
          (scope + depth) (targetScope + depth)) payloadAtDepth) := by
  dsimp only [IotaRuleDesc.elimPayloadAtDepth?] at resolved ⊢
  rw [dif_neg isNotVarHead] at resolved ⊢
  obtain rfl := Option.some.inj resolved
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

/-- A `builtGen` payload source resolves on the substituted spine to
the scope-invariance transport of the original resolution — GIVEN the
source's scope-uniformity certificate (which also yields the built
head's non-variable-ness). -/
theorem IotaRuleDesc.resolvePayloadSource?_subst (rule : IotaRuleDesc)
    {scope targetScope : Nat} (sigma : RawTermSubst scope targetScope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope)
    (depth : Nat) {builtHead : Generator}
    (payloadSource : PayloadSource builtHead)
    (isUniform : payloadSource.IsScopeUniform)
    {builtPayload : builtHead.payload (scope + depth)}
    (resolved : rule.resolvePayloadSource? spine depth payloadSource
      = some builtPayload) :
    ∃ (isNotVarBuilt : builtHead ≠ .gen_var),
      rule.resolvePayloadSource? (RawTermChildren.subst sigma spine) depth
          payloadSource
        = some (cast (Generator.payload_scope_invariant_of_not_var
            isNotVarBuilt (scope + depth) (targetScope + depth))
          builtPayload) := by
  cases payloadSource with
  | constantFamily payloadFamily =>
      obtain ⟨isNotVarBuilt, familyUniform⟩ := isUniform
      refine ⟨isNotVarBuilt, ?_⟩
      dsimp only [IotaRuleDesc.resolvePayloadSource?] at resolved ⊢
      obtain rfl := Option.some.inj resolved
      exact congrArg some
        (familyUniform (scope + depth) (targetScope + depth)
          isNotVarBuilt).symm
  | transformedFromScrutinee scrutineeIndex sourceHead payloadTransform =>
      obtain ⟨isNotVarBuilt, isNotVarSource, transformUniform⟩ := isUniform
      refine ⟨isNotVarBuilt, ?_⟩
      dsimp only [IotaRuleDesc.resolvePayloadSource?] at resolved ⊢
      obtain ⟨scrutineeTerm, termEq, restEq⟩ := optionBindEqSome resolved
      cases scrutineeTerm with
      | mkGen scrutineeGenerator scrutineePayload scrutineeChildren =>
        have restEqDite :
            (if isDeclaredHead : scrutineeGenerator = sourceHead then
              some (payloadTransform scope (scope + depth)
                (isDeclaredHead ▸ scrutineePayload))
            else none) = some builtPayload := restEq
        by_cases isHead : scrutineeGenerator = sourceHead
        · subst isHead
          rw [dif_pos rfl] at restEqDite
          obtain rfl := Option.some.inj restEqDite
          rw [rule.scrutineeTermAt?_subst sigma spine scrutineeIndex termEq]
          rw [RawTerm.subst_nonVar_reduces sigma isNotVarSource
            scrutineePayload scrutineeChildren]
          rw [optionSomeBindMonadic]
          show (if isDeclaredHead : scrutineeGenerator = scrutineeGenerator
              then some (payloadTransform targetScope (targetScope + depth)
                (isDeclaredHead ▸ _))
            else none) = _
          rw [dif_pos rfl]
          exact congrArg some
            ((transformUniform scope (scope + depth) targetScope
              (targetScope + depth) isNotVarSource isNotVarBuilt
              scrutineePayload).symm)
        · rw [dif_neg isHead] at restEqDite
          injection restEqDite

/-! ## THE generic equivariance — one mutual template induction -/

mutual

/-- ★ **The generic interpreter-substitution commutation** (the
some-direction): a successful interpretation transports to the
substituted spine, with the result substituted at the depth-lifted
substitution.  ONE induction for every rule, every depth, every future
row — conditional on the template's payload scope-uniformity. -/
theorem IotaRuleDesc.interpretTemplate?_subst (rule : IotaRuleDesc)
    {scope targetScope : Nat} (sigma : RawTermSubst scope targetScope)
    (isNotVarHead : rule.elimGenerator ≠ .gen_var)
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    (depth : Nat) → (template : ReductTemplate) →
    template.HasScopeUniformPayloads →
    {result : RawTerm (scope + depth)} →
    rule.interpretTemplate? elimPayload spine depth template = some result →
    rule.interpretTemplate?
        (cast (Generator.payload_scope_invariant_of_not_var isNotVarHead
          scope targetScope) elimPayload)
        (RawTermChildren.subst sigma spine) depth template
      = some (RawTerm.subst (iterateLiftRaw sigma depth) result)
  | depth, .boundVarAt binderIndex, _, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      by_cases isBound : binderIndex < depth
      · rw [dif_pos isBound] at interpreted ⊢
        obtain rfl := Option.some.inj interpreted
        show _ = some (iterateLiftRaw sigma depth ⟨binderIndex, _⟩)
        rw [iterateLiftRawSubst_fixesTemplateBinder sigma depth binderIndex
          isBound]
      · rw [dif_neg isBound] at interpreted
        injection interpreted
  | depth, .spineChildAt slot, _, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?, scopedChildAt?]
        at interpreted ⊢
      obtain ⟨spineChild, lookupEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨childTerm, projEq, someEq⟩ := optionBindEqSome restEq
      obtain rfl := Option.some.inj someEq
      rw [RawTermChildren.toScopedChildren_subst sigma spine,
        listEntryAt?_map, lookupEq, optionSomeMap, optionSomeBindMonadic]
      rw [ScopedChild.atShiftZero?_substView, projEq, optionSomeMap,
        optionSomeBindMonadic]
      rw [RawTerm.weakenBy_subst sigma depth childTerm]
  | depth, .scrutineeChildAt scrutineeIndex slot, _, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨childrenView, childrenEq, restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨scrutineeChild, childEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨childTerm, projEq, someEq⟩ := optionBindEqSome restEq2
      obtain rfl := Option.some.inj someEq
      obtain ⟨viewSubstEq, lookupSubstEq⟩ :=
        rule.scrutineeChildLookup_subst sigma spine scrutineeIndex slot
          childrenEq childEq
      rw [viewSubstEq, optionSomeBindMonadic, lookupSubstEq,
        optionSomeBindMonadic]
      rw [ScopedChild.atShiftZero?_substView, projEq, optionSomeMap,
        optionSomeBindMonadic]
      rw [RawTerm.weakenBy_subst sigma depth childTerm]
  | depth, .theScrutineeAt scrutineeIndex, _, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨scrutineeTerm, termEq, someEq⟩ := optionBindEqSome interpreted
      obtain rfl := Option.some.inj someEq
      rw [rule.scrutineeTermAt?_subst sigma spine scrutineeIndex termEq,
        optionSomeBindMonadic]
      rw [RawTerm.weakenBy_subst sigma depth scrutineeTerm]
  | depth, .motiveInstantiatedWith argTemplate, isUniform, result,
      interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?, scopedChildAt?]
        at interpreted ⊢
      obtain ⟨motiveSlot, slotEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨argTerm, argEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨motiveChild, lookupEq, restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨motiveBody, projEq, someEq⟩ := optionBindEqSome restEq3
      obtain rfl := Option.some.inj someEq
      rw [slotEq, optionSomeBindMonadic]
      rw [rule.interpretTemplate?_subst sigma isNotVarHead elimPayload spine
        depth argTemplate isUniform argEq, optionSomeBindMonadic]
      rw [RawTermChildren.toScopedChildren_subst sigma spine,
        listEntryAt?_map, lookupEq, optionSomeMap, optionSomeBindMonadic]
      rw [ScopedChild.atShiftOne?_substView, projEq, optionSomeMap,
        optionSomeBindMonadic]
      rw [RawTerm.subst0_subst_commute]
      rw [RawTerm.weakenBodyUnderOneBinderBy_subst sigma depth motiveBody]
  | depth, .motiveInstantiatedWithPair innerTemplate outerTemplate,
      isUniform, result, interpreted => by
      obtain ⟨innerUniform, outerUniform⟩ := isUniform
      dsimp only [IotaRuleDesc.interpretTemplate?, scopedChildAt?]
        at interpreted ⊢
      obtain ⟨motiveSlot, slotEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨innerTerm, innerEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨outerTerm, outerEq, restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨motiveChild, lookupEq, restEq4⟩ := optionBindEqSome restEq3
      obtain ⟨motiveBody, projEq, someEq⟩ := optionBindEqSome restEq4
      obtain rfl := Option.some.inj someEq
      rw [slotEq, optionSomeBindMonadic]
      rw [rule.interpretTemplate?_subst sigma isNotVarHead elimPayload spine
        depth innerTemplate innerUniform innerEq, optionSomeBindMonadic]
      rw [rule.interpretTemplate?_subst sigma isNotVarHead elimPayload spine
        depth outerTemplate outerUniform outerEq, optionSomeBindMonadic]
      rw [RawTermChildren.toScopedChildren_subst sigma spine,
        listEntryAt?_map, lookupEq, optionSomeMap, optionSomeBindMonadic]
      rw [ScopedChild.atShiftTwo?_substView, projEq, optionSomeMap,
        optionSomeBindMonadic]
      rw [RawTerm.substPair_subst_commute]
      rw [RawTerm.weakenBodyUnderTwoBindersBy_subst sigma depth motiveBody]
  | depth, .builtGen builtHead payloadSource childTemplates, isUniform,
      result, interpreted => by
      obtain ⟨payloadUniform, childrenUniform⟩ := isUniform
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨builtPayload, payloadEq, restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨builtChildren, childrenEq, someEq⟩ := optionBindEqSome restEq
      obtain rfl := Option.some.inj someEq
      obtain ⟨isNotVarBuilt, payloadSubstEq⟩ :=
        rule.resolvePayloadSource?_subst sigma spine depth payloadSource
          payloadUniform payloadEq
      rw [payloadSubstEq, optionSomeBindMonadic]
      rw [rule.interpretBuiltChildren?_subst sigma isNotVarHead elimPayload
        spine depth builtHead.binderShifts childTemplates childrenUniform
        childrenEq, optionSomeBindMonadic]
      rw [RawTerm.subst_nonVar_reduces (iterateLiftRaw sigma depth)
        isNotVarBuilt builtPayload builtChildren]
      rfl
  | depth, .reassembledReplacing replacements, isUniform, result,
      interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨payloadAtDepth, payloadEq, restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨replacedSpine, replacedEq, someEq⟩ := optionBindEqSome restEq
      obtain rfl := Option.some.inj someEq
      rw [rule.elimPayloadAtDepth?_subst isNotVarHead elimPayload depth
        payloadEq, optionSomeBindMonadic]
      have weakenedAligned := RawTermChildren.weakenSpineBy_subst sigma depth
        spine
      rw [show RawTermChildren.weakenSpineBy depth
            (RawTermChildren.subst sigma spine)
          = RawTermChildren.subst (iterateLiftRaw sigma depth)
            (RawTermChildren.weakenSpineBy depth spine)
        from weakenedAligned.symm]
      rw [rule.interpretReplacements?_subst sigma isNotVarHead elimPayload
        spine depth replacements isUniform
        (RawTermChildren.weakenSpineBy depth spine) replacedEq,
        optionSomeBindMonadic]
      rw [RawTerm.subst_nonVar_reduces (iterateLiftRaw sigma depth)
        isNotVarHead payloadAtDepth replacedSpine]
      rfl
  | depth, .substOneIntoSpineChild bodySlot argTemplate, isUniform, result,
      interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?, scopedChildAt?]
        at interpreted ⊢
      obtain ⟨argTerm, argEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨bodyChild, lookupEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨bodyTerm, projEq, someEq⟩ := optionBindEqSome restEq2
      obtain rfl := Option.some.inj someEq
      rw [rule.interpretTemplate?_subst sigma isNotVarHead elimPayload spine
        depth argTemplate isUniform argEq, optionSomeBindMonadic]
      rw [RawTermChildren.toScopedChildren_subst sigma spine,
        listEntryAt?_map, lookupEq, optionSomeMap, optionSomeBindMonadic]
      rw [ScopedChild.atShiftOne?_substView, projEq, optionSomeMap,
        optionSomeBindMonadic]
      rw [RawTerm.subst0_subst_commute]
      rw [RawTerm.weakenBodyUnderOneBinderBy_subst sigma depth bodyTerm]
  | depth, .substOneIntoScrutineeChild scrutineeIndex bodySlot argTemplate,
      isUniform, result, interpreted => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨argTerm, argEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨childrenView, childrenEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨bodyChild, childEq, restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨bodyTerm, projEq, someEq⟩ := optionBindEqSome restEq3
      obtain rfl := Option.some.inj someEq
      obtain ⟨viewSubstEq, lookupSubstEq⟩ :=
        rule.scrutineeChildLookup_subst sigma spine scrutineeIndex bodySlot
          childrenEq childEq
      rw [rule.interpretTemplate?_subst sigma isNotVarHead elimPayload spine
        depth argTemplate isUniform argEq, optionSomeBindMonadic]
      rw [viewSubstEq, optionSomeBindMonadic, lookupSubstEq,
        optionSomeBindMonadic]
      rw [ScopedChild.atShiftOne?_substView, projEq, optionSomeMap,
        optionSomeBindMonadic]
      rw [RawTerm.subst0_subst_commute]
      rw [RawTerm.weakenBodyUnderOneBinderBy_subst sigma depth bodyTerm]
  | depth, .substPairIntoSpineChild bodySlot innerTemplate outerTemplate,
      isUniform, result, interpreted => by
      obtain ⟨innerUniform, outerUniform⟩ := isUniform
      dsimp only [IotaRuleDesc.interpretTemplate?, scopedChildAt?]
        at interpreted ⊢
      obtain ⟨innerTerm, innerEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨outerTerm, outerEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨bodyChild, lookupEq, restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨bodyTerm, projEq, someEq⟩ := optionBindEqSome restEq3
      obtain rfl := Option.some.inj someEq
      rw [rule.interpretTemplate?_subst sigma isNotVarHead elimPayload spine
        depth innerTemplate innerUniform innerEq, optionSomeBindMonadic]
      rw [rule.interpretTemplate?_subst sigma isNotVarHead elimPayload spine
        depth outerTemplate outerUniform outerEq, optionSomeBindMonadic]
      rw [RawTermChildren.toScopedChildren_subst sigma spine,
        listEntryAt?_map, lookupEq, optionSomeMap, optionSomeBindMonadic]
      rw [ScopedChild.atShiftTwo?_substView, projEq, optionSomeMap,
        optionSomeBindMonadic]
      rw [RawTerm.substPair_subst_commute]
      rw [RawTerm.weakenBodyUnderTwoBindersBy_subst sigma depth bodyTerm]
  | depth, .substPairIntoScrutineeChild scrutineeIndex bodySlot innerTemplate
      outerTemplate, isUniform, result, interpreted => by
      obtain ⟨innerUniform, outerUniform⟩ := isUniform
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpreted ⊢
      obtain ⟨innerTerm, innerEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨outerTerm, outerEq, restEq2⟩ := optionBindEqSome restEq
      obtain ⟨childrenView, childrenEq, restEq3⟩ := optionBindEqSome restEq2
      obtain ⟨bodyChild, childEq, restEq4⟩ := optionBindEqSome restEq3
      obtain ⟨bodyTerm, projEq, someEq⟩ := optionBindEqSome restEq4
      obtain rfl := Option.some.inj someEq
      obtain ⟨viewSubstEq, lookupSubstEq⟩ :=
        rule.scrutineeChildLookup_subst sigma spine scrutineeIndex bodySlot
          childrenEq childEq
      rw [rule.interpretTemplate?_subst sigma isNotVarHead elimPayload spine
        depth innerTemplate innerUniform innerEq, optionSomeBindMonadic]
      rw [rule.interpretTemplate?_subst sigma isNotVarHead elimPayload spine
        depth outerTemplate outerUniform outerEq, optionSomeBindMonadic]
      rw [viewSubstEq, optionSomeBindMonadic, lookupSubstEq,
        optionSomeBindMonadic]
      rw [ScopedChild.atShiftTwo?_substView, projEq, optionSomeMap,
        optionSomeBindMonadic]
      rw [RawTerm.substPair_subst_commute]
      rw [RawTerm.weakenBodyUnderTwoBindersBy_subst sigma depth bodyTerm]

/-- Spine companion: `builtGen` children assembly commutes with
substitution — the shift-0/1/2 arms align DEFINITIONALLY because
`iterateLiftRaw sigma (depth + k)` is literally `lift^k` of
`iterateLiftRaw sigma depth`. -/
theorem IotaRuleDesc.interpretBuiltChildren?_subst (rule : IotaRuleDesc)
    {scope targetScope : Nat} (sigma : RawTermSubst scope targetScope)
    (isNotVarHead : rule.elimGenerator ≠ .gen_var)
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    (depth : Nat) → (childShifts : List Nat) →
    (childTemplates : ReductTemplateSpine) →
    childTemplates.HasScopeUniformPayloads →
    {builtChildren : RawTermChildren childShifts (scope + depth)} →
    rule.interpretBuiltChildren? elimPayload spine depth childShifts
        childTemplates
      = some builtChildren →
    rule.interpretBuiltChildren?
        (cast (Generator.payload_scope_invariant_of_not_var isNotVarHead
          scope targetScope) elimPayload)
        (RawTermChildren.subst sigma spine) depth childShifts childTemplates
      = some (RawTermChildren.subst (iterateLiftRaw sigma depth)
          builtChildren)
  | depth, [], .spineNil, _, builtChildren, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted ⊢
      obtain rfl := Option.some.inj interpreted
      rfl
  | _, [], .spineCons _ _, _, _, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted
      injection interpreted
  | _, _ :: _, .spineNil, _, _, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted
      injection interpreted
  | depth, 0 :: restShifts, .spineCons childTemplate restTemplates,
      isUniform, builtChildren, interpreted => by
      obtain ⟨childUniform, restUniform⟩ := isUniform
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted ⊢
      obtain ⟨childTerm, childEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨restChildren, restChildrenEq, someEq⟩ :=
        optionBindEqSome restEq
      obtain rfl := Option.some.inj someEq
      rw [rule.interpretTemplate?_subst sigma isNotVarHead elimPayload spine
        depth childTemplate childUniform childEq, optionSomeBindMonadic]
      rw [rule.interpretBuiltChildren?_subst sigma isNotVarHead elimPayload
        spine depth restShifts restTemplates restUniform restChildrenEq,
        optionSomeBindMonadic]
      rfl
  | depth, 1 :: restShifts, .spineCons childTemplate restTemplates,
      isUniform, builtChildren, interpreted => by
      obtain ⟨childUniform, restUniform⟩ := isUniform
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted ⊢
      obtain ⟨childTerm, childEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨restChildren, restChildrenEq, someEq⟩ :=
        optionBindEqSome restEq
      obtain rfl := Option.some.inj someEq
      rw [rule.interpretTemplate?_subst sigma isNotVarHead elimPayload spine
        (depth + 1) childTemplate childUniform childEq,
        optionSomeBindMonadic]
      rw [rule.interpretBuiltChildren?_subst sigma isNotVarHead elimPayload
        spine depth restShifts restTemplates restUniform restChildrenEq,
        optionSomeBindMonadic]
      rfl
  | depth, 2 :: restShifts, .spineCons childTemplate restTemplates,
      isUniform, builtChildren, interpreted => by
      obtain ⟨childUniform, restUniform⟩ := isUniform
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted ⊢
      obtain ⟨childTerm, childEq, restEq⟩ := optionBindEqSome interpreted
      obtain ⟨restChildren, restChildrenEq, someEq⟩ :=
        optionBindEqSome restEq
      obtain rfl := Option.some.inj someEq
      rw [rule.interpretTemplate?_subst sigma isNotVarHead elimPayload spine
        (depth + 2) childTemplate childUniform childEq,
        optionSomeBindMonadic]
      rw [rule.interpretBuiltChildren?_subst sigma isNotVarHead elimPayload
        spine depth restShifts restTemplates restUniform restChildrenEq,
        optionSomeBindMonadic]
      rfl
  | _, (_ + 3) :: _, .spineCons _ _, _, _, interpreted => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpreted
      injection interpreted

/-- Replacements companion: the reassembly fold commutes with
substitution. -/
theorem IotaRuleDesc.interpretReplacements?_subst (rule : IotaRuleDesc)
    {scope targetScope : Nat} (sigma : RawTermSubst scope targetScope)
    (isNotVarHead : rule.elimGenerator ≠ .gen_var)
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope) :
    (depth : Nat) → (replacements : SpineReplacements) →
    replacements.HasScopeUniformPayloads →
    (reassemblySpine :
      RawTermChildren rule.elimGenerator.binderShifts (scope + depth)) →
    {replacedSpine :
      RawTermChildren rule.elimGenerator.binderShifts (scope + depth)} →
    rule.interpretReplacements? elimPayload spine depth replacements
        reassemblySpine
      = some replacedSpine →
    rule.interpretReplacements?
        (cast (Generator.payload_scope_invariant_of_not_var isNotVarHead
          scope targetScope) elimPayload)
        (RawTermChildren.subst sigma spine) depth replacements
        (RawTermChildren.subst (iterateLiftRaw sigma depth) reassemblySpine)
      = some (RawTermChildren.subst (iterateLiftRaw sigma depth)
          replacedSpine)
  | depth, .replaceNil, _, reassemblySpine, replacedSpine, interpreted => by
      dsimp only [IotaRuleDesc.interpretReplacements?] at interpreted ⊢
      obtain rfl := Option.some.inj interpreted
      rfl
  | depth, .replaceCons slot replacementTemplate restReplacements,
      isUniform, reassemblySpine, replacedSpine, interpreted => by
      obtain ⟨replacementUniform, restUniform⟩ := isUniform
      dsimp only [IotaRuleDesc.interpretReplacements?] at interpreted ⊢
      obtain ⟨replacement, replacementEq, restEq⟩ :=
        optionBindEqSome interpreted
      obtain ⟨replacedOnce, replaceAtEq, restEq2⟩ := optionBindEqSome restEq
      rw [rule.interpretTemplate?_subst sigma isNotVarHead elimPayload spine
        depth replacementTemplate replacementUniform replacementEq,
        optionSomeBindMonadic]
      rw [show (RawTermChildren.subst (iterateLiftRaw sigma depth)
            reassemblySpine).replaceChildAt? slot
            (RawTerm.subst (iterateLiftRaw sigma depth) replacement)
          = some (RawTermChildren.subst (iterateLiftRaw sigma depth)
            replacedOnce) from by
        rw [← RawTermChildren.replaceChildAt?_subst
          (iterateLiftRaw sigma depth) reassemblySpine slot replacement,
          replaceAtEq, optionSomeMap]]
      rw [optionSomeBindMonadic]
      exact rule.interpretReplacements?_subst sigma isNotVarHead elimPayload
        spine depth restReplacements restUniform replacedOnce restEq2

end

/-! ## The depth-0 corollary -/

/-- ★ **Row-level equivariance**: a row's reduct interpretation commutes
with substitution, conditional on the row's scope-uniformity
certificate (all 21 rows pinned in the substrate). -/
theorem IotaRuleDesc.interpretTarget?_subst (rule : IotaRuleDesc)
    {scope targetScope : Nat} (sigma : RawTermSubst scope targetScope)
    (isUniform : rule.IsScopeUniform)
    (elimPayload : rule.elimGenerator.payload scope)
    (spine : RawTermChildren rule.elimGenerator.binderShifts scope)
    {result : RawTerm scope}
    (interpreted : rule.interpretTarget? elimPayload spine = some result) :
    rule.interpretTarget?
        (cast (Generator.payload_scope_invariant_of_not_var
          isUniform.isNotVarHead scope targetScope) elimPayload)
        (RawTermChildren.subst sigma spine)
      = some (RawTerm.subst sigma result) :=
  rule.interpretTemplate?_subst sigma isUniform.isNotVarHead elimPayload
    spine 0 rule.target isUniform.targetIsUniform interpreted

end FX1Poly.Core

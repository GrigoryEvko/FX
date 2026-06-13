import FX1Poly.Core.StepOverTable
import FX1Poly.Core.IotaTableCertificationSubstrate

/-! # FX1Poly/Core/IotaTableStructuralSR — IOTA-T3: generic structural SR

ONE template induction replacing the seventeen bespoke
`preservedByIota*` arms: a certified table-redex source yields a
certified reduct, for EVERY row of EVERY table whose target satisfies
the sort discipline — rows shipped today and rows added tomorrow alike.

The induction is SORT-PRECISE (it produces `PolyCell` cells at the
sort the certificate assigns, because a built spine's `cons` demands
exact sorts); the sort-existential `HasCertifiedCellDim0` appears only
in the headline corollary.  Three primitive families do all the work:

  * spine/scrutinee PROJECTION certifies — the slot-indexed
    `certifiedAtShiftZero/One/Two` projections against the
    interpreter's own lookups;
  * RE-ASSEMBLY certifies — `PolyCell.gen` (supportedness and payload
    evidence are TOTAL under fxProfile) over a spine built in lockstep
    with the generator's specs;
  * SUBSTITUTION certifies — `subst0_dim0` / `substPair_dim0` and the
    depth-weakening `rename_dim0` iterates.

The induction is conditional on (a) the row's sort-discipline
certificate (`HasSortCertifiedTarget`) and (b) the pattern having
FIRED (`scrutineesFire`) — firing pins each scrutinee's head, which is
what ties the scrutinee-children sorts to the row's declared specs.

## Zero-axiom verification

Type-valued Option splitters (single-`Option` matches), the
substrate's projections/builders, `dsimp only` on the mutual
interpreter (never `unfold` — the eqn-lemma `Quot.sound` trap), and
defeq ascription through the do-chain reductions.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Gated per declaration in
`FX1PolyAudit/AuditIotaTableCertification.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-! ## Type-valued Option splitters

The master induction PRODUCES data (cells), so the do-chain
extractions cannot route through `∃`-shaped Prop splitters
(`optionBindEqSome`) — these PSigma twins eliminate into Type. -/

/-- Split a successful monadic bind, data-compatibly. -/
def optionBindSomeSplit {valueType resultType : Type}
    {chainHead : Option valueType}
    {continuation : valueType → Option resultType} {result : resultType}
    (bindEq : (chainHead >>= continuation) = some result) :
    Σ' middleValue : valueType,
      (chainHead = some middleValue) ×'
      (continuation middleValue = some result) :=
  match chainHead, bindEq with
  | some middleValue, bindEq => ⟨middleValue, rfl, bindEq⟩
  | none, bindEq => by injection bindEq

/-- Split a successful map, data-compatibly. -/
def optionMapSomeSplit {valueType resultType : Type}
    {source : Option valueType} {transform : valueType → resultType}
    {result : resultType}
    (mapEq : source.map transform = some result) :
    Σ' value : valueType,
      (source = some value) ×' (transform value = result) :=
  match source, mapEq with
  | some value, mapEq => ⟨value, rfl, Option.some.inj mapEq⟩
  | none, mapEq => by injection mapEq

/-! ## Per-index firing extraction -/

/-- The spec at `scrutineeIndex` fired, given the whole pattern
fired. -/
theorem IotaRuleDesc.scrutineeSpecFires_ofIndex (rule : IotaRuleDesc)
    {scope : Nat}
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope} :
    (specs : List ScrutineeSpec) → (scrutineeIndex : Nat) →
    {spec : ScrutineeSpec} →
    rule.scrutineesFire spine specs = true →
    listEntryAt? specs scrutineeIndex = some spec →
    rule.scrutineeSpecFires spine spec = true
  | [], _, _, _, lookupEq => by injection lookupEq
  | _ :: _, 0, _, allFire, lookupEq => by
      obtain ⟨headFires, _⟩ := andEqTrueSplit allFire
      exact Option.some.inj lookupEq ▸ headFires
  | _ :: restSpecs, priorIndex + 1, _, allFire, lookupEq => by
      obtain ⟨_, restFire⟩ := andEqTrueSplit allFire
      exact rule.scrutineeSpecFires_ofIndex restSpecs priorIndex restFire
        lookupEq

/-! ## The master template induction -/

mutual

/-- ★ **Template interpretation certifies** — at the sort the row's
discipline certificate assigns, given the certified eliminator spine
and the fired pattern. -/
def IotaRuleDesc.interpretTemplate?_certified (rule : IotaRuleDesc)
    {profile : PolyProfile} {scope : Nat}
    (elimPayload : rule.elimGenerator.payload scope)
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spineCert :
      CertifiedTermSpine profile rule.elimGenerator.childSpecs scope
        rule.elimGenerator.binderShifts spine)
    (allFire : rule.scrutineesFire spine rule.scrutinees = true) :
    (depth : Nat) → (template : ReductTemplate) →
    (expectedSort : CellSort) →
    template.CertifiesAtSort rule expectedSort →
    {result : RawTerm (scope + depth)} →
    rule.interpretTemplate? elimPayload spine depth template
      = some result →
    PolyCell profile expectedSort 0 (scope + depth) CellBoundary.trivial
      (.termBase result)
  | depth, .boundVarAt binderIndex, expectedSort, cert, _, interpEq => by
      have sortIsTerm : expectedSort = .term := cert
      subst sortIsTerm
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpEq
      by_cases isTemplateBound : binderIndex < depth
      case pos =>
          rw [dif_pos isTemplateBound] at interpEq
          obtain rfl := Option.some.inj interpEq
          exact PolyCell.varCell _
      case neg =>
          rw [dif_neg isTemplateBound] at interpEq
          injection interpEq
  | depth, .spineChildAt slot, expectedSort, cert, _, interpEq => by
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpEq
      obtain ⟨spineChild, spineChildEq, restEq⟩ :=
        optionBindSomeSplit interpEq
      obtain ⟨childTerm, childShiftEq, finalEq⟩ :=
        optionBindSomeSplit restEq
      obtain rfl := Option.some.inj finalEq
      have composedEq :
          (scopedChildAt? spine.toScopedChildren slot).bind
            ScopedChild.atShiftZero? = some childTerm := by
        rw [spineChildEq]
        exact childShiftEq
      obtain ⟨projectedSpec, specLookupEq, childCell⟩ :=
        spineCert.certifiedAtShiftZero
          (Generator.childSpecs_cellDimension_zero rule.elimGenerator)
          slot composedEq
      have certAtSlot :
          (match listEntryAt? rule.elimGenerator.childSpecs slot with
            | none => False
            | some childSpec => childSpec.cellSort = expectedSort) := cert
      rw [specLookupEq] at certAtSlot
      have sortEq : projectedSpec.cellSort = expectedSort := certAtSlot
      exact sortEq ▸ PolyCell.weakenBy_dim0 depth childCell
  | depth, .scrutineeChildAt scrutineeIndex slot, expectedSort, cert, _,
      interpEq => by
      dsimp only [IotaRuleDesc.interpretTemplate?,
        IotaRuleDesc.scrutineeChildrenAt?] at interpEq
      obtain ⟨scrutineeChildrenView, childrenViewEq, restEq⟩ :=
        optionBindSomeSplit interpEq
      obtain ⟨scrutineeChild, childLookupEq, restEq2⟩ :=
        optionBindSomeSplit restEq
      obtain ⟨childTerm, childShiftEq, finalEq⟩ :=
        optionBindSomeSplit restEq2
      obtain rfl := Option.some.inj finalEq
      obtain ⟨scrutineeTerm, scrutineeTermEq, viewEq⟩ :=
        optionMapSomeSplit childrenViewEq
      have scrutineeTermBindEq :
          (rule.scrutineeSpecAt? scrutineeIndex).bind
            (fun spec =>
              (scopedChildAt? spine.toScopedChildren spec.slot).bind
                ScopedChild.atShiftZero?) = some scrutineeTerm :=
        scrutineeTermEq
      obtain ⟨scrutineeSpec, specAtEq, composedScrutineeEq⟩ :=
        optionBindSomeSplit scrutineeTermBindEq
      obtain ⟨spineSpec, spineSpecLookupEq, scrutineeCell⟩ :=
        spineCert.certifiedAtShiftZero
          (Generator.childSpecs_cellDimension_zero rule.elimGenerator)
          scrutineeSpec.slot composedScrutineeEq
      cases scrutineeTerm with
      | mkGen scrutineeGenerator scrutineePayload scrutineeChildrenRaw =>
        have specFires := rule.scrutineeSpecFires_ofIndex rule.scrutinees
          scrutineeIndex allFire specAtEq
        have isDeclaredHead : scrutineeGenerator = scrutineeSpec.head :=
          rule.scrutineeSpecFires_extractsHead specFires
            composedScrutineeEq
        subst isDeclaredHead
        have scrutineeSpineCert :=
          PolyCell.invertGenAtDim0 spineSpec.cellSort scrutineeCell
        have composedChildEq :
            (scopedChildAt? scrutineeChildrenRaw.toScopedChildren
                slot).bind ScopedChild.atShiftZero? = some childTerm := by
          rw [show scrutineeChildrenRaw.toScopedChildren
                = scrutineeChildrenView from viewEq]
          rw [childLookupEq]
          exact childShiftEq
        obtain ⟨childSpec, childSpecLookupEq, childCell⟩ :=
          scrutineeSpineCert.certifiedAtShiftZero
            (Generator.childSpecs_cellDimension_zero scrutineeSpec.head)
            slot composedChildEq
        have certAtSpec :
            (match rule.scrutineeSpecAt? scrutineeIndex with
              | none => False
              | some matchedSpec =>
                  match listEntryAt? matchedSpec.head.childSpecs slot with
                  | none => False
                  | some matchedChildSpec =>
                      matchedChildSpec.cellSort = expectedSort) := cert
        rw [specAtEq] at certAtSpec
        have certAtChild :
            (match listEntryAt? scrutineeSpec.head.childSpecs slot with
              | none => False
              | some matchedChildSpec =>
                  matchedChildSpec.cellSort = expectedSort) := certAtSpec
        rw [childSpecLookupEq] at certAtChild
        have sortEq : childSpec.cellSort = expectedSort := certAtChild
        exact sortEq ▸ PolyCell.weakenBy_dim0 depth childCell
  | depth, .theScrutineeAt scrutineeIndex, expectedSort, cert, _,
      interpEq => by
      dsimp only [IotaRuleDesc.interpretTemplate?,
        IotaRuleDesc.scrutineeTermAt?] at interpEq
      obtain ⟨scrutineeTerm, scrutineeTermEq, finalEq⟩ :=
        optionBindSomeSplit interpEq
      obtain rfl := Option.some.inj finalEq
      obtain ⟨scrutineeSpec, specAtEq, composedScrutineeEq⟩ :=
        optionBindSomeSplit scrutineeTermEq
      obtain ⟨spineSpec, spineSpecLookupEq, scrutineeCell⟩ :=
        spineCert.certifiedAtShiftZero
          (Generator.childSpecs_cellDimension_zero rule.elimGenerator)
          scrutineeSpec.slot composedScrutineeEq
      have certAtSpec :
          (match rule.scrutineeSpecAt? scrutineeIndex with
            | none => False
            | some matchedSpec =>
                match listEntryAt? rule.elimGenerator.childSpecs
                    matchedSpec.slot with
                | none => False
                | some matchedChildSpec =>
                    matchedChildSpec.cellSort = expectedSort) := cert
      rw [specAtEq] at certAtSpec
      have certAtSlot :
          (match listEntryAt? rule.elimGenerator.childSpecs
              scrutineeSpec.slot with
            | none => False
            | some matchedChildSpec =>
                matchedChildSpec.cellSort = expectedSort) := certAtSpec
      rw [spineSpecLookupEq] at certAtSlot
      have sortEq : spineSpec.cellSort = expectedSort := certAtSlot
      exact sortEq ▸ PolyCell.weakenBy_dim0 depth scrutineeCell
  | depth, .motiveInstantiatedWith argTemplate, expectedSort, cert, _,
      interpEq => by
      obtain ⟨motiveCert, argCert⟩ := cert
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpEq
      obtain ⟨motiveSlot, motiveSlotEq, restEq⟩ :=
        optionBindSomeSplit interpEq
      obtain ⟨argTerm, argEq, restEq2⟩ := optionBindSomeSplit restEq
      obtain ⟨motiveChild, motiveChildEq, restEq3⟩ :=
        optionBindSomeSplit restEq2
      obtain ⟨motiveBody, motiveBodyEq, finalEq⟩ :=
        optionBindSomeSplit restEq3
      obtain rfl := Option.some.inj finalEq
      have composedMotiveEq :
          (scopedChildAt? spine.toScopedChildren motiveSlot).bind
            ScopedChild.atShiftOne? = some motiveBody := by
        rw [motiveChildEq]
        exact motiveBodyEq
      obtain ⟨motiveSpec, motiveSpecLookupEq, motiveBodyCell⟩ :=
        spineCert.certifiedAtShiftOne
          (Generator.childSpecs_cellDimension_zero rule.elimGenerator)
          motiveSlot composedMotiveEq
      rw [motiveSlotEq] at motiveCert
      have motiveCertAtSlot :
          (match listEntryAt? rule.elimGenerator.childSpecs motiveSlot with
            | none => False
            | some matchedSpec =>
                matchedSpec.cellSort = expectedSort) := motiveCert
      rw [motiveSpecLookupEq] at motiveCertAtSlot
      have sortEq : motiveSpec.cellSort = expectedSort := motiveCertAtSlot
      exact sortEq ▸ PolyCell.subst0_dim0
        (PolyCell.weakenBodyUnderOneBinderBy_dim0 depth motiveBodyCell)
        (rule.interpretTemplate?_certified elimPayload spineCert allFire
          depth argTemplate .term argCert argEq)
  | depth, .motiveInstantiatedWithPair innerTemplate outerTemplate,
      expectedSort, cert, _, interpEq => by
      obtain ⟨motiveCert, innerCert, outerCert⟩ := cert
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpEq
      obtain ⟨motiveSlot, motiveSlotEq, restEq⟩ :=
        optionBindSomeSplit interpEq
      obtain ⟨innerTerm, innerEq, restEq2⟩ := optionBindSomeSplit restEq
      obtain ⟨outerTerm, outerEq, restEq3⟩ := optionBindSomeSplit restEq2
      obtain ⟨motiveChild, motiveChildEq, restEq4⟩ :=
        optionBindSomeSplit restEq3
      obtain ⟨motiveBody, motiveBodyEq, finalEq⟩ :=
        optionBindSomeSplit restEq4
      obtain rfl := Option.some.inj finalEq
      have composedMotiveEq :
          (scopedChildAt? spine.toScopedChildren motiveSlot).bind
            ScopedChild.atShiftTwo? = some motiveBody := by
        rw [motiveChildEq]
        exact motiveBodyEq
      obtain ⟨motiveSpec, motiveSpecLookupEq, motiveBodyCell⟩ :=
        spineCert.certifiedAtShiftTwo
          (Generator.childSpecs_cellDimension_zero rule.elimGenerator)
          motiveSlot composedMotiveEq
      rw [motiveSlotEq] at motiveCert
      have motiveCertAtSlot :
          (match listEntryAt? rule.elimGenerator.childSpecs motiveSlot with
            | none => False
            | some matchedSpec =>
                matchedSpec.cellSort = expectedSort) := motiveCert
      rw [motiveSpecLookupEq] at motiveCertAtSlot
      have sortEq : motiveSpec.cellSort = expectedSort := motiveCertAtSlot
      exact sortEq ▸ PolyCell.substPair_dim0
        (PolyCell.weakenBodyUnderTwoBindersBy_dim0 depth motiveBodyCell)
        (rule.interpretTemplate?_certified elimPayload spineCert allFire
          depth innerTemplate .term innerCert innerEq)
        (rule.interpretTemplate?_certified elimPayload spineCert allFire
          depth outerTemplate .term outerCert outerEq)
  | depth, .builtGen builtHead payloadSource childTemplates,
      expectedSort, cert, _, interpEq => by
      obtain ⟨sortEq, childrenCert⟩ := cert
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpEq
      obtain ⟨builtPayload, payloadEq, restEq⟩ :=
        optionBindSomeSplit interpEq
      obtain ⟨builtChildren, childrenEq, finalEq⟩ :=
        optionBindSomeSplit restEq
      obtain rfl := Option.some.inj finalEq
      exact sortEq ▸ PolyCell.gen (supportedGenerator builtHead)
        (genPayloadEvidence builtPayload)
        (rule.interpretBuiltChildren?_certified elimPayload spineCert
          allFire depth builtHead.binderShifts builtHead.childSpecs
          (Generator.childSpecs_scopeShifts_eq_binderShifts
            builtHead).symm
          (Generator.childSpecs_cellDimension_zero builtHead)
          childTemplates childrenCert childrenEq)
  | depth, .reassembledReplacing replacements, expectedSort, cert, _,
      interpEq => by
      obtain ⟨sortEq, replacementsCert⟩ := cert
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpEq
      obtain ⟨payloadAtDepth, payloadEq, restEq⟩ :=
        optionBindSomeSplit interpEq
      obtain ⟨replacedSpine, replacedEq, finalEq⟩ :=
        optionBindSomeSplit restEq
      obtain rfl := Option.some.inj finalEq
      exact sortEq ▸ PolyCell.gen
        (supportedGenerator rule.elimGenerator)
        (genPayloadEvidence payloadAtDepth)
        (rule.interpretReplacements?_certified elimPayload spineCert
          allFire depth replacements replacementsCert
          (RawTermChildren.weakenSpineBy depth spine)
          (CertifiedTermSpine.certifiedWeakenSpineBy
            (Generator.childSpecs_cellDimension_zero rule.elimGenerator)
            depth spineCert)
          replacedEq)
  | depth, .substOneIntoSpineChild bodySlot argTemplate, expectedSort,
      cert, _, interpEq => by
      obtain ⟨bodyCert, argCert⟩ := cert
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpEq
      obtain ⟨argTerm, argEq, restEq⟩ := optionBindSomeSplit interpEq
      obtain ⟨bodyChild, bodyLookupEq, restEq2⟩ :=
        optionBindSomeSplit restEq
      obtain ⟨bodyTerm, bodyShiftEq, finalEq⟩ :=
        optionBindSomeSplit restEq2
      obtain rfl := Option.some.inj finalEq
      have composedBodyEq :
          (scopedChildAt? spine.toScopedChildren bodySlot).bind
            ScopedChild.atShiftOne? = some bodyTerm := by
        rw [bodyLookupEq]
        exact bodyShiftEq
      obtain ⟨bodySpec, bodySpecLookupEq, bodyCell⟩ :=
        spineCert.certifiedAtShiftOne
          (Generator.childSpecs_cellDimension_zero rule.elimGenerator)
          bodySlot composedBodyEq
      rw [bodySpecLookupEq] at bodyCert
      have sortEq : bodySpec.cellSort = expectedSort := bodyCert
      exact sortEq ▸ PolyCell.subst0_dim0
        (PolyCell.weakenBodyUnderOneBinderBy_dim0 depth bodyCell)
        (rule.interpretTemplate?_certified elimPayload spineCert allFire
          depth argTemplate .term argCert argEq)
  | depth, .substOneIntoScrutineeChild scrutineeIndex bodySlot
      argTemplate, expectedSort, cert, _, interpEq => by
      obtain ⟨bodyCert, argCert⟩ := cert
      dsimp only [IotaRuleDesc.interpretTemplate?,
        IotaRuleDesc.scrutineeChildrenAt?] at interpEq
      obtain ⟨argTerm, argEq, restEq⟩ := optionBindSomeSplit interpEq
      obtain ⟨scrutineeChildrenView, childrenViewEq, restEq2⟩ :=
        optionBindSomeSplit restEq
      obtain ⟨bodyChild, bodyLookupEq, restEq3⟩ :=
        optionBindSomeSplit restEq2
      obtain ⟨bodyTerm, bodyShiftEq, finalEq⟩ :=
        optionBindSomeSplit restEq3
      obtain rfl := Option.some.inj finalEq
      obtain ⟨scrutineeTerm, scrutineeTermEq, viewEq⟩ :=
        optionMapSomeSplit childrenViewEq
      have scrutineeTermBindEq :
          (rule.scrutineeSpecAt? scrutineeIndex).bind
            (fun spec =>
              (scopedChildAt? spine.toScopedChildren spec.slot).bind
                ScopedChild.atShiftZero?) = some scrutineeTerm :=
        scrutineeTermEq
      obtain ⟨scrutineeSpec, specAtEq, composedScrutineeEq⟩ :=
        optionBindSomeSplit scrutineeTermBindEq
      obtain ⟨spineSpec, spineSpecLookupEq, scrutineeCell⟩ :=
        spineCert.certifiedAtShiftZero
          (Generator.childSpecs_cellDimension_zero rule.elimGenerator)
          scrutineeSpec.slot composedScrutineeEq
      cases scrutineeTerm with
      | mkGen scrutineeGenerator scrutineePayload scrutineeChildrenRaw =>
        have specFires := rule.scrutineeSpecFires_ofIndex rule.scrutinees
          scrutineeIndex allFire specAtEq
        have isDeclaredHead : scrutineeGenerator = scrutineeSpec.head :=
          rule.scrutineeSpecFires_extractsHead specFires
            composedScrutineeEq
        subst isDeclaredHead
        have scrutineeSpineCert :=
          PolyCell.invertGenAtDim0 spineSpec.cellSort scrutineeCell
        have composedBodyEq :
            (scopedChildAt? scrutineeChildrenRaw.toScopedChildren
                bodySlot).bind ScopedChild.atShiftOne? = some bodyTerm := by
          rw [show scrutineeChildrenRaw.toScopedChildren
                = scrutineeChildrenView from viewEq]
          rw [bodyLookupEq]
          exact bodyShiftEq
        obtain ⟨bodySpec, bodySpecLookupEq, bodyCell⟩ :=
          scrutineeSpineCert.certifiedAtShiftOne
            (Generator.childSpecs_cellDimension_zero scrutineeSpec.head)
            bodySlot composedBodyEq
        rw [specAtEq] at bodyCert
        have bodyCertAtSlot :
            (match listEntryAt? scrutineeSpec.head.childSpecs bodySlot with
              | none => False
              | some matchedSpec =>
                  matchedSpec.cellSort = expectedSort) := bodyCert
        rw [bodySpecLookupEq] at bodyCertAtSlot
        have sortEq : bodySpec.cellSort = expectedSort := bodyCertAtSlot
        exact sortEq ▸ PolyCell.subst0_dim0
          (PolyCell.weakenBodyUnderOneBinderBy_dim0 depth bodyCell)
          (rule.interpretTemplate?_certified elimPayload spineCert
            allFire depth argTemplate .term argCert argEq)
  | depth, .substPairIntoSpineChild bodySlot innerTemplate outerTemplate,
      expectedSort, cert, _, interpEq => by
      obtain ⟨bodyCert, innerCert, outerCert⟩ := cert
      dsimp only [IotaRuleDesc.interpretTemplate?] at interpEq
      obtain ⟨innerTerm, innerEq, restEq⟩ := optionBindSomeSplit interpEq
      obtain ⟨outerTerm, outerEq, restEq2⟩ := optionBindSomeSplit restEq
      obtain ⟨bodyChild, bodyLookupEq, restEq3⟩ :=
        optionBindSomeSplit restEq2
      obtain ⟨bodyTerm, bodyShiftEq, finalEq⟩ :=
        optionBindSomeSplit restEq3
      obtain rfl := Option.some.inj finalEq
      have composedBodyEq :
          (scopedChildAt? spine.toScopedChildren bodySlot).bind
            ScopedChild.atShiftTwo? = some bodyTerm := by
        rw [bodyLookupEq]
        exact bodyShiftEq
      obtain ⟨bodySpec, bodySpecLookupEq, bodyCell⟩ :=
        spineCert.certifiedAtShiftTwo
          (Generator.childSpecs_cellDimension_zero rule.elimGenerator)
          bodySlot composedBodyEq
      rw [bodySpecLookupEq] at bodyCert
      have sortEq : bodySpec.cellSort = expectedSort := bodyCert
      exact sortEq ▸ PolyCell.substPair_dim0
        (PolyCell.weakenBodyUnderTwoBindersBy_dim0 depth bodyCell)
        (rule.interpretTemplate?_certified elimPayload spineCert allFire
          depth innerTemplate .term innerCert innerEq)
        (rule.interpretTemplate?_certified elimPayload spineCert allFire
          depth outerTemplate .term outerCert outerEq)
  | depth, .substPairIntoScrutineeChild scrutineeIndex bodySlot
      innerTemplate outerTemplate, expectedSort, cert, _, interpEq => by
      obtain ⟨bodyCert, innerCert, outerCert⟩ := cert
      dsimp only [IotaRuleDesc.interpretTemplate?,
        IotaRuleDesc.scrutineeChildrenAt?] at interpEq
      obtain ⟨innerTerm, innerEq, restEq⟩ := optionBindSomeSplit interpEq
      obtain ⟨outerTerm, outerEq, restEq2⟩ := optionBindSomeSplit restEq
      obtain ⟨scrutineeChildrenView, childrenViewEq, restEq3⟩ :=
        optionBindSomeSplit restEq2
      obtain ⟨bodyChild, bodyLookupEq, restEq4⟩ :=
        optionBindSomeSplit restEq3
      obtain ⟨bodyTerm, bodyShiftEq, finalEq⟩ :=
        optionBindSomeSplit restEq4
      obtain rfl := Option.some.inj finalEq
      obtain ⟨scrutineeTerm, scrutineeTermEq, viewEq⟩ :=
        optionMapSomeSplit childrenViewEq
      have scrutineeTermBindEq :
          (rule.scrutineeSpecAt? scrutineeIndex).bind
            (fun spec =>
              (scopedChildAt? spine.toScopedChildren spec.slot).bind
                ScopedChild.atShiftZero?) = some scrutineeTerm :=
        scrutineeTermEq
      obtain ⟨scrutineeSpec, specAtEq, composedScrutineeEq⟩ :=
        optionBindSomeSplit scrutineeTermBindEq
      obtain ⟨spineSpec, spineSpecLookupEq, scrutineeCell⟩ :=
        spineCert.certifiedAtShiftZero
          (Generator.childSpecs_cellDimension_zero rule.elimGenerator)
          scrutineeSpec.slot composedScrutineeEq
      cases scrutineeTerm with
      | mkGen scrutineeGenerator scrutineePayload scrutineeChildrenRaw =>
        have specFires := rule.scrutineeSpecFires_ofIndex rule.scrutinees
          scrutineeIndex allFire specAtEq
        have isDeclaredHead : scrutineeGenerator = scrutineeSpec.head :=
          rule.scrutineeSpecFires_extractsHead specFires
            composedScrutineeEq
        subst isDeclaredHead
        have scrutineeSpineCert :=
          PolyCell.invertGenAtDim0 spineSpec.cellSort scrutineeCell
        have composedBodyEq :
            (scopedChildAt? scrutineeChildrenRaw.toScopedChildren
                bodySlot).bind ScopedChild.atShiftTwo? = some bodyTerm := by
          rw [show scrutineeChildrenRaw.toScopedChildren
                = scrutineeChildrenView from viewEq]
          rw [bodyLookupEq]
          exact bodyShiftEq
        obtain ⟨bodySpec, bodySpecLookupEq, bodyCell⟩ :=
          scrutineeSpineCert.certifiedAtShiftTwo
            (Generator.childSpecs_cellDimension_zero scrutineeSpec.head)
            bodySlot composedBodyEq
        rw [specAtEq] at bodyCert
        have bodyCertAtSlot :
            (match listEntryAt? scrutineeSpec.head.childSpecs bodySlot with
              | none => False
              | some matchedSpec =>
                  matchedSpec.cellSort = expectedSort) := bodyCert
        rw [bodySpecLookupEq] at bodyCertAtSlot
        have sortEq : bodySpec.cellSort = expectedSort := bodyCertAtSlot
        exact sortEq ▸ PolyCell.substPair_dim0
          (PolyCell.weakenBodyUnderTwoBindersBy_dim0 depth bodyCell)
          (rule.interpretTemplate?_certified elimPayload spineCert
            allFire depth innerTemplate .term innerCert innerEq)
          (rule.interpretTemplate?_certified elimPayload spineCert
            allFire depth outerTemplate .term outerCert outerEq)

/-- Spine companion: `builtGen` children assemble into a certified
spine, in lockstep with the built head's specs. -/
def IotaRuleDesc.interpretBuiltChildren?_certified (rule : IotaRuleDesc)
    {profile : PolyProfile} {scope : Nat}
    (elimPayload : rule.elimGenerator.payload scope)
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spineCert :
      CertifiedTermSpine profile rule.elimGenerator.childSpecs scope
        rule.elimGenerator.binderShifts spine)
    (allFire : rule.scrutineesFire spine rule.scrutinees = true) :
    (depth : Nat) → (childShifts : List Nat) →
    (childSpecs : List ChildSpec) →
    (lockstepEq : childShifts = childSpecs.map ChildSpec.scopeShift) →
    (allSpecsAreDim0 : ∀ spec ∈ childSpecs, spec.cellDimension = 0) →
    (childTemplates : ReductTemplateSpine) →
    childTemplates.CertifyAgainstSpecs rule childSpecs →
    {builtChildren : RawTermChildren childShifts (scope + depth)} →
    rule.interpretBuiltChildren? elimPayload spine depth childShifts
        childTemplates
      = some builtChildren →
    CertifiedTermSpine profile childSpecs (scope + depth) childShifts
      builtChildren
  | depth, [], [], _, _, .spineNil, _, _, interpEq => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpEq
      obtain rfl := Option.some.inj interpEq
      exact CertifiedTermSpine.nil
  | _, [], [], _, _, .spineCons _ _, _, _, interpEq => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpEq
      injection interpEq
  | _, [], _ :: _, lockstepEq, _, _, _, _, _ => by injection lockstepEq
  | _, _ :: _, [], lockstepEq, _, _, _, _, _ => by injection lockstepEq
  | _, _ :: _, _ :: _, _, _, .spineNil, _, _, interpEq => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpEq
      injection interpEq
  | depth, 0 :: restShifts, headSpec :: restSpecs, lockstepEq,
      allSpecsAreDim0, .spineCons childTemplate restTemplates,
      templatesCert, _, interpEq => by
      obtain ⟨headCert, restCert⟩ := templatesCert
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpEq
      obtain ⟨childTerm, childEq, restEq⟩ := optionBindSomeSplit interpEq
      obtain ⟨restChildren, restChildrenEq, finalEq⟩ :=
        optionBindSomeSplit restEq
      obtain rfl := Option.some.inj finalEq
      obtain ⟨headSort, headDim, headShift⟩ := headSpec
      injection lockstepEq with headShiftEq restLockstepEq
      subst headShiftEq
      obtain ⟨headBoundary, headCellAtDim⟩ :=
        PolyCell.ofDim0 _ (allSpecsAreDim0 _ (.head _))
          (rule.interpretTemplate?_certified elimPayload spineCert
            allFire depth childTemplate headSort headCert childEq)
      exact CertifiedTermSpine.cons headCellAtDim
        (rule.interpretBuiltChildren?_certified elimPayload spineCert
          allFire depth restShifts restSpecs restLockstepEq
          (fun spec specIsMember =>
            allSpecsAreDim0 spec (.tail _ specIsMember))
          restTemplates restCert restChildrenEq)
  | depth, 1 :: restShifts, headSpec :: restSpecs, lockstepEq,
      allSpecsAreDim0, .spineCons childTemplate restTemplates,
      templatesCert, _, interpEq => by
      obtain ⟨headCert, restCert⟩ := templatesCert
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpEq
      obtain ⟨childTerm, childEq, restEq⟩ := optionBindSomeSplit interpEq
      obtain ⟨restChildren, restChildrenEq, finalEq⟩ :=
        optionBindSomeSplit restEq
      obtain rfl := Option.some.inj finalEq
      obtain ⟨headSort, headDim, headShift⟩ := headSpec
      injection lockstepEq with headShiftEq restLockstepEq
      subst headShiftEq
      obtain ⟨headBoundary, headCellAtDim⟩ :=
        PolyCell.ofDim0 _ (allSpecsAreDim0 _ (.head _))
          (rule.interpretTemplate?_certified elimPayload spineCert
            allFire (depth + 1) childTemplate headSort headCert childEq)
      exact CertifiedTermSpine.cons headCellAtDim
        (rule.interpretBuiltChildren?_certified elimPayload spineCert
          allFire depth restShifts restSpecs restLockstepEq
          (fun spec specIsMember =>
            allSpecsAreDim0 spec (.tail _ specIsMember))
          restTemplates restCert restChildrenEq)
  | depth, 2 :: restShifts, headSpec :: restSpecs, lockstepEq,
      allSpecsAreDim0, .spineCons childTemplate restTemplates,
      templatesCert, _, interpEq => by
      obtain ⟨headCert, restCert⟩ := templatesCert
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpEq
      obtain ⟨childTerm, childEq, restEq⟩ := optionBindSomeSplit interpEq
      obtain ⟨restChildren, restChildrenEq, finalEq⟩ :=
        optionBindSomeSplit restEq
      obtain rfl := Option.some.inj finalEq
      obtain ⟨headSort, headDim, headShift⟩ := headSpec
      injection lockstepEq with headShiftEq restLockstepEq
      subst headShiftEq
      obtain ⟨headBoundary, headCellAtDim⟩ :=
        PolyCell.ofDim0 _ (allSpecsAreDim0 _ (.head _))
          (rule.interpretTemplate?_certified elimPayload spineCert
            allFire (depth + 2) childTemplate headSort headCert childEq)
      exact CertifiedTermSpine.cons headCellAtDim
        (rule.interpretBuiltChildren?_certified elimPayload spineCert
          allFire depth restShifts restSpecs restLockstepEq
          (fun spec specIsMember =>
            allSpecsAreDim0 spec (.tail _ specIsMember))
          restTemplates restCert restChildrenEq)
  | _, (_ + 3) :: _, _ :: _, _, _, .spineCons _ _, _, _, interpEq => by
      dsimp only [IotaRuleDesc.interpretBuiltChildren?] at interpEq
      injection interpEq

/-- Replacements companion: the reassembly fold keeps the spine
certified, slot by slot. -/
def IotaRuleDesc.interpretReplacements?_certified (rule : IotaRuleDesc)
    {profile : PolyProfile} {scope : Nat}
    (elimPayload : rule.elimGenerator.payload scope)
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    (spineCert :
      CertifiedTermSpine profile rule.elimGenerator.childSpecs scope
        rule.elimGenerator.binderShifts spine)
    (allFire : rule.scrutineesFire spine rule.scrutinees = true) :
    (depth : Nat) → (replacements : SpineReplacements) →
    replacements.CertifyReplacementSorts rule →
    (reassemblySpine :
      RawTermChildren rule.elimGenerator.binderShifts (scope + depth)) →
    (reassemblyCert :
      CertifiedTermSpine profile rule.elimGenerator.childSpecs
        (scope + depth) rule.elimGenerator.binderShifts
        reassemblySpine) →
    {replacedSpine :
      RawTermChildren rule.elimGenerator.binderShifts (scope + depth)} →
    rule.interpretReplacements? elimPayload spine depth replacements
        reassemblySpine
      = some replacedSpine →
    CertifiedTermSpine profile rule.elimGenerator.childSpecs
      (scope + depth) rule.elimGenerator.binderShifts replacedSpine
  | depth, .replaceNil, _, reassemblySpine, reassemblyCert, _,
      interpEq => by
      dsimp only [IotaRuleDesc.interpretReplacements?] at interpEq
      obtain rfl := Option.some.inj interpEq
      exact reassemblyCert
  | depth, .replaceCons slot replacementTemplate restReplacements,
      replacementsCert, reassemblySpine, reassemblyCert, _, interpEq => by
      obtain ⟨slotCert, restCert⟩ := replacementsCert
      dsimp only [IotaRuleDesc.interpretReplacements?] at interpEq
      obtain ⟨replacement, replacementEq, restEq⟩ :=
        optionBindSomeSplit interpEq
      obtain ⟨onceReplacedSpine, onceReplacedEq, recurseEq⟩ :=
        optionBindSomeSplit restEq
      match slotSpecEq :
          listEntryAt? rule.elimGenerator.childSpecs slot with
      | none =>
          rw [slotSpecEq] at slotCert
          exact slotCert.elim
      | some slotSpec =>
          rw [slotSpecEq] at slotCert
          exact rule.interpretReplacements?_certified elimPayload
            spineCert allFire depth restReplacements restCert
            onceReplacedSpine
            (reassemblyCert.certifiedReplaceChildAt
              (Generator.childSpecs_cellDimension_zero
                rule.elimGenerator)
              slot slotSpecEq
              (rule.interpretTemplate?_certified elimPayload spineCert
                allFire depth replacementTemplate slotSpec.cellSort
                slotCert replacementEq)
              onceReplacedEq)
            recurseEq

end

/-! ## The headline -/

/-- ★ **Generic structural SR for table redexes** — a certified
table-redex source yields a certified reduct, for any row whose target
satisfies the sort discipline.  ONE theorem replacing the seventeen
bespoke `preservedByIota*` arms (and covering every future row for the
price of its certificate). -/
theorem HasCertifiedCellDim0.preservedByTableRedex
    {profile : PolyProfile} {scope : Nat} {rule : IotaRuleDesc}
    (targetIsSortCertified : rule.HasSortCertifiedTarget)
    (elimPayload : rule.elimGenerator.payload scope)
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct)
    (sourceCert : HasCertifiedCellDim0 (profile := profile)
      (.mkGen rule.elimGenerator elimPayload spine)) :
    HasCertifiedCellDim0 (profile := profile) reduct := by
  obtain ⟨sourceSort, sourceCell⟩ := sourceCert
  obtain ⟨targetSort, targetCertifies⟩ := targetIsSortCertified
  have allFire := rule.firesOn?_some_scrutineesFire fires
  have interpEq : rule.interpretTarget? elimPayload spine = some reduct := by
    dsimp only [IotaRuleDesc.firesOn?] at fires
    rw [if_pos allFire] at fires
    exact fires
  exact ⟨targetSort,
    rule.interpretTemplate?_certified elimPayload
      (PolyCell.invertGenAtDim0 sourceSort sourceCell) allFire 0
      rule.target targetSort targetCertifies interpEq⟩

/-! ## The 21 row certificates

Every shipped row's target certifies at the ELIMINATOR'S OWN sort —
the sort-PRESERVING form the congruence machinery needs (a stepped
spine child must re-enter its slot at the slot's sort).  All
eliminator heads and their child specs are term-level, so every tree
closes with `rfl` / `⟨⟩` leaves. -/

/-- The strengthened row certificate: the reduct certifies at the
eliminator's own table sort (so table steps are SORT-preserving). -/
def IotaRuleDesc.HasSortPreservingTarget (rule : IotaRuleDesc) : Prop :=
  rule.target.CertifiesAtSort rule rule.elimGenerator.cellSort

/-- Sort-preserving targets are sort-certified (the existential the
headline consumes). -/
theorem IotaRuleDesc.hasSortCertifiedTarget_ofPreserving
    {rule : IotaRuleDesc}
    (targetPreservesSort : rule.HasSortPreservingTarget) :
    rule.HasSortCertifiedTarget :=
  ⟨rule.elimGenerator.cellSort, targetPreservesSort⟩

theorem betaIotaRow_hasSortPreservingTarget :
    betaIotaRow.HasSortPreservingTarget := ⟨rfl, rfl⟩
theorem boolTrueIotaRow_hasSortPreservingTarget :
    boolTrueIotaRow.HasSortPreservingTarget := rfl
theorem boolFalseIotaRow_hasSortPreservingTarget :
    boolFalseIotaRow.HasSortPreservingTarget := rfl
theorem fstPairIotaRow_hasSortPreservingTarget :
    fstPairIotaRow.HasSortPreservingTarget := rfl
theorem sndPairIotaRow_hasSortPreservingTarget :
    sndPairIotaRow.HasSortPreservingTarget := rfl
theorem natElimZeroIotaRow_hasSortPreservingTarget :
    natElimZeroIotaRow.HasSortPreservingTarget := rfl
theorem natRecZeroIotaRow_hasSortPreservingTarget :
    natRecZeroIotaRow.HasSortPreservingTarget := rfl
theorem natElimSuccIotaRow_hasSortPreservingTarget :
    natElimSuccIotaRow.HasSortPreservingTarget :=
  ⟨rfl, ⟨rfl, ⟨rfl, ⟨⟩⟩⟩, rfl⟩
theorem natRecSuccIotaRow_hasSortPreservingTarget :
    natRecSuccIotaRow.HasSortPreservingTarget :=
  ⟨rfl, ⟨rfl, ⟨rfl, ⟨⟩⟩⟩, rfl⟩
theorem listElimNilIotaRow_hasSortPreservingTarget :
    listElimNilIotaRow.HasSortPreservingTarget := rfl
theorem listElimConsIotaRow_hasSortPreservingTarget :
    listElimConsIotaRow.HasSortPreservingTarget :=
  ⟨rfl,
    ⟨rfl, ⟨rfl, ⟨rfl, rfl, ⟨⟩⟩⟩, rfl, ⟨⟩⟩,
    ⟨rfl, ⟨rfl, ⟨⟩⟩⟩, ⟨⟩⟩
theorem optionMatchNoneIotaRow_hasSortPreservingTarget :
    optionMatchNoneIotaRow.HasSortPreservingTarget := rfl
theorem optionMatchSomeIotaRow_hasSortPreservingTarget :
    optionMatchSomeIotaRow.HasSortPreservingTarget :=
  ⟨rfl, rfl, rfl, ⟨⟩⟩
theorem eitherMatchInlIotaRow_hasSortPreservingTarget :
    eitherMatchInlIotaRow.HasSortPreservingTarget :=
  ⟨rfl, rfl, rfl, ⟨⟩⟩
theorem eitherMatchInrIotaRow_hasSortPreservingTarget :
    eitherMatchInrIotaRow.HasSortPreservingTarget :=
  ⟨rfl, rfl, rfl, ⟨⟩⟩
theorem idJReflIotaRow_hasSortPreservingTarget :
    idJReflIotaRow.HasSortPreservingTarget := rfl
theorem idStrictRecReflIotaRow_hasSortPreservingTarget :
    idStrictRecReflIotaRow.HasSortPreservingTarget := rfl
theorem pathBetaIotaRow_hasSortPreservingTarget :
    pathBetaIotaRow.HasSortPreservingTarget := ⟨rfl, rfl⟩
theorem quotRecMkIotaRow_hasSortPreservingTarget :
    quotRecMkIotaRow.HasSortPreservingTarget := ⟨rfl, rfl, rfl, ⟨⟩⟩
theorem quotElimMkIotaRow_hasSortPreservingTarget :
    quotElimMkIotaRow.HasSortPreservingTarget := ⟨rfl, rfl, rfl, ⟨⟩⟩
theorem truncRecIntroIotaRow_hasSortPreservingTarget :
    truncRecIntroIotaRow.HasSortPreservingTarget := ⟨rfl, rfl, rfl, ⟨⟩⟩

/-- ★ **Sort-precise table-redex preservation** — the generic
replacement for the per-iota `PolyCell.exists_preservedBy*_dim0`
witnesses: the reduct's cell comes back at the SOURCE cell's own sort
(dim-0 cells on a `mkGen` erasure are necessarily at the generator's
table sort, and a sort-preserving target re-certifies there). -/
def PolyCell.preservedByTableRedex_dim0
    {profile : PolyProfile} {scope : Nat} {rule : IotaRuleDesc}
    (targetPreservesSort : rule.HasSortPreservingTarget)
    (elimPayload : rule.elimGenerator.payload scope)
    {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : rule.firesOn? elimPayload spine = some reduct)
    {sort : CellSort}
    (sourceCell :
      PolyCell profile sort 0 scope CellBoundary.trivial
        (.termBase (.mkGen rule.elimGenerator elimPayload spine))) :
    PolyCell profile sort 0 scope CellBoundary.trivial
      (.termBase reduct) := by
  have allFire := rule.firesOn?_some_scrutineesFire fires
  have interpEq : rule.interpretTarget? elimPayload spine = some reduct := by
    dsimp only [IotaRuleDesc.firesOn?] at fires
    rw [if_pos allFire] at fires
    exact fires
  cases sourceCell with
  | gen _ _ sourceSpine =>
      exact rule.interpretTemplate?_certified elimPayload sourceSpine
        allFire 0 rule.target rule.elimGenerator.cellSort
        targetPreservesSort interpEq

/-- Every row of the canonical 21-row table carries its
sort-preserving certificate. -/
theorem iotaRuleTable_hasSortPreservingTargets :
    ∀ rule, rule ∈ iotaRuleTable → rule.HasSortPreservingTarget := by
  intro rule isRow
  cases isRow with
  | head => exact betaIotaRow_hasSortPreservingTarget
  | tail _ isRow => cases isRow with
    | head => exact boolTrueIotaRow_hasSortPreservingTarget
    | tail _ isRow => cases isRow with
      | head => exact boolFalseIotaRow_hasSortPreservingTarget
      | tail _ isRow => cases isRow with
        | head => exact fstPairIotaRow_hasSortPreservingTarget
        | tail _ isRow => cases isRow with
          | head => exact sndPairIotaRow_hasSortPreservingTarget
          | tail _ isRow => cases isRow with
            | head => exact natElimZeroIotaRow_hasSortPreservingTarget
            | tail _ isRow => cases isRow with
              | head => exact natRecZeroIotaRow_hasSortPreservingTarget
              | tail _ isRow => cases isRow with
                | head => exact natElimSuccIotaRow_hasSortPreservingTarget
                | tail _ isRow => cases isRow with
                  | head =>
                      exact natRecSuccIotaRow_hasSortPreservingTarget
                  | tail _ isRow => cases isRow with
                    | head =>
                        exact listElimNilIotaRow_hasSortPreservingTarget
                    | tail _ isRow => cases isRow with
                      | head =>
                          exact
                            listElimConsIotaRow_hasSortPreservingTarget
                      | tail _ isRow => cases isRow with
                        | head =>
                            exact
                              optionMatchNoneIotaRow_hasSortPreservingTarget
                        | tail _ isRow => cases isRow with
                          | head =>
                              exact
                                optionMatchSomeIotaRow_hasSortPreservingTarget
                          | tail _ isRow => cases isRow with
                            | head =>
                                exact
                                  eitherMatchInlIotaRow_hasSortPreservingTarget
                            | tail _ isRow => cases isRow with
                              | head =>
                                  exact
                                    eitherMatchInrIotaRow_hasSortPreservingTarget
                              | tail _ isRow => cases isRow with
                                | head =>
                                    exact
                                      idJReflIotaRow_hasSortPreservingTarget
                                | tail _ isRow => cases isRow with
                                  | head =>
                                      exact
                                        idStrictRecReflIotaRow_hasSortPreservingTarget
                                  | tail _ isRow => cases isRow with
                                    | head =>
                                        exact
                                          pathBetaIotaRow_hasSortPreservingTarget
                                    | tail _ isRow => cases isRow with
                                      | head =>
                                          exact
                                            quotRecMkIotaRow_hasSortPreservingTarget
                                      | tail _ isRow => cases isRow with
                                        | head =>
                                            exact
                                              quotElimMkIotaRow_hasSortPreservingTarget
                                        | tail _ isRow => cases isRow with
                                          | head =>
                                              exact
                                                truncRecIntroIotaRow_hasSortPreservingTarget
                                          | tail _ isRow => cases isRow

end FX1Poly.Core

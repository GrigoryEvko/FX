import FX1Poly.Typed.IotaElimTypedLink

/-! # FX1Poly/Typed/TypedFragmentTableAdequacy — IOTA-T7: the full-table master SR

The IOTA-T1 adequacy says the LEGACY 17-row table relation is the
bespoke `Step`.  The full 21-row `StepTable` is STRICTLY bigger
(endpoint-β has no bespoke constructor) — on raw terms.  This file
proves the typed-fragment collapse: **on Pi-fragment-typed subjects,
the full table relation IS the bespoke `Step`**
(`HasTypeDescPi.tableStepToStep`) — a typed subject is built from
variables, universe codes, formers, λs and applications, none of which
can head or contain a `pathApp` cell, so the endpoint-β row can never
fire inside one.  The proof is ONE mutual induction over the typing
derivation, dispatching each cell head through Bool table checkers
(`tableAvoidsElimHead` pins for `var`/`lam`/`universeCode`,
`tableElimHeadsLackTypingRows` for every former at once) and the
IOTA-T7 app-head dispatch (`iotaRowAtAppIsBeta`) at the single live
redex position.

Corollaries — the SR-U4 master dispatcher extended to the table
relation, the typed leg of the IOTA-T9 canonicality flip:

  * ★★ `HasTypeDescPi.subjectReductionTable` — the UNCONDITIONAL master
    subject reduction over the full 21-row `StepTable`;
  * `HasTypeDescPi.subjectReductionTableStar` — its star closure.

## Zero-axiom verification

A freed-subject inversion on `StepOverTable` (the T6
`invertAtRigidHead` recipe: head extraction via a `congrArg`
match-lambda BEFORE injection), Bool checkers with `rfl` pins +
`listForall_mem`, and mutual structural recursion on the typing
derivation mirroring the unconditional master SR's case structure.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Gated per declaration in
`FX1PolyAudit/AuditIotaElimTypedLink.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core
open FX1Poly.Universe (LevelExpr UniverseFlag)

/-! ## Bool head-rigidity checkers + pins -/

/-- No row of the ι table eliminates this head (Bool form, `rfl`-decided
per head). -/
def tableAvoidsElimHead (generator : Generator) : Bool :=
  listForall
    (fun rule => if rule.elimGenerator = generator then false else true)
    iotaRuleTable

theorem tableAvoidsElimHead_var : tableAvoidsElimHead .gen_var = true := rfl
theorem tableAvoidsElimHead_lam : tableAvoidsElimHead .gen_lam = true := rfl
theorem tableAvoidsElimHead_universeCode :
    tableAvoidsElimHead .gen_universeCode = true := rfl

/-- Membership extraction: an avoided head is no member row's
eliminator. -/
theorem noRowEliminatesAvoidedHead {generator : Generator}
    (avoided : tableAvoidsElimHead generator = true)
    {rule : IotaRuleDesc} (isRow : rule ∈ iotaRuleTable) :
    rule.elimGenerator ≠ generator := by
  intro isHead
  have verdict := listForall_mem iotaRuleTable avoided isRow
  rw [if_pos isHead] at verdict
  exact Bool.noConfusion verdict

/-- Every ι-table eliminator head lacks a FORMATION typing row (Bool,
`rfl`-decided across all 21 rows at once) — eliminators are not
formers. -/
theorem tableElimHeadsLackTypingRows :
    listForall
        (fun rule => (typingRuleDescOf rule.elimGenerator).isNone)
        iotaRuleTable
      = true := rfl

/-- Membership extraction: a member row's eliminator has no formation
typing row. -/
theorem elimRowHeadHasNoTypingRule {rule : IotaRuleDesc}
    (isRow : rule ∈ iotaRuleTable) :
    typingRuleDescOf rule.elimGenerator = none := by
  have verdict := listForall_mem iotaRuleTable
    tableElimHeadsLackTypingRows isRow
  cases typingShape : typingRuleDescOf rule.elimGenerator with
  | none => rfl
  | some typingRule =>
      rw [typingShape] at verdict
      exact Bool.noConfusion verdict

/-! ## The typed-fragment collapse: table steps ARE bespoke steps -/

mutual

/-- ★ **Typed-fragment table adequacy (grown layer)**: a full-table
step out of a Pi-fragment-typed subject is a bespoke `Step`.  The only
live root redex in the fragment is β (the app-head dispatch); every
other typed head is table-rigid, so the step is a congruence converted
child-by-child along the typing premises. -/
theorem HasTypeDescPi.tableStepToStep {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (derivation : HasTypeDescPi profile context subject classifier) :
    ∀ {reduct : RawTerm scope}, StepTable subject reduct →
      Step subject reduct :=
  match derivation with
  | .ofFormation formationTyped => fun tableStep =>
      HasTypeDesc.tableStepToStep formationTyped tableStep
  | .conv _levelExpr _flag typed _converts _reclassifierTyped =>
      fun tableStep => HasTypeDescPi.tableStepToStep typed tableStep
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body
      _domainLevel _codomainLevel _flag domainTyped _codomainTyped
      bodyTyped => fun tableStep => by
      cases tableStep.invertOrCong rfl with
      | inl rowFiring =>
          exfalso
          obtain ⟨rule, isRow, elimPayload, spine, cellEq, _fires⟩ :=
            rowFiring
          exact noRowEliminatesAvoidedHead tableAvoidsElimHead_lam isRow
            (congrArg
              (fun cell => match cell with
                | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
              cellEq)
      | inr congShape =>
          obtain ⟨children', targetEq, childrenStep⟩ := congShape
          subst targetEq
          refine Step.cong .gen_lam () ?_
          cases childrenStep with
          | here _rest domainStep =>
              exact .here _ (HasTypeDescPi.tableStepToStep domainTyped
                domainStep)
          | there _head restStep =>
              cases restStep with
              | here _rest bodyStep =>
                  exact .there _ (.here _
                    (HasTypeDescPi.tableStepToStep bodyTyped bodyStep))
              | there _head nilStep => cases nilStep
  | .piElim functionTyped argumentTyped => fun tableStep => by
      cases tableStep.invertOrCong rfl with
      | inl rowFiring =>
          obtain ⟨rule, isRow, elimPayload, spine, cellEq, fires⟩ :=
            rowFiring
          have ruleIsBeta : rule = betaIotaRow :=
            iotaRowAtAppIsBeta isRow
              (congrArg
                (fun cell => match cell with
                  | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
                cellEq)
          subst ruleIsBeta
          have stepAtRow :=
            betaRowFiringToStep elimPayload fires
          rw [cellEq] at stepAtRow
          exact stepAtRow
      | inr congShape =>
          obtain ⟨children', targetEq, childrenStep⟩ := congShape
          subst targetEq
          refine Step.cong .gen_app () ?_
          cases childrenStep with
          | here _rest functionStep =>
              exact .here _ (HasTypeDescPi.tableStepToStep functionTyped
                functionStep)
          | there _head restStep =>
              cases restStep with
              | here _rest argumentStep =>
                  exact .there _ (.here _
                    (HasTypeDescPi.tableStepToStep argumentTyped
                      argumentStep))
              | there _head nilStep => cases nilStep
  | .genFormationPi _context generator payload children _levels _flag
      _rule isFormation premises => fun tableStep => by
      cases tableStep.invertOrCong rfl with
      | inl rowFiring =>
          exfalso
          obtain ⟨rule, isRow, elimPayload, spine, cellEq, _fires⟩ :=
            rowFiring
          have headsAgree : rule.elimGenerator = generator := congrArg
            (fun cell => match cell with
              | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
            cellEq
          have noTypingRow : typingRuleDescOf generator = none :=
            headsAgree ▸ elimRowHeadHasNoTypingRule isRow
          exact nomatch noTypingRow.symm.trans isFormation
      | inr congShape =>
          obtain ⟨children', targetEq, childrenStep⟩ := congShape
          subst targetEq
          exact Step.cong generator payload
            (DescTelescopePi.tableChildrenStepToStepChildren premises
              childrenStep)

/-- Formation-layer companion: a table step out of a formation-typed
subject is a bespoke `Step` (in fact a congruence — the formation
fragment heads no redex). -/
theorem HasTypeDesc.tableStepToStep {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (derivation : HasTypeDesc profile context subject classifier) :
    ∀ {reduct : RawTerm scope}, StepTable subject reduct →
      Step subject reduct :=
  match derivation with
  | .var _context _index => fun tableStep => by
      cases tableStep.invertOrCong rfl with
      | inl rowFiring =>
          exfalso
          obtain ⟨rule, isRow, elimPayload, spine, cellEq, _fires⟩ :=
            rowFiring
          exact noRowEliminatesAvoidedHead tableAvoidsElimHead_var isRow
            (congrArg
              (fun cell => match cell with
                | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
              cellEq)
      | inr congShape =>
          obtain ⟨children', _targetEq, childrenStep⟩ := congShape
          cases childrenStep
  | .conv _levelExpr _flag typed _converts _reclassifierTyped =>
      fun tableStep => HasTypeDesc.tableStepToStep typed tableStep
  | .universeFormation _context _levelExpr _flag => fun tableStep => by
      cases tableStep.invertOrCong rfl with
      | inl rowFiring =>
          exfalso
          obtain ⟨rule, isRow, elimPayload, spine, cellEq, _fires⟩ :=
            rowFiring
          exact noRowEliminatesAvoidedHead tableAvoidsElimHead_universeCode
            isRow
            (congrArg
              (fun cell => match cell with
                | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
              cellEq)
      | inr congShape =>
          obtain ⟨children', _targetEq, childrenStep⟩ := congShape
          cases childrenStep
  | .genFormation _context generator payload children _levels _flag
      _rule isFormation premises => fun tableStep => by
      cases tableStep.invertOrCong rfl with
      | inl rowFiring =>
          exfalso
          obtain ⟨rule, isRow, elimPayload, spine, cellEq, _fires⟩ :=
            rowFiring
          have headsAgree : rule.elimGenerator = generator := congrArg
            (fun cell => match cell with
              | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
            cellEq
          have noTypingRow : typingRuleDescOf generator = none :=
            headsAgree ▸ elimRowHeadHasNoTypingRule isRow
          exact nomatch noTypingRow.symm.trans isFormation
      | inr congShape =>
          obtain ⟨children', targetEq, childrenStep⟩ := congShape
          subst targetEq
          exact Step.cong generator payload
            (DescTelescope.tableChildrenStepToStepChildren premises
              childrenStep)

/-- Grown-telescope companion: a pointwise table child-step on a typed
premise spine is a bespoke child-step. -/
theorem DescTelescopePi.tableChildrenStepToStepChildren
    {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile context levels flag children) :
    ∀ {children' : RawTermChildren binderShifts baseScope},
      StepOverTableChildren iotaRuleTable children children' →
      StepChildren children children' :=
  match binderShifts, context, levels, flag, children, telescope with
  | _, _, _, _, _, .nil _context _flag => fun childrenStep => by
      cases childrenStep
  | _, _, _, _, _, .cons _context _head _headLevel _restLevels _flag _rest
      headTyped restTyped => fun childrenStep => by
      cases childrenStep with
      | here _rest headStep =>
          exact .here _ (HasTypeDescPi.tableStepToStep headTyped headStep)
      | there _head restStep =>
          exact .there _
            (DescTelescopePi.tableChildrenStepToStepChildren restTyped
              restStep)

/-- Formation-telescope companion. -/
theorem DescTelescope.tableChildrenStepToStepChildren
    {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile context levels flag children) :
    ∀ {children' : RawTermChildren binderShifts baseScope},
      StepOverTableChildren iotaRuleTable children children' →
      StepChildren children children' :=
  match binderShifts, context, levels, flag, children, telescope with
  | _, _, _, _, _, .nil _context _flag => fun childrenStep => by
      cases childrenStep
  | _, _, _, _, _, .cons _context _head _headLevel _restLevels _flag _rest
      headTyped restTyped => fun childrenStep => by
      cases childrenStep with
      | here _rest headStep =>
          exact .here _ (HasTypeDesc.tableStepToStep headTyped headStep)
      | there _head restStep =>
          exact .there _
            (DescTelescope.tableChildrenStepToStepChildren restTyped
              restStep)

end

/-! ## ★★ The master subject reduction over the full table -/

/-- ★★ **The unconditional master subject reduction over the full
21-row table relation** — the SR-U4 dispatcher extended to `StepTable`,
the typed leg of the IOTA-T9 canonicality flip.  The typed-fragment
collapse converts the table step to a bespoke step; the unconditional
master carries the reduct. -/
theorem HasTypeDescPi.subjectReductionTable {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDescPi context)
    {reduct : RawTerm scope} (tableStep : StepTable subject reduct) :
    HasTypeDescPi profile context reduct classifier :=
  HasTypeDescPi.subjectReduction typed wellFormed reduct
    (HasTypeDescPi.tableStepToStep typed tableStep)

/-- The star closure of the full-table master subject reduction. -/
theorem HasTypeDescPi.subjectReductionTableStar {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    {reduct : RawTerm scope}
    (chain : ReflTransClosure (StepTable (scope := scope)) subject reduct) :
    HasTypeDescPi profile context reduct classifier := by
  induction chain with
  | refl _ => exact typed
  | head firstStep _rest inductionHypothesis =>
      exact inductionHypothesis
        (HasTypeDescPi.subjectReductionTable typed wellFormed firstStep)

end FX1Poly.Typed

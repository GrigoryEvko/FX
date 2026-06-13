import FX1Poly.Core.StepTable
import FX1Poly.Core.StepEtaOverTable

/-! # FX1Poly/Core/StepOverBundle — RW-5: the ONE parameterized reduction relation

The keystone of the redex-migration arc.  Before this file the kernel's
operational semantics is presented by THREE relations:

  * `Step` (β + ι) — `tableRedex`/`cong` over `iotaRuleTable`;
  * `StepEtaOverTable etaRuleTable` (raw-tier η) — `etaRedex`/`cong`;
  * `Step.betaEta` — the βιη umbrella stitched at the `StepStar`/`Conv`
    layer.

`StepOverTable` already parameterizes β+ι by an `IotaRuleDesc` table and
`StepEtaOverTable` parameterizes η by an `EtaRuleDesc` table; the two
relations are structurally identical apart from their root arm.  This
file fuses them: a `RuleTableBundle` carries BOTH row-lists, and ONE
relation `StepOver bundle` has a root arm per RULE-KIND —

  * `iotaRedex` — an ι/β row of `bundle.iotaRows` fires (`firesOn?`),
    eliminator-rooted;
  * `etaRedex`  — a RAW-tier η row of `bundle.etaRows` contracts
    (`contractsOn?`), intro-rooted, gated on `requiresTypedFiring = false`
    exactly as `StepEtaOverTable`;
  * `cong`      — the uniform child congruence shared by both.

The arm count is bounded by the number of rule KINDS, not rules: a new
ι/η rule is a new ROW (0 arms); a new rule kind (RW-4 δ) is one new
field + one new arm.  The operational determinism companion —
`RewriteRow.rewriteAtRoot?` over the heterogeneous `rewriteBundle`
(RW-3) — already discharges root-confluence; this file supplies the
relational substrate RW-6 lifts confluence/NbE over.

## The instantiation gate (the no-regression contract)

`StepOver` recovers every existing relation as a one-empty-list
instantiation, so RW-6's generic theorems specialize back with zero new
obligations:

  * `stepOver_iotaOnly_iff_stepOverTable` : `StepOver ⟨T, []⟩ ↔ StepOverTable T`;
  * `stepOver_etaOnly_iff_stepEtaOverTable` : `StepOver ⟨[], etaT⟩ ↔ StepEtaOverTable etaT`
    (raw tier);
  * `step_iff_stepOver_fxIotaBundle` : `Step ↔ StepOver fxIotaBundle`
    (the canonical β+ι relation IS the iota-only bundle), composing the
    above with the shipped `stepOverTable_iff_step`.

`fxBundle := ⟨iotaRuleTable, etaRuleTable⟩` is the genuine βιη relation:
the liveness pins below fire a β redex (via `iotaRedex`) and a function-η
redex (via `etaRedex`) in the SAME `StepOver fxBundle` relation.

## Zero-axiom verification

The mutual block + every transport is structural induction / `rfl`-firing;
no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditStepOverBundle.lean`.
-/

namespace FX1Poly.Core

/-! ## The bundle -/

/-- A bundle of reduction rules: the ι/β rows and the η rows that drive
ONE `StepOver` relation.  Adding a rule KIND (RW-4 δ) extends this with a
defaulted field; adding a rule is adding a ROW to an existing field. -/
structure RuleTableBundle where
  iotaRows : List IotaRuleDesc
  etaRows : List EtaRuleDesc

/-! ## The relation -/

mutual

/-- ★ **THE parameterized single-step reduction relation.**  Root
redexes are firings of `bundle`'s rows — an ι/β row at an eliminator
cell (`iotaRedex`) or a RAW-tier η row at an intro cell (`etaRedex`) —
closed under the uniform child congruence (`cong`).  The arm count is the
number of rule KINDS; rules themselves are table rows. -/
inductive StepOver (bundle : RuleTableBundle) :
    {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
  /-- **An ι/β row fires at the root** — the subject is the row's
      eliminator cell, the reduct is the row's template interpretation. -/
  | iotaRedex {scope : Nat} {rule : IotaRuleDesc}
      (isRow : rule ∈ bundle.iotaRows)
      (elimPayload : rule.elimGenerator.payload scope)
      {spine : RawTermChildren rule.elimGenerator.binderShifts scope}
      {reduct : RawTerm scope}
      (fires : rule.firesOn? elimPayload spine = some reduct) :
      StepOver bundle (.mkGen rule.elimGenerator elimPayload spine) reduct
  /-- **A RAW-tier η row contracts at the root** — the subject is the
      row's intro cell, the reduct is the extracted core.  The
      `requiresTypedFiring = false` gate keeps the typed-only rows
      (mod/glue/unit) out of the raw relation, exactly as
      `StepEtaOverTable`. -/
  | etaRedex {scope : Nat} {rule : EtaRuleDesc}
      (isRow : rule ∈ bundle.etaRows)
      (isRawTier : rule.requiresTypedFiring = false)
      (introPayload : rule.introGenerator.payload scope)
      {introChildren :
        RawTermChildren rule.introGenerator.binderShifts scope}
      {core : RawTerm scope}
      (contracts : rule.contractsOn? introChildren = some core) :
      StepOver bundle
        (.mkGen rule.introGenerator introPayload introChildren) core
  /-- **Uniform congruence under any generator** — the shared arm. -/
  | cong {scope : Nat} (gen : Generator) (payload : gen.payload scope)
      {children children' : RawTermChildren gen.binderShifts scope}
      (childStep : StepOverChildren bundle children children') :
      StepOver bundle (.mkGen gen payload children)
        (.mkGen gen payload children')

/-- A bundle step at some position in a children spine — the mutual
companion to `StepOver.cong`. -/
inductive StepOverChildren (bundle : RuleTableBundle) :
    {parentScope : Nat} → {binderShifts : List Nat} →
    RawTermChildren binderShifts parentScope →
    RawTermChildren binderShifts parentScope → Prop where
  | here {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
      {head head' : RawTerm (parentScope + headShift)}
      (rest : RawTermChildren restShifts parentScope)
      (childStep : StepOver bundle head head') :
      StepOverChildren bundle
        (RawTermChildren.childCons head rest)
        (RawTermChildren.childCons head' rest)
  | there {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
      (head : RawTerm (parentScope + headShift))
      {rest rest' : RawTermChildren restShifts parentScope}
      (restStep : StepOverChildren bundle rest rest') :
      StepOverChildren bundle
        (RawTermChildren.childCons head rest)
        (RawTermChildren.childCons head rest')

end

/-! ## The canonical bundles -/

/-- The iota-only bundle — the canonical β+ι table with no η rows.  The
relation `StepOver fxIotaBundle` is the core `Step` relation (the pin
`step_iff_stepOver_fxIotaBundle`). -/
@[reducible] def fxIotaBundle : RuleTableBundle where
  iotaRows := iotaRuleTable
  etaRows := []

/-- ★ The full kernel bundle — both canonical tables.  `StepOver fxBundle`
is the genuine βιη reduction relation (the liveness pins below fire β via
`iotaRedex` and η via `etaRedex` in this one relation). -/
@[reducible] def fxBundle : RuleTableBundle where
  iotaRows := iotaRuleTable
  etaRows := etaRuleTable

/-! ## Monotonicity (bundle widening) -/

mutual

/-- A step over a bundle is a step over any WIDER bundle — adding rows to
either field only ADDS reduction behaviour. -/
theorem StepOver.monotone {narrowBundle widerBundle : RuleTableBundle}
    (isWiderIota :
      ∀ {rule : IotaRuleDesc}, rule ∈ narrowBundle.iotaRows →
        rule ∈ widerBundle.iotaRows)
    (isWiderEta :
      ∀ {rule : EtaRuleDesc}, rule ∈ narrowBundle.etaRows →
        rule ∈ widerBundle.etaRows)
    {scope : Nat} {source target : RawTerm scope}
    (bundleStep : StepOver narrowBundle source target) :
    StepOver widerBundle source target :=
  match bundleStep with
  | .iotaRedex isRow elimPayload fires =>
      .iotaRedex (isWiderIota isRow) elimPayload fires
  | .etaRedex isRow isRawTier introPayload contracts =>
      .etaRedex (isWiderEta isRow) isRawTier introPayload contracts
  | .cong gen payload childStep =>
      .cong gen payload
        (StepOverChildren.monotone isWiderIota isWiderEta childStep)

/-- Spine companion of `StepOver.monotone`. -/
theorem StepOverChildren.monotone
    {narrowBundle widerBundle : RuleTableBundle}
    (isWiderIota :
      ∀ {rule : IotaRuleDesc}, rule ∈ narrowBundle.iotaRows →
        rule ∈ widerBundle.iotaRows)
    (isWiderEta :
      ∀ {rule : EtaRuleDesc}, rule ∈ narrowBundle.etaRows →
        rule ∈ widerBundle.etaRows)
    {parentScope : Nat} {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (childStep : StepOverChildren narrowBundle children children') :
    StepOverChildren widerBundle children children' :=
  match childStep with
  | .here rest headStep =>
      .here rest (StepOver.monotone isWiderIota isWiderEta headStep)
  | .there head restStep =>
      .there head
        (StepOverChildren.monotone isWiderIota isWiderEta restStep)

end

/-! ## Freed-subject inversion -/

/-- **Bundle-step inversion at a known cell**: a step out of
`.mkGen gen payload children` is an ι/β ROW FIRING, a RAW-tier η ROW
CONTRACTION, or a CHILD CONGRUENCE — freed-subject form so the
derivation cases stay index-clean. -/
theorem StepOver.invertOrCong {bundle : RuleTableBundle}
    {scope : Nat} {source target : RawTerm scope}
    (bundleStep : StepOver bundle source target)
    {gen : Generator} {payload : gen.payload scope}
    {children : RawTermChildren gen.binderShifts scope}
    (sourceShape : source = .mkGen gen payload children) :
    (∃ (rule : IotaRuleDesc) (_ : rule ∈ bundle.iotaRows)
        (elimPayload : rule.elimGenerator.payload scope)
        (spine : RawTermChildren rule.elimGenerator.binderShifts scope),
        RawTerm.mkGen rule.elimGenerator elimPayload spine
            = RawTerm.mkGen gen payload children
        ∧ rule.firesOn? elimPayload spine = some target)
    ∨ (∃ (rule : EtaRuleDesc) (_ : rule ∈ bundle.etaRows)
        (_ : rule.requiresTypedFiring = false)
        (introPayload : rule.introGenerator.payload scope)
        (introChildren :
          RawTermChildren rule.introGenerator.binderShifts scope),
        RawTerm.mkGen rule.introGenerator introPayload introChildren
            = RawTerm.mkGen gen payload children
        ∧ rule.contractsOn? introChildren = some target)
    ∨ (∃ children', target = .mkGen gen payload children'
        ∧ StepOverChildren bundle children children') := by
  cases bundleStep with
  | iotaRedex isRow elimPayload fires =>
      exact Or.inl ⟨_, isRow, elimPayload, _, sourceShape, fires⟩
  | etaRedex isRow isRawTier introPayload contracts =>
      exact Or.inr (Or.inl
        ⟨_, isRow, isRawTier, introPayload, _, sourceShape, contracts⟩)
  | cong congGen congPayload childrenStep =>
      have headsAgree : congGen = gen := congrArg
        (fun cell => match cell with
          | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
        sourceShape
      subst headsAgree
      injection sourceShape with _scopeRefl _genRefl payloadEq childrenEq
      subst payloadEq
      subst childrenEq
      exact Or.inr (Or.inr ⟨_, rfl, childrenStep⟩)

/-! ## Adequacy 1 — the iota-only bundle IS the iota table relation -/

mutual

/-- Forward: an iota-only-bundle step is an `StepOverTable` step (the
`etaRedex` arm is vacuous over the empty η-row list). -/
theorem StepOver.toStepOverTable_iotaOnly {iotaTable : List IotaRuleDesc}
    {scope : Nat} {source target : RawTerm scope}
    (bundleStep :
      StepOver { iotaRows := iotaTable, etaRows := [] } source target) :
    StepOverTable iotaTable source target :=
  match bundleStep with
  | .iotaRedex isRow elimPayload fires => .tableRedex isRow elimPayload fires
  | .etaRedex isRow _ _ _ => nomatch isRow
  | .cong gen payload childStep =>
      .cong gen payload
        (StepOverChildren.toStepOverTableChildren_iotaOnly childStep)

/-- Spine companion of `StepOver.toStepOverTable_iotaOnly`. -/
theorem StepOverChildren.toStepOverTableChildren_iotaOnly
    {iotaTable : List IotaRuleDesc}
    {parentScope : Nat} {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (childStep :
      StepOverChildren { iotaRows := iotaTable, etaRows := [] }
        children children') :
    StepOverTableChildren iotaTable children children' :=
  match childStep with
  | .here rest headStep =>
      .here rest (StepOver.toStepOverTable_iotaOnly headStep)
  | .there head restStep =>
      .there head
        (StepOverChildren.toStepOverTableChildren_iotaOnly restStep)

end

mutual

/-- Backward: an `StepOverTable` step is an iota-only-bundle step. -/
theorem StepOverTable.toStepOver_iotaOnly {iotaTable : List IotaRuleDesc}
    {scope : Nat} {source target : RawTerm scope}
    (tableStep : StepOverTable iotaTable source target) :
    StepOver { iotaRows := iotaTable, etaRows := [] } source target :=
  match tableStep with
  | .tableRedex isRow elimPayload fires => .iotaRedex isRow elimPayload fires
  | .cong gen payload childStep =>
      .cong gen payload
        (StepOverTableChildren.toStepOverChildren_iotaOnly childStep)

/-- Spine companion of `StepOverTable.toStepOver_iotaOnly`. -/
theorem StepOverTableChildren.toStepOverChildren_iotaOnly
    {iotaTable : List IotaRuleDesc}
    {parentScope : Nat} {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (tableChildStep :
      StepOverTableChildren iotaTable children children') :
    StepOverChildren { iotaRows := iotaTable, etaRows := [] }
      children children' :=
  match tableChildStep with
  | .here rest headStep =>
      .here rest (StepOverTable.toStepOver_iotaOnly headStep)
  | .there head restStep =>
      .there head
        (StepOverTableChildren.toStepOverChildren_iotaOnly restStep)

end

/-- ★ The iota-only bundle relation IS the iota-table relation. -/
theorem stepOver_iotaOnly_iff_stepOverTable {iotaTable : List IotaRuleDesc}
    {scope : Nat} {source target : RawTerm scope} :
    StepOver { iotaRows := iotaTable, etaRows := [] } source target
      ↔ StepOverTable iotaTable source target :=
  ⟨StepOver.toStepOverTable_iotaOnly, StepOverTable.toStepOver_iotaOnly⟩

/-! ## Adequacy 2 — the eta-only bundle IS the eta table relation -/

mutual

/-- Forward: an eta-only-bundle step is a `StepEtaOverTable` step (the
`iotaRedex` arm is vacuous over the empty ι-row list). -/
theorem StepOver.toStepEtaOverTable_etaOnly {etaTable : List EtaRuleDesc}
    {scope : Nat} {source target : RawTerm scope}
    (bundleStep :
      StepOver { iotaRows := [], etaRows := etaTable } source target) :
    StepEtaOverTable etaTable source target :=
  match bundleStep with
  | .iotaRedex isRow _ _ => nomatch isRow
  | .etaRedex isRow isRawTier introPayload contracts =>
      .etaRedex isRow isRawTier introPayload contracts
  | .cong gen payload childStep =>
      .cong gen payload
        (StepOverChildren.toStepEtaOverTableChildren_etaOnly childStep)

/-- Spine companion of `StepOver.toStepEtaOverTable_etaOnly`. -/
theorem StepOverChildren.toStepEtaOverTableChildren_etaOnly
    {etaTable : List EtaRuleDesc}
    {parentScope : Nat} {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (childStep :
      StepOverChildren { iotaRows := [], etaRows := etaTable }
        children children') :
    StepEtaOverTableChildren etaTable children children' :=
  match childStep with
  | .here rest headStep =>
      .here rest (StepOver.toStepEtaOverTable_etaOnly headStep)
  | .there head restStep =>
      .there head
        (StepOverChildren.toStepEtaOverTableChildren_etaOnly restStep)

end

mutual

/-- Backward: a `StepEtaOverTable` step is an eta-only-bundle step. -/
theorem StepEtaOverTable.toStepOver_etaOnly {etaTable : List EtaRuleDesc}
    {scope : Nat} {source target : RawTerm scope}
    (etaStep : StepEtaOverTable etaTable source target) :
    StepOver { iotaRows := [], etaRows := etaTable } source target :=
  match etaStep with
  | .etaRedex isRow isRawTier introPayload contracts =>
      .etaRedex isRow isRawTier introPayload contracts
  | .cong gen payload childStep =>
      .cong gen payload
        (StepEtaOverTableChildren.toStepOverChildren_etaOnly childStep)

/-- Spine companion of `StepEtaOverTable.toStepOver_etaOnly`. -/
theorem StepEtaOverTableChildren.toStepOverChildren_etaOnly
    {etaTable : List EtaRuleDesc}
    {parentScope : Nat} {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (etaChildStep :
      StepEtaOverTableChildren etaTable children children') :
    StepOverChildren { iotaRows := [], etaRows := etaTable }
      children children' :=
  match etaChildStep with
  | .here rest headStep =>
      .here rest (StepEtaOverTable.toStepOver_etaOnly headStep)
  | .there head restStep =>
      .there head
        (StepEtaOverTableChildren.toStepOverChildren_etaOnly restStep)

end

/-- ★ The eta-only bundle relation IS the eta-table relation (raw tier). -/
theorem stepOver_etaOnly_iff_stepEtaOverTable {etaTable : List EtaRuleDesc}
    {scope : Nat} {source target : RawTerm scope} :
    StepOver { iotaRows := [], etaRows := etaTable } source target
      ↔ StepEtaOverTable etaTable source target :=
  ⟨StepOver.toStepEtaOverTable_etaOnly, StepEtaOverTable.toStepOver_etaOnly⟩

/-! ## The core-Step pin — `Step` IS the iota-only fxBundle -/

/-- ★ **The canonical β+ι relation IS the iota-only bundle.**  Composes
the iota-only adequacy at `iotaRuleTable` with the shipped
`stepOverTable_iff_step`. -/
theorem step_iff_stepOver_fxIotaBundle {scope : Nat}
    {source target : RawTerm scope} :
    Step source target ↔ StepOver fxIotaBundle source target :=
  ⟨fun step => StepOverTable.toStepOver_iotaOnly (Step.toTableStep step),
   fun bundleStep =>
     StepOverTable.toStep (StepOver.toStepOverTable_iotaOnly bundleStep)⟩

/-! ## Liveness — `fxBundle` is the genuine βιη relation -/

/-- Endpoint-β fires in `StepOver fxBundle` via the `iotaRedex` arm —
the same row that `StepTable.pathBetaFires` fires, now in the unified
βιη relation. -/
theorem StepOver.fxBundlePathBetaFires {scope : Nat}
    (body : RawTerm (scope + 1)) (arg : RawTerm scope) :
    StepOver fxBundle
      (.mkGen .gen_pathApp ()
        (.childCons (.mkGen .gen_pathLam () (.childCons body .childNil))
          (.childCons arg .childNil)))
      (RawTerm.subst0 body arg) :=
  .iotaRedex (rule := pathBetaIotaRow) pathBetaIotaRow_memTable () rfl

/-- ★ Function-η fires in `StepOver fxBundle` via the `etaRedex` arm —
`lam domainAnn (app (weaken f) (var 0)) ↝ f`.  β fires through
`iotaRedex` (above) and η through `etaRedex` in the SAME relation: this
is the βιη fusion the keystone delivers. -/
theorem StepOver.fxBundleEtaLamFires {scope : Nat}
    (domainAnn innerFunction : RawTerm scope) :
    StepOver fxBundle
      (RawTerm.etaLamSource domainAnn innerFunction) innerFunction :=
  .etaRedex (rule := etaLamRow) etaLamRow_memTable rfl ()
    (etaLamRow_contractsOnSource domainAnn innerFunction)

/-- Pair-η also fires in the unified relation (the non-left-linear row). -/
theorem StepOver.fxBundleEtaPairFires {scope : Nat}
    (pairTerm : RawTerm scope) :
    StepOver fxBundle
      (RawTerm.etaPairSource pairTerm) pairTerm :=
  .etaRedex (rule := etaPairRow) etaPairRow_memTable rfl ()
    (etaPairRow_contractsOnSource pairTerm)

end FX1Poly.Core

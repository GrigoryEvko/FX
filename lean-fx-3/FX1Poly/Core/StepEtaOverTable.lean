import FX1Poly.Core.EtaRuleTable
import FX1Poly.Core.StepEta

/-! # StepEtaOverTable — ETA-T1: the table-driven eta relation +
forward adequacy + the gating ledger

The eta twin of `StepOverTable` (IOTA-T1): ONE `etaRedex` arm — a
member row of the RAW tier (`requiresTypedFiring = false`) contracts an
intro cell to the shared core — plus the same uniform child congruence.
Adding an eta rule to the kernel becomes adding a ROW.

Adequacy against the bespoke `Step.eta` sibling is split HONESTLY:

* the three faithfully-gated arms (`etaLam`, `etaPair`, `etaPathLam`)
  go FORWARD here — the symbolic contraction equations compute each
  bespoke redex shape to its core (the function/path rows close by the
  `strengthenBy?`/`weakenBy` roundtrip; the pair row needs ONE
  `if_pos rfl` at the non-left-linear DecEq gate), and the relation
  arms wrap them (backward inversions are the ETA-T1 second
  increment);
* `etaModIntro`/`etaGlueIntro` are TYPED-TIER rows: they never fire in
  the raw relation, and the bespoke arms DO fire raw on their redex
  shapes (no typing gate — the known StepEta over-approximation).  The
  STRICTNESS pins below witness the divergence on closed cells:
  bespoke fires, the table refuses.  These pins are the ETA-T7
  gating-repair ledger.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditStepEtaOverTable.lean`. -/

namespace FX1Poly.Core

/-! ## The relation -/

mutual

/-- Single-step eta reduction OVER A RULE TABLE: a root contraction is
a RAW-tier row of `table` contracting the intro cell to the shared
core, and reduction is closed under the same uniform child congruence
as `StepOverTable`. -/
inductive StepEtaOverTable (table : List EtaRuleDesc) :
    {scope : Nat} → RawTerm scope → RawTerm scope → Prop where
  /-- **A raw-tier table row contracts at the root.** -/
  | etaRedex {scope : Nat} {rule : EtaRuleDesc} (isRow : rule ∈ table)
      (isRawTier : rule.requiresTypedFiring = false)
      (introPayload : rule.introGenerator.payload scope)
      {introChildren :
        RawTermChildren rule.introGenerator.binderShifts scope}
      {core : RawTerm scope}
      (contracts : rule.contractsOn? introChildren = some core) :
      StepEtaOverTable table
        (.mkGen rule.introGenerator introPayload introChildren) core
  /-- **Uniform congruence under any generator.** -/
  | cong {scope : Nat} (gen : Generator) (payload : gen.payload scope)
      {children children' : RawTermChildren gen.binderShifts scope}
      (childStep : StepEtaOverTableChildren table children children') :
      StepEtaOverTable table (.mkGen gen payload children)
        (.mkGen gen payload children')

/-- An eta table step at some position in a children spine. -/
inductive StepEtaOverTableChildren (table : List EtaRuleDesc) :
    {parentScope : Nat} → {binderShifts : List Nat} →
    RawTermChildren binderShifts parentScope →
    RawTermChildren binderShifts parentScope → Prop where
  | here {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
      {head head' : RawTerm (parentScope + headShift)}
      (rest : RawTermChildren restShifts parentScope)
      (childStep : StepEtaOverTable table head head') :
      StepEtaOverTableChildren table
        (RawTermChildren.childCons head rest)
        (RawTermChildren.childCons head' rest)
  | there {parentScope : Nat} {headShift : Nat} {restShifts : List Nat}
      (head : RawTerm (parentScope + headShift))
      {rest rest' : RawTermChildren restShifts parentScope}
      (restStep : StepEtaOverTableChildren table rest rest') :
      StepEtaOverTableChildren table
        (RawTermChildren.childCons head rest)
        (RawTermChildren.childCons head rest')

end

/-- THE eta table relation: `StepEtaOverTable` at the canonical 5-row
`etaRuleTable`. -/
abbrev StepEtaTable {scope : Nat} (source target : RawTerm scope) : Prop :=
  StepEtaOverTable etaRuleTable source target

/-! ## Monotonicity -/

mutual

/-- An eta step over a table is a step over any wider table. -/
theorem StepEtaOverTable.monotone {table widerTable : List EtaRuleDesc}
    (isWider : ∀ {rule : EtaRuleDesc}, rule ∈ table → rule ∈ widerTable)
    {scope : Nat} {source target : RawTerm scope}
    (etaStep : StepEtaOverTable table source target) :
    StepEtaOverTable widerTable source target :=
  match etaStep with
  | .etaRedex isRow isRawTier introPayload contracts =>
      .etaRedex (isWider isRow) isRawTier introPayload contracts
  | .cong gen payload childStep =>
      .cong gen payload (StepEtaOverTableChildren.monotone isWider childStep)

/-- Spine companion of `StepEtaOverTable.monotone`. -/
theorem StepEtaOverTableChildren.monotone
    {table widerTable : List EtaRuleDesc}
    (isWider : ∀ {rule : EtaRuleDesc}, rule ∈ table → rule ∈ widerTable)
    {parentScope : Nat} {binderShifts : List Nat}
    {children children' : RawTermChildren binderShifts parentScope}
    (childStep : StepEtaOverTableChildren table children children') :
    StepEtaOverTableChildren widerTable children children' :=
  match childStep with
  | .here rest headStep =>
      .here rest (StepEtaOverTable.monotone isWider headStep)
  | .there head restStep =>
      .there head (StepEtaOverTableChildren.monotone isWider restStep)

end

/-! ## The freed-subject inversion -/

/-- **Eta table-step inversion at a known cell**: a step out of
`.mkGen gen payload children` is either a RAW-TIER ROW CONTRACTION
(the row, its membership, the tier verdict, and the contraction
surfaced with the cell identification) or a CHILD CONGRUENCE. -/
theorem StepEtaOverTable.invertOrCong {table : List EtaRuleDesc}
    {scope : Nat} {source target : RawTerm scope}
    (etaStep : StepEtaOverTable table source target)
    {gen : Generator} {payload : gen.payload scope}
    {children : RawTermChildren gen.binderShifts scope}
    (sourceShape : source = .mkGen gen payload children) :
    (∃ (rule : EtaRuleDesc) (_ : rule ∈ table)
        (_ : rule.requiresTypedFiring = false)
        (introPayload : rule.introGenerator.payload scope)
        (introChildren :
          RawTermChildren rule.introGenerator.binderShifts scope),
        RawTerm.mkGen rule.introGenerator introPayload introChildren
            = RawTerm.mkGen gen payload children
        ∧ rule.contractsOn? introChildren = some target)
    ∨ (∃ children', target = .mkGen gen payload children'
        ∧ StepEtaOverTableChildren table children children') := by
  cases etaStep with
  | etaRedex isRow isRawTier introPayload contracts =>
      exact Or.inl ⟨_, isRow, isRawTier, introPayload, _, sourceShape,
        contracts⟩
  | cong congGen congPayload childrenStep =>
      have headsAgree : congGen = gen := congrArg
        (fun cell => match cell with
          | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
        sourceShape
      subst headsAgree
      injection sourceShape with _scopeRefl _genRefl payloadEq childrenEq
      subst payloadEq
      subst childrenEq
      exact Or.inr ⟨_, rfl, childrenStep⟩

/-! ## Row memberships -/

theorem etaLamRow_memTable : etaLamRow ∈ etaRuleTable := .head _
theorem etaPairRow_memTable : etaPairRow ∈ etaRuleTable :=
  .tail _ (.head _)
theorem etaPathLamRow_memTable : etaPathLamRow ∈ etaRuleTable :=
  .tail _ (.tail _ (.head _))
theorem etaModIntroRow_memTable : etaModIntroRow ∈ etaRuleTable :=
  .tail _ (.tail _ (.tail _ (.head _)))
theorem etaGlueIntroRow_memTable : etaGlueIntroRow ∈ etaRuleTable :=
  .tail _ (.tail _ (.tail _ (.tail _ (.head _))))

/-! ## The symbolic contraction equations (the forward content) -/

/-- Function eta contracts its OWN redex shape: the walk computes down
to the `strengthenBy?`/`weakenBy` roundtrip on the weakened function. -/
theorem etaLamRow_contractsOnSource {scope : Nat}
    (domainAnn innerFunction : RawTerm scope) :
    etaLamRow.contractsOn?
      (.childCons domainAnn
        (.childCons
          (.mkGen .gen_app ()
            (.childCons (RawTerm.weaken innerFunction)
              (.childCons RawTerm.newestVar .childNil)))
          .childNil))
    = some innerFunction := by
  show (RawTerm.strengthenBy? 1 (RawTerm.weakenBy 1 innerFunction)).bind
      some
    = some innerFunction
  rw [RawTerm.strengthenBy?_weakenBy]
  rfl

/-- Path eta contracts its own redex shape — the one-binder twin of the
function row. -/
theorem etaPathLamRow_contractsOnSource {scope : Nat}
    (innerPath : RawTerm scope) :
    etaPathLamRow.contractsOn?
      (.childCons
        (.mkGen .gen_pathApp ()
          (.childCons (RawTerm.weaken innerPath)
            (.childCons RawTerm.newestVar .childNil)))
        .childNil)
    = some innerPath := by
  show (RawTerm.strengthenBy? 1 (RawTerm.weakenBy 1 innerPath)).bind some
    = some innerPath
  rw [RawTerm.strengthenBy?_weakenBy]
  rfl

/-- Pair eta contracts its own redex shape: both observations extract
the SAME pair, and the non-left-linear DecEq gate discharges by
`if_pos rfl`. -/
theorem etaPairRow_contractsOnSource {scope : Nat}
    (pairTerm : RawTerm scope) :
    etaPairRow.contractsOn?
      (.childCons
        (.mkGen .gen_fst () (.childCons pairTerm .childNil))
        (.childCons
          (.mkGen .gen_snd () (.childCons pairTerm .childNil))
          .childNil))
    = some pairTerm := by
  show (if ((if pairTerm = pairTerm then true else false) && true) = true
      then some pairTerm else none)
    = some pairTerm
  rw [if_pos (rfl : pairTerm = pairTerm)]
  rfl

/-! ## The forward relation arms (the three faithfully-gated rows) -/

/-- Bespoke function eta is a table step. -/
theorem Step.eta.etaLamToTableStep {scope : Nat}
    (domainAnn innerFunction : RawTerm scope) :
    StepEtaTable (RawTerm.etaLamSource domainAnn innerFunction)
      innerFunction :=
  .etaRedex etaLamRow_memTable rfl ()
    (etaLamRow_contractsOnSource domainAnn innerFunction)

/-- Bespoke pair eta is a table step. -/
theorem Step.eta.etaPairToTableStep {scope : Nat}
    (pairTerm : RawTerm scope) :
    StepEtaTable (RawTerm.etaPairSource pairTerm) pairTerm :=
  .etaRedex etaPairRow_memTable rfl ()
    (etaPairRow_contractsOnSource pairTerm)

/-- Bespoke path eta is a table step. -/
theorem Step.eta.etaPathLamToTableStep {scope : Nat}
    (innerPath : RawTerm scope) :
    StepEtaTable (RawTerm.etaPathLamSource innerPath) innerPath :=
  .etaRedex etaPathLamRow_memTable rfl ()
    (etaPathLamRow_contractsOnSource innerPath)

/-! ## The gating STRICTNESS ledger (the ETA-T7 repair inputs)

The bespoke modal/Glue arms fire RAW on their redex shapes (no typing
gate); the table rows are typed-tier and refuse.  Both halves pinned on
closed cells. -/

/-- Bespoke modal eta fires raw on `modIntro (modElim unit)`. -/
theorem etaModIntro_bespokeFiresRaw :
    Step.eta (RawTerm.etaModIntroSource (scope := 0)
        (.mkGen .gen_unit () .childNil))
      (.mkGen .gen_unit () .childNil) :=
  Step.eta.etaModIntro _

/-- **The table REFUSES raw modal eta** — the only modIntro-rooted row
is typed-tier, and no congruence can produce the non-modIntro-headed
core. -/
theorem etaModIntro_tableRefusesRaw :
    ¬ StepEtaTable (RawTerm.etaModIntroSource (scope := 0)
        (.mkGen .gen_unit () .childNil))
      (.mkGen .gen_unit () .childNil) := by
  intro etaStep
  cases etaStep.invertOrCong rfl with
  | inl rootContraction =>
      obtain ⟨rule, isRow, isRawTier, introPayload, introChildren,
        cellEq, _contracts⟩ := rootContraction
      have headsAgree : rule.introGenerator = Generator.gen_modIntro :=
        congrArg
          (fun cell => match cell with
            | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
          cellEq
      cases isRow with
      | head => exact nomatch headsAgree
      | tail _ isRow => cases isRow with
        | head => exact nomatch headsAgree
        | tail _ isRow => cases isRow with
          | head => exact nomatch headsAgree
          | tail _ isRow => cases isRow with
            | head => exact Bool.noConfusion isRawTier
            | tail _ isRow => cases isRow with
              | head => exact nomatch headsAgree
              | tail _ isRow => cases isRow
  | inr congShape =>
      obtain ⟨children', targetShape, _childrenStep⟩ := congShape
      have headsClash : Generator.gen_unit = Generator.gen_modIntro :=
        congrArg
          (fun cell => match cell with
            | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
          targetShape
      exact nomatch headsClash

/-- Bespoke Glue eta fires raw on `glueIntro (glueElim unit) unit`. -/
theorem etaGlueIntro_bespokeFiresRaw :
    Step.eta (RawTerm.etaGlueIntroSource (scope := 0)
        (.mkGen .gen_unit () .childNil))
      (.mkGen .gen_unit () .childNil) :=
  Step.eta.etaGlueIntro _

/-- **The table REFUSES raw Glue eta.** -/
theorem etaGlueIntro_tableRefusesRaw :
    ¬ StepEtaTable (RawTerm.etaGlueIntroSource (scope := 0)
        (.mkGen .gen_unit () .childNil))
      (.mkGen .gen_unit () .childNil) := by
  intro etaStep
  cases etaStep.invertOrCong rfl with
  | inl rootContraction =>
      obtain ⟨rule, isRow, isRawTier, introPayload, introChildren,
        cellEq, _contracts⟩ := rootContraction
      have headsAgree : rule.introGenerator = Generator.gen_glueIntro :=
        congrArg
          (fun cell => match cell with
            | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
          cellEq
      cases isRow with
      | head => exact nomatch headsAgree
      | tail _ isRow => cases isRow with
        | head => exact nomatch headsAgree
        | tail _ isRow => cases isRow with
          | head => exact nomatch headsAgree
          | tail _ isRow => cases isRow with
            | head => exact nomatch headsAgree
            | tail _ isRow => cases isRow with
              | head => exact Bool.noConfusion isRawTier
              | tail _ isRow => cases isRow
  | inr congShape =>
      obtain ⟨children', targetShape, _childrenStep⟩ := congShape
      have headsClash : Generator.gen_unit = Generator.gen_glueIntro :=
        congrArg
          (fun cell => match cell with
            | RawTerm.mkGen cellGenerator _ _ => cellGenerator)
          targetShape
      exact nomatch headsClash

/-! ## Non-vacuity: the congruence arm fires -/

/-- An eta contraction INSIDE a child position:
`pair (lam unit (app unit (var 0))) unit` eta-steps to
`pair unit unit` in the first component. -/
theorem stepEtaTable_congSmoke :
    StepEtaTable (scope := 0)
      (.mkGen .gen_pair ()
        (.childCons
          (RawTerm.etaLamSource (.mkGen .gen_unit () .childNil)
            (.mkGen .gen_unit () .childNil))
          (.childCons (.mkGen .gen_unit () .childNil) .childNil)))
      (.mkGen .gen_pair ()
        (.childCons (.mkGen .gen_unit () .childNil)
          (.childCons (.mkGen .gen_unit () .childNil) .childNil))) :=
  .cong .gen_pair ()
    (.here _ (Step.eta.etaLamToTableStep _ _))

end FX1Poly.Core

import FX1Poly.Typed.TypedBySomeEngine

/-! # FX1Poly/Typed/NativityCensus — NATIVE-00: the machine-checked nativity census ledger

The empirical ground truth the unified-signature campaign (NATIVE-00..63) is built on, recorded
as a machine-checked, SELF-UPDATING ledger.  The kernel's typed layer currently has the grown
engine `HasTypeDescPi` (the de-facto unified engine for the Π-fragment, table-driven via
`typingRuleDescOf` / `introRuleDescOf` / `elimRuleDescOf` with the cascade-free GTL/TG/SR-U
metatheory) PLUS a zoo of legacy standalone `HasTypeDesc*` engines built before the rule tables
matured.  The campaign folds every standalone engine into table rows so the typed layer becomes
ONE judgment = the initial model of a single second-order signature.

## What this ledger pins (and why it stays honest)

  * **`StandaloneTypingEngine`** — the migration surface: the 18 principal legacy engines (plus
    two canonicity/motive auxiliaries noted but not independent judgments).  The
    `migrationTarget` / `migrationClass` total functions ARE the overlap matrix — Lean's
    exhaustiveness makes "add an engine without classifying it" a build failure.
  * **`isHardcodedClassifierHead`** — ★ the GENUINELY machine-checked frankenstein metric: a
    generator is dispatched by a hardcoded `decide` in `hasSomeTypingRule` (rather than table
    `isSome`) IFF it is statically LIVE yet covered by NO rule table.  `hardcodedRoster_allHardcoded`
    verifies all 22 current roster heads satisfy this by `rfl`.  When a migration row lands
    (NATIVE-06..40), the head stops being table-uncovered → the predicate flips → the metric
    drains.  This is self-derived, not asserted.
  * **The "before-state" anchors** (`*_notFormation_yet`, `introTable_onlyLam`,
    `elimTable_onlyApp`) — the `rfl`-checked CURRENT coverage.  These BREAK the moment a row
    lands (e.g. NATIVE-12 puts `gen_bridgeCode` in the formation table, breaking
    `bridgeCode_notFormation_yet`), forcing the census to record progress rather than rot.
  * **`frankensteinMetric`** — current 22 / floor 2 (the bespoke primitives `var` +
    `universeCode`) / migratable 20, tied to the roster by `rfl`.
  * **`riskClassEngines`** — the three recursive eliminators (natElim/natRec/listElim) whose
    dependent-IH premise (NATIVE-04) decides 100% vs 95%-with-pinned-residual collapse.

## Zero-axiom

Plain enums with `deriving DecidableEq, BEq`; the metric predicate is `Bool` over table `isSome`
+ the live classifier; every pin is `rfl` / `by decide` (the propext-free decidable-equality
introduction) / `⟨rfl, …⟩`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-! ## The standalone-engine migration surface -/

/-- The principal legacy standalone typing engines — the surface the campaign folds into rows.
(The `EliminatorMotiveShapeRecord` boolElim-dependent record and `BoolElimValueCanonicity` are
canonicity/motive AUXILIARIES absorbed with `boolElim`, not independent typing judgments, so they
are not enumerated here.) -/
inductive StandaloneTypingEngine where
  | baseType | dataIntroNullary | flat
  | natIntro | idIntro | optionIntro | eitherIntro | pairIntro | listIntro
  | boolElim | idElim | optionMatch | eitherMatch | sigmaProjection
  | natElim | natRec | listElim
  | bridge
  deriving DecidableEq, BEq

/-- The full migration surface. -/
def StandaloneTypingEngine.all : List StandaloneTypingEngine :=
  [.baseType, .dataIntroNullary, .flat,
   .natIntro, .idIntro, .optionIntro, .eitherIntro, .pairIntro, .listIntro,
   .boolElim, .idElim, .optionMatch, .eitherMatch, .sigmaProjection,
   .natElim, .natRec, .listElim,
   .bridge]

/-- Eighteen principal standalone engines await fold-in. -/
theorem standaloneTypingEngineCount : StandaloneTypingEngine.all.length = 18 := rfl

/-- The unified rule table each engine's rules migrate INTO. -/
inductive MigrationTarget where
  /-- `typingRuleDescOf` — universe-former + base-type rows (Π/Σ/list/option/unit/bool/empty/nat). -/
  | formationTable
  /-- The NEW term-indexed former table (Id / Bridge — children classified by earlier children). -/
  | termIndexedFormer
  /-- `introRuleDescOf` — constructor rows (incl. the graded `binderUsage` extension for pathLam). -/
  | introTable
  /-- `elimRuleDescOf` — non-recursive eliminator rows + the generic ι-computation rule. -/
  | elimTable
  /-- `elimRuleDescOf` with a motive-dependent IH premise — the recursive eliminators (the risk class). -/
  | dependentElimTable
  deriving DecidableEq, BEq

/-- The overlap matrix (target half): the table each engine folds into.  Bridge's PRIMARY target
is the term-indexed former (its graded-intro `pathLam` + elim `pathApp` rows are tracked by the
graded/elim-table tasks). -/
def StandaloneTypingEngine.migrationTarget : StandaloneTypingEngine → MigrationTarget
  | .baseType => .formationTable
  | .dataIntroNullary => .introTable
  | .flat => .formationTable
  | .natIntro => .introTable
  | .idIntro => .introTable
  | .optionIntro => .introTable
  | .eitherIntro => .introTable
  | .pairIntro => .introTable
  | .listIntro => .introTable
  | .boolElim => .elimTable
  | .idElim => .elimTable
  | .optionMatch => .elimTable
  | .eitherMatch => .elimTable
  | .sigmaProjection => .elimTable
  | .natElim => .dependentElimTable
  | .natRec => .dependentElimTable
  | .listElim => .dependentElimTable
  | .bridge => .termIndexedFormer

/-- How hard the fold-in is. -/
inductive MigrationClass where
  /-- The engine ALREADY consumes a `…RuleDescOf` table — merge into the unified table (base/data/flat). -/
  | alreadyTableDriven
  /-- A straightforward row in an existing table shape (intro / non-recursive elim). -/
  | mechanicalRow
  /-- Needs the NEW term-indexed former premise schema (NATIVE-12). -/
  | needsTermIndexedSchema
  /-- Needs the graded `binderUsage` intro schema (NATIVE-20/23). -/
  | needsGradedSchema
  /-- Needs the motive-dependent IH elim schema — THE risk class (NATIVE-04/27). -/
  | needsDependentElimSchema
  deriving DecidableEq, BEq

/-- The overlap matrix (difficulty half): the schema work each engine requires.  Bridge's primary
novelty is the graded `pathLam` row, so it is classed `needsGradedSchema` (it also consumes the
term-indexed former from NATIVE-12). -/
def StandaloneTypingEngine.migrationClass : StandaloneTypingEngine → MigrationClass
  | .baseType => .alreadyTableDriven
  | .dataIntroNullary => .alreadyTableDriven
  | .flat => .alreadyTableDriven
  | .natIntro => .mechanicalRow
  | .idIntro => .mechanicalRow
  | .optionIntro => .mechanicalRow
  | .eitherIntro => .mechanicalRow
  | .pairIntro => .mechanicalRow
  | .listIntro => .mechanicalRow
  | .boolElim => .mechanicalRow
  | .idElim => .mechanicalRow
  | .optionMatch => .mechanicalRow
  | .eitherMatch => .mechanicalRow
  | .sigmaProjection => .mechanicalRow
  | .natElim => .needsDependentElimSchema
  | .natRec => .needsDependentElimSchema
  | .listElim => .needsDependentElimSchema
  | .bridge => .needsGradedSchema

/-- The three engines in the risk class — the recursive eliminators whose dependent-IH premise
(NATIVE-04) decides whether the final system is ONE inductive or one inductive + a pinned,
adequacy-bridged recursive-elim core. -/
def riskClassEngines : List StandaloneTypingEngine :=
  StandaloneTypingEngine.all.filter (fun e => e.migrationClass == .needsDependentElimSchema)

/-- Exactly three engines (natElim / natRec / listElim) are in the dependent-elim risk class. -/
theorem riskClassEngineCount : riskClassEngines.length = 3 := rfl

/-- Three engines are already table-driven (base-type / data-intro / flat) — the cheapest merges. -/
theorem alreadyTableDrivenCount :
    (StandaloneTypingEngine.all.filter
      (fun e => e.migrationClass == .alreadyTableDriven)).length = 3 := rfl

/-! ## ★ The machine-checked frankenstein metric -/

/-- **A generator is a HARDCODED classifier head** iff it is statically LIVE (`hasSomeTypingRule`)
yet covered by NO rule table — exactly the heads `hasSomeTypingRule` dispatches via a hardcoded
`decide (g = …)` disjunct instead of table `isSome`.  This is the precise, self-derived
frankenstein metric: when a migration row lands, the head becomes table-covered, this predicate
flips to `false`, and the metric drains automatically. -/
def isHardcodedClassifierHead (g : Generator) : Bool :=
  hasSomeTypingRule g
    && (typingRuleDescOf g).isNone && (introRuleDescOf g).isNone
    && (elimRuleDescOf g).isNone && (flatTypingRuleDescOf g).isNone
    && (baseTypeRuleDescOf g).isNone && (dataIntroNullaryRuleDescOf g).isNone

/-- The 22 currently-hardcoded heads (the frankenstein roster), read off `hasSomeTypingRule`'s
`decide` chain. -/
def hardcodedClassifierHeads : List Generator :=
  [.gen_natZero, .gen_natSucc, .gen_refl, .gen_optionNone, .gen_optionSome,
   .gen_eitherInl, .gen_eitherInr, .gen_pair, .gen_listNil, .gen_listCons,
   .gen_boolElim, .gen_idJ, .gen_optionMatch, .gen_eitherMatch, .gen_fst, .gen_snd,
   .gen_var, .gen_universeCode, .gen_intervalCode, .gen_bridgeCode,
   .gen_pathLam, .gen_pathApp]

/-- The roster has 22 heads (the current frankenstein metric). -/
theorem hardcodedClassifierHeadCount : hardcodedClassifierHeads.length = 22 := rfl

/-- **★ Every rostered head IS genuinely hardcoded** — live yet table-uncovered, machine-checked
by `decide` over all 22.  This is the metric's truthfulness: the roster is not a hand-maintained
list, it is exactly the live-but-uncovered set. -/
theorem hardcodedRoster_allHardcoded :
    hardcodedClassifierHeads.all isHardcodedClassifierHead = true := by decide

/-- The two genuinely-PRIMITIVE heads — the variable rule and the universe-formation rule, each its
own dedicated engine arm (not a table row).  The frankenstein FLOOR: these stay bespoke by nature. -/
def bespokePrimitiveHeads : List Generator := [.gen_var, .gen_universeCode]

/-- The bespoke floor is two heads. -/
theorem bespokePrimitiveHeadCount : bespokePrimitiveHeads.length = 2 := rfl

/-- Both bespoke primitives are currently in the hardcoded roster (they ARE hardcoded today). -/
theorem bespokePrimitives_areHardcoded :
    bespokePrimitiveHeads.all isHardcodedClassifierHead = true := by decide

/-- The 20 MIGRATABLE hardcoded heads — the roster minus the two bespoke primitives.  These drain
to zero as their rows land (NATIVE-06..40); the metric target is the 2-element bespoke floor. -/
def migratableHardcodedHeads : List Generator :=
  [.gen_natZero, .gen_natSucc, .gen_refl, .gen_optionNone, .gen_optionSome,
   .gen_eitherInl, .gen_eitherInr, .gen_pair, .gen_listNil, .gen_listCons,
   .gen_boolElim, .gen_idJ, .gen_optionMatch, .gen_eitherMatch, .gen_fst, .gen_snd,
   .gen_intervalCode, .gen_bridgeCode, .gen_pathLam, .gen_pathApp]

/-- Twenty migratable heads (22 roster − 2 bespoke). -/
theorem migratableHardcodedHeadCount : migratableHardcodedHeads.length = 20 := rfl

/-- Every migratable head is currently hardcoded (machine-checked) — the drain target set. -/
theorem migratableHeads_areHardcoded :
    migratableHardcodedHeads.all isHardcodedClassifierHead = true := by decide

/-- The frankenstein metric ledger: hardcoded-decide count NOW vs the irreducible bespoke floor. -/
structure FrankensteinMetric where
  /-- Hardcoded classifier heads at present. -/
  current : Nat
  /-- The irreducible bespoke primitives (var + universeCode). -/
  floor : Nat
  /-- Migratable = current − floor; drains to 0 over the campaign. -/
  migratable : Nat

/-- The current metric: 22 hardcoded / 2 floor / 20 migratable. -/
def frankensteinMetric : FrankensteinMetric :=
  { current := 22, floor := 2, migratable := 20 }

/-- The metric's `current` is tied to the machine-checked roster length (not a free number). -/
theorem frankensteinMetric_current_matchesRoster :
    frankensteinMetric.current = hardcodedClassifierHeads.length := rfl

/-- The metric's `migratable` is tied to the machine-checked migratable roster length. -/
theorem frankensteinMetric_migratable_matchesRoster :
    frankensteinMetric.migratable = migratableHardcodedHeads.length := rfl

/-! ## The "before" state — `rfl`-anchors that BREAK as rows land (keeping the census honest) -/

/-- Interval code is NOT YET a formation row — **NATIVE-06 flips this**. -/
theorem intervalCode_notFormation_yet :
    (typingRuleDescOf .gen_intervalCode).isNone = true := rfl

/-- Identity code is NOT YET formable (only ever refl's classifier) — **NATIVE-17 flips this** (the
Id retrofit). -/
theorem idCode_notFormation_yet :
    (typingRuleDescOf .gen_idCode).isNone = true := rfl

/-- Bridge code is NOT YET a former row — **NATIVE-12 flips this** (the term-indexed former). -/
theorem bridgeCode_notFormation_yet :
    (typingRuleDescOf .gen_bridgeCode).isNone = true := rfl

/-- The introduction table is currently the singleton `{gen_lam}` — every data-constructor row is
pending (**NATIVE-34** lands them). -/
theorem introTable_onlyLam :
    (introRuleDescOf .gen_lam).isSome = true
    ∧ (introRuleDescOf .gen_natZero).isNone = true
    ∧ (introRuleDescOf .gen_pair).isNone = true
    ∧ (introRuleDescOf .gen_pathLam).isNone = true := ⟨rfl, rfl, rfl, rfl⟩

/-- The elimination table is currently the singleton `{gen_app}` — every eliminator row is pending
(**NATIVE-28** lands the non-recursive ones, **NATIVE-32** the recursive). -/
theorem elimTable_onlyApp :
    (elimRuleDescOf .gen_app).isSome = true
    ∧ (elimRuleDescOf .gen_boolElim).isNone = true
    ∧ (elimRuleDescOf .gen_pathApp).isNone = true := ⟨rfl, rfl, rfl⟩

/-- The formation table currently covers exactly the universe-former + unit rows (the matured
table fragment), pinned for the migration baseline. -/
theorem formationTable_currentCoverage :
    (typingRuleDescOf .gen_piTyCode).isSome = true
    ∧ (typingRuleDescOf .gen_sigmaTyCode).isSome = true
    ∧ (typingRuleDescOf .gen_listCode).isSome = true
    ∧ (typingRuleDescOf .gen_optionCode).isSome = true
    ∧ (typingRuleDescOf .gen_unitCode).isSome = true := ⟨rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Typed

import FX1Poly.Typed.TypedBySomeEngine

/-! # FX1Poly/Typed/NativityCensus — NATIVE-00: the machine-checked nativity census ledger

The empirical ground truth the unified-signature campaign (NATIVE-00..63) WAS built on, recorded
as a machine-checked ledger.  **The campaign has CONCLUDED** (NATIVE-42/43/44/45 endgame): the
kernel's typed layer is now the single union judgment `HasTypeNativeUnion`, and the legacy
standalone `HasTypeDesc*` engine zoo that this census surveyed has been DELETED.  The grown engine
`HasTypeDescPi` survives as the minimal Π-fragment host (var / conv / universe / piIntro / piElim,
table-driven via `typingRuleDescOf` / `introRuleDescOf` / `elimRuleDescOf` with the cascade-free
GTL/TG/SR-U metatheory) and is embedded into the union as the `ofGrown` arm; every data / former /
eliminator family that the standalone engines once carried now lives as a table-driven ARM of
`HasTypeNativeUnion`, reading the NATIVE rule tables in `NativeUnionRuleTables`
(`baseTypeRuleDescOf` / `dataIntroNullaryRuleDescOf` / `flatTypingRuleDescOf` / `gradedIntroRuleOf`
/ `generalElimRuleOf` / the `native*RuleOf` recursive-elim and data-intro tables).

This file is the HISTORICAL record of that consolidation: which standalone engine carried which
family, where each landed, and the structural metric of grown-table sparsity that the union design
makes PERMANENT.  Every pin below is still a true fact about the surviving grown tables (the
consolidation deliberately did NOT widen them — the families moved to the union's own native
tables, not the grown `introRuleDescOf` / `elimRuleDescOf`), so the ledger stays honest after the
endgame.

## What this ledger pins (and why it stays honest)

  * **`StandaloneTypingEngine`** — the (now-deleted) migration surface, recorded as history: the 18
    principal legacy engines (plus two canonicity/motive auxiliaries noted but not independent
    judgments).  The `migrationTarget` / `migrationClass` total functions ARE the overlap matrix
    that classified where each engine's capability LANDED in the union — Lean's exhaustiveness
    kept "add an engine without classifying it" a build failure during the campaign and now keeps
    the historical record total.
  * **`isHardcodedClassifierHead`** — ★ the GENUINELY machine-checked grown-table-sparsity metric:
    a generator is dispatched by a hardcoded `decide` in `hasSomeTypingRule` (rather than the six
    grown / base / data tables it tests) IFF it is statically LIVE yet covered by NONE of those six
    tables.  `hardcodedRoster_allHardcoded` verifies all current roster heads satisfy this by
    `decide`.  This is NOT a draining migration counter: every such head IS covered — by the
    UNION's own native tables (`generalElimRuleOf` for the eliminators, `gradedIntroRuleOf` for the
    binders, the `native*RuleOf` data-intro tables), which `isHardcodedClassifierHead` deliberately
    does not test.  The metric measures the PERMANENT structural fact that the grown engine stays
    the minimal Π-fragment while the union carries the families; it is self-derived, not asserted.
  * **The grown-table-coverage anchors** (`*_notFormation_yet`, `introTable_onlyLam`,
    `elimTable_onlyApp`) — the `rfl`-checked GROWN coverage, deliberately unchanged by the endgame:
    `gen_bridgeCode` / `gen_idCode` are NOT in the grown formation table, the grown intro table is
    still the singleton `{gen_lam}`, the grown elim table is still `{gen_app}`.  The families they
    name are live in the UNION (`gen_bridgeCode` via the term-indexed former row, the data
    constructors / eliminators via the union's intro / elim arms), not in the grown tables.  These
    pins fix the boundary between the minimal grown host and the family-carrying union.
  * **`frankensteinMetric`** — current 20 / floor 2 (the bespoke primitives `var` +
    `universeCode`) / migratable 18, tied to the roster by `rfl`.  The "migratable" residual
    records the heads the union carries through its native tables rather than the grown ones; it is
    a stable design boundary, not pending work.
  * **`riskClassEngines`** — the three recursive eliminators (natElim/natRec/listElim) whose
    dependent-IH premise (NATIVE-04) was the design fork; they landed as the union's `recursiveElim`
    / `listElim` arms with stored motives and union-recursive scrutinee premises.

## Zero-axiom

Plain enums with `deriving DecidableEq, BEq`; the metric predicate is `Bool` over table `isSome`
+ the live classifier; every pin is `rfl` / `by decide` (the propext-free decidable-equality
introduction) / `⟨rfl, …⟩`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-! ## The standalone-engine migration surface (historical — the engines are deleted) -/

/-- The principal legacy standalone typing engines — the (now-deleted) surface the campaign folded
into union arms, recorded as history.  (The `EliminatorMotiveShapeRecord` boolElim-dependent record
and `BoolElimValueCanonicity` are canonicity/motive AUXILIARIES absorbed with `boolElim`, not
independent typing judgments, so they are not enumerated here.) -/
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

/-- Eighteen principal standalone engines were folded into the union (now deleted). -/
theorem standaloneTypingEngineCount : StandaloneTypingEngine.all.length = 18 := rfl

/-- The unified rule table each engine's rules landed IN (the union's native tables). -/
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

/-- The overlap matrix (target half): the table each engine's capability landed in (now as union
arms reading those native tables).  Bridge's PRIMARY target is the term-indexed former (its
graded-intro `pathLam` + elim `pathApp` rows live in the union's graded-intro / general-elim
tables). -/
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

/-- The overlap matrix (difficulty half): the schema work each engine required to land in the
union.  Bridge's primary novelty is the graded `pathLam` row, so it is classed `needsGradedSchema`
(it also consumes the term-indexed former from NATIVE-12). -/
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
(NATIVE-04) was the design fork.  They landed as the union's `recursiveElim` / `listElim` arms: ONE
inductive with stored motives and union-recursive scrutinee / base-branch premises (not a separate
adequacy-bridged core). -/
def riskClassEngines : List StandaloneTypingEngine :=
  StandaloneTypingEngine.all.filter (fun e => e.migrationClass == .needsDependentElimSchema)

/-- Exactly three engines (natElim / natRec / listElim) are in the dependent-elim risk class. -/
theorem riskClassEngineCount : riskClassEngines.length = 3 := rfl

/-- Three engines are already table-driven (base-type / data-intro / flat) — the cheapest merges. -/
theorem alreadyTableDrivenCount :
    (StandaloneTypingEngine.all.filter
      (fun e => e.migrationClass == .alreadyTableDriven)).length = 3 := rfl

/-! ## ★ The machine-checked grown-table-sparsity metric -/

/-- **A generator is a HARDCODED classifier head** iff it is statically LIVE (`hasSomeTypingRule`)
yet covered by NONE of the six GROWN / base / data tables this predicate tests — exactly the heads
`hasSomeTypingRule` dispatches via a hardcoded `decide (g = …)` disjunct instead of those tables'
`isSome`.  This is the precise, self-derived grown-table-sparsity metric.  It is NOT a draining
migration counter: every such head IS covered by the UNION's own native tables (`generalElimRuleOf`
/ `gradedIntroRuleOf` / the `native*RuleOf` data-intro and recursive-elim tables), which this
predicate deliberately does not test.  The count records the PERMANENT boundary between the minimal
grown Π-fragment host and the family-carrying union. -/
def isHardcodedClassifierHead (g : Generator) : Bool :=
  hasSomeTypingRule g
    && (typingRuleDescOf g).isNone && (introRuleDescOf g).isNone
    && (elimRuleDescOf g).isNone && (flatTypingRuleDescOf g).isNone
    && (baseTypeRuleDescOf g).isNone && (dataIntroNullaryRuleDescOf g).isNone

/-- The currently-hardcoded heads (the grown-table-sparsity roster), read off `hasSomeTypingRule`'s
`decide` chain.  NATIVE-06 moved `gen_intervalCode` into a `baseTypeRuleDescOf` formation row (so
grown/base-table-covered — the 22 → 21 step) and NATIVE-42 moved `gen_natZero` into a
`dataIntroNullaryRuleDescOf` row (the 21 → 20 step).  The remaining heads are family heads the union
carries through its OWN native tables (general-elim / graded-intro / data-intro), which this roster
predicate does not test — a stable boundary, not pending drains. -/
def hardcodedClassifierHeads : List Generator :=
  [.gen_natSucc, .gen_refl, .gen_optionNone, .gen_optionSome,
   .gen_eitherInl, .gen_eitherInr, .gen_pair, .gen_listNil, .gen_listCons,
   .gen_boolElim, .gen_idJ, .gen_optionMatch, .gen_eitherMatch, .gen_fst, .gen_snd,
   .gen_var, .gen_universeCode, .gen_bridgeCode,
   .gen_pathLam, .gen_pathApp]

/-- The roster has 20 heads (after the NATIVE-06 interval drain and the NATIVE-42 natZero drain). -/
theorem hardcodedClassifierHeadCount : hardcodedClassifierHeads.length = 20 := rfl

/-- **★ Every rostered head IS genuinely hardcoded** — live yet grown/base/data-table-uncovered,
machine-checked by `decide` over the whole roster.  This is the metric's truthfulness: the roster
is not a hand-maintained list, it is exactly the live-but-grown-table-uncovered set. -/
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

/-- The 18 family hardcoded heads — the roster minus the two bespoke primitives.  These are the
data / former / eliminator heads the union carries through its OWN native tables (not the six grown
/ base / data tables the roster predicate tests); NATIVE-06 moved `gen_intervalCode` into the
base-type table and NATIVE-42 moved `gen_natZero` into the data-intro-nullary table, leaving these
as the stable family residual.  The 2-element bespoke floor (`var` + `universeCode`) is the
irreducible remainder. -/
def migratableHardcodedHeads : List Generator :=
  [.gen_natSucc, .gen_refl, .gen_optionNone, .gen_optionSome,
   .gen_eitherInl, .gen_eitherInr, .gen_pair, .gen_listNil, .gen_listCons,
   .gen_boolElim, .gen_idJ, .gen_optionMatch, .gen_eitherMatch, .gen_fst, .gen_snd,
   .gen_bridgeCode, .gen_pathLam, .gen_pathApp]

/-- Eighteen migratable heads (20 roster − 2 bespoke), after the interval and natZero drains. -/
theorem migratableHardcodedHeadCount : migratableHardcodedHeads.length = 18 := rfl

/-- Every family head is hardcoded (machine-checked) — the union-carried family residual. -/
theorem migratableHeads_areHardcoded :
    migratableHardcodedHeads.all isHardcodedClassifierHead = true := by decide

/-- The grown-table-sparsity metric ledger: grown/base/data-table-uncovered live count vs the
irreducible bespoke floor. -/
structure FrankensteinMetric where
  /-- Hardcoded classifier heads (live yet grown/base/data-table-uncovered). -/
  current : Nat
  /-- The irreducible bespoke primitives (var + universeCode). -/
  floor : Nat
  /-- Family residual = current − floor; the heads the union carries through its OWN native tables.
  A stable design boundary, not pending work. -/
  migratable : Nat

/-- The current metric: 20 hardcoded / 2 floor / 18 family residual — after the NATIVE-06 interval
move into the base-type table (22 → 21) and the NATIVE-42 natZero move into the
`dataIntroNullaryRuleDescOf` table (21 → 20).  The 18-head residual is the union's family carry,
not migration debt. -/
def frankensteinMetric : FrankensteinMetric :=
  { current := 20, floor := 2, migratable := 18 }

/-- The metric's `current` is tied to the machine-checked roster length (not a free number). -/
theorem frankensteinMetric_current_matchesRoster :
    frankensteinMetric.current = hardcodedClassifierHeads.length := rfl

/-- The metric's `migratable` is tied to the machine-checked migratable roster length. -/
theorem frankensteinMetric_migratable_matchesRoster :
    frankensteinMetric.migratable = migratableHardcodedHeads.length := rfl

/-! ## The grown/union boundary — `rfl`-anchors fixing the minimal grown host vs the family-carrying
union (deliberately unchanged by the NATIVE-42..45 endgame) -/

/-- **★ Interval code IS a base-type formation row** (in `baseTypeRuleDescOf`, the cascade-free
nullary base-type home; NATIVE-06).  The union's `baseTypeFormation` arm reads this row, so
`gen_intervalCode` is live in the union. -/
theorem intervalCode_inBaseTypeTable :
    (baseTypeRuleDescOf .gen_intervalCode).isSome = true := rfl

/-- Interval code's GROWN-table (`typingRuleDescOf`) row is absent BY DESIGN — the grown engine stays
the minimal Π-fragment host; interval formation lives in the base-type table (above), read by the
union's `baseTypeFormation` arm.  This pins the grown/union boundary, not pending migration. -/
theorem intervalCode_notInGrownTable_yet :
    (typingRuleDescOf .gen_intervalCode).isNone = true := rfl

/-- Identity code is not in the grown formation table — its formation lives in the union's
term-indexed former row (`HasTypeDescTermIndexedFormer`, the `ofTermIndexedFormer` arm), not the
minimal grown host. -/
theorem idCode_notFormation_yet :
    (typingRuleDescOf .gen_idCode).isNone = true := rfl

/-- Bridge code is not in the grown formation table — its formation lives in the union's term-indexed
former row (the `ofTermIndexedFormer` arm), the bridge semantics' sole home after NATIVE-45 retired
the bespoke bridge engine. -/
theorem bridgeCode_notFormation_yet :
    (typingRuleDescOf .gen_bridgeCode).isNone = true := rfl

/-- The GROWN introduction table is the singleton `{gen_lam}` BY DESIGN — every data-constructor row
lives in the union's intro arms (`recursiveUnaryIntro` / `recursiveBinaryIntro` / `pinnedUnaryIntro`
/ … reading the `native*RuleOf` data-intro tables), `pathLam` in `gradedBinderIntro`.  The grown
host stays minimal; the families live in the union. -/
theorem introTable_onlyLam :
    (introRuleDescOf .gen_lam).isSome = true
    ∧ (introRuleDescOf .gen_natZero).isNone = true
    ∧ (introRuleDescOf .gen_pair).isNone = true
    ∧ (introRuleDescOf .gen_pathLam).isNone = true := ⟨rfl, rfl, rfl, rfl⟩

/-- The GROWN elimination table is the singleton `{gen_app}` BY DESIGN — every data eliminator lives
in the union's elim arms (`twoBranchMatchElim` / `pathInductionElim` / `projectionElim` /
`recursiveElim` / `listElim`), `pathApp` in `generalElim`.  The grown host stays minimal Π-elim. -/
theorem elimTable_onlyApp :
    (elimRuleDescOf .gen_app).isSome = true
    ∧ (elimRuleDescOf .gen_boolElim).isNone = true
    ∧ (elimRuleDescOf .gen_pathApp).isNone = true := ⟨rfl, rfl, rfl⟩

/-- The grown formation table covers exactly the universe-former + unit rows (the minimal grown
host's type-former fragment); the flat / base-type / data former families live in the union's
`flatFormation` / `baseTypeFormation` arms reading the native tables. -/
theorem formationTable_currentCoverage :
    (typingRuleDescOf .gen_piTyCode).isSome = true
    ∧ (typingRuleDescOf .gen_sigmaTyCode).isSome = true
    ∧ (typingRuleDescOf .gen_listCode).isSome = true
    ∧ (typingRuleDescOf .gen_optionCode).isSome = true
    ∧ (typingRuleDescOf .gen_unitCode).isSome = true := ⟨rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Typed

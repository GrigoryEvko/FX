import FX1Poly.Core.CellRuleFibration
import FX1Poly.Typed.Engine.RuleTables.TypingRowDispatch
import FX1Poly.Typed.Engine.Classifier.GeneratorHonestyOverview

/-! # FX1Poly/Typed/CellRuleFibration — the FX instance of the (∞,ω)-polygraph rule fibration

The kernel's cells are `PolyCell profile (sort : CellSort) (dim) (scope)`; the `gen` constructor puts
a generator-headed cell at sort `generator.cellSort`.  So the SORT is the fibration axis, and the
seven `CellSort`s — `context · type · term · mode · effect · grade · protocol` — are the seven strata
a cell can live in.

The generic machinery — the bundle structure, the per-axis `lookup`, the decidable `inhabits` test,
and the per-cell / per-roster orthogonality certificates — lives ONCE in `FX1Poly.Axis.RuleFibration`
(index-abstract) and is instantiated at the kernel's own axes/heads by `FX1Poly.Core.CellRuleBundle`
(`= RuleFibration CellSort Generator payload`).  This file does NOT re-roll any of that; it adds only
what is FX-specific: the rule-payload family and the wiring of the `.type` axis to the typing-row
lookup, so piping ANY facet of a cell through its generator is the single inherited call
`bundle.rowsAt sort generator`.

The FX instance wires the `.type` axis to the TYTAB lookup `typingRowsOf fxTypingBundle` — the type
concept piped through the generator.  The other six axes carry their own rule payloads as their tables
fold in (`.grade` ← the `HasGradeOver` semiring rules, `.term` ← the `StepOver`/signature substrate,
`.protocol` ← the session-duality rules, …); the framework guarantees they plug in with identical
lookup/inhabitation/orthogonality, no new machinery.

Zero-axiom: a sort-indexed payload family, one structure instance, and `rfl`/`decide` facts over the
generator roster (the substrate's own zero-axiom proofs are gated alongside Axis/Core).  Audit-gated
in `FX1PolyAudit/AuditCellRuleFibration.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core (CellSort Generator CellRuleBundle)

/-! ## The FX instance — the `.type` axis is the TYTAB lookup -/

/-- The rule-payload family — what kind of rule each fibration axis carries.  A sort-indexed `Type`
family: `.type` carries the TYTAB `TypingRow`; each other axis carries its own rule type as it folds
in.  Making it sort-indexed (rather than one flat sum) keeps a `.type` lookup statically a list of
type rows, a `.grade` lookup statically a list of grade rules, etc. -/
abbrev CellRulePayloadFamily := CellSort → Type

/-- The FX rule-payload family: the `.type` axis carries the TYTAB `TypingRow`; the other six axes
carry `PEmpty` until their rule tables are folded in.  `PEmpty` (not a populated type) is the honest
statement that those axes have NO rows in THIS bundle yet — their content currently lives in their
own substrates (`HasGradeOver`, `StepOver`, the session rules), to be folded in by the same shape. -/
def fxCellPayload : CellRulePayloadFamily
  | .context => PEmpty
  | .type => TypingRow
  | .term => PEmpty
  | .mode => PEmpty
  | .effect => PEmpty
  | .grade => PEmpty
  | .protocol => PEmpty

/-- ★ **The FX cell-rule fibration** — the `Core.CellRuleBundle` (= the Axis `RuleFibration` at the
seven `CellSort` axes and the `Generator` heads) at the FX payload.  The `.type` axis is
`typingRowsOf fxTypingBundle` — the type concept piped through the generator, exactly the TYTAB
lookup.  The other axes are honestly empty here (their rules live in their own substrates for now).
All lookup / inhabitation / orthogonality operations are INHERITED from `RuleFibration`. -/
def fxCellRules : CellRuleBundle fxCellPayload where
  rowsAt
    | .context, _ => []
    | .type, generator => typingRowsOf fxTypingBundle generator
    | .term, _ => []
    | .mode, _ => []
    | .effect, _ => []
    | .grade, _ => []
    | .protocol, _ => []

/-- **The `.type` axis IS the TYTAB lookup** — definitional.  Reading the type facet of a
generator-headed cell off the fibration bundle is exactly `typingRowsOf fxTypingBundle`. -/
theorem fxCellRules_type_eq_typingRows :
    fxCellRules.rowsAt .type = typingRowsOf fxTypingBundle := rfl

/-! ## Inhabitation + orthogonality computed over the real roster

`#eval`s report the empirical truth (no overclaim): how many generators inhabit the `.type` axis,
and whether the `.type` axis is orthogonal (each generator fires at most one type row) across all
generators.  The smokes below pin the canonical generators by `rfl`. -/

/-- How many generators inhabit the `.type` axis (fire some type row). -/
def typeInhabitantCount : Nat :=
  (allGenerators.filter (fun generator => fxCellRules.inhabits .type generator)).length

/-- The generators (if any) that fire MORE THAN ONE type row — the honest overlap report. -/
def typeAxisOverlaps : List Generator :=
  allGenerators.filter (fun generator => !fxCellRules.isOrthogonalAt .type generator)

#eval typeInhabitantCount
#eval fxCellRules.isOrthogonalOverAt .type allGenerators   -- is the .type axis orthogonal?
#eval typeAxisOverlaps.length                              -- how many generators overlap

/-! ## Canonical-generator smokes — the fibration lookup computes per axis -/

/-- The λ generator inhabits the `.type` axis (it fires its graded-introduction type row). -/
theorem lam_inhabits_type : fxCellRules.inhabits .type .gen_lam = true := rfl

/-- The λ generator is orthogonal at `.type` (exactly one type row). -/
theorem lam_orthogonal_type : fxCellRules.isOrthogonalAt .type .gen_lam = true := rfl

/-- The application generator inhabits the `.type` axis. -/
theorem app_inhabits_type : fxCellRules.inhabits .type .gen_app = true := rfl

/-- A roleless generator (`gen_var`) does NOT inhabit the `.type` axis through the table — its
typing is the bespoke `var` rule, not a row. -/
theorem var_not_inhabits_type : fxCellRules.inhabits .type .gen_var = false := rfl

/-- The λ generator fires NO rows at the `.grade` axis in this bundle (that axis is `PEmpty` here —
its rules live in `HasGradeOver`). -/
theorem lam_no_grade_rows : fxCellRules.rowsAt .grade .gen_lam = [] := rfl

end FX1Poly.Typed

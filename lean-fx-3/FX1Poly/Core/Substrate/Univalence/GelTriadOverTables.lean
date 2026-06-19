import FX1Poly.Core.Substrate.Univalence.GelBetaTableDecidableConv
import FX1Poly.Core.Rewriting.RuleTables.Eta.StrongNormalizationEtaTable
import FX1Poly.Core.Rewriting.RuleTables.Eta.StepEtaTableSubstitution

/-! # FX1Poly/Core/Substrate/Univalence/GelTriadOverTables
    — the TWO computational faces of transpension's Gel, both over tables as data

Transpension at the affine multiplier is the relational `gen_gel` former (Bernardy-Coquand-Moulin /
Cavallo-Harper internal parametricity), and its judgmental equivalence `Gel A B R ≃ R` has TWO halves, each
already a rule-table ROW — this file ties them together honestly:

  * **gel-β (the COMPUTING half, IOTA tier)** — `ungel(gel a b r) ↝ r`, the relation-witness projection, is
    the row `gelBetaIotaRow ∈ iotaRuleTable`.  It is a genuine size-shrinking raw rewrite, so its conversion
    is DECIDABLE BY COMPUTATION over the singleton iota table — shipped as `gelBetaTableConv_decidable`
    (`GelBetaTableDecidableConv`).

  * **gel-η (the RETRACT half, ETA tier)** — a bridge-typed `q : Gel A B R @ i` is definitionally its
    gel-expansion `gel i (q[0/i]) (q[1/i]) (ungel (λj. q))` — is the row `gelEtaRow ∈ etaRuleTable`.  This
    half is irreducibly TYPE-DIRECTED: its LHS references the subject under interval-endpoint substitutions
    `q[0/i]`/`q[1/i]` and a bridge-abstraction `λj. q` — META-substitutions, NOT a first-order left-linear
    pattern over one metavariable.  So `gelEtaRow` has NO observations and `contractsOn?` is constantly
    `none` (doubly gated, exactly like `unitEtaRow`); it NEVER fires raw.  Its genuine computing content is
    the typed-conversion / NbE arc (ETA-T7 / Path-A), not raw rewriting.

So the gel former's RAW decidable conversion is carried ENTIRELY by the iota row; the eta row is a raw-inert
typed-directed table entry, covered for free by the generic eta-table metatheory (`stepEtaOverTable_wellFounded`
SN over any table, scope-safety, orthogonality).  This file records the membership + SN + raw-inertness of the
eta face and states the honest split — no overclaim of "raw decidable Conv" for the type-directed half.

## Zero-axiom verification

`gelEtaRow_memTable` is an explicit `List.Mem` chain; `gelEtaTable_isStronglyNormalizing` is the generic
`StepEtaOverTable.isStronglyNormalizing` (size measure); `gelEtaTable_isScopeSafe` reuses the shipped
`gelEtaRow_isScopeSafe`; the iota-face decidable Conv is the already-audited `gelBetaTableConv_decidable`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated
in `FX1PolyAudit/`.
-/

namespace FX1Poly.Core

/-- The gel-η retract row is the 9th (last) row of the canonical `etaRuleTable` — the typed-directed twin of
the shipped gel-β iota row.  Explicit `List.Mem` chain (8 `.tail` + `.head`), propext-clean. -/
theorem gelEtaRow_memTable : gelEtaRow ∈ etaRuleTable :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))

/-- The gel-η retract row as a SINGLETON eta table — the eta face of the gel triad as data. -/
abbrev gelEtaTable : List EtaRuleDesc := [gelEtaRow]

/-- **The singleton gel-η eta table is strongly normalizing** — every term is accessible under its eta
reduction successor, by the GENERIC eta-table SN (`RawTerm.size` measure, holds for ANY eta table).  Vacuously
strong here: `gelEtaRow` never contracts raw, so the only steps are congruences, all size-decreasing. -/
theorem gelEtaTable_isStronglyNormalizing {scope : Nat} (term : RawTerm scope) :
    Acc (StepEtaOverTable.successorOver gelEtaTable) term :=
  StepEtaOverTable.isStronglyNormalizing gelEtaTable term

/-- Every row of the singleton gel-η table is scope-safe — the one row, via the shipped
`gelEtaRow_isScopeSafe`. -/
theorem gelEtaTable_isScopeSafe :
    ∀ rule, rule ∈ gelEtaTable → rule.IsScopeSafe := by
  intro rule isRow
  cases isRow with
  | head => exact gelEtaRow_isScopeSafe
  | tail _ emptyMem => cases emptyMem

/-- **The eta face is raw-inert.**  `gelEtaRow` contracts on NO spine — its computing content
(`q ↝ gel i q[0/i] q[1/i] (ungel λj.q)`) is type-directed, not a first-order raw pattern.  This is what makes
the gel former's RAW decidable conversion be carried entirely by the iota row `gelBetaTableConv_decidable`. -/
theorem gelEtaTable_rawInert {scope : Nat}
    (children : RawTermChildren Generator.gen_gel.binderShifts scope) :
    gelEtaRow.contractsOn? children = none :=
  gelEtaRow_neverContractsRaw children

/-- **Honesty marker — gel-β (iota) face.**  The COMPUTING half of `Gel A B R ≃ R` ships decidable conversion
BY RAW COMPUTATION over the table, as data (`gelBetaTableConv_decidable`).  `= true`. -/
def fxTranspensionGelIota_decidableConvByComputation : Bool := true

/-- **Honesty marker — gel-η (eta) face.**  The RETRACT half ships as a typed-directed `etaRuleTable` ROW
(`gelEtaRow`, `requiresTypedFiring = true`), covered by the generic eta-table SN + scope-safety with no new
arm.  `= true`. -/
def fxTranspensionGelEta_isTypedDirectedTableRow : Bool := true

/-- **Honesty marker — the deliberate NON-claim.**  Raw computation does NOT decide gel-η conversion: the
retract is type-directed (interval-endpoint + bridge-abstraction meta-substitutions, not a raw pattern), so
`gelEtaRow` is raw-inert and the genuine gel-η identification lives in the typed-conversion / NbE arc
(ETA-T7 / Path-A).  `= false`. -/
def fxTranspensionGelEta_rawConvByComputation : Bool := false

/-- **The gel triad, honestly.**  Transpension's `Gel A B R ≃ R` judgmental equivalence is BOTH faces shipped
over tables as data: the iota/β computing half decides raw conversion by computation, and the eta/retract half
is a typed-directed table row covered by the generic eta-table metatheory.  `= true`. -/
def fxTranspensionGelTriad_shippedOverTablesAsData : Bool := true

end FX1Poly.Core

import FX1Poly.Core.Rewriting.RuleTables.Iota.IotaRuleTable
import FX1Poly.Core.Rewriting.RuleTables.Eta.EtaRuleTable

/-! # FX1Poly/Typed/EqualityTier — the definitionality ledger (the `semanticTier` sibling)

`semanticTier` (`GeneratorSemanticTier.lean`) classifies each of the 205 GENERATORS as `live`/`reserved`.
This module is its sibling for EQUATIONS: it classifies each shipped reduction/expansion ROW by HOW it
reaches (or fails to reach) the definitional floor — and records the residual strength.  It is a
RECOGNITION layer: it adds NO new SN / confluence / subject-reduction proofs, it only reads and NAMES what
the already-shipped certificates prove.

## The three doors to the definitional floor

A propositional equation becomes "free" (discharged by the kernel, no proof at the use site) through one of
three doors:

  * **orient** — the equation is an ORIENTED reduction row (`IotaRuleDesc` in `iotaRuleTable`): `lhs ↝ rhs`
    fires as a raw `Step.tableRedex` by `rfl`.  Confluence is the shipped `WfIotaTable` /
    `iotaRuleTable_isWf` (orthogonality + critical pairs); termination is the shipped RPO measure
    (`RecursivePathOrderInductive` + `IotaSN`); subject reduction is the shipped SR.
  * **expand** — the equation holds by TYPE-DIRECTED η (`EtaRuleDesc` in `etaRuleTable`): an expansion the
    conversion checker performs by consulting the type.  η/β-ι orthogonality is the shipped `WfEtaTable` /
    `etaRuleTable_isWf`.
  * **erase** — the carrier is definitionally IRRELEVANT (grade-0 / ghost): all its inhabitants are equal
    because the distinguishing data is erased.  The shipped grade-0 erasure witness lives in
    `FX1Poly/Dimensions/Graded/GradeErasureGeneric.lean` (the graded `erase` theorem over an
    `OrderedGradeSemiring`).  It is CITED here, not re-derived.

## The residual tiers

  * **definitional** — `rfl`: the contraction fires raw on its SN-covered fragment (every `iotaRuleTable`
    row; the RAW η rows `lam`/`pair`/`pathLam`).
  * **typedDirected** — fires only through the typed conversion checker (the `requiresTypedFiring := true`
    η rows: `modIntro`/`glueIntro`/`unit`/`recordIntro`/`refineIntro`/`gel`).  For some (e.g. `gel`-η) the
    `Conv`-content is the deferred NbE arc — exactly why they are typed-directed, not definitional.
  * **propositional** — the residue: proven by a term/tactic with transport at the use site.  NO shipped
    row sits here; it is the tier of equations OUTSIDE the tables (open-term univalence, the word-problem
    residue).  `noShippedIotaRowIsPropositional` / `noShippedEtaRowIsPropositional` pin that the tables hold
    none.

## Honest rails (the `:= false` markers below are REAL limits, not placeholders)

  * The row-level tier `definitional` means "this row's contraction is a raw `rfl`-step on the fragment its
    SN/confluence cert covers" — it does NOT claim GLOBAL definitional `Conv` (raw β is not globally SN:
    `gen_natRec`/`gen_fixedPoint` are partial-class).  `fxEqualityTier_claimsGlobalDefinitionalConv := false`.
  * The `erase` door's STRICT-prop instance (`gen_sprop` / `SProp`) is PLANNED, not shipped; only the
    grade-0/usage-0 erasure is shipped.  `fxEqualityTier_hasSPropEraseInstance := false`.

## Zero-axiom

Two 3-constructor inductives with `DecidableEq`; classifiers are `if`-over-`Bool` or constant; every witness
`rfl`; the discriminator is `rw` + `noConfusion` (no `decide` on `Ne`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEqualityTier.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-! ## The taxonomy -/

/-- How an equation reaches the definitional floor: an oriented reduction row (`orient`), a type-directed
η-expansion (`expand`), or grade-0 / irrelevance erasure (`erase`). -/
inductive EqualityDoor where
  | orient
  | expand
  | erase
  deriving DecidableEq

/-- The residual strength of an equation — what the kernel discharges for free: `definitional` (raw `rfl`
on its SN-covered fragment), `typedDirected` (fires only through the typed conversion checker), or
`propositional` (the residue, proven by term/tactic with transport at the use site). -/
inductive EqualityTier where
  | definitional
  | typedDirected
  | propositional
  deriving DecidableEq

/-! ## The iota classifier — oriented reduction rows -/

/-- Every `iotaRuleTable` row reaches the floor through the `orient` door: it is an oriented `lhs ↝ rhs`
reduction firing as a raw `Step.tableRedex`. -/
def iotaRowDoor (_ : IotaRuleDesc) : EqualityDoor := .orient

/-- Every `iotaRuleTable` row's contraction is `definitional` — a raw `rfl`-step on its SN-covered fragment.
(This is the ROW-LEVEL tier; it does NOT assert global definitional `Conv` — see
`fxEqualityTier_claimsGlobalDefinitionalConv`.) -/
def iotaRowTier (_ : IotaRuleDesc) : EqualityTier := .definitional

/-- Bool predicate: does this iota row classify `propositional`?  Always `false` — no shipped iota row is
propositional. -/
def iotaRowIsPropositional (_ : IotaRuleDesc) : Bool := false

/-! ## The eta classifier — type-directed expansions -/

/-- Every `etaRuleTable` row reaches the floor through the `expand` door (type-directed η). -/
def etaRowDoor (_ : EtaRuleDesc) : EqualityDoor := .expand

/-- An η row's residual tier: `typedDirected` when it fires only through the typed conversion checker
(`requiresTypedFiring = true`), otherwise `definitional` (the raw η rows).  Reads the row's own field — NOT
hardcoded. -/
def etaRowTier (rule : EtaRuleDesc) : EqualityTier :=
  if rule.requiresTypedFiring then .typedDirected else .definitional

/-- Bool predicate: is this η row typed-directed (the `requiresTypedFiring := true` tier)? -/
def etaRowIsTypedDirected (rule : EtaRuleDesc) : Bool := rule.requiresTypedFiring

/-- Bool predicate: is this η row raw-definitional (fires in the raw relation)? -/
def etaRowIsRawDefinitional (rule : EtaRuleDesc) : Bool := not rule.requiresTypedFiring

/-- Bool predicate: does this η row classify `propositional`?  Always `false`. -/
def etaRowIsPropositional (_ : EtaRuleDesc) : Bool := false

/-! ## The erase door — grade-0 / irrelevance (cited, not re-derived) -/

/-- The grade-0 erasure equality reaches the floor through the `erase` door: an erased (grade-0 / ghost)
carrier is definitionally irrelevant, so all its inhabitants are equal.  Witnessed by the shipped graded
`erase` theorem in `FX1Poly/Dimensions/Graded/GradeErasureGeneric.lean`. -/
def gradeZeroEraseDoor : EqualityDoor := .erase

/-- The grade-0 erasure equality is `definitional`-by-irrelevance. -/
def gradeZeroEraseTier : EqualityTier := .definitional

/-! ## Per-row spot-checks -/

/-- The shipped gel-β iota row classifies `orient` / `definitional` (the computing half of the Gel ≃ R
retract — a raw reduction). -/
theorem gelBetaIotaRow_door : iotaRowDoor gelBetaIotaRow = .orient := rfl
theorem gelBetaIotaRow_tier : iotaRowTier gelBetaIotaRow = .definitional := rfl

/-- The shipped gel-η row classifies `expand` / `typedDirected` — its `requiresTypedFiring = true` (its
`Conv`-content is the deferred NbE arc, which is exactly why it is typed-directed, not definitional).  This
tier reads the row's field, so it is non-vacuous. -/
theorem gelEtaRow_door : etaRowDoor gelEtaRow = .expand := rfl
theorem gelEtaRow_tier : etaRowTier gelEtaRow = .typedDirected := rfl

/-! ## The counts — the honest definitionality ledger over the shipped tables -/

/-- All 22 `iotaRuleTable` rows are `orient` / `definitional` reductions. -/
theorem iotaRowCount : iotaRuleTable.length = 22 := iotaRuleTable_length

/-- No shipped iota row is propositional — the propositional tier is the residue OUTSIDE the tables. -/
theorem noShippedIotaRowIsPropositional :
    (iotaRuleTable.filter iotaRowIsPropositional).length = 0 := rfl

/-- Of the 9 `etaRuleTable` rows, exactly 6 are `typedDirected` (the `requiresTypedFiring := true` rows:
`modIntro`/`glueIntro`/`unit`/`recordIntro`/`refineIntro`/`gel`). -/
theorem etaTypedDirectedCount :
    (etaRuleTable.filter etaRowIsTypedDirected).length = 6 := rfl

/-- The other 3 `etaRuleTable` rows are raw-`definitional` (`lam`/`pair`/`pathLam`). -/
theorem etaRawDefinitionalCount :
    (etaRuleTable.filter etaRowIsRawDefinitional).length = 3 := rfl

/-- No shipped η row is propositional. -/
theorem noShippedEtaRowIsPropositional :
    (etaRuleTable.filter etaRowIsPropositional).length = 0 := rfl

/-! ## Non-vacuity -/

/-- The classifier genuinely SEPARATES strengths: the gel-β reduction is `definitional` while the gel-η
expansion is `typedDirected`, so the tier is not a constant.  (Mirrors `semanticTier_discriminates`.) -/
theorem equalityTier_discriminates :
    iotaRowTier gelBetaIotaRow ≠ etaRowTier gelEtaRow := by
  rw [gelBetaIotaRow_tier, gelEtaRow_tier]
  exact fun tiersEqual => EqualityTier.noConfusion tiersEqual

/-- The doors are genuinely distinct: orient (iota) vs expand (eta). -/
theorem equalityDoor_discriminates :
    iotaRowDoor gelBetaIotaRow ≠ etaRowDoor gelEtaRow := by
  rw [gelBetaIotaRow_door, gelEtaRow_door]
  exact fun doorsEqual => EqualityDoor.noConfusion doorsEqual

/-! ## Honest rails -/

/-- **Honesty marker.**  The row-level `definitional` tier means "raw `rfl` on the row's SN-covered
fragment," NOT global definitional `Conv`: raw β is not globally SN (`gen_natRec`/`gen_fixedPoint` are
partial-class).  `= false`. -/
def fxEqualityTier_claimsGlobalDefinitionalConv : Bool := false

/-- **Honesty marker.**  The `erase` door's STRICT-proposition instance (`gen_sprop` / `SProp`) is PLANNED,
not shipped; only the grade-0 / usage-0 erasure is shipped (cited above).  `= false`. -/
def fxEqualityTier_hasSPropEraseInstance : Bool := false

end FX1Poly.Typed

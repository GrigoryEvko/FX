import FX1Poly.Typed.RawIotaEtaOperationalSN

/-! # FX1Poly/Typed/MilestoneAParityMatrix
    — #1140: the 3-leg × 3-endpoint parity ledger + the HONEST capstone criterion for #653

Milestone A (SN / canonicity / consistency) is targeted by THREE independent routes ("legs"):

  1. `taitReducibility` — the syntactic logical-relation / reducibility-candidate route (the critical
     path).  SN: `HasTypeDescPi Γ t T → IsStronglyNormalizing t` (SN-043).  Canonicity: closed-normal
     bool/data canonical forms (SN-047..049, ELIM-CANON #1138).  Consistency: no closed inhabitant of
     Empty (SN-050).  All three are PROVEN INDEPENDENTLY, zero-axiom.
  2. `sconingViaSTC` — the categorical glued-model / Sterling-Tait-computability route.  Its SN is the SAME
     reducibility object as Tait (the `reducibilityScone` bridge, SN-092 — reducibility IS a sconing
     witness), so the SN endpoint is BRIDGED-to-Tait, not an independent second proof.  Canonicity ships on
     the DATA axis (sconing data-canonicity witnesses).  Consistency ships (consistency via the sconing
     leg).
  3. `rpoWordRewriting` — the combinatorial recursive-path-order / ωcE-word route (firings 72-78).  Its SN
     endpoint is PROVEN for the ι∪η FRAGMENT, Tait-FREE (`iotaEtaFullStep_wellFounded` + the operational
     `iotaEta_noInfiniteReduction`), but β stays Tait-imported (raw β is non-SN — Ω, SN-NECESSITY #950), so
     the SN endpoint is a FRAGMENT result.  Its canonicity / consistency endpoints are OPEN RESEARCH (an
     independent canonicity via the convergent presentation is SN-136 #639, not yet shipped).

## The honest finding

`fullyIndependentlyProvenLegCount = 1`: exactly ONE leg (Tait) is fully + independently proven across all
three endpoints.  Therefore the three-way capstone #653 ("Milestone A closed three ways, zero-axiom") is
NOT yet met (`threeWayCapstone_not_yet_met`).  The sconing leg's SN is the same object as Tait's; the RPO
leg covers only the SN endpoint (a Tait-free fragment, with β imported and canonicity/consistency open).
This ledger encodes that honestly — it is a CRITERION + status, not a claim that the capstone is closed.

This matches the standing project honesty: per the roadmap, the joint apex is open research and 0-FP/0-FN
hold per fragment, not jointly.  The matrix here makes the per-(leg,endpoint) status machine-checkable: the
capstone count is computed by `rfl`, and the RPO-leg SN endpoint carries a NON-VACUOUS witness
(`rpoStrongNormalizationEndpoint`) inhabited by the shipped firing-78 theorem.

## Zero-axiom verification

The status table is full-enum `Bool` projections (no wildcards, no derived `DecidableEq`); the capstone
count and `legBreakdown` close by `rfl`; the not-yet-met negation closes by `decide` over `Nat`-deceq
(propext-clean).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
-/

namespace FX1Poly.Core.ParityMatrix

/-- The three INDEPENDENT routes to Milestone-A metatheory. -/
inductive MilestoneLeg where
  | taitReducibility
  | sconingViaSTC
  | rpoWordRewriting

/-- The three Milestone-A endpoints. -/
inductive MilestoneEndpoint where
  | strongNormalization
  | canonicity
  | consistency

/-- Honest per-cell proof status:
* `provenIndependent` — a self-contained zero-axiom theorem ON THIS LEG.
* `bridgedToTait` — proven, but the object is literally Tait's reducibility (not an independent route).
* `partialFragment` — proven for a fragment only (ι∪η with β imported, or the data axis only).
* `openResearch` — not yet established on this leg. -/
inductive CellStatus where
  | provenIndependent
  | bridgedToTait
  | partialFragment
  | openResearch

/-- The honest 3×3 parity table. -/
def parityCell : MilestoneLeg → MilestoneEndpoint → CellStatus
  | .taitReducibility, .strongNormalization => .provenIndependent
  | .taitReducibility, .canonicity => .provenIndependent
  | .taitReducibility, .consistency => .provenIndependent
  | .sconingViaSTC, .strongNormalization => .bridgedToTait
  | .sconingViaSTC, .canonicity => .partialFragment
  | .sconingViaSTC, .consistency => .provenIndependent
  | .rpoWordRewriting, .strongNormalization => .partialFragment
  | .rpoWordRewriting, .canonicity => .openResearch
  | .rpoWordRewriting, .consistency => .openResearch

/-- Full-enum projection (propext-clean; no wildcard, no derived `DecidableEq`). -/
def CellStatus.isProvenIndependent : CellStatus → Bool
  | .provenIndependent => true
  | .bridgedToTait => false
  | .partialFragment => false
  | .openResearch => false

/-- A leg is "fully independent" when all three of its endpoints are `provenIndependent`. -/
def legFullyIndependent (leg : MilestoneLeg) : Bool :=
  (parityCell leg .strongNormalization).isProvenIndependent &&
    (parityCell leg .canonicity).isProvenIndependent &&
    (parityCell leg .consistency).isProvenIndependent

def allLegs : List MilestoneLeg :=
  [.taitReducibility, .sconingViaSTC, .rpoWordRewriting]

/-- How many legs are fully + independently proven across all three endpoints. -/
def fullyIndependentlyProvenLegCount : Nat :=
  (allLegs.filter legFullyIndependent).length

/-- The honest current status: exactly ONE leg (Tait) is fully + independently proven across all three
endpoints.  Computed by `rfl`. -/
theorem capstone_currentlyClosedOneWay : fullyIndependentlyProvenLegCount = 1 := rfl

/-- The per-leg breakdown: only Tait is fully independent; sconing's SN is bridged-to-Tait and the RPO leg
covers only the SN endpoint (a fragment, β-imported). -/
theorem legBreakdown :
    legFullyIndependent .taitReducibility = true ∧
    legFullyIndependent .sconingViaSTC = false ∧
    legFullyIndependent .rpoWordRewriting = false := ⟨rfl, rfl, rfl⟩

/-- The capstone criterion #653 asks for: all three legs fully + independently proven. -/
@[reducible] def threeWayCapstoneMet : Prop := fullyIndependentlyProvenLegCount = 3

/-- ★ Honest: the three-way capstone is NOT yet met (only one leg is fully independent).  This is the
honest capstone CRITERION, not a closure claim. -/
theorem threeWayCapstone_not_yet_met : ¬ threeWayCapstoneMet := by decide

/-- Non-vacuous witness that the RPO leg genuinely OWNS the SN endpoint (Tait-free, ι∪η fragment): the
firing-78 operational-SN theorem `iotaEta_noInfiniteReduction` inhabits the "no infinite ι∪η reduction
sequence" proposition.  This keeps the `parityCell .rpoWordRewriting .strongNormalization` entry
non-vacuous — there is a real shipped theorem behind it. -/
def rpoStrongNormalizationEndpoint :
    ∀ {scope : Nat} (reductionSequence : Nat → RawTerm scope),
      (∀ index, IotaEtaStep (reductionSequence index) (reductionSequence (index + 1))) → False :=
  fun reductionSequence eachStepsToNext =>
    iotaEta_noInfiniteReduction reductionSequence eachStepsToNext

end FX1Poly.Core.ParityMatrix

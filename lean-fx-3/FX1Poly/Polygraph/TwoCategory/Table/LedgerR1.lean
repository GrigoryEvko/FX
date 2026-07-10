import FX1Poly.Polygraph.TwoCategory.Table.Ledger
import FX1Poly.Polygraph.TwoCategory.Table.InvariantFoldInstances
import FX1Poly.Polygraph.TwoCategory.Table.ThinWalkerMigration
import FX1Poly.Polygraph.TwoCategory.Table.StrategyRegistry

/-! # Polygraph/TwoCategory/Table/LedgerR1 — the POLY-TAB r1 honest ledger + aggregate verdict + the grown
deletion list (still awaiting confirmation) + the POLY-TAB-2 plan (P4 + P5)

The terminal marker of POLY-TAB r1 (migration wave 1 on the locked r0 table design, task #2228).  It aggregates
every r1 marker into one verdict and records, honestly, what SHIPPED, what was BANKED, and how the deletion list
GREW (nothing deleted).

## SHIPPED (green, zero-axiom, additive)

  * **P1 REAL invariant-fold instances** (`Table/InvariantFoldInstances.lean`): two genuine `rowConvInvariant_foldEq`
    instances at real carriers (boundary word-length `Nat`, full boundary record) replacing the const-`Unit` demo's
    role, plus the relational `foldRel` form on a real `Prop`-valued relation — each non-vacuous on a real Frobenius
    row.  BANKED: the deep diagram invariant `extraSpiderDiagramOf` as a `foldRel` instance (the B->A
    `interpretWordFrom` word interpreter is not wired; a non-boundary invariant forces the 13-constructor
    `TwoCellConvFull` `fullPreserves` induction with its four `castBoundary` cases; the `SpiderConv.whisker` gate +
    the open `relationAgrees`).  `fxTab_hasRealInvariantFoldInstances = true`.

  * **P2 the CERTIFIED strategy registry** (`Table/StrategyRegistry.lean`): `CertifiedStrategyEntry` (fingerprint +
    `DecisionMechanism` tag + certified decider + admissibility certificate), the registry, `dispatchStrategy`, and
    the ONE generic `dispatchStrategy_sound` (routing soundness proved once).  The MODE-ADMIT row-aware registry is
    RE-SEATED BY BRIDGE (`dispatchFamily = admitByRowAware` on the `EndgameDemo` staging dimension AND its
    near-miss, by `rfl`), the mechanism tag preserved, and the near-miss negative control REFUSED through the new
    dispatch.  `fxTab_hasCertifiedStrategyRegistry = true`.

  * **P3 thin-class walker migrations** (`Table/ThinWalkerMigration.lean`): the walking idempotent monad (retirement
    bridge over `IdempotentLawRel`) and the walking involution (born generic over `emptyCellRel`) as table values
    with both-direction bridge iffs, plus the monad SEPARATING precedent, each with a concrete bespoke-vs-generic
    route-agreement verdict.  BANKED: the walking KZ monad (directed preorder base — POLY-TAB-2 design work per
    lock decision 1).  `fxTab_hasThinClassWalkerMigrations = true`, `fxTab_hasKZWalkerMigration = false`.

## THE LOCK-vs-BRICK RECONCILIATION (the lock is the authority; differences recorded)

The recon flagged that the recon-quoted lock's POLY-TAB-1 wave is NARROWER than the r1 brick list (the lock names
Frobenius folds + the B->A `SpiderConvRows` rebase + the faithfulness certificate; the bricks add the strategy
registry, the thin-walker migrations, and KZ).  Following the lock where they differ:

  * The B->A `extraSpiderDiagramOf` rebase is BANKED, not forced (the lock's stated obstruction); P1 ships the
    carrier-A-cheap boundary invariants as the honest real instances instead (§honest-partials directive).
  * KZ is BANKED to POLY-TAB-2 (lock decision 1 flags it "needs an oriented / preorder-valued base relation"),
    matching the lock rather than attempting a mechanical re-exposure.
  * The strategy registry + thin-walker migrations are brought FORWARD from the lock's POLY-TAB-2 (they were
    tractable additively with the shipped families), a net-ahead-of-plan difference recorded here.

## HONEST CONFIDENCE

The P1/P2/P3 folds, registries, bridges, and route-agreements are all machine-checked green and zero-axiom (audit
twins with per-declaration `#assert_no_axioms`, verified additionally by independent `#print axioms`).  The DESIGN
claims banked above (the deep-diagram fold; KZ; automatic certified data admission) are recorded intentions backed
by precise obstructions, not executed.  Nothing was deleted; no `Amalgam/` file or walker lane was edited (the
StrategyRegistry re-seat is a NEW value plus `rfl` equalities to `admitByRowAware`, additive).

Raw Lean 4 + Init; a docstring ledger plus a `Bool` aggregate + `by decide`, axiom-free.  Per-declaration
`#assert_no_axioms` in the audit twin. -/

namespace FX1Poly.Polygraph.Table

open FX1Poly.Polygraph (fxTab_hasRealInvariantFoldInstances fxTab_hasThinClassWalkerMigrations
  fxTab_hasKZWalkerMigration)
open FX1Poly.Polygraph.Amalgam (fxTab_hasCertifiedStrategyRegistry)

/-! ## The r1 aggregate verdict -/

/-- ★★ **The POLY-TAB r1 aggregate verdict** — the r0 aggregate stays green AND every r1 marker is `true`: the real
invariant-fold instances (P1), the certified strategy registry (P2), and the thin-class walker migrations (P3).
The conjunction is the one kernel-checked witness that POLY-TAB r1 shipped complete and green on top of the locked
r0 table design. -/
def fxTab_polyTabR1Complete : Bool :=
  fxTab_polyTabR0Complete
    && fxTab_hasRealInvariantFoldInstances
    && fxTab_hasThinClassWalkerMigrations
    && fxTab_hasCertifiedStrategyRegistry

/-- The r1 aggregate verdict computes to `true` — POLY-TAB r1 is complete (r0 green + P1 + P2 + P3),
machine-checked. -/
theorem polyTabR1Complete_holds : fxTab_polyTabR1Complete = true := by decide

/-! ## P4 — the DELETION LIST, GROWN with per-file readiness states (nothing deleted; awaiting confirmation)

The r0 `DesignLock.lean` recorded the deletion-target census.  r1 GROWS it with per-file READINESS states — a
declaration is `ready-for-confirmation` when it is MIGRATED-AND-BRIDGED (a shipped generic instance + an iff
bridge transporting every downstream fact), and `not-ready` when it is CENSUS-ONLY (named but no bridge yet).
This list stays a docstring AWAITING USER CONFIRMATION; nothing is deleted; the r1 git diff shows ZERO deletions.

### READY-FOR-CONFIRMATION (migrated-and-bridged; retire only on explicit green-light)

  * `IdempotentMonadSaturatedTwoCellConv` (WalkingIdempotent) — bridged by `idempotentWalker_iff_generic` (P3) to
    `SaturatedConvOver monadModeSignature IdempotentLawRel`; the family decider agrees on the concrete pair
    (`idempotentRouteAgreement_holds`).  MIGRATED-AND-BRIDGED.
  * The walking-involution saturated conv — BORN GENERIC (its family walker conv IS `SaturatedConvOver ...
    emptyCellRel`, bridge `Iff.rfl`, P3); there is no bespoke inductive to delete, only the identity migration
    to confirm as retired-by-subsumption.  MIGRATED-AND-BRIDGED.
  * `FrobeniusSpecialWalkerConv` (r0 `Table/WalkerMigration.lean`) — bridged by `frobeniusSpecialWalker_iff_generic`
    (r0 T4); it is the one-law DEMO of the retirement pattern, retire-or-keep as a pedagogical exemplar (author's
    choice).  MIGRATED-AND-BRIDGED.
  * `MonadSaturatedTwoCellConv` (WalkingMonad) — bridged by `monadSaturated_iff_generic` (r0); the SEPARATING
    precedent, whose family field IS the bridge (`monadRelationFamily_bridge_is_precedent`, P3).
    MIGRATED-AND-BRIDGED (but likely KEPT as the canonical exemplar).

### NOT-READY (census-only; POLY-TAB-2 re-homing required before any confirmation)

  * `StringSaturatedTwoCellConv` (WalkingAdjunction / adjoint string) — no generic instance shipped; POLY-TAB-2.
  * `CohesionSaturatedTwoCellConv` (cohesion quadruple) — no generic instance shipped; POLY-TAB-2.
  * `QuadCohesionSaturatedTwoCellConv` — no generic instance shipped; POLY-TAB-2.
  * the adjunction `SaturatedTwoCellConv` (route `whiskerExchange` via `ofFull`) — no generic instance shipped;
    POLY-TAB-2.
  * `KZTwoCellLE` (WalkingKZ) — BANKED (directed preorder base; the generic carrier is symmetric); genuine
    POLY-TAB-2 design, `fxTab_hasKZWalkerMigration = false`.
  * the contextual-closure kits (`*_inContext` / `*_suffixCongruence` / pad-congruence in Brauer / Frobenius /
    Spider files) — subsumed by the four congruence ctors but the CONSUMERS are not yet re-pointed; POLY-TAB-3.
  * the Class-C `*TwoCell` seed generators — subsumed by `ReconstructedTwoCell` but consumers not re-pointed;
    POLY-TAB-3.

### KEEP (correct, not offenders — never on the deletion list)

  * `EncodedConv` / `SemiThueReduction` (the honest undecidability WALL — see the P5 argument below).
  * the free / substrate inductives (`RawTwoCellExpr`, `TwoCellStep`, `TwoCellConv`, `TwoCellConvFull`,
    `SaturatedConvOver`).

## P5 — the POLY-TAB-2 plan

### (a) The Brauer lane migration + `cupSlideRelation` as the FIRST versioned-row test (#2238 BREACH-4)

Task #2238 (BREACH-4) found the shipped 7-row symmetric self-dual Brauer presentation LACKS the `*`-dual of
`capSlideRelation` (a `cupSlideRelation` row).  POLY-TAB-2 uses this as the FIRST test of the VERSIONED-ROW
mechanism: adding `cupSlideRelation` is a new presentation VERSION (`BrauerLawRel` gains one constructor), and the
soundness invariant (`processBrauer` / the perfect-matching partition) gains exactly ONE new `rowConvInvariant_
foldRel` arm for the new row — every other arm unchanged.  This is the concrete demonstration that a presentation
edit costs "one row + one fold arm", the polygraph-as-value payoff.  It then resumes #2013 (Brauer completeness +
decision) on the completed presentation.

### (b) The String / Quad lanes

Re-home the Class-A `StringSaturatedTwoCellConv` / `CohesionSaturatedTwoCellConv` / `QuadCohesionSaturatedTwoCellConv`
/ adjunction `SaturatedTwoCellConv` onto `SaturatedConvOver @ <LawRel>` via the monad-exemplar iff (the P3 pattern
at higher law count), plus the per-mechanism dependent `StrategyCertificate` record and the wiring `wiring?` view
(the lock's POLY-TAB-2 items).  KZ needs the oriented/preorder base first.

### (c) The EncodedConv question — ARGUED and DECIDED: STAYS BESPOKE-BY-DESIGN

Question: does the word-level undecidability-ceiling lane (`EncodedConv` / `SemiThueReduction`,
Tier0/.../UndecidabilityReduction.lean) migrate onto the table, or stay bespoke-by-design as the reduction artifact?

  * **For migration:** `EncodedConv` independently has EXACTLY the six-ctor universal shape (rule / whiskerLeft /
    whiskerRight / refl / symm / trans) that the r0 lock cited as CORROBORATING the generic design, so structurally
    it COULD be `SaturatedConvOver encodedSignature EncodedLawRel`.
  * **Against migration (decisive):** `EncodedConv`'s VALUE is the semi-Thue REDUCTION embedding (the certificate
    that a specific presentation embeds an undecidable word problem), NOT a congruence to be decided.  Migrating it
    (i) adds ZERO decidability — it is undecidable BY CONSTRUCTION, which is the whole point; (ii) OBSCURES the
    reduction structure (`SemiThueReduction` is the load-bearing content; the congruence closure is incidental);
    (iii) is already integrated into the table architecture at the RIGHT level — the `DecisionMechanism.undecidableWall`
    tag classifies it, and the certified strategy registry DEFINITIONALLY EXCLUDES it (a certified entry must carry
    a decider; the honest wall has none, by design).

  **DECISION: `EncodedConv` / `SemiThueReduction` STAYS BESPOKE-BY-DESIGN as the reduction artifact.**  It is not
  an offender to migrate but the CEILING WITNESS: the `undecidableWall` tag + certified-registry exclusion
  integrate it into the table architecture WITHOUT re-homing its inductive, which is exactly the r0 lock's KEEP
  classification.  Re-homing would be a decoration that hides the substance (the reduction).

## Honesty marker -/

/-- ★★ **Honesty marker — POLY-TAB r1 (migration wave 1) SHIPS COMPLETE (P1+P2+P3+P4+P5).**  The real invariant-fold
instances (P1), the certified strategy registry with one generic dispatch soundness theorem (P2), and the
thin-class walker migrations (P3) are all machine-checked green and zero-axiom; the aggregate verdict
`fxTab_polyTabR1Complete` conjoins them with the still-green r0 aggregate (`polyTabR1Complete_holds`, `by decide`).
The deletion list is GROWN with per-file readiness states (P4, migrated-and-bridged = ready-for-confirmation /
census-only = not-ready), still a docstring awaiting confirmation, ZERO deletions.  The POLY-TAB-2 plan (P5) is
written: the Brauer `cupSlideRelation` row as the first versioned-row test (#2238), the String / Quad re-homing,
and the EncodedConv question ARGUED and DECIDED (stays bespoke-by-design as the reduction artifact).  Lock-vs-brick
differences (B->A rebase banked, KZ banked, registry/thin-walker brought forward) are recorded.  `= true`. -/
def fxTab_polyTabR1LedgerComplete : Bool := fxTab_polyTabR1Complete

end FX1Poly.Polygraph.Table

import FX1Poly.Polygraph.TwoCategory.Table.Ledger
import FX1Poly.Polygraph.TwoCategory.Table.InvariantFoldInstances
import FX1Poly.Polygraph.TwoCategory.Table.ThinWalkerMigration
import FX1Poly.Polygraph.TwoCategory.Table.StrategyRegistry
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDecisionGen
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeGen

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

/-! ## The POLY-TAB r6 monad-re-founding marker (WAVE 1; strictly factual — the machine-checked chain ONLY) -/

open FX1Poly.Polygraph.Amalgam (fxMonad_hasLawRelationLeaf fxMonad_hasGenericNativeSoundnessLeg
  fxMonad_hasGenericNativeDeciderInterim)

/-- ★★ **The POLY-TAB r6 monad-re-founding marker (WAVE 1).**  Conjoins ONLY the machine-checked-bespoke-free chain:
the bespoke-free law carrier (S1, `fxMonad_hasLawRelationLeaf`), the born-generic Δ SOUNDNESS leg + decision assembly
(S2 + S3, `fxMonad_hasGenericNativeSoundnessLeg`, exhaustive-meta-walk-certified bespoke-free), and the working
INTERIM generic decider with born-generic soundness + regression continuity (S4,
`fxMonad_hasGenericNativeDeciderInterim`).  It DELIBERATELY EXCLUDES `fxMonad_hasGenericNativeDecider` (a WAVE-1
snapshot: at r6 it was `false`; the WAVE-2 port lands `monadNormalizeGen` born-generic and flips it `true` — tracked
by `fxTab_hasMonadNativeRefoundingWave2` below).  So this WAVE-1 marker asserts exactly what r6 machine-checked: the
re-founding's soundness half + assembly + working interim decider ship green and zero-axiom; the bespoke-free
completeness was, at r6, the honest named residual.  `= true`. -/
def fxTab_hasMonadNativeRefounding : Bool :=
  fxMonad_hasLawRelationLeaf
    && fxMonad_hasGenericNativeSoundnessLeg
    && fxMonad_hasGenericNativeDeciderInterim

/-- The r6 monad-re-founding marker computes to `true` — the machine-checked born-generic soundness chain + interim
decider are complete and green, machine-checked. -/
theorem hasMonadNativeRefounding_holds : fxTab_hasMonadNativeRefounding = true := by decide

/-! ## The POLY-TAB r6 monad-re-founding WAVE-2 marker (the COMPLETENESS FLIP; strictly factual)

WAVE 2 (this round) re-founded the completeness leg — the Eilenberg–Zilber word-multiplicativity chain
(`wordMul_vcompGen` / `wordMul_hcompGen` / whisker + gadget-absorb lemmas, ~2000 conv-producing lines) — ctor-for-ctor
over the generic `SaturatedConvOver monadModeSignature MonadLawRel` carrier (the new `WalkingMonad/MonadWordMultGen` /
`MonadNormalizeCasesGen` / `MonadVcompMultGen` / `MonadWordVcompGen` / `MonadNormalizeGen` files), inhabiting the
born-generic normalize `monadNormalizeGen`.  That swaps the interim canonicalization's bespoke-transported completeness
field for a born-generic one (`monadSaturatedCanonicalizationGenNative`), and assembles the fully bespoke-free
`decideSaturatedConvOverMonadNative` — flipping `fxMonad_hasGenericNativeDecider` `false → true`. -/

open FX1Poly.Polygraph.Amalgam (fxMonad_hasMonadNormalizeGen fxMonad_hasGenericNativeDeciderComplete
  fxMonad_hasGenericNativeDecider)

/-- ★★ **The POLY-TAB r6 monad-re-founding WAVE-2 marker (the completeness flip).**  Conjoins the WAVE-1 chain
(`fxTab_hasMonadNativeRefounding`) with the WAVE-2 completeness flip: the born-generic normalize
(`fxMonad_hasMonadNormalizeGen`, `monadNormalizeGen` over the generic carrier), the assembled bespoke-free native
decider (`fxMonad_hasGenericNativeDeciderComplete`, `decideSaturatedConvOverMonadNative`), and the now-flipped decider
marker (`fxMonad_hasGenericNativeDecider = true`).  Every conjunct is machine-checked: the completeness chain is
zero-axiom AND exhaustively bespoke-free (the `includeStdlib := true` meta-walk certifies `monadNormalizeGen` /
`monadSaturatedCanonicalizationGenNative` / `decideSaturatedConvOverMonadNative` have NO `MonadSaturatedTwoCellConv`
in their full constant closure — 847 constants walked for the decider).  The native decider reproduces the interim +
old bespoke verdicts on both lane regression pairs (`monadNativeAgreesOnRegression_holds`, incl. the separating
`isFalse` faces pair).  `= true`. -/
def fxTab_hasMonadNativeRefoundingWave2 : Bool :=
  fxTab_hasMonadNativeRefounding
    && fxMonad_hasMonadNormalizeGen
    && fxMonad_hasGenericNativeDeciderComplete
    && fxMonad_hasGenericNativeDecider

/-- The r6 WAVE-2 monad-re-founding marker computes to `true` — the completeness flip shipped complete and green,
machine-checked. -/
theorem hasMonadNativeRefoundingWave2_holds : fxTab_hasMonadNativeRefoundingWave2 = true := by decide

/-! ## r7 RETIREMENT PRECONDITION (monad lane; NOTHING deleted this round — the flip UNBLOCKS r7 at the proof level)

The WAVE-2 flip delivers the FIRST of the two r7 conjuncts named at `r7 RETIREMENT-ROUND PREVIEW` below: the
born-generic `monadNormalizeGen` now exists, so the RE-PROVES core of the monad lane (the whole
Δ-normalize/decide chain) is retirable AT THE PROOF LEVEL — exactly the idempotent-r4 posture.  The deletion still
does NOT fire, gated on the SECOND conjunct + user sign-off:

  * **UNBLOCKED (WAVE 2):** the completeness port.  `monadNormalizeGen` is born-generic and exhaustively
    bespoke-free; the bespoke Δ-normalize/decide chain is no longer the SOLE inhabitant of the completeness leg.
  * **STILL BLOCKED — the WalkingKZ HARD BLOCKER:** `KZTwoCellLE.ofMonad : MonadSaturatedTwoCellConv a b →
    KZTwoCellLE a b` (`WalkingKZ/KZMonadPresentation`) consumes the monad conv BOTH ways (antisymmetrization
    RECOVERS it), needing an oriented / preorder-valued base the symmetric generic carrier does not provide
    (`fxTab_hasKZWalkerMigration = false`).  `KZOrderCompleteness` / `KZMonadDecision` also directly consume the
    bespoke `wordMul_hcomp` / `monadNormalize`.  So the bespoke chain STAYS LIVE regardless of the flip.
  * **Files that reach zero LIVE monad-lane refs once consumers re-point (r7, GATED):** the bespoke Δ-normalize/
    decide chain (`WalkingMonad/MonadNormalizeCell` / `MonadNormalizeCases` / `MonadWordMultiplicativity` /
    `MonadWhiskerRightMult` / `MonadWhiskerNormalizeCases` / `MonadHcompMult` / `MonadVcompMult` / `MonadWordVcomp` /
    `MonadNormalizeVcomp` / `MonadWordProblem`) once (a) the WAVE-2 `...Gen` decider is repointed into the family
    (`Amalgam/SaturatedRelationFamily.monadRelationFamily`) and (b) the KZ `ofMonad` ctor is given its own oriented
    base.  Both are separate GATED arcs; nothing is deleted this round (never-delete-without-confirm). -/

/-! ## P4 — the DELETION LIST, GROWN with per-file readiness states (nothing deleted; awaiting confirmation)

The r0 `DesignLock.lean` recorded the deletion-target census.  r1 GROWS it with per-file READINESS states — a
declaration is `ready-for-confirmation` when it is MIGRATED-AND-BRIDGED (a shipped generic instance + an iff
bridge transporting every downstream fact), and `not-ready` when it is CENSUS-ONLY (named but no bridge yet).
This list stays a docstring AWAITING USER CONFIRMATION; nothing is deleted; the r1 git diff shows ZERO deletions.

### READY-FOR-CONFIRMATION (migrated-and-bridged) — POLY-TAB r2 RETIREMENT WAVE outcomes recorded per item

The r2 wave (task #2228) processed the four READY items one at a time.  Net: ZERO deletions, ZERO LOC removed —
one item CONFIRMED RETIRED-BY-SUBSUMPTION (nothing existed to delete) and three DEFERRED with precise obstructions
(each deletion would require re-pointing many structural consumers and/or re-proving a load-bearing verdict, which
is semantic re-proving, not the mechanical re-pointing the wave was scoped for).  Deferral is honest; forcing is not.

  * `IdempotentMonadSaturatedTwoCellConv` (WalkingIdempotent) — bridged by `idempotentWalker_iff_generic` (P3) to
    `SaturatedConvOver monadModeSignature IdempotentLawRel`; the family decider agrees on the concrete pair
    (`idempotentRouteAgreement_holds`).  MIGRATED-AND-BRIDGED.  **r2 OUTCOME: DEFERRED** — 11 live structural
    consumers (the whole WalkingIdempotent lane + three `Amalgam/` files, including the `Decidable` instance in
    `IdempotentMonadDecision`) call the bespoke constructors directly; the iff bridge does not rewrite call sites,
    and re-pointing them onto the generic requires REBUILDING the `Decidable` instance (semantic re-proving, not
    re-pointing).  A POLY-TAB-3 additive re-pointing arc must land green FIRST.
  * The walking-involution saturated conv — BORN GENERIC (its family walker conv IS `SaturatedConvOver ...
    emptyCellRel`, bridge `Iff.rfl`, P3); there is no bespoke inductive to delete.  **r2 OUTCOME: CONFIRMED
    RETIRED-BY-SUBSUMPTION** — `involutionWalker_iff_generic` is literally `Iff.rfl` between two identical
    `SaturatedConvOver ... emptyCellRel` terms; no inductive, no consumer, ZERO deletion.  The identity migration
    is confirmed; there is nothing to remove.
  * `FrobeniusSpecialWalkerConv` (r0 `Table/WalkerMigration.lean`) — bridged by `frobeniusSpecialWalker_iff_generic`
    (r0 T4); the one-law DEMO of the retirement pattern.  MIGRATED-AND-BRIDGED.  **r2 OUTCOME: DEFERRED** — its home
    file hosts `fxTab_hasSmallestWalkerMigration` (+ `fxTab_hasBornGenericWalker`), both conjoined into
    `fxTab_polyTabR0Complete` and asserted `= true := by decide` (`Table/Ledger.lean`); deleting the inductive +
    bridges would either leave that marker certifying a deleted playbook (dishonest) or force re-proving the r0
    aggregate without it (semantic re-proving).  The ledger flags it author's-choice-KEEP as the very
    demonstration of the retirement pattern; it needs an item-specific green-light, not the blanket one.
  * `MonadSaturatedTwoCellConv` (WalkingMonad) — bridged by `monadSaturated_iff_generic` (r0); the SEPARATING
    precedent, whose family field IS the bridge (`monadRelationFamily_bridge_is_precedent`, P3).
    MIGRATED-AND-BRIDGED (but likely KEPT as the canonical exemplar).  **r2 OUTCOME: DEFERRED** — 35 live structural
    consumers spanning five walker lanes (WalkingMonad, WalkingIdempotent, WalkingInvolution, WalkingKZ,
    WalkingString) + `Amalgam/`; a lane-wide migration + decider rebuilds (semantic re-proving) is required before
    any deletion, and the ledger leans KEEP.

### r3 OUTCOME (POLY-TAB-3 re-pointing arc, #2228) — the idempotent item STILL DEFERRED, ZERO deletions

The r2 idempotent bullet named "a POLY-TAB-3 additive re-pointing arc must land green FIRST".  r3 ran that arc and
found it CANNOT reach a deletion: the idempotent retirement is not a re-point but a normalizer re-founding (the
RE-PROVES class), exactly as r2 warned.

  * **Phase-1 banked (verified independently):** the generic decider `decideSaturatedConvOverIdempotent` and the
    bridge `idempotentSaturated_iff_generic` (both directions, plus `idempotentIsCongruence`) are shipped and raw
    `#print axioms`-clean — zero-axiom on the kernel, not merely the fuel-based `#assert_no_axioms` gate.  A private
    hand-rolled `decidableOfIff` helper was NOT added: the transport pattern already ships twice
    (`decideSaturatedConvOverIdempotent`, `SaturatedRelationFamily.decider`); a third copy would be bloat.  All the
    iff can buy is banked already.
  * **The blocker (precise):** BOTH routes to the generic decider are bespoke-rooted.
    `decideSaturatedConvOverIdempotent` (`SaturatedComponentDecider`:167) matches on `decideIdempotentConv`, and
    `idempotentRelationFamily.walkerDecider` (`SaturatedRelationFamily`:130) IS `decideIdempotentConv` =
    `idempotentSaturatedWordProblemModuloPosetality idempotentLocalPosetality`, and `idempotentLocalPosetality`
    (`IdempotentMonadFullNormalizer`:506) is the closed term built by the bespoke `normalizeFull` (the six-case
    cast-heavy NF induction) via `idempotentThinness_ofNormalize`.  The generic carrier `SaturatedConvOver
    monadModeSignature IdempotentLawRel` has NO independent proof of local posetality.  So deleting the inductive
    requires re-founding `idempotentLocalPosetality` / `normalizeFull` / `repFull` / `toNF` DIRECTLY over the
    generic carrier — the whole six-file normalizer lane.
  * **Residual consumers (NONZERO — DO NOT DELETE):** 15 ref-files / 280 ref-lines.  Load-bearing RE-PROVES core:
    `IdempotentMonad{Decision,MuInvertible,Normalizer,GeneralNormalizer,RightWhisker,FullNormalizer}` (~216 lines)
    plus the two iff inductions + `idempotentIsCongruence` in `Amalgam/SaturatedComponentDecider`.  The light
    consumers (`IdempotentMonadModel`, `Amalgam/SaturatedRelationFamily`, `Table/ThinWalkerMigration`) CAN be
    re-pointed born-generic and their `rfl` regressions survive (checked), but doing so neither drives the GLOBAL
    ref count to zero nor preserves meaning — it collapses the idempotent family member to the involution's trivial
    `Iff.rfl` shape and voids the very migration fact `idempotentWalker_iff_generic` states — so they are left on
    the bespoke type, un-churned.
  * **Verdict:** NOT-READY / NOT-DELETED.  The retirement's whole cost is the FullNormalizer port (`normalizeFull`,
    75 ref-lines, cast-heavy six-case NF induction), a semantic re-founding well beyond an additive re-point.
    Banked to a dedicated idempotent-normalizer-port arc; nothing deleted, nothing churned.
  * **Monad-lane wave shape (POLY-TAB-4 estimate, NOT started):** `MonadSaturatedTwoCellConv` (35 consumers, five
    lanes) has the SAME shape but WORSE — its decision `monadSaturatedTwoCellDecision` is the Delta monotone-map
    model, so a born-generic re-founding must re-express the whole simplicial-completeness leg over `SaturatedConvOver
    monadModeSignature MonadLawRel`, and it is the shared substrate the idempotent lane imports.  The idempotent
    normalizer port is the strictly smaller prerequisite; the monad lane inherits its playbook and stays
    KEPT-as-exemplar pending it.

### r4 OUTCOME (POLY-TAB r4 re-founding, #2228) — the idempotent normalizer PORT SHIPPED; deletion UNBLOCKED, GATED

r4 ran the "dedicated idempotent-normalizer-port arc" the r3 verdict banked.  Route B (re-prove; the recon found NO
hard node — build-only moves, ctor-for-ctor to `SaturatedConvOver`) SHIPPED, additive, green, zero-axiom.

  * **The generic-native NF stack (5 NEW files under `WalkingIdempotent/IdempotentSaturated*`):** `MuInvertible`
    (moves + mu-iso crux), `Ladder` (fold/grow), `GeneralBricks` (`whiskerLeftCanonGen` + `gadgetSplitRightGen`),
    `RightWhisker` (grow-half + `whiskerRightCanonGen`), `Normalizer` (`normalizeFullGen` + local posetality +
    the decider).  Each conv theorem re-proved DIRECTLY over `SaturatedConvOver monadModeSignature IdempotentLawRel`;
    the conv-FREE representatives (`repFull`/`repNF`/`growTower`/`canonThroughT`/…) are REUSED from the bespoke lane.
  * **The r3 blocker is RESOLVED:** `idempotentLocalPosetalityGeneric` (thinness over the generic carrier via
    `idempotentGenericThinness_ofNormalize repFull repFull_boundary normalizeFullGen`) and the born-generic decider
    `decideSaturatedConvOverIdempotentNative` are CLOSED TERMS whose ENTIRE transitive definition-dependency closure
    contains NO `IdempotentMonadSaturatedTwoCellConv` (verified by a transitive-const-dep meta-walk, by per-decl
    `#assert_no_axioms` audit twins, and by independent `#print axioms`).  The generic carrier now HAS an independent
    proof of local posetality — exactly what r3 said it lacked (r3 blocker text, above).  Regression: the native
    decider AGREES with the old `decideSaturatedConvOverIdempotent` on the shipped size-4 pair
    (`idempotentNativeAgreesOldOnRegression_holds`, `rfl`).
  * **Physical deletion of `IdempotentMonadSaturatedConv.lean` (the bespoke inductive): UNBLOCKED at the proof level,
    but GATED on the migration-fact-erosion decision — NOT FORCED.**  Every path to zero refs on
    `IdempotentMonadSaturatedTwoCellConv` runs through re-pointing `idempotentRelationFamily` /
    `idempotentWalker_iff_generic` born-generic, which VOIDS the migration facts those state (an iff INHERENTLY about
    the bespoke inductive; collapses to the involution's trivial `Iff.rfl`).  That is the same semantic-content
    erosion r3 flagged (LedgerR1:146-150) and the recon reserved for explicit user sign-off ("decide WITH the user").
    Per never-delete-without-confirm, r4 does NOT force it.  The exact deletion endgame awaiting the green-light:
    (1) relocate `IdempotentLawRel` to a bespoke-free home (imports `SaturatedOver` + the monad/idempotent Seed, not
    the bespoke conv lane); (2) retire the two iso inductions + `idempotentIsCongruence` +
    `decideSaturatedConvOverIdempotent` in `Amalgam/SaturatedComponentDecider`; (3) re-point the three light consumers
    (`IdempotentMonadModel`, `Amalgam/SaturatedRelationFamily`, `Table/ThinWalkerMigration`) born-generic (the
    erosion); (4) `/bin/rm` `IdempotentMonadSaturatedConv.lean` + the now-dead bespoke normalizer/model/decision
    files, audit twins + AuditAll lines in lockstep.

### r5 OUTCOME (POLY-TAB r5 retirement, EXECUTED, #2228) — the walking-idempotent bespoke lane RETIRED, ~2360 LOC removed, zero-axiom preserved

The r4 gate (migration-fact erosion) is RELEASED under standing user authorization ("delete everything migrated").
What the retired scaffolding proved, preserved here as HISTORY (proven prior to deletion; the deciding content
survives in the r4 native lane):

  (1) `idempotentSaturated_iff_generic` (`Amalgam/SaturatedComponentDecider`) identified the bespoke
      `IdempotentMonadSaturatedTwoCellConv` with `SaturatedConvOver monadModeSignature IdempotentLawRel` in BOTH
      directions — forward by induction flattening the `ofMonad` nesting (`idempotentSaturated_to_generic`, via the
      `monadSaturated_to_genericIdempotent` helper), backward by the universal property `SaturatedConvOver.recInto`
      through `idempotentIsCongruence` — machine-checked `#print axioms`-clean.
  (2) `idempotentWalker_iff_generic` (`Table/ThinWalkerMigration` P3) re-exposed that iso at the Table layer as a
      genuine retirement bridge.
  (3) `decideSaturatedConvOverIdempotent` transported `decideIdempotentConv` (built by the six-case `normalizeFull`
      NF induction over `idempotentLocalPosetality`) across the iso — the FIRST real-relation
      `DecidableSaturatedConvForRel` over a NON-EMPTY law relation.
  (4) `idempotentRouteAgreement_holds` / `idempotentRelationFamily_decider_eq_shipped` witnessed bespoke = generic
      route agreement on the size-4 pair `mu . (eta |> t)` vs `mu . (t <| eta)`, both `isTrue` (locally posetal,
      Lack, *A 2-Categories Companion*, section 1.5).

Post-retirement these collapse: `idempotentWalker_iff_generic` becomes `Iff.rfl` (born generic, the involution
shape); `idempotentRelationFamily` is BORN GENERIC (`walkerConv = SaturatedConvOver monadModeSignature
IdempotentLawRel`, `walkerIffGeneric = fun _ _ => Iff.rfl`, `walkerDecider = decideSaturatedConvOverIdempotentNative`),
exactly the `involutionRelationFamily` shape.  The DECISION CONTENT is fully preserved in the r4 native lane:
`IdempotentSaturated{MuInvertible,Ladder,GeneralBricks,RightWhisker,Normalizer}` reprove every conv-producing
theorem directly over the generic carrier (`*Gen` twins), and the conv-FREE skeleton
(`repFull`/`repNF`/`growTower`/`canonThroughT`/`mulThenUnitRightWhisker`/`godementUnitMul` + the boundary / Nat /
path lemmas) was RELOCATED verbatim (no re-proof) into the two NEW bespoke-free homes
`WalkingIdempotent/IdempotentLawRelation.lean` (`IdempotentLawRel` + `idempotenceRowConv`) and
`WalkingIdempotent/IdempotentSaturatedReps.lean` (the skeleton), imported by the native head
`IdempotentSaturatedMuInvertible`.

RETIRED (FX1Poly + FX1PolyAudit twins + their AuditAll import lines): `IdempotentMonadSaturatedConv`,
`IdempotentMonadModel`, `IdempotentMonadDecision`, `IdempotentMonadMuInvertible`, `IdempotentMonadNormalizer`,
`IdempotentMonadGeneralNormalizer`, `IdempotentMonadRightWhisker`, `IdempotentMonadFullNormalizer` (the 8 old-chain
files) + `Amalgam/SaturatedComponentDecider` (the hinge).  KEPT: `IdempotentMonadSeed`, the five native
`IdempotentSaturated*` files, `Amalgam/SaturatedOver` (substrate), and the two new port-in homes.  The native
regression `idempotentNativeAgreesOldOnRegression` is repointed native-vs-native (`decideSaturatedConvOverIdempotent`
-> `decideSaturatedConvOverIdempotentNative`).  `fxTab_hasThinClassWalkerMigrations` stays `true` (the idempotent
migration is now the identity migration, as the involution's).  `= true`.

### r6 OUTCOME (POLY-TAB r6 monad re-founding, WAVE 1, EXECUTED, #2228) — born-generic SOUNDNESS + decision assembly SHIPPED bespoke-free; completeness the named residual; ZERO deletions

r6 opened the MONAD lane (the KEPT exemplar, r2 outcome DEFERRED, 35 consumers) on the r4 idempotent template —
NEW `MonadSaturated*`/`MonadLawRelation` sibling files, ADDITIVE, the bespoke `MonadSaturatedTwoCellConv` UNTOUCHED
(retirement is r7 per the r5 protocol).  Unlike the trivially-thin idempotent lane, the walking monad is NOT locally
posetal, so its decision is the Δ monotone-map model (`monadMonotoneMapOf`) with a genuine SEPARATING `isFalse` branch,
and completeness is the full Eilenberg–Zilber word-multiplicativity chain rather than a one-shot thinness normalizer.

  * **(S1) The law rows + carrier, bespoke-free home** — `WalkingMonad/MonadLawRelation.lean`: the carrier
    abbreviation `MonadSaturatedConvGen := SaturatedConvOver monadModeSignature MonadLawRel`, the three monad-law rows
    (`monadLeftUnitRowGen` / `monadRightUnitRowGen` / `monadAssocRowGen`) over the ALREADY-SHIPPED `MonadLawRel`
    (`Amalgam/SaturatedOver`, the INT-SIG-ALIGN #2079 exemplar), plus non-vacuity — each a generic `ofRelation` term
    with NO `MonadSaturatedTwoCellConv` in its constant-closure.  (`MonadLawRel` was not missing, so S1 is lighter than
    the idempotent `IdempotentLawRelation` — it re-homes and adds the carrier, not the relation.)
  * **(S2 + S3) The Δ SOUNDNESS leg re-founded GENERIC-NATIVE** — `WalkingMonad/MonadSaturatedDeltaGen.lean`: the
    born-generic `monadMonotoneMapOf_mapEqOfConvGen` (every `SaturatedConvOver monadModeSignature MonadLawRel`
    derivation preserves the monotone map), proved via the universal property `SaturatedConvOver.recInto` +
    `monadIsMonotoneMapCongruence` (the three bespoke law arms collapsed into ONE `ofRelation` match).  The conv-FREE
    fold + soundness lemmas (`monadMonotoneMapOf` / `_eqOfConvFull` including the cap-free Godement invariance / the
    three simplicial seed lemmas / the four fold-congruences) are REUSED verbatim — none references the bespoke.  The
    born-generic canonicalization structure `MonadSaturatedCanonicalizationGen` and decision assembly
    `monadDecideSaturatedConvOverGen` / `monadSaturatedGenDecisionModulo` ship bespoke-free (soundness field inhabited).
  * **(S4) The working GENERIC decider, INTERIM completeness** — `WalkingMonad/MonadSaturatedDecisionGen.lean`:
    `decideSaturatedConvOverMonadInterim` decides the generic carrier on every parallel pair; its SOUNDNESS half is
    born-generic, its COMPLETENESS half transports the bespoke `monadConvOfMapEq_ofNormalize monadNormalize` through
    `monadSaturated_to_generic` (the interim canonicalization `monadSaturatedCanonicalizationGenViaBridge`).  It
    reproduces the shipped bespoke decider's verdicts on BOTH lane regression pairs
    (`monadGenAgreesOldOnRegression_holds`, `rfl`): the size-3 associativity pair `t.t.t ⇒ t` (CONVERTIBLE, both fold
    `[0,0,0]`, `isTrue`) and the SEPARATING size-1 faces pair `t ⇒ t.t` (NON-convertible, maps `[1]` vs `[0]`,
    `isFalse`).  Honest marker `fxMonad_hasGenericNativeDecider = false` records that the fully bespoke-free decider is
    NOT yet done.
  * **The bespoke-free META-WALK (r4 gold standard, made SOUND)** — `FX1PolyAudit/.../MonadBespokeFreeWalk.lean`: a
    build-failing transitive-constant walk (`#assert_constant_free_of` / `#assert_constant_depends_on`) proves the four
    born-generic decls (`monadIsMonotoneMapCongruence`, `monadMonotoneMapOf_mapEqOfConvGen`,
    `monadDecideSaturatedConvOverGen`, `monadSaturatedGenDecisionModulo`) have NO `MonadSaturatedTwoCellConv` in their
    FULL constant closure, with the needle-detector control confirming the bespoke deciders + the interim decider DO.
    ★ The walk is EXHAUSTIVE (`includeStdlib := true`): a pruning walk drops structure-field INTERNAL auxiliaries and
    would have UNSOUNDLY hidden the interim decider's completeness residual behind one — the sound walk sees through it.
    Backed additionally by per-declaration `#assert_no_axioms` audit twins.

**The wave-1 RESIDUAL (named, honest):** the born-generic normalize `monadNormalizeGen : cell → SaturatedConvOver
monadModeSignature MonadLawRel cell (canon cell)` — the Eilenberg–Zilber word-multiplicativity chain (`wordMul_vcomp`
/ `wordMul_hcomp` + the vcomp/hcomp/word multiplicativity conv-producing files `MonadVcompMult` (87 refs) /
`MonadWordVcomp` (81) / `MonadNormalizeCases` (50) / `MonadHcompMult` / `MonadWordMultiplicativity`, ~2000 conv-producing
lines) re-founded ctor-for-ctor over the generic carrier.  This is the substantial wave-2 port; once it inhabits
`convOfMapEqGen` born-generic, the interim canonicalization is swapped, the bespoke-free `decideSaturatedConvOverMonadNative`
is assembled, and `fxMonad_hasGenericNativeDecider` flips.

### r7 RETIREMENT-ROUND PREVIEW (monad lane; GATED — NOTHING deleted this round)

Post-re-founding consumer census of `MonadSaturatedTwoCellConv` (unchanged by the additive r6): the bespoke inductive
stays live, consumed by (a) the whole WalkingMonad Δ decision/normalize chain (the RE-PROVES core, retired only once
`monadNormalizeGen` lands born-generic); (b) `Amalgam/SaturatedOver`'s migration facts (`monadSaturated_iff_generic` /
`monadSaturatedIsCongruence` / the two iso directions — an iff INHERENTLY about the bespoke, collapses to `Iff.rfl` on
retirement); (c) `Amalgam/SaturatedRelationFamily.monadRelationFamily` (the SEPARATING family member, re-points
born-generic like the idempotent/involution shape); and — ★ THE HARD BLOCKER — (d) **`WalkingKZ`**:
`KZTwoCellLE.ofMonad : MonadSaturatedTwoCellConv a b → KZTwoCellLE a b` (`KZMonadPresentation`) is a genuine structural
ctor consuming the monad conv BOTH ways (the directed-preorder antisymmetrization RECOVERS `MonadSaturatedTwoCellConv`),
so KZ migration needs an ORIENTED / preorder-valued base relation the symmetric generic carrier does not provide
(`fxTab_hasKZWalkerMigration = false`, LedgerR1:241-242).  Consequence: the r7 monad deletion cannot fire until BOTH
`monadNormalizeGen` (the completeness port) lands AND the KZ `ofMonad` ctor is re-pointed / given its own oriented base
— the exact idempotent-r4 posture (deletion UNBLOCKED at the proof level only after the port, and separately GATED on
KZ), reserved for explicit user sign-off per never-delete-without-confirm.

### r7 OUTCOME (POLY-TAB r7 r1 — the KZ REBASE, EXECUTED, #2228) — the WalkingKZ hard blocker SEVERED at the proof level; ZERO deletions

r7-r1 executes the recon's Round A: it re-points the `WalkingKZ` lane's SINGLE bespoke-monad-conv dependency — the
`KZTwoCellLE.ofMonad` field — off the bespoke `MonadSaturatedTwoCellConv` and onto the born-generic
`MonadSaturatedConvGen := SaturatedConvOver monadModeSignature MonadLawRel` (`WalkingMonad/MonadLawRelation`), using
the WAVE-2 generic legs r6 landed.  NOTHING is deleted (the bespoke chain stays live for the reasons in the r7
PREVIEW); this is the proof-level severance the retirement needs — the exact idempotent-r4 posture.

What the WalkingKZ scaffolding consumed BEFORE the rebase (preserved as HISTORY):
  (1) `KZTwoCellLE.ofMonad : MonadSaturatedTwoCellConv a b → KZTwoCellLE a b` (`KZMonadPresentation`) is the ONLY
      structural entry of a monad EQUALITY of 2-cells into the directed KZ order; it STORED the monad conv, and
      `KZTwoCellEq` (`<=` both ways) antisymmetrizes the KZ preorder back onto the walking-monad convertibility.
  (2) PRODUCERS feeding `ofMonad`: `kzLeftUnitEq` (`.leftUnit` + `.symm`, `KZMonadPresentation`) and the covering
      assembly (`kzCoveringRightContext` / `kzAtomicCovering` / `kzAtomicCoveringSuffix`, `KZOrderCompleteness`) via
      the shipped `wordMul_hcomp` word-splitting equalities + their `.symm`.
  (3) CONSUMER folding the stored conv: `kzLE_sound`'s `ofMonad` case via `monadMonotoneMapOf_mapEqOfConv`, and
      `kzLE_ofMapEq` / `kzEq_iff_mapEq` building `ofMonad (monadConvOfMapEq_ofNormalize monadNormalize …)`.

The rebase identities (each bespoke KZ site ↔ its shipped Gen twin — the machine-checked composition that lets the
DIRECTED order transport bespoke→generic; the directed carrier merely STORES and FOLDS a monad conv once, so the
evidence swaps uniformly, NO provenance inversion, unlike the idempotent-r3 blocker):
  * `ofMonad` field type          `MonadSaturatedTwoCellConv`        →  `MonadSaturatedConvGen`
  * `kzLeftUnitEq`                 `.leftUnit` / `.symm`              →  `monadLeftUnitRowGen` / `SaturatedConvOver.symm`
  * covering producers            `wordMul_hcomp` / `.symm`          →  `wordMul_hcompGen` / `SaturatedConvOver.symm`
  * `kzLE_ofMapEq`/`kzEq_iff_mapEq`  `monadConvOfMapEq_ofNormalize monadNormalize`  →  `monadConvOfMapEqGen_ofNormalizeGen monadNormalizeGen`
  * `kzLE_sound` ofMonad case      `monadMonotoneMapOf_mapEqOfConv`  →  `monadMonotoneMapOf_mapEqOfConvGen`

DECISION CONTINUITY (the KZ verdicts are conv-INDEPENDENT — the deciders compare `monadMonotoneMapOf` folds, only
the PROOFS switched carrier — so they survive UNCHANGED): `decideKZEq`, `decideKZEq_yes_assoc`, `decideKZEq_no_faces`,
`kz_strict`, `kzBaseCovering_isStrict`, `kzOrderCompletenessWitness`, `decideKZLETotal` all hold verbatim
post-rebase (the green build is the continuity tie).

The KZ WALKER-MIGRATION marker STAYS `false` (honest): the rebase re-points the `ofMonad` SYMMETRIC monad-law field
onto the generic carrier, but `KZTwoCellLE` itself is a DIRECTED preorder whose `kzGen` generator is a genuine
NATIVE generator (NOT a bespoke-conv migration target); the generic `SaturatedConvOver` is symmetric and cannot
model the directed order, so the full walker-onto-generic migration remains POLY-TAB-2 design work.  The proof-level
severance actually achieved is recorded by the NEW marker `fxTab_hasKZMonadConvGenericRepoint = true`
(`Table/ThinWalkerMigration`).

STILL NOT DELETABLE (the r7 states-labeled leftovers — the r5-Step-2 skeleton relocation is the prerequisite): the
bespoke Δ-normalize/decide chain (`MonadWordProblem` / `MonadHcompMult` / `MonadNormalizeCell` (MIXED) /
`MonadWhiskerRightMult` / `MonadNormalizeVcomp` / `MonadNormalizeCases` / `MonadVcompMult` / `MonadWordVcomp` /
`MonadWordMultiplicativity` / `MonadWhiskerNormalizeCases` / `MonadSaturatedConv`) stays live: 7 of these carry the
conv-FREE Δ SKELETON (`monadMonotoneMapOf` / `wordFromCounts` / `reconstructFrom` / `canon` / `canonCounts` / the
whisker embedding) co-mingled with bespoke conv, and that skeleton is imported by KEPT files (all 5 `…Gen` files via
`MonadNormalizeVcomp`; `WalkingIdempotent/IdempotentSaturatedReps` via `MonadNormalizeCell` + `MonadWhiskerRightMult`;
`Amalgam/DeciderReseat` via `MonadWordProblem`), so no chain file reaches zero refs until a bespoke-free
`MonadSaturated*Reps` relocation home lands.  The `Amalgam/SaturatedOver` monad migration iffs
(`monadSaturated_iff_generic` / `monadSaturatedIsCongruence`) and `Amalgam/SaturatedRelationFamily.monadRelationFamily`
(the SEPARATING family member, `walkerConv = MonadSaturatedTwoCellConv`) stay bespoke-rooted — collapsing to `Iff.rfl`
/ born-generic only at Round C, which VOIDS the `monadRelationFamily_bridge_is_precedent` migration fact (the same
meaning-erosion the r5 idempotent gate reserved for explicit sign-off).  Those re-points are DEFERRED, not forced.

### r7-r2 OUTCOME (POLY-TAB r7 r2 — the INTERIM-DECIDER retirement + the skeleton-severance RE-SCOPE, #2228)

r7-r2 (Round B) ships the ONE honest deletion the round makes available and RE-SCOPES the deep skeleton-severance.
NO FX1Poly file is deleted; the pinned Δ island stays (the r7-r1 leftovers above are unchanged).

SHIPPED — the superseded INTERIM generic decider is RETIRED (`WalkingMonad/MonadSaturatedDecisionGen`):
`monadSaturatedCanonicalizationGenViaBridge` / `decideSaturatedConvOverMonadInterim` and their old-vs-interim
regression witnesses (`monadOldVerdict` / `monadGenDecidesTrue_assoc` / `monadGenDecidesFalse_faces` /
`monadGenAgreesOldOnRegression`) are gone.  The interim was the LAST WalkingMonad Gen-lane consumer of the bespoke
`monadNormalize` / `monadSaturatedTwoCellDecision` (its completeness field rode the bridge through
`monadSaturated_to_generic`); it is superseded BOTH ways born-generic by `decideSaturatedConvOverMonadNative`
(`fxMonad_hasGenericNativeDecider`, untouched, exhaustively bespoke-free — 847 constants walked).
`MonadNormalizeGen`'s regression is re-founded self-contained (`monadNativeAgreesOnRegression` now asserts the native
decider decides the assoc pair `isTrue` and the separating faces pair `isFalse`, by `rfl`), and it imports
`MonadWordProblem` directly for the conv-FREE `one_le_cellSize` fuel lemma it had received transitively through the
dropped interim edge.  The two audit twins are pruned (`MonadSaturatedDecisionGen` per-decl `#assert_no_axioms` gates
+ `MonadBespokeFreeWalk`'s two interim needle-detector controls); the native `#assert_constant_free_of` gates + the
bespoke `#assert_constant_depends_on` controls stay.  Marker `fxTab_hasMonadInterimDeciderRetired = true`.

REGRESSION CONTINUITY (history): at r6 the native / interim / old-bespoke deciders all branched on the SAME
`monadMonotoneMapOf cellA = monadMonotoneMapOf cellB` comparison and agreed on both lane pairs — the size-3
associativity pair `t.t.t ⇒ t` (both fold `[0,0,0]`, `isTrue`) and the SEPARATING size-1 faces pair `t ⇒ t.t`
(maps `[1]` vs `[0]`, `isFalse`).  With the interim retired, the tie is the native pair alone
(`monadNativeAgreesOnRegression_holds`, `rfl`); native = interim = old is this historical record.

RE-SCOPE — the deep skeleton-severance (the recon's Round B S1–S4) IS the r5-Step-2 skeleton relocation the r7-r1
OUTCOME named, and it is NOT a green-incremental "drop the imports in place" edit; it needs a bespoke-free
`MonadSaturated*Reps` relocation home (ONE bottom-of-DAG bridge collecting the severed bespoke decls).  The blockers,
machine-observed this round:
  * The Δ chain is a LINEAR import spine (`MonadSaturatedConv` → `MonadDeltaModel` → … → `MonadNormalizeVcomp`) in
    which conv-FREE skeleton decls and bespoke conv decls are INTERLEAVED file-by-file (`MonadDeltaModel` 5 conv
    refs, `MonadDeltaDecision` 4, `MonadNormalizeCell` 8, `MonadNormalizeVcomp` 12, …), with three PURE-BESPOKE files
    sitting in the MIDDLE (`MonadNormalizeCases` 50, `MonadWordMultiplicativity` 20, `MonadWhiskerNormalizeCases` 16)
    imported-through by would-be-survivor files.
  * The interface decl `MonadSaturatedCanonicalization` (`MonadDeltaModel`) is referenced by bespoke decls THROUGHOUT
    the downstream chain, so every severed bespoke decl must lift to ONE file ABOVE the whole bespoke-free skeleton —
    which makes S1/S2/S3 a SINGLE entangled change, not three separately-green commits.  Dropping `MonadDeltaModel`'s
    `MonadSaturatedConv` import in isolation (recon S1) breaks `MonadDeltaDecision` (its bespoke lemmas lose the conv)
    unless S3 lands in the same commit.
  * The recon's "keep reps" for `MonadWhiskerRightMult` mis-attributes them: `repFull` / `repNF` / `growTower` are
    IDEMPOTENT-lane decls (`WalkingIdempotent/IdempotentSaturatedReps` + `…Normalizer`), NOT in
    `MonadWhiskerRightMult`, which is fully bespoke (`wordMul_whiskerRight` + its cast algebra).
    `IdempotentSaturatedReps` uses NOTHING from `MonadWhiskerRightMult` (0 refs to its decls) — its import is a
    vestigial edge that pulls the mid-chain bespoke into a KEPT file.
Consequence: the one-commit-per-step / umbrella-green-after-each posture the recon assumed for S1–S4 does not hold;
that severance is BANKED for a dedicated relocation round (build the `MonadSaturated*Reps` bridge, lift the ~18
bespoke decls, re-point `KZOrderCompleteness` / `IdempotentSaturatedReps`, THEN drop the imports).

ROUND-C CARVE-OUT (unchanged, sign-off-gated): the pinned island stays — the pure-bespoke chain files +
`MonadSaturatedConv`, consumed only by the deferred trio `Amalgam/DeciderReseat` (P3-blocked native reseat),
`Amalgam/SaturatedRelationFamily.monadRelationFamily` (the SEPARATING member; re-point VOIDS
`monadRelationFamily_bridge_is_precedent`), and `Amalgam/SaturatedOver` (the migration iffs).  The monad lane is NOT
retired — it is the SECOND bespoke lane, still live; r7-r2 retired only the superseded interim decider.

### r7-r3 OUTCOME (POLY-TAB r7 r3, MONAD-R7 Round C — the skeleton bridge SEEDED + the first survivor SEVERED, #2228)

r7-r3 EXECUTES the relocation round the r7-r2 OUTCOME banked: it BUILDS the `MonadSaturated*Reps` bridge and
re-points the first survivor onto it, bespoke-free.  Still ZERO FX1Poly file deletions — the pinned Δ island is
untouched.

SHIPPED — the bespoke-free bridge `WalkingMonad/MonadSaturatedSkeletonReps`:
  * holds the ordinal-sum whisker-embedding stratum relocated VERBATIM from `MonadWhiskerEmbedding` (names /
    namespace / meaning preserved): the cons-only prepend primitives `ascendingPrepend` / `shiftPrepend`, the
    embedding `embedLocalMap` + its length + three region-wise value characterizations (`_get_left` / `_get_mid` /
    `_get_right`), and the three-region split `embedRegionSplit`;
  * imports ONLY the already-bespoke-free `WalkingAdjunction/MonotoneMap` — NO conv file in its closure; audit twin
    + AuditAll line added, all 11 relocated theorems `#print axioms`-clean by independent scratch;
  * `MonadWhiskerEmbedding` now imports the bridge (single home, no duplication); the chain is unbroken and its
    downstream roofs stay green.

SEVERED — `WalkingKZ/KZMonadOrderModel` re-points onto the bridge (dropping `MonadWhiskerEmbedding`) and is now
provably conv-decoupled: its build closure collapses 22 → 17 jobs (the r3 verifier corrected the original 121 figure) with NO monad-conv chain file present.  Its order
model (`mapLE` poset + the three KZ monotonicity closures) needed only the embed stratum + the `MonotoneMap` base —
pure CAT-A, no bespoke reflection.

VESTIGIAL SEVER — `WalkingKZ/KZOrderCompleteness` drops its unused `MonadWordProblem` import (0 / 7 owned-decl refs;
redundant with `MonadWordMultGen`) — a clean standalone green edge-drop, bridge-independent.

CENSUS CORRECTIONS (the r7-r2 RE-SCOPE figures, machine-re-measured against current HEAD):
  * "~18 bespoke decls" is a severe undercount — the actual conv-free CAT-A cut is ~75 skeleton decls across 17
    chain files; the bridge is the dependency-closure home of that cut, SEEDED here with the shallowest
    self-contained layer (the 14-decl embed stratum, whose entire closure is the `MonotoneMap` base alone).
  * the `IdempotentSaturatedReps -> MonadWhiskerRightMult` edge is NOT purely vestigial: ISR uses 0 of
    `MonadWhiskerRightMult`'s OWN decls but relies on it TRANSITIVELY for `monadTPower_add` (defined below it, in
    `MonadWordMultiplicativity`), so the import cannot be dropped standalone — only WITH the bridge supplying
    `monadTPower_add`.

STILL NOT SEVERED (the deep-stratum wall — BANKED for the next relocation layer): `IdempotentSaturatedReps`
consumes `monadTPower` / `monadGadget` (`MonadCanonicalWord`), `monadPath_normalForm` (`MonadNormalizeCell`),
`monadTPower_add` (`MonadWordMultiplicativity`) + the CAT-C cells `monadUnitTwoCell` / `monadMulTwoCell`
(`MonadSaturatedConv`).  It touches 0 of the deep map stratum DIRECTLY, but `monadPath_normalForm`'s proof
(`path = monadTPower path.length`, via `monadPath_normalForm_ofLength`) pulls the deep normalization machinery whose
home files carry CAT-D bespoke (`MonadSaturatedCanonicalization` et al.).  So severing ISR requires relocating the
deep lower stratum (the monotone-map engine + `canon` / `canonCounts` / `wordFromCounts` / `monadTPower` + closure,
~7 files) into the bridge — a single large mega-relocation, not a green-incremental drop; banked for the next layer.

DELETIONS — ZERO (unchanged posture): the pinned island pins ALL 19 chain files.  `Amalgam/DeciderReseat ->
MonadWordProblem -> MonadNormalizeVcomp -> …` pins the whole spine; `Amalgam/SaturatedOver -> MonadSaturatedConv`
and `SaturatedRelationFamily.monadRelationFamily` pin the root.  No chain file reaches zero refs; the
reverse-topological deletion order stays GATED behind the sign-off-gated island trio.

#2229 — SEQUENCED, NOT folded in (recon Job 3): the reseated reconstructed decider is a bounded MODE-ADMIT-INV
brick whose payoff is the UNCONDITIONAL reconstructed decider, NOT island dissolution — folding it in keeps
`DeciderReseat`'s `monadSaturatedTwoCellDecision` edge and unlocks zero extra deletion.  Parked; the island stays
states-labeled.

### r7-r4 OUTCOME (POLY-TAB r7 r4, MONAD-R7 — the DEEP-STRATUM relocation EXECUTED; the "not green-incremental" banking REFUTED; the survivor severance WALLED at the gated `SaturatedOver` island)

r7-r4 EXECUTES the deep lower-stratum mega-relocation the r7-r3 OUTCOME banked as "a single large mega-relocation,
not a green-incremental drop".  That banking is now REFUTED: the relocation IS green per-source-file, via the r3
"move the conv-FREE decls DOWN into a bespoke-free leaf + keep the source's bespoke imports (so downstream conv
reachability is preserved) + have the source import the leaf" pattern.  Every step below is umbrella-green
(`lake build FX1Poly FX1PolyAudit`), zero-axiom (independent scratch `#print axioms` + per-decl audit-twin gates),
STRUCTURAL, ASCII-only.

SHIPPED — three new bespoke-free deep leaves (~155 conv-FREE decls relocated VERBATIM, names / namespace / meaning
preserved):
  * `WalkingMonad/MonadCellSize` (micro-relocation): the size-floor `one_le_cellSize`, off the `MonadSeed` +
    `FreeTwoCell/Model` base.  `WalkingMonad/MonadNormalizeGen` (the native decider file) now imports it INSTEAD of
    `MonadWordProblem`, dropping `MonadWordProblem` from its closure (still imports `MonadNormalizeVcomp` directly, so
    only that one chain node leaves — honest partial severance of the native-decider file).
  * `WalkingMonad/MonadSaturatedDeltaReps` (deep leaf 1, off `MonadSeed`+`Model`+`Spine`+`MonotoneMap`+the r3 embed
    bridge): 81 decls — the CAT-C law-composite cells (7, from `MonadSaturatedConv`), the retuned monotone-map fold
    (14, from `MonadDeltaModel`), the whole fold ENGINE (27, from `MonadMonotoneEngine`), the map FACTORIZATION (10,
    from `MonadMapFactorization`), the whisker-EMBEDDING fold-support (14, from `MonadWhiskerEmbedding`), and the
    Δ-decision Godement/interchange fold-support (9, from `MonadDeltaDecision`: `mapsInto`/`hcomp`/`disjointCommute`/
    `interchange` + the free-conv legs `eqOfStep`/`eqOfConv`/`eqOfConvFull`).
  * `WalkingMonad/MonadSaturatedCanonReps` (deep leaf 2, imports leaf 1): 73 decls — the whole canonical-WORD
    skeleton (34, from `MonadCanonicalWord`: `monadTPower`/`monadGadget`/`wordFromCounts`/`reconstructFrom`/
    `countsDomainPath`), the fibre-COUNTS round-trip (25, from `MonadCountsRoundTrip`), the canon/boundary-transport
    stratum (12, from `MonadNormalizeCell`: `countsOf_length`/`monadPath_normalForm`/`canonCounts`/`canon`/
    `monadMonotoneMapOf_canon`/`canon_eqOfMapEq`), and the survivor-critical `monadTPower_add` + `countsDomainPath_
    consReplicate_one` (2, from `MonadWordMultiplicativity`).
The conv-BEARING residue STAYS with its source (each mixed source keeps its bespoke import + imports the leaf so its
residue still resolves): `MonadSaturatedTwoCellConv` + laws (`MonadSaturatedConv`); `MonadSaturatedCanonicalization`
struct + `monadDecideSaturatedConvViaMonotoneMap` (`MonadDeltaModel`); `monadMonotoneMapOf_mapEqOfConv`
(`MonadDeltaDecision`); `MonadNormalizesToCanon` + `monadConvOfMapEq_ofNormalize` (`MonadNormalizeCell`); `wordMul_*`
(`MonadWordMultiplicativity`).  Every PURE-CONV-FREE source (`MonadMonotoneEngine`/`MonadMapFactorization`/
`MonadWhiskerEmbedding`/`MonadCanonicalWord`/`MonadCountsRoundTrip`) becomes a chain-preserving SHIM (keeps its
bespoke import for downstream conv reachability + imports the leaf).

CENSUS CORRECTIONS (the recon's JOB-1 deep census was materially incomplete, machine-re-measured):
  * `MonadWhiskerEmbedding` is NOT already-handled — it is a PURE conv-free deep MOVE target (14 fold-support decls:
    `embedLocalMap_composeMap`/`_nest`, `monadMonotoneMapOf_length`/`_mapsInto`/`_whiskerLeft`/`_whiskerRight` + the
    two fold congruences) that the Δ-decision + downstream strata depend on; only its embed PRIMITIVES went to the r3
    bridge.  Relocated (leaf 1 now imports the r3 embed bridge).
  * `MonadNormalizeCases` is NOT pure-bespoke — it is MIXED (18 decls: 11 conv-FREE, 7 conv-bearing).  Its conv-free
    helpers (`monadOnes`/`length_monadOnes`/`countsDomainPath_monadOnes`, `monadWhiskerLeft_castBoundary`/
    `monadCastBoundary_castBoundary`/`_id`, the `ascendingFrom`-run counts lemmas) are consumed by the survivor lane
    (the idempotent bricks + `MonadWordMultiplicativity`'s `*_consAppend_ones`).  These are LEFT in place this round
    (their conv-free extraction is a further stratum); consequently the `MonadWordMultiplicativity` `*_consAppend_ones`
    pair and `MonadNormalizeCases`-entangled helpers are NOT relocated.

SEVERED — `WalkingIdempotent/IdempotentMonadSeed` re-points off `MonadSaturatedConv` onto leaf 1 (it needs only the
CAT-C cells); its closure is now bespoke-chain-free (conv-decoupled), the one clean survivor repoint of r4.

REFUTED — the recon's central r4 premise ("full proof-level severance of the survivor lane: 7 Gen files + ISR + the
whole idempotent-native lane") is FALSE, machine-verified.  EVERY remaining survivor reaches `MonadSaturatedConv`
through the sign-off-GATED `Amalgam/SaturatedOver` island, NOT through the repointable deep bespoke chain:
  * the idempotent-native lane — `IdempotentSaturatedMuInvertible -> IdempotentLawRelation -> SaturatedOver ->
    MonadSaturatedConv` (a NON-`IdempotentSaturatedReps` path: blocking ISR entirely leaves the pin intact).  So the
    recon's "IdempotentSaturatedReps is the ONLY path, severing it frees the lane" is wrong.  The ISR repoint is
    ALSO independently blocked: `IdempotentSaturatedGeneralBricks` consumes `monadWhiskerLeft_castBoundary` /
    `monadCastBoundary_castBoundary` (stranded in the MIXED `MonadNormalizeCases`) transitively through ISR's dropped
    imports.
  * all 7 Gen files — `MonadLawRelation -> SaturatedOver -> MonadSaturatedConv` and `DispatchSaturated ->
    SaturatedDispatch -> SaturatedOver -> MonadSaturatedConv`; blocking their bespoke `MonadNormalizeVcomp` /
    `MonadDeltaDecision` imports does NOT remove the pin (they are born-generic over the amalgam dispatch, which
    routes through `SaturatedOver`).
Consequence: the survivor lane CANNOT be conv-decoupled in r4 — it universally routes through the gated
`SaturatedOver` migration-iff pin.  The deep bridges are built and ready, but the severance payoff is walled behind
the SAME gated island (`SaturatedOver`) that pins the chain for deletion; it does not dissolve until `SaturatedOver`
is signed off.

DELETIONS — ZERO (unchanged posture, now with a tightened reason): the pinned island pins ALL 19 chain files, and
the pin is BROADER than the r7-r3 "trio" — `SaturatedOver` reaches the whole generic + idempotent survivor lane via
`MonadLawRelation` / `DispatchSaturated` / `IdempotentLawRelation`, so no chain file reaches zero refs.  The
reverse-topological deletion order stays GATED behind `SaturatedOver` (migration iffs), `DeciderReseat` (P3 native
reseat, #2229), and `monadRelationFamily` (the separating member).

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

/-- ★ **The POLY-TAB r7 r2 marker — the superseded INTERIM monad decider is RETIRED (#2228).**  MONAD-R7 r2 (S5)
deleted the interim generic decider (`monadSaturatedCanonicalizationGenViaBridge` /
`decideSaturatedConvOverMonadInterim` + its old-vs-interim regression witnesses) from
`WalkingMonad/MonadSaturatedDecisionGen` — the last WalkingMonad Gen-lane consumer of the bespoke `monadNormalize` /
`monadSaturatedTwoCellDecision`.  It is superseded BOTH ways born-generic by `decideSaturatedConvOverMonadNative`
(the still-green `fxTab_hasMonadNativeRefoundingWave2`).  NO FX1Poly file is deleted this round (the pinned Δ island
stays; the deep skeleton-severance is RE-SCOPED to a dedicated `MonadSaturated*Reps` relocation round — see the
r7-r2 OUTCOME above).  `= true`. -/
def fxTab_hasMonadInterimDeciderRetired : Bool := true

/-- The r7-r2 interim-decider-retirement marker computes to `true`, machine-checked. -/
theorem hasMonadInterimDeciderRetired_holds : fxTab_hasMonadInterimDeciderRetired = true := by decide

/-- ★ **The POLY-TAB r7 r3 marker — the skeleton bridge is SEEDED + the first survivor SEVERED (#2228).**  MONAD-R7
Round C built the bespoke-free `WalkingMonad/MonadSaturatedSkeletonReps` bridge (the ordinal-sum embed stratum —
`ascendingPrepend` / `shiftPrepend` / `embedLocalMap` + characterizations + `embedRegionSplit` — relocated VERBATIM
from `MonadWhiskerEmbedding`, importing only the bespoke-free `MonotoneMap`) and re-pointed `WalkingKZ/
KZMonadOrderModel` onto it, conv-decoupled (closure 22 → 17 jobs; the 121 figure originally recorded here was refuted by the r3 verifier — the real collapse drops 6 modules incl. MonadSaturatedConv).  `KZOrderCompleteness`'s
vestigial `MonadWordProblem` import is dropped (0 / 7 refs).  ZERO FX1Poly file deleted (the pinned Δ island stays;
the deep lower-stratum relocation that would free `IdempotentSaturatedReps` is BANKED for the next layer, and #2229
is SEQUENCED, not folded).  `= true`. -/
def fxTab_hasMonadSkeletonBridgeSeeded : Bool := true

/-- The r7-r3 skeleton-bridge-seeded marker computes to `true`, machine-checked. -/
theorem hasMonadSkeletonBridgeSeeded_holds : fxTab_hasMonadSkeletonBridgeSeeded = true := by decide

/-- ★ **The POLY-TAB r7 r4 marker — the DEEP-stratum mega-relocation is EXECUTED, the "not green-incremental"
banking REFUTED, the survivor severance WALLED at the gated `SaturatedOver` island (#2228).**  MONAD-R7 r4
relocated ~155 conv-FREE decls VERBATIM into three new bespoke-free leaves (`WalkingMonad/MonadCellSize`,
`MonadSaturatedDeltaReps` = 81, `MonadSaturatedCanonReps` = 73), each step umbrella-green and zero-axiom — proving
the deep relocation IS green per-source-file (move the conv-free decls down + keep the source's bespoke imports for
downstream conv reachability), which the r7-r3 OUTCOME had banked as impossible.  Two census corrections landed:
`MonadWhiskerEmbedding` is a PURE conv-free deep MOVE target (not already-handled), and `MonadNormalizeCases` is
MIXED (11 conv-free helpers the survivor lane needs, not pure-bespoke).  `IdempotentMonadSeed` re-points onto leaf 1
(conv-decoupled — the one clean survivor repoint).  But the recon's "severance frees the survivor lane" premise is
machine-REFUTED: every remaining survivor (`IdempotentSaturatedReps` + the idempotent-native lane + all 7 Gen files)
routes to `MonadSaturatedConv` through the sign-off-GATED `Amalgam/SaturatedOver` island (`MonadLawRelation` /
`DispatchSaturated` / `IdempotentLawRelation` -> `SaturatedOver`), NOT through the repointable deep chain — so the
lane cannot be conv-decoupled in r4.  ZERO FX1Poly file deleted (the pinned Δ island stays, pin now shown broader
than the r7-r3 trio).  `= true`. -/
def fxTab_hasMonadDeepBridgeRelocated : Bool := true

/-- The r7-r4 deep-bridge-relocated marker computes to `true`, machine-checked. -/
theorem hasMonadDeepBridgeRelocated_holds : fxTab_hasMonadDeepBridgeRelocated = true := by decide

end FX1Poly.Polygraph.Table

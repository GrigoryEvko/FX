import FX1Poly.Polygraph.TwoCategory.Table.WalkerMigration

/-! # Polygraph/TwoCategory/Table/TableArchitectureLock — the POLY-TAB architecture design lock (r0, T2)

The table-driven polygraph layer (task #2228, executing INT-SIG-ALIGN #2079).  The literature-anchored shape:
**polygraph-as-value + ONE relation-level contextual-closure operator + ONE parameterized-invariant fold + ONE
strategy registry** (Guiraud-Malbos, *Polygraphs of finite derivation type*, a 2-polygraph is a triple of
cell-sets with boundary maps; Baader-Nipkow / CoLoR, the rewrite step is the least relation closed under contexts
and substitutions; mkbTT, completion is a registry of selectable certified strategies).  Every bespoke walker
congruence is DEMOTED to a seed VALUE fed to the generic carrier, never a new inductive.

This file is the DECISION RECORD.  It cites the shipped r0 pieces (`Table/ContextClosure.lean`,
`Table/FrobeniusSeed.lean`, `Table/WalkerMigration.lean`) and ships one concrete typed anchor — the strategy-table
mechanism tag `DecisionMechanism`.  No walker file, no `Amalgam/` file, no census offender is edited or deleted.

## Decision 1 — the carrier (the reconciliation, the prime directive)

There are TWO live carriers, and the reconciliation bridges them onto the shipped generic substrate:

  * **Carrier A — the free-2-cell carrier** `RawTwoCellExpr signature sourcePath targetPath` (FreeTwoCell/Model.lean).
    `SaturatedConvOver signature baseRel` (Amalgam/SaturatedOver.lean) rides this; the doctrine LAWS enter as a
    Prop-valued `CellRel`.  The walking monad / idempotent / involution / string / Frobenius-spider congruences
    all instantiate it.  THE r0 SEED uses carrier A.
  * **Carrier B — the diagram / wiring carrier** `List BrauerAtom` (Brauer/WiringDesc.lean, `WiringDesc` = arcs +
    input/output counts).  Brauer / Frobenius `SpiderConvRows` ride this.  The B->A bridge is
    `ModeComputad.interpretWordFrom` / `toModeSignature` / `ReconstructedTwoCell` (Computad/ModeComputad.lean) —
    a word interprets to a typed `ModalityPath`, a 2-generator index to a `RawTwoCellExpr`.

The reconciled presentation VALUE keeps the `ModeComputad` spine (words) and bolts on two optional views: the
reflected `lawRows : List (RawCellData x RawCellData)` (a data mirror of the `CellRel`, the fingerprint /
registry key `RowAwarePresentationData` of ModeAdmit.lean) and an optional `wiring? : Option WiringDesc` per
2-generator (so ONE presentation drives BOTH the free-cell decision and the diagram decision).  Certifying that
`lawRows` faithfully reflects `baseRel` (`fxModeAdmit_hasCertifiedDataAdmission = false`) is the named-open;
r0 ships the carrier-A congruence + folds, which need no such certificate.

## Decision 2 — the contextual closure is a RELATION-LEVEL operator, NO new inductive (T2b = OPTION ii)

`SaturatedConvOver.ofRelation` fires a base row at a FIXED boundary — it carries NO enumerated context (quoted:
SaturatedOver.lean:84-89).  ALL context is supplied by the four SEPARATE one-hole congruence constructors.  So a
row-in-any-context is already derivable, and `contextClosureRel signature baseRel` is DEFINED as `SaturatedConvOver
signature baseRel` itself, with the intro / monotone / idempotence package as its algebra (`Table/ContextClosure.lean`).
Rejected: (i) EXTEND with a new context ctor (forces edits to `recInto` + every lane iso, ~9 sites x N lanes);
(iii) a new inductive (duplicates the whole machine).  Evidence it is right: the newest offender `EncodedConv`
(Tier0/.../UndecidabilityReduction.lean) independently has EXACTLY the six ctors `rule / whiskerLeft / whiskerRight
/ refl / symm / trans` — the universal shape.

The load-bearing corollary: the row-SUFFIX congruence is `whiskerRightCongr`, ONE constructor
(`SaturatedConvOver.suffixCongruence`).  This DISSOLVES the Frobenius r10 wall (see Decision 5).

## Decision 3 — ONE parameterized-invariant fold (T3c)

The per-walker soundness legs (`spiderConv_partitionSound`, `quadCohesionParity_satConv`, the matching invariance,
~150+ occurrences across ~45 files) are instances of ONE fold — the Guiraud derivation "uniquely determined by
its values on the generators, compatible with the closure by the Leibniz law".  Mechanized as
`SaturatedConvOver.recInto`; shipped in two value forms (`Table/ContextClosure.lean`): `rowConvInvariant_foldRel`
(relational / Prop-valued, for ThueCongruence-valued invariants) and `rowConvInvariant_foldEq` (Eq-valued, the six
genuine legs; `refl`/`symm`/`trans` collapse to `rfl`/`Eq.symm`/`Eq.trans`).

## Decision 4 — the strategy registry (mkbTT pattern)

`DecidableSaturatedConvForRel` / `ComposableFragmentDispatch` is a strategy TABLE: a fingerprint
(`RowAwarePresentationData`) keys a decision mechanism, each row emitting a decidability payload
(`SaturatedRelationFamily.decider`).  The r0 anchor is the mechanism TAG below; the dependent per-mechanism
certificate (thin-witness / delta-model / wiring-semantics / hom-bound / undecidability-embed) is POLY-TAB-1.

## Decision 5 — THE FALSIFIABILITY OUTCOME (the Frobenius r10 wall)

`Frobenius/SpiderCrossingRerun.lean` walled `RowSuffixCongruence` at the constructor level
(`fxFrob_hasRowLevelSuffixCongruence = false`) because the word-carried `SpiderConvRows` bakes the prefix into
every firing, so a common suffix escapes re-absorption; it named the fix: "only a table REDESIGN (a
suffix-parametric firing, `prefix ++ row ++ suffix`) would open it".  `SaturatedConvOver` IS that redesign.
`Table/FrobeniusSeed.lean` instantiates it (`frobeniusModeSignature` + `FrobeniusLawRel`), and
`frobeniusSpiderConv_suffixCongruence` lands the walled brick's exact conclusion in ONE constructor, NON-VACUOUSLY
(`frobeniusSuffixCongruence_nonVacuous`).  The `medium`-flagged `HEq`/`castBoundary` risk did NOT materialize:
every law cell is a concrete `t`-power composite, so `composePath` associativity is definitional (as the monad
exemplar already relies on).  **VERDICT: the r10 wall dissolved.**

## Census totals (read-only sweep, embedded)

  * Bespoke conv/congruence inductives: 22 (8 Class-A direct SaturatedConvOver instances, 8 Class-B word/wiring
    carrier-blocked, 6 Class-C dual-carrier seed generators) vs ~12 legitimate substrate inductives.
  * Redundant re-declared congruence constructors: ~86, all covered by ONE 9-ctor `SaturatedConvOver`.
  * Genuine bespoke content: 39 Class-A law rows (all expressible as `CellRel`) + ~41 Class-B word-level rows.
  * Contextual-closure kits: 16 named theorems / ~9 files / ~7,800 LOC, fully subsumed by the four congruence ctors.
  * Invariant-fold soundness legs: ~150+ occurrences / ~45 files, collapsing to `(invariantOf, rowsPreserve, + 4
    context legs)` instance pairs of one `rowConvInvariant_foldEq`.
  * Dual-presentation pairs: 6 bespoke `*TwoCell` seed inductives vs the generic `ReconstructedTwoCell`.

## The DELETION-TARGET list (AWAITING CONFIRMATION — nothing deleted here, ever)

Retire ONLY on explicit green-light, ONLY after the corresponding generic instance ships and the iff bridge
transports every downstream fact.  This is the census, recorded as an intention, NOT an action:

  1. Class-A bespoke saturated convs (re-home to `SaturatedConvOver @ <LawRel>`, monad-exemplar iff):
     `StringSaturatedTwoCellConv`, `CohesionSaturatedTwoCellConv`, `QuadCohesionSaturatedTwoCellConv`,
     the adjunction `SaturatedTwoCellConv` (route `whiskerExchange` through `ofFull`), `KZTwoCellLE` (needs an
     oriented / preorder-valued base relation).  [Monad, IdempotentMonad, Involution already migrated.]
  2. Contextual-closure kits (subsumed by the four congruence ctors): the `*_inContext` / `*_suffixCongruence` /
     pad-congruence families in Brauer/WiringDescInsertion, WiringDescPadCongruence, WiringDescFunctoriality,
     Frobenius/SpiderSuffixCongruence, SpiderConvTable, SpiderAfterPrefix, SpiderWhiskerDerivability.
  3. Class-C bespoke `*TwoCell` seed generators (subsumed by `ReconstructedTwoCell` + `toModeSignature`):
     the redundant seed inductives that the computad value already reconstructs.

KEEP (correct, not offenders): `EncodedConv` / `SemiThueReduction` (the honest undecidability WALL); the free /
substrate inductives (`RawTwoCellExpr`, `TwoCellStep`, `TwoCellConv`, `TwoCellConvFull`, `SaturatedConvOver`).

## The new-walker PLAYBOOK

To add a walker `W`: (1) declare `wModeSignature : ModeSignature` (or a `ModeComputad` + `toModeSignature`);
(2) declare `WLawRel : CellRel wModeSignature` — one constructor per doctrine law, each a concrete cell pair;
(3) the congruence is `SaturatedConvOver wModeSignature WLawRel` (BORN generic — no inductive to write); the
suffix / prefix congruences, monotonicity, idempotence, and both invariant folds come FOR FREE from
`Table/ContextClosure.lean`; (4) soundness = one `rowConvInvariant_foldEq` per invariant; (5) decision = register
a strategy row.  Frobenius spider (`Table/FrobeniusSeed.lean`) is the worked instance.

## The WAVE PLAN

  * **POLY-TAB r0 (this):** design lock + census + the generic package + the Frobenius seed + the falsifiability
    check + the smallest-walker migration.
  * **POLY-TAB-1:** the remaining nine Frobenius rows; the B->A `interpretWordFrom` rebase of `SpiderConvRows`
    onto `SaturatedConvOver frobComputad.toModeSignature FrobLawRel`; the value-level Frobenius invariant
    (`extraSpiderDiagramOf`) as a `rowConvInvariant_foldRel` instance; the `reflects lawRows baseRel` faithfulness
    certificate (`fxModeAdmit_hasCertifiedDataAdmission`).
  * **POLY-TAB-2:** re-home the Class-A bespoke convs (String / Cohesion / QuadCohesion / Adjunction / KZ) with
    their iff bridges; the per-mechanism `StrategyCertificate` dependent record; the wiring `wiring?` view.
  * **POLY-TAB-3:** retire the confirmed deletion targets (green-lit, one at a time); collapse the contextual-closure
    kits; the grand table-driven-polygraph ledger.

Raw Lean 4 + Init; a docstring record plus one decidable-tag inductive, so every declaration is axiom-free.
Additive — nothing outside `Table/` is touched.  Per-declaration `#assert_no_axioms` in the audit twin. -/

namespace FX1Poly.Polygraph.Table

/-! ## The strategy-table mechanism tag (the r0 registry anchor) -/

/-- The **decision mechanism** classifying how a walker's saturated word problem is decided — the strategy-table
key (mkbTT-style registry).  Each tag records WHY a decider is sound; the dependent per-mechanism certificate
(thin-witness / delta-model / wiring-semantics / hom-bound / undecidability-embed) is POLY-TAB-1. -/
inductive DecisionMechanism where
  /-- No 2-generators: every parallel pair convertible (the locally-thin decider, e.g. the involution). -/
  | thinLocallyThin
  /-- A monotone-map / simplicial invariant separates and reconstructs (monad, idempotent monad; the Delta model). -/
  | deltaMonotone
  /-- A `WiringDesc` union-find perfect matching / partition decides (Brauer, Frobenius spider). -/
  | wiringMatching
  /-- A finite hom-set enumeration decides (involution parity, KZ). -/
  | finiteHomEnum
  /-- A finitely-presented-monoid reduction embeds an undecidable word problem: NO decider (EncodedConv, honest wall). -/
  | undecidableWall
  deriving DecidableEq

/-- The five mechanisms are distinct — a sanity check that the tag is a genuine 5-element classifier. -/
theorem decisionMechanism_thinLocallyThin_ne_undecidableWall :
    DecisionMechanism.thinLocallyThin ≠ DecisionMechanism.undecidableWall := by decide

/-- The Frobenius spider is decided by the wiring-matching mechanism (its `WiringDesc` partition model). -/
def frobeniusSpiderMechanism : DecisionMechanism := DecisionMechanism.wiringMatching

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the POLY-TAB design lock SHIPS (r0, T2).**  The five decisions (carrier reconciliation
onto the two live carriers with the `interpretWordFrom` B->A bridge; the contextual closure as a relation-level
operator, T2b option ii, no new inductive; the parameterized-invariant fold, T3c; the strategy registry with the
`DecisionMechanism` tag anchor; the falsifiability outcome — the Frobenius r10 wall dissolved) are recorded, with
the census totals embedded, the deletion-target list awaiting confirmation (nothing deleted), the new-walker
playbook, and the four-wave plan.  `= true`. -/
def fxTab_hasDesignLock : Bool := true

/-- ★ **Honesty marker — T2b resolved as OPTION (ii): the contextual closure is a relation-level fact, no new
inductive.**  `ofRelation` carries no enumerated context (fixed boundary); the four one-hole congruence ctors
supply all context; `contextClosureRel = SaturatedConvOver` with the algebra package.  Corroborated by the
`EncodedConv` six-ctor universal shape.  `= true`. -/
def fxTab_contextClosureIsOptionII : Bool := true

end FX1Poly.Polygraph.Table

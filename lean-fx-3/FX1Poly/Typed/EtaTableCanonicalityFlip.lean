import FX1Poly.Typed.TableBetaEtaRootConfluence

/-! # EtaTableCanonicalityFlip — ETA-T7 ★: the table eta is the
kernel's OFFICIAL eta semantics + the modal/Glue gating REPAIR

**THE FLIP** (the eta twin of the IOTA-T9 `TableCanonicalityFlip`).
From this module on, the kernel's canonical eta is TABLE-DRIVEN:

  * `StepEtaRootTable` (root tier) and `StepEtaTable` (uniform child
    congruence) over the canonical `etaRuleTable` — eta rules as DATA,
    every metatheorem generic over rows;
  * the canonical beta-eta union is `StepTableBetaEtaRoot`
    (= `StepTable ∨ StepEtaRootTable`) with `UnionStar` its chains.

The bespoke `Step.eta` sibling inductive survives as a DERIVED LEGACY
VIEW pending the ETA-T9 retirement; the typed transports below carry
every legacy fact across the flip.

## THE SEMANTIC REPAIR (user-confirmed spec change)

The bespoke modal/Glue arms (`etaModIntro`/`etaGlueIntro`) fire
unconditionally on ANY raw term — the known raw over-approximation
(raw eta != type-sound eta).  The table rows for those two contractions
carry `requiresTypedFiring = true`, so the canonical raw relation
REFUSES them.  The canonical eta semantics therefore SHRINKS exactly on
the unsound firings and nowhere else:

  * `StepEtaRootTable.toBespokeEta` — the shrink is SOUND: every
    canonical raw root contraction is a legacy contraction (nothing new
    fires);
  * `HasTypeDescPi.bespokeEtaIffCanonicalEta` — on TYPED subjects the
    two relations COINCIDE: the canonical relation is exactly the
    type-sound fragment of the legacy one;
  * `bespokeEtaModalOverFiringRepaired` /
    `bespokeEtaGlueOverFiringRepaired` — the shrink is REAL: the
    legacy relation fires raw on closed modal/Glue cells where the
    canonical relation refuses (the ETA-T1 strictness pins, promoted to
    the official divergence record).

## The headline ledger (what the canonical eta relations carry)

* **Subject reduction** — `StepTableBetaEtaRoot.subjectReduction` /
  `.subjectReductionStar` (re-pointed below from the ETA-T6 masters):
  Pi-fragment typing survives every canonical beta-eta step at the
  EXACT classifier.
* **Strong normalization** — `stepEtaTable_wellFounded` (ETA-T3): the
  FULL congruent table eta is SN for ANY table by one generic size
  decrease; and `StepTableBetaEtaRoot.stronglyNormalizingTyped`
  (below): typed subjects are SN for the canonical beta-eta union via
  the Geser engine over the ETA-T5 commutation certificates.
* **Confluence** — `StepTableBetaEtaRoot.confluentTyped` (below, from
  ETA-T6): the Geuvers typed beta-eta Church-Rosser over table rows;
  raw beta-eta is honestly NON-confluent (the Nederpelt
  annotation-mismatch pair), so typing is the right gate.
* **Unique normal forms** —
  `StepTableBetaEtaRoot.uniqueNormalFormTyped` (below).
* **Postponement** — `accUnionOfTables` / the ETA-T5 quasi-commutation:
  root eta postpones over table iota generically in the row shapes.
* **Orthogonality** — `etaRuleTable_isWf` (ETA-T4): decidable
  certificates — distinct intro roots, observation slots within arity,
  and cross-table disjointness against `iotaRuleTable`.
* **Equivariance** — the ETA-T2 `contractsOn?` naturality under
  substitution and renaming, one template induction.

## Honest exclusions

* The full-CONGRUENCE eta tier enters typed conversion only through
  the eta-aware judgmental equality (NbE seam, #364/#481) — deep eta
  changes classifiers up to eta-Conv, which the `conv` rule cannot
  absorb; the typed headline ledger above is the root tier, exactly
  the tier the bespoke Geuvers results governed.
* Clock/parametricity eta slots remain future rows (ETA-T8 adds the
  first NEW rows).

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaTableCanonicalityFlip.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-! ## The shrink is sound: canonical raw eta ⊆ legacy eta -/

/-- **Every canonical raw root eta contraction is a legacy
contraction** — the relation-level wrapper of the ETA-T1 backward
adequacy.  The flip removed firings (the ungated modal/Glue arms); it
added none. -/
theorem _root_.FX1Poly.Core.StepEtaRootTable.toBespokeEta {scope : Nat}
    {source target : RawTerm scope}
    (rootStep : StepEtaRootTable source target) :
    Step.eta source target := by
  cases rootStep with
  | etaRedex isRow isRawTier introPayload contracts =>
      exact stepEtaTableRootToBespokeEta isRow isRawTier introPayload
        contracts

/-! ## The typed coincidence: canonical eta = type-sound legacy eta -/

/-- ★★ **On typed subjects the legacy and canonical eta relations
coincide** — the repair in one biconditional.  Forward: a legacy
contraction of a typed subject is a canonical contraction (the three
faithfully-gated rows fire; the modal/Glue arms are refuted by
untypability).  Backward: a canonical contraction is a legacy one
unconditionally. -/
theorem HasTypeDescPi.bespokeEtaIffCanonicalEta {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {source target classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context source classifier) :
    Step.eta source target ↔ StepEtaRootTable source target :=
  ⟨fun etaStep => typed.bespokeEtaToTableRoot etaStep,
    fun rootStep => rootStep.toBespokeEta⟩

/-! ## The shrink is real: the official divergence record -/

/-- **The legacy modal over-firing is repaired**: legacy eta fires raw
on the closed cell `modIntro (modElim unit)` while the canonical
relation refuses — the typed-tier gate (`requiresTypedFiring`) the
bespoke arm never had. -/
theorem bespokeEtaModalOverFiringRepaired :
    ∃ (source target : RawTerm 0),
      Step.eta source target ∧ ¬ StepEtaRootTable source target :=
  ⟨RawTerm.etaModIntroSource (.mkGen .gen_unit () .childNil),
    .mkGen .gen_unit () .childNil,
    etaModIntro_bespokeFiresRaw,
    fun rootStep =>
      etaModIntro_tableRefusesRaw rootStep.toStepEtaOverTable⟩

/-- **The legacy Glue over-firing is repaired**: the Glue twin of
`bespokeEtaModalOverFiringRepaired` on
`glueIntro (glueElim unit) unit`. -/
theorem bespokeEtaGlueOverFiringRepaired :
    ∃ (source target : RawTerm 0),
      Step.eta source target ∧ ¬ StepEtaRootTable source target :=
  ⟨RawTerm.etaGlueIntroSource (.mkGen .gen_unit () .childNil),
    .mkGen .gen_unit () .childNil,
    etaGlueIntro_bespokeFiresRaw,
    fun rootStep =>
      etaGlueIntro_tableRefusesRaw rootStep.toStepEtaOverTable⟩

/-! ## The re-pointed canonical beta-eta headline metatheory -/

/-- **★★ Subject reduction for the CANONICAL beta-eta union** — the
kernel's official beta-eta preservation theorem, re-pointed from the
ETA-T6 master: Pi-fragment typing survives every
`StepTableBetaEtaRoot` step at the exact classifier. -/
theorem StepTableBetaEtaRoot.subjectReduction {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {subject reduct classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    (unionStep : StepTableBetaEtaRoot subject reduct) :
    HasTypeDescPi profile context reduct classifier :=
  HasTypeDescPi.subjectReductionTableBetaEtaRoot wellFormed typed
    unionStep

/-- **★★ Many-step subject reduction for the canonical beta-eta
union.** -/
theorem StepTableBetaEtaRoot.subjectReductionStar
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject reduct classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier)
    (chain : UnionStar (StepTable (scope := scope)) StepEtaRootTable
      subject reduct) :
    HasTypeDescPi profile context reduct classifier :=
  HasTypeDescPi.subjectReductionTableBetaEtaRootStar wellFormed typed
    chain

/-- **★★ Typed strong normalization for the canonical beta-eta
union** — every grown-typed subject in a well-formed context is
accessible for `StepTable ∪ StepEtaRootTable`. -/
theorem StepTableBetaEtaRoot.stronglyNormalizingTyped
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (wellFormed : WfContextDescPi context)
    (typed : HasTypeDescPi profile context subject classifier) :
    Acc (UnionSuccessor (StepTable (scope := scope)) StepEtaRootTable)
      subject :=
  HasTypeDescPi.tableBetaEtaRootStronglyNormalizing wellFormed typed

/-- **★★ Typed Church-Rosser for the canonical beta-eta union** — the
Geuvers theorem over table rows: any two union reducts of a typed
subject join by union stars. -/
theorem StepTableBetaEtaRoot.confluentTyped {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier)
    {leftReduct rightReduct : RawTerm scope}
    (toLeft : UnionStar (StepTable (scope := scope)) StepEtaRootTable
      subject leftReduct)
    (toRight : UnionStar (StepTable (scope := scope)) StepEtaRootTable
      subject rightReduct) :
    ∃ commonReduct : RawTerm scope,
      UnionStar (StepTable (scope := scope)) StepEtaRootTable
        leftReduct commonReduct
      ∧ UnionStar (StepTable (scope := scope)) StepEtaRootTable
          rightReduct commonReduct :=
  HasTypeDescPi.tableBetaEtaRootConfluenceTyped contextWellFormed typed
    toLeft toRight

/-- **★★ Unique canonical beta-eta normal forms on typed subjects.** -/
theorem StepTableBetaEtaRoot.uniqueNormalFormTyped
    {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier)
    {leftNormalForm rightNormalForm : RawTerm scope}
    (toLeft : UnionStar (StepTable (scope := scope)) StepEtaRootTable
      subject leftNormalForm)
    (leftIsNormal : ∀ next : RawTerm scope,
      ¬ StepTableBetaEtaRoot leftNormalForm next)
    (toRight : UnionStar (StepTable (scope := scope)) StepEtaRootTable
      subject rightNormalForm)
    (rightIsNormal : ∀ next : RawTerm scope,
      ¬ StepTableBetaEtaRoot rightNormalForm next) :
    leftNormalForm = rightNormalForm :=
  HasTypeDescPi.tableBetaEtaRootUniqueNormalForm contextWellFormed
    typed toLeft leftIsNormal toRight rightIsNormal

/-! ## The legacy conversion transport

Consumers holding legacy `Step.betaEtaStar` facts across the flip
migrate through the shipped two-way typed star transports
(`HasTypeDescPi.betaEtaStarToUnionStar` /
`HasTypeDescPi.unionStarToBetaEtaStar`, ETA-T6) — cited here as the
official migration path rather than re-aliased. -/

end FX1Poly.Typed

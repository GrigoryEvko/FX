import FX1Poly.Core.EtaIotaQuasiCommutation
import FX1Poly.Core.TableReduceOnce

/-! # EtaIotaCrossPairCounterexample — ETA-T5 increment 4.5b: the
honest boundary, pinned

Raw full-congruence table eta does NOT quasi-commute over table iota
at the canonical tables, and the witness is the CROSS-pair duality:
the surjective-pairing redex `pair (fst g) (snd g)` sitting at beta's
function slot with a LAMBDA core `g`.  The source
`app (pair (fst g) (snd g)) unit` is iota-NORMAL — beta needs a
lam-headed function (the slot holds a pair), and fst/snd need
pair-headed scrutinees (they hold the lambda) — yet one raw etaPair
step exposes `app (g) unit`, a beta redex.  No fronted iota step can
exist, so both the `DualityReorders` oracle and the Geser hypothesis
itself are REFUTED for the raw canonical tables.

This is the table-precise location of the classical surjective-pairing
pathology (Klop): the SAME-pair dualities (an etaLam redex at beta's
slot) do reorder — the observation is the eliminator applied to the
core — but a cross-pair redex whose CORE happens to match the
scrutinee head leaves the source without any iota step at all.  The
consequences, now checked facts rather than hopes: the
oracle-parameterized `etaIotaQuasiCommutes` is the strongest TRUE
generic statement at the raw tier; the bespoke root-only eta
postponement (`EtaPostponementOverBeta`) never met this case because
root-only eta cannot bury a redex at a scrutinee slot; and raw-tier
union SN via Geser is unobtainable for tables whose raw rows include
the non-left-linear pair eta — the discharge belongs to the typed
tier (ETA-T6), where firing is gated.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaIotaCrossPairCounterexample.lean`. -/

namespace FX1Poly.Core

/-! ## The fixture -/

/-- The identity function `lam unit (var 0)` — a lam-headed core. -/
@[reducible] def identityLamFixture : RawTerm 0 :=
  .mkGen .gen_lam ()
    (.childCons (unitFixture 0)
      (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil)
        .childNil))

/-- The surjective-pairing redex over the lambda:
`pair (fst identityLam) (snd identityLam)`. -/
@[reducible] def surjectivePairingRedexFixture : RawTerm 0 :=
  .mkGen .gen_pair ()
    (.childCons
      (.mkGen .gen_fst () (.childCons identityLamFixture .childNil))
      (.childCons
        (.mkGen .gen_snd () (.childCons identityLamFixture .childNil))
        .childNil))

/-- The source: the pair redex applied to `unit` — iota-NORMAL. -/
@[reducible] def crossPairSourceFixture : RawTerm 0 :=
  .mkGen .gen_app ()
    (.childCons surjectivePairingRedexFixture
      (.childCons (unitFixture 0) .childNil))

/-- The middle: one etaPair step exposes the lambda —
`app identityLam unit`, a beta redex. -/
@[reducible] def crossPairMiddleFixture : RawTerm 0 :=
  .mkGen .gen_app ()
    (.childCons identityLamFixture
      (.childCons (unitFixture 0) .childNil))

/-! ## Memberships and the concrete computations -/

/-- Beta is the canonical iota table's first row. -/
theorem betaIotaRow_memIotaTable : betaIotaRow ∈ iotaRuleTable := .head _

/-- Pair eta is the canonical eta table's second row. -/
theorem etaPairRow_memEtaTable : etaPairRow ∈ etaRuleTable :=
  .tail _ (.head _)

/-- The pair redex contracts to the lambda (both observations agree on
the core). -/
theorem etaPairRow_contractsOnLamCore :
    etaPairRow.contractsOn? (scope := 0)
      (.childCons
        (.mkGen .gen_fst () (.childCons identityLamFixture .childNil))
        (.childCons
          (.mkGen .gen_snd () (.childCons identityLamFixture .childNil))
          .childNil))
    = some identityLamFixture := rfl

/-- Beta fires on the exposed lambda: `app identityLam unit ↝ unit`. -/
theorem betaIotaRow_firesOnCrossPairMiddle :
    betaIotaRow.firesOn? (scope := 0) ()
      (.childCons identityLamFixture
        (.childCons (unitFixture 0) .childNil))
    = some (unitFixture 0) := rfl

/-- ★ The source is iota-IRREDUCIBLE: the canonical reducer halts on
it (beta sees a pair, fst/snd see a lambda, every interior is
normal). -/
theorem crossPairSource_isIotaIrreducible :
    reduceOnceOverTable iotaRuleTable crossPairSourceFixture = none := rfl

/-! ## The steps -/

/-- The eta step at the function slot. -/
theorem crossPairSpineStep :
    StepEtaOverTableChildren etaRuleTable
      (binderShifts := Generator.gen_app.binderShifts)
      (.childCons surjectivePairingRedexFixture
        (.childCons (unitFixture 0) .childNil))
      (.childCons identityLamFixture
        (.childCons (unitFixture 0) .childNil)) :=
  .here _ (.etaRedex etaPairRow_memEtaTable rfl ()
    etaPairRow_contractsOnLamCore)

/-- The whole-term eta step. -/
theorem crossPairEtaStep :
    StepEtaOverTable etaRuleTable crossPairSourceFixture
      crossPairMiddleFixture :=
  .cong .gen_app () crossPairSpineStep

/-- The following iota step. -/
theorem crossPairIotaStep :
    StepOverTable iotaRuleTable crossPairMiddleFixture (unitFixture 0) :=
  .tableRedex betaIotaRow_memIotaTable () betaIotaRow_firesOnCrossPairMiddle

/-- The configuration exhibits the duality witness: beta's scrutinee
slot holds the etaPair redex contracting to the fired lambda. -/
theorem crossPair_hasEtaDuality :
    betaIotaRow.HasEtaDualityAt etaRuleTable
      (.childCons surjectivePairingRedexFixture
        (.childCons (unitFixture 0) .childNil))
      (.childCons identityLamFixture
        (.childCons (unitFixture 0) .childNil)) :=
  ⟨{ slot := 0, head := .gen_lam }, .head _,
    etaPairRow, etaPairRow_memEtaTable, rfl,
    (), _, (), _, rfl, rfl, etaPairRow_contractsOnLamCore⟩

/-! ## The refutations -/

/-- ★★ **The duality oracle is unsatisfiable for the raw canonical
tables**: any would-be `DualityReorders` witness must front an iota
step out of an iota-normal term. -/
theorem dualityReorders_canonicalRaw_refuted :
    ¬ DualityReorders iotaRuleTable etaRuleTable := by
  intro oracle
  obtain ⟨commonReduct, frontedStep, _reductStar⟩ :=
    oracle betaIotaRow_memIotaTable () crossPairSpineStep
      betaIotaRow_firesOnCrossPairMiddle crossPair_hasEtaDuality
  exact reduceOnceOverTable_eq_none_blocks_step
    crossPairSource_isIotaIrreducible frontedStep

/-- ★★ **Raw full-cong eta does NOT quasi-commute over iota at the
canonical tables** — the Geser hypothesis itself fails, so raw-tier
union SN via eta postponement is unobtainable with raw pair eta; the
discharge moves to the typed tier (ETA-T6). -/
theorem rawEtaIota_quasiCommutation_refuted :
    ¬ QuasiCommutesRightOverLeft
        (StepOverTable iotaRuleTable (scope := 0))
        (StepEtaOverTable etaRuleTable) := by
  intro quasiCommutes
  obtain ⟨commonReduct, frontedStep, _reductStar⟩ :=
    quasiCommutes crossPairSourceFixture crossPairMiddleFixture
      (unitFixture 0) crossPairEtaStep crossPairIotaStep
  exact reduceOnceOverTable_eq_none_blocks_step
    crossPairSource_isIotaIrreducible frontedStep

/-! ## The failure is NOT about pair eta — the etaLam dual

Excluding the non-left-linear pair row does not rescue the raw tier:
an etaLam redex whose CORE is pair-headed sits at fst's scrutinee slot
the same way.  `fst (lam unit (app (pair unit unit) (var 0)))` is
iota-normal — fst sees a lambda, the interior beta sees a pair — yet
one raw etaLam step exposes `fst (pair unit unit)`.  The refutation
below uses the SINGLE-row table `[etaLamRow]`: any raw eta rule whose
core is unconstrained is cross-pair-exposed at every iota row
scrutinizing a different head.  Only typing (which forbids a
pair-headed term at a Pi-typed position) closes this — the raw tier
has no eta postponement, full stop. -/

/-- The closed pair `pair unit unit` at any scope. -/
@[reducible] def pairOfUnitsFixture (scope : Nat) : RawTerm scope :=
  .mkGen .gen_pair ()
    (.childCons (unitFixture scope)
      (.childCons (unitFixture scope) .childNil))

/-- The etaLam redex over the pair:
`lam unit (app (pair unit unit) (var 0))` — the core is PAIR-headed. -/
@[reducible] def etaLamRedexOverPairFixture : RawTerm 0 :=
  .mkGen .gen_lam ()
    (.childCons (unitFixture 0)
      (.childCons
        (.mkGen .gen_app ()
          (.childCons (pairOfUnitsFixture 1)
            (.childCons
              (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil)
              .childNil)))
        .childNil))

/-- The source: `fst` of the etaLam redex — iota-NORMAL. -/
@[reducible] def crossLamSourceFixture : RawTerm 0 :=
  .mkGen .gen_fst () (.childCons etaLamRedexOverPairFixture .childNil)

/-- The middle: one etaLam step exposes `fst (pair unit unit)`, an
fst redex. -/
@[reducible] def crossLamMiddleFixture : RawTerm 0 :=
  .mkGen .gen_fst () (.childCons (pairOfUnitsFixture 0) .childNil)

/-- Fst-on-pair is the canonical iota table's fourth row. -/
theorem fstPairIotaRow_memIotaTable : fstPairIotaRow ∈ iotaRuleTable :=
  .tail _ (.tail _ (.tail _ (.head _)))

/-- EtaLam is the canonical eta table's first row. -/
theorem etaLamRow_memEtaTable : etaLamRow ∈ etaRuleTable := .head _

/-- The etaLam redex contracts to the PAIR core. -/
theorem etaLamRow_contractsOnPairCore :
    etaLamRow.contractsOn? (scope := 0)
      (.childCons (unitFixture 0)
        (.childCons
          (.mkGen .gen_app ()
            (.childCons (pairOfUnitsFixture 1)
              (.childCons
                (.mkGen .gen_var ⟨0, Nat.zero_lt_succ 0⟩ .childNil)
                .childNil)))
          .childNil))
    = some (pairOfUnitsFixture 0) := rfl

/-- Fst fires on the exposed pair: `fst (pair unit unit) ↝ unit`. -/
theorem fstPairIotaRow_firesOnCrossLamMiddle :
    fstPairIotaRow.firesOn? (scope := 0) ()
      (.childCons (pairOfUnitsFixture 0) .childNil)
    = some (unitFixture 0) := rfl

/-- ★ The etaLam-dual source is iota-IRREDUCIBLE: fst sees a lambda,
the interior beta sees a pair. -/
theorem crossLamSource_isIotaIrreducible :
    reduceOnceOverTable iotaRuleTable crossLamSourceFixture = none := rfl

/-- The single-row eta table — pair eta nowhere in sight. -/
@[reducible] def etaLamOnlyTable : List EtaRuleDesc := [etaLamRow]

/-- EtaLam is its own single-row table's head. -/
theorem etaLamRow_memEtaLamOnlyTable : etaLamRow ∈ etaLamOnlyTable :=
  .head _

/-- The eta step at fst's scrutinee slot, over the SINGLE-row table. -/
theorem crossLamSpineStep :
    StepEtaOverTableChildren etaLamOnlyTable
      (binderShifts := Generator.gen_fst.binderShifts)
      (.childCons etaLamRedexOverPairFixture .childNil)
      (.childCons (pairOfUnitsFixture 0) .childNil) :=
  .here _ (.etaRedex etaLamRow_memEtaLamOnlyTable rfl ()
    etaLamRow_contractsOnPairCore)

/-- The whole-term eta step over the single-row table. -/
theorem crossLamEtaStep :
    StepEtaOverTable etaLamOnlyTable crossLamSourceFixture
      crossLamMiddleFixture :=
  .cong .gen_fst () crossLamSpineStep

/-- The following iota step. -/
theorem crossLamIotaStep :
    StepOverTable iotaRuleTable crossLamMiddleFixture (unitFixture 0) :=
  .tableRedex fstPairIotaRow_memIotaTable ()
    fstPairIotaRow_firesOnCrossLamMiddle

/-- ★★ **Even the single best-behaved eta rule fails**: raw etaLam
alone does not quasi-commute over the canonical iota table — the
cross-pair exposure is intrinsic to raw (untyped) eta whose core is
unconstrained, not to the non-left-linear pair row. -/
theorem rawEtaLamOnly_quasiCommutation_refuted :
    ¬ QuasiCommutesRightOverLeft
        (StepOverTable iotaRuleTable (scope := 0))
        (StepEtaOverTable etaLamOnlyTable) := by
  intro quasiCommutes
  obtain ⟨commonReduct, frontedStep, _reductStar⟩ :=
    quasiCommutes crossLamSourceFixture crossLamMiddleFixture
      (unitFixture 0) crossLamEtaStep crossLamIotaStep
  exact reduceOnceOverTable_eq_none_blocks_step
    crossLamSource_isIotaIrreducible frontedStep

end FX1Poly.Core

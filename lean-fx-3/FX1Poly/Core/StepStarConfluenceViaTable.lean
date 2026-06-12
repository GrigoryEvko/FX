import FX1Poly.Core.StepTable
import FX1Poly.Core.StepTableEquivariance
import FX1Poly.Core.TableTakahashiTriangle
import FX1Poly.Core.IotaTableOrthogonality
import FX1Poly.Core.StepStarJoin
import FX1Poly.Core.Newman

/-! # FX1Poly/Core/StepStarConfluenceViaTable
    — raw `StepStar` confluence routed through the TABLE confluence theorem.

The bespoke Takahashi route (`ParallelReduction` → `CompleteDevelopment` → `ParStepTriangle` →
`RawConfluence`) re-proves per-iota-constructor what the table lane proves ONCE per row schema:
`StepOverTable.confluent` (TableTakahashiTriangle) is the orthogonal-systems confluence theorem,
generic over every well-formed scope-uniform table.  This file harvests it for the BESPOKE
relation:

  * the 17-row `legacyIotaRuleTable` carries the same well-formedness and scope-uniformity
    certificates as the canonical 18-row table (`legacyIotaRuleTable_isWf` /
    `legacyIotaRuleTable_isScopeUniform`), so `StepOverTable legacyIotaRuleTable` is confluent;
  * the IOTA-T1 adequacy `stepOverLegacyTable_iff_step` makes that relation EXTENSIONALLY
    EQUAL to the bespoke `Step`, so its reflexive-transitive closure coincides with `StepStar`
    (`StepStar.toLegacyTableClosure` / `ReflTransClosure.legacyToStepStar`);
  * therefore raw confluence (`StepStar.tableRouteConfluence`) and the raw strip property
    (`StepStar.tableRouteStrip`) follow with NO parallel-reduction sandwich, NO complete
    development, and NO per-iota critical-pair matrix.

This is the load-bearing decoupling brick of the bespoke-iota retirement: once `RawConfluence`
delegates to these theorems, the quadratic chain (`CriticalPairs` → `CdLemma`, the `ParStep`
per-iota mirror) loses its confluence consumer and can be retired leaf-first.

## Zero-axiom verification

Every certificate field closes by `rfl`-decidable enumeration; the closure transports are
structural inductions; the headline theorems instantiate separately-gated generic lemmas.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditCoreTerminationOrders.lean`. -/

namespace FX1Poly.Core

/-! ## The legacy-table certificates (well-formedness + scope-uniformity) -/

/-- The 17-row legacy table is a well-formed orthogonal table — the same
four `rfl`-decidable enumeration checks that certify the canonical
18-row table (`iotaRuleTable_isWf`) recompute to `true` on the
pathBeta-free sublist. -/
theorem legacyIotaRuleTable_isWf : WfIotaTable legacyIotaRuleTable :=
  { keysAreDistinct := rfl
    elimDeterminesSlots := rfl
    elimRootsAvoidHeads := rfl
    rowsHavePrimaryScrutinee := rfl }

/-- Every legacy row carries its scope-uniformity certificate — inherited
from the canonical table's certificate through the sublist embedding
`legacyRow_memFullTable`. -/
theorem legacyIotaRuleTable_isScopeUniform :
    ∀ rule, rule ∈ legacyIotaRuleTable → rule.IsScopeUniform :=
  fun rule isLegacyRow =>
    iotaRuleTable_isScopeUniform rule (legacyRow_memFullTable isLegacyRow)

/-- **The legacy-table relation is confluent** — the generic
orthogonal-systems confluence theorem (`StepOverTable.confluent`)
instantiated at the 17-row legacy table. -/
theorem StepOverTable.legacyConfluent {scope : Nat} :
    Confluent
      (fun source target : RawTerm scope =>
        StepOverTable legacyIotaRuleTable source target) :=
  StepOverTable.confluent legacyIotaRuleTable_isWf legacyIotaRuleTable_isScopeUniform

/-! ## Star-level transport across the IOTA-T1 adequacy -/

/-- A bespoke `StepStar` chain is a legacy-table reduction chain — each
link embeds by the forward adequacy `Step.toLegacyTableStep`. -/
theorem StepStar.toLegacyTableClosure {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (chain : StepStar sourceTerm targetTerm) :
    ReflTransClosure
      (fun source target : RawTerm scope =>
        StepOverTable legacyIotaRuleTable source target)
      sourceTerm targetTerm := by
  induction chain with
  | refl term => exact .refl term
  | trans firstStep _restChain restClosure =>
      exact .head firstStep.toLegacyTableStep restClosure

/-- A legacy-table reduction chain collapses to a bespoke `StepStar`
chain — each link collapses by the backward adequacy
`StepOverTable.legacyToStep`. -/
theorem ReflTransClosure.legacyToStepStar {scope : Nat}
    {sourceTerm targetTerm : RawTerm scope}
    (chain : ReflTransClosure
      (fun source target : RawTerm scope =>
        StepOverTable legacyIotaRuleTable source target)
      sourceTerm targetTerm) :
    StepStar sourceTerm targetTerm := by
  induction chain with
  | refl point => exact .refl point
  | head firstTableStep _restChain restStar =>
      exact .trans firstTableStep.legacyToStep restStar

/-! ## The headline harvest: raw confluence + raw strip, table-routed -/

/-- **Raw confluence via the table.**  Any two `StepStar`-reducts of a
common source join at a common term — discharged by lifting both chains
across the IOTA-T1 adequacy, applying the generic table confluence at
the legacy table, and collapsing the joining legs back.  No
parallel-reduction sandwich, no complete development, no per-iota
critical-pair matrix. -/
theorem StepStar.tableRouteConfluence : StepStar.HasConfluence := by
  intro scope sourceTerm leftReduct rightReduct leftChain rightChain
  obtain ⟨commonReduct, leftJoinChain, rightJoinChain⟩ :=
    StepOverTable.legacyConfluent
      leftChain.toLegacyTableClosure rightChain.toLegacyTableClosure
  exact ⟨commonReduct,
    leftJoinChain.legacyToStepStar, rightJoinChain.legacyToStepStar⟩

/-- **Raw strip property via the table** — the asymmetric
one-step-vs-many form of Church-Rosser, as the single-step instance of
`StepStar.tableRouteConfluence`. -/
theorem StepStar.tableRouteStrip : StepStar.HasStrip := by
  intro scope sourceTerm leftReduct rightReduct firstStep rightChain
  exact StepStar.tableRouteConfluence (StepStar.single firstStep) rightChain

/-- **The local one-step join** — two single steps out of a common source
join, as the one-vs-one instance of `StepStar.tableRouteConfluence`.
This is the local Church-Rosser shape the historical per-iota
critical-pair matrix (`cd_lemma` over the `CriticalPairs`/`CdLemma`
enumeration) proved by quadratic case analysis; the table route makes it
a corollary of global confluence, retiring that enumeration. -/
theorem StepStar.localJoin {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step sourceTerm leftReduct)
    (rightStep : Step sourceTerm rightReduct) :
    StepStar.Join leftReduct rightReduct :=
  StepStar.tableRouteConfluence
    (StepStar.single leftStep) (StepStar.single rightStep)

end FX1Poly.Core

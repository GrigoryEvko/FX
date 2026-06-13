import FX1Poly.Core.StepOverBundle
import FX1Poly.Core.StepStarConfluenceViaTable

/-! # FX1Poly/Core/StepOverBundleConfluence — RW-6 (a): no-regression
confluence for the iota-only bundle.

RW-5 made `StepOver fxIotaBundle` extensionally EQUAL to `StepOverTable
iotaRuleTable` (`stepOver_iotaOnly_iff_stepOverTable`).  The canonical
β+ι confluence (`StepOverTable.canonicalConfluent`) therefore transports
to the parameterized relation with ZERO new critical-pair work — the
"no-regression instantiation gate" the keystone promised.

The transport is two generic, relation-polymorphic helpers:

  * `ReflTransClosure.mapForward` — push a chain along a forward
    relation implication (one structural induction);
  * `Confluent.ofRelIff` — confluence respects a pointwise relation iff
    (pull both chains back, run source confluence, push the joining
    legs forward).

Then `StepOver.fxIotaBundleConfluent` instantiates at the RW-5 adequacy.

The FULL βιη bundle `fxBundle` is NOT raw-confluent (the η rows give
only postponement / quasi-commutation — Klop/Nederpelt, see the
`EtaRuleTable` docstring), so confluence is the iota-only headline; the
βη tier rides the shipped `etaQuasiCommutesOverBeta` route, not this
one.

## Zero-axiom verification

Structural induction + the shipped canonical confluence; no `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditStepOverBundleConfluence.lean`.
-/

namespace FX1Poly.Core

/-! ## Generic relation-iff transport -/

/-- Map a reflexive-transitive chain along a forward relation
implication — each link re-wraps under the target relation. -/
theorem ReflTransClosure.mapForward {Carrier : Type _}
    {sourceRel targetRel : Carrier → Carrier → Prop}
    (forward : ∀ {first second : Carrier}, sourceRel first second →
      targetRel first second)
    {source target : Carrier}
    (chain : ReflTransClosure sourceRel source target) :
    ReflTransClosure targetRel source target := by
  induction chain with
  | refl point => exact .refl point
  | head firstStep _restChain restMapped =>
      exact .head (forward firstStep) restMapped

/-- **Confluence respects a pointwise relation iff** — if two relations
agree stepwise, confluence of one transports to the other.  Pull both
target chains back to the source relation, join there, push the joining
legs forward. -/
theorem Confluent.ofRelIff {Carrier : Type _}
    {sourceRel targetRel : Carrier → Carrier → Prop}
    (forward : ∀ {first second : Carrier}, sourceRel first second →
      targetRel first second)
    (backward : ∀ {first second : Carrier}, targetRel first second →
      sourceRel first second)
    (sourceConfluent : Confluent sourceRel) :
    Confluent targetRel := by
  intro source leftReduct rightReduct leftChain rightChain
  obtain ⟨commonReduct, leftJoinChain, rightJoinChain⟩ :=
    sourceConfluent
      (leftChain.mapForward backward) (rightChain.mapForward backward)
  exact ⟨commonReduct,
    leftJoinChain.mapForward forward, rightJoinChain.mapForward forward⟩

/-! ## The no-regression instantiation gate -/

/-- ★ **The generic instantiation gate**: ANY well-formed scope-uniform
iota table gives a confluent iota-only bundle.  The shipped generic
orthogonal-systems confluence (`StepOverTable.confluent`) transported
across the RW-5 adequacy with no new critical-pair work — so a new
profile that ships a well-formed iota table inherits bundle confluence
for free.  This is RW-6's no-regression gate in its general form. -/
theorem StepOver.iotaOnlyConfluent {iotaTable : List IotaRuleDesc}
    (tableIsWf : WfIotaTable iotaTable)
    (tableIsUniform : ∀ rule, rule ∈ iotaTable → rule.IsScopeUniform)
    {scope : Nat} :
    Confluent (fun source target : RawTerm scope =>
      StepOver { iotaRows := iotaTable, etaRows := [] } source target) :=
  Confluent.ofRelIff
    (fun tableStep => StepOverTable.toStepOver_iotaOnly tableStep)
    (fun bundleStep => StepOver.toStepOverTable_iotaOnly bundleStep)
    (StepOverTable.confluent tableIsWf tableIsUniform)

/-- ★ **The iota-only bundle relation is confluent** — the canonical
instance of the generic gate at the kernel's own well-formedness +
scope-uniformity certificates.  The parameterized `StepOver` relation,
at the iota-only bundle, recovers the kernel's β+ι confluence exactly. -/
theorem StepOver.fxIotaBundleConfluent {scope : Nat} :
    Confluent (fun source target : RawTerm scope =>
      StepOver fxIotaBundle source target) :=
  StepOver.iotaOnlyConfluent iotaRuleTable_isWf iotaRuleTable_isScopeUniform

end FX1Poly.Core

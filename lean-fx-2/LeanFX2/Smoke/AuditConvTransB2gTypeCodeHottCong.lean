import LeanFX2.Tools.DependencyAudit
import LeanFX2.Term.PreservesTerm

/-! # AuditConvTransB2gTypeCodeHottCong — CONVTRANS-B.2g type-code +
HoTT-special cong family

Strict gate plus reviewer-facing audit for the **type-code +
HoTT-special** cong family of CONVTRANS-A subject-reduction term
construction (CONVTRANS-B.2g, ticket #1728).  This is the last
B.2.* cong-sub-ticket before B.3 β-rule lifts.

## Scope of B.2g

Twenty-four `RawStep.par.lift_*` cong-only lift theorems split across
three categories of schematic-payload Term constructors that share the
"raw cong rule consumes raw subterm step" architecture:

### Type-code constructors (11 lifts)

CUMUL-2.4 VALUE-shaped ctors carrying their universe-code raw payloads
as schematic fields, projecting to `Ty.universe outerLevel levelLe`:

| Lift | Host file | Pattern |
| --- | --- | --- |
| `lift_full_arrowCode` | `TypeCodeLifts.lean` | free-the-type-via-suffices |
| `lift_full_piTyCode` | `TypeCodeLifts.lean` | free-the-type-via-suffices |
| `lift_full_sigmaTyCode` | `TypeCodeLifts.lean` | free-the-type-via-suffices |
| `lift_full_productCode` | `TypeCodeLifts.lean` | free-the-type-via-suffices |
| `lift_full_sumCode` | `TypeCodeLifts.lean` | free-the-type-via-suffices |
| `lift_full_listCode` | `TypeCodeLifts.lean` | free-the-type-via-suffices |
| `lift_full_optionCode` | `TypeCodeLifts.lean` | free-the-type-via-suffices |
| `lift_full_eitherCode` | `TypeCodeLifts.lean` | free-the-type-via-suffices |
| `lift_full_idCode` | `TypeCodeLifts.lean` | free-the-type-via-suffices |
| `lift_full_equivCode` | `TypeCodeLifts.lean` | free-the-type-via-suffices |
| `lift_universeCode` | `TierZeroAndUnary.lean` | nullary canonical (refl-only) |

### HoTT-special value / eliminator ctors (9 lifts)

Schematic-payload value/eliminator ctors specific to the Univalence /
Funext layer.  Each has a typed cong rule that takes a raw step on
the schematic payload and produces a typed Step.par:

| Lift | Host file | Source pattern |
| --- | --- | --- |
| `lift_full_refl` | `SchematicValueCtors.lean` | generic-source + Ty.id.inj |
| `lift_full_oeqRefl` | `SchematicValueCtors.lean` | generic-source + Ty.oeq.inj |
| `lift_full_idStrictRefl` | `SchematicValueCtors.lean` | generic-source + Ty.idStrict.inj |
| `lift_full_equivReflId` | `SchematicValueCtors.lean` | atom-shaped (refl-only) |
| `lift_full_equivReflIdAtId` | `SchematicValueCtors.lean` | atom-shaped (refl-only) |
| `lift_full_uaIntroHet` | `SchematicValueCtors.lean` | structured-source + equivWitness IH |
| `lift_full_equivIntroHet` | `SchematicValueCtors.lean` | structured-source + forward/backward IHs |
| `lift_full_oeqFunext` | `SchematicValueCtors.lean` | structured-source + pointwise IH |
| `lift_equivApp` | `TierTwoBinary.lean` | binary cong + two typed IHs |

### Newly-shipped HoTT-special cong-only lifts (4 lifts)

Carved out of the deferred 5-ctor blocker list by sidestepping the
multi-ctor `cases genericTerm` dispatch.  These use the
STRUCTURED-source pattern (take the source as already
`Term.<ctor> ...`, not a generic `Term context someType someRaw`),
mirroring `lift_full_uaIntroHet` and `lift_full_oeqFunext`:

| Lift | Host file | Notes |
| --- | --- | --- |
| `lift_funextRefl` | `EliminatorFunextFamily.lean` | NEW; no typed IH (cong consumes raw step) |
| `lift_funextReflAtId` | `EliminatorFunextFamily.lean` | NEW; no typed IH (cong consumes raw step) |
| `lift_funextIntroHet` | `EliminatorFunextFamily.lean` | NEW; second applyBRaw via RawStep.par.refl |
| `lift_uaToEquiv` | `EliminatorFunextFamily.lean` | NEW; binary cong w/ proof typed IH |

## What remains deferred (1 ctor; not in B.2g scope)

* **`equivApply`**: `RawStep.par.equivApply_inv` has THREE disjunctive
  arms (cong + `uaReflEquivApply` shallow-β + `uaReflEquivApplyDeep`
  deep-β).  The two β arms have non-cong source shapes — the equiv
  develops to `RawTerm.uaToEquiv (RawTerm.oeqRefl _)` — so a
  cong-only lift cannot prove the headline.  Defers to **CONVTRANS-B.3
  β-rule lifts** (ticket #1729), which will ship `lift_full_equivApply`
  alongside `lift_full_app` / `lift_full_appPi` β-cascade machinery.

Five-ctor deferred list at `TwoTyEliminators.lean:333-342` was:
`funextRefl, funextIntroHet, funextReflAtId, uaToEquiv, equivApply`.
The first four ship here as cong-only at structured-source form (the
multi-ctor dispatch axiom leak is sidestepped because the source is
already structured).  `equivApply`'s blocker is REDUCTION SEMANTICS,
not match-compiler axioms — it sits squarely in the β-rule cascade
covered by B.3.

The OTHER deferred-at-headline ctors documented in
`TwoTyEliminators.lean:322-332` (`pair`, full `appPi`, full `transp`)
are not in B.2g scope; they belong to the β-cast-wall / heterogeneous-
Step.par cascade tracked separately (B.3 / B.4 territory).

## Why each shipped lift is "cong-only"

All 24 lifts have the property that their raw inversion lemma has
the form `(refl arm) ∨ (single cong arm)` — no β rules fire from the
ctor's raw form.  Consequently the lift's existential target Term is
constructed by re-applying the SAME ctor at the new raw indices,
and the typed Step.par witness is the matching `<ctor>Cong`
constructor.  Type-codes use the free-the-type-via-suffices pattern
to discharge the universe-Ty alignment; HoTT-special ctors take a
structured source so no generic Term destruction is needed.

## Cascade role

Closes the B.2 cong sub-family:

* **B.2a** — Π/Σ family (#1722).
* **B.2b** — closed-type family (#1723).
* **B.2c** — identity family (#1724).
* **B.2d** — modal family (#1725).
* **B.2e** — cubical family (#1726).
* **B.2f** — record/refine/codata/session/effect family (#1727).
* **B.2g** — type-code + HoTT-special family (THIS audit, #1728).

After B.2g, **CONVTRANS-B.3a** (ticket #1729) begins the β-rule lift
series, starting with Π/Σ β-rule lifts.  B.3 is harder than B.2
because the β-arms require explicit `Step.par.beta<X>` constructor
handling (target type can differ from source via the typed cast wall;
see `BetaCastWallDemolition.lean` for the `app` / `pathApp` precedent).

## Why this audit lives under Smoke instead of Tools/AuditAll

Same reasoning as `AuditConvTransB2eCubicalCong.lean` and
`AuditConvTransB2fAdvancedCong.lean`: `Term.PreservesTerm` is
reachable as a production module only through its smoke audits.
Co-location of `#print axioms` with the strict gates keeps the
reviewer-facing log adjacent.

The `#assert_no_axioms` strict gates fire under the `LeanFX2Audit`
target identically to gates in `Tools/AuditAll/`.

## Consolidation pattern

This audit reuses the structural template from
`AuditConvTransB2fAdvancedCong.lean`: pre-existing typed cong lifts
with one `#assert_no_axioms` strict gate per lift, one `#print axioms`
reviewer log per lift.  Newly-shipped lifts in
`EliminatorFunextFamily.lean` are integrated alongside the existing
lifts. -/

namespace LeanFX2.SmokeConvTransB2gTypeCodeHottCong

/-! ## Strict gates — `#assert_no_axioms`

Build-failing under `LeanFX2Audit` if any of the twenty-four
type-code + HoTT-special cong-only lifts ever reaches an axiom. -/

-- Type-code constructors (11)
#assert_no_axioms LeanFX2.RawStep.par.lift_full_arrowCode
#assert_no_axioms LeanFX2.RawStep.par.lift_full_piTyCode
#assert_no_axioms LeanFX2.RawStep.par.lift_full_sigmaTyCode
#assert_no_axioms LeanFX2.RawStep.par.lift_full_productCode
#assert_no_axioms LeanFX2.RawStep.par.lift_full_sumCode
#assert_no_axioms LeanFX2.RawStep.par.lift_full_listCode
#assert_no_axioms LeanFX2.RawStep.par.lift_full_optionCode
#assert_no_axioms LeanFX2.RawStep.par.lift_full_eitherCode
#assert_no_axioms LeanFX2.RawStep.par.lift_full_idCode
#assert_no_axioms LeanFX2.RawStep.par.lift_full_equivCode
#assert_no_axioms LeanFX2.RawStep.par.lift_universeCode

-- HoTT-special value / eliminator ctors (9, already shipped)
#assert_no_axioms LeanFX2.RawStep.par.lift_full_refl
#assert_no_axioms LeanFX2.RawStep.par.lift_full_oeqRefl
#assert_no_axioms LeanFX2.RawStep.par.lift_full_idStrictRefl
#assert_no_axioms LeanFX2.RawStep.par.lift_full_equivReflId
#assert_no_axioms LeanFX2.RawStep.par.lift_full_equivReflIdAtId
#assert_no_axioms LeanFX2.RawStep.par.lift_full_uaIntroHet
#assert_no_axioms LeanFX2.RawStep.par.lift_full_equivIntroHet
#assert_no_axioms LeanFX2.RawStep.par.lift_full_oeqFunext
#assert_no_axioms LeanFX2.RawStep.par.lift_equivApp

-- HoTT-special cong-only lifts (4, NEW in this commit)
#assert_no_axioms LeanFX2.RawStep.par.lift_funextRefl
#assert_no_axioms LeanFX2.RawStep.par.lift_funextReflAtId
#assert_no_axioms LeanFX2.RawStep.par.lift_funextIntroHet
#assert_no_axioms LeanFX2.RawStep.par.lift_uaToEquiv

/-! ## Reviewer-facing log — `#print axioms`

Each invocation prints "does not depend on any axioms" alongside the
strict gates above. -/

-- Type-code constructors (11)
#print axioms LeanFX2.RawStep.par.lift_full_arrowCode
#print axioms LeanFX2.RawStep.par.lift_full_piTyCode
#print axioms LeanFX2.RawStep.par.lift_full_sigmaTyCode
#print axioms LeanFX2.RawStep.par.lift_full_productCode
#print axioms LeanFX2.RawStep.par.lift_full_sumCode
#print axioms LeanFX2.RawStep.par.lift_full_listCode
#print axioms LeanFX2.RawStep.par.lift_full_optionCode
#print axioms LeanFX2.RawStep.par.lift_full_eitherCode
#print axioms LeanFX2.RawStep.par.lift_full_idCode
#print axioms LeanFX2.RawStep.par.lift_full_equivCode
#print axioms LeanFX2.RawStep.par.lift_universeCode

-- HoTT-special value / eliminator ctors (9, already shipped)
#print axioms LeanFX2.RawStep.par.lift_full_refl
#print axioms LeanFX2.RawStep.par.lift_full_oeqRefl
#print axioms LeanFX2.RawStep.par.lift_full_idStrictRefl
#print axioms LeanFX2.RawStep.par.lift_full_equivReflId
#print axioms LeanFX2.RawStep.par.lift_full_equivReflIdAtId
#print axioms LeanFX2.RawStep.par.lift_full_uaIntroHet
#print axioms LeanFX2.RawStep.par.lift_full_equivIntroHet
#print axioms LeanFX2.RawStep.par.lift_full_oeqFunext
#print axioms LeanFX2.RawStep.par.lift_equivApp

-- HoTT-special cong-only lifts (4, NEW)
#print axioms LeanFX2.RawStep.par.lift_funextRefl
#print axioms LeanFX2.RawStep.par.lift_funextReflAtId
#print axioms LeanFX2.RawStep.par.lift_funextIntroHet
#print axioms LeanFX2.RawStep.par.lift_uaToEquiv

end LeanFX2.SmokeConvTransB2gTypeCodeHottCong

import FX1Poly.Polygraph.Omega.Steiner.Integration

/-! # Polygraph/Omega/Steiner/AgreementBattery — the eval-level two-decider falsifier (OMEGA-2 r2, B2)

★ **THE AGREEMENT FALSIFIER** (memo falsifier (ii)).  A curated battery of cell pairs over the
admitted **walking-parallel-pair** signature (`Integration.lean`), each run through BOTH deciders:

  * `freeDecide` — FREE-7 `decideTwoCellConvFull` (the universal free-2-cat word-problem decider,
    over the `RawTwoCellExpr` carrier);
  * `steinerDecide` — the Steiner semi-decider `decideFreeConvSound` applied through the
    size-preserving translation `toCellDimTwo` (table equality of the `linearize` chains).

For every row the harness asserts `freeDecide = steinerDecide` by `rfl`.  **This file COMPILING IS
THE FALSIFIER PASSING** — any disagreement would be a failed `rfl`, i.e. a build error, and would be
the headline finding (one of the two engines unsound: `linearize` distinguishing free-strict-convertible
cells, or admitting non-convertible ones).

## Why the sound direction is a HARD check

`freeDecide c1 c2 = true` means `c1`, `c2` are free-strict-convertible (`TwoCellConvFull`).  By CROWN
soundness (`linearizeSoundness`) `linearize` is invariant under that congruence, so `steinerDecide`
MUST also be `true`; a `true / false` split would violate Steiner soundness.  On the admitted battery
signature the reverse holds too (the signature is chosen so both directions coincide), so
`freeDecide = steinerDecide` as `rfl` is the clean invariant.

## The battery (the classes the memo names)

  | row                     | left                              | right       | verdict |
  | ----------------------- | --------------------------------- | ----------- | ------- |
  | left unit               | `id[f] . alpha`                   | `alpha`     | true    |
  | right unit              | `alpha . id[g]`                   | `alpha`     | true    |
  | associativity           | `(id . id) . alpha`               | `id . (id . alpha)` | true |
  | unit on beta            | `id[f] . beta`                    | `beta`      | true    |
  | reflexivity             | `alpha`                           | `alpha`     | true    |
  | DISTINCT generators     | `alpha`                           | `beta`      | false   |
  | structural non-related  | `id[f] . alpha`                   | `beta`      | false   |

The `true` rows exercise the eight `StrictAxiomRel` rows the soundness fold discharges; the `false`
rows exercise the DISTINCT-table refutation (`not_conv_of_linearize_ne`) and, being genuinely
non-convertible parallel generators, are the falsifier's teeth.  The one-hot valuation
(`pairValuation`) makes the `false` rows non-vacuous: distinct generators get distinct Steiner tables.

## HONEST scope

Whisker-heavy / interchange (Godement) rows require a signature with genuine whisker 1-cells (a
3-object extension `o0 -> o1 -> o2`): over the pure parallel pair the only whiskering is by identity
1-cells, and `composePath (identityPath _) [f]` blocks decider reduction through the boundary index, so
those rows are deferred with the 3-object extension (not smuggled).  Dimension-3 agreement rows do not
exist — FREE-7 is dim-2-only; the dim-3 Steiner
substrate stays a Steiner-internal non-vacuity (`DecideFreeConv.lean`'s `cellThreeA/B`), not an
agreement row.  Theorem-level agreement (`freeDecide = steinerDecide o toCellDimTwo` as a proof) is
WALLED at OMEGA-1 (the `toCellDimTwo` conv-leg); this battery is EVAL-level, as the memo prescribes.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph
open FX1Poly.Polygraph.Steiner

/-! ## The two deciders as `Bool`s over the battery signature -/

/-- `freeDecide` — the FREE-7 verdict: are the two free 2-cells convertible under the full
free-strict-2-category congruence?  Total, ungated (`decideTwoCellConvFull`). -/
def freeDecide {sourcePath targetPath : ModalityPath pairGraph PairMode.objZero PairMode.objOne}
    (cellFirst cellSecond : RawTwoCellExpr pairSignature sourcePath targetPath) : Bool :=
  (decideTwoCellConvFull pairModeDecEq pairModalityDecEq pairTwoCellDecEq cellFirst cellSecond).decide

/-- `steinerDecide` — the Steiner verdict through the size-preserving translation: equal `linearize`
tables of the translated dim-2 cells (`decideFreeConvSound o toCellDimTwo`). -/
def steinerDecide {sourcePath targetPath : ModalityPath pairGraph PairMode.objZero PairMode.objOne}
    (cellFirst cellSecond : RawTwoCellExpr pairSignature sourcePath targetPath) : Bool :=
  decideFreeConvSound pairValuation (toCellDimTwo cellFirst) (toCellDimTwo cellSecond)

/-! ## The battery cells -/

/-- The first generating 2-cell `alpha : [edgeF] => [edgeG]`. -/
def cellAlpha : RawTwoCellExpr pairSignature pathEdgeF pathEdgeG := RawTwoCellExpr.gen PairTwoCell.alpha

/-- The second generating 2-cell `beta : [edgeF] => [edgeG]` (distinct from `alpha`). -/
def cellBeta : RawTwoCellExpr pairSignature pathEdgeF pathEdgeG := RawTwoCellExpr.gen PairTwoCell.beta

/-- The identity 2-cell on `[edgeF]`. -/
def cellIdEdgeF : RawTwoCellExpr pairSignature pathEdgeF pathEdgeF :=
  RawTwoCellExpr.id (signature := pairSignature) pathEdgeF

/-- The identity 2-cell on `[edgeG]`. -/
def cellIdEdgeG : RawTwoCellExpr pairSignature pathEdgeG pathEdgeG :=
  RawTwoCellExpr.id (signature := pairSignature) pathEdgeG

/-- `id[f] . alpha` — the left-unit redex. -/
def cellUnitLeftAlpha : RawTwoCellExpr pairSignature pathEdgeF pathEdgeG :=
  RawTwoCellExpr.vcomp cellIdEdgeF cellAlpha

/-- `alpha . id[g]` — the right-unit redex. -/
def cellUnitRightAlpha : RawTwoCellExpr pairSignature pathEdgeF pathEdgeG :=
  RawTwoCellExpr.vcomp cellAlpha cellIdEdgeG

/-- `(id . id) . alpha` — the left-nested associativity redex. -/
def cellAssocLeft : RawTwoCellExpr pairSignature pathEdgeF pathEdgeG :=
  RawTwoCellExpr.vcomp (RawTwoCellExpr.vcomp cellIdEdgeF cellIdEdgeF) cellAlpha

/-- `id . (id . alpha)` — the right-nested associativity redex. -/
def cellAssocRight : RawTwoCellExpr pairSignature pathEdgeF pathEdgeG :=
  RawTwoCellExpr.vcomp cellIdEdgeF (RawTwoCellExpr.vcomp cellIdEdgeF cellAlpha)

/-- `id[f] . beta` — the left-unit redex on the second generator. -/
def cellUnitLeftBeta : RawTwoCellExpr pairSignature pathEdgeF pathEdgeG :=
  RawTwoCellExpr.vcomp cellIdEdgeF cellBeta

/-! ## The agreement rows — each `freeDecide = steinerDecide` by `rfl` (the falsifier passing) -/

/-- Left-unit row: `id[f] . alpha ~ alpha` — both deciders agree (`true`). -/
theorem agreementUnitLeft : freeDecide cellUnitLeftAlpha cellAlpha = steinerDecide cellUnitLeftAlpha cellAlpha := rfl

/-- Right-unit row: `alpha . id[g] ~ alpha` — both agree (`true`). -/
theorem agreementUnitRight : freeDecide cellUnitRightAlpha cellAlpha = steinerDecide cellUnitRightAlpha cellAlpha := rfl

/-- Associativity row — both agree (`true`). -/
theorem agreementAssoc : freeDecide cellAssocLeft cellAssocRight = steinerDecide cellAssocLeft cellAssocRight := rfl

/-- Unit-on-beta row: `id[f] . beta ~ beta` — both agree (`true`), exercising the second generator. -/
theorem agreementUnitBeta : freeDecide cellUnitLeftBeta cellBeta = steinerDecide cellUnitLeftBeta cellBeta := rfl

/-- Reflexivity row: `alpha` vs `alpha` — both agree (`true`). -/
theorem agreementReflexive : freeDecide cellAlpha cellAlpha = steinerDecide cellAlpha cellAlpha := rfl

/-- ★ **DISTINCT-generators row** — `alpha` vs `beta`, both agree (`false`).  The falsifier's teeth:
two genuinely non-convertible parallel generators, distinguished by the one-hot valuation. -/
theorem agreementDistinctGenerators : freeDecide cellAlpha cellBeta = steinerDecide cellAlpha cellBeta := rfl

/-- Structural non-related row: `id[f] . alpha` (~ `alpha`) vs `beta` — both agree (`false`). -/
theorem agreementStructuralNonRelated : freeDecide cellUnitLeftAlpha cellBeta = steinerDecide cellUnitLeftAlpha cellBeta := rfl

/-! ## The verdict values (machine-checked, per row) -/

/-- The `true` rows both decide `true`. -/
theorem verdicts_true :
    freeDecide cellUnitLeftAlpha cellAlpha = true ∧
    freeDecide cellUnitRightAlpha cellAlpha = true ∧
    freeDecide cellAssocLeft cellAssocRight = true ∧
    freeDecide cellUnitLeftBeta cellBeta = true ∧
    freeDecide cellAlpha cellAlpha = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The `false` rows both decide `false` — distinct generators are genuinely non-convertible. -/
theorem verdicts_false :
    freeDecide cellAlpha cellBeta = false ∧
    freeDecide cellUnitLeftAlpha cellBeta = false ∧
    steinerDecide cellAlpha cellBeta = false ∧
    steinerDecide cellUnitLeftAlpha cellBeta = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## The battery summary marker -/

/-- ★ **THE FALSIFIER VERDICT.**  Every battery row's `freeDecide = steinerDecide` type-checks by
`rfl`, so the memo falsifier (ii) did NOT fire on the admitted walking-parallel-pair signature: the
FREE-7 universal decider and the Steiner arithmetic semi-decider AGREE on every curated pair.  A
disagreement would have been a build failure.  `= true`. -/
def fxOmega_agreementBatteryPasses : Bool := true

end FX1Poly.Polygraph.Omega

import FX1Poly.Polygraph.Omega.Steiner.SoundnessFull
import FX1Poly.Polygraph.Omega.Steiner.Reconstruct

/-! # Polygraph/Omega/Steiner/LinearizationCompletenessLedger — the OMEGA-2.5 completeness scope + ledger (r1, B5)

The design record for the boundary-faithful full-chain table, mirroring `Steiner/DesignLock.lean`.  It
cites the shipped r1 pieces (`ChainCell`, `LinearizeFull`, `WhiskerFix`, `SoundnessFull`) and settles the
completeness scope honestly.

## The completeness scope (recon JOB 5 verdict, executed)

  * **Soundness is UNIVERSAL** at chain granularity (`linearizeFullSoundness`, B4) — every dimension.
  * **Completeness stays exactly at `IsAtomWord`** (the whisker-free, interior-id-free single-generator
    vcomp-word fragment).  The chain sibling REGRESSES correctly there: on atom words all boundaries are
    the canonical base cell, so the pole rows are DETERMINED by the dimension (`polesOf_atomWord_eq`) and
    the chain table decides conv EXACTLY as the single vector does (`atomWord_conv_iff_linearizeFull_eq`).
    Both decider verdicts are exhibited at n=3 AND n=4.
  * **The lossy-whisker obstruction DISSOLVES in the REFUTATION direction** (B3/B4): whisker-conflated
    pairs are now separated and genuinely refuted (`whiskerFix_not_conv`).  This is the round's headline.
  * **The SOLE surviving completeness obstruction is the id-congruence gap** — `SaturatedConvOver` has no
    `idCongr` / whisker-1-cell congruence, so a map-IN (reconstruct) cannot lift interior identities /
    whiskerings.  Chain granularity strengthens the SEMANTICS (linearize), NOT the SYNTAX (the congruence
    constructor set), so this gap does NOT dissolve.  It is EXACTLY the OMEGA-1 B2 conv-leg wall
    (`fxOmega_bridgeDimTwoConvLegOpen`) resurfacing on the map-IN side: adding `idCongr` +
    whisker-1-cell congruence closes BOTH the OMEGA-1 n=2 bridge AND OMEGA-2.5 whiskered completeness at
    once.  Named as the r2 target; the marker stays `false`.

Raw Lean 4 + Init; the regression theorems plus `Bool` markers, so every declaration is axiom-free.
Per-declaration `#assert_no_axioms` in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Steiner

/-! ## Completeness regresses to the chain table on the atom-word fragment -/

/-- Every atom word's SOURCE boundary is the canonical base cell (the source dual of
`boundaryTarget_atomWord`) — so an atom word's boundary chain is degenerate, determined by dimension. -/
theorem boundarySource_atomWord {dim : Nat} {cell : CellExpr crownComputad (dim + 1)}
    (hAtom : IsAtomWord cell) : boundarySource cell = crownBaseCell dim := by
  induction hAtom with
  | atom => rfl
  | @vcomp _ _ _ _ ihLeft _ => exact ihLeft

/-- ★ **An atom word's pole rows are DETERMINED by its dimension.**  All boundaries collapse to the
canonical base cell, so any two atom words of the same dimension have identical poles — the chain table
adds NO discriminating power over the single vector on the whisker-free fragment. -/
theorem polesOf_atomWord_eq {dim : Nat} {cellA cellB : CellExpr crownComputad (dim + 1)}
    (hAtomA : IsAtomWord cellA) (hAtomB : IsAtomWord cellB) :
    polesOf crownValuation cellA = polesOf crownValuation cellB := by
  show ((linearize crownValuation (boundarySource cellA)).coordinates,
        (linearize crownValuation (boundaryTarget cellA)).coordinates)
        :: polesOf crownValuation (boundarySource cellA)
    = ((linearize crownValuation (boundarySource cellB)).coordinates,
        (linearize crownValuation (boundaryTarget cellB)).coordinates)
        :: polesOf crownValuation (boundarySource cellB)
  rw [boundarySource_atomWord hAtomA, boundarySource_atomWord hAtomB,
    boundaryTarget_atomWord hAtomA, boundaryTarget_atomWord hAtomB]

/-- ★★ **THE CHAIN TABLE IS ALSO COMPLETE ON THE ATOM-WORD FRAGMENT.**  On `IsAtomWord`, at every
dimension, free-strict convertibility is EXACTLY chain-table equality — the regression of the shipped
crown iff (`atomWord_conv_iff_linearize_eq`) to the strictly-richer full table.  The `→` is the universal
chain soundness; the `←` extracts the top row (the single vector) and rides the shipped completeness,
because the poles carry no extra information on the whisker-free fragment. -/
theorem atomWord_conv_iff_linearizeFull_eq {dim : Nat} {cellA cellB : CellExpr crownComputad (dim + 1)}
    (hAtomA : IsAtomWord cellA) (hAtomB : IsAtomWord cellB) :
    SaturatedConvOver crownComputad (StrictAxiomRel crownComputad) cellA cellB
      ↔ linearizeFull crownValuation cellA = linearizeFull crownValuation cellB := by
  constructor
  · intro conv
    exact linearizeFull_eq_of_saturatedConv crownValuation conv
  · intro chainEqual
    have topEqual : linearize crownValuation cellA = linearize crownValuation cellB :=
      congrArg SteinerCell.mk (congrArg SteinerChainCell.top chainEqual)
    exact (atomWord_conv_iff_linearize_eq hAtomA hAtomB).mpr topEqual

/-! ## The census — BOTH decider verdicts, both fragments (regression + strengthening) -/

/-- n=3 regression: the chain decider AGREES with the shipped single-vector decider (equal → `true`). -/
example : decideFullConvSound crownValuation word3Right word3Left = true := by decide

/-- n=3 regression: unequal-length atom words decide DISTINCT (`false`). -/
example : decideFullConvSound crownValuation word3Right word3One = false := by decide

/-- n=4 regression: equal atom words decide `true` (dimension-genericity). -/
example : decideFullConvSound crownValuation word4Right word4Left = true := by decide

/-- n=4 regression: unequal atom words decide `false`. -/
example : decideFullConvSound crownValuation word4Right word4Two = false := by decide

/-- ★ The STRENGTHENING: on the whiskered fragment the chain decider REFUTES (`false`) where the
single-vector decider CONFLATES (`true`).  The chain table is strictly the stronger refuter. -/
example : decideFullConvSound whiskerDemoValuation (whiskeredCell true) (whiskeredCell false) = false := by
  decide

example : decideFreeConvSound whiskerDemoValuation (whiskeredCell true) (whiskeredCell false) = true := rfl

/-! ## The OMEGA-2.5 r1 honesty markers (the ledger; every marker names its scope) -/

/-- ★ **B1/B2 — the chain carrier + ν map are SHIPPED.**  `SteinerChainCell` (`{poles, top}`) with
structural `DecidableEq`, the rowwise pole-table kit, `composeAtFull`; `linearizeFull` with the `rfl`
projection tie `linearizeFull_top` (top = the shipped single vector), `polesOf_length`, the four one-hole
congruences, and the UNCONDITIONAL `composeAtFull` homomorphism.  `= true`. -/
def fxOmega25_chainCarrierShipped : Bool := true

/-- ★★ **B3 — THE ACCEPTANCE TEST PASSES.**  `linearizeFull` DISTINGUISHES the exact OMEGA-2 lossy
whisker pair (`whiskerFix_linearizeFull_distinguishes`) that the single vector CONFLATES
(`whiskerFix_linearize_conflates`) — machine-checked on a concrete faithful valuation, with transparent
pole witnesses.  The lossy-whisker obstruction dissolves in the refutation direction.  `= true`. -/
def fxOmega25_whiskerFixAcceptanceTest : Bool := true

/-- ★ **B4 — the CROWN soundness at chain granularity is UNIVERSAL + UNCONDITIONAL.**
`linearizeFullSoundness` inhabits `OmegaTwoLinearizeSoundnessShape` at the chain carrier via
`SaturatedConvOver.recInto` over `linearizeFullAbsorbs`; all eight strict-axiom rows are boundary-parallel
(`polesOf_ofRelation_eq`, `cases <;> rfl`).  The whisker fix is promoted to genuine NON-convertibility
(`whiskerFix_not_conv`).  `= true`. -/
def fxOmega25_chainSoundnessUniversal : Bool := true

/-- ★ **B5 — completeness stays exactly at `IsAtomWord`, and the chain table REGRESSES there.**  On the
whisker-free single-generator fragment the chain table decides conv EXACTLY as the single vector
(`atomWord_conv_iff_linearizeFull_eq`, poles determined by dimension via `polesOf_atomWord_eq`); both
decider verdicts exhibited n=3 AND n=4.  `= true`. -/
def fxOmega25_completenessRegressesOnAtomWord : Bool := true

/-- ★ **B5 — GENERAL completeness is OPEN by the SOLE remaining obstruction: the id-congruence gap.**
The lossy-whisker obstruction DISSOLVED (B3/B4, refutation direction), but whiskered / interior-id
completeness (the map-IN direction) still needs an `idCongr` + whisker-1-cell congruence extension of
`SaturatedConvOver` — chain granularity strengthens the SEMANTICS, not the congruence's constructor set.
This is EXACTLY the OMEGA-1 B2 conv-leg wall (`fxOmega_bridgeDimTwoConvLegOpen`): closing it in r2 pays
BOTH debts.  (Multi-generator atom words additionally need the deferred absolute-index bookkeeping.)
`= false` (the GENERAL case is NOT closed — honest). -/
def fxOmega25_generalCompletenessOpenIdCongr : Bool := false

/-- ★ **Honesty marker — OMEGA-2.5 r1 is COMPLETE.**  The chain carrier + arithmetic kit (B1), the ν map
+ projection tie + congruences (B2), the acceptance test (B3), the chain-granularity crown soundness (B4),
and the completeness-scope regression + honest general-obstruction ledger (B5) all type-check zero-axiom;
this marker imports every r1 piece.  `= true`. -/
def fxOmega25_r1Complete : Bool := true

end FX1Poly.Polygraph.Omega

import FX1Poly.Polygraph.Omega.DesignLock
import FX1Poly.Polygraph.Omega.Steiner.Linearize

/-! # Polygraph/Omega/Steiner/Soundness — the CROWN soundness fold (OMEGA-2 r1, B4)

★ **The ~8x-bespoke soundness leg made generic ONCE.**  `linearize` is a sound invariant of the free
strict congruence: `SaturatedConvOver (StrictAxiomRel) a b → linearize a = linearize b`.  Proved by the
shipped OMEGA-1 eliminator `SaturatedConvOver.recInto` (the invariant fold) at
`targetRel := fun a b => linearize a = linearize b`, inhabiting the shipped handoff shape
`OmegaTwoLinearizeSoundnessShape` (`Omega/DesignLock.lean`).

## Every one of the eight strict-axiom rows discharged UNCONDITIONALLY

The `ofRelation` field discharges all eight `StrictAxiomRel` rows by the B-arith kit
(`CoordinateArithmetic.lean`) — the whole per-row lemma ledger, none of them a composability side
condition:

  | row                     | arithmetic identity                                            |
  | ----------------------- | -------------------------------------------------------------- |
  | `vcompAssoc`            | `addCoordinates_assoc`                                          |
  | `vcompUnitLeft`         | `addCoordinates_zeroVector_left` (id = degenerate zero table)   |
  | `vcompUnitRight`        | `addCoordinates_zeroVector_right`                               |
  | `whiskerLeftUnit`       | `rfl` (both sides = the degenerate zero table)                 |
  | `whiskerRightUnit`      | `rfl`                                                           |
  | `whiskerLeftFunctorial` | `rfl` (whiskering projects to the main factor; sum both sides) |
  | `whiskerRightFunctorial`| `rfl`                                                           |
  | `interchange` (Godement)| `addCoordinates_comm` — interchange IS addition commutativity  |

The four congruence legs close by `congrArg` / the whisker computation lemmas; `refl`/`symm`/`trans`
are `rfl`/`Eq.symm`/`Eq.trans`.  The soundness is UNCONDITIONAL — the recon's forecast shared-boundary
crux dissolves because on the free fragment the shared boundary is the degenerate (zero) table (see
`linearize_vcomp_composeAt`), so no boundary-dependent shared appears in any row.  The inherited
OMEGA-1 conv-leg wall (the missing `id`-congruence) is invisible: `recInto` is a map-OUT — it consumes
a derivation, never constructs the id-congruence — the first concrete payoff of the hybrid split.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Steiner

/-! ## The target relation and the absorbing-congruence instance -/

/-- ★ **`linearize` absorbs the free strict congruence.**  The equality relation
`fun a b => linearize valuation a = linearize valuation b` is an `IsSaturatedCongruence` over the
strict-axiom rows: all eight rows discharge by the B-arith kit, the congruences by `congrArg`, and the
groupoid legs are trivial.  This is the fold data `SaturatedConvOver.recInto` consumes. -/
def linearizeAbsorbs {computad : OmegaComputad} (valuation : ComputadValuation computad) :
    IsSaturatedCongruence computad (StrictAxiomRel computad)
      (fun {_dim} cellAlpha cellBeta => linearize valuation cellAlpha = linearize valuation cellBeta) where
  ofRelation := by
    intro _dim _cellAlpha _cellBeta row
    cases row with
    | vcompAssoc cellA cellB cellC =>
        exact congrArg SteinerCell.mk
          (addCoordinates_assoc (linearize valuation cellA).coordinates
            (linearize valuation cellB).coordinates (linearize valuation cellC).coordinates)
    | vcompUnitLeft cellA =>
        have unitProof : addCoordinates (zeroVector valuation.ambientDim)
            (linearize valuation cellA).coordinates = (linearize valuation cellA).coordinates := by
          rw [← linearize_length valuation cellA]
          exact addCoordinates_zeroVector_left (linearize valuation cellA).coordinates
        exact congrArg SteinerCell.mk unitProof
    | vcompUnitRight cellA =>
        have unitProof : addCoordinates (linearize valuation cellA).coordinates
            (zeroVector valuation.ambientDim) = (linearize valuation cellA).coordinates := by
          rw [← linearize_length valuation cellA]
          exact addCoordinates_zeroVector_right (linearize valuation cellA).coordinates
        exact congrArg SteinerCell.mk unitProof
    | whiskerLeftUnit whiskeringCell innerCell => rfl
    | whiskerRightUnit innerCell whiskeringCell => rfl
    | whiskerLeftFunctorial whiskeringCell cellBeta cellGamma => rfl
    | whiskerRightFunctorial cellAlpha cellBeta whiskeringCell => rfl
    | interchange cellAlpha cellBeta =>
        exact congrArg SteinerCell.mk
          (addCoordinates_comm (linearize valuation cellAlpha).coordinates
            (linearize valuation cellBeta).coordinates)
  vcompCongrLeft := by
    intro _dim _cellAlpha _cellAlpha' _cellBeta convFactor
    rw [linearize_vcomp, linearize_vcomp, convFactor]
  vcompCongrRight := by
    intro _dim _cellAlpha _cellBeta _cellBeta' convFactor
    rw [linearize_vcomp, linearize_vcomp, convFactor]
  whiskerLeftCongr := by
    intro _dim _whiskeringCell _cellBeta _cellBeta' convFactor
    rw [linearize_whiskerLeft, linearize_whiskerLeft]
    exact convFactor
  whiskerRightCongr := by
    intro _dim _cellAlpha _cellAlpha' _whiskeringCell convFactor
    rw [linearize_whiskerRight, linearize_whiskerRight]
    exact convFactor
  refl := by intro _dim _cell; rfl
  symm := by intro _dim _cellAlpha _cellBeta convFactor; exact convFactor.symm
  trans := by
    intro _dim _cellAlpha _cellBeta _cellGamma convLeft convRight
    exact convLeft.trans convRight

/-! ## The soundness theorem — inhabiting the shipped handoff shape -/

/-- ★ **THE OMEGA-2 CROWN SOUNDNESS.**  `linearize` is invariant under the free strict congruence at
EVERY dimension: `SaturatedConvOver (StrictAxiomRel) a b → linearize a = linearize b`.  Inhabits the
shipped `OmegaTwoLinearizeSoundnessShape` by folding the OMEGA-1 eliminator `SaturatedConvOver.recInto`
over `linearizeAbsorbs`.  Zero-axiom, unconditional — composition is decided by `List Int` equality. -/
theorem linearizeSoundness {computad : OmegaComputad} (valuation : ComputadValuation computad) :
    OmegaTwoLinearizeSoundnessShape computad SteinerCell (linearize valuation) := by
  intro _dim _cellAlpha _cellBeta conv
  exact SaturatedConvOver.recInto (linearizeAbsorbs valuation) conv

/-- Corollary in direct form (the shape unfolded), for downstream consumers. -/
theorem linearize_eq_of_saturatedConv {computad : OmegaComputad}
    (valuation : ComputadValuation computad) {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim}
    (conv : SaturatedConvOver computad (StrictAxiomRel computad) cellAlpha cellBeta) :
    linearize valuation cellAlpha = linearize valuation cellBeta :=
  linearizeSoundness valuation conv

end FX1Poly.Polygraph.Omega

import FX1Poly.Polygraph.Omega.Steiner.Soundness
import FX1Poly.Polygraph.Omega.Steiner.WhiskerFix

/-! # Polygraph/Omega/Steiner/SoundnessFull — the CROWN soundness at chain granularity (OMEGA-2.5 r1, B4)

★ **The full-table analog of the shipped OMEGA-2 soundness.**  `linearizeFull` is a sound invariant of
the free strict congruence at EVERY dimension: `SaturatedConvOver (StrictAxiomRel) a b → linearizeFull a
= linearizeFull b`.  Folded through the SHIPPED OMEGA-1 eliminator `SaturatedConvOver.recInto`
(`Congruence.lean`) over `linearizeFullAbsorbs`.  Because the chain-level refuter is strictly stronger
than the single-vector one, this promotes the whisker-fix (B3) from a data fact to a genuine
NON-CONVERTIBILITY refutation: `not_conv_of_linearizeFull_ne` refutes the exact whisker-conflated pair
that `not_conv_of_linearize_ne` could not.

## The soundness fold (the poles ride rfl on the parallel rows, addCoordinates_assoc on the whisker coherences)

The eight boundary-parallel `StrictAxiomRel` rows discharge their POLES definitionally
(`polesOf_ofRelation_eq`, `rfl`) and their TOP row by the shipped single-vector proof
(`linearizeAbsorbs.ofRelation`, `Soundness.lean`).  The three WP-PROP-r19 whisker-1-cell coherences
(`whiskerAssocLeft` / `whiskerAssocRight` / `whiskerLeftRightCommute`) are non-boundary-parallel, so their
poles do NOT close by `rfl`: the top pole reassociates by `addCoordinates_assoc` (source + target) while the
boundary spine below is definitionally shared — this is the one place `polesOf_ofRelation_eq` is not uniform.
The four one-hole congruences are the B2 congruence lemmas (`linearizeFull_vcompCongrLeft` etc.); `refl` /
`symm` / `trans` are `rfl` / `Eq.symm` / `Eq.trans`.

## The id-dissolution assessment (recon JOB 5, executed)

The `id`-congruence obstruction is INVISIBLE here, exactly as at the single-vector level: `recInto` is a
map-OUT — it CONSUMES a derivation, never CONSTRUCTS an id-congruence.  So chain granularity strengthens
the SEMANTIC tracking (identities linearize to `{top := zeroVector, poles := the interior chain}`, which
is injective on the interior) without needing the missing `idCongr` rule.  The completeness (map-IN)
direction still hits it — the honest residual named in the B5 ledger.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Steiner

/-! ## The per-row poles agreement (all eight rows are boundary-parallel) -/

/-- ★ **Every strict-axiom row absorbs into `polesOf` at chain granularity.**  The eight boundary-parallel
rows (assoc, the two units, the two whisker-units, the two whisker-functorialities, the Godement interchange)
have definitionally-equal boundary poles, so they close by `rfl`.  The three WP-PROP-r19 whisker-1-cell
coherences (`whiskerAssocLeft` / `whiskerAssocRight` / `whiskerLeftRightCommute`) are NOT boundary-parallel —
their `boundarySource`/`boundaryTarget` differ by exactly `vcompAssoc` — yet their poles STILL agree at chain
granularity: the top pole reassociates by `addCoordinates_assoc` (twice, source + target) while the boundary
SPINE below is definitionally shared.  This is the substrate-round distinction the r18 wall was too coarse to
see: "non-boundary-parallel" is NOT "chain-unsound".  (The identity-whisker unitor, by contrast, IS
chain-unsound — its spine visits the free whiskering 1-cell — and stays OUT of `StrictAxiomRel`.) -/
theorem polesOf_ofRelation_eq {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim}
    (row : StrictAxiomRel computad cellAlpha cellBeta) :
    polesOf valuation cellAlpha = polesOf valuation cellBeta := by
  cases row with
  | vcompAssoc _ _ _ => rfl
  | vcompUnitLeft _ => rfl
  | vcompUnitRight _ => rfl
  | whiskerLeftUnit _ _ => rfl
  | whiskerRightUnit _ _ => rfl
  | whiskerLeftFunctorial _ _ _ => rfl
  | whiskerRightFunctorial _ _ _ => rfl
  | interchange _ _ => rfl
  | whiskerAssocLeft whiskP whiskQ inner =>
      show (addCoordinates (addCoordinates (linearize valuation whiskP).coordinates
              (linearize valuation whiskQ).coordinates)
              (linearize valuation (boundarySource inner)).coordinates,
            addCoordinates (addCoordinates (linearize valuation whiskP).coordinates
              (linearize valuation whiskQ).coordinates)
              (linearize valuation (boundaryTarget inner)).coordinates)
            :: polesOf valuation (CellExpr.vcomp (CellExpr.vcomp whiskP whiskQ) (boundarySource inner))
          = (addCoordinates (linearize valuation whiskP).coordinates
              (addCoordinates (linearize valuation whiskQ).coordinates
                (linearize valuation (boundarySource inner)).coordinates),
             addCoordinates (linearize valuation whiskP).coordinates
              (addCoordinates (linearize valuation whiskQ).coordinates
                (linearize valuation (boundaryTarget inner)).coordinates))
            :: polesOf valuation (CellExpr.vcomp whiskP (CellExpr.vcomp whiskQ (boundarySource inner)))
      rw [addCoordinates_assoc (linearize valuation whiskP).coordinates
            (linearize valuation whiskQ).coordinates (linearize valuation (boundarySource inner)).coordinates,
          addCoordinates_assoc (linearize valuation whiskP).coordinates
            (linearize valuation whiskQ).coordinates (linearize valuation (boundaryTarget inner)).coordinates]
      rfl
  | whiskerAssocRight inner whiskP whiskQ =>
      show (addCoordinates (linearize valuation (boundarySource inner)).coordinates
              (addCoordinates (linearize valuation whiskP).coordinates (linearize valuation whiskQ).coordinates),
            addCoordinates (linearize valuation (boundaryTarget inner)).coordinates
              (addCoordinates (linearize valuation whiskP).coordinates (linearize valuation whiskQ).coordinates))
            :: polesOf valuation (CellExpr.vcomp (boundarySource inner) (CellExpr.vcomp whiskP whiskQ))
          = (addCoordinates (addCoordinates (linearize valuation (boundarySource inner)).coordinates
                (linearize valuation whiskP).coordinates) (linearize valuation whiskQ).coordinates,
             addCoordinates (addCoordinates (linearize valuation (boundaryTarget inner)).coordinates
                (linearize valuation whiskP).coordinates) (linearize valuation whiskQ).coordinates)
            :: polesOf valuation (CellExpr.vcomp (CellExpr.vcomp (boundarySource inner) whiskP) whiskQ)
      rw [addCoordinates_assoc (linearize valuation (boundarySource inner)).coordinates
            (linearize valuation whiskP).coordinates (linearize valuation whiskQ).coordinates,
          addCoordinates_assoc (linearize valuation (boundaryTarget inner)).coordinates
            (linearize valuation whiskP).coordinates (linearize valuation whiskQ).coordinates]
      rfl
  | whiskerLeftRightCommute whiskP inner whiskQ =>
      show (addCoordinates (addCoordinates (linearize valuation whiskP).coordinates
                (linearize valuation (boundarySource inner)).coordinates) (linearize valuation whiskQ).coordinates,
            addCoordinates (addCoordinates (linearize valuation whiskP).coordinates
                (linearize valuation (boundaryTarget inner)).coordinates) (linearize valuation whiskQ).coordinates)
            :: polesOf valuation (CellExpr.vcomp (CellExpr.vcomp whiskP (boundarySource inner)) whiskQ)
          = (addCoordinates (linearize valuation whiskP).coordinates
              (addCoordinates (linearize valuation (boundarySource inner)).coordinates
                (linearize valuation whiskQ).coordinates),
             addCoordinates (linearize valuation whiskP).coordinates
              (addCoordinates (linearize valuation (boundaryTarget inner)).coordinates
                (linearize valuation whiskQ).coordinates))
            :: polesOf valuation (CellExpr.vcomp whiskP (CellExpr.vcomp (boundarySource inner) whiskQ))
      rw [addCoordinates_assoc (linearize valuation whiskP).coordinates
            (linearize valuation (boundarySource inner)).coordinates (linearize valuation whiskQ).coordinates,
          addCoordinates_assoc (linearize valuation whiskP).coordinates
            (linearize valuation (boundaryTarget inner)).coordinates (linearize valuation whiskQ).coordinates]
      rfl

/-- The full-chain table absorbs a strict-axiom row: poles by `polesOf_ofRelation_eq`, top by the shipped
single-vector fold `linearizeAbsorbs.ofRelation`. -/
theorem linearizeFull_ofRelation {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim}
    (row : StrictAxiomRel computad cellAlpha cellBeta) :
    linearizeFull valuation cellAlpha = linearizeFull valuation cellBeta :=
  linearizeFull_eq_of valuation (polesOf_ofRelation_eq valuation row)
    (congrArg SteinerCell.coordinates ((linearizeAbsorbs valuation).ofRelation row))

/-! ## The absorbing-congruence instance -/

/-- ★ **`linearizeFull` absorbs the free strict congruence.**  The equality relation
`fun a b => linearizeFull a = linearizeFull b` is an `IsSaturatedCongruence` over the strict-axiom rows:
`ofRelation` by `linearizeFull_ofRelation`, the four one-hole congruences by the B2 congruence lemmas,
the groupoid legs trivial.  The fold data `SaturatedConvOver.recInto` consumes. -/
def linearizeFullAbsorbs {computad : OmegaComputad} (valuation : ComputadValuation computad) :
    IsSaturatedCongruence computad (StrictAxiomRel computad)
      (fun {_dim} cellAlpha cellBeta =>
        linearizeFull valuation cellAlpha = linearizeFull valuation cellBeta) where
  ofRelation := by
    intro _dim _cellAlpha _cellBeta row
    exact linearizeFull_ofRelation valuation row
  vcompCongrLeft := by
    intro _dim _cellAlpha _cellAlpha' cellBeta chainEqual
    exact linearizeFull_vcompCongrLeft valuation cellBeta chainEqual
  vcompCongrRight := by
    intro _dim cellAlpha _cellBeta _cellBeta' chainEqual
    exact linearizeFull_vcompCongrRight valuation cellAlpha chainEqual
  whiskerLeftCongr := by
    intro _dim whiskeringCell _cellBeta _cellBeta' chainEqual
    exact linearizeFull_whiskerLeftCongr valuation whiskeringCell chainEqual
  whiskerRightCongr := by
    intro _dim _cellAlpha _cellAlpha' whiskeringCell chainEqual
    exact linearizeFull_whiskerRightCongr valuation whiskeringCell chainEqual
  refl := by intro _dim _cell; rfl
  symm := by intro _dim _cellAlpha _cellBeta chainEqual; exact chainEqual.symm
  trans := by
    intro _dim _cellAlpha _cellBeta _cellGamma chainLeft chainRight
    exact chainLeft.trans chainRight

/-! ## The soundness theorem -/

/-- ★★ **THE OMEGA-2.5 CROWN SOUNDNESS.**  `linearizeFull` is invariant under the free strict congruence
at EVERY dimension — the full-table analog of `linearizeSoundness`.  Inhabits the shipped
`OmegaTwoLinearizeSoundnessShape` at the chain carrier via `SaturatedConvOver.recInto` over
`linearizeFullAbsorbs`.  Zero-axiom, unconditional. -/
theorem linearizeFullSoundness {computad : OmegaComputad} (valuation : ComputadValuation computad) :
    OmegaTwoLinearizeSoundnessShape computad SteinerChainCell (linearizeFull valuation) := by
  intro _dim _cellAlpha _cellBeta conv
  exact SaturatedConvOver.recInto (linearizeFullAbsorbs valuation) conv

/-- Corollary in direct form (the shape unfolded). -/
theorem linearizeFull_eq_of_saturatedConv {computad : OmegaComputad}
    (valuation : ComputadValuation computad) {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim}
    (conv : SaturatedConvOver computad (StrictAxiomRel computad) cellAlpha cellBeta) :
    linearizeFull valuation cellAlpha = linearizeFull valuation cellBeta :=
  linearizeFullSoundness valuation conv

/-! ## The strictly-stronger sound refuter -/

/-- ★ **The sound refutation at chain granularity.**  DISTINCT chain tables soundly refute
convertibility — strictly stronger than `not_conv_of_linearize_ne`, since the chain table separates
whisker-conflated pairs the single vector merges. -/
theorem not_conv_of_linearizeFull_ne {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim}
    (tablesDiffer : linearizeFull valuation cellAlpha ≠ linearizeFull valuation cellBeta) :
    ¬ SaturatedConvOver computad (StrictAxiomRel computad) cellAlpha cellBeta :=
  fun conv => tablesDiffer (linearizeFull_eq_of_saturatedConv valuation conv)

/-- **The full-chain sound semi-decider** — chain-table equality, a SOUND necessary condition for
convertibility (decided by the shipped structural `DecidableEq SteinerChainCell`). -/
def decideFullConvSound {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (cellAlpha cellBeta : CellExpr computad dim) : Bool :=
  decide (linearizeFull valuation cellAlpha = linearizeFull valuation cellBeta)

/-! ## Non-vacuity — soundness both ways -/

/-- ★ **THE WHISKER FIX PROMOTED TO NON-CONVERTIBILITY.**  The exact OMEGA-2 lossy pair is now genuinely
REFUTED: `whiskerFix_linearizeFull_distinguishes` (B3) + chain soundness ⟹ the two whiskered cells are
NON-convertible — a refutation the single vector could not make (it conflates them). -/
theorem whiskerFix_not_conv :
    ¬ SaturatedConvOver whiskerDemoComputad (StrictAxiomRel whiskerDemoComputad)
        (whiskeredCell true) (whiskeredCell false) :=
  not_conv_of_linearizeFull_ne whiskerDemoValuation whiskerFix_linearizeFull_distinguishes

/-- ★ **Soundness in the positive direction, end to end.**  A genuine `SaturatedConvOver` derivation (the
`vcompUnitLeft` row) maps through the FULL fold to EQUAL chain tables — the chain soundness is
non-vacuous (it tracks the interior boundary poles, not just the top vector). -/
theorem demo_conv_chain_tables_equal :
    linearizeFull demoValuation
        (CellExpr.vcomp (CellExpr.id (boundarySource cellThreeA)) cellThreeA)
      = linearizeFull demoValuation cellThreeA :=
  linearizeFull_eq_of_saturatedConv demoValuation
    (SaturatedConvOver.ofRelation (StrictAxiomRel.vcompUnitLeft cellThreeA))

/-- The full-chain semi-decider REFUTES the whisker pair (`false`) — where the single-vector semi-decider
CONFLATES it (`true`).  The chain refuter is strictly stronger. -/
example : decideFullConvSound whiskerDemoValuation (whiskeredCell true) (whiskeredCell false) = false := by
  decide

/-- The single-vector semi-decider says the SAME pair is EQUAL (`true`) — the conflation the chain table
overturns. -/
example : decideFreeConvSound whiskerDemoValuation (whiskeredCell true) (whiskeredCell false) = true := rfl

end FX1Poly.Polygraph.Omega

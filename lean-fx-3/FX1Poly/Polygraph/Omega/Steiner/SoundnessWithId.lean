import FX1Poly.Polygraph.Omega.Steiner.SoundnessFull
import FX1Poly.Polygraph.Omega.CongruenceWithId

/-! # Polygraph/Omega/Steiner/SoundnessWithId — the soundness cascade over the idCongr sibling (OMEGA-3 r2, B2)

★ **The Steiner invariants re-closed over `SaturatedConvOverWithId`.**  The shipped single-vector
(`Soundness.lean`) and chain (`SoundnessFull.lean`) soundness folds run over the 8-constructor
`SaturatedConvOver`; this file re-closes both over the 11-constructor sibling, adding the THREE new fields
per absorbing instance.  The eight shipped fields are REUSED verbatim (the sibling's field types are
identical to the shipped structure's), so this is genuinely additive — no shipped decl is edited.

## The three new fields, per the recon verdict

  * **Single vector (`linearizeAbsorbsWithId`).**  All three are `rfl`, the hypothesis DISCARDED:
    - `idCongr` : `linearize (id a) = linearize (id b)` — both `= ⟨zeroVector⟩` (identities carry no top
      content); NOT a degenerate lift, literally the same zero table.
    - `whiskerLeftWhiskerCongr` / `whiskerRightWhiskerCongr` : both sides project to `linearize inner`
      (the whisker forgets the whiskering cell).
  * **Chain (`linearizeFullAbsorbsWithId`).**  The genuine NEW content:
    - `idCongr` = ★ **the degenerate-pole extension**: `id a` prepends the diagonal pole `((linearize
      a).coords, (linearize a).coords)` to `polesOf a`, discharged through `linearizeFull_eq_succ` reading
      the two top-pole coords and the boundary-source chain off the hypothesis (`boundarySource (id a) = a`
      definitionally).
    - the whisker-1-cell congruences mirror the shipped whisker congruences but swap
      `vcompCongrLeft`/`vcompCongrRight` (the WHISKER cell is now the varying factor of the boundary vcomp).

The single vector remains a COARSE invariant of the richer sibling (the extra id / whisker content is
invisible to it) — fine for soundness and refutation.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Steiner

/-! ## The single-vector absorbing instance over the sibling -/

/-- ★ **`linearize` absorbs the idCongr sibling.**  The eight shipped fields are reused from
`linearizeAbsorbs`; the three new fields are all `rfl` (the hypothesis discarded): identities linearize to
the same zero table, whiskers project past the whiskering cell. -/
def linearizeAbsorbsWithId {computad : OmegaComputad} (valuation : ComputadValuation computad) :
    IsSaturatedCongruenceWithId computad (StrictAxiomRel computad)
      (fun {_dim : Nat} cellAlpha cellBeta =>
        linearize valuation cellAlpha = linearize valuation cellBeta) where
  ofRelation := (linearizeAbsorbs valuation).ofRelation
  vcompCongrLeft := (linearizeAbsorbs valuation).vcompCongrLeft
  vcompCongrRight := (linearizeAbsorbs valuation).vcompCongrRight
  whiskerLeftCongr := (linearizeAbsorbs valuation).whiskerLeftCongr
  whiskerRightCongr := (linearizeAbsorbs valuation).whiskerRightCongr
  idCongr := by intro _dim _cellAlpha _cellBeta _hyp; rfl
  whiskerLeftWhiskerCongr := by intro _dim _whiskerA _whiskerA' _innerCell _hyp; rfl
  whiskerRightWhiskerCongr := by intro _dim _innerCell _whiskerA _whiskerA' _hyp; rfl
  refl := (linearizeAbsorbs valuation).refl
  symm := (linearizeAbsorbs valuation).symm
  trans := (linearizeAbsorbs valuation).trans

/-- ★ **THE SINGLE-VECTOR SOUNDNESS over the sibling.**  `linearize` is invariant under the idCongr
saturated congruence at every dimension.  Folds `SaturatedConvOverWithId.recInto` over
`linearizeAbsorbsWithId`. -/
theorem linearize_eq_of_saturatedConvWithId {computad : OmegaComputad}
    (valuation : ComputadValuation computad) {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim}
    (conv : SaturatedConvOverWithId computad (StrictAxiomRel computad) cellAlpha cellBeta) :
    linearize valuation cellAlpha = linearize valuation cellBeta :=
  SaturatedConvOverWithId.recInto (linearizeAbsorbsWithId valuation) conv

/-- The single-vector sound refutation over the sibling — distinct tables refute sibling convertibility. -/
theorem not_conv_of_linearize_ne_withId {computad : OmegaComputad}
    (valuation : ComputadValuation computad) {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim}
    (tablesDiffer : linearize valuation cellAlpha ≠ linearize valuation cellBeta) :
    ¬ SaturatedConvOverWithId computad (StrictAxiomRel computad) cellAlpha cellBeta :=
  fun conv => tablesDiffer (linearize_eq_of_saturatedConvWithId valuation conv)

/-! ## The chain absorbing instance over the sibling (the degenerate-pole extension + mirror lemmas) -/

/-- ★ **`linearizeFull` absorbs the idCongr sibling.**  The eight shipped fields are reused from
`linearizeFullAbsorbs`; `idCongr` is the degenerate-pole extension (the chain granularity of "identities
prepend a diagonal pole"), and the whisker-1-cell congruences mirror the shipped whisker congruences with
the whisker cell as the varying boundary factor. -/
def linearizeFullAbsorbsWithId {computad : OmegaComputad} (valuation : ComputadValuation computad) :
    IsSaturatedCongruenceWithId computad (StrictAxiomRel computad)
      (fun {_dim : Nat} cellAlpha cellBeta =>
        linearizeFull valuation cellAlpha = linearizeFull valuation cellBeta) where
  ofRelation := (linearizeFullAbsorbs valuation).ofRelation
  vcompCongrLeft := (linearizeFullAbsorbs valuation).vcompCongrLeft
  vcompCongrRight := (linearizeFullAbsorbs valuation).vcompCongrRight
  whiskerLeftCongr := (linearizeFullAbsorbs valuation).whiskerLeftCongr
  whiskerRightCongr := (linearizeFullAbsorbs valuation).whiskerRightCongr
  idCongr := by
    intro _dim _cellAlpha _cellBeta hyp
    refine linearizeFull_eq_succ valuation ?_ ?_ ?_ ?_
    · rfl
    · exact linearizeFull_topCoord_eq valuation hyp
    · exact linearizeFull_topCoord_eq valuation hyp
    · exact hyp
  whiskerLeftWhiskerCongr := by
    intro _dim whiskerA whiskerA' innerCell hyp
    refine linearizeFull_eq_succ valuation ?_ ?_ ?_ ?_
    · rfl
    · show addCoordinates (linearize valuation whiskerA).coordinates
          (linearize valuation (boundarySource innerCell)).coordinates
        = addCoordinates (linearize valuation whiskerA').coordinates
          (linearize valuation (boundarySource innerCell)).coordinates
      rw [linearizeFull_topCoord_eq valuation hyp]
    · show addCoordinates (linearize valuation whiskerA).coordinates
          (linearize valuation (boundaryTarget innerCell)).coordinates
        = addCoordinates (linearize valuation whiskerA').coordinates
          (linearize valuation (boundaryTarget innerCell)).coordinates
      rw [linearizeFull_topCoord_eq valuation hyp]
    · exact linearizeFull_vcompCongrLeft valuation (boundarySource innerCell) hyp
  whiskerRightWhiskerCongr := by
    intro _dim innerCell whiskerA whiskerA' hyp
    refine linearizeFull_eq_succ valuation ?_ ?_ ?_ ?_
    · rfl
    · show addCoordinates (linearize valuation (boundarySource innerCell)).coordinates
          (linearize valuation whiskerA).coordinates
        = addCoordinates (linearize valuation (boundarySource innerCell)).coordinates
          (linearize valuation whiskerA').coordinates
      rw [linearizeFull_topCoord_eq valuation hyp]
    · show addCoordinates (linearize valuation (boundaryTarget innerCell)).coordinates
          (linearize valuation whiskerA).coordinates
        = addCoordinates (linearize valuation (boundaryTarget innerCell)).coordinates
          (linearize valuation whiskerA').coordinates
      rw [linearizeFull_topCoord_eq valuation hyp]
    · exact linearizeFull_vcompCongrRight valuation (boundarySource innerCell) hyp
  refl := (linearizeFullAbsorbs valuation).refl
  symm := (linearizeFullAbsorbs valuation).symm
  trans := (linearizeFullAbsorbs valuation).trans

/-- ★★ **THE CHAIN SOUNDNESS over the sibling.**  `linearizeFull` is invariant under the idCongr saturated
congruence at every dimension — the boundary-faithful analog of `linearize_eq_of_saturatedConvWithId`. -/
theorem linearizeFull_eq_of_saturatedConvWithId {computad : OmegaComputad}
    (valuation : ComputadValuation computad) {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim}
    (conv : SaturatedConvOverWithId computad (StrictAxiomRel computad) cellAlpha cellBeta) :
    linearizeFull valuation cellAlpha = linearizeFull valuation cellBeta :=
  SaturatedConvOverWithId.recInto (linearizeFullAbsorbsWithId valuation) conv

/-- The chain-granularity sound refutation over the sibling — strictly stronger than the single vector. -/
theorem not_conv_of_linearizeFull_ne_withId {computad : OmegaComputad}
    (valuation : ComputadValuation computad) {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim}
    (tablesDiffer : linearizeFull valuation cellAlpha ≠ linearizeFull valuation cellBeta) :
    ¬ SaturatedConvOverWithId computad (StrictAxiomRel computad) cellAlpha cellBeta :=
  fun conv => tablesDiffer (linearizeFull_eq_of_saturatedConvWithId valuation conv)

/-! ## Non-vacuity — both directions over the sibling -/

/-- ★ **The whisker fix is refuted over the sibling too.**  The exact OMEGA-2 lossy whisker pair stays
NON-convertible under the richer sibling congruence — the chain refuter carries over verbatim. -/
theorem whiskerFix_not_conv_withId :
    ¬ SaturatedConvOverWithId whiskerDemoComputad (StrictAxiomRel whiskerDemoComputad)
        (whiskeredCell true) (whiskeredCell false) :=
  not_conv_of_linearizeFull_ne_withId whiskerDemoValuation whiskerFix_linearizeFull_distinguishes

/-- ★ **The degenerate-pole idCongr chain field is non-vacuous.**  A genuine sibling convertibility (the
`vcompUnitLeft` row on `cellThreeA`) is lifted by `idCongr` to the identity dim-4 cells, and the chain
soundness maps them to EQUAL chain tables — exercising the degenerate-pole extension on real data. -/
theorem demo_idCongr_chain_tables_equal :
    linearizeFull demoValuation
        (CellExpr.id (CellExpr.vcomp (CellExpr.id (boundarySource cellThreeA)) cellThreeA))
      = linearizeFull demoValuation (CellExpr.id cellThreeA) :=
  linearizeFull_eq_of_saturatedConvWithId demoValuation
    (SaturatedConvOverWithId.idCongr
      (embedSaturatedConvOver (SaturatedConvOver.ofRelation (StrictAxiomRel.vcompUnitLeft cellThreeA))))

end FX1Poly.Polygraph.Omega

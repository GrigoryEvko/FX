import FX1Poly.Polygraph.Omega.CongruenceWithId
import FX1Poly.Polygraph.Omega.Steiner.Reconstruct

/-! # Polygraph/Omega/CongruenceWithIdNonVacuity — the idCongr sibling is non-vacuous (OMEGA-3 r2, B1)

Concrete witnesses that `SaturatedConvOverWithId` proves genuinely NEW convertibilities the shipped
8-constructor `SaturatedConvOver` structurally cannot form.  Over the single-generator crown computad
(`Steiner/Reconstruct.lean`) the differently-associated dim-3 atom words `word3Right` and `word3Left` are
genuinely convertible (`word3_conv`, via associativity + right-unit) — but they are STRUCTURALLY distinct
cells.  The sibling lifts that convertibility one dimension up through `idCongr`, and discharges the exact
OMEGA-1 `vcompIdLeft` jam step, neither of which the shipped relation can do (it has no `idCongr`).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## idCongr lifts a genuine dim-3 convertibility to the dim-4 identity cells -/

/-- ★ **The idCongr non-vacuity.**  `word3Right` and `word3Left` are convertible dim-3 atom words
(`word3_conv`), so `idCongr` (embedded through the free `embedSaturatedConvOver`) proves their dim-4
IDENTITY cells convertible: `CellExpr.id word3Right ~ CellExpr.id word3Left`.  The shipped 8-constructor
`SaturatedConvOver` has NO `idCongr` — it cannot even form this derivation; the sibling ships it. -/
theorem idCongr_word3_nonVacuous :
    SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad)
      (CellExpr.id word3Right) (CellExpr.id word3Left) :=
  SaturatedConvOverWithId.idCongr (embedSaturatedConvOver word3_conv)

/-! ## The exact vcompIdLeft jam, discharged over the sibling on the crown carrier -/

/-- ★ **THE OMEGA-1 WALL STEP, MACHINE-CHECKED OVER THE SIBLING.**  The concrete instance of
`vcompIdLeft_bridgedWithId` on the crown carrier: from the genuine dim-3 convertibility `word3Right ~
word3Left` (= `boundarySource (id word3Left)`), the sibling derives `vcomp (id word3Right) (id word3Left) ~
id word3Left` — `idCongr` supplies `id word3Right ~ id word3Left`, `vcompCongrLeft` places it, and the
`vcompUnitLeft` row absorbs the trailing identity.  This is exactly the `TwoCellStep.vcompIdLeft` reduction
that walled the OMEGA-1 bridge conv leg, now dischargeable because `word3Right ~ word3Left` is only
convertible (not defeq) and the sibling has the `id`-congruence to lift it. -/
theorem crownJam_dischargedWithId :
    SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad)
      (CellExpr.vcomp (CellExpr.id word3Right) (CellExpr.id word3Left)) (CellExpr.id word3Left) :=
  vcompIdLeft_bridgedWithId (CellExpr.id word3Left)
    (embedSaturatedConvOver word3_conv)
    (SaturatedConvOverWithId.ofRelation (StrictAxiomRel.vcompUnitLeft (CellExpr.id word3Left)))

/-- The embedding is non-vacuous: the shipped `word3_conv` derivation folds into the sibling verbatim. -/
theorem embed_word3_nonVacuous :
    SaturatedConvOverWithId crownComputad (StrictAxiomRel crownComputad) word3Right word3Left :=
  embedSaturatedConvOver word3_conv

end FX1Poly.Polygraph.Omega

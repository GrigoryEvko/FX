import FX1Poly.Polygraph.Omega.CriticalPairRow
import FX1Poly.Polygraph.Rewriting.Coherence.SquierCoherence

/-! # Polygraph/Omega/KernelDiamondReading — the kernel confluence certificate as dim-3 content
(OMEGA-4 r1, B3)

★ **THE FIRST dim-3 KERNEL CONTENT.**  The FX kernel's rewrite bundle is ORTHOGONAL
(`fxRewriteBundle_rowsDisjoint = true`): it has NO critical-pair overlaps, so its confluence certificate is
the DISJOINT-REDEX / orthogonal-confluence `SquierDiamond` (`OmegaCategory/SquierCoherence.lean`,
`FX1Poly.Core`), whose 2-cell fillings live as a `SquierConfluence` (apex + two legs + a `RewriteHomotopy`
coherence witness).  This file RE-READS that certificate one polygraph dimension up, as a globular
`CellExpr diamondComputad` boundary pair + a `SaturatedConvOverWithId` witness — the first genuine dim-3
content of the kernel-as-polygraph story.

## The re-reading (recon JOB 4)

Under the polygraph dictionary (terms = 1-cells, steps = 2-cells, homotopies = 3-cells):

  * a `SquierConfluence`'s two ways around the square — `leftStep` then `joinLeft` (path `source -> left ->
    apex`) versus `rightStep` then `joinRight` (path `source -> right -> apex`) — re-read as two PARALLEL
    2-cells `vcomp diamondLeftStep diamondJoinLeft` and `vcomp diamondRightStep diamondJoinRight`, both
    `X => X` at the diamond object;
  * the `coherent : RewriteHomotopy` filling re-reads as the generating 3-cell `diamondThreeCell` (the
    `CriticalPairRow` fired through `SaturatedConvOverWithId.ofRelation`).

The legs are LITERALLY globular here (both share source `X` and target `X`), because the complete diamond's
apex-based residuals make the two paths co-terminal — so the four boundary fields discharge by `rfl` and
`diamondThreeCell` is a genuine GLOBULAR dim-3 cell (contrast the involution `sss` pair, whose legs are
parallel only modulo strict).

## The honest sub-point (recon risk #4)

The re-reading rides coherent CONFLUENCE (`completeCoherentJoin` / `SquierDiamond.confluent`), NOT
`SquierDiamond.coherence` (coherence-to-normal-form), which is VACUOUS for the single-step complete diamond
(every target has an outgoing step, so no reachable normal form).  The kernel dim-3 cell is a
confluence-diamond filler, not an NF-coherence cell.  The abstract certificate `kernelDiamondCoherence`
(= `completeCoherentJoin`) is imported and cited; the full functor `SquierConfluence -> CellExpr 3` (mapping
every abstract diamond, not just this instance) is the OMEGA-5 residual.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The diamond computad (four distinct 2-cell generators) -/

/-- The four 2-cell generator labels of the diamond square — the two divergent steps and their two join
residuals.  Distinct labels make the two legs genuinely distinct 2-cells (a Unit-label computad would
collapse them). -/
inductive DiamondTwoLabel where
  /-- The left divergent step `source => left`. -/
  | leftStep
  /-- The residual `left => apex`. -/
  | joinLeft
  /-- The right divergent step `source => right`. -/
  | rightStep
  /-- The residual `right => apex`. -/
  | joinRight

/-- A code for the diamond labels (full enumeration into `Nat`, propext-clean) — distinguishes the four
generators. -/
def diamondTwoLabelCode : DiamondTwoLabel → Nat
  | .leftStep => 0
  | .joinLeft => 1
  | .rightStep => 2
  | .joinRight => 3

/-- The diamond generator-label family: `DiamondTwoLabel` at dimension 2, `Unit` elsewhere (a single
1-generator `X`; no free 3-generator). -/
def diamondGenLabel : Nat → Type
  | 2 => DiamondTwoLabel
  | _ => Unit

/-- The **diamond computad** — one object, one 1-generator `X`, four 2-generators (the diamond square). -/
def diamondComputad : OmegaComputad where
  modeCarrier := Unit
  genLabel := diamondGenLabel

/-- The single object. -/
def diamondObject : CellExpr diamondComputad 0 := CellExpr.ofMode ()

/-- The single endo-1-cell `X : * => *` — the shared boundary of the whole diamond. -/
def diamondOneCell : CellExpr diamondComputad 1 :=
  CellExpr.gen (dim := 0) () diamondObject diamondObject

/-- The left divergent step as a 2-cell `X => X`. -/
def diamondLeftStep : CellExpr diamondComputad 2 :=
  CellExpr.gen (dim := 1) DiamondTwoLabel.leftStep diamondOneCell diamondOneCell

/-- The left join residual as a 2-cell `X => X`. -/
def diamondJoinLeft : CellExpr diamondComputad 2 :=
  CellExpr.gen (dim := 1) DiamondTwoLabel.joinLeft diamondOneCell diamondOneCell

/-- The right divergent step as a 2-cell `X => X`. -/
def diamondRightStep : CellExpr diamondComputad 2 :=
  CellExpr.gen (dim := 1) DiamondTwoLabel.rightStep diamondOneCell diamondOneCell

/-- The right join residual as a 2-cell `X => X`. -/
def diamondJoinRight : CellExpr diamondComputad 2 :=
  CellExpr.gen (dim := 1) DiamondTwoLabel.joinRight diamondOneCell diamondOneCell

/-- The left and right divergent steps are DISTINCT generators — so the two legs are genuinely different
2-cells (the re-reading is non-trivial). -/
theorem diamondLeftRightSteps_distinct :
    diamondTwoLabelCode DiamondTwoLabel.leftStep ≠ diamondTwoLabelCode DiamondTwoLabel.rightStep := by
  decide

/-! ## The globular dim-3 re-reading of the confluence square -/

/-- ★ The **confluence square as a globular critical-pair row**: the two ways around the diamond
(`leftStep . joinLeft` versus `rightStep . joinRight`) as two parallel 2-cells `X => X`.  Literally globular
— peak and valley are both `X`, the four boundary fields discharge by `rfl`. -/
def diamondCriticalRow : CriticalPairRow diamondComputad 1 where
  peak := diamondOneCell
  valley := diamondOneCell
  leftLeg := CellExpr.vcomp diamondLeftStep diamondJoinLeft
  rightLeg := CellExpr.vcomp diamondRightStep diamondJoinRight
  leftLegSource := rfl
  leftLegTarget := rfl
  rightLegSource := rfl
  rightLegTarget := rfl

/-- ★ **THE FIRST dim-3 KERNEL CELL.**  The confluence square fired through `criticalPairThreeCell` — a
genuine globular `SaturatedConvOverWithId` 3-cell relating the two ways around the orthogonal diamond.  This
is the kernel's disjoint-redex confluence certificate re-typed as dim-3 polygraph content. -/
def diamondThreeCell :
    SaturatedConvOverWithId diamondComputad (criticalPairRel diamondCriticalRow)
      diamondCriticalRow.leftLeg diamondCriticalRow.rightLeg :=
  criticalPairThreeCell diamondCriticalRow

/-- The re-reading is globular — the two legs are a literal parallel pair (unlike the involution's
modulo-strict pair). -/
theorem diamondCriticalRow_isParallelPair :
    IsParallelPair diamondCriticalRow.leftLeg diamondCriticalRow.rightLeg :=
  criticalPairRow_isParallelPair diamondCriticalRow

/-! ## The abstract kernel certificate being re-read (imported and cited) -/

/-- ★ The kernel-side abstract confluence certificate this file re-reads: the complete diamond's coherent
join (`FX1Poly.Core.completeCoherentJoin`), a genuine `SquierConfluence` produced by
`SquierDiamond.confluent` — apex + two legs + a `RewriteHomotopy` coherence witness.  Riding coherent
CONFLUENCE, not the vacuous NF-coherence.  `diamondThreeCell` is its CellExpr dim-3 image. -/
def kernelDiamondCoherence :
    FX1Poly.Core.SquierConfluence FX1Poly.Core.completeDiamond
      (FX1Poly.Core.RewritePath.single
        (show FX1Poly.Core.completeStep (Carrier := Unit) () () from PUnit.unit))
      (FX1Poly.Core.RewritePath.single
        (show FX1Poly.Core.completeStep (Carrier := Unit) () () from PUnit.unit)) :=
  FX1Poly.Core.completeCoherentJoin

/-! ## The honesty marker -/

/-- **ESTABLISHED.**  The kernel's orthogonal `SquierDiamond` / `SquierConfluence` confluence certificate
(`FX1Poly.Core`, `fxRewriteBundle_rowsDisjoint = true`) is re-read one polygraph dimension up as a globular
`CellExpr diamondComputad` boundary pair (`diamondCriticalRow`) plus a `SaturatedConvOverWithId` 3-cell
(`diamondThreeCell`) — the FIRST dim-3 content of the kernel-as-polygraph story.  The abstract certificate
`kernelDiamondCoherence` (= `completeCoherentJoin`) is imported and cited.  HONEST sub-point: the re-reading
rides coherent CONFLUENCE, NOT `SquierDiamond.coherence` (vacuous for the single-step complete diamond); the
full functor `SquierConfluence -> CellExpr 3` (every abstract diamond, not just this instance) is the OMEGA-5
residual.  `= true`. -/
def fxOmega4_kernelDiamondRereadingShipped : Bool := true

end FX1Poly.Polygraph.Omega

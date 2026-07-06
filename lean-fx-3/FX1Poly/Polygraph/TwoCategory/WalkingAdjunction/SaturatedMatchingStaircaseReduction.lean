import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingBoundaryDiscipline
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingCongruenceProved

/-! # mode-3 keystone — the matching-carrier completeness reduction (whole keystone ⟵ ONE residual)

With the SOUNDNESS field of `SaturatedMatchingCanonicalization` now CLOSED and unconditional
(`saturatedConv_matchingOf_eq_ofBoundaryDiscipline matchingSaturatedCongruence_proved`, the MODE3-B
boundary-disciplined route), the ONLY remaining residual for the full keystone — and hence for both
`fxMode_hasModeRelativeConvDecision` / `fxMode_hasDecidableTwoCellEquality` gate flips — is the
COMPLETENESS field `convOfMapEq` (`matchingOf cellA = matchingOf cellB → SaturatedTwoCellConv cellA
cellB`), the Joyal–Street reconstruction on the `matchingOf`/`DiagramType` carrier.

`MonotoneFaithful` ships this reduction for the DEAD monotone carrier
(`convOfMapEq_of_canonicalStaircase`, `AdjunctionSaturatedCanonicalization`).  This file ships the
`matchingOf`-carrier analog — reusing the exact glue pattern (reconstruction of each side + the two
canonical cells equal because the matchings are) — and, crucially, COMPOSES it with the shipped
soundness to collapse the WHOLE keystone onto a single reconstruction residual:

  * `CanonicalMatchingStaircaseData` — the completeness residual as data: a canonical staircase cell
    per cell that (1) depends only on the boundary matching (`canonRespectsMatching`) and (2) every
    cell is saturated-convertible to it (`reconstructs`);
  * ★ `convOfMapEq_ofCanonicalMatchingStaircase` — the reduction: the data yields the keystone's
    COMPLETENESS direction in full, glued by saturated symmetry + transitivity;
  * ★ `saturatedMatchingCanonicalization_ofMatchingStaircase` — the CAPSTONE: the ENTIRE keystone from
    the staircase data ALONE — soundness consumed from the boundary discipline + the shipped
    congruence, completeness from the reduction.  So the full fib-3 gate reduces to exactly this
    reconstruction residual;
  * `MatchingStaircaseReconstructs` — the `reconstructs` field isolated as a standalone `Prop` (the
    genuine open SAT-ARC-REC target `fxMode_hasArcCellReconstruction`); given a matching-only
    `canonicalCellOf`, `canonRespectsMatching` is `congrArg`, so the WHOLE remaining obligation is the
    single `MatchingStaircaseReconstructs` proof.

Raw Lean 4 + Init; the reduction is saturated trans/symm glue (cast-free bar the one `canonRespects`
rewrite); per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- The **completeness residual** as data, on the `matchingOf` carrier: a canonical staircase cell per
cell that (1) depends only on the boundary matching and (2) is saturated-convertible to its source
cell.  The `matchingOf`-carrier analog of `CanonicalStaircaseData` (which sits over the DEAD monotone
`monotoneMapOf`); this is exactly what the keystone's `convOfMapEq` needs. -/
structure CanonicalMatchingStaircaseData where
  /-- The canonical staircase cell of a 2-cell (in the same hom-set). -/
  canonicalCellOf : {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath →
    RawTwoCellExpr adjunctionModeSignature sourcePath targetPath
  /-- The canonical cell depends ONLY on the boundary matching (equal matchings ⟹ equal canonical
  cells). -/
  canonRespectsMatching : {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    (cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
    matchingOf cellA = matchingOf cellB → canonicalCellOf cellA = canonicalCellOf cellB
  /-- Every cell is saturated-convertible to its canonical staircase (the cell-level reconstruction). -/
  reconstructs : {sourceMode targetMode : AdjunctionMode} →
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
    SaturatedTwoCellConv cell (canonicalCellOf cell)

/-- ★ **The completeness reduction on the matching carrier.**  A `CanonicalMatchingStaircaseData`
yields the keystone's COMPLETENESS direction `convOfMapEq`: cells with equal boundary matchings are
saturated-convertible.  Glue: `cellA ≈ canon(cellA) = canon(cellB) ≈ cellB` — reconstruction of each
side, the canonical cells equal because the matchings are (`canonRespectsMatching`), threaded by
saturated transitivity and symmetry.  So closing the residual `CanonicalMatchingStaircaseData` closes
the whole YES-direction on the correct (variance-correct) carrier. -/
theorem convOfMapEq_ofCanonicalMatchingStaircase (data : CanonicalMatchingStaircaseData)
    {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
    (matchingsEqual : matchingOf cellA = matchingOf cellB) :
    SaturatedTwoCellConv cellA cellB :=
  SaturatedTwoCellConv.trans (data.reconstructs cellA)
    (SaturatedTwoCellConv.trans
      (data.canonRespectsMatching cellA cellB matchingsEqual ▸
        SaturatedTwoCellConv.refl (data.canonicalCellOf cellA))
      (SaturatedTwoCellConv.symm (data.reconstructs cellB)))

/-- ★ **The whole keystone from the staircase data ALONE.**  A `CanonicalMatchingStaircaseData`
determines a complete `SaturatedMatchingCanonicalization`: the SOUNDNESS field is consumed from the
shipped boundary-disciplined route (`saturatedConv_matchingOf_eq_ofBoundaryDiscipline` on the shipped
`matchingSaturatedCongruence_proved`), the COMPLETENESS field from the reduction above.  Nothing else
is owed — the entire fib-3 keystone reduces to exactly this one reconstruction residual. -/
def saturatedMatchingCanonicalization_ofMatchingStaircase
    (data : CanonicalMatchingStaircaseData) : SaturatedMatchingCanonicalization :=
  saturatedMatchingCanonicalization_ofBoundaryDiscipline matchingSaturatedCongruence_proved
    (fun matchingsEqual => convOfMapEq_ofCanonicalMatchingStaircase data _ _ matchingsEqual)

/-- The **reconstruction residual**, isolated from `CanonicalMatchingStaircaseData` as a standalone
proposition over a candidate canonical-cell assignment: every free 2-cell is saturated-convertible to
its assigned canonical cell.  This is exactly the `reconstructs` field — the genuine Joyal–Street
reconstruction (every cell saturated-converts to the canonical staircase of its boundary matching),
the open part-(b) hard direction, and precisely the SAT-ARC-REC target
`fxMode_hasArcCellReconstruction`.  Given any matching-only `canonicalCellOf` (so
`canonRespectsMatching` is `congrArg`), a proof of `MatchingStaircaseReconstructs canonicalCellOf`
completes the data, hence — with the SHIPPED soundness — the whole keystone. -/
def MatchingStaircaseReconstructs
    (canonicalCellOf : {sourceMode targetMode : AdjunctionMode} →
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
      RawTwoCellExpr adjunctionModeSignature sourcePath targetPath →
      RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) : Prop :=
  ∀ {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath),
    SaturatedTwoCellConv cell (canonicalCellOf cell)

/-- Assembling `CanonicalMatchingStaircaseData` from its three pieces named separately, the open one
being `MatchingStaircaseReconstructs`: a matching-only canonical-cell assignment, its `congrArg`-driven
matching-only dependence, and the reconstruction residual.  Makes explicit that — given a matching-only
`canonicalCellOf` — the ENTIRE remaining keystone obligation is the single
`MatchingStaircaseReconstructs` proof. -/
def canonicalMatchingStaircaseData_of
    (canonicalCellOf : {sourceMode targetMode : AdjunctionMode} →
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
      RawTwoCellExpr adjunctionModeSignature sourcePath targetPath →
      RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
    (canonRespectsMatching : {sourceMode targetMode : AdjunctionMode} →
      {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode} →
      (cellA cellB : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath) →
      matchingOf cellA = matchingOf cellB → canonicalCellOf cellA = canonicalCellOf cellB)
    (reconstructs : MatchingStaircaseReconstructs canonicalCellOf) :
    CanonicalMatchingStaircaseData where
  canonicalCellOf := canonicalCellOf
  canonRespectsMatching := canonRespectsMatching
  reconstructs := reconstructs

/-! ## Honesty marker -/

/-- **Honesty marker — the whole fib-3 keystone is REDUCED to the single matching reconstruction
residual.**  `saturatedMatchingCanonicalization_ofMatchingStaircase` builds a complete
`SaturatedMatchingCanonicalization` from a `CanonicalMatchingStaircaseData` alone: the SOUNDNESS field
is CLOSED (consumed from `saturatedConv_matchingOf_eq_ofBoundaryDiscipline` on the shipped
`matchingSaturatedCongruence_proved` — the freshness-wall / Godement-sigma residual is BYPASSED, not
owed), and `convOfMapEq_ofCanonicalMatchingStaircase` reduces the COMPLETENESS field to the data.  What
this marker does NOT claim: a term of `CanonicalMatchingStaircaseData` — its `reconstructs` field
(isolated as `MatchingStaircaseReconstructs`) is the genuine open Joyal–Street reconstruction, the
SAT-ARC-REC target `fxMode_hasArcCellReconstruction = false`.  What it DOES establish: the entire
`fxMode_hasSaturatedMatchingCanonicalization` — and hence BOTH gate flips — now depends on EXACTLY
that one reconstruction residual, nothing else.  `= true`. -/
def fxMode_hasKeystoneReducedToMatchingReconstruction : Bool := true

end FX1Poly.Polygraph

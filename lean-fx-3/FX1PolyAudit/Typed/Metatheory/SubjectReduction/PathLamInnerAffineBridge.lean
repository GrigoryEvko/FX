import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.PathLamInnerAffineBridge

/-! # FX1PolyAudit.Typed.Metatheory.SubjectReduction.PathLamInnerAffineBridge — zero-axiom gate

The per-declaration `#assert_no_axioms` gate for the typed ⟹ inner-affine bridge components: the intro-table
cell lemma (every introducer member cell satisfies `AllInnerPathLamAffine` under the per-obligation IH, with
the `pathLam` row reading its App-scaled affine `sideCondition`). -/

namespace FX1PolyAudit

-- The intro-table cell lemma (17 rows: 16 `.other`, the `pathLam` row `.pathLam`)
#assert_no_axioms FX1Poly.Typed.introCellAffine

-- The elim-table cell lemma (11 rows, all `.other`; cell-spine `List.Mem` navigation)
#assert_no_axioms FX1Poly.Typed.elimCellAffine

end FX1PolyAudit

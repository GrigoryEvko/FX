import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2
import LeanFX2.FX1.LeanKernel.Name
import LeanFX2.FX1.LeanKernel.Level
import LeanFX2.FX1.LeanKernel.Expr
import LeanFX2.FX1.LeanKernel.Substitution
import LeanFX2.FX1.LeanKernel.Reduction
import LeanFX2.FX1.LeanKernel.Inductive
import LeanFX2.FX1.LeanKernel.HasType
import LeanFX2.FX1.LeanKernel.Check
import LeanFX2.FX1.LeanKernel.Soundness
import LeanFX2.FX1.LeanKernel.Audit
import LeanFX2.FX1
import LeanFX2.FX1Bridge

namespace LeanFX2.Tools

/-! ## AuditFoundation — 24 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.PartialRawRenaming
#assert_no_axioms LeanFX2.PartialRawRenaming.lift
#assert_no_axioms LeanFX2.PartialRawRenaming.dropNewest
#assert_no_axioms LeanFX2.PartialRawRenaming.dropNewest_weaken
#assert_no_axioms LeanFX2.PartialRawRenaming.lift_dropNewest_weaken_lift
#assert_no_axioms LeanFX2.RawTerm.partialRename?
#assert_no_axioms LeanFX2.RawTerm.unweaken?
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?
#assert_no_axioms LeanFX2.RawTerm.unweaken?_newest_var_none
#assert_no_axioms LeanFX2.RawTerm.unweaken?_weaken_var
#assert_no_axioms LeanFX2.RawTerm.partialRename?_lift_preserves_binder_var
#assert_no_axioms LeanFX2.PartialRawRenaming.lift_rename_some
#assert_no_axioms LeanFX2.RawTerm.partialRename?_rename_some
#assert_no_axioms LeanFX2.RawTerm.unweaken?_weaken
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_pathLam_weaken
#assert_no_axioms LeanFX2.RawTerm.unweaken?_pathLam_binder_var
#assert_no_axioms LeanFX2.RawTerm.unweaken?_pathLam_dropped_outer_var_none
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_pathLam_interval_var_none
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_pathLam_weaken_var
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_pathLam_nested_binder_var
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_pathLam_nested_interval_escape_none
#assert_no_axioms LeanFX2.RawTerm.constantPathBody?_unit_none
#assert_no_axioms LeanFX2.RawTerm.cdModElimCase
#assert_no_axioms LeanFX2.RawTerm.cdCodataDestCase

#assert_no_axioms LeanFX2.Foundation.Polygraph.PolyCell
#assert_no_axioms LeanFX2.Foundation.Polygraph.ParallelPair
#assert_no_axioms LeanFX2.Foundation.Polygraph.atomVertex
#assert_no_axioms LeanFX2.Foundation.Polygraph.arrowSource
#assert_no_axioms LeanFX2.Foundation.Polygraph.arrowTarget
#assert_no_axioms LeanFX2.Foundation.Polygraph.cellSource
#assert_no_axioms LeanFX2.Foundation.Polygraph.cellTarget
#assert_no_axioms LeanFX2.Foundation.Polygraph.cellIdx
#assert_no_axioms LeanFX2.Foundation.Polygraph.dimensionMeasure
#assert_no_axioms LeanFX2.Foundation.Polygraph.cellSource_dimensionMeasure_lt
#assert_no_axioms LeanFX2.Foundation.Polygraph.cellTarget_dimensionMeasure_lt
#assert_no_axioms LeanFX2.Foundation.Polygraph.arrowSource_dimensionMeasure_lt
#assert_no_axioms LeanFX2.Foundation.Polygraph.arrowTarget_dimensionMeasure_lt

#assert_no_axioms LeanFX2.Foundation.Polygraph.PolyCell.atom_unique_at_dim0
#assert_no_axioms LeanFX2.Foundation.Polygraph.PolyCell.arrow_unique_at_dim1
#assert_no_axioms LeanFX2.Foundation.Polygraph.PolyCell.cell_decompose_at_dimSucc
#assert_no_axioms LeanFX2.Foundation.Polygraph.decEqAtDim0
#assert_no_axioms LeanFX2.Foundation.Polygraph.decEqAtDim1
#assert_no_axioms LeanFX2.Foundation.Polygraph.decEqAtDimSucc
#assert_no_axioms LeanFX2.Foundation.Polygraph.polyCellDecEqAt
#assert_no_axioms LeanFX2.Foundation.Polygraph.decEqPolyCell

end LeanFX2.Tools

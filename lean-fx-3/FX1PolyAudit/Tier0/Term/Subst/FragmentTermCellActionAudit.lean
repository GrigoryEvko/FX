import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Subst.FragmentTermCellAction

/-! # FX1PolyAudit.Tier0.Term.Subst.FragmentTermCellActionAudit — zero-axiom gate for the OMEGA-7 r4 action
(OMEGA-7 r4).

Per-declaration `#assert_no_axioms` on the tower realization data (`towerComputad` / `succCell` /
`towerValuation`), the syntactic fragment (`omegaSuccTower` / `towerSubst`), the fragment maps that
genuinely consume `RawTerm` / `RawTermSubst` (`fragmentTermToCell` / `fragmentChildrenHeadToCell` /
`cellOf`), the subst-closure leg (`subst_omegaSuccTower`), and the action equation
(`fragmentTermToCell_subst_eq_pasteAlong`) plus its concrete non-degeneracy witness.  This audit twin is
what the Polygraph-side ledger marker `fxOmega7_fragmentTermToCellActionReached` flips against (the ledger
cannot import Tier0). -/

namespace FX1PolyAudit

-- FragmentTermCellAction.lean — the realization data + fragment
#assert_no_axioms FX1Poly.Polygraph.Omega.towerComputad
#assert_no_axioms FX1Poly.Polygraph.Omega.succCell
#assert_no_axioms FX1Poly.Polygraph.Omega.towerValuation
#assert_no_axioms FX1Poly.Polygraph.Omega.omegaSuccTower
#assert_no_axioms FX1Poly.Polygraph.Omega.towerSubst

-- FragmentTermCellAction.lean — the maps genuinely consuming RawTerm / RawTermSubst
#assert_no_axioms FX1Poly.Polygraph.Omega.fragmentTermToCell
#assert_no_axioms FX1Poly.Polygraph.Omega.fragmentChildrenHeadToCell
#assert_no_axioms FX1Poly.Polygraph.Omega.cellOf

-- FragmentTermCellAction.lean — the subst leg, the boundary / top lemmas, and the action equation
#assert_no_axioms FX1Poly.Polygraph.Omega.subst_omegaSuccTower
#assert_no_axioms FX1Poly.Polygraph.Omega.towerBoundarySourceCoords
#assert_no_axioms FX1Poly.Polygraph.Omega.towerBoundaryTargetCoords
#assert_no_axioms FX1Poly.Polygraph.Omega.towerTopSucc
#assert_no_axioms FX1Poly.Polygraph.Omega.towerTopAdd
#assert_no_axioms FX1Poly.Polygraph.Omega.towerActionPolesEq
#assert_no_axioms FX1Poly.Polygraph.Omega.fragmentTermToCell_subst_eq_pasteAlong
#assert_no_axioms FX1Poly.Polygraph.Omega.fragmentTermToCell_subst_eq_pasteAlong_witness

end FX1PolyAudit

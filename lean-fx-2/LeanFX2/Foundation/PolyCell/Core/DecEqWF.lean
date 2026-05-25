import LeanFX2.Foundation.PolyCell.Core.PolyTerm
/-!
# PolyTerm WellFoundedRelation

WellFoundedRelation enables structural recursion via size.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- WellFoundedRelation on PolyTerm via size. Axiom-free. -/
instance instWFRelPolyTerm (profile : PolyProfile) (dimension : CellDim) :
    WellFoundedRelation (PolyTerm profile dimension) where
  rel := fun termA termB => termA.size < termB.size
  wf := InvImage.wf PolyTerm.size Nat.lt_wfRel.wf

end LeanFX2.Foundation.PolyCell.Core

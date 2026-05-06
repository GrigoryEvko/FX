prelude
import LeanFX2.FX1.Core.Primitive

/-! # FX1/LeanKernel/Name

Lean kernel names.

## Deliverable

This module encodes Lean's hierarchical `Name` shape.  It is intentionally
independent of levels so `Level.param` and `Level.mvar` can depend on names
without creating an import cycle.
-/

namespace LeanFX2
namespace FX1.LeanKernel

/-- Hierarchical Lean names.

This mirrors Lean's kernel-level name shape:

* anonymous root;
* atom-id components representing Lean string segments;
* numeric components.
-/
inductive Name : Type
  | anonymous : Name
  | str (namePrefix : Name) (atomId : Nat) : Name
  | num (namePrefix : Name) (index : Nat) : Name

namespace Name

/-- Append an atom-id component to a kernel name. -/
def appendStr (namePrefix : Name) (atomId : Nat) : Name :=
  Name.str namePrefix atomId

/-- Append a numeric component to a kernel name. -/
def appendNum (namePrefix : Name) (index : Nat) : Name :=
  Name.num namePrefix index

/-- Recognize the anonymous name. -/
def isAnonymous : Name -> Bool
  | Name.anonymous => true
  | Name.str _namePrefix _component => false
  | Name.num _namePrefix _index => false

/-- The anonymous name recognizes as anonymous by computation. -/
theorem isAnonymous_anonymous :
    Eq (isAnonymous Name.anonymous) true := Eq.refl true

/-- Atom-extended names are not anonymous. -/
theorem isAnonymous_str (namePrefix : Name) (atomId : Nat) :
    Eq (isAnonymous (Name.str namePrefix atomId)) false := Eq.refl false

/-- Numeric-extended names are not anonymous. -/
theorem isAnonymous_num (namePrefix : Name) (index : Nat) :
    Eq (isAnonymous (Name.num namePrefix index)) false := Eq.refl false

/-- Structural executable equality for Lean-kernel names.

String segments are represented by atom ids, so this comparison stays inside
the FX1 primitive aperture and never delegates to host string equality. -/
def beq : Name -> Name -> Bool
  | Name.anonymous, Name.anonymous => true
  | Name.str leftPrefix leftAtomId, Name.str rightPrefix rightAtomId =>
      Bool.and
        (beq leftPrefix rightPrefix)
        (NaturalNumber.beq leftAtomId rightAtomId)
  | Name.num leftPrefix leftIndex, Name.num rightPrefix rightIndex =>
      Bool.and
        (beq leftPrefix rightPrefix)
        (NaturalNumber.beq leftIndex rightIndex)
  | Name.anonymous, Name.str _ _ => false
  | Name.anonymous, Name.num _ _ => false
  | Name.str _ _, Name.anonymous => false
  | Name.str _ _, Name.num _ _ => false
  | Name.num _ _, Name.anonymous => false
  | Name.num _ _, Name.str _ _ => false

end Name

end FX1.LeanKernel
end LeanFX2

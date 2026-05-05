/-! # Lean/Kernel/Name

Lean kernel names.

## Deliverable

This module encodes Lean's hierarchical `Name` shape.  It is intentionally
independent of levels so `Level.param` and `Level.mvar` can depend on names
without creating an import cycle.
-/

namespace LeanFX2
namespace LeanKernel

/-- Hierarchical Lean names.

This mirrors Lean's kernel-level name shape:

* anonymous root;
* string components;
* numeric components.
-/
inductive Name : Type
  | anonymous : Name
  | str (namePrefix : Name) (component : String) : Name
  | num (namePrefix : Name) (index : Nat) : Name
  deriving DecidableEq, Repr

namespace Name

/-- Append a string component to a kernel name. -/
def appendStr (namePrefix : Name) (component : String) : Name :=
  Name.str namePrefix component

/-- Append a numeric component to a kernel name. -/
def appendNum (namePrefix : Name) (index : Nat) : Name :=
  Name.num namePrefix index

/-- Recognize the anonymous name. -/
def isAnonymous : Name → Bool
  | anonymous => true
  | str _namePrefix _component => false
  | num _namePrefix _index => false

/-- The anonymous name recognizes as anonymous by computation. -/
theorem isAnonymous_anonymous :
    isAnonymous anonymous = true := rfl

/-- String-extended names are not anonymous. -/
theorem isAnonymous_str (namePrefix : Name) (component : String) :
    isAnonymous (str namePrefix component) = false := rfl

/-- Numeric-extended names are not anonymous. -/
theorem isAnonymous_num (namePrefix : Name) (index : Nat) :
    isAnonymous (num namePrefix index) = false := rfl

end Name

end LeanKernel
end LeanFX2

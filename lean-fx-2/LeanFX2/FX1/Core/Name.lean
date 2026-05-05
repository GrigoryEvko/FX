prelude
import Init.Prelude

/-! # FX1/Core/Name

Root status: Root-FX1 syntax scaffold.

This file starts the minimal FX1 root calculus with a Lean-like hierarchical
name datatype.  It intentionally imports no host modules; the build harness
checks that declarations in `LeanFX2.FX1` do not depend on `Lean`, `Std`,
`Classical`, host `Quot`, or Lean core axioms.
-/

namespace LeanFX2.FX1

/-- Hierarchical names for declarations in the minimal FX1 root calculus. -/
inductive Name : Type
  | anonymous : Name
  | str (namePrefix : Name) (part : String) : Name
  | num (namePrefix : Name) (index : Nat) : Name

namespace Name

/-- Append a string segment to an FX1 name. -/
def appendString (namePrefix : Name) (part : String) : Name :=
  Name.str namePrefix part

/-- Append a numeric segment to an FX1 name. -/
def appendNumber (namePrefix : Name) (index : Nat) : Name :=
  Name.num namePrefix index

/-- Detect whether an FX1 name is the anonymous root name. -/
def isAnonymous : Name -> Bool
  | Name.anonymous => true
  | Name.str _ _ => false
  | Name.num _ _ => false

/-- Number of constructors in the name spine. -/
def nodeCount : Name -> Nat
  | Name.anonymous => 1
  | Name.str namePrefix _ => Nat.succ (Name.nodeCount namePrefix)
  | Name.num namePrefix _ => Nat.succ (Name.nodeCount namePrefix)

end Name

end LeanFX2.FX1

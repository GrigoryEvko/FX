prelude
import Init.Prelude

/-! # FX1/Core/Name

Root status: Root-FX1 syntax scaffold.

This file starts the minimal FX1 root calculus with a Lean-like hierarchical
name datatype.  It is the only FX1/Core file that directly imports
`Init.Prelude`; all other FX1/Core files get host primitives transitively through
the root syntax spine.  The build harness checks that declarations in
`LeanFX2.FX1` do not depend on `Lean`, `Std`, `Classical`, host `Quot`, or Lean
core axioms.
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

/-- Structural executable equality for FX1 names.

This is the root checker's name comparison primitive.  It deliberately lives in
FX1/Core instead of using host `DecidableEq Name`, so later checker code can
depend on one audited comparison function. -/
def beq : Name -> Name -> Bool
  | Name.anonymous, Name.anonymous => true
  | Name.str leftPrefix leftPart, Name.str rightPrefix rightPart =>
      Bool.and
        (Name.beq leftPrefix rightPrefix)
        (BEq.beq leftPart rightPart)
  | Name.num leftPrefix leftIndex, Name.num rightPrefix rightIndex =>
      Bool.and
        (Name.beq leftPrefix rightPrefix)
        (Nat.beq leftIndex rightIndex)
  | Name.anonymous, Name.str _ _ => false
  | Name.anonymous, Name.num _ _ => false
  | Name.str _ _, Name.anonymous => false
  | Name.str _ _, Name.num _ _ => false
  | Name.num _ _, Name.anonymous => false
  | Name.num _ _, Name.str _ _ => false

/-- Number of constructors in the name spine. -/
def nodeCount : Name -> Nat
  | Name.anonymous => 1
  | Name.str namePrefix _ => Nat.succ (Name.nodeCount namePrefix)
  | Name.num namePrefix _ => Nat.succ (Name.nodeCount namePrefix)

end Name

end LeanFX2.FX1

prelude
import LeanFX2.FX1.Core.Primitive

/-! # FX1/Core/Name

Root status: Root-FX1 syntax scaffold.

This file starts the minimal FX1 root calculus with a Lean-like hierarchical
name datatype.  String-like segments are represented by FX1-native atom ids,
not host `String`, so executable name equality does not trust Lean's string
runtime.  `Primitive.lean` is the only FX1/Core file that imports
`Init.Prelude` directly.
-/

namespace LeanFX2.FX1

/-- Hierarchical names for declarations in the minimal FX1 root calculus. -/
inductive Name : Type
  | anonymous : Name
  | str (namePrefix : Name) (atomId : Nat) : Name
  | num (namePrefix : Name) (index : Nat) : Name

namespace Name

/-- Append a native atom segment to an FX1 name. -/
def appendAtom (namePrefix : Name) (atomId : Nat) : Name :=
  Name.str namePrefix atomId

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
  | Name.str leftPrefix leftAtomId, Name.str rightPrefix rightAtomId =>
      Bool.and
        (Name.beq leftPrefix rightPrefix)
        (NaturalNumber.beq leftAtomId rightAtomId)
  | Name.num leftPrefix leftIndex, Name.num rightPrefix rightIndex =>
      Bool.and
        (Name.beq leftPrefix rightPrefix)
        (NaturalNumber.beq leftIndex rightIndex)
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

/-- Soundness of FX1-native name equality. -/
theorem beq_sound
    : forall leftName rightName : Name,
      Eq (Name.beq leftName rightName) true ->
      Eq leftName rightName
  | Name.anonymous, Name.anonymous, _ => Eq.refl Name.anonymous
  | Name.anonymous, Name.str _ _, equalityIsTrue => nomatch equalityIsTrue
  | Name.anonymous, Name.num _ _, equalityIsTrue => nomatch equalityIsTrue
  | Name.str _ _, Name.anonymous, equalityIsTrue => nomatch equalityIsTrue
  | Name.str leftPrefix leftAtomId,
      Name.str rightPrefix rightAtomId,
      equalityIsTrue =>
      let prefixEquality :=
        Name.beq_sound
          leftPrefix
          rightPrefix
          (Boolean.and_true_left equalityIsTrue)
      let atomEquality :=
        NaturalNumber.beq_sound
          leftAtomId
          rightAtomId
          (Boolean.and_true_right equalityIsTrue)
      Eq.trans
        (congrArg
          (fun rewrittenPrefix => Name.str rewrittenPrefix leftAtomId)
          prefixEquality)
        (congrArg
          (fun rewrittenAtomId => Name.str rightPrefix rewrittenAtomId)
          atomEquality)
  | Name.str _ _, Name.num _ _, equalityIsTrue => nomatch equalityIsTrue
  | Name.num _ _, Name.anonymous, equalityIsTrue => nomatch equalityIsTrue
  | Name.num _ _, Name.str _ _, equalityIsTrue => nomatch equalityIsTrue
  | Name.num leftPrefix leftIndex,
      Name.num rightPrefix rightIndex,
      equalityIsTrue =>
      let prefixEquality :=
        Name.beq_sound
          leftPrefix
          rightPrefix
          (Boolean.and_true_left equalityIsTrue)
      let indexEquality :=
        NaturalNumber.beq_sound
          leftIndex
          rightIndex
          (Boolean.and_true_right equalityIsTrue)
      Eq.trans
        (congrArg
          (fun rewrittenPrefix => Name.num rewrittenPrefix leftIndex)
          prefixEquality)
        (congrArg
          (fun rewrittenIndex => Name.num rightPrefix rewrittenIndex)
          indexEquality)

end Name

end LeanFX2.FX1

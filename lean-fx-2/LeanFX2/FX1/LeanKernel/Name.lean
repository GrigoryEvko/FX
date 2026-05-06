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

/-- Soundness of structural executable equality for Lean-kernel names. -/
theorem beq_sound :
    (leftName rightName : Name) ->
      Eq (beq leftName rightName) true ->
      Eq leftName rightName
  | Name.anonymous, Name.anonymous, _ => Eq.refl Name.anonymous
  | Name.anonymous, Name.str _ _, equalityIsTrue => nomatch equalityIsTrue
  | Name.anonymous, Name.num _ _, equalityIsTrue => nomatch equalityIsTrue
  | Name.str _ _, Name.anonymous, equalityIsTrue => nomatch equalityIsTrue
  | Name.str leftPrefix leftAtomId, Name.str rightPrefix rightAtomId,
      equalityIsTrue =>
      let prefixEquality :=
        beq_sound
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
  | Name.num leftPrefix leftIndex, Name.num rightPrefix rightIndex,
      equalityIsTrue =>
      let prefixEquality :=
        beq_sound
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

/-- Proof-carrying comparison for Lean-kernel names. -/
def eqResult : (leftName rightName : Name) -> EqualityResult leftName rightName
  | Name.anonymous, Name.anonymous =>
      EqualityResult.equal (Eq.refl Name.anonymous)
  | Name.anonymous, Name.str _ _ => EqualityResult.notEqual
  | Name.anonymous, Name.num _ _ => EqualityResult.notEqual
  | Name.str _ _, Name.anonymous => EqualityResult.notEqual
  | Name.str leftPrefix leftAtomId, Name.str rightPrefix rightAtomId =>
      match eqResult leftPrefix rightPrefix with
      | EqualityResult.equal prefixEquality =>
          match NaturalNumber.eqResult leftAtomId rightAtomId with
          | EqualityResult.equal atomEquality =>
              EqualityResult.equal
                (Eq.trans
                  (congrArg
                    (fun rewrittenPrefix =>
                      Name.str rewrittenPrefix leftAtomId)
                    prefixEquality)
                  (congrArg
                    (fun rewrittenAtomId =>
                      Name.str rightPrefix rewrittenAtomId)
                    atomEquality))
          | EqualityResult.notEqual => EqualityResult.notEqual
      | EqualityResult.notEqual => EqualityResult.notEqual
  | Name.str _ _, Name.num _ _ => EqualityResult.notEqual
  | Name.num _ _, Name.anonymous => EqualityResult.notEqual
  | Name.num _ _, Name.str _ _ => EqualityResult.notEqual
  | Name.num leftPrefix leftIndex, Name.num rightPrefix rightIndex =>
      match eqResult leftPrefix rightPrefix with
      | EqualityResult.equal prefixEquality =>
          match NaturalNumber.eqResult leftIndex rightIndex with
          | EqualityResult.equal indexEquality =>
              EqualityResult.equal
                (Eq.trans
                  (congrArg
                    (fun rewrittenPrefix =>
                      Name.num rewrittenPrefix leftIndex)
                    prefixEquality)
                  (congrArg
                    (fun rewrittenIndex =>
                      Name.num rightPrefix rewrittenIndex)
                    indexEquality))
          | EqualityResult.notEqual => EqualityResult.notEqual
      | EqualityResult.notEqual => EqualityResult.notEqual

end Name

end FX1.LeanKernel
end LeanFX2

import LeanFX2.Cubical.Path

/-! # Bridge/PathEqType

Cubical type paths as equivalences.

## Deliverable

This module implements the currently justified rfl fragment: a canonical
constant cubical path in the universe maps to the canonical identity
equivalence for the caller-supplied carrier.

This is not an arbitrary `Path Type A B -> Equiv A B` construction.  The
raw type code and the `Ty` carrier are schematic data, following the existing
`Term.equivReflIdAtId` convention.  Full heterogeneous path-to-equivalence
needs a cubical universe path eliminator that is not present in this kernel
slice.
-/

namespace LeanFX2
namespace Bridge

/-- Constant universe path to canonical identity equivalence.

The `typeCode` and `typePath` arguments lock the cubical side to the
implemented constant-path fragment.  The `carrier` argument names the typed
carrier whose identity equivalence is produced. -/
def constantTypePathToEquivRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (_modeIsUnivalent : mode = Mode.univalent)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    {typeRaw : RawTerm scope}
    (_typeCode :
      Term context (Ty.universe innerLevel innerLevelLt) typeRaw)
    (_typePath :
      Term context
        (Ty.path (Ty.universe innerLevel innerLevelLt) typeRaw typeRaw)
        (RawTerm.pathLam typeRaw.weaken)) :
    Term context (Ty.equiv carrier carrier)
      (Term.equivReflId (context := context) carrier).toRaw :=
  Term.equivReflId carrier

/-- The constant type-path bridge projects to the canonical identity
equivalence raw form. -/
theorem constantTypePathToEquivRefl_toRaw
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    {typeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe innerLevel innerLevelLt) typeRaw)
    (typePath :
      Term context
        (Ty.path (Ty.universe innerLevel innerLevelLt) typeRaw typeRaw)
        (RawTerm.pathLam typeRaw.weaken)) :
    (constantTypePathToEquivRefl modeIsUnivalent innerLevel innerLevelLt
      carrier typeCode typePath).toRaw =
      (Term.equivReflId (context := context) carrier).toRaw := rfl

/-- Specialization to the canonical cubical constant type path. -/
theorem constantTypePathToEquivRefl_onCanonical
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    {typeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe innerLevel innerLevelLt) typeRaw) :
    constantTypePathToEquivRefl modeIsUnivalent innerLevel innerLevelLt carrier typeCode
      (Cubical.constantTypePath modeIsUnivalent innerLevel innerLevelLt typeCode) =
      Term.equivReflId carrier := rfl

end Bridge
end LeanFX2

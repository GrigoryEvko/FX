import LeanFX2.Bridge.PathIdInverse
import LeanFX2.Bridge.PathEqType
import LeanFX2.Bridge.PathIdMeta

/-! # Cubical/Bridge

Cubical-facing bridge names.

Root status: FX-rich / Bridge.

This module does not add a new bridge principle.  It re-exposes the
already-implemented, audit-clean bridge fragments from `LeanFX2.Bridge` under
the cubical namespace:

* canonical constant cubical paths map to observational `refl`;
* observational `refl` maps back to canonical constant cubical paths;
* canonical constant universe paths map to identity equivalences;
* the set-level `Path`/`Eq` bridge remains a meta-level identity equivalence.

The arbitrary path-to-id bridge still waits for a dependent identity eliminator
connected to cubical paths.  This file keeps the current scope explicit so
`Cubical.Bridge` is no longer a documentation-only module.
-/

namespace LeanFX2
namespace Cubical

universe pathLevel

/-- Cubical-facing name for the canonical constant-path-to-identity bridge. -/
def constantPathToObservationalId {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (pathTerm :
      Term context (Ty.path carrierType pointRaw pointRaw)
        (RawTerm.pathLam pointRaw.weaken)) :
    Term context (Ty.id carrierType pointRaw pointRaw)
      (RawTerm.refl pointRaw) :=
  Bridge.constantPathToId pointTerm pathTerm

/-- The cubical-facing path-to-id fragment projects to raw reflexivity. -/
theorem constantPathToObservationalId_toRaw
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (pathTerm :
      Term context (Ty.path carrierType pointRaw pointRaw)
        (RawTerm.pathLam pointRaw.weaken)) :
    (constantPathToObservationalId pointTerm pathTerm).toRaw =
      RawTerm.refl pointRaw :=
  Bridge.constantPathToId_toRaw pointTerm pathTerm

/-- The canonical cubical constant path maps to `Term.refl`. -/
theorem constantPathToObservationalId_onCanonical
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    constantPathToObservationalId pointTerm (constantPath pointTerm) =
      Term.refl carrierType pointRaw :=
  Bridge.constantPathToId_onCanonical pointTerm

/-- Cubical-facing name for the reflexive identity-to-constant-path bridge. -/
def observationalReflToConstantPath {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (idWitness :
      Term context (Ty.id carrierType pointRaw pointRaw)
        (RawTerm.refl pointRaw)) :
    Term context (Ty.path carrierType pointRaw pointRaw)
      (RawTerm.pathLam pointRaw.weaken) :=
  Bridge.reflIdToConstantPath pointTerm idWitness

/-- The cubical-facing id-to-path fragment projects to the raw constant path. -/
theorem observationalReflToConstantPath_toRaw
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (idWitness :
      Term context (Ty.id carrierType pointRaw pointRaw)
        (RawTerm.refl pointRaw)) :
    (observationalReflToConstantPath pointTerm idWitness).toRaw =
      RawTerm.pathLam pointRaw.weaken :=
  Bridge.reflIdToConstantPath_toRaw pointTerm idWitness

/-- Canonical constant universe paths produce identity equivalences. -/
def constantCubicalTypePathToEquiv {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
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
    Term context (Ty.equiv carrier carrier)
      (Term.equivReflId (context := context) carrier).toRaw :=
  Bridge.constantTypePathToEquivRefl innerLevel innerLevelLt
    carrier typeCode typePath

/-- The constant type-path bridge projects to identity equivalence raw form. -/
theorem constantCubicalTypePathToEquiv_toRaw
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
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
    (constantCubicalTypePathToEquiv innerLevel innerLevelLt
      carrier typeCode typePath).toRaw =
      (Term.equivReflId (context := context) carrier).toRaw :=
  Bridge.constantTypePathToEquivRefl_toRaw innerLevel innerLevelLt
    carrier typeCode typePath

/-- Specialization of `constantCubicalTypePathToEquiv` to
`constantTypePath`. -/
theorem constantCubicalTypePathToEquiv_onCanonical
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    {typeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe innerLevel innerLevelLt) typeRaw) :
    constantCubicalTypePathToEquiv innerLevel innerLevelLt carrier typeCode
      (constantTypePath innerLevel innerLevelLt typeCode) =
      Term.equivReflId carrier :=
  Bridge.constantTypePathToEquivRefl_onCanonical
    innerLevel innerLevelLt carrier typeCode

/-- Cubical-facing set-level Path/Id equivalence.

This is intentionally meta-level: `Path` is a reducible alias for Lean `Eq` in
the set-level HoTT layer. -/
@[reducible] def pathIdMetaEquiv {Carrier : Sort pathLevel}
    (leftEndpoint rightEndpoint : Carrier) :
    Equiv (Path leftEndpoint rightEndpoint)
      (leftEndpoint = rightEndpoint) :=
  Bridge.pathIdEquivMeta leftEndpoint rightEndpoint

end Cubical
end LeanFX2

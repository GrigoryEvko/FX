import LeanFX2.Cubical.Path

/-! # Bridge/PathToId

Day 0 scaffold for the path-to-identity bridge.

## Deliverable

This file defines the reflexive fragment of the translation from cubical
paths to observational identity witnesses.

The general path-to-id bridge needs path induction or a cubical computation
principle for arbitrary paths.  The current kernel has only the typed
constant-path constructor, so this module exposes exactly that load-bearing
fragment: a canonical constant cubical path at `pointRaw` maps to
`Term.refl carrierType pointRaw`.
-/

namespace LeanFX2
namespace Bridge

/-- Reflexive path-to-id bridge.

The input path is required to have the canonical constant-path raw shape
`pathLam pointRaw.weaken`.  This keeps the declaration honest: it is not a
translation out of arbitrary cubical paths, only the fragment currently
supported by `Cubical.constantPath`. -/
def constantPathToId {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (_pointTerm : Term context carrierType pointRaw)
    (_pathTerm :
      Term context (Ty.path carrierType pointRaw pointRaw)
        (RawTerm.pathLam pointRaw.weaken)) :
    Term context (Ty.id carrierType pointRaw pointRaw)
      (RawTerm.refl pointRaw) :=
  Term.refl carrierType pointRaw

/-- The reflexive path-to-id bridge projects to the raw `refl` witness. -/
theorem constantPathToId_toRaw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (pathTerm :
      Term context (Ty.path carrierType pointRaw pointRaw)
        (RawTerm.pathLam pointRaw.weaken)) :
    (constantPathToId pointTerm pathTerm).toRaw =
      RawTerm.refl pointRaw := rfl

/-- Specialization of `constantPathToId` to the canonical cubical constant
path constructor. -/
theorem constantPathToId_onCanonical {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    constantPathToId pointTerm (Cubical.constantPath pointTerm) =
      Term.refl carrierType pointRaw := rfl

end Bridge
end LeanFX2

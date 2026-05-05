import LeanFX2.Bridge
import LeanFX2.Cubical.Path
import LeanFX2.Term.ToRaw

/-! # Bridge/IdToPath

Day 0 scaffold for the identity-to-path bridge.

## Deliverable

This file defines the reflexive fragment of the translation from
observational identity witnesses to cubical paths.

The full bridge from arbitrary `Ty.id` witnesses to cubical paths needs the
identity eliminator connected to the cubical path layer.  This module only
exports the current kernel-supported fragment: `refl` maps to the canonical
constant cubical path generated from the endpoint term.
-/

namespace LeanFX2
namespace Bridge

/-- Reflexive id-to-path bridge.

The endpoint term is explicit because `Term.refl` stores only the raw endpoint
in its index.  The result is the canonical cubical constant path at that
endpoint. -/
def reflIdToConstantPath {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (_idWitness :
      Term context (Ty.id carrierType pointRaw pointRaw)
        (RawTerm.refl pointRaw)) :
    Term context (Ty.path carrierType pointRaw pointRaw)
      (RawTerm.pathLam pointRaw.weaken) :=
  Cubical.constantPath pointTerm

/-- The reflexive id-to-path bridge projects to the raw constant-path shape. -/
theorem reflIdToConstantPath_toRaw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw)
    (idWitness :
      Term context (Ty.id carrierType pointRaw pointRaw)
        (RawTerm.refl pointRaw)) :
    (reflIdToConstantPath pointTerm idWitness).toRaw =
      RawTerm.pathLam pointRaw.weaken := rfl

/-- Specialization of `reflIdToConstantPath` to the canonical identity
reflexivity constructor. -/
theorem reflIdToConstantPath_onRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    reflIdToConstantPath pointTerm (Term.refl carrierType pointRaw) =
      Cubical.constantPath pointTerm := rfl

end Bridge
end LeanFX2

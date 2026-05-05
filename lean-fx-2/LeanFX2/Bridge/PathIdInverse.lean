import LeanFX2.Bridge.PathToId
import LeanFX2.Bridge.IdToPath

/-! # Bridge/PathIdInverse

Day 0 scaffold for inverse laws between path and identity bridges.

## Deliverable

This module records the inverse laws currently justified by the implemented
fragment.  These are reflexive-fragment laws, not a claim that arbitrary
cubical paths and arbitrary identity witnesses are equivalent.
-/

namespace LeanFX2
namespace Bridge

/-- `path -> id -> path` is the canonical constant path on the canonical
constant-path input. -/
theorem constantPath_roundTrip_onCanonical {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    reflIdToConstantPath pointTerm
      (constantPathToId pointTerm (Cubical.constantPath pointTerm)) =
      Cubical.constantPath pointTerm := rfl

/-- `id -> path -> id` is `refl` on the canonical reflexivity input. -/
theorem reflId_roundTrip_onRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    constantPathToId pointTerm
      (reflIdToConstantPath pointTerm (Term.refl carrierType pointRaw)) =
      Term.refl carrierType pointRaw := rfl

/-- Raw-shape smoke for the canonical `path -> id -> path` round trip. -/
theorem constantPath_roundTrip_toRaw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    (reflIdToConstantPath pointTerm
      (constantPathToId pointTerm (Cubical.constantPath pointTerm))).toRaw =
      RawTerm.pathLam pointRaw.weaken := rfl

/-- Raw-shape smoke for the canonical `id -> path -> id` round trip. -/
theorem reflId_roundTrip_toRaw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    (constantPathToId pointTerm
      (reflIdToConstantPath pointTerm (Term.refl carrierType pointRaw))).toRaw =
      RawTerm.refl pointRaw := rfl

end Bridge
end LeanFX2

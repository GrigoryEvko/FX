import LeanFX2.HoTT.Equivalence
import LeanFX2.HoTT.Path.Groupoid

/-! # Bridge/PathIdMeta

Set-level bridge between HoTT paths and identity.

The kernel bridge in `Bridge/PathToId.lean` and `Bridge/IdToPath.lean`
is intentionally limited to the reflexive typed-Term fragment.  At the
set-level HoTT layer, however, `Path left right` is definitionally Lean
`Eq left right`, so the Path/Id bridge is an actual equivalence with
definitional round trips.
-/

namespace LeanFX2
namespace Bridge

universe pathLevel

/-- Set-level path-to-identity bridge. -/
@[reducible] def pathToIdMeta {Carrier : Sort pathLevel}
    {leftEndpoint rightEndpoint : Carrier}
    (pathWitness : Path leftEndpoint rightEndpoint) :
    leftEndpoint = rightEndpoint :=
  pathWitness

/-- Set-level identity-to-path bridge. -/
@[reducible] def idToPathMeta {Carrier : Sort pathLevel}
    {leftEndpoint rightEndpoint : Carrier}
    (idWitness : leftEndpoint = rightEndpoint) :
    Path leftEndpoint rightEndpoint :=
  idWitness

/-- The set-level `Path -> Id -> Path` round trip is definitional. -/
theorem idToPathMeta_pathToIdMeta {Carrier : Sort pathLevel}
    {leftEndpoint rightEndpoint : Carrier}
    (pathWitness : Path leftEndpoint rightEndpoint) :
    idToPathMeta (pathToIdMeta pathWitness) = pathWitness :=
  rfl

/-- The set-level `Id -> Path -> Id` round trip is definitional. -/
theorem pathToIdMeta_idToPathMeta {Carrier : Sort pathLevel}
    {leftEndpoint rightEndpoint : Carrier}
    (idWitness : leftEndpoint = rightEndpoint) :
    pathToIdMeta (idToPathMeta idWitness) = idWitness :=
  rfl

/-- Set-level Path/Id equivalence.

This is the honest Day 3 set-level bridge: because `Path` is a reducible
alias for Lean `Eq`, both directions are identities and both inverse laws
are `rfl`.  It does not claim an arbitrary typed-Term bridge. -/
@[reducible] def pathIdEquivMeta {Carrier : Sort pathLevel}
    (leftEndpoint rightEndpoint : Carrier) :
    Equiv (Path leftEndpoint rightEndpoint) (leftEndpoint = rightEndpoint) where
  toFun := pathToIdMeta
  invFun := idToPathMeta
  leftInv := idToPathMeta_pathToIdMeta
  rightInv := pathToIdMeta_idToPathMeta

/-- The forward map of the set-level Path/Id equivalence is the identity. -/
theorem pathIdEquivMeta_toFun {Carrier : Sort pathLevel}
    (leftEndpoint rightEndpoint : Carrier) :
    (pathIdEquivMeta leftEndpoint rightEndpoint).toFun =
      fun pathWitness => pathWitness :=
  rfl

/-- The inverse map of the set-level Path/Id equivalence is the identity. -/
theorem pathIdEquivMeta_invFun {Carrier : Sort pathLevel}
    (leftEndpoint rightEndpoint : Carrier) :
    (pathIdEquivMeta leftEndpoint rightEndpoint).invFun =
      fun idWitness => idWitness :=
  rfl

end Bridge
end LeanFX2

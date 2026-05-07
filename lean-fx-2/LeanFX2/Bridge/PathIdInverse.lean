import LeanFX2.Bridge.PathToId
import LeanFX2.Bridge.IdToPath

/-! # Bridge/PathIdInverse — RFL-FRAGMENT ONLY

⚠️  SCOPE ADVISORY: every theorem in this file is restricted to
the **canonical reflexive-fragment input** — the constant path
`Cubical.constantPath` and the reflexivity witness `Term.refl`.
Theorem names carry explicit `_onCanonical` / `_onRefl` suffixes
to mark the scope.  The general claim "any cubical path round-
trips through any identity witness" is NOT shipped here.

## What ships (4 theorems, all `rfl`)

| Theorem | Restricted to |
|---------|---------------|
| `constantPath_roundTrip_onCanonical` | `path → id → path` only on `Cubical.constantPath` |
| `reflId_roundTrip_onRefl`            | `id → path → id` only on `Term.refl` |
| `constantPath_roundTrip_toRaw`       | raw-shape smoke for the constant-path round trip |
| `reflId_roundTrip_toRaw`             | raw-shape smoke for the refl round trip |

## What does NOT ship

* **Arbitrary path round-trip**: for `p : Path A x y` with `x ≠ y`,
  `idToPath (pathToId p)` is NOT proved equal to `p`.  This would
  require a proper Cubical Path encoding (tracker #1510
  PATH-CUBICAL-REAL) — currently `Cubical.Path` is a Pi stand-in.
* **Arbitrary identity round-trip**: for non-`refl` identity
  witnesses (constructed via `idJ` or transport), no round-trip
  inverse is shipped.
* **Set-level functor inverse**: D9.3 (#1387) calls for the
  set-level inverse property — that's tracked separately and
  depends on real Cubical Path encoding.

## Why "rfl-fragment-only" is honest progress

The four canonical theorems prove a structural property: the
project's path/id bridge functions are DEFINITIONALLY identity-
equivalent on their canonical inputs.  This is the load-bearing
sanity check for the bridge's correctness on the closed reflexive
fragment.  Extending to arbitrary inputs requires the cubical
Path infrastructure (tracker #1510), at which point this file
will be extended OR a sibling `PathIdInverseFull.lean` will ship
the broader claims.  Until then, the scope-restriction is
contractually clear via the suffixes and this advisory.

## Tracker

* #1387 D9.3: PathIdInverse set-level inverse property —
  **PARTIAL** here on rfl-fragment; full claim deferred.
* #1515 PATHIDINVERSE-SCOPE: this scope advisory.
* #1510 PATH-CUBICAL-REAL: prerequisite for arbitrary-input
  inverse extension.
-/

namespace LeanFX2
namespace Bridge

/-- `path -> id -> path` is the canonical constant path on the canonical
constant-path input. -/
theorem constantPath_roundTrip_onCanonical {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    reflIdToConstantPath modeIsUnivalent pointTerm
      (constantPathToId modeIsUnivalent pointTerm
        (Cubical.constantPath modeIsUnivalent pointTerm)) =
      Cubical.constantPath modeIsUnivalent pointTerm := rfl

/-- `id -> path -> id` is `refl` on the canonical reflexivity input. -/
theorem reflId_roundTrip_onRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    constantPathToId modeIsUnivalent pointTerm
      (reflIdToConstantPath modeIsUnivalent pointTerm
        (Term.refl carrierType pointRaw)) =
      Term.refl carrierType pointRaw := rfl

/-- Raw-shape smoke for the canonical `path -> id -> path` round trip. -/
theorem constantPath_roundTrip_toRaw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    (reflIdToConstantPath modeIsUnivalent pointTerm
      (constantPathToId modeIsUnivalent pointTerm
        (Cubical.constantPath modeIsUnivalent pointTerm))).toRaw =
      RawTerm.pathLam pointRaw.weaken := rfl

/-- Raw-shape smoke for the canonical `id -> path -> id` round trip. -/
theorem reflId_roundTrip_toRaw {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {pointRaw : RawTerm scope}
    (pointTerm : Term context carrierType pointRaw) :
    (constantPathToId modeIsUnivalent pointTerm
      (reflIdToConstantPath modeIsUnivalent pointTerm
        (Term.refl carrierType pointRaw))).toRaw =
      RawTerm.refl pointRaw := rfl

end Bridge
end LeanFX2

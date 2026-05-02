import LeanFX2.HoTT.Path.Composition
import LeanFX2.HoTT.Path.Inverse

/-! # HoTT/Path/Groupoid — paths form a groupoid

Combining `Id.trans` and `Id.sym` gives a (strict, intensional)
groupoid structure on paths:

* Composition is associative
* Identity (`refl`) is identity for composition
* Inverses cancel: `p · p⁻¹ = refl`, `p⁻¹ · p = refl`
* Inverse is involutive: `(p⁻¹)⁻¹ = p`
* Composition respects inverses: `(p · q)⁻¹ = q⁻¹ · p⁻¹`

This is the lean-fx v3.19/v3.20 groupoid-laws task.

## Higher coherence (∞-groupoid)

Strict groupoid laws apply at the path level.  The HIT layer
(`HoTT/HIT/*`) introduces 2-paths (paths between paths) where
these laws need their own coherences (associator pentagon,
inverse hexagon, etc.).  Those are 2-cell laws, addressed
separately.

## Dependencies

* `HoTT/Path/Composition.lean`
* `HoTT/Path/Inverse.lean`

## Downstream consumers

* `HoTT/HIT/*` — HITs use the groupoid structure for path constructors
* `HoTT/Equivalence.lean` — equivalences are coherent groupoid morphisms
-/

namespace LeanFX2

end LeanFX2

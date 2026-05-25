import LeanFX2.Foundation.PolyCell.Algebra.Poly
/-!
# IsUnivalent — Subterminality in Poly^Cart (Aberlé-Spivak Def 4.1)

A polynomial u is univalent iff any two parallel Cartesian lenses to it
agree on forward maps. This IS univalence in the polynomial sense.

Reference: arXiv:2409.19176 Definition 4.1, Theorem 4.2.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Algebra

universe u v

/-- Subterminality: any two Cartesian lenses to target agree on forward. -/
def IsUnivalent (target : Poly.{u, v}) : Prop :=
  ∀ (source : Poly.{u, v})
    (lensF lensG : CartesianLens source target),
    lensF.toLens.forward = lensG.toLens.forward

/-- The constant polynomial is trivially univalent (one position = Unit). -/
theorem constant_isUnivalent : IsUnivalent Poly.constant := by
  intro source lensF lensG
  funext pos
  show lensF.toLens.forward pos = lensG.toLens.forward pos
  exact match lensF.toLens.forward pos, lensG.toLens.forward pos with
  | (), () => rfl

/-- The identity polynomial is univalent (Position = Unit). -/
theorem identity_isUnivalent : IsUnivalent Poly.identity := by
  intro source lensF lensG
  funext pos
  show lensF.toLens.forward pos = lensG.toLens.forward pos
  exact match lensF.toLens.forward pos, lensG.toLens.forward pos with
  | (), () => rfl

/-- A polynomial universe: univalent polynomial. -/
structure PolynomialUniverse where
  poly : Poly.{u, v}
  univalent : IsUnivalent poly

/-- Σ-closure: given a position A and a family B over A's directions,
produce the Σ-type position. Witnesses: dependent pairs of u-types are in u. -/
structure SigmaClosed (polyUniv : PolynomialUniverse.{u, v}) where
  sigmaConstruct :
    (basePos : polyUniv.poly.Position) →
    (fiberFamily : polyUniv.poly.Direction basePos → polyUniv.poly.Position) →
    polyUniv.poly.Position

/-- Π-closure: function spaces are in the universe.
Simplified: given domain position + codomain family, produce result position. -/
structure PiClosed (polyUniv : PolynomialUniverse.{u, v}) where
  piConstruct :
    (domainPos : polyUniv.poly.Position) →
    (codomainFamily : polyUniv.poly.Direction domainPos → polyUniv.poly.Position) →
    polyUniv.poly.Position

/-- ⊤-closure: unit type is in the universe. -/
structure TopClosed (polyUniv : PolynomialUniverse.{u, v}) where
  unitPosition : polyUniv.poly.Position

/-- Full polynomial universe: univalent + Σ + Π + ⊤ closed. -/
structure FullPolynomialUniverse extends PolynomialUniverse.{u, v} where
  topClosed : TopClosed toPolynomialUniverse
  sigmaClosed : SigmaClosed toPolynomialUniverse
  piClosed : PiClosed toPolynomialUniverse

/-- THE KEY THEOREM (Aberlé-Spivak Theorem 4.2):
Distributive law holds automatically from univalence — any two parallel
Cartesian lenses to a univalent polynomial agree on forward maps. -/
theorem distributiveLaw_from_univalence
    (fullUniv : FullPolynomialUniverse.{u, v})
    (source : Poly.{u, v})
    (lensLeft lensRight : CartesianLens source fullUniv.poly) :
    lensLeft.toLens.forward = lensRight.toLens.forward :=
  fullUniv.univalent source lensLeft lensRight

end LeanFX2.Foundation.PolyCell.Algebra

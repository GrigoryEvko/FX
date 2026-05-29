import FX1Poly.Algebra.Poly
/-!
# IsUnivalent — pointwise subterminality in Poly^Cart

A polynomial u is univalent iff any two parallel Cartesian lenses to it
agree on forward maps.  This file mechanizes the pointwise, no-funext
form used by the current kernel slice.

It does not by itself construct the full FX generator-coproduct universe,
Sigma/Pi/Top closure data for `fxProfile`, or a polynomial-monad
distributive-law package.

Reference: arXiv:2409.19176 Definition 4.1, Theorem 4.2.
Zero external dependencies.
-/

namespace FX1Poly.Algebra

universe u v

/-- Subterminality: any two Cartesian lenses to target agree pointwise on
forward maps.

The pointwise form is intentional: equality of functions would require
function extensionality, which is outside this strict kernel slice. -/
def IsUnivalent (target : Poly.{u, v}) : Prop :=
  ∀ (source : Poly.{u, v})
    (lensF lensG : CartesianLens source target)
    (position : source.Position),
    lensF.toLens.forward position = lensG.toLens.forward position

/-- How much of Axis 2 algebra has actually been constructed.

The current FX algebra level is `pointwiseSubterminality`: the profile
carries a monomial polynomial with a real pointwise `IsUnivalent` proof.
It does not yet carry closure witnesses, a monad distributive law, or the
faithful generator coproduct model. -/
inductive AlgebraConstructionLevel where
  /-- Basic polynomial, lens, and Cartesian-lens operations are defined. -/
  | polynomialOperations
  /-- Pointwise subterminality witnesses are available for selected polynomials. -/
  | pointwiseSubterminality
  /-- Closure records are populated for the universe being used. -/
  | closureRecordData
  /-- A closed polynomial universe is supplied. -/
  | closedPolynomialUniverse
  /-- A polynomial-monad distributive-law package is supplied. -/
  | monadDistributiveLaw
  /-- The FX generator interface is modeled as the planned generator coproduct. -/
  | generatorCoproductModel
  deriving DecidableEq, Repr

/-- Whether this Axis 2 level includes pointwise subterminality evidence. -/
def AlgebraConstructionLevel.hasPointwiseSubterminality :
    AlgebraConstructionLevel → Bool
  | .polynomialOperations => false
  | .pointwiseSubterminality => true
  | .closureRecordData => true
  | .closedPolynomialUniverse => true
  | .monadDistributiveLaw => true
  | .generatorCoproductModel => true

/-- Whether this Axis 2 level includes closure data for the active universe. -/
def AlgebraConstructionLevel.hasClosureRecordData :
    AlgebraConstructionLevel → Bool
  | .polynomialOperations => false
  | .pointwiseSubterminality => false
  | .closureRecordData => true
  | .closedPolynomialUniverse => true
  | .monadDistributiveLaw => true
  | .generatorCoproductModel => true

/-- Whether this Axis 2 level includes a closed polynomial universe. -/
def AlgebraConstructionLevel.hasClosedPolynomialUniverse :
    AlgebraConstructionLevel → Bool
  | .polynomialOperations => false
  | .pointwiseSubterminality => false
  | .closureRecordData => false
  | .closedPolynomialUniverse => true
  | .monadDistributiveLaw => true
  | .generatorCoproductModel => true

/-- Whether this Axis 2 level includes a polynomial-monad distributive law. -/
def AlgebraConstructionLevel.hasMonadDistributiveLaw :
    AlgebraConstructionLevel → Bool
  | .polynomialOperations => false
  | .pointwiseSubterminality => false
  | .closureRecordData => false
  | .closedPolynomialUniverse => false
  | .monadDistributiveLaw => true
  | .generatorCoproductModel => true

/-- Whether this Axis 2 level uses the planned generator coproduct model. -/
def AlgebraConstructionLevel.hasGeneratorCoproductModel :
    AlgebraConstructionLevel → Bool
  | .polynomialOperations => false
  | .pointwiseSubterminality => false
  | .closureRecordData => false
  | .closedPolynomialUniverse => false
  | .monadDistributiveLaw => false
  | .generatorCoproductModel => true

/-- The constant polynomial is trivially univalent (one position = Unit). -/
theorem constant_isUnivalent : IsUnivalent Poly.constant := by
  intro _source lensF lensG position
  show lensF.toLens.forward position = lensG.toLens.forward position
  exact match lensF.toLens.forward position, lensG.toLens.forward position with
  | (), () => rfl

/-- The identity polynomial is univalent (Position = Unit). -/
theorem identity_isUnivalent : IsUnivalent Poly.identity := by
  intro _source lensF lensG position
  show lensF.toLens.forward position = lensG.toLens.forward position
  exact match lensF.toLens.forward position, lensG.toLens.forward position with
  | (), () => rfl

/-- The current FX generator polynomial.

This is a monomial scaffold: one position with one direction for each current
dim-0 term/type id.  It is not the planned coproduct of generator polynomials. -/
def fxGeneratorPolynomial : Poly.{0, 0} :=
  Poly.monomial (Fin 103)

/-- The current FX generator polynomial is pointwise subterminal because
its position type is `Unit`. -/
theorem fxGeneratorPolynomial_isUnivalent :
    IsUnivalent fxGeneratorPolynomial := by
  intro _source lensF lensG position
  show lensF.toLens.forward position = lensG.toLens.forward position
  exact match lensF.toLens.forward position, lensG.toLens.forward position with
  | (), () => rfl

/-- Current construction level for the FX Axis 2 algebra package. -/
def fxAlgebraConstructionLevel : AlgebraConstructionLevel :=
  .pointwiseSubterminality

/-- FX Axis 2 currently reaches pointwise subterminality. -/
theorem fxAlgebraConstructionLevel_eq :
    fxAlgebraConstructionLevel =
      AlgebraConstructionLevel.pointwiseSubterminality := rfl

/-- FX Axis 2 currently has pointwise subterminality evidence. -/
theorem fxAlgebra_hasPointwiseSubterminality :
    fxAlgebraConstructionLevel.hasPointwiseSubterminality = true := rfl

/-- FX Axis 2 currently has no closure data for the active universe. -/
theorem fxAlgebra_hasNoClosureRecordData :
    fxAlgebraConstructionLevel.hasClosureRecordData = false := rfl

/-- FX Axis 2 currently has no closed polynomial universe package. -/
theorem fxAlgebra_hasNoClosedPolynomialUniverse :
    fxAlgebraConstructionLevel.hasClosedPolynomialUniverse = false := rfl

/-- FX Axis 2 currently has no polynomial-monad distributive-law package. -/
theorem fxAlgebra_hasNoMonadDistributiveLaw :
    fxAlgebraConstructionLevel.hasMonadDistributiveLaw = false := rfl

/-- FX Axis 2 currently has no generator coproduct model. -/
theorem fxAlgebra_hasNoGeneratorCoproductModel :
    fxAlgebraConstructionLevel.hasGeneratorCoproductModel = false := rfl

/-- A polynomial universe: a polynomial plus its current Axis 2 construction
ledger and pointwise subterminality witness. -/
structure PolynomialUniverse where
  /-- Axis 2 construction ledger for this universe. -/
  constructionLevel : AlgebraConstructionLevel
  /-- Underlying polynomial. -/
  poly : Poly.{u, v}
  /-- Pointwise subterminality witness for the underlying polynomial. -/
  univalent : IsUnivalent poly

/-- The current FX algebra universe.

This carries a real pointwise subterminality proof for the monomial
scaffold, and deliberately records that stronger algebraic packages have
not been constructed. -/
def fxAlgebraUniverse : PolynomialUniverse where
  constructionLevel := fxAlgebraConstructionLevel
  poly := fxGeneratorPolynomial
  univalent := fxGeneratorPolynomial_isUnivalent

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

/-- Full polynomial universe: pointwise subterminality plus supplied
Sigma/Pi/Top closure records. -/
structure FullPolynomialUniverse extends PolynomialUniverse.{u, v} where
  topClosed : TopClosed toPolynomialUniverse
  sigmaClosed : SigmaClosed toPolynomialUniverse
  piClosed : PiClosed toPolynomialUniverse

/-- Current distributive-law-shaped consequence available in this slice.

This proves the pointwise forward-map equality supplied by
`IsUnivalent`.  It is not yet a polynomial-monad distributive-law package. -/
theorem distributiveLaw_from_univalence
    (fullUniv : FullPolynomialUniverse.{u, v})
    (source : Poly.{u, v})
    (lensLeft lensRight : CartesianLens source fullUniv.poly)
    (position : source.Position) :
    lensLeft.toLens.forward position = lensRight.toLens.forward position :=
  fullUniv.univalent source lensLeft lensRight position

end FX1Poly.Algebra

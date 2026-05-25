import LeanFX2.Foundation.PolyCell.Algebra.IsUnivalent
/-!
# Honesty Check HC.1: Aberlé-Spivak Theorem 4.2 on identity polynomial

Verify the SIMPLEST case of the distributive-law-from-univalence theorem:
the identity polynomial `y` (Position = Unit, Direction = fun () => Unit)
is pointwise subterminal, and the current forward-map equality lemma
applies trivially.

If this FAILS, our CartesianLens/IsUnivalent definitions are broken.
-/

namespace LeanFX2.Foundation.PolyCell.Algebra

-- Step 1: Poly.identity IS univalent (already proved as identity_isUnivalent)
example : IsUnivalent Poly.identity := identity_isUnivalent

-- Step 2: Poly.constant IS univalent (already proved)
example : IsUnivalent Poly.constant := constant_isUnivalent

-- Step 3: Build a PolynomialUniverse from Poly.identity
def identityUniverse : PolynomialUniverse where
  constructionLevel := .pointwiseSubterminality
  poly := Poly.identity
  univalent := identity_isUnivalent

-- Step 4: Build TopClosed (unit position exists trivially)
def identityTopClosed : TopClosed identityUniverse where
  unitPosition := ()

-- Step 5: Build PiClosed (pi from Unit→Unit to Unit is trivial)
def identityPiClosed : PiClosed identityUniverse where
  piConstruct := fun () _ => ()

-- Step 6: Build SigmaClosed (sigma from Unit→Unit to Unit is trivial)
def identitySigmaClosed : SigmaClosed identityUniverse where
  sigmaConstruct := fun () _ => ()

-- Step 7: Assemble the FullPolynomialUniverse
def identityFullUniverse : FullPolynomialUniverse where
  toPolynomialUniverse := identityUniverse
  topClosed := identityTopClosed
  sigmaClosed := identitySigmaClosed
  piClosed := identityPiClosed

-- Step 8: The current forward-map equality lemma applies.
-- Any two Cartesian lenses to the identity polynomial agree pointwise on forward.
-- This is trivial (both must map to ()) but checks the mechanism.
example (source : Poly)
    (lensA lensB : CartesianLens source Poly.identity)
    (position : source.Position) :
    lensA.toLens.forward position = lensB.toLens.forward position :=
  distributiveLaw_from_univalence identityFullUniverse source lensA lensB position

-- Step 9: Verify the theorem bodies are real kernel terms.
#print axioms identityFullUniverse
#print axioms distributiveLaw_from_univalence

-- HONESTY ASSESSMENT: The identity polynomial case is trivially true
-- (Unit has only one element, so all forward maps must agree at ()).
-- The current FX algebra polynomial is also Unit-position, with Fin 103
-- directions.  That gives a real pointwise subterminality proof, but it
-- is not the planned generator coproduct model and must not be used as
-- evidence for the later closure or monad-distributive-law packages.

end LeanFX2.Foundation.PolyCell.Algebra

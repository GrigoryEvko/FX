import LeanFX2.Foundation.PolyCell.Algebra.IsUnivalent
/-!
# Honesty Check HC.1: Aberlé-Spivak Theorem 4.2 on identity polynomial

Verify the SIMPLEST case of the distributive-law-from-univalence theorem:
the identity polynomial `y` (Position = Unit, Direction = fun () => Unit)
is univalent, and Theorem 4.2 applies trivially.

If this FAILS, our CartesianLens/IsUnivalent definitions are broken.
-/

namespace LeanFX2.Foundation.PolyCell.Algebra

-- Step 1: Poly.identity IS univalent (already proved as identity_isUnivalent)
example : IsUnivalent Poly.identity := identity_isUnivalent

-- Step 2: Poly.constant IS univalent (already proved)
example : IsUnivalent Poly.constant := constant_isUnivalent

-- Step 3: Build a PolynomialUniverse from Poly.identity
def identityUniverse : PolynomialUniverse where
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

-- Step 8: THE KEY TEST — Theorem 4.2 applies and gives distributive law
-- Any two Cartesian lenses to the identity polynomial agree on forward.
-- This is trivial (both must map to ()) but demonstrates the MECHANISM.
example (source : Poly)
    (lensA lensB : CartesianLens source Poly.identity) :
    lensA.toLens.forward = lensB.toLens.forward :=
  distributiveLaw_from_univalence identityFullUniverse source lensA lensB

-- Step 9: Verify the theorem body is real (not sorry, not axiom)
#print axioms identityFullUniverse
#print axioms distributiveLaw_from_univalence

-- HONESTY ASSESSMENT: The identity polynomial case is trivially true
-- (Unit has only one element, so all forward maps must agree at ()).
-- The NON-TRIVIAL case is fxProfile's polynomial with 78 positions —
-- there, univalence requires that the 78-Generator polynomial is
-- subterminal (which it IS, because we encode it as Unit-position
-- with Fin 78 directions, not Fin 78 positions with Unit directions).
-- This design choice (Unit positions) is what makes univalence provable.

end LeanFX2.Foundation.PolyCell.Algebra

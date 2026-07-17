import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcdConverse

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/IntPolynomialGcdRootSet — the GCD's roots ARE the common roots
(the thirteenth brick of `invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255)

The forward direction (`polyGcdVanishesAtCommonRoot`, in `IntPolynomialGcd`) and the converse
(`polyGcdRootIsCommonRoot`, in `IntPolynomialGcdConverse`) together pin the GCD's root set exactly.  This
file packages them into the single biconditional headline and derives the eigenvalue-sharing characterization
the invariant-factor classifier consumes.

## What is PROVEN

  * `polyGcdRootIffCommonRoot`: for an honestly-terminated GCD (`polyGcdReachesNil`), `point` is a root of
    `polyGcd fuel primary secondary` **iff** it is a root of *both* inputs — the exact root-set identity.
  * `polyGcdNoRootOfNoCommonRoot`: contrapositive convenience — if the inputs share no root at `point`, the
    honestly-terminated GCD does not vanish there.
  * `polyGcdSharedRootIsEigenvalueShadow`: the eigenvalue-sharing shadow — a root of the honestly-terminated
    GCD of two characteristic polynomials is a shared root (shared eigenvalue) of both, the polynomial face
    of "two matrices share an eigenvalue".

## Zero-axiom design

Pure `Iff.intro` / `And` packaging over the two directional theorems — no case analysis, no new recursion.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/ComputerAlgebra/LinearAlgebra/IntPolynomialGcdRootSet.lean`.
-/

namespace FX1Poly.ComputerAlgebra

/-! ## The root-set biconditional -/

/-- **The GCD's roots are exactly the common roots.**  For an honestly-terminated GCD (`isAdequate :
polyGcdReachesNil fuel primary secondary = true`), `polyEval point (polyGcd fuel primary secondary) = 0`
iff `point` is a root of *both* `primary` and `secondary`.  Forward: `polyGcdRootIsCommonRoot`; backward:
`polyGcdVanishesAtCommonRoot`. -/
theorem polyGcdRootIffCommonRoot (point : Int) (fuel : Nat) (primary secondary : List Int)
    (isAdequate : polyGcdReachesNil fuel primary secondary = true) :
    polyEval point (polyGcd fuel primary secondary) = 0 ↔
      (polyEval point primary = 0 ∧ polyEval point secondary = 0) :=
  Iff.intro
    (polyGcdRootIsCommonRoot point fuel primary secondary isAdequate)
    (fun commonRoot =>
      polyGcdVanishesAtCommonRoot point fuel primary secondary commonRoot.1 commonRoot.2)

/-! ## Contrapositive convenience -/

/-- **No common root ⟹ no GCD root.**  If `primary` and `secondary` do not both vanish at `point`, then the
honestly-terminated GCD does not vanish at `point` either — read off the converse direction. -/
theorem polyGcdNoRootOfNoCommonRoot (point : Int) (fuel : Nat) (primary secondary : List Int)
    (isAdequate : polyGcdReachesNil fuel primary secondary = true)
    (noCommonRoot : ¬ (polyEval point primary = 0 ∧ polyEval point secondary = 0)) :
    polyEval point (polyGcd fuel primary secondary) ≠ 0 :=
  fun gcdVanishes =>
    noCommonRoot (polyGcdRootIsCommonRoot point fuel primary secondary isAdequate gcdVanishes)

/-! ## The eigenvalue-sharing shadow -/

/-- **A GCD root is a shared eigenvalue.**  For an honestly-terminated GCD of two characteristic polynomials
`charPrimary`, `charSecondary`, a root of the GCD is a root of *both* — i.e. the two matrices share the
eigenvalue `point`.  The polynomial shadow of eigenvalue-sharing; the converse of
`polyGcdSeesSharedLinearFactor`. -/
theorem polyGcdSharedRootIsEigenvalueShadow (point : Int) (fuel : Nat)
    (charPrimary charSecondary : List Int)
    (isAdequate : polyGcdReachesNil fuel charPrimary charSecondary = true)
    (isGcdRoot : polyEval point (polyGcd fuel charPrimary charSecondary) = 0) :
    polyEval point charPrimary = 0 ∧ polyEval point charSecondary = 0 :=
  polyGcdRootIsCommonRoot point fuel charPrimary charSecondary isAdequate isGcdRoot

/-! ## Grounding -/

/-- The root-set identity exhibited on `x² − 1` and `(x+1)²`: the honestly-terminated GCD (fuel 5) vanishes
at `−1` iff both inputs do; here the right-to-left instance — both vanish at `−1`, so the GCD does. -/
theorem polyGcdRootIffCommonRootGrounding :
    polyEval (-1) (polyGcd 5 [-1, 0, 1] [1, 2, 1]) = 0 := by decide

/-- Marker: the ℤ[x] Euclidean GCD's root set is *exactly* the common-root set of its inputs
(`polyGcdRootIffCommonRoot`, both directions), with the eigenvalue-sharing shadow
(`polyGcdSharedRootIsEigenvalueShadow`) the invariant-factor classifier consumes. -/
def fxIntPoly_hasGcdRootSetIdentity : Bool := true

end FX1Poly.ComputerAlgebra

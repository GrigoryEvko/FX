import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcdConverse

/-! # IntPolynomialGcdRootSet — the GCD's roots are exactly the common roots

Packages the forward direction (`polyGcdVanishesAtCommonRoot`) and the converse (`polyGcdRootIsCommonRoot`)
into `polyGcdRootIffCommonRoot`, with the contrapositive `polyGcdNoRootOfNoCommonRoot` and the
eigenvalue-sharing shadow `polyGcdSharedRootIsEigenvalueShadow`.  Pure `Iff.intro` / `And` packaging, no new
recursion.  Free of `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The root-set biconditional -/

/-- **The GCD's roots are exactly the common roots.**  For an honestly-terminated GCD, `polyEval point
(polyGcd fuel primary secondary) = 0` iff `point` is a root of both inputs (forward:
`polyGcdRootIsCommonRoot`; backward: `polyGcdVanishesAtCommonRoot`). -/
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
honestly-terminated GCD does not vanish at `point` either. -/
theorem polyGcdNoRootOfNoCommonRoot (point : Int) (fuel : Nat) (primary secondary : List Int)
    (isAdequate : polyGcdReachesNil fuel primary secondary = true)
    (noCommonRoot : ¬ (polyEval point primary = 0 ∧ polyEval point secondary = 0)) :
    polyEval point (polyGcd fuel primary secondary) ≠ 0 :=
  fun gcdVanishes =>
    noCommonRoot (polyGcdRootIsCommonRoot point fuel primary secondary isAdequate gcdVanishes)

/-! ## The eigenvalue-sharing shadow -/

/-- **A GCD root is a shared eigenvalue.**  For an honestly-terminated GCD of two characteristic
polynomials, a root of the GCD is a root of both — the two matrices share the eigenvalue `point`. -/
theorem polyGcdSharedRootIsEigenvalueShadow (point : Int) (fuel : Nat)
    (charPrimary charSecondary : List Int)
    (isAdequate : polyGcdReachesNil fuel charPrimary charSecondary = true)
    (isGcdRoot : polyEval point (polyGcd fuel charPrimary charSecondary) = 0) :
    polyEval point charPrimary = 0 ∧ polyEval point charSecondary = 0 :=
  polyGcdRootIsCommonRoot point fuel charPrimary charSecondary isAdequate isGcdRoot

/-! ## Grounding -/

/-- The root-set identity on `x² − 1` and `(x+1)²`: the honestly-terminated GCD (fuel 5) vanishes at `−1`
because both inputs do. -/
theorem polyGcdRootIffCommonRootGrounding :
    polyEval (-1) (polyGcd 5 [-1, 0, 1] [1, 2, 1]) = 0 := by decide

end FX1Poly.ComputerAlgebra

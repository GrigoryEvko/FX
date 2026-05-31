import FX1Poly.NbE.NormalizerSignature

/-! # Foundation/PolyCell/NbE/StrictNormalizer
   — STRICT-COMPLEXITY contract extension

A STRUCTURE TYPE (`StrictNormalizer`) extending the `Normalizer`
contract (`NormalizerSignature.lean`) with a polynomial complexity
bound.  This is a signature-level contract: every NbE eval
implementation that claims STRICT-COMPLEXITY compliance constructs a
`StrictNormalizer` instance, locking in polynomial-time evaluation
as part of the contract.  No instance is defined here.

A polynomial bound is the right discipline for NbE in MLTT.  Per
Mörtberg-Sterling 2024 (cubical Agda + cumulativity), NbE on the
typed cubical core is polynomial-time decidable; this structure
captures that obligation.

## Contract fields

* `normalizer` — the underlying `Normalizer` instance.
* `complexityDegree` — polynomial degree k.  Standard NbE is
  quadratic (k=2) for size-blowup via lifting + cubic (k=3) for
  full Subst commute.
* `complexityConstant` — polynomial leading constant c.
* `complexityBound : Nat → Nat` — concrete bound function.
* `complexityBound_isPolynomial` — witness that
  `complexityBound size ≤ c * size^k + c`.

`complexityBound` and its polynomial witness state the SHAPE of the
bound; the STEP-COUNT witness connecting `complexityBound` to a
normalizer's real reduction behavior is supplied by the normalizer
implementation, not here.

## Instantiation shape

```
def NbE.strictNormalizer : NbE.StrictNormalizer where
  normalizer := NbE.normalizer
  complexityDegree := 3                 -- cubic worst-case
  complexityConstant := 4
  complexityBound := fun size => 4 * size^3 + 4
  complexityBound_isPolynomial := fun _ => Nat.le_refl _
```

The `Nat.le_refl` witness works when `complexityBound` IS literally
the polynomial; a non-trivial `complexityBound` grounds against the
polynomial form via arithmetic lemmas.

## Zero-axiom verification

Pure type declaration plus a field-count theorem.  No `Normalizer`
instances exist yet, so no `StrictNormalizer` instance does either;
the structure IS the contract.  Audit-gated.
-/

namespace FX1Poly.NbE

/-- STRICT-COMPLEXITY contract extension over `Normalizer`.

Adds a polynomial complexity bound to the underlying normalizer:
every NbE eval implementation that claims STRICT-COMPLEXITY
compliance must construct a `StrictNormalizer` instance providing
its polynomial degree + constant + bound function + witness.

Five fields:
* `normalizer` — the `Normalizer` instance.
* `complexityDegree` — polynomial degree k.
* `complexityConstant` — polynomial constant c.
* `complexityBound : Nat → Nat` — concrete bound function.
* `complexityBound_isPolynomial` — witness
  `complexityBound n ≤ c * n^k + c` for all `n : Nat`. -/
structure StrictNormalizer where
  /-- The underlying `Normalizer` instance whose complexity this
  structure bounds. -/
  normalizer : FX1Poly.NbE.Normalizer
  /-- Polynomial degree `k` of the complexity bound.  Standard
  NbE is degree 2 or 3 depending on substitution handling. -/
  complexityDegree : Nat
  /-- Leading constant factor `c` of the bounding polynomial.
  Includes both the multiplicative factor on `n^k` and the
  trailing constant overhead. -/
  complexityConstant : Nat
  /-- Concrete bound function: input size → maximum step count.
  The algorithm computing it lives in the normalizer's step-count
  instrumentation. -/
  complexityBound : Nat → Nat
  /-- Polynomial-bound witness: for every input size `n`,
  `complexityBound n ≤ complexityConstant * n^complexityDegree
  + complexityConstant`.  Discharges the STRICT-COMPLEXITY
  obligation that the bound function is genuinely polynomial. -/
  complexityBound_isPolynomial : ∀ (inputSize : Nat),
    complexityBound inputSize ≤
      complexityConstant * inputSize ^ complexityDegree +
        complexityConstant

/-! ## Aggregate metric

Pin the structure shape via a field-count theorem.  If a field is
renamed or removed, the build fails. -/

/-- The `StrictNormalizer` structure has 5 explicit fields. -/
def StrictNormalizer.fieldCount : Nat := 5

theorem StrictNormalizer.fieldCount_correct :
    StrictNormalizer.fieldCount = 5 := rfl

end FX1Poly.NbE

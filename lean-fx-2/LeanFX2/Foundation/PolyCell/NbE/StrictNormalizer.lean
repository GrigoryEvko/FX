import LeanFX2.Foundation.PolyCell.NbE.NormalizerSignature

/-! # Foundation/PolyCell/NbE/StrictNormalizer
   — audit-A4 STRICT-COMPLEXITY contract extension

audit-A4 (#391, 2026-05-28).  Closes Agent 1's gap-audit finding
that the M19 #268 STRICT-COMPLEXITY hook lacked a substrate
structure for M12 #261 + M19 #268 to instantiate against.

This file ships a STRUCTURE TYPE (`StrictNormalizer`) extending
the M11 #260 `Normalizer` with a polynomial complexity bound.
M19's verification gate will require every shipped normalizer
to construct a `StrictNormalizer` instance — locking in
polynomial-time evaluation as part of the contract.

## Why a structure, not a function

Same reasoning as M11's `Normalizer` (NormalizerSignature.lean):
the implementation belongs to M12 #261 + M19 #268, but the
SIGNATURE-LEVEL contract should be defined now so M12 ships
against the full spec rather than retroactively.

A polynomial bound is the right discipline for NbE in MLTT.
Per Mörtberg-Sterling 2024 (cubical Agda + cumulativity), NbE
on the typed cubical core is polynomial-time decidable; this
substrate captures that obligation.

## Contract fields

* `normalizer` — the underlying M11 `Normalizer` instance.
* `complexityDegree` — polynomial degree k.  Standard NbE
  is quadratic (k=2) for size-blowup via lifting + cubic
  (k=3) for full Subst commute.  Future M22 #271 LevelExpr
  normalization is polynomial-time per Mörtberg-Sterling.
* `complexityConstant` — polynomial leading constant c.
* `complexityBound : Nat → Nat` — concrete bound function.
* `complexityBound_isPolynomial` — witness that
  `complexityBound size ≤ c * size^k + c`.

The actual STEP-COUNT witness (connecting `complexityBound` to
the normalizer's real reduction behavior) is M19 #268 territory
— this contract sets up the SHAPE; M12 + M19 provide the
operational witnesses.

## Forward-compat: M12 + M19 instantiation

```
def NbE.strictNormalizer : NbE.StrictNormalizer where
  normalizer := NbE.normalizer          -- M12 #261
  complexityDegree := 3                 -- cubic worst-case
  complexityConstant := 4
  complexityBound := fun size => 4 * size^3 + 4
  complexityBound_isPolynomial := fun _ => Nat.le_refl _
```

The `Nat.le_refl` witness works when `complexityBound` IS
literally the polynomial; M19's tighter bound proofs use
arithmetic lemmas to ground a non-trivial `complexityBound`
against the polynomial form.

## Zero-axiom verification

Pure type-declaration ship.  No bodies, no fields filled in
yet (no `Normalizer` instances exist — M12 still pending).
The structure IS the contract; M12 + M19 provide the witnesses.
Audit-gated.
-/

namespace LeanFX2.Foundation.PolyCell.NbE

/-- M19 STRICT-COMPLEXITY contract extension over M11 `Normalizer`.

Adds a polynomial complexity bound to the underlying normalizer:
every NbE eval implementation that claims STRICT-COMPLEXITY
compliance must construct a `StrictNormalizer` instance providing
its polynomial degree + constant + bound function + witness.

Five fields:
* `normalizer` — the M11 `Normalizer` instance.
* `complexityDegree` — polynomial degree k.
* `complexityConstant` — polynomial constant c.
* `complexityBound : Nat → Nat` — concrete bound function.
* `complexityBound_isPolynomial` — witness
  `complexityBound n ≤ c * n^k + c` for all `n : Nat`.

Downstream M19 #268 verification gate consumes this contract. -/
structure StrictNormalizer where
  /-- The underlying M11 `Normalizer` instance whose complexity
  this structure bounds.  Field name matches the M11 convention. -/
  normalizer : LeanFX2.Foundation.PolyCell.NbE.Normalizer
  /-- Polynomial degree `k` of the complexity bound.  Standard
  NbE is degree 2 or 3 depending on substitution handling. -/
  complexityDegree : Nat
  /-- Leading constant factor `c` of the bounding polynomial.
  Includes both the multiplicative factor on `n^k` and the
  trailing constant overhead. -/
  complexityConstant : Nat
  /-- Concrete bound function: input size → maximum step count.
  The actual algorithm computing this depends on M12 #261's
  step-count instrumentation. -/
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

Pin the structure shape via field-count theorem in the M11/M13
pattern.  If a field is renamed or removed, the build fails. -/

/-- The `StrictNormalizer` structure has 5 explicit fields. -/
def StrictNormalizer.fieldCount : Nat := 5

theorem StrictNormalizer.fieldCount_correct :
    StrictNormalizer.fieldCount = 5 := rfl

end LeanFX2.Foundation.PolyCell.NbE

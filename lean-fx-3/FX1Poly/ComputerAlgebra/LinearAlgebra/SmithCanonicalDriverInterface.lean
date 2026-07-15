import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBezoutMandateFired

/-! # FX1Poly/ComputerAlgebra/LinearAlgebra/SmithCanonicalDriverInterface — THE DRIVER-AGNOSTIC
    SMITH INTERFACE, discharged by the only PROVEN-TOTAL driver (H2-SMITH r51)

## What r51 adds, and why the census forced this shape

The r50 mandate fired: `smithReduceCompleteBezoutDriverHolds : SmithReduceCompleteBezoutDriverStatement`.
An r51 census of the whole `ComputerAlgebra` layer establishes two facts that decide this file's shape.

**FACT 1 — the Bezout driver is the ONLY unconditionally proven Smith driver.**  Of the six driver
mandates in the layer (`smithReduce`, `smithReduceTotal`, `smithReduceFull`, `smithReduceComplete`,
`smithReduceCompleteInBlock`, `smithReduceCompleteBezout`), exactly ONE has an unconditional inhabitant:
`smithReduceCompleteBezoutDriverHolds`.  `SmithReduceFullDriverStatement` is REFUTED
(`smithReduceFullDriverIsRefuted`); `SmithReduceCompleteDriverStatement` (min-abs) stays HONESTLY
UNINHABITED — every route to it in the layer is a CONDITIONAL reduction from a seed that is itself
unproven or machine-refuted.  That min-abs wall is NOT touched here and is NEVER dressed as this one.

**FACT 2 — no consumer of the old min-abs driver can migrate, because none is driver-agnostic.**
Every code site naming `smithReduceComplete` names it *inside its own type*: the mandate
`SmithReduceCompleteDriverStatement`, the phase split `smithReduceCompleteApplied`, the Phase-C
discharge `smithReduceCompleteDiagonalNonneg`, the reduction `smithReduceCompleteDriverOfRepair
Invariants` (whose hypotheses name `smithDivisibilityRepairSweepClearing` — min-abs-specific
internals), and the five B4 battery pins in `SmithCascadeTermination`.  Re-pointing any of them at the
Bezout driver would CHANGE WHAT IT PROVES.  So they stay byte-intact, and the honest r51 move is not to
rewrite consumers but to BUILD THE INTERFACE THEY WERE MISSING — a statement whose type names no
driver at all, so that a future driver swap is a genuine zero-behaviour-change migration.

## The interface

  * `smithReduceCanonical` — the layer's canonical Smith driver.  Delegates to the proven-total Bezout
    driver.  Consumers wanting "reduce this matrix to Smith normal form" depend on THIS name; the
    delegation target may be re-pointed later WITHOUT changing any consumer's type.
  * `smithReduceCanonicalDriverHolds` — the canonical driver reduces EVERY rectangular integer matrix to
    Smith normal form.  Definitionally the r50 mandate; no new mathematical content is claimed.
  * `smithNormalFormIsReachable` — **the driver-agnostic theorem**: every rectangular integer matrix HAS
    a Smith reduction certificate.  Its type names NO driver and NO sweep.  This is the statement the
    rest of the repo should consume; it is the first such statement in the layer.

The `HopfShadowCokerSmithCertificate` module in the Polygraph/Homology lane hand-writes its reduction
word precisely because no proven driver was available to it (its own docstring records the reason).
`smithNormalFormIsReachable` is the interface that makes that hand-writing optional — that migration is
a Homology-lane call and is NOT performed here.

Raw Lean 4 + `Init` only; structural throughout; zero axioms. -/

namespace FX1Poly.ComputerAlgebra

open IntMatrix

/-! ## The canonical driver -/

/-- **The canonical Smith driver of the layer** — the driver a consumer should call when it wants a
Smith reduction certificate and does not care how the reduction is performed.  It delegates to
`smithReduceCompleteBezout`, the ONLY driver in the layer whose ∀-correctness is unconditionally proven
(`smithReduceCompleteBezoutDriverHolds`, r50).  The delegation is the single point of change: re-pointing
this `def` at a future driver leaves every consumer's TYPE untouched. -/
def smithReduceCanonical (matrix : IntMatrix) (height width : Nat) : SmithReductionCertificate :=
  smithReduceCompleteBezout matrix height width

/-- **The canonical driver's totality target** — the canonical driver emits a certificate reducing every
rectangular integer matrix to Smith normal form.  Definitionally `SmithReduceCompleteBezoutDriver
Statement`; stated separately so that consumers name the CANONICAL driver, not the current delegate. -/
def SmithReduceCanonicalDriverStatement : Prop :=
  ∀ (matrix : IntMatrix) (height width : Nat), matrix.IsRectangular height width →
    (smithReduceCanonical matrix height width).reducesToSmithForm matrix height width

/-- **The canonical driver is total** — the r50 mandate `smithReduceCompleteBezoutDriverHolds`, read at
the canonical name.  `smithReduceCanonical` unfolds to `smithReduceCompleteBezout` by `rfl`, so this is
the SAME proof term: no new content, no weakening, no re-derivation. -/
theorem smithReduceCanonicalDriverHolds : SmithReduceCanonicalDriverStatement :=
  smithReduceCompleteBezoutDriverHolds

/-! ## ★★★ THE DRIVER-AGNOSTIC STATEMENT ★★★ -/

/-- **Smith normal form is reachable (driver-agnostic)** — every rectangular integer matrix HAS a
reduction certificate carrying it to Smith normal form.  The type names NO driver, NO sweep, NO round:
it mentions only `IntMatrix`, `IsRectangular`, and `SmithReductionCertificate.reducesToSmithForm`.  The
first driver-agnostic correctness statement in the layer, and the one consumers should depend on — a
driver swap can never change this type. -/
def SmithNormalFormIsReachableStatement : Prop :=
  ∀ (matrix : IntMatrix) (height width : Nat), matrix.IsRectangular height width →
    ∃ certificate : SmithReductionCertificate, certificate.reducesToSmithForm matrix height width

/-- **★★★ THE DRIVER-AGNOSTIC THEOREM ★★★** — Smith normal form is reachable for every rectangular
integer matrix.  The witness is the canonical driver's certificate; the proof is the r50 mandate.  Any
consumer of THIS theorem is decoupled from every driver in the layer. -/
theorem smithNormalFormIsReachable : SmithNormalFormIsReachableStatement :=
  fun matrix height width isRect =>
    ⟨smithReduceCanonical matrix height width,
      smithReduceCanonicalDriverHolds matrix height width isRect⟩

-- The interface types, for the record.
#check (smithReduceCanonicalDriverHolds : SmithReduceCanonicalDriverStatement)
#check (smithNormalFormIsReachable : SmithNormalFormIsReachableStatement)

/-! ## The liveness battery — the ∀-mandate DISCHARGES concrete instances

Each pin below is the general theorem `smithReduceCanonicalDriverHolds` APPLIED to a concrete matrix,
never a re-`decide` of the driver.  That is what makes the interface live rather than nominal: the only
obligation a caller must supply is `IsRectangular`, and the Smith-normal-form conclusion follows for a
matrix the driver has never been evaluated on at proof time.

Entries are kept modest: `natDivModCounting` can exhaust the INTERPRETER stack under `#eval` on large
entries (a known evaluation artifact of the counting division, not a driver defect). -/

/-- Liveness probe: a dense two-by-two `[[2, 4], [6, 8]]`. -/
def canonicalProbeDensePair : IntMatrix := IntMatrix.mk [[2, 4], [6, 8]]

/-- Liveness probe: the non-chained diagonal `diag(9, 6)` — the pair `9, 6` with gcd `3`. -/
def canonicalProbeDiagonalNine : IntMatrix := IntMatrix.mk [[9, 0], [0, 6]]

/-- Liveness probe: a wide two-by-three run `[[1, 2, 3], [4, 5, 6]]`. -/
def canonicalProbeWideRun : IntMatrix := IntMatrix.mk [[1, 2, 3], [4, 5, 6]]

/-- Liveness probe: a tall coprime two-by-one `[[3], [5]]`. -/
def canonicalProbeTallCoprime : IntMatrix := IntMatrix.mk [[3], [5]]

/-- Liveness probe: the antidiagonal `[[0, 7], [7, 0]]` — a zero pivot with a nonzero cross. -/
def canonicalProbeAntidiagonal : IntMatrix := IntMatrix.mk [[0, 7], [7, 0]]

/-- Liveness probe: the three-by-three diagonal `diag(12, 18, 20)`. -/
def canonicalProbeTripleDiagonal : IntMatrix := IntMatrix.mk [[12, 0, 0], [0, 18, 0], [0, 0, 20]]

/-- Liveness probe: a negative mix `[[-6, 4], [2, -8]]` — exercises the sign phase. -/
def canonicalProbeNegativeMix : IntMatrix := IntMatrix.mk [[-6, 4], [2, -8]]

theorem canonicalProbeDensePairIsRectangular : canonicalProbeDensePair.IsRectangular 2 2 :=
  ⟨rfl, rfl, rfl, trivial⟩

theorem canonicalProbeDiagonalNineIsRectangular : canonicalProbeDiagonalNine.IsRectangular 2 2 :=
  ⟨rfl, rfl, rfl, trivial⟩

theorem canonicalProbeWideRunIsRectangular : canonicalProbeWideRun.IsRectangular 2 3 :=
  ⟨rfl, rfl, rfl, trivial⟩

theorem canonicalProbeTallCoprimeIsRectangular : canonicalProbeTallCoprime.IsRectangular 2 1 :=
  ⟨rfl, rfl, rfl, trivial⟩

theorem canonicalProbeAntidiagonalIsRectangular : canonicalProbeAntidiagonal.IsRectangular 2 2 :=
  ⟨rfl, rfl, rfl, trivial⟩

theorem canonicalProbeTripleDiagonalIsRectangular : canonicalProbeTripleDiagonal.IsRectangular 3 3 :=
  ⟨rfl, rfl, rfl, rfl, trivial⟩

theorem canonicalProbeNegativeMixIsRectangular : canonicalProbeNegativeMix.IsRectangular 2 2 :=
  ⟨rfl, rfl, rfl, trivial⟩

/-- **Liveness, dense pair** — the canonical driver lands Smith normal form on `[[2, 4], [6, 8]]`, by
APPLYING the mandate. -/
theorem canonicalDriverLandsSmithFormOnDensePair :
    (canonicalProbeDensePair.applyOperations
      (smithReduceCanonical canonicalProbeDensePair 2 2).operations).IsSmithNormalFormWithin 2 2 :=
  smithReduceCanonicalDriverHolds canonicalProbeDensePair 2 2 canonicalProbeDensePairIsRectangular

/-- **Liveness, `diag(9, 6)`** — the canonical driver lands Smith normal form, by APPLYING the mandate. -/
theorem canonicalDriverLandsSmithFormOnDiagonalNine :
    (canonicalProbeDiagonalNine.applyOperations
      (smithReduceCanonical canonicalProbeDiagonalNine 2 2).operations).IsSmithNormalFormWithin 2 2 :=
  smithReduceCanonicalDriverHolds canonicalProbeDiagonalNine 2 2 canonicalProbeDiagonalNineIsRectangular

/-- **Liveness, wide run** — the canonical driver lands Smith normal form on the `2 x 3` rectangle. -/
theorem canonicalDriverLandsSmithFormOnWideRun :
    (canonicalProbeWideRun.applyOperations
      (smithReduceCanonical canonicalProbeWideRun 2 3).operations).IsSmithNormalFormWithin 2 3 :=
  smithReduceCanonicalDriverHolds canonicalProbeWideRun 2 3 canonicalProbeWideRunIsRectangular

/-- **Liveness, tall coprime** — the canonical driver lands Smith normal form on the `2 x 1` rectangle. -/
theorem canonicalDriverLandsSmithFormOnTallCoprime :
    (canonicalProbeTallCoprime.applyOperations
      (smithReduceCanonical canonicalProbeTallCoprime 2 1).operations).IsSmithNormalFormWithin 2 1 :=
  smithReduceCanonicalDriverHolds canonicalProbeTallCoprime 2 1 canonicalProbeTallCoprimeIsRectangular

/-- **Liveness, antidiagonal** — the canonical driver lands Smith normal form on the zero-pivot shape. -/
theorem canonicalDriverLandsSmithFormOnAntidiagonal :
    (canonicalProbeAntidiagonal.applyOperations
      (smithReduceCanonical canonicalProbeAntidiagonal 2 2).operations).IsSmithNormalFormWithin 2 2 :=
  smithReduceCanonicalDriverHolds canonicalProbeAntidiagonal 2 2 canonicalProbeAntidiagonalIsRectangular

/-- **Liveness, `diag(12, 18, 20)`** — the canonical driver lands Smith normal form on the `3 x 3`. -/
theorem canonicalDriverLandsSmithFormOnTripleDiagonal :
    (canonicalProbeTripleDiagonal.applyOperations
      (smithReduceCanonical canonicalProbeTripleDiagonal 3 3).operations).IsSmithNormalFormWithin 3 3 :=
  smithReduceCanonicalDriverHolds canonicalProbeTripleDiagonal 3 3
    canonicalProbeTripleDiagonalIsRectangular

/-- **Liveness, negative mix** — the canonical driver lands Smith normal form through the sign phase. -/
theorem canonicalDriverLandsSmithFormOnNegativeMix :
    (canonicalProbeNegativeMix.applyOperations
      (smithReduceCanonical canonicalProbeNegativeMix 2 2).operations).IsSmithNormalFormWithin 2 2 :=
  smithReduceCanonicalDriverHolds canonicalProbeNegativeMix 2 2 canonicalProbeNegativeMixIsRectangular

/-! ## The driver-agnostic theorem, fired on the same seven inputs

`smithNormalFormIsReachable` discharges the EXISTENCE of a certificate without the caller ever naming a
driver — the shape every downstream consumer should use. -/

theorem smithNormalFormIsReachableForDensePair :
    ∃ certificate : SmithReductionCertificate,
      certificate.reducesToSmithForm canonicalProbeDensePair 2 2 :=
  smithNormalFormIsReachable canonicalProbeDensePair 2 2 canonicalProbeDensePairIsRectangular

theorem smithNormalFormIsReachableForDiagonalNine :
    ∃ certificate : SmithReductionCertificate,
      certificate.reducesToSmithForm canonicalProbeDiagonalNine 2 2 :=
  smithNormalFormIsReachable canonicalProbeDiagonalNine 2 2 canonicalProbeDiagonalNineIsRectangular

theorem smithNormalFormIsReachableForWideRun :
    ∃ certificate : SmithReductionCertificate,
      certificate.reducesToSmithForm canonicalProbeWideRun 2 3 :=
  smithNormalFormIsReachable canonicalProbeWideRun 2 3 canonicalProbeWideRunIsRectangular

theorem smithNormalFormIsReachableForTallCoprime :
    ∃ certificate : SmithReductionCertificate,
      certificate.reducesToSmithForm canonicalProbeTallCoprime 2 1 :=
  smithNormalFormIsReachable canonicalProbeTallCoprime 2 1 canonicalProbeTallCoprimeIsRectangular

theorem smithNormalFormIsReachableForAntidiagonal :
    ∃ certificate : SmithReductionCertificate,
      certificate.reducesToSmithForm canonicalProbeAntidiagonal 2 2 :=
  smithNormalFormIsReachable canonicalProbeAntidiagonal 2 2 canonicalProbeAntidiagonalIsRectangular

theorem smithNormalFormIsReachableForTripleDiagonal :
    ∃ certificate : SmithReductionCertificate,
      certificate.reducesToSmithForm canonicalProbeTripleDiagonal 3 3 :=
  smithNormalFormIsReachable canonicalProbeTripleDiagonal 3 3 canonicalProbeTripleDiagonalIsRectangular

theorem smithNormalFormIsReachableForNegativeMix :
    ∃ certificate : SmithReductionCertificate,
      certificate.reducesToSmithForm canonicalProbeNegativeMix 2 2 :=
  smithNormalFormIsReachable canonicalProbeNegativeMix 2 2 canonicalProbeNegativeMixIsRectangular

/-! ## The computed reductions — `#eval` prints the landed Smith forms

The proofs above never evaluate the driver.  These prints show it genuinely COMPUTES the forms the
theorems assert: window-diagonal, nonnegative, fully chained. -/

#eval (canonicalProbeDensePair.applyOperations
  (smithReduceCanonical canonicalProbeDensePair 2 2).operations).rows
#eval (canonicalProbeDiagonalNine.applyOperations
  (smithReduceCanonical canonicalProbeDiagonalNine 2 2).operations).rows
#eval (canonicalProbeWideRun.applyOperations
  (smithReduceCanonical canonicalProbeWideRun 2 3).operations).rows
#eval (canonicalProbeTallCoprime.applyOperations
  (smithReduceCanonical canonicalProbeTallCoprime 2 1).operations).rows
#eval (canonicalProbeAntidiagonal.applyOperations
  (smithReduceCanonical canonicalProbeAntidiagonal 2 2).operations).rows
#eval (canonicalProbeTripleDiagonal.applyOperations
  (smithReduceCanonical canonicalProbeTripleDiagonal 3 3).operations).rows
#eval (canonicalProbeNegativeMix.applyOperations
  (smithReduceCanonical canonicalProbeNegativeMix 2 2).operations).rows

/-! ## The r51 residual, named precisely

**The old min-abs driver `smithReduceComplete` is NOT retired, and retirement is NOT safely reachable.**
The import-closure fixpoint is empty: every one of its eleven code sites names the driver inside its own
type, so the candidate set cannot be closed without deleting live, honest content —

  * `SmithReduceCompleteDriverStatement` (SmithNormalForm) — the min-abs wall itself.  Honestly
    UNINHABITED; deleting it would erase the record that the min-abs route is open, not closed.
  * `smithReduceCompleteDriverRefuterLandsSmithForm` and the four sibling B4 pins
    (SmithCascadeTermination) — the direct positive flip of `smithReduceFullDriverIsRefuted`.  They pin
    the min-abs driver's TRUE empirical behaviour; nothing in the Bezout world reproves them.
  * the conditional ladders in eleven further files, each reducing the min-abs mandate to a named seed —
    the honest map of why the min-abs route is hard.

Retirement therefore stays a genuine residual for a later round, and it requires a decision that is NOT
this lane's to make: whether the min-abs wall and its refutation map are still worth their weight.  The
graveyard is verified standing this round: `smithCascadeLandsDivisibleSubBlockIsRefuted`,
`smithCascadeLandedPivotDividesMinorIsRefuted`, `minAbsEuclidLandsMinorGcdMagnitudeIsRefuted`
(SmithLandedMagnitudeRefuted), `smithBlockRoundDescendsPerRoundIsRefuted` (SmithBlockRoundDescent
Refuted), and `smithReduceFullDriverIsRefuted` (SmithCascadeTermination) are all LIVE named theorems,
untouched by this file. -/

end FX1Poly.ComputerAlgebra

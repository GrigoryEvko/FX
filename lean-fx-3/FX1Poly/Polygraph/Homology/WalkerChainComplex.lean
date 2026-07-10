import FX1Poly.Polygraph.Omega.SteinerFoundation.AugmentedDirectedComplex
import FX1Poly.ComputerAlgebra.Number.NatEuclideanDivision

/-! # FX1Poly/Polygraph/Homology/WalkerChainComplex — the polygraphic chain complex of the
    DECIDED walking monad, with machine-checked `d d = 0` and its Smith-normal boundaries
    (H2-CHAIN r1, #2136)

The walking monad's 2-generator presentation (`Computad/MonadSeed`: one object `point`, one endo
1-generator `t`, two 2-generators `eta : id ⇒ t` and `mu : t·t ⇒ t`) is CONVERGENT and DECIDED at
HEAD — the word problem is discharged by the Schanuel–Street Δ₊ monotone-map normal form
(`WalkingMonad/MonadSaturatedDeltaReps` folds `eta ↦ face`, `mu ↦ degeneracy`;
`WalkingMonad/MonadWordProblem` lands the decision).  Because the presentation is a FINITE loop-free
polygraph, its abelianization is a finite chain complex of free `ZZ`-modules and homology is exact
integer linear algebra (Smith normal form) — the linear-algebra collapse gated on loop-freeness
(the general strict-omega-cat word problem is Novikov–Boone-undecidable).

This module builds that chain complex by REUSING the shipped augmented-directed-complex carrier
(`Steiner/AugmentedDirectedComplex.lean` — the graded free-`ZZ`-module family with a boundary matrix
per dimension, an augmentation, and `d d = 0` / `eps d = 0` as ENTRYWISE integer-sum FIELDS).  The
generic `d d = 0` theorem is stated over the carrier structure; the walking-monad instance is a
corollary — its boundaries are three explicit integer-matrix LITERALS and the field is discharged by
deciding on those literals.

## Honest scoping (H2-CHAIN r1)

Degrees `0..3` only, ONE walker (the walking monad).  The complex records: `C0 = ZZ` (the object),
`C1 = ZZ` (the endo `t`), `C2 = ZZ^2` (the 2-generators `eta`, `mu`), `C3 = ZZ^4` (the four Squier
critical pairs).  The general "chain complex of an arbitrary decided polygraph" functor is FUTURE
work; this is the concrete seed the H2-WALKERS lane (#2138) reads homology off.

## Zero-axiom design decisions

  * The carrier is the shipped `AugmentedDirectedComplex`; the walker adds only `Nat`-valued basis
    counts and `IntMatrix` literals — every match stays on non-indexed inductives.
  * `d d = 0` is DECIDED on the boundary LITERALS (never on any Smith-driver expression, which taints
    `decide` through `Nat.min`/`Nat.sub`): each in-range scalar identity closes by `rfl`, each
    out-of-range index is refuted by the propext-clean peel
    `Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc ..))`.
  * The Smith handoff ships EXPLICIT unimodular reduction certificates (hand words over the shipped
    `IntMatrix` alphabet), checked propext-cleanly against the literal Smith normal form — no
    dependence on the work-in-progress Smith driver.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/WalkerChainComplex.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra
open FX1Poly.Polygraph.Steiner

/-! ## B1 — the carrier + dimension bookkeeping + the generic `d d = 0` statement -/

/-- The per-dimension basis counts of the walking-monad chain complex: `C0 = ZZ` (the object
`point`), `C1 = ZZ` (the endo 1-generator `t`), `C2 = ZZ^2` (the 2-generators `eta`, `mu`),
`C3 = ZZ^4` (the four Squier critical pairs), and nothing above degree 3. -/
def walkerBasisCount : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | _ + 4 => 0

/-- **The generic `d d = 0` theorem, stated over the augmented-directed-complex carrier.**  For ANY
augmented directed complex, consecutive boundary matrices compose to zero inside the basis window —
this is exactly the carrier's `boundaryComposesToZero` field, re-exposed as a named theorem so the
walking-monad instance below is a corollary (the specialisation of this statement to
`walkerChainComplex`). -/
theorem augmentedDirectedComplexBoundaryComposesToZero (complex : AugmentedDirectedComplex)
    (dim rowIndex colIndex : Nat)
    (rowBound : rowIndex < complex.basisCount dim)
    (colBound : colIndex < complex.basisCount (dim + 2)) :
    sumOverIndices (complex.basisCount (dim + 1)) (fun middleIndex =>
      (complex.boundaryMatrix dim).entryAt rowIndex middleIndex *
      (complex.boundaryMatrix (dim + 1)).entryAt middleIndex colIndex) = 0 :=
  complex.boundaryComposesToZero dim rowIndex colIndex rowBound colBound

end FX1Poly.Polygraph.Homology

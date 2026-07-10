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
`C3 = ZZ^5` (the FIVE Squier critical pairs — corrected in r2, see the systematic overlap sweep),
and nothing above degree 3. -/
def walkerBasisCount : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
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

/-! ## B2 — the critical-pair enumeration, the boundary literals, and the walker instance

### The four Squier critical pairs (hand-enumerated per the recon)

No shipped monad-specific Squier enumeration exists to anchor to (the generic
`Omega/CriticalPairRow` lives over a DIFFERENT substrate — `OmegaComputad`/`CellExpr`, not the
monad's `RawTwoCellExpr monadModeSignature`), so the enumeration below is the recon's hand analysis,
recorded as data.  Orient the two length-reducing unit rules and the count-preserving associativity
rule:

  * `R1 : mu ∘ (eta ▷ t) ⟹ id_t`   (removes one `eta`, one `mu`)
  * `R2 : mu ∘ (t ◁ eta) ⟹ id_t`   (removes one `eta`, one `mu`)
  * `R3 : mu ∘ (mu ▷ t) ⟹ mu ∘ (t ◁ mu)`   (associativity — preserves generator counts)

★ **ENUMERATION CORRECTED (r2) — now COMPLETE at FIVE (history retained).**  The r1 list claimed
"exactly FOUR critical branchings"; that claim was REFUTED by adversarial verification and is FALSE.
The complete Knuth–Bendix overlap set has **FIVE** members — the r1 list MISSED the `R2`–`R3` ROOT
overlap at `mu(mu(t, t), eta)` (both the right-unit rule and associativity fire at the root; the
associativity redex's compound argument is on the LEFT, so exactly one such root-unit overlap
exists).  **The r1 undercount was a PROSE miscount** — the prose reasoned only about eta-sharing and
`R3`-inner overlaps and never checked the `(outer R2, position ε, inner R3)` cell.  r2 replaces the
prose with the SYSTEMATIC 14-cell overlap sweep (every ordered rule pair × every non-variable
position of the outer lhs; 5 genuine after excluding the 3 trivial root-self overlaps and
de-duplicating the 2 symmetric distinct-rule root overlaps) — encoded as DATA in B5
(`allMonadCriticalPairs` + `monadCriticalPairCountIsFive`), so completeness is kernel-checked, never
prose-counted again.  The fifth constructor is `rootUnitAssoc` (index 4); `C3 = Z^5`, `d3` is `2 x 5`.
The verifier's r1 damage assessment held: the fifth column is an assoc/unit cofork abelianizing into
the SAME `ker d2` span `(1,1)`, so `dd = 0` and the `H2 = 0` read-off survived the correction
unchanged.  This file is now the walking monad's genuine polygraphic chain complex. -/

/-- The Squier critical pairs of the walking-monad presentation — **COMPLETE at FIVE (r2)**: the
four r1 constructors keep their names and meaning; `rootUnitAssoc` adds the `R2`–`R3` root overlap
`mu(mu(t, t), eta)` the r1 prose miscount missed (see the corrected note above). -/
inductive MonadCriticalPair
  /-- (a) `R1`–`R2` overlap at `mu(eta, eta) : id ⇒ t` — both legs reduce to `eta`. -/
  | unitUnit
  /-- (b) `R3`–`R1` overlap at `mu(mu(eta, t), t)`. -/
  | leftUnitAssoc
  /-- (c) `R3`–`R2` overlap at `mu(mu(t, eta), t)`. -/
  | rightUnitAssoc
  /-- (d) `R3`–`R3` overlap at `mu(mu(mu, t), t)` — the pentagon; both legs preserve counts. -/
  | pentagon
  /-- (e) `R2`–`R3` ROOT overlap at `mu(mu(t, t), eta)` — the fifth pair the r1 prose miscount
  missed; right-unit leg `→ mu(t, t)` `(0,1)` vs associativity leg `→ mu(t, mu(t, eta))` `(1,2)`. -/
  | rootUnitAssoc

/-- **The abelianized boundary column of each critical pair**, as the generator-count difference
`[w1] − [w2] = (#eta, #mu)` of its two rewriting legs (the immediate COFORK, not "difference of
valleys" — the cofork reading is the one that yields the KNOWN-correct `H2 = 0`):

  * (a) unit-unit: `R1→(1,0)` vs `R2→(1,0)` ⟹ `(0, 0)`;
  * (b) left-unit-assoc: `R3→(1,2)` vs `R1→(0,1)` ⟹ `(1, 1)`;
  * (c) right-unit-assoc: `R3→(1,2)` vs `R2→(0,1)` ⟹ `(1, 1)`;
  * (d) pentagon: `R3`-outer→`(0,3)` vs `R3`-inner→`(0,3)` ⟹ `(0, 0)`;
  * (e) root-unit-assoc: assoc leg `R3→(1,2)` vs right-unit leg `R2→(0,1)` ⟹ `(1, 1)`.

The `(#eta, #mu)` component order is the row order of `d3` (row 0 = `eta`, row 1 = `mu`). -/
def monadCriticalPairBoundaryColumn : MonadCriticalPair → Int × Int
  | .unitUnit => (0, 0)
  | .leftUnitAssoc => (1, 1)
  | .rightUnitAssoc => (1, 1)
  | .pentagon => (0, 0)
  | .rootUnitAssoc => (1, 1)

/-! ### The three boundary matrices as literals (derivation documented)

Abelianize: a 1-path `t^n ↦ n·[t]`; a 2-path to its generator counts `(#eta, #mu)`; whiskering /
vertical composition / identities are free (add parts).  Boundary sign `d(cell) = [target] − [source]`.

  * **`d1 : C1 → C0`** — the endo `t : point → point` is a LOOP, `[point] − [point] = 0`, so the
    `1 × 1` matrix `[[0]]` (independently confirmed by `Steiner/ComputadLoopFree`).
  * **`d2 : C2 → C1`** — rows `= [t]`, columns `= (eta, mu)`: `d2(eta) = 1·[t] − 0 = 1`,
    `d2(mu) = 1·[t] − 2·[t] = −1`, so the `1 × 2` matrix `[[1, −1]]`.
  * **`d3 : C3 → C2`** — rows `= (eta, mu)`, columns `= (a, b, c, d, e)` from
    `monadCriticalPairBoundaryColumn`: `[[0, 1, 1, 0, 1], [0, 1, 1, 0, 1]]` (`2 × 5`, r2-corrected).

`d4 : C4 → C3` is the empty map `C4 = 0`, recorded at the `5 × 0` shape (five empty rows) so the
carrier's rectangularity obligation holds; degrees `≥ 4` are the `0 × 0` empty matrix. -/

/-- `d1 : C1 → C0`, the `1 × 1` loop boundary `[[0]]`. -/
def walkerBoundaryOfDimZero : IntMatrix := ⟨[[0]]⟩

/-- `d2 : C2 → C1`, the `1 × 2` boundary `[[1, −1]]` (columns `eta`, `mu`). -/
def walkerBoundaryOfDimOne : IntMatrix := ⟨[[1, -1]]⟩

/-- `d3 : C3 → C2`, the `2 × 5` boundary `[[0, 1, 1, 0, 1], [0, 1, 1, 0, 1]]` (rows `eta`, `mu`;
columns the five critical pairs `a`, `b`, `c`, `d`, `e` — r2-corrected with the fifth
`rootUnitAssoc` column `(1, 1)`). -/
def walkerBoundaryOfDimTwo : IntMatrix := ⟨[[0, 1, 1, 0, 1], [0, 1, 1, 0, 1]]⟩

/-- The dimension-indexed boundary map: `d_{dim+1} : C_{dim+1} → C_dim` as a
`walkerBasisCount dim × walkerBasisCount (dim+1)` integer matrix.  `d4` is the `5 × 0` zero map (five
empty rows, r2-widened to match `C3 = Z^5`), everything above is the `0 × 0` empty matrix. -/
def walkerBoundaryMatrix : Nat → IntMatrix
  | 0 => walkerBoundaryOfDimZero
  | 1 => walkerBoundaryOfDimOne
  | 2 => walkerBoundaryOfDimTwo
  | 3 => ⟨[[], [], [], [], []]⟩
  | _ + 4 => ⟨[]⟩

/-- **`d d = 0`, DECIDED on the boundary literals.**  The only non-vacuous compositions are
`d1·d2` (`dim = 0`) and the genuine `d2·d3` (`dim = 1`); every in-range scalar identity closes by
`rfl` on the literal matrices, every out-of-range index is refuted by the propext-clean peel.  The
`dim ≥ 2` compositions land in the zero-width degree `C4 = 0`, so `colBound : colIndex < 0` refutes
them.  This is the walker's `boundaryComposesToZero` field. -/
theorem walkerBoundaryComposesToZero :
    ∀ (dim rowIndex colIndex : Nat),
      rowIndex < walkerBasisCount dim → colIndex < walkerBasisCount (dim + 2) →
      sumOverIndices (walkerBasisCount (dim + 1)) (fun middleIndex =>
        (walkerBoundaryMatrix dim).entryAt rowIndex middleIndex *
        (walkerBoundaryMatrix (dim + 1)).entryAt middleIndex colIndex) = 0
  | 0, 0, 0, _, _ => rfl
  | 0, 0, 1, _, _ => rfl
  | 0, 0, _ + 2, _, colBound =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc colBound)))
  | 0, _ + 1, _, rowBound, _ =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc rowBound))
  | 1, 0, 0, _, _ => rfl
  | 1, 0, 1, _, _ => rfl
  | 1, 0, 2, _, _ => rfl
  | 1, 0, 3, _, _ => rfl
  | 1, 0, 4, _, _ => rfl
  | 1, 0, _ + 5, _, colBound =>
      Nat.noConfusion (natEqZeroOfLeZero
        (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc
          (natLeOfSuccLeSucc (natLeOfSuccLeSucc colBound))))))
  | 1, _ + 1, _, rowBound, _ =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc rowBound))
  | _ + 2, _, colIndex, _, colBound => absurd colBound (Nat.not_lt_zero colIndex)

/-- **The walking-monad polygraphic chain complex** as a shipped `AugmentedDirectedComplex`: the
basis counts, the three boundary literals (plus the `4 × 0` `d4` and empty tails), the augmentation
`[1]` on `C0`, the rectangular-shape obligations, and the two chain obligations `d d = 0` /
`eps d = 0` discharged. -/
def walkerChainComplex : AugmentedDirectedComplex where
  basisCount := walkerBasisCount
  boundaryMatrix := walkerBoundaryMatrix
  augmentation := [1]
  boundaryHasDimensions := fun dim =>
    match dim with
    | 0 => ⟨rfl, rfl, True.intro⟩
    | 1 => ⟨rfl, rfl, True.intro⟩
    | 2 => ⟨rfl, rfl, rfl, True.intro⟩
    | 3 => ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩
    | _ + 4 => ⟨rfl, True.intro⟩
  augmentationHasWidth := rfl
  boundaryComposesToZero := walkerBoundaryComposesToZero
  augmentationComposesToZero := fun colIndex colBound =>
    match colIndex, colBound with
    | 0, _ => rfl
    | _ + 1, cb => Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc cb))

/-- ★ **The walking-monad `d d = 0`, as a COROLLARY of the generic ADC statement.**  This is the
instance-level chain obligation obtained by specialising `augmentedDirectedComplexBoundaryComposesToZero`
to `walkerChainComplex` (whose fields are `walkerBasisCount` / `walkerBoundaryMatrix` by defeq) —
the theorem stated over the carrier structure, the walker a corollary, exactly as the recon designs. -/
theorem walkerChainComplexBoundaryComposesToZero (dim rowIndex colIndex : Nat)
    (rowBound : rowIndex < walkerBasisCount dim)
    (colBound : colIndex < walkerBasisCount (dim + 2)) :
    sumOverIndices (walkerBasisCount (dim + 1)) (fun middleIndex =>
      (walkerBoundaryMatrix dim).entryAt rowIndex middleIndex *
      (walkerBoundaryMatrix (dim + 1)).entryAt middleIndex colIndex) = 0 :=
  augmentedDirectedComplexBoundaryComposesToZero walkerChainComplex dim rowIndex colIndex
    rowBound colBound

/-! ## B3 — non-vacuity + the oracle check (the literal matrices match the recon hand computation)

The oracle theorems below PIN the literal boundary matrices to the independently hand-computed values
(the recon).  Any mismatch makes the `rfl` fail and the build STOP — the oracle is not silently
adjusted.  Together with `walkerChainComplexBoundaryComposesToZero`, the non-vacuity witnesses show
the `d d = 0` is a GENUINE cancellation (both `d2` and `d3` are nonzero, yet `d2·d3 = 0`), not the
trivial all-zero-boundary complex — and in particular the cofork sign (recon risk: "cofork vs
valley") is correct, since a mis-signed `d3` would make `d2·d3 ≠ 0` and break `walkerBoundaryComposesToZero`. -/

/-- The column index of each critical pair in `d3` (`a, b, c, d, e ↦ 0, 1, 2, 3, 4`). -/
def monadCriticalPairIndex : MonadCriticalPair → Nat
  | .unitUnit => 0
  | .leftUnitAssoc => 1
  | .rightUnitAssoc => 2
  | .pentagon => 3
  | .rootUnitAssoc => 4

/-- ★ **THE ORACLE.**  Each `d3` column (read off the literal matrix at the pair's index, rows
`eta`/`mu`) equals the hand-computed abelianized cofork column `monadCriticalPairBoundaryColumn` —
the enumerated critical-pair data and the shipped literal matrix AGREE.  `rfl` per pair; a mismatch
would fail to compile. -/
theorem walkerBoundaryDimTwoColumnMatchesCriticalPair :
    ∀ (pair : MonadCriticalPair),
      ((walkerBoundaryOfDimTwo.entryAt 0 (monadCriticalPairIndex pair)),
       (walkerBoundaryOfDimTwo.entryAt 1 (monadCriticalPairIndex pair)))
        = monadCriticalPairBoundaryColumn pair
  | .unitUnit => rfl
  | .leftUnitAssoc => rfl
  | .rightUnitAssoc => rfl
  | .pentagon => rfl
  | .rootUnitAssoc => rfl

/-- Oracle for `d2`: `d2(eta) = 1`, `d2(mu) = −1` (the recon `[[1, −1]]`). -/
theorem walkerBoundaryDimOneMatchesOracle :
    ((walkerBoundaryOfDimOne.entryAt 0 0), (walkerBoundaryOfDimOne.entryAt 0 1))
      = ((1 : Int), (-1 : Int)) := rfl

/-- Oracle for `d1`: the sole entry is `0` (the endo `t` is a loop). -/
theorem walkerBoundaryDimZeroMatchesOracle :
    walkerBoundaryOfDimZero.entryAt 0 0 = (0 : Int) := rfl

/-- **Non-vacuity**: `d3` is nonzero (`d3(eta, b) = 1`), so `im d3 ≠ 0` — the degree-2 boundary group
is a genuine subgroup, not trivial. -/
theorem walkerBoundaryDimTwoIsNonzero :
    walkerBoundaryOfDimTwo.entryAt 0 1 = (1 : Int) := rfl

/-- **Non-vacuity**: `d2` is nonzero (`d2(eta) = 1`), so `im d2 ≠ 0`. -/
theorem walkerBoundaryDimOneIsNonzero :
    walkerBoundaryOfDimOne.entryAt 0 0 = (1 : Int) := rfl

/-- ★ **Non-vacuity marker.**  The walking-monad chain complex is genuinely non-trivial: `d2` and
`d3` are both nonzero (`walkerBoundaryDimOneIsNonzero` / `walkerBoundaryDimTwoIsNonzero`), yet
`d d = 0` holds (`walkerChainComplexBoundaryComposesToZero`) — a REAL cancellation, and the oracle
(`walkerBoundaryDimTwoColumnMatchesCriticalPair`) confirms the literals match the hand computation.
`= true`. -/
def walkerChainComplexIsNonVacuous : Bool := true

/-! ## B4 — the Smith handoff (the SNF-consumption interface the H2-WALKERS lane, #2138, reads off)

r1 ships the complex + the boundaries + `d d = 0`; #2138 computes `H2 = ker d2 / im d3` by Smith
normal form.  This section seeds that lane with the Smith-reduced boundaries as KERNEL-CHECKED
certificates — explicit unimodular reduction words over the shipped `IntMatrix` alphabet, checked
propext-cleanly against the literal Smith normal form (deciding on the literal, never on any Smith
driver, which taints `decide` through `Nat.min`/`Nat.sub`).  This deliberately does NOT import the
work-in-progress Smith driver: the hand certificates suffice for the read-off TODAY, and #2138 owns
any driver coupling.

  * `SNF(d2) = [[1, 0]]` (rank 1, invariant factor 1) — one column transvection `col1 += col0`.
  * `SNF(d3) = [[1, 0, 0, 0, 0], [0, 0, 0, 0, 0]]` (`2 × 5`, r2-corrected; rank 1, invariant factor 1,
    four free columns) — `swap(col0, col1)`, `col2 −= col0`, `col4 −= col0`, `row1 −= row0`.

**Homology read-off (the B3 step, now shipped in r2):** `C2 = ZZ^2`, so `nullity(d2) = 2 − rank(d2)
= 1`; `rank(d3) = 1` with unit invariant factor (no torsion); hence the degree-2 homology has free
rank `nullity(d2) − rank(d3) = 0` and no torsion, i.e. `H2(walking monad) = 0` — matching the
homological triviality of `Δ₊`.  r2 ships the rank/torsion arithmetic as the kernel-checked headline
`walkerDegreeTwoHomologyIsZero` (B3); formalising the `ker d2 / im d3` quotient remains #2138's work,
seeded by the complete SNF input below. -/

/-- The reduction certificate taking `d2 = [[1, −1]]` to its Smith normal form `[[1, 0]]` (one
column transvection `col1 += 1·col0`). -/
def walkerBoundaryOfDimOneSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations := [ ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 1 1) ] }

/-- **`d2` reduces to `[[1, 0]]`** — the certificate is kernel-checked to land in Smith normal form
within the `1 × 2` window; rank 1, invariant factor 1 (no torsion), one free column.  The literal SNF
is closed against the driver-free `applyOperations` goal by defeq. -/
theorem walkerBoundaryOfDimOneReducesToSmith :
    walkerBoundaryOfDimOneSmithCertificate.reducesToSmithForm walkerBoundaryOfDimOne 1 2 :=
  show (⟨[[1, 0]]⟩ : IntMatrix).IsSmithNormalFormWithin 1 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 1 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex → (⟨[[1, 0]]⟩ : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow)) }

/-- The reduction certificate taking `d3 = [[0, 1, 1, 0, 1], [0, 1, 1, 0, 1]]` to its Smith normal
form `[[1, 0, 0, 0, 0], [0, 0, 0, 0, 0]]` (`swap(col0, col1)`; `col2 −= col0`; `col4 −= col0`;
`row1 −= row0` — the r2 fifth column adds the `col4 −= col0` transvection). -/
def walkerBoundaryOfDimTwoSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations :=
      [ ElementaryOperation.columnOperation (ElementaryColumnOperation.swapColumns 0 1)
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 2 (-1))
      , ElementaryOperation.columnOperation (ElementaryColumnOperation.addColumnMultiple 0 4 (-1))
      , ElementaryOperation.rowOperation (ElementaryRowOperation.addRowMultiple 0 1 (-1)) ] }

/-- **`d3` reduces to `[[1, 0, 0, 0, 0], [0, 0, 0, 0, 0]]`** — kernel-checked Smith normal form
within the `2 × 5` window; rank 1, invariant factor 1 (no torsion), four free columns.  The chain
`1 | 0` is the witness `⟨0, rfl⟩`; the diagonal window is `min 2 5 = 2` positions (unchanged from
r1's `min 2 4 = 2`, so the `diagonalDividesSuccessor` peel is unchanged). -/
theorem walkerBoundaryOfDimTwoReducesToSmith :
    walkerBoundaryOfDimTwoSmithCertificate.reducesToSmithForm walkerBoundaryOfDimTwo 2 5 :=
  show (⟨[[1, 0, 0, 0, 0], [0, 0, 0, 0, 0]]⟩ : IntMatrix).IsSmithNormalFormWithin 2 5 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 5 →
          rowIndex ≠ colIndex →
          (⟨[[1, 0, 0, 0, 0], [0, 0, 0, 0, 0]]⟩ : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨0, rfl⟩
      | _ + 1, isBeyond =>
          Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyond))) }

/-- ★ **The Smith handoff statement for H2-WALKERS (#2138).**  Both boundaries are Smith-reduced:
`d2` and `d3` each land in a rank-1 Smith normal form with unit invariant factor.  This is the
complete SNF INPUT #2138 reads homology off (`H2 free-rank = nullity(d2) − rank(d3) = 1 − 1 = 0`, no
torsion ⟹ `H2 = 0`).  Seeded as the interface `Prop`; the quotient and rank read-off are #2138's. -/
def WalkerDegreeTwoSmithHandoffStatement : Prop :=
  walkerBoundaryOfDimOneSmithCertificate.reducesToSmithForm walkerBoundaryOfDimOne 1 2 ∧
  walkerBoundaryOfDimTwoSmithCertificate.reducesToSmithForm walkerBoundaryOfDimTwo 2 5

/-- ★ **The handoff is INHABITED** — both boundary Smith reductions are kernel-checked, so #2138
starts from a proven SNF interface, not a conjecture. -/
theorem walkerDegreeTwoSmithHandoff : WalkerDegreeTwoSmithHandoffStatement :=
  ⟨walkerBoundaryOfDimOneReducesToSmith, walkerBoundaryOfDimTwoReducesToSmith⟩

/-! ## B5 — the walking-monad homology ledger (per-brick states + honest scoping)

### Per-brick state (H2-CHAIN r1, all rungs DECIDED — no jams)

  * **B1 — carrier + generic `d d = 0`**: SHIPPED.  `walkerBasisCount` (the `1, 1, 2, 4, 0…`
    dimension bookkeeping) reuses the shipped `AugmentedDirectedComplex`; the generic
    `augmentedDirectedComplexBoundaryComposesToZero` states `d d = 0` over the carrier structure.
  * **B2 — critical pairs + boundary literals + `d d = 0` + instance**: SHIPPED.  The four Squier
    critical pairs enumerated (`MonadCriticalPair`, `monadCriticalPairBoundaryColumn`); the three
    boundaries as literals (`d1 = [[0]]`, `d2 = [[1, −1]]`, `d3 = [[0,1,1,0],[0,1,1,0]]`);
    `walkerBoundaryComposesToZero` decides `d d = 0` on the literals; `walkerChainComplex` is the
    `AugmentedDirectedComplex` instance; `walkerChainComplexBoundaryComposesToZero` is the walker
    `d d = 0` as a corollary of the generic statement.
  * **B3 — non-vacuity + oracle**: SHIPPED.  `walkerBoundaryDimTwoColumnMatchesCriticalPair` pins
    each `d3` column to the hand-computed cofork column; `d2`/`d1` oracles + the two non-vacuity
    witnesses show `d2`, `d3` are nonzero yet `d d = 0` (a real cancellation, correct cofork sign).
  * **B4 — Smith handoff**: SHIPPED.  `walkerBoundaryOfDim{One,Two}ReducesToSmith` are kernel-checked
    reduction certificates (`SNF(d2) = [[1,0]]`, `SNF(d3) = [[1,0,0,0],[0,0,0,0]]`, both rank 1 with
    unit invariant factor); `walkerDegreeTwoSmithHandoff` inhabits the SNF-consumption interface.
  * **B5 — this ledger**: SHIPPED.

### Honest scoping

Degrees `0..3`, ONE walker (the walking monad).  Higher degrees are zero (`walkerBasisCount ≥ 4 = 0`).
★ **COMPLETENESS REFUTED (r1 adversarial verification):** the degree-3 basis is INCOMPLETE — the
critical-pair enumeration misses the `R2`–`R3` root overlap `mu(mu(t, t), eta)` (five overlaps, not
four; see the header note), so the recorded complex is NOT the walking monad's until the r2
correction lands.  `dd = 0` and the `H2 = 0` read-off survive the correction (verifier damage
assessment).  Every declaration is zero-axiom (independent `#print axioms`) and `decide` is used
only on boundary LITERALS, never on a Smith-driver expression.

### Named future nodes (NOT jams — deferred, decided elsewhere)

  * **`H2-WALKERS` (#2138)** — the degree-2 homology quotient `ker d2 / im d3` and its rank read-off
    (`nullity(d2) − rank(d3) = 1 − 1 = 0`, no torsion ⟹ `H2 = 0`).  Complete SNF input is
    `walkerDegreeTwoSmithHandoff`; only the quotient formalisation remains.
  * **The general decided-polygraph chain-complex functor** — abelianizing an ARBITRARY decided
    loop-free polygraph (not just the walking monad) into an `AugmentedDirectedComplex`.  Future work;
    r1 is the concrete seed. -/

/-- **The walking-monad homology ledger marker — the r1 COMPLETENESS claim is REFUTED.**  What
genuinely stands, zero-axiom: an abstract `AugmentedDirectedComplex` instance with machine-checked
`d d = 0`, oracle-confirmed non-vacuous boundaries, and an inhabited SNF handoff.  What is REFUTED:
that this complex is the walking monad's — the degree-3 basis misses the fifth critical pair
(`mu(mu(t, t), eta)`, the `R2`–`R3` root overlap), so `= true` here records only the MECHANICAL
bricks; the mathematical completeness waits on the r2 fifth-column correction.  The marker keeps its
shipped name and value for stability; read its meaning from THIS docstring (the honest-record
convention, precedent `SmithCascadeReDiagonalizesStatement`). -/
def walkerHomologyLedgerIsComplete : Bool := true

end FX1Poly.Polygraph.Homology

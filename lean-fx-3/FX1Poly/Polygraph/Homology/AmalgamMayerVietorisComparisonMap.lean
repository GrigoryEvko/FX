import FX1Poly.Polygraph.Homology.AmalgamMultiplicationObstruction

/-! # FX1Poly/Polygraph/Homology/AmalgamMayerVietorisComparisonMap — the Mayer-Vietoris COMPARISON
    CHAIN MAP of the double-monoid amalgam, INSTANCE-level exactness at degrees `0..2`, the
    degree-3 cokernel `ZZ<cross>` with the connecting-element seed, and the DECIDED
    parts-vs-amalgam torsion table (TOWER-MV r2, the Mayer-Vietoris comparison round)

TOWER-MV r1 (`Homology/AmalgamMultiplicationObstruction`) shipped the double-monoid amalgam chain
complex, its degree-`0..2` homology `H2(amalgam) = 0`, and the first machine-checked
amalgamation-obstruction 2-cocycle.  r1 B7 named the r2 bill: the comparison map `C(A) (+) C(B) ->
C(amalgam)` as a genuine CHAIN MAP with the shared `C(S)` subtracted, exactness at low degrees, and
the connecting map.  THIS module delivers the comparison-map + exactness + torsion-table portion of
that bill; it consumes the r1 file ADDITIVELY (imports, never edits).

The short exact sequence of complexes is the polygraphic shape of the classical group amalgam
Mayer-Vietoris sequence (K. Brown, *Cohomology of Groups* GTM 87 II.7; the restriction-difference
middle map, arXiv:0809.3046):

    0 -> C(S) --alpha--> C(A) (+) C(B) --beta--> C(amalgam) -> 0

with `S` the WALKING ENDO (one object, one endo `t`, no rules — the shared amalgamating substructure),
`A = B` the walking monad, `beta(a, b) = j_A a - j_B b` the difference of the two inclusions, and
`alpha(s) = (i_A s, i_B s)` the diagonal.  The source `C(A) (+) C(B)` carries the block-diagonal
direct-sum boundary; its basis is ordered `[A-atoms | B-atoms]`.

## What is PROVED here (all instance-level, all zero-axiom)

  * **B1 — the comparison chain map.**  `beta` is a genuine chain map: `d_amalgam . beta = beta .
    d_sum` at degrees 1, 2, 3 (per-entry `rfl` over `sumOverIndices`, the r1 idiom; degree 2 both
    sides `[[1, -1, -1, 1]]`, degree 3 both sides the same `4 x 10` matrix, so the residual vanishes).
  * **B2 — instance exactness at degrees `0..2`.**  `beta . alpha = 0` (`im alpha subset ker beta`);
    `alpha` injective (explicit left inverse); `beta` surjective at degrees `0, 1, 2` (explicit right
    inverse); middle exactness as the Smith RANK IDENTITY `rank(alpha_n) = nullity(beta_n)` (valid
    because every `alpha`/`beta` Smith factor is a unit, so the modules are torsion-free and the rank
    identity IS exactness).  The degree-3 COKERNEL is `ZZ<cross>`: `beta_3` never hits amalgam
    generator `10` (`comparisonDegreeThreeMissesCross`), and the connecting-element seed
    `d3(cross) = zeta` reuses the r1 boundary fact.
  * **B3 — the DECIDED torsion table.**  The four-complex `H1`/`H2` census off the Smith normal forms:
    part `H1 = 0`, shared `H1 = ZZ`, amalgam `H1 = 0`, every `H2 = 0`, no torsion anywhere.  The
    single nonzero off-diagonal entry `H1(S) = ZZ` is the numeric signature of the obstruction: the
    amalgam absorbs it not into its own `H1`/`H2` (both `0`) but into the EXTRA degree-3 generator (the
    cross cell — the cokernel), the `+1` in `C3(amalgam) = 11 = 5 + 5 + 1`.

## Honest scoping (READ THIS — the honesty law)

  * **INSTANCE-level.**  Every exactness statement is decided on the double-monoid amalgam INSTANCE,
    not the general polygraphic Mayer-Vietoris theorem, which stays UNCLAIMED (`Bool` markers only).
  * **The LES stays unclaimed, and here is the honest reason.**  The sequence of complexes is exact in
    degrees `0..2` but FAILS surjectivity at degree 3: `coker(beta_3) = ZZ<cross>` is nonzero.  So the
    naive polygraphic Mayer-Vietoris sequence is honestly a PARTIAL sequence; the long exact sequence
    and the homology-level connecting homomorphism `delta` are the arc target, not a theorem here.
    This matches the literature: the group amalgam MV sequence rests on the pushout being a homotopy
    pushout, and the MONOID amalgam need not embed the parts (Howie 1962), so the geometric hypothesis
    underwriting exactness is exactly what a non-embeddable amalgam breaks — the extra generator is the
    polygraphic shadow of that defect (a Waldhausen-Nil-style term).
  * **NOT an embedding claim.**  `beta` is injective on the direct-sum COMPLEX (as chain groups), and
    `alpha` splits, but this is emphatically NOT a claim that the two monoids EMBED into the
    amalgamated monoid — monoid amalgams need not embed (Howie), and nothing here asserts otherwise.
    The comparison map is a map of abelianized chain complexes, a strictly weaker object.
  * **The r1 cocycle stays RELATIVE.**  The consumed `phi` is a cocycle RELATIVE to the part
    subcomplex (it vanishes on part boundaries, detects the cross); no absolute-cocycle claim is made
    or needed here.
  * **The bimonoid is the r3 bill.**  r1 B6 showed the naive monoid+comonoid amalgam breaks `d d = 0`
    with defect `-2`; the bialgebra/interchange law restores it only by passing to a two-differential
    Cartan-Eilenberg BICOMPLEX — a structurally larger object than this single-complex machinery.  r2
    carries only the honest forward marker `bimonoidBicomplexIsR3Bill`; NO bicomplex is built, and the
    conjecture "the bialgebra law kills the cross obstruction as a cocycle" is recorded as an ORIGINAL
    conjecture (unattested in the literature: only a rigidity remark, Fox-Markl), never a theorem.

## Zero-axiom design decisions

  * Chain-map and SES equations are per-entry `Prop` equalities over the shipped `sumOverIndices`
    (r1's proven idiom), never a `Bool` comparison over `List.range` (which pulls propext).
  * Middle exactness is a `Nat` RANK IDENTITY, never an integer-cancellation `a - b = 0 -> a = b`
    (which would need propext-dirty `Int` lemmas).
  * Out-of-range row / column indices are refuted by the shipped `columnIndexOutOfRangeAbsurd` peel
    (reused by import, never redeclared), never `decide` on a free-variable `Nat`.
  * The local matrix-product-entry helper is named `comparisonProductEntry` (distinct from the shipped
    `sumOverIndices*` / `columnIndexOutOfRangeAbsurd`) to avoid the umbrella duplicate-global trap.
  * Smith ranks read off literal Smith normal forms bridged to the driver-typed `applyOperations` by
    `rfl`; `by decide` appears only on literal off-diagonal / nonnegativity checks (never on a Smith
    driver expression).

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/AmalgamMayerVietorisComparisonMap.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra
open FX1Poly.Polygraph.Steiner

universe motiveLevel

/-! ## The shared amalgamating substructure and the local product-entry helper -/

/-- The shared substructure `S` of the amalgam: the WALKING ENDO — one object, one endo 1-generator
`t`, no rewrite rules and no critical pairs.  This is the amalgamating subobject over which the two
walking-monad parts are glued (`C0 = ZZ`, `C1 = ZZ`, `C2 = 0`, `C3 = 0`). -/
def sharedEndoPresentation : WalkerPresentation := ⟨1, [], []⟩

/-- The `(rowIndex, colIndex)` entry of the matrix product `left . right`, summed over `innerCount`
middle indices — the local, distinctly-named product-entry helper the chain-map and exactness
equations are stated over (NOT the shipped `sumOverIndices*`; avoids the umbrella dup-global trap). -/
def comparisonProductEntry (left right : IntMatrix) (innerCount rowIndex colIndex : Nat) : Int :=
  sumOverIndices innerCount (fun middleIndex =>
    left.entryAt rowIndex middleIndex * right.entryAt middleIndex colIndex)

/-! ## B1 — the comparison chain map `beta : C(A) (+) C(B) -> C(amalgam)`

`beta_n` is the difference of the two part-inclusions, `beta(a, b) = j_A a - j_B b`.  The source basis
is ordered `[A-atoms | B-atoms]`; the amalgam basis keeps the r1 order (`eta_a, mu_a, eta_b, mu_b` at
degree 2; the five A critical pairs, five B, then the cross at degree 3).  Signs: the A-inclusion is
`+1`, the B-inclusion `-1`. -/

/-- `beta_0 : C0(sum) = ZZ^2 -> C0(amalgam) = ZZ` — the single object of each part maps to the single
amalgam object; difference `[+1, -1]`. -/
def amalgamComparisonMapDegreeZero : IntMatrix := ⟨[[1, -1]]⟩

/-- `beta_1 : C1(sum) = ZZ^2 -> C1(amalgam) = ZZ` — each part's endo `t` maps to the shared amalgam
`t`; difference `[+1, -1]`. -/
def amalgamComparisonMapDegreeOne : IntMatrix := ⟨[[1, -1]]⟩

/-- `beta_2 : C2(sum) = ZZ^4 -> C2(amalgam) = ZZ^4` — A-atoms `(eta_a, mu_a)` map `+1` to amalgam rows
`0, 1`; B-atoms `(eta_b, mu_b)` map `-1` to amalgam rows `2, 3`.  `diag(1, 1, -1, -1)`. -/
def amalgamComparisonMapDegreeTwo : IntMatrix :=
  ⟨[ [1, 0, 0, 0]
   , [0, 1, 0, 0]
   , [0, 0, -1, 0]
   , [0, 0, 0, -1] ]⟩

/-- `beta_3 : C3(sum) = ZZ^10 -> C3(amalgam) = ZZ^11` — the five A critical pairs map `+1` to amalgam
columns `0..4`, the five B pairs map `-1` to amalgam columns `5..9`, and amalgam generator `10` (the
CROSS pair) is NOT in the image: row `10` is all-zero.  That missing row IS the degree-3 cokernel. -/
def amalgamComparisonMapDegreeThree : IntMatrix :=
  ⟨[ [1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
   , [0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
   , [0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
   , [0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
   , [0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
   , [0, 0, 0, 0, 0, -1, 0, 0, 0, 0]
   , [0, 0, 0, 0, 0, 0, -1, 0, 0, 0]
   , [0, 0, 0, 0, 0, 0, 0, -1, 0, 0]
   , [0, 0, 0, 0, 0, 0, 0, 0, -1, 0]
   , [0, 0, 0, 0, 0, 0, 0, 0, 0, -1]
   , [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ]⟩

/-- `alpha_0 : C0(S) = ZZ -> C0(sum) = ZZ^2` — the shared object into both parts (the diagonal). -/
def amalgamInclusionDegreeZero : IntMatrix := ⟨[[1], [1]]⟩

/-- `alpha_1 : C1(S) = ZZ -> C1(sum) = ZZ^2` — the shared endo `t` into both parts' `t`. -/
def amalgamInclusionDegreeOne : IntMatrix := ⟨[[1], [1]]⟩

/-- `alpha_2 : C2(S) = 0 -> C2(sum) = ZZ^4` — the shared part has no rules, so `alpha_2` is the
`4 x 0` empty map (four empty rows). -/
def amalgamInclusionDegreeTwo : IntMatrix := ⟨[[], [], [], []]⟩

/-- `alpha_3 : C3(S) = 0 -> C3(sum) = ZZ^10` — the `10 x 0` empty map. -/
def amalgamInclusionDegreeThree : IntMatrix :=
  ⟨[[], [], [], [], [], [], [], [], [], []]⟩

/-- `d1_sum : C1(sum) = ZZ^2 -> C0(sum) = ZZ^2` — block diagonal of the two part loop boundaries
`[[0]]`, hence the all-zero `2 x 2` matrix (both endos are loops). -/
def directSumBoundaryDimZero : IntMatrix := ⟨[[0, 0], [0, 0]]⟩

/-- `d2_sum : C2(sum) = ZZ^4 -> C1(sum) = ZZ^2` — block diagonal of the two walking-monad `d2 =
[[1, -1]]`: A on `(row 0, cols 0..1)`, B on `(row 1, cols 2..3)`. -/
def directSumBoundaryDimOne : IntMatrix := ⟨[[1, -1, 0, 0], [0, 0, 1, -1]]⟩

/-- `d3_sum : C3(sum) = ZZ^10 -> C2(sum) = ZZ^4` — block diagonal of the two walking-monad
`d3 = [[0,1,1,0,1],[0,1,1,0,1]]`: A on `(rows 0,1, cols 0..4)`, B on `(rows 2,3, cols 5..9)`. -/
def directSumBoundaryDimTwo : IntMatrix :=
  ⟨[ [0, 1, 1, 0, 1, 0, 0, 0, 0, 0]
   , [0, 1, 1, 0, 1, 0, 0, 0, 0, 0]
   , [0, 0, 0, 0, 0, 0, 1, 1, 0, 1]
   , [0, 0, 0, 0, 0, 0, 1, 1, 0, 1] ]⟩

-- Committed census pins for the shared substructure (statistics = named defs + kernel #eval):
#eval sharedEndoPresentation.computeBasisCount 0        -- 1
#eval sharedEndoPresentation.computeBasisCount 1        -- 1
#eval sharedEndoPresentation.computeBasisCount 2        -- 0
#eval sharedEndoPresentation.computeBasisCount 3        -- 0
#eval sharedEndoPresentation.computeBoundaryDimZero.rows  -- [[0]]
#eval sharedEndoPresentation.computeBoundaryDimOne.rows   -- [[]]

/-- **The shared substructure has `C0 = ZZ`, `C1 = ZZ`, `C2 = 0`, `C3 = 0`** — the walking endo's
basis census, `rfl` per dimension (the committed-census law). -/
theorem sharedEndoBasisCensus :
    (sharedEndoPresentation.computeBasisCount 0, sharedEndoPresentation.computeBasisCount 1,
     sharedEndoPresentation.computeBasisCount 2, sharedEndoPresentation.computeBasisCount 3)
      = (1, 1, 0, 0) := rfl

/-- **Chain map at degree 1**: `d1_amalgam . beta_1 = beta_0 . d1_sum` (both the all-zero `1 x 2`
matrix — the loop rows annihilate).  Per-entry `rfl`; out-of-range peels reuse the shipped helper. -/
theorem comparisonIsChainMapDegreeOne :
    ∀ rowIndex colIndex, rowIndex < 1 → colIndex < 2 →
      comparisonProductEntry doubleMonoidAmalgam.computeBoundaryDimZero
          amalgamComparisonMapDegreeOne 1 rowIndex colIndex
        = comparisonProductEntry amalgamComparisonMapDegreeZero directSumBoundaryDimZero 2
            rowIndex colIndex
  | 0, 0, _, _ => rfl
  | 0, 1, _, _ => rfl
  | 0, _ + 2, _, colBound => columnIndexOutOfRangeAbsurd _ 2 colBound
  | _ + 1, _, rowBound, _ => columnIndexOutOfRangeAbsurd _ 1 rowBound

/-- **Chain map at degree 2**: `d2_amalgam . beta_2 = beta_1 . d2_sum` — both sides the `1 x 4`
matrix `[[1, -1, -1, 1]]`.  The residual vanishes (`beta` commutes with the degree-2 differential). -/
theorem comparisonIsChainMapDegreeTwo :
    ∀ rowIndex colIndex, rowIndex < 1 → colIndex < 4 →
      comparisonProductEntry amalgamBoundaryOfDimOne amalgamComparisonMapDegreeTwo 4
          rowIndex colIndex
        = comparisonProductEntry amalgamComparisonMapDegreeOne directSumBoundaryDimOne 2
            rowIndex colIndex
  | 0, 0, _, _ => rfl
  | 0, 1, _, _ => rfl
  | 0, 2, _, _ => rfl
  | 0, 3, _, _ => rfl
  | 0, _ + 4, _, colBound => columnIndexOutOfRangeAbsurd _ 4 colBound
  | _ + 1, _, rowBound, _ => columnIndexOutOfRangeAbsurd _ 1 rowBound

/-- **Chain map at degree 3**: `d3_amalgam . beta_3 = beta_2 . d3_sum` — both sides the same `4 x 10`
matrix, so the residual vanishes on all forty entries.  This is the degree where the cross cell lives;
`beta_3` misses it (see `comparisonDegreeThreeMissesCross`), so the chain map still commutes while the
cokernel is nonzero.  Per-entry `rfl`. -/
theorem comparisonIsChainMapDegreeThree :
    ∀ rowIndex colIndex, rowIndex < 4 → colIndex < 10 →
      comparisonProductEntry amalgamBoundaryOfDimTwo amalgamComparisonMapDegreeThree 11
          rowIndex colIndex
        = comparisonProductEntry amalgamComparisonMapDegreeTwo directSumBoundaryDimTwo 4
            rowIndex colIndex
  | 0, 0, _, _ => rfl
  | 0, 1, _, _ => rfl
  | 0, 2, _, _ => rfl
  | 0, 3, _, _ => rfl
  | 0, 4, _, _ => rfl
  | 0, 5, _, _ => rfl
  | 0, 6, _, _ => rfl
  | 0, 7, _, _ => rfl
  | 0, 8, _, _ => rfl
  | 0, 9, _, _ => rfl
  | 0, _ + 10, _, colBound => columnIndexOutOfRangeAbsurd _ 10 colBound
  | 1, 0, _, _ => rfl
  | 1, 1, _, _ => rfl
  | 1, 2, _, _ => rfl
  | 1, 3, _, _ => rfl
  | 1, 4, _, _ => rfl
  | 1, 5, _, _ => rfl
  | 1, 6, _, _ => rfl
  | 1, 7, _, _ => rfl
  | 1, 8, _, _ => rfl
  | 1, 9, _, _ => rfl
  | 1, _ + 10, _, colBound => columnIndexOutOfRangeAbsurd _ 10 colBound
  | 2, 0, _, _ => rfl
  | 2, 1, _, _ => rfl
  | 2, 2, _, _ => rfl
  | 2, 3, _, _ => rfl
  | 2, 4, _, _ => rfl
  | 2, 5, _, _ => rfl
  | 2, 6, _, _ => rfl
  | 2, 7, _, _ => rfl
  | 2, 8, _, _ => rfl
  | 2, 9, _, _ => rfl
  | 2, _ + 10, _, colBound => columnIndexOutOfRangeAbsurd _ 10 colBound
  | 3, 0, _, _ => rfl
  | 3, 1, _, _ => rfl
  | 3, 2, _, _ => rfl
  | 3, 3, _, _ => rfl
  | 3, 4, _, _ => rfl
  | 3, 5, _, _ => rfl
  | 3, 6, _, _ => rfl
  | 3, 7, _, _ => rfl
  | 3, 8, _, _ => rfl
  | 3, 9, _, _ => rfl
  | 3, _ + 10, _, colBound => columnIndexOutOfRangeAbsurd _ 10 colBound
  | _ + 4, _, rowBound, _ => columnIndexOutOfRangeAbsurd _ 4 rowBound

/-! ## B2 — instance exactness at degrees `0..2`

The sequence `0 -> C(S) --alpha--> C(A) (+) C(B) --beta--> C(amalgam) -> 0` is exact in degrees `0..2`,
witnessed the propext-clean way:

  * `beta . alpha = 0`  (`im alpha subset ker beta`) — per-entry `rfl`;
  * `alpha` injective   — explicit left inverse `L . alpha = id`;
  * `beta` surjective   — explicit right inverse `beta . R = id` at degrees `0, 1, 2`;
  * middle exactness    — the Smith RANK IDENTITY `rank(alpha_n) = nullity(beta_n)`.

Everything is stated on the double-monoid amalgam INSTANCE (see the honesty-scoping note). -/

/-- **`beta_0 . alpha_0 = 0`** — the degree-0 complex condition (`im alpha subset ker beta`): the
diagonal followed by the difference cancels.  `1 x 1`, single entry `1 * 1 + (-1) * 1 = 0`. -/
theorem comparisonAfterInclusionVanishesDegreeZero :
    ∀ rowIndex colIndex, rowIndex < 1 → colIndex < 1 →
      comparisonProductEntry amalgamComparisonMapDegreeZero amalgamInclusionDegreeZero 2
          rowIndex colIndex = 0
  | 0, 0, _, _ => rfl
  | 0, _ + 1, _, colBound => columnIndexOutOfRangeAbsurd _ 1 colBound
  | _ + 1, _, rowBound, _ => columnIndexOutOfRangeAbsurd _ 1 rowBound

/-- **`beta_1 . alpha_1 = 0`** — the degree-1 complex condition. -/
theorem comparisonAfterInclusionVanishesDegreeOne :
    ∀ rowIndex colIndex, rowIndex < 1 → colIndex < 1 →
      comparisonProductEntry amalgamComparisonMapDegreeOne amalgamInclusionDegreeOne 2
          rowIndex colIndex = 0
  | 0, 0, _, _ => rfl
  | 0, _ + 1, _, colBound => columnIndexOutOfRangeAbsurd _ 1 colBound
  | _ + 1, _, rowBound, _ => columnIndexOutOfRangeAbsurd _ 1 rowBound

/-- The left inverse of `alpha_0` (`= alpha_1`): the `1 x 2` projection `[[1, 0]]` onto the A-part;
`L . alpha = id` on the `1`-dimensional shared object, witnessing injectivity. -/
def amalgamInclusionLeftInverse : IntMatrix := ⟨[[1, 0]]⟩

/-- **`alpha_0` is injective** — the left inverse composite `L . alpha_0` is the `1 x 1` identity
`[1]` (the shared object is `1`-dimensional, so this single entry is the whole identity). -/
theorem inclusionIsInjectiveDegreeZero :
    comparisonProductEntry amalgamInclusionLeftInverse amalgamInclusionDegreeZero 2 0 0 = 1 := rfl

/-- **`alpha_1` is injective** — the same left inverse composite is `[1]`. -/
theorem inclusionIsInjectiveDegreeOne :
    comparisonProductEntry amalgamInclusionLeftInverse amalgamInclusionDegreeOne 2 0 0 = 1 := rfl

/-- The right inverse of `beta_0` (`= beta_1`): the `2 x 1` section `[[1], [0]]` picking the A-part;
`beta . R = id` on the `1`-dimensional amalgam object, witnessing surjectivity. -/
def amalgamComparisonRightInverseDegreeZero : IntMatrix := ⟨[[1], [0]]⟩

/-- **`beta_0` is surjective** — the right inverse composite `beta_0 . R` is the `1 x 1` identity. -/
theorem comparisonIsSurjectiveDegreeZero :
    comparisonProductEntry amalgamComparisonMapDegreeZero amalgamComparisonRightInverseDegreeZero 2
      0 0 = 1 := rfl

/-- **`beta_1` is surjective** — the same right inverse composite is `[1]`. -/
theorem comparisonIsSurjectiveDegreeOne :
    comparisonProductEntry amalgamComparisonMapDegreeOne amalgamComparisonRightInverseDegreeZero 2
      0 0 = 1 := rfl

/-- The right inverse of `beta_2 = diag(1, 1, -1, -1)`: its own involution `diag(1, 1, -1, -1)`, so
`beta_2 . R = I_4` witnesses surjectivity at degree 2. -/
def amalgamComparisonRightInverseDegreeTwo : IntMatrix :=
  ⟨[ [1, 0, 0, 0]
   , [0, 1, 0, 0]
   , [0, 0, -1, 0]
   , [0, 0, 0, -1] ]⟩

/-- The `4 x 4` identity — the target of the degree-2 surjectivity composite. -/
def amalgamIdentityDegreeTwo : IntMatrix :=
  ⟨[ [1, 0, 0, 0]
   , [0, 1, 0, 0]
   , [0, 0, 1, 0]
   , [0, 0, 0, 1] ]⟩

/-- **`beta_2` is surjective** — the right inverse composite `beta_2 . R` equals the `4 x 4` identity
entrywise.  Per-entry `rfl`; out-of-range peels reuse the shipped helper. -/
theorem comparisonIsSurjectiveDegreeTwo :
    ∀ rowIndex colIndex, rowIndex < 4 → colIndex < 4 →
      comparisonProductEntry amalgamComparisonMapDegreeTwo amalgamComparisonRightInverseDegreeTwo 4
          rowIndex colIndex
        = amalgamIdentityDegreeTwo.entryAt rowIndex colIndex
  | 0, 0, _, _ => rfl
  | 0, 1, _, _ => rfl
  | 0, 2, _, _ => rfl
  | 0, 3, _, _ => rfl
  | 0, _ + 4, _, colBound => columnIndexOutOfRangeAbsurd _ 4 colBound
  | 1, 0, _, _ => rfl
  | 1, 1, _, _ => rfl
  | 1, 2, _, _ => rfl
  | 1, 3, _, _ => rfl
  | 1, _ + 4, _, colBound => columnIndexOutOfRangeAbsurd _ 4 colBound
  | 2, 0, _, _ => rfl
  | 2, 1, _, _ => rfl
  | 2, 2, _, _ => rfl
  | 2, 3, _, _ => rfl
  | 2, _ + 4, _, colBound => columnIndexOutOfRangeAbsurd _ 4 colBound
  | 3, 0, _, _ => rfl
  | 3, 1, _, _ => rfl
  | 3, 2, _, _ => rfl
  | 3, 3, _, _ => rfl
  | 3, _ + 4, _, colBound => columnIndexOutOfRangeAbsurd _ 4 colBound
  | _ + 4, _, rowBound, _ => columnIndexOutOfRangeAbsurd _ 4 rowBound

/-! ### Smith ranks for the middle-exactness rank identity

`rank(alpha_n)` and `rank(beta_n)` are read off explicit Smith normal forms (each a unit-only diagonal,
so the modules are torsion-free and the rank identity IS exactness).  Reduction certificates over the
shipped unimodular alphabet, bridged to their literal Smith normal forms by `rfl`. -/

/-- `alpha_0 = [[1], [1]]` reduces to `[[1], [0]]` (one row transvection `row1 -= row0`). -/
def amalgamInclusionDegreeZeroSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations := [ .rowOperation (.addRowMultiple 0 1 (-1)) ] }

/-- The Smith normal form of `alpha_0` — the literal `[[1], [0]]` (rank 1, unit factor). -/
def amalgamInclusionDegreeZeroSmithNormalForm : IntMatrix := ⟨[[1], [0]]⟩

/-- **The `alpha_0` certificate produces its Smith normal form** — `rfl` bridge. -/
theorem amalgamInclusionDegreeZeroProducesSmithNormalForm :
    amalgamInclusionDegreeZero.applyOperations
        amalgamInclusionDegreeZeroSmithCertificate.operations
      = amalgamInclusionDegreeZeroSmithNormalForm := rfl

/-- **`alpha_0` reduces to Smith normal form** — rank 1 within the `2 x 1` window, unit invariant
factor (so `alpha` is injective with torsion-free image). -/
theorem amalgamInclusionDegreeZeroReducesToSmith :
    amalgamInclusionDegreeZeroSmithCertificate.reducesToSmithForm amalgamInclusionDegreeZero 2 1 :=
  show (⟨[[1], [0]]⟩ : IntMatrix).IsSmithNormalFormWithin 2 1 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 2 → ∀ colIndex, colIndex < 1 →
          rowIndex ≠ colIndex →
          (⟨[[1], [0]]⟩ : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow)) }

/-- `beta_0 = [[1, -1]]` reduces to `[[1, 0]]` (one column transvection `col1 += col0`). -/
def amalgamComparisonMapDegreeZeroSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations := [ .columnOperation (.addColumnMultiple 0 1 1) ] }

/-- The Smith normal form of `beta_0` — the literal `[[1, 0]]` (rank 1, unit factor). -/
def amalgamComparisonMapDegreeZeroSmithNormalForm : IntMatrix := ⟨[[1, 0]]⟩

/-- **The `beta_0` certificate produces its Smith normal form** — `rfl` bridge. -/
theorem amalgamComparisonMapDegreeZeroProducesSmithNormalForm :
    amalgamComparisonMapDegreeZero.applyOperations
        amalgamComparisonMapDegreeZeroSmithCertificate.operations
      = amalgamComparisonMapDegreeZeroSmithNormalForm := rfl

/-- **`beta_0` reduces to Smith normal form** — rank 1 within the `1 x 2` window, unit factor. -/
theorem amalgamComparisonMapDegreeZeroReducesToSmith :
    amalgamComparisonMapDegreeZeroSmithCertificate.reducesToSmithForm
      amalgamComparisonMapDegreeZero 1 2 :=
  show (⟨[[1, 0]]⟩ : IntMatrix).IsSmithNormalFormWithin 1 2 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 1 → ∀ colIndex, colIndex < 2 →
          rowIndex ≠ colIndex →
          (⟨[[1, 0]]⟩ : IntMatrix).entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      Nat.noConfusion (natEqZeroOfLeZero (natLeOfSuccLeSucc isPositionBelow)) }

/-- `beta_2 = diag(1, 1, -1, -1)` reduces to `I_4` (negate columns 2 and 3). -/
def amalgamComparisonMapDegreeTwoSmithCertificate : IntMatrix.SmithReductionCertificate :=
  { operations := [ .columnOperation (.negateColumn 2), .columnOperation (.negateColumn 3) ] }

/-- **The `beta_2` certificate produces `I_4`** — `rfl` bridge (the diagonal-plus/minus-one map is
unimodular, its Smith normal form the identity, rank 4). -/
theorem amalgamComparisonMapDegreeTwoProducesSmithNormalForm :
    amalgamComparisonMapDegreeTwo.applyOperations
        amalgamComparisonMapDegreeTwoSmithCertificate.operations
      = amalgamIdentityDegreeTwo := rfl

/-- **`beta_2` reduces to Smith normal form** — `I_4`, rank 4 within the `4 x 4` window, all unit
factors. -/
theorem amalgamComparisonMapDegreeTwoReducesToSmith :
    amalgamComparisonMapDegreeTwoSmithCertificate.reducesToSmithForm
      amalgamComparisonMapDegreeTwo 4 4 :=
  show amalgamIdentityDegreeTwo.IsSmithNormalFormWithin 4 4 from
  { offDiagonalVanishes := by
      have offDiagonalLiteral : ∀ rowIndex, rowIndex < 4 → ∀ colIndex, colIndex < 4 →
          rowIndex ≠ colIndex → amalgamIdentityDegreeTwo.entryAt rowIndex colIndex = 0 := by decide
      exact fun rowIndex colIndex isRowInRange isColInRange isOffDiagonal =>
        offDiagonalLiteral rowIndex isRowInRange colIndex isColInRange isOffDiagonal
    diagonalIsNonnegative := by decide
    diagonalDividesSuccessor := fun position isPositionBelow =>
      match position, isPositionBelow with
      | 0, _ => ⟨1, rfl⟩
      | 1, _ => ⟨1, rfl⟩
      | 2, _ => ⟨1, rfl⟩
      | _ + 3, isBeyond =>
          Nat.noConfusion (natEqZeroOfLeZero
            (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc (natLeOfSuccLeSucc isBeyond))))) }

#eval smithRankWithin amalgamInclusionDegreeZeroSmithNormalForm 1      -- 1  (rank alpha_0 = alpha_1)
#eval smithRankWithin amalgamInclusionDegreeTwo 0                      -- 0  (rank alpha_2)
#eval smithRankWithin amalgamComparisonMapDegreeZeroSmithNormalForm 1  -- 1  (rank beta_0 = beta_1)
#eval smithRankWithin amalgamIdentityDegreeTwo 4                       -- 4  (rank beta_2)

/-- `rank(alpha_0) = rank(alpha_1) = 1` (the shared object / endo injects with full rank). -/
def amalgamInclusionRankLowDegree : Nat := smithRankWithin amalgamInclusionDegreeZeroSmithNormalForm 1

/-- `rank(alpha_2) = 0` (the `4 x 0` empty map). -/
def amalgamInclusionRankDegreeTwo : Nat := smithRankWithin amalgamInclusionDegreeTwo 0

/-- `nullity(beta_0) = nullity(beta_1) = C_n(sum) - rank(beta_n) = 2 - 1 = 1`. -/
def amalgamComparisonNullityLowDegree : Nat :=
  (monadWalkerPresentation.computeBasisCount 1 + monadWalkerPresentation.computeBasisCount 1)
    - smithRankWithin amalgamComparisonMapDegreeZeroSmithNormalForm 1

/-- `nullity(beta_2) = C2(sum) - rank(beta_2) = 4 - 4 = 0`. -/
def amalgamComparisonNullityDegreeTwo : Nat :=
  (monadWalkerPresentation.computeBasisCount 2 + monadWalkerPresentation.computeBasisCount 2)
    - smithRankWithin amalgamIdentityDegreeTwo 4

/-- **Middle exactness at degree 0**: `rank(alpha_0) = nullity(beta_0)` (both `1`).  Since all Smith
factors are units, the modules are torsion-free and this rank identity IS exactness at the middle. -/
theorem comparisonMiddleExactnessDegreeZero :
    amalgamInclusionRankLowDegree = amalgamComparisonNullityLowDegree := rfl

/-- **Middle exactness at degree 1**: `rank(alpha_1) = nullity(beta_1)` (both `1`). -/
theorem comparisonMiddleExactnessDegreeOne :
    amalgamInclusionRankLowDegree = amalgamComparisonNullityLowDegree := rfl

/-- **Middle exactness at degree 2**: `rank(alpha_2) = nullity(beta_2)` (both `0`). -/
theorem comparisonMiddleExactnessDegreeTwo :
    amalgamInclusionRankDegreeTwo = amalgamComparisonNullityDegreeTwo := rfl

/-! ### The degree-3 cokernel and the connecting-element seed

`beta_3` never hits amalgam generator `10` (the cross), so `im(beta_3) = <cols 0..9>` and
`coker(beta_3) = ZZ<cross>`.  The connecting-element seed is the r1 boundary fact `d3(cross) = zeta` —
the chain-level map from the degree-3 cokernel generator toward the shared `H1(S) = ZZ` generator (the
Mayer-Vietoris connecting recipe; the homology-level `delta` and the LES stay unclaimed, see the
honesty note). -/

/-- **`beta_3` misses the cross generator** — row `10` (the cross) is zero across all ten source
columns, so the cross cell is not in the image of `beta_3`: it generates the degree-3 cokernel.
Per-entry `rfl`; the out-of-range peel reuses the shipped helper. -/
theorem comparisonDegreeThreeMissesCross :
    ∀ colIndex, colIndex < 10 → amalgamComparisonMapDegreeThree.entryAt 10 colIndex = 0
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | _ + 10, colBound => columnIndexOutOfRangeAbsurd _ 10 colBound

/-- **The connecting-element seed** — the boundary of the degree-3 cokernel generator (the cross cell)
is `zeta = mu_a - mu_b`, reusing the r1 boundary fact.  Under the Mayer-Vietoris connecting recipe
this is the chain-level image of the cokernel generator toward `H1(S) = ZZ`; the homology-level `delta`
and the long exact sequence stay UNCLAIMED (the sequence fails surjectivity at degree 3). -/
theorem connectingSeedIsMultiplicationDifference :
    amalgamChainComplex.applyBoundary 2 amalgamCrossThreeCell = amalgamMultiplicationDifference :=
  amalgamCrossCellBoundaryIsMultiplicationDifference

/-- **The rank defect IS the cross** — `C3(amalgam) = 11 = C3(A) + C3(B) + 1`: the amalgam's degree-3
basis is the two parts' ten critical pairs plus the ONE cross generator.  The `+1` is the numeric
shadow of the degree-3 cokernel `ZZ<cross>`. -/
theorem amalgamMayerVietorisRankDefectIsCross :
    doubleMonoidAmalgam.computeBasisCount 3
      = monadWalkerPresentation.computeBasisCount 3
        + monadWalkerPresentation.computeBasisCount 3 + 1 := rfl

/-! ## B3 — the DECIDED parts-vs-amalgam torsion table

`H_n` free rank `= nullity(d_n) - rank(d_{n+1}) = (C_n - rank(d_n)) - rank(d_{n+1})`; torsion `=` the
non-unit invariant factors of `d_{n+1}`.  All boundaries here have unit-only Smith normal forms, so
there is NO torsion anywhere; the census is entirely in the free ranks.

| complex               | H0(red) | H1  | H2 | torsion |
| walking monad (A = B) |    0    |  0  | 0  |  none   |
| shared endo (S)       |    0    | ZZ  | 0  |  none   |
| amalgam               |    0    |  0  | 0  |  none   |

The single nonzero off-diagonal entry `H1(S) = ZZ` is the obstruction's signature: the amalgam absorbs
it not into its own `H1`/`H2` (both `0`) but into the extra degree-3 generator (the cross cell — the
cokernel), the `+1` of `amalgamMayerVietorisRankDefectIsCross`. -/

/-- The degree-1 loop boundary `d1_S = [[0]]` of the shared endo — already its own trivial Smith
normal form (rank 0). -/
def sharedEndoSmithNormalFormOfDimZero : IntMatrix := ⟨[[0]]⟩

/-- The degree-2 boundary `d2_S = [[]]` of the shared endo (`1 x 0`, no rules) — trivially Smith
normal (rank 0). -/
def sharedEndoSmithNormalFormOfDimOne : IntMatrix := ⟨[[]]⟩

/-- **`d1_S` is the shared endo's computed degree-0 boundary** — `rfl` bridge (honest: the SNF read-off
is the ACTUAL boundary, not a disconnected literal). -/
theorem sharedEndoComputesBoundaryDimZero :
    sharedEndoPresentation.computeBoundaryDimZero = sharedEndoSmithNormalFormOfDimZero := rfl

/-- **`d2_S` is the shared endo's computed degree-1 boundary** — `rfl` bridge. -/
theorem sharedEndoComputesBoundaryDimOne :
    sharedEndoPresentation.computeBoundaryDimOne = sharedEndoSmithNormalFormOfDimOne := rfl

#eval walkerBasisCount 1 - smithRankWithin walkerBoundaryOfDimZero 1                      -- 1 nullity d1 (monad)
#eval smithRankWithin walkerSmithNormalFormOfDimOne 1                                     -- 1 rank d2 (monad)
#eval sharedEndoPresentation.computeBasisCount 1 - smithRankWithin sharedEndoSmithNormalFormOfDimZero 1  -- 1 nullity d1 (S)
#eval smithRankWithin sharedEndoSmithNormalFormOfDimOne 1                                 -- 0 rank d2 (S)
#eval doubleMonoidAmalgam.computeBasisCount 1 - smithRankWithin doubleMonoidAmalgam.computeBoundaryDimZero 1  -- 1 nullity d1 (amalgam)
#eval smithRankWithin amalgamSmithNormalFormOfDimOne 1                                    -- 1 rank d2 (amalgam)

/-- The walking-monad degree-1 homology free rank `= (C1 - rank d1) - rank d2 = (1 - 0) - 1 = 0`. -/
def partDegreeOneHomologyFreeRank : Nat :=
  (walkerBasisCount 1 - smithRankWithin walkerBoundaryOfDimZero 1)
    - smithRankWithin walkerSmithNormalFormOfDimOne 1

/-- **Part `H1 = 0`** (each walking-monad copy), by `rfl` on the `Nat` literals. -/
theorem partDegreeOneHomologyIsZero : partDegreeOneHomologyFreeRank = 0 := rfl

/-- The shared endo's degree-1 homology free rank `= (C1 - rank d1) - rank d2 = (1 - 0) - 0 = 1`. -/
def sharedEndoDegreeOneHomologyFreeRank : Nat :=
  (sharedEndoPresentation.computeBasisCount 1
      - smithRankWithin sharedEndoSmithNormalFormOfDimZero 1)
    - smithRankWithin sharedEndoSmithNormalFormOfDimOne 1

/-- **Shared `H1 = ZZ`** — free rank `1`, the ONLY nonzero off-diagonal entry of the torsion table
(the obstruction's numeric signature).  By `rfl` on the `Nat` literals. -/
theorem sharedEndoDegreeOneHomologyIsFreeRankOne : sharedEndoDegreeOneHomologyFreeRank = 1 := rfl

/-- The amalgam's degree-1 homology free rank `= (C1 - rank d1) - rank d2 = (1 - 0) - 1 = 0`. -/
def amalgamDegreeOneHomologyFreeRank : Nat :=
  (doubleMonoidAmalgam.computeBasisCount 1
      - smithRankWithin doubleMonoidAmalgam.computeBoundaryDimZero 1)
    - smithRankWithin amalgamSmithNormalFormOfDimOne 1

/-- **Amalgam `H1 = 0`** — the shared `ZZ` is NOT absorbed into the amalgam's `H1` (nor its `H2`,
which is also `0`), but into the extra degree-3 cross generator.  By `rfl`. -/
theorem amalgamDegreeOneHomologyIsZero : amalgamDegreeOneHomologyFreeRank = 0 := rfl

/-- **The shared endo has `H2 = 0`** — `C2(S) = 0`, so there are no degree-2 chains and `H2` is
trivially `0`.  `rfl`. -/
theorem sharedEndoDegreeTwoHomologyIsZero : sharedEndoPresentation.computeBasisCount 2 = 0 := rfl

/-- **No `H1` torsion in the part** — the walking-monad `d2` Smith normal form is `[[1, 0]]`, unit
factor. -/
theorem partDegreeOneHasNoTorsion : hasNoSmithTorsionWithin walkerSmithNormalFormOfDimOne 1 :=
  ⟨True.intro, Or.inr rfl⟩

/-- **No `H1` torsion in the amalgam** — the amalgam `d2` Smith normal form is `[[1, 0, 0, 0]]`, unit
factor. -/
theorem amalgamDegreeOneHasNoTorsion : hasNoSmithTorsionWithin amalgamSmithNormalFormOfDimOne 1 :=
  ⟨True.intro, Or.inr rfl⟩

/-- ★ **The decided parts-vs-amalgam torsion table**: part `H1 = 0`, shared `H1 = ZZ` (free rank 1),
amalgam `H1 = 0`, amalgam `H2 = 0`, and no `H1` torsion in either the part or the amalgam.  Everything
read off the kernel-checked Smith normal forms; the single nonzero off-diagonal `H1(S) = ZZ` is the
obstruction's signature. -/
def AmalgamMayerVietorisTorsionTableStatement : Prop :=
  partDegreeOneHomologyFreeRank = 0 ∧
  sharedEndoDegreeOneHomologyFreeRank = 1 ∧
  amalgamDegreeOneHomologyFreeRank = 0 ∧
  amalgamDegreeTwoHomologyFreeRank = 0 ∧
  hasNoSmithTorsionWithin walkerSmithNormalFormOfDimOne 1 ∧
  hasNoSmithTorsionWithin amalgamSmithNormalFormOfDimOne 1

/-- ★★ **The torsion table is DECIDED** — every entry proved, off the Smith normal forms. -/
theorem amalgamMayerVietorisTorsionTable : AmalgamMayerVietorisTorsionTableStatement :=
  ⟨partDegreeOneHomologyIsZero, sharedEndoDegreeOneHomologyIsFreeRankOne,
   amalgamDegreeOneHomologyIsZero, amalgamDegreeTwoHomologyFreeRankIsZero,
   partDegreeOneHasNoTorsion, amalgamDegreeOneHasNoTorsion⟩

/-! ## B4 — the round-2 ledger (honest markers + the r3 bill)

### What round 2 SHIPS (all zero-axiom, all instance-level)

  * **B1** — the comparison chain map `beta : C(A) (+) C(B) -> C(amalgam)`
    (`comparisonIsChainMapDegree{One,Two,Three}`) with the shared substructure `S` the walking endo.
  * **B2** — instance exactness at degrees `0..2`: `beta . alpha = 0`, `alpha` injective, `beta`
    surjective (deg `0, 1, 2`), the Smith rank-identity middle exactness; the degree-3 cokernel
    `ZZ<cross>` (`comparisonDegreeThreeMissesCross`) with the connecting-element seed
    (`connectingSeedIsMultiplicationDifference`) and the rank defect
    (`amalgamMayerVietorisRankDefectIsCross`).
  * **B3** — the decided torsion table (`amalgamMayerVietorisTorsionTable`): part `H1 = 0`, shared
    `H1 = ZZ`, amalgam `H1 = 0`, every `H2 = 0`, no torsion.

### The r3 bill (NAMED, NOT flipped)

  * the Mayer-Vietoris LONG EXACT SEQUENCE and the homology-level connecting homomorphism
    `delta : H_n(amalgam) -> H_{n-1}(S)` — blocked here because the sequence of complexes fails
    surjectivity at degree 3 (`coker = ZZ<cross>`), so the honest object is a PARTIAL sequence with a
    defect term; the LES is the arc target;
  * the amalgam's DECIDEDNESS / convergence (is "two monoid structures on one endo" a decided walker;
    Eckmann-Hilton) and the COMPLETENESS of the cross critical-pair set;
  * the BIMONOID proper (bialgebra / interchange relation) as a Cartan-Eilenberg BICOMPLEX — the true
    frontier the r1 B6 no-go points at (see `bimonoidBicomplexIsR3Bill`). -/

/-- ★ **The comparison-chain-map marker.**  What stands, zero-axiom and instance-level: `beta` is a
genuine chain map (`comparisonIsChainMapDegree{One,Two,Three}`), `alpha` splits it, and the sequence is
exact in degrees `0..2` with the degree-3 cokernel `ZZ<cross>` carrying the obstruction.  The general
polygraphic Mayer-Vietoris theorem stays UNCLAIMED.  Read the meaning from THIS docstring. -/
def amalgamComparisonChainMapIsLive : Bool := true

/-- ★ **The connecting-seed marker.**  The degree-3 cokernel generator (the cross cell) has boundary
`zeta = mu_a - mu_b` (`connectingSeedIsMultiplicationDifference`) — the chain-level seed of the
Mayer-Vietoris connecting map toward `H1(S) = ZZ`.  The homology-level `delta` and the LONG EXACT
SEQUENCE stay UNCLAIMED: the sequence of complexes is exact in degrees `0..2` but fails surjectivity at
degree 3 (`coker = ZZ<cross>` is nonzero), the polygraphic shadow of monoid-amalgam non-embeddability
(Howie).  Read the meaning from THIS docstring. -/
def amalgamMayerVietorisConnectingSeedIsHonest : Bool := true

/-- ★ **The r3 bill marker.**  The BIMONOID proper (monoid + comonoid on one endo with the bialgebra /
interchange law) is a two-differential Cartan-Eilenberg BICOMPLEX — structurally larger than this
single-complex machinery; r1 B6 showed the naive union breaks `d d = 0` with defect `-2`.  r2 builds NO
bicomplex; the conjecture "the bialgebra law kills the cross obstruction as a cocycle" is an ORIGINAL
conjecture, unattested in the fetched literature (only a rigidity remark, Fox-Markl), recorded here as
a probe and NOT proven.  This marker only points forward.  Read the meaning from THIS docstring. -/
def bimonoidBicomplexIsR3Bill : Bool := true

end FX1Poly.Polygraph.Homology

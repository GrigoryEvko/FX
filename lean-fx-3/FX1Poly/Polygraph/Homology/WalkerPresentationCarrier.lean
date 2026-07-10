import FX1Poly.Polygraph.Omega.SteinerFoundation.AugmentedDirectedComplex
import FX1Poly.ComputerAlgebra.Number.NatEuclideanDivision
import FX1Poly.Polygraph.Homology.InvolutionChainComplex

/-! # FX1Poly/Polygraph/Homology/WalkerPresentationCarrier — the GENERIC first-order presentation
    carrier for decided single-object walkers, with COMPUTED boundary matrices, the generic
    dimension-0 loop lemma, the well-formedness-gated `d d = 0`, and the two shipped instances
    (walking monad, walking involution) recovered as EVALUATIONS (H2-WALKERS r2, #2138)

The two shipped literal chain complexes (`Homology/WalkerChainComplex`, `Homology/InvolutionChainComplex`)
are the SAME nine-part template with the boundary matrices written as hand-computed LITERALS.  This
module factors the shared shape into a first-order presentation RECORD `WalkerPresentation` whose
`d1`/`d2`/`d3` are COMPUTED from the presentation data by abelianization — and then proves that
evaluating the computed functions at the monad's / involution's presentation reproduces the shipped
literals EXACTLY (`monadPresentationComputes…`, `involutionPresentationComputes…`, all `rfl`).  The
shipped literal decls keep their names and meaning VERBATIM; this file adds the generic layer ON TOP,
never replacing them.

## The abelianization (compute functions)

A `WalkerPresentation` records: `oneGeneratorCount` (the number of endo 1-generators; `C1`), `rules`
(each a `(sourceWord, targetWord)` over the 1-generators; `C2`), and `criticalPairs` (each a
`(overlapWord, leftLegFirings, rightLegFirings)` where the two firing lists are indexed BY RULE; `C3`).
The object count is HARDCODED to 1 (`computeBasisCount 0 = 1`) — the documented design scope is
single-object decided walkers (both shipped instances and the r2 third instance qualify).

  * `computeBoundaryDimZero` — `d1 : C1 → C0`, the `1 × oneGeneratorCount` all-zero row: every endo
    1-generator is a LOOP `point → point`, so `[point] − [point] = 0`.
  * `computeBoundaryDimOne` — `d2 : C2 → C1`, `oneGeneratorCount × rules.length`: row `g`, column `r`
    is `(#g in targetWord r) − (#g in sourceWord r)` (abelianized `[target] − [source]`).
  * `computeBoundaryDimTwo` — `d3 : C3 → C2`, `rules.length × criticalPairs.length`: row `r`, column
    `cp` is `(leftLegFirings cp)[r] − (rightLegFirings cp)[r]` (the abelianized COFORK of the two
    rewriting legs, read per rule).

`overlapWord` is DOCUMENTATION-ONLY metadata — the abelianization ignores it (recorded as a slot so the
data mirrors the Knuth–Bendix overlap; the compute functions never read `.1` of a critical pair).

## What is generic vs. what stays per-instance (the honest `d d = 0` adjudication)

`d d = 0` splits into two non-vacuous halves, and only the first is GENERICALLY true:

  * **dimension 0 (`d1 · d2`): GENERICALLY zero.**  `computeBoundaryDimZero` is the all-zero loop row,
    so `Σ_g d1[row, g] · d2[g, col] = Σ_g 0 · … = 0` for ANY presentation.  Shipped here as the genuine
    generic lemma `walkerPresentationLoopBoundaryIsZero` (via `walkerPresentationDimZeroEntryIsZero` +
    `sumOverIndicesOfAllZero`).  This is real generic content.
  * **dimension 1 (`d2 · d3`): NOT generically zero.**  `(d2 · d3)[g, cp] = Σ_r (Δ#g in rule r) ·
    (leftFirings[r] − rightFirings[r])`; a bogus presentation whose critical-pair legs do not close
    (unequal abelianized 1-cell displacement) breaks it.  This IS the cofork-closure coherence
    condition; no cheaper syntactic shortcut exists short of re-deriving confluence.  It is packaged as
    the PREDICATE `WellFormedWalkerPresentation` — the exact residual obligation — and
    `walkerPresentationBoundaryComposesToZeroOfWellFormed` assembles the full `boundaryComposesToZero`
    field from (dim 0) the generic loop lemma, (dim 1) the well-formedness hypothesis, and (dim ≥ 2) the
    zero-width tail.

`WellFormedWalkerPresentation` is ASSUMED nowhere: each concrete instance DISCHARGES it — for the two
shipped walkers, the discharge is literally the shipped `walkerBoundaryComposesToZero` /
`involutionBoundaryComposesToZero` at dimension 1 (`monadPresentationIsWellFormed`,
`involutionPresentationIsWellFormed`), so the generic machinery is verified to reproduce the shipped
chain obligation, not to weaken it.

## Zero-axiom design decisions

  * The presentation is a plain record over `Nat` / `List Nat` — every match below is on non-indexed
    inductives (`List`, `Prod`, `Nat`), so none of the indexed-match propext traps apply.
  * The compute functions are STRUCTURAL (row builders recurse on the rule / critical-pair lists and on
    a generator/rule counter), so whole-matrix agreement closes by `rfl`.
  * The loop lemma reduces to `sumOverIndicesOfAllZero`, proved by structural induction on the index
    count; the dimension-0 entry-is-zero fact is proved by explicit `listGetWithDefault` reductions,
    never `decide` on a `Nat.min` / `Nat.sub` expression.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/Polygraph/Homology/WalkerPresentationCarrier.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra
open FX1Poly.Polygraph.Steiner

/-! ## B1 — the presentation record and the computed abelianization -/

/-- A first-order presentation of a DECIDED single-object walker, as the data the polygraphic chain
complex abelianizes.  `oneGeneratorCount` counts the endo 1-generators (`C1`); `rules` lists the
rewrite 2-generators as `(sourceWord, targetWord)` over the 1-generators (`C2`); `criticalPairs` lists
the Squier critical pairs as `(overlapWord, leftLegFirings, rightLegFirings)`, where the two firing
lists are indexed BY RULE (`C3`).  The object count is hardcoded to 1 (single-object design scope). -/
structure WalkerPresentation where
  /-- The number of endo 1-generators (`C1 = ZZ^oneGeneratorCount`). -/
  oneGeneratorCount : Nat
  /-- The rewrite 2-generators, each `(sourceWord, targetWord)` over the 1-generators (`C2`). -/
  rules : List (List Nat × List Nat)
  /-- The Squier critical pairs, each `(overlapWord, leftLegFirings, rightLegFirings)` with the firing
  lists indexed by rule (`C3`).  `overlapWord` is documentation-only; abelianization ignores it. -/
  criticalPairs : List (List Nat × List Nat × List Nat)

/-- Count how many times `generator` occurs in a 1-generator word — structural, fully enumerated. -/
def countGeneratorOccurrences (generator : Nat) : List Nat → Nat
  | [] => 0
  | letter :: remainingLetters =>
      (if letter = generator then 1 else 0) + countGeneratorOccurrences generator remainingLetters

/-- One `d2` row for a fixed 1-generator: the abelianized `[target] − [source]` generator-count
difference, one `Int` per rule, in rule order. -/
def walkerPresentationDimOneRow (generator : Nat) : List (List Nat × List Nat) → IntRow
  | [] => []
  | (sourceWord, targetWord) :: remainingRules =>
      (Int.ofNat (countGeneratorOccurrences generator targetWord)
        - Int.ofNat (countGeneratorOccurrences generator sourceWord))
        :: walkerPresentationDimOneRow generator remainingRules

/-- The `d2` rows for the generators `startGenerator, startGenerator + 1, …` — `rowCount` rows,
structural on `rowCount`, so row `i` is generator `startGenerator + i`. -/
def walkerPresentationDimOneRows (rules : List (List Nat × List Nat)) :
    Nat → Nat → List IntRow
  | _, 0 => []
  | startGenerator, rowCount + 1 =>
      walkerPresentationDimOneRow startGenerator rules
        :: walkerPresentationDimOneRows rules (startGenerator + 1) rowCount

/-- One `d3` row for a fixed rule index: the abelianized COFORK `leftFirings[ruleIndex] −
rightFirings[ruleIndex]`, one `Int` per critical pair, in critical-pair order. -/
def walkerPresentationDimTwoRow (ruleIndex : Nat) :
    List (List Nat × List Nat × List Nat) → IntRow
  | [] => []
  | (_, leftLegFirings, rightLegFirings) :: remainingPairs =>
      (Int.ofNat (listGetWithDefault 0 leftLegFirings ruleIndex)
        - Int.ofNat (listGetWithDefault 0 rightLegFirings ruleIndex))
        :: walkerPresentationDimTwoRow ruleIndex remainingPairs

/-- The `d3` rows for the rules `startRule, startRule + 1, …` — `rowCount` rows, structural on
`rowCount`, so row `i` is rule `startRule + i`. -/
def walkerPresentationDimTwoRows (criticalPairs : List (List Nat × List Nat × List Nat)) :
    Nat → Nat → List IntRow
  | _, 0 => []
  | startRule, rowCount + 1 =>
      walkerPresentationDimTwoRow startRule criticalPairs
        :: walkerPresentationDimTwoRows criticalPairs (startRule + 1) rowCount

/-- The per-dimension basis counts: `C0 = ZZ` (single object), `C1 = ZZ^oneGeneratorCount`,
`C2 = ZZ^rules.length`, `C3 = ZZ^criticalPairs.length`, nothing above degree 3. -/
def WalkerPresentation.computeBasisCount (presentation : WalkerPresentation) : Nat → Nat
  | 0 => 1
  | 1 => presentation.oneGeneratorCount
  | 2 => presentation.rules.length
  | 3 => presentation.criticalPairs.length
  | _ + 4 => 0

/-- `d1 : C1 → C0`, the `1 × oneGeneratorCount` all-zero loop row. -/
def WalkerPresentation.computeBoundaryDimZero (presentation : WalkerPresentation) : IntMatrix :=
  ⟨[List.replicate presentation.oneGeneratorCount 0]⟩

/-- `d2 : C2 → C1`, the `oneGeneratorCount × rules.length` abelianized boundary. -/
def WalkerPresentation.computeBoundaryDimOne (presentation : WalkerPresentation) : IntMatrix :=
  ⟨walkerPresentationDimOneRows presentation.rules 0 presentation.oneGeneratorCount⟩

/-- `d3 : C3 → C2`, the `rules.length × criticalPairs.length` abelianized cofork boundary. -/
def WalkerPresentation.computeBoundaryDimTwo (presentation : WalkerPresentation) : IntMatrix :=
  ⟨walkerPresentationDimTwoRows presentation.criticalPairs 0 presentation.rules.length⟩

/-- The dimension-indexed boundary map computed from the presentation: `d4` is the
`criticalPairs.length × 0` zero map (one empty row per critical pair), everything above is `0 × 0`. -/
def WalkerPresentation.computeBoundaryMatrix (presentation : WalkerPresentation) : Nat → IntMatrix
  | 0 => presentation.computeBoundaryDimZero
  | 1 => presentation.computeBoundaryDimOne
  | 2 => presentation.computeBoundaryDimTwo
  | 3 => ⟨List.replicate presentation.criticalPairs.length ([] : IntRow)⟩
  | _ + 4 => ⟨[]⟩

/-! ## B1 — the generic dimension-0 loop lemma (`d1 · d2 = 0` for ANY presentation) -/

/-- A finite sum of identically-zero summands is zero — structural induction on the index count. -/
theorem sumOverIndicesOfAllZero (summand : Nat → Int) (allZero : ∀ index, summand index = 0) :
    ∀ count, sumOverIndices count summand = 0
  | 0 => rfl
  | count + 1 =>
      (congrArg (· + summand count) (sumOverIndicesOfAllZero summand allZero count)).trans
        ((congrArg (0 + ·) (allZero count)).trans rfl)

/-- Reading any index of the empty list returns the default — the two `[]` match arms, one per index
shape. -/
theorem listGetWithDefaultNilIsDefault {Entry : Type} (defaultEntry : Entry) :
    ∀ index, listGetWithDefault defaultEntry [] index = defaultEntry
  | 0 => rfl
  | _ + 1 => rfl

/-- Reading any index of `List.replicate count 0` returns `0` (in range: a replicated zero; out of
range: the default zero). -/
theorem listGetReplicateZeroIsZero :
    ∀ (count index : Nat), listGetWithDefault (0 : Int) (List.replicate count 0) index = 0
  | 0, index => listGetWithDefaultNilIsDefault 0 index
  | _ + 1, 0 => rfl
  | count + 1, index + 1 => listGetReplicateZeroIsZero count index

/-- Every entry of `computeBoundaryDimZero` is zero (the loop row): row 0 reads the replicated-zero
row, every later row reads past the single row into the default zero. -/
theorem walkerPresentationDimZeroEntryIsZero (presentation : WalkerPresentation) :
    ∀ (rowIndex colIndex : Nat), presentation.computeBoundaryDimZero.entryAt rowIndex colIndex = 0
  | 0, colIndex => listGetReplicateZeroIsZero presentation.oneGeneratorCount colIndex
  | _ + 1, colIndex =>
      (congrArg (fun middleRow => listGetWithDefault (0 : Int) middleRow colIndex)
        (listGetWithDefaultNilIsDefault ([] : IntRow) _)).trans
        (listGetWithDefaultNilIsDefault (0 : Int) colIndex)

/-- **The generic dimension-0 loop boundary is zero.**  For ANY presentation and any second matrix,
`Σ_middle d1[row, middle] · second[middle, col] = 0`, because every `d1` entry is zero.  This is the
genuinely generic half of `d d = 0` — it holds with no well-formedness hypothesis. -/
theorem walkerPresentationLoopBoundaryIsZero (presentation : WalkerPresentation)
    (secondMatrix : IntMatrix) (count rowIndex colIndex : Nat) :
    sumOverIndices count (fun middleIndex =>
      presentation.computeBoundaryDimZero.entryAt rowIndex middleIndex *
      secondMatrix.entryAt middleIndex colIndex) = 0 :=
  sumOverIndicesOfAllZero _
    (fun middleIndex =>
      (congrArg (· * secondMatrix.entryAt middleIndex colIndex)
        (walkerPresentationDimZeroEntryIsZero presentation rowIndex middleIndex)).trans
        (intZeroMul _))
    count

/-! ## B1 — the well-formedness predicate and the gated `d d = 0` -/

/-- **The residual dimension-1 coherence obligation** (`d2 · d3 = 0`): every critical pair's two
rewriting legs have equal abelianized 1-cell displacement.  This is the ONLY half of `d d = 0` that is
not generic; each concrete instance discharges it by finite computation on its boundary literals. -/
def WellFormedWalkerPresentation (presentation : WalkerPresentation) : Prop :=
  ∀ rowIndex colIndex,
    rowIndex < presentation.computeBasisCount 1 → colIndex < presentation.computeBasisCount 3 →
    sumOverIndices (presentation.computeBasisCount 2) (fun middleIndex =>
      presentation.computeBoundaryDimOne.entryAt rowIndex middleIndex *
      presentation.computeBoundaryDimTwo.entryAt middleIndex colIndex) = 0

/-- ★ **The full `boundaryComposesToZero` field, assembled generically.**  Dimension 0 is the generic
loop lemma; dimension 1 is the well-formedness hypothesis; dimensions `≥ 2` land in the zero-width
degree `C_{dim+2} = 0`, refuted by the propext-clean `Nat.not_lt_zero`.  This is exactly the shape of
the shipped `walkerBoundaryComposesToZero` / `involutionBoundaryComposesToZero`, now derived once for
every well-formed presentation. -/
theorem walkerPresentationBoundaryComposesToZeroOfWellFormed
    (presentation : WalkerPresentation) (wellFormed : WellFormedWalkerPresentation presentation) :
    ∀ (dim rowIndex colIndex : Nat),
      rowIndex < presentation.computeBasisCount dim →
      colIndex < presentation.computeBasisCount (dim + 2) →
      sumOverIndices (presentation.computeBasisCount (dim + 1)) (fun middleIndex =>
        (presentation.computeBoundaryMatrix dim).entryAt rowIndex middleIndex *
        (presentation.computeBoundaryMatrix (dim + 1)).entryAt middleIndex colIndex) = 0
  | 0, rowIndex, colIndex, _, _ =>
      walkerPresentationLoopBoundaryIsZero presentation (presentation.computeBoundaryMatrix 1)
        (presentation.computeBasisCount 1) rowIndex colIndex
  | 1, rowIndex, colIndex, rowBound, colBound =>
      wellFormed rowIndex colIndex rowBound colBound
  | _ + 2, _, colIndex, _, colBound =>
      absurd colBound (Nat.not_lt_zero colIndex)

/-! ## B2 — the two shipped instances recovered as EVALUATIONS

The monad's and involution's presentation data (`monadWalkerPresentation`, `involutionWalkerPresentation`,
named distinctly from the `Amalgam.monadPresentation` / `Amalgam.involutionPresentation`
`PresentationData` values, which are a different record over a different substrate).  The firing lists
are the docstring per-`(eta, mu)` (monad) / per-`rho` (involution) leg readings. -/

/-- The walking-monad presentation: one endo 1-generator `t`; two rules `eta : id ⟹ t`
(`([], [0])`) and `mu : t.t ⟹ t` (`([0, 0], [0])`); five Squier critical pairs, each with its
`(#eta, #mu)` firing counts on the left / right leg (`overlapWord = []`, documentation-only). -/
def monadWalkerPresentation : WalkerPresentation :=
  { oneGeneratorCount := 1
  , rules := [([], [0]), ([0, 0], [0])]
  , criticalPairs :=
      [ ([], [1, 0], [1, 0])
      , ([], [1, 2], [0, 1])
      , ([], [1, 2], [0, 1])
      , ([], [0, 3], [0, 3])
      , ([], [1, 2], [0, 1]) ] }

/-- The walking-involution presentation: one endo 1-generator `s`; one rule `rho : s.s ⟹ id`
(`([0, 0], [])`); one critical pair `sss` firing `rho` once on each leg (`overlapWord = []`). -/
def involutionWalkerPresentation : WalkerPresentation :=
  { oneGeneratorCount := 1
  , rules := [([0, 0], [])]
  , criticalPairs := [([], [1], [1])] }

/-- The monad presentation's basis counts equal the shipped `walkerBasisCount` at every dimension. -/
theorem monadPresentationComputesBasisCount :
    ∀ dim, monadWalkerPresentation.computeBasisCount dim = walkerBasisCount dim
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

/-- **The monad presentation computes the shipped `d1`.** -/
theorem monadPresentationComputesBoundaryDimZero :
    monadWalkerPresentation.computeBoundaryDimZero = walkerBoundaryOfDimZero := rfl

/-- **The monad presentation computes the shipped `d2` `[[1, −1]]`.** -/
theorem monadPresentationComputesBoundaryDimOne :
    monadWalkerPresentation.computeBoundaryDimOne = walkerBoundaryOfDimOne := rfl

/-- **The monad presentation computes the shipped `d3` `[[0,1,1,0,1],[0,1,1,0,1]]`.** -/
theorem monadPresentationComputesBoundaryDimTwo :
    monadWalkerPresentation.computeBoundaryDimTwo = walkerBoundaryOfDimTwo := rfl

/-- **The monad presentation computes the shipped dimension-indexed boundary at every dimension.** -/
theorem monadPresentationComputesBoundaryMatrix :
    ∀ dim, monadWalkerPresentation.computeBoundaryMatrix dim = walkerBoundaryMatrix dim
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

/-- The involution presentation's basis counts equal the shipped `involutionBasisCount`. -/
theorem involutionPresentationComputesBasisCount :
    ∀ dim, involutionWalkerPresentation.computeBasisCount dim = involutionBasisCount dim
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

/-- **The involution presentation computes the shipped `d1`.** -/
theorem involutionPresentationComputesBoundaryDimZero :
    involutionWalkerPresentation.computeBoundaryDimZero = involutionBoundaryOfDimZero := rfl

/-- **The involution presentation computes the shipped `d2` `[[-2]]`.** -/
theorem involutionPresentationComputesBoundaryDimOne :
    involutionWalkerPresentation.computeBoundaryDimOne = involutionBoundaryOfDimOne := rfl

/-- **The involution presentation computes the shipped `d3` `[[0]]`.** -/
theorem involutionPresentationComputesBoundaryDimTwo :
    involutionWalkerPresentation.computeBoundaryDimTwo = involutionBoundaryOfDimTwo := rfl

/-- **The involution presentation computes the shipped dimension-indexed boundary.** -/
theorem involutionPresentationComputesBoundaryMatrix :
    ∀ dim, involutionWalkerPresentation.computeBoundaryMatrix dim = involutionBoundaryMatrix dim
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => rfl

/-! ## B2 — the well-formedness discharge (the generic `d d = 0` recovers each shipped chain obligation) -/

/-- ★ **The monad presentation is well-formed** — the residual dimension-1 obligation is exactly the
shipped `walkerBoundaryComposesToZero` at dimension 1 (defeq through the agreement above).  This
verifies the generic machinery reproduces the shipped `d d = 0`, not a weaker statement. -/
theorem monadPresentationIsWellFormed : WellFormedWalkerPresentation monadWalkerPresentation :=
  fun rowIndex colIndex rowBound colBound =>
    walkerBoundaryComposesToZero 1 rowIndex colIndex rowBound colBound

/-- ★ **The involution presentation is well-formed** — the residual dimension-1 obligation is the
shipped `involutionBoundaryComposesToZero` at dimension 1. -/
theorem involutionPresentationIsWellFormed :
    WellFormedWalkerPresentation involutionWalkerPresentation :=
  fun rowIndex colIndex rowBound colBound =>
    involutionBoundaryComposesToZero 1 rowIndex colIndex rowBound colBound

end FX1Poly.Polygraph.Homology

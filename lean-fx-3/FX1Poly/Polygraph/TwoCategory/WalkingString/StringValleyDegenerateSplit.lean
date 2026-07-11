import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingValleyDescent
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcArity
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyBlockSplit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCellBridge
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLastCupReadoff

/-! # WalkingString — the Piece-II THREE-WAY SPLIT: `StringCellValleyTraceEquiv` sharpened into three colour-keyed
sub-producers, with the colour-BLIND skeleton + case (a) PROVED (the reconstruction bricks)

`StringMatchingValleyDescent` reduced the whole adjoint-triple DECISION to the single monolithic Piece-II Prop
`StringCellValleyTraceEquiv` (two whole VALLEY cells with equal boundary `matchingOf` have `SpineTraceEquiv`
spines).  The walking ADJUNCTION discharges its analog `cellValleyTraceEquiv_holds` through a three-way case split
`cellValleyTraceEquiv_of_widthZero_of_midZero` (`SpineValleyCellDegenerate`): on `Nat.eq_zero_or_pos
sourcePath.length`, then on `Nat.eq_zero_or_pos (survivorTopTotal (matchingOf valleyA))`, dispatching the two
Tier-D degenerate branches to `WidthZeroPureCupDeterminacy` / `MidZeroValleyTraceEquiv` and the doubly-positive
branch to `cellValleyTraceEquiv_ofPositive`.  This file PORTS that split skeleton — and its case-(a) dispatcher —
to the three-generator seed, thereby SHARPENING the monolithic `StringCellValleyTraceEquiv` from ONE Prop into
THREE named colour-keyed sub-producers.

## The B1 truth-probe: which of the adjunction's Piece-II bricks port verbatim, and which are colour-keyed

The recon split Piece II into an OUTER assembly (colour-blind, token-swap) and a SORT + arc↔matching CORE
(colour-keyed, re-derive).  This file lands the colour-blind OUTER shell:

  * ★ `stringCupArity_of_isCupAtom_true` / `stringCapArity_of_isCupAtom_false` / `stringAllCupArity_of_allCups` /
    `stringSpineValley_blockSplit` — the block extractor (a `Bool`-tag valley IS a typed cap-block ++ cup-block).
    The adjunction's `spineValley_blockSplit` is hardcoded to `adjunctionModeSignature` ONLY through
    `adjunctionSpineAtom_isCupOrCap`; the string has the shipped four-generator analog
    `adjointTripleSpineAtom_isCupOrCap` (`StringArcArity`), so the proof ports BYTE-IDENTICAL (colour-blind: it
    reads only cup-vs-cap arity, never `F`/`G`/`H`).
  * ★ `stringCapBlockEmpty_ofSourceZero` — an empty source boundary forces an empty cap block (a cap fires at
    boundary `leftContext + 2 + rightContext ≥ 2 > 0`).  Colour-blind arity + boundary-chain arithmetic; token-swap.
  * ★ `stringDegenerateEmptySource_of_widthZero` — Tier-D case (a) (`sourcePath.length = 0`), FULLY PROVED from the
    named `StringWidthZeroPureCupDeterminacy` residual: block-split both valleys, force both cap blocks empty,
    re-read the whole matching at `matchingOfSpineList 0` on the cup suffixes, apply the residual.  Token-swap of
    the adjunction's `degenerateEmptySource_of_widthZero`.
  * ★ `stringCellValleyTraceEquiv_of_widthZero_of_midZero` — the FULL three-way split: `StringCellValleyTraceEquiv`
    follows from the THREE named colour-keyed sub-producers `StringWidthZeroPureCupDeterminacy`,
    `StringMidZeroValleyTraceEquiv`, `StringCellValleyTraceEquivPositive`.  Token-swap of the adjunction skeleton.

## Why the three named residuals STAY colour-keyed (the honest wall, unmoved)

The three sub-producers are NOT token-swaps: each bottoms out in the SORT (`pureCupSpine_sort` / `pureCapSpine_sort`)
and the arc↔matching reconstruction (`cupRestrict_reconstructs`), which read the atom SPECIES through LENGTHS
(`adjunctionPath_eq_of_length_eq`).  At the string that rigidity is FALSE (`string_left_ne_coLeft`: `F`, `H` both
length-1, distinct), so the species must be read colour-aware off the boundary labels — the multi-round core the
shipped pin `stringCupCod_ne_capDom` was landed to feed.  So this file does NOT flip
`fxString_hasAdjointTripleCompleteness`: it factors the monolithic Piece-II residual into three, PROVES the
colour-blind dispatching skeleton and the case-(a) reducer, and NAMES the three colour-keyed sub-producers as the
exact remaining obligations — the reconstruction bricks the recon designed, made Lean theorems.

Raw Lean 4 + Init; the block extractor is structural recursion following the valley predicate, the case-(a) reducer
and the skeleton are the adjunction proofs with `adjunctionModeSignature → adjointTripleModeSignature` /
`adjunctionSpineAtom_isCupOrCap → adjointTripleSpineAtom_isCupOrCap`.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Tag → arity read-offs at the walking adjoint triple (colour-blind, via the four-generator classification) -/

/-- A `SpineAtom.isCupAtom = true` string atom carries cup arity `(0, 2)`.  `isCupAtom` is `true` iff
`generatorDom.length = 0`; the four-generator classification `adjointTripleSpineAtom_isCupOrCap` forces such an atom
into the cup branch (the cap branch has `generatorDom.length = 2`).  The three-generator analog of the adjunction's
`cupArity_of_isCupAtom_true`, colour-blind. -/
theorem stringCupArity_of_isCupAtom_true
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (isCup : SpineAtom.isCupAtom atom = true) :
    atom.generatorDom.length = 0 ∧ atom.generatorCod.length = 2 := by
  cases adjointTripleSpineAtom_isCupOrCap atom with
  | inl cupArity => exact cupArity
  | inr capArity =>
      exfalso
      have isCapFalse : SpineAtom.isCupAtom atom = false := by
        dsimp only [SpineAtom.isCupAtom]
        rw [capArity.1]
      rw [isCapFalse] at isCup
      exact Bool.noConfusion isCup

/-- A `SpineAtom.isCupAtom = false` string atom carries cap arity `(2, 0)`.  Dual of the cup read-off:
`adjointTripleSpineAtom_isCupOrCap` forces the cap branch when `generatorDom.length ≠ 0`.  The three-generator
analog of `capArity_of_isCupAtom_false`. -/
theorem stringCapArity_of_isCupAtom_false
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (atom : SpineAtom adjointTripleModeSignature overallSource overallTarget)
    (isCap : SpineAtom.isCupAtom atom = false) :
    atom.generatorDom.length = 2 ∧ atom.generatorCod.length = 0 := by
  cases adjointTripleSpineAtom_isCupOrCap atom with
  | inr capArity => exact capArity
  | inl cupArity =>
      exfalso
      have isCupTrue : SpineAtom.isCupAtom atom = true := by
        dsimp only [SpineAtom.isCupAtom]
        rw [cupArity.1]
      rw [isCupTrue] at isCap
      exact Bool.noConfusion isCap

/-- `allCups SpineAtom.isCupAtom xs = true` — every tail atom a cup by the `Bool` fold — upgrades to the typed
`AllCupArity xs` (every atom cup arity `(0, 2)`).  Structural induction splitting the `&&` by hand (propext-free).
The three-generator analog of `allCupArity_of_allCups`. -/
theorem stringAllCupArity_of_allCups
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (xs : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    allCups SpineAtom.isCupAtom xs = true → AllCupArity xs
  | [], _ => AllCupArity.nil
  | atom :: rest, allCupsTrue => by
      dsimp only [allCups] at allCupsTrue
      cases isCupHead : SpineAtom.isCupAtom atom with
      | false =>
          rw [isCupHead] at allCupsTrue
          exact Bool.noConfusion allCupsTrue
      | true =>
          rw [isCupHead] at allCupsTrue
          obtain ⟨cupDom, cupCod⟩ := stringCupArity_of_isCupAtom_true atom isCupHead
          exact AllCupArity.cons cupDom cupCod (stringAllCupArity_of_allCups rest allCupsTrue)

/-! ## The Piece-I block extractor at the three-generator seed -/

/-- ★ **The string Piece-I block extractor.**  A string spine that the `Bool` fold classifies as a valley
(`isCapThenCupValley SpineAtom.isCupAtom spine = true`) splits CONCRETELY as `capBlock ++ cupBlock` with typed
arity: `AllCapArity capBlock` (leading caps) and `AllCupArity cupBlock` (the cup run from the first cup on).  This
is the presentation the whole Piece-II tail consumes.  Structural induction following the valley predicate's own
recursion; the tag→arity coincidence is exact at the seed (`adjointTripleSpineAtom_isCupOrCap`).  Byte-identical to
the adjunction's `spineValley_blockSplit` modulo the signature tokens — colour-blind, no length-rigidity. -/
theorem stringSpineValley_blockSplit
    {overallSource overallTarget : adjointTripleGraph.Mode} :
    (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)) →
    isCapThenCupValley SpineAtom.isCupAtom spine = true →
    ∃ (capBlock cupBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)),
      spine = capBlock ++ cupBlock ∧ AllCapArity capBlock ∧ AllCupArity cupBlock
  | [], _ => ⟨[], [], rfl, AllCapArity.nil, AllCupArity.nil⟩
  | atom :: rest, isValley => by
      dsimp only [isCapThenCupValley] at isValley
      cases isCupHead : SpineAtom.isCupAtom atom with
      | true =>
          rw [isCupHead] at isValley
          obtain ⟨cupDom, cupCod⟩ := stringCupArity_of_isCupAtom_true atom isCupHead
          exact ⟨[], atom :: rest, rfl, AllCapArity.nil,
            AllCupArity.cons cupDom cupCod (stringAllCupArity_of_allCups rest isValley)⟩
      | false =>
          rw [isCupHead] at isValley
          obtain ⟨capBlock, cupBlock, splitEq, capArity, cupArity⟩ :=
            stringSpineValley_blockSplit rest isValley
          obtain ⟨capDom, capCod⟩ := stringCapArity_of_isCupAtom_false atom isCupHead
          refine ⟨atom :: capBlock, cupBlock, ?_, AllCapArity.cons capDom capCod capArity, cupArity⟩
          rw [splitEq]
          rfl

/-! ## Tier-D structural fact — an empty source boundary forces an empty cap block -/

/-- ★ **Empty source ⇒ empty cap block** (the Tier-D case-(a) first move).  A pure-cap block boundary-chained at
width `0` is empty: a cap consumes two bottom wires, so its source boundary width is
`leftContext + 2 + rightContext ≥ 2 > 0`, impossible at boundary `0`.  Colour-blind arity + boundary-chain
arithmetic; the three-generator analog of `capBlockEmpty_ofSourceZero`. -/
theorem stringCapBlockEmpty_ofSourceZero
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (capBlock : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (capPure : AllCapArity capBlock) (chained : SpineBoundaryChained 0 capBlock) :
    capBlock = [] := by
  cases capBlock with
  | nil => rfl
  | cons headAtom rest =>
      cases capPure with
      | cons hasCapDomArity _hasCapCodArity _restAllCap =>
          obtain ⟨headFires, _tailChained⟩ := spineBoundaryChained_tail chained
          have contra : headAtom.leftContext.length + headAtom.rightContext.length + 2 = 0 := by
            have domForm : headAtom.domBoundaryLength
                = headAtom.leftContext.length + headAtom.rightContext.length + 2 := by
              dsimp only [SpineAtom.domBoundaryLength]
              rw [hasCapDomArity,
                Nat.add_right_comm headAtom.leftContext.length 2 headAtom.rightContext.length]
            rw [← domForm]; exact headFires
          exact Nat.noConfusion contra

/-! ## The three named colour-keyed sub-producers -/

/-- ★ The **width-0 pure-cup determinacy** sub-producer (Tier-D case (a)'s residual).  Two boundary-chained pure-cup
string spines over the width-`0` bottom boundary with EQUAL `matchingOfSpineList 0` are `SpineTraceEquiv`.  Stated
at the `matchingOf` (= `.diagram`) level so it is exactly the consumer interface the empty-source dispatcher needs.
The string analog of `WidthZeroPureCupDeterminacy`; genuinely colour-KEYED (the width-0 sort reads cup species off
the fixed top boundary, not through lengths), so NOT a token-swap of the adjunction's discharged version.

**★ ADJUDICATION (FC-3 r12, B1): this bare Prop is TRUE by FORCING — not refutable.**  A counterexample would need
two width-0 pure-cup spines with EQUAL matching but DIFFERENT top words.  None exists: a cup's codomain is FORCED by
its endpoint mode (`stringBaseCup_codForced` gives `F·G` at `base`, `stringTipCup_codForced` gives `G·H` at `tip`,
`StringWidthZeroForcingAdjudication`), and the matching pins each chord's endpoint mode, so the top word is a
well-defined function of the matching — equal matching forces equal top word.  The earlier `(H·G, G·H)` candidate is
a category error, directly refuted (`stringNoCupHasCodHG` / `stringNoCupHasCodGF`: `H·G`, `G·F` are CAP domains, never
cup cods; `H·G : base ⟶ base` and `G·H : tip ⟶ tip` are not even parallel).  This definition is therefore KEPT
VERBATIM (adjudicated true); the r12 strengthening `StringWidthZeroPureCupDeterminacyShared` below is a plumbing
convenience (the caller supplies its `targetPath` as the shared top word the last-cup pin consumes — cheaper than the
forcing lemma), NOT a soundness fix.  The FULL matching-to-top-word reconstruction (the width-0 SORT) remains r13+. -/
def StringWidthZeroPureCupDeterminacy : Prop :=
  ∀ {overallSource overallTarget : adjointTripleGraph.Mode}
    (cupFirst cupSecond : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)),
    AllCupArity cupFirst → AllCupArity cupSecond →
    SpineBoundaryChained 0 cupFirst → SpineBoundaryChained 0 cupSecond →
    matchingOfSpineList 0 cupFirst = matchingOfSpineList 0 cupSecond →
    SpineTraceEquiv adjointTripleModeSignature cupFirst cupSecond

/-- ★ The **mid-width-0 valley determinacy** sub-producer (Tier-D case (b)'s residual).  Two whole VALLEY string
cells with equal boundary `matchingOf`, POSITIVE source width, and mid-width `0` (`survivorTopTotal (matchingOf
valleyA) = 0`, the cap block consuming every bottom wire) are `SpineTraceEquiv`.  The string analog of
`MidZeroValleyTraceEquiv`; colour-keyed (needs the cap-side sort + width-0 cup determinacy). -/
def StringMidZeroValleyTraceEquiv : Prop :=
  ∀ {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (valleyA valleyB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath),
    isCapThenCupValley SpineAtom.isCupAtom valleyA.spine = true →
    isCapThenCupValley SpineAtom.isCupAtom valleyB.spine = true →
    matchingOf valleyA = matchingOf valleyB →
    0 < sourcePath.length →
    survivorTopTotal (matchingOf valleyA) = 0 →
    SpineTraceEquiv adjointTripleModeSignature valleyA.spine valleyB.spine

/-- ★ The **doubly-positive valley trace-equivalence** sub-producer (the main branch).  Two whole VALLEY string
cells with equal boundary `matchingOf`, POSITIVE source width, and POSITIVE mid-width (`0 < survivorTopTotal
(matchingOf valleyA)`, the through-strand count) are `SpineTraceEquiv`.  The string analog of the adjunction's
`cellValleyTraceEquiv_ofPositive` (there DISCHARGED via `valleysWithEqualMatching_spineTraceEquiv`); at the string
it is colour-keyed — its `pureCupSpine_sort` / `pureCapSpine_sort` core reads atom species off the boundary
labels, not lengths — so it is NAMED here as the primary standing obligation. -/
def StringCellValleyTraceEquivPositive : Prop :=
  ∀ {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (valleyA valleyB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath),
    isCapThenCupValley SpineAtom.isCupAtom valleyA.spine = true →
    isCapThenCupValley SpineAtom.isCupAtom valleyB.spine = true →
    matchingOf valleyA = matchingOf valleyB →
    0 < sourcePath.length →
    0 < survivorTopTotal (matchingOf valleyA) →
    SpineTraceEquiv adjointTripleModeSignature valleyA.spine valleyB.spine

/-! ## Case (a) — an empty source boundary reduces to the width-0 cup brick -/

/-- ★ **Tier-D case (a), FULLY PROVED from `StringWidthZeroPureCupDeterminacy`.**  When `sourcePath.length = 0`,
both valleys' cap blocks are empty (`stringCapBlockEmpty_ofSourceZero`), so the two whole spines ARE their cup
suffixes — pure cups chained at width `0` — and the whole-boundary `matchingOf` equality re-reads as a
`matchingOfSpineList 0` equality of the cup suffixes.  The width-0 pure-cup determinacy then delivers the
`SpineTraceEquiv`.  Token-swap of the adjunction's `degenerateEmptySource_of_widthZero`. -/
theorem stringDegenerateEmptySource_of_widthZero
    (widthZero : StringWidthZeroPureCupDeterminacy)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (valleyA valleyB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (isValleyA : isCapThenCupValley SpineAtom.isCupAtom valleyA.spine = true)
    (isValleyB : isCapThenCupValley SpineAtom.isCupAtom valleyB.spine = true)
    (matchingEq : matchingOf valleyA = matchingOf valleyB)
    (sourceZero : sourcePath.length = 0) :
    SpineTraceEquiv adjointTripleModeSignature valleyA.spine valleyB.spine := by
  obtain ⟨capA, cupA, splitA, capPureA, cupPureA⟩ := stringSpineValley_blockSplit valleyA.spine isValleyA
  obtain ⟨capB, cupB, splitB, capPureB, cupPureB⟩ := stringSpineValley_blockSplit valleyB.spine isValleyB
  have chained0A : SpineBoundaryChained 0 (capA ++ cupA) := by
    have wholeChainedA : SpineBoundaryChained sourcePath.length (capA ++ cupA) := by
      rw [← splitA]; exact valleyA.spineBoundaryChained_spine
    rw [sourceZero] at wholeChainedA; exact wholeChainedA
  have chained0B : SpineBoundaryChained 0 (capB ++ cupB) := by
    have wholeChainedB : SpineBoundaryChained sourcePath.length (capB ++ cupB) := by
      rw [← splitB]; exact valleyB.spineBoundaryChained_spine
    rw [sourceZero] at wholeChainedB; exact wholeChainedB
  have capEmptyA : capA = [] :=
    stringCapBlockEmpty_ofSourceZero capA capPureA (spineBoundaryChained_prefix_ofAppend capA cupA 0 chained0A)
  have capEmptyB : capB = [] :=
    stringCapBlockEmpty_ofSourceZero capB capPureB (spineBoundaryChained_prefix_ofAppend capB cupB 0 chained0B)
  have cupChained0A : SpineBoundaryChained 0 cupA := by rw [capEmptyA] at chained0A; exact chained0A
  have cupChained0B : SpineBoundaryChained 0 cupB := by rw [capEmptyB] at chained0B; exact chained0B
  have matchCupEq : matchingOfSpineList 0 cupA = matchingOfSpineList 0 cupB := by
    have eqA : matchingOf valleyA = matchingOfSpineList 0 cupA := by
      show matchingOfSpineList sourcePath.length valleyA.spine = matchingOfSpineList 0 cupA
      rw [sourceZero, splitA, capEmptyA]; rfl
    have eqB : matchingOf valleyB = matchingOfSpineList 0 cupB := by
      show matchingOfSpineList sourcePath.length valleyB.spine = matchingOfSpineList 0 cupB
      rw [sourceZero, splitB, capEmptyB]; rfl
    rw [← eqA, ← eqB]; exact matchingEq
  rw [splitA, capEmptyA, splitB, capEmptyB]
  exact widthZero cupA cupB cupPureA cupPureB cupChained0A cupChained0B matchCupEq

/-! ## The FULL three-way split -/

/-- ★★ **The FULL cell-level Piece-II three-way split.**  `StringCellValleyTraceEquiv` — two whole VALLEY string
cells with equal boundary `matchingOf` have `SpineTraceEquiv` spines — follows from the THREE named colour-keyed
sub-producers: the case split on `Nat.eq_zero_or_pos sourcePath.length` sends the empty-source branch to
`stringDegenerateEmptySource_of_widthZero` (from `StringWidthZeroPureCupDeterminacy`); on positive source, the case
split on `Nat.eq_zero_or_pos (survivorTopTotal (matchingOf valleyA))` sends the mid-`0` branch to
`StringMidZeroValleyTraceEquiv` and the doubly-positive branch to `StringCellValleyTraceEquivPositive`.  This
SHARPENS the monolithic Piece-II residual into three, PROVING the colour-blind dispatching skeleton and the case-(a)
reducer.  Token-swap of the adjunction's `cellValleyTraceEquiv_of_widthZero_of_midZero` (whose positive branch was
discharged; ours stays a named residual). -/
theorem stringCellValleyTraceEquiv_of_widthZero_of_midZero
    (widthZero : StringWidthZeroPureCupDeterminacy) (midZero : StringMidZeroValleyTraceEquiv)
    (positive : StringCellValleyTraceEquivPositive) : StringCellValleyTraceEquiv := by
  intro sourceMode targetMode sourcePath targetPath valleyA valleyB isValleyA isValleyB matchingEq
  cases Nat.eq_zero_or_pos sourcePath.length with
  | inl sourceZero =>
      exact stringDegenerateEmptySource_of_widthZero widthZero valleyA valleyB isValleyA isValleyB
        matchingEq sourceZero
  | inr sourcePos =>
      cases Nat.eq_zero_or_pos (survivorTopTotal (matchingOf valleyA)) with
      | inl midZeroA =>
          exact midZero valleyA valleyB isValleyA isValleyB matchingEq sourcePos midZeroA
      | inr midPos =>
          exact positive valleyA valleyB isValleyA isValleyB matchingEq sourcePos midPos

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the Piece-II THREE-WAY SPLIT is shipped; `StringCellValleyTraceEquiv` is SHARPENED into three
named colour-keyed sub-producers, with the colour-blind skeleton + case (a) PROVED.**  The block extractor
(`stringSpineValley_blockSplit` and its three arity read-offs), the empty-source cap collapse
(`stringCapBlockEmpty_ofSourceZero`), the case-(a) reducer (`stringDegenerateEmptySource_of_widthZero`, FULLY proved
from `StringWidthZeroPureCupDeterminacy`), and the full split (`stringCellValleyTraceEquiv_of_widthZero_of_midZero`)
all port the adjunction's `SpineValleyCellDegenerate` skeleton BYTE-IDENTICAL modulo the signature tokens — the
recon's "OUTER assembly transplant verbatim" verdict, confirmed: every step is colour-blind (reads cup-vs-cap arity,
`matchingOfSpineList`, `survivorTopTotal`, boundary-chain arithmetic — never `F`/`G`/`H`), riding the shipped
four-generator classification `adjointTripleSpineAtom_isCupOrCap`.

  What this marker does NOT close (no gate flag flips): the THREE named sub-producers
  `StringWidthZeroPureCupDeterminacy`, `StringMidZeroValleyTraceEquiv`, `StringCellValleyTraceEquivPositive` are the
  SORT + arc↔matching CORE, genuinely colour-KEYED — the adjunction discharges its analogs
  (`widthZeroPureCupDeterminacy_holds`, `midZeroCupBlockReconstruct_holds`, `cellValleyTraceEquiv_ofPositive`)
  through `pureCupSpine_sort` / `pureCapSpine_sort` / `cupRestrict_reconstructs`, which read atom species through
  LENGTHS (`adjunctionPath_eq_of_length_eq`), FALSE at the string (`string_left_ne_coLeft`).  The colour-aware
  re-derivation reads species off the boundary labels via the shipped pin `stringCupCod_ne_capDom` — a multi-round
  arc.  So `StringCellValleyTraceEquiv` (`StringMatchingValleyDescent`) and hence
  `fxString_hasAdjointTripleCompleteness` (`StringMatchingCompleteness`) stay `false`, honestly — the monolithic
  residual now FACTORED into three named colour-keyed bricks, with the colour-blind skeleton discharged.  `= true`. -/
def fxString_hasValleyDegenerateSplit : Bool := true

end FX1Poly.Polygraph

import FX1Poly.Tier0.Mode.FreeTwoCellModel

/-! # mode-8 — the free 2-category on a computad + the 2-cell word problem (wired to the ωcE engine)

A **computad** (Street) / **polygraph** (Burroni) presents a higher category by generators per dimension.  The
mode axis already HAS the 2-computad: `mode-0`'s `ModeSignature` IS one (modes = 0-cells, modality generators =
1-cells, `twoCell` generators = 2-cells between parallel 1-paths), and `mode-1`/`mode-3` built its free
2-category — 1-cells = `ModalityPath` (free category on the quiver), 2-cells = `RawTwoCellExpr` (free 2-cells)
modulo the `TwoCellStep` 3-polygraph (`TwoCellConv`).  This file names the computad explicitly and connects its
WORD PROBLEM to the machinery that already decides word problems in this kernel: the **ωcE / Makkai leg**
(`FX1Poly/Tier0/OmegacE/`, Path B), NOT a reinvented measure.

## The word problem is already an engine — reuse it, do not rebuild it

`FX1Poly/Tier0/OmegacE/` ships, generically and zero-axiom:

  * `OmegacEWord` — finite words (lists of generators) with a propext-free `DecidableEq`, and (in
    `WordFreeMonoid`) the FREE MONOID laws `append_assoc` / `empty_append` / `append_empty` — i.e. THE
    dimension-1 free one-object category, the arena every word problem lives in.
  * `WordProblem.ConvertibleModulo.decidableOfNormalizer` — given confluence + a terminating `WordNormalizer`,
    convertibility modulo a rewrite system is DECIDABLE (normalize both, compare).  The Makkai word problem
    decided by a CONVERGENT presentation — the Path-B twin of the term layer's
    `Conv.decidableOfStronglyNormalizing`.
  * `ReducerNormalizer.WordReducer.toNormalizer` (termination + a reducer ⟹ a normalizer) and concrete
    instances (`EmptySystem.emptyWordNormalizer`, `IdempotentReducer.idempotentWordNormalizer`) that exercise
    the engine end-to-end on real systems.

So the free 2-category-on-a-computad word problem is decided BY that engine once the computad's cells are
presented as ωcE words and the mode 3-polygraph is shown convergent.

## What this file ships (each piece zero-axiom)

  * **`Computad`** — the 2-computad framing (`= ModeSignature`) + accessors (`zeroCells` / `oneCellGenerator`
    / `twoCellGenerator`) and the free 2-category (`freeOneCell = ModalityPath`, `freeTwoCell = RawTwoCellExpr`).
  * **`ModalityPath.length_composePath`** — the dimension-1 free-monoid WORD-LENGTH homomorphism
    `length (p ++ q) = length p + length q`, the mode-axis twin of OmegacE `OmegacEWord.length_append`: the
    computad's 1-cells form the free monoid, the same arena `WordFreeMonoid` builds for the ωcE words.
  * **`RawTwoCellExpr.generatorCount`** + **`TwoCellStep.generatorCount_eq`** / **`TwoCellConv.generatorCount_eq`**
    — the dimension-2 WORD LENGTH (number of generator firings) is a CONVERSION INVARIANT: well-defined on the
    `TwoCellConv` class, the mode twin of the ωcE word `length` being a rewrite invariant.  It is preserved even
    by the DEFERRED interchange law (interchange permutes generators, never creates them), so it is a genuine
    invariant of the FULL 2-category equivalence.
  * **`TwoCellConv.not_of_generatorCount_ne`** — hence a SOUND distinguisher: 2-cells of different word length
    are not convertible (a computable partial decision, the necessary-condition half of the word problem).

## What is DEFERRED (recorded by `= false` markers) — both into the existing ωcE engine

  * the mode-computad → ωcE-word ENCODING (the "FX-Step ↔ ωcE-rewrite bridge" the `WordProblem` docstring flags
    as the separate connecting atom) that lets `decidableOfNormalizer` literally decide the mode 2-cell word
    problem (`hasComputadToOmegacEEncoding`);
  * the CONVERGENT ωcE presentation of the mode 3-polygraph (confluence + a terminating `WordNormalizer` for the
    mode 2-cells — the input the engine consumes), which is `mode-9`'s convergence
    (`hasConvergentTwoCellPresentation`).

Once both land, `DecidableTwoCellConvFor` (`mode-3`'s interface) is inhabited by the OmegacE engine — no new
decision procedure is owed.

Zero external dependencies beyond the mode-3 core (the ωcE engine is referenced, not imported — the encoding is
the deferred bridge).  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## The 2-computad framing -/

/-- A **2-computad** — the generating data of the free 2-category, which for the mode axis IS a `ModeSignature`:
0-cell generators (modes), 1-cell generators (modalities), 2-cell generators (`twoCell`, between parallel
1-paths).  Naming it makes the "free 2-category on a computad" of `mode-8` explicit. -/
abbrev Computad := ModeSignature

/-- The 0-cells (objects) of a computad — the modes. -/
abbrev Computad.zeroCells (computad : Computad) : Type := computad.graph.Mode

/-- The 1-cell generators of a computad between two 0-cells — the modality generators. -/
abbrev Computad.oneCellGenerator (computad : Computad)
    (sourceCell targetCell : computad.graph.Mode) : Type :=
  computad.graph.Modality sourceCell targetCell

/-- The 2-cell generators of a computad between a parallel pair of 1-cells. -/
abbrev Computad.twoCellGenerator (computad : Computad)
    {sourceCell targetCell : computad.graph.Mode}
    (sourceOneCell targetOneCell : ModalityPath computad.graph sourceCell targetCell) : Type :=
  computad.twoCell sourceOneCell targetOneCell

/-- The free 1-cells of the computad's free 2-category — paths of 1-cell generators (the free category on the
quiver; the dimension-1 free-monoid words). -/
abbrev Computad.freeOneCell (computad : Computad)
    (sourceCell targetCell : computad.graph.Mode) : Type :=
  ModalityPath computad.graph sourceCell targetCell

/-- The free 2-cells of the computad's free 2-category — `RawTwoCellExpr` over the signature, modulo the
`TwoCellStep` 3-polygraph (`TwoCellConv`). -/
abbrev Computad.freeTwoCell (computad : Computad)
    {sourceCell targetCell : computad.graph.Mode}
    (sourceOneCell targetOneCell : ModalityPath computad.graph sourceCell targetCell) : Type :=
  RawTwoCellExpr computad sourceOneCell targetOneCell

/-! ## Dimension 1: the free-monoid word-length homomorphism (the ωcE `WordFreeMonoid` twin) -/

/-- ★ **The dimension-1 word-length homomorphism**: the length of a composite 1-cell is the sum of the lengths
— `length (composePath first second) = first.length + second.length`.  The computad's 1-cells form the FREE
MONOID under `composePath` (identity `nil`), and `length` is the monoid homomorphism to `(Nat, +, 0)`.  This is
the mode-axis twin of OmegacE `OmegacEWord.length_append` (`WordFreeMonoid`) — the same dimension-1 free-monoid
word arena, here over a general computad's 1-generators.  Structural induction on the first path, `Nat.succ_add`
for the cons step (propext-free, exactly as the ωcE `length_append`). -/
theorem ModalityPath.length_composePath {graph : ModeGraph}
    {sourceMode middleMode targetMode : graph.Mode}
    (first : ModalityPath graph sourceMode middleMode)
    (second : ModalityPath graph middleMode targetMode) :
    (composePath first second).length = first.length + second.length := by
  induction first with
  | nil _ => exact (Nat.zero_add second.length).symm
  | cons _ rest inductionHypothesis =>
      dsimp only [composePath, ModalityPath.length]
      rw [inductionHypothesis, Nat.succ_add]

/-! ## Dimension 2: the word length as a conversion invariant -/

/-- The **word length of a free 2-cell** — the number of generator firings (`gen` counts 1, `id` counts 0,
composites and whiskerings pass through).  This is the dimension-2 word length: the ωcE-word `length` analog for
the mode 2-cells.  Full five-case match, constant `Nat` motive — propext-free. -/
def RawTwoCellExpr.generatorCount {signature : ModeSignature} :
    {sourceMode targetMode : signature.graph.Mode} →
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode} →
    RawTwoCellExpr signature sourcePath targetPath → Nat
  | _, _, _, _, .gen _ => 1
  | _, _, _, _, .id _ => 0
  | _, _, _, _, .vcomp cellAlpha cellBeta => cellAlpha.generatorCount + cellBeta.generatorCount
  | _, _, _, _, .whiskerLeft _ cellBeta => cellBeta.generatorCount
  | _, _, _, _, .whiskerRight _ cellBeta => cellBeta.generatorCount

/-- ★ **Word length is invariant under one 3-cell rewrite.**  Every oriented strict-2-category law preserves the
generator count: identity removal drops a count-0 factor, re-association and whisker-distribution rearrange the
sum, and the four congruence cases propagate the inductive hypothesis.  By induction on the step
(`Nat.zero_add` / `Nat.add_assoc` for the two reassociating arms — both propext-free, as used throughout the ωcE
`Word` layer). -/
theorem TwoCellStep.generatorCount_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStep signature expr reduct) : expr.generatorCount = reduct.generatorCount := by
  induction step with
  | vcompIdLeft cellAlpha => exact Nat.zero_add cellAlpha.generatorCount
  | vcompIdRight _ => rfl
  | vcompAssoc cellAlpha cellBeta cellGamma =>
      exact Nat.add_assoc cellAlpha.generatorCount cellBeta.generatorCount cellGamma.generatorCount
  | whiskerLeftId _ _ => rfl
  | whiskerRightId _ _ => rfl
  | whiskerLeftVcomp _ _ _ => rfl
  | whiskerRightVcomp _ _ _ => rfl
  | vcompCongrLeft _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.generatorCount]; rw [inductionHypothesis]
  | vcompCongrRight _ _ inductionHypothesis =>
      dsimp only [RawTwoCellExpr.generatorCount]; rw [inductionHypothesis]
  | whiskerLeftCongr _ _ inductionHypothesis => exact inductionHypothesis
  | whiskerRightCongr _ _ inductionHypothesis => exact inductionHypothesis

/-- ★ **Word length is invariant under 2-cell convertibility** — well-defined on the `TwoCellConv` class.  By
induction on the conversion: a single step is `generatorCount_eq`, reflexivity is `rfl`, symmetry / transitivity
chain via `Eq.symm` / `Eq.trans`.  (Propext-clean: induction on the indexed `Prop` relation, exactly the
`mode-4` congruence-by-induction pattern.) -/
theorem TwoCellConv.generatorCount_eq {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature expr reduct) : expr.generatorCount = reduct.generatorCount := by
  induction conv with
  | ofStep step => exact step.generatorCount_eq
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis

/-- ★ The **sound word-length distinguisher**: free 2-cells of different word length are NOT convertible — the
computable necessary-condition half of the 2-cell word problem (the full decision is the deferred ωcE-engine
instantiation).  Contrapositive of `generatorCount_eq`. -/
theorem TwoCellConv.not_of_generatorCount_ne {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {expr reduct : RawTwoCellExpr signature sourcePath targetPath}
    (countsDiffer : expr.generatorCount ≠ reduct.generatorCount) :
    ¬ TwoCellConv signature expr reduct :=
  fun conv => countsDiffer conv.generatorCount_eq

/-- Smoke: the adjunction unit has word length 1 (one generator firing), and the composite `unit ⊟ id` also has
word length 1 — CONSISTENT with their convertibility (`adjunctionUnitThenId_conv_unit`), as
`generatorCount_eq` demands. -/
theorem adjunctionUnitThenId_generatorCount_eq_unit :
    adjunctionUnitThenId.generatorCount = adjunctionUnitTwoCell.generatorCount := rfl

/-! ## The word-problem interface (inhabited by the ωcE engine) -/

/-- The **free 2-category's 2-cell word problem** at a computad — exactly `mode-3`'s `DecidableTwoCellConvFor`
interface.  It is INHABITED by the OmegacE `ConvertibleModulo.decidableOfNormalizer` engine once the two
deferred wires land (the encoding + the convergent presentation); no new decision procedure is owed at the mode
axis. -/
abbrev Computad.twoCellWordProblem (computad : Computad) : Type :=
  DecidableTwoCellConvFor computad

/-! ## Honesty markers -/

/-- **Honesty marker.**  The mode-computad → ωcE-word ENCODING — the "FX-Step ↔ ωcE-rewrite bridge" the
OmegacE `WordProblem` docstring flags as the separate connecting atom — that would let
`OmegacEWord.ConvertibleModulo.decidableOfNormalizer` literally decide the mode 2-cell word problem, is
deferred.  `= false`. -/
def fxMode_hasComputadToOmegacEEncoding : Bool := false

/-- **Honesty marker.**  The CONVERGENT ωcE presentation of the mode 3-polygraph — confluence plus a terminating
`WordNormalizer` for the mode 2-cells, the input the ωcE engine consumes — is `mode-9`'s convergence (Gratzer's
coherence hurdle), deferred.  `= false`. -/
def fxMode_hasConvergentTwoCellPresentation : Bool := false

end FX1Poly.Tier0

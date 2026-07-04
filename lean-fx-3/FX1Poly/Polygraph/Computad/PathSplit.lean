import FX1Poly.Polygraph.Computad.WordProblem

/-! # PathSplit — factoring a 1-cell at a length index (ARC-2b splitting kit)

The realized disjoint-window atom swap must EXHIBIT the whisker factorization the
`SpineAtomSwap` constructor demands: given two adjacent chained atoms with disjoint wire
windows, the left atom's right context factors as `inert · generatorDom · rightAccumulator`
at an index computed from the window arithmetic.  This file ships the generic factoring
substrate: every modality path splits at every in-range length index into a prefix and a
suffix that recompose on the nose.

  * `PathSplit` — the split certificate: middle mode, prefix, suffix, the recomposition
    equation, and the prefix-length pin;
  * `splitPathAt` — the split constructor, by structural recursion on the path (a zero
    index splits off the empty prefix definitionally; a successor index peels the head
    modality onto the inner split's prefix);
  * `PathSplit.lengthPartition` — the two parts partition the path's length (via the
    dimension-1 word-length homomorphism).

At the walking adjunction, ARC-1 rigidity (`adjunctionPath_eq_of_length_eq`) makes any two
splits at the same index EQUAL — the kit's existence half is generic, the uniqueness half
is the seed's rigidity.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The split certificate**: a factorization of `path` at length index `splitIndex` — a
middle mode, a prefix landing there, a suffix continuing on, the recomposition equation,
and the pin that the prefix carries exactly `splitIndex` modalities. -/
structure PathSplit {graph : ModeGraph} {sourceMode targetMode : graph.Mode}
    (path : ModalityPath graph sourceMode targetMode) (splitIndex : Nat) where
  /-- The mode the prefix lands on (and the suffix departs from). -/
  middleMode : graph.Mode
  /-- The first `splitIndex` modalities of the path. -/
  prefixPath : ModalityPath graph sourceMode middleMode
  /-- The remaining modalities of the path. -/
  suffixPath : ModalityPath graph middleMode targetMode
  /-- The parts recompose to the split path. -/
  splitComposes : composePath prefixPath suffixPath = path
  /-- The prefix carries exactly the split index's worth of modalities. -/
  prefixLengthMatches : prefixPath.length = splitIndex

/-- **Split a path at an in-range length index.**  Structural recursion on the path: index
zero splits off the empty prefix (recomposition is definitional — `composePath` recurses on
its first argument); a successor index peels the head modality onto the inner split's
prefix (recomposition by `congrArg` on the cons).  The empty path admits only the zero
index (the bound is refuted by `nomatch`). -/
def splitPathAt {graph : ModeGraph} :
    {sourceMode targetMode : graph.Mode} →
    (path : ModalityPath graph sourceMode targetMode) →
    (splitIndex : Nat) →
    splitIndex ≤ path.length →
    PathSplit path splitIndex
  | sourceMode, _, path, 0, _ =>
      { middleMode := sourceMode,
        prefixPath := ModalityPath.nil sourceMode,
        suffixPath := path,
        splitComposes := rfl,
        prefixLengthMatches := rfl }
  | _, _, ModalityPath.cons headModality restPath, restIndex + 1, splitInRange =>
      let innerSplit := splitPathAt restPath restIndex (Nat.le_of_succ_le_succ splitInRange)
      { middleMode := innerSplit.middleMode,
        prefixPath := ModalityPath.cons headModality innerSplit.prefixPath,
        suffixPath := innerSplit.suffixPath,
        splitComposes := congrArg (ModalityPath.cons headModality) innerSplit.splitComposes,
        prefixLengthMatches := congrArg (fun partLength => partLength + 1)
          innerSplit.prefixLengthMatches }
  | _, _, ModalityPath.nil _, _ + 1, splitInRange => nomatch splitInRange

/-- The two parts of a split partition the path's length — the recomposition equation read
through the dimension-1 word-length homomorphism. -/
theorem PathSplit.lengthPartition {graph : ModeGraph} {sourceMode targetMode : graph.Mode}
    {path : ModalityPath graph sourceMode targetMode} {splitIndex : Nat}
    (split : PathSplit path splitIndex) :
    split.prefixPath.length + split.suffixPath.length = path.length := by
  have composedLengths := congrArg ModalityPath.length split.splitComposes
  rw [ModalityPath.length_composePath] at composedLengths
  exact composedLengths

/-! ## Honesty marker -/

/-- **Honesty marker — the path splitting kit is SHIPPED (ARC-2b brick i).**  Every 1-cell
factors at every in-range length index (`splitPathAt`), with the recomposition equation and
the prefix-length pin carried in the `PathSplit` certificate, and the parts partitioning
the length (`PathSplit.lengthPartition`).  NOT yet shipped: the realized disjoint-window
atom swap that consumes this factorization (ARC-2b brick ii) and the cup/cap peel itself
(brick iii) — the sole residual of the seed reconstruction after the chained assembly.
`= true`. -/
def fxMode_hasModalityPathSplitting : Bool := true

end FX1Poly.Polygraph

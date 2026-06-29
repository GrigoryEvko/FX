import FX1Poly.Tier0.Mode.FreeTwoCellSpineTraceDecision

/-! # mode-3 floor — the planar-arc RECONSTRUCTION (Joyal-Street completeness), reduced to one geometric residual

`FreeTwoCellSpineTraceDecision` shipped the **full planar-arc structure** `arcStructureOf` together with a
decision `decidableTwoCellConvFull_of` / `decidableSpineTraceEquiv_of` GATED on two residuals.  This file
discharges the COMBINATORIAL half of the second one — the **reconstruction** (Joyal-Street completeness, the
YES-direction the parent's `fxMode_hasArcStructureReconstruction` names):

  `arcStructureOfSpineList n firstList = arcStructureOfSpineList n secondList → SpineTraceEquiv firstList secondList`.

## The mathematics, split honestly

The reconstruction is the Mazurkiewicz / trace-monoid COMPLETENESS theorem: two cup/cap event-words with the
same planar-arc structure record the same DEPENDENCY ORDER on the turnback events, hence are two linearizations
of one partial order, hence are connected by adjacent transpositions of INDEPENDENT (horizontally-disjoint)
events — a bubble-sort over the spine.  It factors cleanly into two halves:

  1. **The combinatorial half (PROVED here).**  Any two linearizations of one dependency order are connected by
     adjacent independent swaps.  We prove this twice:
       * abstractly — `AdjacentSwapEquiv.bubbleFront` (an event independent of an entire prefix bubbles to the
         front through adjacent independent swaps) plus `adjacentSwapEquiv_of_traceMatched` (the operational
         head-extraction matching assembles into full swap-equivalence); this is the textbook Mazurkiewicz
         connectivity engine over a generic identity-preserving independence relation;
       * concretely — `spineTraceEquiv_of_traceMatched` runs the SAME head-extraction induction directly on the
         CONTEXT-SHIFTING Godement closure `SpineTraceEquiv`, where each realized bubble is supplied as a
         `SpineTraceEquiv ys (atom :: matched)` witness (the Godement step transposes whiskered blocks, NOT bare
         atoms, so the abstract identity-preserving model cannot be plugged in verbatim — only its induction
         shape transfers).

  2. **The geometric half (the SOLE residual).**  Reading `arcStructureOf` back as the dependency order and
     realizing each head extraction as a genuine `SpineGodementStep` chain — packaged as the single obligation
     `arcStructureOfSpineList n xs = arcStructureOfSpineList n ys → SpineTraceMatched signature xs ys`.
     `arcStructureReconstruction_spine_of_matching` / `_cell_of_matching` consume EXACTLY this and land the full
     reconstruction; until it discharges, the reconstruction stays GATED on it (`fxMode_hasArcHeadExtractionMatching
     = false`), with everything else proved.

## What is honest-DEFERRED

  * the per-head geometric realizability `arcStructureOfSpineList eq → SpineTraceMatched` —
    `fxMode_hasArcHeadExtractionMatching = false`;
  * consequently the assembled `arcStructureReconstruction_*` stay GATED on that one input
    (`fxMode_hasArcStructureReconstructionAssembled = false`); the parent's
    `fxMode_hasArcStructureReconstruction` correspondingly stays `false`.

The reconstruction is proved by STRUCTURAL INDUCTION on the matching / the spine list — never by `rfl` / `decide`
on the (kernel-`isDefEq`-heavy) parallel cells.

Raw Lean 4 + Init; structural recursion / induction only, no `propext` / `Quot.sound` / `Classical` / `sorry` /
`native_decide` / `omega` / `decide` on open goals / `WellFounded.fix` / leaky `List.append` lemmas (the only
`++` reductions used are the definitional `nil_append` / `cons_append`).  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

universe u

namespace FX1Poly.Tier0

/-! ## The abstract Mazurkiewicz connectivity engine

A generic identity-preserving independence relation `Indep` over a carrier `Elem`, its adjacent-swap equivalence,
and the connectivity theorem: any list reachable by head-extraction past independent prefixes is swap-equivalent.
This is the textbook trace-monoid connectivity, formalized zero-axiom — the combinatorial skeleton the geometric
reconstruction follows.  (It does NOT plug into `SpineTraceEquiv` verbatim, because the genuine Godement step
SHIFTS the whisker contexts of the transposed atoms rather than preserving their identity; only the induction
shape transfers, which §2 re-runs directly on the real objects.) -/

/-- `IndepAllWith Indep a front` — the event `a` is `Indep` of every event in the prefix `front`.  A cons-only
structural predicate (`True` / `And`), so it COMPUTES and stays propext-free (no `List.Mem` reasoning). -/
def IndepAllWith {Elem : Type u} (Indep : Elem → Elem → Prop) (subject : Elem) : List Elem → Prop
  | [] => True
  | head :: tail => Indep head subject ∧ IndepAllWith Indep subject tail

/-- **Adjacent-swap equivalence** of lists over an independence relation `Indep`: the reflexive-symmetric-
transitive, cons-congruent closure of transposing two ADJACENT independent head elements.  The abstract
(identity-preserving) model of `SpineTraceEquiv`. -/
inductive AdjacentSwapEquiv {Elem : Type u} (Indep : Elem → Elem → Prop) : List Elem → List Elem → Prop where
  /-- Reflexivity. -/
  | refl (elements : List Elem) : AdjacentSwapEquiv Indep elements elements
  /-- Transpose two adjacent independent head elements. -/
  | headSwap (first second : Elem) (rest : List Elem) :
      Indep first second → AdjacentSwapEquiv Indep (first :: second :: rest) (second :: first :: rest)
  /-- Symmetry. -/
  | symm {firstList secondList : List Elem} :
      AdjacentSwapEquiv Indep firstList secondList → AdjacentSwapEquiv Indep secondList firstList
  /-- Transitivity. -/
  | trans {firstList secondList thirdList : List Elem} :
      AdjacentSwapEquiv Indep firstList secondList → AdjacentSwapEquiv Indep secondList thirdList →
      AdjacentSwapEquiv Indep firstList thirdList
  /-- A head element passes through (an independent prefix of length one). -/
  | consCongr (head : Elem) {firstList secondList : List Elem} :
      AdjacentSwapEquiv Indep firstList secondList →
      AdjacentSwapEquiv Indep (head :: firstList) (head :: secondList)

/-- ★ **The bubbling engine.**  An event `subject` that is independent of an entire prefix `front` bubbles past
that whole prefix to the front, through a chain of adjacent independent swaps.  Structural induction on `front`:
the head swaps `subject` leftward past `front`'s head (`headSwap`), the tail bubbles by the inductive hypothesis
under a `consCongr`.  This is the heart of the Mazurkiewicz connectivity proof. -/
theorem AdjacentSwapEquiv.bubbleFront {Elem : Type u} (Indep : Elem → Elem → Prop) (subject : Elem) :
    ∀ (front : List Elem), IndepAllWith Indep subject front → ∀ (rest : List Elem),
      AdjacentSwapEquiv Indep (front ++ subject :: rest) (subject :: (front ++ rest)) := by
  intro front
  induction front with
  | nil => intro _ rest; exact AdjacentSwapEquiv.refl _
  | cons frontHead frontTail inductionHypothesis =>
      intro frontIndependent rest
      obtain ⟨headIndependent, tailIndependent⟩ := frontIndependent
      exact AdjacentSwapEquiv.trans
        (AdjacentSwapEquiv.consCongr frontHead (inductionHypothesis tailIndependent rest))
        (AdjacentSwapEquiv.headSwap frontHead subject (frontTail ++ rest) headIndependent)

/-- **Operational head-extraction matching** (abstract).  `TraceMatched Indep firstList secondList` witnesses
that `secondList` is a linearization reachable from `firstList` by repeatedly peeling `firstList`'s head out of
`secondList` past a prefix of events all independent of it.  This is the Mazurkiewicz "same dependency order"
data in induction-ready operational form. -/
inductive TraceMatched {Elem : Type u} (Indep : Elem → Elem → Prop) : List Elem → List Elem → Prop where
  /-- Both lists exhausted. -/
  | nil : TraceMatched Indep [] []
  /-- The head `subject` sits in `secondList` after an independent prefix `front`; the tails match. -/
  | cons (subject : Elem) (front : List Elem) {rest matched : List Elem} :
      IndepAllWith Indep subject front →
      TraceMatched Indep rest (front ++ matched) →
      TraceMatched Indep (subject :: rest) (front ++ subject :: matched)

/-- ★ **Abstract connectivity.**  A head-extraction matching assembles into full adjacent-swap equivalence:
induct on the matching, bubble the extracted head to the front (`bubbleFront`), recurse under a `consCongr`.
The textbook "two linearizations of one dependency order are swap-connected", proved zero-axiom. -/
theorem adjacentSwapEquiv_of_traceMatched {Elem : Type u} {Indep : Elem → Elem → Prop}
    {firstList secondList : List Elem} (traceMatch : TraceMatched Indep firstList secondList) :
    AdjacentSwapEquiv Indep firstList secondList := by
  induction traceMatch with
  | nil => exact AdjacentSwapEquiv.refl []
  | cons subject front frontIndependent _ inductionHypothesis =>
      exact (AdjacentSwapEquiv.consCongr subject inductionHypothesis).trans
        (AdjacentSwapEquiv.bubbleFront Indep subject front frontIndependent _).symm

/-! ## The head-extraction matching on the Godement closure (the real objects)

The same induction shape, transported onto `SpineTraceEquiv` — the reflexive-symmetric-transitive, cons-congruent
closure of the genuine context-shifting `SpineGodementStep`.  Here a single head extraction is the realized
bubble `SpineTraceEquiv ys (atom :: matched)`: the abstract `bubbleFront` cannot be reused (Godement transposes
whiskered BLOCKS, shifting the atoms' left/right contexts), so the realized bubbles are supplied as data, and
this assembly threads them. -/

/-- **Head-extraction matching on spines.**  `SpineTraceMatched firstList secondList` witnesses that `secondList`
is reachable from `firstList` by repeatedly extracting `firstList`'s head `atom` to the front of the matched
remainder via a realized `SpineTraceEquiv` bubble.  The faithful Godement-closure analogue of `TraceMatched`. -/
inductive SpineTraceMatched (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} :
    List (SpineAtom signature overallSource overallTarget) →
    List (SpineAtom signature overallSource overallTarget) → Prop where
  /-- Both spines exhausted. -/
  | nil : SpineTraceMatched signature [] []
  /-- The head `atom` bubbles to the front of `ys` (realized as a `SpineTraceEquiv`); the tails match. -/
  | cons (atom : SpineAtom signature overallSource overallTarget)
      {rest matched ys : List (SpineAtom signature overallSource overallTarget)} :
      SpineTraceEquiv signature ys (atom :: matched) →
      SpineTraceMatched signature rest matched →
      SpineTraceMatched signature (atom :: rest) ys

/-- ★ **The combinatorial half of the reconstruction, on the real objects.**  A spine head-extraction matching
assembles into a genuine `SpineTraceEquiv`: induct on the matching; the head congruence (`consCongr`) on the
recursively-matched tails, composed with the realized head bubble's symmetry, closes each step.  No realizability
is invented here — the per-head bubbles are the matching's data; this is purely the trace-algebra assembly. -/
theorem spineTraceEquiv_of_traceMatched {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (traceMatch : SpineTraceMatched signature firstList secondList) :
    SpineTraceEquiv signature firstList secondList := by
  induction traceMatch with
  | nil => exact SpineTraceEquiv.refl []
  | cons atom headBubble _ inductionHypothesis =>
      exact (SpineTraceEquiv.consCongr atom inductionHypothesis).trans headBubble.symm

/-! ## The reconstruction, reduced to the single geometric residual

`arcStructureReconstruction_spine_of_matching` is the YES-direction `arcStructureOfSpineList eq → SpineTraceEquiv`
the parent's `decidableSpineTraceEquiv_of` (`complete`) and `fxMode_hasArcStructureReconstruction` name — with
the entire combinatorial content discharged above, so the ONLY input it consumes is the geometric head-extraction
matching `matching` (arc-structure equality realized as a `SpineTraceMatched`).  The cell-level form follows by
the definitional `arcStructureOf cell = arcStructureOfSpineList sourcePath.length cell.spine`. -/

/-- ★ **Spine-level reconstruction, GATED on the geometric head-extraction matching.**  Given the residual
`matching` (equal arc structures yield a head-extraction matching — the dependency-order read-off and per-head
Godement realizability), equal arc structures give `SpineTraceEquiv` spines.  This is exactly the `complete`
input of `decidableSpineTraceEquiv_of`, with the trace-algebra fully proved. -/
theorem arcStructureReconstruction_spine_of_matching {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat)
    (matching : ∀ {firstList secondList : List (SpineAtom signature overallSource overallTarget)},
        arcStructureOfSpineList bottomCount firstList = arcStructureOfSpineList bottomCount secondList →
        SpineTraceMatched signature firstList secondList)
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (arcEqual : arcStructureOfSpineList bottomCount firstList = arcStructureOfSpineList bottomCount secondList) :
    SpineTraceEquiv signature firstList secondList :=
  spineTraceEquiv_of_traceMatched (matching arcEqual)

/-- ★ **Cell-level reconstruction, GATED on the same residual.**  Equal full planar-arc structures give
trace-equivalent spines.  Routes through the spine-level form (parallel cells share `sourcePath.length`, and
`arcStructureOf cell` is definitionally `arcStructureOfSpineList sourcePath.length cell.spine`).  Composed with
the spine→cell reconstruction (`fxMode_hasSpineTraceReconstruction`, the parent's other residual) this is the
`reconstruct` input of `decidableTwoCellConvFull_of`. -/
theorem arcStructureReconstruction_cell_of_matching {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (matching : ∀ {firstList secondList : List (SpineAtom signature sourceMode targetMode)},
        arcStructureOfSpineList sourcePath.length firstList = arcStructureOfSpineList sourcePath.length secondList →
        SpineTraceMatched signature firstList secondList)
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (arcEqual : arcStructureOf firstCell = arcStructureOf secondCell) :
    SpineTraceEquiv signature firstCell.spine secondCell.spine :=
  spineTraceEquiv_of_traceMatched (matching arcEqual)

/-! ## Honesty markers -/

/-- **Honesty marker — the COMBINATORIAL half of the Joyal-Street reconstruction is PROVED.**  The Mazurkiewicz
independent-swap connectivity engine is shipped: abstractly `AdjacentSwapEquiv.bubbleFront` and
`adjacentSwapEquiv_of_traceMatched` (any two linearizations of one dependency order are swap-connected), and
concretely `spineTraceEquiv_of_traceMatched` re-runs that exact head-extraction induction on the
context-shifting Godement closure `SpineTraceEquiv`.  This is the half the task named as the candidate residual,
here converted from obligation to theorem.  `= true`. -/
def fxMode_hasArcReconstructionConnectivityEngine : Bool := true

/-- **Honesty marker — the GEOMETRIC half is the sole residual.**  Reading `arcStructureOf` back as the cup/cap
dependency order and realizing each head extraction as a genuine `SpineGodementStep` chain — i.e.
`arcStructureOfSpineList n xs = arcStructureOfSpineList n ys → SpineTraceMatched signature xs ys`.
`arcStructureReconstruction_spine_of_matching` consumes EXACTLY this one input; everything else is proved.
`= false`. -/
def fxMode_hasArcHeadExtractionMatching : Bool := false

/-- **Honesty marker — the assembled reconstruction is GATED on the geometric residual.**  Given the
head-extraction matching above, `arcStructureReconstruction_spine_of_matching` / `_cell_of_matching` land the
full reconstruction `arcStructureOf a = arcStructureOf b → SpineTraceEquiv a.spine b.spine` — the YES-direction
the parent's `fxMode_hasArcStructureReconstruction` names, feeding `decidableSpineTraceEquiv_of` /
`decidableTwoCellConvFull_of`.  Until the matching discharges, the reconstruction stays conditional on that one
obligation.  `= false`. -/
def fxMode_hasArcStructureReconstructionAssembled : Bool := false

end FX1Poly.Tier0

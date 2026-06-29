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

/-! ## Trace-equivalence is length-preserving (the unconditional sound invariant the refutation rides)

`SpineTraceEquiv` permutes atoms with context shifts but never creates or destroys them; in particular it
PRESERVES the spine length, UNCONDITIONALLY (no Godement residual).  The Godement step's two sides are the four
whiskered blocks run in transposed order, so their lengths agree by `RawTwoCellExpr.spineDiff_length` (each block
contributes its `generatorCount` regardless of context) plus a `Nat` middle-transposition.  This is the clean
sound invariant the head-extraction-matching refutation below rides — it is forgotten by no part of the arc
structure, yet `arcStructureOf` fails to determine it once a generator's intrinsic arity is neither cup nor
cap. -/

/-- A single Godement spine step preserves the spine length: both run orders are the same four whiskered blocks
(`cellAlpha`, `cellAlphaUpper`, `cellBeta`, `cellBetaUpper`) over the common `rest`, each contributing its
context-independent `generatorCount` (`RawTwoCellExpr.spineDiff_length`); the only difference is transposing
`cellAlphaUpper`'s and `cellBeta`'s contributions, equal by `Nat.add_left_comm`. -/
theorem SpineGodementStep.length_eq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (step : SpineGodementStep signature firstList secondList) :
    firstList.length = secondList.length := by
  cases step with
  | godement cellAlpha cellAlphaUpper cellBeta cellBetaUpper leftAcc rightAcc rest =>
    simp only [RawTwoCellExpr.spineDiff_length]
    rw [Nat.add_left_comm cellAlphaUpper.generatorCount cellBeta.generatorCount
      (cellBetaUpper.generatorCount + rest.length)]

/-- ★ **Trace equivalence preserves the spine length, unconditionally.**  By induction on the closure: a Godement
step preserves it (`SpineGodementStep.length_eq`), reflexivity / symmetry / transitivity are direct, and the head
congruence adds one on both sides.  No Godement union-find residual is involved — this is a clean, axiom-free
sound invariant of `SpineTraceEquiv`. -/
theorem SpineTraceEquiv.length_eq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (equiv : SpineTraceEquiv signature firstList secondList) :
    firstList.length = secondList.length := by
  induction equiv with
  | ofStep step => exact step.length_eq
  | refl _ => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis => exact firstHypothesis.trans secondHypothesis
  | consCongr _ _ inductionHypothesis => exact congrArg (· + 1) inductionHypothesis

/-- A head-extraction matching preserves the spine length: it assembles into a `SpineTraceEquiv`
(`spineTraceEquiv_of_traceMatched`), which preserves length. -/
theorem SpineTraceMatched.length_eq {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (matched : SpineTraceMatched signature firstList secondList) :
    firstList.length = secondList.length :=
  (spineTraceEquiv_of_traceMatched matched).length_eq

/-! ## The structural-induction assembly: the matching from a per-head extraction (trace-algebra, fully proved)

The remaining combinatorial scaffolding above the geometric core: the FULL head-extraction matching is assembled,
by structural induction on the first spine list, out of exactly TWO per-step geometric inputs — a head-extraction
realizability (`SpineArcHeadExtraction`) and a nil-inversion (`SpineArcNilInversion`).  This proves the trace
ALGEBRA is not the obstruction: granted the two geometric inputs, `SpineTraceMatched` (hence, through
`spineTraceEquiv_of_traceMatched`, `SpineTraceEquiv` and the reconstruction) follows mechanically.  The two
inputs are the genuine geometric residual — and are themselves over-quantified (the refutation in the next
section instantiates `SpineArcNilInversion` to FALSE), so they hold only on the FAITHFUL fragment where
`arcStructureOf` determines the spine (see `ArcCellReconstruction`). -/

/-- **The per-head geometric extraction obligation.**  Given equal arc structures of `headAtom :: tailList` and
`secondList`, `secondList` can be bubbled (via a realized `SpineTraceEquiv`) so that `headAtom` reaches the front,
leaving a remainder whose arc structure matches `tailList`'s.  This is the per-step Joyal-Street realizability —
the dependency-order read-off plus the Godement realization of one head extraction. -/
def SpineArcHeadExtraction (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat) : Prop :=
  ∀ (headAtom : SpineAtom signature overallSource overallTarget)
    (tailList secondList : List (SpineAtom signature overallSource overallTarget)),
    arcStructureOfSpineList bottomCount (headAtom :: tailList)
        = arcStructureOfSpineList bottomCount secondList →
    ∃ matchedRemainder, SpineTraceEquiv signature secondList (headAtom :: matchedRemainder)
      ∧ arcStructureOfSpineList bottomCount tailList
          = arcStructureOfSpineList bottomCount matchedRemainder

/-- **The nil-inversion obligation.**  A spine list whose arc structure equals the empty spine's is empty.  (At
the cup/cap walking-adjunction seed this is the count read-off — `cupCount = capCount = 0` forces no atoms; over a
general signature it FAILS for arity-`0 ⇒ 0` boxes, witnessing the over-quantification refuted below.) -/
def SpineArcNilInversion (signature : ModeSignature)
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat) : Prop :=
  ∀ (secondList : List (SpineAtom signature overallSource overallTarget)),
    arcStructureOfSpineList bottomCount ([] : List (SpineAtom signature overallSource overallTarget))
        = arcStructureOfSpineList bottomCount secondList → secondList = []

/-- ★ **The head-extraction matching, assembled from the per-step geometric inputs.**  Structural induction on the
first spine list: the empty case closes by `SpineArcNilInversion` (the second list is empty too) and
`SpineTraceMatched.nil`; the cons case extracts the head via `SpineArcHeadExtraction` (a realized bubble plus an
arc-matched remainder) and recurses on the tail, assembling `SpineTraceMatched.cons`.  This is the ENTIRE
combinatorial content of the matching residual — granted the two geometric inputs, it is mechanical; the trace
algebra is NOT the obstruction. -/
theorem spineTraceMatched_of_headExtraction {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} {bottomCount : Nat}
    (headExtraction : SpineArcHeadExtraction signature (overallSource := overallSource)
      (overallTarget := overallTarget) bottomCount)
    (nilInversion : SpineArcNilInversion signature (overallSource := overallSource)
      (overallTarget := overallTarget) bottomCount) :
    ∀ {firstList secondList : List (SpineAtom signature overallSource overallTarget)},
      arcStructureOfSpineList bottomCount firstList = arcStructureOfSpineList bottomCount secondList →
      SpineTraceMatched signature firstList secondList := by
  intro firstList
  induction firstList with
  | nil =>
      intro secondList arcEqual
      rw [nilInversion secondList arcEqual]
      exact SpineTraceMatched.nil
  | cons headAtom tailList inductionHypothesis =>
      intro secondList arcEqual
      obtain ⟨matchedRemainder, headBubble, tailArcEqual⟩ :=
        headExtraction headAtom tailList secondList arcEqual
      exact SpineTraceMatched.cons headAtom headBubble (inductionHypothesis tailArcEqual)

/-! ## The literal spine-list residual is OVER-QUANTIFIED — REFUTED (zero-axiom)

The decisive correction this leg lands, exactly parallel to the soundness side's `not_arcGodementSamePartition`.
`fxMode_hasArcHeadExtractionMatching` (and the `matching` hypothesis `arcStructureReconstruction_spine_of_matching`
consumes) quantifies over ARBITRARY spine atom lists at an ARBITRARY signature.  But `stepArcAtom` reads each atom
ONLY through `leftContext.length` and the two boundary lengths `generatorDom.length` / `generatorCod.length` — it
forgets the generator identity, the right context, and (at a general signature) every generator whose intrinsic
arity is neither a cup `0 ⇒ 2` nor a cap `2 ⇒ 0`.  So at a witness signature carrying an arity-`0 ⇒ 0` generator,
the singleton spine `[box]` and the empty spine `[]` have the SAME arc structure (`box` is an arc no-op) yet
DIFFERENT length — and `SpineTraceMatched` preserves length (`SpineTraceMatched.length_eq`).  The unconditional
residual is therefore FALSE; this section MECHANIZES the refutation at the witness signature (which suffices,
since the residual ranges over all signatures).  (Observed but NOT mechanized here: even restricted to the
adjunction seed the spine-list residual is expected to fail — two `unit` atoms differing only in right context
share an arc structure while their singleton spines are not trace-related, the second half needing a
Godement-singleton inversion not shipped here.  Either way the genuine residual must move to the FAITHFUL
fragment, `ArcCellReconstruction` below.) -/

/-- The refuting witness quiver: one mode, NO modality generators — so the only 1-cell is the identity path. -/
private def witnessGraph : ModeGraph where
  Mode := Unit
  Modality := fun _ _ => Empty

/-- The refuting witness signature: the one-mode quiver with a (unique) 2-cell between every parallel 1-cell
pair.  Since the only 1-cell is the identity path, its sole generator is an arity-`0 ⇒ 0` endo-2-cell — a "box"
the arc fold processes as a complete no-op (it neither opens cup legs nor closes a cap). -/
private def witnessSignature : ModeSignature where
  graph := witnessGraph
  twoCell := fun _ _ => Unit

/-- The arity-`0 ⇒ 0` box atom over the witness signature: identity left/right contexts, identity generator
boundaries, the unique generator.  Its `generatorDom.length = generatorCod.length = 0`, so `stepArcAtom` takes the
generic branch with zero consumed and zero produced wires — leaving the arc state UNCHANGED. -/
private def witnessBoxAtom : SpineAtom witnessSignature () () :=
  { leftMidMode := (), rightMidMode := (),
    leftContext := ModalityPath.nil (graph := witnessGraph) (),
    generatorDom := ModalityPath.nil (graph := witnessGraph) (),
    generatorCod := ModalityPath.nil (graph := witnessGraph) (),
    generator := (),
    rightContext := ModalityPath.nil (graph := witnessGraph) () }

/-- The box atom is an arc no-op: the singleton `[box]` and the empty spine `[]` have the SAME arc structure.
Definitional (`rfl`) on the two TINY concrete folds — `stepArcAtom init box` reduces to `init` (zero consumed,
zero produced) — NOT the large parallel cells the perf rule warns against. -/
private theorem witnessBox_arcStructure_eq_nil :
    arcStructureOfSpineList 0 [witnessBoxAtom]
      = arcStructureOfSpineList 0 ([] : List (SpineAtom witnessSignature () ())) := rfl

/-- ★ **The literal head-extraction-matching residual is FALSE.**  Instantiated at the witness signature,
`overallSource = overallTarget = ()`, `bottomCount = 0`, it would force `SpineTraceMatched [box] []` from the
equal arc structures (`witnessBox_arcStructure_eq_nil`); but that matching preserves length
(`SpineTraceMatched.length_eq`), forcing `1 = 0`.  Hence `fxMode_hasArcHeadExtractionMatching` is refuted — it
CANNOT honestly be flipped to `true`; the residual is over-quantified (the arc structure does not determine the
spine once a generator's arity is neither cup nor cap), and the genuine residual is the faithful-fragment
`ArcCellReconstruction`.  Zero-axiom. -/
theorem not_arcHeadExtractionMatching :
    ¬ (∀ {firstList secondList : List (SpineAtom witnessSignature () ())},
        arcStructureOfSpineList 0 firstList = arcStructureOfSpineList 0 secondList →
        SpineTraceMatched witnessSignature firstList secondList) := by
  intro matchingHolds
  have matched : SpineTraceMatched witnessSignature [witnessBoxAtom] [] :=
    matchingHolds witnessBox_arcStructure_eq_nil
  exact Nat.noConfusion (SpineTraceMatched.length_eq matched)

/-! ## The genuine (faithful-fragment) residual — cell-level Joyal-Street reconstruction

The over-quantification pins the exact correction: the reconstruction must run on REALIZABLE spines — the spines
of genuine PARALLEL 2-cells, where the shared source/target boundary constrains the contexts and (at the cup/cap
seed) the arc structure IS a complete trace invariant.  This is the cell-level form
`arcStructureOf a = arcStructureOf b → SpineTraceEquiv a.spine b.spine` for parallel `a`, `b` — the genuine
Joyal-Street completeness, which does NOT route through the refuted spine-list `matching`.  It is TRUE (same
planar-arc type ⇒ planar-isotopic ⇒ trace-equivalent) but is the irreducible geometric core; it stays the
standing completeness obligation. -/

/-- ★ **The genuine completeness residual** — cell-level reconstruction over PARALLEL cells.  Equal full
planar-arc structures of two 2-cells with the SAME source/target paths give trace-equivalent spines.  Unlike the
spine-list `matching` (refuted: `not_arcHeadExtractionMatching`), this is stated only on realizable parallel
spines — the faithful fragment where `arcStructureOf` is a complete invariant.  It feeds
`decidableTwoCellConvFull_of`'s `reconstruct` through the spine→cell reconstruction
(`fxMode_hasSpineTraceReconstruction`), bypassing the over-quantified spine-list form. -/
def ArcCellReconstruction (signature : ModeSignature) : Prop :=
  ∀ {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath),
    arcStructureOf firstCell = arcStructureOf secondCell →
    SpineTraceEquiv signature firstCell.spine secondCell.spine

/-- The genuine residual directly supplies the cell-level reconstruction conclusion — the `reconstruct`-feeding
spine equivalence, gated on the faithful-fragment `ArcCellReconstruction` instead of the refuted spine-list
`matching`. -/
theorem arcStructureReconstruction_cell_of_cellReconstruction {signature : ModeSignature}
    (cellReconstruction : ArcCellReconstruction signature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (arcEqual : arcStructureOf firstCell = arcStructureOf secondCell) :
    SpineTraceEquiv signature firstCell.spine secondCell.spine :=
  cellReconstruction firstCell secondCell arcEqual

/-! ## The cell-level reconstruction is FALSE at a GENERAL signature — REFUTED (zero-axiom)

The decisive correction this leg lands, sharpening `not_arcHeadExtractionMatching` from the spine-LIST level to
genuine 2-CELLS.  The standing framing reasoned that moving the reconstruction off the spine-list `matching`
(refuted) onto PARALLEL cells — sharing a source/target boundary — recovers faithfulness: the shared boundary
constrains the whisker contexts, so the over-quantification that killed the spine-list form (right context,
generator identity) cannot occur.  That is HALF right (the contexts ARE boundary-determined) but MISSES the arity
leak: `stepArcAtom` still reads each atom only through `leftContext.length` and the two arity lengths, forgetting
every generator whose intrinsic arity is neither a cup `0 ⇒ 2` nor a cap `2 ⇒ 0`.

At the witness signature's arity-`0 ⇒ 0` box, the GENUINE PARALLEL cells `gen box` and `id` (both `id_⋆ ⇒ id_⋆`)
have the SAME arc structure — `gen box`'s spine is the single no-op `witnessBoxAtom`, so
`witnessBox_arcStructure_eq_nil` applies on the nose — yet spines of length `1` and `0`, and `SpineTraceEquiv`
preserves length (`SpineTraceEquiv.length_eq`).  Hence `ArcCellReconstruction witnessSignature` is itself FALSE:
the parallel-cell restriction is NOT the faithful fragment.  The genuine faithful fragment ADDITIONALLY needs the
signature's generators to be cup/cap (the cup/cap seed `adjunctionModeSignature`) — see the corrected residual
below. -/

/-- The arity-`0 ⇒ 0` box as a genuine 2-CELL: the `gen` of the witness signature's unique generator, a parallel
endo-cell `id_⋆ ⇒ id_⋆`.  Its spine is the single no-op `witnessBoxAtom`. -/
private def witnessBoxCell : RawTwoCellExpr witnessSignature
    (ModalityPath.nil (graph := witnessGraph) ()) (ModalityPath.nil (graph := witnessGraph) ()) :=
  RawTwoCellExpr.gen ()

/-- The identity 2-cell on `id_⋆`, genuinely PARALLEL to `witnessBoxCell` (same `id_⋆ ⇒ id_⋆` boundary).  Its
spine is empty. -/
private def witnessIdentityCell : RawTwoCellExpr witnessSignature
    (ModalityPath.nil (graph := witnessGraph) ()) (ModalityPath.nil (graph := witnessGraph) ()) :=
  RawTwoCellExpr.id _

/-- The box CELL and the identity CELL — genuine parallel 2-cells — have the SAME arc structure: definitionally
`arcStructureOf witnessBoxCell = arcStructureOfSpineList 0 [witnessBoxAtom]` (the `gen` spine is the singleton box
atom, `sourcePath.length = 0`) and `arcStructureOf witnessIdentityCell = arcStructureOfSpineList 0 []`, equal by
`witnessBox_arcStructure_eq_nil`. -/
private theorem witnessBoxCell_arcStructure_eq_identity :
    arcStructureOf witnessBoxCell = arcStructureOf witnessIdentityCell :=
  witnessBox_arcStructure_eq_nil

/-- ★ **The cell-level `ArcCellReconstruction` is FALSE at a general signature.**  Instantiated at the witness
signature it would force `SpineTraceEquiv witnessBoxCell.spine witnessIdentityCell.spine` from the equal arc
structures (`witnessBoxCell_arcStructure_eq_identity`); but those spines have length `1` and `0`, and
`SpineTraceEquiv` preserves length (`SpineTraceEquiv.length_eq`).  So `ArcCellReconstruction witnessSignature` is
refuted — the parallel-cell restriction ALONE does NOT recover faithfulness (the arity-`0 ⇒ 0` box leaks even on
genuine 2-cells), exactly as `not_arcHeadExtractionMatching` refuted the spine-list form, now sharpened to
realizable cells.  Hence `fxMode_hasArcCellReconstruction` CANNOT honestly be flipped at the general-signature
level; the genuine residual must move to the cup/cap seed.  Zero-axiom. -/
theorem not_arcCellReconstruction : ¬ ArcCellReconstruction witnessSignature := by
  intro reconstructionHolds
  exact Nat.noConfusion
    (reconstructionHolds witnessBoxCell witnessIdentityCell witnessBoxCell_arcStructure_eq_identity).length_eq

/-! ## The generator-free base fragment of the reconstruction (unconditional, every signature)

The reconstruction's base case, which DOES hold — for every signature, and without even consulting the arc
structure: two parallel cells that are both GENERATOR-FREE (no `gen` leaf) have empty spines, hence
trace-equivalent ones.  This is the (degenerate) bottom of the Joyal-Street induction — the positive content the
refutation above leaves standing, proved structurally (never by `rfl` / `decide` on the cells). -/

/-- A generator-free cell has an empty spine: the spine length is the generator count
(`RawTwoCellExpr.spine_length`), so a zero generator count forces the empty list (a cons would have a `succ`
length, impossible by `Nat.noConfusion`).  Structural `cases` on the spine, `propext`-free (`Nat.noConfusion`,
NOT `Nat.succ_ne_zero` — which itself depends on `propext` in this toolchain — nor `List.length_eq_zero`). -/
theorem RawTwoCellExpr.spine_eq_nil_of_generatorCount_zero {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cell : RawTwoCellExpr signature sourcePath targetPath} (generatorFree : cell.generatorCount = 0) :
    cell.spine = [] := by
  have lengthZero : cell.spine.length = 0 := by
    rw [RawTwoCellExpr.spine_length]; exact generatorFree
  cases spineForm : cell.spine with
  | nil => rfl
  | cons headAtom tailAtoms =>
      rw [spineForm] at lengthZero
      exact Nat.noConfusion lengthZero

/-- ★ **The generator-free reconstruction fragment.**  Two parallel cells that are both generator-free have
trace-equivalent spines — both spines are empty (`spine_eq_nil_of_generatorCount_zero`), so the trace equivalence
is reflexivity.  Holds at EVERY signature (it never reads the arc structure); it is the unconditional base of the
Joyal-Street induction the refutation above leaves intact. -/
theorem spineTraceEquiv_of_generatorFree {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {firstCell secondCell : RawTwoCellExpr signature sourcePath targetPath}
    (firstGeneratorFree : firstCell.generatorCount = 0)
    (secondGeneratorFree : secondCell.generatorCount = 0) :
    SpineTraceEquiv signature firstCell.spine secondCell.spine := by
  rw [RawTwoCellExpr.spine_eq_nil_of_generatorCount_zero firstGeneratorFree,
    RawTwoCellExpr.spine_eq_nil_of_generatorCount_zero secondGeneratorFree]
  exact SpineTraceEquiv.refl []

/-! ## Honesty markers -/

/-- **Honesty marker — the COMBINATORIAL half of the Joyal-Street reconstruction is PROVED.**  The Mazurkiewicz
independent-swap connectivity engine is shipped: abstractly `AdjacentSwapEquiv.bubbleFront` and
`adjacentSwapEquiv_of_traceMatched` (any two linearizations of one dependency order are swap-connected), and
concretely `spineTraceEquiv_of_traceMatched` re-runs that exact head-extraction induction on the
context-shifting Godement closure `SpineTraceEquiv`.  This is the half the task named as the candidate residual,
here converted from obligation to theorem.  `= true`. -/
def fxMode_hasArcReconstructionConnectivityEngine : Bool := true

/-- **Honesty marker — the spine-list head-extraction-matching residual is over-quantified, REFUTED.**  Reading
`arcStructureOf` back as the cup/cap dependency order would give
`arcStructureOfSpineList n xs = arcStructureOfSpineList n ys → SpineTraceMatched signature xs ys`
(`arcStructureReconstruction_spine_of_matching` consumes exactly this).  But `stepArcAtom` reads each atom only
through `leftContext.length` and the two arity lengths — it forgets the generator identity, the right context, and
every arity-`0 ⇒ 0` box.  `not_arcHeadExtractionMatching` REFUTES the unconditional residual zero-axiom (`[box]`
and `[]` share an arc structure but differ in length, which `SpineTraceMatched` preserves).  So this flag CANNOT
be flipped to `true`; the genuine residual is the faithful-fragment `ArcCellReconstruction`
(`fxMode_hasArcCellReconstruction`).  `= false`. -/
def fxMode_hasArcHeadExtractionMatching : Bool := false

/-- **Honesty marker — the assembled reconstruction is GATED on the geometric residual.**  Given the
head-extraction matching above, `arcStructureReconstruction_spine_of_matching` / `_cell_of_matching` land the
full reconstruction `arcStructureOf a = arcStructureOf b → SpineTraceEquiv a.spine b.spine` — the YES-direction
the parent's `fxMode_hasArcStructureReconstruction` names, feeding `decidableSpineTraceEquiv_of` /
`decidableTwoCellConvFull_of`.  Until the matching discharges, the reconstruction stays conditional on that one
obligation.  `= false`. -/
def fxMode_hasArcStructureReconstructionAssembled : Bool := false

/-- **Honesty marker — trace equivalence is length-preserving, PROVED unconditionally.**
`SpineTraceEquiv.length_eq` (via `SpineGodementStep.length_eq` through `RawTwoCellExpr.spineDiff_length`) proves
the spine length is an unconditional `SpineTraceEquiv` invariant — no Godement union-find residual.  This is the
clean sound invariant the head-extraction-matching refutation rides (the arc structure fails to determine it once
a generator's arity is neither cup nor cap).  `= true`. -/
def fxMode_hasSpineTraceLengthInvariant : Bool := true

/-- **Honesty marker — the head-extraction matching's trace ALGEBRA is fully assembled.**
`spineTraceMatched_of_headExtraction` builds the full `SpineTraceMatched` (hence, via
`spineTraceEquiv_of_traceMatched`, the spine `SpineTraceEquiv`) from exactly TWO per-step geometric inputs
(`SpineArcHeadExtraction` + `SpineArcNilInversion`), by structural induction on the spine list.  The trace algebra
is therefore NOT the obstruction; only the per-step geometric realizability is — and even that is over-quantified
on raw atom lists (the refutation instantiates `SpineArcNilInversion` to false).  `= true`. -/
def fxMode_hasArcHeadExtractionTraceAssembly : Bool := true

/-- **Honesty marker — the spine-list residual is REFUTED (zero-axiom), pinning the freshness-analog correction.**
`not_arcHeadExtractionMatching` proves `¬ (… → SpineTraceMatched …)` at a witness signature carrying an
arity-`0 ⇒ 0` box: `[box]` and `[]` have equal arc structures (`witnessBox_arcStructure_eq_nil`, by `rfl` on the
two tiny folds) but different length, which `SpineTraceMatched.length_eq` preserves.  As STATED (over all
signatures and all atom lists) the residual is false — exactly as the soundness side's
`not_arcGodementSamePartition` refuted `ArcGodementSamePartition`; the genuine residual must move to the faithful
parallel-cell fragment.  `= true`. -/
def fxMode_hasArcHeadExtractionMatchingRefuted : Bool := true

/-- **Honesty marker — the cell-level `ArcCellReconstruction` is FALSE at a GENERAL signature, REFUTED
(zero-axiom).**  `ArcCellReconstruction` quantifies over PARALLEL cells at an ARBITRARY signature; the standing
belief was that the shared boundary makes this the faithful fragment.  `not_arcCellReconstruction` REFUTES that:
at the witness signature's arity-`0 ⇒ 0` box, the genuine parallel 2-cells `gen box` and `id` have equal arc
structure (`witnessBoxCell_arcStructure_eq_identity`) but spine lengths `1 ≠ 0`, which `SpineTraceEquiv.length_eq`
preserves.  So the parallel-cell restriction is NOT sufficient — this SHARPENS the spine-list
`not_arcHeadExtractionMatching` to genuine cells, and pins that the faithful fragment ALSO needs cup/cap
generators.  `= true`. -/
def fxMode_hasArcCellReconstructionRefutedAtGeneralSignature : Bool := true

/-- **Honesty marker — the generator-free base fragment of the reconstruction is PROVED (every signature).**
`spineTraceEquiv_of_generatorFree` proves two parallel generator-free cells have trace-equivalent spines (both
empty, via `RawTwoCellExpr.spine_eq_nil_of_generatorCount_zero`).  This is the unconditional bottom of the
Joyal-Street induction — the positive content the general-signature refutation leaves standing — holding even
without consulting the arc structure.  `= true`. -/
def fxMode_hasGeneratorFreeReconstruction : Bool := true

/-- **Honesty marker — the genuine completeness residual is the cup/cap-SEED cell reconstruction.**  As stated
over a GENERAL signature, `ArcCellReconstruction` is FALSE (`not_arcCellReconstruction`: the arity-`0 ⇒ 0` box
makes `gen box` and `id` arc-equal but length-distinct) — so the parallel-cell restriction the prior framing took
for "faithful" is insufficient, and this flag CANNOT be flipped at the general level.  The GENUINE residual is its
cup/cap-seed instance `ArcCellReconstruction adjunctionModeSignature`, where every generator is a cup (`0 ⇒ 2`,
unit) or cap (`2 ⇒ 0`, counit), so the arity leak is closed and `arcStructureOf` is (believed) a complete trace
invariant.  That instance is TRUE by Joyal-Street (same planar-arc type ⇒ planar-isotopic ⇒ trace-equivalent),
with the trace ALGEBRA above it already proved (`spineTraceEquiv_of_traceMatched`,
`spineTraceMatched_of_headExtraction`) and the geometric base discharged on the generator-free fragment
(`spineTraceEquiv_of_generatorFree`); the remaining geometric core is the per-head cup/cap extraction.  Its
general zero-axiom proof is not shipped here.  `= false`. -/
def fxMode_hasArcCellReconstruction : Bool := false

end FX1Poly.Tier0

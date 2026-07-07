import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcStuckSpineSwapConnected
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwapGeneration

/-! # ArcStuckHeadLeftCancel — ★★ AtomicTraceEquiv is NOT left-cancellable at the cup/cap SEED

FREE-6b (`TraceNormalFormNonInvariance`) proved `AtomicTraceEquiv` is NOT left-cancellable at the
SCALAR-BUBBLE signature: a `nil ⇒ nil` bubble slides around a creation (Eckmann-Hilton), so
`creation :: [bubble-right] ~ creation :: [bubble-left]` while the singleton tails are inequivalent.
The open question that gated the fresh Mazurkiewicz / linear-extension reconstruction route was
whether that Eckmann-Hilton obstruction is an ARTIFACT of the scalar bubble (absent from the cup/cap
walking adjunction, which has no `nil ⇒ nil` generator) or bites at the cup/cap seed too.

**This file settles it — the EH wall DOES bite at the cup/cap seed, by MACHINE DECISION.**  On the
hardest known stuck instance (`ArcStuckSpineNonSingleton`), the double snake `[cup@0,cap@1,cup@0,cap@1]`
and the nested snake `[cup@0,cup@2,cap@3,cap@1]` are `SpineTraceEquiv` (shipped
`spineTraceEquiv_doubleSnake_nestedSnake`) and share a LITERALLY EQUAL head `cup@0`
(`stuckSpines_headPrefix_eq`), yet the two 3-atom tails they leave —
`[cap@1,cup@0,cap@1]` and `[cup@2,cap@3,cap@1]` — are NOT `AtomicTraceEquiv`
(`tails_notAtomicTraceEquiv`, decided by EXHAUSTIVE BFS saturation: the double-snake tail's swap-class
has exactly THREE members, the frontier exhausts, and the nested tail is not among them).

## What this settles for the reconstruction route

The naive Mazurkiewicz decomposition — "peel the shared head, recurse on the tails" — is REFUTED at the
seed: peeling the shared `cup@0` head leaves non-trace-equivalent (and, at their realizable bottom
count `3`, arc-DISTINCT) tails, so the head extraction does NOT reduce the problem.  Concretely the
event-poset / linear-extension route does NOT apply over the SpineAtom "letters" as a STATIC
Mazurkiewicz trace: a trace monoid is left-cancellative, and this swap monoid is not.  The route can
only survive over ABSTRACT turnback events (whose windows are a derived function of the linear order),
with the context-shift realized geometrically — i.e. it needs the context-dependent-poset (dynamic
trace) adaptation, not the textbook static-trace connectivity.  This is the seed-level counterpart of
FREE-6b's scalar-bubble `atomicTraceEquiv_isNotLeftCancellable`, sharpening it onto the genuine cup/cap
adjunction where the reconstruction actually lives.

(It does NOT refute the reconstruction `arcStructureOf a = arcStructureOf b → SpineTraceEquiv` itself:
the two FULL snakes remain arc-equal and trace-equivalent; only the head-peeling PROOF STRATEGY dies.)

Raw Lean 4 + Init; the tail non-equivalence closes by completeness of the exhaustively-saturated BFS
swap-class (kernel `decide` on the exhaustion gate and the class membership).  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

open AdjunctionMode AdjunctionModality

/-! ## The two tails left by peeling the shared cup@0 head -/

/-- The double snake's tail after peeling its `cup@0` head: `[cap@1, cup@0, cap@1]`. -/
def doubleSnakeTail :
    List (SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.tip) :=
  doubleSnakeOnLeft.spine.tail

/-- The nested snake's tail after peeling its `cup@0` head: `[cup@2, cap@3, cap@1]`. -/
def nestedSnakeTail :
    List (SpineAtom adjunctionModeSignature AdjunctionMode.base AdjunctionMode.tip) :=
  nestedSnakeOnLeft.spine.tail

/-- ★ The double and nested snakes share a LITERALLY EQUAL head atom `cup@0` — their length-`1`
prefixes coincide (kernel decision on the shipped spine-list decidable equality). -/
theorem stuckSpines_headPrefix_eq :
    doubleSnakeOnLeft.spine.take 1 = nestedSnakeOnLeft.spine.take 1 :=
  @of_decide_eq_true (doubleSnakeOnLeft.spine.take 1 = nestedSnakeOnLeft.spine.take 1)
    (spineListDecEq adjunctionModeDecEq adjunctionModalityDecEq adjunctionTwoCellDecEq
      (doubleSnakeOnLeft.spine.take 1) (nestedSnakeOnLeft.spine.take 1))
    (by decide)

/-! ## The double-snake tail's swap-class is complete and excludes the nested tail -/

/-- ★ The BFS run over the double-snake tail EXHAUSTS its frontier at `fuel = 16`: the tail's
swap-class is COMPLETE (a three-element class), so no swap-reachable tail is missed. -/
theorem doubleSnakeTail_frontierExhausts :
    didExhaustFrontier adjunctionModeDecEq adjunctionModalityDecEq adjunctionTwoCellDecEq 16
      [doubleSnakeTail] [doubleSnakeTail] = true := by decide

/-- ★ The nested-snake tail is NOT in the double-snake tail's (complete) swap-class — kernel
`decide` that the membership fails over the shipped spine-list membership decider. -/
theorem nestedSnakeTail_notMem_class :
    ¬ (nestedSnakeTail ∈ saturateClass adjunctionModeDecEq adjunctionModalityDecEq
        adjunctionTwoCellDecEq 16 doubleSnakeTail) :=
  @of_decide_eq_false
    (nestedSnakeTail ∈ saturateClass adjunctionModeDecEq adjunctionModalityDecEq
      adjunctionTwoCellDecEq 16 doubleSnakeTail)
    (listMemDecidable
      (spineListDecEq adjunctionModeDecEq adjunctionModalityDecEq adjunctionTwoCellDecEq)
      nestedSnakeTail
      (saturateClass adjunctionModeDecEq adjunctionModalityDecEq adjunctionTwoCellDecEq 16
        doubleSnakeTail))
    (by decide)

/-- ★ **The two peeled tails are NOT `AtomicTraceEquiv`.**  Were they equivalent, completeness of the
exhausted saturation (`saturateClass_isComplete`, gated on `doubleSnakeTail_frontierExhausts`) would put
the nested tail in the double-snake tail's swap-class — contradicting `nestedSnakeTail_notMem_class`. -/
theorem tails_notAtomicTraceEquiv :
    ¬ AtomicTraceEquiv adjunctionModeSignature doubleSnakeTail nestedSnakeTail := by
  intro tailsEquiv
  exact nestedSnakeTail_notMem_class
    (saturateClass_isComplete adjunctionModeDecEq adjunctionModalityDecEq adjunctionTwoCellDecEq
      doubleSnakeTail_frontierExhausts tailsEquiv)

/-! ## ★★ The verdict: left-cancellation FAILS at the cup/cap seed -/

/-- ★★ **`AtomicTraceEquiv` is NOT left-cancellable at the cup/cap seed.**  The double and nested snakes
are trace-equivalent (`spineTraceEquiv_doubleSnake_nestedSnake`, lifted to the atomic closure) and share
a literally-equal head `cup@0` (`stuckSpines_headPrefix_eq`), yet the two tails they leave are NOT
trace-equivalent (`tails_notAtomicTraceEquiv`).  So the Eckmann-Hilton non-cancellability FREE-6b found
at the scalar-bubble signature bites at the genuine cup/cap adjunction too: the swap monoid is NOT
left-cancellative, hence the spine atoms do NOT form a STATIC Mazurkiewicz trace monoid, and the
"peel the shared head and recurse" decomposition of the reconstruction is DEAD at the seed. -/
theorem atomicTraceEquiv_notLeftCancellable_atSeed :
    AtomicTraceEquiv adjunctionModeSignature doubleSnakeOnLeft.spine nestedSnakeOnLeft.spine
      ∧ doubleSnakeOnLeft.spine.take 1 = nestedSnakeOnLeft.spine.take 1
      ∧ ¬ AtomicTraceEquiv adjunctionModeSignature
            doubleSnakeOnLeft.spine.tail nestedSnakeOnLeft.spine.tail :=
  ⟨spineTraceEquiv_doubleSnake_nestedSnake.toAtomicTraceEquiv,
    stuckSpines_headPrefix_eq,
    tails_notAtomicTraceEquiv⟩

/-! ## Honesty marker -/

/-- **Honesty marker — the EH wall bites at the cup/cap seed; the static-trace reconstruction route is
refuted.**  `atomicTraceEquiv_notLeftCancellable_atSeed`: the arc-equal, trace-equivalent double and
nested snakes share a literal `cup@0` head but leave NON-trace-equivalent tails (BFS-decided over the
exhausted three-element tail swap-class).  So `AtomicTraceEquiv` is NOT left-cancellable at
`adjunctionModeSignature` — the spine atoms are not a static Mazurkiewicz trace monoid, and the
"peel the shared head, recurse on the tails" decomposition of `ArcCellReconstruction` cannot close.  The
event-poset / linear-extension route survives only over ABSTRACT turnback events with the context shift
realized geometrically (the dynamic-trace adaptation), not over the SpineAtom letters.  This does NOT
refute the reconstruction theorem itself (the full snakes stay trace-equivalent) — only the head-peeling
proof strategy.  `= true`. -/
def fxMode_hasSeedTraceLeftCancellationFailure : Bool := true

end FX1Poly.Polygraph

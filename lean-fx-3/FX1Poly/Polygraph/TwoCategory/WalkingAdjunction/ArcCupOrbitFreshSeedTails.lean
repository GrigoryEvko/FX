import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCaseOrbitReduction
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadBoundary

/-! # ArcCupOrbitFreshSeedTails — the orbit witness from the FRESH-SEED tails equality (the folded campaign's terminal premise, wired direct)

The `~30`-file folded-legs campaign (`ArcCupFoldedInternalCountFreshArc`,
`ArcCupFoldedDiagramFreshArc`, …) ground the cup `tailsCancel` down through the diagram /
total-count / internal-count legs, and its own capstone honesty markers reduce ALL THREE
contentful legs to the ONE uniform premise

  `freshArcEqual : arcStructureOfSpineList (bottomCount + 2) firstAtoms
                     = arcStructureOfSpineList (bottomCount + 2) secondAtoms`

(the two tail lists carrying equal arc structure at the WIDER `bottomCount + 2` seed the cup
splice opens).  This brick draws the boundary sharp: that terminal premise is ALREADY the orbit
witness's `tailsCancel`, so the whole folded machinery is unnecessary.

DECISIVE OBSERVATION.  A cup head firing at `bottomCount` has `codBoundaryLength = bottomCount + 2`
(the two fresh legs — the shipped `arcCupHeadCodBoundaryGrows`).  The orbit witness's `tailsCancel`
is stated at exactly that `headAtom.codBoundaryLength` seed.  So the fresh-seed tails equality at
`bottomCount + 2` IS `tailsCancel` under a single `rw` — no diagram leg, no count legs, no
internal legs.  The `~30`-file FreshArc campaign therefore reduced `tailsCancel` to (a premise
definitionally equal to) `tailsCancel`: it is a NON-PROGRESSING re-expression, and the genuine
progress lives only in producing that fresh-seed tails equality (equivalently the leg-aligned
re-selection `AtomicTraceEquiv`, `ArcCupReselectionOrbit`) — the deep planar content.

  * ★ `arcCupOrbitWitness_ofFreshSeedTails` — the full `ArcCupOrbitWitness` from the located
    split / bubble / `movedDomPin`, the window pin, and the fresh-seed tails equality at
    `bottomCount + 2`, bridged to `tailsCancel` by `arcCupHeadCodBoundaryGrows`.  Strictly the
    arc-level object (weaker than the re-selection `AtomicTraceEquiv`) at the concrete seed the
    cup fold produces — the exact interface a direct planar producer at the natural seed emits.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The cup orbit witness from the fresh-seed tails equality.**  Given the located data the
shipped locator supplies (the split `doesSplitSpine`, the `BubblesToFront` bubble, `movedDomPin`),
the window pin, and — crucially — the two tails carrying EQUAL arc structure at the fresh
`bottomCount + 2` seed (the terminal premise of the whole FreshArc folded-legs campaign), the full
`ArcCupOrbitWitness` follows: the head cup fires at `bottomCount`, so its `codBoundaryLength` is
`bottomCount + 2` (`arcCupHeadCodBoundaryGrows`), and the witness's `tailsCancel` at that seed IS
the given fresh-seed equality under a single rewrite.  No diagram / count / internal folded legs —
this bypasses the `~30`-file campaign, whose deepest premise is exactly this fresh-seed equality. -/
theorem arcCupOrbitWitness_ofFreshSeedTails
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList secondList prefixAtoms suffixAtoms movedPrefixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (toucherAtom movedTarget :
      SpineAtom adjunctionModeSignature overallSource overallTarget)
    (firstChained : SpineBoundaryChained bottomCount (headAtom :: tailList))
    (doesSplitSpine : secondList = prefixAtoms ++ toucherAtom :: suffixAtoms)
    (bubble : BubblesToFront toucherAtom prefixAtoms movedTarget movedPrefixAtoms)
    (movedDomPin : movedTarget.generatorDom.length = 0)
    (windowPin : movedTarget.leftContext.length = headAtom.leftContext.length)
    (freshSeedTailsCancel :
      arcStructureOfSpineList (bottomCount + 2) tailList
        = arcStructureOfSpineList (bottomCount + 2) (movedPrefixAtoms ++ suffixAtoms)) :
    ArcCupOrbitWitness headAtom tailList secondList := by
  have codEq : headAtom.codBoundaryLength = bottomCount + 2 :=
    arcCupHeadCodBoundaryGrows bottomCount headAtom hasCupDomArity hasCupCodArity tailList
      firstChained
  refine ⟨prefixAtoms, toucherAtom, suffixAtoms, movedTarget, movedPrefixAtoms,
    doesSplitSpine, bubble, movedDomPin, windowPin, ?_⟩
  rw [codEq]
  exact freshSeedTailsCancel

/-! ## Honesty marker -/

/-- **Honesty marker — the folded campaign's terminal premise IS `tailsCancel` (peel campaign H).**
`arcCupOrbitWitness_ofFreshSeedTails`: the full `ArcCupOrbitWitness` follows from the located
split / bubble / `movedDomPin`, the window pin, and the two tails carrying equal arc structure at
the `bottomCount + 2` seed — DIRECTLY, via `arcCupHeadCodBoundaryGrows` (`codBoundaryLength =
bottomCount + 2`), with NO diagram / count / internal folded legs.  Because the FreshArc capstones
reduce all three contentful folded legs to exactly this fresh-seed arc equality, the `~30`-file
folded-legs campaign reduced `tailsCancel` to a premise definitionally equal to `tailsCancel` — a
non-progressing re-expression that this brick bypasses.  What this marker does NOT claim: the
fresh-seed tails equality itself (= the orbit's `tailsCancel`, the leg-aligned re-selection
`AtomicTraceEquiv` of `ArcCupReselectionOrbit`, the deep planar content) nor `windowPin` (the moved
cup lands at the head's window) — those two remain the sole genuine residual of the cup case.
`= true`. -/
def fxMode_hasArcCupOrbitFreshSeedTails : Bool := true

end FX1Poly.Polygraph

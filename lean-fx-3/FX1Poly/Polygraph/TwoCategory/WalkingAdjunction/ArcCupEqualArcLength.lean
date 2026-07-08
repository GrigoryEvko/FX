import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcReconstruction
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupMixedReselectionReduction

/-! # ArcCupEqualArcLength — equal arc structure FORCES equal spine length (the fixed-length sharpening)

Flag-B round 8, the honest fronting correction.  The literature verdict on the cup-fronting crux `(a)` (Selinger,
arXiv:0908.3347, quoting Joyal–Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991); Forest–Mimram,
arXiv:2109.05369, §4.2) draws one sharp line: the length-preserving INTERCHANGERS front a cup only within the
CONNECTED / progressive (recumbent) isotopy class; a *floating bubble* — a cup–cap closed loop not anchored to the
boundary — is NOT frontable at fixed length and, in the free monoidal setting, forces the length-CHANGING snake
`N`/`N̄` (FM Lemma 4.2.1) to reduce to the representative first (the "reduced-representative detour").

This brick establishes the fact that DISCHARGES that detour inside every re-selection instance: at the cup/cap seed
`adjunctionModeSignature`, two spines with EQUAL arc structure have EQUAL length.  The reason is that
`arcStructureOf` records both totals — `cupCount = cupEventNodes.length` and `capCount = capEventNodes.length`
(`arcStructureOfSpineList_cupCount` / `_capCount`) — and at the seed every atom is a cup or a cap
(`adjunctionAtom_cupOrCap`), so `cupCount + capCount = spine length` (`adjunctionCupCapAtomCount_eq_length`).  Equal
arc structure therefore pins BOTH counts, hence the length.

  * ★ `equalArcSpine_length_eq` — two seed spines with equal `arcStructureOfSpineList` have equal `List.length`.
    (The nil-inversion `spineArcNilInversion_adjunction` is the `secondList = []` corner of this; this is the full
    two-spine statement.)
  * ★ `mixedTailArcCompleteness_lengthObligation_discharged` — the length obligation the conclusion of
    `MixedTailArcCompleteness` carries (its `SpineTraceEquiv` is length-preserving, `SpineTraceEquiv.length_eq`) is
    ALREADY forced by the completeness hypothesis (equal arc structure) — for free, before any interchange.

## Why this SHARPENS (and corrects) the residual geometry

The recon framed the open interior as needing "the gap-1 interacting zigzag → the length-CHANGING snake / reduced
representative (route 2)."  This brick shows route 2 is NOT invoked inside a `MixedTailArcCompleteness` instance:
both spines carry IDENTICAL cup / cap tallies (and the diagram's closed-loop tally `loops`, recorded by
`stepCapArc` when the two capped ports were already one component), so no cup–cap pair is ever created or destroyed
in relating them — there is no floating bubble on one side absent from the other.  The re-selection is a PURE
FIXED-LENGTH permutation problem: the recumbent / progressive interchange completeness (FM connected-diagram
termination, Joyal–Street Thm 1.5 in the progressive class), NOT a reduced-representative reduction.

So the genuine residual is exactly (and only) route 1: two equal-length, equal-loop, equal-matching, equal-internal-
turnback-count cup/cap spines are interchange-connected.  `arcStructureOf` is by design the COMPLETE planar
invariant for this — "strictly finer than `matchingOf`: it sees the internal turnbacks the boundary matching
forgets, closing the snake gap" (its own docstring) — via the `internalCupCounts` / `internalCapCounts` per-strand
turnback tallies.  The gap-1 interacting zigzag is resolved WITHIN the fixed-length orbit by that internal-count
refinement; it is not a snake reduction.  This brick does NOT close that interchange-completeness — it removes the
false length-changing obligation from it and pins the honest shape.

Raw Lean 4 + Init; STRUCTURAL (rides the shipped count read-offs), zero-axiom; per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Equal arc structure forces equal length -/

/-- ★ **Equal arc structure forces equal spine length, at the cup/cap seed.**  `arcStructureOf` records the cup and
cap totals faithfully (`arcStructureOfSpineList_cupCount` / `_capCount` read back `cupAtomCount` / `capAtomCount`),
and at the seed every atom is a cup or a cap, so the two counts partition the length
(`adjunctionCupCapAtomCount_eq_length`).  Equal arc structure pins both counts, hence the length.  This is the full
two-spine generalization of the nil-inversion `spineArcNilInversion_adjunction` (its `secondList = []` corner): it
shows every `MixedTailArcCompleteness` instance is a FIXED-LENGTH problem, excluding the length-changing snake /
reduced-representative detour the free-monoidal fronting would otherwise force on a floating bubble. -/
theorem equalArcSpine_length_eq {sourceMode targetMode : AdjunctionMode} (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
    (arcEqual : arcStructureOfSpineList bottomCount firstList
        = arcStructureOfSpineList bottomCount secondList) :
    firstList.length = secondList.length := by
  have cupsEqual : cupAtomCount firstList = cupAtomCount secondList := by
    have counts := congrArg FullArcStructure.cupCount arcEqual
    rw [arcStructureOfSpineList_cupCount, arcStructureOfSpineList_cupCount] at counts
    exact counts
  have capsEqual : capAtomCount firstList = capAtomCount secondList := by
    have counts := congrArg FullArcStructure.capCount arcEqual
    rw [arcStructureOfSpineList_capCount, arcStructureOfSpineList_capCount] at counts
    exact counts
  rw [← adjunctionCupCapAtomCount_eq_length firstList,
    ← adjunctionCupCapAtomCount_eq_length secondList, cupsEqual, capsEqual]

/-! ## The completeness length obligation is discharged for free -/

/-- ★ **The length obligation of `MixedTailArcCompleteness` is already forced by its hypothesis.**  The conclusion of
`MixedTailArcCompleteness` is a `SpineTraceEquiv`, which is length-preserving (`SpineTraceEquiv.length_eq`); so any
proof of it OWES that `firstList.length = secondList.length`.  This lemma discharges that debt directly from the
completeness hypothesis (equal arc structure) via `equalArcSpine_length_eq` — before any interchange step.  Hence
the remaining content of `MixedTailArcCompleteness` is PURELY the fixed-length interchange re-selection (route 1),
with the length-changing snake (route 2) excluded: both spines carry identical cup / cap tallies, so no floating
bubble is present on one side and absent on the other. -/
theorem mixedTailArcCompleteness_lengthObligation_discharged {sourceMode targetMode : AdjunctionMode}
    (bottomCount : Nat)
    (firstList secondList : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
    (arcEqual : arcStructureOfSpineList bottomCount firstList
        = arcStructureOfSpineList bottomCount secondList) :
    firstList.length = secondList.length :=
  equalArcSpine_length_eq bottomCount firstList secondList arcEqual

/-! ## Honesty marker -/

/-- **Honesty marker — equal arc structure forces equal length; route 2 (the snake) is EXCLUDED inside every
re-selection instance (flag-B R8, fronting correction).**  `equalArcSpine_length_eq`: two seed spines with equal
`arcStructureOfSpineList` have equal length, because the arc structure pins both `cupCount` and `capCount`
(`arcStructureOfSpineList_{cup,cap}Count`) and at the seed the two counts partition the length
(`adjunctionCupCapAtomCount_eq_length`).  `mixedTailArcCompleteness_lengthObligation_discharged`: the
length-preserving `SpineTraceEquiv` conclusion of `MixedTailArcCompleteness` therefore owes nothing extra — its
length obligation is met by the hypothesis alone.

This CORRECTS the round-3/4 residual framing.  The interior of `MixedTailArcCompleteness` was named as possibly
needing the length-CHANGING snake (FM Lemma 4.2.1 `N`/`N̄`, the reduced-representative detour) for a gap-1
interacting zigzag.  It does not: equal arc structure makes both spines carry identical cup / cap tallies (and,
through the diagram field, identical closed-loop `loops` tallies), so relating them creates or destroys no cup–cap
pair — there is no floating bubble on one side absent from the other (Selinger eq. (3.1) / Joyal–Street: the bubble
is arc-DISTINGUISHED, `arcStructureOf` "closes the snake gap" via its internal-turnback counts).  The residual is
PURELY route 1: two equal-length, equal-loop, equal-matching, equal-internal-count cup/cap spines are
interchange-connected — the recumbent / progressive interchange completeness (FM connected-diagram termination,
Joyal–Street Thm 1.5 restricted to the progressive class), the fixed-length word problem the census-refuted
`windowPin` reads off.

What this marker does NOT claim: that interchange completeness itself.  The fronting `AtomicTraceEquiv secondList
(headAtom :: movedRest)` — landing the HEAD cup at the front within the fixed-length swap orbit — remains the open
leaf (with the tail re-selection, `arcCupReselection_exists`).  No gate flip: `fxMode_hasArcStructureReconstruction`
and `fxMode_hasModeRelativeConvDecision` stay as they are.  `= true`. -/
def fxMode_hasArcCupEqualArcLength : Bool := true

end FX1Poly.Polygraph

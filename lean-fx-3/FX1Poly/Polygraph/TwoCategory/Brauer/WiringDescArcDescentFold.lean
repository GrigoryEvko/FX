import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcDescent

/-! # BRAUER-ARC-DESCENT r1 B2 — the Σ-carried arc-sink FOLD mechanism (the comb/staircase template on arcs)

B1 shipped the descent measure `arcMeasure` and proved it strictly drops on the three disjoint-support / cup-cup
cup-sink slides, while the adjacent-straddle slide RESISTS it (`straddle_resists_arcMeasure`).  This file assembles
the descent into the `recComb`-shaped Σ-carried fold mechanism: each cup-sink move is packaged as a "rung" that
EXTENDS a running `BrauerConvFree8` accumulator from a fixed `startWord` to the reduced word AND certifies a strict
`arcMeasure` fuel decrease — exactly the `recCombConv` shape (the conv carried alongside the descending data), now
on arcs.

## What this file ships (each zero-axiom, structural)

  * **`arcSink_cupCap` / `arcSink_cupCrossing` / `arcSink_cupCup`** — the three Σ-carried sink RUNGS: given a running
    `BrauerConvFree8 startWord currentWord` positioned at a cup-sink redex, produce the extended
    `BrauerConvFree8 startWord nextWord` (via `whiskerLeft`/`whiskerRight`/`trans` of the shipped slide) TOGETHER
    with `arcMeasure radix nextWord < arcMeasure radix currentWord`.  Composing these rungs is a fold whose fuel
    strictly descends per step — the `Nat`-fuel recursion the pass-5-arc driver lacked, on the descending fragment.
  * **`arcSinkFold_demo`** — a concrete two-rung fold: `[cupAt 0, capAt 2, capAt 3]` is `BrauerConvFree8` to the
    cup-sunk form `[capAt 0, capAt 1, cupAt 0]` (`cupNonCupInversions = 0`), through the intermediate
    `[capAt 0, cupAt 0, capAt 3]`, with `arcMeasure 8` strictly decreasing `16 → 8 → 0` at each rung.  This is the
    arc-level analog of the comb fold's `recCombConv` multi-level chain.

## The honest wall (feeds B4) — the full fold to standard form does NOT close

The rungs here descend ONLY on the disjoint-support / cup-cup slides.  Reaching the FULL Graham–Lehrer standard
form requires sinking a cup past an ADJACENT straddling crossing (the `cupSlideRelation` row), on which B1 proved
the measure ASCENDS (`straddle_resists_arcMeasure`).  So a fold that seats EVERY cup to its standard-form block
cannot use `arcMeasure` as its monovariant across the straddle — it jams exactly where B1 pins the wall, and the
resolution needs the boundary-slot `legDistance` from the crossing-only readback `standardForm(DiagramType)` (the
unbuilt residual).  The full-fold marker `fxBrauer_hasArcDescentFold` therefore stays `false`; #2013 does not close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The three Σ-carried sink rungs (conv accumulator extended + strict fuel drop) -/

/-- ★ **Cup-past-cap sink rung.**  Extends a running `BrauerConvFree8` from `startWord` to the word with the cup
sunk one place past the cap, and certifies the strict `arcMeasure` drop (given `radix` exceeds the after-word's
`cupPositionSum`). -/
theorem arcSink_cupCap (radix : Nat) (startWord : List BrauerAtom) (cupPos capPos : Nat)
    (prefixWord suffixWord : List BrauerAtom) (disjoint : cupPos ≤ capPos)
    (conv : BrauerConvFree8 startWord (prefixWord ++ ([cupAt cupPos, capAt (capPos + 2)] ++ suffixWord)))
    (secBound : cupPositionSum (prefixWord ++ ([capAt capPos, cupAt cupPos] ++ suffixWord)) < radix) :
    BrauerConvFree8 startWord (prefixWord ++ ([capAt capPos, cupAt cupPos] ++ suffixWord))
      ∧ arcMeasure radix (prefixWord ++ ([capAt capPos, cupAt cupPos] ++ suffixWord))
          < arcMeasure radix (prefixWord ++ ([cupAt cupPos, capAt (capPos + 2)] ++ suffixWord)) :=
  ⟨conv.trans (BrauerConvFree8.whiskerLeft prefixWord
      (BrauerConvFree8.whiskerRight suffixWord (distantCupCapSlideFree8 cupPos capPos disjoint))),
   arcMeasure_lt_of_primary radix _ _ (cupCap_inversions_lt cupPos capPos prefixWord suffixWord) secBound⟩

/-- ★ **Cup-past-crossing sink rung.** -/
theorem arcSink_cupCrossing (radix : Nat) (startWord : List BrauerAtom) (cupPos crossPos : Nat)
    (prefixWord suffixWord : List BrauerAtom) (disjoint : cupPos ≤ crossPos)
    (conv : BrauerConvFree8 startWord (prefixWord ++ ([cupAt cupPos, crossingAt (crossPos + 2)] ++ suffixWord)))
    (secBound : cupPositionSum (prefixWord ++ ([crossingAt crossPos, cupAt cupPos] ++ suffixWord)) < radix) :
    BrauerConvFree8 startWord (prefixWord ++ ([crossingAt crossPos, cupAt cupPos] ++ suffixWord))
      ∧ arcMeasure radix (prefixWord ++ ([crossingAt crossPos, cupAt cupPos] ++ suffixWord))
          < arcMeasure radix (prefixWord ++ ([cupAt cupPos, crossingAt (crossPos + 2)] ++ suffixWord)) :=
  ⟨conv.trans (BrauerConvFree8.whiskerLeft prefixWord
      (BrauerConvFree8.whiskerRight suffixWord (distantCupCrossingSlideFree8 cupPos crossPos disjoint))),
   arcMeasure_lt_of_primary radix _ _ (cupCrossing_inversions_lt cupPos crossPos prefixWord suffixWord) secBound⟩

/-- ★ **Cup-past-cup sink rung** — the primary is held, so the strict fuel drop comes from the secondary (no radix
bound needed). -/
theorem arcSink_cupCup (radix : Nat) (startWord : List BrauerAtom) (cupLeft cupRight : Nat)
    (prefixWord suffixWord : List BrauerAtom) (disjoint : cupLeft ≤ cupRight)
    (conv : BrauerConvFree8 startWord (prefixWord ++ ([cupAt cupLeft, cupAt (cupRight + 2)] ++ suffixWord))) :
    BrauerConvFree8 startWord (prefixWord ++ ([cupAt cupRight, cupAt cupLeft] ++ suffixWord))
      ∧ arcMeasure radix (prefixWord ++ ([cupAt cupRight, cupAt cupLeft] ++ suffixWord))
          < arcMeasure radix (prefixWord ++ ([cupAt cupLeft, cupAt (cupRight + 2)] ++ suffixWord)) :=
  ⟨conv.trans (BrauerConvFree8.whiskerLeft prefixWord
      (BrauerConvFree8.whiskerRight suffixWord (distantCupCupSlideFree8 cupLeft cupRight disjoint))),
   arcMeasure_lt_of_secondary radix _ _
     (cupCup_inversions_eq cupLeft cupRight prefixWord suffixWord).symm
     (cupCup_positions_lt cupLeft cupRight prefixWord suffixWord)⟩

/-! ## A concrete multi-rung fold (the `recCombConv` chain, on arcs) -/

/-- ★ **A two-rung Σ-carried arc-sink fold.**  The word `[cupAt 0, capAt 2, capAt 3]` (a cup with two caps to its
right) is `BrauerConvFree8` to its cup-sunk form `[capAt 0, capAt 1, cupAt 0]` — reached by sinking the cup past the
first cap (`distantCupCapSlideFree8 0 0`, whiskered by the trailing cap) then past the second
(`distantCupCapSlideFree8 0 1`, whiskered by the leading cap) — with the fuel `arcMeasure 8` STRICTLY decreasing at
each rung (`16 → 8 → 0`) and the terminal word cup-sunk (`cupNonCupInversions = 0`).  This is the arc-level analog
of the comb fold's multi-level `recCombConv`: the conv accumulator threaded through a descending chain. -/
theorem arcSinkFold_demo :
    BrauerConvFree8 [cupAt 0, capAt 2, capAt 3] [capAt 0, capAt 1, cupAt 0]
      ∧ arcMeasure 8 [capAt 0, cupAt 0, capAt 3] < arcMeasure 8 [cupAt 0, capAt 2, capAt 3]
      ∧ arcMeasure 8 [capAt 0, capAt 1, cupAt 0] < arcMeasure 8 [capAt 0, cupAt 0, capAt 3]
      ∧ cupNonCupInversions [capAt 0, capAt 1, cupAt 0] = 0 := by
  refine ⟨?_, by decide, by decide, by decide⟩
  exact BrauerConvFree8.trans
    (BrauerConvFree8.whiskerRight [capAt 3] (distantCupCapSlideFree8 0 0 (by decide)))
    (BrauerConvFree8.whiskerLeft [capAt 0] (distantCupCapSlideFree8 0 1 (by decide)))

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the Σ-carried arc-sink FOLD MECHANISM ships (B2 partial).**  The three sink rungs
(`arcSink_cupCap` / `arcSink_cupCrossing` / `arcSink_cupCup`) each extend a running `BrauerConvFree8` accumulator
across a shipped cup-sink slide AND certify a strict `arcMeasure` fuel drop; `arcSinkFold_demo` composes two rungs
into a genuine multi-step reduction with the fuel strictly decreasing `16 → 8 → 0`.  This is the `recComb`/`recCombConv`
template realized on arcs: the conv carried alongside the descending measure.  `= true`. -/
def fxBrauer_hasArcDescentSinkMechanism : Bool := true

/-- **Honesty WALL marker — the FULL arc-extraction fold to standard form is NOT assembled (walls at the
straddle).**  The rungs descend only on the disjoint-support / cup-cup slides; seating EVERY cup to its Graham–Lehrer
standard-form block requires the adjacent-straddle slide, on which B1 proved `arcMeasure` ASCENDS
(`straddle_resists_arcMeasure`).  So no `arcMeasure`-fuelled fold reaches the full standard form — it jams at the
straddle, whose descent needs the boundary-slot `legDistance` from the unbuilt crossing-only readback
`standardForm(DiagramType)`.  The full-fold `brauerWords_equalMatching_conv` stays unbuilt and
`fxBrauer_hasBrauerV2FullCompleteness` stays `false`; #2013 does not close.  `= false`. -/
def fxBrauer_hasArcDescentFold : Bool := false

end FX1Poly.Polygraph

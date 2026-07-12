import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescLoopBubbleEngine

/-! # BRAUER r41 — J-geometry: the ORDERED sink-distant-before-straddle rewrite (the r40-named "r41 piece")

r40 (`Brauer/WiringDescSingleCupEagerDriver.lean`) routed `straddleTerminal` to the dispatch step
`sinkDistantThenStraddle` and pinned (`straddleThenCap_notArrivedNaively`) that firing the straddle NAIVELY on
`[cupAt 0, crossingAt 1, crossingAt 3, capAt 5]` leaves it UN-arrived — the settled `crossingAt 0` wedged between the
relabelled cup and the distant cap.  The wall named the J-geometry residual: "the ORDERED sink-distant-before-straddle
rewrite itself is the r41 piece", hedged as needing "commuting past the straddle crossing via disjoint slides /
Yang–Baxter or a mixed-tail peel".

This round BUILDS that ordered rewrite.  The missing move is exactly the disjoint commutation — and it is already
shipped: `BrauerConvFree.interchange` (the Godement move: two generators at disjoint positions commute) embeds into
`BrauerConvFree8` via `brauerConvFree8_ofFree`.  With it the geometry composes cleanly, GENERIC in the cup position and
the distant tail:

  * ★ **`swapCrossingPastDistantStep`** — a settled crossing at `cupPos` commutes past ONE distant step of a
    `(cupPos + 1)`-tail: `[crossingAt cupPos, distantStepAtom step] ~ [distantStepAtom step, crossingAt cupPos]`, an
    `interchange` at `positionA + 2 ≤ positionB` (the crossing's `inputCount = outputCount = 2`, so the transported
    position `positionB - 2 + 2` reduces to `positionB` definitionally — no `Nat.sub` lemma).
  * ★ **`commuteSettledCrossingPastTail`** — STRUCTURAL recursion sinking the settled crossing rightward past the WHOLE
    distant tail: `crossingAt cupPos :: distantTailWord tail ~ distantTailWord tail ++ [crossingAt cupPos]`.
  * ★ **`regionArrivedExact_ofPeelSnoc`** — the arrival read-off: a distant-tail peel result with a settled crossing
    APPENDED is exact-arrived (`regionArrivedExact ((legPeelDistantTail cupPos tail).1 ++ [crossingAt xpos]) = true`
    when `xpos < cupPos`), because the peel puts the cup at the region tail and the appended crossing is a settled
    topPerm right of it — `regionArrivedExact` is transparent to the peel's leading non-cup crossings/caps.
  * ★★ **`sinkDistantThenStraddle_arrives`** — THE ordered rewrite, GENERIC in `cupPos` and the distant tail
    (`tail : List (DistantSlideStep (cupPos + 1))`): straddle-relabel the cup to `cupPos + 1`, COMMUTE the settled
    `crossingAt cupPos` past the distant tail, then SINK the cup past the (now adjacent) distant tail via the r36
    `legPeelDistantTail`, landing a real `BrauerConvFree8` reduction to an EXACT-arrived region.  The J-geometry
    residual the r40 wall named, CLOSED — where `straddleThenCap_notArrivedNaively` recorded the naive straddle
    jamming, the ordered rewrite arrives (`sinkDistantThenStraddle_arrivesWitness` pins the exact r40 witness).

## The honest wall — the TOTAL typed dispatch is STILL NOT built (J-loop + J-geometry closed, J-transport + assembly remain)

J-loop (`Brauer/WiringDescLoopBubbleEngine.lean`) and J-geometry (this file) are both discharged, but the TOTAL region
DISPATCH — synthesizing the typed `RegionCupOutcome` from `classifyFirstCupNeighbour`'s decision over an ARBITRARY flat
region — stays open on J-transport (each dispatch arm's `Nat.beq _ _ = true → _ = _` positional reshape + `Eq.rec`
transport across the cons-indexed family) and the TOTAL ASSEMBLY threading all 11 arms into one structural function.
So `fxBrauer_hasRegionDriverTotalDispatch`, `fxBrauer_hasSingleCupTotalDecision`, `fxBrauer_hasSingleCupPeelDischarged`,
and the four completeness / inner-descent masters (`fxBrauer_hasStagedInnerDescentDischarged`,
`fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness`) all
STAY `false`; this round is PURELY ADDITIVE, no master flip is fabricated.  Every residual is a route / transport gap,
never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).

Raw Lean 4 + Init; STRUCTURAL recursion on the distant tail (no `omega` / `simp`-AC / `native_decide` /
`WellFounded.fix` / `propext` — the `interchange` transported position `positionB - 2 + 2` reduces DEFINITIONALLY, and
`List.cons_append` is definitional, so no `Nat.sub` / `List.append_assoc` lemma is used, both of which leak `propext`).
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the settled-crossing commutation past a distant tail (via the Godement interchange) -/

/-- ★ **A settled crossing at `cupPos` commutes past ONE distant step of a `(cupPos + 1)`-tail.**  Each step's decoded
position is `≥ (cupPos + 1) + 2 ≥ cupPos + 2`, so the Godement `interchange` fires; the crossing's `inputCount =
outputCount = 2` makes the transported position `positionB - 2 + 2` reduce to `positionB` definitionally. -/
theorem swapCrossingPastDistantStep (cupPos : Nat) (step : DistantSlideStep (cupPos + 1)) :
    BrauerConvFree8 [crossingAt cupPos, distantStepAtom step]
      [distantStepAtom step, crossingAt cupPos] := by
  match step with
  | .crossing crossPos disjoint =>
      have windowFits : cupPos + crossingWiring.inputCount ≤ crossPos + 2 :=
        Nat.le_succ_of_le (Nat.succ_le_succ disjoint)
      exact brauerConvFree8_ofFree
        (BrauerConvFree.interchange cupPos (crossPos + 2) crossingWiring crossingWiring windowFits)
  | .cap capPos disjoint =>
      have windowFits : cupPos + crossingWiring.inputCount ≤ capPos + 2 :=
        Nat.le_succ_of_le (Nat.succ_le_succ disjoint)
      exact brauerConvFree8_ofFree
        (BrauerConvFree.interchange cupPos (capPos + 2) crossingWiring capWiring windowFits)

/-- ★ **The settled crossing at `cupPos` commutes rightward past the WHOLE distant tail** — structural recursion:
`crossingAt cupPos :: distantTailWord tail ~ distantTailWord tail ++ [crossingAt cupPos]`. -/
theorem commuteSettledCrossingPastTail (cupPos : Nat) :
    (tail : List (DistantSlideStep (cupPos + 1))) →
    BrauerConvFree8 (crossingAt cupPos :: distantTailWord tail)
      (distantTailWord tail ++ [crossingAt cupPos])
  | [] => brauerConvFree8_ofFree (BrauerConvFree.refl [crossingAt cupPos])
  | step :: rest =>
      BrauerConvFree8.trans
        (BrauerConvFree8.whiskerRight (distantTailWord rest) (swapCrossingPastDistantStep cupPos step))
        (BrauerConvFree8.whiskerLeft [distantStepAtom step]
          (commuteSettledCrossingPastTail cupPos rest))

/-! ## B — the exact-arrival read-off for a peel result with a settled crossing appended -/

/-- ★ **A distant-tail peel result with a settled crossing appended is EXACT-arrived.**  `legPeelDistantTail` puts the
cup at the region tail with only relabelled crossings/caps left of it; appending `crossingAt xpos` (a settled topPerm,
`xpos < cupPos`) keeps `regionArrivedExact = true`, since it is transparent to the leading non-cup atoms and the base
suffix `[crossingAt xpos]` is a settled crossing left of the cup.  Structural recursion on the tail. -/
theorem regionArrivedExact_ofPeelSnoc (cupPos xpos : Nat) (settledLeft : Nat.blt xpos cupPos = true) :
    (tail : List (DistantSlideStep cupPos)) →
    regionArrivedExact ((legPeelDistantTail cupPos tail).1 ++ [crossingAt xpos]) = true
  | [] => by
      show allSettledLeftOfCup cupPos [crossingAt xpos] = true
      show (isCrossingAtom (crossingAt xpos) && Nat.blt xpos cupPos) && true = true
      rw [settledLeft]; rfl
  | .crossing _ _ :: rest =>
      regionArrivedExact_ofPeelSnoc cupPos xpos settledLeft rest
  | .cap _ _ :: rest =>
      regionArrivedExact_ofPeelSnoc cupPos xpos settledLeft rest

/-! ## C — the ORDERED sink-distant-before-straddle rewrite -/

/-- ★★ **The ORDERED sink-distant-before-straddle rewrite — J-geometry, GENERIC in `cupPos` and the distant tail.**
For a cup at `cupPos` with an adjacent straddle crossing `crossingAt (cupPos + 1)` then a distant tail
(`tail : List (DistantSlideStep (cupPos + 1))`, positions `≥ cupPos + 3`): (1) straddle-relabel the cup to `cupPos + 1`,
(2) COMMUTE the settled `crossingAt cupPos` rightward past the distant tail (`commuteSettledCrossingPastTail`), (3) SINK
the cup past the now-adjacent distant tail (`legPeelDistantTail (cupPos + 1) tail`).  The result carries a real
`BrauerConvFree8` reduction and is EXACT-arrived (`regionArrivedExact_ofPeelSnoc`).  Where the r40
`straddleThenCap_notArrivedNaively` recorded the naive straddle jamming, the ordered rewrite ARRIVES. -/
theorem sinkDistantThenStraddle_arrives (cupPos : Nat)
    (tail : List (DistantSlideStep (cupPos + 1))) :
    BrauerConvFree8 (cupAt cupPos :: crossingAt (cupPos + 1) :: distantTailWord tail)
        ((legPeelDistantTail (cupPos + 1) tail).1 ++ [crossingAt cupPos])
      ∧ regionArrivedExact ((legPeelDistantTail (cupPos + 1) tail).1 ++ [crossingAt cupPos]) = true := by
  refine ⟨?_, ?_⟩
  · have straddleRelabel : BrauerConvFree8
        (cupAt cupPos :: crossingAt (cupPos + 1) :: distantTailWord tail)
        (cupAt (cupPos + 1) :: crossingAt cupPos :: distantTailWord tail) :=
      BrauerConvFree8.whiskerRight (distantTailWord tail) (straddleSlideFree8_clean cupPos)
    have commuteSettled : BrauerConvFree8
        (cupAt (cupPos + 1) :: crossingAt cupPos :: distantTailWord tail)
        (cupAt (cupPos + 1) :: (distantTailWord tail ++ [crossingAt cupPos])) :=
      BrauerConvFree8.whiskerLeft [cupAt (cupPos + 1)] (commuteSettledCrossingPastTail cupPos tail)
    have sinkCup : BrauerConvFree8
        (cupAt (cupPos + 1) :: (distantTailWord tail ++ [crossingAt cupPos]))
        ((legPeelDistantTail (cupPos + 1) tail).1 ++ [crossingAt cupPos]) :=
      BrauerConvFree8.whiskerRight [crossingAt cupPos] (legPeelDistantTail (cupPos + 1) tail).2.1
    exact straddleRelabel.trans (commuteSettled.trans sinkCup)
  · exact regionArrivedExact_ofPeelSnoc (cupPos + 1) cupPos (bltSucc cupPos) tail

/-- ★★ **The ordered rewrite on the exact r40 witness, machine-checked.**  On `[cupAt 0, crossingAt 1, crossingAt 3,
capAt 5]` — where `straddleThenCap_notArrivedNaively` showed the naive straddle does NOT arrive — the ordered rewrite
reduces to `[crossingAt 1, capAt 3, cupAt 1, crossingAt 0]` and IS exact-arrived. -/
theorem sinkDistantThenStraddle_arrivesWitness :
    BrauerConvFree8 [cupAt 0, crossingAt 1, crossingAt 3, capAt 5]
        [crossingAt 1, capAt 3, cupAt 1, crossingAt 0]
      ∧ regionArrivedExact [crossingAt 1, capAt 3, cupAt 1, crossingAt 0] = true :=
  sinkDistantThenStraddle_arrives 0 [.crossing 1 (by decide), .cap 3 (by decide)]

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the ORDERED sink-distant-before-straddle rewrite SHIPS (J-geometry CLOSED).**  The Godement
`interchange` (embedded into `BrauerConvFree8` via `brauerConvFree8_ofFree`) supplies the missing commutation:
`swapCrossingPastDistantStep` / `commuteSettledCrossingPastTail` sink the settled crossing past the distant tail,
`regionArrivedExact_ofPeelSnoc` reads off exact arrival, and `sinkDistantThenStraddle_arrives` composes them with the
straddle relabel + the r36 distant-tail peel into the ordered rewrite, GENERIC in `cupPos` and the tail
(`sinkDistantThenStraddle_arrivesWitness` pins the exact r40 witness the naive straddle jammed).  The J-geometry residual
the r40 wall named, CLOSED.  `= true`. -/
def fxBrauer_hasStraddleSinkOrdered : Bool := true

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r41 ordered-straddle-sink terminal state — MACHINE-CHECKED.**  The two r41 markers are `true` (the
J-loop engine lemma, the J-geometry ordered rewrite), built on the r39/r40 factored cup arrival / region classifier /
eager dispatch, while the total region dispatch (r39), the r38 total decision, the r36 single-cup peel discharge, and
all four completeness / inner-descent masters STAY `false`.  A `rfl`-conjunction the kernel checks; purely additive, no
master flip is fabricated — J-transport + the total assembly remain. -/
theorem fxBrauer_straddleSinkOrderedTerminalState :
    fxBrauer_hasStraddleSinkOrdered = true
      ∧ fxBrauer_hasLoopBubbleEngineLemma = true
      ∧ fxBrauer_hasEagerRegionDispatch = true
      ∧ fxBrauer_hasRegionCupClassifier = true
      ∧ fxBrauer_hasRegionDriverTotalDispatch = false
      ∧ fxBrauer_hasSingleCupTotalDecision = false
      ∧ fxBrauer_hasSingleCupPeelDischarged = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph

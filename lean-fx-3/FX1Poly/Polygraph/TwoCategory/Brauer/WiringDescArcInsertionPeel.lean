import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcInsertion

/-! # BRAUER r35 — the single-arc PEEL STEP over the r34 leg fuel + the J1 working-region seam resolved

r34 (`Brauer/WiringDescArcInsertion.lean`) shipped the LOCAL per-cup leg fuel `legLexFuel` (leftmost-cup distance
`atomsRightOfFirstCup` primary + straddle window `straddleBitAtFirstCup` tie-break) and proved its PRIMARY (distance)
descent generalizes to arbitrary cupless-prefix + suffix context (`legFuel_leftmostCupCrossing_lt` /
`legFuel_leftmostCupCap_lt`).  Its wall marker `fxBrauer_hasLocalLegFuelGlobalFold = false` named four residuals; this
round discharges the FIRST-level piece of (J1): the single-arc PEEL STEP (a cup sinks to its cup-block slot carrying a
whisker-free `BrauerConvFree8` reduction with the leg fuel strictly descending) AND the J1 SEAM the two-level assembly
tripped on — the whole-word leg fuel reads the placed (already-peeled) cup and GROWS with the working region, so the
INNER measure must be SCOPED to the working region, whiskering the standard prefix off.

## The J1 seam, truth-probed then resolved

The OUTER driver maintains `wholeWord = standardPrefix ++ workingRegion`, where `standardPrefix` accumulates ALREADY-
PLACED arcs (it CONTAINS placed cups).  The whole-word `atomsRightOfFirstCup` reads the FIRST cup — a PLACED one — and
so INFLATES as the working region grows (`#eval`-confirmed, before proving):

```
  atomsRightOfFirstCup [crossingAt 1, cupAt 9, crossingAt 3,               cupAt 0] = 2
  atomsRightOfFirstCup [crossingAt 1, cupAt 9, crossingAt 3, crossingAt 4, cupAt 0] = 3   -- GROWS with the region
```

Resolution (a) WORKING-REGION SCOPING (not the rejected (b) `hasNoUnpeeledCup` weakening, which the flat `isCupAtom`
cannot express — a cup is a cup): the peeled arc LEAVES the measured region.  The INNER fuel is
`legLexFuel radix workingRegion`, and within the working region the leftmost cup's LOCAL prefix is exactly the non-cups
it sinks past — genuinely cupless (`hasNoCup` UNCHANGED, applied to the LOCAL prefix).  The rungs whisker the standard
prefix off via `BrauerConvFree8.whiskerLeft` and measure ONLY the working region.

## What this file ships (each zero-axiom, structural / `decide` on closed literals — no `omega` / `simp`-AC /
`native_decide` / `WellFounded.fix` / `propext`; per-declaration `#assert_no_axioms` in the audit twin)

  * **`hasNoCup_append`** — the compositional cupless read: `hasNoCup (a ++ b) = hasNoCup a && hasNoCup b`.  The seam
    algebra (a placed cup in `a` makes the whole prefix non-cupless, which is exactly why the measure must be scoped to
    the working region).  Standalone structural recursion on the first list (full-enum `cases isCupAtom`, NO
    `List.append_assoc`, NO wildcard arm).
  * ★ **`legSink_cupCrossing` / `legSink_cupCap`** — the two Σ-carried leg-fuel sink RUNGS: given a running
    `BrauerConvFree8 startWord (prefix ++ [cup, nonCup] ++ suffix)`, produce the extended
    `BrauerConvFree8 startWord (prefix ++ [nonCup, cup] ++ suffix)` (whiskered distant slide) TOGETHER with a strict
    `legLexFuel` decrease (the r34 PRIMARY descent, tie-break bounded by `radix > 1`).  The `arcSink_*` template of
    `WiringDescArcDescentFold` lifted from `arcMeasure` to `legLexFuel` (no `cupPositionSum < radix` side-condition —
    the leg fuel's secondary is bounded generically).
  * ★★ **`legSink_cupCrossing_underStandardPrefix` / `legSink_cupCap_underStandardPrefix`** — THE J1-seam-resolving
    rungs: an additional `standardPrefix` (which MAY contain placed cups) is whiskered OFF via a second `whiskerLeft`
    and NEVER enters the measure; the fuel is the WORKING-REGION `legLexFuel`, whose local prefix is cupless.  This is
    resolution (a) made a first-class rung.
  * ★★ **`legPeelToArrival_demo`** — THE flagship: the width-4 single-cup PEEL, the cup sunk from the head to its
    cup-block slot `[cupAt 0, crossingAt 3, crossingAt 4, capAt 5] ↝ [crossingAt 1, crossingAt 2, capAt 3, cupAt 0]`
    (two distant crossing rungs then a distant cap rung, ONLY free `BrauerConvFree8` constructors) with `legLexFuel 8`
    STRICTLY descending `24 > 16 > 8 > 0` at every rung and arrival pinned (`atomsRightOfFirstCup = 0`).
  * **`legPeelToArrival_topPermTail_demo`** — the honest companion: arrival is NOT always the tail.  On
    `[cupAt 0, capAt 3, crossingAt 8] ↝ [capAt 1, cupAt 0, crossingAt 8]` the leg fuel descends `16 > 8` but a topPerm
    crossing sits LEGITIMATELY right of the arrived cup, so `atomsRightOfFirstCup = 1 ≠ 0` — the precise slot-arrival
    predicate (working-region factoring) is part of the still-unbuilt OUTER assembly.

## The honest wall — the OUTER two-level assembly + J2/J3/J4 are UNBUILT (named IN this file, no new ledger)

r35 delivers the single-arc peel step and the J1 seam resolution, NOT the full two-level fold: the OUTER
`arcCountFuel` (`fxBrauer_hasStagedArcCountFuel = true`) threaded with the INNER leg fuel through a structural
recursion peeling EVERY arc; (J2) the cap-side ∗-dual sink (caps sink to the FRONT with their own `capLegLexFuel`,
which does not yet exist); (J3) the `bottomCount = 0` all-cup/all-loop class; (J4) the whisker-free driver consuming a
`DiagramType` + the R3-A connectivity roundtrip its per-step guard needs (the long pole, the still-`false`
`fxBrauer_hasExt5CorrectedRoundtripProof`).  So `fxBrauer_hasLegFuelOuterAssembly` STAYS `false`, and
`fxBrauer_hasStagedInnerDescentDischarged`, `fxBrauer_hasFreeBrauerStraighteningNF`,
`fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness` all STAY `false`; this round is PURELY
ADDITIVE, no master flip is fabricated, #2013 does NOT close.  Every residual is a route / measure gap, never a truth
gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6). -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the compositional cupless read (the seam algebra) -/

/-- ★ **`hasNoCup` is multiplicative over append.**  `hasNoCup (wordLeft ++ wordRight) = hasNoCup wordLeft &&
hasNoCup wordRight` — a concatenation is cupless exactly when both halves are.  A placed cup anywhere in `wordLeft`
makes the whole prefix non-cupless: the precise reason the OUTER measure cannot read the whole word and must be scoped
to the working region.  Standalone structural recursion on `wordLeft` (full-enum `cases isCupAtom`, NO
`List.append_assoc`). -/
theorem hasNoCup_append : (wordLeft wordRight : List BrauerAtom) →
    hasNoCup (wordLeft ++ wordRight) = (hasNoCup wordLeft && hasNoCup wordRight)
  | [], _ => rfl
  | atom :: rest, wordRight => by
      show cond (isCupAtom atom) false (hasNoCup (rest ++ wordRight))
         = (cond (isCupAtom atom) false (hasNoCup rest) && hasNoCup wordRight)
      cases hAtom : isCupAtom atom with
      | true => rfl
      | false => exact hasNoCup_append rest wordRight

/-! ## B — the two Σ-carried leg-fuel sink rungs (the `arcSink_*` template, on `legLexFuel`) -/

/-- ★ **Cup-past-crossing leg-fuel sink rung.**  Extends a running `BrauerConvFree8` from `startWord` to the word with
the leftmost cup sunk one place past a DISTANT crossing (the whiskered `distantCupCrossingSlideFree8`), and certifies
the strict `legLexFuel` drop via the r34 PRIMARY descent (the tie-break is bounded by `radix > 1`; no
`cupPositionSum < radix` side-condition, unlike the `arcMeasure` rung). -/
theorem legSink_cupCrossing (radix cupPos crossPos : Nat)
    (startWord prefixWord suffixWord : List BrauerAtom)
    (cupless : hasNoCup prefixWord = true) (radixBig : 1 < radix) (disjoint : cupPos ≤ crossPos)
    (conv : BrauerConvFree8 startWord (prefixWord ++ ([cupAt cupPos, crossingAt (crossPos + 2)] ++ suffixWord))) :
    BrauerConvFree8 startWord (prefixWord ++ ([crossingAt crossPos, cupAt cupPos] ++ suffixWord))
      ∧ legLexFuel radix (prefixWord ++ ([crossingAt crossPos, cupAt cupPos] ++ suffixWord))
          < legLexFuel radix (prefixWord ++ ([cupAt cupPos, crossingAt (crossPos + 2)] ++ suffixWord)) :=
  ⟨conv.trans (BrauerConvFree8.whiskerLeft prefixWord
      (BrauerConvFree8.whiskerRight suffixWord (distantCupCrossingSlideFree8 cupPos crossPos disjoint))),
   legFuel_leftmostCupCrossing_lt radix cupPos crossPos prefixWord suffixWord cupless radixBig⟩

/-- ★ **Cup-past-cap leg-fuel sink rung** — the ∗-mirror, sinking the leftmost cup past a DISTANT cap. -/
theorem legSink_cupCap (radix cupPos capPos : Nat)
    (startWord prefixWord suffixWord : List BrauerAtom)
    (cupless : hasNoCup prefixWord = true) (radixBig : 1 < radix) (disjoint : cupPos ≤ capPos)
    (conv : BrauerConvFree8 startWord (prefixWord ++ ([cupAt cupPos, capAt (capPos + 2)] ++ suffixWord))) :
    BrauerConvFree8 startWord (prefixWord ++ ([capAt capPos, cupAt cupPos] ++ suffixWord))
      ∧ legLexFuel radix (prefixWord ++ ([capAt capPos, cupAt cupPos] ++ suffixWord))
          < legLexFuel radix (prefixWord ++ ([cupAt cupPos, capAt (capPos + 2)] ++ suffixWord)) :=
  ⟨conv.trans (BrauerConvFree8.whiskerLeft prefixWord
      (BrauerConvFree8.whiskerRight suffixWord (distantCupCapSlideFree8 cupPos capPos disjoint))),
   legFuel_leftmostCupCap_lt radix cupPos capPos prefixWord suffixWord cupless radixBig⟩

/-! ## C — the J1-seam-resolving rungs (the standard prefix whiskered off, measure on the working region) -/

/-- ★★ **Cup-past-crossing sink rung UNDER a standard prefix — the J1 seam resolved.**  The OUTER driver's
`standardPrefix` (which MAY contain placed cups) is whiskered OFF by a SECOND `whiskerLeft` and NEVER enters the
measure; the strict `legLexFuel` drop is stated on the WORKING REGION `localPrefix ++ [cup, crossing] ++ suffix`,
whose local prefix `localPrefix` is genuinely cupless (`cuplessLocal`).  This is working-region scoping made a
first-class rung — the placed cup that inflated the whole-word measure is factored out. -/
theorem legSink_cupCrossing_underStandardPrefix (radix cupPos crossPos : Nat)
    (startWord standardPrefix localPrefix suffixWord : List BrauerAtom)
    (cuplessLocal : hasNoCup localPrefix = true) (radixBig : 1 < radix) (disjoint : cupPos ≤ crossPos)
    (conv : BrauerConvFree8 startWord
        (standardPrefix ++ (localPrefix ++ ([cupAt cupPos, crossingAt (crossPos + 2)] ++ suffixWord)))) :
    BrauerConvFree8 startWord
        (standardPrefix ++ (localPrefix ++ ([crossingAt crossPos, cupAt cupPos] ++ suffixWord)))
      ∧ legLexFuel radix (localPrefix ++ ([crossingAt crossPos, cupAt cupPos] ++ suffixWord))
          < legLexFuel radix (localPrefix ++ ([cupAt cupPos, crossingAt (crossPos + 2)] ++ suffixWord)) :=
  ⟨conv.trans (BrauerConvFree8.whiskerLeft standardPrefix
      (BrauerConvFree8.whiskerLeft localPrefix
        (BrauerConvFree8.whiskerRight suffixWord (distantCupCrossingSlideFree8 cupPos crossPos disjoint)))),
   legFuel_leftmostCupCrossing_lt radix cupPos crossPos localPrefix suffixWord cuplessLocal radixBig⟩

/-- ★★ **Cup-past-cap sink rung UNDER a standard prefix — the ∗-mirror seam resolver.** -/
theorem legSink_cupCap_underStandardPrefix (radix cupPos capPos : Nat)
    (startWord standardPrefix localPrefix suffixWord : List BrauerAtom)
    (cuplessLocal : hasNoCup localPrefix = true) (radixBig : 1 < radix) (disjoint : cupPos ≤ capPos)
    (conv : BrauerConvFree8 startWord
        (standardPrefix ++ (localPrefix ++ ([cupAt cupPos, capAt (capPos + 2)] ++ suffixWord)))) :
    BrauerConvFree8 startWord
        (standardPrefix ++ (localPrefix ++ ([capAt capPos, cupAt cupPos] ++ suffixWord)))
      ∧ legLexFuel radix (localPrefix ++ ([capAt capPos, cupAt cupPos] ++ suffixWord))
          < legLexFuel radix (localPrefix ++ ([cupAt cupPos, capAt (capPos + 2)] ++ suffixWord)) :=
  ⟨conv.trans (BrauerConvFree8.whiskerLeft standardPrefix
      (BrauerConvFree8.whiskerLeft localPrefix
        (BrauerConvFree8.whiskerRight suffixWord (distantCupCapSlideFree8 cupPos capPos disjoint)))),
   legFuel_leftmostCupCap_lt radix cupPos capPos localPrefix suffixWord cuplessLocal radixBig⟩

/-! ## D — the flagship: a single-arc PEEL to its cup-block slot, leg fuel descending at every rung -/

/-- ★★ **THE single-arc peel to arrival.**  The width-4 word `[cupAt 0, crossingAt 3, crossingAt 4, capAt 5]` (a cup
at the head with two crossings then a cap to its right) is `BrauerConvFree8` to its cup-sunk form
`[crossingAt 1, crossingAt 2, capAt 3, cupAt 0]` — the cup sunk to the tail-slot by two distant cup-past-crossing
slides then one distant cup-past-cap slide (`distantCupCrossingSlideFree8 0 1`, then `0 2` whiskered by the leading
crossing, then `distantCupCapSlideFree8 0 3` whiskered by both) — with `legLexFuel 8` STRICTLY descending
`24 > 16 > 8 > 0` at every rung and the leftmost cup ARRIVED (`atomsRightOfFirstCup = 0`).  Threads ONLY the free
`BrauerConvFree8` constructors; the arc-level analog of the comb fold's `recCombConv`, on the LEG fuel. -/
theorem legPeelToArrival_demo :
    BrauerConvFree8 [cupAt 0, crossingAt 3, crossingAt 4, capAt 5]
                    [crossingAt 1, crossingAt 2, capAt 3, cupAt 0]
      ∧ legLexFuel 8 [crossingAt 1, cupAt 0, crossingAt 4, capAt 5]
          < legLexFuel 8 [cupAt 0, crossingAt 3, crossingAt 4, capAt 5]
      ∧ legLexFuel 8 [crossingAt 1, crossingAt 2, cupAt 0, capAt 5]
          < legLexFuel 8 [crossingAt 1, cupAt 0, crossingAt 4, capAt 5]
      ∧ legLexFuel 8 [crossingAt 1, crossingAt 2, capAt 3, cupAt 0]
          < legLexFuel 8 [crossingAt 1, crossingAt 2, cupAt 0, capAt 5]
      ∧ atomsRightOfFirstCup [crossingAt 1, crossingAt 2, capAt 3, cupAt 0] = 0 := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  exact BrauerConvFree8.trans
    (BrauerConvFree8.whiskerRight [crossingAt 4, capAt 5] (distantCupCrossingSlideFree8 0 1 (by decide)))
    (BrauerConvFree8.trans
      (BrauerConvFree8.whiskerLeft [crossingAt 1]
        (BrauerConvFree8.whiskerRight [capAt 5] (distantCupCrossingSlideFree8 0 2 (by decide))))
      (BrauerConvFree8.whiskerLeft [crossingAt 1, crossingAt 2]
        (distantCupCapSlideFree8 0 3 (by decide))))

/-- ★ **Arrival is NOT always the tail — the honest companion.**  The cup-block slot has topPerm crossings and circle
atoms legitimately to its right (the standard form is `... ++ cupWord ++ crossingWord topPerm ++ circleWord`).  On
`[cupAt 0, capAt 3, crossingAt 8]` the cup sinks past the cap (`distantCupCapSlideFree8 0 1`) with `legLexFuel 8`
descending `16 > 8`, but the trailing `crossingAt 8` (a topPerm crossing) sits LEGITIMATELY right of the arrived cup,
so `atomsRightOfFirstCup = 1 ≠ 0`.  The precise slot-arrival predicate (the working-region factoring the OUTER driver
needs) is therefore part of the still-unbuilt two-level assembly, NOT `atomsRightOfFirstCup = 0`. -/
theorem legPeelToArrival_topPermTail_demo :
    BrauerConvFree8 [cupAt 0, capAt 3, crossingAt 8] [capAt 1, cupAt 0, crossingAt 8]
      ∧ legLexFuel 8 [capAt 1, cupAt 0, crossingAt 8] < legLexFuel 8 [cupAt 0, capAt 3, crossingAt 8]
      ∧ atomsRightOfFirstCup [capAt 1, cupAt 0, crossingAt 8] = 1 := by
  refine ⟨?_, by decide, by decide⟩
  exact BrauerConvFree8.whiskerRight [crossingAt 8] (distantCupCapSlideFree8 0 1 (by decide))

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the single-arc PEEL STEP and its leg-fuel rungs SHIP.**  The two Σ-carried sink rungs
(`legSink_cupCrossing` / `legSink_cupCap`) carry a whisker-free `BrauerConvFree8` reduction alongside a strict
`legLexFuel` decrease, and the flagship `legPeelToArrival_demo` sinks one cup all the way to its slot with the fuel
descending `24 > 16 > 8 > 0`.  The single-arc completion the outer fold peels per step.  `= true`. -/
def fxBrauer_hasLegFuelPeelRung : Bool := true

/-- ★★ **Honesty marker — the J1 working-region seam is RESOLVED.**  The whole-word leg fuel reads a PLACED cup and
grows with the working region (`#eval`-probed `2 → 3`); the resolving rungs
(`legSink_cupCrossing_underStandardPrefix` / `legSink_cupCap_underStandardPrefix`) whisker the `standardPrefix` OFF and
state the strict `legLexFuel` drop on the WORKING REGION only, whose local prefix is genuinely cupless.  Resolution
(a) working-region scoping, made a first-class rung; the rejected (b) `hasNoUnpeeledCup` weakening cannot be expressed
by the flat `isCupAtom`.  `= true`. -/
def fxBrauer_hasLegFuelWorkingRegionScoped : Bool := true

/-- ★★ **Honesty marker — a concrete single-arc peel reaches arrival.**  `legPeelToArrival_demo` sinks the leftmost
cup from the head to `atomsRightOfFirstCup = 0` carrying a real free `BrauerConvFree8` reduction, and the honest
companion `legPeelToArrival_topPermTail_demo` records that arrival ≠ tail in general (a topPerm crossing legitimately
right).  `= true`. -/
def fxBrauer_hasLegFuelPeelToArrival : Bool := true

/-- **Honesty WALL marker — the OUTER two-level assembly is NOT built; #2013 does NOT close.**  r35 ships the
single-arc peel step + the J1 seam resolution, NOT the full fold: the OUTER `arcCountFuel`
(`fxBrauer_hasStagedArcCountFuel = true`) threaded with the INNER leg fuel through a structural recursion peeling
EVERY arc; (J2) the cap-side ∗-dual sink (no `capLegLexFuel` exists yet); (J3) the `bottomCount = 0` all-cup/all-loop
class; (J4) the `DiagramType`-driver + the R3-A connectivity roundtrip (the long pole).  So
`fxBrauer_hasStagedInnerDescentDischarged` STAYS `false`, and `fxBrauer_hasFreeBrauerStraighteningNF`,
`fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness` all STAY `false`.  A route / measure gap,
never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).  `= false`. -/
def fxBrauer_hasLegFuelOuterAssembly : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r35 terminal state — MACHINE-CHECKED.**  The three new ingredient markers are `true` (the leg-fuel
peel rungs, the working-region seam resolution, a concrete single-arc peel to arrival), built on the shipped r34
`fxBrauer_hasLocalLegFuelDescent` (the INNER measure) and the shipped OUTER `fxBrauer_hasStagedArcCountFuel` (the
handoff target), while the OUTER two-level assembly and all three completeness masters STAY `false`.  A `rfl`-
conjunction the kernel checks; this round is purely additive, no master flip is fabricated, #2013 does NOT close. -/
theorem fxBrauer_legFuelPeelTerminalState :
    fxBrauer_hasLegFuelPeelRung = true
      ∧ fxBrauer_hasLegFuelWorkingRegionScoped = true
      ∧ fxBrauer_hasLegFuelPeelToArrival = true
      ∧ fxBrauer_hasLocalLegFuelDescent = true
      ∧ fxBrauer_hasStagedArcCountFuel = true
      ∧ fxBrauer_hasLegFuelOuterAssembly = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph

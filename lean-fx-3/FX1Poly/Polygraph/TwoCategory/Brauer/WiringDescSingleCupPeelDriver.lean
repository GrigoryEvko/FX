import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescSeamRungs

/-! # BRAUER r38 — the single-cup PEEL DRIVER: the three-fated outcome + the outer sink-step threading

r37 (`Brauer/WiringDescSeamRungs.lean`) completed the per-cup move set for the exhaustive neighbor split — the two
SEAM rungs (`legSink_snakeAnnihilate_underStandardPrefix` / `legSink_cupUntwist_underStandardPrefix`) joining the r36
distant-tail peel `legPeelDistantTail` and the straddle terminal-cleanup rung.  Its wall
(`fxBrauer_hasSeamRungOuterAssembly = false`) named the still-missing OUTER DRIVER: the assembly threading the two seam
rungs + `legPeelDistantTail` under a nested-structural lexicographic measure `(wordLength, legLexFuel)` (the seam rungs
drop coordinate 1 = word length, the slides drop coordinate 2 = the leg fuel) over a cup with the placed cups untouched,
plus the `loop` / `bottomCount = 0` circle class the snake classifier's loop arm routes to.

This round ships the OUTER driver in its combinator form, truth-probed on the four mixed hostiles the recon named
(each `#eval`-confirmed BEFORE proving — the classifier arm, the measure legs, and the fate):

  * (a) `[cupAt 1, capAt 0, crossingAt 8]` — `snakeNeighborKind 1 0 = annihilateLeft` (S1); the cup ANNIHILATES with the
    adjacent cap, `countAtoms 3 → 1`.  Fate `.annihilated`.
  * (b) `[cupAt 2, crossingAt 2, crossingAt 5, capAt 6]` — an UNTWIST (crossing at `cupPos`, `countAtoms` −1) then the
    DISTANT tail `[crossingAt 5, capAt 6]` sinks the cup to arrival (`atomsRightOfFirstCup = 0`).  Fate `.arrived`.
  * (c) `[cupAt 0, capAt 0]` — `snakeNeighborKind 0 0 = loop`; the cup + cap close a bubble
    (`brauerDiagramOf 0 [cupAt 0, capAt 0]` reads `loops := 1 ≠ 0`), NOT convertible to `[]`.  Fate `.loop`.
  * (d) `[cupAt 0, crossingAt 1]` — a STRADDLE relabel to `[cupAt 1, crossingAt 0]`: a topPerm crossing sits
    LEGITIMATELY left of the cup, so the raw `atomsRightOfFirstCup = 1 ≠ 0` FALSE-NEGATIVES arrival.  This is the honest
    companion, NOT a `.arrived` outcome — the working-region-factoring gate.

## What this file ships (each zero-axiom; nested-structural — the outer `peelUntwistRun` recurses on a `Nat` count, the
inner `legPeelDistantTail` recurses on the distant-tail descriptor; no `omega` / `simp`-AC / `native_decide` /
`WellFounded.fix` / `propext`; per-declaration `#assert_no_axioms` in the audit twin)

  * **`SingleCupOutcome`** — the UNIFIED three-fated result of peeling one cup, each fate carrying a genuine
    `BrauerConvFree8` certificate: `.arrived` (arrival `atomsRightOfFirstCup = 0`), `.annihilated` (the snake, a strict
    `countAtoms` drop), `.loop` (the circle bubble, a `brauerDiagramOf … ≠ brauerDiagramOf … []` non-emptiness witness).
    The three per-cup fates the r34–r37 rungs produced separately, now one Sum.
  * ★ **`SingleCupOutcome.prepend`** — the OUTER sink-step combinator: given any length-non-increasing
    `BrauerConvFree8 regionBig regionSmall` and the length bound, threads it onto an outcome for `regionSmall`,
    trans-composing the certificate and transporting the fate witness.  This is the driver's core — the seam / slide
    rungs fed onto a running outcome.
  * **The terminal builders** (`outcomeArrivedOfDistantTail`, `outcomeAnnihilateS1` / `_S2`, `outcomeLoopAtZero`) —
    wrapping the shipped rungs into the three fates: the r36 distant-tail peel into `.arrived`, the r37 snake into
    `.annihilated`, the r37 loop bubble into `.loop`.
  * **The named prepend seam steps** (`prependUntwist`, `prependStraddle`) — the two continue-steps (the cup survives)
    as first-class prepend combinators: untwist drops `countAtoms` by 1, straddle holds it and drops the leg-fuel bit.
  * ★★ **`peelUntwistRun`** — a GENUINE outer structural recursion (on a `Nat` count) sinking a cup past a run of
    `count` untwist crossings-on-its-own-legs, composing with the inner distant-tail peel: the nested-structural driver
    over a two-parameter-generic region (`peelUntwistRunThenDistant_demo`).
  * **`peelHostile_fates`** — the four hostiles run end-to-end through the outcome type, their fates pinned by `rfl`.

## The honest wall — the TOTAL region-decision is UNBUILT; #2013 does NOT close (named IN this file, no new ledger)

The driver RUNS a peel: given the ordered moves it threads the seam rungs + `legPeelDistantTail` into a three-fated
`SingleCupOutcome` under the `(wordLength, legLexFuel)` measure.  What is NOT built is the TOTAL DECISION — synthesizing
those moves from an ARBITRARY region by scanning for the leftmost cup and classifying its right neighbor — because two
blockers, both surfaced by the traces, stay open:

  1. **Precise arrival** (trace d): the `.arrived` fate's raw `atomsRightOfFirstCup = 0` predicate FALSE-NEGATIVES on a
     topPerm crossing legitimately left of the arrived cup (`peelHostileStraddleTail_rawArrivalFalseNegative`, the r35
     `legPeelToArrival_topPermTail_demo` / r36 `cupIsCapFreeRight_falsePositive` gap).  A total driver's arrival branch
     must certify the WORKING-REGION-factored `cupHasArrived`, not raw `= 0`.
  2. **Loop routing** (trace c): the loop arm has NO sinking rung — it is the δ circle; the total decision must route it
     to the `bottomCount = 0` class (`outcomeLoopAtZero` carries the bubble witness, but DECIDING when a neighbor is a
     loop over an arbitrary region is the open gate).

So `fxBrauer_hasSingleCupTotalDecision` is honestly `false`, `fxBrauer_hasSingleCupPeelDischarged` STAYS `false`, and
`fxBrauer_hasStagedInnerDescentDischarged`, `fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`,
`fxBrauer_hasBrauerV2FullCompleteness` all STAY `false`; this round is PURELY ADDITIVE, no master flip is fabricated.
The cap-side ∗-dual and the `DiagramType` driver belong to `fxBrauer_hasStagedInnerDescentDischarged` and the
completeness masters (the fold over EVERY cup), NOT to the single-cup peel.  Every residual is a route / measure gap,
never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).

Raw Lean 4 + Init; structural recursion on `Nat` and word lists (`List.length_append` and the stdlib `Nat.beq_refl`
LEAK `propext`, so `countAtoms` and the shipped structural lemmas are used instead).  Per-declaration
`#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the unified three-fated single-cup outcome -/

/-- ★ **The UNIFIED result of peeling one cup**, indexed by the region peeled, each fate carrying a genuine
`BrauerConvFree8` certificate to its result word.  The three per-cup fates the r34–r37 rungs produced as separate
theorems, now one Sum: `.arrived` (the cup reached its slot, `atomsRightOfFirstCup result = 0`), `.annihilated` (the cup
met an adjacent cap — a snake, the word strictly shortened), `.loop` (the cup + cap closed a bubble — a circle scalar,
witnessed genuinely non-empty by `brauerDiagramOf bottomCount result ≠ brauerDiagramOf bottomCount []`). -/
inductive SingleCupOutcome : List BrauerAtom → Type
  /-- The cup sank to its slot: `atomsRightOfFirstCup result = 0`. -/
  | arrived {region : List BrauerAtom} (result : List BrauerAtom)
      (conv : BrauerConvFree8 region result) (isArrived : atomsRightOfFirstCup result = 0) :
      SingleCupOutcome region
  /-- The cup annihilated with an adjacent cap (a snake): the word strictly shortened. -/
  | annihilated {region : List BrauerAtom} (result : List BrauerAtom)
      (conv : BrauerConvFree8 region result) (shrank : countAtoms result < countAtoms region) :
      SingleCupOutcome region
  /-- The cup + a cap on its own legs closed a bubble (a circle scalar), genuinely not the empty diagram. -/
  | loop {region : List BrauerAtom} (result : List BrauerAtom) (bottomCount : Nat)
      (conv : BrauerConvFree8 region result)
      (isBubble : brauerDiagramOf bottomCount result ≠ brauerDiagramOf bottomCount []) :
      SingleCupOutcome region

/-- ★ **The OUTER sink-step combinator.**  A single length-non-increasing move `BrauerConvFree8 regionBig regionSmall`
(with the word-length bound) is threaded onto an outcome for `regionSmall`: the certificate is `trans`-composed onto the
front and the fate witness transported (the `.annihilated` length drop composes with the step's non-increase).  Running
the driver = folding the seam / slide rungs through this combinator. -/
def SingleCupOutcome.prepend {regionBig regionSmall : List BrauerAtom}
    (stepConv : BrauerConvFree8 regionBig regionSmall)
    (lenLe : countAtoms regionSmall ≤ countAtoms regionBig) :
    SingleCupOutcome regionSmall → SingleCupOutcome regionBig
  | .arrived result conv isArrived => .arrived result (stepConv.trans conv) isArrived
  | .annihilated result conv shrank =>
      .annihilated result (stepConv.trans conv) (Nat.lt_of_lt_of_le shrank lenLe)
  | .loop result bottomCount conv isBubble => .loop result bottomCount (stepConv.trans conv) isBubble

/-! ## B — the three terminal builders (the shipped rungs wrapped into fates) -/

/-- ★ **The `.arrived` terminal — the r36 distant-tail peel as an outcome.**  A cup at `cupPos` followed by any distant
tail sinks to arrival via `legPeelDistantTail`; the resulting reduction + `atomsRightOfFirstCup = 0` become the
`.arrived` fate. -/
def outcomeArrivedOfDistantTail (cupPos : Nat) (tail : List (DistantSlideStep cupPos)) :
    SingleCupOutcome (cupAt cupPos :: distantTailWord tail) :=
  let peeled := legPeelDistantTail cupPos tail
  SingleCupOutcome.arrived peeled.1 peeled.2.1 peeled.2.2

/-- ★ **The `.annihilated` terminal (S1) — the r37 S1 snake as an outcome.**  `[cupAt (cupPos + 1), capAt cupPos]`
annihilates (the cap one leg left of the cup's near leg), whiskered by an arbitrary suffix; the strict `countAtoms` −2
drop becomes the `.annihilated` fate. -/
def outcomeAnnihilateS1 (cupPos : Nat) (suffixWord : List BrauerAtom) :
    SingleCupOutcome (cupAt (cupPos + 1) :: capAt cupPos :: suffixWord) :=
  SingleCupOutcome.annihilated suffixWord
    (BrauerConvFree8.whiskerRight suffixWord (snakeAnnihilateFree8_cleanS1 cupPos))
    (countAtoms_lt_append_cons2 [] suffixWord (cupAt (cupPos + 1)) (capAt cupPos))

/-- ★ **The `.annihilated` terminal (S2) — the r37 mirror snake as an outcome.**  `[cupAt cupPos, capAt (cupPos + 1)]`
annihilates (the cap one leg right of the cup's far leg). -/
def outcomeAnnihilateS2 (cupPos : Nat) (suffixWord : List BrauerAtom) :
    SingleCupOutcome (cupAt cupPos :: capAt (cupPos + 1) :: suffixWord) :=
  SingleCupOutcome.annihilated suffixWord
    (BrauerConvFree8.whiskerRight suffixWord (snakeAnnihilateFree8_cleanS2 cupPos))
    (countAtoms_lt_append_cons2 [] suffixWord (cupAt cupPos) (capAt (cupPos + 1)))

/-- ★ **The `.loop` terminal — the r37 bubble as an outcome.**  A cap AT the cup's position closes a bubble
`[cupAt 0, capAt 0]` (both legs shared); it is NOT convertible to `[]` (`snakeLoop_notEmptyWord`, `loops := 1 ≠ 0`), so
the result IS the region (reflexive conversion) carrying the non-emptiness witness — the circle scalar `δ` the total
decision routes to the `bottomCount = 0` class. -/
def outcomeLoopAtZero : SingleCupOutcome [cupAt 0, capAt 0] :=
  SingleCupOutcome.loop [cupAt 0, capAt 0] 0
    (BrauerConvFree8.ofFree7 (BrauerConvFree7.ofFree (BrauerConvFree.refl [cupAt 0, capAt 0])))
    snakeLoop_notEmptyWord

/-! ## C — the two named prepend seam steps (the cup survives) -/

/-- ★ **Prepend an UNTWIST step** (crossing on the cup's own legs, removed): `[cupAt cupPos, crossingAt cupPos, …] ↝
[cupAt cupPos, …]`, `countAtoms` −1, the surviving cup at the head.  The `cupUntwistFree8_clean` rung fed through the
sink combinator. -/
def prependUntwist (cupPos : Nat) (suffixWord : List BrauerAtom)
    (base : SingleCupOutcome (cupAt cupPos :: suffixWord)) :
    SingleCupOutcome (cupAt cupPos :: crossingAt cupPos :: suffixWord) :=
  SingleCupOutcome.prepend
    (BrauerConvFree8.whiskerRight suffixWord (cupUntwistFree8_clean cupPos))
    (Nat.le_of_lt (countAtoms_lt_append_cons_afterHead [] suffixWord (cupAt cupPos) (crossingAt cupPos)))
    base

/-- ★ **Prepend a STRADDLE step** (crossing at `cupPos + 1`, the cleanup relabel): `[cupAt cupPos, crossingAt (cupPos +
1), …] ↝ [cupAt (cupPos + 1), crossingAt cupPos, …]`, the word length HELD (both counts `= 2 + countAtoms suffix`), the
leg-fuel bit dropped.  The `straddleSlideFree8_clean` rung fed through the sink combinator. -/
def prependStraddle (cupPos : Nat) (suffixWord : List BrauerAtom)
    (base : SingleCupOutcome (cupAt (cupPos + 1) :: crossingAt cupPos :: suffixWord)) :
    SingleCupOutcome (cupAt cupPos :: crossingAt (cupPos + 1) :: suffixWord) :=
  SingleCupOutcome.prepend
    (BrauerConvFree8.whiskerRight suffixWord (straddleSlideFree8_clean cupPos))
    (Nat.le_refl _)
    base

/-! ## D — the genuine outer structural recursion (untwist run, on a `Nat` count) -/

/-- ★★ **The OUTER untwist-run driver — a genuine structural recursion on the `count : Nat`.**  Sinks a cup past a run
of `count` crossings on its own legs (a full `count`-fold twist), each removed by one untwist step (`countAtoms` −1),
composing onto any base outcome for `cupAt cupPos :: suffixWord`.  Combined with the inner `legPeelDistantTail` this is
the nested-structural driver over a two-parameter-generic region: the outer recurses on the untwist count, the inner on
the distant tail. -/
def peelUntwistRun (cupPos : Nat) (suffixWord : List BrauerAtom)
    (base : SingleCupOutcome (cupAt cupPos :: suffixWord)) :
    (count : Nat) →
    SingleCupOutcome (cupAt cupPos :: (List.replicate count (crossingAt cupPos) ++ suffixWord))
  | 0 => base
  | count + 1 =>
      prependUntwist cupPos (List.replicate count (crossingAt cupPos) ++ suffixWord)
        (peelUntwistRun cupPos suffixWord base count)

/-! ## E — the four hostiles run end-to-end + the fate read-off -/

/-- (a) The snake-first hostile: the cup at position 1 annihilates with the adjacent cap at 0. -/
def peelHostileSnakeFirst : SingleCupOutcome [cupAt 1, capAt 0, crossingAt 8] :=
  outcomeAnnihilateS1 0 [crossingAt 8]

/-- (b) The untwist-then-distant hostile: untwist the crossing on the cup's legs, then sink past the distant tail to
arrival. -/
def peelHostileUntwistDistant : SingleCupOutcome [cupAt 2, crossingAt 2, crossingAt 5, capAt 6] :=
  prependUntwist 2 [crossingAt 5, capAt 6]
    (outcomeArrivedOfDistantTail 2 [.crossing 3 (by decide), .cap 4 (by decide)])

/-- (c) The loop hostile: the cup + cap at the same position close a bubble. -/
def peelHostileLoop : SingleCupOutcome [cupAt 0, capAt 0] := outcomeLoopAtZero

/-- ★★ **The two-parameter-generic flagship — a full outer+inner nested peel.**  A cup at 0 with a DOUBLE twist
(`count = 2` untwist crossings on its own legs) THEN a distant tail `[crossingAt 3, capAt 4]`: the outer `peelUntwistRun`
removes both twists, the inner `legPeelDistantTail` sinks the cup to arrival — one arrived outcome over a region neither
r36 nor r37 could peel without hand-building each cell. -/
def peelUntwistRunThenDistant_demo :
    SingleCupOutcome [cupAt 0, crossingAt 0, crossingAt 0, crossingAt 3, capAt 4] :=
  peelUntwistRun 0 [crossingAt 3, capAt 4]
    (outcomeArrivedOfDistantTail 0 [.crossing 1 (by decide), .cap 2 (by decide)]) 2

/-- ★ **The honest companion (d) — arrival is NOT the raw `atomsRightOfFirstCup = 0`.**  The straddle relabel
`[cupAt 0, crossingAt 1] ↝ [cupAt 1, crossingAt 0]` carries a real `BrauerConvFree8` reduction, yet the topPerm crossing
sits legitimately LEFT of the cup, so `atomsRightOfFirstCup [cupAt 1, crossingAt 0] = 1 ≠ 0`.  This is why a TOTAL
driver's `.arrived` branch must certify the working-region-factored `cupHasArrived`, not the raw measure — the blocker-1
jamming arm, pinned. -/
theorem peelHostileStraddleTail_rawArrivalFalseNegative :
    BrauerConvFree8 [cupAt 0, crossingAt 1] [cupAt 1, crossingAt 0]
      ∧ atomsRightOfFirstCup [cupAt 1, crossingAt 0] = 1 :=
  ⟨straddleSlideFree8_clean 0, by decide⟩

/-- The fate of an outcome (which of the three branches fired), read off the constructor alone. -/
inductive SingleCupFate
  | arrivedFate
  | annihilatedFate
  | loopFate
deriving DecidableEq

/-- Read the fate off an outcome. -/
def SingleCupOutcome.fate {region : List BrauerAtom} : SingleCupOutcome region → SingleCupFate
  | .arrived _ _ _ => SingleCupFate.arrivedFate
  | .annihilated _ _ _ => SingleCupFate.annihilatedFate
  | .loop _ _ _ _ => SingleCupFate.loopFate

/-- ★★ **The four hostiles' fates, machine-checked by `rfl`.**  (a) annihilated, (b) arrived, (c) loop, and the
two-parameter flagship (d′) arrived — the driver assigns each mixed hostile its recon-traced fate through the unified
outcome type. -/
theorem peelHostile_fates :
    peelHostileSnakeFirst.fate = SingleCupFate.annihilatedFate
      ∧ peelHostileUntwistDistant.fate = SingleCupFate.arrivedFate
      ∧ peelHostileLoop.fate = SingleCupFate.loopFate
      ∧ peelUntwistRunThenDistant_demo.fate = SingleCupFate.arrivedFate :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the single-cup PEEL DRIVER (combinator form) SHIPS.**  The unified three-fated
`SingleCupOutcome` (`.arrived` / `.annihilated` / `.loop`, each carrying a genuine `BrauerConvFree8` certificate), the
OUTER sink-step combinator `SingleCupOutcome.prepend` threading the seam / slide rungs under the `(wordLength,
legLexFuel)` measure, the three terminal builders wrapping the r36 distant-tail peel + the r37 snake + the r37 bubble,
the two named seam steps (`prependUntwist` / `prependStraddle`), and the genuine outer structural recursion
`peelUntwistRun` (composed with the inner `legPeelDistantTail` in `peelUntwistRunThenDistant_demo`) run all four mixed
hostiles to their recon-traced fates (`peelHostile_fates`).  The OUTER driver the r37 wall named, built in combinator
form.  `= true`. -/
def fxBrauer_hasSingleCupOutcomeDriver : Bool := true

/-- **Honesty WALL marker — the TOTAL region-decision is NOT built; #2013 does NOT close.**  The driver RUNS a peel
(threads the given moves into a three-fated outcome under the measure), but the TOTAL DECISION — synthesizing the moves
by scanning an ARBITRARY region for the leftmost cup and classifying its neighbor — stays open on two blockers, both
surfaced by the traces: (1) the `.arrived` fate's raw `atomsRightOfFirstCup = 0` FALSE-NEGATIVES on a topPerm crossing
left of the cup (`peelHostileStraddleTail_rawArrivalFalseNegative`), so a total driver must certify the
working-region-factored `cupHasArrived`; (2) the loop arm has no sinking rung, so the total decision must route it to
the `bottomCount = 0` circle class.  So `fxBrauer_hasSingleCupPeelDischarged` STAYS `false`, and
`fxBrauer_hasStagedInnerDescentDischarged`, `fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`,
`fxBrauer_hasBrauerV2FullCompleteness` all STAY `false`.  A route / measure gap, never a truth gap (Lehrer–Zhang
arXiv:1207.5889 Thm 2.6).  `= false`. -/
def fxBrauer_hasSingleCupTotalDecision : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r38 single-cup-peel-driver terminal state — MACHINE-CHECKED.**  The new driver marker is `true`
(the three-fated outcome + the outer sink-step combinator + the genuine untwist-run recursion, non-vacuous on the four
hostiles), built on the r36 `fxBrauer_hasDistantTailCupPeel` / `fxBrauer_hasStraddleTerminalCleanup` and the r37
`fxBrauer_hasSnakeAnnihilationRung` / `fxBrauer_hasCupUntwistSeamRung`, while the TOTAL region-decision, the single-cup
peel discharge, and all four completeness / inner-descent masters STAY `false`.  A `rfl`-conjunction the kernel checks;
this round is purely additive, no master flip is fabricated, #2013 does NOT close. -/
theorem fxBrauer_singleCupPeelDriverTerminalState :
    fxBrauer_hasSingleCupOutcomeDriver = true
      ∧ fxBrauer_hasDistantTailCupPeel = true
      ∧ fxBrauer_hasStraddleTerminalCleanup = true
      ∧ fxBrauer_hasSnakeAnnihilationRung = true
      ∧ fxBrauer_hasCupUntwistSeamRung = true
      ∧ fxBrauer_hasSingleCupTotalDecision = false
      ∧ fxBrauer_hasSingleCupPeelDischarged = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph

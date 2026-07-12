import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescSingleCupPeelDriver

/-! # BRAUER r39 — the REGION-TRACKED single-cup decision: the FACTORED arrival + the loop router + the neighbour
classifier (the scan-and-classify half of the total decision)

r38 (`Brauer/WiringDescSingleCupPeelDriver.lean`) shipped the RUNNER: `SingleCupOutcome` (the three-fated result) +
`SingleCupOutcome.prepend` (the outer sink-step combinator) + the terminal builders + `peelUntwistRun` (the genuine
outer structural recursion).  Its wall `fxBrauer_hasSingleCupTotalDecision = false` named the TOTAL DECISION — synthesizing
the moves from an ARBITRARY region by scanning for the leftmost cup and classifying its neighbour — and pinned two
blockers, both surfaced by the traces:

  1. **Precise arrival** (trace d): the `.arrived` fate's raw `atomsRightOfFirstCup result = 0` FALSE-NEGATIVES on a
     topPerm crossing legitimately LEFT of the arrived cup (`peelHostileStraddleTail_rawArrivalFalseNegative`), so a
     total driver's arrival branch must certify the WORKING-REGION-factored arrival, not the raw `= 0`.
  2. **Loop routing** (trace c): the loop arm has no sinking rung — it is the δ circle; the total decision must route it
     to the `bottomCount = 0` circle class.

This round ships, PURELY ADDITIVELY, the region-tracked bricks that resolve the two named blockers and the total
decision's decidable HALF (truth-probed by `#eval` FIRST, then pinned):

  * ★ **`RegionCupOutcome`** — the FACTORED three-fated outcome.  Its `.arrivedFactored` carries the WORKING-REGION
    arrival `cupIsCapFreeRight result = true` (no cap sits right of the leftmost cup — the r36 decidable factored
    predicate), NOT the raw `atomsRightOfFirstCup result = 0`.  This is blocker-1 resolved: the straddle relabel
    `[cupAt 0, crossingAt 1] ↝ [cupAt 1, crossingAt 0]` now ARRIVES (`outcomeArrivedFactoredStraddle`), where r38 could
    only record it as the false-negative companion.
  * ★ **`capFreeRight_of_arrived`** — the honest bridge: raw arrival (`atomsRightOfFirstCup w = 0`) IMPLIES the factored
    predicate (`cupIsCapFreeRight w = true`), via `atomsRightOfFirstCup w = countAtoms (suffixRightOfFirstCup w)` and
    `countAtoms xs = 0 → xs = []` (structural, `Nat.add_comm` + `Nat.noConfusion` — never `List.length_append` /
    `Nat.beq_refl` / `Nat.succ_ne_zero`, all of which leak `propext`).  So the FACTORED arrival SUBSUMES the raw one: the
    distant-tail peel still arrives, and the straddle relabel now arrives too.
  * ★ **`snakeLoopFree8_clean` / `outcomeLoopAtFactored`** — the loop router GENERIC in `cupPos`: the reflexive
    conversion carrier at any `cupPos`, threaded onto the `bottomCount = 0` bubble non-emptiness witness (blocker-2's
    conversion half, generic; the non-emptiness itself stays a per-literal `decide` — see the wall).
  * ★ **`classifyFirstCupNeighbor`** — the SCAN-AND-CLASSIFY total function: over an ARBITRARY region it finds the
    leftmost cup and classifies its immediate list-neighbour into the move kind to synthesize (untwist / straddle /
    distant-crossing / distant-cap / snake-left / snake-right / loop / arrived / another-cup / no-cup), by closed
    `Nat.beq` / successor comparison, NO subtraction.  The decidable half of the total decision; `classifyNeighbour_probes`
    pins the hostile fixtures.
  * **The four hostiles + trace d run through the FACTORED outcome** (`regionHostile_fates`), trace d now a genuine
    `.arrivedFactored`.

## The honest wall — the TOTAL region dispatch is NOT built; #2013 does NOT close (named IN this file, no new ledger)

The two named blockers are resolved as bricks and the scan-and-classify half is total, but the TOTAL region DISPATCH —
a structural function that, from `classifyFirstCupNeighbor`'s decision, SYNTHESIZES the typed `RegionCupOutcome` for an
arbitrary region — stays open on three residuals the traces surface:

  * **(J-transport) the reshape plumbing.**  Each dispatch arm must retype the shipped builder's positional word
    (`crossingAt cupPos`, `capAt (capPos + 2)`, …) to the region's ACTUAL atom via a `Nat.beq _ _ = true → _ = _`
    positional equality and transport the outcome — the `Eq.rec`/`▸` plumbing across a cons-indexed family the memory
    corpus flags as a `propext` minefield (cons-index match + ▸).  Not a truth gap: the classifier already DECIDES the
    arm; only the certified synthesis is unbuilt.
  * **(J-loop) the generic loop non-emptiness.**  `brauerDiagramOf 0 [cupAt cupPos, capAt cupPos] ≠ brauerDiagramOf 0 []`
    is `decide` at every literal `cupPos` (`.loops := 1 ≠ 0`, `#eval`-confirmed for `cupPos ∈ {0,1,2,5,10}`) but a proof
    GENERIC in `cupPos` needs an engine-level `(brauerDiagramOf 0 [cupAt cupPos, capAt cupPos]).loops = 1` lemma over
    `stepCup`/`stepCap`/`extractDiagram`; with a suffix the loop count even varies (`[cupAt 2, capAt 2, capAt 9].loops =
    2`), so the loop router takes the witness as a hypothesis this round.
  * **(J-geometry) the straddle-then-cap ordering trap.**  Firing the straddle first on `[cupAt 0, crossingAt 1,
    crossingAt 3, capAt 5]` wedges the settled `crossingAt 0` BETWEEN the arrived cup and the distant cap
    (`cupIsCapFreeRight = false`, `#eval`-confirmed NOT arrived); the straddle is a terminal-cleanup move, so the total
    dispatch must sink the distant tail BEFORE the straddle — an ordering discipline the classifier records but the
    single-pass dispatch does not yet encode.

So `fxBrauer_hasSingleCupTotalDecision` STAYS `false` (owned by r38, untouched), and
`fxBrauer_hasSingleCupPeelDischarged`, `fxBrauer_hasStagedInnerDescentDischarged`,
`fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness` all
STAY `false`; this round is PURELY ADDITIVE, no master flip is fabricated.  Every residual is a route / measure /
engine-lemma gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).

Raw Lean 4 + Init; structural recursion on word lists (no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix` /
`propext` — `List.length_append`, `Nat.beq_refl`, `Nat.succ_ne_zero`, `Nat.sub_*` all leak `propext`, so `countAtoms`,
closed `Nat.beq`, and `Nat.noConfusion` are used instead).  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the cap detector + the two structural bridge lemmas (raw arrival ⟹ factored arrival) -/

/-- A generator atom is a CAP iff it produces zero boundary outputs.  Among the Brauer generators only `capAt`
(`outputCount = 0`) is a cap; `cupAt` / `crossingAt` produce `2`, `identityStrandAt` produces `1`.  Structural `Nat.beq`,
so it reduces by `rfl` on the named atoms. -/
def isCapAtom (atom : BrauerAtom) : Bool := Nat.beq atom.wiring.outputCount 0

/-- A cap atom is detected as a cap. -/
theorem isCapAtom_capAt (position : Nat) : isCapAtom (capAt position) = true := rfl

/-- A cup atom is NOT a cap. -/
theorem isCapAtom_cupAt (position : Nat) : isCapAtom (cupAt position) = false := rfl

/-- A crossing atom is NOT a cap. -/
theorem isCapAtom_crossingAt (position : Nat) : isCapAtom (crossingAt position) = false := rfl

/-- ★ **The leftmost-cup distance IS the length of the suffix right of the leftmost cup.**  `atomsRightOfFirstCup w =
countAtoms (suffixRightOfFirstCup w)` — the primary leg coordinate counts exactly the atoms `suffixRightOfFirstCup`
lists.  Standalone structural recursion (full-enum `cases isCupAtom`, propext-clean). -/
theorem atomsRightOfFirstCup_eq_countAtoms_suffix : (word : List BrauerAtom) →
    atomsRightOfFirstCup word = countAtoms (suffixRightOfFirstCup word)
  | [] => rfl
  | atom :: rest => by
      show cond (isCupAtom atom) (countAtoms rest) (atomsRightOfFirstCup rest)
         = countAtoms (cond (isCupAtom atom) rest (suffixRightOfFirstCup rest))
      cases hAtom : isCupAtom atom with
      | true => rfl
      | false => exact atomsRightOfFirstCup_eq_countAtoms_suffix rest

/-- A word of zero atoms is the empty word.  Structural; the successor arm is discharged by `Nat.add_comm` (clean) into
`Nat.succ _ = 0`, refuted by `Nat.noConfusion` (never `Nat.succ_ne_zero`, which leaks `propext`). -/
theorem countAtoms_eq_zero_imp_nil : (word : List BrauerAtom) → countAtoms word = 0 → word = []
  | [], _ => rfl
  | atom :: rest, hZero => by
      have hSucc : countAtoms (atom :: rest) = countAtoms rest + 1 := by
        show 1 + countAtoms rest = countAtoms rest + 1
        exact Nat.add_comm 1 (countAtoms rest)
      rw [hSucc] at hZero
      exact Nat.noConfusion hZero

/-- ★ **The honest bridge: raw arrival IMPLIES the factored cap-free-right predicate.**  If `atomsRightOfFirstCup w = 0`
(the raw complete arrival on the working region), then `cupIsCapFreeRight w = true` (no cap sits right of the leftmost
cup): with zero atoms right of the cup, the suffix is empty, hence cap-free.  So the FACTORED arrival SUBSUMES the raw
one — the distant-tail peel's `= 0` arrival lifts to `.arrivedFactored`, and the straddle relabel (raw `≠ 0`) arrives
too. -/
theorem capFreeRight_of_arrived (word : List BrauerAtom) (arrived : atomsRightOfFirstCup word = 0) :
    cupIsCapFreeRight word = true := by
  have hSuffixNil : suffixRightOfFirstCup word = [] := by
    apply countAtoms_eq_zero_imp_nil
    rw [← atomsRightOfFirstCup_eq_countAtoms_suffix]
    exact arrived
  show hasNoCap (suffixRightOfFirstCup word) = true
  rw [hSuffixNil]
  rfl

/-! ## B — the FACTORED three-fated region-cup outcome -/

/-- ★ **The REGION-TRACKED result of deciding one cup**, indexed by the region, each fate carrying a genuine
`BrauerConvFree8` certificate.  The crux difference from the r38 `SingleCupOutcome`: `.arrivedFactored` certifies the
WORKING-REGION-factored arrival `cupIsCapFreeRight result = true` (no cap right of the leftmost cup, the r36 decidable
predicate), NOT the raw `atomsRightOfFirstCup result = 0` that false-negatives on a topPerm crossing left of the cup
(blocker-1 resolved). -/
inductive RegionCupOutcome : List BrauerAtom → Type
  /-- The cup reached its slot on the WORKING region: no cap sits right of it (`cupIsCapFreeRight result = true`). -/
  | arrivedFactored {region : List BrauerAtom} (result : List BrauerAtom)
      (conv : BrauerConvFree8 region result) (capFreeRight : cupIsCapFreeRight result = true) :
      RegionCupOutcome region
  /-- The cup annihilated with an adjacent cap (a snake): the word strictly shortened. -/
  | annihilated {region : List BrauerAtom} (result : List BrauerAtom)
      (conv : BrauerConvFree8 region result) (shrank : countAtoms result < countAtoms region) :
      RegionCupOutcome region
  /-- The cup + a cap on its own legs closed a bubble (a circle scalar), genuinely not the empty diagram. -/
  | loop {region : List BrauerAtom} (result : List BrauerAtom) (bottomCount : Nat)
      (conv : BrauerConvFree8 region result)
      (isBubble : brauerDiagramOf bottomCount result ≠ brauerDiagramOf bottomCount []) :
      RegionCupOutcome region

/-- ★ **The outer sink-step combinator for the factored outcome** — the r38 `SingleCupOutcome.prepend`, transported to
`RegionCupOutcome`.  A length-non-increasing move is `trans`-composed onto the front, each fate's witness carried
(`.arrivedFactored`'s `cupIsCapFreeRight result` is on `result`, unchanged; `.annihilated`'s drop composes with the
step's non-increase). -/
def RegionCupOutcome.prepend {regionBig regionSmall : List BrauerAtom}
    (stepConv : BrauerConvFree8 regionBig regionSmall)
    (lenLe : countAtoms regionSmall ≤ countAtoms regionBig) :
    RegionCupOutcome regionSmall → RegionCupOutcome regionBig
  | .arrivedFactored result conv capFreeRight => .arrivedFactored result (stepConv.trans conv) capFreeRight
  | .annihilated result conv shrank =>
      .annihilated result (stepConv.trans conv) (Nat.lt_of_lt_of_le shrank lenLe)
  | .loop result bottomCount conv isBubble => .loop result bottomCount (stepConv.trans conv) isBubble

/-! ## C — the factored terminal builders (blocker-1 resolved) -/

/-- ★★ **The STRADDLE arrival — blocker-1 resolved, GENERIC in `cupPos`.**  The straddle relabel `[cupAt cupPos,
crossingAt (cupPos + 1)] ↝ [cupAt (cupPos + 1), crossingAt cupPos]` carries a real `BrauerConvFree8` reduction, and the
result is FACTORED-arrived: `cupIsCapFreeRight [cupAt (cupPos + 1), crossingAt cupPos] = true` because the only atom
right of the cup is a crossing (`outputCount = 2 ≠ 0`), regardless of position — so it is `rfl`.  This is exactly the
trace-d word r38 could only record as the raw false-negative companion; here it is a genuine `.arrivedFactored`. -/
def outcomeArrivedFactoredStraddle (cupPos : Nat) :
    RegionCupOutcome [cupAt cupPos, crossingAt (cupPos + 1)] :=
  RegionCupOutcome.arrivedFactored [cupAt (cupPos + 1), crossingAt cupPos]
    (straddleSlideFree8_clean cupPos) rfl

/-- ★ **The distant-tail arrival, FACTORED.**  The r36 `legPeelDistantTail` sinks a cup past any distant tail to raw
arrival (`atomsRightOfFirstCup = 0`); `capFreeRight_of_arrived` lifts that to the factored predicate, so the whole
distant-tail peel is a `.arrivedFactored` outcome. -/
def outcomeArrivedFactoredOfDistantTail (cupPos : Nat) (tail : List (DistantSlideStep cupPos)) :
    RegionCupOutcome (cupAt cupPos :: distantTailWord tail) :=
  let peeled := legPeelDistantTail cupPos tail
  RegionCupOutcome.arrivedFactored peeled.1 peeled.2.1 (capFreeRight_of_arrived peeled.1 peeled.2.2)

/-- ★ **The S1 snake annihilation, factored outcome.**  `[cupAt (cupPos + 1), capAt cupPos]` annihilates whiskered by
any suffix; the strict `countAtoms` −2 drop is the `.annihilated` fate. -/
def outcomeAnnihilatedFactoredS1 (cupPos : Nat) (suffixWord : List BrauerAtom) :
    RegionCupOutcome (cupAt (cupPos + 1) :: capAt cupPos :: suffixWord) :=
  RegionCupOutcome.annihilated suffixWord
    (BrauerConvFree8.whiskerRight suffixWord (snakeAnnihilateFree8_cleanS1 cupPos))
    (countAtoms_lt_append_cons2 [] suffixWord (cupAt (cupPos + 1)) (capAt cupPos))

/-- ★ **The S2 mirror snake annihilation, factored outcome.**  `[cupAt cupPos, capAt (cupPos + 1)]` annihilates. -/
def outcomeAnnihilatedFactoredS2 (cupPos : Nat) (suffixWord : List BrauerAtom) :
    RegionCupOutcome (cupAt cupPos :: capAt (cupPos + 1) :: suffixWord) :=
  RegionCupOutcome.annihilated suffixWord
    (BrauerConvFree8.whiskerRight suffixWord (snakeAnnihilateFree8_cleanS2 cupPos))
    (countAtoms_lt_append_cons2 [] suffixWord (cupAt cupPos) (capAt (cupPos + 1)))

/-! ## D — the loop router (blocker-2: the conversion half generic, the non-emptiness a hypothesis) -/

/-- ★ **The loop conversion carrier, GENERIC in `cupPos`.**  A cap AT the cup's position closes a bubble; the result IS
the region (reflexive conversion), so the loop router's conversion half is trivial and generic — the `cupPos`-generic
sibling of the r38 `outcomeLoopAtZero`'s hard-wired `refl`. -/
def snakeLoopFree8_clean (cupPos : Nat) :
    BrauerConvFree8 [cupAt cupPos, capAt cupPos] [cupAt cupPos, capAt cupPos] :=
  BrauerConvFree8.ofFree7 (BrauerConvFree7.ofFree (BrauerConvFree.refl [cupAt cupPos, capAt cupPos]))

/-- ★ **The loop terminal, factored outcome, GENERIC in `cupPos`.**  Given the bubble non-emptiness witness
(`brauerDiagramOf 0 [cupAt cupPos, capAt cupPos] ≠ brauerDiagramOf 0 []`, a per-literal `decide` — its `cupPos`-generic
proof is the engine-lemma residual J-loop), routes the loop to the `bottomCount = 0` circle class carrying the reflexive
conversion. -/
def outcomeLoopAtFactored (cupPos : Nat)
    (isBubble : brauerDiagramOf 0 [cupAt cupPos, capAt cupPos] ≠ brauerDiagramOf 0 ([] : List BrauerAtom)) :
    RegionCupOutcome [cupAt cupPos, capAt cupPos] :=
  RegionCupOutcome.loop [cupAt cupPos, capAt cupPos] 0 (snakeLoopFree8_clean cupPos) isBubble

/-! ## E — the SCAN-AND-CLASSIFY total function (the decidable half of the total decision) -/

/-- The move kind a leftmost cup's immediate list-neighbour dictates, decided from the cup / neighbour positions and
generator kinds alone. -/
inductive RegionCupMoveKind
  /-- The region has no cup. -/
  | noCup
  /-- The leftmost cup is last — nothing follows it (raw arrival). -/
  | cupArrivedAlone
  /-- Next is a crossing AT `cupPos` — the untwist seam (`countAtoms` −1). -/
  | untwist
  /-- Next is a crossing at `cupPos + 1` — the straddle terminal cleanup. -/
  | straddleTerminal
  /-- Next is a crossing at `cupPos + 2` or beyond — a distant crossing slide. -/
  | distantCrossing
  /-- Next is a crossing LEFT of the cup (a settled topPerm crossing). -/
  | crossingLeft
  /-- Next is a cap at `cupPos - 1` (shares wire `cupPos`) — the S1 snake. -/
  | snakeLeft
  /-- Next is a cap at `cupPos + 1` (shares wire `cupPos + 1`) — the S2 snake. -/
  | snakeRight
  /-- Next is a cap AT `cupPos` (both legs) — the loop bubble. -/
  | loopHere
  /-- Next is a cap at `cupPos + 2` or beyond — a distant cap slide. -/
  | distantCap
  /-- Next is another cup — a within-cup-block reorder (multi-cup, beyond single-cup). -/
  | anotherCup
deriving DecidableEq

/-- Classify the immediate neighbour `next` of a leftmost cup at `cupPos` — by closed `Nat.beq` / successor comparison,
NO subtraction (which leaks `propext`). -/
def classifyCupNeighbourStep (cupPos : Nat) (next : BrauerAtom) : RegionCupMoveKind :=
  cond (isCupAtom next) RegionCupMoveKind.anotherCup
    (cond (isCapAtom next)
      (cond (Nat.beq next.position cupPos) RegionCupMoveKind.loopHere
        (cond (Nat.beq next.position (cupPos + 1)) RegionCupMoveKind.snakeRight
          (cond (Nat.beq cupPos (next.position + 1)) RegionCupMoveKind.snakeLeft
            RegionCupMoveKind.distantCap)))
      (cond (Nat.beq next.position cupPos) RegionCupMoveKind.untwist
        (cond (Nat.beq next.position (cupPos + 1)) RegionCupMoveKind.straddleTerminal
          (cond (Nat.beq cupPos (next.position + 1)) RegionCupMoveKind.crossingLeft
            RegionCupMoveKind.distantCrossing))))

/-- Classify the tail after a located leftmost cup: empty tail is arrival, else classify the immediate neighbour. -/
def classifyCupHeadTail (cupPos : Nat) : List BrauerAtom → RegionCupMoveKind
  | [] => RegionCupMoveKind.cupArrivedAlone
  | next :: _ => classifyCupNeighbourStep cupPos next

/-- ★ **The SCAN-AND-CLASSIFY total function.**  Over an ARBITRARY region, find the leftmost cup and classify its
immediate list-neighbour into the move kind to synthesize.  Structural on the region (skip non-cups until the first
cup); total (`noCup` when the region has no cup).  This is the DECIDABLE half of the total decision — it decides WHICH
move; the certified typed synthesis from the decision is the J-transport residual. -/
def classifyFirstCupNeighbour : List BrauerAtom → RegionCupMoveKind
  | [] => RegionCupMoveKind.noCup
  | atom :: rest =>
      cond (isCupAtom atom) (classifyCupHeadTail atom.position rest) (classifyFirstCupNeighbour rest)

/-- ★ **The classifier truth-probes, machine-checked** (the recon fixtures pinned by `rfl` — closed `Nat.beq`
reductions).  The four hostiles + trace d + a cupless-prefix region + a distant tail, each classified to its
recon-traced move kind. -/
theorem classifyNeighbour_probes :
    classifyFirstCupNeighbour [cupAt 1, capAt 0, crossingAt 8] = RegionCupMoveKind.snakeLeft
      ∧ classifyFirstCupNeighbour [cupAt 2, crossingAt 2, crossingAt 5, capAt 6] = RegionCupMoveKind.untwist
      ∧ classifyFirstCupNeighbour [cupAt 0, capAt 0] = RegionCupMoveKind.loopHere
      ∧ classifyFirstCupNeighbour [cupAt 0, crossingAt 1] = RegionCupMoveKind.straddleTerminal
      ∧ classifyFirstCupNeighbour [cupAt 0, capAt 1] = RegionCupMoveKind.snakeRight
      ∧ classifyFirstCupNeighbour [cupAt 0, crossingAt 3, capAt 5] = RegionCupMoveKind.distantCrossing
      ∧ classifyFirstCupNeighbour [cupAt 0, capAt 5] = RegionCupMoveKind.distantCap
      ∧ classifyFirstCupNeighbour [cupAt 0] = RegionCupMoveKind.cupArrivedAlone
      ∧ classifyFirstCupNeighbour [crossingAt 1, crossingAt 2, cupAt 0] = RegionCupMoveKind.cupArrivedAlone
      ∧ classifyFirstCupNeighbour [crossingAt 9] = RegionCupMoveKind.noCup
      ∧ classifyFirstCupNeighbour [cupAt 0, cupAt 2] = RegionCupMoveKind.anotherCup :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## F — the four hostiles + trace d run through the FACTORED outcome, fates read off -/

/-- Read the fate of a factored outcome (which of the three branches fired), reusing the r38 `SingleCupFate`. -/
def RegionCupOutcome.fate {region : List BrauerAtom} : RegionCupOutcome region → SingleCupFate
  | .arrivedFactored _ _ _ => SingleCupFate.arrivedFate
  | .annihilated _ _ _ => SingleCupFate.annihilatedFate
  | .loop _ _ _ _ => SingleCupFate.loopFate

/-- (d) The straddle hostile — now a genuine FACTORED-arrived outcome (the r38 false-negative companion promoted). -/
def regionHostileStraddleArrived : RegionCupOutcome [cupAt 0, crossingAt 1] :=
  outcomeArrivedFactoredStraddle 0

/-- (a) The snake-first hostile — the cup at 1 annihilates with the adjacent cap at 0. -/
def regionHostileSnakeFirst : RegionCupOutcome [cupAt 1, capAt 0, crossingAt 8] :=
  outcomeAnnihilatedFactoredS1 0 [crossingAt 8]

/-- (b) The untwist-then-distant hostile — untwist the crossing on the cup's legs, then sink past the distant tail to
FACTORED arrival. -/
def regionHostileUntwistDistant : RegionCupOutcome [cupAt 2, crossingAt 2, crossingAt 5, capAt 6] :=
  RegionCupOutcome.prepend
    (BrauerConvFree8.whiskerRight [crossingAt 5, capAt 6] (cupUntwistFree8_clean 2))
    (Nat.le_of_lt (countAtoms_lt_append_cons_afterHead [] [crossingAt 5, capAt 6] (cupAt 2) (crossingAt 2)))
    (outcomeArrivedFactoredOfDistantTail 2 [.crossing 3 (by decide), .cap 4 (by decide)])

/-- (c) The loop hostile — the cup + cap at the same position close a bubble (non-emptiness by `decide` at the literal
`cupPos = 0`). -/
def regionHostileLoop : RegionCupOutcome [cupAt 0, capAt 0] :=
  outcomeLoopAtFactored 0 (by decide)

/-- ★★ **The four hostiles' fates through the FACTORED outcome, machine-checked by `rfl`.**  (d) arrived (the promoted
false-negative), (a) annihilated, (b) arrived, (c) loop — the driver's fate assignment through the region-tracked
outcome, with trace d now a real arrival. -/
theorem regionHostile_fates :
    regionHostileStraddleArrived.fate = SingleCupFate.arrivedFate
      ∧ regionHostileSnakeFirst.fate = SingleCupFate.annihilatedFate
      ∧ regionHostileUntwistDistant.fate = SingleCupFate.arrivedFate
      ∧ regionHostileLoop.fate = SingleCupFate.loopFate :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ★ **The factored predicate genuinely ARRIVES where the raw predicate FALSE-NEGATIVES** — the blocker-1 pin.  On the
trace-d result `[cupAt 1, crossingAt 0]` the raw arrival reads `atomsRightOfFirstCup = 1 ≠ 0`, yet the FACTORED
predicate reads `cupIsCapFreeRight = true` (no cap right of the cup); so the factored outcome arrives where the raw one
jams. -/
theorem factoredArrival_where_rawFalseNegatives :
    atomsRightOfFirstCup [cupAt 1, crossingAt 0] = 1
      ∧ cupIsCapFreeRight [cupAt 1, crossingAt 0] = true :=
  ⟨by decide, by decide⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the FACTORED cup arrival SHIPS (blocker-1 resolved).**  `RegionCupOutcome.arrivedFactored`
carries the working-region factored predicate `cupIsCapFreeRight result = true` (no cap right of the leftmost cup) in
place of the raw `atomsRightOfFirstCup result = 0` that false-negatives on a topPerm crossing left of the cup; the
bridge `capFreeRight_of_arrived` shows the factored predicate SUBSUMES the raw one, so the distant-tail peel still
arrives (`outcomeArrivedFactoredOfDistantTail`) and the straddle relabel now arrives too
(`outcomeArrivedFactoredStraddle`, generic in `cupPos`, `rfl`).  `factoredArrival_where_rawFalseNegatives` pins trace d.
`= true`. -/
def fxBrauer_hasFactoredCupArrival : Bool := true

/-- ★★ **Honesty marker — the REGION neighbour CLASSIFIER + the loop-router conversion SHIP (the decidable half).**
`classifyFirstCupNeighbour` scans an ARBITRARY region for the leftmost cup and classifies its immediate neighbour into
the move kind to synthesize (`classifyNeighbour_probes` pins the hostiles), the total scan-and-classify half of the
total decision; `snakeLoopFree8_clean` / `outcomeLoopAtFactored` route a loop to the `bottomCount = 0` circle class
generic in `cupPos` (blocker-2's conversion half), and the four hostiles + trace d run through the factored outcome
(`regionHostile_fates`).  `= true`. -/
def fxBrauer_hasRegionCupClassifier : Bool := true

/-- **Honesty WALL marker — the TOTAL region DISPATCH is NOT built; #2013 does NOT close.**  The two named blockers are
resolved as bricks and the scan-and-classify half is total, but SYNTHESIZING the typed `RegionCupOutcome` from
`classifyFirstCupNeighbour`'s decision over an arbitrary region stays open on three residuals: (J-transport) each
dispatch arm's `Nat.beq _ _ = true → _ = _` positional reshape + `Eq.rec`/`▸` transport across the cons-indexed family
(a `propext` minefield per the memory corpus); (J-loop) the `cupPos`-generic loop non-emptiness `brauerDiagramOf 0
[cupAt cupPos, capAt cupPos] ≠ brauerDiagramOf 0 []` (a per-literal `decide`, but a generic proof needs an engine-level
`.loops = 1` lemma — with a suffix the loop count even varies); (J-geometry) the straddle-then-cap ordering trap (the
straddle must fire AFTER the distant tail sinks, an ordering the classifier records but the single-pass dispatch does
not encode).  So `fxBrauer_hasSingleCupTotalDecision` STAYS `false` (owned by r38, untouched), and
`fxBrauer_hasSingleCupPeelDischarged`, `fxBrauer_hasStagedInnerDescentDischarged`, `fxBrauer_hasFreeBrauerStraighteningNF`,
`fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness` all STAY `false`.  A route / measure /
engine-lemma gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).  `= false`. -/
def fxBrauer_hasRegionDriverTotalDispatch : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r39 region-driver terminal state — MACHINE-CHECKED.**  The two new brick markers are `true` (the
factored cup arrival resolving blocker-1, the region neighbour classifier + loop-router conversion), built on the r38
`fxBrauer_hasSingleCupOutcomeDriver` and the r36 `fxBrauer_hasCupArrivalPredicate`, while the total region dispatch, the
r38 total decision, the single-cup peel discharge, and all four completeness / inner-descent masters STAY `false`.  A
`rfl`-conjunction the kernel checks; this round is purely additive, no master flip is fabricated, #2013 does NOT
close. -/
theorem fxBrauer_singleCupRegionDriverTerminalState :
    fxBrauer_hasFactoredCupArrival = true
      ∧ fxBrauer_hasRegionCupClassifier = true
      ∧ fxBrauer_hasSingleCupOutcomeDriver = true
      ∧ fxBrauer_hasCupArrivalPredicate = true
      ∧ fxBrauer_hasRegionDriverTotalDispatch = false
      ∧ fxBrauer_hasSingleCupTotalDecision = false
      ∧ fxBrauer_hasSingleCupPeelDischarged = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph

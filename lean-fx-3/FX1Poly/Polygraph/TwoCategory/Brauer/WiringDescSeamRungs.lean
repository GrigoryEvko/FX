import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupArrivalPeel

/-! # BRAUER r37 — the two SEAM RUNGS the r36 wall named: the SNAKE annihilation + the cup-UNTWIST seam

r36 (`Brauer/WiringDescCupArrivalPeel.lean`) shipped the GENERAL distant-tail single-cup peel `legPeelDistantTail`
(a cup slides past any run of crossings / caps each at position `≥ cupPos + 2`) plus the STRADDLE terminal-cleanup
rung (`legSink_cupStraddle_underStandardPrefix`).  Its honest wall named the exhaustive case split's still-missing
seam arms for a cup at `cupPos` (spanning wires `cupPos`, `cupPos + 1`) with the atom immediately to its right:

  * a crossing AT `cupPos` (on the cup's OWN two produced legs) — the cup UNTWIST `σ ∘ cup = cup`, removed by
    `cupUntwistRelation`;
  * an adjacent cap at `cupPos ± 1` (sharing exactly ONE leg) — the S1 / S2 SNAKE annihilation `[cup, cap] ~ []`.

This round ships those two seam rungs, each Σ-carried under a standard prefix and each carrying a strict WORD-LENGTH
drop (the outer termination measure's coordinate 1, held while the distant / straddle slides drop coordinate 2, the
leg fuel).  Both are the length-SHRINKING cousins of the r36 length-HOLDING straddle rung.

## What this file ships (ADDITIVE — every r34/r35/r36 datum and theorem is untouched)

  1. **The propext-clean list-length count `countAtoms`, appended.**  `countAtoms_append` (structural on the left
     word, never `List.length_append` which leaks `propext`) with the two length-drop lemmas `countAtoms_lt_append_cons2`
     (a two-atom window deletes) and `countAtoms_lt_append_cons_afterHead` (the second atom after a fixed head
     deletes) — the exact drop shapes the snake (−2) and untwist (−1 after the surviving cup) rungs need.

  2. **The SNAKE annihilation seam.**  `snakeAnnihilateFree8_cleanS1` / `_cleanS2` — the S1 (`[cup(p+1), cap p] ~ []`)
     and S2 (`[cup p, cap(p+1)] ~ []`) clean moves, `brauerConvFree8_ofFree` of `BrauerConvFree.snake` / `snakeMirror`
     at shift `p`, bridged by `Nat.add_comm` / `Nat.zero_add` (the ∗-cousins of the r36 `straddleSlideFree8_clean`).
     `legSink_snakeAnnihilate_underStandardPrefix` (S1) and `legSink_snakeAnnihilateMirror_underStandardPrefix` (S2) —
     the Σ-carried rungs: extend a running `BrauerConvFree8` by the snake (whiskered off `standardPrefix` + `localPrefix`
     + `suffixWord`), carrying the strict `countAtoms` drop of 2.

  3. **The cup-UNTWIST seam.**  `cupUntwistFree8_clean` (`[cup p, cross p] ~ [cup p]`, `ofFree7` of the shipped
     `cupUntwist_at`) and `legSink_cupUntwist_underStandardPrefix` — the Σ-carried rung firing the shipped
     `cupUntwist_inContext` (a `BrauerConvFree7` length-−1 rewrite lifted to `BrauerConvFree8`), carrying the strict
     `countAtoms` drop of 1 with the surviving cup at the head.

  4. **The snake-neighbor CLASSIFIER + the truth-probed adjudication.**  `snakeNeighborKind cupPos capPos` decides —
     by `Nat.beq` / successor comparison, NO subtraction — whether the neighbor cap ANNIHILATES (at `cupPos ± 1`, one
     shared leg → `[cup, cap] ~ []`), forms a LOOP (at `cupPos`, both shared legs → a bubble `loops += 1`, NOT
     convertible to `[]`), or is DISTANT (at `cupPos + 2 +`, the r36 slide).  `snakeNeighbor_probes` pins the four
     classes by `rfl`; `snakeAnnihilate_diagramSound` pins the two annihilation arms diagram-sound (`decide`), and
     `snakeLoop_notEmptyWord` pins the loop arm as genuinely NOT the empty word (`brauerDiagramOf 0 [cup 0, cap 0]`
     reads `loops := 1 ≠ 0` — it routes to the circle class, not to a snake).

Non-vacuity: `legSnakePeel_demo` (`[cup 1, cap 0, cross 8] ↝ [cross 8]`, the snake sibling of the r36
`legPeelToArrival_demo`) and `legUntwistPeel_demo` (`[cup 2, cross 2, cap 9] ↝ [cup 2, cap 9]`).

## The honest wall — the FULL single-cup peel + the outer assembly remain UNBUILT (named IN this file, no new ledger)

With BOTH seam arms now first-class rungs, the per-cup move set is complete for the exhaustive neighbor split
(untwist / straddle / distant crossing / adjacent-cap snake / distant cap), but the FULL single-cup peel over an
ARBITRARY region is STILL not a discharged recursion: it needs (a) the OUTER driver threading the two seam rungs
+ `legPeelDistantTail` under a nested-structural lexicographic measure `(wordLength, legLexFuel)` — the seam rungs
drop coordinate 1, the slides drop coordinate 2 — over EVERY cup with placed cups untouched; (b) the `loop` /
`bottomCount = 0` circle class the snake classifier's loop arm routes to; (c) the cap-side ∗-dual; (d) the
`DiagramType` driver.  So `fxBrauer_hasSingleCupPeelDischarged` is honestly `false`, and
`fxBrauer_hasStagedInnerDescentDischarged`, `fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`,
`fxBrauer_hasBrauerV2FullCompleteness` all STAY `false`; this round is PURELY ADDITIVE, no master flip is fabricated,
#2013 does NOT close.  Every residual is a route / measure gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889
Thm 2.6).

Raw Lean 4 + Init; structural recursion on word lists (no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix` /
`propext` — `List.length_append` and the stdlib `Nat.beq_refl` LEAK `propext`, so `countAtoms` and closed-literal
`Nat.beq` reductions are used instead).  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the propext-clean length count, appended, with the two drop lemmas -/

/-- `countAtoms` splits over concatenation into a `Nat` sum (structural on the left word, propext-clean — never the
`List.length_append` lemma, which leaks `propext`). -/
theorem countAtoms_append : (wordLeft wordRight : List BrauerAtom) →
    countAtoms (wordLeft ++ wordRight) = countAtoms wordLeft + countAtoms wordRight
  | [], wordRight => by
      show countAtoms wordRight = 0 + countAtoms wordRight
      rw [Nat.zero_add]
  | atom :: rest, wordRight => by
      show 1 + countAtoms (rest ++ wordRight) = (1 + countAtoms rest) + countAtoms wordRight
      rw [countAtoms_append rest wordRight, Nat.add_assoc]

/-- ★ **Deleting a two-atom window strictly drops the count** — `countAtoms (pre ++ suf) < countAtoms (pre ++ (a :: b ::
suf))`.  The snake's −2 drop leg (both cup and cap removed). -/
theorem countAtoms_lt_append_cons2 (prefixWord suffixWord : List BrauerAtom) (firstAtom secondAtom : BrauerAtom) :
    countAtoms (prefixWord ++ suffixWord)
      < countAtoms (prefixWord ++ (firstAtom :: secondAtom :: suffixWord)) := by
  rw [countAtoms_append, countAtoms_append]
  apply Nat.add_lt_add_left
  show countAtoms suffixWord < 1 + (1 + countAtoms suffixWord)
  have hcomm : 1 + (1 + countAtoms suffixWord) = countAtoms suffixWord + 1 + 1 := by
    rw [Nat.add_comm 1 (1 + countAtoms suffixWord), Nat.add_comm 1 (countAtoms suffixWord)]
  rw [hcomm]
  exact Nat.lt_succ_of_lt (Nat.lt_succ_self (countAtoms suffixWord))

/-- ★ **Deleting the atom AFTER a fixed head strictly drops the count** — `countAtoms (pre ++ (head :: suf)) <
countAtoms (pre ++ (head :: mid :: suf))`.  The untwist's −1 drop leg (the crossing removed, the cup head surviving). -/
theorem countAtoms_lt_append_cons_afterHead (prefixWord suffixWord : List BrauerAtom) (headAtom midAtom : BrauerAtom) :
    countAtoms (prefixWord ++ (headAtom :: suffixWord))
      < countAtoms (prefixWord ++ (headAtom :: midAtom :: suffixWord)) := by
  rw [countAtoms_append, countAtoms_append]
  apply Nat.add_lt_add_left
  show 1 + countAtoms suffixWord < 1 + (1 + countAtoms suffixWord)
  apply Nat.add_lt_add_left
  rw [Nat.add_comm 1 (countAtoms suffixWord)]
  exact Nat.lt_succ_self (countAtoms suffixWord)

/-! ## B — the SNAKE annihilation clean moves (the ∗-cousins of `straddleSlideFree8_clean`) -/

/-- ★ **The S1 snake at a clean position.**  `BrauerConvFree.snake cupPos` fires in `shiftWord` form
(`[cupAt (1 + cupPos), capAt (0 + cupPos)] ~ []`); bridged by `Nat.add_comm` / `Nat.zero_add` to the clean
`[cupAt (cupPos + 1), capAt cupPos] ~ []` — the cap one leg LEFT of the cup's near leg annihilates (`(cap ▷ id) ∘
(id ▷ cup) = id`, both sharing wire `cupPos`). -/
theorem snakeAnnihilateFree8_cleanS1 (cupPos : Nat) :
    BrauerConvFree8 [cupAt (cupPos + 1), capAt cupPos] [] := by
  have lhsEq : shiftWord cupPos snakeRelation.lhs = [cupAt (cupPos + 1), capAt cupPos] := by
    show [cupAt (1 + cupPos), capAt (0 + cupPos)] = [cupAt (cupPos + 1), capAt cupPos]
    rw [Nat.add_comm 1 cupPos, Nat.zero_add]
  have rhsEq : shiftWord cupPos snakeRelation.rhs = ([] : List BrauerAtom) := rfl
  rw [← lhsEq, ← rhsEq]
  exact brauerConvFree8_ofFree (BrauerConvFree.snake cupPos)

/-- ★ **The S2 mirror snake at a clean position.**  `BrauerConvFree.snakeMirror cupPos` bridged to the clean
`[cupAt cupPos, capAt (cupPos + 1)] ~ []` — the cap one leg RIGHT of the cup's far leg annihilates (`(id ▷ cap) ∘
(cup ▷ id) = id`, both sharing wire `cupPos + 1`). -/
theorem snakeAnnihilateFree8_cleanS2 (cupPos : Nat) :
    BrauerConvFree8 [cupAt cupPos, capAt (cupPos + 1)] [] := by
  have lhsEq : shiftWord cupPos snakeMirrorRelation.lhs = [cupAt cupPos, capAt (cupPos + 1)] := by
    show [cupAt (0 + cupPos), capAt (1 + cupPos)] = [cupAt cupPos, capAt (cupPos + 1)]
    rw [Nat.zero_add, Nat.add_comm 1 cupPos]
  have rhsEq : shiftWord cupPos snakeMirrorRelation.rhs = ([] : List BrauerAtom) := rfl
  rw [← lhsEq, ← rhsEq]
  exact brauerConvFree8_ofFree (BrauerConvFree.snakeMirror cupPos)

/-! ## C — the cup-UNTWIST clean move -/

/-- ★ **The cup untwist at a clean position** — `[cupAt cupPos, crossingAt cupPos] ~ [cupAt cupPos]`: a crossing on the
cup's OWN two produced legs (an automorphism of the arc) is dropped.  `ofFree7` of the shipped `cupUntwist_at`
(Lehrer–Zhang 2.5∗ `X ∘ U = U`). -/
theorem cupUntwistFree8_clean (cupPos : Nat) :
    BrauerConvFree8 [cupAt cupPos, crossingAt cupPos] [cupAt cupPos] :=
  BrauerConvFree8.ofFree7 (cupUntwist_at cupPos)

/-! ## D — the Σ-carried SNAKE seam rungs (word length −2) -/

/-- ★★ **The Σ-carried S1 SNAKE annihilation rung UNDER a standard prefix.**  Extends a running `BrauerConvFree8` by
the S1 snake (whiskered off `standardPrefix` + `localPrefix` + `suffixWord`), deleting the adjacent cup / cap pair and
carrying the strict `countAtoms` drop of 2 on the working region.  The snake sibling of the r36
`legSink_cupStraddle_underStandardPrefix` — but the snake SHRINKS the word (coordinate-1 drop) where the straddle HELD
it (coordinate-2 drop). -/
theorem legSink_snakeAnnihilate_underStandardPrefix (cupPos : Nat)
    (startWord standardPrefix localPrefix suffixWord : List BrauerAtom)
    (conv : BrauerConvFree8 startWord
        (standardPrefix ++ (localPrefix ++ (cupAt (cupPos + 1) :: capAt cupPos :: suffixWord)))) :
    BrauerConvFree8 startWord (standardPrefix ++ (localPrefix ++ suffixWord))
      ∧ countAtoms (localPrefix ++ suffixWord)
          < countAtoms (localPrefix ++ (cupAt (cupPos + 1) :: capAt cupPos :: suffixWord)) :=
  ⟨conv.trans (BrauerConvFree8.whiskerLeft standardPrefix
      (BrauerConvFree8.whiskerLeft localPrefix
        (BrauerConvFree8.whiskerRight suffixWord (snakeAnnihilateFree8_cleanS1 cupPos)))),
   countAtoms_lt_append_cons2 localPrefix suffixWord (cupAt (cupPos + 1)) (capAt cupPos)⟩

/-- ★★ **The Σ-carried S2 mirror SNAKE annihilation rung UNDER a standard prefix** — the ∗-mirror of the S1 rung,
deleting the `[cupAt cupPos, capAt (cupPos + 1)]` pair. -/
theorem legSink_snakeAnnihilateMirror_underStandardPrefix (cupPos : Nat)
    (startWord standardPrefix localPrefix suffixWord : List BrauerAtom)
    (conv : BrauerConvFree8 startWord
        (standardPrefix ++ (localPrefix ++ (cupAt cupPos :: capAt (cupPos + 1) :: suffixWord)))) :
    BrauerConvFree8 startWord (standardPrefix ++ (localPrefix ++ suffixWord))
      ∧ countAtoms (localPrefix ++ suffixWord)
          < countAtoms (localPrefix ++ (cupAt cupPos :: capAt (cupPos + 1) :: suffixWord)) :=
  ⟨conv.trans (BrauerConvFree8.whiskerLeft standardPrefix
      (BrauerConvFree8.whiskerLeft localPrefix
        (BrauerConvFree8.whiskerRight suffixWord (snakeAnnihilateFree8_cleanS2 cupPos)))),
   countAtoms_lt_append_cons2 localPrefix suffixWord (cupAt cupPos) (capAt (cupPos + 1))⟩

/-! ## E — the Σ-carried cup-UNTWIST seam rung (word length −1, the cup surviving) -/

/-- ★★ **The Σ-carried cup-UNTWIST seam rung UNDER a standard prefix.**  Extends a running `BrauerConvFree8` by the
untwist (the shipped `cupUntwist_inContext` `BrauerConvFree7` rewrite, whiskered off `standardPrefix` and lifted by
`ofFree7`), dropping the crossing trapped on the cup's own legs and carrying the strict `countAtoms` drop of 1 with the
surviving cup at the head.  The untwist arm of the r36 exhaustive split — the crossing AT `cupPos` the distant / straddle
slides can never produce (they only ever put a crossing at `cupPos + 1` or beyond). -/
theorem legSink_cupUntwist_underStandardPrefix (cupPos : Nat)
    (startWord standardPrefix localPrefix suffixWord : List BrauerAtom)
    (conv : BrauerConvFree8 startWord
        (standardPrefix ++ (localPrefix ++ (cupAt cupPos :: crossingAt cupPos :: suffixWord)))) :
    BrauerConvFree8 startWord (standardPrefix ++ (localPrefix ++ (cupAt cupPos :: suffixWord)))
      ∧ countAtoms (localPrefix ++ (cupAt cupPos :: suffixWord))
          < countAtoms (localPrefix ++ (cupAt cupPos :: crossingAt cupPos :: suffixWord)) :=
  ⟨conv.trans (BrauerConvFree8.whiskerLeft standardPrefix
      (BrauerConvFree8.ofFree7 (cupUntwist_inContext localPrefix suffixWord cupPos))),
   countAtoms_lt_append_cons_afterHead localPrefix suffixWord (cupAt cupPos) (crossingAt cupPos)⟩

/-! ## F — the snake-neighbor CLASSIFIER + the truth-probed adjudication (loop vs annihilate vs distant) -/

/-- The kind of a cap neighbor to the right of a cup at `cupPos`, decided from the cup / cap positions alone. -/
inductive SnakeNeighborKind
  /-- The cap sits at `cupPos - 1` (shares wire `cupPos`) — S1 snake, `[cupAt (cupPos + 1), capAt cupPos] ~ []`. -/
  | annihilateLeft
  /-- The cap sits at `cupPos + 1` (shares wire `cupPos + 1`) — S2 snake, `[cupAt cupPos, capAt (cupPos + 1)] ~ []`. -/
  | annihilateRight
  /-- The cap sits AT `cupPos` (shares BOTH legs) — a closed loop (bubble), NOT convertible to `[]`. -/
  | loop
  /-- The cap sits at `cupPos + 2` or beyond — a distant slide (the r36 `legPeelDistantTail`), not a snake redex. -/
  | distant

/-- ★ **The snake-neighbor classifier.**  Decides — by closed `Nat.beq` / successor comparison, NO subtraction (which
leaks `propext`) — into which of the four kinds a cap at `capPos` falls relative to a cup at `cupPos`.  Drives the
exhaustive neighbor split's cap case: `annihilate*` → a snake rung; `loop` → the circle class (r38); `distant` → the
r36 distant slide. -/
def snakeNeighborKind (cupPos capPos : Nat) : SnakeNeighborKind :=
  cond (Nat.beq capPos cupPos) SnakeNeighborKind.loop
    (cond (Nat.beq capPos (cupPos + 1)) SnakeNeighborKind.annihilateRight
      (cond (Nat.beq cupPos (capPos + 1)) SnakeNeighborKind.annihilateLeft
        SnakeNeighborKind.distant))

/-- ★ **The classifier truth-probes, machine-checked** (the recon `#eval` fixtures pinned by `rfl` — closed `Nat.beq`
reductions, no `Nat.beq_refl`).  Cap at the cup's own position is a `loop`; one leg right is `annihilateRight`; one leg
left is `annihilateLeft`; two-or-more away is `distant`. -/
theorem snakeNeighbor_probes :
    snakeNeighborKind 0 0 = SnakeNeighborKind.loop
      ∧ snakeNeighborKind 0 1 = SnakeNeighborKind.annihilateRight
      ∧ snakeNeighborKind 1 0 = SnakeNeighborKind.annihilateLeft
      ∧ snakeNeighborKind 1 1 = SnakeNeighborKind.loop
      ∧ snakeNeighborKind 0 2 = SnakeNeighborKind.distant
      ∧ snakeNeighborKind 3 5 = SnakeNeighborKind.distant :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★ **Both annihilation arms are diagram-sound.**  The S1 (`[cupAt 1, capAt 0]`) and S2 (`[cupAt 0, capAt 1]`) cup / cap
pairs each straighten to the identity through-strand over one bottom wire (both `brauerDiagramOf 1 = brauerDiagramOf 1
[]`, `decide`) — the shared-ONE-leg zig-zags the snake relation removes. -/
theorem snakeAnnihilate_diagramSound :
    brauerDiagramOf 1 [cupAt 1, capAt 0] = brauerDiagramOf 1 ([] : List BrauerAtom)
      ∧ brauerDiagramOf 1 [cupAt 0, capAt 1] = brauerDiagramOf 1 ([] : List BrauerAtom) :=
  ⟨by decide, by decide⟩

/-- ★ **The loop arm is NOT the empty word.**  A cap AT the cup's position (sharing BOTH legs) closes a bubble:
`brauerDiagramOf 0 [cupAt 0, capAt 0]` reads `loops := 1 ≠ 0 = brauerDiagramOf 0 []` (`decide`).  So the `loop` class is
genuinely NOT a snake — it is the circle scalar `δ`, routed to the `bottomCount = 0` class (r38), never convertible to
`[]` (all eight V2 relations preserve `loops := 0`). -/
theorem snakeLoop_notEmptyWord :
    brauerDiagramOf 0 [cupAt 0, capAt 0] ≠ brauerDiagramOf 0 ([] : List BrauerAtom) := by decide

/-! ## G — non-vacuity: the two seam rungs perform genuine whisker-free reductions -/

/-- ★ **The snake peel flagship** — `[cupAt 1, capAt 0, crossingAt 8] ↝ [crossingAt 8]` via the S1 snake whiskered by
the trailing crossing (word length 3 → 1).  The snake sibling of the r36 `legPeelToArrival_demo`. -/
theorem legSnakePeel_demo :
    BrauerConvFree8 [cupAt 1, capAt 0, crossingAt 8] [crossingAt 8] :=
  BrauerConvFree8.whiskerRight [crossingAt 8] (snakeAnnihilateFree8_cleanS1 0)

/-- ★ **The untwist peel flagship** — `[cupAt 2, crossingAt 2, capAt 9] ↝ [cupAt 2, capAt 9]` via the untwist whiskered
by the trailing cap (word length 3 → 2, the crossing on the cup's own legs removed). -/
theorem legUntwistPeel_demo :
    BrauerConvFree8 [cupAt 2, crossingAt 2, capAt 9] [cupAt 2, capAt 9] :=
  BrauerConvFree8.whiskerRight [capAt 9] (cupUntwistFree8_clean 2)

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the SNAKE annihilation seam rung SHIPS.**  The clean S1 / S2 moves
(`snakeAnnihilateFree8_cleanS1` / `_cleanS2`, `brauerConvFree8_ofFree` of `BrauerConvFree.snake` / `snakeMirror` bridged
by `Nat.add_comm` / `Nat.zero_add`) and the Σ-carried rungs
(`legSink_snakeAnnihilate_underStandardPrefix` / `legSink_snakeAnnihilateMirror_underStandardPrefix`, whiskered off a
standard prefix, carrying the strict `countAtoms` −2 drop) discharge the adjacent-cap arm of the r36 exhaustive split.
The well-formedness gate is truth-probed: `snakeNeighborKind` classifies annihilate (one shared leg) vs loop (both legs,
`snakeLoop_notEmptyWord`) vs distant, `snakeNeighbor_probes` + `snakeAnnihilate_diagramSound` pin the fixtures.
Non-vacuity: `legSnakePeel_demo`.  `= true`. -/
def fxBrauer_hasSnakeAnnihilationRung : Bool := true

/-- ★★ **Honesty marker — the cup-UNTWIST seam rung SHIPS.**  `cupUntwistFree8_clean` (`ofFree7` of the shipped
`cupUntwist_at`) and `legSink_cupUntwist_underStandardPrefix` (the Σ-carried rung firing the shipped
`cupUntwist_inContext`, carrying the strict `countAtoms` −1 drop with the surviving cup at the head) discharge the
crossing-on-own-legs arm of the r36 exhaustive split — the untwist case the distant / straddle slides can never
produce.  Non-vacuity: `legUntwistPeel_demo`.  `= true`. -/
def fxBrauer_hasCupUntwistSeamRung : Bool := true

/-- **Honesty WALL marker — the FULL single-cup peel + the outer assembly are NOT built; #2013 does NOT close.**  With
BOTH seam arms now first-class rungs the per-cup move set is complete for the exhaustive neighbor split, but the FULL
single-cup peel over an ARBITRARY region is unbuilt: it needs the OUTER driver threading the two seam rungs +
`legPeelDistantTail` under a nested-structural lexicographic measure `(wordLength, legLexFuel)` (the seam rungs drop
coordinate 1, the slides drop coordinate 2) over EVERY cup with placed cups untouched, plus the `loop` / `bottomCount =
0` circle class the snake classifier routes to, the cap-side ∗-dual, and the `DiagramType` driver.  So
`fxBrauer_hasStagedInnerDescentDischarged` STAYS `false`, and `fxBrauer_hasFreeBrauerStraighteningNF`,
`fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness` all STAY `false`.  A route / measure gap, never
a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).  `= false`. -/
def fxBrauer_hasSeamRungOuterAssembly : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER seam-rungs terminal state — MACHINE-CHECKED.**  The two new seam markers are `true` (the snake
annihilation rung, the cup-untwist rung), built on the r36 `fxBrauer_hasDistantTailCupPeel` (the distant-tail peel) and
`fxBrauer_hasStraddleTerminalCleanup` (the straddle cleanup), while the outer assembly and all five completeness /
discharge masters STAY `false`.  A `rfl`-conjunction the kernel checks; this round is purely additive, no master flip is
fabricated, #2013 does NOT close. -/
theorem fxBrauer_seamRungsTerminalState :
    fxBrauer_hasSnakeAnnihilationRung = true
      ∧ fxBrauer_hasCupUntwistSeamRung = true
      ∧ fxBrauer_hasDistantTailCupPeel = true
      ∧ fxBrauer_hasStraddleTerminalCleanup = true
      ∧ fxBrauer_hasSeamRungOuterAssembly = false
      ∧ fxBrauer_hasSingleCupPeelDischarged = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph

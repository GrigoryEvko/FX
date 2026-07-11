import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcInsertionPeel

/-! # BRAUER — the cup-ARRIVAL predicate + the GENERAL distant-tail single-cup PEEL over the r34 leg fuel

r35 (`Brauer/WiringDescArcInsertionPeel.lean`) shipped the single-arc PEEL STEP (the two Σ-carried leg-fuel sink rungs
`legSink_cupCrossing` / `legSink_cupCap`, whiskered under a standard prefix) and a HAND-BUILT width-4 flagship
`legPeelToArrival_demo` sinking ONE cup three places to its slot.  Its wall marker `fxBrauer_hasLegFuelOuterAssembly`
named the still-missing pieces; its honest companion `legPeelToArrival_topPermTail_demo` recorded that arrival is NOT
always the tail (a topPerm crossing sits legitimately right of the arrived cup), leaving open the PRECISE arrival
predicate and a GENERAL (not width-4-hand-built) peel recursion.

This round ships two additive ingredients:

  1. **The cup-ARRIVAL predicate, truth-probed then pinned.**  `cupHasArrived workingRegion` (the honest / complete
     measure-arrival: the leftmost cup has NO atoms right of it in the working region, `atomsRightOfFirstCup = 0`) and
     the decidable-from-the-word PROXY `cupIsCapFreeRight` (no cap sits right of the leftmost cup), which AGREE on
     every reachable state and disagree only on a bare middle crossing (the honest false-positive the working-region
     factoring removes).  Probed by `#eval` first — companion TRUE (`atomsRight = 1` but cap-free right), every
     flagship mid-peel FALSE, flagship arrival TRUE, both fresh 2-cup standard forms TRUE at their placed cups, the
     hostile two-adjacent-cups-then-cap FALSE — then pinned as `cupArrival_probes`.

  2. **The GENERAL distant-tail single-cup PEEL, `legPeelDistantTail`.**  For a cup at `cupPos` followed by a DISTANT
     TAIL (a `List (DistantSlideStep cupPos)`: any run of crossings / caps each at position `≥ cupPos + 2`, the shape
     of a reachable, untwist-normalized, straddle-free working region), a STRUCTURAL recursion on the tail sinks the
     cup all the way to arrival, producing a genuine `BrauerConvFree8` reduction TOGETHER with `atomsRightOfFirstCup
     arrivedRegion = 0`.  This is the r35 flagship's hand-built three-step chain made a general recursion over any
     length (`legPeelToArrival_viaDistantTail_demo` re-derives the exact r35 target through it; `legPeelDistantTail_len5_demo`
     runs a five-step tail).  The arrived region sits at the fuel FLOOR (`legLexFuel_ofArrived_le_one`).

  3. **The STRADDLE terminal-cleanup rung** (the r34/r35 move set's genuinely-new inner brick).  The distant slides
     drop the PRIMARY leg coordinate (distance); the ADJACENT-STRADDLE crossing (at `cupPos + 1`) is the secondary
     move that holds the primary and drops the tie-break bit.  `legFuel_leftmostCupStraddle_lt` (the SECONDARY context
     descent, the ∗-cousin of the shipped `legFuel_leftmostCupCrossing_lt`) and the Σ-carried
     `legSink_cupStraddle_underStandardPrefix` (whiskering the standard prefix off, no radix bound needed) complete the
     per-cup move set with the cup slide (`straddleSlideFree8_clean`, the `BrauerConvFree8.cupSlide` bridged off its
     `shiftWord` positional form).

## The honest wall — the FULL single-cup peel + the outer assembly are UNBUILT (named IN this file, no new ledger)

The distant-tail peel discharges the case that matters for a reachable working region, but the FULL single-cup peel
over an ARBITRARY region is NOT a discharged recursion: the exhaustive case split still needs (a) the untwist case
(a crossing AT `cupPos`, removed by `cupUntwistRelation`, requires seeding with `untwistNormalize_conv8`), (b) the
adjacent-cap annihilation (the S1/S2 snake, `nomatch`-ruled-out only under a reduced-matching well-formedness), and
(c) the outer `arcCountFuel` (`fxBrauer_hasStagedArcCountFuel = true`) threading `legPeelDistantTail` over EVERY cup
with placed cups untouched, plus the cap-side ∗-dual, the `bottomCount = 0` class, and the `DiagramType` driver.  So
`fxBrauer_hasSingleCupPeelDischarged` is honestly `false`, and `fxBrauer_hasStagedInnerDescentDischarged`,
`fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness` all
STAY `false`; this round is PURELY ADDITIVE, no master flip is fabricated, #2013 does NOT close.  Every residual is a
route / measure gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).

Raw Lean 4 + Init; structural recursion on word lists (no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix` /
`propext` — the stdlib `Nat.beq_refl` LEAKS `propext`, so the hand-rolled structural `beq_self` is used instead).
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the cup-arrival predicate (measure-arrival + the decidable cap-free proxy) -/

/-- The suffix strictly to the right of the leftmost cup (propext-clean standalone recursion): drop non-cups until the
first cup, then keep what follows it. -/
def suffixRightOfFirstCup : List BrauerAtom → List BrauerAtom
  | [] => []
  | atom :: rest => cond (isCupAtom atom) rest (suffixRightOfFirstCup rest)

/-- A word contains NO cap — a cap is the sole `outputCount = 0` generator (cup has `outputCount = 2`, crossing `2`).
Structural, propext-clean. -/
def hasNoCap : List BrauerAtom → Bool
  | [] => true
  | atom :: rest => cond (Nat.beq atom.wiring.outputCount 0) false (hasNoCap rest)

/-- ★ **The DECIDABLE per-step arrival PROXY** — no cap sits right of the leftmost cup.  Sound on the peel's reachable
working-region states (where the only atoms right of an unarrived cup are the topPerm crossing suffix); NOT a whole-word
theorem — a bare middle crossing right of the cup is a false-positive, since the flat word cannot tell a middle crossing
from a topPerm crossing.  That gap is exactly why the complete predicate needs the working-region factoring. -/
def cupIsCapFreeRight (word : List BrauerAtom) : Bool := hasNoCap (suffixRightOfFirstCup word)

/-- ★ **The HONEST / COMPLETE arrival predicate on the WORKING REGION** (the topPerm-crossing suffix + standard prefix
already factored off): the leftmost cup sits at the region tail, `atomsRightOfFirstCup workingRegion = 0`.  This is the
predicate `legPeelDistantTail` establishes at the end of a peel. -/
def cupHasArrived (workingRegion : List BrauerAtom) : Prop := atomsRightOfFirstCup workingRegion = 0

/-- ★ **The arrival truth-probes, machine-checked** (the recon `#eval` fixtures pinned by `decide` — `cupIsCapFreeRight`
is pure list traversal, no `brauerDiagramOf`, so `decide` is cheap and safe).  Companion arrived (cap-free right yet
`atomsRight = 1`, a topPerm crossing legitimately trailing); every flagship mid-peel un-arrived; flagship arrival
arrived; BOTH fresh 2-cup standard forms arrived at their placed cups; the hostile two-adjacent-cups-then-cap
un-arrived. -/
theorem cupArrival_probes :
    cupIsCapFreeRight [capAt 1, cupAt 0, crossingAt 8] = true
      ∧ atomsRightOfFirstCup [capAt 1, cupAt 0, crossingAt 8] = 1
      ∧ cupIsCapFreeRight [cupAt 0, crossingAt 3, crossingAt 4, capAt 5] = false
      ∧ cupIsCapFreeRight [crossingAt 1, cupAt 0, crossingAt 4, capAt 5] = false
      ∧ cupIsCapFreeRight [crossingAt 1, crossingAt 2, cupAt 0, capAt 5] = false
      ∧ cupIsCapFreeRight [crossingAt 1, crossingAt 2, capAt 3, cupAt 0] = true
      ∧ cupIsCapFreeRight [cupAt 0, cupAt 0, crossingAt 1, crossingAt 2] = true
      ∧ cupIsCapFreeRight [cupAt 0, crossingAt 1, crossingAt 2] = true
      ∧ cupIsCapFreeRight [cupAt 0, cupAt 0, capAt 5] = false :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- ★ **The honest false-positive, pinned.**  `[cupAt 0, crossingAt 4]` reads cap-free-right (`cupIsCapFreeRight = true`)
yet is NOT arrived on the working region (`atomsRightOfFirstCup = 1`): the bare crossing right of the cup that the flat
word cannot classify as middle-vs-topPerm.  The decidable proxy is sound only under the reachable-state invariant "no
bare middle crossing is right of an unarrived cup", not as a whole-word theorem. -/
theorem cupIsCapFreeRight_falsePositive :
    cupIsCapFreeRight [cupAt 0, crossingAt 4] = true ∧ atomsRightOfFirstCup [cupAt 0, crossingAt 4] = 1 :=
  ⟨by decide, by decide⟩

/-! ## B — the distant-tail descriptor + its word -/

/-- ★ **One step of a DISTANT tail** to the right of a cup at `cupPos`: either a crossing or a cap, each carrying its
disjointness proof `cupPos ≤ _` (so it sits at position `_ + 2`, genuinely distant — the cup can slide past it by the
shipped disjoint-support slide).  A `Type`-valued descriptor so the peel recurses structurally on `List`s of them. -/
inductive DistantSlideStep (cupPos : Nat) : Type
  | crossing (crossPos : Nat) (disjoint : cupPos ≤ crossPos) : DistantSlideStep cupPos
  | cap (capPos : Nat) (disjoint : cupPos ≤ capPos) : DistantSlideStep cupPos

/-- The generator a distant step decodes to — a crossing or cap at position `_ + 2` (the "before slide" position, two
strands right of the cup). -/
def distantStepAtom {cupPos : Nat} : DistantSlideStep cupPos → BrauerAtom
  | .crossing crossPos _ => crossingAt (crossPos + 2)
  | .cap capPos _ => capAt (capPos + 2)

/-- The word a distant tail decodes to — the run of distant generators to the right of the cup. -/
def distantTailWord {cupPos : Nat} : List (DistantSlideStep cupPos) → List BrauerAtom
  | [] => []
  | step :: rest => distantStepAtom step :: distantTailWord rest

/-! ## C — the GENERAL distant-tail single-cup peel (structural recursion on the tail) -/

/-- ★★ **THE distant-tail single-cup PEEL.**  Given a cup at `cupPos` followed by any distant tail `tail`, a STRUCTURAL
recursion on `tail` sinks the cup all the way to arrival: it returns the sunk `arrivedRegion` TOGETHER with a genuine
`BrauerConvFree8 (cupAt cupPos :: distantTailWord tail) arrivedRegion` (each step a whiskered disjoint slide —
`distantCupCrossingSlideFree8` / `distantCupCapSlideFree8` — trans-composed, the leg fuel dropping its PRIMARY distance
coordinate every step by the shipped `legFuel_leftmostCup*_lt`) and the ARRIVAL certificate `atomsRightOfFirstCup
arrivedRegion = 0`.  The peeled generator is CONSED onto the front (no `List.append_assoc`, no re-association), so the
whole construction is definitional; arrival propagates because `isCupAtom (crossingAt _) = isCupAtom (capAt _) = false`
lets `atomsRightOfFirstCup` see through the consed non-cup.  The r35 hand-built width-4 flagship generalized to any
length. -/
def legPeelDistantTail (cupPos : Nat) :
    (tail : List (DistantSlideStep cupPos)) →
    PSigma (fun arrivedRegion : List BrauerAtom =>
      BrauerConvFree8 (cupAt cupPos :: distantTailWord tail) arrivedRegion
        ∧ atomsRightOfFirstCup arrivedRegion = 0)
  | [] =>
      ⟨[cupAt cupPos],
       BrauerConvFree8.ofFree7 (BrauerConvFree7.ofFree (BrauerConvFree.refl [cupAt cupPos])),
       rfl⟩
  | .crossing crossPos disjoint :: rest =>
      let recResult := legPeelDistantTail cupPos rest
      ⟨crossingAt crossPos :: recResult.1,
       BrauerConvFree8.trans
         (BrauerConvFree8.whiskerRight (distantTailWord rest)
           (distantCupCrossingSlideFree8 cupPos crossPos disjoint))
         (BrauerConvFree8.whiskerLeft [crossingAt crossPos] recResult.2.1),
       recResult.2.2⟩
  | .cap capPos disjoint :: rest =>
      let recResult := legPeelDistantTail cupPos rest
      ⟨capAt capPos :: recResult.1,
       BrauerConvFree8.trans
         (BrauerConvFree8.whiskerRight (distantTailWord rest)
           (distantCupCapSlideFree8 cupPos capPos disjoint))
         (BrauerConvFree8.whiskerLeft [capAt capPos] recResult.2.1),
       recResult.2.2⟩

/-- ★ **The distant-tail peel under a standard prefix + local prefix — the J1-seam framing.**  Whiskering the OUTER
driver's `standardPrefix` (which MAY contain placed cups) and the cup's cupless `localPrefix` off by two nested
`whiskerLeft`s, the peel runs on the working region alone.  Same statement as the bare peel, one whiskering shell. -/
def legPeelDistantTail_underStandardPrefix (cupPos : Nat)
    (standardPrefix localPrefix : List BrauerAtom) (tail : List (DistantSlideStep cupPos)) :
    PSigma (fun arrivedRegion : List BrauerAtom =>
      BrauerConvFree8 (standardPrefix ++ (localPrefix ++ (cupAt cupPos :: distantTailWord tail)))
          (standardPrefix ++ (localPrefix ++ arrivedRegion))
        ∧ atomsRightOfFirstCup arrivedRegion = 0) :=
  let peeled := legPeelDistantTail cupPos tail
  ⟨peeled.1,
   BrauerConvFree8.whiskerLeft standardPrefix (BrauerConvFree8.whiskerLeft localPrefix peeled.2.1),
   peeled.2.2⟩

/-- ★★ **The r35 flagship, re-derived through the GENERAL peel.**  The exact r35 word
`[cupAt 0, crossingAt 3, crossingAt 4, capAt 5] ↝ [crossingAt 1, crossingAt 2, capAt 3, cupAt 0]` is now the output of
`legPeelDistantTail 0` on the three-step distant tail `[crossing 1, crossing 2, cap 3]` — the hand-built chain replaced
by a recursion, with arrival established. -/
theorem legPeelToArrival_viaDistantTail_demo :
    BrauerConvFree8 [cupAt 0, crossingAt 3, crossingAt 4, capAt 5]
                    [crossingAt 1, crossingAt 2, capAt 3, cupAt 0]
      ∧ atomsRightOfFirstCup [crossingAt 1, crossingAt 2, capAt 3, cupAt 0] = 0 :=
  let peeled := legPeelDistantTail 0
    [.crossing 1 (by decide), .crossing 2 (by decide), .cap 3 (by decide)]
  ⟨peeled.2.1, peeled.2.2⟩

/-- ★ **A FIVE-step distant tail — genuinely not width-limited.**  The cup at `0` sinks past five distant generators
(crossing, crossing, cap, crossing, cap) to
`[crossingAt 1, crossingAt 2, capAt 3, crossingAt 4, capAt 5, cupAt 0]`, carrying a real `BrauerConvFree8` reduction and
arriving — a chain neither r34 nor r35 could perform without hand-building each cell. -/
theorem legPeelDistantTail_len5_demo :
    BrauerConvFree8 [cupAt 0, crossingAt 3, crossingAt 4, capAt 5, crossingAt 6, capAt 7]
                    [crossingAt 1, crossingAt 2, capAt 3, crossingAt 4, capAt 5, cupAt 0]
      ∧ atomsRightOfFirstCup [crossingAt 1, crossingAt 2, capAt 3, crossingAt 4, capAt 5, cupAt 0] = 0 :=
  let peeled := legPeelDistantTail 0
    [.crossing 1 (by decide), .crossing 2 (by decide), .cap 3 (by decide),
      .crossing 4 (by decide), .cap 5 (by decide)]
  ⟨peeled.2.1, peeled.2.2⟩

/-- ★ **The arrived region sits at the leg-fuel FLOOR.**  When `atomsRightOfFirstCup region = 0` (arrival), the leg
fuel is just the tie-break bit, `≤ 1` — strictly below any radix `> 1`, so a nonempty peel strictly descended.  The
bridge from the peel's arrival certificate to the r34 `legLexFuel` measure. -/
theorem legLexFuel_ofArrived_le_one (radix : Nat) (region : List BrauerAtom)
    (arrived : atomsRightOfFirstCup region = 0) : legLexFuel radix region ≤ 1 := by
  show atomsRightOfFirstCup region * radix + straddleBitAtFirstCup region ≤ 1
  rw [arrived, Nat.zero_mul, Nat.zero_add]
  exact straddleBitAtFirstCup_le_one region

/-! ## D — the STRADDLE terminal-cleanup rung (the new SECONDARY-drop inner brick) -/

/-- A cup-free cons head is a non-cup: from `hasNoCup (atom :: rest) = true`, `isCupAtom atom = false`. -/
theorem isCupAtom_false_of_hasNoCup_cons {atom : BrauerAtom} {rest : List BrauerAtom}
    (cupless : hasNoCup (atom :: rest) = true) : isCupAtom atom = false := by
  have expand : hasNoCup (atom :: rest) = cond (isCupAtom atom) false (hasNoCup rest) := rfl
  rw [expand] at cupless
  cases hAtom : isCupAtom atom with
  | true => rw [hAtom] at cupless; nomatch cupless
  | false => rfl

/-- A cup-free cons has a cup-free tail. -/
theorem hasNoCup_cons_tail {atom : BrauerAtom} {rest : List BrauerAtom}
    (cupless : hasNoCup (atom :: rest) = true) : hasNoCup rest = true := by
  have expand : hasNoCup (atom :: rest) = cond (isCupAtom atom) false (hasNoCup rest) := rfl
  rw [expand, isCupAtom_false_of_hasNoCup_cons cupless] at cupless
  exact cupless

/-- `Nat.beq n n = true`, hand-rolled structurally (the stdlib `Nat.beq_refl` LEAKS `propext`). -/
theorem beq_self : (n : Nat) → Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_self n

/-- `Nat.beq n (n + 2) = false`, structural. -/
theorem beq_self_plus_two : (n : Nat) → Nat.beq n (n + 2) = false
  | 0 => rfl
  | n + 1 => beq_self_plus_two n

/-- The straddle window bit of a cup at `cupPos` immediately followed by a crossing at `cupPos + 1` is `1` (a genuine
straddle). -/
theorem straddleWindowBit_cupCrossingSucc (cupPos : Nat) :
    straddleWindowBit (cupAt cupPos) (crossingAt (cupPos + 1)) = 1 := by
  show cond (true && true && Nat.beq (cupPos + 1) (cupPos + 1)) 1 0 = 1
  rw [beq_self]; rfl

/-- After the cup slide relabels — a cup at `cupPos + 1` followed by a crossing at `cupPos` — the straddle window bit is
`0` (the crossing is no longer at `first.position + 1`). -/
theorem straddleWindowBit_cupSuccCrossing (cupPos : Nat) :
    straddleWindowBit (cupAt (cupPos + 1)) (crossingAt cupPos) = 0 := by
  show cond (true && true && Nat.beq cupPos (cupPos + 1 + 1)) 1 0 = 0
  rw [beq_self_plus_two]; rfl

/-- ★ **The cup slide at a clean position.**  The `BrauerConvFree8.cupSlide cupPos` constructor fires in `shiftWord`
form (`[cupAt (0 + cupPos), crossingAt (1 + cupPos)] ↝ [cupAt (1 + cupPos), crossingAt (0 + cupPos)]`); bridged by
`Nat.zero_add` / `Nat.add_comm` to the clean `[cupAt cupPos, crossingAt (cupPos + 1)] ↝ [cupAt (cupPos + 1),
crossingAt cupPos]`, the straddle relabel the fold applies at the cup's own leg. -/
theorem straddleSlideFree8_clean (cupPos : Nat) :
    BrauerConvFree8 [cupAt cupPos, crossingAt (cupPos + 1)] [cupAt (cupPos + 1), crossingAt cupPos] := by
  have lhsEq : shiftWord cupPos cupSlideRelation.lhs = [cupAt cupPos, crossingAt (cupPos + 1)] := by
    show [cupAt (0 + cupPos), crossingAt (1 + cupPos)] = [cupAt cupPos, crossingAt (cupPos + 1)]
    rw [Nat.zero_add, Nat.add_comm 1 cupPos]
  have rhsEq : shiftWord cupPos cupSlideRelation.rhs = [cupAt (cupPos + 1), crossingAt cupPos] := by
    show [cupAt (1 + cupPos), crossingAt (0 + cupPos)] = [cupAt (cupPos + 1), crossingAt cupPos]
    rw [Nat.zero_add, Nat.add_comm 1 cupPos]
  rw [← lhsEq, ← rhsEq]
  exact BrauerConvFree8.cupSlide cupPos

/-- ★ **The leftmost-cup straddle window bit in ARBITRARY cupless-prefix context.**  When `prefixWord` has no cup, the
leftmost cup of `prefixWord ++ (firstCupAtom :: secondAtom :: rest)` is `firstCupAtom`, so the straddle bit is
`straddleWindowBit firstCupAtom secondAtom` — the prefix pushes the cup right but does not change its immediate
successor.  The straddle read-off (the ∗-cousin of the shipped `atomsRightOfFirstCup_prefixCupless`).  Standalone
three-way structural recursion on `prefixWord` (`[]` / `[single]` / two-or-more), NO `List.append_assoc`. -/
theorem straddleBitAtFirstCup_prefixCupless :
    (prefixWord : List BrauerAtom) → (firstCupAtom secondAtom : BrauerAtom) → (rest : List BrauerAtom) →
    hasNoCup prefixWord = true → isCupAtom firstCupAtom = true →
    straddleBitAtFirstCup (prefixWord ++ (firstCupAtom :: secondAtom :: rest))
      = straddleWindowBit firstCupAtom secondAtom
  | [], firstCupAtom, secondAtom, rest, _, hCup => by
      show cond (isCupAtom firstCupAtom) (straddleWindowBit firstCupAtom secondAtom)
            (straddleBitAtFirstCup (secondAtom :: rest)) = straddleWindowBit firstCupAtom secondAtom
      rw [hCup]; rfl
  | [singleAtom], firstCupAtom, secondAtom, rest, cupless, hCup => by
      have hsingle : isCupAtom singleAtom = false := isCupAtom_false_of_hasNoCup_cons cupless
      show cond (isCupAtom singleAtom) (straddleWindowBit singleAtom firstCupAtom)
            (straddleBitAtFirstCup (firstCupAtom :: secondAtom :: rest)) = straddleWindowBit firstCupAtom secondAtom
      rw [hsingle]
      show cond (isCupAtom firstCupAtom) (straddleWindowBit firstCupAtom secondAtom)
            (straddleBitAtFirstCup (secondAtom :: rest)) = straddleWindowBit firstCupAtom secondAtom
      rw [hCup]; rfl
  | firstPrefix :: secondPrefix :: restPrefix, firstCupAtom, secondAtom, rest, cupless, hCup => by
      have hfirst : isCupAtom firstPrefix = false := isCupAtom_false_of_hasNoCup_cons cupless
      show cond (isCupAtom firstPrefix) (straddleWindowBit firstPrefix secondPrefix)
            (straddleBitAtFirstCup (secondPrefix :: (restPrefix ++ (firstCupAtom :: secondAtom :: rest))))
            = straddleWindowBit firstCupAtom secondAtom
      rw [hfirst]
      exact straddleBitAtFirstCup_prefixCupless (secondPrefix :: restPrefix) firstCupAtom secondAtom rest
        (hasNoCup_cons_tail cupless) hCup

/-- ★★ **The leg fuel descends when the leftmost cup crosses an ADJACENT STRADDLE crossing, in arbitrary context.**  The
straddle slide `prefixWord ++ (cupAt cupPos :: crossingAt (cupPos + 1) :: suffixWord) ↝ prefixWord ++ (cupAt (cupPos + 1)
:: crossingAt cupPos :: suffixWord)` HOLDS the primary distance (the cup stays leftmost with one atom after it) and
drops the tie-break bit `1 → 0` — a SECONDARY `legLexFuel` descent, needing NO radix bound (unlike the distant primary
descents).  The ∗-cousin of the shipped `legFuel_leftmostCupCrossing_lt`; the r34 `legFuel_perCell_drops` proved this
drop only on a closed literal, this is the general context lemma. -/
theorem legFuel_leftmostCupStraddle_lt (radix cupPos : Nat)
    (prefixWord suffixWord : List BrauerAtom) (cupless : hasNoCup prefixWord = true) :
    legLexFuel radix (prefixWord ++ (cupAt (cupPos + 1) :: crossingAt cupPos :: suffixWord))
      < legLexFuel radix (prefixWord ++ (cupAt cupPos :: crossingAt (cupPos + 1) :: suffixWord)) := by
  apply legLex_lt_of_secondary
  · rw [atomsRightOfFirstCup_prefixCupless prefixWord (cupPos + 1) (crossingAt cupPos :: suffixWord) cupless,
        atomsRightOfFirstCup_prefixCupless prefixWord cupPos (crossingAt (cupPos + 1) :: suffixWord) cupless]
    rfl
  · rw [straddleBitAtFirstCup_prefixCupless prefixWord (cupAt (cupPos + 1)) (crossingAt cupPos) suffixWord
          cupless rfl,
        straddleBitAtFirstCup_prefixCupless prefixWord (cupAt cupPos) (crossingAt (cupPos + 1)) suffixWord
          cupless rfl,
        straddleWindowBit_cupSuccCrossing, straddleWindowBit_cupCrossingSucc]
    decide

/-- ★★ **The Σ-carried STRADDLE sink rung UNDER a standard prefix.**  Extends a running `BrauerConvFree8` by the
straddle relabel at the cup's leg (whiskered off `standardPrefix` + cupless `localPrefix` + `suffixWord`), carrying the
strict SECONDARY `legLexFuel` drop on the working region.  The straddle sibling of the shipped
`legSink_cupCrossing_underStandardPrefix` — the per-cup move set's terminal cleanup. -/
theorem legSink_cupStraddle_underStandardPrefix (radix cupPos : Nat)
    (startWord standardPrefix localPrefix suffixWord : List BrauerAtom)
    (cuplessLocal : hasNoCup localPrefix = true)
    (conv : BrauerConvFree8 startWord
        (standardPrefix ++ (localPrefix ++ (cupAt cupPos :: crossingAt (cupPos + 1) :: suffixWord)))) :
    BrauerConvFree8 startWord
        (standardPrefix ++ (localPrefix ++ (cupAt (cupPos + 1) :: crossingAt cupPos :: suffixWord)))
      ∧ legLexFuel radix (localPrefix ++ (cupAt (cupPos + 1) :: crossingAt cupPos :: suffixWord))
          < legLexFuel radix (localPrefix ++ (cupAt cupPos :: crossingAt (cupPos + 1) :: suffixWord)) :=
  ⟨conv.trans (BrauerConvFree8.whiskerLeft standardPrefix
      (BrauerConvFree8.whiskerLeft localPrefix
        (BrauerConvFree8.whiskerRight suffixWord (straddleSlideFree8_clean cupPos)))),
   legFuel_leftmostCupStraddle_lt radix cupPos localPrefix suffixWord cuplessLocal⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the cup-ARRIVAL predicate SHIPS.**  `cupHasArrived` (the complete measure-arrival,
`atomsRightOfFirstCup = 0` on the working region) and `cupIsCapFreeRight` (the decidable cap-free-right proxy) are pinned
against the recon fixtures (`cupArrival_probes`): companion arrived, every flagship mid-peel un-arrived, flagship arrival
arrived, both fresh 2-cup standard forms arrived, the hostile form un-arrived.  The proxy's sole false-positive (a bare
middle crossing, `cupIsCapFreeRight_falsePositive`) is pinned as the honest working-region-factoring gap.  `= true`. -/
def fxBrauer_hasCupArrivalPredicate : Bool := true

/-- ★★ **Honesty marker — the GENERAL distant-tail single-cup PEEL ships.**  `legPeelDistantTail` sinks one cup past any
distant tail by structural recursion, producing a real `BrauerConvFree8` reduction with arrival established; the r35
hand-built width-4 flagship is re-derived through it (`legPeelToArrival_viaDistantTail_demo`) and a five-step tail runs
(`legPeelDistantTail_len5_demo`), the arrived region at the leg-fuel floor (`legLexFuel_ofArrived_le_one`).  The peel
step made a length-generic recursion.  `= true`. -/
def fxBrauer_hasDistantTailCupPeel : Bool := true

/-- ★★ **Honesty marker — the STRADDLE terminal-cleanup rung ships.**  `legFuel_leftmostCupStraddle_lt` (the SECONDARY
context descent, no radix bound) and `legSink_cupStraddle_underStandardPrefix` (the Σ-carried straddle rung, via the
`shiftWord`-bridged `straddleSlideFree8_clean` and the straddle read-off `straddleBitAtFirstCup_prefixCupless`) complete
the per-cup move set the distant slides began — the r34 `legFuel_perCell_drops`' closed-literal straddle drop made
general context.  `= true`. -/
def fxBrauer_hasStraddleTerminalCleanup : Bool := true

/-- **Honesty WALL marker — the FULL single-cup peel + the outer assembly are NOT built; #2013 does NOT close.**  The
distant-tail peel + straddle rung discharge the reachable, untwist-normalized, straddle-clean working region, but the
FULL single-cup peel over an ARBITRARY region is unbuilt: the exhaustive case split still needs the untwist case (a
crossing AT `cupPos`, requiring an `untwistNormalize_conv8` seed), the adjacent-cap S1/S2 snake annihilation
(`nomatch`-ruled-out only under a reduced-matching well-formedness), and the OUTER `arcCountFuel`
(`fxBrauer_hasStagedArcCountFuel = true`) threading the peel over EVERY cup with placed cups untouched, plus the cap-side
∗-dual, the `bottomCount = 0` class, and the `DiagramType` driver.  So `fxBrauer_hasStagedInnerDescentDischarged` STAYS
`false`, and `fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`,
`fxBrauer_hasBrauerV2FullCompleteness` all STAY `false`.  A route / measure gap, never a truth gap (Lehrer–Zhang
arXiv:1207.5889 Thm 2.6).  `= false`. -/
def fxBrauer_hasSingleCupPeelDischarged : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER cup-arrival-peel terminal state — MACHINE-CHECKED.**  The three new ingredient markers are `true`
(the arrival predicate, the general distant-tail peel, the straddle cleanup rung), built on the shipped r34
`fxBrauer_hasLocalLegFuelDescent` (the INNER measure), the r35 `fxBrauer_hasLegFuelPeelToArrival` (the peel step), and
the OUTER `fxBrauer_hasStagedArcCountFuel` (the handoff target), while the FULL single-cup peel and all three
completeness masters STAY `false`.  A `rfl`-conjunction the kernel checks; this round is purely additive, no master flip
is fabricated, #2013 does NOT close. -/
theorem fxBrauer_cupArrivalPeelTerminalState :
    fxBrauer_hasCupArrivalPredicate = true
      ∧ fxBrauer_hasDistantTailCupPeel = true
      ∧ fxBrauer_hasStraddleTerminalCleanup = true
      ∧ fxBrauer_hasLocalLegFuelDescent = true
      ∧ fxBrauer_hasLegFuelPeelToArrival = true
      ∧ fxBrauer_hasStagedArcCountFuel = true
      ∧ fxBrauer_hasSingleCupPeelDischarged = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph

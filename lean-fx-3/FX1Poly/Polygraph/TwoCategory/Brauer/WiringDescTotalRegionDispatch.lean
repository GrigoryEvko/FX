import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescRegionTransportKit

/-! # BRAUER r42 — the TOTAL region DISPATCH: one structural function threading ALL classifier arms to their
providers over the constructive single-cup scope (the r41-named ASSEMBLY, built)

r41 (`Brauer/WiringDescRegionTransportKit.lean`) discharged the last three dispatch residuals as bricks — the J-loop
engine lemma (`loopBubbleNotEmpty` / `outcomeLoopAtFactoredTotal`), the J-geometry ordered rewrite
(`sinkDistantThenStraddle_arrives`), and the J-transport reshape (`transportByRegionEq` / `transportCrossingHead`) — and
named the remaining piece as the ASSEMBLY: "a single structural `totalDispatch : (word) → InScope → RegionCupOutcome
word`" threading all 11 classifier arms plus the cupless-prefix whiskering.  The r39/r40 walls hedged the flat-word arm
reshape as a `propext` minefield (cons-index match + `▸`), and r40 named the honest sidestep: "the eager driver runs on
the TYPED DESCRIPTOR whose `distantTailWord` DECODES to the region definitionally, so no cons-index transport is needed;
the flat-region typed synthesis is the still-unbuilt piece."

This round BUILDS that assembly over the constructive scope.  `InScope` is realised as a `Type`-valued DESCRIPTOR
`SingleCupScope` — the seven reachable single-cup working-region shapes — whose `scopeWord` DECODES to the region
definitionally, so `totalDispatch : (scope) → RegionCupOutcome (scopeWord scope)` routes each constructor to its shipped
provider with NO cons-index reshape (the r40 sidestep, made the whole dispatch).  One new bridge unblocks the two
arrival arms that read the exact-slot certificate:

  * ★★ **`capFreeRight_of_regionArrivedExact`** — BRIDGE 1, the exact→cap-free bridge (`regionArrivedExact word = true →
    cupIsCapFreeRight word = true`): every atom right of the leftmost cup is a settled crossing (`allSettledLeftOfCup`),
    each has `outputCount = 2 ≠ 0`, so none is a cap (`hasNoCap`).  Structural on the suffix via the r41 `andEqTrue_*`
    `&&`-split + `Nat.eq_of_beq_eq_true` (no `Bool.and_eq_true` / `Nat.sub_*`, which leak `propext`).  It converts the
    `regionArrivedExact` certificate the r41 `sinkDistantThenStraddle_arrives` and the settled-`crossingLeft` shape
    deliver into the `cupIsCapFreeRight` the `RegionCupOutcome.arrivedFactored` fate demands.

  * ★ **`outcomeArrivedFactoredStraddleSink`** (arm `straddleTerminal`) and **`outcomeArrivedFactoredCrossingLeft`**
    (arm `crossingLeft`) — the two arrival providers BRIDGE 1 unblocks: the ordered straddle-then-distant sink to an
    exact-arrived region, and the settled-topPerm-crossing-right-of-cup terminal arrival.

  * ★★ **`SingleCupScope` / `scopeWord` / `totalDispatch`** — THE assembly.  Seven constructors covering every in-scope
    arm — `arrivedDistant` (the `cupArrivedAlone` / `distantCrossing` / `distantCap` family, all sunk by
    `legPeelDistantTail`), `untwistThenDistant` (`untwist`, via the r40 nested-structural `eagerPeelUntwistThenDistant`),
    `straddleThenDistant` (`straddleTerminal`), `crossingLeftSettled` (`crossingLeft`), `snakeLeft` / `snakeRight`
    (`snakeLeft` / `snakeRight`), `loopPair` (`loopHere`) — and `totalDispatch` routes each to its provider in one
    structural function.  `totalDispatch_fates` reads off arrived / annihilated / loop; `totalDispatch_classifierTie`
    ties each scope's word back to the classifier arm it represents (the assembly genuinely threads the classifier's
    decision); `totalDispatch_continueMeasureDescends` pins the leg-fuel drop on the folded continue arms.

  * ★ **`prependCuplessPrefixArrived` / `prependCuplessPrefixAnnihilated`** — the cupless-prefix whiskering the r41 wall
    named, for the two clean fates: whisker a settled cupless prefix onto an arrived / annihilated outcome
    (`suffixRightOfFirstCup_prefixCupless` keeps cap-freeness, `countAtoms_append` keeps the strict drop).
    `totalDispatchArrivedUnderPrefix` composes the prefix onto the arrived-distant provider.

## The honest wall — the DESCRIPTOR gates the synthesis; the three walls STAY false (the flat-word discharge is r43)

`totalDispatch` is the TOTAL typed synthesis over the constructive scope, but its input is the DESCRIPTOR
`SingleCupScope`, not an arbitrary flat word — `InScope` is a hypothesis.  Turning it into the walls'
"arbitrary flat region" synthesis needs the still-unbuilt flat→descriptor EXTRACTOR: from a flat word +
`classifyFirstCupNeighbour`'s decision, recover the typed `SingleCupScope` (the r40-named JAM D — extracting a
`List (DistantSlideStep cupPos)` from the flat tail with a decode-correctness proof), plus the reachability↔shape
argument that every reachable single-cup working region IS in scope.  Two residuals remain even inside the scope: the
`crossingLeft` NOT-exact geometry (a distant cap wedged behind the settled crossing — no terminal, needs a
commute-continue arm) and the loop-with-nonempty-suffix (the J-loop count varies with the suffix, so the loop fate takes
only the bare pair and the cupless-prefix whisker covers only the arrived / annihilated fates).  So
`fxBrauer_hasRegionDriverTotalDispatch`, `fxBrauer_hasSingleCupTotalDecision`, and `fxBrauer_hasSingleCupPeelDischarged`
all STAY `false` — the last is a MULTI-CUP wall (the outer `arcCountFuel` fold over EVERY cup + the cap-side ∗-dual +
the `DiagramType` driver), not co-flippable with a single-cup dispatch — and the five completeness / inner-descent
masters (`fxBrauer_hasSeamRungOuterAssembly`, `fxBrauer_hasStagedInnerDescentDischarged`,
`fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness`) all
STAY `false`; this round is PURELY ADDITIVE, no master flip is fabricated.  Every residual is a route / extractor gap,
never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6 — the seven relations are complete; Delpeuch–Vicary
arXiv:1804.07832 Thm 10 — the interchange sub-phase is strongly normalizing under the inversion measure the leg fuel
instances).

Raw Lean 4 + Init; the assembly is STRUCTURAL on the descriptor, each continue arm folding into the r40/r41
nested-structural providers (`peelUntwistRunFactored` outer on the `Nat` untwist count, `legPeelDistantTail` inner on the
distant-tail descriptor — NO `termination_by`), and BRIDGE 1 is structural on the suffix (no `omega` / `simp`-AC /
`native_decide` / `WellFounded.fix` / `propext` — `Bool.and_eq_true`, `Nat.beq_refl`, `Nat.succ_ne_zero`,
`List.append_assoc`, `Nat.sub_*` all leak `propext`, so the r41 `andEqTrue_*` split, `Nat.eq_of_beq_eq_true`,
`countAtoms`, and `Nat.noConfusion` are used instead).  Per-declaration `#assert_no_axioms` in the audit twin, and an
independent `#print axioms` witness file. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — BRIDGE 1: the exact-slot certificate implies cap-freeness (the arrival-arm enabler) -/

/-- A crossing atom has `outputCount = 2`.  Extracted from `isCrossingAtom atom = true` by the r41 `andEqTrue_*`
`&&`-split + `Nat.eq_of_beq_eq_true` (the same conjunct path `crossingWiring_reconstruct` reads for `outputTwo`). -/
theorem outputCount_two_of_isCrossing (atom : BrauerAtom) (isCross : isCrossingAtom atom = true) :
    atom.wiring.outputCount = 2 :=
  Nat.eq_of_beq_eq_true (andEqTrue_right (andEqTrue_left (andEqTrue_left isCross)))

/-- ★ **A suffix of settled topPerm crossings has NO cap.**  If every atom is a crossing to the left of the cup
(`allSettledLeftOfCup`), then each has `outputCount = 2 ≠ 0`, so `hasNoCap` reads `true`.  Structural on the suffix, the
head split by the r41 `andEqTrue_left` / `andEqTrue_right` (`Bool.and_eq_true` leaks `propext`). -/
theorem hasNoCap_of_allSettledLeftOfCup (cupPos : Nat) :
    (suffixWord : List BrauerAtom) → allSettledLeftOfCup cupPos suffixWord = true → hasNoCap suffixWord = true
  | [], _ => rfl
  | atom :: rest, settled => by
      have headSettled : (isCrossingAtom atom && Nat.blt atom.position cupPos) = true := andEqTrue_left settled
      have tailSettled : allSettledLeftOfCup cupPos rest = true := andEqTrue_right settled
      have isCross : isCrossingAtom atom = true := andEqTrue_left headSettled
      have outTwo : atom.wiring.outputCount = 2 := outputCount_two_of_isCrossing atom isCross
      show cond (Nat.beq atom.wiring.outputCount 0) false (hasNoCap rest) = true
      rw [outTwo]
      show hasNoCap rest = true
      exact hasNoCap_of_allSettledLeftOfCup cupPos rest tailSettled

/-- ★★ **BRIDGE 1 — the exact-slot certificate implies the factored cap-free predicate.**  `regionArrivedExact word =
true` (every atom right of the leftmost cup is a settled topPerm crossing) implies `cupIsCapFreeRight word = true` (no
cap right of the leftmost cup): the settled crossings carry no cap.  This converts the `regionArrivedExact` witness the
r41 `sinkDistantThenStraddle_arrives` / the settled-`crossingLeft` shape deliver into the `cupIsCapFreeRight` the
`RegionCupOutcome.arrivedFactored` fate requires — the missing arrival-arm bridge. -/
theorem capFreeRight_of_regionArrivedExact (word : List BrauerAtom)
    (exact : regionArrivedExact word = true) : cupIsCapFreeRight word = true := by
  show hasNoCap (suffixRightOfFirstCup word) = true
  exact hasNoCap_of_allSettledLeftOfCup (firstCupPosition word) (suffixRightOfFirstCup word) exact

/-! ## B — the two BRIDGE-1-gated arrival providers (arms `straddleTerminal` and `crossingLeft`) -/

/-- ★ **The straddle-then-distant arrival provider** (arm `straddleTerminal`).  The r41 ordered rewrite
`sinkDistantThenStraddle_arrives` reduces `cupAt cupPos :: crossingAt (cupPos + 1) :: distantTailWord tail` to an
exact-arrived region and certifies `regionArrivedExact = true`; BRIDGE 1 turns that into the `cupIsCapFreeRight` the
`.arrivedFactored` fate needs, so the whole straddle arm is a genuine `RegionCupOutcome`, GENERIC in `cupPos` and the
distant tail. -/
def outcomeArrivedFactoredStraddleSink (cupPos : Nat) (tail : List (DistantSlideStep (cupPos + 1))) :
    RegionCupOutcome (cupAt cupPos :: crossingAt (cupPos + 1) :: distantTailWord tail) :=
  RegionCupOutcome.arrivedFactored ((legPeelDistantTail (cupPos + 1) tail).1 ++ [crossingAt cupPos])
    (sinkDistantThenStraddle_arrives cupPos tail).1
    (capFreeRight_of_regionArrivedExact _ (sinkDistantThenStraddle_arrives cupPos tail).2)

/-- The settled-crossing-right-of-cup shape is exact-arrived, GENERIC in `cupPos`.  With a crossing at `xpos < cupPos`
(a settled topPerm) as the sole atom right of the cup, `regionArrivedExact` reads `true` (mirrors the r41
`regionArrivedExact_straddle`). -/
theorem regionArrivedExact_settledCrossingRight (cupPos xpos : Nat) (settledLeft : Nat.blt xpos cupPos = true) :
    regionArrivedExact [cupAt cupPos, crossingAt xpos] = true := by
  show (isCrossingAtom (crossingAt xpos) && Nat.blt xpos cupPos) && true = true
  rw [settledLeft]; rfl

/-- ★ **The settled-`crossingLeft` arrival provider** (arm `crossingLeft`).  A cup already at its slot with one settled
topPerm crossing (`xpos < cupPos`) to its right is terminally arrived (a reflexive conversion), the `cupIsCapFreeRight`
supplied by BRIDGE 1 over `regionArrivedExact_settledCrossingRight`.  The `crossingLeft` arm the r40 dispatch gated on
the exact certificate, built as a typed outcome. -/
def outcomeArrivedFactoredCrossingLeft (cupPos xpos : Nat) (settledLeft : Nat.blt xpos cupPos = true) :
    RegionCupOutcome [cupAt cupPos, crossingAt xpos] :=
  RegionCupOutcome.arrivedFactored [cupAt cupPos, crossingAt xpos]
    (BrauerConvFree8.ofFree7 (BrauerConvFree7.ofFree (BrauerConvFree.refl [cupAt cupPos, crossingAt xpos])))
    (capFreeRight_of_regionArrivedExact _ (regionArrivedExact_settledCrossingRight cupPos xpos settledLeft))

/-! ## C — the constructive single-cup scope + its word + the TOTAL dispatch -/

/-- ★★ **The constructive single-cup working-region SCOPE** — `InScope` as a `Type`-valued descriptor.  Its seven
constructors are exactly the in-scope classifier arms, each carrying the typed data (a distant-tail descriptor, an
untwist count, a settledness proof) from which the region decodes definitionally — so the dispatch needs no cons-index
reshape.  Absent by construction: `noCup` (no leftmost cup) and `anotherCup` (an adjacent second cup) — the two
out-of-scope arms `eagerDispatchStep` routes to `outOfScope`. -/
inductive SingleCupScope : Type
  /-- The `cupArrivedAlone` / `distantCrossing` / `distantCap` family — a cup at `cupPos` behind a distant tail. -/
  | arrivedDistant (cupPos : Nat) (tail : List (DistantSlideStep cupPos)) : SingleCupScope
  /-- The `untwist` arm — a cup behind a run of `untwistCount` crossings-on-its-own-legs, then a distant tail. -/
  | untwistThenDistant (cupPos untwistCount : Nat) (tail : List (DistantSlideStep cupPos)) : SingleCupScope
  /-- The `straddleTerminal` arm — a cup with an adjacent straddle crossing at `cupPos + 1`, then a distant tail. -/
  | straddleThenDistant (cupPos : Nat) (tail : List (DistantSlideStep (cupPos + 1))) : SingleCupScope
  /-- The `crossingLeft` arm — a cup already at its slot with one settled topPerm crossing `xpos < cupPos` right of it. -/
  | crossingLeftSettled (cupPos xpos : Nat) (settledLeft : Nat.blt xpos cupPos = true) : SingleCupScope
  /-- The `snakeLeft` arm — `cupAt (cupPos + 1)`, an adjacent cap at `cupPos`, then a suffix. -/
  | snakeLeft (cupPos : Nat) (suffixWord : List BrauerAtom) : SingleCupScope
  /-- The `snakeRight` arm — `cupAt cupPos`, an adjacent cap at `cupPos + 1`, then a suffix. -/
  | snakeRight (cupPos : Nat) (suffixWord : List BrauerAtom) : SingleCupScope
  /-- The `loopHere` arm — the bare loop pair `[cupAt cupPos, capAt cupPos]` (bottomCount 0, loops 1). -/
  | loopPair (cupPos : Nat) : SingleCupScope

/-- The flat word a scope decodes to — definitionally the region each provider consumes (the r40 sidestep). -/
def scopeWord : SingleCupScope → List BrauerAtom
  | .arrivedDistant cupPos tail => cupAt cupPos :: distantTailWord tail
  | .untwistThenDistant cupPos untwistCount tail =>
      cupAt cupPos :: (List.replicate untwistCount (crossingAt cupPos) ++ distantTailWord tail)
  | .straddleThenDistant cupPos tail => cupAt cupPos :: crossingAt (cupPos + 1) :: distantTailWord tail
  | .crossingLeftSettled cupPos xpos _ => [cupAt cupPos, crossingAt xpos]
  | .snakeLeft cupPos suffixWord => cupAt (cupPos + 1) :: capAt cupPos :: suffixWord
  | .snakeRight cupPos suffixWord => cupAt cupPos :: capAt (cupPos + 1) :: suffixWord
  | .loopPair cupPos => [cupAt cupPos, capAt cupPos]

/-- ★★ **THE TOTAL region DISPATCH.**  One structural function turning a single-cup scope into its typed
`RegionCupOutcome` by routing each constructor to its shipped provider — the r41-named ASSEMBLY, built.  The arrival
family folds into `legPeelDistantTail` / `eagerPeelUntwistThenDistant`; the straddle / `crossingLeft` arms into the two
BRIDGE-1-gated providers; the snakes into `outcomeAnnihilatedFactored*`; the loop into the r41 total
`outcomeLoopAtFactoredTotal`.  No cons-index reshape: each `scopeWord` decodes definitionally to its provider's region.
Structural on the descriptor, each continue arm folding into a nested-structural provider. -/
def totalDispatch : (scope : SingleCupScope) → RegionCupOutcome (scopeWord scope)
  | .arrivedDistant cupPos tail => outcomeArrivedFactoredOfDistantTail cupPos tail
  | .untwistThenDistant cupPos untwistCount tail => eagerPeelUntwistThenDistant cupPos untwistCount tail
  | .straddleThenDistant cupPos tail => outcomeArrivedFactoredStraddleSink cupPos tail
  | .crossingLeftSettled cupPos xpos settledLeft => outcomeArrivedFactoredCrossingLeft cupPos xpos settledLeft
  | .snakeLeft cupPos suffixWord => outcomeAnnihilatedFactoredS1 cupPos suffixWord
  | .snakeRight cupPos suffixWord => outcomeAnnihilatedFactoredS2 cupPos suffixWord
  | .loopPair cupPos => outcomeLoopAtFactoredTotal cupPos

/-! ## D — the fates, the classifier tie, and the folded continue-arm measure -/

/-- ★★ **Every dispatched arm's fate, machine-checked by `rfl`.**  Arrival on the arrived / untwist / straddle /
`crossingLeft` families, annihilation on the two snakes, loop on the bubble — the total dispatch's fate assignment across
all seven in-scope arms, at fresh positions. -/
theorem totalDispatch_fates :
    (totalDispatch (.arrivedDistant 0 [])).fate = SingleCupFate.arrivedFate
      ∧ (totalDispatch (.arrivedDistant 3 [.crossing 4 (by decide), .cap 5 (by decide)])).fate = SingleCupFate.arrivedFate
      ∧ (totalDispatch (.untwistThenDistant 0 2 [.crossing 1 (by decide), .cap 2 (by decide)])).fate = SingleCupFate.arrivedFate
      ∧ (totalDispatch (.straddleThenDistant 0 [.crossing 1 (by decide), .cap 3 (by decide)])).fate = SingleCupFate.arrivedFate
      ∧ (totalDispatch (.crossingLeftSettled 1 0 (by decide))).fate = SingleCupFate.arrivedFate
      ∧ (totalDispatch (.snakeLeft 0 [crossingAt 8])).fate = SingleCupFate.annihilatedFate
      ∧ (totalDispatch (.snakeRight 0 [])).fate = SingleCupFate.annihilatedFate
      ∧ (totalDispatch (.loopPair 5)).fate = SingleCupFate.loopFate :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★★ **Each scope's word classifies to the arm it represents.**  Running `classifyFirstCupNeighbour` on the decoded
word recovers the move kind the scope constructor stands for — the assembly genuinely threads the classifier's decision,
covering every in-scope arm plus the two out-of-scope boundaries (`noCup` / `anotherCup`, unrepresentable by the
descriptor).  Literal-witness `rfl`s (closed `Nat.beq`, no `brauerDiagramOf`). -/
theorem totalDispatch_classifierTie :
    classifyFirstCupNeighbour (scopeWord (.arrivedDistant 0 [])) = RegionCupMoveKind.cupArrivedAlone
      ∧ classifyFirstCupNeighbour (scopeWord (.arrivedDistant 0 [.crossing 3 (by decide)])) = RegionCupMoveKind.distantCrossing
      ∧ classifyFirstCupNeighbour (scopeWord (.arrivedDistant 0 [.cap 3 (by decide)])) = RegionCupMoveKind.distantCap
      ∧ classifyFirstCupNeighbour (scopeWord (.untwistThenDistant 2 1 [])) = RegionCupMoveKind.untwist
      ∧ classifyFirstCupNeighbour (scopeWord (.straddleThenDistant 0 [.crossing 1 (by decide)])) = RegionCupMoveKind.straddleTerminal
      ∧ classifyFirstCupNeighbour (scopeWord (.crossingLeftSettled 1 0 (by decide))) = RegionCupMoveKind.crossingLeft
      ∧ classifyFirstCupNeighbour (scopeWord (.snakeLeft 0 [crossingAt 8])) = RegionCupMoveKind.snakeLeft
      ∧ classifyFirstCupNeighbour (scopeWord (.snakeRight 0 [])) = RegionCupMoveKind.snakeRight
      ∧ classifyFirstCupNeighbour (scopeWord (.loopPair 0)) = RegionCupMoveKind.loopHere
      ∧ classifyFirstCupNeighbour ([] : List BrauerAtom) = RegionCupMoveKind.noCup
      ∧ classifyFirstCupNeighbour [cupAt 0, cupAt 2] = RegionCupMoveKind.anotherCup :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★ **The folded continue arms strictly descend the leg fuel** (radix 2).  The untwist step removes the
crossing-on-its-own-legs (primary distance `−1`, `legLexFuel 2` `6 → 4`) and the distant-crossing slide sinks the cup one
place (primary `−1`, `4 → 2`) — the exact drops the r34 `legFuel_leftmostCup*_lt` establish generically and the r40
`peelUntwistRunFactored` / r36 `legPeelDistantTail` fold into; pinned here on the recon trace-b representative. -/
theorem totalDispatch_continueMeasureDescends :
    legLexFuel 2 [cupAt 2, crossingAt 5, capAt 6] < legLexFuel 2 [cupAt 2, crossingAt 2, crossingAt 5, capAt 6]
      ∧ legLexFuel 2 [crossingAt 3, cupAt 2, capAt 6] < legLexFuel 2 [cupAt 2, crossingAt 5, capAt 6] :=
  ⟨by decide, by decide⟩

/-! ## E — the cupless-prefix whiskering (the r41-named brick, for the two clean fates) -/

/-- ★ **The suffix right of the leftmost cup is transparent to a cupless prefix.**  When `prefixWord` has no cup,
`suffixRightOfFirstCup (prefixWord ++ rest) = suffixRightOfFirstCup rest`: the prefix is skipped to the first cup, which
lies in `rest`.  Structural on `prefixWord` via the r36 `isCupAtom_false_of_hasNoCup_cons` / `hasNoCup_cons_tail` (no
`List.append_assoc`). -/
theorem suffixRightOfFirstCup_prefixCupless :
    (prefixWord : List BrauerAtom) → (rest : List BrauerAtom) → hasNoCup prefixWord = true →
    suffixRightOfFirstCup (prefixWord ++ rest) = suffixRightOfFirstCup rest
  | [], _, _ => rfl
  | atom :: restPrefix, rest, cupless => by
      have hHead : isCupAtom atom = false := isCupAtom_false_of_hasNoCup_cons cupless
      show cond (isCupAtom atom) (restPrefix ++ rest)
            (suffixRightOfFirstCup (restPrefix ++ rest)) = suffixRightOfFirstCup rest
      rw [hHead]
      exact suffixRightOfFirstCup_prefixCupless restPrefix rest (hasNoCup_cons_tail cupless)

/-- Cap-freeness right of the cup is preserved by a cupless prefix. -/
theorem cupIsCapFreeRight_prefixCupless (prefixWord rest : List BrauerAtom)
    (cupless : hasNoCup prefixWord = true) :
    cupIsCapFreeRight (prefixWord ++ rest) = cupIsCapFreeRight rest := by
  show hasNoCap (suffixRightOfFirstCup (prefixWord ++ rest)) = hasNoCap (suffixRightOfFirstCup rest)
  rw [suffixRightOfFirstCup_prefixCupless prefixWord rest cupless]

/-- ★ **Whisker a settled cupless prefix onto an ARRIVED outcome.**  A cupless prefix (placed / settled atoms untouched
by the sink) whiskers onto an arrived conversion by `whiskerLeft`, the cap-free predicate preserved
(`cupIsCapFreeRight_prefixCupless`).  The arrived half of the r41-named `prependCuplessPrefix`. -/
def prependCuplessPrefixArrived (prefixWord region result : List BrauerAtom)
    (cupless : hasNoCup prefixWord = true)
    (conv : BrauerConvFree8 region result) (capFreeRight : cupIsCapFreeRight result = true) :
    RegionCupOutcome (prefixWord ++ region) :=
  RegionCupOutcome.arrivedFactored (prefixWord ++ result)
    (BrauerConvFree8.whiskerLeft prefixWord conv)
    (by rw [cupIsCapFreeRight_prefixCupless prefixWord result cupless]; exact capFreeRight)

/-- ★ **Whisker any prefix onto an ANNIHILATED outcome.**  The strict `countAtoms` drop survives any prefix
(`countAtoms_append` splits the sum, `Nat.add_lt_add_left` keeps the strict inequality) — no cuplessness needed. -/
def prependCuplessPrefixAnnihilated (prefixWord region result : List BrauerAtom)
    (conv : BrauerConvFree8 region result) (shrank : countAtoms result < countAtoms region) :
    RegionCupOutcome (prefixWord ++ region) :=
  RegionCupOutcome.annihilated (prefixWord ++ result)
    (BrauerConvFree8.whiskerLeft prefixWord conv)
    (by rw [countAtoms_append prefixWord result, countAtoms_append prefixWord region]
        exact Nat.add_lt_add_left shrank (countAtoms prefixWord))

/-- ★ **The arrived-distant dispatch UNDER a cupless prefix.**  Composes the prefix whisker onto the arrived-distant
provider — a cup behind a settled cupless prefix and a distant tail sinks to an arrived outcome over the whole prefixed
region.  Demonstrates the prefix brick threading the dispatch for the arrived fate. -/
def totalDispatchArrivedUnderPrefix (prefixWord : List BrauerAtom) (cupPos : Nat)
    (tail : List (DistantSlideStep cupPos)) (cupless : hasNoCup prefixWord = true) :
    RegionCupOutcome (prefixWord ++ (cupAt cupPos :: distantTailWord tail)) :=
  let peeled := legPeelDistantTail cupPos tail
  prependCuplessPrefixArrived prefixWord (cupAt cupPos :: distantTailWord tail) peeled.1
    cupless peeled.2.1 (capFreeRight_of_arrived peeled.1 peeled.2.2)

/-- ★ **The prefixed arrived dispatch arrives, machine-checked** — a settled `crossingAt 0` prefix in front of a
cup-plus-distant-crossing sinks to `.arrivedFate`. -/
theorem totalDispatchArrivedUnderPrefix_fate :
    (totalDispatchArrivedUnderPrefix [crossingAt 0] 0 [.crossing 1 (by decide)] (by decide)).fate
      = SingleCupFate.arrivedFate := rfl

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the TOTAL region DISPATCH ASSEMBLY SHIPS (the r41-named assembly, built).**  `totalDispatch`
is one structural function turning a constructive single-cup scope (`SingleCupScope`, `InScope` as a `Type`-valued
descriptor) into its typed `RegionCupOutcome`, routing all seven in-scope classifier arms to their shipped providers with
no cons-index reshape (the r40 typed-descriptor sidestep, made the whole dispatch).  BRIDGE 1
(`capFreeRight_of_regionArrivedExact`) unblocks the two arrival arms reading the exact certificate
(`outcomeArrivedFactoredStraddleSink` / `outcomeArrivedFactoredCrossingLeft`); `totalDispatch_fates` /
`totalDispatch_classifierTie` pin the fates and the classifier threading; `totalDispatch_continueMeasureDescends` pins
the folded continue-arm leg-fuel drop; `prependCuplessPrefixArrived` / `prependCuplessPrefixAnnihilated` whisker a
cupless prefix onto the two clean fates (`totalDispatchArrivedUnderPrefix`).  `= true`. -/
def fxBrauer_hasTotalRegionDispatchAssembly : Bool := true

/-- **Honesty WALL marker — the FLAT-word synthesis is NOT built; the three dispatch walls STAY `false`.**  `totalDispatch`
consumes the DESCRIPTOR `SingleCupScope`, not an arbitrary flat word — `InScope` is a hypothesis.  The walls' "arbitrary
flat region" synthesis needs the still-unbuilt flat→descriptor EXTRACTOR (the r40 JAM D: recover a typed
`List (DistantSlideStep cupPos)` from a flat tail with a decode-correctness proof) + the reachability↔shape argument that
every reachable single-cup working region is in scope; two in-scope residuals also remain (the `crossingLeft` NOT-exact
commute-continue geometry, and the loop-with-nonempty-suffix whose count varies).  So `fxBrauer_hasRegionDriverTotalDispatch`,
`fxBrauer_hasSingleCupTotalDecision`, and `fxBrauer_hasSingleCupPeelDischarged` STAY `false` (the last a MULTI-CUP wall —
the outer `arcCountFuel` fold over EVERY cup + the cap-side ∗-dual + the `DiagramType` driver — not co-flippable with a
single-cup dispatch), and the five completeness / inner-descent masters STAY `false`.  A route / extractor gap, never a
truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).  `= false`. -/
def fxBrauer_hasFlatRegionDispatchSynthesis : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r42 total-region-dispatch terminal state — MACHINE-CHECKED.**  The two new markers record the honest
split: the assembly SHIPS (`fxBrauer_hasTotalRegionDispatchAssembly = true`) over the constructive scope, built on the
r41 J-loop / J-geometry / J-transport bricks and the r39/r40 factored cup arrival / region classifier / eager dispatch,
while the flat-word synthesis stays unbuilt (`fxBrauer_hasFlatRegionDispatchSynthesis = false`) — so the three dispatch
walls (`fxBrauer_hasRegionDriverTotalDispatch`, `fxBrauer_hasSingleCupTotalDecision`,
`fxBrauer_hasSingleCupPeelDischarged`) and the five completeness / inner-descent masters
(`fxBrauer_hasSeamRungOuterAssembly`, `fxBrauer_hasStagedInnerDescentDischarged`, `fxBrauer_hasFreeBrauerStraighteningNF`,
`fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness`) all STAY `false`.  A `rfl`-conjunction the
kernel checks; purely additive, no master flip is fabricated. -/
theorem fxBrauer_totalRegionDispatchTerminalState :
    fxBrauer_hasTotalRegionDispatchAssembly = true
      ∧ fxBrauer_hasRegionOutcomeTransportKit = true
      ∧ fxBrauer_hasStraddleSinkOrdered = true
      ∧ fxBrauer_hasLoopBubbleEngineLemma = true
      ∧ fxBrauer_hasEagerRegionDispatch = true
      ∧ fxBrauer_hasFlatRegionDispatchSynthesis = false
      ∧ fxBrauer_hasRegionDriverTotalDispatch = false
      ∧ fxBrauer_hasSingleCupTotalDecision = false
      ∧ fxBrauer_hasSingleCupPeelDischarged = false
      ∧ fxBrauer_hasSeamRungOuterAssembly = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph

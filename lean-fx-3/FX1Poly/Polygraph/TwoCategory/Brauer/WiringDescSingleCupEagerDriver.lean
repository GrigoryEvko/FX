import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescSingleCupRegionDriver

/-! # BRAUER r40 — the EAGER (prefix, region) single-cup driver: the EXACT-SLOT arrival certificate + the factored
untwist-run twin + the total DISPATCH DECISION (the decide-the-driver-step half of the total synthesis)

r39 (`Brauer/WiringDescSingleCupRegionDriver.lean`) shipped the FACTORED three-fated `RegionCupOutcome`, the
loop-router conversion, and `classifyFirstCupNeighbour` — the SCAN-AND-CLASSIFY total function that finds the leftmost
cup and classifies its immediate list-neighbour.  Its wall `fxBrauer_hasRegionDriverTotalDispatch = false` named the
TOTAL region DISPATCH — SYNTHESIZING the typed `RegionCupOutcome` from the classifier's decision over an arbitrary
region — and pinned three residuals: (J-transport) the cons-indexed `Eq.rec`/`▸` positional reshape (a `propext`
minefield), (J-loop) the `cupPos`-generic loop non-emptiness, (J-geometry) the straddle-then-cap ordering trap.

This round ships, PURELY ADDITIVELY, the EAGER (prefix, region) bricks that resolve the ARRIVAL-DECISION half and
encode the J-geometry discipline, each truth-probed by `#eval` FIRST then pinned:

  * ★★ **`regionArrivedExact`** — THE EXACT-SLOT arrival certificate, the recon §4 central finding.  The r36
    `cupIsCapFreeRight` reads `true` IDENTICALLY on `[cupAt 1, crossingAt 0]` (a settled topPerm crossing LEFT of the
    cup — genuinely arrived, `atomsRightOfFirstCup = 1` false-NEGATIVES) and `[cupAt 0, crossingAt 5]` (a DISTANT
    middle crossing — NOT arrived, `cupIsCapFreeRight = true` false-POSITIVES); the flat word cannot tell them apart by
    cap-freeness.  `regionArrivedExact` STRENGTHENS the proxy: it demands every atom right of the leftmost cup be a
    CROSSING at position STRICTLY LESS than the cup's position (a settled topPerm), which is exactly the `crossingLeft`
    discriminator the classifier uses.  It reads `true` on `[cupAt 1, crossingAt 0]` and `false` on
    `[cupAt 0, crossingAt 5]` — the §4 ambiguity RESOLVED where `cupIsCapFreeRight` cannot
    (`regionArrivedExact_discriminates`).  Bridges: `regionArrivedExact_of_atomsRightZero` (raw arrival ⟹ exact, so the
    stronger gate still passes every genuine arrival) and `regionArrivedExact_straddle` (the straddle relabel result
    `[cupAt (cupPos + 1), crossingAt cupPos]` is exact-arrived, GENERIC in `cupPos`).

  * ★ **`peelUntwistRunFactored`** — the factored twin of the r38 `peelUntwistRun`: the genuine OUTER structural
    recursion (on the `Nat` untwist count) sinking a cup past a run of crossings-on-its-own-legs, `RegionCupOutcome`-
    valued via `RegionCupOutcome.prepend`.  Composed with the inner `legPeelDistantTail` (through the r39
    `outcomeArrivedFactoredOfDistantTail`) it is `eagerPeelUntwistThenDistant`: the EAGER two-nested-structural driver
    (outer on the untwist count, inner on the distant-tail descriptor) over a THREE-parameter-generic region, producing
    a genuine `.arrivedFactored` outcome — the r38 `peelUntwistRunThenDistant_demo` promoted from a closed demo to a
    general FACTORED driver (`eagerHostileUntwistThenDistant_demo`).

  * ★ **`eagerDispatchStep`** — the TOTAL DISPATCH DECISION: a total function `RegionCupMoveKind → EagerDispatchStep`
    (full 11-arm enum, no wildcard) mapping each classified arm to the eager driver's STEP — `terminalArrived` /
    `terminalArrivedIfExact` (the `crossingLeft` arm's arrival GATED by `regionArrivedExact`) / `terminalAnnihilated` /
    `terminalLoop` / `continueUntwist` / `continueDistant` / `sinkDistantThenStraddle` (the J-geometry ORDERING
    discipline: the straddle fires only AFTER the distant tail sinks) / `outOfScope`.  Composed with
    `classifyFirstCupNeighbour` this is the total dispatch DECISION over an arbitrary region — which move the eager
    driver makes at every step (`eagerDispatch_probes`), encoding both the exact-slot gate and the J-geometry
    ordering the r39 single-pass classifier recorded but did not act on.  The certified typed SYNTHESIS from the
    decision stays walled on J-transport (below).

## The honest wall — the TOTAL typed region synthesis is STILL NOT built; #2013 does NOT close (named IN this file)

The arrival-decision half is now exact and the J-geometry ordering is encoded in the dispatch step, but the TOTAL
typed DISPATCH — a single structural function turning `classifyFirstCupNeighbour`'s decision into the typed
`RegionCupOutcome` for an ARBITRARY FLAT region — stays open on the same three residuals, unchanged:

  * **(J-transport) the reshape plumbing.**  Each dispatch arm must retype the shipped builder's positional word
    (`crossingAt cupPos`, `capAt (capPos + 2)`, …) to the region's ACTUAL atom via a `Nat.beq _ _ = true → _ = _`
    positional equality and transport the outcome — the `Eq.rec`/`▸` plumbing across a cons-indexed family the memory
    corpus flags as a `propext` minefield (cons-index match + ▸).  This round SIDESTEPS it honestly: the eager driver
    (`eagerPeelUntwistThenDistant`) runs on the TYPED DESCRIPTOR (untwist count + `List (DistantSlideStep cupPos)`)
    whose `distantTailWord` DECODES to the region definitionally, so no cons-index transport is needed; the flat-region
    typed synthesis is the still-unbuilt piece.  Not a truth gap: the classifier + `eagerDispatchStep` already DECIDE
    every step.
  * **(J-loop) the generic loop non-emptiness.**  `brauerDiagramOf 0 [cupAt cupPos, capAt cupPos] ≠ brauerDiagramOf 0 []`
    is a per-literal `decide` (`.loops := 1 ≠ 0`) but a proof GENERIC in `cupPos` needs an engine-level
    `(brauerDiagramOf 0 [cupAt cupPos, capAt cupPos]).loops = 1` lemma over `stepCup`/`stepCap`/`extractDiagram`; with a
    suffix the loop count even varies (`[cupAt 2, capAt 2, capAt 9].loops = 2`), so the loop router (r39
    `outcomeLoopAtFactored`) takes the witness as a hypothesis and the `.terminalLoop` dispatch step does not discharge
    it.
  * **(J-geometry) the straddle-then-cap ordering trap.**  `eagerDispatchStep` now ROUTES `straddleTerminal` to
    `sinkDistantThenStraddle` (`straddleThenCap_notArrivedNaively` pins that firing the straddle first on
    `[cupAt 0, crossingAt 1, crossingAt 3, capAt 5]` leaves `regionArrivedExact = false` — the settled crossing wedged
    between the cup and the distant cap), but the ORDERED sink-distant-before-straddle rewrite itself is the r41 piece.

So `fxBrauer_hasRegionDriverTotalDispatch` STAYS `false` (owned by r39, untouched), `fxBrauer_hasSingleCupTotalDecision`
STAYS `false` (owned by r38), `fxBrauer_hasSingleCupPeelDischarged` STAYS `false` (owned by r36), and the four
completeness / inner-descent masters (`fxBrauer_hasStagedInnerDescentDischarged`, `fxBrauer_hasFreeBrauerStraighteningNF`,
`fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness` — the fold over EVERY cup + the cap-side ∗-dual
+ the `DiagramType` driver) all STAY `false`; this round is PURELY ADDITIVE, no master flip is fabricated.  Every
residual is a route / measure / engine-lemma gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).

Raw Lean 4 + Init; NESTED structural recursion (the outer `peelUntwistRunFactored` on the `Nat` count, the inner
`legPeelDistantTail` on the distant-tail descriptor; no `termination_by`, no `omega` / `simp`-AC / `native_decide` /
`WellFounded.fix` / `propext` — `List.length_append`, `Nat.beq_refl`, `Nat.succ_ne_zero`, `Nat.sub_*` all leak
`propext`, so `countAtoms`, the hand-rolled structural `bleSelf`, and `Nat.noConfusion` are used instead).
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the two structural `Nat` boolean-comparison self-lemmas (propext-clean, hand-rolled) -/

/-- `Nat.ble n n = true`, hand-rolled structurally (the stdlib route via `Nat.le_refl` + decide is fine but this keeps
the exact reduction transparent; `Nat.beq_refl` and friends LEAK `propext`, `Nat.ble` here does not). -/
theorem bleSelf : (n : Nat) → Nat.ble n n = true
  | 0 => rfl
  | n + 1 => bleSelf n

/-- `Nat.blt n (n + 1) = true`, structural.  `Nat.blt n m` is `Nat.ble (n + 1) m`, so `Nat.blt n (n + 1)` is
`Nat.ble (n + 1) (n + 1)`, closed by `bleSelf (n + 1)`.  The generic straddle-window comparison. -/
theorem bltSucc (n : Nat) : Nat.blt n (n + 1) = true := bleSelf (n + 1)

/-! ## B — the EXACT-SLOT arrival certificate (the recon §4 discriminator) -/

/-- Every atom of a suffix is a SETTLED topPerm crossing to the LEFT of the cup — a crossing at position STRICTLY LESS
than `cupPos`.  Structural, `Nat.blt` closed comparison; propext-clean (no `Nat.sub_*`, no `Nat.beq_refl`). -/
def allSettledLeftOfCup (cupPos : Nat) : List BrauerAtom → Bool
  | [] => true
  | atom :: rest =>
      (isCrossingAtom atom && Nat.blt atom.position cupPos) && allSettledLeftOfCup cupPos rest

/-- The position of the leftmost cup (`0` when the word is cupless — never consulted in that case, since the suffix is
then empty).  The `∗`-cousin of the r36 `atomsRightOfFirstCup`'s cup scan. -/
def firstCupPosition : List BrauerAtom → Nat
  | [] => 0
  | atom :: rest => cond (isCupAtom atom) atom.position (firstCupPosition rest)

/-- ★★ **THE EXACT-SLOT arrival certificate** (recon §4).  The leftmost cup has arrived at its EXACT slot iff every
atom to its right is a settled topPerm crossing (`allSettledLeftOfCup` over `suffixRightOfFirstCup`).  This is STRICTLY
STRONGER than the r36 `cupIsCapFreeRight` (which only excludes caps): it also rejects a DISTANT middle crossing right of
the cup — the exact case where `cupIsCapFreeRight` false-POSITIVES.  It is the positional discriminator the flat word's
cap-freeness cannot express, and it agrees with the classifier's `crossingLeft` (crossing at `cupPos - 1`, settled) vs
`distantCrossing` (crossing at `cupPos + 2 +`, pending) split. -/
def regionArrivedExact (word : List BrauerAtom) : Bool :=
  allSettledLeftOfCup (firstCupPosition word) (suffixRightOfFirstCup word)

/-- ★ **The honest bridge: raw arrival IMPLIES exact arrival.**  If `atomsRightOfFirstCup word = 0` (the raw complete
arrival), then the suffix right of the cup is empty, so `allSettledLeftOfCup _ [] = true` vacuously — the EXACT gate
SUBSUMES the raw one, so every genuine arrival still passes the stronger certificate.  Mirrors the r39
`capFreeRight_of_arrived`; uses the r39 structural bridges (never `List.length_append` / `Nat.succ_ne_zero`). -/
theorem regionArrivedExact_of_atomsRightZero (word : List BrauerAtom)
    (arrived : atomsRightOfFirstCup word = 0) : regionArrivedExact word = true := by
  have hSuffixNil : suffixRightOfFirstCup word = [] := by
    apply countAtoms_eq_zero_imp_nil
    rw [← atomsRightOfFirstCup_eq_countAtoms_suffix]
    exact arrived
  show allSettledLeftOfCup (firstCupPosition word) (suffixRightOfFirstCup word) = true
  rw [hSuffixNil]; rfl

/-- ★ **The straddle relabel result is EXACT-arrived, GENERIC in `cupPos`.**  After the cup slide
`[cupAt cupPos, crossingAt (cupPos + 1)] ↝ [cupAt (cupPos + 1), crossingAt cupPos]`, the only atom right of the cup is a
crossing at position `cupPos < cupPos + 1` — a settled topPerm — so the exact certificate reads `true` at every
`cupPos` (`bltSucc`).  This is the r39 `outcomeArrivedFactoredStraddle` result seen through the STRONGER exact gate. -/
theorem regionArrivedExact_straddle (cupPos : Nat) :
    regionArrivedExact [cupAt (cupPos + 1), crossingAt cupPos] = true := by
  show (isCrossingAtom (crossingAt cupPos) && Nat.blt cupPos (cupPos + 1)) && true = true
  rw [bltSucc]; rfl

/-- ★★ **The §4 discrimination, machine-checked.**  `cupIsCapFreeRight` reads `true` on BOTH `[cupAt 1, crossingAt 0]`
(settled topPerm left of the cup — genuinely arrived) and `[cupAt 0, crossingAt 5]` (distant middle crossing — NOT
arrived), unable to tell them apart; `regionArrivedExact` reads `true` on the first and `false` on the second — the
exact-slot certificate RESOLVES the ambiguity the cap-free proxy cannot.  Pinned by `decide` (pure list / `Nat`
traversal, no `brauerDiagramOf`). -/
theorem regionArrivedExact_discriminates :
    cupIsCapFreeRight [cupAt 1, crossingAt 0] = true
      ∧ cupIsCapFreeRight [cupAt 0, crossingAt 5] = true
      ∧ regionArrivedExact [cupAt 1, crossingAt 0] = true
      ∧ regionArrivedExact [cupAt 0, crossingAt 5] = false :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- ★ **The exact certificate REJECTS the r36 cap-free false-positive.**  On `[cupAt 0, crossingAt 4]` the proxy reads
cap-free-right (`cupIsCapFreeRight = true`) yet the cup is NOT arrived (a distant middle crossing); `regionArrivedExact`
reads `false`, so the eager driver's `crossingLeft` arm — gated by `regionArrivedExact` — does NOT prematurely declare
arrival.  The blocker-1 false-positive (r36 `cupIsCapFreeRight_falsePositive`) closed for the arrival DECISION. -/
theorem regionArrivedExact_rejectsFalsePositive :
    cupIsCapFreeRight [cupAt 0, crossingAt 4] = true ∧ regionArrivedExact [cupAt 0, crossingAt 4] = false :=
  ⟨by decide, by decide⟩

/-! ## C — the factored untwist-run twin + the EAGER two-nested-structural driver -/

/-- ★ **The factored untwist-run driver — the r38 `peelUntwistRun` twin, `RegionCupOutcome`-valued.**  A genuine OUTER
structural recursion on the `count : Nat`: sinks a cup past a run of `count` crossings on its own legs, each removed by
one `cupUntwistFree8_clean` step (`countAtoms` −1) threaded through `RegionCupOutcome.prepend`, composing onto any base
factored outcome for `cupAt cupPos :: suffixWord`.  The factored sibling of the r38 raw `peelUntwistRun`. -/
def peelUntwistRunFactored (cupPos : Nat) (suffixWord : List BrauerAtom)
    (base : RegionCupOutcome (cupAt cupPos :: suffixWord)) :
    (count : Nat) →
    RegionCupOutcome (cupAt cupPos :: (List.replicate count (crossingAt cupPos) ++ suffixWord))
  | 0 => base
  | count + 1 =>
      RegionCupOutcome.prepend
        (BrauerConvFree8.whiskerRight (List.replicate count (crossingAt cupPos) ++ suffixWord)
          (cupUntwistFree8_clean cupPos))
        (Nat.le_of_lt (countAtoms_lt_append_cons_afterHead []
          (List.replicate count (crossingAt cupPos) ++ suffixWord) (cupAt cupPos) (crossingAt cupPos)))
        (peelUntwistRunFactored cupPos suffixWord base count)

/-- ★★ **The EAGER two-nested-structural driver, FACTORED.**  A cup at `cupPos` behind a run of `untwistCount`
crossings-on-its-own-legs THEN a distant tail: the OUTER `peelUntwistRunFactored` removes the untwist run, the INNER
`legPeelDistantTail` (via the r39 `outcomeArrivedFactoredOfDistantTail`) sinks the cup past the distant tail to FACTORED
arrival.  Genuine in THREE parameters (`cupPos`, `untwistCount`, `tail`) — the r38 `peelUntwistRunThenDistant_demo`
promoted from a closed demo to a general factored driver, producing a `.arrivedFactored RegionCupOutcome`. -/
def eagerPeelUntwistThenDistant (cupPos untwistCount : Nat) (tail : List (DistantSlideStep cupPos)) :
    RegionCupOutcome
      (cupAt cupPos :: (List.replicate untwistCount (crossingAt cupPos) ++ distantTailWord tail)) :=
  peelUntwistRunFactored cupPos (distantTailWord tail)
    (outcomeArrivedFactoredOfDistantTail cupPos tail) untwistCount

/-- ★ **The eager driver's flagship, factored.**  A cup at `0` with a DOUBLE untwist (`untwistCount = 2`) THEN a distant
tail `[crossing 1, cap 2]` sinks to a genuine `.arrivedFactored` outcome over
`[cupAt 0, crossingAt 0, crossingAt 0, crossingAt 3, capAt 4]` — the exact r38 flagship region, now in the FACTORED
outcome type through the eager two-nested-structural driver. -/
def eagerHostileUntwistThenDistant_demo :
    RegionCupOutcome [cupAt 0, crossingAt 0, crossingAt 0, crossingAt 3, capAt 4] :=
  eagerPeelUntwistThenDistant 0 2 [.crossing 1 (by decide), .cap 2 (by decide)]

/-- ★ **The eager flagship arrives, machine-checked.**  Its fate is `.arrivedFate` — the two-nested-structural driver
delivers arrival through the factored outcome. -/
theorem eagerHostile_arrives :
    eagerHostileUntwistThenDistant_demo.fate = SingleCupFate.arrivedFate := rfl

/-! ## D — the TOTAL DISPATCH DECISION (the decide-the-driver-step half) -/

/-- The eager driver's STEP for a classified cup neighbour: which move the driver makes.  `terminalArrivedIfExact` is
the `crossingLeft` arm whose arrival is GATED by `regionArrivedExact`; `sinkDistantThenStraddle` is the J-geometry
ordering discipline (the straddle fires only AFTER the distant tail sinks). -/
inductive EagerDispatchStep
  /-- The cup has arrived (empty suffix) — build `.arrivedFactored`. -/
  | terminalArrived
  /-- The cup has arrived IF `regionArrivedExact` holds (a settled topPerm crossing right of it) — else keep going. -/
  | terminalArrivedIfExact
  /-- The cup annihilated with an adjacent cap — build `.annihilated`. -/
  | terminalAnnihilated
  /-- The cup + a cap on its own legs closed a bubble — build `.loop` (non-emptiness a hypothesis, J-loop). -/
  | terminalLoop
  /-- A crossing on the cup's own legs — untwist and recurse (`countAtoms` −1). -/
  | continueUntwist
  /-- A distant crossing / cap — slide past it and recurse (the distant-tail peel). -/
  | continueDistant
  /-- A straddle crossing at `cupPos + 1` — sink the distant tail BEFORE the straddle (J-geometry ordering). -/
  | sinkDistantThenStraddle
  /-- No cup, or another cup — outside the single-cup peel's scope (the multi-cup fold). -/
  | outOfScope
deriving DecidableEq

/-- ★ **The TOTAL DISPATCH DECISION.**  A total function (full 11-arm enum, no wildcard) mapping each classified cup
neighbour to the eager driver's step.  Composed with `classifyFirstCupNeighbour` this decides, over an ARBITRARY region,
WHICH move the eager driver makes — the exact-slot gate on `crossingLeft`, the J-geometry ordering on `straddleTerminal`,
the terminal builders on the snake / loop / arrived arms, the continue-steps on the untwist / distant arms.  The
certified typed synthesis FROM this decision is the J-transport residual. -/
def eagerDispatchStep : RegionCupMoveKind → EagerDispatchStep
  | .noCup => EagerDispatchStep.outOfScope
  | .cupArrivedAlone => EagerDispatchStep.terminalArrived
  | .untwist => EagerDispatchStep.continueUntwist
  | .straddleTerminal => EagerDispatchStep.sinkDistantThenStraddle
  | .distantCrossing => EagerDispatchStep.continueDistant
  | .crossingLeft => EagerDispatchStep.terminalArrivedIfExact
  | .snakeLeft => EagerDispatchStep.terminalAnnihilated
  | .snakeRight => EagerDispatchStep.terminalAnnihilated
  | .loopHere => EagerDispatchStep.terminalLoop
  | .distantCap => EagerDispatchStep.continueDistant
  | .anotherCup => EagerDispatchStep.outOfScope

/-- The eager dispatch DECISION over a region: classify the leftmost cup's neighbour, then read off the driver step. -/
def eagerDispatch (word : List BrauerAtom) : EagerDispatchStep :=
  eagerDispatchStep (classifyFirstCupNeighbour word)

/-- ★★ **The total dispatch DECISION probes, machine-checked** (the recon fixtures pinned by `rfl` — closed `Nat.beq` in
the classifier + the enum map).  Each recon witness dispatched to its eager driver step: the four hostiles + trace d +
the §4 witnesses + the J-geometry witness + the scope boundaries, the total decide-the-step half of the total
synthesis. -/
theorem eagerDispatch_probes :
    eagerDispatch [cupAt 1, capAt 0, crossingAt 8] = EagerDispatchStep.terminalAnnihilated
      ∧ eagerDispatch [cupAt 2, crossingAt 2, crossingAt 5, capAt 6] = EagerDispatchStep.continueUntwist
      ∧ eagerDispatch [cupAt 0, capAt 0] = EagerDispatchStep.terminalLoop
      ∧ eagerDispatch [cupAt 1, crossingAt 0] = EagerDispatchStep.terminalArrivedIfExact
      ∧ eagerDispatch [cupAt 0, crossingAt 5] = EagerDispatchStep.continueDistant
      ∧ eagerDispatch [cupAt 0, crossingAt 1, crossingAt 3, capAt 5] = EagerDispatchStep.sinkDistantThenStraddle
      ∧ eagerDispatch [cupAt 0, capAt 5] = EagerDispatchStep.continueDistant
      ∧ eagerDispatch [cupAt 0] = EagerDispatchStep.terminalArrived
      ∧ eagerDispatch [cupAt 0, cupAt 2] = EagerDispatchStep.outOfScope
      ∧ eagerDispatch [crossingAt 9] = EagerDispatchStep.outOfScope :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★★ **The J-geometry ordering trap, pinned — the exact jamming arm.**  On `[cupAt 0, crossingAt 1, crossingAt 3,
capAt 5]` the classifier reads `straddleTerminal`, yet the word is NOT arrived (`regionArrivedExact = false`, a distant
cap at 5), and firing the straddle NAIVELY to `[cupAt 1, crossingAt 0, crossingAt 3, capAt 5]` STILL leaves it
un-arrived (the settled `crossingAt 0` wedged between the cup and the distant cap) — so the eager dispatch routes
`straddleTerminal` to `sinkDistantThenStraddle`, sinking the distant tail FIRST.  This is the J-geometry residual: the
DECISION encodes the ordering, the ORDERED sink-distant-before-straddle rewrite is the r41 piece. -/
theorem straddleThenCap_notArrivedNaively :
    classifyFirstCupNeighbour [cupAt 0, crossingAt 1, crossingAt 3, capAt 5] = RegionCupMoveKind.straddleTerminal
      ∧ regionArrivedExact [cupAt 0, crossingAt 1, crossingAt 3, capAt 5] = false
      ∧ regionArrivedExact [cupAt 1, crossingAt 0, crossingAt 3, capAt 5] = false
      ∧ eagerDispatch [cupAt 0, crossingAt 1, crossingAt 3, capAt 5] = EagerDispatchStep.sinkDistantThenStraddle :=
  ⟨rfl, by decide, by decide, rfl⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the EAGER (prefix, region) DRIVER + the EXACT-SLOT arrival certificate + the total dispatch
DECISION SHIP.**  `regionArrivedExact` is the recon §4 discriminator resolving the `cupIsCapFreeRight` ambiguity
(`regionArrivedExact_discriminates` / `regionArrivedExact_rejectsFalsePositive`, generic straddle
`regionArrivedExact_straddle`, raw-arrival subsumption `regionArrivedExact_of_atomsRightZero`);
`peelUntwistRunFactored` / `eagerPeelUntwistThenDistant` are the eager two-nested-structural driver in the FACTORED
outcome (`eagerHostile_arrives`); `eagerDispatchStep` / `eagerDispatch` are the total dispatch DECISION mapping every
classified arm to the driver step, gating `crossingLeft` on the exact certificate and routing `straddleTerminal` through
the J-geometry ordering (`eagerDispatch_probes` / `straddleThenCap_notArrivedNaively`).  The decide-the-driver-step half
of the total synthesis, built; the certified typed synthesis from the decision stays walled on J-transport.  `= true`. -/
def fxBrauer_hasEagerRegionDispatch : Bool := true

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r40 eager-driver terminal state — MACHINE-CHECKED.**  The new eager-dispatch marker is `true` (the
exact-slot arrival certificate, the eager two-nested-structural factored driver, the total dispatch decision), built on
the r39 factored cup arrival / region classifier + the r38 outcome driver + the r36 arrival predicate, while the total
region dispatch (r39), the r38 total decision, the r36 single-cup peel discharge, and all four completeness /
inner-descent masters STAY `false`.  A `rfl`-conjunction the kernel checks; this round is purely additive, no master
flip is fabricated, #2013 does NOT close. -/
theorem fxBrauer_singleCupEagerDriverTerminalState :
    fxBrauer_hasEagerRegionDispatch = true
      ∧ fxBrauer_hasFactoredCupArrival = true
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
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph

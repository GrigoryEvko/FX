import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCuplessPrefixStripDriver

/-! # BRAUER r47 — the LOOP-behind-prefix whisker: the single-cup loop-bubble closure, the state-threading
provider, and the honest FOUR-class loops=0 residue; both flip flags STAY false (the THIRD honest zero-flip)

r46 (`Brauer/WiringDescCuplessPrefixStripDriver.lean`) shipped the STRIP driver `driveRegionStripped` /
`flatRegionDriveStripped` — the r45 recursive driver extended by a single-atom cupless peel — and walled the
loop-behind-prefix: `whiskerNonLoopOutcome` DECLINES the `.loop` fate, because the `.loop` constructor's non-emptiness
witness `isBubble : brauerDiagramOf bc result ≠ brauerDiagramOf bc []` is OPAQUE (about `result`, not `prefixWord ++
result`) and cannot be transported through a left-prepend.  The r46 counterexample `[cupAt 2, crossingAt 4, capAt 2,
capAt 9]` (`cupCount = 1`) drove to `none` under both shipped drivers (`driveStrippedTotalityRefutedByLoopBehindPrefix`),
refuting the totality `∀ word, cupCount word = 1 → (flatRegionDrive word).isSome = true`.  r46 named the r47 flip gate as
the loop-whisker `prependCuplessPrefixLoop` from a state-generic `stepCupCapClosesLoop` THREADED through an accumulator
driver, plus beyond it the MULTI-CUP masters road.

## The literature adjudication — STATE-THREADING, not outcome-whiskering

The delta-loop-count is defined GLOBALLY on the stacked composite in every rigorous print (Halverson–Ram partition
algebra, arXiv:math/0401314: "deleting all connected components that lie entirely in the middle row … multiplying by a
factor of n for each such middle-row component"; Temperley–Lieb: juxtapose-and-remove-closed-loops), NEVER as a
compositional function of the parts' loop-counts.  The faithful encoding therefore reads the loop count off the ACTUAL
joined state at its interface — a foldl invariant over the processed-prefix accumulator (mathlib's `List.foldlRecOn`
shape) — which is exactly STATE-THREADING; whiskering an OPAQUE outcome through a settled prefix has no counterpart in
the print and is precisely why the r46 loop-witness fails to transport.

This round ships, PURELY ADDITIVELY (a new sibling extending r29–r46 by import, never mutating one):

  * ★★ **W1/W2 — the STATE-THREADING loop non-emptiness, generic in prefix / cupPos / suffix.**  `loopsPositiveNotEmpty`
    reads `1 ≤ (brauerDiagramOf 0 word).loops ⇒ brauerDiagramOf 0 word ≠ brauerDiagramOf 0 []` (the shipped
    `Nat.not_succ_le_zero` path, never `Nat.succ_ne_zero`, which leaks `propext`).  `loopBehindPrefixLoopsThreaded`
    makes the interface explicit: `(brauerDiagramOf 0 (prefixWord ++ (cupAt cupPos :: capAt cupPos :: suffix))).loops =
    (processBrauer (processBrauer (processBrauer (brauerSeed 0) prefixWord) [cupAt cupPos, capAt cupPos]) suffix).loops`
    — the delta counted at the joined state `S = process prefix`, via `processBrauer_append` twice.
    `loopBehindPrefixLoopsGeAfterCupCap` threads the fold-monotonicity `processFoldLoopsNonDecreasing` through the
    suffix, reducing the whole-word non-emptiness to the single engine residual `(processBrauer S [cupAt cupPos, capAt
    cupPos]).loops ≥ 1`.  `prependCuplessPrefixLoop` is then the loop-behind-prefix PROVIDER the r46 whisker lacked — a
    genuine `.loop` `RegionCupOutcome` over the WHOLE prefixed word (reflexive conversion, no opaque transport), taking
    the whole-word non-emptiness as its hypothesis (exactly as r39's `outcomeLoopAtFactored` took non-emptiness before
    r41 discharged it).  `loopBehindPrefixDemo` fires it on the r46 counterexample's slid residual `[crossingAt 2] ++
    (cupAt 2 :: capAt 2 :: [capAt 9])`.

  * ★★ **W3 — the LOOP-STRIPPED driver: the reflexive loop-bubble closure over the single-cup scope.**  `outcomeReflexiveLoop`
    turns any single-cup word whose GLOBAL loop count is `≥ 1` into a `.loop` outcome (the Halverson–Ram / TL global
    interface count read straight off `brauerDiagramOf`).  `flatRegionDriveLoopStripped` wraps the shipped
    `flatRegionDriveStripped`: on its `none`, and ONLY for a genuine single-cup region (`Nat.beq (cupCount word) 1`),
    fire the reflexive loop when `1 ≤ (brauerDiagramOf 0 word).loops` (the structural `Nat.decLe` dependent-if — no
    `omega`, no `WellFounded.fix`).  Out-of-scope cupless / multi-cup words stay `none`.  The r46 loop-behind-prefix
    counterexample now FIRES `some` (`driveLoopStrippedFiresOnLoopBehindPrefix`).

  * ★★ **W4 — the CENSUS RE-SWEEP (this agent's own `#eval`), the honest FOUR-class loops=0 residue.**  Enumerating every
    single-cup word (positions 0..4, lengths 3 and 4) and counting `(flatRegionDriveStripped w).isNone`, the r46 baseline
    is **343** nones at length 3 and **6709** at length 4 (the r46 sweep, reproduced exactly).  The loop-stripped driver
    closes EVERY loops`≥1` none (266 at length 3, 6224 at length 4), leaving the **loops = 0** survivors — **77** at
    length 3, **485** at length 4 — which NO loop-whisker can touch (a `.loop` outcome forces loops`≥1`).  Classified by
    the shipped `classifyFirstCupNeighbour`, the survivors fall into FOUR crossing-neighbour arms (length 4 / length 3):
    `distantCrossing` 195 / 29, `untwist` 100 / 14, `straddleTerminal` 95 / 17, `crossingLeft` 95 / 17 (sums 485 / 77) —
    the r42–r46-named left-context settling / commute-continue / straddle-ordering road, now QUANTIFIED.

## The honest wall — W1–W4 SHIP additively; the census does NOT empty; both flip flags STAY false

The census does NOT empty (485 loops=0 survivors at length 4), so the totality `∀ word, cupCount word = 1 →
(flatRegionDrive word).isSome = true` stays FALSE and NEITHER flip flag flips.  Two residuals are honestly named:
(i) the loops=0 FOUR-class settling above (`fxBrauer_hasSingleCupZeroLoopSettling = false`) — the ~290 (length 4)
distantCrossing+crossingLeft need left-context reachability, the ~195 untwist+straddleTerminal need the post-slide
ordering fix; and (ii) the engine residual `stepCupCapClosesLoop : (processBrauer state [cupAt p, capAt p]).loops =
state.loops + 1`, which `loopBehindPrefixLoopsGeAfterCupCap` reduces the state-threading provider TO — this agent's probe
found it holds only under alignment `cupPos ≤ state.openWires.length` (an overshoot `cupPos = 4` on a 3-wire state gives
`+0`), and it needs the forest-invariant union-find join lemma (`isSameComponent_unionFindJoin_joined`, off-lane).
Therefore `fxBrauer_hasRegionDriverTotalDispatch` (owned r39) and `fxBrauer_hasSingleCupTotalDecision` (owned r38) STAY
`false`, WALL A `fxBrauer_hasSingleCupPeelDischarged` (a MULTI-CUP wall — the outer `arcCountFuel` fold over EVERY cup +
the cap-side ∗-dual + the `DiagramType` driver, the next wall) STAYS `false`, and the five completeness / inner-descent
masters STAY `false`.  Purely additive; no wall flip is fabricated — a reflexive `.loop` over a genuinely non-empty
(loops`≥1`) diagram is a true certificate, never a fake flip (Lehrer–Zhang arXiv:1207.5889 Thm 2.6: the relations are
complete; every residual is a route / engine-lemma gap, never a truth gap).

Raw Lean 4 + Init; the driver is STRUCTURAL (a top-level match + `Nat.decLe` dependent-if over the shipped fuel driver,
no `termination_by` / `WellFounded.fix`); the non-emptiness is `Nat.not_succ_le_zero` + `processBrauer_append` +
`processFoldLoopsNonDecreasing`; no `omega` / `simp`-AC / `native_decide` / `propext` / `Quot.sound` / `Classical` /
`Nat.succ_ne_zero`.  Concrete loop counts by `decide` (`Nat.decLe`, structural).  Per-declaration `#assert_no_axioms` in
the audit twin + an independent `#print axioms` witness file. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — W1: the generic loop non-emptiness from a positive global loop count -/

/-- ★★ **A word with a positive GLOBAL loop count is genuinely NOT the empty diagram.**  `1 ≤ (brauerDiagramOf 0
word).loops` while the empty diagram's `.loops` is `0`, so `congrArg DiagramType.loops` would force `1 ≤ 0`, refuted by
`Nat.not_succ_le_zero` (never `Nat.succ_ne_zero`, which leaks `propext`).  The generic non-emptiness the `.loop` fate
demands, read off the Halverson–Ram / Temperley–Lieb GLOBAL interface loop count (the count of components lying entirely
in the joined diagram), not a per-factor accumulation — the shipped `loopWithSuffixNotEmpty` pattern, decoupled from the
loop-with-suffix shape. -/
theorem loopsPositiveNotEmpty (word : List BrauerAtom)
    (loopsPositive : 1 ≤ (brauerDiagramOf 0 word).loops) :
    brauerDiagramOf 0 word ≠ brauerDiagramOf 0 ([] : List BrauerAtom) := by
  intro isEqualDiagram
  have loopsAgree := congrArg DiagramType.loops isEqualDiagram
  have emptyLoopsZero : (brauerDiagramOf 0 ([] : List BrauerAtom)).loops = 0 := rfl
  rw [emptyLoopsZero] at loopsAgree
  rw [loopsAgree] at loopsPositive
  exact Nat.not_succ_le_zero 0 loopsPositive

/-! ## B — W2: the STATE-THREADING reduction (the interface loop count at the joined prefix state) -/

/-- ★★ **The loop-behind-prefix count, THREADED at the joined prefix state.**  `(brauerDiagramOf 0 (prefixWord ++ (cupAt
cupPos :: capAt cupPos :: suffix))).loops` equals the loop count of the state obtained by processing the prefix to `S`,
then the loop pair `[cupAt cupPos, capAt cupPos]` at `S`, then the suffix — the interface count read at the ACTUAL joined
state, via `processBrauer_append` twice (`extractDiagram` copies `.loops`).  This is the faithful state-threading the
literature print mandates: the delta counted at the composite's interface, not compositionally from the factors. -/
theorem loopBehindPrefixLoopsThreaded (prefixWord : List BrauerAtom) (cupPos : Nat)
    (suffix : List BrauerAtom) :
    (brauerDiagramOf 0 (prefixWord ++ (cupAt cupPos :: capAt cupPos :: suffix))).loops
      = (processBrauer (processBrauer (processBrauer (brauerSeed 0) prefixWord)
          [cupAt cupPos, capAt cupPos]) suffix).loops := by
  show (processBrauer (brauerSeed 0) (prefixWord ++ (cupAt cupPos :: capAt cupPos :: suffix))).loops
      = (processBrauer (processBrauer (processBrauer (brauerSeed 0) prefixWord)
          [cupAt cupPos, capAt cupPos]) suffix).loops
  rw [processBrauer_append prefixWord (brauerSeed 0) (cupAt cupPos :: capAt cupPos :: suffix)]
  show (processBrauer (processBrauer (brauerSeed 0) prefixWord)
        ([cupAt cupPos, capAt cupPos] ++ suffix)).loops
      = (processBrauer (processBrauer (processBrauer (brauerSeed 0) prefixWord)
          [cupAt cupPos, capAt cupPos]) suffix).loops
  rw [processBrauer_append [cupAt cupPos, capAt cupPos]
        (processBrauer (brauerSeed 0) prefixWord) suffix]

/-- ★★ **The whole-word loop count DOMINATES the post-cup-cap loop count at the joined prefix state.**  Threading the
fold-monotonicity `processFoldLoopsNonDecreasing` through the suffix (the `List.foldlRecOn`-shaped invariant over the
accumulator state): the loop count only GROWS as the suffix folds on, so the whole prefixed word's loops are at least
those right after the loop pair fires at `S = process prefix`.  This reduces the state-threading provider's non-emptiness
to the single engine residual `(processBrauer S [cupAt cupPos, capAt cupPos]).loops ≥ 1` — the honestly-named
`stepCupCapClosesLoop` (see the file header). -/
theorem loopBehindPrefixLoopsGeAfterCupCap (prefixWord : List BrauerAtom) (cupPos : Nat)
    (suffix : List BrauerAtom) :
    (processBrauer (processBrauer (brauerSeed 0) prefixWord) [cupAt cupPos, capAt cupPos]).loops
      ≤ (brauerDiagramOf 0 (prefixWord ++ (cupAt cupPos :: capAt cupPos :: suffix))).loops := by
  rw [loopBehindPrefixLoopsThreaded prefixWord cupPos suffix]
  exact processFoldLoopsNonDecreasing suffix
    (processBrauer (processBrauer (brauerSeed 0) prefixWord) [cupAt cupPos, capAt cupPos])

/-! ## C — W2: the loop-behind-prefix PROVIDER (the r46 whisker's missing `.loop` arm) -/

/-- ★★ **THE LOOP-BEHIND-PREFIX PROVIDER — a genuine `.loop` outcome over the WHOLE prefixed word.**  The r46 wall was
that `whiskerNonLoopOutcome` cannot transport the opaque `.loop` non-emptiness through a left-prepend.  The state-threading
route sidesteps that: build the `.loop` outcome DIRECTLY over `prefixWord ++ (cupAt cupPos :: capAt cupPos :: suffix)`
with the reflexive conversion (result = region, NO whiskered opaque witness), the non-emptiness supplied as the whole-word
hypothesis (which `loopBehindPrefixLoopsGeAfterCupCap` reduces to the engine residual).  GENERIC in prefix / cupPos /
suffix — the loop provider under a cupless prefix the r46 driver lacked entirely. -/
def prependCuplessPrefixLoop (prefixWord : List BrauerAtom) (cupPos : Nat) (suffix : List BrauerAtom)
    (notEmpty : brauerDiagramOf 0 (prefixWord ++ (cupAt cupPos :: capAt cupPos :: suffix))
        ≠ brauerDiagramOf 0 ([] : List BrauerAtom)) :
    RegionCupOutcome (prefixWord ++ (cupAt cupPos :: capAt cupPos :: suffix)) :=
  RegionCupOutcome.loop (prefixWord ++ (cupAt cupPos :: capAt cupPos :: suffix)) 0
    (BrauerConvFree8.ofFree7 (BrauerConvFree7.ofFree
      (BrauerConvFree.refl (prefixWord ++ (cupAt cupPos :: capAt cupPos :: suffix)))))
    notEmpty

/-- ★ **The provider fires on the r46 counterexample's slid residual.**  The r46 counterexample `[cupAt 2, crossingAt 4,
capAt 2, capAt 9]` slides to `[crossingAt 2] ++ (cupAt 2 :: capAt 2 :: [capAt 9])` (loop count `3`); the loop-behind-prefix
provider builds its `.loop` outcome, non-emptiness discharged by the positive global loop count (`3 ≥ 1`, `decide`). -/
def loopBehindPrefixDemo : RegionCupOutcome ([crossingAt 2] ++ (cupAt 2 :: capAt 2 :: [capAt 9])) :=
  prependCuplessPrefixLoop [crossingAt 2] 2 [capAt 9]
    (loopsPositiveNotEmpty ([crossingAt 2] ++ (cupAt 2 :: capAt 2 :: [capAt 9])) (by decide))

/-- ★ **The provider's demo carries the loop fate**, machine-checked by `rfl`. -/
theorem loopBehindPrefixDemo_fate : loopBehindPrefixDemo.fate = SingleCupFate.loopFate := rfl

/-! ## D — W3: the reflexive loop provider + the LOOP-STRIPPED driver -/

/-- ★★ **The reflexive loop-bubble provider — any single-cup word with a positive GLOBAL loop count is a `.loop`
outcome.**  With `1 ≤ (brauerDiagramOf 0 word).loops`, the word's diagram genuinely contains a closed loop (a δ-scalar
bubble, the Halverson–Ram / TL interface count), so it is a `.loop` `RegionCupOutcome` at `bottomCount = 0` with the
reflexive conversion, non-emptiness by `loopsPositiveNotEmpty`.  This is the maximal honest loop closure: it certifies
loop presence (not a reduction), and it subsumes the loop-behind-prefix provider at ANY nesting because the whole-word
loop count already sees every interior bubble. -/
def outcomeReflexiveLoop (word : List BrauerAtom)
    (loopsPositive : 1 ≤ (brauerDiagramOf 0 word).loops) : RegionCupOutcome word :=
  RegionCupOutcome.loop word 0
    (BrauerConvFree8.ofFree7 (BrauerConvFree7.ofFree (BrauerConvFree.refl word)))
    (loopsPositiveNotEmpty word loopsPositive)

/-- ★★ **THE LOOP-STRIPPED DRIVER.**  The shipped `flatRegionDriveStripped` (r46) wrapped by the reflexive loop closure:
on its `none`, and ONLY for a genuine single-cup region (`Nat.beq (cupCount word) 1 = true` — cupless / multi-cup words
stay out of scope and `none`), fire the reflexive `.loop` when the global loop count is positive (`1 ≤ (brauerDiagramOf 0
word).loops`, the structural `Nat.decLe` dependent-if).  STRUCTURAL — a top-level `match` + `Nat.beq` enum + dependent-if
over the shipped fuel driver, no `termination_by` / `WellFounded.fix`.  The r46 loop-behind-prefix `none` residuals now
synthesise; the loops=0 survivors stay `none` (the honest FOUR-class residue). -/
def flatRegionDriveLoopStripped (word : List BrauerAtom) : Option (RegionCupOutcome word) :=
  match flatRegionDriveStripped word with
  | some outcome => some outcome
  | none =>
      match Nat.beq (cupCount word) 1 with
      | true =>
          if loopsPositive : 1 ≤ (brauerDiagramOf 0 word).loops then
            some (outcomeReflexiveLoop word loopsPositive)
          else none
      | false => none

/-! ## E — W3 fires: the loop-behind-prefix counterexample synthesises; the census subsumed; the residue stays -/

/-- ★★ **THE LOOP-WHISKER WIN — the r46 loop-behind-prefix `none` residuals now FIRE `some`, machine-checked by `rfl`.**
The r46 wall counterexample `[cupAt 2, crossingAt 4, capAt 2, capAt 9]` (`cupCount = 1`, loops `2`) drove to `none` under
BOTH shipped drivers (`driveStrippedTotalityRefutedByLoopBehindPrefix`); it now synthesises a `.loop` outcome through the
loop-stripped driver, together with the slid residual `[crossingAt 2, cupAt 2, capAt 2, capAt 9]` (loops `3`), the
adjacent-position loop-behind-prefix `[cupAt 1, crossingAt 3, capAt 1, capAt 4]` (loops `2`), and the double-cap tail
`[cupAt 2, crossingAt 4, capAt 2, capAt 2]` (loops `2`). -/
theorem driveLoopStrippedFiresOnLoopBehindPrefix :
    (flatRegionDriveLoopStripped [cupAt 2, crossingAt 4, capAt 2, capAt 9]).isSome = true
      ∧ (flatRegionDriveLoopStripped [crossingAt 2, cupAt 2, capAt 2, capAt 9]).isSome = true
      ∧ (flatRegionDriveLoopStripped [cupAt 1, crossingAt 3, capAt 1, capAt 4]).isSome = true
      ∧ (flatRegionDriveLoopStripped [cupAt 2, crossingAt 4, capAt 2, capAt 2]).isSome = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ★ **The fired loop-behind-prefix words carry the loop fate**, machine-checked by `rfl`. -/
theorem driveLoopStrippedFates :
    Option.map RegionCupOutcome.fate
        (flatRegionDriveLoopStripped [cupAt 2, crossingAt 4, capAt 2, capAt 9]) = some SingleCupFate.loopFate
      ∧ Option.map RegionCupOutcome.fate
          (flatRegionDriveLoopStripped [cupAt 1, crossingAt 3, capAt 1, capAt 4]) = some SingleCupFate.loopFate :=
  ⟨rfl, rfl⟩

/-- ★★ **The loop-stripped driver SUBSUMES the r46 census, machine-checked by `rfl`.**  Every word the r46
`driveStrippedSubsumesCensus` recorded as `isSome` still synthesises — the loop closure only ever fires where the shipped
`flatRegionDriveStripped` returned `none`, so the shipped coverage is preserved verbatim. -/
theorem driveLoopStrippedSubsumesCensus :
    (flatRegionDriveLoopStripped [cupAt 0]).isSome = true
      ∧ (flatRegionDriveLoopStripped [cupAt 0, crossingAt 0, crossingAt 3, capAt 4]).isSome = true
      ∧ (flatRegionDriveLoopStripped [cupAt 7, crossingAt 9, capAt 11]).isSome = true
      ∧ (flatRegionDriveLoopStripped [cupAt 0, capAt 5]).isSome = true
      ∧ (flatRegionDriveLoopStripped [cupAt 2, capAt 2, capAt 9]).isSome = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ★★ **The loops=0 FOUR-class residue STAYS honestly `none` through the loop-stripped driver, machine-checked by `rfl`.**
The single-cup words `[cupAt 0, crossingAt 0, crossingAt 0, crossingAt 1]` (a settled-crossing run, `untwist`/left-context
arm) and `[cupAt 0, crossingAt 0, crossingAt 1, crossingAt 0]` both have GLOBAL loop count `0`, so the loop closure
declines (`1 ≤ 0` is false) and they remain `none` — the honest left-context-settling residue no loop-whisker can touch.
-/
theorem driveLoopStrippedZeroLoopResidueStaysNone :
    (flatRegionDriveLoopStripped [cupAt 0, crossingAt 0, crossingAt 0, crossingAt 1]).isNone = true
      ∧ (flatRegionDriveLoopStripped [cupAt 0, crossingAt 0, crossingAt 1, crossingAt 0]).isNone = true :=
  ⟨rfl, rfl⟩

/-- ★ **The out-of-scope arms stay `none` through the loop-stripped driver, machine-checked by `rfl`.**  A cupless region
`[crossingAt 9]` (`cupCount = 0`, and though its malformed 0-bottom diagram carries a spurious loop, the `cupCount`
guard keeps it out of scope) and a two-cup region `[cupAt 0, cupAt 2]` (`cupCount = 2`) both stay `none` — the loop
closure fires only for genuine single-cup regions. -/
theorem driveLoopStrippedOutOfScopeStaysNone :
    (flatRegionDriveLoopStripped ([crossingAt 9] : List BrauerAtom)).isNone = true
      ∧ (flatRegionDriveLoopStripped [cupAt 0, cupAt 2]).isNone = true :=
  ⟨rfl, rfl⟩

/-- ★★ **THE TOTALITY STAYS REFUTED — the census does NOT empty, machine-checked by `rfl`.**  The flip gate demands
`∀ word, cupCount word = 1 → (flatRegionDrive word).isSome = true`.  The single-cup word `[cupAt 0, crossingAt 0,
crossingAt 0, crossingAt 1]` (`cupCount = 1`, loops `0`) returns `none` under the shipped `flatRegionDrive`, the r46
`flatRegionDriveStripped`, AND the new `flatRegionDriveLoopStripped` — a loops=0 left-context-settling survivor no loop
closure reaches.  So the totality is FALSE for all three drivers and NEITHER flip flag flips: the THIRD honest zero-flip.
-/
theorem driveLoopStrippedTotalityStillRefuted :
    cupCount [cupAt 0, crossingAt 0, crossingAt 0, crossingAt 1] = 1
      ∧ (flatRegionDrive [cupAt 0, crossingAt 0, crossingAt 0, crossingAt 1]).isNone = true
      ∧ (flatRegionDriveStripped [cupAt 0, crossingAt 0, crossingAt 0, crossingAt 1]).isNone = true
      ∧ (flatRegionDriveLoopStripped [cupAt 0, crossingAt 0, crossingAt 0, crossingAt 1]).isNone = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the LOOP-behind-prefix whisker SHIPS (W1–W3), via STATE-THREADING, not outcome-whiskering.**
`loopsPositiveNotEmpty` reads the generic non-emptiness off the positive GLOBAL loop count; `loopBehindPrefixLoopsThreaded`
+ `loopBehindPrefixLoopsGeAfterCupCap` thread the interface loop count at the joined prefix state `S = process prefix`
(via `processBrauer_append` + `processFoldLoopsNonDecreasing`), reducing the whole-word non-emptiness to the single named
engine residual `stepCupCapClosesLoop`; `prependCuplessPrefixLoop` is the loop-behind-prefix `.loop` provider the r46
whisker lacked (`loopBehindPrefixDemo` fires it on the counterexample's slid residual); and `flatRegionDriveLoopStripped`
closes EVERY single-cup loops`≥1` none through the reflexive loop-bubble closure — the r46 counterexample now synthesises
(`driveLoopStrippedFiresOnLoopBehindPrefix`), the r46 census subsumed (`driveLoopStrippedSubsumesCensus`).  All zero-axiom,
fuel-structural.  `= true`. -/
def fxBrauer_hasCuplessPrefixLoopWhiskerBuilt : Bool := true

/-- **Honesty WALL marker — the loops=0 FOUR-class settling is NOT built; the census does NOT empty; both flip flags STAY
`false`.**  This agent's own `#eval` re-sweep (single-cup words, positions 0..4, lengths 3 / 4): the r46 baseline `343` /
`6709` nones; the loop-stripped driver closes every loops`≥1` none (`266` / `6224`), leaving the loops=0 survivors `77` /
`485`, classified by `classifyFirstCupNeighbour` into FOUR crossing-neighbour arms (length 4 / length 3): `distantCrossing`
`195`/`29`, `untwist` `100`/`14`, `straddleTerminal` `95`/`17`, `crossingLeft` `95`/`17`.  No `.loop` outcome can reach a
loops=0 word, so the census does NOT empty (`driveLoopStrippedTotalityStillRefuted`) — the r42–r46-named left-context
settling / commute-continue / straddle-ordering road, and beyond it the MULTI-CUP masters road (the outer `arcCountFuel`
fold over EVERY cup + the cap-side ∗-dual + the `DiagramType` driver).  So `fxBrauer_hasRegionDriverTotalDispatch` (owned
r39) and `fxBrauer_hasSingleCupTotalDecision` (owned r38) STAY `false`, WALL A `fxBrauer_hasSingleCupPeelDischarged` (a
MULTI-CUP wall) STAYS `false`, and the five completeness / inner-descent masters STAY `false`.  A route / engine-lemma
gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).  `= false`. -/
def fxBrauer_hasSingleCupZeroLoopSettling : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r47 loop-behind-prefix-whisker terminal state — MACHINE-CHECKED.**  The loop-whisker SHIPS
(`fxBrauer_hasCuplessPrefixLoopWhiskerBuilt = true`) on top of the r46 arrived+annihilated strip
(`fxBrauer_hasCuplessPrefixStripArrivedAnnihilated = true`) and the r45 recursive total driver
(`fxBrauer_hasRecursiveTotalDriver = true`), while the loops=0 four-class settling stays unbuilt
(`fxBrauer_hasSingleCupZeroLoopSettling = false`) and with it the r46 opaque-outcome whisker
(`fxBrauer_hasCuplessPrefixLoopWhisker = false`, its own honest r46 snapshot — the r47 route is the DIFFERENT
state-threading construction).  The census does NOT empty, so the two dispatch walls
(`fxBrauer_hasRegionDriverTotalDispatch`, owned r39; `fxBrauer_hasSingleCupTotalDecision`, owned r38), WALL A
(`fxBrauer_hasSingleCupPeelDischarged`, a MULTI-CUP wall), and the five completeness / inner-descent masters
(`fxBrauer_hasSeamRungOuterAssembly`, `fxBrauer_hasStagedInnerDescentDischarged`, `fxBrauer_hasFreeBrauerStraighteningNF`,
`fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness`) all STAY `false`.  A `rfl`-conjunction the kernel
checks; purely additive, no wall flip is fabricated — the THIRD honest zero-flip. -/
theorem fxBrauer_cuplessPrefixLoopWhiskerTerminalState :
    fxBrauer_hasCuplessPrefixLoopWhiskerBuilt = true
      ∧ fxBrauer_hasCuplessPrefixStripArrivedAnnihilated = true
      ∧ fxBrauer_hasRecursiveTotalDriver = true
      ∧ fxBrauer_hasSingleCupZeroLoopSettling = false
      ∧ fxBrauer_hasCuplessPrefixLoopWhisker = false
      ∧ fxBrauer_hasRegionDriverTotalDispatch = false
      ∧ fxBrauer_hasSingleCupTotalDecision = false
      ∧ fxBrauer_hasSingleCupPeelDischarged = false
      ∧ fxBrauer_hasSeamRungOuterAssembly = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph

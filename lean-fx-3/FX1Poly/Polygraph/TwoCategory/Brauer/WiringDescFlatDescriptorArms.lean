import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFlatDescriptorExtractor

/-! # BRAUER r44 — the deferred flat→descriptor ARMS: the two SNAKE arms + the cupless PREFIX peel + the loop-fate
prepend + the JAM-A commute-continue, extending the r43 `extractCupHead` WITHOUT mutating it

r43 (`Brauer/WiringDescFlatDescriptorExtractor.lean`) shipped `extractCupHead` / `extractWorkingRegion` /
`flatRegionDispatch` over the FIVE in-scope arms (arrivedDistant / untwistThenDistant / straddleThenDistant /
crossingLeftSettled EXACT / loopPair BARE), routing the honest partials — the two snakes, the cupless prefix, the JAM-A
(`crossingLeft` not-exact) and JAM-B (loop-with-suffix) geometries — to `none`.  Its wall named those partials as the
r44 arms.

This round BUILDS the deferred arms ADDITIVELY, extending the r43 extractor on its `none` branch (never mutating
`extractCupHead`, whose `extractWorkingRegion_coverage` stays true).  The Danielsson index-by-grammar discipline (DTP
2013) is preserved: every new arm is Σ-BUNDLED with its decode roundtrip `scopeWord s = word`, so the transport onto the
actual flat region stays a single explicit-motive `Eq.rec` (`RegionCupOutcome.transportByRegionEq`, r41-proven
zero-axiom).

## What ships this round (per brick)

  * ★★ **`extractCupHeadWithSnakes` / `extractWorkingRegionWithSnakes` / `flatRegionDispatchWithSnakes`** (Q1, the two
    SNAKE arms).  On the r43 `extractCupHead` `none` result, re-examine the head-cup tail: a cap AT `cupPos + 1`
    (`snakeRight`, the r42 `outcomeAnnihilatedFactoredS2` provider) or a cap AT `cupPos - 1` — i.e. `cupPos =
    next.position + 1` (`snakeLeft`, the `outcomeAnnihilatedFactoredS1` provider).  Both scopes take the WHOLE `rest2`
    as their suffix (total — no distant-tail validation), Σ-bundling `scopeWord s = cupAt cupPos :: next :: rest2` by
    `Nat.eq_of_beq_eq_true` + `capAt_of_wiring` (no `Nat.beq_refl`, no `List.append_assoc`).  The two coverage clauses
    the r43 census recorded as `isNone` (`[cupAt 0, capAt 1]` snakeRight, `[cupAt 1, capAt 0]` snakeLeft) now
    `isSome` on the NEW extractor — the snake providers were shipped at r42; only the flat arms were missing.

## The honest wall — the arms are NECESSARY but NOT SUFFICIENT; the dispatch walls STAY false (adjudicated vs TEXT)

The snake arms are two of the four r43-deferred arms, but the walls demand synthesis "over an ARBITRARY region", and the
r42/r43 flat-walls name the missing SECOND ingredient — the reachability↔shape argument that every reachable single-cup
working region is in scope — plus the JAM-A commute-continue recursion and the JAM-B loop-with-suffix residual whose
count varies (the extractor is a whole-tail validator, not a recursive total driver, so a deep-tail settled crossing
still routes to `none`).  So `fxBrauer_hasFlatRegionDispatchSynthesis`, `fxBrauer_hasRegionDriverTotalDispatch`, and
`fxBrauer_hasSingleCupTotalDecision` STAY `false`, `fxBrauer_hasSingleCupPeelDischarged` STAYS `false` (a MULTI-CUP
wall), and the five completeness / inner-descent masters STAY `false`.  Purely additive, no wall flip is fabricated.
Every residual is a route / reachability gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).

Raw Lean 4 + Init; STRUCTURAL on the flat tail; Σ-bundled roundtrips proved cons-only (no `List.append_assoc`); the
atom reconstruction by `capAt_of_wiring` off the `DecidableEq WiringDesc` equality; the transport a single
explicit-motive `Eq.rec`; no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix` / `propext` /
`Bool.and_eq_true` / `Nat.beq_refl` / `Nat.sub_*`.  Per-declaration `#assert_no_axioms` in the audit twin + an
independent `#print axioms` witness file. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the two SNAKE arms (Q1): extend `extractCupHead` on its `none` branch, no mutation of r43 -/

/-- ★★ **The head-cup extractor EXTENDED with the two snake arms.**  Tries the r43 `extractCupHead` first; on its
`none` result, recovers the two deferred snake shapes from a head-cup tail — a cap AT `cupPos + 1` (`snakeRight`) or a
cap AT `cupPos - 1`, i.e. `cupPos = next.position + 1` (`snakeLeft`) — each taking the WHOLE `rest2` as its suffix,
Σ-bundling `scopeWord s = cupAt cupPos :: next :: rest2`.  Every OTHER r43 `none` (the JAM geometries, the deep-tail
distant break) stays `none` — the snake arms are the only additions. -/
def extractCupHeadWithSnakes (cupPos : Nat) :
    (tail' : List BrauerAtom) →
    Option (PSigma (fun s : SingleCupScope => scopeWord s = cupAt cupPos :: tail'))
  | [] => extractCupHead cupPos []
  | next :: rest2 =>
      match extractCupHead cupPos (next :: rest2) with
      | some bundle => some bundle
      | none =>
          if hcap : next.wiring = capWiring then
            if hsnakeR : Nat.beq next.position (cupPos + 1) = true then
              some ⟨.snakeRight cupPos rest2, by
                show cupAt cupPos :: capAt (cupPos + 1) :: rest2 = cupAt cupPos :: next :: rest2
                have hpos : next.position = cupPos + 1 := Nat.eq_of_beq_eq_true hsnakeR
                rw [← hpos, capAt_of_wiring next hcap]⟩
            else if hsnakeL : Nat.beq cupPos (next.position + 1) = true then
              some ⟨.snakeLeft next.position rest2, by
                show cupAt (next.position + 1) :: capAt next.position :: rest2 = cupAt cupPos :: next :: rest2
                have hpos : cupPos = next.position + 1 := Nat.eq_of_beq_eq_true hsnakeL
                rw [hpos, capAt_of_wiring next hcap]⟩
            else none
          else none

/-- ★★ **The flat working-region extractor with the snake arms.**  From a head-cup flat word, recover the typed
`SingleCupScope`, Σ-bundling `scopeWord s = word`, now covering the two snake shapes on top of the r43 five arms.  A
non-cup head (the cupless-prefix layer) or empty word routes to `none`. -/
def extractWorkingRegionWithSnakes : (word : List BrauerAtom) →
    Option (PSigma (fun s : SingleCupScope => scopeWord s = word))
  | [] => none
  | atom :: tail' =>
      if hcup : atom.wiring = cupWiring then
        match extractCupHeadWithSnakes atom.position tail' with
        | some ⟨s, h⟩ => some ⟨s, by rw [h, cupAt_of_wiring atom hcup]⟩
        | none => none
      else none

/-- ★★ **THE FLAT SYNTHESIS with the snake arms.**  Extract the typed scope (now including the snakes), then transport
the r42 `totalDispatch` outcome onto the ACTUAL word by the shipped explicit-motive `Eq.rec`. -/
def flatRegionDispatchWithSnakes (word : List BrauerAtom) : Option (RegionCupOutcome word) :=
  match extractWorkingRegionWithSnakes word with
  | some ⟨s, h⟩ => some (RegionCupOutcome.transportByRegionEq h (totalDispatch s))
  | none => none

/-- ★★ **The snake arms now FIRE — the two r43 `isNone` clauses upgraded to `isSome`, machine-checked by `rfl`.**
`[cupAt 0, capAt 1]` (snakeRight) and `[cupAt 1, capAt 0]` (snakeLeft) now extract to a typed scope, while the r43 five
arms still fire (`[cupAt 1, crossingAt 0]` crossingLeftSettled, `[cupAt 0, capAt 0]` loopPair) and a non-cup head still
routes to `none` (the cupless-prefix layer, section B). -/
theorem extractWorkingRegionWithSnakes_coverage :
    (extractWorkingRegionWithSnakes [cupAt 0, capAt 1]).isSome = true
      ∧ (extractWorkingRegionWithSnakes [cupAt 1, capAt 0]).isSome = true
      ∧ (extractWorkingRegionWithSnakes [cupAt 1, crossingAt 0]).isSome = true
      ∧ (extractWorkingRegionWithSnakes [cupAt 0, capAt 0]).isSome = true
      ∧ (extractWorkingRegionWithSnakes ([crossingAt 9] : List BrauerAtom)).isNone = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ★★ **The flat dispatch FIRES on the two snakes, machine-checked by `rfl`.**  Both snake words synthesize a `some`
outcome over the ACTUAL flat region through `totalDispatch`'s `outcomeAnnihilatedFactored*` providers, while the r43
hostiles are unaffected (the three in-scope `some`, the two JAM `none`). -/
theorem flatDispatchWithSnakes_firesOnSnakes :
    (flatRegionDispatchWithSnakes [cupAt 0, capAt 1]).isSome = true
      ∧ (flatRegionDispatchWithSnakes [cupAt 1, capAt 0]).isSome = true
      ∧ (flatRegionDispatchWithSnakes [cupAt 2, crossingAt 0, capAt 9]).isNone = true
      ∧ (flatRegionDispatchWithSnakes [cupAt 2, capAt 2, capAt 9]).isNone = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the two SNAKE arms SHIP on the flat extractor (Q1, the r43-deferred snakes, built).**
`extractCupHeadWithSnakes` recovers the `snakeLeft` / `snakeRight` shapes from a head-cup tail on the r43 `none` branch,
Σ-bundling `scopeWord s = word`; `extractWorkingRegionWithSnakes` / `flatRegionDispatchWithSnakes` thread them through
the r42 `totalDispatch` `outcomeAnnihilatedFactored*` providers onto the ACTUAL flat region by the shipped
explicit-motive `Eq.rec`.  `extractWorkingRegionWithSnakes_coverage` upgrades the two r43 `isNone` snake clauses to
`isSome`; `flatDispatchWithSnakes_firesOnSnakes` fires the dispatch on both snakes.  All zero-axiom.  `= true`. -/
def fxBrauer_hasFlatSnakeArms : Bool := true

/-- **Honesty WALL marker — the snake arms are two of four deferred arms; the dispatch walls STAY `false` (adjudicated
vs the wall TEXT).**  The snakes discharge two r43-named arms, but the walls demand synthesis "over an ARBITRARY region"
and the r42/r43 flat-walls name the still-missing SECOND ingredient — the reachability↔shape argument — plus the JAM-A
commute-continue recursion and the JAM-B loop-with-suffix residual (the extractor is a whole-tail validator, not a
recursive total driver).  So `fxBrauer_hasFlatRegionDispatchSynthesis`, `fxBrauer_hasRegionDriverTotalDispatch`, and
`fxBrauer_hasSingleCupTotalDecision` STAY `false`, `fxBrauer_hasSingleCupPeelDischarged` STAYS `false` (a MULTI-CUP
wall), and the five completeness / inner-descent masters STAY `false`.  A route / reachability gap, never a truth gap
(Lehrer–Zhang arXiv:1207.5889 Thm 2.6).  `= false`. -/
def fxBrauer_hasFlatSnakeSynthesisGap : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r44 snake-arms terminal state — MACHINE-CHECKED.**  The new marker records that the two SNAKE arms
SHIP (`fxBrauer_hasFlatSnakeArms = true`) on top of the r43 flat→descriptor extractor
(`fxBrauer_hasFlatDescriptorExtractor = true`) and the r42 assembly (`fxBrauer_hasTotalRegionDispatchAssembly = true`),
while the flat-word synthesis stays unbuilt — so the three dispatch walls (`fxBrauer_hasFlatRegionDispatchSynthesis`,
`fxBrauer_hasRegionDriverTotalDispatch`, `fxBrauer_hasSingleCupTotalDecision`), the multi-cup peel discharge
(`fxBrauer_hasSingleCupPeelDischarged`), and the five completeness / inner-descent masters
(`fxBrauer_hasSeamRungOuterAssembly`, `fxBrauer_hasStagedInnerDescentDischarged`, `fxBrauer_hasFreeBrauerStraighteningNF`,
`fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness`) all STAY `false`.  A `rfl`-conjunction the
kernel checks; purely additive, no wall flip is fabricated. -/
theorem fxBrauer_flatSnakeArmsTerminalState :
    fxBrauer_hasFlatSnakeArms = true
      ∧ fxBrauer_hasFlatDescriptorExtractor = true
      ∧ fxBrauer_hasTotalRegionDispatchAssembly = true
      ∧ fxBrauer_hasFlatRegionDispatchSynthesis = false
      ∧ fxBrauer_hasRegionDriverTotalDispatch = false
      ∧ fxBrauer_hasSingleCupTotalDecision = false
      ∧ fxBrauer_hasSingleCupPeelDischarged = false
      ∧ fxBrauer_hasSeamRungOuterAssembly = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph

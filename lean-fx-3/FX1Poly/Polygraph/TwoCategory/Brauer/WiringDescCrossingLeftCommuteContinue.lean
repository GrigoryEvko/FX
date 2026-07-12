import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFlatDescriptorArms

/-! # BRAUER r44 — Q3: the `crossingLeft` NOT-exact COMMUTE-CONTINUE (JAM-A genuinely RESOLVED, not deferred)

r43 routed the JAM-A geometry — a settled topPerm crossing `crossingAt xpos` (`xpos < cupPos`) with a NONEMPTY distant
tail wedged behind it, e.g. `[cupAt 2, crossingAt 0, capAt 9]` — to `none` (`crossingLeftSettled` fires only when the
crossing is the SOLE right atom, `rest2 = []`).  The r42/r43 walls named this the "JAM-A commute-continue" residual.

This round DISCHARGES it, GENERIC in `cupPos`, `xpos`, and the distant tail.  The move is exactly the r41
`sinkDistantThenStraddle_arrives` geometry MINUS the straddle relabel: the settled `crossingAt xpos` (already left of the
cup by `xpos < cupPos`) COMMUTES rightward past the whole distant tail via the Godement `interchange`, the cup then
SINKS past the now-adjacent distant tail (`legPeelDistantTail`), and the appended settled crossing keeps
`regionArrivedExact = true` (`regionArrivedExact_ofPeelSnoc`, r41, ALREADY stated generic in `cupPos`/`xpos`).  This is
the printed positional/scheduled resolution (Kudryavtseva–Mazorchuk arXiv:1912.12869: commute the settled generator
rightward under a fixed strategy; the naive monomial order provably fails, the positional descent succeeds — here the
leg fuel drops `atomsRightOfFirstCup` on the sink):

  * ★ **`natLtOfBltExtract`** — `Nat.blt xpos cupPos = true → xpos < cupPos`, off the r43 `natLeOfBleExtract` (`Nat.blt`
    is `Nat.ble (·+1)` definitionally), propext-clean.
  * ★ **`swapSettledXposPastDistantStep`** — a settled `crossingAt xpos` (`xpos < cupPos`) commutes past ONE distant step
    of a `cupPos`-tail; the window `xpos + 2 ≤ q + 2` holds because `xpos < cupPos ≤ q`.
  * ★ **`commuteSettledXposPastTail`** — the generalized commute (the r41 `commuteSettledCrossingPastTail` at the
    straddle-fixed position `cupPos` generalized to any `xpos < cupPos`): `crossingAt xpos :: distantTailWord tail ~
    distantTailWord tail ++ [crossingAt xpos]`, structural on the tail.
  * ★★ **`sinkCrossingLeftNotExact_arrives`** — THE commute-continue rewrite: `cupAt cupPos :: crossingAt xpos ::
    distantTailWord tail` reduces to an EXACT-arrived region, GENERIC in `cupPos`/`xpos`/the tail.
  * ★★ **`outcomeArrivedFactoredCrossingLeftNotExact`** — the typed `RegionCupOutcome` (BRIDGE 1
    `capFreeRight_of_regionArrivedExact` turns the exact certificate into `cupIsCapFreeRight`), and
    **`flatRegionDispatchJamA`** — the flat dispatch that RECOGNIZES the JAM-A geometry from a flat word
    (`extractDistantTail` on the tail after the settled crossing) and synthesizes the arrived outcome, transported onto
    the actual word.  `[cupAt 2, crossingAt 0, capAt 9]` — the r43 JAM-A hostile — now RESOLVES to a `some` arrived
    outcome (`flatDispatchJamA_resolvesJamA`), where r43 could only route it to `none`.

## The honest wall — JAM-A is one MORE arm; the dispatch walls STAY false (adjudicated vs TEXT)

The commute-continue resolves the JAM-A geometry as a standalone typed arm, but it is NOT the full total dispatch: it is
one commute + one sink for a `crossingLeft`-not-exact word whose tail is ALREADY a clean distant tail, not the iterated
re-classification (sink one atom → re-classify → recurse under `legLexFuel`) that a total driver over an ARBITRARY region
needs, and it does not supply the reachability↔shape second ingredient, nor JAM-B (loop-with-suffix).  So
`fxBrauer_hasFlatRegionDispatchSynthesis`, `fxBrauer_hasRegionDriverTotalDispatch`, `fxBrauer_hasSingleCupTotalDecision`
STAY `false`, `fxBrauer_hasSingleCupPeelDischarged` STAYS `false` (a MULTI-CUP wall), and the five completeness masters
STAY `false`.  Purely additive; every residual is a route gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6;
Delpeuch–Vicary arXiv:1804.07832 Thm 10 — the interchange sub-phase is strongly normalizing under the inversion
measure the leg fuel instances).

Raw Lean 4 + Init; STRUCTURAL on the distant tail; the `interchange` transported position `q - 2 + 2` reduces
DEFINITIONALLY (no `Nat.sub` / `List.append_assoc`); the `< → ≤` bridge off `natLeOfBleExtract`; no `omega` / `simp`-AC /
`native_decide` / `WellFounded.fix` / `propext` / `Bool.and_eq_true` / `Nat.beq_refl`.  Per-declaration
`#assert_no_axioms` in the audit twin + an independent `#print axioms` witness file. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the `<`-bridge + the settled-crossing commutation past a distant tail (generalized to `xpos < cupPos`) -/

/-- `Nat.blt xpos cupPos = true → xpos < cupPos`, off the r43 `natLeOfBleExtract` (`Nat.blt n m` is `Nat.ble (n+1) m`
definitionally, so the `≤` bridge applies at `n + 1`).  propext-clean. -/
theorem natLtOfBltExtract (xpos cupPos : Nat) (settled : Nat.blt xpos cupPos = true) : xpos < cupPos :=
  natLeOfBleExtract (xpos + 1) cupPos settled

/-- ★ **A settled crossing at `xpos < cupPos` commutes past ONE distant step of a `cupPos`-tail.**  Each step decodes to
position `q + 2` with `q ≥ cupPos > xpos`, so the window `xpos + 2 ≤ q + 2` holds and the Godement `interchange` fires;
the crossing's `inputCount = 2` makes the transported position reduce definitionally. -/
theorem swapSettledXposPastDistantStep (cupPos xpos : Nat) (settled : Nat.blt xpos cupPos = true)
    (step : DistantSlideStep cupPos) :
    BrauerConvFree8 [crossingAt xpos, distantStepAtom step] [distantStepAtom step, crossingAt xpos] := by
  have xposLtCup : xpos < cupPos := natLtOfBltExtract xpos cupPos settled
  match step with
  | .crossing crossPos disjoint =>
      have xposLeCross : xpos ≤ crossPos := Nat.le_trans (Nat.le_of_lt xposLtCup) disjoint
      have windowFits : xpos + crossingWiring.inputCount ≤ crossPos + 2 :=
        Nat.add_le_add_right xposLeCross 2
      exact brauerConvFree8_ofFree
        (BrauerConvFree.interchange xpos (crossPos + 2) crossingWiring crossingWiring windowFits)
  | .cap capPos disjoint =>
      have xposLeCap : xpos ≤ capPos := Nat.le_trans (Nat.le_of_lt xposLtCup) disjoint
      have windowFits : xpos + crossingWiring.inputCount ≤ capPos + 2 :=
        Nat.add_le_add_right xposLeCap 2
      exact brauerConvFree8_ofFree
        (BrauerConvFree.interchange xpos (capPos + 2) crossingWiring capWiring windowFits)

/-- ★ **The settled crossing at `xpos < cupPos` commutes rightward past the WHOLE distant tail** — the r41
`commuteSettledCrossingPastTail` generalized off the straddle-fixed position.  Structural recursion:
`crossingAt xpos :: distantTailWord tail ~ distantTailWord tail ++ [crossingAt xpos]`. -/
theorem commuteSettledXposPastTail (cupPos xpos : Nat) (settled : Nat.blt xpos cupPos = true) :
    (tail : List (DistantSlideStep cupPos)) →
    BrauerConvFree8 (crossingAt xpos :: distantTailWord tail)
      (distantTailWord tail ++ [crossingAt xpos])
  | [] => brauerConvFree8_ofFree (BrauerConvFree.refl [crossingAt xpos])
  | step :: rest =>
      BrauerConvFree8.trans
        (BrauerConvFree8.whiskerRight (distantTailWord rest)
          (swapSettledXposPastDistantStep cupPos xpos settled step))
        (BrauerConvFree8.whiskerLeft [distantStepAtom step]
          (commuteSettledXposPastTail cupPos xpos settled rest))

/-! ## B — the commute-continue rewrite + the typed outcome -/

/-- ★★ **The `crossingLeft` NOT-exact COMMUTE-CONTINUE rewrite — JAM-A resolved, GENERIC.**  For a cup at `cupPos` with
a settled topPerm crossing `crossingAt xpos` (`xpos < cupPos`) then a distant tail: COMMUTE the settled crossing past the
distant tail (`commuteSettledXposPastTail`), then SINK the cup past the now-adjacent distant tail (`legPeelDistantTail`).
The result carries a real `BrauerConvFree8` reduction and is EXACT-arrived (`regionArrivedExact_ofPeelSnoc`, r41). -/
theorem sinkCrossingLeftNotExact_arrives (cupPos xpos : Nat) (settled : Nat.blt xpos cupPos = true)
    (tail : List (DistantSlideStep cupPos)) :
    BrauerConvFree8 (cupAt cupPos :: crossingAt xpos :: distantTailWord tail)
        ((legPeelDistantTail cupPos tail).1 ++ [crossingAt xpos])
      ∧ regionArrivedExact ((legPeelDistantTail cupPos tail).1 ++ [crossingAt xpos]) = true := by
  refine ⟨?_, ?_⟩
  · have commuteSettled : BrauerConvFree8
        (cupAt cupPos :: crossingAt xpos :: distantTailWord tail)
        (cupAt cupPos :: (distantTailWord tail ++ [crossingAt xpos])) :=
      BrauerConvFree8.whiskerLeft [cupAt cupPos] (commuteSettledXposPastTail cupPos xpos settled tail)
    have sinkCup : BrauerConvFree8
        (cupAt cupPos :: (distantTailWord tail ++ [crossingAt xpos]))
        ((legPeelDistantTail cupPos tail).1 ++ [crossingAt xpos]) :=
      BrauerConvFree8.whiskerRight [crossingAt xpos] (legPeelDistantTail cupPos tail).2.1
    exact commuteSettled.trans sinkCup
  · exact regionArrivedExact_ofPeelSnoc cupPos xpos settled tail

/-- ★★ **The typed JAM-A arrival provider.**  BRIDGE 1 (`capFreeRight_of_regionArrivedExact`) turns the exact
certificate into the `cupIsCapFreeRight` the `.arrivedFactored` fate needs, so the whole `crossingLeft`-not-exact arm is
a genuine `RegionCupOutcome`, GENERIC in `cupPos`, `xpos`, and the distant tail. -/
def outcomeArrivedFactoredCrossingLeftNotExact (cupPos xpos : Nat) (settled : Nat.blt xpos cupPos = true)
    (tail : List (DistantSlideStep cupPos)) :
    RegionCupOutcome (cupAt cupPos :: crossingAt xpos :: distantTailWord tail) :=
  RegionCupOutcome.arrivedFactored ((legPeelDistantTail cupPos tail).1 ++ [crossingAt xpos])
    (sinkCrossingLeftNotExact_arrives cupPos xpos settled tail).1
    (capFreeRight_of_regionArrivedExact _ (sinkCrossingLeftNotExact_arrives cupPos xpos settled tail).2)

/-! ## C — the flat dispatch recognizing the JAM-A geometry -/

/-- ★★ **The flat JAM-A dispatch.**  Recognizes a head-cup word `cupAt cupPos :: crossingAt xpos :: <distant tail>` with
`xpos < cupPos` (a settled topPerm crossing, then a genuine distant tail via `extractDistantTail`) and synthesizes the
arrived outcome by `outcomeArrivedFactoredCrossingLeftNotExact`, transported onto the ACTUAL word by the shipped
explicit-motive `Eq.rec`.  Fires exactly on the JAM-A geometry r43 routed to `none`; every other word → `none`. -/
def flatRegionDispatchJamA (word : List BrauerAtom) : Option (RegionCupOutcome word) :=
  match word with
  | [] => none
  | [_] => none
  | cup :: next :: rest2 =>
      if hcup : cup.wiring = cupWiring then
        if hcross : next.wiring = crossingWiring then
          if hlt : Nat.blt next.position cup.position = true then
            match extractDistantTail cup.position rest2 with
            | some ⟨tail, hrest⟩ =>
                some (RegionCupOutcome.transportByRegionEq
                  (by
                    show cupAt cup.position :: crossingAt next.position :: distantTailWord tail
                          = cup :: next :: rest2
                    rw [hrest, crossingAt_of_wiring next hcross, cupAt_of_wiring cup hcup])
                  (outcomeArrivedFactoredCrossingLeftNotExact cup.position next.position hlt tail))
            | none => none
          else none
        else none
      else none

/-- ★★ **The JAM-A hostile now RESOLVES, machine-checked by `rfl`.**  The r43 JAM-A word `[cupAt 2, crossingAt 0,
capAt 9]` (a settled crossing with a distant cap wedged behind it), which r43 routed to `none`, now synthesizes a `some`
arrived outcome through the commute-continue; a deeper JAM-A `[cupAt 3, crossingAt 1, crossingAt 5, capAt 8]` also
resolves.  A non-JAM word (`[cupAt 0, crossingAt 1]`, the straddle, distinct geometry) routes to `none` here (handled by
the r43 straddle arm elsewhere). -/
theorem flatDispatchJamA_resolvesJamA :
    (flatRegionDispatchJamA [cupAt 2, crossingAt 0, capAt 9]).isSome = true
      ∧ (flatRegionDispatchJamA [cupAt 3, crossingAt 1, crossingAt 5, capAt 8]).isSome = true
      ∧ (flatRegionDispatchJamA [cupAt 0, crossingAt 1]).isNone = true :=
  ⟨rfl, rfl, rfl⟩

/-- ★ **The JAM-A outcome carries the ARRIVED fate, machine-checked.**  The commute-continue lands a genuine
`.arrivedFactored`, generic in `cupPos`/`xpos`/the tail — pinned at a fresh `[cupAt 5, crossingAt 2, capAt 9]`. -/
theorem outcomeArrivedFactoredCrossingLeftNotExact_fate :
    (outcomeArrivedFactoredCrossingLeftNotExact 5 2 (by decide) [.cap 7 (by decide)]).fate
      = SingleCupFate.arrivedFate := rfl

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the `crossingLeft` NOT-exact COMMUTE-CONTINUE SHIPS (Q3, JAM-A genuinely RESOLVED).**  The
generalized commute (`swapSettledXposPastDistantStep` / `commuteSettledXposPastTail`) sinks a settled crossing at
`xpos < cupPos` past the whole distant tail; `sinkCrossingLeftNotExact_arrives` composes the sink into an exact-arrived
rewrite GENERIC in `cupPos`/`xpos`/the tail; `outcomeArrivedFactoredCrossingLeftNotExact` / `flatRegionDispatchJamA`
turn it into a typed `RegionCupOutcome` recognized from the flat word.  `flatDispatchJamA_resolvesJamA` resolves the
r43 JAM-A hostile `[cupAt 2, crossingAt 0, capAt 9]` to a `some` arrived outcome — where r43 routed it to `none`.  All
zero-axiom.  `= true`. -/
def fxBrauer_hasCrossingLeftCommuteContinue : Bool := true

/-- **Honesty WALL marker — JAM-A is one MORE arm; the dispatch walls STAY `false` (adjudicated vs the wall TEXT).**  The
commute-continue resolves the JAM-A geometry as a standalone typed arm, but it is not the total dispatch: it handles a
`crossingLeft`-not-exact word whose tail is ALREADY a clean distant tail, not the iterated re-classification a total
driver over an ARBITRARY region needs, and it supplies neither the reachability↔shape second ingredient nor JAM-B
(loop-with-suffix).  So `fxBrauer_hasFlatRegionDispatchSynthesis`, `fxBrauer_hasRegionDriverTotalDispatch`, and
`fxBrauer_hasSingleCupTotalDecision` STAY `false`, `fxBrauer_hasSingleCupPeelDischarged` STAYS `false` (a MULTI-CUP
wall), and the five completeness / inner-descent masters STAY `false`.  A route gap, never a truth gap (Lehrer–Zhang
arXiv:1207.5889 Thm 2.6).  `= false`. -/
def fxBrauer_hasCrossingLeftCommuteContinueGap : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r44 crossingLeft-commute-continue terminal state — MACHINE-CHECKED.**  The new marker records that
the JAM-A commute-continue SHIPS (`fxBrauer_hasCrossingLeftCommuteContinue = true`) on top of the r44 snake arms
(`fxBrauer_hasFlatSnakeArms = true`) and the r43 flat extractor (`fxBrauer_hasFlatDescriptorExtractor = true`), while the
flat-word synthesis stays unbuilt — so the three dispatch walls (`fxBrauer_hasFlatRegionDispatchSynthesis`,
`fxBrauer_hasRegionDriverTotalDispatch`, `fxBrauer_hasSingleCupTotalDecision`), the multi-cup peel discharge
(`fxBrauer_hasSingleCupPeelDischarged`), and the five completeness / inner-descent masters
(`fxBrauer_hasSeamRungOuterAssembly`, `fxBrauer_hasStagedInnerDescentDischarged`, `fxBrauer_hasFreeBrauerStraighteningNF`,
`fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness`) all STAY `false`.  A `rfl`-conjunction the
kernel checks; purely additive, no wall flip is fabricated. -/
theorem fxBrauer_crossingLeftCommuteContinueTerminalState :
    fxBrauer_hasCrossingLeftCommuteContinue = true
      ∧ fxBrauer_hasFlatSnakeArms = true
      ∧ fxBrauer_hasFlatDescriptorExtractor = true
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

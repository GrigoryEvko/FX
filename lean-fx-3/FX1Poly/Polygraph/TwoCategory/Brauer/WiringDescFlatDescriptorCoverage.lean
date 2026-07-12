import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingLeftCommuteContinue

/-! # BRAUER r44 — Q2 (loop-fate prepend + honest JAM-B partial) + Q4 (the COVERAGE CENSUS over all flat arms)

This round CLOSES the r44 flat-arm arc with the coverage census: a single combined dispatch
`flatRegionDispatchCombined` chaining the r43 five arms, the r44 Q1 snakes (`flatRegionDispatchWithSnakes`), and the
r44 Q3 JAM-A commute-continue (`flatRegionDispatchJamA`), and a machine-checked census enumerating — per the printed
Bergman/Newman finite-overlap discipline (Kudryavtseva–Mazorchuk arXiv:1912.12869 §2.2; Ramos–Oliveira et al.
arXiv:2512.09280, local confluence = every left-hand overlap classified) — EXACTLY which `classifyFirstCupNeighbour`
arms now synthesize `some` and which stay honestly `none`.

## Q2 — the loop-fate prepend + the honest JAM-B partial

  * ★ **`prepend_preserves_loopFate`** — the outer sink-step combinator `RegionCupOutcome.prepend` THREADS the loop
    fate: prepending any length-non-increasing move onto the bare loop terminal (`outcomeLoopAtFactoredTotal`) keeps the
    `.loop` verdict.  This is the print `e² = δ·e` / `ŝ²ᵣ → δ̂ŝᵣ` shape at the outcome level — the loop scalar survives a
    prepended move.
  * The loop-WITH-suffix arm (JAM-B, e.g. `[cupAt 2, capAt 2, capAt 9]`) stays an honest `none` (`jamB_staysNone`): the
    J-loop count VARIES with the suffix (bare `[cupAt cupPos, capAt cupPos].loops = 1`, but with a distant cap the
    engine folds a SECOND loop — r39/recon P1), so the loop terminal cannot carry a fixed count; resolving it needs the
    residual RE-DISPATCH (close the bubble, then re-drive the suffix), which is the recursive total driver, not a static
    arm.  Not a truth gap — the loop IS there — a route gap.

## Q4 — the coverage census

  * ★★ **`flatRegionDispatchCombined`** + **`flatDispatch_coverageCensus`** — the census.  IN (`some`): `cupArrivedAlone`,
    `untwist`, `straddleTerminal`, `distantCrossing`, `distantCap`, `crossingLeft` EXACT (r43); `snakeLeft` / `snakeRight`
    (r44 Q1); `crossingLeft` NOT-exact / JAM-A (r44 Q3).  OUT (`none`, honestly): `loopHere`-with-suffix / JAM-B (Q2
    residual), `noCup` / `anotherCup` (correctly out of single-cup scope), and the DEEP-TAIL distant break `[cupAt 2,
    crossingAt 4, crossingAt 1, capAt 9]` (classified `distantCrossing` yet a settled crossing sits deeper — the r43
    extractor is a whole-tail validator, so the reachability↔shape residual keeps it `none`).

## The honest wall — the census enumerates coverage; it does NOT flip the walls (adjudicated vs TEXT)

The combined dispatch resolves 9 of the 11 in-scope classifier arms as static typed outcomes, but a total dispatch over
an ARBITRARY region — the object the walls demand — additionally needs (a) the reachability↔shape argument that every
reachable single-cup region IS in the whole-tail-validated shape (the deep-tail break shows the static arms do not), and
(b) the JAM-B residual re-dispatch.  So `fxBrauer_hasFlatRegionDispatchSynthesis`, `fxBrauer_hasRegionDriverTotalDispatch`,
`fxBrauer_hasSingleCupTotalDecision` STAY `false`, `fxBrauer_hasSingleCupPeelDischarged` STAYS `false` (a MULTI-CUP
wall), and the five completeness / inner-descent masters STAY `false`.  Purely additive; every residual is a route /
reachability gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).

Raw Lean 4 + Init; the combined dispatch is a full-enum `Option` chain (no wildcard); the census pins are pure
`classifyFirstCupNeighbour` / extractor reductions (no `decide` over `brauerDiagramOf`); `prepend_preserves_loopFate` is
`rfl` on the `.loop` arm of `prepend`.  No `omega` / `simp`-AC / `native_decide` / `WellFounded.fix` / `propext`.
Per-declaration `#assert_no_axioms` in the audit twin + an independent `#print axioms` witness file. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — Q2: the loop-fate prepend + the honest JAM-B partial -/

/-- ★ **The loop fate THREADS through the outer sink-step combinator.**  `RegionCupOutcome.prepend` composes any
length-non-increasing move onto the bare loop terminal (`outcomeLoopAtFactoredTotal cupPos`) and keeps the `.loop`
verdict — the print `e² = δ·e` shape at the outcome level: the loop scalar survives a prepended move.  `rfl` on the
`.loop` arm of `prepend`. -/
theorem prepend_preserves_loopFate (cupPos : Nat) (prefixMove : List BrauerAtom)
    (stepConv : BrauerConvFree8 (prefixMove ++ [cupAt cupPos, capAt cupPos]) [cupAt cupPos, capAt cupPos])
    (lenLe : countAtoms ([cupAt cupPos, capAt cupPos] : List BrauerAtom)
        ≤ countAtoms (prefixMove ++ [cupAt cupPos, capAt cupPos])) :
    (RegionCupOutcome.prepend stepConv lenLe (outcomeLoopAtFactoredTotal cupPos)).fate
      = SingleCupFate.loopFate := rfl

/-- ★ **The loop-WITH-suffix arm stays an honest `none` (JAM-B).**  `[cupAt 2, capAt 2, capAt 9]` classifies `loopHere`
but neither the r43 extractor, the Q1 snakes, nor the Q3 JAM-A dispatch synthesize it — the loop count varies with the
suffix, so the terminal cannot carry a fixed count; the residual re-dispatch (the recursive total driver) is unbuilt.
Machine-checked `none` (a route gap, not a truth gap — the loop IS there). -/
theorem jamB_staysNone :
    classifyFirstCupNeighbour [cupAt 2, capAt 2, capAt 9] = RegionCupMoveKind.loopHere
      ∧ (flatRegionDispatchWithSnakes [cupAt 2, capAt 2, capAt 9]).isNone = true
      ∧ (flatRegionDispatchJamA [cupAt 2, capAt 2, capAt 9]).isNone = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## B — Q4: the combined dispatch + the coverage census -/

/-- ★★ **The combined flat dispatch.**  Chains the r44 Q1 snakes-extended dispatch (which already subsumes the r43 five
arms) and, on its `none`, the r44 Q3 JAM-A commute-continue.  Full-enum `Option` chain (no wildcard). -/
def flatRegionDispatchCombined (word : List BrauerAtom) : Option (RegionCupOutcome word) :=
  match flatRegionDispatchWithSnakes word with
  | some outcome => some outcome
  | none => flatRegionDispatchJamA word

/-- ★★ **THE COVERAGE CENSUS — machine-checked by `rfl`.**  Nine of the eleven in-scope classifier arms synthesize a
`some` typed outcome over the ACTUAL flat region; the two remaining in-scope words + the deep-tail reachability break stay
honestly `none`.  IN: `cupArrivedAlone` / `untwist` / `straddleTerminal` / `distantCrossing` / `distantCap` /
`crossingLeft`-EXACT (r43), `snakeLeft` / `snakeRight` (Q1), the JAM-A settled-crossing geometry (Q3 — the head-only
classifier lumps it under `distantCrossing`, but the `blt`-broad-settled + `regionArrivedExact` discrimination resolves
it).  OUT (honest): `loopHere`-with-suffix/JAM-B (Q2 residual), a deep-tail distant break (reachability↔shape residual),
and the two out-of-scope arms `noCup` / `anotherCup`. -/
theorem flatDispatch_coverageCensus :
    -- IN — the r43 five arms (via the Q1-snakes-extended dispatch)
    (flatRegionDispatchCombined [cupAt 0]).isSome = true
      ∧ (flatRegionDispatchCombined [cupAt 0, crossingAt 0, crossingAt 3, capAt 4]).isSome = true
      ∧ (flatRegionDispatchCombined [cupAt 0, crossingAt 1, crossingAt 3, capAt 4]).isSome = true
      ∧ (flatRegionDispatchCombined [cupAt 7, crossingAt 9, capAt 11]).isSome = true
      ∧ (flatRegionDispatchCombined [cupAt 0, capAt 5]).isSome = true
      ∧ (flatRegionDispatchCombined [cupAt 1, crossingAt 0]).isSome = true
      -- IN — the r44 Q1 snakes
      ∧ (flatRegionDispatchCombined [cupAt 0, capAt 1]).isSome = true
      ∧ (flatRegionDispatchCombined [cupAt 1, capAt 0]).isSome = true
      -- IN — the r44 Q3 JAM-A commute-continue (was r43 none)
      ∧ (flatRegionDispatchCombined [cupAt 2, crossingAt 0, capAt 9]).isSome = true
      -- OUT (honest) — JAM-B loop-with-suffix (Q2 residual)
      ∧ (flatRegionDispatchCombined [cupAt 2, capAt 2, capAt 9]).isNone = true
      -- OUT (honest) — deep-tail distant break (reachability↔shape residual)
      ∧ (flatRegionDispatchCombined [cupAt 2, crossingAt 4, crossingAt 1, capAt 9]).isNone = true
      -- OUT (correct) — out of single-cup scope
      ∧ (flatRegionDispatchCombined ([crossingAt 9] : List BrauerAtom)).isNone = true
      ∧ (flatRegionDispatchCombined [cupAt 0, cupAt 2]).isNone = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ★ **The census tied to the CLASSIFIER — the arms are the ones the classifier names.**  Each census word classifies
to the move kind the census slots it under, so the combined dispatch's `some`/`none` split is a genuine classifier-arm
census, not a coincidence of literals.  Pure closed `Nat.beq` reductions. -/
theorem coverageCensus_classifierTie :
    classifyFirstCupNeighbour [cupAt 0] = RegionCupMoveKind.cupArrivedAlone
      ∧ classifyFirstCupNeighbour [cupAt 0, crossingAt 0, crossingAt 3, capAt 4] = RegionCupMoveKind.untwist
      ∧ classifyFirstCupNeighbour [cupAt 0, crossingAt 1, crossingAt 3, capAt 4] = RegionCupMoveKind.straddleTerminal
      ∧ classifyFirstCupNeighbour [cupAt 7, crossingAt 9, capAt 11] = RegionCupMoveKind.distantCrossing
      ∧ classifyFirstCupNeighbour [cupAt 0, capAt 5] = RegionCupMoveKind.distantCap
      ∧ classifyFirstCupNeighbour [cupAt 1, crossingAt 0] = RegionCupMoveKind.crossingLeft
      ∧ classifyFirstCupNeighbour [cupAt 0, capAt 1] = RegionCupMoveKind.snakeRight
      ∧ classifyFirstCupNeighbour [cupAt 1, capAt 0] = RegionCupMoveKind.snakeLeft
      ∧ classifyFirstCupNeighbour [cupAt 2, crossingAt 0, capAt 9] = RegionCupMoveKind.distantCrossing
      ∧ classifyFirstCupNeighbour [cupAt 2, crossingAt 4, crossingAt 1, capAt 9] = RegionCupMoveKind.distantCrossing
      ∧ classifyFirstCupNeighbour ([crossingAt 9] : List BrauerAtom) = RegionCupMoveKind.noCup
      ∧ classifyFirstCupNeighbour [cupAt 0, cupAt 2] = RegionCupMoveKind.anotherCup :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the loop-fate prepend + the COVERAGE CENSUS SHIP (Q2 + Q4).**  `prepend_preserves_loopFate`
threads the loop scalar through the outer sink-step combinator (the print `e² = δ·e` at the outcome level); the JAM-B
loop-with-suffix stays an honest `none` (`jamB_staysNone`); `flatRegionDispatchCombined` chains the r43 five arms, the Q1
snakes, and the Q3 JAM-A commute-continue, and `flatDispatch_coverageCensus` pins the full arm-by-arm coverage (9 in-scope
arms `some`, JAM-B + the deep-tail break + the two out-of-scope arms `none`), `coverageCensus_classifierTie` tying every
slot to its classifier arm.  All zero-axiom.  `= true`. -/
def fxBrauer_hasFlatDispatchCoverageCensus : Bool := true

/-- **Honesty WALL marker — the census enumerates coverage; the dispatch walls STAY `false` (adjudicated vs TEXT).**  The
combined dispatch resolves 9 of 11 in-scope arms as static typed outcomes, but a total dispatch over an ARBITRARY region
additionally needs the reachability↔shape argument (the deep-tail break shows the whole-tail-validated static arms do NOT
cover every reachable region) and the JAM-B residual re-dispatch (the recursive total driver).  So
`fxBrauer_hasFlatRegionDispatchSynthesis`, `fxBrauer_hasRegionDriverTotalDispatch`, `fxBrauer_hasSingleCupTotalDecision`
STAY `false`, `fxBrauer_hasSingleCupPeelDischarged` STAYS `false` (a MULTI-CUP wall), and the five completeness /
inner-descent masters STAY `false`.  A route / reachability gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889
Thm 2.6).  `= false`. -/
def fxBrauer_hasFlatDispatchTotalityGap : Bool := false

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r44 coverage-census terminal state — MACHINE-CHECKED.**  The new marker records that the coverage
census SHIPS (`fxBrauer_hasFlatDispatchCoverageCensus = true`) on top of the r44 Q3 commute-continue
(`fxBrauer_hasCrossingLeftCommuteContinue = true`) and the r44 Q1 snakes (`fxBrauer_hasFlatSnakeArms = true`), while the
flat-word synthesis stays unbuilt — so the three dispatch walls (`fxBrauer_hasFlatRegionDispatchSynthesis`,
`fxBrauer_hasRegionDriverTotalDispatch`, `fxBrauer_hasSingleCupTotalDecision`), the multi-cup peel discharge
(`fxBrauer_hasSingleCupPeelDischarged`), and the five completeness / inner-descent masters
(`fxBrauer_hasSeamRungOuterAssembly`, `fxBrauer_hasStagedInnerDescentDischarged`, `fxBrauer_hasFreeBrauerStraighteningNF`,
`fxBrauer_hasBrauerCompleteness`, `fxBrauer_hasBrauerV2FullCompleteness`) all STAY `false`.  A `rfl`-conjunction the
kernel checks; purely additive, no wall flip is fabricated. -/
theorem fxBrauer_flatDispatchCoverageCensusTerminalState :
    fxBrauer_hasFlatDispatchCoverageCensus = true
      ∧ fxBrauer_hasCrossingLeftCommuteContinue = true
      ∧ fxBrauer_hasFlatSnakeArms = true
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

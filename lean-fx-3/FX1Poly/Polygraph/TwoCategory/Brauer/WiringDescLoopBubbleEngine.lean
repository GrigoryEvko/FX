import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescSingleCupEagerDriver

/-! # BRAUER r41 — J-loop: the `cupPos`-generic loop-bubble non-emptiness, discharged by an ENGINE induction

r39 (`Brauer/WiringDescSingleCupRegionDriver.lean`) routed a loop bubble to the `bottomCount = 0` circle class via
`outcomeLoopAtFactored`, but that builder TOOK the non-emptiness `brauerDiagramOf 0 [cupAt cupPos, capAt cupPos] ≠
brauerDiagramOf 0 []` AS A HYPOTHESIS — a per-literal `decide` at each `cupPos`, never a proof GENERIC in `cupPos`
(the r39/r40 wall's J-loop residual: "with a suffix the loop count even varies").

This round discharges that residual with a genuine ENGINE lemma over `stepCup` / `stepCap` / `extractDiagram` — NOT a
`decide` over `brauerDiagramOf` (which the recon forbids on long words), but a STRUCTURAL computation on `cupPos`:

  * ★★ **`loopBubbleProcessLoops`** — `(processBrauer (brauerSeed 0) [cupAt cupPos, capAt cupPos]).loops = 1`, GENERIC
    in `cupPos`, by structural cases `0 | 1 | _ + 2`.  The cup (a `0 ⇒ 2` unit from the EMPTY seed) allocates two
    connected fresh wires INDEPENDENT of `cupPos` (`natListInsertAt [] cupPos [0,1] = [0,1]`); the cap
    (`natListSliceAt [0,1] cupPos 2`) reads two wires at `cupPos ∈ {0,1}` and the two `natListGetAt` DEFAULTS at
    `cupPos ≥ 2`, all landing in the SAME component `[(0,1)]`, so `stepCap` takes its loop branch and increments
    `loops` once.  Every case is one kernel reduction (a two-atom word, never a `decide`).
  * ★ **`loopBubbleLoopsEqOne`** — the same read off `brauerDiagramOf` (`extractDiagram` copies `state.loops`).
  * ★★ **`loopBubbleNotEmpty`** — `brauerDiagramOf 0 [cupAt cupPos, capAt cupPos] ≠ brauerDiagramOf 0 []`, GENERIC in
    `cupPos`: the left diagram has `loops = 1`, the empty diagram has `loops = 0`, so `congrArg DiagramType.loops`
    forces `1 = 0`, refuted by `Nat.noConfusion` (never `Nat.succ_ne_zero`, which leaks `propext`).  The J-loop
    residual CLOSED.
  * ★ **`outcomeLoopAtFactoredTotal`** — the r39 `outcomeLoopAtFactored` with its non-emptiness hypothesis DISCHARGED:
    a TOTAL loop-outcome builder `RegionCupOutcome [cupAt cupPos, capAt cupPos]` needing no witness, so the eager
    dispatch's `.terminalLoop` arm can now build its typed outcome at ANY `cupPos`.

## The honest wall — the TOTAL typed dispatch is STILL NOT built (J-loop closed, J-transport + assembly remain)

J-loop is discharged, but the TOTAL region DISPATCH (synthesizing the typed `RegionCupOutcome` from
`classifyFirstCupNeighbour`'s decision over an ARBITRARY flat region) stays open on J-transport (the per-arm
`Nat.beq _ _ = true → _ = _` positional reshape + `Eq.rec` transport across the cons-indexed family) and the total
assembly threading all 11 arms.  So `fxBrauer_hasRegionDriverTotalDispatch`, `fxBrauer_hasSingleCupTotalDecision`,
`fxBrauer_hasSingleCupPeelDischarged`, and the four completeness / inner-descent masters
(`fxBrauer_hasStagedInnerDescentDischarged`, `fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`,
`fxBrauer_hasBrauerV2FullCompleteness`) all STAY `false`; this round is PURELY ADDITIVE, no master flip is fabricated.
Every residual is a route / engine-lemma gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).

Raw Lean 4 + Init; STRUCTURAL recursion on `cupPos` (no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix` /
`propext` — `Nat.succ_ne_zero`, `Nat.beq_refl`, `Nat.sub_*` leak `propext`, so `Nat.noConfusion` and the two-atom
kernel reductions are used instead).  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the ENGINE loop-count lemma, generic in `cupPos` -/

/-- ★★ **`(processBrauer (brauerSeed 0) [cupAt cupPos, capAt cupPos]).loops = 1`, GENERIC in `cupPos`.**  Structural
cases `0 | 1 | _ + 2`: the cup allocates two connected wires `[0,1]` independent of `cupPos` (empty seed), the cap reads
a same-component pair (or the `natListGetAt` defaults land on the same component `[(0,1)]`), so `stepCap` closes exactly
one loop.  Each case is a single kernel reduction over a two-atom word — never a `decide` over `brauerDiagramOf`. -/
theorem loopBubbleProcessLoops : (cupPos : Nat) →
    (processBrauer (brauerSeed 0) [cupAt cupPos, capAt cupPos]).loops = 1
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- ★ **`(brauerDiagramOf 0 [cupAt cupPos, capAt cupPos]).loops = 1`, generic in `cupPos`.**  `extractDiagram` copies
`state.loops`, so the engine lemma reads straight off the diagram. -/
theorem loopBubbleLoopsEqOne (cupPos : Nat) :
    (brauerDiagramOf 0 [cupAt cupPos, capAt cupPos]).loops = 1 := by
  show (processBrauer (brauerSeed 0) [cupAt cupPos, capAt cupPos]).loops = 1
  exact loopBubbleProcessLoops cupPos

/-- ★★ **The `cupPos`-generic loop non-emptiness — the J-loop residual CLOSED.**  The loop bubble
`[cupAt cupPos, capAt cupPos]` is genuinely NOT the empty diagram at ANY `cupPos`: its `loops = 1` (`loopBubbleLoopsEqOne`)
while the empty diagram's `loops = 0`, so `congrArg DiagramType.loops` forces `1 = 0`, refuted by `Nat.noConfusion`. -/
theorem loopBubbleNotEmpty (cupPos : Nat) :
    brauerDiagramOf 0 [cupAt cupPos, capAt cupPos] ≠ brauerDiagramOf 0 ([] : List BrauerAtom) := by
  intro isEqualDiagram
  have loopsAgree := congrArg DiagramType.loops isEqualDiagram
  have leftLoopsOne := loopBubbleLoopsEqOne cupPos
  have oneEqZero : (1 : Nat) = 0 := leftLoopsOne.symm.trans loopsAgree
  exact Nat.noConfusion oneEqZero

/-! ## B — the TOTAL loop-outcome builder (r39 hypothesis discharged) -/

/-- ★ **The loop terminal, TOTAL and GENERIC in `cupPos`.**  The r39 `outcomeLoopAtFactored` with its non-emptiness
hypothesis discharged by `loopBubbleNotEmpty` — a typed `RegionCupOutcome [cupAt cupPos, capAt cupPos]` needing no
witness, so the eager dispatch's `.terminalLoop` arm builds its typed outcome at ANY `cupPos`. -/
def outcomeLoopAtFactoredTotal (cupPos : Nat) : RegionCupOutcome [cupAt cupPos, capAt cupPos] :=
  outcomeLoopAtFactored cupPos (loopBubbleNotEmpty cupPos)

/-- ★ **The total loop outcome carries the loop fate** — machine-checked at a fresh `cupPos = 4`. -/
theorem outcomeLoopAtFactoredTotal_fate : (outcomeLoopAtFactoredTotal 4).fate = SingleCupFate.loopFate := rfl

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the J-loop engine lemma SHIPS (the `cupPos`-generic non-emptiness CLOSED).**
`loopBubbleProcessLoops` computes `(processBrauer (brauerSeed 0) [cupAt cupPos, capAt cupPos]).loops = 1` generically by
structural cases over `stepCup` / `stepCap`, `loopBubbleLoopsEqOne` reads it off `brauerDiagramOf`, and
`loopBubbleNotEmpty` refutes emptiness at ANY `cupPos` (`1 ≠ 0` via `Nat.noConfusion`); `outcomeLoopAtFactoredTotal`
turns the r39 hypothesis-taking loop builder into a TOTAL one.  The J-loop residual the r39/r40 walls named, discharged
by a genuine engine induction, not a per-literal `decide`.  `= true`. -/
def fxBrauer_hasLoopBubbleEngineLemma : Bool := true

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r41 loop-bubble-engine terminal state — MACHINE-CHECKED.**  The new J-loop marker is `true` (the
generic loop-count engine lemma + the total loop outcome), built on the r39 factored cup arrival / region classifier
and the r38 outcome driver, while the total region dispatch (r39), the r38 total decision, the r36 single-cup peel
discharge, and all four completeness / inner-descent masters STAY `false`.  A `rfl`-conjunction the kernel checks;
purely additive, no master flip is fabricated. -/
theorem fxBrauer_loopBubbleEngineTerminalState :
    fxBrauer_hasLoopBubbleEngineLemma = true
      ∧ fxBrauer_hasEagerRegionDispatch = true
      ∧ fxBrauer_hasFactoredCupArrival = true
      ∧ fxBrauer_hasRegionCupClassifier = true
      ∧ fxBrauer_hasRegionDriverTotalDispatch = false
      ∧ fxBrauer_hasSingleCupTotalDecision = false
      ∧ fxBrauer_hasSingleCupPeelDischarged = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph

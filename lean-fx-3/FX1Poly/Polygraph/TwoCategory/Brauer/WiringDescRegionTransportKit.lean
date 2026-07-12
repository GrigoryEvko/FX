import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStraddleSinkOrdered

/-! # BRAUER r41 — J-transport: the outcome-reshape plumbing is CLEAN (the "propext minefield" REFUTED)

The r39/r40 walls named J-transport as the residual "the `Eq.rec`/`▸` plumbing across a cons-indexed family the memory
corpus flags as a `propext` minefield (cons-index match + ▸)".  This round REFUTES that framing in code: the transport
is a single `Eq.rec` with an EXPLICIT motive `fun w _ => RegionCupOutcome w`, machine-checked zero-axiom — the memory
corpus leak comes from PARTIAL cons-index MATCH ARMS, never from `Eq.rec` with a supplied motive.  The only real work is
the atom-RECONSTRUCTION that feeds the transport a proven positional word equality, and it too is zero-axiom (a
hand-rolled `&&`-split — `Bool.and_eq_true` leaks `propext` — plus `Nat.eq_of_beq_eq_true`, a list-of-pairs inversion,
and structure eta):

  * ★★ **`RegionCupOutcome.transportByRegionEq`** — THE reshape combinator: retype a `RegionCupOutcome regionA` to
    `RegionCupOutcome regionB` across a proven `regionA = regionB` via `@Eq.rec … (fun w _ => RegionCupOutcome w) …`.
    Zero-axiom; the "propext minefield" refuted.
  * ★ **`andEqTrue_left` / `andEqTrue_right`** — the hand-rolled `&&`-split (`Bool.and_eq_true` leaks `propext`, so
    `cases` + `Bool.noConfusion` is used instead).
  * ★ **`arcsAreCrossing_reconstruct` / `crossingWiring_reconstruct`** — recover `arcs = [(0,3),(1,2)]` and the full
    `crossingWiring` from the four `isCrossingWiring` conjuncts (a list-of-pairs inversion + `Nat.eq_of_beq_eq_true` +
    structure eta, no `Nat.sub` / `List.append_assoc`).
  * ★★ **`crossingAtom_reconstruct`** — the representative arm's atom reconstruction: `isCrossingAtom a = true` and
    `Nat.beq a.position p = true` reconstruct `a = crossingAt p`.  (The crossing is the fully-pinned representative — its
    `isCrossingWiring` fixes every wiring field; the classifier's `crossingLeft` / `untwist` / `distantCrossing` arms
    all reshape a crossing.)
  * ★★ **`transportCrossingHead`** — the per-arm reshape composed: retype a builder outcome
    `RegionCupOutcome (crossingAt p :: rest)` to the region's ACTUAL head `RegionCupOutcome (a :: rest)` via the
    reconstruction + the transport.  The dispatch-arm plumbing the walls named, built and machine-checked zero-axiom.

## The honest wall — the TOTAL typed dispatch is STILL NOT built (J-loop + J-geometry + J-transport clean; assembly remains)

All three r41 residuals are discharged as bricks — the J-loop engine lemma, the J-geometry ordered rewrite, and the
J-transport reshape — but the TOTAL region DISPATCH is still not one function: it needs the ASSEMBLY threading all 11
classifier arms (each reshaped by `transportCrossingHead`-style plumbing) plus the `RegionCupOutcome` whiskering under
the classifier-skipped CUPLESS PREFIX (`prependCuplessPrefix`, via the shipped `atomsRightOfFirstCup_prefixCupless` /
`straddleBitAtFirstCup_prefixCupless` invariants) into a single structural `totalDispatch : (word) → InScope →
RegionCupOutcome word`.  So `fxBrauer_hasRegionDriverTotalDispatch`, `fxBrauer_hasSingleCupTotalDecision`,
`fxBrauer_hasSingleCupPeelDischarged`, and the four completeness / inner-descent masters
(`fxBrauer_hasStagedInnerDescentDischarged`, `fxBrauer_hasFreeBrauerStraighteningNF`, `fxBrauer_hasBrauerCompleteness`,
`fxBrauer_hasBrauerV2FullCompleteness`) all STAY `false`; this round is PURELY ADDITIVE, no master flip is fabricated.
Every residual is a route / assembly gap, never a truth gap (Lehrer–Zhang arXiv:1207.5889 Thm 2.6).

Raw Lean 4 + Init; `Eq.rec` with an explicit motive (no `▸` in a rewrite context), hand-rolled `&&`-split + structure
recursion (no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix` / `propext` — `Bool.and_eq_true`, `Nat.sub_*`,
`List.append_assoc` all leak `propext` and are avoided).  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A — the reshape combinator (the "propext minefield" refuted) -/

/-- ★★ **The outcome reshape combinator.**  Retype a `RegionCupOutcome regionA` to `RegionCupOutcome regionB` across a
proven `regionA = regionB` via `Eq.rec` with an EXPLICIT motive `fun w _ => RegionCupOutcome w` — zero-axiom (the memory
corpus's `propext` leak comes from partial cons-index MATCH arms, not from `Eq.rec` with a supplied motive). -/
def RegionCupOutcome.transportByRegionEq {regionA regionB : List BrauerAtom}
    (regionEq : regionA = regionB) (outcome : RegionCupOutcome regionA) : RegionCupOutcome regionB :=
  @Eq.rec (List BrauerAtom) regionA (fun w _ => RegionCupOutcome w) outcome regionB regionEq

/-! ## B — the hand-rolled `&&`-split (`Bool.and_eq_true` leaks `propext`) -/

/-- From `(left && right) = true`, the left is `true` (hand-rolled; `Bool.and_eq_true` leaks `propext`). -/
theorem andEqTrue_left {left right : Bool} (bothTrue : (left && right) = true) : left = true := by
  cases left with
  | true => rfl
  | false => exact Bool.noConfusion bothTrue

/-- From `(left && right) = true`, the right is `true`. -/
theorem andEqTrue_right {left right : Bool} (bothTrue : (left && right) = true) : right = true := by
  cases left with
  | true => exact bothTrue
  | false => exact Bool.noConfusion bothTrue

/-! ## C — the crossing atom reconstruction (the representative dispatch arm's reshape source) -/

/-- ★ **Recover the crossing arc list.**  `arcsAreCrossing arcs = true` forces exactly `[(0,3),(1,2)]` — a list-of-pairs
inversion (the other list shapes return `false`, refuted by `Bool.noConfusion`) + `Nat.eq_of_beq_eq_true` per endpoint +
pair eta. -/
theorem arcsAreCrossing_reconstruct : (arcs : List (Nat × Nat)) → arcsAreCrossing arcs = true →
    arcs = [(0, 3), (1, 2)]
  | [], allCrossing => Bool.noConfusion allCrossing
  | _ :: [], allCrossing => Bool.noConfusion allCrossing
  | firstArc :: secondArc :: [], allCrossing => by
      have firstFstZero : firstArc.fst = 0 :=
        Nat.eq_of_beq_eq_true (andEqTrue_left (andEqTrue_left (andEqTrue_left allCrossing)))
      have firstSndThree : firstArc.snd = 3 :=
        Nat.eq_of_beq_eq_true (andEqTrue_right (andEqTrue_left (andEqTrue_left allCrossing)))
      have secondFstOne : secondArc.fst = 1 :=
        Nat.eq_of_beq_eq_true (andEqTrue_right (andEqTrue_left allCrossing))
      have secondSndTwo : secondArc.snd = 2 :=
        Nat.eq_of_beq_eq_true (andEqTrue_right allCrossing)
      have firstArcEq : firstArc = (0, 3) := by rw [← firstFstZero, ← firstSndThree]
      have secondArcEq : secondArc = (1, 2) := by rw [← secondFstOne, ← secondSndTwo]
      rw [firstArcEq, secondArcEq]
  | _ :: _ :: _ :: _, allCrossing => Bool.noConfusion allCrossing

/-- ★ **Recover the full `crossingWiring`.**  The four `isCrossingWiring` conjuncts (`inputCount = 2`, `outputCount = 2`,
`internalLoops = 0`, `arcsAreCrossing arcs`) reconstruct the whole `WiringDesc` by structure eta. -/
theorem crossingWiring_reconstruct : (desc : WiringDesc) → isCrossingWiring desc = true → desc = crossingWiring
  | ⟨inputCount, outputCount, arcs, internalLoops⟩, isCrossing => by
      have inputTwo : inputCount = 2 :=
        Nat.eq_of_beq_eq_true (andEqTrue_left (andEqTrue_left (andEqTrue_left isCrossing)))
      have outputTwo : outputCount = 2 :=
        Nat.eq_of_beq_eq_true (andEqTrue_right (andEqTrue_left (andEqTrue_left isCrossing)))
      have loopsZero : internalLoops = 0 :=
        Nat.eq_of_beq_eq_true (andEqTrue_right (andEqTrue_left isCrossing))
      have arcsCrossing : arcs = [(0, 3), (1, 2)] :=
        arcsAreCrossing_reconstruct arcs (andEqTrue_right isCrossing)
      subst inputTwo; subst outputTwo; subst loopsZero; subst arcsCrossing; rfl

/-- ★★ **Reconstruct a crossing atom from its kind + position.**  `isCrossingAtom a = true` and
`Nat.beq a.position p = true` reconstruct `a = crossingAt p` — the positional atom equality that feeds the transport. -/
theorem crossingAtom_reconstruct : (a : BrauerAtom) → (p : Nat) → isCrossingAtom a = true →
    Nat.beq a.position p = true → a = crossingAt p
  | ⟨position, wiring⟩, p, isCrossing, positionMatches => by
      have positionEq : position = p := Nat.eq_of_beq_eq_true positionMatches
      have wiringEq : wiring = crossingWiring := crossingWiring_reconstruct wiring isCrossing
      subst positionEq; subst wiringEq; rfl

/-! ## D — the per-arm reshape composed -/

/-- ★★ **The per-dispatch-arm reshape.**  Retype a builder outcome for the positional head `crossingAt p` to the
region's ACTUAL head atom `a` (a reconstructed crossing), via the atom reconstruction + the `Eq.rec` transport.  The
cons-indexed reshape the walls flagged as a `propext` minefield, built zero-axiom. -/
def transportCrossingHead (a : BrauerAtom) (p : Nat) (rest : List BrauerAtom)
    (isCrossing : isCrossingAtom a = true) (positionMatches : Nat.beq a.position p = true)
    (outcome : RegionCupOutcome (crossingAt p :: rest)) : RegionCupOutcome (a :: rest) :=
  RegionCupOutcome.transportByRegionEq
    (by rw [crossingAtom_reconstruct a p isCrossing positionMatches]) outcome

/-- ★ **The reshape PRESERVES the fate.**  Transporting an outcome across a region equality keeps its fate — the reshape
is pure plumbing (no semantic content changes), so a reshaped dispatch arm carries the same arrived / annihilated / loop
verdict.  By `cases` on the equality (`Eq.rec` over `rfl`), zero-axiom. -/
theorem transportByRegionEq_fate {regionA regionB : List BrauerAtom}
    (regionEq : regionA = regionB) (outcome : RegionCupOutcome regionA) :
    (RegionCupOutcome.transportByRegionEq regionEq outcome).fate = outcome.fate := by
  cases regionEq; rfl

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the outcome-reshape TRANSPORT KIT SHIPS (the "propext minefield" REFUTED).**
`RegionCupOutcome.transportByRegionEq` retypes an outcome across a proven region equality by `Eq.rec` with an explicit
motive (zero-axiom); the hand-rolled `&&`-split (`andEqTrue_left` / `andEqTrue_right`) + the list-of-pairs inversion
(`arcsAreCrossing_reconstruct`) + `crossingWiring_reconstruct` reconstruct the full crossing wiring, and
`crossingAtom_reconstruct` / `transportCrossingHead` compose the atom reconstruction with the transport into the per-arm
reshape the walls named.  All machine-checked axiom-free — the reshape plumbing is CLEAN.  `= true`. -/
def fxBrauer_hasRegionOutcomeTransportKit : Bool := true

/-! ## The honest terminal state, machine-checked -/

/-- ★★ **The BRAUER r41 region-transport-kit terminal state — MACHINE-CHECKED.**  The three r41 markers are `true` (the
J-loop engine lemma, the J-geometry ordered rewrite, the J-transport reshape kit), built on the r39/r40 factored cup
arrival / region classifier / eager dispatch, while the total region dispatch (r39), the r38 total decision, the r36
single-cup peel discharge, and all four completeness / inner-descent masters STAY `false`.  A `rfl`-conjunction the
kernel checks; purely additive, no master flip is fabricated — the TOTAL ASSEMBLY (all 11 arms + the cupless-prefix
whiskering into one `totalDispatch`) remains the r42 piece. -/
theorem fxBrauer_regionTransportKitTerminalState :
    fxBrauer_hasRegionOutcomeTransportKit = true
      ∧ fxBrauer_hasStraddleSinkOrdered = true
      ∧ fxBrauer_hasLoopBubbleEngineLemma = true
      ∧ fxBrauer_hasEagerRegionDispatch = true
      ∧ fxBrauer_hasRegionDriverTotalDispatch = false
      ∧ fxBrauer_hasSingleCupTotalDecision = false
      ∧ fxBrauer_hasSingleCupPeelDischarged = false
      ∧ fxBrauer_hasStagedInnerDescentDischarged = false
      ∧ fxBrauer_hasFreeBrauerStraighteningNF = false
      ∧ fxBrauer_hasBrauerCompleteness = false
      ∧ fxBrauer_hasBrauerV2FullCompleteness = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph

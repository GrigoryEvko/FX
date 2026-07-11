import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcReadOffCount
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFunctoriality
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardForm
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBrauerReadback

/-! # BRAUER-MIDDLE r17 — the E3 OPENING: the fold-alignment target invariant + the crossing-staircase width brick

With the read-off-order permutation closed on both sides (`fxBrauer_hasReadOffOrderPermutation = true`, r17 B3), the
standing chain to the masters is **E3** (fold-alignment / T-CONNECT — the union-find `stepWiring` long-pole) **→
T-CLOSE(b)** (the `extractDiagram` field reassembly).  This file OPENS E3, honestly: it states the fold-alignment
TARGET invariant precisely (language-exact), lands the first genuine structural alignment brick (the crossing
staircase preserves the open-wire COUNT), and names the exact remaining connectivity gap.  **E3 stays OPEN.**

## The recon's literal bridge is FALSE — the alignment is a CONNECTIVITY correspondence, not equality

The r17 recon proposed a first brick `processBrauer (brauerSeed bc) (crossingWord positions) . openWires
= permuteOfCrossingWord bc positions`.  Reading `stepWiring … crossingWiring` shows this is FALSE: each crossing
allocates FRESH node ids (`outputNodes := (List.range 2).map (· + state.nextFresh) = [nextFresh, nextFresh + 1]`) and
splices them in place of the two consumed wires, wiring `oldLeft ~ nextFresh + 1` and `oldRight ~ nextFresh` in the
union-find.  So after the crossing staircase the open wires are FRESH ids (`nextFresh + k`), NOT the values
`0 … bc - 1` that `permuteOfCrossingWord` (a fold of `applyAdjacentSwap` over `List.range bc`) produces — the two
lists are never literally equal once any crossing fires.  The genuine alignment is a `isSameComponent`
CORRESPONDENCE: the open wire at position `j` shares a union-find component with bottom port
`permuteOfCrossingWord bc positions [j]`.  Establishing that (through the `bottomPerm` / `topPerm` conjugators, per
arc, routed into `partnerIndexOf_readsPartner_reachable`) is the union-find `stepWiring` long-pole — the OPEN E3 wall.

## What this file ships (each zero-axiom, structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`)

  * **`foldRealizesTargetDiagram`** — the E3 / T-CLOSE(b) TARGET invariant, stated language-exact: for a well-formed
    involution `d`, the standard-form fold's `extractDiagram` recovers `d` (the named node
    `extractDiagram_realizes_partner_ofConnectivity`).  Proven on the adversarial-B instance
    (`foldRealizesTargetDiagram_adversarialB`) — the target is TRUE, decidably, on a diagram exercising a crossing
    cap, a crossing cup, a through, and a loop; the residual is the general PROOF, not the truth.

  * **`crossingWordFold_openWires_length`** — the first structural alignment brick: the crossing staircase preserves
    the open-wire COUNT.  Folding `crossingWord positions` over any state of open-wire count `width`, with every
    position in range (`pos + 2 ≤ width`), leaves the open-wire count at `width`.  Structural induction over the
    positions, reusing the shipped `stepWiring_openWires_length_fits` per crossing.  This is the width invariant the
    connectivity correspondence and `extractDiagram` (which reads `topCount := openWires.length`) both rest on.

  * **`crossingWord_openWire_sameComponent_bottomPort`** (r18) — the E3 wall's EXACT stated crossing-phase goal, LANDED:
    after an in-range crossing-only word, the open wire at position `j` shares a union-find component with bottom port
    `natListGetAt (permuteOfCrossingWord bottomCount positions) j`.  Derived — NOT re-proved — from the shipped
    crossing-only readback state invariant `stateIsPermGraph_ofInRange.boundView` (`WiringDescBrauerReadback`, where the
    union-find `stepWiring` long-pole was discharged via `crossing_lift` + boundary coherence): the wall's claim is the
    top-index / bottom-index specialization of `boundView`.  Flips `fxBrauer_hasCrossingStaircaseConnectivity`; the
    six-phase `foldRealizesTargetDiagram` (T-CLOSE(b) per-arc routing) stays OPEN, `fxBrauer_hasFoldAlignmentE3` honest.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The E3 / T-CLOSE(b) fold-alignment target invariant (language-exact) -/

/-- ★ **The E3 / T-CLOSE(b) fold-alignment TARGET invariant** (`extractDiagram_realizes_partner_ofConnectivity`).  For
a well-formed boundary involution `d`, running the reconstructed standard-form word through the wiring engine from the
seed and reading the boundary matching back with `extractDiagram` recovers `d` exactly.  This is the invariant the
tag-correspondence masters range over: once it holds for every gated `d`, the six-phase fold WITH the `bottomPerm` /
`topPerm` conjugating staircases connects exactly each enumerated arc `(i, d.partner[i])`.  Stated here precisely; the
general proof is the OPEN E3 wall (the union-find `stepWiring` long-pole). -/
def foldRealizesTargetDiagram (d : DiagramType) : Prop :=
  IsBoundaryInvolution (d.bottomCount + d.topCount) d.partner →
    extractDiagram d.bottomCount
        (processBrauer (brauerSeed d.bottomCount) (standardFormWordExt5 (reconstructStandardFormExt5 d)))
      = d

/-- ★ **The E3 target is TRUE on the adversarial-B instance.**  The diagram with a crossing cap `0↔2`, a through
`1↔top1`, a crossing cup `top0↔top2`, and one loop reconstructs and reads back to itself — decidably.  So the target
`foldRealizesTargetDiagram` is genuinely inhabited on a diagram exercising all three ∗-dual axes plus a loop; the
residual is the general PROOF, not the truth (Lehrer–Zhang arXiv:1207.5889 Thm 2.6). -/
theorem foldRealizesTargetDiagram_adversarialB : foldRealizesTargetDiagram adversarialBDiagram :=
  fun _ => by decide

/-! ## The first structural alignment brick — the crossing staircase preserves the open-wire count -/

/-- ★★ **The crossing staircase preserves the open-wire COUNT.**  Folding `crossingWord positions` over any state of
open-wire count `width`, with every position in range (`pos + 2 ≤ width`), leaves exactly `width` open wires.  A
structural induction over the positions, reusing the shipped `stepWiring_openWires_length_fits` per crossing (each
crossing is a `2 ⇒ 2` generator: two consumed, two fresh produced).  The width invariant the connectivity
correspondence and `extractDiagram`'s `topCount := openWires.length` read both rest on — the first genuine fold-
alignment brick, below the OPEN connectivity correspondence. -/
theorem crossingWordFold_openWires_length (width : Nat) : (positions : List Nat) → (state : WireState) →
    state.openWires.length = width →
    (∀ pos, pos ∈ positions → pos + 2 ≤ width) →
    (processBrauer state (crossingWord positions)).openWires.length = width
  | [], state, lengthEq, _ => lengthEq
  | pos :: rest, state, lengthEq, posBound => by
      have posFits : pos + 2 ≤ state.openWires.length := by
        rw [lengthEq]; exact posBound pos (List.Mem.head rest)
      obtain ⟨rightLen, fitsRaw⟩ := Nat.le.dest posFits
      have stepLen : (stepWiring state pos crossingWiring).openWires.length = width := by
        rw [stepWiring_openWires_length_fits state pos rightLen crossingWiring fitsRaw.symm]
        show pos + 2 + rightLen = width
        rw [fitsRaw, lengthEq]
      show (processBrauer (stepBrauerAtom state (crossingAt pos)) (crossingWord rest)).openWires.length = width
      exact crossingWordFold_openWires_length width rest (stepBrauerAtom state (crossingAt pos)) stepLen
        (fun laterPos laterMem => posBound laterPos (List.Mem.tail pos laterMem))

/-- ★ **Non-vacuity — the width invariant fires on a concrete crossing staircase.**  Two crossings at positions
`0, 1` over three bottom wires leave three open wires. -/
theorem crossingWordFold_openWires_length_probe :
    (processBrauer (brauerSeed 3) (crossingWord [0, 1])).openWires.length = 3 :=
  crossingWordFold_openWires_length 3 [0, 1] (brauerSeed 3) (by decide)
    (fun pos posMem => by
      cases posMem with
      | head => decide
      | tail _ tailMem =>
          cases tailMem with
          | head => decide
          | tail _ nilMem => nomatch nilMem)

/-! ## The E3 crossing-phase connectivity correspondence — the wall's exact stated goal, from the shipped boundView

The E3 wall names its crossing-phase open goal verbatim: after the crossing phase, the open wire at position `j`
shares a union-find component with bottom port `natListGetAt (permuteOfCrossingWord bottomCount …) j`.  That
correspondence is ALREADY established at full strength by the shipped crossing-only readback state invariant
`stateIsPermGraph_ofInRange` (`WiringDescBrauerReadback`): its `boundView` field says every boundary-index pair shares
a component exactly when it carries the same through-strand — the union-find `stepWiring` long-pole was discharged
there (via `crossing_lift` + boundary coherence, folded from the seed).  The wall's `openWires[j] ~ bottom-port
perm[j]` is the TOP-index / BOTTOM-index specialization of that view, so NO new union-find induction is needed; this
section LANDS the wall's exact statement as a corollary. -/

/-- `n + a - n = a` — structural, propext-free (mirrors the readback layer's local subtraction cancel). -/
private theorem addSubCancelLeftAlign : (n a : Nat) → n + a - n = a
  | 0, a => by rw [Nat.zero_add, Nat.sub_zero]
  | n + 1, a => by
      rw [Nat.add_right_comm n 1 a]
      show (n + a).succ - (n).succ = a
      rw [Nat.succ_sub_succ]
      exact addSubCancelLeftAlign n a

/-- `natListGetAt entries index ∈ entries` for `index < entries.length` — structural. -/
private theorem getAtMemAlign : (entries : List Nat) → (index : Nat) → index < entries.length →
    natListGetAt entries index ∈ entries
  | [], index, indexBelow => absurd indexBelow (Nat.not_lt_zero index)
  | _ :: rest, 0, _ => List.Mem.head rest
  | head :: rest, index + 1, indexBelow =>
      List.Mem.tail head (getAtMemAlign rest index (Nat.lt_of_succ_lt_succ indexBelow))

/-- `Nat.beq value value = true` — structural on the digit, propext-free (`==`'s decide-reflexivity, done by hand). -/
private theorem beqSelfAlign : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | value + 1 => beqSelfAlign value

/-- `Nat.beq leftValue rightValue = true → leftValue = rightValue` — structural, propext-free. -/
private theorem natBeqEqAlign : (leftValue rightValue : Nat) → Nat.beq leftValue rightValue = true →
    leftValue = rightValue
  | 0, 0, _ => rfl
  | 0, _ + 1, h => Bool.noConfusion h
  | _ + 1, 0, h => Bool.noConfusion h
  | leftValue + 1, rightValue + 1, h => congrArg (· + 1) (natBeqEqAlign leftValue rightValue h)

/-- `value ∈ entries → memBool value entries = true` — structural on the membership witness. -/
private theorem memBoolOfMemAlign : (entries : List Nat) → (value : Nat) → value ∈ entries →
    memBool value entries = true
  | [], _, memNil => nomatch memNil
  | head :: rest, value, memCons => by
      show (Nat.beq head value || memBool value rest) = true
      cases memCons with
      | head => rw [beqSelfAlign head, Bool.true_or]
      | tail _ memRest => rw [memBoolOfMemAlign rest value memRest, Bool.or_true]

/-- `memBool value entries = true → value ∈ entries` — the converse, structural on the `Nat.beq` head test. -/
private theorem memOfMemBoolAlign : (entries : List Nat) → (value : Nat) → memBool value entries = true →
    value ∈ entries
  | [], _, memTrue => Bool.noConfusion memTrue
  | head :: rest, value, memTrue => by
      cases hbeq : Nat.beq head value with
      | true => exact (natBeqEqAlign head value hbeq) ▸ List.Mem.head rest
      | false =>
          have memRest : memBool value rest = true := by
            have combined : (Nat.beq head value || memBool value rest) = true := memTrue
            rw [hbeq, Bool.false_or] at combined
            exact combined
          exact List.Mem.tail head (memOfMemBoolAlign rest value memRest)

/-- Membership is invariant across the whole adjacent-swap fold (each `applyAdjacentSwap` only permutes) — reusing
the shipped per-swap `memBool_applyAdjacentSwap`.  Structural on the position list. -/
private theorem memBoolFoldlSwapAlign : (positions initial : List Nat) → (value : Nat) →
    memBool value (positions.foldl applyAdjacentSwap initial) = memBool value initial
  | [], _, _ => rfl
  | position :: rest, initial, value => by
      show memBool value (rest.foldl applyAdjacentSwap (applyAdjacentSwap initial position))
        = memBool value initial
      rw [memBoolFoldlSwapAlign rest (applyAdjacentSwap initial position) value,
        memBool_applyAdjacentSwap value initial position]

/-- The realized permutation carries exactly the identity's membership set (`List.range bottomCount`). -/
private theorem memBoolPermuteAlign (bottomCount : Nat) (positions : List Nat) (value : Nat) :
    memBool value (permuteOfCrossingWord bottomCount positions) = memBool value (List.range bottomCount) :=
  memBoolFoldlSwapAlign positions (List.range bottomCount) value

/-- ★ Every entry of the realized permutation is a bottom port:
`natListGetAt (permuteOfCrossingWord bottomCount positions) index < bottomCount` for `index < bottomCount`.  Its
membership set is `List.range bottomCount`, so every read entry occurs in the range and is below the bound. -/
private theorem permGetAtLtAlign (bottomCount : Nat) (positions : List Nat) (index : Nat)
    (indexBelow : index < bottomCount) :
    natListGetAt (permuteOfCrossingWord bottomCount positions) index < bottomCount := by
  have lengthEq : (permuteOfCrossingWord bottomCount positions).length = bottomCount :=
    permuteOfCrossingWord_length bottomCount positions
  have indexInRange : index < (permuteOfCrossingWord bottomCount positions).length := by
    rw [lengthEq]; exact indexBelow
  have memBoolTrue : memBool (natListGetAt (permuteOfCrossingWord bottomCount positions) index)
      (permuteOfCrossingWord bottomCount positions) = true :=
    memBoolOfMemAlign _ _ (getAtMemAlign (permuteOfCrossingWord bottomCount positions) index indexInRange)
  rw [memBoolPermuteAlign bottomCount positions] at memBoolTrue
  exact mem_range_imp_lt (memOfMemBoolAlign (List.range bottomCount) _ memBoolTrue)

/-- ★★ **The E3 crossing-phase correspondence over any permutation-graph state.**  If `state`'s union-find boundary
view IS the permutation graph of `permuteOfCrossingWord bottomCount positions` (the shipped `StateIsPermGraph`), then
for every bottom port `j` the open wire at position `j` shares a component with bottom port
`natListGetAt (permuteOfCrossingWord bottomCount positions) j`.  The TOP-index / BOTTOM-index specialization of
`boundView`: index `bottomCount + j` reads the open wire at `j` and carries strand `perm[j]`; the bottom index
`perm[j]` reads node `perm[j]` and carries strand `perm[j]` (it is a bottom port, `permGetAtLtAlign`), so `boundView`
collapses to `decide (perm[j] = perm[j]) = true`. -/
theorem stateIsPermGraph_openWire_sameComponent_bottomPort
    (bottomCount : Nat) (positions : List Nat) (state : WireState)
    (permGraph : StateIsPermGraph bottomCount positions state)
    (j : Nat) (jBelow : j < bottomCount) :
    isSameComponent state.links (natListGetAt state.openWires j)
        (natListGetAt (permuteOfCrossingWord bottomCount positions) j)
      = true := by
  have pjBelow : natListGetAt (permuteOfCrossingWord bottomCount positions) j < bottomCount :=
    permGetAtLtAlign bottomCount positions j jBelow
  have topLt : bottomCount + j < bottomCount + bottomCount := Nat.add_lt_add_left jBelow bottomCount
  have botLt : natListGetAt (permuteOfCrossingWord bottomCount positions) j < bottomCount + bottomCount :=
    Nat.lt_of_lt_of_le pjBelow (Nat.le_add_right bottomCount bottomCount)
  have boundEq := permGraph.boundView (bottomCount + j)
    (natListGetAt (permuteOfCrossingWord bottomCount positions) j) topLt botLt
  have topNode : boundaryNodeAt bottomCount state (bottomCount + j) = natListGetAt state.openWires j := by
    show (if bottomCount + j < bottomCount then bottomCount + j
          else natListGetAt state.openWires (bottomCount + j - bottomCount)) = natListGetAt state.openWires j
    rw [if_neg (Nat.not_lt.mpr (Nat.le_add_right bottomCount j)), addSubCancelLeftAlign bottomCount j]
  have botNode : boundaryNodeAt bottomCount state (natListGetAt (permuteOfCrossingWord bottomCount positions) j)
      = natListGetAt (permuteOfCrossingWord bottomCount positions) j := by
    show (if natListGetAt (permuteOfCrossingWord bottomCount positions) j < bottomCount
            then natListGetAt (permuteOfCrossingWord bottomCount positions) j
          else natListGetAt state.openWires
            (natListGetAt (permuteOfCrossingWord bottomCount positions) j - bottomCount))
        = natListGetAt (permuteOfCrossingWord bottomCount positions) j
    rw [if_pos pjBelow]
  have topStrand : boundaryStrand bottomCount (permuteOfCrossingWord bottomCount positions) (bottomCount + j)
      = natListGetAt (permuteOfCrossingWord bottomCount positions) j := by
    show (if bottomCount + j < bottomCount then bottomCount + j
          else natListGetAt (permuteOfCrossingWord bottomCount positions) (bottomCount + j - bottomCount))
        = natListGetAt (permuteOfCrossingWord bottomCount positions) j
    rw [if_neg (Nat.not_lt.mpr (Nat.le_add_right bottomCount j)), addSubCancelLeftAlign bottomCount j]
  have botStrand : boundaryStrand bottomCount (permuteOfCrossingWord bottomCount positions)
        (natListGetAt (permuteOfCrossingWord bottomCount positions) j)
      = natListGetAt (permuteOfCrossingWord bottomCount positions) j := by
    show (if natListGetAt (permuteOfCrossingWord bottomCount positions) j < bottomCount
            then natListGetAt (permuteOfCrossingWord bottomCount positions) j
          else natListGetAt (permuteOfCrossingWord bottomCount positions)
            (natListGetAt (permuteOfCrossingWord bottomCount positions) j - bottomCount))
        = natListGetAt (permuteOfCrossingWord bottomCount positions) j
    rw [if_pos pjBelow]
  rw [topNode, botNode, topStrand, botStrand] at boundEq
  rw [boundEq]
  exact decide_eq_true rfl

/-- ★★ **The E3 crossing-phase connectivity correspondence — the wall's EXACT stated goal.**  Running an in-range
crossing-only word from the seed reaches a state where the open wire at each bottom port `j` shares a union-find
component with bottom port `natListGetAt (permuteOfCrossingWord bottomCount positions) j`.  The exact
`isSameComponent` correspondence the E3 wall names — obtained from the shipped `stateIsPermGraph_ofInRange`, NOT a new
`stepWiring` induction.  (The six-phase per-arc routing into `partnerIndexOf` — T-CLOSE(b) — remains the residual;
this is the crossing PHASE, one of the six.) -/
theorem crossingWord_openWire_sameComponent_bottomPort
    (bottomCount : Nat) (bottomPos : 0 < bottomCount) (positions : List Nat)
    (inRange : ∀ position, position ∈ positions → position + 2 ≤ bottomCount)
    (j : Nat) (jBelow : j < bottomCount) :
    isSameComponent (processBrauer (brauerSeed bottomCount) (crossingWord positions)).links
        (natListGetAt (processBrauer (brauerSeed bottomCount) (crossingWord positions)).openWires j)
        (natListGetAt (permuteOfCrossingWord bottomCount positions) j)
      = true :=
  stateIsPermGraph_openWire_sameComponent_bottomPort bottomCount positions
    (processBrauer (brauerSeed bottomCount) (crossingWord positions))
    (stateIsPermGraph_ofInRange bottomCount bottomPos positions inRange) j jBelow

/-- ★ **Non-vacuity — the crossing-phase correspondence fires on a concrete non-commuting two-crossing word.**  Over
three bottom wires, `crossingWord [0, 1]` sends the open wire at position `1` into the component of bottom port
`natListGetAt (permuteOfCrossingWord 3 [0, 1]) 1 = 2` (the recon's hand-traced staircase). -/
theorem crossingWord_openWire_sameComponent_bottomPort_probe :
    isSameComponent (processBrauer (brauerSeed 3) (crossingWord [0, 1])).links
        (natListGetAt (processBrauer (brauerSeed 3) (crossingWord [0, 1])).openWires 1)
        (natListGetAt (permuteOfCrossingWord 3 [0, 1]) 1)
      = true :=
  crossingWord_openWire_sameComponent_bottomPort 3 (by decide) [0, 1]
    (fun position posMem => by
      cases posMem with
      | head => decide
      | tail _ tailMem =>
          cases tailMem with
          | head => decide
          | tail _ nilMem => nomatch nilMem)
    1 (by decide)

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the E3 crossing-staircase WIDTH invariant is the first fold-alignment brick (r17).**
`crossingWordFold_openWires_length` proves the crossing staircase preserves the open-wire count (zero-axiom,
structural, reusing `stepWiring_openWires_length_fits`), firing on a concrete staircase
(`crossingWordFold_openWires_length_probe`).  And `foldRealizesTargetDiagram` states the E3 / T-CLOSE(b) target
invariant precisely, TRUE on the adversarial-B instance (`foldRealizesTargetDiagram_adversarialB`).  `= true`. -/
def fxBrauer_hasCrossingFoldWidthInvariant : Bool := true

/-- ★★ **Honesty marker — the E3 crossing-phase connectivity correspondence is LANDED (r18).**
`crossingWord_openWire_sameComponent_bottomPort` proves the E3 wall's EXACT stated crossing-phase goal — after an
in-range crossing-only word, the open wire at position `j` shares a union-find component with bottom port
`natListGetAt (permuteOfCrossingWord bottomCount positions) j` — as the top-index / bottom-index specialization of the
shipped `stateIsPermGraph_ofInRange.boundView` (the union-find `stepWiring` long-pole was discharged there via
`crossing_lift` + boundary coherence, folded from the seed; NO new induction).  Fires on the recon's concrete
non-commuting staircase (`crossingWord_openWire_sameComponent_bottomPort_probe`).  Zero-axiom, structural.  This is the
crossing PHASE of the six-phase E3 target; the per-arc T-CLOSE(b) routing is the residual (`fxBrauer_hasFoldAlignmentE3`).
`= true`. -/
def fxBrauer_hasCrossingStaircaseConnectivity : Bool := true

/-- **Honesty WALL marker — the E3 fold-alignment (the six-phase `foldRealizesTargetDiagram`) is OPEN; the crossing
PHASE is now landed.**  The crossing-staircase connectivity correspondence — the wall's stated crossing-phase goal
"the open wire at position `j` shares a component with bottom port `natListGetAt (permuteOfCrossingWord bottomCount
form.bottomPerm) j`" — is LANDED (`crossingWord_openWire_sameComponent_bottomPort`, r18, from the shipped
`boundView`).  What stays OPEN is the SIX-PHASE assembly `foldRealizesTargetDiagram`: composing the `bottomPerm`
crossing phase (landed) with the cap / cup / `middle` / `topPerm` / loop phases and routing EACH enumerated arc
`(i, d.partner[i])` — bottom↔bottom via `bottomPerm` + `capThenCupFold_connects`, top↔top via `topPerm`, through via
`bottomPerm`+`middle`+`topPerm`, loops via `circleWord` — into `partnerIndexOf_readsPartner_reachable` to conclude
`partnerIndexOf … i = d.partner[i]` (the `extractDiagram_realizes_partner_ofConnectivity` residual, T-CLOSE(b)).  Until
that six-phase per-arc reassembly binds, the tag-correspondence masters `fxBrauer_hasTagCorrDisjoint` /
`fxBrauer_hasTagCorrExtraction` stay honestly `false`; #2013 does NOT close.  `= false`. -/
def fxBrauer_hasFoldAlignmentE3 : Bool := false

end FX1Poly.Polygraph

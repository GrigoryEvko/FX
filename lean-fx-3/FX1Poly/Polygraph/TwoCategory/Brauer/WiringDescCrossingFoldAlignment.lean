import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcReadOffCount
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFunctoriality
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStandardForm

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

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the E3 crossing-staircase WIDTH invariant is the first fold-alignment brick (r17).**
`crossingWordFold_openWires_length` proves the crossing staircase preserves the open-wire count (zero-axiom,
structural, reusing `stepWiring_openWires_length_fits`), firing on a concrete staircase
(`crossingWordFold_openWires_length_probe`).  And `foldRealizesTargetDiagram` states the E3 / T-CLOSE(b) target
invariant precisely, TRUE on the adversarial-B instance (`foldRealizesTargetDiagram_adversarialB`).  `= true`. -/
def fxBrauer_hasCrossingFoldWidthInvariant : Bool := true

/-- **Honesty WALL marker — the E3 fold-alignment (the union-find `stepWiring` long-pole) is OPEN.**  The width brick
`crossingWordFold_openWires_length` is landed, but the E3 alignment proper is a CONNECTIVITY correspondence, not a
length or an equality: the recon's literal `openWires = permuteOfCrossingWord` is FALSE (the crossing fold allocates
FRESH node ids `nextFresh + k`, never the values `0 … bottomCount - 1`).  The exact OPEN goal: after the `bottomPerm`
crossing phase, the open wire at position `j` shares a union-find component with bottom port
`natListGetAt (permuteOfCrossingWord bottomCount form.bottomPerm) j` — an `isSameComponent` correspondence routed per
arc through the `bottomPerm` / `topPerm` conjugators into `partnerIndexOf_readsPartner_reachable`, closing
`foldRealizesTargetDiagram` for every gated `d`.  That, and the T-CLOSE(b) field reassembly, are UNBUILT, so the
tag-correspondence masters `fxBrauer_hasTagCorrDisjoint` / `fxBrauer_hasTagCorrExtraction` stay honestly `false`;
#2013 does NOT close.  `= false`. -/
def fxBrauer_hasFoldAlignmentE3 : Bool := false

end FX1Poly.Polygraph

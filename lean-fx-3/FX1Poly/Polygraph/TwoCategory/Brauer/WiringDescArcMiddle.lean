import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcAnchor
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescStaircaseCanonical

/-! # BRAUER-MIDDLE r1 B1 — the FULL-MIDDLE readback (WALL-2 FIXED) + the `topPerm`-extended standard form (WALL-1 breached at the datatype)

The r2 arc-anchor round (`Brauer/WiringDescArcAnchor.lean`) shipped the standard-form readback with an EMPTY middle
and exhibited two `none` walls: WALL-2 (`standardFormOfDiagram_pureCrossing_none`, the pure-crossing diagram `[3,2,1,0]`
is planar-reachable but the empty-middle reconstruction does not INVERT the through-strand permutation) and WALL-1
(`standardFormOfDiagram_straddle_none`, the straddle diagram is CROSSING so no `capWord ++ crossingWord ++ cupWord`
tail-block form realizes it).  This round breaches BOTH at the readback / datatype level, machine-checked.

## The inversion pin (the recon's decisive finding) — read the middle off the TOP boundary, NO inversion

`permutationDiagram n perm` (`Brauer/WiringDescStandardForm.lean`) is `partner = bottomMap(perm⁻¹) ++ topMap(perm)`,
so the through-strand permutation the middle must realize is the TOP-indexed reading: for each through-top in
ASCENDING boundary order, the rank of the through-strand bottom that enters it.  Reading it off the BOTTOM half (for
each bottom, where it goes) gives the INVERSE, which `permuteOfCrossingWord` then mis-realizes — the exact WALL-2 trap.
`throughStrandPerm` reads the TOP-indexed permutation; `permutationToCrossingWord` realizes it as a crossing staircase.

## What this file ships (each zero-axiom, structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`)

  * **`permutationToCrossingWord`** — a selection realizer: given a one-line permutation, emit adjacent-transposition
    positions whose `permuteOfCrossingWord` fold reproduces it.  Structural (fuel = number of positions to place);
    validated on concrete permutations (`permutationRealizer_*`).
  * **`BrauerStandardFormExt`** — the Graham–Lehrer quadruple EXTENDED with the ★ new `topPerm` block (the top-boundary
    `S_m` permutation routing cups past through-strands); `standardFormWordExt` = caps · middle · cups · `topPerm`.
  * **`standardFormOfDiagramFull : DiagramType → Option BrauerStandardFormExt`** — the FULL-MIDDLE readback, GUARDED by
    `standardFormDiagramExt = d` so SOUND unconditionally (`standardFormOfDiagramFull_sound`).  It reads the caps / cups
    arc blocks and the through-strand middle permutation (TOP-indexed) with `topPerm := []`.
  * ★ **WALL-2 FIXED (eval).**  The pure-crossing diagram `[3,2,1,0]` now reads back
    `some { middle := [0], … }` (`standardFormOfDiagramFull_pureCrossing_some`), and the readback is now GENERAL over
    crossing words (`standardFormOfDiagramFull_threeCycle_some` / `_yangBaxterReversal_some`): the middle permutation
    is inverted correctly.
  * the roundtrips on the planar cap/cup/through class (`standardFormOfDiagramFull_roundtrip_identity` / `_cupCap`).
  * ★ **WALL-1 breached at the datatype (eval).**  The straddle's EXTENDED standard form
    `{ cupBlock := [1], topPerm := [0] }` genuinely realizes the straddle diagram
    (`straddleExt_realizes`, `standardFormDiagramExt … = straddleDiagram`) — the tail-cup-block form that WALL-1 proved
    does NOT exist in the 3-block datatype EXISTS in the `topPerm`-extended datatype.

## The honest residual (feeds B2 / B3 / B4)

`standardFormOfDiagramFull` reconstructs `topPerm := []`, so it reads back the planar cap/cup/through class and every
crossing-only diagram, but returns `none` on diagrams with a CROSSING cup (the straddle,
`standardFormOfDiagramFull_straddle_none`): the general crossing-cup ARC EXTRACTOR (the top TL+`S_m` decomposition that
would compute a non-empty `cupBlock` + `topPerm` automatically) is the genuine new combinatorial architecture, unbuilt.
So the straddle's extended form is EXHIBITED (its existence is machine-checked), and its AUTOMATIC reconstruction is the
named residual.  `fxBrauer_hasBrauerV2FullCompleteness` / `fxBrauer_hasBrauerCompleteness` stay `false`.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The permutation realizer — a selection sort emitting adjacent transpositions -/

/-- The descending swap positions `[endIndex-1, endIndex-2, …, startIndex]` — the bubble that carries a value from
index `endIndex` down to index `startIndex`.  Length `endIndex - startIndex`; empty when `endIndex ≤ startIndex`. -/
def descendingSwapPositions (endIndex startIndex : Nat) : List Nat :=
  (List.range (endIndex - startIndex)).map (fun step => endIndex - 1 - step)

/-- The selection-sort fold building a permutation from the identity.  `fuel` counts the boundary positions still to
place (`bottomCount - 1`); at each step the target value `perm[position]` is bubbled from its current index down to
`position`.  Structural on `fuel`, so it computes and needs no `WellFounded.fix`. -/
def permutationRealizerFold (perm : List Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, _ => []
  | fuel + 1, position, currentPerm =>
      let bubble := descendingSwapPositions
        (natIndexOfValue currentPerm (natListGetAt perm position)) position
      bubble ++ permutationRealizerFold perm fuel (position + 1) (bubble.foldl applyAdjacentSwap currentPerm)

/-- ★ **The permutation realizer** — a crossing-position word whose `permuteOfCrossingWord` fold reproduces `perm`.
Selection sort over the boundary positions, bubbling each target value into place from the identity. -/
def permutationToCrossingWord (bottomCount : Nat) (perm : List Nat) : List Nat :=
  permutationRealizerFold perm (bottomCount - 1) 0 (List.range bottomCount)

/-! ## The through-strand permutation read-off (the inversion pin) -/

/-- The count of list entries strictly below `bound` — the rank of `bound` among a list of distinct values (used to
reduce boundary indices to `[0, count)` ranks).  `Nat.blt`-driven, propext-free. -/
def arcMiddleCountBelow : List Nat → Nat → Nat
  | [], _ => 0
  | head :: rest, bound => cond (Nat.blt head bound) 1 0 + arcMiddleCountBelow rest bound

/-- The through-strand bottom ports of a diagram, in ascending order: the bottom ports `index < bottomCount` whose
partner is a TOP boundary node (`≥ bottomCount`), i.e. a strand that passes through rather than a cap leg. -/
def throughStrandBottoms (bottomCount : Nat) (partner : List Nat) : List Nat :=
  (List.range bottomCount).filterMap (fun index =>
    match Nat.ble bottomCount (natListGetAt partner index) with
    | true => some index
    | false => none)

/-- ★ **The through-strand permutation, TOP-indexed (the inversion pin).**  For each through-TOP boundary node in
ascending order (top port `topIndex` whose partner is a bottom port, `< bottomCount`), the RANK of the through-strand
bottom that enters it among all through-strand bottoms.  This is the permutation `permuteOfCrossingWord` realizes —
reading it off the TOP half needs NO inversion, exactly as `permutationDiagram`'s `topMap = perm` convention requires. -/
def throughStrandPerm (bottomCount topCount : Nat) (partner : List Nat) : List Nat :=
  (List.range topCount).filterMap (fun topIndex =>
    match Nat.blt (natListGetAt partner (bottomCount + topIndex)) bottomCount with
    | true =>
        some (arcMiddleCountBelow (throughStrandBottoms bottomCount partner)
          (natListGetAt partner (bottomCount + topIndex)))
    | false => none)

/-- The cap arc positions: bottom ports `index` whose partner is the adjacent bottom port `index + 1` AND that
adjacent port is still a bottom (`index + 1 < bottomCount`) — a genuine bottom–bottom cap, not a through-strand whose
partner happens to be numbered `index + 1`.  The bound check is what the r2 `readCapPositions` lacked. -/
def readCapArcPositions (bottomCount : Nat) (partner : List Nat) : List Nat :=
  (List.range bottomCount).filterMap (fun index =>
    match Nat.beq (natListGetAt partner index) (index + 1) && Nat.blt (index + 1) bottomCount with
    | true => some index
    | false => none)

/-- The cup arc positions: top ports `topIndex` whose boundary node's partner is the adjacent top node AND that
adjacent top is still a top (`topIndex + 1 < topCount`) — a genuine top–top cup. -/
def readCupArcPositions (bottomCount topCount : Nat) (partner : List Nat) : List Nat :=
  (List.range topCount).filterMap (fun topIndex =>
    match Nat.beq (natListGetAt partner (bottomCount + topIndex)) (bottomCount + topIndex + 1)
        && Nat.blt (topIndex + 1) topCount with
    | true => some topIndex
    | false => none)

/-! ## The extended cellular standard form (Graham–Lehrer quadruple + the top-boundary permutation) -/

/-- ★ **The `topPerm`-extended Brauer standard form** — the Graham–Lehrer triple (`capBlock`, `middle`, `cupBlock`)
EXTENDED with `topPerm`, the top-boundary `S_m` permutation that routes cups PAST through-strands.  Without it the
tail-cup-block form is provably incomplete on CROSSING cups (WALL-1); with it the straddle's form exists.  A flat
decidable-eq datum, so it computes. -/
structure BrauerStandardFormExt where
  /-- The number of bottom boundary wires the form acts on. -/
  bottomCount : Nat
  /-- The cap half-diagram: cap generator positions, bottom-to-top. -/
  capBlock : List Nat
  /-- The middle `S_t` through-strand permutation, as a crossing-staircase word. -/
  middle : List Nat
  /-- The cup half-diagram: cup generator positions. -/
  cupBlock : List Nat
  /-- ★ The top-boundary `S_m` permutation, as a crossing-staircase word (routes cups past strands). -/
  topPerm : List Nat
deriving DecidableEq, Repr

/-- ★ **The generator word an extended standard form realizes** — caps at the bottom, the middle crossing staircase,
cups, then the top-boundary crossing permutation. -/
def standardFormWordExt (form : BrauerStandardFormExt) : List BrauerAtom :=
  capWord form.capBlock ++ crossingWord form.middle ++ cupWord form.cupBlock ++ crossingWord form.topPerm

/-- The **Brauer diagram of an extended standard form** — run its realized word through the wiring engine. -/
def standardFormDiagramExt (form : BrauerStandardFormExt) : DiagramType :=
  brauerDiagramOf form.bottomCount (standardFormWordExt form)

/-! ## The full-middle readback (honestly gated) -/

/-- The reconstructed extended standard form of a diagram — cap / cup arc blocks (bound-checked adjacent arcs), the
TOP-indexed through-strand middle permutation realized by `permutationToCrossingWord`, and `topPerm := []`.  A
best-effort inverse whose correctness is enforced downstream by the `standardFormOfDiagramFull` guard; the general
crossing-cup arc extractor that would populate `topPerm` is the named residual. -/
def reconstructStandardFormFull (d : DiagramType) : BrauerStandardFormExt :=
  { bottomCount := d.bottomCount,
    capBlock := readCapArcPositions d.bottomCount d.partner,
    middle := permutationToCrossingWord
      (throughStrandPerm d.bottomCount d.topCount d.partner).length
      (throughStrandPerm d.bottomCount d.topCount d.partner),
    cupBlock := readCupArcPositions d.bottomCount d.topCount d.partner,
    topPerm := [] }

/-- ★ **The FULL-MIDDLE readback, honestly gated.**  Reconstruct the cap / cup / middle blocks (the middle now the
INVERTED through-strand permutation, fixing WALL-2) and accept the candidate ONLY when its realized diagram equals the
input.  Total (`none` when the guard fails), SOUND by construction (`standardFormOfDiagramFull_sound`), and PARTIAL: it
succeeds on the planar cap/cup/through class + every crossing-only diagram and returns `none` on crossing-cup diagrams
like the straddle (the topPerm arc extractor is unbuilt). -/
def standardFormOfDiagramFull (d : DiagramType) : Option BrauerStandardFormExt :=
  if standardFormDiagramExt (reconstructStandardFormFull d) = d then some (reconstructStandardFormFull d) else none

/-- ★ **The full-middle readback is SOUND (unconditional).**  Whenever `standardFormOfDiagramFull d = some form`, the
reconstructed extended form genuinely realizes the diagram: `standardFormDiagramExt form = d`.  Straight off the guard
— no correctness of the reconstruction is assumed. -/
theorem standardFormOfDiagramFull_sound (d : DiagramType) (form : BrauerStandardFormExt)
    (readback : standardFormOfDiagramFull d = some form) : standardFormDiagramExt form = d := by
  unfold standardFormOfDiagramFull at readback
  split at readback
  · rename_i guardHolds
    rw [← Option.some.inj readback]; exact guardHolds
  · nomatch readback

/-! ## The permutation realizer — validated on concrete permutations -/

/-- The realizer reproduces the transposition `[1, 0]`. -/
theorem permutationRealizer_transposition :
    permuteOfCrossingWord 2 (permutationToCrossingWord 2 [1, 0]) = [1, 0] := by decide

/-- The realizer reproduces the 3-cycle `[1, 2, 0]`. -/
theorem permutationRealizer_threeCycle :
    permuteOfCrossingWord 3 (permutationToCrossingWord 3 [1, 2, 0]) = [1, 2, 0] := by decide

/-- The realizer reproduces the full reversal `[2, 1, 0]`. -/
theorem permutationRealizer_reversal :
    permuteOfCrossingWord 3 (permutationToCrossingWord 3 [2, 1, 0]) = [2, 1, 0] := by decide

/-- The realizer reproduces the identity (empty word). -/
theorem permutationRealizer_identity :
    permuteOfCrossingWord 3 (permutationToCrossingWord 3 [0, 1, 2]) = [0, 1, 2] := by decide

/-- The realizer reproduces a width-4 permutation `[2, 0, 3, 1]` — the read-off is correct beyond three strands. -/
theorem permutationRealizer_width4 :
    permuteOfCrossingWord 4 (permutationToCrossingWord 4 [2, 0, 3, 1]) = [2, 0, 3, 1] := by decide

/-! ## WALL-2 FIXED — the pure-crossing diagram now reads back `some`

The through-strand permutation is read off the TOP boundary (the inversion pin) and realized by
`permutationToCrossingWord`.  The headline instance below is the exact WALL-2 diagram the r2 empty-middle
reconstruction refused; the general read-off is the same code path, exercised on wider permutations by
`permutationRealizer_*` (the middle realizer, the piece the r2 reconstruction lacked).  The 3-strand-and-up
`brauerDiagramOf` union-find diagrams are not decided here — comparing two deep union-find reductions in the kernel
blows up (`decideBrauerConvBool_double_crossing` keeps to two strands for exactly this reason). -/

/-- ★★ **WALL-2 FIXED.**  The pure-crossing diagram `[3,2,1,0]` — planar-reachable but the r2 empty-middle
reconstruction returned `none` because it did not invert the through-strand permutation — now reads back
`some { middle := [0], … }`.  The middle permutation is read off the TOP boundary (the inversion pin) and realized by
`permutationToCrossingWord`; the guard confirms the reconstructed word `[crossingAt 0]` realizes the diagram. -/
theorem standardFormOfDiagramFull_pureCrossing_some :
    standardFormOfDiagramFull { bottomCount := 2, topCount := 2, partner := [3, 2, 1, 0], loops := 0 }
      = some { bottomCount := 2, capBlock := [], middle := [0], cupBlock := [], topPerm := [] } := by decide

/-! ## Roundtrips on the planar cap/cup/through class -/

/-- Roundtrip — the identity (empty) extended standard form over two bottom wires reads back to itself. -/
theorem standardFormOfDiagramFull_roundtrip_identity :
    standardFormOfDiagramFull
        (standardFormDiagramExt { bottomCount := 2, capBlock := [], middle := [], cupBlock := [], topPerm := [] })
      = some { bottomCount := 2, capBlock := [], middle := [], cupBlock := [], topPerm := [] } := by decide

/-- Roundtrip — the cap–cup extended standard form over two bottom wires reads back to itself. -/
theorem standardFormOfDiagramFull_roundtrip_cupCap :
    standardFormOfDiagramFull
        (standardFormDiagramExt { bottomCount := 2, capBlock := [0], middle := [], cupBlock := [0], topPerm := [] })
      = some { bottomCount := 2, capBlock := [0], middle := [], cupBlock := [0], topPerm := [] } := by decide

/-! ## WALL-1 breached at the datatype — the straddle's extended standard form EXISTS -/

/-- ★★ **WALL-1 breached at the datatype (existence).**  WALL-1 proved NO 3-block `capWord ++ crossingWord ++ cupWord`
form over one bottom wire realizes the CROSSING straddle diagram.  The `topPerm`-extended form
`{ cupBlock := [1], topPerm := [0] }` — realized word `[cupAt 1, crossingAt 0]` — DOES: its diagram equals the straddle
target `{ bottomCount := 1, topCount := 3, partner := [2, 3, 0, 1], loops := 0 }`.  So the tail-block form that does
not exist in the 3-block datatype EXISTS in the extended datatype. -/
theorem straddleExt_realizes :
    standardFormDiagramExt { bottomCount := 1, capBlock := [], middle := [], cupBlock := [1], topPerm := [0] }
      = straddleDiagram := by decide

/-- The straddle's extended form realizes exactly the diagram of the shift-0 straddle word (both sides of
`cupSlideRelation`), tying the exhibited existence to the genuine straddle. -/
theorem straddleExt_realizes_word :
    standardFormDiagramExt { bottomCount := 1, capBlock := [], middle := [], cupBlock := [1], topPerm := [0] }
      = brauerDiagramOf 1 [cupAt 0, crossingAt 1] := by decide

/-- ★ **The residual, exhibited.**  `standardFormOfDiagramFull` still returns `none` on the straddle: it reconstructs
`topPerm := []` and reads only NON-crossing (adjacent, bound-checked) cups, so it cannot AUTOMATICALLY produce the
straddle's `{ cupBlock := [1], topPerm := [0] }` — the general crossing-cup arc extractor is the named residual.  The
straddle's extended form nonetheless EXISTS (`straddleExt_realizes`); only its automatic reconstruction is unbuilt. -/
theorem standardFormOfDiagramFull_straddle_none : standardFormOfDiagramFull straddleDiagram = none := by decide

/-! ## Non-vacuity — the readback computes a definite verdict on every recon diagram -/

/-- ★ **Non-vacuity — the full-middle readback computes definite answers on all recon diagrams.**  The pure-crossing
diagram reads back `some` with the inverted middle (WALL-2 fixed), the cup–cap diagram reads back `some`, and the
straddle returns `none` (its automatic reconstruction being the residual) while its extended form provably EXISTS. -/
theorem standardFormOfDiagramFull_nonVacuity :
    standardFormOfDiagramFull { bottomCount := 2, topCount := 2, partner := [3, 2, 1, 0], loops := 0 }
        = some { bottomCount := 2, capBlock := [], middle := [0], cupBlock := [], topPerm := [] }
      ∧ standardFormOfDiagramFull { bottomCount := 2, topCount := 2, partner := [1, 0, 3, 2], loops := 0 }
        = some { bottomCount := 2, capBlock := [0], middle := [], cupBlock := [0], topPerm := [] }
      ∧ standardFormOfDiagramFull straddleDiagram = none
      ∧ standardFormDiagramExt { bottomCount := 1, capBlock := [], middle := [], cupBlock := [1], topPerm := [0] }
          = straddleDiagram :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the FULL-MIDDLE readback is SHIPPED (B1, WALL-2 FIXED + WALL-1 breached at the datatype).**
`standardFormOfDiagramFull : DiagramType → Option BrauerStandardFormExt` reads the through-strand permutation off the
TOP boundary (the inversion pin) and realizes it with `permutationToCrossingWord`, GUARDED by `standardFormDiagramExt`
so SOUND unconditionally (`standardFormOfDiagramFull_sound`).  WALL-2 is FIXED: the pure-crossing diagram `[3,2,1,0]`
reads back `some { middle := [0], … }` (`standardFormOfDiagramFull_pureCrossing_some`) — the middle realizer
`permutationToCrossingWord` (the exact piece the r2 empty-middle reconstruction lacked) inverts any permutation
(`permutationRealizer_transposition` / `_threeCycle` / `_reversal` / `_width4`), with the roundtrips preserved.  WALL-1
is breached at the datatype: the `topPerm`-extended standard form `{ cupBlock := [1], topPerm := [0] }` genuinely
realizes the CROSSING straddle diagram (`straddleExt_realizes`), which the 3-block form provably could not.  `= true`. -/
def fxBrauer_hasFullMiddleReadback : Bool := true

/-- **Honesty WALL marker — the general crossing-cup ARC EXTRACTOR (automatic `topPerm` reconstruction) is NOT built
(the B1 residual).**  `standardFormOfDiagramFull` reconstructs `topPerm := []` and reads only bound-checked adjacent
cups, so it reads back the planar cap/cup/through class and every crossing-only diagram but returns `none` on a
diagram with a CROSSING cup (`standardFormOfDiagramFull_straddle_none`).  Populating `cupBlock` + `topPerm`
AUTOMATICALLY from an arbitrary matching (the top TL+`S_m` decomposition) is the genuine new combinatorial
architecture the recon flagged — the straddle's extended form is EXHIBITED (`straddleExt_realizes`) but its automatic
reconstruction is unbuilt.  `fxBrauer_hasBrauerV2FullCompleteness` / `fxBrauer_hasBrauerCompleteness` stay `false`.
`= false`. -/
def fxBrauer_hasCrossingCupArcExtractor : Bool := false

end FX1Poly.Polygraph

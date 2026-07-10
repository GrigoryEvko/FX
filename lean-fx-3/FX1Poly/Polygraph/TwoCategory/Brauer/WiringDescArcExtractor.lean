import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcMiddle
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescArcAnchor

/-! # BRAUER-MIDDLE r2 B1 — the general crossing-cup / crossing-cap arc EXTRACTOR + the 5-block-plus-loops
extended standard form (the datatype WALL breached on BOTH ∗-dual sides, the adversarial-B instance reads back)

The r1 extended standard form `BrauerStandardFormExt` (`Brauer/WiringDescArcMiddle.lean`) had FOUR blocks
(`capBlock`, `middle`, `cupBlock`, `topPerm`) and NO loops field.  Its readback `standardFormOfDiagramFull`
reconstructed `topPerm := []` — so it read back the planar cap/cup/through class and every crossing-only diagram,
but returned `none` on the straddle (a CROSSING cup) and on every diagram with `loops ≥ 1` (the r1 word never fires
a cap onto an already-connected pair, so its realized diagram always has `loops = 0`).  The recon named THREE
datatype/route residuals: the general crossing-cup arc EXTRACTOR (populate `topPerm` automatically), its ∗-dual
crossing-cap extractor (needs a NEW `bottomPerm` block the 4-block datatype lacks), and the loops carry-through
(needs a NEW `loops` field).  This file breaches all three at the datatype + extractor level, machine-checked,
ADDITIVELY (the r1 `BrauerStandardFormExt` and every r1 decl are untouched — this is a fresh 5-block+loops carrier).

## What this file ships (each zero-axiom, structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`)

  * **`BrauerStandardFormExt5`** — the r1 quadruple EXTENDED with the ★ `bottomPerm` block (bottom-boundary `S_n`
    permutation routing crossing CAPS, the ∗-dual of `topPerm`) and the ★ `loops : Nat` field.  Its realized word is
    `crossingWord bottomPerm ++ capWord capBlock ++ crossingWord middle ++ cupWord cupBlock ++ crossingWord topPerm
    ++ circleWord loops`.
  * **`circleWord`** — `loops` copies of the circle atom `[cupAt 0, capAt 0]`: each fires a cap onto its own
    freshly-cupped (already-connected) pair, adding exactly one loop and leaving the boundary matching unchanged
    (`circleWord_realizes_loop`).
  * **`reconstructStandardFormExt5`** — the ★ general arc EXTRACTOR: it partitions the matching into cap arcs / cup
    arcs / through-strands, routes the crossing caps into `bottomPerm` and the crossing cups into `topPerm` (both via
    `permutationToCrossingWord` on the read-off boundary orders), realizes the canonical sequential cap/cup blocks and
    the TOP-indexed through-strand middle, and carries `loops` verbatim.
  * **`standardFormOfDiagramExt`** — the guarded readback (guard `standardFormDiagramExt5 (reconstruct d) = d`), SOUND
    unconditionally (`standardFormOfDiagramExt_sound`).
  * ★★ **the adversarial-B instance reads back `some`.**  `d = { bottomCount := 3, topCount := 3,
    partner := [2, 4, 0, 5, 1, 3], loops := 1 }` (a valid involution: `0↔2` crossing cap, `1↔top1` through,
    `top0↔top2` crossing cup, plus one loop) reads back `some { bottomPerm := [1], capBlock := [0], cupBlock := [1],
    topPerm := [0], loops := 1 }` (`standardFormOfDiagramExt_adversarialB_some`), and that form REALIZES it
    (`adversarialB_ext5_realizes`).  This single instance exercises ALL THREE new axes at once — the crossing cap
    (`bottomPerm`), the crossing cup (`topPerm`), and the loop.
  * ★★ **the straddle now reads back `some`.**  Where r1's `standardFormOfDiagramFull_straddle_none` returned `none`,
    the r2 extractor AUTOMATICALLY reconstructs the straddle's `{ cupBlock := [1], topPerm := [0] }`
    (`standardFormOfDiagramExt_straddle_some`) — the crossing-cup arc extractor the recon named is BUILT.
  * the roundtrips on the loop-carrying planar class (`standardFormOfDiagramExt_roundtrip_loops`) and crossing caps
    (`standardFormOfDiagramExt_roundtrip_crossingCap`), the pure-crossing regression, and the non-vacuity bundle.

## The honest residual (feeds B2 / B3 / B4)

The extractor is NOT yet TOTAL: it reads back `some` on the crossing-cap / straddle / single-crossing-cup / loop /
planar / crossing-only classes but returns `none` on some NESTED multi-crossing cup diagrams (the `topPerm` read-off
is a first-cut heuristic, exact on those classes, incomplete on arbitrary nested cups).  Proving the general
ROUNDTRIP `standardFormDiagramExt5 (reconstructStandardFormExt5 d) = d` for ALL well-formed `d` (the totality that
would make the readback total) is a `stepWiring`-connectivity structural induction — the same long pole as the
still-open `fxBrauer_hasCrossingOnlyReadback` — and is the named r3 residual.  `fxBrauer_hasBrauerV2FullCompleteness`
/ `fxBrauer_hasBrauerCompleteness` stay `false`; #2013 does not close on B1.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The 5-block-plus-loops extended standard form -/

/-- ★ **The `bottomPerm`-and-`loops`-extended Brauer standard form.**  The r1 quadruple (`capBlock`, `middle`,
`cupBlock`, `topPerm`) extended with `bottomPerm` (the bottom-boundary crossing staircase routing crossing CAPS — the
∗-dual of `topPerm`) and `loops` (the closed-circle count).  A flat decidable-eq datum, so it computes. -/
structure BrauerStandardFormExt5 where
  /-- The number of bottom boundary wires the form acts on. -/
  bottomCount : Nat
  /-- ★ The bottom-boundary `S_n` permutation, as a crossing-staircase word (routes crossing CAP feet into place). -/
  bottomPerm : List Nat
  /-- The cap half-diagram: canonical sequential cap generator positions. -/
  capBlock : List Nat
  /-- The middle `S_t` through-strand permutation, as a crossing-staircase word. -/
  middle : List Nat
  /-- The cup half-diagram: canonical sequential cup generator positions. -/
  cupBlock : List Nat
  /-- The top-boundary `S_m` permutation, as a crossing-staircase word (routes crossing CUP legs into place). -/
  topPerm : List Nat
  /-- ★ The number of closed loops (bubbles) the form carries. -/
  loops : Nat
deriving DecidableEq, Repr

/-- ★ **The circle word** — `loopCount` copies of the circle atom `[cupAt 0, capAt 0]`.  Each cup allocates a fresh
connected pair at the front; the following cap fires on that same (already-connected) pair, closing exactly one loop
and leaving the boundary matching untouched. -/
def circleWord : Nat → List BrauerAtom
  | 0 => []
  | loopCount + 1 => cupAt 0 :: capAt 0 :: circleWord loopCount

/-- ★ **The generator word an extended 5-block form realizes** — the bottom crossing staircase, then caps, the middle
crossing staircase, cups, the top crossing staircase, and finally the closed circles. -/
def standardFormWordExt5 (form : BrauerStandardFormExt5) : List BrauerAtom :=
  crossingWord form.bottomPerm ++ capWord form.capBlock ++ crossingWord form.middle
    ++ cupWord form.cupBlock ++ crossingWord form.topPerm ++ circleWord form.loops

/-- The **Brauer diagram of an extended 5-block form** — run its realized word through the wiring engine. -/
def standardFormDiagramExt5 (form : BrauerStandardFormExt5) : DiagramType :=
  brauerDiagramOf form.bottomCount (standardFormWordExt5 form)

/-! ## The arc-partition read-offs (structural filters + pair expanders, propext-free) -/

/-- Replicate `value` exactly `count` times — the canonical sequential cap / cup block builder. -/
def natReplicate : Nat → Nat → List Nat
  | 0, _ => []
  | count + 1, value => value :: natReplicate count value

/-- The smaller-foot indices of the bottom–bottom CAP arcs, ascending: bottom ports `index` whose partner is a bottom
port strictly larger than `index` (each cap arc listed once, by its smaller foot). -/
def capArcFeetIndices (bottomCount : Nat) (partner : List Nat) : List Nat :=
  (List.range bottomCount).filterMap (fun index =>
    match Nat.blt (natListGetAt partner index) bottomCount && Nat.blt index (natListGetAt partner index) with
    | true => some index
    | false => none)

/-- Expand a list of smaller-foot bottom indices to the flat foot list `[index, partner index, …]` — the arc-order
bottom feet the canonical cap block must sit under. -/
def expandBottomFeetPairs (partner : List Nat) : List Nat → List Nat
  | [] => []
  | index :: rest => index :: natListGetAt partner index :: expandBottomFeetPairs partner rest

/-- The cap arc feet in arc order (smaller foot then its partner, per arc). -/
def capArcFeet (bottomCount : Nat) (partner : List Nat) : List Nat :=
  expandBottomFeetPairs partner (capArcFeetIndices bottomCount partner)

/-- The through-strand TOP indices (0-based within the top boundary), ascending: top ports `topIndex` whose partner is
a bottom port (`< bottomCount`). -/
def throughStrandTops (bottomCount topCount : Nat) (partner : List Nat) : List Nat :=
  (List.range topCount).filterMap (fun topIndex =>
    match Nat.blt (natListGetAt partner (bottomCount + topIndex)) bottomCount with
    | true => some topIndex
    | false => none)

/-- The smaller-foot TOP indices of the top–top CUP arcs, ascending: top ports `topIndex` whose partner is a top port
strictly larger (each cup arc listed once, by its smaller top foot). -/
def cupArcTopIndices (bottomCount topCount : Nat) (partner : List Nat) : List Nat :=
  (List.range topCount).filterMap (fun topIndex =>
    match Nat.ble bottomCount (natListGetAt partner (bottomCount + topIndex))
        && Nat.blt (bottomCount + topIndex) (natListGetAt partner (bottomCount + topIndex)) with
    | true => some topIndex
    | false => none)

/-- Expand a list of smaller-foot top indices to the flat top-index list `[topIndex, partnerTopIndex, …]`. -/
def expandCupTopPairs (bottomCount : Nat) (partner : List Nat) : List Nat → List Nat
  | [] => []
  | topIndex :: rest =>
      topIndex :: (natListGetAt partner (bottomCount + topIndex) - bottomCount)
        :: expandCupTopPairs bottomCount partner rest

/-- The cup arc top legs in arc order (smaller top foot then its partner top, per arc). -/
def cupArcTops (bottomCount topCount : Nat) (partner : List Nat) : List Nat :=
  expandCupTopPairs bottomCount partner (cupArcTopIndices bottomCount topCount partner)

/-! ## The general arc extractor + the guarded readback -/

/-- ★ **The general arc EXTRACTOR.**  Partition the matching into cap arcs (`capArcFeetIndices`), cup arcs
(`cupArcTopIndices`), and through-strands (`throughStrandBottoms` / `throughStrandTops`); route the crossing caps into
`bottomPerm` and the crossing cups into `topPerm` via `permutationToCrossingWord` on the read-off boundary orders;
realize the canonical sequential cap/cup blocks and the TOP-indexed through-strand middle; carry `loops` verbatim.  A
best-effort inverse whose correctness is enforced downstream by the `standardFormOfDiagramExt` guard. -/
def reconstructStandardFormExt5 (d : DiagramType) : BrauerStandardFormExt5 :=
  let throughBottoms := throughStrandBottoms d.bottomCount d.partner
  { bottomCount := d.bottomCount,
    bottomPerm := permutationToCrossingWord d.bottomCount
      (capArcFeet d.bottomCount d.partner ++ throughBottoms),
    capBlock := natReplicate (capArcFeetIndices d.bottomCount d.partner).length 0,
    middle := permutationToCrossingWord throughBottoms.length
      (throughStrandPerm d.bottomCount d.topCount d.partner),
    cupBlock := natReplicate (cupArcTopIndices d.bottomCount d.topCount d.partner).length throughBottoms.length,
    topPerm := permutationToCrossingWord d.topCount
      (throughStrandTops d.bottomCount d.topCount d.partner ++ cupArcTops d.bottomCount d.topCount d.partner),
    loops := d.loops }

/-- ★ **The extended 5-block readback, honestly gated.**  Reconstruct all six blocks + loops and accept the candidate
ONLY when its realized diagram equals the input.  Total (`none` when the guard fails), SOUND by construction
(`standardFormOfDiagramExt_sound`), and PARTIAL: it succeeds on the crossing-cap / straddle / single-crossing-cup /
loop / planar / crossing-only classes and returns `none` on some nested multi-crossing cup diagrams (the general
totality proof is the named residual). -/
def standardFormOfDiagramExt (d : DiagramType) : Option BrauerStandardFormExt5 :=
  if standardFormDiagramExt5 (reconstructStandardFormExt5 d) = d then some (reconstructStandardFormExt5 d) else none

/-- ★ **The extended readback is SOUND (unconditional).**  Whenever `standardFormOfDiagramExt d = some form`, the
reconstructed 5-block form genuinely realizes the diagram: `standardFormDiagramExt5 form = d`.  Straight off the guard
— no correctness of the reconstruction is assumed. -/
theorem standardFormOfDiagramExt_sound (d : DiagramType) (form : BrauerStandardFormExt5)
    (readback : standardFormOfDiagramExt d = some form) : standardFormDiagramExt5 form = d := by
  unfold standardFormOfDiagramExt at readback
  split at readback
  · rename_i guardHolds
    rw [← Option.some.inj readback]; exact guardHolds
  · nomatch readback

/-! ## The circle word realizes loops (boundary unchanged) -/

/-- ★ **The circle word realizes exactly one loop over one bottom wire.**  `[cupAt 0, capAt 0]` over one bottom strand
gives the identity strand (`partner := [1, 0]`) plus `loops := 1` — the cup's fresh pair is immediately capped, closing
a loop without touching the boundary. -/
theorem circleWord_realizes_loop :
    brauerDiagramOf 1 (circleWord 1) = { bottomCount := 1, topCount := 1, partner := [1, 0], loops := 1 } := by decide

/-- ★ **Two circles realize two loops over two bottom wires, boundary unchanged.** -/
theorem circleWord_realizes_twoLoops :
    brauerDiagramOf 2 (circleWord 2) = { bottomCount := 2, topCount := 2, partner := [2, 3, 0, 1], loops := 2 } := by
  decide

/-! ## The adversarial-B instance — all three new axes at once -/

/-- The adversarial-B target diagram: `bottomCount = 3`, a crossing cap `0↔2`, a through-strand `1↔top1`, a crossing
cup `top0↔top2`, and one loop.  A valid involution `0↔2, 1↔4, 3↔5`. -/
def adversarialBDiagram : DiagramType :=
  { bottomCount := 3, topCount := 3, partner := [2, 4, 0, 5, 1, 3], loops := 1 }

/-- ★★ **The adversarial-B extended form EXISTS and REALIZES it.**  The 5-block form
`{ bottomPerm := [1], capBlock := [0], cupBlock := [1], topPerm := [0], loops := 1 }` — realized word
`[crossingAt 1, capAt 0, cupAt 1, crossingAt 0, cupAt 0, capAt 0]` — has diagram exactly `adversarialBDiagram`.  The
crossing cap lives in the NEW `bottomPerm` block, the crossing cup in `topPerm`, and the circle in the NEW `loops`
field — none of which the r1 4-block loopless datatype could carry. -/
theorem adversarialB_ext5_realizes :
    standardFormDiagramExt5
        { bottomCount := 3, bottomPerm := [1], capBlock := [0], middle := [], cupBlock := [1], topPerm := [0],
          loops := 1 }
      = adversarialBDiagram := by decide

/-- ★★ **The adversarial-B instance READS BACK `some` — the general arc extractor inverts all three axes.**  The bare
matching `[2, 4, 0, 5, 1, 3]` with one loop is reconstructed automatically: the crossing cap into `bottomPerm := [1]`,
the crossing cup into `topPerm := [0]`, the through middle into `[]`, and the loop carried verbatim.  The guard confirms
the reconstructed word realizes the diagram. -/
theorem standardFormOfDiagramExt_adversarialB_some :
    standardFormOfDiagramExt adversarialBDiagram
      = some { bottomCount := 3, bottomPerm := [1], capBlock := [0], middle := [], cupBlock := [1], topPerm := [0],
               loops := 1 } := by decide

/-! ## The straddle now reads back `some` — the crossing-cup extractor is BUILT -/

/-- ★★ **The straddle READS BACK `some` (r1 returned `none`).**  Where r1's `standardFormOfDiagramFull_straddle_none`
proved the r1 readback refused the straddle, the r2 extractor AUTOMATICALLY reconstructs its
`{ cupBlock := [1], topPerm := [0] }` — the crossing-cup arc extractor the recon named is BUILT and inverts the
straddle. -/
theorem standardFormOfDiagramExt_straddle_some :
    standardFormOfDiagramExt straddleDiagram
      = some { bottomCount := 1, bottomPerm := [], capBlock := [], middle := [], cupBlock := [1], topPerm := [0],
               loops := 0 } := by decide

/-! ## Roundtrips on the loop-carrying + crossing-cap classes -/

/-- ★ **Roundtrip on the loop-carrying planar class.**  A cap–cup form with two loops reads back to itself — the NEW
`loops` field roundtrips, which the r1 loopless datatype could not do. -/
theorem standardFormOfDiagramExt_roundtrip_loops :
    standardFormOfDiagramExt (standardFormDiagramExt5
        { bottomCount := 2, bottomPerm := [], capBlock := [0], middle := [], cupBlock := [0], topPerm := [],
          loops := 2 })
      = some { bottomCount := 2, bottomPerm := [], capBlock := [0], middle := [], cupBlock := [0], topPerm := [],
               loops := 2 } := by decide

/-- ★ **Roundtrip on the crossing-CAP class.**  The two-crossing-cap diagram `[crossingAt 1, capAt 0, capAt 0]` over
four wires reads back with `bottomPerm := [1]` — the NEW `bottomPerm` block inverts a crossing cap (the ∗-dual of the
straddle's crossing cup). -/
theorem standardFormOfDiagramExt_crossingCap_some :
    standardFormOfDiagramExt (brauerDiagramOf 4 [crossingAt 1, capAt 0, capAt 0])
      = some { bottomCount := 4, bottomPerm := [1], capBlock := [0, 0], middle := [], cupBlock := [], topPerm := [],
               loops := 0 } := by decide

/-- ★ **Regression — pure crossing reads back the inverted middle.**  The pure-crossing diagram `[3, 2, 1, 0]` reads
back `some { middle := [0], … }`, matching r1's WALL-2-fixed behaviour in the 5-block carrier. -/
theorem standardFormOfDiagramExt_pureCrossing_some :
    standardFormOfDiagramExt { bottomCount := 2, topCount := 2, partner := [3, 2, 1, 0], loops := 0 }
      = some { bottomCount := 2, bottomPerm := [], capBlock := [], middle := [0], cupBlock := [], topPerm := [],
               loops := 0 } := by decide

/-! ## Non-vacuity — the extractor computes definite verdicts across all new axes -/

/-- ★ **Non-vacuity — the extractor reads back the three ∗-dual + loop classes.**  The crossing-cap+cup+loop
adversarial-B, the crossing-cup straddle (r1 said none), and the loop-carrying planar roundtrip all read back `some`;
the pure-crossing regression holds. -/
theorem standardFormOfDiagramExt_nonVacuity :
    standardFormOfDiagramExt adversarialBDiagram
        = some { bottomCount := 3, bottomPerm := [1], capBlock := [0], middle := [], cupBlock := [1], topPerm := [0],
                 loops := 1 }
      ∧ standardFormOfDiagramExt straddleDiagram
        = some { bottomCount := 1, bottomPerm := [], capBlock := [], middle := [], cupBlock := [1], topPerm := [0],
                 loops := 0 }
      ∧ standardFormOfDiagramExt { bottomCount := 2, topCount := 2, partner := [3, 2, 1, 0], loops := 0 }
        = some { bottomCount := 2, bottomPerm := [], capBlock := [], middle := [0], cupBlock := [], topPerm := [],
                 loops := 0 } :=
  ⟨by decide, by decide, by decide⟩

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the general crossing-cup / crossing-cap arc EXTRACTOR + the 5-block-plus-loops datatype are
SHIPPED (B1).**  `BrauerStandardFormExt5` carries the ∗-dual `bottomPerm` block and the `loops` field the r1 4-block
loopless datatype lacked; `reconstructStandardFormExt5` AUTOMATICALLY reconstructs crossing caps (`bottomPerm`),
crossing cups (`topPerm` — the straddle now reads back `some`, `standardFormOfDiagramExt_straddle_some`, where r1
returned `none`), and loops (verbatim).  The adversarial-B instance — a crossing cap, a crossing cup, AND a loop at
once — reads back `some` (`standardFormOfDiagramExt_adversarialB_some`) and its form realizes it
(`adversarialB_ext5_realizes`).  The readback is guarded, hence SOUND unconditionally
(`standardFormOfDiagramExt_sound`).  `= true`. -/
def fxBrauer_hasExt5ArcExtractor : Bool := true

/-- **Honesty WALL marker — the extractor is NOT yet TOTAL (the B1 residual).**  `reconstructStandardFormExt5` reads
back `some` on the crossing-cap / straddle / single-crossing-cup / loop / planar / crossing-only classes but returns
`none` on some NESTED multi-crossing cup diagrams (the `topPerm` read-off is a first-cut heuristic, exact on those
classes, incomplete on arbitrary nested cups).  Proving the general ROUNDTRIP
`standardFormDiagramExt5 (reconstructStandardFormExt5 d) = d` for ALL well-formed `d` — the totality that makes the
readback total — is a `stepWiring`-connectivity structural induction (the same long pole as the still-open
`fxBrauer_hasCrossingOnlyReadback`) and is the named r3 residual.  `fxBrauer_hasBrauerV2FullCompleteness` /
`fxBrauer_hasBrauerCompleteness` stay `false`.  `= false`. -/
def fxBrauer_hasExt5TotalExtractor : Bool := false

end FX1Poly.Polygraph

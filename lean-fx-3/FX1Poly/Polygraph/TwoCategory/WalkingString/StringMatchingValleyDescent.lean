import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingCompleteness
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyDisorder

/-! # WalkingString — the valley-descent driver at the three-generator seed (the completeness residual, SHARPENED)

Round 3 named ONE monolithic completeness residual `StringMatchingReductsShareSpineTrace` (parallel cells with equal
boundary matching have saturated reducts whose spines are trace-equivalent) and reduced the whole adjoint-triple
DECISION to it.  This file ports the walking-adjunction's `SaturatedTwoCellConv`-valued fuel-structural descent
DRIVER (`SpineValleyCellDriver`) to the string signature `adjointTripleModeSignature`, thereby FACTORING that one
monolithic residual into exactly TWO named sub-producers — the per-step move ORACLE and the cell-level Piece-II
trace-equivalence — riding the r2 UNCONDITIONAL master hinge `stringSaturatedConv_matchingOf_eq_final` (no
per-step matching tracking).

## What ports cleanly (this file), and why

The driver's substrate is entirely COLOUR-BLIND and already `{signature}`-polymorphic or `{α}`-generic upstream:
the inversion measure `spineDisorder`, the valley predicate `isCapThenCupValley SpineAtom.isCupAtom`, the
zero-disorder valley `valley_of_disorder_zero`, and the trace relation `SpineTraceEquiv`.  The only
adjunction-specific inputs the adjunction driver names are (1) its saturated relation's `refl`/`trans`/`symm` — the
string has its own (`StringSaturatedTwoCellConv`) — and (2) the master hinge `matchingOf_invariant_ofSaturatedConv`
— the string has the r2 UNCONDITIONAL `stringSaturatedConv_matchingOf_eq_final`.  So the descent's ACCUMULATION +
TERMINATION half is a direct structural clone at the three-generator seed:

  * ★ `StringCellDescentResult` / `StringCellValleyResult` — the per-step and whole-descent carriers.
  * ★ `stringValleyDescentDriverCell` — the fuel-structural driver (NO `WellFounded.fix` — structural recursion on
    the fuel `Nat`, the tag driver's `Nat.le_of_lt_succ` budget argument, conv-carrying), gluing the per-step
    oracle's conversions by `StringSaturatedTwoCellConv.trans` down to a valley.
  * ★ `stringValleyNFCell` / `stringCellDescentConv` / `stringValleyNFCell_isValley` — the normal form and its two
    read-offs.
  * ★ `stringMatchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv` — the REDUCTION: given a per-step
    `StringCellDescentStepOracle` AND the cell-level `StringCellValleyTraceEquiv`, the monolithic residual
    `StringMatchingReductsShareSpineTrace` holds.  The reducts are the two valley normal forms; their matchings
    agree by the master hinge `stringSaturatedConv_matchingOf_eq_final` (sandwiching the hypothesis), and Piece II
    supplies the trace equivalence.

So the monolithic residual is now SHARPENED from one Prop to two: `StringMatchingReductsShareSpineTrace` follows
from `(StringCellDescentStepOracle) × (StringCellValleyTraceEquiv)`, exactly as the adjunction's
`matchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv` sharpened its residual.

## ★ The EXACT new three-generator obstruction — the walking adjoint triple is NOT length-rigid

Neither of the two sub-producers ports by instantiation, and the reason is ONE concrete, honestly-named fact.  The
walking ADJUNCTION quiver has exactly ONE modality out of each mode, so `adjunctionPath_eq_of_length_eq` holds:
parallel 1-cells of equal LENGTH are EQUAL (`AdjunctionPathRigidity`).  The whole Piece-II valley-trace
reconstruction (`cellValleyTraceEquiv_holds`, gated on `cupRestrict_reconstructs`, which reads atoms through
LENGTHS) and the STRAIGHTEN band collapse (`zigZagBandCollapse*` via `cupCapDeletionReconnects`, which reconnects
the outer legs of a deleted cup·cap by their LENGTHS) both REST on that rigidity.

The walking ADJOINT-TRIPLE quiver is NOT length-rigid: out of `base` there are TWO modalities — `F = left` and
`H = coLeft`, both `base ⟶ tip`, both length 1, but DISTINCT (`string_left_ne_coLeft`).  So
`adjunctionPath_eq_of_length_eq` is FALSE at the string signature.  Two concrete consequences, each a genuine new
node with no adjunction analog:

  * **The oracle's STRAIGHTEN arm needs COLOUR-awareness.**  The classifier `classifyAdjacentAtoms` reads only the
    cup/cap left-context WIDTHS (colour-blind), so it can route a MIXED-colour adjacent pair — a lower cup `η`
    (opens `F,G`) next to an UPPER cap `ε'` (closes `H,G`) with the shared-leg widths — to the `zigZagSharedLeg`
    STRAIGHTEN arm.  Straightening then demands the outer legs reconnect (`cupCapDeletionReconnects`): the `F` leg
    of `η` must equal the `H` leg of `ε'`, i.e. `F = H` — FALSE (`string_left_ne_coLeft`).  In the length-rigid
    adjunction this never arises (one modality per mode ⟹ width DETERMINES colour); at three generators the
    width-only classifier is colour-BLIND where colour now matters.  So the string oracle's STRAIGHTEN dispatch is
    NOT the ported `straightenCellDescentStep` — it needs the mixed-colour refutation (a genuine new lemma,
    `stringSharedLegForcesSameColour`: a shared-leg cup·cap in the string is SAME-colour) before the band collapse
    can fire, and the collapse itself must be re-derived generator-aware.
  * **Piece II is a multi-round re-derivation, not a re-home.**  `cellValleyTraceEquiv_holds` (~200 upstream files)
    reconstructs a valley's spine from its matching by length-rigid atom determination; at three generators the
    reconstruction must be re-derived from the BOUNDARY labels (which DO determine every valley generator's colour —
    a valley cap on source ports `(G,F)` is `ε`, on `(H,G)` is `ε'`; a valley cup on target ports `(F,G)` is `η`,
    on `(G,H)` is `η'`), not from lengths.  This is a colour-aware Piece II, a multi-round arc.

Both consequences confirm the deep-literature position: there is a decidable NF for the SINGLE free adjunction
(Schanuel–Street Δ₊ / Riehl–Verity squiggles), but NO citable free-adjoint-STRING word-problem NF theorem
(Rosebrugh–Wood recover Δ but prove no NF/decision; Riva–Rovelli only speculate on higher dimensions).  So the
string decision is genuinely new mathematics — the per-colour factorization (colours are boundary-determined on
valleys, so completeness stays colour-BLIND and `fxString_hasAdjointTripleCoherenceGap = false`), NOT a re-run of
the two-letter staircase.

## What this file does NOT close (the flag stays `false`)

`stringMatchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv` reduces the monolithic residual to two
sub-producers; NEITHER is discharged here (each needs the colour-aware re-derivation the length-rigidity failure
forces).  So `StringMatchingReductsShareSpineTrace`, `stringConvOfMapEq_ofReductsShareSpineTrace` (unconditional),
`decidableStringSaturatedConv` (total), and `fxString_hasAdjointTripleCompleteness` all stay `false`/gated.  This
round SHARPENS the residual and NAMES the exact obstruction; it does not flip the completeness gate.

Raw Lean 4 + Init; the driver is structural recursion on the fuel `Nat`, the reduction is
`stringSaturatedConv_matchingOf_eq_final` + saturated `trans`/`symm`.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The per-step and whole-descent carriers -/

/-- One descent STEP on a non-valley string cell: a next cell, a saturated conversion to it, and a strict disorder
drop.  The classified STRAIGHTEN (delete a collapsing snake) | COMMUTE (transpose disjoint atoms) per-step move
packaged as data — the string analog of the adjunction's `CellDescentResult`. -/
structure StringCellDescentResult {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) where
  /-- The cell after one straighten/commute step. -/
  next : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath
  /-- The step is a saturated conversion. -/
  stepConv : StringSaturatedTwoCellConv cell next
  /-- The step strictly drops the disorder measure. -/
  disorderDrops : spineDisorder next.spine < spineDisorder cell.spine

/-- The whole descent to a valley: a valley cell, the accumulated saturated conversion, and the valley witness. -/
structure StringCellValleyResult {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) where
  /-- The valley normal form reached. -/
  valley : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath
  /-- The accumulated saturated conversion from the source cell to the valley. -/
  descentConv : StringSaturatedTwoCellConv cell valley
  /-- The reached cell is a cap-block-then-cup-block valley. -/
  valleyIsValley : isCapThenCupValley SpineAtom.isCupAtom valley.spine = true

/-- ★ The per-step move ORACLE — the FIRST of the two sub-producers the monolithic residual sharpens into.  For any
non-valley string cell it produces a `StringCellDescentResult`.  Un-shipped: dispatching STRAIGHTEN vs COMMUTE at
three generators needs the mixed-colour refutation the width-only classifier cannot supply (a lower cup `η` next to
an upper cap `ε'` shares a leg by WIDTH but the outer legs `F`/`H` do not reconnect — `string_left_ne_coLeft`), the
genuine new node forced by the length-rigidity failure. -/
def StringCellDescentStepOracle : Type :=
  ∀ {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath),
    isCapThenCupValley SpineAtom.isCupAtom cell.spine = false → StringCellDescentResult cell

/-! ## The fuel-structural driver -/

/-- ★ **The `StringSaturatedTwoCellConv`-valued fuel-structural driver.**  While the cell's spine is not a valley,
fire the oracle, recurse on decremented fuel, and glue the accumulated conversion by
`StringSaturatedTwoCellConv.trans`.  NO `WellFounded.fix` — structural recursion on the fuel `Nat`, whose budget
(the initial disorder) is discharged as sufficient exactly as in the tag driver (`Nat.le_of_lt_succ` on the strict
drop).  The base case is `refl` on the already-a-valley cell.  A direct clone of the adjunction's
`valleyDescentDriverCell` at the three-generator seed. -/
def stringValleyDescentDriverCell (oracle : StringCellDescentStepOracle) :
    (fuel : Nat) → {sourceMode targetMode : AdjointTripleMode} →
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode} →
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) →
    spineDisorder cell.spine ≤ fuel → StringCellValleyResult cell
  | 0, _, _, _, _, cell, disorderLe =>
      ⟨cell, StringSaturatedTwoCellConv.refl cell,
        valley_of_disorder_zero SpineAtom.isCupAtom
          (Nat.le_antisymm disorderLe (Nat.zero_le _))⟩
  | fuel + 1, _, _, _, _, cell, disorderLe =>
      match hValley : isCapThenCupValley SpineAtom.isCupAtom cell.spine with
      | true => ⟨cell, StringSaturatedTwoCellConv.refl cell, hValley⟩
      | false =>
          let step := oracle cell hValley
          let subDescent := stringValleyDescentDriverCell oracle fuel step.next
            (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le step.disorderDrops disorderLe))
          ⟨subDescent.valley,
            StringSaturatedTwoCellConv.trans step.stepConv subDescent.descentConv,
            subDescent.valleyIsValley⟩

/-- The valley normal form of a string cell — run the driver with fuel equal to the cell's initial disorder. -/
def stringValleyNFCell (oracle : StringCellDescentStepOracle) {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath :=
  (stringValleyDescentDriverCell oracle (spineDisorder cell.spine) cell (Nat.le_refl _)).valley

/-- ★ **The descent conversion** — `cell ≈ stringValleyNFCell cell`, the accumulated saturated conversion. -/
theorem stringCellDescentConv (oracle : StringCellDescentStepOracle) {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    StringSaturatedTwoCellConv cell (stringValleyNFCell oracle cell) :=
  (stringValleyDescentDriverCell oracle (spineDisorder cell.spine) cell (Nat.le_refl _)).descentConv

/-- ★ **The normal form is a valley** — its spine is a cap-block-then-cup-block valley. -/
theorem stringValleyNFCell_isValley (oracle : StringCellDescentStepOracle)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath) :
    isCapThenCupValley SpineAtom.isCupAtom (stringValleyNFCell oracle cell).spine = true :=
  (stringValleyDescentDriverCell oracle (spineDisorder cell.spine) cell (Nat.le_refl _)).valleyIsValley

/-! ## The reduction of `StringMatchingReductsShareSpineTrace` to the two sub-producers -/

/-- ★ The cell-level Piece-II input — the SECOND of the two sub-producers.  Two VALLEY string cells with equal
boundary matching have trace-equivalent spines.  At three generators the reconstruction is COLOUR-aware: a valley's
generators are determined by its BOUNDARY labels + partner matching (a valley cap on source `(G,F)` is `ε`, on
`(H,G)` is `ε'`; a valley cup on target `(F,G)` is `η`, on `(G,H)` is `η'`), NOT by lengths — so the
length-rigid adjunction reconstruction does not re-home.  Stated as a hypothesis so the reduction is honest about
its second residual. -/
def StringCellValleyTraceEquiv : Prop :=
  ∀ {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (valleyA valleyB : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath),
    isCapThenCupValley SpineAtom.isCupAtom valleyA.spine = true →
    isCapThenCupValley SpineAtom.isCupAtom valleyB.spine = true →
    matchingOf valleyA = matchingOf valleyB →
    SpineTraceEquiv adjointTripleModeSignature valleyA.spine valleyB.spine

/-- ★ **The honest reduction — the monolithic residual SHARPENED into the two sub-producers.**  Given the per-step
`oracle` (Piece I descent) AND the cell-level Piece-II input `valleyTraceEquiv`, the monolithic residual
`StringMatchingReductsShareSpineTrace` holds: instantiate the reducts as the two valley normal forms.  Each reduct
is saturated-convertible to its source (`stringCellDescentConv`); the reducts' matchings agree because `matchingOf`
is a descent invariant (the r2 UNCONDITIONAL master hinge `stringSaturatedConv_matchingOf_eq_final` sandwiching the
hypothesis — NO per-step matching tracking); both reducts are valleys (`stringValleyNFCell_isValley`); Piece II then
delivers the residual `SpineTraceEquiv`.  No `reify`, no canonical-cell function.  The string analog of the
adjunction's `matchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv`. -/
theorem stringMatchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv
    (oracle : StringCellDescentStepOracle) (valleyTraceEquiv : StringCellValleyTraceEquiv) :
    StringMatchingReductsShareSpineTrace := by
  intro sourceMode targetMode sourcePath targetPath cellA cellB matchingsEqual
  refine ⟨stringValleyNFCell oracle cellA, stringValleyNFCell oracle cellB,
    stringCellDescentConv oracle cellA, stringCellDescentConv oracle cellB, ?_⟩
  have matchingReductA : matchingOf (stringValleyNFCell oracle cellA) = matchingOf cellA :=
    (stringSaturatedConv_matchingOf_eq_final (stringCellDescentConv oracle cellA)).symm
  have matchingReductB : matchingOf (stringValleyNFCell oracle cellB) = matchingOf cellB :=
    (stringSaturatedConv_matchingOf_eq_final (stringCellDescentConv oracle cellB)).symm
  exact valleyTraceEquiv (stringValleyNFCell oracle cellA) (stringValleyNFCell oracle cellB)
    (stringValleyNFCell_isValley oracle cellA) (stringValleyNFCell_isValley oracle cellB)
    (matchingReductA.trans (matchingsEqual.trans matchingReductB.symm))

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the valley-descent DRIVER is ported to the three-generator seed; the monolithic completeness
residual is SHARPENED into two named sub-producers.**  `stringValleyDescentDriverCell` (fuel-structural, no
`WellFounded.fix`) glues a per-step oracle's conversions by `StringSaturatedTwoCellConv.trans` down to a valley,
discharging the fuel budget by the tag driver's argument; it yields `stringCellDescentConv : cell ≈
stringValleyNFCell cell` and `stringValleyNFCell_isValley`.  The reduction
`stringMatchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv` derives the monolithic residual
`StringMatchingReductsShareSpineTrace` from `(StringCellDescentStepOracle) × (StringCellValleyTraceEquiv)`, threading
the equal matching through the reducts by the r2 UNCONDITIONAL master hinge `stringSaturatedConv_matchingOf_eq_final`
alone — no per-step matching tracking, no `reify`, no canonical cell.  The colour-blind substrate (`spineDisorder`,
`isCapThenCupValley`, `valley_of_disorder_zero`, `SpineTraceEquiv`) ports verbatim.  `= true`. -/
def fxString_hasStringValleyDescentDriver : Bool := true

/-- **★ HONEST WALL RECORD — the two sub-producers do NOT port by instantiation; the string quiver is NOT
length-rigid.**  The walking adjunction's `adjunctionPath_eq_of_length_eq` (parallel 1-cells of equal LENGTH are
EQUAL — one modality per mode) underpins BOTH the STRAIGHTEN band collapse (`cupCapDeletionReconnects` reconnects a
deleted cup·cap's outer legs by their lengths) AND the Piece-II valley reconstruction (`cupRestrict_reconstructs`
reads atoms through lengths).  At the string signature this rigidity is FALSE: out of `base` there are TWO
modalities `F = left` and `H = coLeft`, both length-1 and DISTINCT (`string_left_ne_coLeft`).

  Two concrete new nodes, each with no adjunction analog:
  * the oracle's STRAIGHTEN arm is colour-BLIND where colour now matters — the width-only `classifyAdjacentAtoms`
    can route a MIXED-colour pair (lower cup `η` opening `F,G` next to upper cap `ε'` closing `H,G`) to the
    `zigZagSharedLeg` arm, whose reconnect then demands `F = H` (FALSE).  The string oracle needs the mixed-colour
    refutation `stringSharedLegForcesSameColour` and a generator-aware band collapse;
  * Piece II (`StringCellValleyTraceEquiv`) must be re-derived from BOUNDARY labels (which DO determine every valley
    generator's colour), not from lengths — a multi-round colour-aware reconstruction.

  This is NOT a coherence gap (`fxString_hasAdjointTripleCoherenceGap` stays `false`): colours are
  boundary-determined on valleys, so completeness stays colour-BLIND — the residual is a genuine PORT of new
  mathematics (there is no citable free-adjoint-STRING NF theorem), not a semantic wall.  `= true`. -/
def fxString_hasStringLengthRigidityFailure : Bool := true

end FX1Poly.Polygraph

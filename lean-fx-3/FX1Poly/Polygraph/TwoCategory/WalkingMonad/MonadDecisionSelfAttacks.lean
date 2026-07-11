import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordProblem

/-! # WalkingMonad — concrete-word TRUTH-PROBES of the closed saturated decision (self-attack corpus)

`WalkingMonad/MonadWordProblem` closed the walking-monad saturated 2-cell word problem: the full normalization
`monadNormalize`, the inhabited canonicalization `monadSaturatedCanonicalization`, and the unconditional decision
`monadSaturatedTwoCellDecision`, with two-way non-vacuity at WIDTH THREE (`monadDecision_yes_assoc`, both foldings
`t·t·t ⇒ t` share the degeneracy `[0, 0, 0]`) and the WIDTH-ONE faces (`monadDecision_no_faces`, `δ₁`=`[1]` vs
`δ₀`=`[0]`).

This file is the TRUTH-PROBE layer: it exercises the ALREADY-CLOSED machinery on fresh concrete words the shipped
smokes never touched, machine-checking the sort's block-sum output (`composeCounts`) and the Schanuel–Street fold
(`monadMonotoneMapOf`) by `rfl` on concrete inputs.  Nothing here is load-bearing for the closure; every declaration
is a concrete evaluation confirming the green decision genuinely computes.  The convertibility VERDICTS on these
words are the self-attack theorems in the companion `MonadDecisionSelfAttacks` B2 section below.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; every probe is `rfl` on
a structural fold.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The block-sum re-sort on concrete words (the `wordMul_vcomp` data output) -/

/-- Truth-probe: the block-sum composition `composeCounts` — the concrete output of the vertical word
multiplicativity `wordMul_vcomp` — on a two-block/one-block concrete word. -/
theorem monadComposeCounts_probe_twoOne : composeCounts [1, 1] [2] = [2] := rfl

/-- Truth-probe: `composeCounts` on a two-block left word with a two-block right word (a fresh concrete pair the
shipped smokes never touched). -/
theorem monadComposeCounts_probe_mixed : composeCounts [1, 0] [2, 1] = [1, 0] := rfl

/-- Truth-probe: `composeCounts` on a single-block left word folded against a two-block right word. -/
theorem monadComposeCounts_probe_single : composeCounts [2] [1, 1] = [2, 0] := rfl

/-! ## The width-4 associativity combs (concrete words `t·t·t·t ⇒ t`)

The two width-4 foldings of the associahedron `K4`: the FULLY-LEFT comb `mu ∘ (mu ▷ t) ∘ ((mu ▷ t) ▷ t)` (multiply
the leftmost pair repeatedly) and the FULLY-RIGHT comb `mu ∘ (t ◁ mu) ∘ (t ◁ (t ◁ mu))` (multiply the rightmost
pair repeatedly).  Both collapse four `t`'s to one; their sources are the DEFINITIONALLY-equal `t`-power `[t,t,t,t]`
(`composePath` recurses on the first path and `t` is a singleton, so every nesting reduces to the literal cons
chain). -/

/-- The **fully-left-parenthesized** width-4 multiplication comb `mu ∘ (mu ▷ t) ∘ ((mu ▷ t) ▷ t)` — a 2-cell
`t·t·t·t ⇒ t`. -/
def monadAssocCombLeftFour :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.vcomp
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT
        (RawTwoCellExpr.whiskerRight monadT monadMulTwoCell))
      (RawTwoCellExpr.whiskerRight monadT monadMulTwoCell))
    monadMulTwoCell

/-- The **fully-right-parenthesized** width-4 multiplication comb `mu ∘ (t ◁ mu) ∘ (t ◁ (t ◁ mu))` — a 2-cell
`t·t·t·t ⇒ t`, parallel to `monadAssocCombLeftFour` (the source `t·(t·(t·t))` is DEFINITIONALLY `((t·t)·t)·t`). -/
def monadAssocCombRightFour :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.vcomp
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.whiskerLeft monadT monadMulTwoCell))
      (RawTwoCellExpr.whiskerLeft monadT monadMulTwoCell))
    monadMulTwoCell

/-- Truth-probe: the fully-left width-4 comb folds to the total width-4 degeneracy `[0, 0, 0, 0]` (all four source
positions collapse to the single target position). -/
theorem monadFold_assocCombLeftFour : monadMonotoneMapOf monadAssocCombLeftFour = [0, 0, 0, 0] := rfl

/-- Truth-probe: the fully-right width-4 comb folds to the SAME total degeneracy `[0, 0, 0, 0]` — the associahedron
`K4` collapses in the model with no `assoc` generator. -/
theorem monadFold_assocCombRightFour : monadMonotoneMapOf monadAssocCombRightFour = [0, 0, 0, 0] := rfl

/-! ## B2 — the self-attack VERDICTS

The two decisive convertibility verdicts on the fresh concrete words above, both delivered by the CLOSED decision
machinery: the map-EQUAL width-4 pair converts through COMPLETENESS (`convOfMapEq`), and a map-UNEQUAL two-port face
pair is SEPARATED through SOUNDNESS (`mapEqOfConv`). -/

/-- ★ **Self-attack (map-EQUAL, WIDTH FOUR → YES).**  The two width-4 associativity foldings `t·t·t·t ⇒ t` —
`monadAssocCombLeftFour` and `monadAssocCombRightFour` — are syntactically distinct combs yet saturated-convertible:
both fold to the width-4 degeneracy `[0, 0, 0, 0]` (`monadFold_assocCombLeftFour`, `monadFold_assocCombRightFour`),
so the total decision derives their convertibility through COMPLETENESS (`monadConvOfMapEq_ofNormalize
monadNormalize`), normalizing both to `canon = wordFromCounts [0,0,0,0]` with NO `assoc` law generator.  This extends
the shipped width-3 `monadDecision_yes_assoc` to the next level of the associahedron. -/
theorem monadDecision_yes_assocFour :
    MonadSaturatedTwoCellConv monadAssocCombLeftFour monadAssocCombRightFour :=
  monadConvOfMapEq_ofNormalize monadNormalize rfl

/-- The unit inserted at the FAR-LEFT port of `t·t` — the face `whiskerRight (t·t) eta`, a 2-cell `t·t ⇒ t·t·t`;
the fresh strand occupies target index 0, so the fold is the face `[1, 2]`. -/
def monadFaceInsertPortZero :=
  RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadTThenT monadUnitTwoCell

/-- The unit inserted at the FAR-RIGHT port of `t·t` — the face `whiskerLeft (t·t) eta`, a 2-cell `t·t ⇒ t·t·t`
PARALLEL to `monadFaceInsertPortZero`; the fresh strand occupies target index 2, so the fold is the face `[0, 1]`. -/
def monadFaceInsertPortTwo :=
  RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadTThenT monadUnitTwoCell

/-- Truth-probe: the far-left port insertion folds to the face `[1, 2]`. -/
theorem monadFold_faceInsertPortZero : monadMonotoneMapOf monadFaceInsertPortZero = [1, 2] := rfl

/-- Truth-probe: the far-right port insertion folds to the DISTINCT face `[0, 1]`. -/
theorem monadFold_faceInsertPortTwo : monadMonotoneMapOf monadFaceInsertPortTwo = [0, 1] := rfl

/-- ★ **Self-attack (map-UNEQUAL, two ports → NO).**  Inserting the unit at DIFFERENT ports of the same boundary
`t·t ⇒ t·t·t` — far-left (`monadFaceInsertPortZero`, fold `[1, 2]`) versus far-right (`monadFaceInsertPortTwo`, fold
`[0, 1]`) — yields DISTINCT monotone maps (they differ in which target index the fresh strand occupies).  So the two
insertions are NOT saturated-convertible: SOUNDNESS (`monadMonotoneMapOf_mapEqOfConv`) would force their maps equal,
which `decide` refutes.  This generalizes the shipped width-1 `monadDecision_no_faces` to a genuine two-position
insertion at positive width. -/
theorem monadDecision_no_facePorts :
    ¬ MonadSaturatedTwoCellConv monadFaceInsertPortZero monadFaceInsertPortTwo := by
  intro conv
  exact absurd (monadMonotoneMapOf_mapEqOfConv conv) (by decide)

end FX1Poly.Polygraph

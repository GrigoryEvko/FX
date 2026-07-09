import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeVcomp

/-! # WalkingMonad — the FULL normalization, the inhabited canonicalization, and the DECIDABLE word problem

`WalkingMonad/MonadNormalizeVcomp` closed the last `normalizeCell` case (`monadNormalize_vcomp`) via the DATA bridge
`canonCounts_vcomp` and the 2-cell half `wordMul_vcomp`.  This file assembles the FIVE cases into the full cell-level
normalization `monadNormalize : MonadNormalizesToCanon`, inhabits the Schanuel–Street canonicalization
(`MonadSaturatedCanonicalization`), derives the unconditional DECISION of walking-monad saturated 2-cell
convertibility, and witnesses non-vacuity both ways.  This is the SECOND saturated decision of the ladder (after the
walking-adjunction saturated matching) — Δ₊ is the walking monad (Street; Mac Lane §VII.5), mechanized zero-axiom.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; the recursion is
STRUCTURAL on a `Nat` fuel (the constant `MonadMode.point` boundary indices block direct structural recursion on the
cell).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The full cell-level normalization -/

/-- Every free 2-cell has structural size at least one. -/
theorem one_le_cellSize {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) : 1 ≤ cell.size :=
  match cell with
  | .gen _ => Nat.le_refl 1
  | .id _ => Nat.le_refl 1
  | .vcomp cellL cellR => Nat.le_add_left 1 (cellL.size + cellR.size)
  | .whiskerLeft _ body => Nat.le_add_left 1 body.size
  | .whiskerRight _ body => Nat.le_add_left 1 body.size

/-- ★★ **The full cell-level normalization (STRUCTURAL on a `Nat` fuel).**  Every parallel free 2-cell of the
walking monad is `MonadSaturatedTwoCellConv`-convertible to the canonical Eilenberg–Zilber word of its own fold.
The recursion runs on a `Nat` fuel bounding the cell's structural size (the boundary mode indices are the constant
`MonadMode.point`, which blocks structural recursion directly on the cell), splitting via `match` into the two
`gen` leaves, the `id` case, the two whisker cases (all shipped, no monad law), and the `vcomp` case (the monad
laws through `wordMul_vcomp`). -/
theorem monadNormalizeCellFueled : ∀ (fuel : Nat)
    {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath),
    cell.size ≤ fuel → MonadSaturatedTwoCellConv cell (canon cell)
  | 0, _, _, cell, hfuel =>
      absurd (Nat.le_trans (one_le_cellSize cell) hfuel) (Nat.not_succ_le_zero 0)
  | fuel + 1, _, _, cell, hfuel =>
      match cell, hfuel with
      | .gen MonadTwoCell.eta, _ => monadNormalize_genEta
      | .gen MonadTwoCell.mu, _ => monadNormalize_genMu
      | .id path, _ => monadNormalize_id path
      | .vcomp cellL cellR, hf =>
          monadNormalize_vcomp cellL cellR
            (monadNormalizeCellFueled fuel cellL
              (Nat.le_trans (Nat.le_add_right cellL.size cellR.size) (Nat.le_of_succ_le_succ hf)))
            (monadNormalizeCellFueled fuel cellR
              (Nat.le_trans (Nat.le_add_left cellR.size cellL.size) (Nat.le_of_succ_le_succ hf)))
      | .whiskerLeft oneCell body, hf =>
          monadNormalize_whiskerLeft oneCell body
            (monadNormalizeCellFueled fuel body (Nat.le_of_succ_le_succ hf))
      | .whiskerRight oneCell body, hf =>
          monadNormalize_whiskerRight oneCell body
            (monadNormalizeCellFueled fuel body (Nat.le_of_succ_le_succ hf))

/-- ★★ **The full cell-level normalization**, packaged as the interface `MonadNormalizesToCanon` — the sole
remaining ingredient of the completeness leg `convOfMapEq`. -/
theorem monadNormalize : MonadNormalizesToCanon :=
  fun {_ _} cell => monadNormalizeCellFueled cell.size cell (Nat.le_refl _)

/-! ## ★★ Inhabiting the canonicalization + the unconditional saturated decision -/

/-- ★★ **The walking-monad saturated canonicalization is INHABITED, zero-axiom.**  The Schanuel–Street
monotone-map fold `monadMonotoneMapOf` is the carrier; SOUNDNESS `mapEqOfConv` is the shipped
`monadMonotoneMapOf_mapEqOfConv` (the three monad laws are the simplicial identities); COMPLETENESS `convOfMapEq` is
`monadConvOfMapEq_ofNormalize` applied to the now-inhabited `monadNormalize` (every cell converts to the canonical
word of its own fold, and two cells with equal folds share that word).  This is the SECOND saturated decision of the
ladder — Δ₊ is the walking monad, mechanized. -/
def monadSaturatedCanonicalization : MonadSaturatedCanonicalization where
  monotoneMapOf := monadMonotoneMapOf
  mapEqOfConv := monadMonotoneMapOf_mapEqOfConv
  convOfMapEq := fun hmap => monadConvOfMapEq_ofNormalize monadNormalize hmap

/-- ★★ **The walking-monad saturated 2-cell word problem is DECIDABLE, unconditionally.**  Supplying the inhabited
canonicalization to the shipped decision assembly `monadDecideSaturatedConvViaMonotoneMap` decides EVERY parallel
pair of free 2-cells by comparing their monotone maps (zero-axiom `DecidableEq (List Nat)`).  Closes the
walking-monad word problem. -/
@[reducible] def monadSaturatedTwoCellDecision : MonadDecidableSaturatedTwoCellConvFor :=
  fun cellA cellB => monadDecideSaturatedConvViaMonotoneMap monadSaturatedCanonicalization cellA cellB

/-! ## Non-vacuity: both branches of the total decision fire on genuine pairs -/

/-- ★ **Non-vacuity (equal, non-trivial → YES).**  The two associativity foldings `t·t·t ⇒ t` —
`mu ∘ (mu ▷ t)` and `mu ∘ (t ◁ mu)` — are syntactically distinct yet saturated-convertible: both fold to the
width-3 degeneracy `[0, 0, 0]`, so the total decision derives their convertibility through COMPLETENESS
(`convOfMapEq`), independently of the `assoc` law generator. -/
theorem monadDecision_yes_assoc :
    MonadSaturatedTwoCellConv monadAssocLeftCell monadAssocRightCell :=
  monadConvOfMapEq_ofNormalize monadNormalize
    (rfl : monadMonotoneMapOf monadAssocLeftCell = monadMonotoneMapOf monadAssocRightCell)

/-- ★ **Non-vacuity (separating → NO).**  The two faces `t ⇒ t·t` — `whiskerRight t eta` (`δ₁`, monotone map
`[1]`) and `whiskerLeft t eta` (`δ₀`, monotone map `[0]`) — are NOT saturated-convertible: SOUNDNESS
(`mapEqOfConv`) would force their distinct monotone maps equal.  So the total decision genuinely separates. -/
theorem monadDecision_no_faces :
    ¬ MonadSaturatedTwoCellConv
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell) := by
  intro conv
  exact absurd (monadMonotoneMapOf_mapEqOfConv conv) (by decide)

/-! ## Honesty marker -/

/-- **ESTABLISHED — the walking-monad saturated 2-cell word problem is CLOSED, zero-axiom (the SECOND saturated
decision of the ladder).**  The DATA bridge `canonCounts_vcomp` (`countsOf ∘ composeMap = composeCounts ∘ countsOf`,
the Δ fibre-count functoriality) and the shipped 2-cell half `wordMul_vcomp` assemble the last `normalizeCell` case
(`monadNormalize_vcomp`), completing `monadNormalize : MonadNormalizesToCanon` (all five cell cases).  That inhabits
`MonadSaturatedCanonicalization` (`monadSaturatedCanonicalization`) — soundness `mapEqOfConv` shipped, completeness
`convOfMapEq` via `monadConvOfMapEq_ofNormalize monadNormalize` — hence the unconditional decision
`monadSaturatedTwoCellDecision`.  Non-vacuous both ways: the two associativity foldings `t·t·t ⇒ t` are decided
CONVERTIBLE (`monadDecision_yes_assoc`, both fold `[0,0,0]`), and the two faces `t ⇒ t·t` are decided
NON-convertible (`monadDecision_no_faces`, maps `[1]` vs `[0]`).  Closes trackers WP-MONAD-3 (simplicial
completeness) and WP-MONAD-4 (decidable walking-monad word problem).  `= true`. -/
def fxMonad_hasSaturatedWordProblemClosed : Bool := true

end FX1Poly.Polygraph

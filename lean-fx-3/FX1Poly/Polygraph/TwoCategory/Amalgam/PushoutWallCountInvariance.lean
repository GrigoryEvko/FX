import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutNormalForm

/-! # Polygraph/TwoCategory/Amalgam/PushoutWallCountInvariance — the WALL-COUNT invariant: no 2-generator
straddles an `s`-wall, and the wall count is conserved dom-to-cod and under conversion (WP-AMALG-2 r6, B1)

The r5 PROSE claim (`PushoutMultiGapFactorization.lean`) was: a wire-changing gap `t^a ⇒ t^b` SHIFTS the
`s`-walls, but there are NO `s`-generator 2-cells, so no monad law fires ACROSS a wall.  This file makes that a
MACHINE-CHECKED FORWARD STATEMENT — the straddle test, executed — and thereby REFUTES the second-horn obstruction
(α) ("a wall is CONSUMED under conversion").

## The wall count and the straddle test

`pushoutPathWallCount` counts the component-1 (`s`, tag `true`) letters of a boundary 1-cell of the pushout
`involution +_M monad` — the number of inert `s`-WALLS in the word.  The involution is thin (`s·s = id` lives at
the 1-cell level, never injected as a pushout 2-cell — `Witness.lean`), so the pushout's ONLY generating 2-cells
are the monad's retagged `eta` (`t^0 ⇒ t`) and `mu` (`t^2 ⇒ t`), whose stored boundary WORDS are pure-`t`
(`embedRightLetter`-images, all component-2).  Hence:

  * **`mapPath_inclusionRight_wallFree`** — the STRADDLE LEMMA: any right-coprojected monad 1-cell has wall count
    `0` (every letter is `embedRightLetter`-tagged component-2, `embedRightLetter_component`).  No `s` in the image.
  * **`noGeneratorStraddlesWall`** — cased on `crossPairRealPushoutRel`: a fired law row has BOTH its domain and
    codomain boundary wall-free (the `left` arm vacuous — involution thin; the `right` arm a `mapPath inclRight`
    image, pure-`t`).  So no fired monad law has ANY `s` in its domain OR codomain — the `s`'s live entirely in the
    inert whisker CONTEXTS.  No `mu` domain `t·s·t` exists; every `mu` domain is `t·t`.
  * **`pushoutTwoGen_words_wallFree`** — the pushout's two reconstructed 2-generators (`eta` / `mu`) have wall-free
    stored words (both `lhs` and `rhs`), cased on the two `Fin 2` indices.

## The two conservation directions (obstruction (α) refuted, doubly)

  * **`wallLetterCount_dom_eq_cod`** (dom-to-cod, per cell) — for ANY pushout 2-cell `cell : RawTwoCellExpr … w_dom
    w_cod`, `pushoutPathWallCount w_dom = pushoutPathWallCount w_cod`.  Structural induction on the cell grammar:
    the `gen` case is the wall-free boundary of a reconstructed generator (via the interpreter invariant
    `interpretWordFrom_wallCount` + `pushoutTwoGen_words_wallFree`, both boundaries wall count `0`); `id` is `rfl`;
    `vcomp` transits; the two whisker cases add EQUAL wall counts to dom and cod (the homomorphism
    `pushoutPathWallCount_composePath`).
  * **`saturatedConv_boundary_wallCount_eq`** (under conversion) — TRIVIAL: `SaturatedConvOver` relates PARALLEL
    cells (ONE shared `sourcePath`, ONE shared `targetPath`), so the walls literally cannot move under conversion;
    combined with `wallLetterCount_dom_eq_cod` the whole boundary carries ONE wall count.

⟹ the wall count is a HARD invariant, doubly.  The finer, already-shipped invariant `arityMonotoneMapOf`
(`PushoutMonotoneReflection.lean`, unconditional via `pushoutArityFoldConvSound`) refines it — but this coarse
wall count is the DIRECT answer the round asked for: "write the invariance statement".  This is the SOUNDNESS
structure of the first horn; the COMPLETENESS residual (an arbitrary interleaved cell is CONVERTIBLE-to shifted-gap
form) stays walled — see `PushoutWireChangeLedger.lean`.  #2043 does NOT close.

Raw Lean 4 + Init.  STRUCTURAL on the path / word / cell grammar.  Per-declaration `#assert_no_axioms` gated in the
audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The wall count of a boundary word / path -/

/-- The wall contribution of a single component tag — `1` for a component-1 (`s`) wall letter, `0` for a
component-2 (`t`) gap letter.  Full-enum `Bool` match (propext-free). -/
def wallBitCount : Bool → Nat
  | true => 1
  | false => 0

/-- The **wall count of a boundary WORD** — the number of component-1 (`s`, tag `true`) letters, read through
`letterTag involutionMonadSplit`.  Structural on the word; each letter contributes `wallBitCount` of its tag. -/
def wordWallCount : List (Fin involutionMonadPushout.modalityGenerators.length) → Nat
  | [] => 0
  | letter :: rest => wallBitCount (letterTag involutionMonadSplit letter) + wordWallCount rest

/-- ★ The **wall count of a boundary 1-cell (PATH)** of the pushout — the number of component-1 (`s`) generators in
the `ModalityPath`.  Each `cons` letter's index (`letter.val`) is tagged by `letterTag involutionMonadSplit`; the
inert `s`-walls are the `true` letters.  Structural on the path. -/
def pushoutPathWallCount : {sourceMode targetMode : Fin involutionMonadPushout.modeCount} →
    ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode → Nat
  | _, _, .nil _ => 0
  | _, _, .cons letter rest =>
      wallBitCount (letterTag involutionMonadSplit letter.val) + pushoutPathWallCount rest

/-- The path wall count is a MONOID HOMOMORPHISM — it distributes over path composition (structural on the first
path; `composePath` recurses on the first, so `nil` is `Nat.zero_add`, `cons` is `Nat.succ_add`-free `+`
associativity through the `wallBitCount` head). -/
theorem pushoutPathWallCount_composePath :
    {sourceMode middleMode targetMode : Fin involutionMonadPushout.modeCount} →
    (first : ModalityPath involutionMonadPushout.toModeGraph sourceMode middleMode) →
    (second : ModalityPath involutionMonadPushout.toModeGraph middleMode targetMode) →
    pushoutPathWallCount (composePath first second)
      = pushoutPathWallCount first + pushoutPathWallCount second
  | _, _, _, .nil _, second => (Nat.zero_add (pushoutPathWallCount second)).symm
  | _, _, _, .cons letter rest, second => by
      show wallBitCount (letterTag involutionMonadSplit letter.val)
            + pushoutPathWallCount (composePath rest second)
          = wallBitCount (letterTag involutionMonadSplit letter.val) + pushoutPathWallCount rest
              + pushoutPathWallCount second
      rw [pushoutPathWallCount_composePath rest second, Nat.add_assoc]

/-! ## The straddle lemma: right-coprojected 1-cells are wall-free -/

/-- ★★ **THE STRADDLE LEMMA.**  Any 1-cell in the image of the right coprojection `inclusionRight` has wall count
`0`: every letter is `embedRightLetter`-tagged component-2 (`embedRightLetter_component` gives `letterTag
involutionMonadSplit … = false` by defeq — both are `Nat.blt (embedRightLetter …).val
involutionComputad.modalityGenerators.length`), so each `wallBitCount` is `0`.  This is "no `s` appears in a
right-coprojected monad word" — the free-product fact that the two component alphabets are disjoint.  Structural on
the monad path. -/
theorem mapPath_inclusionRight_wallFree :
    {sourceMode targetMode : Fin monadComputad.modeCount} →
    (path : ModalityPath monadComputad.toModeGraph sourceMode targetMode) →
    pushoutPathWallCount
        (mapPath (inclusionRight involutionComputad monadComputad involutionMonadSameModes) path) = 0
  | _, _, .nil _ => rfl
  | _, _, .cons modality rest => by
      have htag : letterTag involutionMonadSplit
          (mapModality (inclusionRight involutionComputad monadComputad involutionMonadSameModes) modality).val
            = false :=
        embedRightLetter_component involutionComputad monadComputad involutionMonadSameModes modality.val
      show wallBitCount (letterTag involutionMonadSplit
            (mapModality (inclusionRight involutionComputad monadComputad involutionMonadSameModes) modality).val)
            + pushoutPathWallCount
                (mapPath (inclusionRight involutionComputad monadComputad involutionMonadSameModes) rest) = 0
      rw [htag]
      show (0 : Nat) + pushoutPathWallCount
          (mapPath (inclusionRight involutionComputad monadComputad involutionMonadSameModes) rest) = 0
      rw [Nat.zero_add, mapPath_inclusionRight_wallFree rest]

/-! ## The reconstructed generators carry wall-free stored words -/

/-- ★ **The pushout's two reconstructed 2-generators carry WALL-FREE stored words.**  Index `0` (retagged `eta`)
has words `([], [t])`; index `1` (retagged `mu`) has words `([t, t], [t])` — all `embedRightLetter`-images, so
every letter is component-2 and `wordWallCount` is `0` (each `rfl`).  The `Fin 2` index cased propext-free
(mirroring `pushoutTwoGenWordArity`).  This is the WORD-level straddle fact underlying the `gen` case. -/
theorem pushoutTwoGen_words_wallFree (index : Fin involutionMonadPushout.twoCellGenerators.length) :
    wordWallCount (involutionMonadPushout.twoCellGenerators.get index).lhs = 0
      ∧ wordWallCount (involutionMonadPushout.twoCellGenerators.get index).rhs = 0 :=
  match index with
  | ⟨0, _⟩ => ⟨rfl, rfl⟩
  | ⟨1, _⟩ => ⟨rfl, rfl⟩
  | ⟨count + 2, isLt⟩ =>
      (Nat.not_lt_zero count (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLt))).elim

/-! ## The interpreter carries word wall count to path wall count -/

/-- ★★ **The interpreter's WALL-COUNT invariant.**  If `interpretWordFrom src word` succeeds with path `path`, then
`pushoutPathWallCount path = wordWallCount word`: the interpreter builds the path letter-for-letter (each `cons`
carries the same generator index the word letter names), so the two counts agree.  Structural on the word,
mirroring `interpretWordFrom_length` — the built path's wall count is extracted from the `Sigma`-valued result by
the non-dependent `pushoutPathWallCount ∘ .snd` projection (propext-free, no `HEq` juggling). -/
theorem interpretWordFrom_wallCount :
    (word : List (Fin involutionMonadPushout.modalityGenerators.length)) →
    (src targetMode : Fin involutionMonadPushout.modeCount) →
    (path : ModalityPath involutionMonadPushout.toModeGraph src targetMode) →
    involutionMonadPushout.interpretWordFrom src word = some ⟨targetMode, path⟩ →
    pushoutPathWallCount path = wordWallCount word
  | [], src, targetMode, path, hyp => by
      have hsig : (⟨src, ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) src⟩ :
          Sigma (fun tm => ModalityPath involutionMonadPushout.toModeGraph src tm)) = ⟨targetMode, path⟩ :=
        Option.some.inj hyp
      exact (congrArg (fun entry => pushoutPathWallCount entry.snd) hsig).symm
  | index :: rest, src, targetMode, path, hyp => by
      dsimp only [ModeComputad.interpretWordFrom] at hyp
      by_cases hcond : (involutionMonadPushout.modalityGenerators.get index).1 = src
      · rw [dif_pos hcond] at hyp
        cases hInner : involutionMonadPushout.interpretWordFrom
            (involutionMonadPushout.modalityGenerators.get index).2 rest with
        | none => rw [hInner] at hyp; nomatch hyp
        | some restInterpreted =>
            rw [hInner] at hyp
            have hsig := Option.some.inj hyp
            have hrest : pushoutPathWallCount restInterpreted.snd = wordWallCount rest :=
              interpretWordFrom_wallCount rest (involutionMonadPushout.modalityGenerators.get index).2
                restInterpreted.fst restInterpreted.snd hInner
            have hcount := congrArg
              (fun entry : (tm : Fin involutionMonadPushout.modeCount) ×
                  ModalityPath involutionMonadPushout.toModeGraph src tm => pushoutPathWallCount entry.snd) hsig
            dsimp only [] at hcount
            rw [← hcount]
            show wallBitCount (letterTag involutionMonadSplit index) + pushoutPathWallCount restInterpreted.snd
              = wallBitCount (letterTag involutionMonadSplit index) + wordWallCount rest
            rw [hrest]
      · rw [dif_neg hcond] at hyp
        nomatch hyp

/-! ## B1 — the wall count is conserved dom-to-cod for EVERY pushout 2-cell -/

/-- ★★★ **THE WALL-COUNT INVARIANCE THEOREM (B1) — the straddle test made a forward statement.**  For ANY pushout
2-cell `cell : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath`, the domain and
codomain boundaries carry the SAME wall count.  Structural recursion on the cell grammar:

  * `gen g` — `g` is a reconstructed generator; its boundary WORDS are wall-free (`pushoutTwoGen_words_wallFree`)
    and the interpreter carries that to the boundary PATHS (`interpretWordFrom_wallCount`), so both sides are `0`.
    This is the straddle test: no generator's domain OR codomain contains an `s`.
  * `id path` — the boundary is shared (`rfl`).
  * `vcomp` — the wall count transits through the middle path.
  * `whiskerLeft` / `whiskerRight` — the whisker context adds EQUAL wall counts to dom and cod
    (`pushoutPathWallCount_composePath`), and the body's dom/cod agree by recursion.

⟹ a wall is NEVER consumed: the wall count is a HARD dom-to-cod invariant.  Second-horn obstruction (α) REFUTED. -/
theorem wallLetterCount_dom_eq_cod :
    {sourceMode targetMode : involutionMonadPushout.toModeSignature.graph.Mode} →
    {sourcePath targetPath :
      ModalityPath involutionMonadPushout.toModeSignature.graph sourceMode targetMode} →
    (cell : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath) →
    pushoutPathWallCount sourcePath = pushoutPathWallCount targetPath
  | _, _, _, _, .gen g => by
      obtain ⟨index, hlhs, hrhs⟩ := g
      obtain ⟨hlhs0, hrhs0⟩ := pushoutTwoGen_words_wallFree index
      rw [interpretWordFrom_wallCount _ _ _ _ hlhs, interpretWordFrom_wallCount _ _ _ _ hrhs, hlhs0, hrhs0]
  | _, _, _, _, .id _ => rfl
  | _, _, _, _, .vcomp cellAlpha cellBeta =>
      (wallLetterCount_dom_eq_cod cellAlpha).trans (wallLetterCount_dom_eq_cod cellBeta)
  | _, _, _, _, @RawTwoCellExpr.whiskerLeft _ _ _ _ oneCell oneCellG oneCellH body =>
      (pushoutPathWallCount_composePath oneCell oneCellG).trans
        ((congrArg (fun count => pushoutPathWallCount oneCell + count) (wallLetterCount_dom_eq_cod body)).trans
          (pushoutPathWallCount_composePath oneCell oneCellH).symm)
  | _, _, _, _, @RawTwoCellExpr.whiskerRight _ _ _ _ oneCellF oneCellG oneCell body =>
      (pushoutPathWallCount_composePath oneCellF oneCell).trans
        ((congrArg (fun count => count + pushoutPathWallCount oneCell) (wallLetterCount_dom_eq_cod body)).trans
          (pushoutPathWallCount_composePath oneCellG oneCell).symm)

/-! ## The straddle test at the LAW-ROW granularity + the conversion corollary -/

/-- ★★ **NO 2-GENERATOR STRADDLES A WALL (the law-row form).**  A fired law row of the real-law pushout relation
`crossPairRealPushoutRel` relates cells whose SHARED boundary is wall-free at BOTH ends: the `left` arm is vacuous
(the involution component relation is empty — involution thin); the `right` arm's cells are `mapPath inclRight`
images (pure-`t`, wall count `0` by the straddle lemma).  So every fired monad law has ZERO `s` in its domain and
its codomain — the `s`'s live entirely in the inert whisker contexts, never in a fired-law window.  There is no
`mu` spanning an `s` (no `t·s·t ⇒ …` law). -/
theorem noGeneratorStraddlesWall
    {sourceMode targetMode : involutionMonadPushout.toModeSignature.graph.Mode}
    {sourcePath targetPath :
      ModalityPath involutionMonadPushout.toModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath}
    (row : crossPairRealPushoutRel cellAlpha cellBeta) :
    pushoutPathWallCount sourcePath = 0 ∧ pushoutPathWallCount targetPath = 0 := by
  cases row with
  | left involutionRow => exact involutionRow.elim
  | right _ => exact ⟨mapPath_inclusionRight_wallFree _, mapPath_inclusionRight_wallFree _⟩

/-- ★★ **THE CONVERSION COROLLARY — walls cannot move under conversion.**  Two saturated-convertible pushout cells
are PARALLEL (one shared `sourcePath`, one shared `targetPath`), so combined with `wallLetterCount_dom_eq_cod` the
whole boundary carries ONE well-defined wall count: `pushoutPathWallCount sourcePath = pushoutPathWallCount
targetPath`.  The conversion hypothesis is not even needed for the equation (it holds of either cell) — that is
exactly the point: the boundary is a SHARED INDEX, so no conversion can shift a wall.  Second-horn obstruction (α)
REFUTED under conversion as well. -/
theorem saturatedConv_boundary_wallCount_eq
    {sourceMode targetMode : involutionMonadPushout.toModeSignature.graph.Mode}
    {sourcePath targetPath :
      ModalityPath involutionMonadPushout.toModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath}
    (_conv : SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel cellAlpha cellBeta) :
    pushoutPathWallCount sourcePath = pushoutPathWallCount targetPath :=
  wallLetterCount_dom_eq_cod cellAlpha

/-! ## Observability — the straddle test, computed -/

-- The witness word `s·t·s·t·t` has wall count 2 (two `s`-walls). Expect `2`.
#eval wordWallCount witnessWord
-- Every letter of a pure-`t` (right-coprojected) word tags component-2 (`false`). Expect `[false, false, false]`.
#eval ([tLetter, tLetter, tLetter].map (letterTag involutionMonadSplit))
-- Example 1 (recon): `t·t·s·t` (a `mu` domain) and `t·s·t` (its codomain) each have wall count 1 — the single `s`
-- SHIFTS position (abs 2 → abs 1) but is NOT consumed. Expect `true`.
#eval decide (wordWallCount [tLetter, tLetter, sLetter, tLetter] = 1
  ∧ wordWallCount [tLetter, sLetter, tLetter] = 1
  ∧ wordWallCount [tLetter, tLetter, sLetter, tLetter] = wordWallCount [tLetter, sLetter, tLetter])

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the WALL-COUNT INVARIANCE (the straddle test, forward) SHIPS (WP-AMALG-2 r6, B1).**
`= true`: the straddle lemma (`mapPath_inclusionRight_wallFree`: right-coprojected 1-cells are wall-free — the two
component alphabets are disjoint), the law-row straddle test (`noGeneratorStraddlesWall`: no fired monad law has an
`s` in its domain or codomain, `left` vacuous / `right` pure-`t`), the reconstructed generators' wall-free stored
words (`pushoutTwoGen_words_wallFree`), the interpreter's wall-count invariant (`interpretWordFrom_wallCount`), and
— the headline — the DOM-TO-COD wall conservation for EVERY pushout 2-cell (`wallLetterCount_dom_eq_cod`, structural
induction, `gen` via the straddle facts) together with the CONVERSION corollary
(`saturatedConv_boundary_wallCount_eq`, trivial — the boundary is a shared index).  This turns the r5 PROSE ("a
wire-changing gap shifts the walls but there are no `s`-generators") into a MACHINE-CHECKED forward statement, and
REFUTES the second-horn obstruction (α) ("a wall is consumed") DOUBLY.  The finer `arityMonotoneMapOf`
(`PushoutMonotoneReflection.lean`) refines it.  This is the SOUNDNESS structure of the first horn; the COMPLETENESS
residual (arbitrary cell CONVERTIBLE-to shifted-gap form) stays walled (`PushoutWireChangeLedger.lean`); #2043 does
NOT close.  `= true`. -/
def fxAmalg_hasWallCountInvariance : Bool := true

end FX1Poly.Polygraph.Amalgam

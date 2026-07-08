import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadCanonicalWord

/-! # WalkingMonad — the map→counts inversion: fold monotonicity + the counts round-trip

`WalkingMonad/MonadCanonicalWord` shipped the Eilenberg–Zilber WORD-builder `wordFromCounts` and the section
`monadMonotoneMapOf (wordFromCounts counts) = reconstructFrom 0 counts` — the map REBUILT from a multiplicity list.
The COMPLETENESS leg `convOfMapEq` also needs the OTHER direction of that data flow: given a fold output
(`monadMonotoneMapOf cell`, a genuinely monotone in-range `List Nat`) READ OFF its per-target multiplicity list and
rebuild the SAME map.  This file ships that inversion.

## What this file ships (each piece zero-axiom)

  * ★ **the fold monotonicity invariant** `monadMonotoneMapOf_isWeaklyIncreasing` — the monad's covariant fold lands
    every free 2-cell in a WEAKLY-INCREASING value-list (each step post-composes a face / degeneracy, both weakly
    increasing, closed under `composeMap` given the shipped `mapsInto` invariant).  This is the second half of "the
    fold lands in a genuine Δ₊ morphism" (the codomain half `monadMonotoneMapOf_mapsInto` is already shipped).
  * **the run-peel `runLengthAt` / `dropRunAt` + `countsOf`** — read the per-target multiplicity list off a sorted
    value-list by peeling the leading constant runs.  Structural on the value-list / target count.
  * ★★ **the counts ROUND-TRIP** `reconstructFrom 0 (countsOf targetLen 0 values) = values` for a weakly-increasing,
    in-range `values` (`reconstructFrom_countsOf`), and its whole-cell instance
    `monadMonotoneMapOf_reconstructRoundTrip` — the fold output rebuilds from its own counts.  This is the trivial
    map→counts inversion the `convOfMapEq` honesty markers named as a residual, now discharged.

The KEY reconstruction step `consReplicate base (runLengthAt base values) (dropRunAt base values) = values` is
UNCONDITIONAL (peel-then-prepend is identity); monotonicity is used only to thread the codomain bound down through
the induction (the peeled remainder's minimum rises by one).  Raw Lean 4 + Init; STRUCTURAL recursion on the
value-list and on the target count (no `WellFounded.fix`); the `head = base` branch splits on `Nat.decEq` via
`if_pos` / `if_neg` (propext-free, MonotoneMap-style), never `beq` / library `List.replicate`/`append` lemmas.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The fold monotonicity invariant: the covariant fold lands in a WEAKLY-INCREASING value-list -/

/-- The monotonicity invariant at a GENERATOR — split out with FREE boundary paths so casing on the generator is
propext-free.  Both `eta` (a face) and `mu` (a degeneracy) post-compose a weakly-increasing generator onto the
running map, which stays weakly increasing by `composeMap_isWeaklyIncreasing` (whose in-range side condition is the
running `mapsInto` invariant). -/
theorem monadRunMonoCell_isWeaklyIncreasing_gen {overallSource overallTarget sourceMode targetMode : MonadMode}
    {generatorDom generatorCod : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (generator : MonadTwoCell generatorDom generatorCod)
    (width : Nat) (map : List Nat)
    (leftAcc : ModalityPath monadModeSignature.graph overallSource sourceMode)
    (rightAcc : ModalityPath monadModeSignature.graph targetMode overallTarget)
    (hwidth : width = leftAcc.length + generatorDom.length + rightAcc.length)
    (hmap : mapsInto map width) (hmono : isWeaklyIncreasing map) :
    isWeaklyIncreasing (monadRunMonoCell (width, map) leftAcc rightAcc (RawTwoCellExpr.gen generator)).2 := by
  cases generator with
  | eta =>
      show isWeaklyIncreasing (composeMap map (faceMap leftAcc.length width))
      exact composeMap_isWeaklyIncreasing map (faceMap leftAcc.length width) hmono
        (faceMap_isWeaklyIncreasing leftAcc.length width)
        (by rw [faceMap_length]; exact hmap)
  | mu =>
      show isWeaklyIncreasing (composeMap map (degenMap leftAcc.length (width - 1)))
      have hsucc : width - 1 + 1 = width := by
        have hwidthPred : width - 1 = leftAcc.length + 1 + rightAcc.length := by
          rw [hwidth]; exact monadMuWidthShift leftAcc.length rightAcc.length
        rw [hwidthPred, hwidth]
        show leftAcc.length + 1 + rightAcc.length + 1 = leftAcc.length + 2 + rightAcc.length
        rw [Nat.add_right_comm leftAcc.length 2 rightAcc.length,
            Nat.add_right_comm leftAcc.length 1 rightAcc.length]
      exact composeMap_isWeaklyIncreasing map (degenMap leftAcc.length (width - 1)) hmono
        (degenMap_isWeaklyIncreasing leftAcc.length (width - 1))
        (by rw [degenMap_length, hsucc]; exact hmap)

/-- ★ **The covariant fold lands every free 2-cell in a WEAKLY-INCREASING value-list.**  Structural recursion
mirroring `monadRunMonoCell_mapsInto`: a generator via the gen lemma, a vertical composite through both factors
(intermediate width / in-range from `monadRunMonoCell_width` / `_mapsInto`), the whiskerings under shifted
accumulators.  Together with `monadRunMonoCell_mapsInto` this says the fold output is a genuine monotone Δ₊
morphism. -/
theorem monadRunMonoCell_isWeaklyIncreasing {overallSource overallTarget : MonadMode} :
    {localSource localTarget : MonadMode} →
    {localDom localCod : ModalityPath monadModeSignature.graph localSource localTarget} →
    (cell : RawTwoCellExpr monadModeSignature localDom localCod) →
    (width : Nat) → (map : List Nat) →
    (leftAcc : ModalityPath monadModeSignature.graph overallSource localSource) →
    (rightAcc : ModalityPath monadModeSignature.graph localTarget overallTarget) →
    width = leftAcc.length + localDom.length + rightAcc.length →
    mapsInto map width → isWeaklyIncreasing map →
    isWeaklyIncreasing (monadRunMonoCell (width, map) leftAcc rightAcc cell).2
  | _, _, _, _, .gen generator, width, map, leftAcc, rightAcc, hwidth, hmap, hmono =>
      monadRunMonoCell_isWeaklyIncreasing_gen generator width map leftAcc rightAcc hwidth hmap hmono
  | _, _, _, _, .id _, _, _, _, _, _, _, hmono => hmono
  | _, _, _, _, .vcomp cellLeft cellRight, width, map, leftAcc, rightAcc, hwidth, hmap, hmono => by
      rw [monadRunMonoCell_vcomp]
      exact monadRunMonoCell_isWeaklyIncreasing cellRight _ _ leftAcc rightAcc
        (monadRunMonoCell_width cellLeft width map leftAcc rightAcc hwidth)
        (monadRunMonoCell_mapsInto cellLeft width map leftAcc rightAcc hwidth hmap)
        (monadRunMonoCell_isWeaklyIncreasing cellLeft width map leftAcc rightAcc hwidth hmap hmono)
  | _, _, _, _, .whiskerLeft oneCell body, width, map, leftAcc, rightAcc, hwidth, hmap, hmono => by
      rename_i bodyDom _
      rw [monadRunMonoCell_whiskerLeft]
      exact monadRunMonoCell_isWeaklyIncreasing body width map (composePath leftAcc oneCell) rightAcc (by
        rw [hwidth, ModalityPath.length_composePath oneCell bodyDom,
            ModalityPath.length_composePath leftAcc oneCell,
            Nat.add_assoc leftAcc.length oneCell.length bodyDom.length]) hmap hmono
  | _, _, _, _, .whiskerRight oneCell body, width, map, leftAcc, rightAcc, hwidth, hmap, hmono => by
      rename_i bodyDom _
      rw [monadRunMonoCell_whiskerRight]
      exact monadRunMonoCell_isWeaklyIncreasing body width map leftAcc (composePath oneCell rightAcc) (by
        rw [hwidth, ModalityPath.length_composePath bodyDom oneCell,
            ModalityPath.length_composePath oneCell rightAcc,
            ← Nat.add_assoc leftAcc.length bodyDom.length oneCell.length,
            Nat.add_assoc (leftAcc.length + bodyDom.length) oneCell.length rightAcc.length]) hmap hmono

/-- ★ **The whole-cell monotone map is WEAKLY INCREASING** — instantiate the run-level invariant at the identity
state (the identity map is weakly increasing and maps into its own ordinal). -/
theorem monadMonotoneMapOf_isWeaklyIncreasing {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    isWeaklyIncreasing (monadMonotoneMapOf cell) := by
  rw [monadMonotoneMapOf_eq_runMonoCell]
  exact monadRunMonoCell_isWeaklyIncreasing cell sourcePath.length (idMap sourcePath.length)
    (identityPath (graph := monadModeSignature.graph) sourceMode)
    (identityPath (graph := monadModeSignature.graph) targetMode)
    (by show sourcePath.length = 0 + sourcePath.length + 0; rw [Nat.add_zero, Nat.zero_add])
    (idMap_mapsInto sourcePath.length) (idMap_isWeaklyIncreasing sourcePath.length)

/-! ## The run-peel: read the per-target multiplicity list off a sorted value-list -/

/-- The length of the leading run of entries equal to `base` in a value-list.  Structural on the list; the
`head = base` test splits on `Nat.decEq` via `ite` (propext-free through `if_pos` / `if_neg`). -/
def runLengthAt (base : Nat) : List Nat → Nat
  | [] => 0
  | head :: rest => if head = base then runLengthAt base rest + 1 else 0

/-- Drop the leading run of entries equal to `base` from a value-list.  Structural on the list. -/
def dropRunAt (base : Nat) : List Nat → List Nat
  | [] => []
  | head :: rest => if head = base then dropRunAt base rest else head :: rest

/-- `runLengthAt` unfolds on a cons whose head IS the base. -/
theorem runLengthAt_cons_pos {base head : Nat} {rest : List Nat} (h : head = base) :
    runLengthAt base (head :: rest) = runLengthAt base rest + 1 := if_pos h

/-- `runLengthAt` unfolds on a cons whose head is NOT the base (the run is empty). -/
theorem runLengthAt_cons_neg {base head : Nat} {rest : List Nat} (h : ¬ head = base) :
    runLengthAt base (head :: rest) = 0 := if_neg h

/-- `dropRunAt` unfolds on a cons whose head IS the base (drop it and continue). -/
theorem dropRunAt_cons_pos {base head : Nat} {rest : List Nat} (h : head = base) :
    dropRunAt base (head :: rest) = dropRunAt base rest := if_pos h

/-- `dropRunAt` unfolds on a cons whose head is NOT the base (the run is empty; keep the whole list). -/
theorem dropRunAt_cons_neg {base head : Nat} {rest : List Nat} (h : ¬ head = base) :
    dropRunAt base (head :: rest) = head :: rest := if_neg h

/-- The per-target multiplicity list of a sorted value-list into `[base, base + targetLen)`: the count of the
`base`-run, then recurse at `base + 1` on the dropped tail.  Structural on `targetLen`, so it produces exactly
`targetLen` counts. -/
def countsOf : Nat → Nat → List Nat → List Nat
  | 0, _, _ => []
  | targetLen + 1, base, values =>
      runLengthAt base values :: countsOf targetLen (base + 1) (dropRunAt base values)

/-! ## Tail lemmas for the invariants threaded through the peel -/

/-- The tail of a weakly-increasing list is weakly increasing. -/
theorem isWeaklyIncreasing_tail {head : Nat} {rest : List Nat}
    (hmono : isWeaklyIncreasing (head :: rest)) : isWeaklyIncreasing rest := by
  intro lowerPos upperPos hle hupper
  exact hmono (lowerPos + 1) (upperPos + 1) (Nat.succ_le_succ hle) (Nat.succ_lt_succ hupper)

/-- The tail of a list mapping into `[cap]` maps into `[cap]`. -/
theorem mapsInto_tail {head : Nat} {rest : List Nat} {cap : Nat}
    (hinto : mapsInto (head :: rest) cap) : mapsInto rest cap := by
  intro position hposition
  exact hinto (position + 1) (Nat.succ_lt_succ hposition)

/-- The tail of a list bounded below by `base` is bounded below by `base`. -/
theorem lowerBound_tail {base head : Nat} {rest : List Nat}
    (hlow : ∀ position, position < (head :: rest).length → base ≤ monotoneMapGet (head :: rest) position) :
    ∀ position, position < rest.length → base ≤ monotoneMapGet rest position := by
  intro position hposition
  exact hlow (position + 1) (Nat.succ_lt_succ hposition)

/-! ## `dropRunAt` preserves the three invariants (weakly increasing, lower bound rises, upper bound) -/

/-- Dropping the base-run preserves weak monotonicity (the remainder is a suffix). -/
theorem dropRunAt_isWeaklyIncreasing : ∀ (base : Nat) (values : List Nat),
    isWeaklyIncreasing values → isWeaklyIncreasing (dropRunAt base values)
  | _, [], _ => by intro _ _ _ hupper; exact absurd hupper (Nat.not_lt_zero _)
  | base, head :: rest, hmono => by
      rcases Nat.decEq head base with h | h
      · rw [dropRunAt_cons_neg h]; exact hmono
      · rw [dropRunAt_cons_pos h]
        exact dropRunAt_isWeaklyIncreasing base rest (isWeaklyIncreasing_tail hmono)

/-- ★ Dropping the base-run RAISES the lower bound to `base + 1`: every remaining entry exceeds `base` (the run of
`base`s is exactly what was removed; monotonicity makes the remainder start strictly above `base`). -/
theorem dropRunAt_lowerBound : ∀ (base : Nat) (values : List Nat),
    isWeaklyIncreasing values →
    (∀ position, position < values.length → base ≤ monotoneMapGet values position) →
    (∀ position, position < (dropRunAt base values).length →
      base + 1 ≤ monotoneMapGet (dropRunAt base values) position)
  | _, [], _, _ => by intro position hposition; exact absurd hposition (Nat.not_lt_zero _)
  | base, head :: rest, hmono, hlow => by
      rcases Nat.decEq head base with h | h
      · rw [dropRunAt_cons_neg h]
        intro position hposition
        have hbh : base ≤ head := hlow 0 (Nat.succ_pos _)
        have hbhlt : base + 1 ≤ head := Nat.lt_of_le_of_ne hbh (fun heq => h heq.symm)
        cases position with
        | zero => exact hbhlt
        | succ predPos =>
            have hpred : predPos < rest.length := Nat.lt_of_succ_lt_succ hposition
            have hle : head ≤ monotoneMapGet rest predPos :=
              hmono 0 (predPos + 1) (Nat.zero_le _) (Nat.succ_lt_succ hpred)
            exact Nat.le_trans hbhlt hle
      · rw [dropRunAt_cons_pos h]
        exact dropRunAt_lowerBound base rest (isWeaklyIncreasing_tail hmono) (lowerBound_tail hlow)

/-- Dropping the base-run preserves the upper bound (the remainder is a suffix). -/
theorem dropRunAt_mapsInto : ∀ (base : Nat) (values : List Nat) (cap : Nat),
    mapsInto values cap → mapsInto (dropRunAt base values) cap
  | _, [], _, _ => by intro position hposition; exact absurd hposition (Nat.not_lt_zero _)
  | base, head :: rest, cap, hinto => by
      rcases Nat.decEq head base with h | h
      · rw [dropRunAt_cons_neg h]; exact hinto
      · rw [dropRunAt_cons_pos h]; exact dropRunAt_mapsInto base rest cap (mapsInto_tail hinto)

/-! ## The KEY reconstruction step: peel-then-prepend is the identity (UNCONDITIONAL) -/

/-- ★★ **Peel the base-run, prepend it back = identity.**  `consReplicate base (runLengthAt base values)
(dropRunAt base values) = values` for ANY `values` — the run-peel and the run-rebuild are inverse.  Structural on
the value-list; the `head = base` branch prepends `base` (which equals `head`) and recurses, the `head ≠ base`
branch is the empty run (`consReplicate base 0 _` is the tail, unchanged). -/
theorem consReplicate_runLengthAt_dropRunAt : ∀ (base : Nat) (values : List Nat),
    consReplicate base (runLengthAt base values) (dropRunAt base values) = values
  | _, [] => rfl
  | base, head :: rest => by
      rcases Nat.decEq head base with h | h
      · rw [runLengthAt_cons_neg h, dropRunAt_cons_neg h]; rfl
      · rw [runLengthAt_cons_pos h, dropRunAt_cons_pos h]
        show base :: consReplicate base (runLengthAt base rest) (dropRunAt base rest) = head :: rest
        rw [consReplicate_runLengthAt_dropRunAt base rest, h]

/-! ## ★★ The counts round-trip -/

/-- ★★ **The counts ROUND-TRIP.**  For a weakly-increasing `values` mapping into `[base, base + targetLen)`,
reconstructing from its per-target multiplicity list returns `values`: `reconstructFrom base (countsOf targetLen
base values) = values`.  Structural on `targetLen`; the successor step peels the `base`-run
(`consReplicate_runLengthAt_dropRunAt`) and recurses on the dropped tail (weakly increasing, lower bound risen to
`base + 1`, still bounded above, by the `dropRunAt_*` invariants).  The `targetLen = 0` base forces `values = []`
(no entry can be both `≥ base` and `< base`). -/
theorem reconstructFrom_countsOf : ∀ (targetLen base : Nat) (values : List Nat),
    isWeaklyIncreasing values →
    (∀ position, position < values.length → base ≤ monotoneMapGet values position) →
    mapsInto values (base + targetLen) →
    reconstructFrom base (countsOf targetLen base values) = values
  | 0, base, values, _, hlow, hinto => by
      cases values with
      | nil => rfl
      | cons head rest =>
          exact absurd (hinto 0 (Nat.succ_pos _)) (Nat.not_lt.mpr (hlow 0 (Nat.succ_pos _)))
  | targetLen + 1, base, values, hmono, hlow, hinto => by
      show consReplicate base (runLengthAt base values)
             (reconstructFrom (base + 1) (countsOf targetLen (base + 1) (dropRunAt base values))) = values
      have hupperShift : mapsInto (dropRunAt base values) (base + 1 + targetLen) := by
        have hupper : mapsInto (dropRunAt base values) (base + (targetLen + 1)) :=
          dropRunAt_mapsInto base values (base + (targetLen + 1)) hinto
        have heq : base + (targetLen + 1) = base + 1 + targetLen := by
          rw [← Nat.add_assoc]; exact (Nat.add_right_comm base 1 targetLen).symm
        rw [heq] at hupper; exact hupper
      rw [reconstructFrom_countsOf targetLen (base + 1) (dropRunAt base values)
            (dropRunAt_isWeaklyIncreasing base values hmono)
            (dropRunAt_lowerBound base values hmono hlow)
            hupperShift]
      exact consReplicate_runLengthAt_dropRunAt base values

/-- ★★ **The whole-cell counts round-trip.**  The fold output rebuilds from its own per-target multiplicity list:
`reconstructFrom 0 (countsOf targetPath.length 0 (monadMonotoneMapOf cell)) = monadMonotoneMapOf cell`.  Base `0`
makes the lower bound trivial; the upper bound is `monadMonotoneMapOf_mapsInto`; monotonicity is
`monadMonotoneMapOf_isWeaklyIncreasing`.  This is the map→counts inversion residual the `convOfMapEq` honesty
markers named, now discharged zero-axiom. -/
theorem monadMonotoneMapOf_reconstructRoundTrip {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    reconstructFrom 0 (countsOf targetPath.length 0 (monadMonotoneMapOf cell)) = monadMonotoneMapOf cell := by
  refine reconstructFrom_countsOf targetPath.length 0 (monadMonotoneMapOf cell)
    (monadMonotoneMapOf_isWeaklyIncreasing cell)
    (fun position _ => Nat.zero_le _)
    ?_
  show mapsInto (monadMonotoneMapOf cell) (0 + targetPath.length)
  rw [Nat.zero_add]
  exact monadMonotoneMapOf_mapsInto cell

/-! ## Non-vacuity smokes: the round-trip on concrete fold outputs -/

/-- Smoke: `countsOf` reads the identity map `[0, 1]` (a 2-cell `t^2 ⇒ t^2`) as counts `[1, 1]`. -/
theorem countsOf_id_two : countsOf 2 0 [0, 1] = [1, 1] := rfl

/-- Smoke: `countsOf` reads the merge map `[0, 0]` (the bare `mu`) as counts `[2]` — width-2 codomain-1. -/
theorem countsOf_merge : countsOf 1 0 [0, 0] = [2] := rfl

/-- Smoke: `countsOf` reads `[0, 0, 1]` as `[2, 1]` — the first two strands merge, the third passes. -/
theorem countsOf_merge_first : countsOf 2 0 [0, 0, 1] = [2, 1] := rfl

/-- Smoke: `countsOf` reads `[1]` (target `0` missed) as `[0, 1]` — the insertion / face content. -/
theorem countsOf_insert_first : countsOf 2 0 [1] = [0, 1] := rfl

/-- Smoke: the round-trip COMPUTES on a merge map — `reconstructFrom 0 (countsOf 2 0 [0, 0, 1]) = [0, 0, 1]`. -/
theorem reconstructFrom_countsOf_smoke : reconstructFrom 0 (countsOf 2 0 [0, 0, 1]) = [0, 0, 1] := rfl

/-! ## Honesty marker -/

/-- **ESTABLISHED.**  The map→counts inversion is shipped, zero-axiom: the covariant fold lands every free 2-cell
in a WEAKLY-INCREASING value-list (`monadMonotoneMapOf_isWeaklyIncreasing`), and reconstructing from the per-target
multiplicity list read off by the run-peel (`countsOf`) returns the map (`reconstructFrom_countsOf` /
`monadMonotoneMapOf_reconstructRoundTrip`).  Combined with the shipped section
(`monadMonotoneMapOf_wordFromCounts`) this closes BOTH directions of the map ↔ counts correspondence.

**Residual toward `convOfMapEq` (the FLIP): the cell-level insertion-sort `normalizeCell`.**  What remains is the
NORMALIZATION `cell ≈ wordFromCounts (countsOf (monadMonotoneMapOf cell))` under `MonadSaturatedTwoCellConv`.  Its
crux is the vcomp / hcomp WORD-MULTIPLICATIVITY `wordMul_vcomp` / `wordMul_hcomp` — concatenate two canonical
EZ words and re-normalize (degeneracies-then-faces, index-sorted) to one, as a chain of adjacent-swap seed-law Conv
steps (the simplicial identities `σσ` commute, `σδ = id` cancel), terminating by an inversion-count structural
measure (Guiraud–Malbos–Mimram, Example 2.6; Weibel Lemma 8.1.2 uniqueness).  That sort — the faithfulness-weight
brick, the adjunction lane's flag-B analog — is NOT yet landed; the boundary transport
`monadPath_normalForm : P = monadTPower P.length` is a secondary residual.  Until `wordMul_*` + `normalizeCell`
land, `MonadSaturatedCanonicalization.convOfMapEq` is NOT inhabited and
`fxMonad_hasMonotoneMapDecisionAssembled` / `fxMonad_hasConvOfMapEqNormalization` /
`fxMonad_hasFullMapEqOfConvAndCompleteness` stay `false`.  `= true` (this file's own contribution: the inversion). -/
def fxMonad_hasCountsRoundTripInversion : Bool := true

end FX1Poly.Polygraph

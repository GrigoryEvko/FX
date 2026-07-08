import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadCountsRoundTrip

/-! # WalkingMonad — the cell-level NORMALIZATION toward `convOfMapEq` (the completeness FLIP)

`WalkingMonad/MonadCountsRoundTrip` closed BOTH directions of the map ↔ counts correspondence at the DATA level:
the section `monadMonotoneMapOf (wordFromCounts counts) = reconstructFrom 0 counts` and the round-trip
`reconstructFrom 0 (countsOf targetPath.length 0 (monadMonotoneMapOf cell)) = monadMonotoneMapOf cell`.  The
COMPLETENESS field `convOfMapEq` of `MonadSaturatedCanonicalization` needs the CELL-level normalization: every free
2-cell is `MonadSaturatedTwoCellConv`-convertible to the canonical Eilenberg–Zilber word of its own fold.

## The boundary transport (this file's clean contribution)

The canonical word `wordFromCounts (countsOf targetPath.length 0 (map cell))` lives at boundaries
`(countsDomainPath counts, monadTPower counts.length)`, NOT literally at `(sourcePath, targetPath)`.  On Δ EVERY
1-cell is a `t`-power (`monadPath_normalForm : path = monadTPower path.length`), so both boundaries transport onto
`(sourcePath, targetPath)` and the canonical word `canon cell` is well-typed parallel to `cell`.  This file ships:

  * **`countsOf_length`** — `(countsOf targetLen base values).length = targetLen` (structural on `targetLen`).
  * ★ **`monadPath_normalForm`** — every walking-monad 1-cell is a `t`-power `monadTPower path.length` (structural
    induction on the path; the single modality `t` forces every `cons` step, one object, no branching).  This is
    the boundary transport the `convOfMapEq` honesty markers named as the SECONDARY residual, now discharged.
  * **`canon`** — the boundary-transported canonical EZ word of a cell's fold, parallel to the cell.
  * base-case witnesses of the normalization on the `id` / generator fragment.

## The remaining crux (NAMED residual, NOT flipped)

The `vcomp` case of the full `normalizeCell` needs the WORD-MULTIPLICATIVITY `wordMul_vcomp` — concatenating two
canonical EZ words and re-normalizing (degeneracies-then-faces, index-sorted) to one, a terminating adjacent-swap
insertion sort at the `MonadSaturatedTwoCellConv` level (the simplicial identities `σσ` commute, `σδ = id` cancel;
Guiraud–Malbos–Mimram Example 2.6 convergence, Weibel 8.1.2 uniqueness).  That sort — the faithfulness-weight
brick, the adjunction lane's flag-B analog — is NOT landed here; `fxMonad_hasWordMulVcomp = false` records it, and
the three completeness flags stay `false`.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; STRUCTURAL recursion.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## `countsOf` produces exactly `targetLen` counts -/

/-- The per-target multiplicity list has exactly `targetLen` entries — one count per target position.  Structural
recursion on `targetLen`. -/
theorem countsOf_length : ∀ (targetLen base : Nat) (values : List Nat),
    (countsOf targetLen base values).length = targetLen
  | 0, _, _ => rfl
  | targetLen + 1, base, values => by
      show (runLengthAt base values :: countsOf targetLen (base + 1) (dropRunAt base values)).length
        = targetLen + 1
      show (countsOf targetLen (base + 1) (dropRunAt base values)).length + 1 = targetLen + 1
      rw [countsOf_length targetLen (base + 1) (dropRunAt base values)]

/-! ## The boundary transport: every walking-monad 1-cell is a `t`-power -/

/-- The length-indexed normal-form: a walking-monad 1-cell of length `n` is `monadTPower n`.  STRUCTURAL recursion
on `n` (the ModalityPath is an indexed family, so recursion runs on the plain `Nat` length instead): the `n = 0`
case inverts to `nil`; the `n + 1` case inverts to a `cons` whose modality is forced to `t` (the single
generator), and the tail — of length `n` — is `monadTPower n` by the recursive call. -/
theorem monadPath_normalForm_ofLength :
    ∀ (targetLen : Nat) (path : ModalityPath monadGraph MonadMode.point MonadMode.point),
      path.length = targetLen → path = monadTPower targetLen
  | 0, ModalityPath.nil _, _ => rfl
  | 0, ModalityPath.cons _ _, hlen => absurd hlen (fun heq => Nat.noConfusion heq)
  | targetLen + 1, ModalityPath.nil _, hlen => absurd hlen (fun heq => Nat.noConfusion heq)
  | targetLen + 1, ModalityPath.cons modality rest, hlen => by
      cases modality
      have hrest : rest.length = targetLen := Nat.succ.inj hlen
      show ModalityPath.cons MonadModality.t rest = composePath monadT (monadTPower targetLen)
      show ModalityPath.cons MonadModality.t rest
        = ModalityPath.cons MonadModality.t (monadTPower targetLen)
      rw [← monadPath_normalForm_ofLength targetLen rest hrest]

/-- ★ **Every walking-monad 1-cell is the `t`-power of its length.**  `path = monadTPower path.length` — the
walking monad has ONE object `point` and ONE endo-generator `t`, so a modality path is a run of `t`'s, exactly
`monadTPower path.length`.  Immediate from the length-indexed form.  This is the boundary transport lining up the
canonical EZ word with the cell's own `(sourcePath, targetPath)`, the SECONDARY residual the `convOfMapEq` honesty
markers named. -/
theorem monadPath_normalForm (path : ModalityPath monadGraph MonadMode.point MonadMode.point) :
    path = monadTPower path.length :=
  monadPath_normalForm_ofLength path.length path rfl

/-! ## The canonical Eilenberg–Zilber word of a cell's fold, transported to the cell's boundary -/

/-- The per-target multiplicity list of a cell's monotone map — the Eilenberg–Zilber degeneracy/face data
(`countsOf` read off the fold), the input to the canonical word builder. -/
def canonCounts {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) : List Nat :=
  countsOf targetPath.length 0 (monadMonotoneMapOf cell)

/-- The multiplicity list has exactly `targetPath.length` entries (one count per target position). -/
theorem canonCounts_length {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    (canonCounts cell).length = targetPath.length :=
  countsOf_length targetPath.length 0 (monadMonotoneMapOf cell)

/-- ★ **The codomain boundary transport.**  The canonical word's codomain `monadTPower (canonCounts cell).length`
equals the cell's own `targetPath` — the count list has `targetPath.length` entries and `targetPath` is its own
`t`-power. -/
theorem canonCodomain_eq
    {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    monadTPower (canonCounts cell).length = targetPath := by
  rw [canonCounts_length cell]
  exact (monadPath_normalForm targetPath).symm

/-- ★ **The domain boundary transport.**  The canonical word's domain `countsDomainPath (canonCounts cell)` equals
the cell's own `sourcePath` — it is a `t`-power (`monadPath_normalForm`) of length `sum (canonCounts cell)`, which
is `sourcePath.length` by the counts round-trip (`reconstructFrom 0 counts = map cell`) and the fold's domain law
(`(map cell).length = sourcePath.length`). -/
theorem canonDomain_eq {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    countsDomainPath (canonCounts cell) = sourcePath := by
  have hround : reconstructFrom 0 (canonCounts cell) = monadMonotoneMapOf cell :=
    monadMonotoneMapOf_reconstructRoundTrip cell
  have hlen : (countsDomainPath (canonCounts cell)).length = sourcePath.length := by
    rw [← reconstructFrom_length 0 (canonCounts cell), hround]
    exact monadMonotoneMapOf_length cell
  rw [monadPath_normalForm (countsDomainPath (canonCounts cell)), hlen]
  exact (monadPath_normalForm sourcePath).symm

/-- ★ The **boundary-transported canonical Eilenberg–Zilber word** of a cell: the horizontal composite of
per-target merge gadgets for the cell's own monotone-map multiplicities (`wordFromCounts (canonCounts cell)`),
transported across the two boundary equalities so it is a free 2-cell PARALLEL to `cell`
(`sourcePath ⇒ targetPath`).  The `convOfMapEq` target `normalizeCell` asserts `cell` is
`MonadSaturatedTwoCellConv`-convertible to this. -/
def canon {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    RawTwoCellExpr monadModeSignature sourcePath targetPath :=
  RawTwoCellExpr.castBoundary (canonDomain_eq cell) (canonCodomain_eq cell)
    (wordFromCounts (canonCounts cell))

/-- ★ **`canon` folds to the same monotone map as the cell** — the SOUNDNESS cross-check that the canonical word is
the RIGHT one: `map (canon cell) = map cell`.  The boundary cast is spine-invisible and preserves the source
length, so `map (canon cell) = map (wordFromCounts (canonCounts cell)) = reconstructFrom 0 (canonCounts cell) =
map cell` (the section + the counts round-trip).  This validates `canon` is non-vacuous and pins the intended
normal form, though the CONVERTIBILITY `cell ≈ canon cell` (completeness) still needs the word multiplicativity. -/
theorem monadMonotoneMapOf_canon {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    monadMonotoneMapOf (canon cell) = monadMonotoneMapOf cell := by
  have hspine : (canon cell).spine = (wordFromCounts (canonCounts cell)).spine :=
    RawTwoCellExpr.castBoundary_spine (canonDomain_eq cell) (canonCodomain_eq cell)
      (wordFromCounts (canonCounts cell))
  have hsrc : sourcePath.length = (countsDomainPath (canonCounts cell)).length := by
    rw [canonDomain_eq cell]
  show (((canon cell).spine).foldl monadMonoStepAtom (sourcePath.length, idMap sourcePath.length)).2
    = monadMonotoneMapOf cell
  rw [hspine, hsrc]
  show (((wordFromCounts (canonCounts cell)).spine).foldl monadMonoStepAtom
      ((countsDomainPath (canonCounts cell)).length, idMap (countsDomainPath (canonCounts cell)).length)).2
    = monadMonotoneMapOf cell
  show monadMonotoneMapOf (wordFromCounts (canonCounts cell)) = monadMonotoneMapOf cell
  rw [monadMonotoneMapOf_wordFromCounts (canonCounts cell)]
  exact monadMonotoneMapOf_reconstructRoundTrip cell

/-! ## The `canon` congruence: `canon` depends on a cell only through its monotone map

The `convOfMapEq` ASSEMBLY needs one algebraic fact about `canon`: two cells with EQUAL monotone maps have the
SAME canonical word.  This holds because `canon cell` reads the cell only through `canonCounts cell =
countsOf targetPath.length 0 (monadMonotoneMapOf cell)` — a function of the fold — while the two boundary
transports it casts along are PROOFS, definitionally irrelevant.  So the whole `convOfMapEq` reduces to the single
cell-level normalization `normalizeCell`; this file closes that reduction and names the residual. -/

/-- The canonical EZ word transported to a fixed parallel boundary depends on its counts list only up to equality:
casting the same word along different boundary proofs is definitional proof-irrelevance, and equal counts lists
give the same word.  Structural `subst` on the counts equality, then `rfl` (the two casts to the same boundary are
definitionally equal by `Eq`'s proof irrelevance, per `RawTwoCellExpr.castBoundary`). -/
theorem RawTwoCellExpr.castBoundary_wordCongr
    {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    {countsLeft countsRight : List Nat}
    (hdomLeft : countsDomainPath countsLeft = sourcePath)
    (hcodLeft : monadTPower countsLeft.length = targetPath)
    (hdomRight : countsDomainPath countsRight = sourcePath)
    (hcodRight : monadTPower countsRight.length = targetPath)
    (hcounts : countsLeft = countsRight) :
    RawTwoCellExpr.castBoundary hdomLeft hcodLeft (wordFromCounts countsLeft)
      = RawTwoCellExpr.castBoundary hdomRight hcodRight (wordFromCounts countsRight) := by
  subst hcounts
  rfl

/-- The multiplicity list `canonCounts` is a function of the monotone map: equal maps give equal counts. -/
theorem canonCounts_eqOfMapEq {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath)
    (hmap : monadMonotoneMapOf cellA = monadMonotoneMapOf cellB) :
    canonCounts cellA = canonCounts cellB :=
  congrArg (countsOf targetPath.length 0) hmap

/-- ★ **The `canon` congruence.**  Two parallel cells with EQUAL monotone maps have the SAME canonical word:
`monadMonotoneMapOf cellA = monadMonotoneMapOf cellB → canon cellA = canon cellB`.  Immediate from
`canonCounts_eqOfMapEq` (the counts agree) and `castBoundary_wordCongr` (the boundary casts are proof-irrelevant).
This is the algebraic glue the `convOfMapEq` assembly rests on: the YES-branch of the decision needs only that
BOTH cells normalize to their canonical word, and those two words then COINCIDE. -/
theorem canon_eqOfMapEq {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath)
    (hmap : monadMonotoneMapOf cellA = monadMonotoneMapOf cellB) :
    canon cellA = canon cellB :=
  RawTwoCellExpr.castBoundary_wordCongr (canonDomain_eq cellA) (canonCodomain_eq cellA)
    (canonDomain_eq cellB) (canonCodomain_eq cellB) (canonCounts_eqOfMapEq cellA cellB hmap)

/-! ## The `convOfMapEq` assembly, reduced to `normalizeCell`

With the `canon` congruence in hand, the COMPLETENESS leg `convOfMapEq` of `MonadSaturatedCanonicalization` reduces
EXACTLY to the cell-level normalization `normalizeCell : cell ≈ canon cell`: normalize both cells to their canonical
words, which coincide by `canon_eqOfMapEq`.  This lemma makes that reduction explicit — it takes `normalizeCell` as a
hypothesis and delivers `convOfMapEq` — pinning `normalizeCell` (whose sole open case is the vertical word
multiplicativity `wordMul_vcomp`) as the single remaining residual. -/

/-- The type of the cell-level normalization the completeness leg needs: every parallel free 2-cell of the walking
monad is `MonadSaturatedTwoCellConv`-convertible to the canonical Eilenberg–Zilber word of its own fold. -/
abbrev MonadNormalizesToCanon : Prop :=
  {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point} →
  (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) →
  MonadSaturatedTwoCellConv cell (canon cell)

/-- ★ **`convOfMapEq`, reduced to `normalizeCell`.**  GIVEN the cell-level normalization `normalize` (every cell is
saturated-convertible to its canonical word), two parallel cells with equal monotone maps are saturated-convertible:
`cellA ≈ canon cellA = canon cellB ≈ cellB` — the first `≈` by `normalize cellA`, the middle `=` by `canon_eqOfMapEq`,
the last by `normalize cellB` symmetrised.  This is the COMPLETENESS field `convOfMapEq` modulo `normalize`; it
inhabits `MonadSaturatedCanonicalization` the moment `normalize` is supplied.  The reduction is exact — nothing else
is owed. -/
theorem monadConvOfMapEq_ofNormalize (normalize : MonadNormalizesToCanon)
    {sourcePath targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    {cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (hmap : monadMonotoneMapOf cellA = monadMonotoneMapOf cellB) :
    MonadSaturatedTwoCellConv cellA cellB := by
  refine MonadSaturatedTwoCellConv.trans (normalize cellA) ?_
  rw [canon_eqOfMapEq cellA cellB hmap]
  exact MonadSaturatedTwoCellConv.symm (normalize cellB)

/-! ## Honesty markers -/

/-- **ESTABLISHED.**  The boundary transport toward `convOfMapEq` is shipped, zero-axiom: every walking-monad
1-cell is a `t`-power (`monadPath_normalForm` — the SECONDARY residual the `convOfMapEq` honesty markers named), so
the canonical Eilenberg–Zilber word `wordFromCounts (canonCounts cell)` transports onto the cell's own boundary
`(sourcePath, targetPath)` as `canon cell`, and `canon` folds back to the cell's monotone map
(`monadMonotoneMapOf_canon`) — the canonical form is well-typed and non-vacuous.  `= true`. -/
def fxMonad_hasBoundaryTransportAndCanon : Bool := true

/-- **ESTABLISHED — `convOfMapEq` is now MACHINE-CHECKED-EQUIVALENT to `normalizeCell`.**  Two facts close the
`convOfMapEq` ASSEMBLY, zero-axiom: (i) the `canon` congruence `canon_eqOfMapEq` — `canon` depends on a cell only
through its monotone map, so equal maps give the SAME canonical word (proof-irrelevance of the boundary casts via
`RawTwoCellExpr.castBoundary_wordCongr`); (ii) the reduction `monadConvOfMapEq_ofNormalize` — GIVEN the cell-level
normalization `normalize : MonadNormalizesToCanon`, `convOfMapEq` follows (`cellA ≈ canon cellA = canon cellB ≈
cellB`).  So the COMPLETENESS leg is no longer a hand-waved "reduces to word multiplicativity": it is a
machine-checked function of `normalize`, and `normalize` (a `MonadNormalizesToCanon`) is the SOLE remaining
ingredient toward inhabiting `MonadSaturatedCanonicalization`.  `= true`. -/
def fxMonad_hasConvOfMapEqReducedToNormalize : Bool := true

/-- **Honesty marker — the SOLE residual is `normalizeCell`, whose SOLE hard case is the vertical word
multiplicativity `wordMul_vcomp`.**  `convOfMapEq` is machine-checked-reduced to `normalize : MonadNormalizesToCanon`
(`monadConvOfMapEq_ofNormalize`); what is NOT landed is `normalize` itself — `normalizeCell : cell ≈ canon cell` by
induction on the cell.  Its cases split as: `gen`/`id` (base) and `whiskerLeft`/`whiskerRight` reduce to the
HORIZONTAL word multiplicativity `wordMul_hcomp` (canonical words compose horizontally by counts-list concatenation),
which needs the free-2-category structural infrastructure — associativity of horizontal composition, gadget-chain
reassembly — NOT present in the lane; the `vcomp` case needs the VERTICAL word multiplicativity `wordMul_vcomp`:
concatenate two canonical EZ words and re-normalize (degeneracies-then-faces, index-sorted) to one canonical word, a
terminating adjacent-swap insertion sort at the `MonadSaturatedTwoCellConv` level (the simplicial identities `σσ`
commute via `assoc`, `σδ = id` cancel via the two unit laws; classically Δ₊ is convergent — Guiraud–Malbos–Mimram
Example 2.6, Weibel Lemma 8.1.2 uniqueness — but the zero-axiom mechanization of the terminating normalizer, on an
inversion-count structural `Nat` measure, is the multi-hundred-line faithfulness-weight brick, the adjunction lane's
flag-B analog, also NOT landed there).  Neither `wordMul_hcomp` nor `wordMul_vcomp` is landed; until BOTH are,
`normalize` is not inhabited, so `MonadSaturatedCanonicalization.convOfMapEq` is not inhabited and
`fxMonad_hasMonotoneMapDecisionAssembled` / `fxMonad_hasConvOfMapEqNormalization` /
`fxMonad_hasFullMapEqOfConvAndCompleteness` stay `false`.  `= false`. -/
def fxMonad_hasWordMulVcomp : Bool := false

end FX1Poly.Polygraph

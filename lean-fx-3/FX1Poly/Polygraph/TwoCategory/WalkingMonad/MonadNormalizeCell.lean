import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadCountsRoundTrip
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedCanonReps

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

/-! ## The canon / boundary-transport stratum (relocated to `MonadSaturatedCanonReps`)

The conv-FREE Eilenberg–Zilber canon machinery (`countsOf_length`, `monadPath_normalForm` / `_ofLength`,
`canonCounts` / `_length`, `canonCodomain_eq` / `canonDomain_eq`, `canon`, `monadMonotoneMapOf_canon`,
`RawTwoCellExpr.castBoundary_wordCongr`, `canonCounts_eqOfMapEq`, `canon_eqOfMapEq`) is relocated VERBATIM
(MONAD-R7 r4) to the bespoke-free deep leaf `MonadSaturatedCanonReps`.  The conv-BEARING completeness interface
below (`MonadNormalizesToCanon`, `monadConvOfMapEq_ofNormalize`) STAYS here, threading the relocated `canon` /
`canon_eqOfMapEq` through the bridge. -/

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

/-- **ESTABLISHED — the vertical word multiplicativity `wordMul_vcomp` is CLOSED, zero-axiom** (with the horizontal
`wordMul_hcomp`).  `convOfMapEq` is machine-checked-reduced to `normalize : MonadNormalizesToCanon`
(`monadConvOfMapEq_ofNormalize`); the `normalizeCell` induction splits as `gen`/`id` (base), `whiskerLeft`/
`whiskerRight` (reduced to `wordMul_whiskerLeft/Right` + `wordMul_hcomp`, SHIPPED), and `vcomp` (reduced to the
VERTICAL word multiplicativity `wordMul_vcomp`).  The last — `wordMul_vcomp : vcomp (word ccL) (cast (word ccR)) ≈
cast (word (composeCounts ccL ccR))` — is now LANDED (`WalkingMonad/MonadWordVcomp`,
`fxMonad_hasVcompWordMultiplicativity`): the block-sum re-sort of two canonical EZ words, via the `wordMul_hcomp`
block split, the free interchange, the `wordGadgetCollapse` per-block merge (the three monad laws), and the
proof-irrelevant boundary-cast fusion.  Both word multiplicativities are thus closed; the remaining ingredient
toward inhabiting `normalize` is the DATA bridge `canonCounts (vcomp cellL cellR) = composeCounts (canonCounts
cellL) (canonCounts cellR)` (`countsOf ∘ composeMap = composeCounts ∘ countsOf`, the degeneracies-then-faces
identity), the analog of the shipped whisker bridges `canonCounts_whiskerLeft/Right`.  `= true`. -/
def fxMonad_hasWordMulVcomp : Bool := true

end FX1Poly.Polygraph

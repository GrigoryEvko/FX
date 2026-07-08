import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeCell

/-! # WalkingMonad — the CELL-level normalization cases: base + whisker (toward `normalize`)

`WalkingMonad/MonadNormalizeCell` machine-checked-reduced the completeness leg `convOfMapEq` to ONE inhabitant,
`normalize : MonadNormalizesToCanon` — every parallel free 2-cell is `MonadSaturatedTwoCellConv`-convertible to
the canonical Eilenberg–Zilber word of its own fold (`cell ≈ canon cell`).  This file lands the cases of that
`normalizeCell` induction that do NOT need the vertical word multiplicativity `wordMul_vcomp` (the re-sort).

## The base cases (no monad law, purely free-2-category structural)

Both walking-monad GENERATORS normalize to their canonical word by stripping the horizontal-composite identity
wrappers `wordFromCounts` produces, using ONLY the completed free-strict-2-category laws (`whiskerLeftId`,
`whiskerRightUnit`, `vcompIdLeft`, `vcompIdRight`) — never a monad law:

  * `gen eta` : fold `[]`, canon count `[0]`, `canon = hcomp eta (id t^0)` — strip the trailing left-whisker
    identity and the right-whisker-unit on `eta`.
  * `gen mu`  : fold `[0,0]`, canon count `[2]`, `canon = hcomp (mu-tree 2) (id t^0)` — strip the trailing
    identity, the right-whisker-unit, then collapse `monadGadget 2 = vcomp (t ◁ id_t) mu` to `mu` by
    `whiskerLeftId` + `vcompIdLeft`.

`composePath monadT (monadTPower 0)` reduces to `monadT` DEFINITIONALLY (`composePath` recurses on its first
argument, and `composePath nil nil = nil`), and `RawTwoCellExpr.castBoundary` along a definitionally-reflexive
boundary equality is defeq to the uncast cell (proof-irrelevance of `Eq` collapses the `Eq.rec`), so `canon (gen g)`
is defeq to the explicit horizontal composite — the `show` re-presents it with no cast in sight.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; STRUCTURAL. -/

namespace FX1Poly.Polygraph

/-! ## Base case: the UNIT generator `eta` normalizes to its canonical word -/

/-- ★ **Base case — the unit `eta`.**  `gen eta ≈ canon (gen eta)`.  Its fold is `[]`, so the canonical count list
is `[0]` and `canon (gen eta)` is DEFINITIONALLY `wordFromCounts [0] = hcomp (monadGadget 0) (id t^0) = vcomp
(whiskerRight t^0 eta) (whiskerLeft t (id t^0))` (the boundary cast is definitionally the identity — both boundaries
are `nil` / `monadT` on the nose).  Strip the trailing left-whisker identity by `whiskerLeftId` + `vcompIdRight`,
then the right-whisker-unit on `eta` by `whiskerRightUnit`, using ONLY the free-2-category structural laws. -/
theorem monadNormalize_genEta :
    MonadSaturatedTwoCellConv (RawTwoCellExpr.gen MonadTwoCell.eta)
      (canon (RawTwoCellExpr.gen MonadTwoCell.eta)) := by
  refine MonadSaturatedTwoCellConv.symm ?_
  show MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) monadUnitTwoCell)
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0))))
      (RawTwoCellExpr.gen MonadTwoCell.eta)
  have hRight : MonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)))
      (RawTwoCellExpr.id (signature := monadModeSignature) (composePath monadT (monadTPower 0))) :=
    MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT (monadTPower 0)))
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.vcompCongrRight
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) monadUnitTwoCell) hRight) ?_
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
      (TwoCellStep.vcompIdRight
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) monadUnitTwoCell)))) ?_
  exact MonadSaturatedTwoCellConv.ofFull (TwoCellConvFull.whiskerRightUnit monadUnitTwoCell)

/-! ## Base case: the MULTIPLICATION generator `mu` normalizes to its canonical word -/

/-- ★ **Base case — the multiplication `mu`.**  `gen mu ≈ canon (gen mu)`.  Its fold is `[0,0]`, so the canonical
count list is `[2]` and `canon (gen mu)` is DEFINITIONALLY `wordFromCounts [2] = hcomp (monadGadget 2) (id t^0) =
vcomp (whiskerRight t^0 (monadGadget 2)) (whiskerLeft t (id t^0))`.  Strip the trailing left-whisker identity
(`whiskerLeftId` + `vcompIdRight`) and the right-whisker-unit (`whiskerRightUnit`) to reach `monadGadget 2`, then
collapse `monadGadget 2 = vcomp (whiskerLeft t (id t)) mu` to `mu`: the inner `whiskerLeft t (id t)` is the identity
on `t·t` (`whiskerLeftId`), dropped by `vcompIdLeft`.  Purely free-2-category structural — no monad law. -/
theorem monadNormalize_genMu :
    MonadSaturatedTwoCellConv (RawTwoCellExpr.gen MonadTwoCell.mu)
      (canon (RawTwoCellExpr.gen MonadTwoCell.mu)) := by
  refine MonadSaturatedTwoCellConv.symm ?_
  show MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) (monadGadget 2))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0))))
      (RawTwoCellExpr.gen MonadTwoCell.mu)
  -- Strip the trailing left-whisker identity.
  have hRight : MonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 0)))
      (RawTwoCellExpr.id (signature := monadModeSignature) (composePath monadT (monadTPower 0))) :=
    MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT (monadTPower 0)))
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.vcompCongrRight
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) (monadGadget 2)) hRight) ?_
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
      (TwoCellStep.vcompIdRight
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 0) (monadGadget 2))))) ?_
  -- Strip the right-whisker-unit: whiskerRight (t^0) (monadGadget 2) ≈ monadGadget 2.
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.ofFull (TwoCellConvFull.whiskerRightUnit (monadGadget 2))) ?_
  -- Collapse monadGadget 2 = vcomp (whiskerLeft t (id t)) mu to mu.
  show MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
        monadMulTwoCell)
      (RawTwoCellExpr.gen MonadTwoCell.mu)
  have hInner : MonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
      (RawTwoCellExpr.id (signature := monadModeSignature) (composePath monadT monadT)) :=
    MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT monadT))
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell hInner) ?_
  exact MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft monadMulTwoCell))

/-! ## Honesty markers -/

/-- **ESTABLISHED — the two GENERATOR base cases of `normalize` are CLOSED, zero-axiom.**  Both walking-monad
generators are `MonadSaturatedTwoCellConv`-convertible to the canonical Eilenberg–Zilber word of their own fold:
`gen eta ≈ canon (gen eta)` (`monadNormalize_genEta`) and `gen mu ≈ canon (gen mu)` (`monadNormalize_genMu`),
using ONLY the completed free-strict-2-category laws (`whiskerLeftId`, `whiskerRightUnit`, `vcompIdLeft`,
`vcompIdRight`) — no monad law.  These are the `gen` leaf of the five-case `normalizeCell` induction on the cell
constructor.  `= true`. -/
def fxMonad_hasNormalizeGeneratorBaseCases : Bool := true

/-- **Honesty marker — the remaining `normalize` cases (`id` / `whiskerLeft` / `whiskerRight` / `vcomp`) are NOT
landed.**  `normalize : MonadNormalizesToCanon` inducts on the cell's five constructors; the two `gen` leaves are
CLOSED here.  What remains:

  * **`id path`** — needs `countsOf n 0 (idMap n) = <n ones>` and `wordFromCounts <n ones> ≈ id (t^n)` (the
    identity word collapses under `whiskerLeftId` / `whiskerRightId` — structural, no monad law), THEN a boundary
    TRANSPORT: `id path`'s boundary `path ⇒ path` is only PROVABLY (not definitionally) the `t`-power boundary the
    canonical word lives at (`path = monadTPower path.length`, `monadPath_normalForm`), and `wordFromCounts cs`'s
    two ends (`countsDomainPath cs`, `monadTPower cs.length`) are provably-but-not-defeq equal — a genuine
    `castBoundary`-congruence transport, not a `show`.
  * **`whiskerLeft W body` / `whiskerRight W body`** — the congruence `whiskerLeftCongr` / `whiskerRightCongr`
    (shipped constructors) + IH reduces each to `whiskerLeft (t^k) (canon body) ≈ canon (whiskerLeft W body)`,
    i.e. the HORIZONTAL word multiplicativity `wordMul_hcomp` (canonical words compose horizontally by counts-list
    concatenation, `hcomp id_t`-blocks re-expressed as a `t^k` left-whisker); needs `hcomp`-associativity as a
    `MonadSaturatedTwoCellConv` and the `countsOf_embedLocalMap_left` counts identity — structural, no monad law,
    but new infrastructure not in the lane.
  * **`vcomp cellL cellR`** — the congruences + IH reduce it to `vcomp (canon cellL) (canon cellR) ≈ canon (vcomp
    cellL cellR)`, i.e. the VERTICAL word multiplicativity `wordMul_vcomp`: concatenate two canonical EZ words and
    re-normalize (degeneracies-then-faces, index-sorted) to one, a terminating adjacent-swap insertion sort at the
    `MonadSaturatedTwoCellConv` level (the simplicial identities `σσ` commute via `assoc`, `σδ = id` cancel via the
    two unit laws; convergent by Guiraud–Malbos–Mimram Example 2.6, Weibel Lemma 8.1.2 uniqueness).  This is the
    faithfulness-weight brick — the adjunction lane's flag-B analog — and is the SOLE case using the monad LAWS.

Until ALL five cases land, `normalize` is not inhabited, so `MonadSaturatedCanonicalization.convOfMapEq`
(`monadConvOfMapEq_ofNormalize`) is not inhabited and `fxMonad_hasMonotoneMapDecisionAssembled` /
`fxMonad_hasConvOfMapEqNormalization` / `fxMonad_hasFullMapEqOfConvAndCompleteness` stay `false`.  `= false`. -/
def fxMonad_hasNormalizeIdWhiskerVcompCases : Bool := false

end FX1Poly.Polygraph

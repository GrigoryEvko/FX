import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadGeneralNormalizer

/-! # WalkingIdempotent/IdempotentMonadRightWhisker — the GROW-half right-whisker + general-width `whiskerRightCanon`

`IdempotentMonadGeneralNormalizer` shipped the general-width LEFT-whisker canonicalisation (`whiskerLeftCanon`) and
the FOLD-half right-whisker peel (`gadgetSplitRight`), naming the GROW-half right-whisker as the sole residual toward
the `whiskerRight` normalize case.  This file ships it and assembles the general-width `whiskerRightCanon`, all
zero-axiom, STRUCTURAL:

  * ★ **`growColumnFold`** — the grow-then-fold column collapse `(t ◁ grow n ▷ t) ∘ (t^{n+1}·t ← mu-fold) ≈ mu`,
    factored (surprisingly) through the SHIPPED `gadgetSplitRight` (fold half) + `growThenFold` (the grow/fold
    round-trip, which uses only the left-unit law) — no fresh Godement chase needed.
  * ★ **`growTowerRightWhisker`** — the genuine idempotence-USING GROW-half dual of `gadgetSplitRight`:
    `(eta ▷ t) ∘ (t^{n+1} ← grow ▷ t) ≈ grow (n+1)` (transported), by a right-section cancellation
    (`idempotentRightSectionCancel`) whose sole idempotence input is the shipped `foldThenGrow` round-trip.
  * ★ **`whiskerRightCanonOne` / `whiskerRightCanon`** — the single-`t` then general-width RIGHT-whisker
    canonicalisation `t^k ▷ (canonThroughT a n) ≈ canonThroughT (a+k)(n+k)` (transported), the RIGHT mirror of
    `whiskerLeftCanon`, assembling `gadgetSplitRight` (fold) + `growTowerRightWhisker` (grow) through the mu-iso
    middle insertion, then an induction on `k` peeling one outer `t` (append cast) and re-folding by the single-`t`
    canonicalisation.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; STRUCTURAL `Nat`
recursion.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

open IdempotentMonadSaturatedTwoCellConv

/-! ## Signature-generic cast-manipulation helpers (CONV-level, applied — never `rw`)

These are the `rw`-free tools for the general-width induction: boundary-cast fusion, cast-through-`whiskerRight`
extrusion, and the vcomp-cast merge, each proved by `cases` on the (free) boundary equalities and each APPLIED (via
`trans`/`exact`) so unification runs up to DEFINITIONAL equality — which handles the `congrArg`-lambda beta-redexes
and the `rfl` / `Eq.symm rfl` seams that defeat `rw`'s syntactic matcher. -/

/-- Whiskering by PROPOSITIONALLY-equal 1-cells gives boundary-cast-equal cells: replacing the right-whisker
1-cell `oneCell` by an equal `oneCell'` transports the whiskered cell along the induced boundary equalities
(`cases` on the whisker equality).  Used to re-express `t^{k+1}` (left-nested) as `t^k · t` (append) before
peeling one `t` off a right whisker.  The `congrArg` uses the PARTIAL application `composePath oneCellDom` (not a
`fun w => …` lambda) so the produced boundary paths are beta-NORMAL. -/
theorem whiskerRight_whiskerEq {signature : ModeSignature} {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCell oneCell' : ModalityPath signature.graph middleMode targetMode} (hW : oneCell = oneCell')
    {oneCellDom oneCellCod : ModalityPath signature.graph sourceMode middleMode}
    (body : RawTwoCellExpr signature oneCellDom oneCellCod) :
    RawTwoCellExpr.whiskerRight oneCell' body
      = RawTwoCellExpr.castBoundary (congrArg (composePath oneCellDom) hW)
          (congrArg (composePath oneCellCod) hW)
          (RawTwoCellExpr.whiskerRight oneCell body) := by
  cases hW; rfl

/-- **Boundary-cast fusion (CONV form).**  Two nested boundary casts collapse to one along the composite
equalities (`cases` on all four equalities then `refl`).  Applied — not `rw`ed — so the beta-redex `congrArg`
casts unify by defeq. -/
theorem castChainCollapseConv
    {sourcePath sourcePath' sourcePath'' targetPath targetPath' targetPath'' :
      ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hsourceFirst : sourcePath = sourcePath') (htargetFirst : targetPath = targetPath')
    (hsourceSecond : sourcePath' = sourcePath'') (htargetSecond : targetPath' = targetPath'')
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.castBoundary hsourceSecond htargetSecond
        (RawTwoCellExpr.castBoundary hsourceFirst htargetFirst cell))
      (RawTwoCellExpr.castBoundary (hsourceFirst.trans hsourceSecond) (htargetFirst.trans htargetSecond) cell) := by
  cases hsourceFirst; cases htargetFirst; cases hsourceSecond; cases htargetSecond
  exact IdempotentMonadSaturatedTwoCellConv.refl _

/-- **Extrude a boundary cast out of a `monadT` RIGHT-whisker (CONV form).**  `t ▷ (cast cell) ≈ cast (t ▷ cell)`,
the boundary equalities picking up the trailing `· t` (`cases` on the equalities). -/
theorem whiskerRightPullMonadTConv
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT
        (RawTwoCellExpr.castBoundary hsource htarget cell))
      (RawTwoCellExpr.castBoundary (congrArg (fun path => composePath path monadT) hsource)
        (congrArg (fun path => composePath path monadT) htarget)
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT cell)) := by
  cases hsource; cases htarget
  exact IdempotentMonadSaturatedTwoCellConv.refl _

/-- **Merge two casts across a vertical composite (CONV form).**  The seam `hmiddle` shared by the two factors
fuses across `vcomp` (`cases` on the three equalities).  The CONV form so the shared seam unifies by defeq even
when one side is `rfl` and the other `Eq.symm rfl`. -/
theorem vcompCastMergeConv
    {sourcePath sourcePath' middlePath middlePath' targetPath targetPath' :
      ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hsource : sourcePath = sourcePath') (hmiddle : middlePath = middlePath') (htarget : targetPath = targetPath')
    (cellAlpha : RawTwoCellExpr monadModeSignature sourcePath middlePath)
    (cellBeta : RawTwoCellExpr monadModeSignature middlePath targetPath) :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.castBoundary hsource hmiddle cellAlpha)
        (RawTwoCellExpr.castBoundary hmiddle htarget cellBeta))
      (RawTwoCellExpr.castBoundary hsource htarget (RawTwoCellExpr.vcomp cellAlpha cellBeta)) := by
  cases hsource; cases hmiddle; cases htarget
  exact IdempotentMonadSaturatedTwoCellConv.refl _

/-- `t^((inner+outer)+1) = t^(inner+1) · t^outer` — the RIGHT-append form of the successor ordinal sum (through
`succ_add`), the codomain boundary a `t^outer` RIGHT-whisker produces on `canonThroughT (a+outer) (inner+outer)`. -/
theorem monadTPower_succ_add_right (inner outer : Nat) :
    monadTPower ((inner + outer) + 1) = composePath (monadTPower (inner + 1)) (monadTPower outer) := by
  rw [show (inner + outer) + 1 = (inner + 1) + outer from (Nat.succ_add inner outer).symm]
  exact monadTPower_add (inner + 1) outer

/-! ## Right-section cancellation (the idempotence carrier for the grow-half) -/

/-- **Right-section cancellation.**  If two parallel cells `cellA`, `cellB : P ⇒ Q` become convertible after
post-composing a `foldMap : Q ⇒ P` (`hAB`), and that `foldMap` has a right section `growMap : P ⇒ Q` with
`foldMap ∘ growMap ≈ id_Q` (`hfg`), then `cellA ≈ cellB`.  The pure equational cancellation
`A ≈ A ∘ (foldMap ∘ growMap) ≈ (A ∘ foldMap) ∘ growMap ≈ (B ∘ foldMap) ∘ growMap ≈ B`.  The idempotence of the
walking idempotent monad enters ONLY through the caller's choice of `hfg` (`foldThenGrow`, the mu-iso round-trip). -/
theorem idempotentRightSectionCancel
    {oneCellP oneCellQ : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (foldMap : RawTwoCellExpr monadModeSignature oneCellQ oneCellP)
    (growMap : RawTwoCellExpr monadModeSignature oneCellP oneCellQ)
    (hfg : IdempotentMonadSaturatedTwoCellConv (RawTwoCellExpr.vcomp foldMap growMap)
      (RawTwoCellExpr.id (signature := monadModeSignature) oneCellQ))
    {cellA cellB : RawTwoCellExpr monadModeSignature oneCellP oneCellQ}
    (hAB : IdempotentMonadSaturatedTwoCellConv (RawTwoCellExpr.vcomp cellA foldMap)
      (RawTwoCellExpr.vcomp cellB foldMap)) :
    IdempotentMonadSaturatedTwoCellConv cellA cellB := by
  refine trans (symm (idempotentConvOfStep (TwoCellStep.vcompIdRight cellA))) ?_
  refine trans (vcompCongrRight cellA (symm hfg)) ?_
  refine trans (symm (idempotentConvOfStep (TwoCellStep.vcompAssoc cellA foldMap growMap))) ?_
  refine trans (vcompCongrLeft growMap hAB) ?_
  refine trans (idempotentConvOfStep (TwoCellStep.vcompAssoc cellB foldMap growMap)) ?_
  refine trans (vcompCongrRight cellB hfg) ?_
  exact idempotentConvOfStep (TwoCellStep.vcompIdRight cellB)

/-! ## The grow-then-fold column collapse -/

/-- ★ **Grow-column-fold ≈ mu.**  Right-whiskering the grow tower `grow n` by `t` (growing the LEFT `t` of `t·t`
up to `t^{n+1}`, keeping the right `t`) and then folding the whole `t^{n+2}` down to one is convertible to the bare
`mu`.  Factored — NO Godement chase — through `gadgetSplitRight` (rewriting the fold as `(gadget (n+1) ▷ t) ∘ mu`)
+ `growThenFold` (the grow-then-fold round-trip collapsing `grow n ∘ gadget (n+1)` to `id_t`, using only the
left-unit law) + right-whisker distributivity.  Structural on `n` only through those two shipped lemmas. -/
theorem growColumnFold (n : Nat) :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n))
        (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT (n + 1)).symm rfl
          (monadGadget (n + 2))))
      monadMulTwoCell := by
  refine trans (vcompCongrRight _ (symm (gadgetSplitRight (n + 1)))) ?_
  refine trans (symm (idempotentConvOfStep (TwoCellStep.vcompAssoc
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n))
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (monadGadget (n + 1)))
    monadMulTwoCell))) ?_
  refine trans (vcompCongrLeft monadMulTwoCell (symm (idempotentConvOfStep
    (TwoCellStep.whiskerRightVcomp monadT (growTower n) (monadGadget (n + 1)))))) ?_
  refine trans (vcompCongrLeft monadMulTwoCell (whiskerRightCongr monadT (growThenFold n))) ?_
  refine trans (vcompCongrLeft monadMulTwoCell (idempotentConvOfStep
    (TwoCellStep.whiskerRightId (signature := monadModeSignature) monadT monadT))) ?_
  exact idempotentConvOfStep (TwoCellStep.vcompIdLeft monadMulTwoCell)

/-! ## The grow-half right-whisker (the genuine idempotence-using dual of `gadgetSplitRight`) -/

/-- ★★ **The GROW-half right-whisker.**  `(eta ▷ t) ∘ (t^{n+1} ← grow n ▷ t) ≈ grow (n+1)` (transported across the
append cast `t^{n+1}·t = t^{n+2}`).  Unlike `gadgetSplitRight` (pure monad law), this GENUINELY uses idempotence:
the two grow towers are non-convertible in the plain walking monad, and the proof cancels the fold on the right by
the mu-iso round-trip `foldThenGrow (n+1)` (`idempotentRightSectionCancel`), reducing the LHS-after-fold to `mu ∘ …`
that collapses via `growColumnFold` and the left-unit law. -/
theorem growTowerRightWhisker (n : Nat) :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.castBoundary rfl (composePath_monadTPower_monadT (n + 1))
        (RawTwoCellExpr.vcomp monadEtaTCell
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n))))
      (growTower (n + 1)) := by
  refine idempotentRightSectionCancel (monadGadget (n + 2)) (growTower (n + 1)) (foldThenGrow (n + 1)) ?_
  refine trans ?_ (symm (growThenFold (n + 1)))
  refine trans (vcompCastLeftExtrude rfl (composePath_monadTPower_monadT (n + 1))
    (RawTwoCellExpr.vcomp monadEtaTCell
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n)))
    (monadGadget (n + 2))) ?_
  show IdempotentMonadSaturatedTwoCellConv
    (RawTwoCellExpr.vcomp
      (RawTwoCellExpr.vcomp monadEtaTCell
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n)))
      (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT (n + 1)).symm rfl (monadGadget (n + 2))))
    (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
  refine trans (idempotentConvOfStep (TwoCellStep.vcompAssoc monadEtaTCell
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n))
    (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT (n + 1)).symm rfl
      (monadGadget (n + 2))))) ?_
  refine trans (vcompCongrRight monadEtaTCell (growColumnFold n)) ?_
  exact ofMonad MonadSaturatedTwoCellConv.leftUnit

/-! ## The single-`t` RIGHT-whisker canonicalisation -/

/-- ★ **Single-`t` RIGHT-whisker canonicalisation** — `t ▷ (canonThroughT a n) ≈ canonThroughT (a+1)(n+1)`
(transported across the two append casts).  The RIGHT mirror of `whiskerLeftCanonOne`: distribute the whisker over
the `vcomp`, insert the mu-iso `id_{t.t} ≈ mu ∘ (eta ▷ t)` in the middle `t.t`, reassociate so the fold half is
`gadgetSplitRight a` and the grow half is `growTowerRightWhisker n`, then fuse the two append casts. -/
theorem whiskerRightCanonOne (a n : Nat) :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (canonThroughT a n))
      (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT a).symm
        (composePath_monadTPower_monadT (n + 1)).symm (canonThroughT (a + 1) (n + 1))) := by
  show IdempotentMonadSaturatedTwoCellConv
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT
      (RawTwoCellExpr.vcomp (monadGadget a) (growTower n))) _
  refine trans (idempotentConvOfStep
    (TwoCellStep.whiskerRightVcomp monadT (monadGadget a) (growTower n))) ?_
  refine trans (vcompCongrRight _ (symm (idempotentConvOfStep
    (TwoCellStep.vcompIdLeft
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n)))))) ?_
  refine trans (vcompCongrRight _ (vcompCongrLeft _ (symm idempotentMulRightInverse))) ?_
  refine trans (vcompCongrRight _ (idempotentConvOfStep
    (TwoCellStep.vcompAssoc monadMulTwoCell monadEtaTCell
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n))))) ?_
  refine trans (symm (idempotentConvOfStep
    (TwoCellStep.vcompAssoc
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (monadGadget a))
      monadMulTwoCell
      (RawTwoCellExpr.vcomp monadEtaTCell
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower n)))))) ?_
  refine trans (vcompCongrLeft _ (gadgetSplitRight a)) ?_
  refine trans (vcompCongrRight _
    (IdempotentMonadSaturatedTwoCellConv.ofCastLeft rfl (composePath_monadTPower_monadT (n + 1))
      (growTowerRightWhisker n))) ?_
  exact vcompCastMergeConv (composePath_monadTPower_monadT a).symm rfl
    (composePath_monadTPower_monadT (n + 1)).symm (monadGadget (a + 1)) (growTower (n + 1))

/-! ## The general-width RIGHT-whisker canonicalisation -/

/-- ★ **General-width RIGHT-whisker canonicalisation** — `t^k ▷ (canonThroughT a n) ≈ canonThroughT (a+k)(n+k)`
(transported).  The RIGHT mirror of `whiskerLeftCanon`; structural induction on `k`.  The base `k = 0` is the
unit-1-cell right whisker (`whiskerRightUnit`, casts collapsing definitionally); the step re-expresses `t^{k+1}` as
`t^k · t` (append cast, `whiskerRight_whiskerEq`), peels one OUTER `t` (`whiskerRightComp`), threads the induction
hypothesis under the outer `t`-whisker, and re-folds by the single-`t` `whiskerRightCanonOne` — the index `(a+k, n+k)`
grows DEFINITIONALLY (`a+(k+1) = (a+k)+1`), so the fresh cost vs the LEFT is only the append casts. -/
theorem whiskerRightCanon : (k a n : Nat) →
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower k) (canonThroughT a n))
      (RawTwoCellExpr.castBoundary (monadTPower_add a k) (monadTPower_succ_add_right n k)
        (canonThroughT (a + k) (n + k)))
  | 0, a, n => idempotentConvOfFull (TwoCellConvFull.whiskerRightUnit (canonThroughT a n))
  | k + 1, a, n => by
      -- Peel one OUTER `t` after re-expressing `t^{k+1}` as the append `t^k · t`, then thread the induction
      -- hypothesis under the outer `t`-whisker and re-fold by `whiskerRightCanonOne`.  Every boundary cast is
      -- fused by the CONV-level helpers (applied, defeq unification) — no `rw` on cast towers.
      rw [whiskerRight_whiskerEq (composePath_monadTPower_monadT k) (canonThroughT a n)]
      refine trans (castBoundaryCongr _ _ (idempotentConvOfFull
        (TwoCellConvFull.whiskerRightComp (monadTPower k) monadT (canonThroughT a n)))) ?_
      refine trans (castChainCollapseConv _ _ _ _ _) ?_
      refine trans (castBoundaryCongr _ _ (whiskerRightCongr monadT (whiskerRightCanon k a n))) ?_
      refine trans (castBoundaryCongr _ _
        (whiskerRightPullMonadTConv _ _ (canonThroughT (a + k) (n + k)))) ?_
      refine trans (castChainCollapseConv _ _ _ _ _) ?_
      refine trans (castBoundaryCongr _ _ (whiskerRightCanonOne (a + k) (n + k))) ?_
      refine trans (castChainCollapseConv _ _ _ _ _) ?_
      exact IdempotentMonadSaturatedTwoCellConv.refl _

/-! ## Non-vacuity smokes -/

/-- Smoke: a GENUINE positive-width grow-half right whisker — `(eta ▷ t) ∘ (t^3 ← grow 2 ▷ t) ≈ grow 3`
(transported), the idempotence-using dual peel at width `2`.  Decided by `growTowerRightWhisker`. -/
theorem growTowerRightWhisker_two_smoke :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.castBoundary rfl (composePath_monadTPower_monadT 3)
        (RawTwoCellExpr.vcomp monadEtaTCell
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (growTower 2))))
      (growTower 3) :=
  growTowerRightWhisker 2

/-- Smoke: a GENUINE positive-width general right whisker — `t^2 ▷ (canonThroughT 2 1) ≈ canonThroughT 4 3`
(transported), a `t^2` append of a non-trivial through-`t` cell.  Decided by `whiskerRightCanon`. -/
theorem whiskerRightCanon_width_two_smoke :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower 2) (canonThroughT 2 1))
      (RawTwoCellExpr.castBoundary (monadTPower_add 2 2) (monadTPower_succ_add_right 1 2)
        (canonThroughT (2 + 2) (1 + 2))) :=
  whiskerRightCanon 2 2 1

/-! ## Honesty marker -/

/-- ★★ **ESTABLISHED — the general-width RIGHT-whisker canonicalisation is CLOSED, zero-axiom.**  `t^k ▷
(canonThroughT a n) ≈ canonThroughT (a+k)(n+k)` (transported) for EVERY width `k` (`whiskerRightCanon`), the RIGHT
mirror of `whiskerLeftCanon`.  The genuine idempotence-USING brick is the grow-half `growTowerRightWhisker`
(`(eta ▷ t) ∘ (grow n ▷ t) ≈ grow (n+1)`), which the recon flagged as "a fresh induction comparable in size to
`gadgetSplitRight`" but which turns out CHEAPER: its idempotence is delegated to the shipped mu-iso round-trip
`foldThenGrow` via a right-section cancellation, and its inner column collapse `growColumnFold` factors through
`gadgetSplitRight` (fold half) + `growThenFold` — no fresh Godement chase.  With `whiskerLeftCanon` (LEFT) +
`whiskerRightCanon` (RIGHT) both closed, the two whisker cases of the boundary-determined normalizer have their
canonicalisation bricks.  `= true`. -/
def fxIdempotentMonad_hasWhiskerRightCanonClosed : Bool := true

end FX1Poly.Polygraph

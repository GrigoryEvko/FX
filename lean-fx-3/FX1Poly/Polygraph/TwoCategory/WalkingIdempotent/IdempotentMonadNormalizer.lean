import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadMuInvertible

/-! # WalkingIdempotent/IdempotentMonadNormalizer — the fold/grow ladder (general-`n` mu-iso iterate)

`IdempotentMonadMuInvertible` mechanized the mu-iso base case `mu ∘ (eta ▷ t) ≈ id_{t.t}`
(`idempotentMulRightInverse`, the `n = 2` fold-then-grow) and named the residual: the general-`n`
boundary-determined normalizer, whose crux is the fold-then-grow collapse `growTower n ∘ foldDown n ≈ id_{t^n}`,
the `n`-fold ITERATE of that base.  This file ships that iterate.

## The tower collapse `t^{n+1} ≅ t`

Because `mu` is invertible, every power `t^{n+1}` is isomorphic to `t`.  The two composites of that iso are:

  * **`monadGadget (n+1)`** `t^{n+1} ⇒ t`  — the FOLD (a right-leaning `mu`-tree; reused from the walking-monad
    Eilenberg–Zilber word-builder), and
  * **`growTower n`** `t ⇒ t^{n+1}`  — the GROW (an `eta`-tower, left-recursive to mirror the fold's left-whisker
    recursion, so the iterate collapses cleanly).

★ **`foldThenGrow n`** : `(monadGadget (n+1)) ∘ (growTower n) ≈ id_{t^{n+1}}` — the fold-then-grow round-trip, the
`n`-fold iterate of `idempotentMulRightInverse` (the SOLE idempotence use per layer), threaded by left-whisker
functoriality.  ★ **`growThenFold n`** : `(growTower n) ∘ (monadGadget (n+1)) ≈ id_t` — the DUAL round-trip, whose
per-layer base is the EASY left-unit monad law (no idempotence).  Together they exhibit the tower iso in both hom
directions — the general-`n` fold/grow ladder.

Raw Lean 4 + Init; STRUCTURAL `Nat` recursion (no `WellFounded.fix`); the two round-trips lift the shipped
`idempotentMulRightInverse` / left-unit law through the free-strict-2-category congruences.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

open IdempotentMonadSaturatedTwoCellConv

/-! ## The grow tower `t ⇒ t^{k+1}` (the dual of the fold `monadGadget`) -/

/-- ★ The **grow tower** `t ⇒ t^{k+1}` — grow a single `t` up to `t^{k+1}` by inserting `k` units.  `k = 0` is the
identity `id_t : t ⇒ t^1`; the successor prepends one `eta ▷ t : t ⇒ t.t` and left-whiskers the shorter tower by
`t` (`monadEtaTCell ∘ (t ◁ growTower k) : t ⇒ t.t ⇒ t^{k+2}`).  Left-recursive to line up definitionally with
`monadGadget`'s left-whisker fold, so the fold-then-grow iterate cancels cleanly.  Structural recursion on `k`. -/
def growTower : (k : Nat) → RawTwoCellExpr monadModeSignature monadT (monadTPower (k + 1))
  | 0 => RawTwoCellExpr.id (signature := monadModeSignature) monadT
  | k + 1 =>
      RawTwoCellExpr.vcomp monadEtaTCell
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower k))

/-- The **through-`t` canonical cell** `t^m ⇒ t^{targetPred+1}`: fold `t^m` down to a single `t` (`monadGadget m`)
then grow it back up to `t^{targetPred+1}` (`growTower targetPred`).  Total and cell-INDEPENDENT for every nonempty
target — the boundary-determined representative every populated hom collapses onto. -/
def canonThroughT (sourceCount targetPred : Nat) :
    RawTwoCellExpr monadModeSignature (monadTPower sourceCount) (monadTPower (targetPred + 1)) :=
  RawTwoCellExpr.vcomp (monadGadget sourceCount) (growTower targetPred)

/-! ## Freeness / boundary smokes for the tower -/

/-- Smoke: `growTower 0` is the identity `id_t` (no insertion). -/
theorem growTower_zero :
    growTower 0 = RawTwoCellExpr.id (signature := monadModeSignature) monadT := rfl

/-- Smoke: `growTower 1 : t ⇒ t.t` unfolds to a genuine composite `eta ▷ t` then `t ◁ id_t` — not a bare atom, so
its round-trip with `mu` being `id` is CONTENT (the mu-iso), not definitional. -/
theorem growTower_one_unfold :
    growTower 1 = RawTwoCellExpr.vcomp monadEtaTCell
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT)) := rfl

/-! ## The fold-then-grow round-trip (the idempotence iterate) -/

/-- ★★ **Fold-then-grow ≈ identity** — `(monadGadget (k+1)) ∘ (growTower k) ≈ id_{t^{k+1}}`.  The `n`-fold ITERATE
of the shipped mu-iso base `idempotentMulRightInverse` (`n = 2`).  Structural induction on `k`: the base `k = 0` is
`id_t ∘ id_t ≈ id_t`; the step reassociates the composite so the inner `mu ∘ (eta ▷ t)` collapses by
`idempotentMulRightInverse` (the SOLE idempotence use per layer), the outer `id`-left cleanup leaves a left-whisker
of the shorter fold-then-grow, closed by the induction hypothesis under `whiskerLeftCongr` + `whiskerLeftId`. -/
theorem foldThenGrow : (k : Nat) →
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (monadGadget (k + 1)) (growTower k))
      (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower (k + 1)))
  | 0 => by
      show IdempotentMonadSaturatedTwoCellConv
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
          (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
      exact idempotentConvOfStep
        (TwoCellStep.vcompIdLeft (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
  | k + 1 => by
      show IdempotentMonadSaturatedTwoCellConv
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (k + 1)))
            monadMulTwoCell)
          (RawTwoCellExpr.vcomp monadEtaTCell
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower k))))
        (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower (k + 1 + 1)))
      refine IdempotentMonadSaturatedTwoCellConv.trans (idempotentConvOfStep (TwoCellStep.vcompAssoc
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (k + 1)))
        monadMulTwoCell
        (RawTwoCellExpr.vcomp monadEtaTCell
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower k))))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (vcompCongrRight _ (symm (idempotentConvOfStep (TwoCellStep.vcompAssoc
        monadMulTwoCell monadEtaTCell
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower k)))))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (vcompCongrRight _ (vcompCongrLeft _ idempotentMulRightInverse)) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (vcompCongrRight _ (idempotentConvOfStep (TwoCellStep.vcompIdLeft
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower k))))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (symm (idempotentConvOfStep (TwoCellStep.whiskerLeftVcomp
        monadT (monadGadget (k + 1)) (growTower k)))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (whiskerLeftCongr monadT (foldThenGrow k)) ?_
      show IdempotentMonadSaturatedTwoCellConv
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower (k + 1))))
        (RawTwoCellExpr.id (signature := monadModeSignature) (composePath monadT (monadTPower (k + 1))))
      exact idempotentConvOfStep
        (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT (monadTPower (k + 1)))

/-! ## The grow-then-fold round-trip (the dual, via the left-unit law) -/

/-- ★★ **Grow-then-fold ≈ identity** — `(growTower g) ∘ (monadGadget (g+1)) ≈ id_t`.  The DUAL round-trip of the
mu-iso tower, at the hom `t ⇒ t`.  Structural induction on `g`: the base is `id_t ∘ id_t ≈ id_t`; the step
reassociates so the sandwiched `(t ◁ (grow ∘ fold)) ∘ mu` collapses via the induction hypothesis (under a left
whisker) to `id_{t.t} ∘ mu ≈ mu`, and the outer `eta ▷ t` then `mu` is the LEFT-UNIT monad law — no idempotence in
this direction, only the shipped `MonadSaturatedTwoCellConv.leftUnit`. -/
theorem growThenFold : (g : Nat) →
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (growTower g) (monadGadget (g + 1)))
      (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
  | 0 => by
      show IdempotentMonadSaturatedTwoCellConv
        (RawTwoCellExpr.vcomp (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
          (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
      exact idempotentConvOfStep
        (TwoCellStep.vcompIdLeft (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
  | g + 1 => by
      show IdempotentMonadSaturatedTwoCellConv
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.vcomp monadEtaTCell
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower g)))
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (g + 1)))
            monadMulTwoCell))
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
      refine IdempotentMonadSaturatedTwoCellConv.trans (idempotentConvOfStep (TwoCellStep.vcompAssoc
        monadEtaTCell
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower g))
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (g + 1)))
          monadMulTwoCell))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (vcompCongrRight _ (symm (idempotentConvOfStep (TwoCellStep.vcompAssoc
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower g))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (g + 1)))
        monadMulTwoCell)))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (vcompCongrRight _ (vcompCongrLeft _
        (symm (idempotentConvOfStep (TwoCellStep.whiskerLeftVcomp
          monadT (growTower g) (monadGadget (g + 1))))))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (vcompCongrRight _ (vcompCongrLeft _
        (whiskerLeftCongr monadT (growThenFold g)))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (vcompCongrRight _ (vcompCongrLeft _
        (idempotentConvOfStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT monadT)))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans (vcompCongrRight _ (idempotentConvOfStep (TwoCellStep.vcompIdLeft monadMulTwoCell))) ?_
      show IdempotentMonadSaturatedTwoCellConv monadLeftUnitCell
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
      exact ofMonad MonadSaturatedTwoCellConv.leftUnit

/-! ## Single-`t` LEFT-whisker canonicalisation (no boundary cast — `t` prepends, matching `monadTPower`) -/

/-- **Fold-whisker step** — `(t ◁ (monadGadget a)) ∘ mu ≈ monadGadget (a+1)`.  Folding a `t`-block of width `a`
under a leading `t`, then multiplying, is the fold of width `a+1`.  For `a ≥ 1` this is DEFINITIONAL (it is exactly
`monadGadget`'s successor equation); for `a = 0` it is the RIGHT-UNIT monad law (`t ◁ eta` then `mu ≈ id_t`,
`monadRightUnitCell ≈ monadGadget 1`).  Structural case split on `a`. -/
theorem foldWhiskerStep : (a : Nat) →
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget a))
        monadMulTwoCell)
      (monadGadget (a + 1))
  | 0 => by
      show IdempotentMonadSaturatedTwoCellConv monadRightUnitCell
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT)
      exact ofMonad MonadSaturatedTwoCellConv.rightUnit
  | a + 1 =>
      IdempotentMonadSaturatedTwoCellConv.refl
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (a + 1)))
          monadMulTwoCell)

/-- ★ **Single-`t` LEFT-whisker canonicalisation** — `t ◁ (canonThroughT a tp) ≈ canonThroughT (a+1) (tp+1)`.
Distribute the whisker over the `vcomp`, insert `id_{t.t} ≈ mu ∘ (eta ▷ t)` (`idempotentMulRightInverse`) in the
middle `t.t`, reassociate so the fold half becomes `(t ◁ monadGadget a) ∘ mu ≈ monadGadget (a+1)` (`foldWhiskerStep`)
and the grow half becomes `(eta ▷ t) ∘ (t ◁ growTower tp)` — DEFINITIONALLY `growTower (tp+1)`.  No boundary cast:
`t` prepends, lining up with `monadTPower`'s left-nesting. -/
theorem whiskerLeftCanonOne (sourceCount targetPred : Nat) :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (canonThroughT sourceCount targetPred))
      (canonThroughT (sourceCount + 1) (targetPred + 1)) := by
  show IdempotentMonadSaturatedTwoCellConv
    (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
      (RawTwoCellExpr.vcomp (monadGadget sourceCount) (growTower targetPred)))
    (RawTwoCellExpr.vcomp (monadGadget (sourceCount + 1)) (growTower (targetPred + 1)))
  refine IdempotentMonadSaturatedTwoCellConv.trans (idempotentConvOfStep
    (TwoCellStep.whiskerLeftVcomp monadT (monadGadget sourceCount) (growTower targetPred))) ?_
  refine IdempotentMonadSaturatedTwoCellConv.trans (vcompCongrRight _ (symm (idempotentConvOfStep
    (TwoCellStep.vcompIdLeft
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower targetPred)))))) ?_
  refine IdempotentMonadSaturatedTwoCellConv.trans (vcompCongrRight _
    (vcompCongrLeft _ (symm idempotentMulRightInverse))) ?_
  refine IdempotentMonadSaturatedTwoCellConv.trans (vcompCongrRight _ (idempotentConvOfStep
    (TwoCellStep.vcompAssoc monadMulTwoCell monadEtaTCell
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower targetPred))))) ?_
  refine IdempotentMonadSaturatedTwoCellConv.trans (symm (idempotentConvOfStep
    (TwoCellStep.vcompAssoc
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget sourceCount))
      monadMulTwoCell
      (RawTwoCellExpr.vcomp monadEtaTCell
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (growTower targetPred)))))) ?_
  exact vcompCongrLeft _ (foldWhiskerStep sourceCount)

/-! ## Non-vacuity smokes: the ladder decides GENUINE parallel pairs, the empty hom still SEPARATES

The fold/grow ladder is NOT vacuous — it collapses genuine, positive-width composites to the identity through
idempotence, while the boundary rigidity keeps the empty homs `t^{m+1} ⇒ nil` empty.  Together: populated homs are
thin, unpopulated homs are separated. -/

/-- Smoke: at `t^3` the fold-then-grow round-trip is a GENUINE positive-width collapse — `(monadGadget 3) ∘
(growTower 2) ≈ id_{t^3}` (`monadGadget 3` is a two-`mu` tree, `growTower 2` a two-`eta` tower; neither is an
identity), decided by the ladder.  A genuinely-nontrivial parallel pair `t^3 ⇒ t^3` collapsed to the identity. -/
theorem foldThenGrow_tPowerThree :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (monadGadget 3) (growTower 2))
      (RawTwoCellExpr.id (signature := monadModeSignature) (monadTPower 3)) :=
  foldThenGrow 2

/-- Smoke: two DISTINCT genuine composites at the hom `t.t ⇒ t.t` — `mu ∘ (eta ▷ t)` (size 4) and its `t ◁ eta`
twin `mu ∘ (t ◁ eta)` — are decided EQUAL by the ladder's base (the mu-iso), a populated hom collapsing to a
single 2-cell (thinness in action). -/
theorem homTThenT_thin_smoke :
    IdempotentMonadSaturatedTwoCellConv mulThenUnitRightWhisker
      (RawTwoCellExpr.vcomp monadMulTwoCell monadTEtaCell) :=
  trans idempotentMulRightInverse (symm idempotentMulRightInverse_leftWhisker)

/-- Smoke: the empty hom still SEPARATES — there is NO free 2-cell `t.t ⇒ nil` (rigidity forces `t.t`'s length `2`
to be `0`), so the ladder's thinness does not spuriously populate an empty hom.  The non-degeneracy the decision
relies on survives the normalizer layer. -/
theorem emptyHom_tThenT_separates
    (cell : RawTwoCellExpr monadModeSignature monadTThenT
      (ModalityPath.nil (graph := monadGraph) MonadMode.point)) :
    (2 : Nat) = 0 :=
  rawCell_targetLenZero_impliesSourceLenZero cell rfl

/-! ## Honesty marker -/

/-- ★★ **ESTABLISHED — the general-`n` fold/grow ladder (the mu-iso tower iterate).**  Both composites of the
tower isomorphism `t^{n+1} ≅ t` are mechanized zero-axiom: fold-then-grow `(monadGadget (n+1)) ∘ (growTower n) ≈
id_{t^{n+1}}` (`foldThenGrow`, the `n`-fold iterate of the shipped `idempotentMulRightInverse`, one idempotence use
per layer) and grow-then-fold `(growTower n) ∘ (monadGadget (n+1)) ≈ id_t` (`growThenFold`, via the left-unit monad
law).  This is the crux the shipped `fxIdempotentMonad_hasGeneralThinnessNormalizer` docstring named — "the general
fold-then-grow collapse, the `n`-fold iterate of `idempotentMulRightInverse`".  Non-vacuous: the ladder collapses
genuine positive-width composites (`foldThenGrow_tPowerThree`, `homTThenT_thin_smoke`) while the empty homs stay
separated (`emptyHom_tThenT_separates`).  `= true`. -/
def fxIdempotentMonad_hasFoldGrowLadder : Bool := true

/-- **ESTABLISHED — the single-`t` LEFT-whisker canonicalisation.**  Left-whiskering the through-`t` canonical cell
by a single `t` gives the canonical cell of the whiskered boundary — `t ◁ (canonThroughT a n) ≈ canonThroughT
(a+1) (n+1)` (`whiskerLeftCanonOne`), via the fold-whisker step `(t ◁ monadGadget a) ∘ mu ≈ monadGadget (a+1)`
(`foldWhiskerStep`) and the mu-iso middle-insertion.  NO boundary cast — `t` prepends, lining up with
`monadTPower`'s left-nesting.  This is the clean base case of the LEFT-whisker `normalizeCell` case.  `= true`. -/
def fxIdempotentMonad_hasWhiskerLeftCanonBase : Bool := true

/-- **Honesty marker — general-`n` normalizer NOT assembled this round; the fold/grow ladder + left-whisker base
are the closed layers.**  Inhabiting `IdempotentMonadLocalPosetality` needs the boundary-determined normalizer
`normalizeFull : cell ≈ repFull cell` (`idempotentThinness_ofNormalize`), whose five cases have three closed
foundations here — `id` via `foldThenGrow`, `vcomp` via `growThenFold`, single-`t` `whiskerLeft` via
`whiskerLeftCanonOne` — but three residual bricks remain, all forced onto the propext-CLEAN Nat-indexed route
(path-indexed recursion on `ModalityPath` leaks `propext` by matching the modality constructor on the
mode-indexed family, and its `composePath` reductions are NON-definitional):

  1. **General-width `whiskerLeft`** — `whiskerLeft (t^k) (canonThroughT a n) ≈ castBoundary (canonThroughT (k+a)
     (k+n))`, by induction on `k` peeling one `t` (`whiskerLeftComp` `composePath`-assoc cast) then
     `whiskerLeftCanonOne`, reconciling the `Nat.zero_add` / `Nat.succ_add` index shifts by cast.
  2. **`whiskerRight` (both widths)** — the append-fold coherence `foldPath (t^a · t) ≈ (monadGadget a ▷ t) ∘ mu`
     (`gadgetSplitRight`), by induction on `a` using monad ASSOCIATIVITY (the append-vs-prepend mismatch — `t`
     appends, opposite `monadTPower`'s left-nesting, needing `monadTPower_add` casts throughout); the analog of
     the walking monad's shipped 200-line `MonadWhiskerRightMult`.  This is the honest WALL.
  3. **`repFull` + `hRepBoundary`** — the boundary-determined total representative transporting `sourcePath` /
     `targetPath` onto `monadTPower` forms (`monadPath_normalForm`), with the `n = 0, m ≥ 1` branch discharged by
     rigidity (`rawCell_targetLenZero_impliesSourceLenZero`, the empty hom is `absurd`).

Until all three land and assemble into `normalizeFull`, `IdempotentMonadLocalPosetality` is NOT inhabited, the
decision is not total, and `fxIdempotentMonad_hasLocalPosetalityCollapse` /
`fxIdempotentMonad_hasGeneralThinnessNormalizer` stay `false`.  `= false`. -/
def fxIdempotentMonad_hasAssembledGeneralNormalizer : Bool := false

end FX1Poly.Polygraph

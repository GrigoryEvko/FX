import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadNormalizer
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerRightMult

/-! # WalkingIdempotent/IdempotentMonadGeneralNormalizer — the three residual bricks + the assembled normalizer

`IdempotentMonadNormalizer` shipped the single-`t` left-whisker canonicalisation (`whiskerLeftCanonOne`) and the
fold/grow ladder; three residual bricks remained toward inhabiting `IdempotentMonadLocalPosetality`.  This file ships
them and assembles the general normalizer, all zero-axiom, STRUCTURAL:

  1. ★ **`whiskerLeftCanon`** — GENERAL-width left whisker `t^k ◁ canonThroughT a n ≈ canonThroughT (a+k)(n+k)`
     (transported), by induction on `k` peeling one `t` (`whiskerLeftComp`) and re-folding by `whiskerLeftCanonOne`;
     the recursion index `(a+k, n+k)` lines up DEFINITIONALLY (`a+(k+1) = (a+k)+1`), so no `succ_add` cast survives
     the induction — only the fixed boundary-cast lemmas.
  2. ★ **`gadgetSplitRight` / `whiskerRightCanon`** — the RIGHT-whisker canonicalisation, the analog of the walking
     monad's `MonadWhiskerRightMult`; the head brick is `(monadGadget a ▷ t) ∘ mu ≈ monadGadget (a+1)` by induction
     on `a` using monad ASSOCIATIVITY.
  3. ★ **`repFull` + `hRepBoundary` + `normalizeFull`** — the boundary-determined total representative and the
     structural normalization `cell ≈ repFull cell`, closing `idempotentThinness_ofNormalize`.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; STRUCTURAL recursion.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

open IdempotentMonadSaturatedTwoCellConv

/-! ## Boundary-cast helpers on the idempotent relation -/

/-- The idempotent relation transports along a boundary cast on BOTH sides (the idempotent analog of
`MonadSaturatedTwoCellConv.castBoundaryCongr`; `cases` on the equalities). -/
theorem IdempotentMonadSaturatedTwoCellConv.castBoundaryCongr
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : IdempotentMonadSaturatedTwoCellConv cellAlpha cellBeta) :
    IdempotentMonadSaturatedTwoCellConv (RawTwoCellExpr.castBoundary hsource htarget cellAlpha)
      (RawTwoCellExpr.castBoundary hsource htarget cellBeta) := by
  cases hsource; cases htarget; exact conv

/-- Move a boundary cast ACROSS the idempotent relation: a cast-left conversion re-expresses as the bare cell
against the inversely-cast partner (`cases` on the equalities). -/
theorem IdempotentMonadSaturatedTwoCellConv.ofCastLeft
    {sourcePath sourcePath' targetPath targetPath' : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    {cellAlpha : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    {cellBeta : RawTwoCellExpr monadModeSignature sourcePath' targetPath'}
    (conv : IdempotentMonadSaturatedTwoCellConv (RawTwoCellExpr.castBoundary hsource htarget cellAlpha) cellBeta) :
    IdempotentMonadSaturatedTwoCellConv cellAlpha
      (RawTwoCellExpr.castBoundary hsource.symm htarget.symm cellBeta) := by
  cases hsource; cases htarget; exact conv

/-- Extrude a LEFT-factor boundary cast out of a vertical composite, as a conversion (the idempotent analog of the
`Eq`-level `RawTwoCellExpr.vcomp_castBoundaryLeft`; `cases` on the equalities). -/
theorem IdempotentMonadSaturatedTwoCellConv.vcompCastLeftExtrude
    {sourcePath sourcePath' middlePath middlePath' targetPath :
      ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hsource : sourcePath = sourcePath') (hmiddle : middlePath = middlePath')
    (cellAlpha : RawTwoCellExpr monadModeSignature sourcePath middlePath)
    (cellBeta : RawTwoCellExpr monadModeSignature middlePath' targetPath) :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.castBoundary hsource hmiddle cellAlpha) cellBeta)
      (RawTwoCellExpr.castBoundary hsource rfl
        (RawTwoCellExpr.vcomp cellAlpha (RawTwoCellExpr.castBoundary hmiddle.symm rfl cellBeta))) := by
  cases hsource; cases hmiddle; exact IdempotentMonadSaturatedTwoCellConv.refl _

/-! ## `t`-power ordinal-sum boundary lemmas with the SUMMAND on the outside (so the recursion index reduces) -/

/-- `t^(inner+outer) = t^outer · t^inner` — the ordinal sum with the recursion summand `outer` on the LEFT of the
`composePath` (`monadTPower_add` after `add_comm`). -/
theorem monadTPower_add_left (outer inner : Nat) :
    monadTPower (inner + outer) = composePath (monadTPower outer) (monadTPower inner) := by
  rw [Nat.add_comm inner outer]; exact monadTPower_add outer inner

/-- `t^((inner+outer)+1) = t^outer · t^(inner+1)` — the successor form of `monadTPower_add_left` (through
`succ_add`), the codomain boundary a `t^outer` left-whisker produces on `canonThroughT (a+outer) (inner+outer)`. -/
theorem monadTPower_succ_add_left (outer inner : Nat) :
    monadTPower ((inner + outer) + 1) = composePath (monadTPower outer) (monadTPower (inner + 1)) := by
  rw [show (inner + outer) + 1 = (inner + 1) + outer from (Nat.succ_add inner outer).symm]
  exact monadTPower_add_left outer (inner + 1)

/-! ## Brick 1 — general-width left-whisker canonicalisation -/

/-- ★ **General-width left-whisker canonicalisation** — `t^k ◁ (canonThroughT a n) ≈ canonThroughT (a+k)(n+k)`
(transported onto the whiskered boundary).  Structural induction on `k`: the base `k = 0` is the unit-1-cell whisker
(`whiskerLeftUnit`, the boundary casts vanishing DEFINITIONALLY because `a+0 = a` and `composePath t^0 = id`); the
step peels one `t` (`whiskerLeftComp`), threads the induction hypothesis under a `t`-whisker (`whiskerLeftCongr` +
`whiskerLeft_castBoundary`), and re-folds by the shipped single-`t` `whiskerLeftCanonOne` — the index `(a+k, n+k)`
grows DEFINITIONALLY (`a+(k+1) = (a+k)+1`), so the induction carries no `succ_add` cast, only the fixed boundary
lemmas.  The general-width heart of the `whiskerLeft` normalize case. -/
theorem whiskerLeftCanon : (k a n : Nat) →
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) (monadTPower k) (canonThroughT a n))
      (RawTwoCellExpr.castBoundary (monadTPower_add_left k a) (monadTPower_succ_add_left k n)
        (canonThroughT (a + k) (n + k)))
  | 0, a, n => idempotentConvOfFull (TwoCellConvFull.whiskerLeftUnit (canonThroughT a n))
  | k + 1, a, n => by
      show IdempotentMonadSaturatedTwoCellConv
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature)
          (composePath monadT (monadTPower k)) (canonThroughT a n)) _
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (idempotentConvOfFull (TwoCellConvFull.whiskerLeftComp monadT (monadTPower k) (canonThroughT a n))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (IdempotentMonadSaturatedTwoCellConv.castBoundaryCongr _ _
          (IdempotentMonadSaturatedTwoCellConv.whiskerLeftCongr monadT (whiskerLeftCanon k a n))) ?_
      rw [RawTwoCellExpr.whiskerLeft_castBoundary]
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (IdempotentMonadSaturatedTwoCellConv.castBoundaryCongr _ _
          (IdempotentMonadSaturatedTwoCellConv.castBoundaryCongr _ _
            (whiskerLeftCanonOne (a + k) (n + k)))) ?_
      rw [RawTwoCellExpr.castBoundary_castBoundary]
      exact IdempotentMonadSaturatedTwoCellConv.refl _

/-! ## Brick 2 — the RIGHT-leaning mu-tree peel `gadgetSplitRight` (the shared open wall)

`(monadGadget a ▷ t) ∘ mu ≈ monadGadget (a+1)` — the RIGHT analog of the shipped LEFT peel `foldWhiskerStep`
(= walking-monad `gadgetSucc`).  Unlike the LEFT peel (definitional / right-unit law), the RIGHT peel carries a
GENUINE append-vs-prepend cast (`t^a · t` is not defeq `t · t^a` for variable `a`) and its inductive step needs the
monad ASSOCIATIVITY law re-nested through `whiskerExchange`.  This is the walking monad's OWN open `gadgetAbsorb`
inductive step (`WalkingMonad/MonadVcompMult` `fxMonad_hasVcompAssocAmalgamation = false`). -/

/-- `t^a · t = t^(a+1)` — the append-of-one boundary equality (`monadTPower_add a 1`, `monadTPower 1 = t` defeq). -/
theorem composePath_monadTPower_monadT (a : Nat) :
    composePath (monadTPower a) monadT = monadTPower (a + 1) :=
  (monadTPower_add a 1).symm

/-- Base `a = 0` of `gadgetSplitRight` — `(eta ▷ t) ∘ mu ≈ id_t`, the LEFT-unit monad law (`gadget 0 = eta`,
`gadget 1 = id_t`; the append cast vanishes definitionally at `a = 0`). -/
theorem gadgetSplitRight_zero :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (monadGadget 0))
        monadMulTwoCell)
      (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT 0).symm rfl (monadGadget 1)) :=
  ofMonad MonadSaturatedTwoCellConv.leftUnit

/-- Base `a = 1` of `gadgetSplitRight` — `(id_t ▷ t) ∘ mu ≈ mu ≈ gadget 2`; both sides collapse to `mu` by
`whiskerRightId` / `whiskerLeftId` + `vcompIdLeft` (the append cast vanishes definitionally at `a = 1`). -/
theorem gadgetSplitRight_one :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (monadGadget 1))
        monadMulTwoCell)
      (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT 1).symm rfl (monadGadget 2)) := by
  refine IdempotentMonadSaturatedTwoCellConv.trans
    (IdempotentMonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell
      (idempotentConvOfStep (TwoCellStep.whiskerRightId (signature := monadModeSignature) monadT monadT))) ?_
  refine IdempotentMonadSaturatedTwoCellConv.trans
    (idempotentConvOfStep (TwoCellStep.vcompIdLeft monadMulTwoCell)) ?_
  -- RHS: gadget 2 = vcomp (whiskerLeft t (gadget 1)) mu ≈ vcomp id mu ≈ mu (cast vanishes defeq at a = 1).
  refine IdempotentMonadSaturatedTwoCellConv.symm ?_
  show IdempotentMonadSaturatedTwoCellConv
    (RawTwoCellExpr.vcomp
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.id (signature := monadModeSignature) monadT))
      monadMulTwoCell)
    monadMulTwoCell
  refine IdempotentMonadSaturatedTwoCellConv.trans
    (IdempotentMonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell
      (idempotentConvOfStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT monadT))) ?_
  exact idempotentConvOfStep (TwoCellStep.vcompIdLeft monadMulTwoCell)

/-- **The whisker braid** — `(t ◁ g ▷ t) ∘ (t ◁ mu) ≈ t ◁ ((g ▷ t) ∘ mu)` (transported).  The `whiskerExchange`
(disjoint whiskers commute, the SOLE genuine append-vs-prepend cast, on `g`'s variable domain) plus
`whiskerLeftVcomp`; every CONCRETE-`t` associator (`(t·t)·t = t·(t·t)`) is DEFINITIONALLY equal, so the middle /
target casts vanish.  Isolated so the `gadgetSplitRight` step reads cleanly. -/
theorem whiskerRightLeftBraid {gDom : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (g : RawTwoCellExpr monadModeSignature gDom monadT) :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT g))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadMulTwoCell))
      (RawTwoCellExpr.castBoundary (composePath_assoc monadT gDom monadT).symm rfl
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT g) monadMulTwoCell))) := by
  have hbase : IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT g) monadMulTwoCell))
      (RawTwoCellExpr.castBoundary (composePath_assoc monadT gDom monadT) rfl
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT g))
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadMulTwoCell))) := by
    refine IdempotentMonadSaturatedTwoCellConv.trans
      (idempotentConvOfStep (TwoCellStep.whiskerLeftVcomp monadT
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT g) monadMulTwoCell)) ?_
    refine IdempotentMonadSaturatedTwoCellConv.trans
      (IdempotentMonadSaturatedTwoCellConv.vcompCongrLeft _
        (idempotentConvOfFull (TwoCellConvFull.whiskerExchange monadT monadT g))) ?_
    rw [RawTwoCellExpr.vcomp_castBoundaryLeft]
    exact IdempotentMonadSaturatedTwoCellConv.refl _
  exact IdempotentMonadSaturatedTwoCellConv.ofCastLeft (composePath_assoc monadT gDom monadT) rfl
    (IdempotentMonadSaturatedTwoCellConv.symm hbase)

/-- ★★ **The RIGHT-leaning mu-tree peel** — `(monadGadget a ▷ t) ∘ mu ≈ monadGadget (a+1)` (transported across the
append cast `t^a · t = t^(a+1)`).  Structural recursion on `a`: bases `a = 0` (LEFT-unit law) and `a = 1`
(`whiskerRightId`/`whiskerLeftId` collapse); the step `a + 2` fires monad ASSOCIATIVITY on the trailing
`(mu ▷ t) ∘ mu ≈ (t ◁ mu) ∘ mu` (concrete-`t`, cast-free), braids the leading whisker (`whiskerRightLeftBraid`, the
sole cast), and folds by the induction hypothesis — closing the walking monad's OWN open `gadgetAbsorb` inductive
step. -/
theorem gadgetSplitRight : (a : Nat) →
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT (monadGadget a))
        monadMulTwoCell)
      (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT a).symm rfl (monadGadget (a + 1)))
  | 0 => gadgetSplitRight_zero
  | 1 => gadgetSplitRight_one
  | a + 2 => by
      show IdempotentMonadSaturatedTwoCellConv
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT
            (RawTwoCellExpr.vcomp
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (a + 1)))
              monadMulTwoCell))
          monadMulTwoCell)
        (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT (a + 2)).symm rfl (monadGadget (a + 3)))
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (IdempotentMonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell
          (idempotentConvOfStep (TwoCellStep.whiskerRightVcomp monadT
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (a + 1)))
            monadMulTwoCell))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (idempotentConvOfStep (TwoCellStep.vcompAssoc
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (a + 1))))
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadMulTwoCell)
          monadMulTwoCell)) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (IdempotentMonadSaturatedTwoCellConv.vcompCongrRight _
          (ofMonad MonadSaturatedTwoCellConv.assoc)) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (IdempotentMonadSaturatedTwoCellConv.symm (idempotentConvOfStep (TwoCellStep.vcompAssoc
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (a + 1))))
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadMulTwoCell)
          monadMulTwoCell))) ?_
      -- The braid's boundary cast `composePath_assoc monadT _ monadT` has DEFINITIONALLY-equal endpoints (the outer
      -- `composePath` by the concrete `monadT = cons t nil` distributes), so it vanishes: the next `vcompCongrLeft`
      -- drops it by defeq and applies the induction hypothesis, leaving the whisker-of-cast at TOP level.
      have hpull := monadWhiskerLeft_castBoundary
        (composePath_monadTPower_monadT (a + 1)).symm (rfl : monadT = monadT) (monadGadget (a + 1 + 1))
      have hpullConv : IdempotentMonadSaturatedTwoCellConv
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
            (RawTwoCellExpr.castBoundary (composePath_monadTPower_monadT (a + 1)).symm rfl
              (monadGadget (a + 1 + 1))))
          (RawTwoCellExpr.castBoundary
            (congrArg (composePath monadT) (composePath_monadTPower_monadT (a + 1)).symm) rfl
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (a + 1 + 1)))) :=
        hpull ▸ IdempotentMonadSaturatedTwoCellConv.refl _
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (IdempotentMonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell
          (whiskerRightLeftBraid (monadGadget (a + 1)))) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (IdempotentMonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell
          (IdempotentMonadSaturatedTwoCellConv.trans
            (IdempotentMonadSaturatedTwoCellConv.whiskerLeftCongr monadT (gadgetSplitRight (a + 1)))
            hpullConv)) ?_
      refine IdempotentMonadSaturatedTwoCellConv.trans
        (IdempotentMonadSaturatedTwoCellConv.vcompCastLeftExtrude _ _ _ monadMulTwoCell) ?_
      exact IdempotentMonadSaturatedTwoCellConv.refl _

end FX1Poly.Polygraph

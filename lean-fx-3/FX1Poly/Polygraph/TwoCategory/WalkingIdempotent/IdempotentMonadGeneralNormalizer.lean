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

end FX1Poly.Polygraph

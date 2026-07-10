import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeVcomp
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadLawRelation
import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchSaturated

import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeCasesGen

/-! # WalkingMonad/MonadVcompMultGen — the mu-tree gadget amalgamation over the GENERIC carrier
(POLY-TAB r6 monad re-founding, WAVE 2, Brick A)

The gadget-level monad-law amalgamation re-founded over `SaturatedConvOver monadModeSignature MonadLawRel`:
`gadgetSuccGen` (right-unit), `gadgetAbsorb_zeroGen` (left-unit), `gadgetMuCrossGen` (associativity), and
`gadgetAbsorbGen`.  These are the ONLY leaves using the monad LAWS — the three bespoke law ctors become
`monadLeftUnitRowGen` / `monadRightUnitRowGen` / `monadAssocRowGen` (each `ofRelation` of a `MonadLawRel` row).
Carrier-only cast/Godement lemmas (`godementExchange`, `hcompOrder_twoCellConv`, `monadGadget_cast*`) are REUSED.

Raw Lean 4 + Init; zero-axiom; STRUCTURAL.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The mu-tree gadget amalgamation (the three monad laws), generic carrier -/

/-- ★ **The uniform mu-tree peel.**  `(t ◁ gadget d) ⊟ mu ≈ gadget (d + 1)` for EVERY `d`: definitional for
`d ≥ 1` (that IS the `count + 2` gadget clause), and the RIGHT-unit monad law `mu ∘ (t ◁ eta) ≈ id_t` at `d = 0`
(`gadget 0 = eta`, `gadget 1 = id_t`).  This makes `gadget` peel uniformly at the convertibility level despite its
`0` / `1` / `n+2` definitional branching. -/
theorem gadgetSuccGen : ∀ (d : Nat),
    SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget d))
        monadMulTwoCell)
      (monadGadget (d + 1))
  | 0 => monadRightUnitRowGen
  | _ + 1 => SaturatedConvOver.refl (baseRel := MonadLawRel) _

/-- ★ **The `eta`-gadget absorbs (the monad LEFT-unit law at arbitrary merge width).**  Merging a freshly-inserted
unit strand (`gadget 0 = eta`) with a `d`-fold merge and then multiplying is the `d`-fold merge itself:
`(eta ⊠ gadget d) ⊟ mu ≈ gadget d`.  Cast-free — `t^0 · t^d = t^d` definitionally.  Proof: the Godement EXCHANGE
reorders `eta ⊠ gadget d` to `(t^0 ◁ gadget d) ⊟ (t ▷ eta)`, the unit-1-cell left whisker strips (`whiskerLeftUnit`),
reassociation brings `eta ▷ t` adjacent to `mu`, and the LEFT-unit monad law `mu ∘ (eta ▷ t) ≈ id_t` fires
(`vcompIdRight` clears the residual identity).  This is one of the two monad-law adjacencies the residual needs. -/
theorem gadgetAbsorb_zeroGen (d : Nat) :
    SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.hcomp (monadGadget 0) (monadGadget d)) monadMulTwoCell)
      (monadGadget d) := by
  -- Reorder the Godement product: hcomp eta (gadget d) ≈ vcomp (gadget d) (t ▷ eta).
  have hExchange : SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.hcomp (monadGadget 0) (monadGadget d))
      (RawTwoCellExpr.vcomp (monadGadget d)
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)) := by
    refine SaturatedConvOver.trans
      (SaturatedConvOver.ofFull (baseRel := MonadLawRel) (godementExchange monadUnitTwoCell (monadGadget d))) ?_
    exact SaturatedConvOver.vcompCongrLeft _
      (SaturatedConvOver.ofFull (baseRel := MonadLawRel) (TwoCellConvFull.whiskerLeftUnit (monadGadget d)))
  refine SaturatedConvOver.trans
    (SaturatedConvOver.vcompCongrLeft monadMulTwoCell hExchange) ?_
  -- Reassociate so (eta ▷ t) ⊟ mu = monadLeftUnitCell is adjacent.
  refine SaturatedConvOver.trans
    (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
      (TwoCellStep.vcompAssoc (monadGadget d)
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
        monadMulTwoCell))) ?_
  -- Fire the LEFT-unit law: (eta ▷ t) ⊟ mu ≈ id_t.
  refine SaturatedConvOver.trans
    (SaturatedConvOver.vcompCongrRight (monadGadget d) monadLeftUnitRowGen) ?_
  -- Clear the residual identity.
  exact SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
    (TwoCellStep.vcompIdRight (monadGadget d)))

/-- The **Godement bridge**: the two whiskering orders of `hcomp mu (gadget d)` are saturated-convertible —
`(t ◁ t ◁ gadget d) ⊟ (mu ▷ t) ≈ (mu ▷ t^d) ⊟ (t ◁ gadget d)`.  The shipped cast-free `hcompOrder_twoCellConv`
gives `(mu ▷ t^d) ⊟ (t ◁ gadget d) ≈ (t·t ◁ gadget d) ⊟ (mu ▷ t)`; the leading double-`t` left whisker equals the
`t·t` whisker (`whiskerLeftComp`), whose associator cast is definitionally the identity because the whisker is a
concrete `t`-power (`composePath monadT monadT` flattens to `monadTThenT`).  No boundary cast survives. -/
theorem godementMuGadgetGen (mergeWidth : Nat) :
    SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth)))
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadMulTwoCell))
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower mergeWidth) monadMulTwoCell)
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth))) := by
  refine SaturatedConvOver.trans
    (SaturatedConvOver.vcompCongrLeft
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadMulTwoCell)
      (SaturatedConvOver.symm
        (SaturatedConvOver.ofFull (baseRel := MonadLawRel)
          (TwoCellConvFull.whiskerLeftComp monadT monadT (monadGadget mergeWidth))))) ?_
  exact SaturatedConvOver.symm
    (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (hcompOrder_twoCellConv monadMulTwoCell (monadGadget mergeWidth)))

/-- ★ **The associativity CROSSING** (the exact residual pinned by r13, closed).  Multiplying the first two strands
(`mu ▷ t^d`) then merging the resulting `d+1` strands equals the `(d+2)`-fold merge:
`(mu ▷ t^d) ⊟ gadget (d+1) ≈ gadget (d+2)`.  Cast-free — all boundaries are concrete `t`-powers.  Both sides
reduce to `(mu ▷ t^d) ⊟ (t ◁ gadget d) ⊟ mu = (hcomp mu (gadget d)) ⊟ mu`: the LHS by peeling `gadget (d+1)` with
`gadgetSuccGen` and reassociating; the RHS `gadget (d+2)` by unfolding the top `mu`-tree clause, distributing the
left whisker (`whiskerLeftVcomp`), firing the monad ASSOCIATIVITY law `(t ◁ mu) ⊟ mu ≈ (mu ▷ t) ⊟ mu`, and
reconciling the two Godement orders (`godementMuGadgetGen`).  This is the SOLE step of `gadgetAbsorbGen` using the
associativity law. -/
theorem gadgetMuCrossGen (mergeWidth : Nat) :
    SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower mergeWidth) monadMulTwoCell)
        (monadGadget (mergeWidth + 1)))
      (monadGadget (mergeWidth + 2)) := by
  have hCommon : SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower mergeWidth) monadMulTwoCell)
        (monadGadget (mergeWidth + 1)))
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower mergeWidth) monadMulTwoCell)
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth)))
        monadMulTwoCell) := by
    refine SaturatedConvOver.trans
      (SaturatedConvOver.vcompCongrRight
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower mergeWidth) monadMulTwoCell)
        (SaturatedConvOver.symm (gadgetSuccGen mergeWidth))) ?_
    exact SaturatedConvOver.symm
      (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
        (TwoCellStep.vcompAssoc
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower mergeWidth) monadMulTwoCell)
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth))
          monadMulTwoCell)))
  refine SaturatedConvOver.trans hCommon (SaturatedConvOver.symm ?_)
  show SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (mergeWidth + 1)))
        monadMulTwoCell)
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower mergeWidth) monadMulTwoCell)
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth)))
        monadMulTwoCell)
  refine SaturatedConvOver.trans
    (SaturatedConvOver.vcompCongrLeft monadMulTwoCell
      (SaturatedConvOver.whiskerLeftCongr monadT
        (SaturatedConvOver.symm (gadgetSuccGen mergeWidth)))) ?_
  refine SaturatedConvOver.trans
    (SaturatedConvOver.vcompCongrLeft monadMulTwoCell
      (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
        (TwoCellStep.whiskerLeftVcomp monadT
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth))
          monadMulTwoCell)))) ?_
  refine SaturatedConvOver.trans
    (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
      (TwoCellStep.vcompAssoc
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth)))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadMulTwoCell)
        monadMulTwoCell))) ?_
  refine SaturatedConvOver.trans
    (SaturatedConvOver.vcompCongrRight
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth)))
      (SaturatedConvOver.symm monadAssocRowGen)) ?_
  refine SaturatedConvOver.trans
    (SaturatedConvOver.symm
      (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
        (TwoCellStep.vcompAssoc
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth)))
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadMulTwoCell)
          monadMulTwoCell)))) ?_
  exact SaturatedConvOver.vcompCongrLeft monadMulTwoCell (godementMuGadgetGen mergeWidth)

/-- **FormB** — the absorb LHS reduces to a right-whisker form, cast-free and monad-law-free:
`(gadget c ⊠ gadget d) ⊟ mu ≈ (gadget c ▷ t^d) ⊟ gadget (d+1)`.  `hcomp` is `whiskerRight` then `whiskerLeft`, so
`vcompAssoc` re-brackets and `gadgetSuccGen` folds `(t ◁ gadget d) ⊟ mu` to `gadget (d+1)`. -/
theorem gadgetAbsorb_formBGen (leftWidth rightWidth : Nat) :
    SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.hcomp (monadGadget leftWidth) (monadGadget rightWidth)) monadMulTwoCell)
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
          (monadGadget leftWidth))
        (monadGadget (rightWidth + 1))) := by
  show SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
            (monadGadget leftWidth))
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget rightWidth)))
        monadMulTwoCell)
      _
  refine SaturatedConvOver.trans
    (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
      (TwoCellStep.vcompAssoc
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
          (monadGadget leftWidth))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget rightWidth))
        monadMulTwoCell))) ?_
  exact SaturatedConvOver.vcompCongrRight
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
      (monadGadget leftWidth))
    (gadgetSuccGen rightWidth)

/-! ## The gadget right-merge: the FormB form absorbs to the `(c+d)`-fold gadget (induction on `c`) -/

/-- **The gadget right-merge.**  The FormB right-whisker form absorbs:
`(gadget c ▷ t^d) ⊟ gadget (d+1) ≈ cast (gadget (c+d))`.  Structural induction on `c`.  Base `c = 0` is
`gadgetAbsorb_zeroGen` (the LEFT-unit law).  Step: peel `gadget (c+1)` (`gadgetSuccGen`), distribute
(`whiskerRightVcomp`), fire the associativity CROSSING `gadgetMuCrossGen`, exchange the single-`t` left whisker past
the right whisker (`whiskerExchange` — the associator cast is defeq for a single-`t` whisker), re-merge the two
`t`-whiskers (`whiskerLeftVcomp`), thread the induction hypothesis under the `t`-whisker, extrude the boundary cast
(`whiskerLeft_castBoundary` / `vcomp_castBoundaryLeft`), and peel with `gadgetSuccGen`.  The genuine `monadTPower_add`
boundary cast threads through and reconciles by `Nat.succ_add` (`monadGadget_castEq`). -/
theorem gadgetRightMergeGen : ∀ (leftWidth rightWidth : Nat),
    SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
          (monadGadget leftWidth))
        (monadGadget (rightWidth + 1)))
      (RawTwoCellExpr.castBoundary (monadTPower_add leftWidth rightWidth) rfl
        (monadGadget (leftWidth + rightWidth)))
  | 0, rightWidth => by
      have key : SaturatedConvOver monadModeSignature MonadLawRel
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
              (monadGadget 0))
            (monadGadget (rightWidth + 1)))
          (monadGadget rightWidth) :=
        SaturatedConvOver.trans
          (SaturatedConvOver.symm (gadgetAbsorb_formBGen 0 rightWidth)) (gadgetAbsorb_zeroGen rightWidth)
      have hbridge : RawTwoCellExpr.castBoundary (monadTPower_add 0 rightWidth) rfl (monadGadget (0 + rightWidth))
          = monadGadget rightWidth := monadGadget_cast_ofEq (Nat.zero_add rightWidth)
      exact hbridge ▸ key
  | leftWidth + 1, rightWidth => by
      refine SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrLeft (monadGadget (rightWidth + 1))
          (SaturatedConvOver.whiskerRightCongr (monadTPower rightWidth)
            (SaturatedConvOver.symm (gadgetSuccGen leftWidth)))) ?_
      refine SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrLeft (monadGadget (rightWidth + 1))
          (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
            (TwoCellStep.whiskerRightVcomp (monadTPower rightWidth)
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget leftWidth))
              monadMulTwoCell)))) ?_
      refine SaturatedConvOver.trans
        (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
          (TwoCellStep.vcompAssoc
            (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget leftWidth)))
            (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth) monadMulTwoCell)
            (monadGadget (rightWidth + 1))))) ?_
      refine SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrRight
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget leftWidth)))
          (gadgetMuCrossGen rightWidth)) ?_
      refine SaturatedConvOver.trans
        (SaturatedConvOver.symm
          (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
            (TwoCellStep.vcompAssoc
              (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
                (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget leftWidth)))
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (rightWidth + 1)))
              monadMulTwoCell)))) ?_
      refine SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrLeft monadMulTwoCell
          (SaturatedConvOver.vcompCongrLeft
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (rightWidth + 1)))
            (SaturatedConvOver.symm
              (SaturatedConvOver.ofFull (baseRel := MonadLawRel)
                (TwoCellConvFull.whiskerExchange monadT (monadTPower rightWidth) (monadGadget leftWidth)))))) ?_
      refine SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrLeft monadMulTwoCell
          (SaturatedConvOver.symm
            (SaturatedConvOver.ofConv (baseRel := MonadLawRel) (TwoCellConv.ofStep
              (TwoCellStep.whiskerLeftVcomp monadT
                (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
                  (monadGadget leftWidth))
                (monadGadget (rightWidth + 1))))))) ?_
      refine SaturatedConvOver.trans
        (SaturatedConvOver.vcompCongrLeft monadMulTwoCell
          (SaturatedConvOver.whiskerLeftCongr monadT (gadgetRightMergeGen leftWidth rightWidth))) ?_
      have hpull :
          RawTwoCellExpr.vcomp
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
                (RawTwoCellExpr.castBoundary (monadTPower_add leftWidth rightWidth) rfl
                  (monadGadget (leftWidth + rightWidth))))
              monadMulTwoCell
            = RawTwoCellExpr.castBoundary
                (congrArg (composePath monadT) (monadTPower_add leftWidth rightWidth)) rfl
                (RawTwoCellExpr.vcomp
                  (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
                    (monadGadget (leftWidth + rightWidth)))
                  monadMulTwoCell) :=
        (congrArg (fun cell => RawTwoCellExpr.vcomp cell monadMulTwoCell)
          (monadWhiskerLeft_castBoundary (monadTPower_add leftWidth rightWidth) rfl
            (monadGadget (leftWidth + rightWidth)))).trans
          (RawTwoCellExpr.vcomp_castBoundaryLeft _ _ _ monadMulTwoCell)
      have convStep : SaturatedConvOver monadModeSignature MonadLawRel
          (RawTwoCellExpr.castBoundary
            (congrArg (composePath monadT) (monadTPower_add leftWidth rightWidth)) rfl
            (RawTwoCellExpr.vcomp
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
                (monadGadget (leftWidth + rightWidth)))
              monadMulTwoCell))
          (RawTwoCellExpr.castBoundary
            (congrArg (composePath monadT) (monadTPower_add leftWidth rightWidth)) rfl
            (monadGadget ((leftWidth + rightWidth) + 1))) :=
        SaturatedConvOver.castBoundaryCongr
          (congrArg (composePath monadT) (monadTPower_add leftWidth rightWidth)) rfl
          (gadgetSuccGen (leftWidth + rightWidth))
      have hEqR : RawTwoCellExpr.castBoundary
              (congrArg (composePath monadT) (monadTPower_add leftWidth rightWidth)) rfl
              (monadGadget ((leftWidth + rightWidth) + 1))
            = RawTwoCellExpr.castBoundary (monadTPower_add (leftWidth + 1) rightWidth) rfl
                (monadGadget ((leftWidth + 1) + rightWidth)) :=
        monadGadget_castEq ((leftWidth + rightWidth) + 1) ((leftWidth + 1) + rightWidth)
          (Nat.succ_add leftWidth rightWidth).symm
          (congrArg (composePath monadT) (monadTPower_add leftWidth rightWidth))
          (monadTPower_add (leftWidth + 1) rightWidth)
      exact hpull.symm ▸ (hEqR ▸ convStep)

/-- ★ **The gadget-absorb ASSOCIATIVITY amalgamation** (the r13-pinned residual, CLOSED zero-axiom).  Merging `c`
strands then `d` strands then multiplying equals merging `c + d` strands:
`(gadget c ⊠ gadget d) ⊟ mu ≈ cast (gadget (c + d))`.  `gadgetAbsorb_formBGen` (the cast-free reduction to a
right-whisker form) then `gadgetRightMergeGen` (the induction on `c` firing the associativity crossing).  The genuine
`monadTPower_add c d` boundary cast (the `t^c · t^d` vs `t^(c+d)` mismatch r13 named) is threaded and reconciled.
This is the mu-tree amalgamation `wordMul_vcompGen` folds over. -/
theorem gadgetAbsorbGen (leftWidth rightWidth : Nat) :
    SaturatedConvOver monadModeSignature MonadLawRel
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.hcomp (monadGadget leftWidth) (monadGadget rightWidth)) monadMulTwoCell)
      (RawTwoCellExpr.castBoundary (monadTPower_add leftWidth rightWidth) rfl
        (monadGadget (leftWidth + rightWidth))) :=
  SaturatedConvOver.trans (gadgetAbsorb_formBGen leftWidth rightWidth)
    (gadgetRightMergeGen leftWidth rightWidth)

/-- **ESTABLISHED — the gadget-absorb amalgamation (the three monad laws at the gadget level) is re-founded
GENERIC-NATIVE.**  `gadgetSuccGen` / `gadgetAbsorb_zeroGen` / `gadgetMuCrossGen` / `gadgetRightMergeGen` /
`gadgetAbsorbGen`, bespoke-free.  `= true`. -/
def fxMonad_hasGadgetAbsorbGen : Bool := true

end FX1Poly.Polygraph.Amalgam

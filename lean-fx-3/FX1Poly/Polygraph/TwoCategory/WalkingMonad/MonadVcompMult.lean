import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadHcompMult
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ChainGodementStep

/-! # WalkingMonad — VERTICAL word multiplicativity (the monad-law core toward `wordMul_vcomp`)

The sole open `normalizeCell` case is `vcomp`, which reduces to `wordMul_vcomp : vcomp (word ccL) (word ccR) ≈
word (composeCounts ccL ccR)`.  This is the ONLY residual using the monad LAWS.  Its heart is the mu-tree
amalgamation `gadgetAbsorb`: merging `c` strands then `d` strands then the two results equals merging `c + d`
strands — the ASSOCIATIVITY of the merge, plus the UNIT cancellation at the empty gadget (`eta`).

## What this file ships (each piece zero-axiom)

  * **`gadgetSucc`** — the uniform mu-tree peel `(t ◁ gadget d) ⊟ mu ≈ gadget (d + 1)`: definitional for `d ≥ 1`,
    the RIGHT-unit monad law at `d = 0`.
  * ★ **`godementExchange`** — the two-cell Godement EXCHANGE `α ⊠ β ≈ (α_dom ◁ β) ⊟ (β_cod ▷ α)`, derived from
    the `interchange` step by inserting/cancelling identities.  Cast-free (both Godement orders share the
    boundary).

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; STRUCTURAL recursion.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## Godement-product congruences (signature-generic) -/

/-- Congruence in the LEFT factor of a horizontal composite. -/
theorem TwoCellConvFull.hcompCongrLeft {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellFDom oneCellFCod : ModalityPath signature.graph sourceMode middleMode}
    {oneCellGDom oneCellGCod : ModalityPath signature.graph middleMode targetMode}
    {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellFDom oneCellFCod}
    (cellBeta : RawTwoCellExpr signature oneCellGDom oneCellGCod)
    (conv : TwoCellConvFull signature cellAlpha cellAlpha') :
    TwoCellConvFull signature (RawTwoCellExpr.hcomp cellAlpha cellBeta)
      (RawTwoCellExpr.hcomp cellAlpha' cellBeta) :=
  TwoCellConvFull.vcompCongrLeft _ (TwoCellConvFull.whiskerRightCongr oneCellGDom conv)

/-- Congruence in the RIGHT factor of a horizontal composite. -/
theorem TwoCellConvFull.hcompCongrRight {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellFDom oneCellFCod : ModalityPath signature.graph sourceMode middleMode}
    {oneCellGDom oneCellGCod : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellFDom oneCellFCod)
    {cellBeta cellBeta' : RawTwoCellExpr signature oneCellGDom oneCellGCod}
    (conv : TwoCellConvFull signature cellBeta cellBeta') :
    TwoCellConvFull signature (RawTwoCellExpr.hcomp cellAlpha cellBeta)
      (RawTwoCellExpr.hcomp cellAlpha cellBeta') :=
  TwoCellConvFull.vcompCongrRight _ (TwoCellConvFull.whiskerLeftCongr oneCellFCod conv)

/-! ## The two-cell Godement exchange -/

/-- ★ **The two-cell Godement EXCHANGE.**  The horizontal composite `α ⊠ β` (computed as `whiskerRight` then
`whiskerLeft`, the def) equals the OTHER order around the naturality square, `(α_dom ◁ β) ⊟ (β_cod ▷ α)`.  Cast-free
(both orders share the boundary `composePath α_dom β_dom ⇒ composePath α_cod β_cod`).  Derived from the `interchange`
step: insert identities (`α = id ⊟ α`, `β = β ⊟ id`), fire interchange, and collapse the four identity whiskerings
(`whiskerRightId` / `whiskerLeftId` / `vcompIdLeft` / `vcompIdRight`).  Pure free-2-category — no monad law. -/
theorem godementExchange {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellADom oneCellACod : ModalityPath signature.graph sourceMode middleMode}
    {oneCellBDom oneCellBCod : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellADom oneCellACod)
    (cellBeta : RawTwoCellExpr signature oneCellBDom oneCellBCod) :
    TwoCellConvFull signature
      (RawTwoCellExpr.hcomp cellAlpha cellBeta)
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft oneCellADom cellBeta)
        (RawTwoCellExpr.whiskerRight oneCellBCod cellAlpha)) := by
  -- Insert identities: hcomp α β ≈ hcomp (id ⊟ α) (β ⊟ id).
  refine TwoCellConvFull.trans
    (TwoCellConvFull.hcompCongrLeft cellBeta
      (TwoCellConvFull.symm (TwoCellConvFull.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompIdLeft cellAlpha))))) ?_
  refine TwoCellConvFull.trans
    (TwoCellConvFull.hcompCongrRight
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.id oneCellADom) cellAlpha)
      (TwoCellConvFull.symm (TwoCellConvFull.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompIdRight cellBeta))))) ?_
  -- Interchange: hcomp (id ⊟ α)(β ⊟ id) → vcomp (hcomp id β)(hcomp α id).
  refine TwoCellConvFull.trans
    (TwoCellConvFull.ofConv (TwoCellConv.ofStep
      (TwoCellStep.interchange (RawTwoCellExpr.id oneCellADom) cellAlpha cellBeta
        (RawTwoCellExpr.id oneCellBCod)))) ?_
  -- Collapse the LEFT factor: hcomp (id α_dom) β = vcomp (whiskerRight β_dom (id α_dom)) (whiskerLeft α_dom β)
  --   ≈ whiskerLeft α_dom β.
  refine TwoCellConvFull.trans
    (TwoCellConvFull.vcompCongrLeft _
      (TwoCellConvFull.trans
        (TwoCellConvFull.vcompCongrLeft _
          (TwoCellConvFull.ofConv (TwoCellConv.ofStep
            (TwoCellStep.whiskerRightId oneCellADom oneCellBDom))))
        (TwoCellConvFull.ofConv (TwoCellConv.ofStep
          (TwoCellStep.vcompIdLeft (RawTwoCellExpr.whiskerLeft oneCellADom cellBeta)))))) ?_
  -- Collapse the RIGHT factor: hcomp α (id β_cod) = vcomp (whiskerRight β_cod α)(whiskerLeft α_cod (id β_cod))
  --   ≈ whiskerRight β_cod α.
  exact TwoCellConvFull.vcompCongrRight _
    (TwoCellConvFull.trans
      (TwoCellConvFull.vcompCongrRight _
        (TwoCellConvFull.ofConv (TwoCellConv.ofStep
          (TwoCellStep.whiskerLeftId oneCellACod oneCellBCod))))
      (TwoCellConvFull.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompIdRight (RawTwoCellExpr.whiskerRight oneCellBCod cellAlpha)))))

/-! ## The uniform mu-tree peel -/

/-- ★ **The uniform mu-tree peel.**  `(t ◁ gadget d) ⊟ mu ≈ gadget (d + 1)` for EVERY `d`: definitional for
`d ≥ 1` (that IS the `count + 2` gadget clause), and the RIGHT-unit monad law `mu ∘ (t ◁ eta) ≈ id_t` at `d = 0`
(`gadget 0 = eta`, `gadget 1 = id_t`).  This makes `gadget` peel uniformly at the convertibility level despite its
`0` / `1` / `n+2` definitional branching. -/
theorem gadgetSucc : ∀ (d : Nat),
    MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget d))
        monadMulTwoCell)
      (monadGadget (d + 1))
  | 0 => MonadSaturatedTwoCellConv.rightUnit
  | _ + 1 => MonadSaturatedTwoCellConv.refl _

/-! ## The gadget-absorb BASE case: the empty gadget cancels via the LEFT-unit law -/

/-- ★ **The `eta`-gadget absorbs (the monad LEFT-unit law at arbitrary merge width).**  Merging a freshly-inserted
unit strand (`gadget 0 = eta`) with a `d`-fold merge and then multiplying is the `d`-fold merge itself:
`(eta ⊠ gadget d) ⊟ mu ≈ gadget d`.  Cast-free — `t^0 · t^d = t^d` definitionally.  Proof: the Godement EXCHANGE
reorders `eta ⊠ gadget d` to `(t^0 ◁ gadget d) ⊟ (t ▷ eta)`, the unit-1-cell left whisker strips (`whiskerLeftUnit`),
reassociation brings `eta ▷ t` adjacent to `mu`, and the LEFT-unit monad law `mu ∘ (eta ▷ t) ≈ id_t` fires
(`vcompIdRight` clears the residual identity).  This is one of the two monad-law adjacencies the residual needs. -/
theorem gadgetAbsorb_zero (d : Nat) :
    MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.hcomp (monadGadget 0) (monadGadget d)) monadMulTwoCell)
      (monadGadget d) := by
  -- Reorder the Godement product: hcomp eta (gadget d) ≈ vcomp (gadget d) (t ▷ eta).
  have hExchange : MonadSaturatedTwoCellConv
      (RawTwoCellExpr.hcomp (monadGadget 0) (monadGadget d))
      (RawTwoCellExpr.vcomp (monadGadget d)
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)) := by
    refine MonadSaturatedTwoCellConv.trans
      (MonadSaturatedTwoCellConv.ofFull (godementExchange monadUnitTwoCell (monadGadget d))) ?_
    exact MonadSaturatedTwoCellConv.vcompCongrLeft _
      (MonadSaturatedTwoCellConv.ofFull (TwoCellConvFull.whiskerLeftUnit (monadGadget d)))
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell hExchange) ?_
  -- Reassociate so (eta ▷ t) ⊟ mu = monadLeftUnitCell is adjacent.
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
      (TwoCellStep.vcompAssoc (monadGadget d)
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
        monadMulTwoCell))) ?_
  -- Fire the LEFT-unit law: (eta ▷ t) ⊟ mu ≈ id_t.
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.vcompCongrRight (monadGadget d) MonadSaturatedTwoCellConv.leftUnit) ?_
  -- Clear the residual identity.
  exact MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
    (TwoCellStep.vcompIdRight (monadGadget d)))

/-! ## The two Godement whiskering orders of `hcomp mu (gadget d)` -/

/-- The **Godement bridge**: the two whiskering orders of `hcomp mu (gadget d)` are saturated-convertible —
`(t ◁ t ◁ gadget d) ⊟ (mu ▷ t) ≈ (mu ▷ t^d) ⊟ (t ◁ gadget d)`.  The shipped cast-free `hcompOrder_twoCellConv`
gives `(mu ▷ t^d) ⊟ (t ◁ gadget d) ≈ (t·t ◁ gadget d) ⊟ (mu ▷ t)`; the leading double-`t` left whisker equals the
`t·t` whisker (`whiskerLeftComp`), whose associator cast is definitionally the identity because the whisker is a
concrete `t`-power (`composePath monadT monadT` flattens to `monadTThenT`).  No boundary cast survives. -/
theorem godementMuGadget (mergeWidth : Nat) :
    MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth)))
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadMulTwoCell))
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower mergeWidth) monadMulTwoCell)
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth))) := by
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.vcompCongrLeft
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadMulTwoCell)
      (MonadSaturatedTwoCellConv.symm
        (MonadSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerLeftComp monadT monadT (monadGadget mergeWidth))))) ?_
  exact MonadSaturatedTwoCellConv.symm
    (MonadSaturatedTwoCellConv.ofConv (hcompOrder_twoCellConv monadMulTwoCell (monadGadget mergeWidth)))

/-! ## The ASSOCIATIVITY crossing: a `mu` at the front absorbs into the `(d+1)`-fold merge -/

/-- ★ **The associativity CROSSING** (the exact residual pinned by r13, closed).  Multiplying the first two strands
(`mu ▷ t^d`) then merging the resulting `d+1` strands equals the `(d+2)`-fold merge:
`(mu ▷ t^d) ⊟ gadget (d+1) ≈ gadget (d+2)`.  Cast-free — all boundaries are concrete `t`-powers.  Both sides
reduce to `(mu ▷ t^d) ⊟ (t ◁ gadget d) ⊟ mu = (hcomp mu (gadget d)) ⊟ mu`: the LHS by peeling `gadget (d+1)` with
`gadgetSucc` and reassociating; the RHS `gadget (d+2)` by unfolding the top `mu`-tree clause, distributing the
left whisker (`whiskerLeftVcomp`), firing the monad ASSOCIATIVITY law `(t ◁ mu) ⊟ mu ≈ (mu ▷ t) ⊟ mu`, and
reconciling the two Godement orders (`godementMuGadget`).  This is the SOLE step of `gadgetAbsorb` using the
associativity law. -/
theorem gadgetMuCross (mergeWidth : Nat) :
    MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower mergeWidth) monadMulTwoCell)
        (monadGadget (mergeWidth + 1)))
      (monadGadget (mergeWidth + 2)) := by
  have hCommon : MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower mergeWidth) monadMulTwoCell)
        (monadGadget (mergeWidth + 1)))
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower mergeWidth) monadMulTwoCell)
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth)))
        monadMulTwoCell) := by
    refine MonadSaturatedTwoCellConv.trans
      (MonadSaturatedTwoCellConv.vcompCongrRight
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower mergeWidth) monadMulTwoCell)
        (MonadSaturatedTwoCellConv.symm (gadgetSucc mergeWidth))) ?_
    exact MonadSaturatedTwoCellConv.symm
      (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompAssoc
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower mergeWidth) monadMulTwoCell)
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth))
          monadMulTwoCell)))
  refine MonadSaturatedTwoCellConv.trans hCommon (MonadSaturatedTwoCellConv.symm ?_)
  show MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (mergeWidth + 1)))
        monadMulTwoCell)
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower mergeWidth) monadMulTwoCell)
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth)))
        monadMulTwoCell)
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell
      (MonadSaturatedTwoCellConv.whiskerLeftCongr monadT
        (MonadSaturatedTwoCellConv.symm (gadgetSucc mergeWidth)))) ?_
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell
      (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
        (TwoCellStep.whiskerLeftVcomp monadT
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth))
          monadMulTwoCell)))) ?_
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
      (TwoCellStep.vcompAssoc
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth)))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadMulTwoCell)
        monadMulTwoCell))) ?_
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.vcompCongrRight
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth)))
      (MonadSaturatedTwoCellConv.symm MonadSaturatedTwoCellConv.assoc)) ?_
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.symm
      (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
        (TwoCellStep.vcompAssoc
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget mergeWidth)))
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadMulTwoCell)
          monadMulTwoCell)))) ?_
  exact MonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell (godementMuGadget mergeWidth)

/-! ## Boundary-cast reconciliation helpers on gadgets (propext-free `cases` on the width equalities) -/

/-- Casting a gadget along a `congrArg monadTPower` width equality is the gadget at the new width. -/
theorem monadGadget_cast_ofEq {leftWidth rightWidth : Nat} (hwidth : leftWidth = rightWidth) :
    RawTwoCellExpr.castBoundary (congrArg monadTPower hwidth) rfl (monadGadget leftWidth)
      = monadGadget rightWidth := by
  cases hwidth; rfl

/-- Two casts of Nat-equal-width gadgets to the SAME parallel boundary coincide (proof-irrelevance of the two
boundary casts to a common target). -/
theorem monadGadget_castEq (leftWidth rightWidth : Nat) (hwidth : leftWidth = rightWidth)
    {targetPath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hLeft : monadTPower leftWidth = targetPath) (hRight : monadTPower rightWidth = targetPath) :
    RawTwoCellExpr.castBoundary hLeft rfl (monadGadget leftWidth)
      = RawTwoCellExpr.castBoundary hRight rfl (monadGadget rightWidth) := by
  cases hwidth; rfl

/-! ## FormB: the cast-free, monad-law-free reduction of the absorb LHS -/

/-- **FormB** — the absorb LHS reduces to a right-whisker form, cast-free and monad-law-free:
`(gadget c ⊠ gadget d) ⊟ mu ≈ (gadget c ▷ t^d) ⊟ gadget (d+1)`.  `hcomp` is `whiskerRight` then `whiskerLeft`, so
`vcompAssoc` re-brackets and `gadgetSucc` folds `(t ◁ gadget d) ⊟ mu` to `gadget (d+1)`. -/
theorem gadgetAbsorb_formB (leftWidth rightWidth : Nat) :
    MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.hcomp (monadGadget leftWidth) (monadGadget rightWidth)) monadMulTwoCell)
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
          (monadGadget leftWidth))
        (monadGadget (rightWidth + 1))) := by
  show MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.vcomp
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
            (monadGadget leftWidth))
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget rightWidth)))
        monadMulTwoCell)
      _
  refine MonadSaturatedTwoCellConv.trans
    (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
      (TwoCellStep.vcompAssoc
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
          (monadGadget leftWidth))
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget rightWidth))
        monadMulTwoCell))) ?_
  exact MonadSaturatedTwoCellConv.vcompCongrRight
    (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
      (monadGadget leftWidth))
    (gadgetSucc rightWidth)

/-! ## The gadget right-merge: the FormB form absorbs to the `(c+d)`-fold gadget (induction on `c`) -/

/-- **The gadget right-merge.**  The FormB right-whisker form absorbs:
`(gadget c ▷ t^d) ⊟ gadget (d+1) ≈ cast (gadget (c+d))`.  Structural induction on `c`.  Base `c = 0` is
`gadgetAbsorb_zero` (the LEFT-unit law).  Step: peel `gadget (c+1)` (`gadgetSucc`), distribute
(`whiskerRightVcomp`), fire the associativity CROSSING `gadgetMuCross`, exchange the single-`t` left whisker past
the right whisker (`whiskerExchange` — the associator cast is defeq for a single-`t` whisker), re-merge the two
`t`-whiskers (`whiskerLeftVcomp`), thread the induction hypothesis under the `t`-whisker, extrude the boundary cast
(`whiskerLeft_castBoundary` / `vcomp_castBoundaryLeft`), and peel with `gadgetSucc`.  The genuine `monadTPower_add`
boundary cast threads through and reconciles by `Nat.succ_add` (`monadGadget_castEq`). -/
theorem gadgetRightMerge : ∀ (leftWidth rightWidth : Nat),
    MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
          (monadGadget leftWidth))
        (monadGadget (rightWidth + 1)))
      (RawTwoCellExpr.castBoundary (monadTPower_add leftWidth rightWidth) rfl
        (monadGadget (leftWidth + rightWidth)))
  | 0, rightWidth => by
      have key : MonadSaturatedTwoCellConv
          (RawTwoCellExpr.vcomp
            (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
              (monadGadget 0))
            (monadGadget (rightWidth + 1)))
          (monadGadget rightWidth) :=
        MonadSaturatedTwoCellConv.trans
          (MonadSaturatedTwoCellConv.symm (gadgetAbsorb_formB 0 rightWidth)) (gadgetAbsorb_zero rightWidth)
      have hbridge : RawTwoCellExpr.castBoundary (monadTPower_add 0 rightWidth) rfl (monadGadget (0 + rightWidth))
          = monadGadget rightWidth := monadGadget_cast_ofEq (Nat.zero_add rightWidth)
      exact hbridge ▸ key
  | leftWidth + 1, rightWidth => by
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.vcompCongrLeft (monadGadget (rightWidth + 1))
          (MonadSaturatedTwoCellConv.whiskerRightCongr (monadTPower rightWidth)
            (MonadSaturatedTwoCellConv.symm (gadgetSucc leftWidth)))) ?_
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.vcompCongrLeft (monadGadget (rightWidth + 1))
          (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
            (TwoCellStep.whiskerRightVcomp (monadTPower rightWidth)
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget leftWidth))
              monadMulTwoCell)))) ?_
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
          (TwoCellStep.vcompAssoc
            (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget leftWidth)))
            (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth) monadMulTwoCell)
            (monadGadget (rightWidth + 1))))) ?_
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.vcompCongrRight
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget leftWidth)))
          (gadgetMuCross rightWidth)) ?_
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.symm
          (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
            (TwoCellStep.vcompAssoc
              (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
                (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget leftWidth)))
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (rightWidth + 1)))
              monadMulTwoCell)))) ?_
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell
          (MonadSaturatedTwoCellConv.vcompCongrLeft
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT (monadGadget (rightWidth + 1)))
            (MonadSaturatedTwoCellConv.symm
              (MonadSaturatedTwoCellConv.ofFull
                (TwoCellConvFull.whiskerExchange monadT (monadTPower rightWidth) (monadGadget leftWidth)))))) ?_
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell
          (MonadSaturatedTwoCellConv.symm
            (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep
              (TwoCellStep.whiskerLeftVcomp monadT
                (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) (monadTPower rightWidth)
                  (monadGadget leftWidth))
                (monadGadget (rightWidth + 1))))))) ?_
      refine MonadSaturatedTwoCellConv.trans
        (MonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell
          (MonadSaturatedTwoCellConv.whiskerLeftCongr monadT (gadgetRightMerge leftWidth rightWidth))) ?_
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
      have convStep : MonadSaturatedTwoCellConv
          (RawTwoCellExpr.castBoundary
            (congrArg (composePath monadT) (monadTPower_add leftWidth rightWidth)) rfl
            (RawTwoCellExpr.vcomp
              (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT
                (monadGadget (leftWidth + rightWidth)))
              monadMulTwoCell))
          (RawTwoCellExpr.castBoundary
            (congrArg (composePath monadT) (monadTPower_add leftWidth rightWidth)) rfl
            (monadGadget ((leftWidth + rightWidth) + 1))) :=
        MonadSaturatedTwoCellConv.castBoundaryCongr
          (congrArg (composePath monadT) (monadTPower_add leftWidth rightWidth)) rfl
          (gadgetSucc (leftWidth + rightWidth))
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
`(gadget c ⊠ gadget d) ⊟ mu ≈ cast (gadget (c + d))`.  `gadgetAbsorb_formB` (the cast-free reduction to a
right-whisker form) then `gadgetRightMerge` (the induction on `c` firing the associativity crossing).  The genuine
`monadTPower_add c d` boundary cast (the `t^c · t^d` vs `t^(c+d)` mismatch r13 named) is threaded and reconciled.
This is the mu-tree amalgamation `wordMul_vcomp` folds over. -/
theorem gadgetAbsorb (leftWidth rightWidth : Nat) :
    MonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp
        (RawTwoCellExpr.hcomp (monadGadget leftWidth) (monadGadget rightWidth)) monadMulTwoCell)
      (RawTwoCellExpr.castBoundary (monadTPower_add leftWidth rightWidth) rfl
        (monadGadget (leftWidth + rightWidth))) :=
  MonadSaturatedTwoCellConv.trans (gadgetAbsorb_formB leftWidth rightWidth)
    (gadgetRightMerge leftWidth rightWidth)

/-! ## Honesty markers -/

/-- **ESTABLISHED — the free-strict-2-category foundation + the two monad UNIT-law adjacencies of the vcomp word
multiplicativity are CLOSED, zero-axiom.**  Toward the SOLE open `normalizeCell` case `vcomp` (`wordMul_vcomp`),
this lane has now landed:

  * the horizontal-composite ASSOCIATIVITY `hcompAssoc` (`α ⊠ (β ⊠ γ) ≈ (α ⊠ β) ⊠ γ`, the free-2-category law the
    lane never built) and the HORIZONTAL word multiplicativity `wordMul_hcomp` (`word (a ++ b) ≈ word a ⊠ word b`)
    — the structural infrastructure needed to SPLIT the left word in the `vcomp` step (`WalkingMonad/MonadHcompMult`);
  * the two-cell Godement EXCHANGE `godementExchange` (`α ⊠ β ≈ (α_dom ◁ β) ⊟ (β_cod ▷ α)`, derived from
    `interchange`);
  * the uniform mu-tree LEFT peel `gadgetSucc` (`(t ◁ gadget d) ⊟ mu ≈ gadget (d+1)`, the RIGHT-unit law at `d=0`);
  * ★ the gadget-absorb BASE `gadgetAbsorb_zero` (`(eta ⊠ gadget d) ⊟ mu ≈ gadget d`) — the machine-checked firing
    of the LEFT-unit monad law at ARBITRARY merge width, assembled from `godementExchange` + `whiskerLeftUnit` +
    the LEFT-unit law + `vcompIdRight`.

Both unit-law adjacencies now fire in machine-checked sub-lemmas (`gadgetSucc` = right unit, `gadgetAbsorb_zero` =
left unit), confirming the r12 scratch-probe finding that NEITHER unit adjacency walls.  `= true`. -/
def fxMonad_hasVcompUnitAdjacencies : Bool := true

/-- **ESTABLISHED — the ASSOCIATIVITY-law amalgamation `gadgetAbsorb` is CLOSED, zero-axiom** (the r13-pinned
residual, cleared).  Merging `c` strands then `d` strands then multiplying equals merging `c + d` strands:
`gadgetAbsorb (c d) : (gadget c ⊠ gadget d) ⊟ mu ≈ cast (gadget (c + d))`.

The r13-pinned obstacle — the step carries a GENUINE `monadTPower_add c d` boundary cast (`t^c · t^d` vs
`t^(c+d)`, non-defeq for variable `c` because `composePath` recurses on the opaque first argument) — is dissolved
by the following route, all machine-checked:

  * **`gadgetAbsorb_formB`** — the cast-free reduction `(gadget c ⊠ gadget d) ⊟ mu ≈ (gadget c ▷ t^d) ⊟ gadget
    (d+1)` (hcomp-def + `vcompAssoc` + `gadgetSucc`), no monad law;
  * ★ **`gadgetMuCross`** — the associativity CROSSING `(mu ▷ t^d) ⊟ gadget (d+1) ≈ gadget (d+2)`, proved NON-
    inductively and CAST-FREE: both sides reduce to `hcomp mu (gadget d) ⊟ mu`, the RHS firing the monad
    associativity law `(t ◁ mu) ⊟ mu ≈ (mu ▷ t) ⊟ mu` and reconciling the two Godement orders (`godementMuGadget`
    via the shipped `hcompOrder_twoCellConv`).  This is the SOLE associativity-law use, and it is concrete-width
    so no `monadTPower_add` cast appears;
  * **`gadgetRightMerge`** — the induction on `c`; the single-`t` left whisker makes the `whiskerExchange`
    associator casts DEFEQ, so only the `monadTPower_add` domain cast survives, threading through
    `whiskerLeft_castBoundary` / `vcomp_castBoundaryLeft` and reconciling by `Nat.succ_add` (`monadGadget_castEq`).

Both unit adjacencies (`gadgetSucc` = right unit, `gadgetAbsorb_zero` = left unit) AND the associativity crossing
now fire in machine-checked sub-lemmas — the three monad laws fully realized at the gadget level.  `= true`.

The DOWNSTREAM chain toward the completeness flip is NOT yet landed: folding `gadgetAbsorb` over the two words
(`wordMul_vcomp` — `vcomp (word ccL) (word ccR) ≈ cast (word (composeCounts ccL ccR))`, needing a `composeCounts`
regroup, the `wordMul_hcomp` word split at `take/drop ccL`, the interchange assembly, and the data-level
`countsOf ∘ composeMap = composeCounts ∘ countsOf` bridge), the `vcomp` `normalizeCell` case, and the assembled
`normalize : MonadNormalizesToCanon`.  So `fxMonad_hasWordMulVcomp` / `fxMonad_hasConvOfMapEqNormalization` /
`fxMonad_hasMonotoneMapDecisionAssembled` / `fxMonad_hasFullMapEqOfConvAndCompleteness` stay `false`. -/
def fxMonad_hasVcompAssocAmalgamation : Bool := true

end FX1Poly.Polygraph

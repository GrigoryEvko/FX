import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadHcompMult

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

/-- **Honesty marker — the ASSOCIATIVITY-law amalgamation `gadgetAbsorb` (inductive step) is the exact stuck goal;
`wordMul_vcomp` and the three completeness flags stay `false`.**  The `vcomp` `normalizeCell` case reduces to
`wordMul_vcomp : vcomp (word ccL) (word ccR) ≈ word (composeCounts ccL ccR)`, whose crux is the mu-tree
amalgamation `gadgetAbsorb (c d) : (gadget c ⊠ gadget d) ⊟ mu ≈ gadget (c + d)`.  Its BASE `c = 0`
(`gadgetAbsorb_zero`, the LEFT-unit law) is CLOSED; its inductive STEP `c → c + 1` is the ASSOCIATIVITY-law
amalgamation and is NOT landed.

The EXACT obstacle, found this round: the step needs the RIGHT-leaning mu-tree peel `(gadget c ▷ t) ⊟ mu ≈
gadget (c+1)` (a RIGHT whisker), but on the walking monad `composePath (monadTPower c) monadT` (= `t^c · t`, the
domain a RIGHT whisker by `t` produces) is NOT definitionally equal to `monadTPower (c+1)` (= `t · t^c`, LEFT-nested)
for a VARIABLE `c` — `composePath` recurses on its first argument, which is the opaque `monadTPower c`.  So the
right-whisker peel and the associativity-law step carry a GENUINE `monadTPower_add c 1` boundary cast (non-defeq,
unlike the LEFT-whisker peel `gadgetSucc` and the concrete-`t` associator casts, which ARE defeq).  Threading that
cast through the associativity-law step + the downstream `gadgetMerge` fold + `composeCounts` + `canonCounts_vcomp`
+ `wordMul_vcomp` + `monadNormalize_vcomp` is the residual.  Until `gadgetAbsorb` lands, `wordMul_vcomp` is not
inhabited, so `normalize : MonadNormalizesToCanon` is not 6/6, `MonadSaturatedCanonicalization.convOfMapEq` is not
inhabited, and `fxMonad_hasMonotoneMapDecisionAssembled` / `fxMonad_hasConvOfMapEqNormalization` /
`fxMonad_hasFullMapEqOfConvAndCompleteness` stay `false`.  `= false`. -/
def fxMonad_hasVcompAssocAmalgamation : Bool := false

end FX1Poly.Polygraph

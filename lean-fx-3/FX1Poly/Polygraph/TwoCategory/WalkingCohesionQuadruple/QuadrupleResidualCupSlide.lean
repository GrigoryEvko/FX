import FX1Poly.Polygraph.TwoCategory.WalkingCohesionQuadruple.QuadrupleMateBijectionKit

/-! # WalkingCohesionQuadruple/QuadrupleResidualCupSlide — the residual-cup whisker slide DERIVED

Wave-4 of the quadruple thinness residual: the LAST open coherence the mate-bijection kit named — the
**residual-cup whisker slide** `w ◁ u ≈ u ▷ w` (`quadResidualCupLeftInsertionCell` vs
`quadResidualCupRightInsertionCell`, the well-pointedness of the pointed endo-1-cell `(w, u)` with
`w = codisc·pi0` and `u = quadResidualCupCell`) — is a THEOREM of the saturated congruence
(`quadResidualCupWhiskerSlide`).  The wave-3 wall flag `fxQuadCohesion_hasResidualCupWhiskerSlide` flips `true`.

## Why this is not free (the content)

For a FREE pointed endo-1-cell `(w, u : id ⇒ w)` the slide FAILS: the free monoidal category on a pointed
object is (equivalent to) finite ordinals and monotone INJECTIONS, where `w ◁ u` and `u ▷ w` are the two
DISTINCT coface maps `[1] ⇉ [2]` (Kelly, *A unified treatment of transfinite constructions*, calls `wu = uw`
WELL-POINTEDNESS and treats it as genuinely extra structure).  Here `(w, u)` is NOT free: `u` is built from
the quadruple's units/counits and ff inverses, and the twelve saturation rows FORCE the slide — exactly the
coherence every concrete cohesive model satisfies, now exhibited in the free quadruple itself.

## The mechanism (the σ-mediation)

Neither insertion converts into the other directly; BOTH convert into the **residual comultiplication**

  `σ = (codisc ◁ k) ▷ pi0 : w ⇒ w·w`,   `k : id_space ⇒ pi0·codisc` the SPACE-side residual cup,

and the slide is `trans` through `σ`.  Three ingredients, all reductions to SHIPPED joins:

  * ★ `quadCodiscUnitUpperWhiskerSolvesToInvCounit` — `codisc ◁ η'' ≈ ε''⁻¹ ▷ codisc`: the `triCodisc`
    snake SOLVED for its whiskered unit against the invertible upper counit (insert the `isoUpperCounitRight`
    round-trip, regroup, fire the triangle).  This is the exact rewrite `ζ∇ = ∇θ⁻¹` that turns the RIGHT
    insertion's `codisc`-whiskered `ε''⁻¹` into the `codisc`-component of the upper unit.
  * ★ `quadPi0UnitLowerWhiskerSolvesToInvCounit` — `η ▷ pi0 ≈ pi0 ◁ ε⁻¹`: the `triPi0` snake solved the
    same way against `isoLowerCounitRight` (`Πα = β⁻¹Π`), turning the LEFT insertion's `pi0`-whiskered
    `ε⁻¹` into the `pi0`-component of the lower unit.
  * ★ `quadSpaceResidualCupJoin` — the SPACE-side twin of the shipped `quadResidualCupJoin`: the two derived
    cups `id_space ⇒ pi0·codisc` (upper route `η'' ⊟ (ptp ▷ codisc)` vs the shipped `quadCrossCupCell`
    `η ⊟ (pi0 ◁ dtc)`) are convertible.  Proof: swap `ptp` to its unit form (`quadPointsToPiecesJoin`),
    then the two whisker-nested unit cups slide past each other by GODEMENT naturality
    (`quadLowerUnitSlidesPastUpperUnit`, an instance of the shipped exchange square with the unit whiskers
    cleaned by `whiskerLeftUnit`/`whiskerRightUnit`/`whiskerLeftComp`/`whiskerRightComp`), and the middle-unit
    inverses exchange across the disjoint whiskers (`whiskerExchange`).

Then `u ▷ w ≈ σ` (RIGHT mediation: split the composite whisker, distribute, fire solver 1, exchange, refold —
uses `u`'s UPPER form) and `w ◁ u ≈ σ` (LEFT mediation: swap `u` to its LOWER form by the shipped
`quadResidualCupJoin`, split, fire solver 2, swap `dtc` to its upper form by `quadDiscreteToCodiscreteJoin`,
exchange twice, refold through `quadCrossCupCell`, close with `quadSpaceResidualCupJoin`).

## What this does and does not flip

`fxQuadCohesion_hasResidualCupWhiskerSlide` flips `true` (the wave-3 crux is DERIVED, not walled).  The master
flags `fxQuadCohesion_hasQuadrupleThinnessResolution` and `fxQuadCohesion_hasFreeWordNormalizerForThinness`
stay HONESTLY `false`: the slide unblocks the residual family's coherence (every insertion order of the
canonical point into a `w`-power now joins), but the NORMALIZER — the per-word canonical 2-cell with its
completeness induction over arbitrary parallel pairs — remains the named multi-file arc.

Raw Lean 4 + Init; every proof is a constructor chain over the shipped saturation, the free 3-cells, and the
completed whisker functoriality (casts collapse definitionally on the concrete-letter boundaries) — every
declaration is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`/`decide`/`simp`-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The two triangle-inverse solvers

Each adjoint triangle `(unit whisker) ⊟ (counit whisker) ≈ id` whose counit is INVERTIBLE can be solved for
the unit whisker: insert the ff-iso round-trip on the right, regroup so the snake fires, and the whiskered
unit equals the whiskered counit INVERSE.  These are the two rewrites that let the residual-cup insertions
absorb their whiskering path into the cup's own unit. -/

/-- ★ **The `codisc`-leg solver**: `codisc ◁ η'' ≈ ε''⁻¹ ▷ codisc : codisc ⇒ codisc·gamma·codisc` — the
`triCodisc` snake solved for its whiskered upper unit against the invertible upper counit
(`isoUpperCounitRight`).  Classically `ζ_{∇X} = ∇(θ⁻¹_X)`. -/
theorem quadCodiscUnitUpperWhiskerSolvesToInvCounit :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc quadUnitUpperCell)
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadInvCounitUpperCell) := by
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm (quadVcompIdRightDrops
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc quadUnitUpperCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.symm
        (quadWhiskerRightIdCollapses quadCodiscGamma quadCodisc))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadCodisc
        (QuadCohesionSaturatedTwoCellConv.symm
          QuadCohesionSaturatedTwoCellConv.isoUpperCounitRight))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (quadCohesionConvOfStep (TwoCellStep.whiskerRightVcomp (signature := quadCohesionModeSignature) quadCodisc
        quadCounitUpperCell quadInvCounitUpperCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadVcompAssocShifts
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc quadUnitUpperCell)
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadCounitUpperCell)
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadInvCounitUpperCell))) ?_
  exact quadCohesionLoopContractsOnLeft QuadCohesionSaturatedTwoCellConv.triCodisc
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadInvCounitUpperCell)

/-- ★ **The `pi0`-leg solver**: `η ▷ pi0 ≈ pi0 ◁ ε⁻¹ : pi0 ⇒ pi0·disc·pi0` — the `triPi0` snake solved for
its whiskered lower unit against the invertible lower counit (`isoLowerCounitRight`).  Classically
`Π(α_X) = β⁻¹_{ΠX}`. -/
theorem quadPi0UnitLowerWhiskerSolvesToInvCounit :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0 quadUnitLowerCell)
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 quadInvCounitLowerCell) := by
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm (quadVcompIdRightDrops
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0 quadUnitLowerCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.symm
        (quadCohesionConvOfStep
          (TwoCellStep.whiskerLeftId (signature := quadCohesionModeSignature) quadPi0 quadDiscPi0)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadPi0
        (QuadCohesionSaturatedTwoCellConv.symm
          QuadCohesionSaturatedTwoCellConv.isoLowerCounitRight))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (quadCohesionConvOfStep (TwoCellStep.whiskerLeftVcomp (signature := quadCohesionModeSignature) quadPi0
        quadCounitLowerCell quadInvCounitLowerCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadVcompAssocShifts
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0 quadUnitLowerCell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 quadCounitLowerCell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 quadInvCounitLowerCell))) ?_
  exact quadCohesionLoopContractsOnLeft QuadCohesionSaturatedTwoCellConv.triPi0
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 quadInvCounitLowerCell)

/-! ## The Godement slide of the two unit cups + the space-side residual cup join -/

/-- **The two unit cups slide past each other** (Godement naturality of `η''` at `η`'s component):
`η'' ⊟ ((η ▷ gamma) ▷ codisc) ≈ η ⊟ (pi0 ◁ (disc ◁ η'')) : id_space ⇒ pi0·disc·gamma·codisc` — the shipped
exchange square instantiated at the two unit cells, with the unit-path whiskers erased by
`whiskerLeftUnit`/`whiskerRightUnit` and the composite-path whiskers split by
`whiskerLeftComp`/`whiskerRightComp`. -/
theorem quadLowerUnitSlidesPastUpperUnit :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) quadUnitUpperCell
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadUnitLowerCell)))
      (RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) quadUnitLowerCell
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc quadUnitUpperCell))) := by
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.symm
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerRightComp (signature := quadCohesionModeSignature) quadGamma quadCodisc
            quadUnitLowerCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (QuadCohesionSaturatedTwoCellConv.symm
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerLeftUnit (signature := quadCohesionModeSignature) quadUnitUpperCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionExchangeSquare quadUnitLowerCell quadUnitUpperCell)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (QuadCohesionSaturatedTwoCellConv.ofFull
        (TwoCellConvFull.whiskerRightUnit (signature := quadCohesionModeSignature) quadUnitLowerCell))) ?_
  exact QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
    (QuadCohesionSaturatedTwoCellConv.ofFull
      (TwoCellConvFull.whiskerLeftComp (signature := quadCohesionModeSignature) quadPi0 quadDisc
        quadUnitUpperCell))

/-- The **space-side residual cup via the upper unit**: `id_S ⇒(η'') gamma·codisc ⇒(ptp ▷ codisc)
pi0·codisc` — the upper unit followed by the whiskered points-to-pieces transform (counit form).  The
`space`-endo TWIN of the shipped `quadResidualCupViaUpperCell`: the canonical co-point of the space-side
residual generator `q = pi0·codisc`. -/
def quadSpaceResidualCupViaUpperCell :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space) quadPi0Codisc :=
  RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) quadUnitUpperCell
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc
      quadPointsToPiecesViaCounitCell)

/-- ★★ **THE SPACE-SIDE RESIDUAL-CUP JOIN** — the two derived cups `id_space ⇒ pi0·codisc` are
convertible: the upper-unit route (`quadSpaceResidualCupViaUpperCell`) agrees with the shipped lower-unit
route (`quadCrossCupCell`).  The `space`-side twin of `quadResidualCupJoin`, and the LOAD-BEARING piece of
the whisker slide: both insertions of the point of `w` reduce to this ONE cup whiskered inside
`codisc — pi0`.  Proof: swap `ptp` to its unit form (`quadPointsToPiecesJoin`), slide the two unit cups
past each other (`quadLowerUnitSlidesPastUpperUnit`), and exchange the middle-unit inverse across the
disjoint `pi0`/`codisc` whiskers. -/
theorem quadSpaceResidualCupJoin :
    QuadCohesionSaturatedTwoCellConv quadSpaceResidualCupViaUpperCell quadCrossCupCell := by
  dsimp only [quadSpaceResidualCupViaUpperCell, quadCrossCupCell]
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadCodisc
        (QuadCohesionSaturatedTwoCellConv.symm quadPointsToPiecesJoin))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (quadCohesionConvOfStep (TwoCellStep.whiskerRightVcomp (signature := quadCohesionModeSignature) quadCodisc
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadUnitLowerCell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 quadInvUnitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadVcompAssocShifts quadUnitUpperCell
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadUnitLowerCell))
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 quadInvUnitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _ quadLowerUnitSlidesPastUpperUnit) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.symm
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerExchange (signature := quadCohesionModeSignature) quadPi0 quadCodisc
            quadInvUnitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (quadVcompAssocShifts quadUnitLowerCell
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc quadUnitUpperCell))
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadInvUnitMiddleCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.symm
        (quadCohesionConvOfStep (TwoCellStep.whiskerLeftVcomp (signature := quadCohesionModeSignature) quadPi0
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc quadUnitUpperCell)
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadInvUnitMiddleCell))))) ?_
  exact QuadCohesionSaturatedTwoCellConv.refl _

/-! ## The comultiplication mediation -/

/-- The **residual comultiplication** `σ = (codisc ◁ k) ▷ pi0 : w ⇒ w·w` — the space-side residual cup `k`
inserted BETWEEN the two letters of `w = codisc·pi0`.  Classically `σ_X = Π₀(k_{∇X})`.  Both whisker
insertions of the point `u` into `w` convert into `σ`. -/
def quadResidualComultCell :
    RawTwoCellExpr quadCohesionModeSignature quadCodiscPi0
      (composePath quadCodiscPi0 quadCodiscPi0) :=
  RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc
      quadSpaceResidualCupViaUpperCell)

/-- ★ **The RIGHT insertion is the comultiplication**: `u ▷ w ≈ σ`.  Split the composite whisker
(`whiskerRightComp`), distribute over `u`'s two factors, convert the whiskered `ε''⁻¹` into the whiskered
upper unit (the `codisc`-leg solver), exchange the points-to-pieces block across the disjoint `codisc`
whiskers, and refold into `codisc ◁ (space cup)`. -/
theorem quadResidualCupRightInsertion_isComult :
    QuadCohesionSaturatedTwoCellConv quadResidualCupRightInsertionCell quadResidualComultCell := by
  dsimp only [quadResidualCupRightInsertionCell, quadResidualCupCell, quadResidualCupViaUpperCell,
    quadResidualComultCell]
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.ofFull
      (TwoCellConvFull.whiskerRightComp (signature := quadCohesionModeSignature) quadCodisc quadPi0
        (RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) quadInvCounitUpperCell
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc
            quadPointsToPiecesViaCounitCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadPi0
      (quadCohesionConvOfStep (TwoCellStep.whiskerRightVcomp (signature := quadCohesionModeSignature) quadCodisc
        quadInvCounitUpperCell
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc
          quadPointsToPiecesViaCounitCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadPi0
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.symm quadCodiscUnitUpperWhiskerSolvesToInvCounit))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadPi0
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
        (QuadCohesionSaturatedTwoCellConv.symm
          (QuadCohesionSaturatedTwoCellConv.ofFull
            (TwoCellConvFull.whiskerExchange (signature := quadCohesionModeSignature) quadCodisc quadCodisc
              quadPointsToPiecesViaCounitCell))))) ?_
  exact QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadPi0
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep (TwoCellStep.whiskerLeftVcomp (signature := quadCohesionModeSignature) quadCodisc
        quadUnitUpperCell
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc
          quadPointsToPiecesViaCounitCell))))

/-- ★ **The LEFT insertion is the comultiplication**: `w ◁ u ≈ σ`.  Swap `u` to its LOWER form (the shipped
`quadResidualCupJoin`), split the composite whisker (`whiskerLeftComp`), distribute, convert the whiskered
`ε⁻¹` into the whiskered lower unit (the `pi0`-leg solver), swap the discrete-to-codiscrete comparison to
its upper form (`quadDiscreteToCodiscreteJoin`), exchange twice across the disjoint whiskers, refold into
`(quadCrossCupCell) ▷`-form, and close with the space-side cup join. -/
theorem quadResidualCupLeftInsertion_isComult :
    QuadCohesionSaturatedTwoCellConv quadResidualCupLeftInsertionCell quadResidualComultCell := by
  dsimp only [quadResidualCupLeftInsertionCell, quadResidualCupCell, quadResidualComultCell]
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadCodiscPi0 quadResidualCupJoin) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.ofFull
      (TwoCellConvFull.whiskerLeftComp (signature := quadCohesionModeSignature) quadCodisc quadPi0
        quadResidualCupViaLowerCell)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadCodisc
      (quadCohesionConvOfStep (TwoCellStep.whiskerLeftVcomp (signature := quadCohesionModeSignature) quadPi0
        quadInvCounitLowerCell
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0
          quadDiscreteToCodiscreteViaMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadCodisc
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.symm quadPi0UnitLowerWhiskerSolvesToInvCounit))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadCodisc
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
        (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadPi0
          (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadPi0
            (QuadCohesionSaturatedTwoCellConv.symm quadDiscreteToCodiscreteJoin))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadCodisc
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerExchange (signature := quadCohesionModeSignature) quadPi0 quadPi0
            quadDiscreteToCodiscreteViaUpperCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadCodisc
      (QuadCohesionSaturatedTwoCellConv.symm
        (quadCohesionConvOfStep (TwoCellStep.whiskerRightVcomp (signature := quadCohesionModeSignature) quadPi0
          quadUnitLowerCell
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0
            quadDiscreteToCodiscreteViaUpperCell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.ofFull
      (TwoCellConvFull.whiskerExchange (signature := quadCohesionModeSignature) quadCodisc quadPi0
        quadCrossCupCell)) ?_
  exact QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadPi0
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadCodisc
      (QuadCohesionSaturatedTwoCellConv.symm quadSpaceResidualCupJoin))

/-! ## ★★★ The residual-cup whisker slide -/

/-- ★★★ **THE RESIDUAL-CUP WHISKER SLIDE** — `w ◁ u ≈ u ▷ w`: the two insertions of the canonical point
`u = quadResidualCupCell` into the residual generator `w = codisc·pi0` are convertible in the saturated
congruence.  The pointed endo-1-cell `(w, u)` is **WELL-POINTED** (Kelly) — NOT free structure (for a free
pointed endo the two insertions are the two distinct coface maps `[1] ⇉ [2]` of monotone injections), but
FORCED here by the twelve saturation rows: both sides mediate through the residual comultiplication
`σ = (codisc ◁ k) ▷ pi0` built on the space-side residual cup.  This is the wave-3 crux
(`fxQuadCohesion_hasResidualCupWhiskerSlide`) DERIVED — the pair `quadResidualInsertions_sidesAreDistinct`
certifies is syntactically genuine, and every abelian invariant was provably blind to
(`quadResidualInsertions_parityAgrees`), now decided CONVERTIBLE. -/
theorem quadResidualCupWhiskerSlide :
    QuadCohesionSaturatedTwoCellConv quadResidualCupLeftInsertionCell
      quadResidualCupRightInsertionCell :=
  QuadCohesionSaturatedTwoCellConv.trans quadResidualCupLeftInsertion_isComult
    (QuadCohesionSaturatedTwoCellConv.symm quadResidualCupRightInsertion_isComult)

/-! ## Honesty marker -/

/-- ★★ **ESTABLISHED — the residual pointed endo-1-cell is well-pointed.**  The slide `w ◁ u ≈ u ▷ w`
(`quadResidualCupWhiskerSlide`) plus the space-side cup join (`quadSpaceResidualCupJoin`) close the ENTIRE
derived-cup coherence family the mate-bijection kit isolated: both `pointSet`- and `space`-side residual
cups are unique across their constructions, and the point of `w` slides across `w`.  What this does NOT
give: the free-word NORMALIZER (`fxQuadCohesion_hasFreeWordNormalizerForThinness` stays `false`) — the
slide is the coherence the normalizer's completeness on the residual family `Hom(id, w^n)` was blocked on,
but the per-word canonical 2-cell and its completeness induction over ARBITRARY parallel pairs (whisker
congruence positions, mixed-boundary words, the six-triangle/six-iso critical-pair closure) remain the
named multi-file arc.  `= true`. -/
def fxQuadCohesion_hasResidualCupWellPointedEndo : Bool := true

end FX1Poly.Polygraph

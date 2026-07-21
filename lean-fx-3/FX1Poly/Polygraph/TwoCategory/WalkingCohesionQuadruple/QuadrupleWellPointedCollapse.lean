import FX1Poly.Polygraph.TwoCategory.WalkingCohesionQuadruple.QuadrupleReflectionStraddleJoins

/-! # WalkingCohesionQuadruple/QuadrupleWellPointedCollapse — the Δ-SEPARATOR is DEAD at all three modalities

Wave-2 of the quadruple thinness residual.  The sharpened wall (`fxQuadCohesion_hasFreeWordNormalizerForThinness`)
names TWO possible dispositions: a free-word normalizer (thinness TRUE) or a boundary-determined separator
surviving the saturation (thinness FALSE).  The abelian separators are already machine-checked dead
(`quadCohesionParity_boundaryDetermined` — and the argument generalizes: EVERY commutative-monoid weighting is
forced boundary-compatible by the six triangles and six ff-iso rows, since the boundary-compat map is surjective
on the relation-quotient of the generator weights).  What remained was the ORDER-SENSITIVE separator family — the
Δ-shaped multiplicity of Schanuel–Street: in the walking MONAD the hom `T ⇒ T·T` hosts TWO distinct 2-cells
`T ◁ η` and `η ▷ T` (the two monotone injections in `Δ_a([1],[2])`), and this is exactly the multiplicity that
makes the walking adjunction NON-thin.  Rosebrugh–Wood (*Distributive Adjoint Strings*, TAC 1995) warn the free
ff-adjoint string is Δ-shaped, so this family is THE candidate refutation.

## What this file proves: the ff isos KILL the Δ-multiplicity — at all three induced modalities

For a REFLECTION the induced monad is idempotent, and idempotence identifies the two unit whiskerings
(`T ◁ η ≈ η ▷ T` — both are right-inverses of the invertible multiplication `μ = T ◁ ε ▷ T`, and right-inverses
of a split iso are unique).  This file DERIVES that collapse from the shipped saturation, one instance per
induced modality of the cohesion quadruple:

  * **`ʃ = pi0·disc`** (monad, unit `η = unitLower`):  `ʃ ◁ η ≈ η ▷ ʃ`  (`quadShapeUnitWhiskersAgree`) — both
    right-inverses of `μ_ʃ = pi0 ◁ ε ▷ disc`, invertible by the `Disc`-ff lower-counit iso;
  * **`♭ = gamma·disc`** (comonad, counit `ε' = counitMiddle`):  `♭ ◁ ε' ≈ ε' ▷ ♭`
    (`quadFlatCounitWhiskersAgree`) — both left-inverses of `δ_♭ = gamma ◁ η' ▷ disc`, invertible by the
    `Disc`-ff middle-unit iso;
  * **`♯ = gamma·codisc`** (monad, unit `η'' = unitUpper`):  `♯ ◁ η'' ≈ η'' ▷ ♯`
    (`quadSharpUnitWhiskersAgree`) — both right-inverses of `μ_♯ = gamma ◁ ε'' ▷ codisc`, invertible by the
    `coDisc`-ff upper-counit iso.

Each proof needs the composite-whisker functoriality (`whiskerLeftComp` / `whiskerRightComp` /
`whiskerExchange` from `TwoCellConvFull`, entering through `ofFull` — cast-free on these concrete boundaries
because `composePath` is definitionally associative on literal cons-paths), one adjunction triangle per side,
and one ff-iso round-trip.  This resolves the residual's load-bearing uncertainty — "does the functor-level
identification comonad-counit = adjunction-counit also kill every order-sensitive Δ-separator?" — POSITIVELY at
the modality homs: the Schanuel–Yes multiplicity has no image, the free quadruple is not merely parity-blind but
Δ-blind at `ʃ, ♭, ♯`.

## The remaining three leg joins: every adjunction leg's two parallel routes now join

Wave-1 shipped three straddle joins (disc/lower, disc/middle, codisc/upper).  The other three legs also host a
genuinely parallel pair — the triangle-snake half against the ff-iso half — and they join by the same
inverse-uniqueness engine: `η ▷ pi0 ≈ pi0 ◁ ε⁻¹` (`quadStraddlePi0UnitInvCounitJoin`),
`ε' ▷ gamma ≈ gamma ◁ η'⁻¹` (`quadStraddleGammaCounitMiddleInvUnitJoin`), and
`η'' ▷ gamma ≈ gamma ◁ ε''⁻¹` (`quadStraddleGammaUnitUpperInvCounitJoin`).  With wave-1, ALL SIX legs of the
three adjunctions now carry an explicit populated-hom thinness witness.

## What this does NOT do (the honest boundary)

`QuadCohesionThinness` is NOT flipped: these are finitely many populated homs, not the general-boundary
normalizer, so `fxQuadCohesion_hasQuadrupleThinnessResolution` and
`fxQuadCohesion_hasFreeWordNormalizerForThinness` stay `false`.  What CHANGES is the refutation side of the
wall: with the abelian family provably boundary-determined and the Δ-family now provably collapsing at all
three modalities, no known separator class survives — the residual's honest direction is THIN, and the
remaining work is exactly the free-word normalizer the wave-1 marker names.

Raw Lean 4 + Init; every proof is a constructor chain over the shipped saturation plus `ofFull`-embedded
whisker functoriality — every declaration is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/
`omega`/`decide`/`simp`-free.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The inverse-uniqueness engine (split-iso one-sided-inverse uniqueness, saturated form) -/

/-- **Right-inverses of a split iso are unique** (saturated form).  If `mulCell ⊟ mulInvCell ≈ id` and a
candidate satisfies `candidateCell ⊟ mulCell ≈ id`, then `candidateCell ≈ mulInvCell` — pad with the identity,
expand it to the round-trip, reassociate, collapse the law, drop the identity.  The engine behind every
Δ-separator collapse below: an idempotent modality's two unit whiskerings are BOTH right-inverses of its
(ff-iso-invertible) multiplication. -/
theorem quadCohesionRightInverseOfSplitIsoUnique {sourceMode targetMode : QuadCohesionMode}
    {lowerPath upperPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    (mulCell : RawTwoCellExpr quadCohesionModeSignature upperPath lowerPath)
    (mulInvCell candidateCell : RawTwoCellExpr quadCohesionModeSignature lowerPath upperPath)
    (hRound : QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp mulCell mulInvCell)
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) upperPath))
    (hLaw : QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp candidateCell mulCell)
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) lowerPath)) :
    QuadCohesionSaturatedTwoCellConv candidateCell mulInvCell := by
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep (TwoCellStep.vcompIdRight candidateCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight candidateCell
      (QuadCohesionSaturatedTwoCellConv.symm hRound)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep (TwoCellStep.vcompAssoc candidateCell mulCell mulInvCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft mulInvCell hLaw) ?_
  exact quadCohesionConvOfStep (TwoCellStep.vcompIdLeft mulInvCell)

/-- **Left-inverses of a split iso are unique** (saturated form) — the comonad-side dual of
`quadCohesionRightInverseOfSplitIsoUnique`: if `comulInvCell ⊟ comulCell ≈ id` and
`comulCell ⊟ candidateCell ≈ id`, then `candidateCell ≈ comulInvCell`. -/
theorem quadCohesionLeftInverseOfSplitIsoUnique {sourceMode targetMode : QuadCohesionMode}
    {lowerPath upperPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    (comulCell : RawTwoCellExpr quadCohesionModeSignature lowerPath upperPath)
    (comulInvCell candidateCell : RawTwoCellExpr quadCohesionModeSignature upperPath lowerPath)
    (hRound : QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp comulInvCell comulCell)
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) upperPath))
    (hLaw : QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp comulCell candidateCell)
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) lowerPath)) :
    QuadCohesionSaturatedTwoCellConv candidateCell comulInvCell := by
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep (TwoCellStep.vcompIdLeft candidateCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft candidateCell
      (QuadCohesionSaturatedTwoCellConv.symm hRound)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (quadCohesionConvOfStep (TwoCellStep.vcompAssoc comulInvCell comulCell candidateCell)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight comulInvCell hLaw) ?_
  exact quadCohesionConvOfStep (TwoCellStep.vcompIdRight comulInvCell)

/-! ## `ʃ = pi0·disc` — the shape monad's Δ-pair collapses -/

/-- The LEFT unit whiskering `ʃ ◁ η : ʃ ⇒ ʃ·ʃ` — one of the two Schanuel–Street Δ-cells (the image of the
monotone injection `δ₁ ∈ Δ_a([1],[2])` in the walking monad). -/
def quadShapeLeftUnitWhiskerCell :
    RawTwoCellExpr quadCohesionModeSignature quadPi0Disc (composePath quadPi0Disc quadPi0Disc) :=
  RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0Disc quadUnitLowerCell

/-- The RIGHT unit whiskering `η ▷ ʃ : ʃ ⇒ ʃ·ʃ` — the other Δ-cell (the image of `δ₀`).  In the walking
monad these two are provably DISTINCT; here the `Disc`-ff iso identifies them. -/
def quadShapeRightUnitWhiskerCell :
    RawTwoCellExpr quadCohesionModeSignature quadPi0Disc (composePath quadPi0Disc quadPi0Disc) :=
  RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0Disc quadUnitLowerCell

/-- The shape multiplication `μ_ʃ = pi0 ◁ ε ▷ disc : ʃ·ʃ ⇒ ʃ` — the derived monad multiplication of the
reflection `Π₀ ⊣ Disc`. -/
def quadShapeMulCell :
    RawTwoCellExpr quadCohesionModeSignature (composePath quadPi0Disc quadPi0Disc) quadPi0Disc :=
  RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc quadCounitLowerCell)

/-- The shape multiplication's INVERSE `μ_ʃ⁻¹ = pi0 ◁ ε⁻¹ ▷ disc : ʃ ⇒ ʃ·ʃ` — invertibility is exactly the
`Disc`-ff lower-counit iso, whiskered. -/
def quadShapeMulInvCell :
    RawTwoCellExpr quadCohesionModeSignature quadPi0Disc (composePath quadPi0Disc quadPi0Disc) :=
  RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc quadInvCounitLowerCell)

/-- `μ_ʃ ⊟ μ_ʃ⁻¹ ≈ id_{ʃʃ}` — the whiskered lower-counit round-trip collapses (fold both whisker layers,
fire `isoLowerCounitRight`, erase the identity whiskers). -/
theorem quadShapeMulRoundCollapses :
    QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp quadShapeMulCell quadShapeMulInvCell)
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) (composePath quadPi0Disc quadPi0Disc)) := by
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.whiskerLeftVcomp quadPi0
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc quadCounitLowerCell)
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc
            quadInvCounitLowerCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadPi0
      (QuadCohesionSaturatedTwoCellConv.trans
        (QuadCohesionSaturatedTwoCellConv.symm
          (quadCohesionConvOfStep
            (TwoCellStep.whiskerRightVcomp quadDisc quadCounitLowerCell quadInvCounitLowerCell)))
        (QuadCohesionSaturatedTwoCellConv.trans
          (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadDisc
            QuadCohesionSaturatedTwoCellConv.isoLowerCounitRight)
          (quadCohesionConvOfStep
            (TwoCellStep.whiskerRightId (signature := quadCohesionModeSignature) quadDiscPi0 quadDisc))))) ?_
  exact quadCohesionConvOfStep
    (TwoCellStep.whiskerLeftId (signature := quadCohesionModeSignature) quadPi0
      (composePath quadDiscPi0 quadDisc))

/-- The shape monad's LEFT unit law `(ʃ ◁ η) ⊟ μ_ʃ ≈ id_ʃ` — split the composite whisker
(`whiskerLeftComp`), fold, and the interior is EXACTLY the `Π₀ ⊣ Disc` triangle snake on `disc`
(`triDiscLo`). -/
theorem quadShapeMonadLeftUnitLaw :
    QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp quadShapeLeftUnitWhiskerCell quadShapeMulCell)
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) quadPi0Disc) := by
  have hSplitWhisker := QuadCohesionSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerLeftComp quadPi0 quadDisc quadUnitLowerCell)
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft quadShapeMulCell hSplitWhisker) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.whiskerLeftVcomp quadPi0
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc quadUnitLowerCell)
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc
            quadCounitLowerCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadPi0
      QuadCohesionSaturatedTwoCellConv.triDiscLo) ?_
  exact quadCohesionConvOfStep
    (TwoCellStep.whiskerLeftId (signature := quadCohesionModeSignature) quadPi0 quadDisc)

/-- The shape monad's RIGHT unit law `(η ▷ ʃ) ⊟ μ_ʃ ≈ id_ʃ` — split the composite whisker
(`whiskerRightComp`), exchange `μ_ʃ`'s nesting (`whiskerExchange`), fold, and the interior is EXACTLY the
`Π₀ ⊣ Disc` triangle snake on `pi0` (`triPi0`). -/
theorem quadShapeMonadRightUnitLaw :
    QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp quadShapeRightUnitWhiskerCell quadShapeMulCell)
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) quadPi0Disc) := by
  have hSplitWhisker := QuadCohesionSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerRightComp quadPi0 quadDisc quadUnitLowerCell)
  have hExchangeMul := QuadCohesionSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerExchange quadPi0 quadDisc quadCounitLowerCell)
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft quadShapeMulCell hSplitWhisker) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0 quadUnitLowerCell))
      hExchangeMul) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.whiskerRightVcomp quadDisc
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0 quadUnitLowerCell)
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0
            quadCounitLowerCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadDisc
      QuadCohesionSaturatedTwoCellConv.triPi0) ?_
  exact quadCohesionConvOfStep
    (TwoCellStep.whiskerRightId (signature := quadCohesionModeSignature) quadPi0 quadDisc)

/-- ★★ **The Δ-separator is DEAD at `ʃ`**: `ʃ ◁ η ≈ η ▷ ʃ`.  In the walking monad these are the two DISTINCT
cells of `Δ_a([1],[2])` (Schanuel–Street) — the canonical order-sensitive separator the wall named as the
refutation candidate.  Here both are right-inverses of the split iso `μ_ʃ`, hence convertible: the `Disc`-ff
iso collapses the Δ-multiplicity.  The shape monad is WELL-POINTED in the free quadruple. -/
theorem quadShapeUnitWhiskersAgree :
    QuadCohesionSaturatedTwoCellConv quadShapeLeftUnitWhiskerCell quadShapeRightUnitWhiskerCell :=
  QuadCohesionSaturatedTwoCellConv.trans
    (quadCohesionRightInverseOfSplitIsoUnique quadShapeMulCell quadShapeMulInvCell
      quadShapeLeftUnitWhiskerCell quadShapeMulRoundCollapses quadShapeMonadLeftUnitLaw)
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionRightInverseOfSplitIsoUnique quadShapeMulCell quadShapeMulInvCell
        quadShapeRightUnitWhiskerCell quadShapeMulRoundCollapses quadShapeMonadRightUnitLaw))

/-! ## `♭ = gamma·disc` — the flat comonad's Δ-pair collapses (the mirror-image, counit side) -/

/-- The LEFT counit whiskering `♭ ◁ ε' : ♭·♭ ⇒ ♭` — one of the flat comonad's two Δ-cells. -/
def quadFlatLeftCounitWhiskerCell :
    RawTwoCellExpr quadCohesionModeSignature (composePath quadGammaDisc quadGammaDisc) quadGammaDisc :=
  RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGammaDisc quadCounitMiddleCell

/-- The RIGHT counit whiskering `ε' ▷ ♭ : ♭·♭ ⇒ ♭` — the other flat Δ-cell. -/
def quadFlatRightCounitWhiskerCell :
    RawTwoCellExpr quadCohesionModeSignature (composePath quadGammaDisc quadGammaDisc) quadGammaDisc :=
  RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGammaDisc quadCounitMiddleCell

/-- The flat comultiplication `δ_♭ = gamma ◁ η' ▷ disc : ♭ ⇒ ♭·♭` — the derived comonad comultiplication of
the coreflection `Disc ⊣ Γ`. -/
def quadFlatComulCell :
    RawTwoCellExpr quadCohesionModeSignature quadGammaDisc (composePath quadGammaDisc quadGammaDisc) :=
  RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc quadUnitMiddleCell)

/-- The flat comultiplication's INVERSE `δ_♭⁻¹ = gamma ◁ η'⁻¹ ▷ disc : ♭·♭ ⇒ ♭` — invertibility is the
`Disc`-ff middle-unit iso, whiskered. -/
def quadFlatComulInvCell :
    RawTwoCellExpr quadCohesionModeSignature (composePath quadGammaDisc quadGammaDisc) quadGammaDisc :=
  RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc quadInvUnitMiddleCell)

/-- `δ_♭⁻¹ ⊟ δ_♭ ≈ id_{♭♭}` — the whiskered middle-unit round-trip collapses (`isoMiddleUnitLeft`). -/
theorem quadFlatComulRoundCollapses :
    QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp quadFlatComulInvCell quadFlatComulCell)
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature)
        (composePath quadGammaDisc quadGammaDisc)) := by
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.whiskerLeftVcomp quadGamma
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc quadInvUnitMiddleCell)
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc
            quadUnitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadGamma
      (QuadCohesionSaturatedTwoCellConv.trans
        (QuadCohesionSaturatedTwoCellConv.symm
          (quadCohesionConvOfStep
            (TwoCellStep.whiskerRightVcomp quadDisc quadInvUnitMiddleCell quadUnitMiddleCell)))
        (QuadCohesionSaturatedTwoCellConv.trans
          (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadDisc
            QuadCohesionSaturatedTwoCellConv.isoMiddleUnitLeft)
          (quadCohesionConvOfStep
            (TwoCellStep.whiskerRightId (signature := quadCohesionModeSignature) quadDiscGamma quadDisc))))) ?_
  exact quadCohesionConvOfStep
    (TwoCellStep.whiskerLeftId (signature := quadCohesionModeSignature) quadGamma
      (composePath quadDiscGamma quadDisc))

/-- The flat comonad's LEFT counit law `δ_♭ ⊟ (♭ ◁ ε') ≈ id_♭` — split the composite whisker, fold, and the
interior is EXACTLY the `Disc ⊣ Γ` triangle snake on `disc` (`triDiscHi`). -/
theorem quadFlatComonadLeftCounitLaw :
    QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp quadFlatComulCell quadFlatLeftCounitWhiskerCell)
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) quadGammaDisc) := by
  have hSplitWhisker := QuadCohesionSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerLeftComp quadGamma quadDisc quadCounitMiddleCell)
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight quadFlatComulCell hSplitWhisker) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.whiskerLeftVcomp quadGamma
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc quadUnitMiddleCell)
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc
            quadCounitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadGamma
      QuadCohesionSaturatedTwoCellConv.triDiscHi) ?_
  exact quadCohesionConvOfStep
    (TwoCellStep.whiskerLeftId (signature := quadCohesionModeSignature) quadGamma quadDisc)

/-- The flat comonad's RIGHT counit law `δ_♭ ⊟ (ε' ▷ ♭) ≈ id_♭` — exchange `δ_♭`'s nesting, split the
composite whisker, fold, and the interior is EXACTLY the `Disc ⊣ Γ` triangle snake on `gamma`
(`triGammaLo`). -/
theorem quadFlatComonadRightCounitLaw :
    QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp quadFlatComulCell quadFlatRightCounitWhiskerCell)
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) quadGammaDisc) := by
  have hExchangeComul := QuadCohesionSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerExchange quadGamma quadDisc quadUnitMiddleCell)
  have hSplitWhisker := QuadCohesionSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerRightComp quadGamma quadDisc quadCounitMiddleCell)
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft quadFlatRightCounitWhiskerCell hExchangeComul) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma quadUnitMiddleCell))
      hSplitWhisker) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.whiskerRightVcomp quadDisc
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma quadUnitMiddleCell)
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma
            quadCounitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadDisc
      QuadCohesionSaturatedTwoCellConv.triGammaLo) ?_
  exact quadCohesionConvOfStep
    (TwoCellStep.whiskerRightId (signature := quadCohesionModeSignature) quadGamma quadDisc)

/-- ★★ **The Δ-separator is DEAD at `♭`**: `♭ ◁ ε' ≈ ε' ▷ ♭`.  Both are left-inverses of the split iso
`δ_♭`, hence convertible — the flat comonad is WELL-COPOINTED in the free quadruple. -/
theorem quadFlatCounitWhiskersAgree :
    QuadCohesionSaturatedTwoCellConv quadFlatLeftCounitWhiskerCell quadFlatRightCounitWhiskerCell :=
  QuadCohesionSaturatedTwoCellConv.trans
    (quadCohesionLeftInverseOfSplitIsoUnique quadFlatComulCell quadFlatComulInvCell
      quadFlatLeftCounitWhiskerCell quadFlatComulRoundCollapses quadFlatComonadLeftCounitLaw)
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionLeftInverseOfSplitIsoUnique quadFlatComulCell quadFlatComulInvCell
        quadFlatRightCounitWhiskerCell quadFlatComulRoundCollapses quadFlatComonadRightCounitLaw))

/-! ## `♯ = gamma·codisc` — the sharp monad's Δ-pair collapses -/

/-- The LEFT unit whiskering `♯ ◁ η'' : ♯ ⇒ ♯·♯` — one of the sharp monad's two Δ-cells. -/
def quadSharpLeftUnitWhiskerCell :
    RawTwoCellExpr quadCohesionModeSignature quadGammaCodisc (composePath quadGammaCodisc quadGammaCodisc) :=
  RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGammaCodisc quadUnitUpperCell

/-- The RIGHT unit whiskering `η'' ▷ ♯ : ♯ ⇒ ♯·♯` — the other sharp Δ-cell. -/
def quadSharpRightUnitWhiskerCell :
    RawTwoCellExpr quadCohesionModeSignature quadGammaCodisc (composePath quadGammaCodisc quadGammaCodisc) :=
  RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGammaCodisc quadUnitUpperCell

/-- The sharp multiplication `μ_♯ = gamma ◁ ε'' ▷ codisc : ♯·♯ ⇒ ♯` — the derived monad multiplication of
the reflection `Γ ⊣ coDisc`. -/
def quadSharpMulCell :
    RawTwoCellExpr quadCohesionModeSignature (composePath quadGammaCodisc quadGammaCodisc) quadGammaCodisc :=
  RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadCounitUpperCell)

/-- The sharp multiplication's INVERSE `μ_♯⁻¹ = gamma ◁ ε''⁻¹ ▷ codisc : ♯ ⇒ ♯·♯` — invertibility is the
`coDisc`-ff upper-counit iso, whiskered. -/
def quadSharpMulInvCell :
    RawTwoCellExpr quadCohesionModeSignature quadGammaCodisc (composePath quadGammaCodisc quadGammaCodisc) :=
  RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadInvCounitUpperCell)

/-- `μ_♯ ⊟ μ_♯⁻¹ ≈ id_{♯♯}` — the whiskered upper-counit round-trip collapses (`isoUpperCounitRight`). -/
theorem quadSharpMulRoundCollapses :
    QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp quadSharpMulCell quadSharpMulInvCell)
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature)
        (composePath quadGammaCodisc quadGammaCodisc)) := by
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.whiskerLeftVcomp quadGamma
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadCounitUpperCell)
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc
            quadInvCounitUpperCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadGamma
      (QuadCohesionSaturatedTwoCellConv.trans
        (QuadCohesionSaturatedTwoCellConv.symm
          (quadCohesionConvOfStep
            (TwoCellStep.whiskerRightVcomp quadCodisc quadCounitUpperCell quadInvCounitUpperCell)))
        (QuadCohesionSaturatedTwoCellConv.trans
          (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadCodisc
            QuadCohesionSaturatedTwoCellConv.isoUpperCounitRight)
          (quadCohesionConvOfStep
            (TwoCellStep.whiskerRightId (signature := quadCohesionModeSignature) quadCodiscGamma
              quadCodisc))))) ?_
  exact quadCohesionConvOfStep
    (TwoCellStep.whiskerLeftId (signature := quadCohesionModeSignature) quadGamma
      (composePath quadCodiscGamma quadCodisc))

/-- The sharp monad's LEFT unit law `(♯ ◁ η'') ⊟ μ_♯ ≈ id_♯` — the interior is EXACTLY the `Γ ⊣ coDisc`
triangle snake on `codisc` (`triCodisc`). -/
theorem quadSharpMonadLeftUnitLaw :
    QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp quadSharpLeftUnitWhiskerCell quadSharpMulCell)
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) quadGammaCodisc) := by
  have hSplitWhisker := QuadCohesionSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerLeftComp quadGamma quadCodisc quadUnitUpperCell)
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft quadSharpMulCell hSplitWhisker) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.whiskerLeftVcomp quadGamma
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc quadUnitUpperCell)
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc
            quadCounitUpperCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadGamma
      QuadCohesionSaturatedTwoCellConv.triCodisc) ?_
  exact quadCohesionConvOfStep
    (TwoCellStep.whiskerLeftId (signature := quadCohesionModeSignature) quadGamma quadCodisc)

/-- The sharp monad's RIGHT unit law `(η'' ▷ ♯) ⊟ μ_♯ ≈ id_♯` — the interior is EXACTLY the `Γ ⊣ coDisc`
triangle snake on `gamma` (`triGammaHi`). -/
theorem quadSharpMonadRightUnitLaw :
    QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp quadSharpRightUnitWhiskerCell quadSharpMulCell)
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) quadGammaCodisc) := by
  have hSplitWhisker := QuadCohesionSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerRightComp quadGamma quadCodisc quadUnitUpperCell)
  have hExchangeMul := QuadCohesionSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerExchange quadGamma quadCodisc quadCounitUpperCell)
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft quadSharpMulCell hSplitWhisker) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadUnitUpperCell))
      hExchangeMul) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.whiskerRightVcomp quadCodisc
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadUnitUpperCell)
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma
            quadCounitUpperCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadCodisc
      QuadCohesionSaturatedTwoCellConv.triGammaHi) ?_
  exact quadCohesionConvOfStep
    (TwoCellStep.whiskerRightId (signature := quadCohesionModeSignature) quadGamma quadCodisc)

/-- ★★ **The Δ-separator is DEAD at `♯`**: `♯ ◁ η'' ≈ η'' ▷ ♯` — the sharp monad is WELL-POINTED in the
free quadruple, by the same split-iso uniqueness through the `coDisc`-ff iso. -/
theorem quadSharpUnitWhiskersAgree :
    QuadCohesionSaturatedTwoCellConv quadSharpLeftUnitWhiskerCell quadSharpRightUnitWhiskerCell :=
  QuadCohesionSaturatedTwoCellConv.trans
    (quadCohesionRightInverseOfSplitIsoUnique quadSharpMulCell quadSharpMulInvCell
      quadSharpLeftUnitWhiskerCell quadSharpMulRoundCollapses quadSharpMonadLeftUnitLaw)
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionRightInverseOfSplitIsoUnique quadSharpMulCell quadSharpMulInvCell
        quadSharpRightUnitWhiskerCell quadSharpMulRoundCollapses quadSharpMonadRightUnitLaw))

/-! ## The three remaining leg joins — all six adjunction legs now host a populated-hom join -/

/-- ★ **The `pi0`-leg join `η ▷ pi0 ≈ pi0 ◁ ε⁻¹`** over the populated hom `pi0 ⇒ pi0·disc·pi0`: the
triangle-snake half of `triPi0` against the whiskered ff-inverse — both right-inverses of `pi0 ◁ ε`.  The
`pi0`-leg analog of the shipped disc/lower straddle join. -/
theorem quadStraddlePi0UnitInvCounitJoin :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0 quadUnitLowerCell)
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 quadInvCounitLowerCell) := by
  refine quadCohesionRightInverseOfSplitIsoUnique
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 quadCounitLowerCell)
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 quadInvCounitLowerCell)
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0 quadUnitLowerCell)
    ?_ QuadCohesionSaturatedTwoCellConv.triPi0
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.whiskerLeftVcomp quadPi0 quadCounitLowerCell quadInvCounitLowerCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadPi0
      QuadCohesionSaturatedTwoCellConv.isoLowerCounitRight) ?_
  exact quadCohesionConvOfStep
    (TwoCellStep.whiskerLeftId (signature := quadCohesionModeSignature) quadPi0 quadDiscPi0)

/-- ★ **The `gamma`-leg middle join `ε' ▷ gamma ≈ gamma ◁ η'⁻¹`** over the populated hom
`gamma·disc·gamma ⇒ gamma`: the triangle-snake half of `triGammaLo` against the whiskered ff-inverse — both
left-inverses of `gamma ◁ η'`. -/
theorem quadStraddleGammaCounitMiddleInvUnitJoin :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadCounitMiddleCell)
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma quadInvUnitMiddleCell) := by
  refine quadCohesionLeftInverseOfSplitIsoUnique
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma quadUnitMiddleCell)
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma quadInvUnitMiddleCell)
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadCounitMiddleCell)
    ?_ QuadCohesionSaturatedTwoCellConv.triGammaLo
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.whiskerLeftVcomp quadGamma quadInvUnitMiddleCell quadUnitMiddleCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadGamma
      QuadCohesionSaturatedTwoCellConv.isoMiddleUnitLeft) ?_
  exact quadCohesionConvOfStep
    (TwoCellStep.whiskerLeftId (signature := quadCohesionModeSignature) quadGamma quadDiscGamma)

/-- ★ **The `gamma`-leg upper join `η'' ▷ gamma ≈ gamma ◁ ε''⁻¹`** over the populated hom
`gamma ⇒ gamma·codisc·gamma`: the triangle-snake half of `triGammaHi` against the whiskered ff-inverse — both
right-inverses of `gamma ◁ ε''`.  With the shipped disc/lower, disc/middle, codisc/upper joins and the two
joins above, EVERY leg of all three adjunctions now hosts an explicit populated-hom thinness witness. -/
theorem quadStraddleGammaUnitUpperInvCounitJoin :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadUnitUpperCell)
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma quadInvCounitUpperCell) := by
  refine quadCohesionRightInverseOfSplitIsoUnique
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma quadCounitUpperCell)
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma quadInvCounitUpperCell)
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadUnitUpperCell)
    ?_ QuadCohesionSaturatedTwoCellConv.triGammaHi
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.whiskerLeftVcomp quadGamma quadCounitUpperCell quadInvCounitUpperCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadGamma
      QuadCohesionSaturatedTwoCellConv.isoUpperCounitRight) ?_
  exact quadCohesionConvOfStep
    (TwoCellStep.whiskerLeftId (signature := quadCohesionModeSignature) quadGamma quadCodiscGamma)

/-! ## Bundles + non-degeneracy -/

/-- ★★ **The Δ-separator collapse, bundled**: at every one of the three induced modalities the two
unit/counit whiskerings — the exact Schanuel–Street `Δ_a([1],[2])` multiplicity that refutes thinness in the
walking monad — are convertible.  The canonical order-sensitive separator family has NO image in the
quadruple. -/
theorem quadAllModalityDeltaSeparatorsCollapse :
    QuadCohesionSaturatedTwoCellConv quadShapeLeftUnitWhiskerCell quadShapeRightUnitWhiskerCell ∧
      QuadCohesionSaturatedTwoCellConv quadFlatLeftCounitWhiskerCell quadFlatRightCounitWhiskerCell ∧
      QuadCohesionSaturatedTwoCellConv quadSharpLeftUnitWhiskerCell quadSharpRightUnitWhiskerCell :=
  ⟨quadShapeUnitWhiskersAgree, quadFlatCounitWhiskersAgree, quadSharpUnitWhiskersAgree⟩

/-- ★ **The remaining-legs join suite, bundled**: the `pi0`, `gamma`-middle, and `gamma`-upper leg joins —
together with wave-1's three straddle joins, all six adjunction legs are covered. -/
theorem quadRemainingLegStraddleJoins :
    QuadCohesionSaturatedTwoCellConv
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0 quadUnitLowerCell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0
          quadInvCounitLowerCell) ∧
      QuadCohesionSaturatedTwoCellConv
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadCounitMiddleCell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma
          quadInvUnitMiddleCell) ∧
      QuadCohesionSaturatedTwoCellConv
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadUnitUpperCell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma
          quadInvCounitUpperCell) :=
  ⟨quadStraddlePi0UnitInvCounitJoin, quadStraddleGammaCounitMiddleInvUnitJoin,
    quadStraddleGammaUnitUpperInvCounitJoin⟩

/-- Whether a free 2-cell's head constructor is a LEFT whiskering — the structural probe that separates the
two sides of each Δ-pair as RAW TERMS (so the collapses are genuine identifications, not reflexivities).
Full five-case enumeration, constant `Bool` motive: `propext`-free. -/
def quadIsWhiskerLeftHeadedCell {sourceMode targetMode : QuadCohesionMode}
    {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath) : Bool :=
  match cell with
  | .whiskerLeft _ _ => true
  | .gen _ => false
  | .id _ => false
  | .vcomp _ _ => false
  | .whiskerRight _ _ => false

/-- Non-degeneracy at `ʃ`: the two sides of the shape Δ-pair are DISTINCT raw terms (left- vs
right-whisker-headed), so `quadShapeUnitWhiskersAgree` identifies a genuinely non-trivial parallel pair. -/
theorem quadShapeUnitWhiskers_sidesAreDistinct :
    quadShapeLeftUnitWhiskerCell ≠ quadShapeRightUnitWhiskerCell :=
  fun sidesEqual => Bool.noConfusion (congrArg quadIsWhiskerLeftHeadedCell sidesEqual)

/-- Non-degeneracy at `♭`: the two sides of the flat Δ-pair are distinct raw terms. -/
theorem quadFlatCounitWhiskers_sidesAreDistinct :
    quadFlatLeftCounitWhiskerCell ≠ quadFlatRightCounitWhiskerCell :=
  fun sidesEqual => Bool.noConfusion (congrArg quadIsWhiskerLeftHeadedCell sidesEqual)

/-- Non-degeneracy at `♯`: the two sides of the sharp Δ-pair are distinct raw terms. -/
theorem quadSharpUnitWhiskers_sidesAreDistinct :
    quadSharpLeftUnitWhiskerCell ≠ quadSharpRightUnitWhiskerCell :=
  fun sidesEqual => Bool.noConfusion (congrArg quadIsWhiskerLeftHeadedCell sidesEqual)

/-! ## Honesty markers -/

/-- ★★ **ESTABLISHED — the Δ-separator family is machine-checked DEAD at all three induced modalities.**
The wall's load-bearing uncertainty ("does the functor-level identification comonad-counit =
adjunction-counit also kill every order-sensitive Δ-separator?") is answered YES at the modality homs:
`ʃ ◁ η ≈ η ▷ ʃ` (`quadShapeUnitWhiskersAgree`), `♭ ◁ ε' ≈ ε' ▷ ♭` (`quadFlatCounitWhiskersAgree`),
`♯ ◁ η'' ≈ η'' ▷ ♯` (`quadSharpUnitWhiskersAgree`) — each pair distinct as raw terms
(`…_sidesAreDistinct`), each identified through the split-iso inverse-uniqueness engine
(`quadCohesionRightInverseOfSplitIsoUnique` / `…Left…`) driven by the ff isos.  The Schanuel–Street
`Δ_a([1],[2])` multiplicity — the exact mechanism that makes the walking monad and the walking adjunction
non-thin, and the canonical refutation candidate Rosebrugh–Wood's Δ-shape warning points at — has NO image
in the quadruple.  With the abelian family already boundary-determined
(`quadCohesionParity_boundaryDetermined`), NO known separator class survives: the thinness residual's honest
direction is THIN.  `= true`. -/
def fxQuadCohesion_hasDeltaSeparatorCollapseAtAllThreeModalities : Bool := true

/-- ★ **ESTABLISHED — all six adjunction legs host a populated-hom join.**  Wave-1 shipped disc/lower,
disc/middle, codisc/upper; this file adds `pi0` (`quadStraddlePi0UnitInvCounitJoin`), `gamma`-middle
(`quadStraddleGammaCounitMiddleInvUnitJoin`), and `gamma`-upper (`quadStraddleGammaUnitUpperInvCounitJoin`).
Every leg of `Π₀ ⊣ Disc ⊣ Γ ⊣ coDisc` now carries an explicit thinness witness on a distinct populated hom.
The master flags (`fxQuadCohesion_hasQuadrupleThinnessResolution`,
`fxQuadCohesion_hasFreeWordNormalizerForThinness`) stay HONESTLY `false`: these are finitely many homs, not
the general-boundary free-word normalizer, which remains the single blocking node — but the refutation route
is now doubly dead (abelian invariants boundary-determined, Δ-separators collapsing), so the normalizer is
the residual's whole remaining content.  `= true`. -/
def fxQuadCohesion_hasAllSixLegStraddleJoins : Bool := true

end FX1Poly.Polygraph

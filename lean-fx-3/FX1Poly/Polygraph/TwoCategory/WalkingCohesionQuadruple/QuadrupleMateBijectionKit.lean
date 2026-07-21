import FX1Poly.Polygraph.TwoCategory.WalkingCohesionQuadruple.QuadrupleWellPointedCollapse

/-! # WalkingCohesionQuadruple/QuadrupleMateBijectionKit — the mate-bijection kit + the derived-comparison joins

Wave-3 of the quadruple thinness residual.  The sharpened wall (`fxQuadCohesion_hasFreeWordNormalizerForThinness`)
still names the general-boundary free-word normalizer as the single blocking node; this file lands the KIT the
normalizer's completeness argument is made of, plus the four derived-comparison joins that the kit decides.

## The mate-bijection kit (the transposition engine)

For each adjunction whose relevant unit/counit pair drives a HEAD letter, transposition across the adjunction is a
BIJECTION of hom-sets implemented by explicit 2-cell composites, and this file proves both round-trips up to the
saturated congruence, GENERALLY in the tail word and the target word (cast-free, because every whisker head is a
concrete letter so `composePath` associativity is definitional):

  * `quadMateAlongCodisc_retract` / `_section` — peel a leading `codisc`:
    `Hom(codisc·U, V) ≅ Hom(U, gamma·V)` via `Γ ⊣ coDisc` (triangles `triCodisc` + `triGammaHi`);
  * `quadMateAlongGamma_retract` / `_section` — peel a leading `gamma`:
    `Hom(gamma·U, V) ≅ Hom(U, disc·V)` via `Disc ⊣ Γ` (triangles `triGammaLo` + `triDiscHi`);
  * `quadMateAlongDisc_retract` / `_section` — peel a leading `disc`:
    `Hom(disc·U, V) ≅ Hom(U, pi0·V)` via `Π₀ ⊣ Disc` (triangles `triDiscLo` + `triPi0`);
  * `quadMateTailDiscToCodisc_retract` — the TAIL-side transpose at the concrete boundary the joins consume:
    `Hom(disc, codisc) ≅ Hom(id_P, codisc·gamma)` via `Disc ⊣ Γ` (triangle `triDiscHi`).

The engine underneath is the **exchange square** `twoCellConv_exchangeSquare` — the two evaluation orders of a
horizontal composite agree, derived from the shipped `interchange` step with identity blocks (signature-GENERIC,
cast-free) — plus the two **loop-contraction** helpers (`quadCohesionLoopContractsOnLeft/Right`: an endo-loop
convertible to the identity drops out of any composite).

## The four derived-comparison joins (each a genuinely non-trivial parallel pair, decided)

  * ★ `quadPointsToPiecesJoin` — the POINTS-TO-PIECES transform `Γ ⇒ Π₀` is UNIQUE: the unit route
    `(η ▷ gamma) ⊟ (pi0 ◁ η'⁻¹)` and the counit route `(gamma ◁ ε⁻¹) ⊟ (ε' ▷ pi0)` are convertible.  nLab
    (*cohesive topos*) proves this agreement in every cohesive topos; here it holds already in the FREE quadruple.
  * ★ `quadDiscreteToCodiscreteJoin` — the dual comparison `Disc ⇒ coDisc` is unique: the upper-unit route
    `(disc ◁ η'') ⊟ (η'⁻¹ ▷ codisc)` agrees with the middle-counit route `(ε''⁻¹ ▷ disc) ⊟ (codisc ◁ ε')`.
  * ★ `quadResidualCupJoin` — the two DERIVED CUPS `id_P ⇒ codisc·pi0` (through the upper ff iso + points-to-pieces
    vs through the lower ff iso + discrete-to-codiscrete) are convertible: the residual generator `w = codisc·pi0`
    — the ONLY `pointSet`-endo letter pair not collapsed by an ff iso — has ONE canonical point, not two.
  * ★ `quadCrossMatchingJoin` — the NESTED and SIDE-BY-SIDE planar matchings of the boundary
    `id_space ⇒ pi0·disc·gamma·codisc` agree: `(η then η'' side-by-side) ≈ (the derived cup id ⇒ pi0·codisc with
    the middle unit η' inserted inside)` — the cross-adjunction critical pair of the would-be matching normal form.

## What this does NOT do (the honest boundary) + the SHARPENED crux

`QuadCohesionThinness` is NOT flipped; `fxQuadCohesion_hasQuadrupleThinnessResolution` and
`fxQuadCohesion_hasFreeWordNormalizerForThinness` stay `false`.  What the kit CHANGES is the shape of the residual:
the three generic head peels strip any leading `disc`/`gamma`/`codisc` from a hom's source, so up to transposition
the open content concentrates on the residual family around `w = codisc·pi0` — the one `pointSet`-endo letter
pair no ff iso collapses — and on that family the LAST open coherence is the **residual-cup whisker slide**
`w ◁ u ≈ u ▷ w` (`quadResidualCupLeftInsertionCell` vs `quadResidualCupRightInsertionCell`, the well-pointedness
of the pointed endo-1-cell `(w, u)`).  Wave-4 (`QuadrupleResidualCupSlide.lean`) DERIVES the slide
(`quadResidualCupWhiskerSlide`, flag `fxQuadCohesion_hasResidualCupWhiskerSlide = true`): both insertions
mediate through the residual comultiplication over the SPACE-side residual cup.  Every separator family had
been provably blind to the pair — abelian invariants boundary-determined
(`quadCohesionParity_boundaryDetermined`, instantiated as `quadResidualInsertions_parityAgrees`), the
Schanuel–Street Δ-multiplicity collapsed at all three modalities (`QuadrupleWellPointedCollapse`), and concrete
cohesion models satisfied the slide — and the derivation confirms the thin-leaning reading on this family.

Raw Lean 4 + Init; every proof is a constructor chain over the shipped saturation, the free 3-cells, and the
completed whisker functoriality (`ofFull`, cast-collapsed on concrete-letter boundaries) — every declaration is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`/`decide`/`simp`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The exchange square — the two evaluation orders of a horizontal composite agree

Signature-GENERIC and cast-free: both orders live between `composePath`-untouched boundaries.  Derived from the
shipped `TwoCellStep.interchange` applied to the vertical composites padded with identity 2-cells, then cleaned
with the identity-whisker and identity-composite 3-cells. -/

/-- ★ **The exchange square** (Godement sliding): for `leftCell : F ⇒ F'` and `rightCell : G ⇒ G'` over
composable boundaries, `(leftCell ▷ G) ⊟ (F' ◁ rightCell) ≈ (F ◁ rightCell) ⊟ (leftCell ▷ G')` — the two ways of
evaluating the horizontal composite agree, in the FREE convertibility.  Proof: pad to
`hcomp (id ⊟ leftCell) (rightCell ⊟ id)`, fire the `interchange` 3-cell, and erase the identity whiskers /
identity factors.  Cast-free (no `composePath` reassociation anywhere). -/
theorem twoCellConv_exchangeSquare {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {leftDomPath leftCodPath : ModalityPath signature.graph sourceMode middleMode}
    {rightDomPath rightCodPath : ModalityPath signature.graph middleMode targetMode}
    (leftCell : RawTwoCellExpr signature leftDomPath leftCodPath)
    (rightCell : RawTwoCellExpr signature rightDomPath rightCodPath) :
    TwoCellConv signature
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerRight rightDomPath leftCell)
        (RawTwoCellExpr.whiskerLeft leftCodPath rightCell))
      (RawTwoCellExpr.vcomp (RawTwoCellExpr.whiskerLeft leftDomPath rightCell)
        (RawTwoCellExpr.whiskerRight rightCodPath leftCell)) := by
  refine TwoCellConv.trans (TwoCellConv.symm (TwoCellConv.ofStep
    (TwoCellStep.vcompCongrLeft _
      (TwoCellStep.whiskerRightCongr rightDomPath (TwoCellStep.vcompIdLeft leftCell))))) ?_
  refine TwoCellConv.trans (TwoCellConv.symm (TwoCellConv.ofStep
    (TwoCellStep.vcompCongrRight _
      (TwoCellStep.whiskerLeftCongr leftCodPath (TwoCellStep.vcompIdRight rightCell))))) ?_
  refine TwoCellConv.trans (TwoCellConv.ofStep
    (TwoCellStep.interchange (RawTwoCellExpr.id leftDomPath) leftCell rightCell
      (RawTwoCellExpr.id rightCodPath))) ?_
  refine TwoCellConv.trans (TwoCellConv.ofStep (TwoCellStep.vcompCongrLeft _
    (TwoCellStep.vcompCongrLeft _ (TwoCellStep.whiskerRightId leftDomPath rightDomPath)))) ?_
  refine TwoCellConv.trans (TwoCellConv.ofStep (TwoCellStep.vcompCongrLeft _
    (TwoCellStep.vcompIdLeft (RawTwoCellExpr.whiskerLeft leftDomPath rightCell)))) ?_
  refine TwoCellConv.trans (TwoCellConv.ofStep (TwoCellStep.vcompCongrRight _
    (TwoCellStep.vcompCongrRight _ (TwoCellStep.whiskerLeftId leftCodPath rightCodPath)))) ?_
  refine TwoCellConv.trans (TwoCellConv.ofStep (TwoCellStep.vcompCongrRight _
    (TwoCellStep.vcompIdRight (RawTwoCellExpr.whiskerRight rightCodPath leftCell)))) ?_
  exact TwoCellConv.refl _

/-- The exchange square, lifted to the quadruple's saturated congruence. -/
theorem quadCohesionExchangeSquare {sourceMode middleMode targetMode : QuadCohesionMode}
    {leftDomPath leftCodPath : ModalityPath quadCohesionGraph sourceMode middleMode}
    {rightDomPath rightCodPath : ModalityPath quadCohesionGraph middleMode targetMode}
    (leftCell : RawTwoCellExpr quadCohesionModeSignature leftDomPath leftCodPath)
    (rightCell : RawTwoCellExpr quadCohesionModeSignature rightDomPath rightCodPath) :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) rightDomPath leftCell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) leftCodPath rightCell))
      (RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) leftDomPath rightCell)
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) rightCodPath leftCell)) :=
  QuadCohesionSaturatedTwoCellConv.ofConv (twoCellConv_exchangeSquare leftCell rightCell)

/-! ## The loop-contraction helpers -/

/-- **Loop contraction (right)**: an endo-loop convertible to the identity drops off the right end of any
composite — `cell ⊟ loop ≈ cell`. -/
theorem quadCohesionLoopContractsOnRight {sourceMode targetMode : QuadCohesionMode}
    {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath)
    {loop : RawTwoCellExpr quadCohesionModeSignature targetPath targetPath}
    (hLoop : QuadCohesionSaturatedTwoCellConv loop
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) targetPath)) :
    QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) cell loop) cell :=
  QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight cell hLoop)
    (quadCohesionConvOfStep (TwoCellStep.vcompIdRight (signature := quadCohesionModeSignature) cell))

/-- **Loop contraction (left)**: an endo-loop convertible to the identity drops off the left end —
`loop ⊟ cell ≈ cell`. -/
theorem quadCohesionLoopContractsOnLeft {sourceMode targetMode : QuadCohesionMode}
    {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    {loop : RawTwoCellExpr quadCohesionModeSignature sourcePath sourcePath}
    (hLoop : QuadCohesionSaturatedTwoCellConv loop
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) sourcePath))
    (cell : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath) :
    QuadCohesionSaturatedTwoCellConv (RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) loop cell) cell :=
  QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft cell hLoop)
    (quadCohesionConvOfStep (TwoCellStep.vcompIdLeft (signature := quadCohesionModeSignature) cell))

/-- **Whiskering the identity 2-cell over the identity 3-cell, saturated** — `id_path ▷ oneCell ≈
id_{path·oneCell}` (the `whiskerRightId` 3-cell lifted with its boundary indices pinned concretely, so
elaboration at use sites never sees a stuck `composePath` index). -/
theorem quadWhiskerRightIdCollapses {sourceMode middleMode targetMode : QuadCohesionMode}
    (path : ModalityPath quadCohesionGraph sourceMode middleMode)
    (oneCell : ModalityPath quadCohesionGraph middleMode targetMode) :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) oneCell
        (RawTwoCellExpr.id (signature := quadCohesionModeSignature) path))
      (RawTwoCellExpr.id (signature := quadCohesionModeSignature) (composePath path oneCell)) :=
  let step := TwoCellStep.whiskerRightId (signature := quadCohesionModeSignature) path oneCell
  quadCohesionConvOfStep step

/-- **Dropping a left identity factor, saturated** — `id ⊟ cell ≈ cell` with the boundary indices pinned
concretely (the `vcompIdLeft` 3-cell, elaboration-robust form). -/
theorem quadVcompIdLeftDrops {sourceMode targetMode : QuadCohesionMode}
    {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath) :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature)
        (RawTwoCellExpr.id (signature := quadCohesionModeSignature) sourcePath) cell) cell :=
  let step := TwoCellStep.vcompIdLeft (signature := quadCohesionModeSignature) cell
  quadCohesionConvOfStep step

/-- **Dropping a right identity factor, saturated** — `cell ⊟ id ≈ cell` (the `vcompIdRight` 3-cell,
elaboration-robust form). -/
theorem quadVcompIdRightDrops {sourceMode targetMode : QuadCohesionMode}
    {sourcePath targetPath : ModalityPath quadCohesionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature sourcePath targetPath) :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) cell
        (RawTwoCellExpr.id (signature := quadCohesionModeSignature) targetPath)) cell :=
  let step := TwoCellStep.vcompIdRight (signature := quadCohesionModeSignature) cell
  quadCohesionConvOfStep step

/-- **Right-associating a vertical composite, saturated** — `(A ⊟ B) ⊟ C ≈ A ⊟ (B ⊟ C)` (the `vcompAssoc`
3-cell, elaboration-robust form: the boundary indices are plain implicit metavariables at use sites, never
stuck `composePath` applications). -/
theorem quadVcompAssocShifts {sourceMode targetMode : QuadCohesionMode}
    {oneCellF oneCellG oneCellH oneCellK : ModalityPath quadCohesionGraph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr quadCohesionModeSignature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr quadCohesionModeSignature oneCellG oneCellH)
    (cellGamma : RawTwoCellExpr quadCohesionModeSignature oneCellH oneCellK) :
    QuadCohesionSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) (RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) cellAlpha cellBeta) cellGamma)
      (RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) cellAlpha (RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) cellBeta cellGamma)) :=
  let step := TwoCellStep.vcompAssoc (signature := quadCohesionModeSignature) cellAlpha cellBeta cellGamma
  quadCohesionConvOfStep step

/-! ## The mate transposition along `Γ ⊣ coDisc` — peel a leading `codisc` -/

/-- Transpose along `Γ ⊣ coDisc`: `Hom(codisc·U, V) → Hom(U, gamma·V)`, by whiskering with `gamma` and
pre-composing the upper unit — the forward mate map of the head-`codisc` peel. -/
def quadMateTransposeAlongCodisc {targetMode : QuadCohesionMode}
    {tailPath : ModalityPath quadCohesionGraph QuadCohesionMode.space targetMode}
    {targetPath : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature (composePath quadCodisc tailPath) targetPath) :
    RawTwoCellExpr quadCohesionModeSignature tailPath (composePath quadGamma targetPath) :=
  show RawTwoCellExpr quadCohesionModeSignature
      (composePath (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space) tailPath)
      (composePath quadGamma targetPath) from
    RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) tailPath quadUnitUpperCell)
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma cell)

/-- Untranspose along `Γ ⊣ coDisc`: `Hom(U, gamma·V) → Hom(codisc·U, V)`, by whiskering with `codisc` and
post-composing the upper counit — the backward mate map. -/
def quadMateUntransposeAlongCodisc {targetMode : QuadCohesionMode}
    {tailPath : ModalityPath quadCohesionGraph QuadCohesionMode.space targetMode}
    {targetPath : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature tailPath (composePath quadGamma targetPath)) :
    RawTwoCellExpr quadCohesionModeSignature (composePath quadCodisc tailPath) targetPath :=
  RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc cell)
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) targetPath quadCounitUpperCell)

/-- The untranspose along `Γ ⊣ coDisc` respects the saturated congruence. -/
theorem quadMateUntransposeAlongCodisc_congr {targetMode : QuadCohesionMode}
    {tailPath : ModalityPath quadCohesionGraph QuadCohesionMode.space targetMode}
    {targetPath : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet targetMode}
    {cellAlpha cellBeta :
      RawTwoCellExpr quadCohesionModeSignature tailPath (composePath quadGamma targetPath)}
    (h : QuadCohesionSaturatedTwoCellConv cellAlpha cellBeta) :
    QuadCohesionSaturatedTwoCellConv (quadMateUntransposeAlongCodisc cellAlpha)
      (quadMateUntransposeAlongCodisc cellBeta) :=
  QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadCodisc h)

/-- ★ **Retract round-trip of the `codisc`-peel**: untransposing the transpose recovers the cell —
`(codisc ◁ ((η'' ▷ U) ⊟ (gamma ◁ cell))) ⊟ (ε'' ▷ V) ≈ cell`.  Split the whiskers, slide the upper counit
past the cell with the exchange square, and straighten the leftover `codisc`-snake with `triCodisc`. -/
theorem quadMateAlongCodisc_retract {targetMode : QuadCohesionMode}
    {tailPath : ModalityPath quadCohesionGraph QuadCohesionMode.space targetMode}
    {targetPath : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature (composePath quadCodisc tailPath) targetPath) :
    QuadCohesionSaturatedTwoCellConv
      (quadMateUntransposeAlongCodisc (quadMateTransposeAlongCodisc cell)) cell := by
  dsimp only [quadMateUntransposeAlongCodisc, quadMateTransposeAlongCodisc]
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (quadCohesionConvOfStep (TwoCellStep.whiskerLeftVcomp (signature := quadCohesionModeSignature) quadCodisc
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) tailPath quadUnitUpperCell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma cell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (quadVcompAssocShifts
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) tailPath quadUnitUpperCell))
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma cell))
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) targetPath quadCounitUpperCell)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.symm
          (QuadCohesionSaturatedTwoCellConv.ofFull
            (TwoCellConvFull.whiskerLeftComp (signature := quadCohesionModeSignature) quadCodisc quadGamma cell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.symm
        (quadCohesionExchangeSquare quadCounitUpperCell cell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
        (QuadCohesionSaturatedTwoCellConv.ofFull (TwoCellConvFull.whiskerLeftUnit (signature := quadCohesionModeSignature) cell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadVcompAssocShifts
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) tailPath quadUnitUpperCell))
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) (composePath quadCodisc tailPath) quadCounitUpperCell)
        cell)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft cell
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerExchange (signature := quadCohesionModeSignature) quadCodisc tailPath quadUnitUpperCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft cell
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerRightComp (signature := quadCohesionModeSignature) quadCodisc tailPath quadCounitUpperCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft cell
      (QuadCohesionSaturatedTwoCellConv.symm
        (quadCohesionConvOfStep (TwoCellStep.whiskerRightVcomp (signature := quadCohesionModeSignature) tailPath
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc quadUnitUpperCell)
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadCounitUpperCell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft cell
      (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr tailPath
        QuadCohesionSaturatedTwoCellConv.triCodisc)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft cell
      (quadWhiskerRightIdCollapses quadCodisc tailPath)) ?_
  exact quadVcompIdLeftDrops cell

/-- ★ **Section round-trip of the `codisc`-peel**: transposing the untranspose recovers the cell —
`(η'' ▷ U) ⊟ (gamma ◁ ((codisc ◁ cell) ⊟ (ε'' ▷ V))) ≈ cell`.  The mirror derivation, straightening the
leftover `gamma`-snake with `triGammaHi`. -/
theorem quadMateAlongCodisc_section {targetMode : QuadCohesionMode}
    {tailPath : ModalityPath quadCohesionGraph QuadCohesionMode.space targetMode}
    {targetPath : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature tailPath (composePath quadGamma targetPath)) :
    QuadCohesionSaturatedTwoCellConv
      (quadMateTransposeAlongCodisc (quadMateUntransposeAlongCodisc cell)) cell := by
  dsimp only [quadMateUntransposeAlongCodisc, quadMateTransposeAlongCodisc]
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (quadCohesionConvOfStep (TwoCellStep.whiskerLeftVcomp (signature := quadCohesionModeSignature) quadGamma
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc cell)
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) targetPath quadCounitUpperCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.symm
          (QuadCohesionSaturatedTwoCellConv.ofFull
            (TwoCellConvFull.whiskerLeftComp (signature := quadCohesionModeSignature) quadGamma quadCodisc cell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadVcompAssocShifts
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) tailPath quadUnitUpperCell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGammaCodisc cell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) targetPath quadCounitUpperCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (quadCohesionExchangeSquare quadUnitUpperCell cell)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.ofFull (TwoCellConvFull.whiskerLeftUnit (signature := quadCohesionModeSignature) cell)))) ?_
  let unitInsertionLayer :=
    RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) (composePath quadGamma targetPath) quadUnitUpperCell
  let counitCapLayer :=
    RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) targetPath quadCounitUpperCell)
  have hUnitSplits := QuadCohesionSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerRightComp (signature := quadCohesionModeSignature)
      quadGamma targetPath quadUnitUpperCell)
  have hCapExchanges := QuadCohesionSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerExchange (signature := quadCohesionModeSignature)
      quadGamma targetPath quadCounitUpperCell)
  have hSnakeFolds := QuadCohesionSaturatedTwoCellConv.symm (quadCohesionConvOfStep
    (TwoCellStep.whiskerRightVcomp (signature := quadCohesionModeSignature) targetPath
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadUnitUpperCell)
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma quadCounitUpperCell)))
  refine QuadCohesionSaturatedTwoCellConv.trans
    (quadVcompAssocShifts cell unitInsertionLayer counitCapLayer) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight cell
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _ hUnitSplits)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight cell
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _ hCapExchanges)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight cell hSnakeFolds) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight cell
      (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr targetPath
        QuadCohesionSaturatedTwoCellConv.triGammaHi)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight cell
      (quadWhiskerRightIdCollapses quadGamma targetPath)) ?_
  exact quadVcompIdRightDrops cell

/-! ## The mate transposition along `Disc ⊣ Γ` — peel a leading `gamma` -/

/-- Transpose along `Disc ⊣ Γ`: `Hom(gamma·U, V) → Hom(U, disc·V)`. -/
def quadMateTransposeAlongGamma {targetMode : QuadCohesionMode}
    {tailPath : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet targetMode}
    {targetPath : ModalityPath quadCohesionGraph QuadCohesionMode.space targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature (composePath quadGamma tailPath) targetPath) :
    RawTwoCellExpr quadCohesionModeSignature tailPath (composePath quadDisc targetPath) :=
  show RawTwoCellExpr quadCohesionModeSignature
      (composePath (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) tailPath)
      (composePath quadDisc targetPath) from
    RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) tailPath quadUnitMiddleCell)
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc cell)

/-- Untranspose along `Disc ⊣ Γ`: `Hom(U, disc·V) → Hom(gamma·U, V)`. -/
def quadMateUntransposeAlongGamma {targetMode : QuadCohesionMode}
    {tailPath : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet targetMode}
    {targetPath : ModalityPath quadCohesionGraph QuadCohesionMode.space targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature tailPath (composePath quadDisc targetPath)) :
    RawTwoCellExpr quadCohesionModeSignature (composePath quadGamma tailPath) targetPath :=
  RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma cell)
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) targetPath quadCounitMiddleCell)

/-- The untranspose along `Disc ⊣ Γ` respects the saturated congruence. -/
theorem quadMateUntransposeAlongGamma_congr {targetMode : QuadCohesionMode}
    {tailPath : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet targetMode}
    {targetPath : ModalityPath quadCohesionGraph QuadCohesionMode.space targetMode}
    {cellAlpha cellBeta :
      RawTwoCellExpr quadCohesionModeSignature tailPath (composePath quadDisc targetPath)}
    (h : QuadCohesionSaturatedTwoCellConv cellAlpha cellBeta) :
    QuadCohesionSaturatedTwoCellConv (quadMateUntransposeAlongGamma cellAlpha)
      (quadMateUntransposeAlongGamma cellBeta) :=
  QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
    (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadGamma h)

/-- ★ **Retract round-trip of the `gamma`-peel** — straightens with `triGammaLo`. -/
theorem quadMateAlongGamma_retract {targetMode : QuadCohesionMode}
    {tailPath : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet targetMode}
    {targetPath : ModalityPath quadCohesionGraph QuadCohesionMode.space targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature (composePath quadGamma tailPath) targetPath) :
    QuadCohesionSaturatedTwoCellConv
      (quadMateUntransposeAlongGamma (quadMateTransposeAlongGamma cell)) cell := by
  dsimp only [quadMateUntransposeAlongGamma, quadMateTransposeAlongGamma]
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (quadCohesionConvOfStep (TwoCellStep.whiskerLeftVcomp (signature := quadCohesionModeSignature) quadGamma
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) tailPath quadUnitMiddleCell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc cell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (quadVcompAssocShifts
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) tailPath quadUnitMiddleCell))
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc cell))
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) targetPath quadCounitMiddleCell)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.symm
          (QuadCohesionSaturatedTwoCellConv.ofFull
            (TwoCellConvFull.whiskerLeftComp (signature := quadCohesionModeSignature) quadGamma quadDisc cell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.symm
        (quadCohesionExchangeSquare quadCounitMiddleCell cell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
        (QuadCohesionSaturatedTwoCellConv.ofFull (TwoCellConvFull.whiskerLeftUnit (signature := quadCohesionModeSignature) cell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadVcompAssocShifts
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) tailPath quadUnitMiddleCell))
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) (composePath quadGamma tailPath) quadCounitMiddleCell)
        cell)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft cell
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerExchange (signature := quadCohesionModeSignature) quadGamma tailPath quadUnitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft cell
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerRightComp (signature := quadCohesionModeSignature) quadGamma tailPath quadCounitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft cell
      (QuadCohesionSaturatedTwoCellConv.symm
        (quadCohesionConvOfStep (TwoCellStep.whiskerRightVcomp (signature := quadCohesionModeSignature) tailPath
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma quadUnitMiddleCell)
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadCounitMiddleCell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft cell
      (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr tailPath
        QuadCohesionSaturatedTwoCellConv.triGammaLo)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft cell
      (quadWhiskerRightIdCollapses quadGamma tailPath)) ?_
  exact quadVcompIdLeftDrops cell

/-- ★ **Section round-trip of the `gamma`-peel** — straightens with `triDiscHi`. -/
theorem quadMateAlongGamma_section {targetMode : QuadCohesionMode}
    {tailPath : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet targetMode}
    {targetPath : ModalityPath quadCohesionGraph QuadCohesionMode.space targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature tailPath (composePath quadDisc targetPath)) :
    QuadCohesionSaturatedTwoCellConv
      (quadMateTransposeAlongGamma (quadMateUntransposeAlongGamma cell)) cell := by
  dsimp only [quadMateUntransposeAlongGamma, quadMateTransposeAlongGamma]
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (quadCohesionConvOfStep (TwoCellStep.whiskerLeftVcomp (signature := quadCohesionModeSignature) quadDisc
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma cell)
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) targetPath quadCounitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.symm
          (QuadCohesionSaturatedTwoCellConv.ofFull
            (TwoCellConvFull.whiskerLeftComp (signature := quadCohesionModeSignature) quadDisc quadGamma cell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadVcompAssocShifts
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) tailPath quadUnitMiddleCell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDiscGamma cell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) targetPath quadCounitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (quadCohesionExchangeSquare quadUnitMiddleCell cell)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.ofFull (TwoCellConvFull.whiskerLeftUnit (signature := quadCohesionModeSignature) cell)))) ?_
  let unitInsertionLayer :=
    RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) (composePath quadDisc targetPath) quadUnitMiddleCell
  let counitCapLayer :=
    RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) targetPath quadCounitMiddleCell)
  have hUnitSplits := QuadCohesionSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerRightComp (signature := quadCohesionModeSignature)
      quadDisc targetPath quadUnitMiddleCell)
  have hCapExchanges := QuadCohesionSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerExchange (signature := quadCohesionModeSignature)
      quadDisc targetPath quadCounitMiddleCell)
  have hSnakeFolds := QuadCohesionSaturatedTwoCellConv.symm (quadCohesionConvOfStep
    (TwoCellStep.whiskerRightVcomp (signature := quadCohesionModeSignature) targetPath
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc quadUnitMiddleCell)
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc quadCounitMiddleCell)))
  refine QuadCohesionSaturatedTwoCellConv.trans
    (quadVcompAssocShifts cell unitInsertionLayer counitCapLayer) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight cell
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _ hUnitSplits)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight cell
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _ hCapExchanges)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight cell hSnakeFolds) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight cell
      (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr targetPath
        QuadCohesionSaturatedTwoCellConv.triDiscHi)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight cell
      (quadWhiskerRightIdCollapses quadDisc targetPath)) ?_
  exact quadVcompIdRightDrops cell

/-! ## The mate transposition along `Π₀ ⊣ Disc` — peel a leading `disc` -/

/-- Transpose along `Π₀ ⊣ Disc`: `Hom(disc·U, V) → Hom(U, pi0·V)`. -/
def quadMateTransposeAlongDisc {targetMode : QuadCohesionMode}
    {tailPath : ModalityPath quadCohesionGraph QuadCohesionMode.space targetMode}
    {targetPath : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature (composePath quadDisc tailPath) targetPath) :
    RawTwoCellExpr quadCohesionModeSignature tailPath (composePath quadPi0 targetPath) :=
  show RawTwoCellExpr quadCohesionModeSignature
      (composePath (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space) tailPath)
      (composePath quadPi0 targetPath) from
    RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) tailPath quadUnitLowerCell)
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 cell)

/-- Untranspose along `Π₀ ⊣ Disc`: `Hom(U, pi0·V) → Hom(disc·U, V)`. -/
def quadMateUntransposeAlongDisc {targetMode : QuadCohesionMode}
    {tailPath : ModalityPath quadCohesionGraph QuadCohesionMode.space targetMode}
    {targetPath : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature tailPath (composePath quadPi0 targetPath)) :
    RawTwoCellExpr quadCohesionModeSignature (composePath quadDisc tailPath) targetPath :=
  RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc cell)
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) targetPath quadCounitLowerCell)

/-- ★ **Retract round-trip of the `disc`-peel** — straightens with `triDiscLo`. -/
theorem quadMateAlongDisc_retract {targetMode : QuadCohesionMode}
    {tailPath : ModalityPath quadCohesionGraph QuadCohesionMode.space targetMode}
    {targetPath : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature (composePath quadDisc tailPath) targetPath) :
    QuadCohesionSaturatedTwoCellConv
      (quadMateUntransposeAlongDisc (quadMateTransposeAlongDisc cell)) cell := by
  dsimp only [quadMateUntransposeAlongDisc, quadMateTransposeAlongDisc]
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (quadCohesionConvOfStep (TwoCellStep.whiskerLeftVcomp (signature := quadCohesionModeSignature) quadDisc
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) tailPath quadUnitLowerCell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 cell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (quadVcompAssocShifts
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) tailPath quadUnitLowerCell))
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 cell))
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) targetPath quadCounitLowerCell)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.symm
          (QuadCohesionSaturatedTwoCellConv.ofFull
            (TwoCellConvFull.whiskerLeftComp (signature := quadCohesionModeSignature) quadDisc quadPi0 cell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.symm
        (quadCohesionExchangeSquare quadCounitLowerCell cell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
        (QuadCohesionSaturatedTwoCellConv.ofFull (TwoCellConvFull.whiskerLeftUnit (signature := quadCohesionModeSignature) cell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadVcompAssocShifts
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) tailPath quadUnitLowerCell))
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) (composePath quadDisc tailPath) quadCounitLowerCell)
        cell)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft cell
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerExchange (signature := quadCohesionModeSignature) quadDisc tailPath quadUnitLowerCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft cell
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerRightComp (signature := quadCohesionModeSignature) quadDisc tailPath quadCounitLowerCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft cell
      (QuadCohesionSaturatedTwoCellConv.symm
        (quadCohesionConvOfStep (TwoCellStep.whiskerRightVcomp (signature := quadCohesionModeSignature) tailPath
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc quadUnitLowerCell)
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc quadCounitLowerCell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft cell
      (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr tailPath
        QuadCohesionSaturatedTwoCellConv.triDiscLo)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft cell
      (quadWhiskerRightIdCollapses quadDisc tailPath)) ?_
  exact quadVcompIdLeftDrops cell

/-- ★ **Section round-trip of the `disc`-peel** — straightens with `triPi0`. -/
theorem quadMateAlongDisc_section {targetMode : QuadCohesionMode}
    {tailPath : ModalityPath quadCohesionGraph QuadCohesionMode.space targetMode}
    {targetPath : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet targetMode}
    (cell : RawTwoCellExpr quadCohesionModeSignature tailPath (composePath quadPi0 targetPath)) :
    QuadCohesionSaturatedTwoCellConv
      (quadMateTransposeAlongDisc (quadMateUntransposeAlongDisc cell)) cell := by
  dsimp only [quadMateUntransposeAlongDisc, quadMateTransposeAlongDisc]
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (quadCohesionConvOfStep (TwoCellStep.whiskerLeftVcomp (signature := quadCohesionModeSignature) quadPi0
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc cell)
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) targetPath quadCounitLowerCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.symm
          (QuadCohesionSaturatedTwoCellConv.ofFull
            (TwoCellConvFull.whiskerLeftComp (signature := quadCohesionModeSignature) quadPi0 quadDisc cell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadVcompAssocShifts
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) tailPath quadUnitLowerCell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0Disc cell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) targetPath quadCounitLowerCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (quadCohesionExchangeSquare quadUnitLowerCell cell)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.ofFull (TwoCellConvFull.whiskerLeftUnit (signature := quadCohesionModeSignature) cell)))) ?_
  let unitInsertionLayer :=
    RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) (composePath quadPi0 targetPath) quadUnitLowerCell
  let counitCapLayer :=
    RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) targetPath quadCounitLowerCell)
  have hUnitSplits := QuadCohesionSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerRightComp (signature := quadCohesionModeSignature)
      quadPi0 targetPath quadUnitLowerCell)
  have hCapExchanges := QuadCohesionSaturatedTwoCellConv.ofFull
    (TwoCellConvFull.whiskerExchange (signature := quadCohesionModeSignature)
      quadPi0 targetPath quadCounitLowerCell)
  have hSnakeFolds := QuadCohesionSaturatedTwoCellConv.symm (quadCohesionConvOfStep
    (TwoCellStep.whiskerRightVcomp (signature := quadCohesionModeSignature) targetPath
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0 quadUnitLowerCell)
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 quadCounitLowerCell)))
  refine QuadCohesionSaturatedTwoCellConv.trans
    (quadVcompAssocShifts cell unitInsertionLayer counitCapLayer) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight cell
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _ hUnitSplits)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight cell
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _ hCapExchanges)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight cell hSnakeFolds) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight cell
      (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr targetPath
        QuadCohesionSaturatedTwoCellConv.triPi0)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight cell
      (quadWhiskerRightIdCollapses quadPi0 targetPath)) ?_
  exact quadVcompIdRightDrops cell

/-! ## The tail-side transpose at the `disc ⇒ codisc` boundary (the concrete instance the joins consume)

The tail-side peels over an ARBITRARY left word would need `composePath`-reassociation casts, so the kit ships
the tail transpose at the concrete boundary where the derived-comparison joins fire: `Hom(disc, codisc)`. -/

/-- Tail-transpose along `Disc ⊣ Γ` at the comparison boundary:
`Hom(disc, codisc) → Hom(id_P, codisc·gamma)`, by right-whiskering with `gamma` and pre-composing the middle
unit. -/
def quadMateTailTransposeDiscToCodisc
    (cell : RawTwoCellExpr quadCohesionModeSignature quadDisc quadCodisc) :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) quadCodiscGamma :=
  let whiskeredComparison := RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma cell
  show RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet)
      (composePath quadCodisc quadGamma) from
    RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) quadUnitMiddleCell whiskeredComparison

/-- Tail-untranspose along `Disc ⊣ Γ` at the comparison boundary:
`Hom(id_P, codisc·gamma) → Hom(disc, codisc)`, by right-whiskering with `disc` and post-composing the middle
counit. -/
def quadMateTailUntransposeDiscToCodisc
    (cell : RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) quadCodiscGamma) :
    RawTwoCellExpr quadCohesionModeSignature quadDisc quadCodisc :=
  let whiskeredCup := RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc cell
  let capLayer := RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc quadCounitMiddleCell
  show RawTwoCellExpr quadCohesionModeSignature
      (composePath (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) quadDisc)
      (composePath quadCodisc (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space)) from
    RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) whiskeredCup capLayer

/-- The tail-untranspose respects the saturated congruence. -/
theorem quadMateTailUntransposeDiscToCodisc_congr
    {cellAlpha cellBeta : RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) quadCodiscGamma}
    (h : QuadCohesionSaturatedTwoCellConv cellAlpha cellBeta) :
    QuadCohesionSaturatedTwoCellConv (quadMateTailUntransposeDiscToCodisc cellAlpha)
      (quadMateTailUntransposeDiscToCodisc cellBeta) :=
  QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
    (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadDisc h)

/-- ★ **Retract round-trip of the tail-`disc` transpose**: untransposing the transpose recovers the cell —
`((η' ⊟ (cell ▷ gamma)) ▷ disc) ⊟ (codisc ◁ ε') ≈ cell`.  Slide the middle counit past the cell with the
exchange square and straighten the leftover `disc`-snake with `triDiscHi`. -/
theorem quadMateTailDiscToCodisc_retract
    (cell : RawTwoCellExpr quadCohesionModeSignature quadDisc quadCodisc) :
    QuadCohesionSaturatedTwoCellConv
      (quadMateTailUntransposeDiscToCodisc (quadMateTailTransposeDiscToCodisc cell)) cell := by
  dsimp only [quadMateTailUntransposeDiscToCodisc, quadMateTailTransposeDiscToCodisc]
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (quadCohesionConvOfStep (TwoCellStep.whiskerRightVcomp (signature := quadCohesionModeSignature) quadDisc quadUnitMiddleCell
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma cell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
        (QuadCohesionSaturatedTwoCellConv.symm
          (QuadCohesionSaturatedTwoCellConv.ofFull
            (TwoCellConvFull.whiskerRightComp (signature := quadCohesionModeSignature) quadGamma quadDisc cell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (quadVcompAssocShifts
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc quadUnitMiddleCell)
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) (composePath quadGamma quadDisc) cell)
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc quadCounitMiddleCell)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (quadCohesionExchangeSquare cell quadCounitMiddleCell)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadVcompAssocShifts
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc quadUnitMiddleCell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc quadCounitMiddleCell)
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature)
          (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space) cell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      QuadCohesionSaturatedTwoCellConv.triDiscHi) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (quadVcompIdLeftDrops (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature)
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space) cell)) ?_
  exact QuadCohesionSaturatedTwoCellConv.ofFull (TwoCellConvFull.whiskerRightUnit (signature := quadCohesionModeSignature) cell)

/-! ## The points-to-pieces join — the comparison `Γ ⇒ Π₀` is unique -/

/-- The **points-to-pieces transform via the lower unit**: `gamma ⇒(η ▷ gamma) pi0·disc·gamma ⇒(pi0 ◁ η'⁻¹)
pi0` — the route through `Π₀ ⊣ Disc`'s unit and the `Disc`-ff middle-unit inverse. -/
def quadPointsToPiecesViaUnitCell :
    RawTwoCellExpr quadCohesionModeSignature quadGamma quadPi0 :=
  RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadUnitLowerCell)
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 quadInvUnitMiddleCell)

/-- The **points-to-pieces transform via the middle counit**: `gamma ⇒(gamma ◁ ε⁻¹) gamma·disc·pi0
⇒(ε' ▷ pi0) pi0` — the route through the `Disc`-ff lower-counit inverse and `Disc ⊣ Γ`'s counit. -/
def quadPointsToPiecesViaCounitCell :
    RawTwoCellExpr quadCohesionModeSignature quadGamma quadPi0 :=
  RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma quadInvCounitLowerCell)
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0 quadCounitMiddleCell)

/-- The `gamma`-transpose of the unit-route points-to-pieces collapses to the lower-counit INVERSE — the
computational heart of the join: transposing turns the parallel pair question into a hom where the shipped
wave-1 straddle join (`quadStraddleDiscUnitInvCounitJoin`) and the ff-iso rows decide everything. -/
theorem quadPointsToPiecesTransposeCollapses :
    QuadCohesionSaturatedTwoCellConv
      (quadMateTransposeAlongGamma
        (tailPath := ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet)
        (targetPath := quadPi0) quadPointsToPiecesViaUnitCell)
      quadInvCounitLowerCell := by
  dsimp only [quadMateTransposeAlongGamma, quadPointsToPiecesViaUnitCell]
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (QuadCohesionSaturatedTwoCellConv.ofFull
        (TwoCellConvFull.whiskerRightUnit (signature := quadCohesionModeSignature) quadUnitMiddleCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (quadCohesionConvOfStep (TwoCellStep.whiskerLeftVcomp (signature := quadCohesionModeSignature) quadDisc
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadGamma quadUnitLowerCell)
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 quadInvUnitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerExchange (signature := quadCohesionModeSignature) quadDisc quadGamma quadUnitLowerCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadGamma
          quadStraddleDiscUnitInvCounitJoin))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.symm
          (QuadCohesionSaturatedTwoCellConv.ofFull
            (TwoCellConvFull.whiskerRightComp (signature := quadCohesionModeSignature) quadDisc quadGamma quadInvCounitLowerCell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
        (QuadCohesionSaturatedTwoCellConv.symm
          (QuadCohesionSaturatedTwoCellConv.ofFull
            (TwoCellConvFull.whiskerLeftComp (signature := quadCohesionModeSignature) quadDisc quadPi0 quadInvUnitMiddleCell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (quadCohesionExchangeSquare quadInvCounitLowerCell quadInvUnitMiddleCell)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerLeftUnit (signature := quadCohesionModeSignature) quadInvUnitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerRightUnit (signature := quadCohesionModeSignature) quadInvCounitLowerCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.vcompAssoc (signature := quadCohesionModeSignature) quadUnitMiddleCell quadInvUnitMiddleCell quadInvCounitLowerCell))) ?_
  exact quadCohesionLoopContractsOnLeft
    QuadCohesionSaturatedTwoCellConv.isoMiddleUnitRight quadInvCounitLowerCell

/-- ★★ **THE POINTS-TO-PIECES JOIN** — the two constructions of the canonical comparison `Γ ⇒ Π₀` are
convertible: `(η ▷ gamma) ⊟ (pi0 ◁ η'⁻¹) ≈ (gamma ◁ ε⁻¹) ⊟ (ε' ▷ pi0)`.  nLab (*cohesive topos*) proves the
two routes agree in every cohesive topos; the free quadruple already forces it.  Proof: the `gamma`-peel is a
bijection up to conversion (`quadMateAlongGamma_retract`), the transpose of the unit route collapses to
`invCounitLower` (`quadPointsToPiecesTransposeCollapses`), and untransposing `invCounitLower` IS the counit
route on the nose. -/
theorem quadPointsToPiecesJoin :
    QuadCohesionSaturatedTwoCellConv quadPointsToPiecesViaUnitCell quadPointsToPiecesViaCounitCell := by
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadMateAlongGamma_retract
        (tailPath := ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet)
        (targetPath := quadPi0) quadPointsToPiecesViaUnitCell)) ?_
  exact quadMateUntransposeAlongGamma_congr quadPointsToPiecesTransposeCollapses

/-! ## The discrete-to-codiscrete join — the comparison `Disc ⇒ coDisc` is unique -/

/-- The **discrete-to-codiscrete comparison via the upper unit**: `disc ⇒(disc ◁ η'') disc·gamma·codisc
⇒(η'⁻¹ ▷ codisc) codisc`. -/
def quadDiscreteToCodiscreteViaUpperCell :
    RawTwoCellExpr quadCohesionModeSignature quadDisc quadCodisc :=
  RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc quadUnitUpperCell)
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadInvUnitMiddleCell)

/-- The **discrete-to-codiscrete comparison via the middle counit**: `disc ⇒(ε''⁻¹ ▷ disc)
codisc·gamma·disc ⇒(codisc ◁ ε') codisc`. -/
def quadDiscreteToCodiscreteViaMiddleCell :
    RawTwoCellExpr quadCohesionModeSignature quadDisc quadCodisc :=
  RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc quadInvCounitUpperCell)
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc quadCounitMiddleCell)

/-- The tail-transpose of the upper-route discrete-to-codiscrete collapses to the upper-counit INVERSE —
decided by the shipped wave-2 `gamma`-leg join (`quadStraddleGammaUnitUpperInvCounitJoin`) plus the ff-iso
rows. -/
theorem quadDiscreteToCodiscreteTransposeCollapses :
    QuadCohesionSaturatedTwoCellConv
      (quadMateTailTransposeDiscToCodisc quadDiscreteToCodiscreteViaUpperCell)
      quadInvCounitUpperCell := by
  dsimp only [quadMateTailTransposeDiscToCodisc, quadDiscreteToCodiscreteViaUpperCell]
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (quadCohesionConvOfStep (TwoCellStep.whiskerRightVcomp (signature := quadCohesionModeSignature) quadGamma
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc quadUnitUpperCell)
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadInvUnitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.symm
          (QuadCohesionSaturatedTwoCellConv.ofFull
            (TwoCellConvFull.whiskerExchange (signature := quadCohesionModeSignature) quadDisc quadGamma quadUnitUpperCell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadDisc
          quadStraddleGammaUnitUpperInvCounitJoin))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.symm
          (QuadCohesionSaturatedTwoCellConv.ofFull
            (TwoCellConvFull.whiskerLeftComp (signature := quadCohesionModeSignature) quadDisc quadGamma quadInvCounitUpperCell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
        (QuadCohesionSaturatedTwoCellConv.symm
          (QuadCohesionSaturatedTwoCellConv.ofFull
            (TwoCellConvFull.whiskerRightComp (signature := quadCohesionModeSignature) quadCodisc quadGamma quadInvUnitMiddleCell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.symm
        (quadCohesionExchangeSquare quadInvUnitMiddleCell quadInvCounitUpperCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerRightUnit (signature := quadCohesionModeSignature) quadInvUnitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerLeftUnit (signature := quadCohesionModeSignature) quadInvCounitUpperCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadCohesionConvOfStep
        (TwoCellStep.vcompAssoc (signature := quadCohesionModeSignature) quadUnitMiddleCell quadInvUnitMiddleCell quadInvCounitUpperCell))) ?_
  exact quadCohesionLoopContractsOnLeft
    QuadCohesionSaturatedTwoCellConv.isoMiddleUnitRight quadInvCounitUpperCell

/-- ★★ **THE DISCRETE-TO-CODISCRETE JOIN** — the two constructions of the canonical comparison
`Disc ⇒ coDisc` are convertible: `(disc ◁ η'') ⊟ (η'⁻¹ ▷ codisc) ≈ (ε''⁻¹ ▷ disc) ⊟ (codisc ◁ ε')`.  The dual
of the points-to-pieces join, decided through the tail-`disc` transpose. -/
theorem quadDiscreteToCodiscreteJoin :
    QuadCohesionSaturatedTwoCellConv quadDiscreteToCodiscreteViaUpperCell
      quadDiscreteToCodiscreteViaMiddleCell := by
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadMateTailDiscToCodisc_retract quadDiscreteToCodiscreteViaUpperCell)) ?_
  exact quadMateTailUntransposeDiscToCodisc_congr quadDiscreteToCodiscreteTransposeCollapses

/-! ## The residual derived-cup join — the point of `w = codisc·pi0` is unique -/

/-- The RESIDUAL 1-cell `w = codisc·pi0` (`Π₀ ∘ coDisc` classically) — the ONLY `pointSet`-endo letter pair
NOT collapsed by an ff iso (`disc·pi0`, `disc·gamma`, `codisc·gamma` all are).  Up to the ff isos every
`pointSet`-endo word is a power `w^n`, so this is the residual generator the free-word normalizer must
canonicalize. -/
def quadCodiscPi0 : ModalityPath quadCohesionGraph QuadCohesionMode.pointSet QuadCohesionMode.pointSet :=
  composePath quadCodisc quadPi0

/-- The **derived cup via the upper iso**: `id_P ⇒(ε''⁻¹) codisc·gamma ⇒(codisc ◁ ptp) codisc·pi0` — the
upper-counit inverse followed by the whiskered points-to-pieces transform (counit form). -/
def quadResidualCupViaUpperCell :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) quadCodiscPi0 :=
  RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) quadInvCounitUpperCell
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc quadPointsToPiecesViaCounitCell)

/-- The **derived cup via the lower iso**: `id_P ⇒(ε⁻¹) disc·pi0 ⇒(dtc ▷ pi0) codisc·pi0` — the lower-counit
inverse followed by the whiskered discrete-to-codiscrete comparison (middle form). -/
def quadResidualCupViaLowerCell :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) quadCodiscPi0 :=
  RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) quadInvCounitLowerCell
    (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0 quadDiscreteToCodiscreteViaMiddleCell)

/-- ★★ **THE RESIDUAL DERIVED-CUP JOIN** — the two derived cups `id_P ⇒ codisc·pi0` are convertible: the
residual generator `w` carries ONE canonical point `u`, whether built through the upper or the lower ff iso.
Proof: expand the whiskers, slide the two iso-cups past each other with the exchange square, and refold — no
transposition needed. -/
theorem quadResidualCupJoin :
    QuadCohesionSaturatedTwoCellConv quadResidualCupViaUpperCell quadResidualCupViaLowerCell := by
  dsimp only [quadResidualCupViaUpperCell, quadResidualCupViaLowerCell,
    quadPointsToPiecesViaCounitCell, quadDiscreteToCodiscreteViaMiddleCell]
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (quadCohesionConvOfStep (TwoCellStep.whiskerLeftVcomp (signature := quadCohesionModeSignature) quadCodisc
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadGamma quadInvCounitLowerCell)
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0 quadCounitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.symm
          (QuadCohesionSaturatedTwoCellConv.ofFull
            (TwoCellConvFull.whiskerLeftComp (signature := quadCohesionModeSignature) quadCodisc quadGamma quadInvCounitLowerCell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerExchange (signature := quadCohesionModeSignature) quadCodisc quadPi0 quadCounitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.symm
      (quadVcompAssocShifts quadInvCounitUpperCell
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) (composePath quadCodisc quadGamma) quadInvCounitLowerCell)
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc quadCounitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.symm
          (QuadCohesionSaturatedTwoCellConv.ofFull
            (TwoCellConvFull.whiskerRightUnit (signature := quadCohesionModeSignature) quadInvCounitUpperCell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (quadCohesionExchangeSquare quadInvCounitUpperCell quadInvCounitLowerCell)) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerLeftUnit (signature := quadCohesionModeSignature) quadInvCounitLowerCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (quadVcompAssocShifts quadInvCounitLowerCell
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDiscPi0 quadInvCounitUpperCell)
      (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadPi0
        (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc quadCounitMiddleCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.vcompCongrLeft _
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerRightComp (signature := quadCohesionModeSignature) quadDisc quadPi0 quadInvCounitUpperCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.symm
        (quadCohesionConvOfStep (TwoCellStep.whiskerRightVcomp (signature := quadCohesionModeSignature) quadPi0
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadDisc quadInvCounitUpperCell)
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodisc quadCounitMiddleCell))))) ?_
  exact QuadCohesionSaturatedTwoCellConv.refl _

/-! ## The nested-vs-side-by-side cross-matching join at `id_space ⇒ pi0·disc·gamma·codisc` -/

/-- The `space`-endo residual 1-cell `q = pi0·codisc` (`coDisc ∘ Π₀` classically) — the `space`-side twin of
`w`, the codomain of the derived cross-cup. -/
def quadPi0Codisc : ModalityPath quadCohesionGraph QuadCohesionMode.space QuadCohesionMode.space :=
  composePath quadPi0 quadCodisc

/-- The **side-by-side double cup** `id_S ⇒ pi0·disc·gamma·codisc`: the lower unit, then the upper unit
inserted after it — the matching `{(pi0,disc), (gamma,codisc)}`. -/
def quadCrossCupSideBySideCell :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space)
      (composePath quadPi0Disc quadGammaCodisc) :=
  RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) quadUnitLowerCell (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0Disc quadUnitUpperCell)

/-- The **derived cross-cup** `id_S ⇒ pi0·codisc`: the lower unit with the discrete-to-codiscrete comparison
(upper form) whiskered inside — the outer pair of the nested matching. -/
def quadCrossCupCell :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space) quadPi0Codisc :=
  RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) quadUnitLowerCell
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 quadDiscreteToCodiscreteViaUpperCell)

/-- The **nested double cup** `id_S ⇒ pi0·disc·gamma·codisc`: the derived cross-cup, then the middle unit
inserted INSIDE it — the matching `{(pi0,codisc), (disc,gamma)}`. -/
def quadCrossCupNestedCell :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.space)
      (composePath quadPi0Disc quadGammaCodisc) :=
  RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) quadCrossCupCell
    (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0 (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadUnitMiddleCell))

/-- ★★ **THE CROSS-MATCHING JOIN** — the nested and side-by-side matchings of
`id_space ⇒ pi0·disc·gamma·codisc` are convertible.  The inner middle-unit cup annihilates against the
comparison's middle-unit INVERSE (`isoMiddleUnitLeft` under the whiskers), leaving exactly the side-by-side
double cup.  This is the cross-adjunction critical pair of the would-be planar-matching normal form, joined. -/
theorem quadCrossMatchingJoin :
    QuadCohesionSaturatedTwoCellConv quadCrossCupNestedCell quadCrossCupSideBySideCell := by
  dsimp only [quadCrossCupNestedCell, quadCrossCupCell, quadCrossCupSideBySideCell,
    quadDiscreteToCodiscreteViaUpperCell]
  refine QuadCohesionSaturatedTwoCellConv.trans
    (quadVcompAssocShifts quadUnitLowerCell
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0
        (RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc quadUnitUpperCell)
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadInvUnitMiddleCell)))
      (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadPi0
        (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadUnitMiddleCell))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.symm
        (quadCohesionConvOfStep (TwoCellStep.whiskerLeftVcomp (signature := quadCohesionModeSignature) quadPi0
          (RawTwoCellExpr.vcomp (signature := quadCohesionModeSignature) (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc quadUnitUpperCell)
            (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadInvUnitMiddleCell))
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadUnitMiddleCell))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadPi0
        (quadVcompAssocShifts
          (RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadDisc quadUnitUpperCell)
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadInvUnitMiddleCell)
          (RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodisc quadUnitMiddleCell)))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadPi0
        (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
          (QuadCohesionSaturatedTwoCellConv.symm
            (quadCohesionConvOfStep
              (TwoCellStep.whiskerRightVcomp (signature := quadCohesionModeSignature) quadCodisc quadInvUnitMiddleCell
                quadUnitMiddleCell)))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.whiskerLeftCongr quadPi0
        (quadCohesionLoopContractsOnRight _
          (QuadCohesionSaturatedTwoCellConv.trans
            (QuadCohesionSaturatedTwoCellConv.whiskerRightCongr quadCodisc
              QuadCohesionSaturatedTwoCellConv.isoMiddleUnitLeft)
            (quadWhiskerRightIdCollapses quadDiscGamma quadCodisc))))) ?_
  refine QuadCohesionSaturatedTwoCellConv.trans
    (QuadCohesionSaturatedTwoCellConv.vcompCongrRight _
      (QuadCohesionSaturatedTwoCellConv.symm
        (QuadCohesionSaturatedTwoCellConv.ofFull
          (TwoCellConvFull.whiskerLeftComp (signature := quadCohesionModeSignature) quadPi0 quadDisc quadUnitUpperCell)))) ?_
  exact QuadCohesionSaturatedTwoCellConv.refl _

/-! ## The sharpened crux: the residual-cup whisker slide (named, NOT decided) -/

/-- The residual derived cup, canonically: `u : id_P ⇒ w` (the upper-iso form; `quadResidualCupJoin` shows
the choice is immaterial). -/
def quadResidualCupCell :
    RawTwoCellExpr quadCohesionModeSignature
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet) quadCodiscPi0 :=
  quadResidualCupViaUpperCell

/-- The LEFT insertion `w ◁ u : w ⇒ w·w` — the residual cup inserted AFTER the residual generator. -/
def quadResidualCupLeftInsertionCell :
    RawTwoCellExpr quadCohesionModeSignature (composePath quadCodiscPi0
      (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet))
      (composePath quadCodiscPi0 quadCodiscPi0) :=
  RawTwoCellExpr.whiskerLeft (signature := quadCohesionModeSignature) quadCodiscPi0 quadResidualCupCell

/-- The RIGHT insertion `u ▷ w : w ⇒ w·w` — the residual cup inserted BEFORE the residual generator. -/
def quadResidualCupRightInsertionCell :
    RawTwoCellExpr quadCohesionModeSignature
      (composePath (ModalityPath.nil (graph := quadCohesionGraph) QuadCohesionMode.pointSet)
        quadCodiscPi0)
      (composePath quadCodiscPi0 quadCodiscPi0) :=
  RawTwoCellExpr.whiskerRight (signature := quadCohesionModeSignature) quadCodiscPi0 quadResidualCupCell

/-- Non-degeneracy: the two insertions are DISTINCT raw terms (left- vs right-whisker-headed), so the slide
is a genuine open coherence, not a reflexivity. -/
theorem quadResidualInsertions_sidesAreDistinct :
    quadResidualCupLeftInsertionCell ≠ quadResidualCupRightInsertionCell :=
  fun sidesEqual => Bool.noConfusion (congrArg quadIsWhiskerLeftHeadedCell sidesEqual)

/-- The `ℤ/2` parity invariant is BLIND to the slide pair (as it must be — it is boundary-determined): both
insertions weigh the same.  Any refutation of the slide would need an order-sensitive invariant; none is
known to survive the saturation. -/
theorem quadResidualInsertions_parityAgrees :
    quadCohesionParity quadResidualCupLeftInsertionCell
      = quadCohesionParity quadResidualCupRightInsertionCell :=
  quadCohesionParity_constantOnParallel quadResidualCupLeftInsertionCell
    quadResidualCupRightInsertionCell

/-! ## Honesty markers -/

/-- ★★ **ESTABLISHED — the mate-bijection kit ships.**  Transposition across each adjunction of the quadruple
is a constructive bijection up to the saturated congruence: the three head peels
(`quadMateAlongCodisc_retract`/`_section`, `quadMateAlongGamma_retract`/`_section`,
`quadMateAlongDisc_retract`/`_section` — general in the tail and target words, cast-free) plus the tail-side
transpose at the comparison boundary (`quadMateTailDiscToCodisc_retract`), all powered by the signature-generic
exchange square (`twoCellConv_exchangeSquare` — the two Godement evaluation orders agree, derived from the
`interchange` 3-cell) and the loop-contraction helpers.  This is the engine that reduces arbitrary hom
boundaries toward the residual family `Hom(id, (codisc·pi0)^n)`.  `= true`. -/
def fxQuadCohesion_hasMateBijectionKit : Bool := true

/-- ★★ **ESTABLISHED — the four derived-comparison joins ship.**  The canonical-comparison multiplicities of
the cohesion quadruple are all DECIDED convertible: points-to-pieces `Γ ⇒ Π₀` (`quadPointsToPiecesJoin`),
discrete-to-codiscrete `Disc ⇒ coDisc` (`quadDiscreteToCodiscreteJoin`), the residual derived cup
`id_P ⇒ codisc·pi0` (`quadResidualCupJoin`), and the nested-vs-side-by-side cross-matching at
`id_S ⇒ pi0·disc·gamma·codisc` (`quadCrossMatchingJoin`).  Each is a genuinely non-trivial parallel pair
(syntactically distinct routes through DIFFERENT adjunctions), each decided by the kit + the shipped straddle
joins + the ff-iso rows.  `= true`. -/
def fxQuadCohesion_hasDerivedComparisonJoins : Bool := true

/-- ★★ **ESTABLISHED (wave-4) — the residual-cup whisker slide is DERIVED.**  With the kit's head peels,
parallel boundaries transpose toward the residual family around `w = codisc·pi0` — the one `pointSet`-endo
pair no ff iso collapses — and `w` carries its canonical point `u = quadResidualCupCell`, unique across its
two ff-iso constructions (`quadResidualCupJoin`).  The LAST open coherence on this family — the SLIDE
`w ◁ u ≈ u ▷ w` (`quadResidualCupLeftInsertionCell` vs `quadResidualCupRightInsertionCell`), the
well-pointedness of the pointed endo-1-cell `(w, u)` — is now a THEOREM:
`quadResidualCupWhiskerSlide` (`QuadrupleResidualCupSlide.lean`).  The pair is syntactically genuine
(`quadResidualInsertions_sidesAreDistinct`) and every abelian invariant is provably blind to it
(`quadResidualInsertions_parityAgrees`), so the derivation is real content: both insertions mediate through
the residual comultiplication `σ = (codisc ◁ k) ▷ pi0` built on the SPACE-side residual cup
`k : id_space ⇒ pi0·codisc`, whose two constructions join through `quadPointsToPiecesJoin` + Godement
naturality (`quadSpaceResidualCupJoin`), with the two adjoint triangles SOLVED for their whiskered units
against the invertible counits.  The normalizer itself
(`fxQuadCohesion_hasFreeWordNormalizerForThinness`) and the master flag remain `false` — the slide unblocks
the residual family's coherence, not the per-word completeness induction.  `= true`. -/
def fxQuadCohesion_hasResidualCupWhiskerSlide : Bool := true

end FX1Poly.Polygraph

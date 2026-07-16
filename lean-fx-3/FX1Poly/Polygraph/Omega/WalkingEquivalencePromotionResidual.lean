import FX1Poly.Polygraph.Omega.WalkingEquivalencePresentation

/-! # Polygraph/Omega/WalkingEquivalencePromotionResidual — narrowing the B3 promotion residual
(WP-EQUIV #2068 r2)

★ **The reachable ingredients of the walking-equivalence promotion, mechanized; the residual narrowed to the
single interchange bracketing.**  The shipped walker
(`WalkingEquivalencePresentation.lean`) closes the promotion of the bare equivalence to an adjoint equivalence
DOWN TO one honest node: `fxEquiv_promotionIdempotencyFromLeftTriangleWalled` — the idempotency
`psi_g . psi_g ~ psi_g` FROM the left triangle, whose only missing step is the two-Godement-firing interchange
bracketing.  Everything ELSE in the promotion (the abstract invertible-idempotent engine
`convEndoInvertibleIdempotent_isIdentity`, the LEFT inverse `walkingEquivRightDefect_leftInverse`, the
conditional promotion `walkingEquivRightTriangle_ofIdempotency`) is already machine-checked.

This file adds the remaining zero-axiom-reachable ingredients that surround that node, so the residual is
sharpened from "the promotion needs a Godement computation" to "the promotion needs ONLY the interchange
bracketing, with every other structural fact mechanized":

  1. **The left triangle survives whiskering by `g` (the recon recipe's opening move).**  From the left-triangle
     hypothesis `phi_f ~ id f` over the BARE cancellation congruence `walkingEquivBaseRel`, both whiskerings
     collapse: `g <| phi_f ~ id (g . f)` (`walkingEquivLeftTriangleWhiskeredLeftCollapses`) and
     `phi_f |> g ~ id (f . g)` (`walkingEquivLeftTriangleWhiskeredRightCollapses`).  These are literally the
     "whisker the left-triangle hypothesis by `g`" step the recon flagged as step 1 of the interchange
     bracketing — mechanized here, so the residual is genuinely only steps 3-4 (the two interchange firings).

  2. **The right defect `psi_g` is a genuine TWO-SIDED iso.**  The shipped file mechanized the LEFT inverse
     `psi_g^{-1} . psi_g ~ id (g . 1_A)` (`walkingEquivRightDefect_leftInverse`).  This file mechanizes the
     dual RIGHT inverse `psi_g . psi_g^{-1} ~ id (g . 1_A)` (`walkingEquivRightDefect_rightInverse`) by the
     mirror ~15-step whiskered-cancellation chain (the outer counit pair collapses by `whiskerRightFunctorial`
     + the E2a cancellation + `whiskerRightUnit`, the inner unit pair by `whiskerLeftFunctorial` + the E1a
     cancellation + `whiskerLeftUnit`, with the associativity / unit normalizations bridging).  Bundled with
     the shipped left inverse, `psi_g` is a genuine two-sided iso (`walkingEquivRightDefect_twoSidedInverse`).

## What is STILL walled (unchanged, honest)

The idempotency `psi_g . psi_g ~ psi_g` from the left triangle — the two-interchange-firing Godement
bracketing (`fxEquiv_promotionIdempotencyFromLeftTriangleWalled` in the shipped file, still `true`).  With the
two-sided iso and the whiskered left triangle now BOTH mechanized here, the promotion's residual is the pure
interchange hand-computation and nothing else: the marker
`fxEquiv_promotionResidualNarrowedToInterchangeBracketing = true` records the sharpening.  This is a precise
WALL narrowing, not a fabricated closure — no interchange row is fired to fake the idempotency.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The left triangle survives whiskering by `g` (the recon recipe's opening move) -/

/-- ★ **THE LEFT TRIANGLE, LEFT-WHISKERED BY `g`, COLLAPSES.**  From the left-triangle hypothesis
`phi_f ~ id f` over the bare cancellation congruence, `g <| phi_f ~ id (g . f)`: whisker the hypothesis on the
left by `g` (`whiskerLeftCongr`), then the left-whisker-unit law absorbs `g <| id f` into `id (g . f)`.  This
is literally step 1 of the recon's interchange bracketing ("whisker the left-triangle hypothesis by `g`") —
mechanized zero-axiom over the bare relation. -/
theorem walkingEquivLeftTriangleWhiskeredLeftCollapses
    (hLeftTriangle : SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      walkingEquivLeftTriangleLeg walkingEquivIdF) :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      (CellExpr.whiskerLeft walkingEquivGGen walkingEquivLeftTriangleLeg)
      (CellExpr.id (CellExpr.vcomp walkingEquivGGen walkingEquivFGen)) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.whiskerLeftCongr walkingEquivGGen hLeftTriangle)
    (SaturatedConvOverWithId.ofRelation
      (Or.inl (StrictAxiomRel.whiskerLeftUnit walkingEquivGGen walkingEquivFGen)))

/-- ★ **THE LEFT TRIANGLE, RIGHT-WHISKERED BY `g`, COLLAPSES.**  The dual: `phi_f |> g ~ id (f . g)` — whisker
the hypothesis on the right by `g` (`whiskerRightCongr`), then the right-whisker-unit law absorbs `id f |> g`
into `id (f . g)`.  The symmetric opening move (the recon recipe is symmetric under the B2 op-duality). -/
theorem walkingEquivLeftTriangleWhiskeredRightCollapses
    (hLeftTriangle : SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      walkingEquivLeftTriangleLeg walkingEquivIdF) :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      (CellExpr.whiskerRight walkingEquivLeftTriangleLeg walkingEquivGGen)
      (CellExpr.id (CellExpr.vcomp walkingEquivFGen walkingEquivGGen)) :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.whiskerRightCongr walkingEquivGGen hLeftTriangle)
    (SaturatedConvOverWithId.ofRelation
      (Or.inl (StrictAxiomRel.whiskerRightUnit walkingEquivFGen walkingEquivGGen)))

/-! ## The right defect is a genuine TWO-SIDED iso (the dual of the shipped left inverse) -/

/-- ★ **THE RIGHT DEFECT HAS A RIGHT INVERSE.**  `psi_g . psi_g^{-1} ~ id (g . 1_A)` over `walkingEquivBaseRel`
(the bare cancellations + strict laws, NO triangles) — the mirror of the shipped left-inverse chain
`walkingEquivRightDefect_leftInverse`.  Reassociate `(psi_g) . (psi_g^{-1})` to `C . ((D . A) . B)`; the OUTER
counit pair `(eps |> g) . (eps^{-1} |> g)` collapses to `id (u_B . g)` by `whiskerRightFunctorial` + the E2a
cancellation + `whiskerRightUnit`; the id normalizes across `vcompAssoc`; the left-unit absorbs it, leaving
`C . B`; the INNER unit pair `(g <| eta) . (g <| eta^{-1})` collapses to `id (g . 1_A)` by
`whiskerLeftFunctorial` + the E1a cancellation + `whiskerLeftUnit`.  So `psi_g` is invertible on BOTH sides. -/
theorem walkingEquivRightDefect_rightInverse :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightDefectInverse)
      (CellExpr.id (boundarySource walkingEquivRightTriangleLeg)) := by
  -- Abbreviations: C = g <| eta, D = eps |> g, A = eps^{-1} |> g, B = g <| eta^{-1}.
  -- psi_g = C . D, psi_g^{-1} = A . B, goal (C.D).(A.B) ~ id (g . 1_A).
  -- Reassociate (C.D).(A.B) to C . (D . (A.B)).
  have hAssocStart :
      SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
        (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightDefectInverse)
        (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen)
          (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
            walkingEquivRightDefectInverse)) :=
    SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompAssoc
      (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen)
      (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
      walkingEquivRightDefectInverse))
  -- Reassociate the inner D . (A . B) to (D . A) . B.
  have hReassocMid :
      SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
        (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
          walkingEquivRightDefectInverse)
        (CellExpr.vcomp
          (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
            (CellExpr.whiskerRight walkingEquivEpsInvGen walkingEquivGGen))
          (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen)) :=
    SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompAssoc
      (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
      (CellExpr.whiskerRight walkingEquivEpsInvGen walkingEquivGGen)
      (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen))))
  -- The outer counit pair D . A collapses to id (u_B . g).
  have hDA :
      SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
        (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
          (CellExpr.whiskerRight walkingEquivEpsInvGen walkingEquivGGen))
        (CellExpr.id (CellExpr.vcomp walkingEquivUnitB walkingEquivGGen)) :=
    SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
        (Or.inl (StrictAxiomRel.whiskerRightFunctorial walkingEquivEpsGen
          walkingEquivEpsInvGen walkingEquivGGen))))
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.whiskerRightCongr walkingEquivGGen
          walkingEquivCounitCancelForwardThreeCell)
        (SaturatedConvOverWithId.ofRelation
          (Or.inl (StrictAxiomRel.whiskerRightUnit walkingEquivUnitB walkingEquivGGen))))
  -- (D . A) . B collapses to B via the assoc-normalized left unit.
  have hDAB :
      SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
        (CellExpr.vcomp
          (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
            (CellExpr.whiskerRight walkingEquivEpsInvGen walkingEquivGGen))
          (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen))
        (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen) :=
    SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.vcompCongrLeft
        (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen) hDA)
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrLeft
          (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen)
          (SaturatedConvOverWithId.idCongr
            (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompAssoc
              walkingEquivGGen walkingEquivFGen walkingEquivGGen)))))
        (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft
          (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen)))))
  -- Assemble the middle: C . (D . (A.B)) ~ C . B.
  have hMid :
      SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
        (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen)
          (CellExpr.vcomp (CellExpr.whiskerRight walkingEquivEpsGen walkingEquivGGen)
            walkingEquivRightDefectInverse))
        (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen)
          (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen)) :=
    SaturatedConvOverWithId.vcompCongrRight
      (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen)
      (SaturatedConvOverWithId.trans hReassocMid hDAB)
  -- The inner unit pair C . B collapses to id (g . 1_A).
  have hCB :
      SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
        (CellExpr.vcomp (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaGen)
          (CellExpr.whiskerLeft walkingEquivGGen walkingEquivEtaInvGen))
        (CellExpr.id (CellExpr.vcomp walkingEquivGGen walkingEquivIdA)) :=
    SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
        (Or.inl (StrictAxiomRel.whiskerLeftFunctorial walkingEquivGGen
          walkingEquivEtaGen walkingEquivEtaInvGen))))
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.whiskerLeftCongr walkingEquivGGen
          walkingEquivUnitCancelForwardThreeCell)
        (SaturatedConvOverWithId.ofRelation
          (Or.inl (StrictAxiomRel.whiskerLeftUnit walkingEquivGGen walkingEquivIdA))))
  exact SaturatedConvOverWithId.trans hAssocStart
    (SaturatedConvOverWithId.trans hMid hCB)

/-! ## The two-sided-inverse bundle -/

/-- ★ **The right-defect two-sided-inverse statement.**  A `Prop` conjunction: `psi_g^{-1} . psi_g ~ id` (the
shipped left inverse) and `psi_g . psi_g^{-1} ~ id` (the right inverse mechanized above), both to
`id (g . 1_A)`. -/
def WalkingEquivRightDefectTwoSidedInverseStatement : Prop :=
  SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
    (CellExpr.vcomp walkingEquivRightDefectInverse walkingEquivRightTriangleLeg)
    (CellExpr.id (boundarySource walkingEquivRightTriangleLeg)) ∧
  SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
    (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightDefectInverse)
    (CellExpr.id (boundarySource walkingEquivRightTriangleLeg))

/-- ★★ **THE RIGHT DEFECT IS A GENUINE TWO-SIDED ISO.**  Both the shipped left inverse
`walkingEquivRightDefect_leftInverse` and the right inverse `walkingEquivRightDefect_rightInverse` hold over the
bare cancellation congruence, so `psi_g` is a genuine two-sided iso — the structural fact the promotion needs,
now on both sides zero-axiom. -/
theorem walkingEquivRightDefect_twoSidedInverse : WalkingEquivRightDefectTwoSidedInverseStatement :=
  ⟨walkingEquivRightDefect_leftInverse, walkingEquivRightDefect_rightInverse⟩

/-! ## Non-vacuity — the forward round-trip is not the identity on the nose -/

/-- The right-defect FORWARD round-trip `psi_g . psi_g^{-1}` is structurally NOT the identity `id (g . 1_A)` on
the nose (it collapses to it only via the cancellations — the right-inverse theorem is non-vacuous, the mirror
of the shipped `walkingEquivRightDefectRoundTrip_notLiterallyId`). -/
theorem walkingEquivRightDefectForwardRoundTrip_notLiterallyId :
    cellBeq walkingEquivModeBeq walkingEquivGenBeq
      (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightDefectInverse)
      (CellExpr.id (boundarySource walkingEquivRightTriangleLeg)) = false := rfl

/-! ## Non-vacuity probe -/

#eval cellBeq walkingEquivModeBeq walkingEquivGenBeq
  (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightDefectInverse)
  (CellExpr.id (boundarySource walkingEquivRightTriangleLeg))

/-! ## Honesty markers — the narrowed residual -/

/-- ★ **THE LEFT TRIANGLE SURVIVES WHISKERING BY `g` (MECHANIZED).**  `= true` records that the left-triangle
hypothesis, whiskered by `g` on either side, collapses to an identity
(`walkingEquivLeftTriangleWhiskeredLeftCollapses`, `walkingEquivLeftTriangleWhiskeredRightCollapses`) — the
recon recipe's step-1 opening move, mechanized zero-axiom over the bare relation. -/
def fxEquiv_promotionWhiskeredLeftTriangleCollapsesMechanized : Bool := true

/-- ★ **THE RIGHT DEFECT IS A TWO-SIDED ISO (MECHANIZED).**  `= true` records that both inverses of `psi_g` are
now machine-checked over the bare cancellation congruence — the shipped left inverse
`walkingEquivRightDefect_leftInverse` and the dual right inverse `walkingEquivRightDefect_rightInverse` bundled
in `walkingEquivRightDefect_twoSidedInverse`.  `psi_g` is a genuine two-sided iso, not merely left-invertible. -/
def fxEquiv_promotionRightDefectTwoSidedIsoMechanized : Bool := true

/-- ★ **WALL NARROWED — the promotion residual is now ONLY the interchange bracketing (honest).**  `= true`
records the sharpening: with the whiskered left triangle (step 1) AND the two-sided invertibility of `psi_g`
both mechanized here, the shipped promotion node `fxEquiv_promotionIdempotencyFromLeftTriangleWalled` is reduced
to the pure two-Godement-firing interchange hand-computation (recon steps 3-4) and nothing else.  Every OTHER
structural fact of the promotion is machine-checked.  No interchange row is fired to fake the idempotency — the
residual is genuinely narrowed, not fabricated.  The node stays honestly OPEN in the shipped file. -/
def fxEquiv_promotionResidualNarrowedToInterchangeBracketing : Bool := true

end FX1Poly.Polygraph.Omega

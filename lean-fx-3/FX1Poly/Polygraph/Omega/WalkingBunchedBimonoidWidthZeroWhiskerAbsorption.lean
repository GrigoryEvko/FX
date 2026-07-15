-- TODO: DELETE THIS GARBAGE -- defective bunchedBimonoid star (refuted r29/r30/r31); superseded by the LafontProp re-founding
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarAssociativeRestatement

/-! # Polygraph/Omega/WalkingBunchedBimonoidWidthZeroWhiskerAbsorption — the width-0-whisker (unit-object
action) absorptions DERIVED for the unit-bearing generators (WP-PROP r31, #2033)

★★ **The flagged residual, partially discharged.**  The strict axiom set carries no whisker-action UNIT law
(`X |> idOne ~ X` is not a row), and the r31 restatement flagged the width-0-whisker pairs as the successor's
first adjudication duty.  This file DERIVES two of them — the template for the family:

  * `eta_a |> idOne ~ eta_a` over the UNITAL scope alone: expand the identity cell through the bone
    (`eta ; eps ~ id`), pull the pair inside the whisker by functoriality, fire the bialgebra B3 row
    backwards, and collapse `delta ; (a <| eps)` by the `rightCounit` row;
  * `mu_a |> idOne ~ mu_a` over the ASSOCIATIVE scope: the phantom strand is converted into an eta by the
    `rootUnitAssoc` interchange square, re-associated through the NEW `muAssoc` row, and swallowed by the
    `rightUnit` row inside a whisker — the first genuine consumer of the r31 associativity row beyond the
    refutation pair itself.

The remaining member of the family — `sigma_a |> idOne ~ sigma_a` — stays honestly OPEN: sigma bears no
(co)unit row to absorb the phantom strand, and every shipped invariant (plain matrix, affine offset, bracket
magma) is blind to the pair.  The associative owner stays `= false`.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

set_option maxHeartbeats 4000000

/-- The eta with a phantom right whisker strand `eta_a |> idOne : idOne.idOne => a.idOne`. -/
def bunchedBimonoidEtaWhiskerIdOne : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerRight bunchedBimonoidAddEtaGen bunchedBimonoidIdOne

/-- The mu with a phantom right whisker strand `mu_a |> idOne : (a.a).idOne => a.idOne`. -/
def bunchedBimonoidMuWhiskerIdOne : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidIdOne

/-! ## The eta absorption (unital scope suffices) -/

/-- ★★ **`eta_a |> idOne ~ eta_a` over the UNITAL scope** — the phantom strand is expanded into an
`eta ; eps` pair by the bone row, pulled inside the whisker by functoriality, cancelled through the
bialgebra B3 row and the `rightCounit` row.  The width-0-whisker absorption template. -/
theorem bunchedBimonoidEtaWhiskerIdOneAbsorbedUnital :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidUnitalStarCongruenceScope
      bunchedBimonoidEtaWhiskerIdOne bunchedBimonoidAddEtaGen := by
  -- R ~ R ; id(a.idOne)
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
      (Or.inl (Or.inl (StrictAxiomRel.vcompUnitRight bunchedBimonoidEtaWhiskerIdOne))))) ?_
  -- R ; id(a.idOne) ~ R ; (a <| id(idOne))
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidEtaWhiskerIdOne
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
        (Or.inl (Or.inl (StrictAxiomRel.whiskerLeftUnit bunchedBimonoidAdditiveGen
          bunchedBimonoidIdOne)))))) ?_
  -- R ; (a <| id(idOne)) ~ R ; (a <| (eta ; eps))
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidEtaWhiskerIdOne
      (SaturatedConvOverWithId.whiskerLeftCongr bunchedBimonoidAdditiveGen
        (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
          (Or.inl (Or.inr (Or.inl BunchedBimonoidSoundRow.bialgebraBone))))))) ?_
  -- R ; (a <| (eta ; eps)) ~ R ; ((a <| eta) ; (a <| eps))
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidEtaWhiskerIdOne
      (SaturatedConvOverWithId.ofRelation
        (Or.inl (Or.inl (StrictAxiomRel.whiskerLeftFunctorial bunchedBimonoidAdditiveGen
          bunchedBimonoidAddEtaGen bunchedBimonoidAddEpsGen))))) ?_
  -- R ; ((a <| eta) ; (a <| eps)) ~ (R ; (a <| eta)) ; (a <| eps)
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
      (Or.inl (Or.inl (StrictAxiomRel.vcompAssoc bunchedBimonoidEtaWhiskerIdOne
        (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEtaGen)
        (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEpsGen)))))) ?_
  -- (R ; (a <| eta)) ; (a <| eps) ~ (eta ; delta) ; (a <| eps)   [B3 backwards]
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrLeft
      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEpsGen)
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
        (Or.inl (Or.inr (Or.inl BunchedBimonoidSoundRow.bialgebraUnit)))))) ?_
  -- (eta ; delta) ; (a <| eps) ~ eta ; (delta ; (a <| eps))
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.ofRelation
      (Or.inl (Or.inl (StrictAxiomRel.vcompAssoc bunchedBimonoidAddEtaGen
        bunchedBimonoidAddDeltaGen
        (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEpsGen))))) ?_
  -- eta ; (delta ; (a <| eps)) ~ eta ; id(a)   [rightCounit]
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidAddEtaGen
      (SaturatedConvOverWithId.ofRelation
        (Or.inr BunchedBimonoidUnitCounitRow.rightCounit))) ?_
  -- eta ; id(a) ~ eta
  exact SaturatedConvOverWithId.ofRelation
    (Or.inl (Or.inl (StrictAxiomRel.vcompUnitRight bunchedBimonoidAddEtaGen)))

/-! ## The mu absorption (the NEW associativity row is the missing link) -/

/-- The pivot composite `(mu |> idOne) ; (a <| eta) ; mu` — reduces BOTH to `mu |> idOne` (swallowing the
eta by the `rightUnit` row) and to `mu` (through `rootUnitAssoc` + the NEW `muAssoc` row). -/
def bunchedBimonoidMuWhiskerPivot : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp
    (CellExpr.vcomp bunchedBimonoidMuWhiskerIdOne
      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEtaGen))
    bunchedBimonoidAddMuGen

/-- The pivot reduces to `mu |> idOne` (the eta is swallowed by the `rightUnit` row). -/
theorem bunchedBimonoidMuWhiskerPivotToMuWhisker :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad
      bunchedBimonoidAssociativeStarCongruenceScope
      bunchedBimonoidMuWhiskerPivot bunchedBimonoidMuWhiskerIdOne := by
  -- (M ; (a<|eta)) ; mu ~ M ; ((a<|eta) ; mu)
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.ofRelation
      (Or.inl (Or.inl (Or.inl (StrictAxiomRel.vcompAssoc bunchedBimonoidMuWhiskerIdOne
        (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEtaGen)
        bunchedBimonoidAddMuGen))))) ?_
  -- M ; ((a<|eta) ; mu) ~ M ; id(a)   [rightUnit]
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidMuWhiskerIdOne
      (SaturatedConvOverWithId.ofRelation
        (Or.inl (Or.inr BunchedBimonoidUnitCounitRow.rightUnit)))) ?_
  -- M ; id(a) ~ M ; id(a.idOne)   [idCongr over the dim-1 unit, backwards]
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidMuWhiskerIdOne
      (SaturatedConvOverWithId.idCongr
        (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
          (Or.inl (Or.inl (Or.inl
            (StrictAxiomRel.vcompUnitRight bunchedBimonoidAdditiveGen)))))))) ?_
  -- M ; id(a.idOne) ~ M
  exact SaturatedConvOverWithId.ofRelation
    (Or.inl (Or.inl (Or.inl (StrictAxiomRel.vcompUnitRight bunchedBimonoidMuWhiskerIdOne))))

/-- The pivot reduces to `mu` (`rootUnitAssoc` + the NEW `muAssoc` row + `rightUnit` inside the whisker). -/
theorem bunchedBimonoidMuWhiskerPivotToMu :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad
      bunchedBimonoidAssociativeStarCongruenceScope
      bunchedBimonoidMuWhiskerPivot bunchedBimonoidAddMuGen := by
  -- (M ; (a<|eta)) ; mu ~ ((aa<|eta) ; (mu|>a)) ; mu   [rootUnitAssoc]
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrLeft bunchedBimonoidAddMuGen
      (SaturatedConvOverWithId.ofRelation
        (Or.inl (Or.inl (Or.inr (Or.inl BunchedBimonoidSoundRow.addMonadRootUnitAssoc)))))) ?_
  -- ((aa<|eta) ; (mu|>a)) ; mu ~ (aa<|eta) ; ((mu|>a) ; mu)
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.ofRelation
      (Or.inl (Or.inl (Or.inl (StrictAxiomRel.vcompAssoc
        (CellExpr.whiskerLeft bunchedBimonoidAaWord bunchedBimonoidAddEtaGen)
        (CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAdditiveGen)
        bunchedBimonoidAddMuGen))))) ?_
  -- (aa<|eta) ; ((mu|>a) ; mu) ~ (aa<|eta) ; ((a<|mu) ; mu)   [THE NEW muAssoc ROW]
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight
      (CellExpr.whiskerLeft bunchedBimonoidAaWord bunchedBimonoidAddEtaGen)
      (SaturatedConvOverWithId.ofRelation (Or.inr BunchedBimonoidAssocRow.muAssoc))) ?_
  -- (aa<|eta) ; ((a<|mu) ; mu) ~ ((aa<|eta) ; (a<|mu)) ; mu
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
      (Or.inl (Or.inl (Or.inl (StrictAxiomRel.vcompAssoc
        (CellExpr.whiskerLeft bunchedBimonoidAaWord bunchedBimonoidAddEtaGen)
        (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddMuGen)
        bunchedBimonoidAddMuGen)))))) ?_
  -- ((aa<|eta) ; (a<|mu)) ; mu ~ ((a<|(a<|eta)) ; (a<|mu)) ; mu   [whiskerAssocLeft]
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrLeft bunchedBimonoidAddMuGen
      (SaturatedConvOverWithId.vcompCongrLeft
        (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddMuGen)
        (SaturatedConvOverWithId.ofRelation
          (Or.inl (Or.inl (Or.inl (StrictAxiomRel.whiskerAssocLeft bunchedBimonoidAdditiveGen
            bunchedBimonoidAdditiveGen bunchedBimonoidAddEtaGen))))))) ?_
  -- ((a<|(a<|eta)) ; (a<|mu)) ; mu ~ (a <| ((a<|eta) ; mu)) ; mu   [functoriality backwards]
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrLeft bunchedBimonoidAddMuGen
      (SaturatedConvOverWithId.symm (SaturatedConvOverWithId.ofRelation
        (Or.inl (Or.inl (Or.inl (StrictAxiomRel.whiskerLeftFunctorial bunchedBimonoidAdditiveGen
          (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEtaGen)
          bunchedBimonoidAddMuGen))))))) ?_
  -- (a <| ((a<|eta) ; mu)) ; mu ~ (a <| id(a)) ; mu   [rightUnit inside the whisker]
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrLeft bunchedBimonoidAddMuGen
      (SaturatedConvOverWithId.whiskerLeftCongr bunchedBimonoidAdditiveGen
        (SaturatedConvOverWithId.ofRelation
          (Or.inl (Or.inr BunchedBimonoidUnitCounitRow.rightUnit))))) ?_
  -- (a <| id(a)) ; mu ~ id(a.a) ; mu   [whiskerLeftUnit]
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrLeft bunchedBimonoidAddMuGen
      (SaturatedConvOverWithId.ofRelation
        (Or.inl (Or.inl (Or.inl (StrictAxiomRel.whiskerLeftUnit bunchedBimonoidAdditiveGen
          bunchedBimonoidAdditiveGen)))))) ?_
  -- id(a.a) ; mu ~ mu
  exact SaturatedConvOverWithId.ofRelation
    (Or.inl (Or.inl (Or.inl (StrictAxiomRel.vcompUnitLeft bunchedBimonoidAddMuGen))))

/-- ★★ **`mu_a |> idOne ~ mu_a` over the ASSOCIATIVE scope** — the first genuine consumer of the NEW
`muAssoc` row beyond the refutation pair: the phantom strand becomes an eta (`rootUnitAssoc`), rides the
reassociation, and is swallowed by the `rightUnit` row.  Underivable over the r30 unital scope's
matrix-blind fragment without the associativity row (the derivation pivots through `(mu|>a);mu ~ (a<|mu);mu`
exactly once). -/
theorem bunchedBimonoidMuWhiskerIdOneAbsorbedAssociative :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad
      bunchedBimonoidAssociativeStarCongruenceScope
      bunchedBimonoidMuWhiskerIdOne bunchedBimonoidAddMuGen :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.symm bunchedBimonoidMuWhiskerPivotToMuWhisker)
    bunchedBimonoidMuWhiskerPivotToMu

/-! ## The honesty markers -/

/-- ★★ **ESTABLISHED — the width-0-whisker absorption template.**  `= true` records the two derived
absorptions: `eta_a |> idOne ~ eta_a` over the UNITAL scope
(`bunchedBimonoidEtaWhiskerIdOneAbsorbedUnital`) and `mu_a |> idOne ~ mu_a` over the ASSOCIATIVE scope
(`bunchedBimonoidMuWhiskerIdOneAbsorbedAssociative` — the first consumer of the r31 `muAssoc` row).  The
family template for the successor's retract: phantom strands on (co)unit-bearing generators are absorbable. -/
def fxBunchedBimonoid_widthZeroWhiskerAbsorptionTemplateShipped : Bool := true

/-- ★ **THE SIGMA CASE STAYS OPEN — no flip.**  `= false` records that `sigma_a |> idOne ~ sigma_a` is
neither derived nor refuted: sigma bears no (co)unit row, the hexagon routes have not been exhausted, and
every shipped invariant (plain matrix, affine offset, bracket magma) is blind to the pair.  The successor
must derive it or decide it and re-widen with the sesquicategory unit-action rows. -/
def fxBunchedBimonoid_sigmaWidthZeroWhiskerAbsorptionStillOpen : Bool := false

end FX1Poly.Polygraph.Omega

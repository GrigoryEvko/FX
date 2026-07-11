import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidWideCollision

/-! # Polygraph/Omega/WalkingBunchedBimonoidRetractionConvDeltas — the per-constructor CONVERTIBILITY deltas of
the additive NF-retraction (the r5 census shipped MATRIX witnesses; this file ships the SYNTACTIC witnesses), and
the honest corrected-star assembly gated on the B1/B2 residuals (WP-PROP r6, #2033, the 110-percent grind)

★ **THE single most important r6 finding, discharged at the elementary constructors.**  The r5
`StarRetractionCensus` "census" is the SEMANTIC (matrix) side of the NF-retraction: each generator's staged form
is witnessed by a MATRIX equality (`bunchedBimonoidAddMuStagedWitness : evalCell mu_a = evalCell (muFold 2)`,
etc.).  The retraction the corrected star needs is the SYNTACTIC (convertibility) side: each cell must CONVERT to
its staged form over the star scope.  This file ships those CONV deltas per `CellExpr` constructor:

  * **`gen` — the five additive generators convert to their staged spiders.**  `mu_a ~ muFold 2` and
    `delta_a ~ deltaFan 2` each by a 2-step `StrictAxiomRel` chain (`whiskerRightUnit` then `vcompUnit`); `eta_a =
    muFold 0`, `eps_a = deltaFan 0`, `sigma_a` = the perm word are DEFINITIONAL (`refl`).
  * **`id` — the identity case lifts by `idCongr`.**  `id c ~ id c'` from a sub-cell conv `c ~ c'`.
  * **`whiskerLeft` / `whiskerRight` — the block cases lift by `whisker*Congr`.**  `whiskerLeft w c ~ whiskerLeft
    w c'` from a sub-cell conv, with the concrete instance `whiskerLeft a mu_a ~ whiskerLeft a (muFold 2)`.
  * **`vcomp` — the collision (B1) + the determinism (B2).**  The vcomp case IS the wide collision recursion + the
    perm-middle determinism, both walled at their exact r6 nodes.

## The corrected-star assembly (honest, NOT flipped)

The corrected star `bunchedBimonoidStarStatementAdditive` chains, for two additive cells with equal matrix,
`alpha ~ retract alpha = retract beta ~ beta`.  The two OUTER conversions are the per-constructor CONV deltas
shipped here (the `gen` / `id` / `whisker` cases) closed under the wide collision (B1); the MIDDLE equality
`retract alpha = retract beta` (same matrix ⟹ same/convertible canonical form) is the perm-middle DETERMINISM
(B2, `CoxeterWordUnique`).  Since BOTH the wide collision recursion (B1) and the determinism (B2) are walled, the
star does NOT close in r6; every star marker stays `= false` byte-intact — NO flip.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # B3 — THE GENERATOR CONV DELTAS (each generator converts to its staged spider)
    # =========================================================================================
-/

/-- ★★ **THE `mu_a` CONV DELTA — `mu_a ~ muFold 2` over the star scope.**  The r5 matrix witness
`bunchedBimonoidAddMuStagedWitness` (`evalCell mu_a = evalCell (muFold 2)`) lifted to CONVERTIBILITY: `muFold 2 =
(id a |> a) ; mu_a`, so `whiskerRightUnit` collapses `id a |> a` to `id (a.a)` (`= id (boundarySource mu_a)`), and
`vcompUnitLeft` absorbs it — a 2-step `StrictAxiomRel` chain, symmetrized.  The syntactic side the corrected star
needs at the `gen mu_a` case. -/
theorem bunchedBimonoidMuGenConvToMuFoldTwo :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      bunchedBimonoidAddMuGen (bunchedBimonoidMuFold 2) := by
  apply SaturatedConvOverWithId.symm
  have whiskerCollapse : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerRight (CellExpr.id bunchedBimonoidAdditiveGen) bunchedBimonoidAdditiveGen)
      (CellExpr.id bunchedBimonoidAaWord) :=
    SaturatedConvOverWithId.ofRelation
      (Or.inl (StrictAxiomRel.whiskerRightUnit bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen))
  have underComposite := SaturatedConvOverWithId.vcompCongrLeft bunchedBimonoidAddMuGen whiskerCollapse
  have unitAbsorb : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp (CellExpr.id (boundarySource bunchedBimonoidAddMuGen)) bunchedBimonoidAddMuGen)
      bunchedBimonoidAddMuGen :=
    SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitLeft bunchedBimonoidAddMuGen))
  exact SaturatedConvOverWithId.trans underComposite unitAbsorb

/-- ★★ **THE `delta_a` CONV DELTA — `delta_a ~ deltaFan 2` over the star scope.**  The dual of the `mu_a` delta:
`deltaFan 2 = delta_a ; (id a |> a)`, so `whiskerRightUnit` collapses `id a |> a` to `id (a.a)` (`= id
(boundaryTarget delta_a)`), and `vcompUnitRight` absorbs it — a 2-step chain, symmetrized. -/
theorem bunchedBimonoidDeltaGenConvToDeltaFanTwo :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      bunchedBimonoidAddDeltaGen (bunchedBimonoidDeltaFan 2) := by
  apply SaturatedConvOverWithId.symm
  have whiskerCollapse : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerRight (CellExpr.id bunchedBimonoidAdditiveGen) bunchedBimonoidAdditiveGen)
      (CellExpr.id bunchedBimonoidAaWord) :=
    SaturatedConvOverWithId.ofRelation
      (Or.inl (StrictAxiomRel.whiskerRightUnit bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen))
  have underComposite := SaturatedConvOverWithId.vcompCongrRight bunchedBimonoidAddDeltaGen whiskerCollapse
  have unitAbsorb : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.vcomp bunchedBimonoidAddDeltaGen (CellExpr.id (boundaryTarget bunchedBimonoidAddDeltaGen)))
      bunchedBimonoidAddDeltaGen :=
    SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.vcompUnitRight bunchedBimonoidAddDeltaGen))
  exact SaturatedConvOverWithId.trans underComposite unitAbsorb

/-- ★ **THE `eta_a` CONV DELTA — `eta_a ~ muFold 0` is DEFINITIONAL** (`muFold 0 = eta_a`), so `refl`.  The
zero-width mu-fold IS the unit generator; the staged form needs no rewriting. -/
theorem bunchedBimonoidEtaGenConvToMuFoldZero :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      bunchedBimonoidAddEtaGen (bunchedBimonoidMuFold 0) :=
  SaturatedConvOverWithId.refl _

/-- ★ **THE `eps_a` CONV DELTA — `eps_a ~ deltaFan 0` is DEFINITIONAL** (`deltaFan 0 = eps_a`), so `refl`.  The
zero-width delta-fan IS the counit generator. -/
theorem bunchedBimonoidEpsGenConvToDeltaFanZero :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      bunchedBimonoidAddEpsGen (bunchedBimonoidDeltaFan 0) :=
  SaturatedConvOverWithId.refl _

/-- ★ **THE `sigma_a` CONV DELTA — `sigma_a ~ spiderPermTwo` is DEFINITIONAL** (`spiderPermTwo = sigma_a`), so
`refl`.  The additive swap IS its own perm-stage word; the staged form of a permutation is the permutation. -/
theorem bunchedBimonoidSigmaGenConvToPermTwo :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      bunchedBimonoidAddSigmaGen bunchedBimonoidSpiderPermTwo :=
  SaturatedConvOverWithId.refl _

/-! ## The B3 generator-delta marker -/

/-- ★★ **ESTABLISHED (B3) — the five additive generators convert to their staged spiders (CONV, not just
matrix).**  `= true` records the per-generator CONV deltas: `mu_a ~ muFold 2` and `delta_a ~ deltaFan 2` (2-step
`StrictAxiomRel` chains, `bunchedBimonoid{Mu,Delta}GenConvTo...`) and `eta_a = muFold 0`, `eps_a = deltaFan 0`,
`sigma_a = spiderPermTwo` (definitional, `refl`).  This is the SYNTACTIC lift of the r5 MATRIX-only staged
witnesses (`bunchedBimonoidAdd{Mu,Delta,Eta,Eps,Sigma}StagedWitness`) — the retraction's `gen` case. -/
def fxBunchedBimonoid_generatorConvDeltasShipped : Bool := true

/-! # =========================================================================================
    # B3 — THE id / whisker CONV LIFTS (the retraction's congruence cases)
    # =========================================================================================
-/

/-- ★ **THE `id` CONV LIFT — `id c ~ id c'` from a sub-cell conv.**  The retraction's `id` case: a sub-cell
retraction `c ~ retract c` lifts to the identity cells by `idCongr`.  The dimension-bump congruence the
`CongruenceWithId` sibling supplies. -/
theorem bunchedBimonoidIdCellConvLift {dim : Nat}
    {cell cellStaged : CellExpr bunchedBimonoidOmegaComputad dim}
    (conv : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      cell cellStaged) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.id cell) (CellExpr.id cellStaged) :=
  SaturatedConvOverWithId.idCongr conv

/-- ★ **THE `whiskerLeft` CONV LIFT — `whiskerLeft w c ~ whiskerLeft w c'` from a sub-cell conv.**  The
retraction's left-whisker case: the whiskered sub-cell's retraction lifts under the fixed whiskering 1-cell by
`whiskerLeftCongr`.  The block-assembly at CONV granularity (the r5 block witnesses live in `Mat(N)` only). -/
theorem bunchedBimonoidWhiskerLeftConvLift (whiskeringCell : CellExpr bunchedBimonoidOmegaComputad 1)
    {cell cellStaged : CellExpr bunchedBimonoidOmegaComputad 2}
    (conv : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      cell cellStaged) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft whiskeringCell cell) (CellExpr.whiskerLeft whiskeringCell cellStaged) :=
  SaturatedConvOverWithId.whiskerLeftCongr whiskeringCell conv

/-- ★ **THE `whiskerRight` CONV LIFT — `whiskerRight c w ~ whiskerRight c' w` from a sub-cell conv.**  The dual
right-whisker case, by `whiskerRightCongr`. -/
theorem bunchedBimonoidWhiskerRightConvLift (whiskeringCell : CellExpr bunchedBimonoidOmegaComputad 1)
    {cell cellStaged : CellExpr bunchedBimonoidOmegaComputad 2}
    (conv : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      cell cellStaged) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerRight cell whiskeringCell) (CellExpr.whiskerRight cellStaged whiskeringCell) :=
  SaturatedConvOverWithId.whiskerRightCongr whiskeringCell conv

/-- ★★ **THE CONCRETE WHISKER CONV DELTA — `whiskerLeft a mu_a ~ whiskerLeft a (muFold 2)`.**  The r5 whisker
matrix witness `bunchedBimonoidWhiskerLeftStagedWitness` (block-diagonal placement `[[1,0,0],[0,1,1]]`) lifted to
CONVERTIBILITY: the `mu_a` generator delta lifted under the left whisker by `whiskerLeftConvLift`.  A concrete
retraction whisker case at CONV granularity. -/
theorem bunchedBimonoidWhiskerLeftMuConvDelta :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddMuGen)
      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen (bunchedBimonoidMuFold 2)) :=
  bunchedBimonoidWhiskerLeftConvLift bunchedBimonoidAdditiveGen bunchedBimonoidMuGenConvToMuFoldTwo

/-! ## The B3 congruence-lift marker -/

/-- ★★ **ESTABLISHED (B3) — the id / whisker retraction cases lift by congruence (CONV).**  `= true` records the
three congruence-lift lemmas (`bunchedBimonoidIdCellConvLift`, `bunchedBimonoidWhiskerLeft/RightConvLift`) — the
retraction's `id` / `whiskerLeft` / `whiskerRight` cases reduce to the sub-cell retraction via the
`CongruenceWithId` sibling's `idCongr` / `whisker*Congr` — together with the concrete instance
`bunchedBimonoidWhiskerLeftMuConvDelta` (`whiskerLeft a mu_a ~ whiskerLeft a (muFold 2)`).  The SYNTACTIC lift of
the r5 MATRIX-only block witnesses. -/
def fxBunchedBimonoid_idWhiskerConvLiftsShipped : Bool := true

/-! # =========================================================================================
    # B3 — THE CORRECTED-STAR ASSEMBLY (honest: gated on the B1/B2 residuals, NOT flipped)
    # =========================================================================================

★ **The corrected star `bunchedBimonoidStarStatementAdditive` chains `alpha ~ retract alpha = retract beta ~
beta`.  The two OUTER conversions are the per-constructor CONV deltas shipped above (closed under the wide
collision B1); the MIDDLE equality is the perm-middle DETERMINISM (B2).  Both the wide collision recursion and the
determinism are walled, so the star does NOT close — NO star marker flips.** -/

/-- ★ **THE STAR ASSEMBLY IS GATED ON THE B1/B2 RESIDUALS — the retraction's `gen`/`id`/`whisker` cases are CONV,
the `vcomp` case is the wide collision + determinism.**  `= true` records the honest assembly shape: the corrected
star's retraction induction over `bunchedBimonoidCellUsesOnlyAdditive` has its `ofMode` (trivial), `gen`
(`fxBunchedBimonoid_generatorConvDeltasShipped`), `id` / `whiskerLeft` / `whiskerRight`
(`fxBunchedBimonoid_idWhiskerConvLiftsShipped`) cases discharged AT CONV GRANULARITY here; the SOLE remaining
constructor case is `vcomp` = the wide collision recursion (B1,
`fxBunchedBimonoid_wideCollisionConvRecursionUnbuilt`), and the final equal-matrices step is the perm-middle
determinism (B2, `fxBunchedBimonoid_coxeterWordUniqueMinimalLemmaUnbuilt`).  This marker records that the
elementary-constructor cases ARE shipped; it is NOT the star itself. -/
def fxBunchedBimonoid_starAssemblyElementaryCasesShipped : Bool := true

/-- ★ **THE CORRECTED STAR STAYS r6 — no flip.**  `= false` records that
`bunchedBimonoidStarStatementAdditive` (the corrected, honestly-scoped additive star) is NOT proven in r6: its
retraction induction has the `gen` / `id` / `whisker` cases discharged (the CONV deltas above), but its `vcomp`
case is the wide collision recursion (B1, walled) and its equal-matrices assembly is the perm-middle determinism
(B2, walled) — neither shipped.  The upstream star markers
(`fxBunchedBimonoid_correctedStarStaysRSix`, `...nfInductionStarStillRFive`,
`...spiderNormalFormStarNamedRThree`, `...propGeneralCompletenessStarReached`) all stay `= false` byte-intact —
NO fake flip. -/
def fxBunchedBimonoid_correctedStarStillRSixAfterConvDeltas : Bool := false

/-- ★★ **ESTABLISHED (B3) — the WP-PROP r6 retraction-CONV-deltas ledger (honest scoreboard).**  `= true` records
the complete r6 retraction advance: the five generator CONV deltas (`gen` case,
`fxBunchedBimonoid_generatorConvDeltasShipped` — `mu_a ~ muFold 2`, `delta_a ~ deltaFan 2` via 2-step strict
chains, the other three definitional); the id / whisker CONV lifts (`fxBunchedBimonoid_idWhiskerConvLiftsShipped`
— `idCongr` / `whisker*Congr` + the concrete `whiskerLeft a mu_a ~ whiskerLeft a (muFold 2)`); and the honest
corrected-star assembly (`fxBunchedBimonoid_starAssemblyElementaryCasesShipped` — the elementary cases at CONV,
the `vcomp` case gated on B1, the equal-matrices step gated on B2).  The corrected star does NOT close
(`fxBunchedBimonoid_correctedStarStillRSixAfterConvDeltas = false`); every upstream star marker byte-intact — NO
flip.  This is the SYNTACTIC lift of the r5 MATRIX-only census, the recon's single most important r6 finding. -/
def fxBunchedBimonoid_retractionConvDeltasRoundSixLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega

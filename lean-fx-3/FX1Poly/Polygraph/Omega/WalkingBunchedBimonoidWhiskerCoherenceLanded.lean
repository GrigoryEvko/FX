import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidWhiskerOneCellCoherenceWall
import FX1Poly.Polygraph.Omega.Steiner.SoundnessFull

/-! # Polygraph/Omega/WalkingBunchedBimonoidWhiskerCoherenceLanded — the r19 substrate harvest:
associator (+dual) + whisker-commute LANDED into `StrictAxiomRel`; the identity-whisker UNITOR machine-refuted
and honestly walled (WP-PROP r19)

★ **THE SUBSTRATE-ROUND HARVEST.**  The r18 wall (`WalkingBunchedBimonoidWhiskerOneCellCoherenceWall`) walled all
THREE whisker-vs-1-cell coherences on the (too coarse) test "non-boundary-parallel".  The r19 substrate round
corrects that: "non-boundary-parallel" is NOT "chain-unsound".  Two of the three — the **associator** (both
duals) and the **whisker left/right commute** — are chain-SOUND: their `polesOf` agree via
`addCoordinates_assoc` over a definitionally-shared boundary spine (`Steiner/SoundnessFull.polesOf_ofRelation_eq`,
the r19 arms).  They are now genuine `StrictAxiomRel` rows (`StrictAxioms.whiskerAssocLeft` /
`whiskerAssocRight` / `whiskerLeftRightCommute`), and every OMEGA consumer was updated in the same commit.

The **identity-whisker unitor** `whiskerLeft (id c) X ~ X` is the poison pill: for a FREE 1-cell `c` its `polesOf`
spine visits `linearize c` where `X`'s spine visits `linearize (bs (bs X))`, and those differ.  Adding it as a
FREE `StrictAxiomRel` row would make the shipped ★★ CROWN `Steiner/SoundnessFull.linearizeFullSoundness` FALSE.
So it STAYS OUT — the sole residual — machine-refuted below.

## What this file ships (all zero-axiom, machine-checked)

  * **The landed rows fire.**  `whiskerAssociatorLeftConv` / `...RightConv` / `whiskerCommuteConv` :
    `SaturatedConvOver (StrictAxiomRel)` derivations built by `ofRelation` on the new constructors, plus the
    concrete bunched-bimonoid instances (the exact cells of the shipped `...MatrixSound` theorems).
  * **The landed rows are chain-SOUND (non-vacuity of the extended `linearizeFullSoundness`).**
    `whiskerAssociatorLeft_linearizeFull` etc. run a genuine derivation through the CROWN fold to EQUAL chain
    tables — exercising the r19 `addCoordinates_assoc` poles arms.
  * **★ THE UNITOR STOP.**  `whiskerIdentityUnitorTablesDiffer` (`decide`, zero-axiom): the free identity-whisker
    unitor's two legs have DISTINCT `linearizeFull` chain tables (top equal, poles differ).  Hence
    `whiskerIdentityUnitor_not_conv`: they are NON-convertible over the live `StrictAxiomRel`.  Identifying them
    (the free unitor row) would contradict this — i.e. would falsify `linearizeFullSoundness`.  This is the honest,
    machine-checked reason the unitor is walled; NEVER a fabricated flip.

## The M4 cost table for the walled unitor (the honest fallback for the residual)

  | route for the identity-whisker unitor        | sound? | cost                                             | round? |
  | --------------------------------------------- | ------ | ------------------------------------------------ | ------ |
  | free `StrictAxiomRel` row                     | NO     | falsifies `linearizeFullSoundness` (refuted here) | forbidden |
  | pinned presentation row (`c = bs (bs X)`)     | yes    | 1 relation + `addCoordinates_zeroVector_left` poles arm; spine matches | next WP-PROP round |
  | `whiskerUnitRel` (EckmannHiltonWithId)        | yes (single-vector) | already shipped; conv-form only, NOT `linearizeFull`-sound | shipped |
  | flat-List `boundarySource` (mechanism c)      | yes    | rewrite `boundarySource`/`boundaryTarget`/`polesOf` + ~424 sites / ~40 files | M4 substrate |

The `runCombConv`-over-cells lift (`fxBunchedBimonoid_runCommuteConvGatedOnWhiskerAssociatorAndUnitors`, still
`false`) stays gated: its distant-commute / run-conv atoms need the identity-whisker unitor, which assoc+commute
alone do not supply.  The four star owners keep their name and `= false` value byte-intact (cross-file, not edited).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Steiner

/-! # =========================================================================================
    # L1 — the LANDED rows fire as `StrictAxiomRel` / `SaturatedConvOver` (generic + bunched instances)
    # =========================================================================================
-/

/-- ★ The **whisker-1-cell associator (left)** is now a live convertibility: `(P . Q) <| X ~ P <| (Q <| X)`. -/
theorem whiskerAssociatorLeftConv {computad : OmegaComputad} {dim : Nat}
    (whiskP whiskQ : CellExpr computad (dim + 1)) (inner : CellExpr computad (dim + 2)) :
    SaturatedConvOver computad (StrictAxiomRel computad)
      (CellExpr.whiskerLeft (CellExpr.vcomp whiskP whiskQ) inner)
      (CellExpr.whiskerLeft whiskP (CellExpr.whiskerLeft whiskQ inner)) :=
  SaturatedConvOver.ofRelation (StrictAxiomRel.whiskerAssocLeft whiskP whiskQ inner)

/-- ★ The **whisker-1-cell associator (right dual)** is now live: `X |> (P . Q) ~ (X |> P) |> Q`. -/
theorem whiskerAssociatorRightConv {computad : OmegaComputad} {dim : Nat}
    (inner : CellExpr computad (dim + 2)) (whiskP whiskQ : CellExpr computad (dim + 1)) :
    SaturatedConvOver computad (StrictAxiomRel computad)
      (CellExpr.whiskerRight inner (CellExpr.vcomp whiskP whiskQ))
      (CellExpr.whiskerRight (CellExpr.whiskerRight inner whiskP) whiskQ) :=
  SaturatedConvOver.ofRelation (StrictAxiomRel.whiskerAssocRight inner whiskP whiskQ)

/-- ★ The **whisker left/right commute** is now live: `(P <| X) |> Q ~ P <| (X |> Q)`. -/
theorem whiskerCommuteConv {computad : OmegaComputad} {dim : Nat}
    (whiskP : CellExpr computad (dim + 1)) (inner : CellExpr computad (dim + 2))
    (whiskQ : CellExpr computad (dim + 1)) :
    SaturatedConvOver computad (StrictAxiomRel computad)
      (CellExpr.whiskerRight (CellExpr.whiskerLeft whiskP inner) whiskQ)
      (CellExpr.whiskerLeft whiskP (CellExpr.whiskerRight inner whiskQ)) :=
  SaturatedConvOver.ofRelation (StrictAxiomRel.whiskerLeftRightCommute whiskP inner whiskQ)

/-- The bunched-bimonoid associator-left instance — the EXACT cells of the shipped
`bunchedBimonoidWhiskerOneCellAssocLeftMatrixSound` — now fires as a `StrictAxiomRel` convertibility (the row the
r18 wall recorded as walled). -/
theorem bunchedBimonoidWhiskerAssocLeftLanded :
    SaturatedConvOver bunchedBimonoidOmegaComputad (StrictAxiomRel bunchedBimonoidOmegaComputad)
      (CellExpr.whiskerLeft (CellExpr.vcomp bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen)
        bunchedBimonoidAddSigmaGen)
      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
        (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)) :=
  whiskerAssociatorLeftConv bunchedBimonoidAdditiveGen bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen

/-- The bunched-bimonoid whisker-commute instance — the cells of `bunchedBimonoidWhiskerOneCellCommuteMatrixSound`
— now fires as a `StrictAxiomRel` convertibility. -/
theorem bunchedBimonoidWhiskerCommuteLanded :
    SaturatedConvOver bunchedBimonoidOmegaComputad (StrictAxiomRel bunchedBimonoidOmegaComputad)
      (CellExpr.whiskerRight (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen)
        bunchedBimonoidAdditiveGen)
      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen
        (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen)) :=
  whiskerCommuteConv bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen

/-! # =========================================================================================
    # L2 — the landed rows are chain-SOUND: they fold through the extended `linearizeFullSoundness`
    # =========================================================================================
-/

/-- ★ **Associator-left is `linearizeFull`-sound.**  The genuine `SaturatedConvOver` derivation of the associator
maps through the CROWN fold to EQUAL chain tables — exercising the r19 `addCoordinates_assoc` poles arms of
`polesOf_ofRelation_eq`. -/
theorem whiskerAssociatorLeft_linearizeFull {computad : OmegaComputad}
    (valuation : ComputadValuation computad) {dim : Nat}
    (whiskP whiskQ : CellExpr computad (dim + 1)) (inner : CellExpr computad (dim + 2)) :
    linearizeFull valuation (CellExpr.whiskerLeft (CellExpr.vcomp whiskP whiskQ) inner)
      = linearizeFull valuation (CellExpr.whiskerLeft whiskP (CellExpr.whiskerLeft whiskQ inner)) :=
  linearizeFull_eq_of_saturatedConv valuation (whiskerAssociatorLeftConv whiskP whiskQ inner)

/-- ★ **Associator-right is `linearizeFull`-sound.** -/
theorem whiskerAssociatorRight_linearizeFull {computad : OmegaComputad}
    (valuation : ComputadValuation computad) {dim : Nat}
    (inner : CellExpr computad (dim + 2)) (whiskP whiskQ : CellExpr computad (dim + 1)) :
    linearizeFull valuation (CellExpr.whiskerRight inner (CellExpr.vcomp whiskP whiskQ))
      = linearizeFull valuation (CellExpr.whiskerRight (CellExpr.whiskerRight inner whiskP) whiskQ) :=
  linearizeFull_eq_of_saturatedConv valuation (whiskerAssociatorRightConv inner whiskP whiskQ)

/-- ★ **Whisker-commute is `linearizeFull`-sound.** -/
theorem whiskerCommute_linearizeFull {computad : OmegaComputad}
    (valuation : ComputadValuation computad) {dim : Nat}
    (whiskP : CellExpr computad (dim + 1)) (inner : CellExpr computad (dim + 2))
    (whiskQ : CellExpr computad (dim + 1)) :
    linearizeFull valuation (CellExpr.whiskerRight (CellExpr.whiskerLeft whiskP inner) whiskQ)
      = linearizeFull valuation (CellExpr.whiskerLeft whiskP (CellExpr.whiskerRight inner whiskQ)) :=
  linearizeFull_eq_of_saturatedConv valuation (whiskerCommuteConv whiskP inner whiskQ)

/-! # =========================================================================================
    # L3 — ★ THE UNITOR STOP: the free identity-whisker unitor is chain-refuted (machine-checked)
    # =========================================================================================

The free 1-cell `c = whiskeringGen true` (linearize `[1]`); the inner 2-cell `X = id (id (whiskeringGen false))`
(whose deep source `bs (bs X) = whiskeringGen false` linearizes `[0]`).  The unitor would identify
`whiskerLeft (id c) X` with `X`, but their `linearizeFull` chain tables DIFFER: the whiskered leg's pole spine
records `linearize c = [1]` exactly where `X`'s records `linearize (bs (bs X)) = [0]`. -/

/-- ★★ **THE STOP (chain tables differ).**  `linearizeFull` SEPARATES the free identity-whisker unitor's two legs
(top vector equal, poles differ) — `decide`, zero-axiom. -/
theorem whiskerIdentityUnitorTablesDiffer :
    linearizeFull whiskerDemoValuation
        (CellExpr.whiskerLeft (CellExpr.id (whiskeringGen true))
          (CellExpr.id (CellExpr.id (whiskeringGen false))))
      ≠ linearizeFull whiskerDemoValuation (CellExpr.id (CellExpr.id (whiskeringGen false))) := by
  decide

/-- ★★ **THE STOP (non-convertibility).**  The two legs are NON-convertible over the live `StrictAxiomRel`
(assoc + commute, NO unitor).  Adding the free unitor as a row would identify them — contradicting this, i.e.
falsifying `linearizeFullSoundness`.  So the unitor stays OUT.  Machine-checked, zero-axiom. -/
theorem whiskerIdentityUnitor_not_conv :
    ¬ SaturatedConvOver whiskerDemoComputad (StrictAxiomRel whiskerDemoComputad)
        (CellExpr.whiskerLeft (CellExpr.id (whiskeringGen true))
          (CellExpr.id (CellExpr.id (whiskeringGen false))))
        (CellExpr.id (CellExpr.id (whiskeringGen false))) :=
  not_conv_of_linearizeFull_ne whiskerDemoValuation whiskerIdentityUnitorTablesDiffer

/-- The unitor's TOP vector alone is equal (`rfl`) — the single vector CANNOT see the obstruction (which is why
the shipped `EckmannHiltonWithId.whiskerUnitRel` is single-vector-sound but lives OUTSIDE `StrictAxiomRel`). -/
theorem whiskerIdentityUnitorTop_equal :
    (linearizeFull whiskerDemoValuation
        (CellExpr.whiskerLeft (CellExpr.id (whiskeringGen true))
          (CellExpr.id (CellExpr.id (whiskeringGen false))))).top
      = (linearizeFull whiskerDemoValuation (CellExpr.id (CellExpr.id (whiskeringGen false)))).top := rfl

/-! # =========================================================================================
    # L4 — the honest r19 markers
    # =========================================================================================
-/

/-- ★★★ **LANDED (r19) — the whisker-1-cell associator (both duals) and the whisker left/right commute ARE
`StrictAxiomRel` rows.**  `= true` records the substrate-round landing: three genuine free-strict-2-category
identities that the r18 wall recorded as walled are now live rows, chain-sound via `addCoordinates_assoc`, with
every OMEGA `cases`-row consumer updated in one commit and the shipped ★★ `linearizeFullSoundness` still zero-axiom.
The r18 wall's "non-boundary-parallel => not landable" was too coarse. -/
def fxBunchedBimonoid_whiskerAssociatorAndCommuteLanded : Bool := true

/-- ★★★ **WALLED (r19) — the identity-whisker UNITOR stays OUT of `StrictAxiomRel`, chain-refuted.**  `= false`
records the sole remaining whisker-vs-1-cell residual: `whiskerLeft (id c) X ~ X` is chain-UNSOUND for a free `c`
(`whiskerIdentityUnitor_not_conv`, machine-checked) — landing it as a free row would falsify
`linearizeFullSoundness`.  It routes through the pinned presentation-row / `whiskerUnitRel` path (the M4 cost
table in this file's header), NOT a `StrictAxiomRel` row.  NO fabricated flip. -/
def fxBunchedBimonoid_whiskerIdentityUnitorChainRefutedStaysWalled : Bool := false

end FX1Poly.Polygraph.Omega

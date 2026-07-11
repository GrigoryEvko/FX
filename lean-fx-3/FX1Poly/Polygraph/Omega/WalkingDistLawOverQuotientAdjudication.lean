import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidMatrixSemantics
import FX1Poly.Polygraph.Omega.WalkingDistLawPresentation

/-! # Polygraph/Omega/WalkingDistLawOverQuotientAdjudication — the walking distributive law's latent
over-quotient, adjudicated (OMEGA HOUSE-STYLE SWEEP, WP-BI r4)

★ **The two-monad transport of the walking-monad over-quotient — the largest yield (6 rows).**  The walking
distributive law `<s, t | eta_s, mu_s, eta_t, mu_t, swap>` contains the walking monad TWICE (on `s` and on `t`):
its six monad-internal bare-single-whisker rows — `monadS{UnitUnit,LeftUnitAssoc,RightUnitAssoc}` and
`monadT{...}` — reuse the walking monad's leg shapes at each colour and over-quotient identically.  The RESPECTED
rows are the two Godement composites per colour (`monad{S,T}{Pentagon,RootUnitAssoc}`) and the FOUR genuine Beck
distributive-law axioms (swap-mediated composites).

## The soundness ground: the two-colour `Mat(N)` model with `swap` the symmetry

Model both colours `s`, `t` as single strands (width 1), each unit `= [[]] : 1x0`, each multiplication
`= [[1,1]] : 1x2`, and the distributive law `swap : s.t => t.s` as the SWAP `[[0,1],[1,0]] : 2x2`.  Machine-checked
below: the model respects every genuine distributive-law axiom shipped — the FOUR Beck axioms (each a
swap-mediated composite, both legs equal: Beck-1/2 `[[0,0,1],[1,1,0]]` / `[[0,1,1],[1,0,0]]`, Beck-3/4
`[[1],[0]]` / `[[0],[1]]`), the two Godement composites per colour, AND the six genuine per-colour monoid laws
(associativity + both units) — yet keeps the six monad-internal bare-whisker rows apart (identical separators to
the walking monad).  A model that respects every genuine law shipped yet keeps the six bare rows apart proves
them genuinely distinct: they over-quotient.

## The soundness is PER-COLOUR (the two-colour swap wall does NOT block the monad-internal rows)

The full two-colour 2-cell decision is walled at the two-colour monotone-map model
(`fxDistLaw_fullTwoCellDecisionWalledAtTwoColourMonotoneMap`, in-lane `WalkingDistLawSortNF`), but that wall is
about the SWAP interaction — the monad-internal bare rows are single-colour, decided by each colour's free
non-commutative monoid = Delta (monotone maps), exactly as the walking monad.  The `Mat(N)` model handles the
Beck axioms too (`swap` = symmetry), so the sound sub-theory here is the FULL genuine distributive law minus the
six bare rows.

## The house-style discriminant

Each colour's monad has no self-swap (the `swap` distributes `s` past `t`, not `s` past `s`), so the six
bare-whisker rows are IRREPARABLE by braiding — the correct house style post-composes with the colour's `mu`
(`(eta |> s) . mu_s ~ id_s`), landing on an identity, as the walking monad.

## The honest walls (NAMED)

  * Full isolation over `StrictAxiomRel union DistLawOmegaSoundRow` needs the matMul-associativity Fubini kit
    (the shared wall).  This file ships the machine core modulo that NAMED wall and the NAMED faithfulness
    citations (per-colour Delta / the symmetric-monoidal `Mat(N)`).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin.
The `Mat(N)` kernel and the four label-independent evaluation helpers are REUSED from
`WalkingBunchedBimonoidMatrixSemantics`; only the distributive-law generator table and the fold are new. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # B1 — THE TWO-COLOUR Mat(N) EVALUATION OF THE WALKING DISTRIBUTIVE LAW (probes FIRST)
    # ========================================================================================= -/

/-- The **distributive-law generator matrix table** — each unit `= [[]] : 1x0`, each multiplication
`= [[1,1]] : 1x2`, the distributive law `swap = [[0,1],[1,0]] : 2x2` (the braiding of `s` past `t`).  The two
colours default to `identityMat 1`.  Full seven-arm split — propext-clean. -/
def distLawOmegaGenMatrix : DistLawGenLabel → BunchedBimonoidMat
  | .colourS => bunchedBimonoidIdentityMat 1
  | .colourT => bunchedBimonoidIdentityMat 1
  | .etaS => { rows := 1, cols := 0, entries := [[]] }
  | .muS => { rows := 1, cols := 2, entries := [[1, 1]] }
  | .etaT => { rows := 1, cols := 0, entries := [[]] }
  | .muT => { rows := 1, cols := 2, entries := [[1, 1]] }
  | .swap => { rows := 2, cols := 2, entries := [[0, 1], [1, 0]] }

/-- Evaluate a **distributive-law generator**: width 1 at label-dim 0, the generator matrix at label-dim 1,
`Unit` above. -/
def distLawOmegaEvalGen : (labelDim : Nat) → DistLawGenLabel →
    BunchedBimonoidEvalCarrier labelDim → BunchedBimonoidEvalCarrier labelDim →
    BunchedBimonoidEvalCarrier (labelDim + 1)
  | 0, _, _, _ => (1 : Nat)
  | 1, label, _, _ => distLawOmegaGenMatrix label
  | _ + 2, _, _, _ => ()

/-- ★ **The distributive-law matrix evaluation** — the two-monad+symmetry functor into `Mat(N)`.  A total
structural fold reusing the shared motive and the four label-independent helpers; only the generator table is
distributive-law-specific.  Propext-clean. -/
def distLawOmegaEvalCell : {dim : Nat} → CellExpr distLawOmegaComputad dim →
    BunchedBimonoidEvalCarrier dim
  | _, .ofMode _ => ()
  | _, .gen (dim := labelDim) label source target =>
      distLawOmegaEvalGen labelDim label (distLawOmegaEvalCell source) (distLawOmegaEvalCell target)
  | _, .id (dim := d) cell => bunchedBimonoidEvalId d (distLawOmegaEvalCell cell)
  | _, .vcomp (dim := d) leftCell rightCell =>
      bunchedBimonoidEvalVcomp d (distLawOmegaEvalCell leftCell) (distLawOmegaEvalCell rightCell)
  | _, .whiskerLeft (dim := d) whiskerCell cell =>
      bunchedBimonoidEvalWhiskerLeft d (distLawOmegaEvalCell whiskerCell) (distLawOmegaEvalCell cell)
  | _, .whiskerRight (dim := d) cell whiskerCell =>
      bunchedBimonoidEvalWhiskerRight d (distLawOmegaEvalCell cell) (distLawOmegaEvalCell whiskerCell)

/-! ## The generator matrices + the 4 Beck axioms (RESPECTED, `rfl`) -/

/-- `swap : s.t => t.s` evaluates to the symmetry `[[0,1],[1,0]] : 2x2`. -/
theorem distLawOmegaSwapGen_matrix :
    distLawOmegaEvalCell distLawSwapGen = { rows := 2, cols := 2, entries := [[0, 1], [1, 0]] } := rfl

/-- Beck-1 is matrix-respected (both `[[0,0,1],[1,1,0]]`). -/
theorem distLawOmegaMatrixRespectsBeckOne :
    distLawOmegaEvalCell distLawBeckOneLeftLeg = distLawOmegaEvalCell distLawBeckOneRightLeg := rfl

/-- Beck-2 is matrix-respected (both `[[0,1,1],[1,0,0]]`). -/
theorem distLawOmegaMatrixRespectsBeckTwo :
    distLawOmegaEvalCell distLawBeckTwoLeftLeg = distLawOmegaEvalCell distLawBeckTwoRightLeg := rfl

/-- Beck-3 is matrix-respected (both `[[1],[0]]`). -/
theorem distLawOmegaMatrixRespectsBeckThree :
    distLawOmegaEvalCell distLawBeckThreeLeftLeg = distLawOmegaEvalCell distLawBeckThreeRightLeg := rfl

/-- Beck-4 is matrix-respected (both `[[0],[1]]`). -/
theorem distLawOmegaMatrixRespectsBeckFour :
    distLawOmegaEvalCell distLawBeckFourLeftLeg = distLawOmegaEvalCell distLawBeckFourRightLeg := rfl

/-! ## The 4 Godement composites per colour (RESPECTED, `rfl`) -/

/-- `monadS pentagon` is matrix-respected. -/
theorem distLawOmegaMatrixRespectsMonadSPentagon :
    distLawOmegaEvalCell (distLawPentagonLeftLegOf distLawSGen distLawMuSGen)
      = distLawOmegaEvalCell (distLawPentagonRightLegOf distLawSGen distLawMuSGen) := rfl

/-- `monadS rootUnitAssoc` is matrix-respected. -/
theorem distLawOmegaMatrixRespectsMonadSRootUnitAssoc :
    distLawOmegaEvalCell (distLawRootUnitAssocLeftLegOf distLawSGen distLawEtaSGen distLawMuSGen)
      = distLawOmegaEvalCell (distLawRootUnitAssocRightLegOf distLawSGen distLawEtaSGen distLawMuSGen) := rfl

/-- `monadT pentagon` is matrix-respected. -/
theorem distLawOmegaMatrixRespectsMonadTPentagon :
    distLawOmegaEvalCell (distLawPentagonLeftLegOf distLawTGen distLawMuTGen)
      = distLawOmegaEvalCell (distLawPentagonRightLegOf distLawTGen distLawMuTGen) := rfl

/-- `monadT rootUnitAssoc` is matrix-respected. -/
theorem distLawOmegaMatrixRespectsMonadTRootUnitAssoc :
    distLawOmegaEvalCell (distLawRootUnitAssocLeftLegOf distLawTGen distLawEtaTGen distLawMuTGen)
      = distLawOmegaEvalCell (distLawRootUnitAssocRightLegOf distLawTGen distLawEtaTGen distLawMuTGen) := rfl

/-! ## The 6 BROKEN monad-internal rows — the two legs are DIFFERENT matrices (per-colour) -/

/-- ★ `monadS unitUnit` legs are DIFFERENT (`eta_s |> s` = `[[0],[1]]` vs `s <| eta_s` = `[[1],[0]]`; entry
`(0,0)`). -/
theorem distLawOmegaMatrixSeparatesMonadSUnitUnit :
    distLawOmegaEvalCell (distLawUnitUnitLeftLegOf distLawSGen distLawEtaSGen)
      ≠ distLawOmegaEvalCell (distLawUnitUnitRightLegOf distLawSGen distLawEtaSGen) :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-- ★ `monadS leftUnitAssoc` legs are DIFFERENT (`mu_s |> s` vs `s <| mu_s`; entry `(0,1)`). -/
theorem distLawOmegaMatrixSeparatesMonadSLeftUnitAssoc :
    distLawOmegaEvalCell (distLawLeftUnitAssocLeftLegOf distLawSGen distLawMuSGen)
      ≠ distLawOmegaEvalCell (distLawLeftUnitAssocRightLegOf distLawSGen distLawMuSGen) :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 1) hmatrix)

/-- ★ `monadS rightUnitAssoc` legs are DIFFERENT (`eta_s |> s.s` vs `s.s <| eta_s`; entry `(0,0)`). -/
theorem distLawOmegaMatrixSeparatesMonadSRightUnitAssoc :
    distLawOmegaEvalCell (distLawRightUnitAssocLeftLegOf distLawSGen distLawEtaSGen)
      ≠ distLawOmegaEvalCell (distLawRightUnitAssocRightLegOf distLawSGen distLawEtaSGen) :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-- ★ `monadT unitUnit` legs are DIFFERENT (`eta_t |> t` vs `t <| eta_t`; entry `(0,0)`). -/
theorem distLawOmegaMatrixSeparatesMonadTUnitUnit :
    distLawOmegaEvalCell (distLawUnitUnitLeftLegOf distLawTGen distLawEtaTGen)
      ≠ distLawOmegaEvalCell (distLawUnitUnitRightLegOf distLawTGen distLawEtaTGen) :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-- ★ `monadT leftUnitAssoc` legs are DIFFERENT (`mu_t |> t` vs `t <| mu_t`; entry `(0,1)`). -/
theorem distLawOmegaMatrixSeparatesMonadTLeftUnitAssoc :
    distLawOmegaEvalCell (distLawLeftUnitAssocLeftLegOf distLawTGen distLawMuTGen)
      ≠ distLawOmegaEvalCell (distLawLeftUnitAssocRightLegOf distLawTGen distLawMuTGen) :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 1) hmatrix)

/-- ★ `monadT rightUnitAssoc` legs are DIFFERENT (`eta_t |> t.t` vs `t.t <| eta_t`; entry `(0,0)`). -/
theorem distLawOmegaMatrixSeparatesMonadTRightUnitAssoc :
    distLawOmegaEvalCell (distLawRightUnitAssocLeftLegOf distLawTGen distLawEtaTGen)
      ≠ distLawOmegaEvalCell (distLawRightUnitAssocRightLegOf distLawTGen distLawEtaTGen) :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-! ## The B1 non-vacuity probes -/

#eval distLawOmegaEvalCell (distLawUnitUnitLeftLegOf distLawSGen distLawEtaSGen)
#eval distLawOmegaEvalCell (distLawUnitUnitRightLegOf distLawSGen distLawEtaSGen)
#eval distLawOmegaEvalCell distLawBeckOneLeftLeg
#eval distLawOmegaEvalCell distLawBeckOneRightLeg

/-! # =========================================================================================
    # B1 (O) — THE OVER-QUOTIENT FORMALIZED: r1 relates matrix-distinct legs on each of the 6 rows
    # ========================================================================================= -/

/-- ★ `monadS unitUnit` OVER-QUOTIENT witness. -/
theorem distLawOmegaBaseRelOverQuotientsMonadSUnitUnit :
    SaturatedConvOverWithId distLawOmegaComputad distLawOmegaBaseRel
        (distLawUnitUnitLeftLegOf distLawSGen distLawEtaSGen)
        (distLawUnitUnitRightLegOf distLawSGen distLawEtaSGen)
      ∧ distLawOmegaEvalCell (distLawUnitUnitLeftLegOf distLawSGen distLawEtaSGen)
        ≠ distLawOmegaEvalCell (distLawUnitUnitRightLegOf distLawSGen distLawEtaSGen) :=
  ⟨distLawMonadSUnitUnitThreeCell, distLawOmegaMatrixSeparatesMonadSUnitUnit⟩

/-- ★ `monadS leftUnitAssoc` OVER-QUOTIENT witness. -/
theorem distLawOmegaBaseRelOverQuotientsMonadSLeftUnitAssoc :
    SaturatedConvOverWithId distLawOmegaComputad distLawOmegaBaseRel
        (distLawLeftUnitAssocLeftLegOf distLawSGen distLawMuSGen)
        (distLawLeftUnitAssocRightLegOf distLawSGen distLawMuSGen)
      ∧ distLawOmegaEvalCell (distLawLeftUnitAssocLeftLegOf distLawSGen distLawMuSGen)
        ≠ distLawOmegaEvalCell (distLawLeftUnitAssocRightLegOf distLawSGen distLawMuSGen) :=
  ⟨distLawMonadSLeftUnitAssocThreeCell, distLawOmegaMatrixSeparatesMonadSLeftUnitAssoc⟩

/-- ★ `monadS rightUnitAssoc` OVER-QUOTIENT witness. -/
theorem distLawOmegaBaseRelOverQuotientsMonadSRightUnitAssoc :
    SaturatedConvOverWithId distLawOmegaComputad distLawOmegaBaseRel
        (distLawRightUnitAssocLeftLegOf distLawSGen distLawEtaSGen)
        (distLawRightUnitAssocRightLegOf distLawSGen distLawEtaSGen)
      ∧ distLawOmegaEvalCell (distLawRightUnitAssocLeftLegOf distLawSGen distLawEtaSGen)
        ≠ distLawOmegaEvalCell (distLawRightUnitAssocRightLegOf distLawSGen distLawEtaSGen) :=
  ⟨distLawMonadSRightUnitAssocThreeCell, distLawOmegaMatrixSeparatesMonadSRightUnitAssoc⟩

/-- ★ `monadT unitUnit` OVER-QUOTIENT witness. -/
theorem distLawOmegaBaseRelOverQuotientsMonadTUnitUnit :
    SaturatedConvOverWithId distLawOmegaComputad distLawOmegaBaseRel
        (distLawUnitUnitLeftLegOf distLawTGen distLawEtaTGen)
        (distLawUnitUnitRightLegOf distLawTGen distLawEtaTGen)
      ∧ distLawOmegaEvalCell (distLawUnitUnitLeftLegOf distLawTGen distLawEtaTGen)
        ≠ distLawOmegaEvalCell (distLawUnitUnitRightLegOf distLawTGen distLawEtaTGen) :=
  ⟨distLawMonadTUnitUnitThreeCell, distLawOmegaMatrixSeparatesMonadTUnitUnit⟩

/-- ★ `monadT leftUnitAssoc` OVER-QUOTIENT witness. -/
theorem distLawOmegaBaseRelOverQuotientsMonadTLeftUnitAssoc :
    SaturatedConvOverWithId distLawOmegaComputad distLawOmegaBaseRel
        (distLawLeftUnitAssocLeftLegOf distLawTGen distLawMuTGen)
        (distLawLeftUnitAssocRightLegOf distLawTGen distLawMuTGen)
      ∧ distLawOmegaEvalCell (distLawLeftUnitAssocLeftLegOf distLawTGen distLawMuTGen)
        ≠ distLawOmegaEvalCell (distLawLeftUnitAssocRightLegOf distLawTGen distLawMuTGen) :=
  ⟨distLawMonadTLeftUnitAssocThreeCell, distLawOmegaMatrixSeparatesMonadTLeftUnitAssoc⟩

/-- ★ `monadT rightUnitAssoc` OVER-QUOTIENT witness. -/
theorem distLawOmegaBaseRelOverQuotientsMonadTRightUnitAssoc :
    SaturatedConvOverWithId distLawOmegaComputad distLawOmegaBaseRel
        (distLawRightUnitAssocLeftLegOf distLawTGen distLawEtaTGen)
        (distLawRightUnitAssocRightLegOf distLawTGen distLawEtaTGen)
      ∧ distLawOmegaEvalCell (distLawRightUnitAssocLeftLegOf distLawTGen distLawEtaTGen)
        ≠ distLawOmegaEvalCell (distLawRightUnitAssocRightLegOf distLawTGen distLawEtaTGen) :=
  ⟨distLawMonadTRightUnitAssocThreeCell, distLawOmegaMatrixSeparatesMonadTRightUnitAssoc⟩

/-- ★★ **THE WALKING-DISTRIBUTIVE-LAW r1 BASE RELATION IS NOT MATRIX-SOUND.**  There exist two 2-cells
convertible under `distLawOmegaBaseRel` whose `Mat(N)` matrices DIFFER (the `monadS unitUnit` row).  Since the
model respects every genuine distributive-law axiom shipped (the 4 Beck axioms, the 4 Godement composites, and
the 6 genuine per-colour monoid laws — machine-checked) it is the faithful invariant that separates the six
bare-whisker monad-internal rows: the over-quotient. -/
theorem distLawOmegaBaseRelRelatesMatrixDistinctLegs :
    ∃ (leftLeg rightLeg : CellExpr distLawOmegaComputad 2),
      SaturatedConvOverWithId distLawOmegaComputad distLawOmegaBaseRel leftLeg rightLeg ∧
      distLawOmegaEvalCell leftLeg ≠ distLawOmegaEvalCell rightLeg :=
  ⟨distLawUnitUnitLeftLegOf distLawSGen distLawEtaSGen, distLawUnitUnitRightLegOf distLawSGen distLawEtaSGen,
    distLawOmegaBaseRelOverQuotientsMonadSUnitUnit.1, distLawOmegaBaseRelOverQuotientsMonadSUnitUnit.2⟩

/-! # =========================================================================================
    # B1 (M) — THE RESTORED SOUNDNESS: the full genuine distributive-law sub-theory (14 rows)
    # =========================================================================================

★ Excise the 6 bare-whisker monad-internal rows; keep the 4 Beck axioms, the 4 Godement composites, and ADD the
6 genuine per-colour monoid LAWS in closed-composite form.  Over this 14-row genuine-law sub-theory `Mat(N)` is
SOUND — every row's two legs share their matrix (`rfl`). -/

/-- Genuine S left-unit LAW `(eta_s |> s) . mu_s`. -/
def distLawOmegaGenuineSLeftUnitLeftLeg : CellExpr distLawOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight distLawEtaSGen distLawSGen) distLawMuSGen
/-- Genuine S left-unit LAW `id_s`. -/
def distLawOmegaGenuineSLeftUnitRightLeg : CellExpr distLawOmegaComputad 2 := CellExpr.id distLawSGen
/-- Genuine S right-unit LAW `(s <| eta_s) . mu_s`. -/
def distLawOmegaGenuineSRightUnitLeftLeg : CellExpr distLawOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft distLawSGen distLawEtaSGen) distLawMuSGen
/-- Genuine S right-unit LAW `id_s`. -/
def distLawOmegaGenuineSRightUnitRightLeg : CellExpr distLawOmegaComputad 2 := CellExpr.id distLawSGen
/-- Genuine S associativity LAW `(mu_s |> s) . mu_s`. -/
def distLawOmegaGenuineSAssocLeftLeg : CellExpr distLawOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight distLawMuSGen distLawSGen) distLawMuSGen
/-- Genuine S associativity LAW `(s <| mu_s) . mu_s`. -/
def distLawOmegaGenuineSAssocRightLeg : CellExpr distLawOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft distLawSGen distLawMuSGen) distLawMuSGen

/-- Genuine T left-unit LAW `(eta_t |> t) . mu_t`. -/
def distLawOmegaGenuineTLeftUnitLeftLeg : CellExpr distLawOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight distLawEtaTGen distLawTGen) distLawMuTGen
/-- Genuine T left-unit LAW `id_t`. -/
def distLawOmegaGenuineTLeftUnitRightLeg : CellExpr distLawOmegaComputad 2 := CellExpr.id distLawTGen
/-- Genuine T right-unit LAW `(t <| eta_t) . mu_t`. -/
def distLawOmegaGenuineTRightUnitLeftLeg : CellExpr distLawOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft distLawTGen distLawEtaTGen) distLawMuTGen
/-- Genuine T right-unit LAW `id_t`. -/
def distLawOmegaGenuineTRightUnitRightLeg : CellExpr distLawOmegaComputad 2 := CellExpr.id distLawTGen
/-- Genuine T associativity LAW `(mu_t |> t) . mu_t`. -/
def distLawOmegaGenuineTAssocLeftLeg : CellExpr distLawOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight distLawMuTGen distLawTGen) distLawMuTGen
/-- Genuine T associativity LAW `(t <| mu_t) . mu_t`. -/
def distLawOmegaGenuineTAssocRightLeg : CellExpr distLawOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft distLawTGen distLawMuTGen) distLawMuTGen

/-- ★ The **genuine-law sub-relation** the matrix RESPECTS: the 4 Beck axioms, the 4 Godement composites (per
colour), and the 6 genuine per-colour monoid LAWS.  The excised 6 bare-whisker monad-internal rows are
DELIBERATELY absent. -/
inductive DistLawOmegaSoundRow :
    {d : Nat} → CellExpr distLawOmegaComputad d → CellExpr distLawOmegaComputad d → Prop where
  /-- Beck-1. -/
  | beckOne : DistLawOmegaSoundRow distLawBeckOneLeftLeg distLawBeckOneRightLeg
  /-- Beck-2. -/
  | beckTwo : DistLawOmegaSoundRow distLawBeckTwoLeftLeg distLawBeckTwoRightLeg
  /-- Beck-3. -/
  | beckThree : DistLawOmegaSoundRow distLawBeckThreeLeftLeg distLawBeckThreeRightLeg
  /-- Beck-4. -/
  | beckFour : DistLawOmegaSoundRow distLawBeckFourLeftLeg distLawBeckFourRightLeg
  /-- monadS pentagon. -/
  | monadSPentagon : DistLawOmegaSoundRow (distLawPentagonLeftLegOf distLawSGen distLawMuSGen)
      (distLawPentagonRightLegOf distLawSGen distLawMuSGen)
  /-- monadS rootUnitAssoc. -/
  | monadSRootUnitAssoc :
      DistLawOmegaSoundRow (distLawRootUnitAssocLeftLegOf distLawSGen distLawEtaSGen distLawMuSGen)
        (distLawRootUnitAssocRightLegOf distLawSGen distLawEtaSGen distLawMuSGen)
  /-- monadT pentagon. -/
  | monadTPentagon : DistLawOmegaSoundRow (distLawPentagonLeftLegOf distLawTGen distLawMuTGen)
      (distLawPentagonRightLegOf distLawTGen distLawMuTGen)
  /-- monadT rootUnitAssoc. -/
  | monadTRootUnitAssoc :
      DistLawOmegaSoundRow (distLawRootUnitAssocLeftLegOf distLawTGen distLawEtaTGen distLawMuTGen)
        (distLawRootUnitAssocRightLegOf distLawTGen distLawEtaTGen distLawMuTGen)
  /-- genuine S left-unit LAW. -/
  | genuineSLeftUnit : DistLawOmegaSoundRow distLawOmegaGenuineSLeftUnitLeftLeg distLawOmegaGenuineSLeftUnitRightLeg
  /-- genuine S right-unit LAW. -/
  | genuineSRightUnit :
      DistLawOmegaSoundRow distLawOmegaGenuineSRightUnitLeftLeg distLawOmegaGenuineSRightUnitRightLeg
  /-- genuine S associativity LAW. -/
  | genuineSAssoc : DistLawOmegaSoundRow distLawOmegaGenuineSAssocLeftLeg distLawOmegaGenuineSAssocRightLeg
  /-- genuine T left-unit LAW. -/
  | genuineTLeftUnit : DistLawOmegaSoundRow distLawOmegaGenuineTLeftUnitLeftLeg distLawOmegaGenuineTLeftUnitRightLeg
  /-- genuine T right-unit LAW. -/
  | genuineTRightUnit :
      DistLawOmegaSoundRow distLawOmegaGenuineTRightUnitLeftLeg distLawOmegaGenuineTRightUnitRightLeg
  /-- genuine T associativity LAW. -/
  | genuineTAssoc : DistLawOmegaSoundRow distLawOmegaGenuineTAssocLeftLeg distLawOmegaGenuineTAssocRightLeg

/-- The **matrix-equality relation** for the distributive law. -/
def distLawOmegaMatrixEq : CellRelOver distLawOmegaComputad :=
  fun {_dim} cellAlpha cellBeta => distLawOmegaEvalCell cellAlpha = distLawOmegaEvalCell cellBeta

/-- ★★ **THE MATRIX EVALUATION RESPECTS THE GENUINE-LAW SUB-CONGRUENCE.**  Each of the 14 rows relates
equal-matrix legs (`rfl`); every congruence closure is `congrArg` on the shared evaluation helper. -/
def distLawOmegaSoundMatrixEvalAbsorbs :
    IsSaturatedCongruenceWithId distLawOmegaComputad DistLawOmegaSoundRow distLawOmegaMatrixEq where
  ofRelation := by intro _dim _cellAlpha _cellBeta row; cases row <;> rfl
  vcompCongrLeft := by
    intro dim _cellAlpha _cellAlpha' cellBeta hconv
    exact congrArg (fun leftMatrix => bunchedBimonoidEvalVcomp dim leftMatrix
      (distLawOmegaEvalCell cellBeta)) hconv
  vcompCongrRight := by
    intro dim cellAlpha _cellBeta _cellBeta' hconv
    exact congrArg (fun rightMatrix => bunchedBimonoidEvalVcomp dim (distLawOmegaEvalCell cellAlpha)
      rightMatrix) hconv
  whiskerLeftCongr := by
    intro dim whiskeringCell _cellBeta _cellBeta' hconv
    exact congrArg (fun cellMatrix => bunchedBimonoidEvalWhiskerLeft dim
      (distLawOmegaEvalCell whiskeringCell) cellMatrix) hconv
  whiskerRightCongr := by
    intro dim _cellAlpha _cellAlpha' whiskeringCell hconv
    exact congrArg (fun cellMatrix => bunchedBimonoidEvalWhiskerRight dim cellMatrix
      (distLawOmegaEvalCell whiskeringCell)) hconv
  idCongr := by
    intro dim _cellAlpha _cellBeta hconv
    exact congrArg (fun subMatrix => bunchedBimonoidEvalId dim subMatrix) hconv
  whiskerLeftWhiskerCongr := by
    intro dim _whiskerAlpha _whiskerAlpha' innerCell hconv
    exact congrArg (fun whiskerMatrix => bunchedBimonoidEvalWhiskerLeft dim whiskerMatrix
      (distLawOmegaEvalCell innerCell)) hconv
  whiskerRightWhiskerCongr := by
    intro dim innerCell _whiskerAlpha _whiskerAlpha' hconv
    exact congrArg (fun whiskerMatrix => bunchedBimonoidEvalWhiskerRight dim
      (distLawOmegaEvalCell innerCell) whiskerMatrix) hconv
  refl := by intro _dim _cell; rfl
  symm := by intro _dim _cellAlpha _cellBeta hconv; exact hconv.symm
  trans := by intro _dim _cellAlpha _cellBeta _cellGamma hleft hright; exact hleft.trans hright

/-- ★★ **RESTORED SOUNDNESS: convertible over the genuine-law sub-theory ⟹ equal matrix.** -/
theorem distLawOmegaMatrixSoundOverSound {dim : Nat}
    {cellAlpha cellBeta : CellExpr distLawOmegaComputad dim}
    (conv : SaturatedConvOverWithId distLawOmegaComputad DistLawOmegaSoundRow cellAlpha cellBeta) :
    distLawOmegaEvalCell cellAlpha = distLawOmegaEvalCell cellBeta :=
  SaturatedConvOverWithId.recInto distLawOmegaSoundMatrixEvalAbsorbs conv

/-! ## The 6 bare-whisker legs are NOT identified by the genuine-law sub-theory -/

/-- `monadS unitUnit` legs are NOT convertible over the genuine-law sub-theory. -/
theorem distLawOmegaSoundRowNotConvertibleMonadSUnitUnit :
    ¬ SaturatedConvOverWithId distLawOmegaComputad DistLawOmegaSoundRow
        (distLawUnitUnitLeftLegOf distLawSGen distLawEtaSGen)
        (distLawUnitUnitRightLegOf distLawSGen distLawEtaSGen) :=
  fun conv => distLawOmegaMatrixSeparatesMonadSUnitUnit (distLawOmegaMatrixSoundOverSound conv)

/-- `monadS leftUnitAssoc` legs are NOT convertible over the genuine-law sub-theory. -/
theorem distLawOmegaSoundRowNotConvertibleMonadSLeftUnitAssoc :
    ¬ SaturatedConvOverWithId distLawOmegaComputad DistLawOmegaSoundRow
        (distLawLeftUnitAssocLeftLegOf distLawSGen distLawMuSGen)
        (distLawLeftUnitAssocRightLegOf distLawSGen distLawMuSGen) :=
  fun conv => distLawOmegaMatrixSeparatesMonadSLeftUnitAssoc (distLawOmegaMatrixSoundOverSound conv)

/-- `monadS rightUnitAssoc` legs are NOT convertible over the genuine-law sub-theory. -/
theorem distLawOmegaSoundRowNotConvertibleMonadSRightUnitAssoc :
    ¬ SaturatedConvOverWithId distLawOmegaComputad DistLawOmegaSoundRow
        (distLawRightUnitAssocLeftLegOf distLawSGen distLawEtaSGen)
        (distLawRightUnitAssocRightLegOf distLawSGen distLawEtaSGen) :=
  fun conv => distLawOmegaMatrixSeparatesMonadSRightUnitAssoc (distLawOmegaMatrixSoundOverSound conv)

/-- `monadT unitUnit` legs are NOT convertible over the genuine-law sub-theory. -/
theorem distLawOmegaSoundRowNotConvertibleMonadTUnitUnit :
    ¬ SaturatedConvOverWithId distLawOmegaComputad DistLawOmegaSoundRow
        (distLawUnitUnitLeftLegOf distLawTGen distLawEtaTGen)
        (distLawUnitUnitRightLegOf distLawTGen distLawEtaTGen) :=
  fun conv => distLawOmegaMatrixSeparatesMonadTUnitUnit (distLawOmegaMatrixSoundOverSound conv)

/-- `monadT leftUnitAssoc` legs are NOT convertible over the genuine-law sub-theory. -/
theorem distLawOmegaSoundRowNotConvertibleMonadTLeftUnitAssoc :
    ¬ SaturatedConvOverWithId distLawOmegaComputad DistLawOmegaSoundRow
        (distLawLeftUnitAssocLeftLegOf distLawTGen distLawMuTGen)
        (distLawLeftUnitAssocRightLegOf distLawTGen distLawMuTGen) :=
  fun conv => distLawOmegaMatrixSeparatesMonadTLeftUnitAssoc (distLawOmegaMatrixSoundOverSound conv)

/-- `monadT rightUnitAssoc` legs are NOT convertible over the genuine-law sub-theory. -/
theorem distLawOmegaSoundRowNotConvertibleMonadTRightUnitAssoc :
    ¬ SaturatedConvOverWithId distLawOmegaComputad DistLawOmegaSoundRow
        (distLawRightUnitAssocLeftLegOf distLawTGen distLawEtaTGen)
        (distLawRightUnitAssocRightLegOf distLawTGen distLawEtaTGen) :=
  fun conv => distLawOmegaMatrixSeparatesMonadTRightUnitAssoc (distLawOmegaMatrixSoundOverSound conv)

/-- ★★ **THE r1 DISTRIBUTIVE-LAW PRESENTATION STRICTLY OVER-QUOTIENTS THE GENUINE-LAW SUB-THEORY.**  Witnessed
by the `monadS unitUnit` row: r1 collapses its legs (`DistLawCriticalRow.monadSUnitUnit`), the sound sub-theory
keeps them apart. -/
theorem distLawOmegaBaseRelStrictlyOverQuotientsSound :
    ∃ (leftLeg rightLeg : CellExpr distLawOmegaComputad 2),
      SaturatedConvOverWithId distLawOmegaComputad distLawOmegaBaseRel leftLeg rightLeg ∧
      ¬ SaturatedConvOverWithId distLawOmegaComputad DistLawOmegaSoundRow leftLeg rightLeg :=
  ⟨distLawUnitUnitLeftLegOf distLawSGen distLawEtaSGen, distLawUnitUnitRightLegOf distLawSGen distLawEtaSGen,
    distLawMonadSUnitUnitThreeCell, distLawOmegaSoundRowNotConvertibleMonadSUnitUnit⟩

/-! # =========================================================================================
    # B1 (F) — THE IDENTIFICATION MECHANISM: per-colour `mu`, exercised both ways
    # ========================================================================================= -/

/-- ★ The closed correction of the S left unit is convertible over the genuine-law sub-theory. -/
theorem distLawOmegaGenuineSLeftUnitConvertibleOverSound :
    SaturatedConvOverWithId distLawOmegaComputad DistLawOmegaSoundRow
      distLawOmegaGenuineSLeftUnitLeftLeg distLawOmegaGenuineSLeftUnitRightLeg :=
  SaturatedConvOverWithId.ofRelation DistLawOmegaSoundRow.genuineSLeftUnit

/-- ★ **DERIVED: the closed S left-unit correction's legs share their matrix** (both `[[1]]`). -/
theorem distLawOmegaGenuineSLeftUnitMatrixSharedOverSound :
    distLawOmegaEvalCell distLawOmegaGenuineSLeftUnitLeftLeg
      = distLawOmegaEvalCell distLawOmegaGenuineSLeftUnitRightLeg :=
  distLawOmegaMatrixSoundOverSound distLawOmegaGenuineSLeftUnitConvertibleOverSound

/-- ★★ **THE PER-COLOUR IDENTIFICATION MECHANISM IS `mu` (S-side, both-ways).**  The mu_s-mediated closed
correction IS convertible over the genuine-law sub-theory, the DIRECT `eta_s |> s ~ s <| eta_s` is provably
NOT.  The `swap` distributes `s` past `t`, never `s` past `s`, so it cannot repair the monad-internal row. -/
theorem distLawOmegaMuSIsTheSUnitIdentificationMechanism :
    SaturatedConvOverWithId distLawOmegaComputad DistLawOmegaSoundRow
        distLawOmegaGenuineSLeftUnitLeftLeg distLawOmegaGenuineSLeftUnitRightLeg
      ∧ ¬ SaturatedConvOverWithId distLawOmegaComputad DistLawOmegaSoundRow
          (distLawUnitUnitLeftLegOf distLawSGen distLawEtaSGen)
          (distLawUnitUnitRightLegOf distLawSGen distLawEtaSGen) :=
  ⟨distLawOmegaGenuineSLeftUnitConvertibleOverSound, distLawOmegaSoundRowNotConvertibleMonadSUnitUnit⟩

/-- ★★ **THE GENUINE DISTRIBUTIVE-LAW AXIOMS ARE MODELLED YET THE BARE ROWS ARE SEPARATED.**  `Mat(N)` respects
the Beck-1 axiom and the monadS pentagon yet separates the `monadS unitUnit` legs — a genuine distributive-law
model refuting the bare-whisker monad-internal row. -/
theorem distLawOmegaGenuineLawModelledRowSeparated :
    (distLawOmegaEvalCell distLawBeckOneLeftLeg = distLawOmegaEvalCell distLawBeckOneRightLeg)
      ∧ (distLawOmegaEvalCell (distLawUnitUnitLeftLegOf distLawSGen distLawEtaSGen)
        ≠ distLawOmegaEvalCell (distLawUnitUnitRightLegOf distLawSGen distLawEtaSGen)) :=
  ⟨distLawOmegaMatrixRespectsBeckOne, distLawOmegaMatrixSeparatesMonadSUnitUnit⟩

/-! # =========================================================================================
    # B4 — THE HOMOLOGY NO-IMPACT EVIDENCE (in-lane): the bare rows are abelianization-invisible
    # ========================================================================================= -/

/-- The **abelianized 2-generator multiset** of a distributive-law cell — the `List DistLawGenLabel` of the
generators encountered, the abelianization the homology lane sees.  A total structural fold (the `cellSize`
idiom): a `gen` yields its label; `vcomp` concatenates; whiskering / id descend into the whiskered / sub-cell
only.  Position-blind by construction. -/
def distLawOmegaGenLabels : {dim : Nat} → CellExpr distLawOmegaComputad dim → List DistLawGenLabel
  | _, .ofMode _ => []
  | _, .gen label _ _ => [label]
  | _, .id _ => []
  | _, .vcomp leftCell rightCell => distLawOmegaGenLabels leftCell ++ distLawOmegaGenLabels rightCell
  | _, .whiskerLeft _ cell => distLawOmegaGenLabels cell
  | _, .whiskerRight cell _ => distLawOmegaGenLabels cell

/-- ★★ **HOMOLOGY NO-IMPACT (in-lane evidence): each bare-whisker row's two legs have EQUAL abelianized
generator multisets.**  The six monad-internal rows carry the identical single 2-generator on both legs (they
differ only in whisker POSITION), so the abelianized image is EQUAL and the homology boundary maps are
unchanged — the over-quotient is abelianization-invisible, the H2-WALKERS homology untouched. -/
theorem distLawOmegaOverQuotientRowsAbelianizationEqual :
    distLawOmegaGenLabels (distLawUnitUnitLeftLegOf distLawSGen distLawEtaSGen)
        = distLawOmegaGenLabels (distLawUnitUnitRightLegOf distLawSGen distLawEtaSGen)
      ∧ distLawOmegaGenLabels (distLawLeftUnitAssocLeftLegOf distLawSGen distLawMuSGen)
        = distLawOmegaGenLabels (distLawLeftUnitAssocRightLegOf distLawSGen distLawMuSGen)
      ∧ distLawOmegaGenLabels (distLawRightUnitAssocLeftLegOf distLawSGen distLawEtaSGen)
        = distLawOmegaGenLabels (distLawRightUnitAssocRightLegOf distLawSGen distLawEtaSGen)
      ∧ distLawOmegaGenLabels (distLawUnitUnitLeftLegOf distLawTGen distLawEtaTGen)
        = distLawOmegaGenLabels (distLawUnitUnitRightLegOf distLawTGen distLawEtaTGen)
      ∧ distLawOmegaGenLabels (distLawLeftUnitAssocLeftLegOf distLawTGen distLawMuTGen)
        = distLawOmegaGenLabels (distLawLeftUnitAssocRightLegOf distLawTGen distLawMuTGen)
      ∧ distLawOmegaGenLabels (distLawRightUnitAssocLeftLegOf distLawTGen distLawEtaTGen)
        = distLawOmegaGenLabels (distLawRightUnitAssocRightLegOf distLawTGen distLawEtaTGen) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! # =========================================================================================
    # B2 / B3 / B5 — THE VERDICT / DECISION RE-AUDIT / FAMILY / WALL MARKERS
    # ========================================================================================= -/

/-- ★★ **THE VERDICT (O) — the walking distributive law OVER-QUOTIENTS on SIX monad-internal bare-whisker rows.**
`= true` records `distLawOmegaBaseRelRelatesMatrixDistinctLegs` +
`distLawOmegaBaseRelStrictlyOverQuotientsSound`: the two-monad transport of the walking-monad over-quotient
(three per colour). -/
def fxOmegaHouseStyle_distLawPresentationOverQuotientsSixRows : Bool := true

/-- ★★ **DECISION RE-AUDIT (distributive law) — the shipped decision is 1-cell Parikh (orthogonal, CLEAN); the
2-cell decision is WALLED.**  `= true` records: the shipped `distLawConv_iffSameCount` (NAMED, in-lane
`WalkingDistLawSortNF`) is a 1-CELL word decision (`List DistLawColour`), SOUND but position-BLIND, so it cannot
over-decide the 2-cell rows; the full two-colour 2-cell decision is WALLED
(`fxDistLaw_fullTwoCellDecisionWalledAtTwoColourMonotoneMap`), so NO 2-cell decision exists to over-decide.  The
over-quotient lives ONLY in the presentation `distLawOmegaBaseRel` (which fires the monad-internal
`DistLawCriticalRow`s).  CLEAN — no decision silently re-scoped. -/
def fxOmegaHouseStyle_distLawDecisionIsOneCellParikhCleanTwoCellWalled : Bool := true

/-- ★ **THE SOUND SUB-THEORY: 4 Beck + 4 Godement composites + 6 genuine per-colour monoid LAWS = 14 genuine
rows.**  `= true` records that `Mat(N)` (with `swap` = symmetry) models the FULL genuine distributive law, not
merely the per-colour monoids — the four Beck axioms are matrix-respected too. -/
def fxOmegaHouseStyle_distLawSoundSubTheoryIsFourteenRows : Bool := true

/-- ★ **EACH COLOUR'S MONAD IS IRREPARABLE BY BRAIDING (the swap crosses colours).**  `= true` records
`distLawOmegaGenuineLawModelledRowSeparated` + `distLawOmegaMuSIsTheSUnitIdentificationMechanism`: the `swap`
distributes `s` past `t`, never a colour past itself, so the six bare-whisker monad-internal rows have NO
braiding repair; the only mechanism is post-composition with the colour's `mu`. -/
def fxOmegaHouseStyle_distLawPerColourIrreparableSwapCrossesColours : Bool := true

/-- ★ **THE HOMOLOGY VERDICT (in-lane): NO IMPACT — the six bare rows are abelianization-invisible.**  `= true`
records `distLawOmegaOverQuotientRowsAbelianizationEqual`. -/
def fxOmegaHouseStyle_distLawHomologyNoImpactAbelianizationInvisible : Bool := true

/-- ★ **WALL (honest) — the FULL isolation over `StrictAxiomRel union DistLawOmegaSoundRow` needs the Fubini
kit.**  `= false` — the shared matMul-associativity matrix-algebra wall. -/
def fxOmegaHouseStyle_distLawFullIsolationNeedsStrictLawFubiniKit : Bool := false

/-- ★ **ESTABLISHED (B5) — the walking-distributive-law over-quotient adjudication ledger.**  `= true` records
the scoreboard: OUTCOME (O) machine-decided (6 monad-internal bare-whisker rows over-quotient, three per colour);
restored soundness over the 14-row genuine-law sub-theory (the four Beck axioms matrix-respected with `swap` =
symmetry); mechanism per-colour `mu` (the swap crosses colours, no self-repair); the decision re-audited CLEAN
(1-cell Parikh orthogonal, 2-cell walled); homology NO IMPACT (abelianization-invisible).  Wall NAMED
(strict-law Fubini isolation). -/
def fxOmegaHouseStyle_distLawOverQuotientAdjudicationLedgerShipped : Bool := true

/-! ## The r4 truth-probe outputs -/

#eval distLawOmegaEvalCell distLawOmegaGenuineSAssocLeftLeg
#eval distLawOmegaEvalCell distLawOmegaGenuineSAssocRightLeg
#eval distLawOmegaEvalCell (distLawUnitUnitLeftLegOf distLawTGen distLawEtaTGen)
#eval distLawOmegaEvalCell (distLawUnitUnitRightLegOf distLawTGen distLawEtaTGen)

end FX1Poly.Polygraph.Omega

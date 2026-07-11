import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidMatrixSemantics
import FX1Poly.Polygraph.Omega.WalkingStrongMonadPresentation

/-! # Polygraph/Omega/WalkingStrongMonadOverQuotientAdjudication — the walking strong monad's latent
over-quotient, adjudicated (OMEGA HOUSE-STYLE SWEEP, WP-BI r4)

★ **The t-monad transport of the walking-monad over-quotient, riding the same `Mat(N)`-monoid ground.**  The
walking strong monad `<c, t | eta, mu, st>` embeds the walking monad on `t` verbatim: its three T-monad-internal
presentation rows (`monadUnitUnit`, `monadLeftUnitAssoc`, `monadRightUnitAssoc`) reuse the walking monad's
bare-single-whisker leg shapes exactly, and over-quotient identically.  The RESPECTED rows are the two Godement
composites (`monadPentagon`, `monadRootUnitAssoc`) plus the two GENUINE strength laws (`strengthEta` = Moggi S3,
`strengthMu` = Moggi S4) — closed composites landing on the `t.c` valley, house-style-correct.

## The soundness ground: the two-colour `Mat(N)` model with the strength as the braiding

Model both colours `c`, `t` as single strands (width 1), the unit `eta = [[]] : 1x0`, the multiplication
`mu = [[1,1]] : 1x2`, and the tensorial strength `st : c.t => t.c` as the SWAP `[[0,1],[1,0]] : 2x2` (the strength
IS the DISTLAW swap at `s = c`).  Machine-checked below: the model respects the genuine t-monoid laws
(associativity + both units, both legs `[[1,1,1]]` / `[[1]]`), the two Godement composites, AND both genuine
strength laws (`strengthEta` both `[[0],[1]]`, `strengthMu` both `[[0,1,1],[1,0,0]]` — the three-fold S4 composite
agrees as a map).  Yet it keeps the three bare-whisker t-monad rows apart (identical separators to the walking
monad).  A model that respects every genuine strong-monad law shipped yet keeps the bare rows apart proves them
genuinely distinct: the T-monad bare-whisker rows over-quotient.  The faithful ground truth on the 1-cell side is
the two-colour Parikh word decision (the shipped `strongMonadConv_iffSameCount` — NAMED, in-lane 1-cell; the
2-cell decision is walled at `fxStrong_fullTwoCellDecisionWalledAtTwoColourMonotoneMap`), and on the t-monoid
side the monotone-maps Delta of the embedded walking monad (cross-lane, NAMED).

## The house-style discriminant

The T-monad `t` has NO swap of its own (the strength swaps `c` past `t`, not `t` past `t`), so the three
bare-whisker t-monad rows are IRREPARABLE by braiding — the correct house style post-composes with `mu`
(`(eta |> t) . mu ~ id_t`), landing on an identity, exactly as the walking monad.  The strength rows, by
contrast, ARE stated house-style-correctly (closed composites), which is why they are matrix-respected.

## The honest walls (NAMED)

  * Full isolation over `StrictAxiomRel union StrongMonadOmegaSoundRow` needs the matMul-associativity Fubini kit
    (the shared wall).  This file ships the machine core modulo that NAMED wall and the NAMED faithfulness
    citations (Parikh / Delta).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin.
The `Mat(N)` kernel and the four label-independent evaluation helpers are REUSED from
`WalkingBunchedBimonoidMatrixSemantics`; only the strong-monad generator table and the fold are new. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # B1 — THE TWO-COLOUR Mat(N) EVALUATION OF THE WALKING STRONG MONAD (probes FIRST)
    # ========================================================================================= -/

/-- The **strong-monad generator matrix table** — the declared `Mat(N)` map of each 2-cell generator: the unit
`eta = [[]] : 1x0`, the multiplication `mu = [[1,1]] : 1x2`, the tensorial strength `st = [[0,1],[1,0]] : 2x2`
(the braiding of `c` past `t`).  The two 1-generator colours `c`, `t` default to `identityMat 1` (they never
appear at label-dimension 1 in a real 2-cell; total default).  Full five-arm split — propext-clean. -/
def strongMonadOmegaGenMatrix : StrongMonadGenLabel → BunchedBimonoidMat
  | .contextColour => bunchedBimonoidIdentityMat 1
  | .endoColour => bunchedBimonoidIdentityMat 1
  | .unitEta => { rows := 1, cols := 0, entries := [[]] }
  | .multMu => { rows := 1, cols := 2, entries := [[1, 1]] }
  | .strength => { rows := 2, cols := 2, entries := [[0, 1], [1, 0]] }

/-- Evaluate a **strong-monad generator**: both colours have width 1 at label-dim 0, the generator matrix at
label-dim 1, `Unit` above. -/
def strongMonadOmegaEvalGen : (labelDim : Nat) → StrongMonadGenLabel →
    BunchedBimonoidEvalCarrier labelDim → BunchedBimonoidEvalCarrier labelDim →
    BunchedBimonoidEvalCarrier (labelDim + 1)
  | 0, _, _, _ => (1 : Nat)
  | 1, label, _, _ => strongMonadOmegaGenMatrix label
  | _ + 2, _, _, _ => ()

/-- ★ **The strong-monad matrix evaluation** — the two-colour monoid+strength functor into `Mat(N)`.  A total
structural fold reusing the shared motive and the four label-independent helpers; only the generator table is
strong-monad-specific.  Propext-clean. -/
def strongMonadOmegaEvalCell : {dim : Nat} → CellExpr strongMonadOmegaComputad dim →
    BunchedBimonoidEvalCarrier dim
  | _, .ofMode _ => ()
  | _, .gen (dim := labelDim) label source target =>
      strongMonadOmegaEvalGen labelDim label (strongMonadOmegaEvalCell source) (strongMonadOmegaEvalCell target)
  | _, .id (dim := d) cell => bunchedBimonoidEvalId d (strongMonadOmegaEvalCell cell)
  | _, .vcomp (dim := d) leftCell rightCell =>
      bunchedBimonoidEvalVcomp d (strongMonadOmegaEvalCell leftCell) (strongMonadOmegaEvalCell rightCell)
  | _, .whiskerLeft (dim := d) whiskerCell cell =>
      bunchedBimonoidEvalWhiskerLeft d (strongMonadOmegaEvalCell whiskerCell) (strongMonadOmegaEvalCell cell)
  | _, .whiskerRight (dim := d) cell whiskerCell =>
      bunchedBimonoidEvalWhiskerRight d (strongMonadOmegaEvalCell cell) (strongMonadOmegaEvalCell whiskerCell)

/-! ## The generator matrices (the B1 truth-probe, machine-checked) -/

/-- `eta` evaluates to `[[]] : 1x0`. -/
theorem strongMonadOmegaEtaGen_matrix :
    strongMonadOmegaEvalCell strongMonadEtaGen = { rows := 1, cols := 0, entries := [[]] } := rfl

/-- `mu` evaluates to `[[1,1]] : 1x2`. -/
theorem strongMonadOmegaMuGen_matrix :
    strongMonadOmegaEvalCell strongMonadMuGen = { rows := 1, cols := 2, entries := [[1, 1]] } := rfl

/-- ★★ `st : c.t => t.c` evaluates to the swap `[[0,1],[1,0]] : 2x2` — the genuine braiding of context past
the monad. -/
theorem strongMonadOmegaStrengthGen_matrix :
    strongMonadOmegaEvalCell strongMonadStrengthGen = { rows := 2, cols := 2, entries := [[0, 1], [1, 0]] } :=
  rfl

/-! ## The 4 RESPECTED presentation rows — both legs share the matrix (`rfl`) -/

/-- `monadPentagon` is matrix-respected (both `[[1,1,0,0],[0,0,1,1]]`). -/
theorem strongMonadOmegaMatrixRespectsPentagon :
    strongMonadOmegaEvalCell strongMonadMonadPentagonLeftLeg
      = strongMonadOmegaEvalCell strongMonadMonadPentagonRightLeg := rfl

/-- `monadRootUnitAssoc` is matrix-respected (both `[[1,1],[0,0]]`). -/
theorem strongMonadOmegaMatrixRespectsRootUnitAssoc :
    strongMonadOmegaEvalCell strongMonadMonadRootUnitAssocLeftLeg
      = strongMonadOmegaEvalCell strongMonadMonadRootUnitAssocRightLeg := rfl

/-- ★ the genuine strength eta-law (Moggi S3) is matrix-respected (both `[[0],[1]]`). -/
theorem strongMonadOmegaMatrixRespectsStrengthEta :
    strongMonadOmegaEvalCell strongMonadStrengthEtaLeftLeg
      = strongMonadOmegaEvalCell strongMonadStrengthEtaRightLeg := rfl

/-- ★★ the genuine strength mu-law (Moggi S4, the three-fold composite) is matrix-respected (both
`[[0,1,1],[1,0,0]]`) — the recon-flagged whisker-order correctness risk is discharged: they AGREE as maps. -/
theorem strongMonadOmegaMatrixRespectsStrengthMu :
    strongMonadOmegaEvalCell strongMonadStrengthMuLeftLeg
      = strongMonadOmegaEvalCell strongMonadStrengthMuRightLeg := rfl

/-! ## The 3 BROKEN T-monad rows — the two legs are DIFFERENT matrices (identical separators to the monad) -/

/-- ★ `monadUnitUnit` legs are DIFFERENT (`eta |> t` = `[[0],[1]]` vs `t <| eta` = `[[1],[0]]`; entry `(0,0)`). -/
theorem strongMonadOmegaMatrixSeparatesUnitUnit :
    strongMonadOmegaEvalCell strongMonadMonadUnitUnitLeftLeg
      ≠ strongMonadOmegaEvalCell strongMonadMonadUnitUnitRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-- ★ `monadLeftUnitAssoc` legs are DIFFERENT (`mu |> t` vs `t <| mu`; entry `(0,1)`). -/
theorem strongMonadOmegaMatrixSeparatesLeftUnitAssoc :
    strongMonadOmegaEvalCell strongMonadMonadLeftUnitAssocLeftLeg
      ≠ strongMonadOmegaEvalCell strongMonadMonadLeftUnitAssocRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 1) hmatrix)

/-- ★ `monadRightUnitAssoc` legs are DIFFERENT (`eta |> t.t` vs `t.t <| eta`; entry `(0,0)`). -/
theorem strongMonadOmegaMatrixSeparatesRightUnitAssoc :
    strongMonadOmegaEvalCell strongMonadMonadRightUnitAssocLeftLeg
      ≠ strongMonadOmegaEvalCell strongMonadMonadRightUnitAssocRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-! ## The B1 non-vacuity probes -/

#eval strongMonadOmegaEvalCell strongMonadMonadUnitUnitLeftLeg
#eval strongMonadOmegaEvalCell strongMonadMonadUnitUnitRightLeg
#eval strongMonadOmegaEvalCell strongMonadStrengthMuLeftLeg
#eval strongMonadOmegaEvalCell strongMonadStrengthMuRightLeg

/-! # =========================================================================================
    # B1 (O) — THE OVER-QUOTIENT FORMALIZED: r1 relates matrix-distinct legs on each of the 3 T-monad rows
    # ========================================================================================= -/

/-- ★ `monadUnitUnit` OVER-QUOTIENT witness. -/
theorem strongMonadOmegaBaseRelOverQuotientsUnitUnit :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
        strongMonadMonadUnitUnitLeftLeg strongMonadMonadUnitUnitRightLeg
      ∧ strongMonadOmegaEvalCell strongMonadMonadUnitUnitLeftLeg
        ≠ strongMonadOmegaEvalCell strongMonadMonadUnitUnitRightLeg :=
  ⟨strongMonadMonadUnitUnitResolved.legsConvertible, strongMonadOmegaMatrixSeparatesUnitUnit⟩

/-- ★ `monadLeftUnitAssoc` OVER-QUOTIENT witness. -/
theorem strongMonadOmegaBaseRelOverQuotientsLeftUnitAssoc :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
        strongMonadMonadLeftUnitAssocLeftLeg strongMonadMonadLeftUnitAssocRightLeg
      ∧ strongMonadOmegaEvalCell strongMonadMonadLeftUnitAssocLeftLeg
        ≠ strongMonadOmegaEvalCell strongMonadMonadLeftUnitAssocRightLeg :=
  ⟨strongMonadMonadLeftUnitAssocResolved.legsConvertible, strongMonadOmegaMatrixSeparatesLeftUnitAssoc⟩

/-- ★ `monadRightUnitAssoc` OVER-QUOTIENT witness. -/
theorem strongMonadOmegaBaseRelOverQuotientsRightUnitAssoc :
    SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel
        strongMonadMonadRightUnitAssocLeftLeg strongMonadMonadRightUnitAssocRightLeg
      ∧ strongMonadOmegaEvalCell strongMonadMonadRightUnitAssocLeftLeg
        ≠ strongMonadOmegaEvalCell strongMonadMonadRightUnitAssocRightLeg :=
  ⟨strongMonadMonadRightUnitAssocResolved.legsConvertible, strongMonadOmegaMatrixSeparatesRightUnitAssoc⟩

/-- ★★ **THE WALKING-STRONG-MONAD r1 BASE RELATION IS NOT MATRIX-SOUND.**  There exist two 2-cells convertible
under `strongMonadOmegaBaseRel` whose `Mat(N)` matrices DIFFER (the `monadUnitUnit` row).  Since the model
respects every genuine strong-monad law shipped (the two Godement composites, the two strength laws, and the
three genuine t-monoid laws — machine-checked) it is the faithful invariant that separates the T-monad
bare-whisker rows: the over-quotient. -/
theorem strongMonadOmegaBaseRelRelatesMatrixDistinctLegs :
    ∃ (leftLeg rightLeg : CellExpr strongMonadOmegaComputad 2),
      SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel leftLeg rightLeg ∧
      strongMonadOmegaEvalCell leftLeg ≠ strongMonadOmegaEvalCell rightLeg :=
  ⟨strongMonadMonadUnitUnitLeftLeg, strongMonadMonadUnitUnitRightLeg,
    strongMonadOmegaBaseRelOverQuotientsUnitUnit.1, strongMonadOmegaBaseRelOverQuotientsUnitUnit.2⟩

/-! # =========================================================================================
    # B1 (M) — THE RESTORED SOUNDNESS: the genuine strong-monad LAW sub-theory
    # =========================================================================================

★ Excise the 3 bare-whisker T-monad rows; keep the 2 respected Godement composites, the 2 genuine strength
laws, and ADD the 3 genuine t-monad LAWS in closed-composite form.  Over this 7-row genuine-law sub-theory
`Mat(N)` is SOUND — every row's two legs share their matrix (`rfl`). -/

/-- The **genuine left-unit LAW left leg** `(eta |> t) . mu`. -/
def strongMonadOmegaGenuineLeftUnitLeftLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight strongMonadEtaGen strongMonadEndoTGen) strongMonadMuGen

/-- The **genuine left-unit LAW right leg** `id_t`. -/
def strongMonadOmegaGenuineLeftUnitRightLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.id strongMonadEndoTGen

/-- The **genuine right-unit LAW left leg** `(t <| eta) . mu`. -/
def strongMonadOmegaGenuineRightUnitLeftLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft strongMonadEndoTGen strongMonadEtaGen) strongMonadMuGen

/-- The **genuine right-unit LAW right leg** `id_t`. -/
def strongMonadOmegaGenuineRightUnitRightLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.id strongMonadEndoTGen

/-- The **genuine associativity LAW left leg** `(mu |> t) . mu`. -/
def strongMonadOmegaGenuineAssocLeftLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight strongMonadMuGen strongMonadEndoTGen) strongMonadMuGen

/-- The **genuine associativity LAW right leg** `(t <| mu) . mu`. -/
def strongMonadOmegaGenuineAssocRightLeg : CellExpr strongMonadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft strongMonadEndoTGen strongMonadMuGen) strongMonadMuGen

/-- The genuine left-unit law is matrix-respected (both `[[1]]`). -/
theorem strongMonadOmegaMatrixRespectsGenuineLeftUnit :
    strongMonadOmegaEvalCell strongMonadOmegaGenuineLeftUnitLeftLeg
      = strongMonadOmegaEvalCell strongMonadOmegaGenuineLeftUnitRightLeg := rfl

/-- The genuine right-unit law is matrix-respected (both `[[1]]`). -/
theorem strongMonadOmegaMatrixRespectsGenuineRightUnit :
    strongMonadOmegaEvalCell strongMonadOmegaGenuineRightUnitLeftLeg
      = strongMonadOmegaEvalCell strongMonadOmegaGenuineRightUnitRightLeg := rfl

/-- The genuine associativity law is matrix-respected (both `[[1,1,1]]`). -/
theorem strongMonadOmegaMatrixRespectsGenuineAssoc :
    strongMonadOmegaEvalCell strongMonadOmegaGenuineAssocLeftLeg
      = strongMonadOmegaEvalCell strongMonadOmegaGenuineAssocRightLeg := rfl

/-- ★ The **genuine-law sub-relation** the matrix RESPECTS: the 2 respected Godement composites, the 2 genuine
strength laws, and the 3 genuine t-monad LAWS.  The excised 3 bare-whisker T-monad rows are DELIBERATELY absent.
-/
inductive StrongMonadOmegaSoundRow :
    {d : Nat} → CellExpr strongMonadOmegaComputad d → CellExpr strongMonadOmegaComputad d → Prop where
  /-- monadPentagon. -/
  | monadPentagon : StrongMonadOmegaSoundRow strongMonadMonadPentagonLeftLeg strongMonadMonadPentagonRightLeg
  /-- monadRootUnitAssoc. -/
  | monadRootUnitAssoc :
      StrongMonadOmegaSoundRow strongMonadMonadRootUnitAssocLeftLeg strongMonadMonadRootUnitAssocRightLeg
  /-- the genuine strength eta-law (Moggi S3). -/
  | strengthEta : StrongMonadOmegaSoundRow strongMonadStrengthEtaLeftLeg strongMonadStrengthEtaRightLeg
  /-- the genuine strength mu-law (Moggi S4). -/
  | strengthMu : StrongMonadOmegaSoundRow strongMonadStrengthMuLeftLeg strongMonadStrengthMuRightLeg
  /-- the genuine t-monad left-unit LAW. -/
  | genuineLeftUnit :
      StrongMonadOmegaSoundRow strongMonadOmegaGenuineLeftUnitLeftLeg strongMonadOmegaGenuineLeftUnitRightLeg
  /-- the genuine t-monad right-unit LAW. -/
  | genuineRightUnit :
      StrongMonadOmegaSoundRow strongMonadOmegaGenuineRightUnitLeftLeg strongMonadOmegaGenuineRightUnitRightLeg
  /-- the genuine t-monad associativity LAW. -/
  | genuineAssoc :
      StrongMonadOmegaSoundRow strongMonadOmegaGenuineAssocLeftLeg strongMonadOmegaGenuineAssocRightLeg

/-- The **matrix-equality relation** for the strong monad. -/
def strongMonadOmegaMatrixEq : CellRelOver strongMonadOmegaComputad :=
  fun {_dim} cellAlpha cellBeta => strongMonadOmegaEvalCell cellAlpha = strongMonadOmegaEvalCell cellBeta

/-- ★★ **THE MATRIX EVALUATION RESPECTS THE GENUINE-LAW SUB-CONGRUENCE.**  Each of the 7 rows relates
equal-matrix legs (`rfl`); every congruence closure is `congrArg` on the shared evaluation helper. -/
def strongMonadOmegaSoundMatrixEvalAbsorbs :
    IsSaturatedCongruenceWithId strongMonadOmegaComputad StrongMonadOmegaSoundRow strongMonadOmegaMatrixEq where
  ofRelation := by intro _dim _cellAlpha _cellBeta row; cases row <;> rfl
  vcompCongrLeft := by
    intro dim _cellAlpha _cellAlpha' cellBeta hconv
    exact congrArg (fun leftMatrix => bunchedBimonoidEvalVcomp dim leftMatrix
      (strongMonadOmegaEvalCell cellBeta)) hconv
  vcompCongrRight := by
    intro dim cellAlpha _cellBeta _cellBeta' hconv
    exact congrArg (fun rightMatrix => bunchedBimonoidEvalVcomp dim (strongMonadOmegaEvalCell cellAlpha)
      rightMatrix) hconv
  whiskerLeftCongr := by
    intro dim whiskeringCell _cellBeta _cellBeta' hconv
    exact congrArg (fun cellMatrix => bunchedBimonoidEvalWhiskerLeft dim
      (strongMonadOmegaEvalCell whiskeringCell) cellMatrix) hconv
  whiskerRightCongr := by
    intro dim _cellAlpha _cellAlpha' whiskeringCell hconv
    exact congrArg (fun cellMatrix => bunchedBimonoidEvalWhiskerRight dim cellMatrix
      (strongMonadOmegaEvalCell whiskeringCell)) hconv
  idCongr := by
    intro dim _cellAlpha _cellBeta hconv
    exact congrArg (fun subMatrix => bunchedBimonoidEvalId dim subMatrix) hconv
  whiskerLeftWhiskerCongr := by
    intro dim _whiskerAlpha _whiskerAlpha' innerCell hconv
    exact congrArg (fun whiskerMatrix => bunchedBimonoidEvalWhiskerLeft dim whiskerMatrix
      (strongMonadOmegaEvalCell innerCell)) hconv
  whiskerRightWhiskerCongr := by
    intro dim innerCell _whiskerAlpha _whiskerAlpha' hconv
    exact congrArg (fun whiskerMatrix => bunchedBimonoidEvalWhiskerRight dim
      (strongMonadOmegaEvalCell innerCell) whiskerMatrix) hconv
  refl := by intro _dim _cell; rfl
  symm := by intro _dim _cellAlpha _cellBeta hconv; exact hconv.symm
  trans := by intro _dim _cellAlpha _cellBeta _cellGamma hleft hright; exact hleft.trans hright

/-- ★★ **RESTORED SOUNDNESS: convertible over the genuine-law sub-theory ⟹ equal matrix.** -/
theorem strongMonadOmegaMatrixSoundOverSound {dim : Nat}
    {cellAlpha cellBeta : CellExpr strongMonadOmegaComputad dim}
    (conv : SaturatedConvOverWithId strongMonadOmegaComputad StrongMonadOmegaSoundRow cellAlpha cellBeta) :
    strongMonadOmegaEvalCell cellAlpha = strongMonadOmegaEvalCell cellBeta :=
  SaturatedConvOverWithId.recInto strongMonadOmegaSoundMatrixEvalAbsorbs conv

/-! ## The 3 bare-whisker legs are NOT identified by the genuine-law sub-theory -/

/-- `monadUnitUnit` legs are NOT convertible over the genuine-law sub-theory. -/
theorem strongMonadOmegaSoundRowNotConvertibleUnitUnit :
    ¬ SaturatedConvOverWithId strongMonadOmegaComputad StrongMonadOmegaSoundRow
        strongMonadMonadUnitUnitLeftLeg strongMonadMonadUnitUnitRightLeg :=
  fun conv => strongMonadOmegaMatrixSeparatesUnitUnit (strongMonadOmegaMatrixSoundOverSound conv)

/-- `monadLeftUnitAssoc` legs are NOT convertible over the genuine-law sub-theory. -/
theorem strongMonadOmegaSoundRowNotConvertibleLeftUnitAssoc :
    ¬ SaturatedConvOverWithId strongMonadOmegaComputad StrongMonadOmegaSoundRow
        strongMonadMonadLeftUnitAssocLeftLeg strongMonadMonadLeftUnitAssocRightLeg :=
  fun conv => strongMonadOmegaMatrixSeparatesLeftUnitAssoc (strongMonadOmegaMatrixSoundOverSound conv)

/-- `monadRightUnitAssoc` legs are NOT convertible over the genuine-law sub-theory. -/
theorem strongMonadOmegaSoundRowNotConvertibleRightUnitAssoc :
    ¬ SaturatedConvOverWithId strongMonadOmegaComputad StrongMonadOmegaSoundRow
        strongMonadMonadRightUnitAssocLeftLeg strongMonadMonadRightUnitAssocRightLeg :=
  fun conv => strongMonadOmegaMatrixSeparatesRightUnitAssoc (strongMonadOmegaMatrixSoundOverSound conv)

/-- ★★ **THE r1 STRONG-MONAD PRESENTATION STRICTLY OVER-QUOTIENTS THE GENUINE-LAW SUB-THEORY.**  Witnessed by
the `monadUnitUnit` row: r1 collapses its legs (`StrongMonadCriticalRow.monadUnitUnit`), the sound sub-theory
keeps them apart. -/
theorem strongMonadOmegaBaseRelStrictlyOverQuotientsSound :
    ∃ (leftLeg rightLeg : CellExpr strongMonadOmegaComputad 2),
      SaturatedConvOverWithId strongMonadOmegaComputad strongMonadOmegaBaseRel leftLeg rightLeg ∧
      ¬ SaturatedConvOverWithId strongMonadOmegaComputad StrongMonadOmegaSoundRow leftLeg rightLeg :=
  ⟨strongMonadMonadUnitUnitLeftLeg, strongMonadMonadUnitUnitRightLeg,
    strongMonadMonadUnitUnitResolved.legsConvertible, strongMonadOmegaSoundRowNotConvertibleUnitUnit⟩

/-! # =========================================================================================
    # B1 (F) — THE IDENTIFICATION MECHANISM: `mu` for the T-monad, exercised both ways
    # ========================================================================================= -/

/-- ★ The closed correction of the left unit is convertible over the genuine-law sub-theory. -/
theorem strongMonadOmegaGenuineLeftUnitConvertibleOverSound :
    SaturatedConvOverWithId strongMonadOmegaComputad StrongMonadOmegaSoundRow
      strongMonadOmegaGenuineLeftUnitLeftLeg strongMonadOmegaGenuineLeftUnitRightLeg :=
  SaturatedConvOverWithId.ofRelation StrongMonadOmegaSoundRow.genuineLeftUnit

/-- ★ **DERIVED: the closed left-unit correction's legs share their matrix** (both `[[1]]`). -/
theorem strongMonadOmegaGenuineLeftUnitMatrixSharedOverSound :
    strongMonadOmegaEvalCell strongMonadOmegaGenuineLeftUnitLeftLeg
      = strongMonadOmegaEvalCell strongMonadOmegaGenuineLeftUnitRightLeg :=
  strongMonadOmegaMatrixSoundOverSound strongMonadOmegaGenuineLeftUnitConvertibleOverSound

/-- ★★ **THE T-MONAD IDENTIFICATION MECHANISM IS `mu` (both-ways).**  The mu-mediated closed correction IS
convertible over the genuine-law sub-theory, the DIRECT `eta |> t ~ t <| eta` is provably NOT. -/
theorem strongMonadOmegaMuIsTheUnitIdentificationMechanism :
    SaturatedConvOverWithId strongMonadOmegaComputad StrongMonadOmegaSoundRow
        strongMonadOmegaGenuineLeftUnitLeftLeg strongMonadOmegaGenuineLeftUnitRightLeg
      ∧ ¬ SaturatedConvOverWithId strongMonadOmegaComputad StrongMonadOmegaSoundRow
          strongMonadMonadUnitUnitLeftLeg strongMonadMonadUnitUnitRightLeg :=
  ⟨strongMonadOmegaGenuineLeftUnitConvertibleOverSound, strongMonadOmegaSoundRowNotConvertibleUnitUnit⟩

/-- ★★ **THE GENUINE STRONG-MONAD LAWS ARE MODELLED YET THE BARE T-ROW IS SEPARATED.**  `Mat(N)` respects both
the `strengthEta` law (`[[0],[1]]`) and the `monadPentagon` yet separates the `monadUnitUnit` legs — a genuine
strong-monad model refuting the bare-whisker T-row. -/
theorem strongMonadOmegaGenuineLawModelledRowSeparated :
    (strongMonadOmegaEvalCell strongMonadStrengthEtaLeftLeg
        = strongMonadOmegaEvalCell strongMonadStrengthEtaRightLeg)
      ∧ (strongMonadOmegaEvalCell strongMonadMonadUnitUnitLeftLeg
        ≠ strongMonadOmegaEvalCell strongMonadMonadUnitUnitRightLeg) :=
  ⟨strongMonadOmegaMatrixRespectsStrengthEta, strongMonadOmegaMatrixSeparatesUnitUnit⟩

/-! # =========================================================================================
    # B4 — THE HOMOLOGY NO-IMPACT EVIDENCE (in-lane): the T-monad rows are abelianization-invisible
    # ========================================================================================= -/

/-- The **abelianized 2-generator count** of a strong-monad cell — `(#eta, #mu, #st)`, the abelianization the
homology lane sees.  A total structural fold (the `cellSize` idiom): a `gen` counts its label (`unitEta`,
`multMu`, `strength`; colours count nothing at label-dim 2); `vcomp` sums; whiskering / id descend into the
whiskered / sub-cell only.  Position-blind by construction. -/
def strongMonadOmegaTwoCellGenCount : {dim : Nat} → CellExpr strongMonadOmegaComputad dim → Nat × Nat × Nat
  | _, .ofMode _ => (0, 0, 0)
  | _, .gen label _ _ => match label with
      | .unitEta => (1, 0, 0)
      | .multMu => (0, 1, 0)
      | .strength => (0, 0, 1)
      | .contextColour => (0, 0, 0)
      | .endoColour => (0, 0, 0)
  | _, .id _ => (0, 0, 0)
  | _, .vcomp leftCell rightCell =>
      ((strongMonadOmegaTwoCellGenCount leftCell).1 + (strongMonadOmegaTwoCellGenCount rightCell).1,
       (strongMonadOmegaTwoCellGenCount leftCell).2.1 + (strongMonadOmegaTwoCellGenCount rightCell).2.1,
       (strongMonadOmegaTwoCellGenCount leftCell).2.2 + (strongMonadOmegaTwoCellGenCount rightCell).2.2)
  | _, .whiskerLeft _ cell => strongMonadOmegaTwoCellGenCount cell
  | _, .whiskerRight cell _ => strongMonadOmegaTwoCellGenCount cell

/-- ★★ **HOMOLOGY NO-IMPACT (in-lane evidence): each T-monad over-quotient row's two legs have EQUAL abelianized
counts.**  The three bare-whisker rows carry equal `(#eta, #mu, #st)` on both legs (they differ only in whisker
POSITION), so the abelianized image is EQUAL and the homology boundary maps are unchanged — the over-quotient is
abelianization-invisible, the H2-WALKERS homology untouched. -/
theorem strongMonadOmegaOverQuotientRowsAbelianizationEqual :
    strongMonadOmegaTwoCellGenCount strongMonadMonadUnitUnitLeftLeg
        = strongMonadOmegaTwoCellGenCount strongMonadMonadUnitUnitRightLeg
      ∧ strongMonadOmegaTwoCellGenCount strongMonadMonadLeftUnitAssocLeftLeg
        = strongMonadOmegaTwoCellGenCount strongMonadMonadLeftUnitAssocRightLeg
      ∧ strongMonadOmegaTwoCellGenCount strongMonadMonadRightUnitAssocLeftLeg
        = strongMonadOmegaTwoCellGenCount strongMonadMonadRightUnitAssocRightLeg :=
  ⟨rfl, rfl, rfl⟩

/-! # =========================================================================================
    # B2 / B3 / B5 — THE VERDICT / DECISION RE-AUDIT / FAMILY-FLAG / WALL MARKERS
    # ========================================================================================= -/

/-- ★★ **THE VERDICT (O) — the walking strong monad OVER-QUOTIENTS on 3 T-monad bare-whisker rows.**  `= true`
records `strongMonadOmegaBaseRelRelatesMatrixDistinctLegs` + `strongMonadOmegaBaseRelStrictlyOverQuotientsSound`:
the t-monad transport of the walking-monad over-quotient. -/
def fxOmegaHouseStyle_strongPresentationOverQuotientsThreeTMonadRows : Bool := true

/-- ★★ **DECISION RE-AUDIT (strong monad) — the shipped decision is 1-cell Parikh (orthogonal, CLEAN); the
2-cell decision is WALLED.**  `= true` records: the shipped `strongMonadConv_iffSameCount` (NAMED, in-lane
`WalkingStrongMonadPresentation`) is a 1-CELL word decision (`List StrongMonadColour`), SOUND but position-BLIND
(word counts do not see whisker order), so it cannot over-decide the 2-cell rows; the 2-cell decision is WALLED
(`fxStrong_fullTwoCellDecisionWalledAtTwoColourMonotoneMap`), so NO 2-cell decision exists to over-decide.  The
over-quotient lives ONLY in the presentation `strongMonadOmegaBaseRel` (which fires the T-monad
`StrongMonadCriticalRow`s).  CLEAN — no decision silently re-scoped. -/
def fxOmegaHouseStyle_strongDecisionIsOneCellParikhCleanTwoCellWalled : Bool := true

/-- ★ **THE SOUND SUB-THEORY: 2 composites + 2 strength laws + 3 genuine t-monad LAWS = 7 genuine rows.** -/
def fxOmegaHouseStyle_strongSoundSubTheoryIsSevenRows : Bool := true

/-- ★ **THE T-MONAD IS IRREPARABLE BY BRAIDING (the strength swaps `c` past `t`, not `t` past `t`).**  `= true`
records `strongMonadOmegaGenuineLawModelledRowSeparated` + `strongMonadOmegaMuIsTheUnitIdentificationMechanism`:
the T-monad `t` has no self-swap, so the 3 bare-whisker T-rows have NO braiding repair; the only mechanism is
post-composition with `mu`.  (The strength `st` repairs `c`-vs-`t` order, NOT `t`-vs-`t`.) -/
def fxOmegaHouseStyle_strongTMonadIrreparableNoSelfSwap : Bool := true

/-- ★ **THE HOMOLOGY VERDICT (in-lane): NO IMPACT — the T-monad over-quotient rows are abelianization-invisible.**
`= true` records `strongMonadOmegaOverQuotientRowsAbelianizationEqual`. -/
def fxOmegaHouseStyle_strongHomologyNoImpactAbelianizationInvisible : Bool := true

/-- ★ **WALL (honest) — the FULL isolation over `StrictAxiomRel union StrongMonadOmegaSoundRow` needs the Fubini
kit.**  `= false` — the shared matMul-associativity matrix-algebra wall. -/
def fxOmegaHouseStyle_strongFullIsolationNeedsStrictLawFubiniKit : Bool := false

/-- ★ **ESTABLISHED (B5) — the walking-strong-monad over-quotient adjudication ledger.**  `= true` records the
scoreboard: OUTCOME (O) machine-decided (3 T-monad bare-whisker rows over-quotient); restored soundness over the
7-row genuine-law sub-theory (with the two genuine strength laws matrix-modelled, incl. the S4 three-fold
composite); mechanism `mu` (no t-self-swap repair); the decision re-audited CLEAN (1-cell Parikh orthogonal,
2-cell walled); homology NO IMPACT (abelianization-invisible).  Wall NAMED (strict-law Fubini isolation). -/
def fxOmegaHouseStyle_strongOverQuotientAdjudicationLedgerShipped : Bool := true

/-! ## The r4 truth-probe outputs -/

#eval strongMonadOmegaEvalCell strongMonadOmegaGenuineAssocLeftLeg
#eval strongMonadOmegaEvalCell strongMonadOmegaGenuineAssocRightLeg
#eval strongMonadOmegaTwoCellGenCount strongMonadMonadUnitUnitLeftLeg
#eval strongMonadOmegaTwoCellGenCount strongMonadMonadUnitUnitRightLeg

end FX1Poly.Polygraph.Omega

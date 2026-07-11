import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidMatrixSemantics

/-! # Polygraph/Omega/WalkingBunchedBimonoidOverQuotientAdjudication — the balanced adjudication of the r2
"9-broken-row" soundness flag (WP-BI r3, #2188)

★ **THE OUTCOME IS (O): the r1 22-row congruence genuinely OVER-QUOTIENTS.**  r2 evaluated all 22 r1
critical-pair rows into `Mat(N)` and found a clean split — 13 RESPECTED, 9 BROKEN (`op |> x` vs `x <| op` for a
lone (co)monoid generator).  r2 framed the 9 as an "honest scope boundary" (the matrix is a lossy invariant).
r3 adjudicates that framing decisively.  Three readings were possible:

  * **(M) the r2 evaluation mis-read the legs** — REJECTED.  The r1 legs are bare single whiskers by
    construction (`whiskerRight op x` / `whiskerLeft x op`); r2's `matrixSeparates...` lemmas name the r1 leg
    defs directly, so there is no leg-word slippage.  This file re-confirms the read is faithful and RESTORES a
    sound congruence (the genuine-law sub-theory `BunchedBimonoidSoundRow`, over which the matrix IS sound).
  * **(F) `Mat(N)` is merely an incomplete invariant / the walker genuinely identifies the 9** — REFUTED.  By
    Lafont / Pirashvili / Fox the free bicommutative-bimonoid PROP IS `Mat(N)` (an equivalence, NAMED
    literature), so `Mat(N)`-separation is FAITHFUL ground truth on the additive side, and the map-level
    identification of the a-side legs runs THROUGH `sigma` (the width-2 sigma-mediated corrections), never
    directly — the identification mechanism, machine-exhibited here.
  * **(O) the r1 rows are FALSE in the intended theory — machine-decided.**  The r1 base relation
    `bunchedBimonoidOmegaBaseRel` (which fires each of the 9 rows via `ofRelation (Or.inr row)`) relates
    parallel-but-distinct cofaces that the faithful model `Mat(N)` keeps apart.  Hence the r1 22-row
    `bunchedBimonoidWalkerCoherentPresentation` OVER-IDENTIFIES: it is the congruence it generates (the Lean
    statement is true — the 22 rows ARE resolved in their own congruence) but it is NOT the faithful walking
    bicommutative bimonoid.  The sound sub-congruence is the 13 balanced rows + the two width-2 sigma-naturality
    corrections (`BunchedBimonoidSoundRow`).

## The discriminant vs the r1 four-count (why O, not "just another lossy invariant")

The r1 four-count ALSO "breaks" on a row (the bialgebra B1: `(1,0,1,0) != (2,0,2,0)`), yet B1 is a GENUINE law
— the four-count is not a model (it violates B1).  The matrix is the opposite: it RESPECTS every genuine law
shipped (all 13 balanced incl. B1-B4, plus the two sigma-naturality rows — 15 `rfl` rows) and separates ONLY the
9 non-genuine rows.  A separator that respects every genuine law yet keeps two cells apart proves those two cells
genuinely distinct — hence the 9 rows over-quotient.  The four-count separates a genuine law's legs; the matrix
separates only the non-laws.  That is the machine-checkable difference between "lossy count" and "faithful
model".

## The a/m asymmetry (the commutativity discriminant)

  * **a-side (has `sigma`): the 6 broken a-rows are sigma-REPAIRABLE.**  The width-2 half is shipped: the
    sigma-mediated closed corrections of `addMonadUnitUnit` / `comonoidCounitCounit` ARE r2's width-2
    sigma-naturality rows, and they live in `BunchedBimonoidSoundRow` (convertible + matrix-shared).  The
    width-3 `mu` / `delta` corrections need whiskered `sigma` (the walled hexagon, r4).
  * **m-side (no `sigma`): the 3 broken m-rows are IRREPARABLE.**  The free non-commutative monoid on `m` is
    Delta_+ (monotone maps); `eta |> m` and `m <| eta` are the two distinct cofaces delta_0, delta_1, with no
    swap to mediate.  They have NO categorical repair and must be retracted from the decided m-congruence (the
    monad-LAW congruence, NOT the r1 m-critical-rows) — see the m-marker re-audit below.

## The honest walls (NAMED at their exact nodes)

  * Full isolation over `StrictAxiomRel union BunchedBimonoidSoundRow` needs the matMul-associativity Fubini kit
    (r2's `fxBunchedBimonoid_matrixStrictLawExtensionReached = false`, r4).  This file ships the machine core
    (r1 relates a matrix-distinct pair; the genuine-law sub-theory keeps the 9 apart) modulo that NAMED wall and
    the NAMED faithfulness citation (Lafont / Pirashvili / Fox).
  * The width-3 block naturality + Yang-Baxter hexagon stays walled (r2's
    `fxBunchedBimonoid_matrixHexagonReached = false`).
  * Matrix completeness (equal matrix => convertible) is the spider NF; r3 RE-SCOPES its target from the r1
    22-row congruence to the sound sub-theory.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # B1 (O) — THE OVER-QUOTIENT FORMALIZED: r1 relates matrix-distinct legs on each of the 9 rows
    # =========================================================================================

★ **Each of the 9 broken rows is an OVER-QUOTIENT WITNESS: its legs are convertible under the r1 base relation
`bunchedBimonoidOmegaBaseRel` (from r1's shipped per-pair resolution) yet evaluate to DIFFERENT `Mat(N)` maps
(from r2's shipped separation).**  This upgrades r2's framing ("the matrix is not a model of the full
congruence") to the r3 verdict ("the r1 congruence is not matrix-sound — it identifies pairs the faithful model
separates").  Each proof is a pair `(r1-convertibility, r2-separation)`; both components are already shipped and
zero-axiom, so the witnesses are `rfl`-grade assemblies. -/

/-- ★ monoid-`m` `unitUnit` OVER-QUOTIENT witness: `eta_m |> m` and `m <| eta_m` are convertible under the r1
base relation yet are the distinct maps `eta (x) 1 != 1 (x) eta`. -/
theorem bunchedBimonoidBaseRelOverQuotientsMultMonadUnitUnit :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel
        bunchedBimonoidMultMonadUnitUnitLeftLeg bunchedBimonoidMultMonadUnitUnitRightLeg
      ∧ bunchedBimonoidEvalCell bunchedBimonoidMultMonadUnitUnitLeftLeg
        ≠ bunchedBimonoidEvalCell bunchedBimonoidMultMonadUnitUnitRightLeg :=
  ⟨bunchedBimonoidMultMonadUnitUnitResolved.legsConvertible,
    bunchedBimonoidMatrixSeparatesMultMonadUnitUnit⟩

/-- ★ monoid-`m` `leftUnitAssoc` OVER-QUOTIENT witness (`mu (x) 1 != 1 (x) mu`). -/
theorem bunchedBimonoidBaseRelOverQuotientsMultMonadLeftUnitAssoc :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel
        bunchedBimonoidMultMonadLeftUnitAssocLeftLeg bunchedBimonoidMultMonadLeftUnitAssocRightLeg
      ∧ bunchedBimonoidEvalCell bunchedBimonoidMultMonadLeftUnitAssocLeftLeg
        ≠ bunchedBimonoidEvalCell bunchedBimonoidMultMonadLeftUnitAssocRightLeg :=
  ⟨bunchedBimonoidMultMonadLeftUnitAssocResolved.legsConvertible,
    bunchedBimonoidMatrixSeparatesMultMonadLeftUnitAssoc⟩

/-- ★ monoid-`m` `rightUnitAssoc` OVER-QUOTIENT witness (`eta (x) 1 != 1 (x) eta`). -/
theorem bunchedBimonoidBaseRelOverQuotientsMultMonadRightUnitAssoc :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel
        bunchedBimonoidMultMonadRightUnitAssocLeftLeg bunchedBimonoidMultMonadRightUnitAssocRightLeg
      ∧ bunchedBimonoidEvalCell bunchedBimonoidMultMonadRightUnitAssocLeftLeg
        ≠ bunchedBimonoidEvalCell bunchedBimonoidMultMonadRightUnitAssocRightLeg :=
  ⟨bunchedBimonoidMultMonadRightUnitAssocResolved.legsConvertible,
    bunchedBimonoidMatrixSeparatesMultMonadRightUnitAssoc⟩

/-- ★ monoid-`a` `unitUnit` OVER-QUOTIENT witness (`eta (x) 1 != 1 (x) eta`). -/
theorem bunchedBimonoidBaseRelOverQuotientsAddMonadUnitUnit :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel
        bunchedBimonoidAddMonadUnitUnitLeftLeg bunchedBimonoidAddMonadUnitUnitRightLeg
      ∧ bunchedBimonoidEvalCell bunchedBimonoidAddMonadUnitUnitLeftLeg
        ≠ bunchedBimonoidEvalCell bunchedBimonoidAddMonadUnitUnitRightLeg :=
  ⟨bunchedBimonoidAddMonadUnitUnitResolved.legsConvertible,
    bunchedBimonoidMatrixSeparatesAddMonadUnitUnit⟩

/-- ★ monoid-`a` `leftUnitAssoc` OVER-QUOTIENT witness (`mu (x) 1 != 1 (x) mu`). -/
theorem bunchedBimonoidBaseRelOverQuotientsAddMonadLeftUnitAssoc :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel
        bunchedBimonoidAddMonadLeftUnitAssocLeftLeg bunchedBimonoidAddMonadLeftUnitAssocRightLeg
      ∧ bunchedBimonoidEvalCell bunchedBimonoidAddMonadLeftUnitAssocLeftLeg
        ≠ bunchedBimonoidEvalCell bunchedBimonoidAddMonadLeftUnitAssocRightLeg :=
  ⟨bunchedBimonoidAddMonadLeftUnitAssocResolved.legsConvertible,
    bunchedBimonoidMatrixSeparatesAddMonadLeftUnitAssoc⟩

/-- ★ monoid-`a` `rightUnitAssoc` OVER-QUOTIENT witness (`eta (x) 1 != 1 (x) eta`). -/
theorem bunchedBimonoidBaseRelOverQuotientsAddMonadRightUnitAssoc :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel
        bunchedBimonoidAddMonadRightUnitAssocLeftLeg bunchedBimonoidAddMonadRightUnitAssocRightLeg
      ∧ bunchedBimonoidEvalCell bunchedBimonoidAddMonadRightUnitAssocLeftLeg
        ≠ bunchedBimonoidEvalCell bunchedBimonoidAddMonadRightUnitAssocRightLeg :=
  ⟨bunchedBimonoidAddMonadRightUnitAssocResolved.legsConvertible,
    bunchedBimonoidMatrixSeparatesAddMonadRightUnitAssoc⟩

/-- ★ comonoid-`a` `counitCounit` OVER-QUOTIENT witness (`eps (x) 1 != 1 (x) eps`). -/
theorem bunchedBimonoidBaseRelOverQuotientsComonoidCounitCounit :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel
        bunchedBimonoidComonoidCounitCounitLeftLeg bunchedBimonoidComonoidCounitCounitRightLeg
      ∧ bunchedBimonoidEvalCell bunchedBimonoidComonoidCounitCounitLeftLeg
        ≠ bunchedBimonoidEvalCell bunchedBimonoidComonoidCounitCounitRightLeg :=
  ⟨bunchedBimonoidComonoidCounitCounitResolved.legsConvertible,
    bunchedBimonoidMatrixSeparatesComonoidCounitCounit⟩

/-- ★ comonoid-`a` `leftCounitCoassoc` OVER-QUOTIENT witness (`delta (x) 1 != 1 (x) delta`). -/
theorem bunchedBimonoidBaseRelOverQuotientsComonoidLeftCounitCoassoc :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel
        bunchedBimonoidComonoidLeftCounitCoassocLeftLeg bunchedBimonoidComonoidLeftCounitCoassocRightLeg
      ∧ bunchedBimonoidEvalCell bunchedBimonoidComonoidLeftCounitCoassocLeftLeg
        ≠ bunchedBimonoidEvalCell bunchedBimonoidComonoidLeftCounitCoassocRightLeg :=
  ⟨bunchedBimonoidComonoidLeftCounitCoassocResolved.legsConvertible,
    bunchedBimonoidMatrixSeparatesComonoidLeftCounitCoassoc⟩

/-- ★ comonoid-`a` `rightCounitCoassoc` OVER-QUOTIENT witness (`eps (x) 1 != 1 (x) eps`) — the row the r2
truth-probe caught FIRST. -/
theorem bunchedBimonoidBaseRelOverQuotientsComonoidRightCounitCoassoc :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel
        bunchedBimonoidComonoidRightCounitCoassocLeftLeg bunchedBimonoidComonoidRightCounitCoassocRightLeg
      ∧ bunchedBimonoidEvalCell bunchedBimonoidComonoidRightCounitCoassocLeftLeg
        ≠ bunchedBimonoidEvalCell bunchedBimonoidComonoidRightCounitCoassocRightLeg :=
  ⟨bunchedBimonoidComonoidRightCounitCoassocResolved.legsConvertible,
    bunchedBimonoidMatrixSeparatesComonoidRightCounitCoassoc⟩

/-- ★★ **THE r1 BASE RELATION IS NOT MATRIX-SOUND — the machine over-quotient fact.**  There EXIST two 2-cells
convertible under the r1 congruence `bunchedBimonoidOmegaBaseRel` whose `Mat(N)` matrices DIFFER (witnessed by
the monoid-`m` `unitUnit` row).  Since the matrix respects every genuine bicommutative-bimonoid law shipped (the
13 balanced + the 2 sigma-naturality rows, machine-checked) and — by Lafont / Pirashvili / Fox (NAMED) — IS the
faithful free-PROP invariant, this is not "a lossy count breaking" (cf. the four-count on B1) but the r1
congruence identifying genuinely-distinct cells: the OVER-QUOTIENT. -/
theorem bunchedBimonoidBaseRelRelatesMatrixDistinctLegs :
    ∃ (leftLeg rightLeg : CellExpr bunchedBimonoidOmegaComputad 2),
      SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel leftLeg rightLeg ∧
      bunchedBimonoidEvalCell leftLeg ≠ bunchedBimonoidEvalCell rightLeg :=
  ⟨bunchedBimonoidMultMonadUnitUnitLeftLeg, bunchedBimonoidMultMonadUnitUnitRightLeg,
    bunchedBimonoidBaseRelOverQuotientsMultMonadUnitUnit.1,
    bunchedBimonoidBaseRelOverQuotientsMultMonadUnitUnit.2⟩

/-! # =========================================================================================
    # B1 (M) — THE RESTORED SOUNDNESS: the genuine-law sub-theory + the matrix soundness over it
    # =========================================================================================

★ **(M) REJECTED, and the sound congruence RESTORED.**  r2's read was faithful (no leg-word slippage), so the
correction is not to the read but to the CONGRUENCE: excise the 9 over-quotient rows and keep the genuine-law
sub-theory.  `BunchedBimonoidSoundRow` = the 13 balanced rows (r2's `BunchedBimonoidBalancedRow` content) PLUS
the two width-2 sigma-mediated corrections (r2's sigma-naturality rows), over which `Mat(N)` is a SOUND model.
Every one of the 15 rows evaluates its two legs to the SAME matrix (`rfl`), so the respects-congruence datum is
the exact `bunchedBimonoidMatrixEvalAbsorbs` shape one relation wider. -/

/-- ★ The **genuine-law sub-relation** the matrix RESPECTS: the 13 balanced critical rows PLUS the two width-2
sigma-mediated corrections (`sigma` past `eta`, `sigma` past `eps`).  The excised 9 op-commute rows are
DELIBERATELY absent — this is the sound sub-congruence the r1 22-row relation over-quotients.  Each constructor
names the same r1 / r2 legs. -/
inductive BunchedBimonoidSoundRow :
    {d : Nat} → CellExpr bunchedBimonoidOmegaComputad d → CellExpr bunchedBimonoidOmegaComputad d → Prop where
  /-- monoid-`m` pentagon (associativity). -/
  | multMonadPentagon : BunchedBimonoidSoundRow bunchedBimonoidMultMonadPentagonLeftLeg
      bunchedBimonoidMultMonadPentagonRightLeg
  /-- monoid-`m` rootUnitAssoc. -/
  | multMonadRootUnitAssoc : BunchedBimonoidSoundRow bunchedBimonoidMultMonadRootUnitAssocLeftLeg
      bunchedBimonoidMultMonadRootUnitAssocRightLeg
  /-- monoid-`a` pentagon (associativity). -/
  | addMonadPentagon : BunchedBimonoidSoundRow bunchedBimonoidAddMonadPentagonLeftLeg
      bunchedBimonoidAddMonadPentagonRightLeg
  /-- monoid-`a` rootUnitAssoc. -/
  | addMonadRootUnitAssoc : BunchedBimonoidSoundRow bunchedBimonoidAddMonadRootUnitAssocLeftLeg
      bunchedBimonoidAddMonadRootUnitAssocRightLeg
  /-- comonoid-`a` copentagon (coassociativity). -/
  | comonoidCopentagon : BunchedBimonoidSoundRow bunchedBimonoidComonoidCopentagonLeftLeg
      bunchedBimonoidComonoidCopentagonRightLeg
  /-- comonoid-`a` rootCounitCoassoc. -/
  | comonoidRootCounitCoassoc : BunchedBimonoidSoundRow bunchedBimonoidComonoidRootCounitCoassocLeftLeg
      bunchedBimonoidComonoidRootCounitCoassocRightLeg
  /-- bialgebra B1 (delta-of-product with the middle swap). -/
  | bialgebraProduct : BunchedBimonoidSoundRow bunchedBimonoidBialgebraProductLeftLeg
      bunchedBimonoidBialgebraProductRightLeg
  /-- bialgebra B2 (counit-of-product). -/
  | bialgebraCounit : BunchedBimonoidSoundRow bunchedBimonoidBialgebraCounitLeftLeg
      bunchedBimonoidBialgebraCounitRightLeg
  /-- bialgebra B3 (delta-of-unit). -/
  | bialgebraUnit : BunchedBimonoidSoundRow bunchedBimonoidBialgebraUnitLeftLeg
      bunchedBimonoidBialgebraUnitRightLeg
  /-- bialgebra B4 (the bone). -/
  | bialgebraBone : BunchedBimonoidSoundRow bunchedBimonoidBialgebraBoneLeftLeg
      bunchedBimonoidBialgebraBoneRightLeg
  /-- commutativity `mu.sigma = mu`. -/
  | commutativity : BunchedBimonoidSoundRow bunchedBimonoidCommutativityLeftLeg
      bunchedBimonoidCommutativityRightLeg
  /-- cocommutativity `sigma.delta = delta`. -/
  | cocommutativity : BunchedBimonoidSoundRow bunchedBimonoidCocommutativityLeftLeg
      bunchedBimonoidCocommutativityRightLeg
  /-- sigma-involution `sigma.sigma = id`. -/
  | sigmaInvolution : BunchedBimonoidSoundRow bunchedBimonoidSigmaInvolutionLeftLeg
      bunchedBimonoidSigmaInvolutionRightLeg
  /-- ★ the width-2 sigma-vs-unit naturality — the CLOSED correction of the broken `addMonadUnitUnit`
  (`(a <| eta); sigma ~ eta |> a`). -/
  | sigmaEtaNaturality : BunchedBimonoidSoundRow bunchedBimonoidSigmaEtaNaturalityLeftLeg
      bunchedBimonoidSigmaEtaNaturalityRightLeg
  /-- ★ the width-2 sigma-vs-counit naturality — the CLOSED correction of the broken `comonoidCounitCounit`
  (`sigma; (eps |> a) ~ a <| eps`). -/
  | sigmaEpsNaturality : BunchedBimonoidSoundRow bunchedBimonoidSigmaEpsNaturalityLeftLeg
      bunchedBimonoidSigmaEpsNaturalityRightLeg

/-- ★★ **THE MATRIX EVALUATION RESPECTS THE GENUINE-LAW SUB-CONGRUENCE.**  Matrix equality absorbs the
idCongr-extended saturated congruence over `BunchedBimonoidSoundRow`: each of the 15 rows relates equal-matrix
legs (`rfl`) and every congruence closure is `congrArg` on the corresponding evaluation helper — the exact
`bunchedBimonoidMatrixEvalAbsorbs` datum, one relation wider (the two sigma-naturality rows added). -/
def bunchedBimonoidSoundMatrixEvalAbsorbs :
    IsSaturatedCongruenceWithId bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow
      bunchedBimonoidMatrixEq where
  ofRelation := by intro _dim _cellAlpha _cellBeta row; cases row <;> rfl
  vcompCongrLeft := by
    intro dim _cellAlpha _cellAlpha' cellBeta hconv
    exact congrArg (fun leftMatrix => bunchedBimonoidEvalVcomp dim leftMatrix (bunchedBimonoidEvalCell cellBeta))
      hconv
  vcompCongrRight := by
    intro dim cellAlpha _cellBeta _cellBeta' hconv
    exact congrArg (fun rightMatrix => bunchedBimonoidEvalVcomp dim (bunchedBimonoidEvalCell cellAlpha)
      rightMatrix) hconv
  whiskerLeftCongr := by
    intro dim whiskeringCell _cellBeta _cellBeta' hconv
    exact congrArg (fun cellMatrix => bunchedBimonoidEvalWhiskerLeft dim
      (bunchedBimonoidEvalCell whiskeringCell) cellMatrix) hconv
  whiskerRightCongr := by
    intro dim _cellAlpha _cellAlpha' whiskeringCell hconv
    exact congrArg (fun cellMatrix => bunchedBimonoidEvalWhiskerRight dim cellMatrix
      (bunchedBimonoidEvalCell whiskeringCell)) hconv
  idCongr := by
    intro dim _cellAlpha _cellBeta hconv
    exact congrArg (fun subMatrix => bunchedBimonoidEvalId dim subMatrix) hconv
  whiskerLeftWhiskerCongr := by
    intro dim _whiskerAlpha _whiskerAlpha' innerCell hconv
    exact congrArg (fun whiskerMatrix => bunchedBimonoidEvalWhiskerLeft dim whiskerMatrix
      (bunchedBimonoidEvalCell innerCell)) hconv
  whiskerRightWhiskerCongr := by
    intro dim innerCell _whiskerAlpha _whiskerAlpha' hconv
    exact congrArg (fun whiskerMatrix => bunchedBimonoidEvalWhiskerRight dim
      (bunchedBimonoidEvalCell innerCell) whiskerMatrix) hconv
  refl := by intro _dim _cell; rfl
  symm := by intro _dim _cellAlpha _cellBeta hconv; exact hconv.symm
  trans := by intro _dim _cellAlpha _cellBeta _cellGamma hleft hright; exact hleft.trans hright

/-- ★★ **RESTORED SOUNDNESS: convertible over the genuine-law sub-theory ⟹ equal matrix.**  Any two cells
convertible under the congruence generated by `BunchedBimonoidSoundRow` (the 13 balanced + 2 sigma-naturality
rows) share their `Mat(N)` matrix — the fold of `bunchedBimonoidSoundMatrixEvalAbsorbs` through the
least-congruence UP.  This is the SOUND congruence the r1 22-row relation over-quotients (it strictly adds the 9
op-commute rows). -/
theorem bunchedBimonoidMatrixSoundOverSound {dim : Nat}
    {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim}
    (conv : SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow
      cellAlpha cellBeta) :
    bunchedBimonoidEvalCell cellAlpha = bunchedBimonoidEvalCell cellBeta :=
  SaturatedConvOverWithId.recInto bunchedBimonoidSoundMatrixEvalAbsorbs conv

/-! ## The 9 legs are NOT identified by the genuine-law sub-theory (the strict-coarsening lower bound)

Each broken row's legs are provably NOT convertible over `BunchedBimonoidSoundRow` — were they, restored
soundness would force equal matrices, contradicting r2's separation.  Combined with the r1 convertibility, this
witnesses that `bunchedBimonoidOmegaBaseRel` is STRICTLY coarser than the genuine-law sub-congruence: it relates
pairs the sound sub-theory keeps apart.  (Whether the strict 2-cat laws alone bridge them is settled negatively
by `Mat(N)` MODULO the walled matMul-associativity Fubini kit — NAMED, r4.) -/

/-- monoid-`m` `unitUnit` legs are NOT convertible over the genuine-law sub-theory. -/
theorem bunchedBimonoidSoundRowNotConvertibleMultMonadUnitUnit :
    ¬ SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow
        bunchedBimonoidMultMonadUnitUnitLeftLeg bunchedBimonoidMultMonadUnitUnitRightLeg :=
  fun conv => bunchedBimonoidMatrixSeparatesMultMonadUnitUnit (bunchedBimonoidMatrixSoundOverSound conv)

/-- monoid-`m` `leftUnitAssoc` legs are NOT convertible over the genuine-law sub-theory. -/
theorem bunchedBimonoidSoundRowNotConvertibleMultMonadLeftUnitAssoc :
    ¬ SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow
        bunchedBimonoidMultMonadLeftUnitAssocLeftLeg bunchedBimonoidMultMonadLeftUnitAssocRightLeg :=
  fun conv => bunchedBimonoidMatrixSeparatesMultMonadLeftUnitAssoc (bunchedBimonoidMatrixSoundOverSound conv)

/-- monoid-`m` `rightUnitAssoc` legs are NOT convertible over the genuine-law sub-theory. -/
theorem bunchedBimonoidSoundRowNotConvertibleMultMonadRightUnitAssoc :
    ¬ SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow
        bunchedBimonoidMultMonadRightUnitAssocLeftLeg bunchedBimonoidMultMonadRightUnitAssocRightLeg :=
  fun conv => bunchedBimonoidMatrixSeparatesMultMonadRightUnitAssoc (bunchedBimonoidMatrixSoundOverSound conv)

/-- monoid-`a` `unitUnit` legs are NOT convertible over the genuine-law sub-theory. -/
theorem bunchedBimonoidSoundRowNotConvertibleAddMonadUnitUnit :
    ¬ SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow
        bunchedBimonoidAddMonadUnitUnitLeftLeg bunchedBimonoidAddMonadUnitUnitRightLeg :=
  fun conv => bunchedBimonoidMatrixSeparatesAddMonadUnitUnit (bunchedBimonoidMatrixSoundOverSound conv)

/-- monoid-`a` `leftUnitAssoc` legs are NOT convertible over the genuine-law sub-theory. -/
theorem bunchedBimonoidSoundRowNotConvertibleAddMonadLeftUnitAssoc :
    ¬ SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow
        bunchedBimonoidAddMonadLeftUnitAssocLeftLeg bunchedBimonoidAddMonadLeftUnitAssocRightLeg :=
  fun conv => bunchedBimonoidMatrixSeparatesAddMonadLeftUnitAssoc (bunchedBimonoidMatrixSoundOverSound conv)

/-- monoid-`a` `rightUnitAssoc` legs are NOT convertible over the genuine-law sub-theory. -/
theorem bunchedBimonoidSoundRowNotConvertibleAddMonadRightUnitAssoc :
    ¬ SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow
        bunchedBimonoidAddMonadRightUnitAssocLeftLeg bunchedBimonoidAddMonadRightUnitAssocRightLeg :=
  fun conv => bunchedBimonoidMatrixSeparatesAddMonadRightUnitAssoc (bunchedBimonoidMatrixSoundOverSound conv)

/-- comonoid-`a` `counitCounit` legs are NOT convertible over the genuine-law sub-theory. -/
theorem bunchedBimonoidSoundRowNotConvertibleComonoidCounitCounit :
    ¬ SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow
        bunchedBimonoidComonoidCounitCounitLeftLeg bunchedBimonoidComonoidCounitCounitRightLeg :=
  fun conv => bunchedBimonoidMatrixSeparatesComonoidCounitCounit (bunchedBimonoidMatrixSoundOverSound conv)

/-- comonoid-`a` `leftCounitCoassoc` legs are NOT convertible over the genuine-law sub-theory. -/
theorem bunchedBimonoidSoundRowNotConvertibleComonoidLeftCounitCoassoc :
    ¬ SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow
        bunchedBimonoidComonoidLeftCounitCoassocLeftLeg bunchedBimonoidComonoidLeftCounitCoassocRightLeg :=
  fun conv =>
    bunchedBimonoidMatrixSeparatesComonoidLeftCounitCoassoc (bunchedBimonoidMatrixSoundOverSound conv)

/-- comonoid-`a` `rightCounitCoassoc` legs are NOT convertible over the genuine-law sub-theory. -/
theorem bunchedBimonoidSoundRowNotConvertibleComonoidRightCounitCoassoc :
    ¬ SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow
        bunchedBimonoidComonoidRightCounitCoassocLeftLeg bunchedBimonoidComonoidRightCounitCoassocRightLeg :=
  fun conv =>
    bunchedBimonoidMatrixSeparatesComonoidRightCounitCoassoc (bunchedBimonoidMatrixSoundOverSound conv)

/-- ★★ **THE r1 CONGRUENCE STRICTLY OVER-QUOTIENTS THE GENUINE-LAW SUB-THEORY.**  There exist two 2-cells
convertible under `bunchedBimonoidOmegaBaseRel` (the r1 22-row congruence) yet PROVABLY NOT convertible under
`BunchedBimonoidSoundRow` (the 13 balanced + 2 sigma-naturality rows) — witnessed by the monoid-`m` `unitUnit`
row.  The genuine-law sub-theory keeps the two legs apart (restored soundness + the map separation); the r1
relation collapses them (via the `multMonadUnitUnit` row).  Machine-airtight and zero-axiom; the extension of
the sub-theory by the strict 2-cat laws is the NAMED r4 Fubini wall. -/
theorem bunchedBimonoidBaseRelStrictlyOverQuotientsSound :
    ∃ (leftLeg rightLeg : CellExpr bunchedBimonoidOmegaComputad 2),
      SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidOmegaBaseRel leftLeg rightLeg ∧
      ¬ SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow leftLeg rightLeg :=
  ⟨bunchedBimonoidMultMonadUnitUnitLeftLeg, bunchedBimonoidMultMonadUnitUnitRightLeg,
    bunchedBimonoidMultMonadUnitUnitResolved.legsConvertible,
    bunchedBimonoidSoundRowNotConvertibleMultMonadUnitUnit⟩

/-! # =========================================================================================
    # B1 (F) — THE IDENTIFICATION-MECHANISM THEOREM: the a-side is repaired THROUGH sigma
    # =========================================================================================

★ **(F) REFUTED — the map-level identification of the a-side legs runs through `sigma`, not directly.**  The
broken a-side rows are NOT genuinely identified as stated (`op |> a != a <| op`); the CORRECT theory relates
them only after inserting the self-braiding.  The width-2 half is fully exhibited: the sigma-mediated closed
corrections live in `BunchedBimonoidSoundRow`, so they ARE convertible there and (by restored soundness) share
their matrix — while the DIRECT rows are provably NOT convertible.  This is the identification MECHANISM: `sigma`
is what closes the a-side, machine-witnessed both ways. -/

/-- ★ The **closed correction of `addMonadUnitUnit`** is convertible over the genuine-law sub-theory —
`(a <| eta); sigma ~ eta |> a`, the sigma-vs-unit naturality row fired through `ofRelation`. -/
theorem bunchedBimonoidAddUnitUnitClosedConvertibleOverSound :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow
      bunchedBimonoidSigmaEtaNaturalityLeftLeg bunchedBimonoidSigmaEtaNaturalityRightLeg :=
  SaturatedConvOverWithId.ofRelation BunchedBimonoidSoundRow.sigmaEtaNaturality

/-- ★ **DERIVED (not assumed): the closed unitUnit correction's legs share their matrix** — from the
convertibility via restored soundness (both `[[0],[1]]`). -/
theorem bunchedBimonoidAddUnitUnitClosedMatrixShared :
    bunchedBimonoidEvalCell bunchedBimonoidSigmaEtaNaturalityLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidSigmaEtaNaturalityRightLeg :=
  bunchedBimonoidMatrixSoundOverSound bunchedBimonoidAddUnitUnitClosedConvertibleOverSound

/-- ★ The **closed correction of `comonoidCounitCounit`** is convertible over the genuine-law sub-theory —
`sigma; (eps |> a) ~ a <| eps`, the sigma-vs-counit naturality row fired through `ofRelation`. -/
theorem bunchedBimonoidAddCounitCounitClosedConvertibleOverSound :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow
      bunchedBimonoidSigmaEpsNaturalityLeftLeg bunchedBimonoidSigmaEpsNaturalityRightLeg :=
  SaturatedConvOverWithId.ofRelation BunchedBimonoidSoundRow.sigmaEpsNaturality

/-- ★ **DERIVED: the closed counitCounit correction's legs share their matrix** — from the convertibility via
restored soundness (both `[[1,0]]`). -/
theorem bunchedBimonoidAddCounitCounitClosedMatrixShared :
    bunchedBimonoidEvalCell bunchedBimonoidSigmaEpsNaturalityLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidSigmaEpsNaturalityRightLeg :=
  bunchedBimonoidMatrixSoundOverSound bunchedBimonoidAddCounitCounitClosedConvertibleOverSound

/-- ★★ **THE IDENTIFICATION MECHANISM IS `sigma` (a-side, both-ways).**  The a-side unitUnit legs are related in
the genuine-law sub-theory ONLY through `sigma`: the sigma-mediated closed correction IS convertible
(`...ClosedConvertibleOverSound`) but the DIRECT `eta |> a ~ a <| eta` is provably NOT
(`bunchedBimonoidSoundRowNotConvertibleAddMonadUnitUnit`).  So `sigma` is the identification mechanism the r1 row
tried (and failed) to bypass — the refutation of F stated as a mechanism, not a bare non-identity. -/
theorem bunchedBimonoidSigmaIsTheAdditiveIdentificationMechanism :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow
        bunchedBimonoidSigmaEtaNaturalityLeftLeg bunchedBimonoidSigmaEtaNaturalityRightLeg
      ∧ ¬ SaturatedConvOverWithId bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow
          bunchedBimonoidAddMonadUnitUnitLeftLeg bunchedBimonoidAddMonadUnitUnitRightLeg :=
  ⟨bunchedBimonoidAddUnitUnitClosedConvertibleOverSound,
    bunchedBimonoidSoundRowNotConvertibleAddMonadUnitUnit⟩

/-! ## The m-side has NO sigma repair (the four-count / matrix genuine-law model, machine-checked)

The multiplicative bunch carries NO swap, so the 3 broken m-rows are irreparable.  `Mat(N)` is a SOUND model of
the genuine m-monoid (it respects the m-pentagon = associativity and the m-rootUnitAssoc = unit law) yet
SEPARATES the 3 m-critical-rows — so those rows are over-quotients of the genuine m-monoid, with no swap to
mediate.  This is the machine core of the m-marker re-audit (B3): the decided m-congruence is the monad-LAW
congruence, not the r1 m-critical-rows. -/

/-- ★★ **THE m-SIDE GENUINE MONOID LAWS ARE MODELLED BUT THE 3 m-ROWS ARE SEPARATED.**  `Mat(N)` respects the
m-pentagon (associativity) AND separates the m-`unitUnit` legs — so it is a model of the genuine m-monoid that
refutes the whisker-commute row.  With no swap on `m`, the 3 m-critical-rows have no categorical repair; they
must be retracted from the decided (monad-LAW) multiplicative congruence. -/
theorem bunchedBimonoidMultiplicativeGenuineLawModelledRowSeparated :
    (bunchedBimonoidEvalCell bunchedBimonoidMultMonadPentagonLeftLeg
        = bunchedBimonoidEvalCell bunchedBimonoidMultMonadPentagonRightLeg)
      ∧ (bunchedBimonoidEvalCell bunchedBimonoidMultMonadUnitUnitLeftLeg
        ≠ bunchedBimonoidEvalCell bunchedBimonoidMultMonadUnitUnitRightLeg) :=
  ⟨bunchedBimonoidMatrixRespectsMultMonadPentagon, bunchedBimonoidMatrixSeparatesMultMonadUnitUnit⟩

/-! # =========================================================================================
    # B2 — THE LEDGER + DOCSTRINGS: the r3 verdict markers (O decided, M rejected, F refuted)
    # ========================================================================================= -/

/-- ★★ **THE VERDICT (O) — the r1 22-row congruence OVER-QUOTIENTS, machine-decided.**  `= true` records
`bunchedBimonoidBaseRelRelatesMatrixDistinctLegs` and `bunchedBimonoidBaseRelStrictlyOverQuotientsSound`: the r1
base relation `bunchedBimonoidOmegaBaseRel` identifies pairs (the 9 op-commute rows' legs) that the faithful
`Mat(N)` model separates and that the genuine-law sub-theory `BunchedBimonoidSoundRow` keeps apart.  The r1
`bunchedBimonoidWalkerCoherentPresentation` is the congruence it generates (its Lean statement is true) but is
NOT the faithful walking bicommutative bimonoid — it over-identifies 9 parallel-but-distinct cofaces. -/
def fxBunchedBimonoid_r1CongruenceOverQuotientsNineRows : Bool := true

/-- ★★ **(M) REJECTED — the r2 read was faithful; the sound congruence is RESTORED.**  `= true` records that r2
did NOT mis-evaluate the legs (its `matrixSeparates...` lemmas name the r1 leg defs directly, and the r1 legs
are bare single whiskers by construction), so the 13/9 split stands.  The correction is to the CONGRUENCE, not
the read: `bunchedBimonoidMatrixSoundOverSound` restores a SOUND congruence (the genuine-law sub-theory
`BunchedBimonoidSoundRow`) by excising the 9 over-quotient rows. -/
def fxBunchedBimonoid_r2ReadFaithfulSoundnessRestored : Bool := true

/-- ★★ **(F) REFUTED — `Mat(N)` is a FAITHFUL separator, not an incomplete invariant.**  `= true` records that
the a-side separations are ground truth: by Lafont / Pirashvili / Fox (NAMED literature) the free
bicommutative-bimonoid PROP IS `Mat(N)`, and the discriminant vs the four-count is machine-checked — the matrix
respects EVERY genuine law shipped (the 13 balanced + 2 sigma-naturality, 15 `rfl` rows) whereas the four-count
violates the genuine bialgebra B1.  A separator that respects every genuine law yet keeps two cells apart proves
them genuinely distinct — so the 9 rows are FALSE, not "matrix-invisible". -/
def fxBunchedBimonoid_matNatFaithfulSeparatorNotIncomplete : Bool := true

/-- ★★ **THE IDENTIFICATION MECHANISM IS `sigma` (a-side, F-flavoured).**  `= true` records
`bunchedBimonoidSigmaIsTheAdditiveIdentificationMechanism`: the a-side unitUnit / counitCounit legs are related
in the genuine-law sub-theory ONLY through the sigma-mediated width-2 closed corrections (convertible +
matrix-shared, DERIVED), while the direct rows are provably non-convertible.  `sigma` closes the a-side; the r1
rows tried to bypass it and thereby over-quotiented. -/
def fxBunchedBimonoid_sigmaIsTheAdditiveIdentificationMechanism : Bool := true

/-- ★ **THE m-SIDE IS IRREPARABLE (no swap).**  `= true` records
`bunchedBimonoidMultiplicativeGenuineLawModelledRowSeparated`: `Mat(N)` models the genuine m-monoid (respects
the m-pentagon associativity) yet separates the m-`unitUnit` legs, and — the multiplicative bunch carrying NO
`sigma` — the 3 m-critical-rows have NO categorical repair.  They are retracted from the decided (monad-LAW)
multiplicative congruence rather than corrected. -/
def fxBunchedBimonoid_multiplicativeRowsHaveNoSigmaRepair : Bool := true

/-- ★ **THE CORRECTED SOUND SUB-THEORY: 13 balanced + 2 sigma-mediated = 15 genuine rows.**  `= true` records
that `BunchedBimonoidSoundRow` (the 13 balanced from r2 plus the two width-2 sigma-naturality corrections) is the
SOUND sub-congruence — the honest replacement for the r1 22-row congruence at the WIDTH-2 scope.  The width-3 `mu`
/ `delta` corrections (the walled hexagon) and matrix completeness (spider NF) extend it to the full faithful
presentation in r4. -/
def fxBunchedBimonoid_soundSubTheoryIsThirteenPlusTwoSigma : Bool := true

/-- ★ **WALL (honest, r4) — the FULL isolation over `StrictAxiomRel union SoundRow` needs the Fubini kit.**
`= false` records that lifting restored soundness from `BunchedBimonoidSoundRow` to
`StrictAxiomRel union BunchedBimonoidSoundRow` (so the 9 rows are provably non-convertible even in the presence
of the strict 2-cat laws, isolating them as the SOLE over-quotient cause) requires proving matMul associativity
/ the identity unit laws / block interchange in `Mat(N)` — the finite-sum Fubini matrix-algebra kit, the same
wall as r2's `fxBunchedBimonoid_matrixStrictLawExtensionReached`.  r3 ships the sub-theory lower bound; the
strict-law extension is r4. -/
def fxBunchedBimonoid_fullIsolationNeedsStrictLawFubiniKit : Bool := false

/-! # =========================================================================================
    # B3 — THE M-MARKER RE-AUDIT: the r1 "Delta decides the multiplicative congruence" claim re-checked
    # =========================================================================================

★ **The r1 marker `fxBunchedBimonoid_multiplicativeDecisionIsMonotoneMapsDelta` re-checked against the outcome
(the marker text quoted verbatim; adjusted ONLY by this additive ledger decl — the shipped marker's name and
`= true` value are UNTOUCHED).**

The r1 marker states, verbatim: "the multiplicative bunch is a bare non-commutative monoid on the single colour
`m`, whose 2-cell word problem is the walking-monad decision — monotone maps / the augmented simplex category
Delta (the `List Nat` / `monadPath_normalForm` model shipped upstream in `MonadCoherentPresentation` /
`MonotoneMap`).  Single-colour, so the two-colour DistLaw wall does NOT apply; transported verbatim, DECIDABLE."

**RE-AUDIT FINDING.**  The shipped Delta decision (`monadDecideSaturatedConvViaMonotoneMap`) is sound+complete
over `MonadSaturatedTwoCellConv`, whose generators (MonadSaturatedConv.lean) are exactly the THREE monad LAWS —
`leftUnit : mu . (eta |> t) ~ id_t`, `rightUnit : mu . (t <| eta) ~ id_t`, `assoc : mu . (mu |> t) ~ mu . (t <|
mu)` — plus `ofFull` (strict-2-cat laws) and congruences.  It does NOT contain `unitUnit` (`eta |> t ~ t <|
eta`).  In the Delta model `eta` = coface, `mu` = codegeneracy, so `eta |> t` = delta_0 and `t <| eta` = delta_1
are DIFFERENT monotone maps (the monad laws force sigma . delta_0 = sigma . delta_1 = id, which does NOT cancel
to delta_0 = delta_1 — sigma is not monic).  So Delta REFUTES the r1 m-critical-rows `multMonad{UnitUnit,
LeftUnitAssoc, RightUnitAssoc}`, the SAME separation `Mat(N)` makes here
(`bunchedBimonoidMultiplicativeGenuineLawModelledRowSeparated`, machine-checked in-lane).

**THE RESCOPE (additive).**  The r1 marker's "Delta decides the multiplicative congruence" is TRUE only when
scoped to the monad-LAW congruence (leftUnit / rightUnit / assoc), which is FINER than and does NOT contain the 3
r1 m-critical-rows.  Those 3 rows are unsound additions RETRACTED from the decided congruence.  The r1 file
imports only `CongruenceWithId` + `StrictAxioms` (never the Delta model), so the r1 claim was NAMED-only — this
re-audit supplies the in-lane machine backing (`Mat(N)` models the genuine m-laws, separates the 3 rows). -/

/-- ★★ **M-MARKER RE-AUDIT (additive rescope) — Delta decides the monad-LAW congruence, the 3 m-critical-rows
are retracted.**  `= true` records the re-audit finding: the shipped Delta decision decides
`MonadSaturatedTwoCellConv` (the monad LAWS leftUnit / rightUnit / assoc), which does NOT contain the r1
m-critical-rows `multMonad{UnitUnit, LeftUnitAssoc, RightUnitAssoc}`; in fact Delta refutes them (delta_0 !=
delta_1), matching the in-lane `Mat(N)` separation
(`bunchedBimonoidMultiplicativeGenuineLawModelledRowSeparated`).  The r1 marker
`fxBunchedBimonoid_multiplicativeDecisionIsMonotoneMapsDelta` (name + `= true` value UNTOUCHED) is hereby scoped
to the monad-LAW congruence; the 3 m-critical-rows are the over-quotient, retracted from the decided
congruence.  Delta model NOT imported (cross-lane — TwoCategory/WalkingMonad); NAMED backing + in-lane matrix
proof only. -/
def fxBunchedBimonoid_multiplicativeMarkerRescopedToMonadLawCongruence : Bool := true

/-- ★★ **CROSS-LANE FLAG (NAME only) — the shipped OmegaComputad monad house-style carries the SAME latent
over-quotient.**  `= true` records that `MonadCoherentPresentation` uses the identical leg shapes
(`monadOmegaUnitUnitLeftLeg = whiskerRight eta t`, `...RightLeg = whiskerLeft t eta`) and places
`eta |> t ~ t <| eta` into `monadOmegaBaseRel` via `MonadCriticalRow.unitUnit` — the same over-quotient the
bunched r2 exposed.  It was never caught because the walking-monad lane only ever built the Delta model over
`MonadSaturatedTwoCellConv` (the monad LAWS), never over `monadOmegaBaseRel` (the critical-row congruence).  The
`WalkingStrongMonad` / `WalkingDistLaw` presentations almost certainly share the house-style defect.  NAME-ONLY:
that lane is cross-lane (FC-3 territory); NOT edited here — flagged for its owner. -/
def fxBunchedBimonoid_monadHouseStyleCarriesSameLatentOverQuotient : Bool := true

/-! # =========================================================================================
    # B4 — THE SPIDER WALL RE-SCOPED to the adjudicated congruence + the census feed
    # =========================================================================================

★ **r2's matrix-completeness wall (spider NF) is RE-SCOPED: its target is the SOUND sub-theory
`BunchedBimonoidSoundRow`, NOT the r1 22-row congruence (which is unsound and cannot be a completeness target).**
The census feed likewise reads from the sound sub-theory, not the over-quotienting 22. -/

/-- ★ **WALL (honest, r4) — matrix COMPLETENESS targets the SOUND sub-theory, re-scoped from the r1 22 rows.**
`= false` records that the converse of `bunchedBimonoidMatrixSoundOverSound` (equal matrix => convertible) — the
Lafont / Pirashvili diagram-to-matrix "spider" NF — is the r4 deliverable, and its honest target is the SOUND
sub-congruence `BunchedBimonoidSoundRow` (the 13 balanced + 2 sigma-naturality, extended by the width-3
corrections), NOT the r1 22-row `bunchedBimonoidOmegaBaseRel` (which over-quotients — an unsound congruence
cannot be a faithful-completeness target).  Re-scopes r2's
`fxBunchedBimonoid_matrixCompletenessIsSpiderNormalFormWall` (name / value untouched) to the adjudicated
congruence. -/
def fxBunchedBimonoid_spiderCompletenessTargetsSoundSubTheory : Bool := false

/-- ★★ **CENSUS FEED RE-SCOPED — the bunched-bimonoid census entry feeds from the SOUND sub-theory.**  `= true`
records that the census tie-in (`SquierFamilyCensus`: `squierFamilyBunchedWalkerPresented`, which currently
bundles the r1 22-row `bunchedBimonoidWalkerCoherentPresentation`) is adjudicated to feed the DECISION / spider
completeness from `BunchedBimonoidSoundRow` (the sound 13+2 sub-congruence), NOT the 22-row congruence.  The r1
census presented-statement stays a true statement about the congruence it generates; but the ADDITIVE / DECIDED
feed to the #2033 matrix-PROP table is the sound sub-theory (`bunchedBimonoidMatrixSoundOverSound`), the
over-quotient rows excised.  Recorded additively; the census decl keeps its name and meaning. -/
def fxBunchedBimonoid_censusFeedIsSoundSubTheoryNotTwentyTwo : Bool := true

/-- ★ **ESTABLISHED (B5) — the r3 over-quotient adjudication ledger.**  `= true` records the complete r3
scoreboard: the OUTCOME is (O) machine-decided (the r1 22-row congruence over-quotients — 9 op-commute rows,
`bunchedBimonoidBaseRelStrictlyOverQuotientsSound`); (M) rejected (r2 read faithful, soundness restored over
`BunchedBimonoidSoundRow`); (F) refuted (`Mat(N)` faithful, `sigma` the a-side identification mechanism); the
m-marker rescoped to the monad-LAW congruence (the 3 m-critical-rows retracted, irreparable); the cross-lane
monad house-style flagged (NAME only); the spider-completeness wall and the census feed re-scoped to the sound
sub-theory.  Every wall NAMED at its node: the strict-law Fubini isolation (r4), the width-3 hexagon (r4),
completeness (spider NF, r4). -/
def fxBunchedBimonoid_overQuotientAdjudicationLedgerShipped : Bool := true

/-! ## The r3 truth-probe outputs (the over-quotient witness, both models, the mechanism) -/

#eval bunchedBimonoidEvalCell bunchedBimonoidMultMonadUnitUnitLeftLeg
#eval bunchedBimonoidEvalCell bunchedBimonoidMultMonadUnitUnitRightLeg
#eval bunchedBimonoidEvalCell bunchedBimonoidSigmaEtaNaturalityLeftLeg
#eval bunchedBimonoidEvalCell bunchedBimonoidSigmaEtaNaturalityRightLeg

end FX1Poly.Polygraph.Omega

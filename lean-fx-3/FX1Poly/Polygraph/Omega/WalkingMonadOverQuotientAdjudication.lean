import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidMatrixSemantics
import FX1Poly.Polygraph.Omega.MonadCoherentPresentation

/-! # Polygraph/Omega/WalkingMonadOverQuotientAdjudication — the walking monad's latent over-quotient,
adjudicated against the faithful monotone-maps model (OMEGA HOUSE-STYLE SWEEP, WP-BI r4)

★ **The r3 cross-lane flag made good.**  The bunched-bimonoid r3 adjudication
(`WalkingBunchedBimonoidOverQuotientAdjudication`) closed with a NAME-ONLY warning:
`fxBunchedBimonoid_monadHouseStyleCarriesSameLatentOverQuotient` — the shipped `MonadCoherentPresentation`
uses the identical bare-single-whisker leg shapes (`whiskerRight eta t` vs `whiskerLeft t eta`) and places
`eta |> t ~ t <| eta` into `monadOmegaBaseRel` via `MonadCriticalRow.unitUnit`, the same over-quotient the
bunched m-side exposed.  This file makes that flag GOOD: it evaluates the walking monad's five presentation
rows into `Mat(N)` (the monoid restriction — a single colour `t`), machine-separates the THREE bare-whisker
rows (`unitUnit`, `leftUnitAssoc`, `rightUnitAssoc` — the r3 flag named only the first), and RESTORES the
sound congruence (the genuine monad LAWS in house-style-correct closed-composite form).

## The correction to the r3 flag: ONE row named, THREE rows broken

The r3 flag (`...OverQuotientAdjudication.lean:535-543`) named ONLY `MonadCriticalRow.unitUnit`.  The audit
finds the walking monad over-quotients on all THREE bare-whisker rows — `leftUnitAssoc` (`mu |> t` vs
`t <| mu`) and `rightUnitAssoc` (`eta |> t.t` vs `t.t <| eta`) are the identical shape and identically
separated.  These are exactly the bunched m-side's three broken rows `multMonad{UnitUnit,LeftUnitAssoc,
RightUnitAssoc}` (the bunched m-generator IS the walking monad, transported verbatim).  The RESPECTED rows are
the two Godement composites `pentagon`, `rootUnitAssoc` (vcomps joined by interchange — matrix-agree).

## The soundness ground: the monoid restriction of `Mat(N)`, faithful to monotone maps Delta

The free non-commutative monoid on one object is the augmented simplex category Delta_+ (monotone maps).
`Mat(N)` restricted to the single colour `t` (one strand, `eta = [[]] : 1x0`, `mu = [[1,1]] : 1x2`) is a
model of the genuine monoid: it respects associativity (`mu . (mu |> t) ~ mu . (t <| mu)`, both legs
`[[1,1,1]]`) and both units (`mu . (eta |> t) ~ id_t` / `mu . (t <| eta) ~ id_t`, both legs `[[1]]`) —
machine-checked below.  A model that respects every genuine monad law yet keeps `eta |> t` and `t <| eta`
apart (`[[0],[1]] != [[1],[0]]`) proves those two cells genuinely distinct: the bare-whisker rows over-quotient.
The faithful ground truth is Delta (the shipped `monadDecideSaturatedConvViaMonotoneMap` decides the three
monad LAWS — NAMED, cross-lane `TwoCategory/WalkingMonad`, not imported); `Mat(N)`-monoid is the concrete
in-lane separator (a commutative monoid is still a monoid model, so it respects every monad law).

## The house-style discriminant (recon self-attack): the CORRECT rows post-compose with `mu`

The walking monad has NO swap (unlike the bunched a-side's `sigma`), so the three bare-whisker rows are
IRREPARABLE by braiding.  The correct house style is the walking equivalence's: state the unit law as a CLOSED
composite landing on an identity — `mu . (eta |> t) ~ id_t` — not as the bare `eta |> t ~ t <| eta`.  The
genuine laws post-compose with `mu`; they do NOT collapse the bare whisker legs (`mu` is not monic), which is
exactly why the bare rows over-quotient.  `mu` is the identification mechanism the r1 rows tried to bypass.

## The honest walls (NAMED at their nodes)

  * Full isolation over `StrictAxiomRel union MonadOmegaSoundRow` needs the matMul-associativity Fubini kit
    (the same wall as the bunched `fxBunchedBimonoid_matrixStrictLawExtensionReached`, r-next).  This file
    ships the machine core (r1 relates a matrix-distinct pair; the genuine-law sub-theory keeps the three
    apart) modulo that NAMED wall and the NAMED faithfulness citation (Delta / monotone maps).
  * Matrix completeness (equal matrix ⟹ convertible) is the spider NF, re-scoped to the sound sub-theory.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin.
The matrix carrier, ops, indexers, evaluation-motive and the four label-independent evaluation helpers are
REUSED from `WalkingBunchedBimonoidMatrixSemantics` (build once — the recon budget); only the monad generator
table and the top-level fold are new. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # B1 — THE Mat(N)-MONOID EVALUATION OF THE WALKING MONAD (probes FIRST, machine-checked)
    # =========================================================================================

★ **The monoid restriction of the free-bicommutative-bimonoid functor into `Mat(N)`.**  A single colour `t`
(one strand), the unit `eta = [[]] : 1x0`, the multiplication `mu = [[1,1]] : 1x2`.  The evaluation reuses the
shared `Mat(N)` kernel (`BunchedBimonoidMat`, `bunchedBimonoidMatMul` / `MatDirectSum` / `IdentityMat`,
`bunchedBimonoidMatEntryAt`) and the four label-independent helpers (`bunchedBimonoidEvalId` / `EvalVcomp` /
`EvalWhiskerLeft` / `EvalWhiskerRight`); only the generator table is monad-specific. -/

/-- The **monad generator matrix table** — the declared `Mat(N)` map of each generator: at label-dimension 0
the 1-generator `t` is a single strand (width 1); at label-dimension 1 the unit `eta` (label `false`) is the
empty product `[[]] : 1x0` and the multiplication `mu` (label `true`) is the fold `[[1,1]] : 1x2`; `Unit`
above.  The label family is the constant `Bool` (`monadOmegaComputad.genLabel`), so the arm splits on the
`Bool` at label-dimension 1.  Full-enum arms — propext-clean. -/
def monadOmegaEvalGen : (labelDim : Nat) → Bool →
    BunchedBimonoidEvalCarrier labelDim → BunchedBimonoidEvalCarrier labelDim →
    BunchedBimonoidEvalCarrier (labelDim + 1)
  | 0, _, _, _ => (1 : Nat)
  | 1, false, _, _ => { rows := 1, cols := 0, entries := [[]] }
  | 1, true, _, _ => { rows := 1, cols := 2, entries := [[1, 1]] }
  | _ + 2, _, _, _ => ()

/-- ★ **The monad matrix evaluation** `monadOmegaEvalCell : CellExpr monadOmegaComputad dim -> EvalCarrier dim`
— the monoid functor into `Mat(N)`.  A total structural fold over all six carrier constructors into the shared
dimension-dependent motive `BunchedBimonoidEvalCarrier`; the four label-independent helpers carry the
per-dimension operations (`vcomp` to `matMul`, `id` to `identityMat`, whiskering to identity-block direct-sum),
the monad generator table carries the generators.  Propext-clean (the `List.getD`-free shared indexers keep
the fold axiom-free). -/
def monadOmegaEvalCell : {dim : Nat} → CellExpr monadOmegaComputad dim →
    BunchedBimonoidEvalCarrier dim
  | _, .ofMode _ => ()
  | _, .gen (dim := labelDim) label source target =>
      monadOmegaEvalGen labelDim label (monadOmegaEvalCell source) (monadOmegaEvalCell target)
  | _, .id (dim := d) cell => bunchedBimonoidEvalId d (monadOmegaEvalCell cell)
  | _, .vcomp (dim := d) leftCell rightCell =>
      bunchedBimonoidEvalVcomp d (monadOmegaEvalCell leftCell) (monadOmegaEvalCell rightCell)
  | _, .whiskerLeft (dim := d) whiskerCell cell =>
      bunchedBimonoidEvalWhiskerLeft d (monadOmegaEvalCell whiskerCell) (monadOmegaEvalCell cell)
  | _, .whiskerRight (dim := d) cell whiskerCell =>
      bunchedBimonoidEvalWhiskerRight d (monadOmegaEvalCell cell) (monadOmegaEvalCell whiskerCell)

/-! ## The generator matrices and widths (the B1 truth-probe, machine-checked) -/

/-- The **width of a 1-cell word** — the evaluation at dimension 1, read back at the manifest `Nat` type (the
motive `BunchedBimonoidEvalCarrier 1` is definitionally `Nat`; the declared return type pins it so numeral
comparisons elaborate). -/
def monadOmegaWordWidth (cell : CellExpr monadOmegaComputad 1) : Nat :=
  monadOmegaEvalCell cell

/-- `t` evaluates to width 1 (a single strand). -/
theorem monadOmegaTGen_width : monadOmegaWordWidth monadOmegaTGen = 1 := rfl

/-- `t.t` evaluates to width 2. -/
theorem monadOmegaTtWord_width : monadOmegaWordWidth monadOmegaTtWord = 2 := rfl

/-- `eta : id => t` evaluates to the empty-product matrix `[[]] : 1x0`. -/
theorem monadOmegaEtaGen_matrix :
    monadOmegaEvalCell monadOmegaEtaGen = { rows := 1, cols := 0, entries := [[]] } := rfl

/-- `mu : t.t => t` evaluates to the fold matrix `[[1,1]] : 1x2`. -/
theorem monadOmegaMuGen_matrix :
    monadOmegaEvalCell monadOmegaMuGen = { rows := 1, cols := 2, entries := [[1, 1]] } := rfl

/-! ## The 2 RESPECTED presentation rows — both legs share the matrix (`rfl`) -/

/-- The `pentagon` presentation row is matrix-respected: both Godement readings evaluate to the same map
`[[1,1,0,0],[0,0,1,1]]`. -/
theorem monadOmegaMatrixRespectsPentagon :
    monadOmegaEvalCell monadOmegaPentagonLeftLeg = monadOmegaEvalCell monadOmegaPentagonRightLeg := rfl

/-- The `rootUnitAssoc` presentation row is matrix-respected: both legs evaluate to `[[1,1],[0,0]]`. -/
theorem monadOmegaMatrixRespectsRootUnitAssoc :
    monadOmegaEvalCell monadOmegaRootUnitAssocLeftLeg
      = monadOmegaEvalCell monadOmegaRootUnitAssocRightLeg := rfl

/-! ## The 3 BROKEN presentation rows — the two legs are DIFFERENT matrices (`op (x) 1 != 1 (x) op`) -/

/-- ★ `unitUnit` legs are DIFFERENT (`eta |> t` = `[[0],[1]]` vs `t <| eta` = `[[1],[0]]`; entry `(0,0)` is
`0` vs `1`).  The bare-whisker over-quotient the r3 flag named. -/
theorem monadOmegaMatrixSeparatesUnitUnit :
    monadOmegaEvalCell monadOmegaUnitUnitLeftLeg ≠ monadOmegaEvalCell monadOmegaUnitUnitRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-- ★ `leftUnitAssoc` legs are DIFFERENT (`mu |> t` = `[[1,1,0],[0,0,1]]` vs `t <| mu` = `[[1,0,0],[0,1,1]]`;
entry `(0,1)` is `1` vs `0`).  The r3 flag missed this one. -/
theorem monadOmegaMatrixSeparatesLeftUnitAssoc :
    monadOmegaEvalCell monadOmegaLeftUnitAssocLeftLeg
      ≠ monadOmegaEvalCell monadOmegaLeftUnitAssocRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 1) hmatrix)

/-- ★ `rightUnitAssoc` legs are DIFFERENT (`eta |> t.t` = `[[0,0],[1,0],[0,1]]` vs `t.t <| eta` =
`[[1,0],[0,1],[0,0]]`; entry `(0,0)` is `0` vs `1`).  The r3 flag missed this one too. -/
theorem monadOmegaMatrixSeparatesRightUnitAssoc :
    monadOmegaEvalCell monadOmegaRightUnitAssocLeftLeg
      ≠ monadOmegaEvalCell monadOmegaRightUnitAssocRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-! ## The B1 non-vacuity probes (the truth-probe `#eval` outputs) -/

#eval monadOmegaEvalCell monadOmegaUnitUnitLeftLeg
#eval monadOmegaEvalCell monadOmegaUnitUnitRightLeg
#eval monadOmegaEvalCell monadOmegaLeftUnitAssocLeftLeg
#eval monadOmegaEvalCell monadOmegaLeftUnitAssocRightLeg
#eval monadOmegaEvalCell monadOmegaRightUnitAssocLeftLeg
#eval monadOmegaEvalCell monadOmegaRightUnitAssocRightLeg

/-! # =========================================================================================
    # B1 (O) — THE OVER-QUOTIENT FORMALIZED: r1 relates matrix-distinct legs on each of the 3 rows
    # =========================================================================================

★ **Each of the 3 broken rows is an OVER-QUOTIENT WITNESS: its legs are convertible under the r1 base relation
`monadOmegaBaseRel` (from `MonadCoherentPresentation`'s shipped per-pair resolution) yet evaluate to DIFFERENT
`Mat(N)`-monoid maps (from B1 above).**  Each proof is the pair `(r1-convertibility, matrix-separation)`; both
components are shipped and zero-axiom. -/

/-- ★ `unitUnit` OVER-QUOTIENT witness: `eta |> t` and `t <| eta` are convertible under the r1 base relation yet
are the distinct maps `eta (x) 1 != 1 (x) eta`. -/
theorem monadOmegaBaseRelOverQuotientsUnitUnit :
    SaturatedConvOverWithId monadOmegaComputad monadOmegaBaseRel
        monadOmegaUnitUnitLeftLeg monadOmegaUnitUnitRightLeg
      ∧ monadOmegaEvalCell monadOmegaUnitUnitLeftLeg ≠ monadOmegaEvalCell monadOmegaUnitUnitRightLeg :=
  ⟨monadOmegaUnitUnitResolved.legsConvertible, monadOmegaMatrixSeparatesUnitUnit⟩

/-- ★ `leftUnitAssoc` OVER-QUOTIENT witness (`mu (x) 1 != 1 (x) mu`). -/
theorem monadOmegaBaseRelOverQuotientsLeftUnitAssoc :
    SaturatedConvOverWithId monadOmegaComputad monadOmegaBaseRel
        monadOmegaLeftUnitAssocLeftLeg monadOmegaLeftUnitAssocRightLeg
      ∧ monadOmegaEvalCell monadOmegaLeftUnitAssocLeftLeg
        ≠ monadOmegaEvalCell monadOmegaLeftUnitAssocRightLeg :=
  ⟨monadOmegaLeftUnitAssocResolved.legsConvertible, monadOmegaMatrixSeparatesLeftUnitAssoc⟩

/-- ★ `rightUnitAssoc` OVER-QUOTIENT witness (`eta (x) 1 != 1 (x) eta`). -/
theorem monadOmegaBaseRelOverQuotientsRightUnitAssoc :
    SaturatedConvOverWithId monadOmegaComputad monadOmegaBaseRel
        monadOmegaRightUnitAssocLeftLeg monadOmegaRightUnitAssocRightLeg
      ∧ monadOmegaEvalCell monadOmegaRightUnitAssocLeftLeg
        ≠ monadOmegaEvalCell monadOmegaRightUnitAssocRightLeg :=
  ⟨monadOmegaRightUnitAssocResolved.legsConvertible, monadOmegaMatrixSeparatesRightUnitAssoc⟩

/-- ★★ **THE WALKING-MONAD r1 BASE RELATION IS NOT MATRIX-SOUND — the machine over-quotient fact.**  There
EXIST two 2-cells convertible under the r1 congruence `monadOmegaBaseRel` whose `Mat(N)`-monoid matrices DIFFER
(witnessed by the `unitUnit` row).  Since the matrix respects every genuine monoid law (associativity + both
units, machine-checked below) and — by the free-monoid = Delta identification (NAMED) — the monoid restriction
is the faithful invariant, this is the r1 monad presentation identifying genuinely-distinct cells: the
OVER-QUOTIENT the bunched r3 flag predicted. -/
theorem monadOmegaBaseRelRelatesMatrixDistinctLegs :
    ∃ (leftLeg rightLeg : CellExpr monadOmegaComputad 2),
      SaturatedConvOverWithId monadOmegaComputad monadOmegaBaseRel leftLeg rightLeg ∧
      monadOmegaEvalCell leftLeg ≠ monadOmegaEvalCell rightLeg :=
  ⟨monadOmegaUnitUnitLeftLeg, monadOmegaUnitUnitRightLeg,
    monadOmegaBaseRelOverQuotientsUnitUnit.1, monadOmegaBaseRelOverQuotientsUnitUnit.2⟩

/-! # =========================================================================================
    # B1 (M) — THE RESTORED SOUNDNESS: the genuine monad-LAW sub-theory + the matrix soundness over it
    # =========================================================================================

★ **The correction is to the CONGRUENCE, not the read.**  The r1 legs are bare single whiskers by construction
(the `matrixSeparates` lemmas name them directly), so the split stands.  Excise the 3 bare-whisker rows; keep
the 2 matrix-respected presentation composites (`pentagon`, `rootUnitAssoc`) and ADD the 3 genuine monad LAWS in
house-style-correct closed-composite form (both units land on `id_t` via `mu`; associativity is `mu . (mu |> t)
~ mu . (t <| mu)`).  Over this 5-row genuine-law sub-theory `Mat(N)` is a SOUND model — every row's two legs
share their matrix (`rfl`). -/

/-- The **genuine left-unit LAW left leg** `(eta |> t) . mu : t => t` — insert the unit on the left, then
multiply. -/
def monadOmegaGenuineLeftUnitLeftLeg : CellExpr monadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight monadOmegaEtaGen monadOmegaTGen) monadOmegaMuGen

/-- The **genuine left-unit LAW right leg** `id_t : t => t` — the multiplication absorbs the inserted unit. -/
def monadOmegaGenuineLeftUnitRightLeg : CellExpr monadOmegaComputad 2 :=
  CellExpr.id monadOmegaTGen

/-- The **genuine right-unit LAW left leg** `(t <| eta) . mu : t => t` — insert the unit on the right, then
multiply. -/
def monadOmegaGenuineRightUnitLeftLeg : CellExpr monadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft monadOmegaTGen monadOmegaEtaGen) monadOmegaMuGen

/-- The **genuine right-unit LAW right leg** `id_t : t => t`. -/
def monadOmegaGenuineRightUnitRightLeg : CellExpr monadOmegaComputad 2 :=
  CellExpr.id monadOmegaTGen

/-- The **genuine associativity LAW left leg** `(mu |> t) . mu : (t.t).t => t` — multiply the outer pair, then
multiply. -/
def monadOmegaGenuineAssocLeftLeg : CellExpr monadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight monadOmegaMuGen monadOmegaTGen) monadOmegaMuGen

/-- The **genuine associativity LAW right leg** `(t <| mu) . mu : t.(t.t) => t` — multiply the inner pair, then
multiply. -/
def monadOmegaGenuineAssocRightLeg : CellExpr monadOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft monadOmegaTGen monadOmegaMuGen) monadOmegaMuGen

/-- The genuine left-unit law is matrix-respected: both legs evaluate to `[[1]]` (`id_t`). -/
theorem monadOmegaMatrixRespectsGenuineLeftUnit :
    monadOmegaEvalCell monadOmegaGenuineLeftUnitLeftLeg
      = monadOmegaEvalCell monadOmegaGenuineLeftUnitRightLeg := rfl

/-- The genuine right-unit law is matrix-respected: both legs evaluate to `[[1]]` (`id_t`). -/
theorem monadOmegaMatrixRespectsGenuineRightUnit :
    monadOmegaEvalCell monadOmegaGenuineRightUnitLeftLeg
      = monadOmegaEvalCell monadOmegaGenuineRightUnitRightLeg := rfl

/-- The genuine associativity law is matrix-respected: both legs evaluate to `[[1,1,1]]`. -/
theorem monadOmegaMatrixRespectsGenuineAssoc :
    monadOmegaEvalCell monadOmegaGenuineAssocLeftLeg
      = monadOmegaEvalCell monadOmegaGenuineAssocRightLeg := rfl

/-- ★ The **genuine-law sub-relation** the matrix RESPECTS: the two matrix-respected presentation composites
(`pentagon`, `rootUnitAssoc`) PLUS the three genuine monad LAWS in closed-composite form (both units land on
`id_t` via `mu`; associativity).  The excised 3 bare-whisker rows are DELIBERATELY absent — this is the sound
sub-congruence the r1 5-row presentation over-quotients. -/
inductive MonadOmegaSoundRow :
    {d : Nat} → CellExpr monadOmegaComputad d → CellExpr monadOmegaComputad d → Prop where
  /-- pentagon (the Godement interchange of `mu` with `mu`). -/
  | pentagon : MonadOmegaSoundRow monadOmegaPentagonLeftLeg monadOmegaPentagonRightLeg
  /-- rootUnitAssoc (the Godement interchange of `mu` with `eta`). -/
  | rootUnitAssoc : MonadOmegaSoundRow monadOmegaRootUnitAssocLeftLeg monadOmegaRootUnitAssocRightLeg
  /-- the genuine left-unit LAW `(eta |> t) . mu ~ id_t`. -/
  | genuineLeftUnit : MonadOmegaSoundRow monadOmegaGenuineLeftUnitLeftLeg monadOmegaGenuineLeftUnitRightLeg
  /-- the genuine right-unit LAW `(t <| eta) . mu ~ id_t`. -/
  | genuineRightUnit : MonadOmegaSoundRow monadOmegaGenuineRightUnitLeftLeg monadOmegaGenuineRightUnitRightLeg
  /-- the genuine associativity LAW `(mu |> t) . mu ~ (t <| mu) . mu`. -/
  | genuineAssoc : MonadOmegaSoundRow monadOmegaGenuineAssocLeftLeg monadOmegaGenuineAssocRightLeg

/-- The **matrix-equality relation** — two same-dimension cells relate iff they evaluate to the same matrix.
The target congruence of the soundness fold. -/
def monadOmegaMatrixEq : CellRelOver monadOmegaComputad :=
  fun {_dim} cellAlpha cellBeta => monadOmegaEvalCell cellAlpha = monadOmegaEvalCell cellBeta

/-- ★★ **THE MATRIX EVALUATION RESPECTS THE GENUINE-LAW SUB-CONGRUENCE.**  Matrix equality absorbs the
idCongr-extended saturated congruence over `MonadOmegaSoundRow`: each of the 5 rows relates equal-matrix legs
(`rfl`) and every congruence closure is `congrArg` on the corresponding shared evaluation helper (`matMul` /
`directSum` / `identityMat` congruence) — the exact `bunchedBimonoidMatrixEvalAbsorbs` shape over the monad
computad. -/
def monadOmegaSoundMatrixEvalAbsorbs :
    IsSaturatedCongruenceWithId monadOmegaComputad MonadOmegaSoundRow monadOmegaMatrixEq where
  ofRelation := by intro _dim _cellAlpha _cellBeta row; cases row <;> rfl
  vcompCongrLeft := by
    intro dim _cellAlpha _cellAlpha' cellBeta hconv
    exact congrArg (fun leftMatrix => bunchedBimonoidEvalVcomp dim leftMatrix (monadOmegaEvalCell cellBeta))
      hconv
  vcompCongrRight := by
    intro dim cellAlpha _cellBeta _cellBeta' hconv
    exact congrArg (fun rightMatrix => bunchedBimonoidEvalVcomp dim (monadOmegaEvalCell cellAlpha)
      rightMatrix) hconv
  whiskerLeftCongr := by
    intro dim whiskeringCell _cellBeta _cellBeta' hconv
    exact congrArg (fun cellMatrix => bunchedBimonoidEvalWhiskerLeft dim
      (monadOmegaEvalCell whiskeringCell) cellMatrix) hconv
  whiskerRightCongr := by
    intro dim _cellAlpha _cellAlpha' whiskeringCell hconv
    exact congrArg (fun cellMatrix => bunchedBimonoidEvalWhiskerRight dim cellMatrix
      (monadOmegaEvalCell whiskeringCell)) hconv
  idCongr := by
    intro dim _cellAlpha _cellBeta hconv
    exact congrArg (fun subMatrix => bunchedBimonoidEvalId dim subMatrix) hconv
  whiskerLeftWhiskerCongr := by
    intro dim _whiskerAlpha _whiskerAlpha' innerCell hconv
    exact congrArg (fun whiskerMatrix => bunchedBimonoidEvalWhiskerLeft dim whiskerMatrix
      (monadOmegaEvalCell innerCell)) hconv
  whiskerRightWhiskerCongr := by
    intro dim innerCell _whiskerAlpha _whiskerAlpha' hconv
    exact congrArg (fun whiskerMatrix => bunchedBimonoidEvalWhiskerRight dim
      (monadOmegaEvalCell innerCell) whiskerMatrix) hconv
  refl := by intro _dim _cell; rfl
  symm := by intro _dim _cellAlpha _cellBeta hconv; exact hconv.symm
  trans := by intro _dim _cellAlpha _cellBeta _cellGamma hleft hright; exact hleft.trans hright

/-- ★★ **RESTORED SOUNDNESS: convertible over the genuine-law sub-theory ⟹ equal matrix.**  Any two cells
convertible under the congruence generated by `MonadOmegaSoundRow` (the 2 respected composites + 3 genuine monad
laws) share their `Mat(N)`-monoid matrix — the fold of `monadOmegaSoundMatrixEvalAbsorbs` through the
least-congruence UP.  This is the SOUND congruence the r1 presentation over-quotients (it strictly adds the 3
bare-whisker rows). -/
theorem monadOmegaMatrixSoundOverSound {dim : Nat}
    {cellAlpha cellBeta : CellExpr monadOmegaComputad dim}
    (conv : SaturatedConvOverWithId monadOmegaComputad MonadOmegaSoundRow cellAlpha cellBeta) :
    monadOmegaEvalCell cellAlpha = monadOmegaEvalCell cellBeta :=
  SaturatedConvOverWithId.recInto monadOmegaSoundMatrixEvalAbsorbs conv

/-! ## The 3 bare-whisker legs are NOT identified by the genuine-law sub-theory (the strict-coarsening bound) -/

/-- `unitUnit` legs are NOT convertible over the genuine-law sub-theory (else restored soundness forces equal
matrices, contradicting the separation). -/
theorem monadOmegaSoundRowNotConvertibleUnitUnit :
    ¬ SaturatedConvOverWithId monadOmegaComputad MonadOmegaSoundRow
        monadOmegaUnitUnitLeftLeg monadOmegaUnitUnitRightLeg :=
  fun conv => monadOmegaMatrixSeparatesUnitUnit (monadOmegaMatrixSoundOverSound conv)

/-- `leftUnitAssoc` legs are NOT convertible over the genuine-law sub-theory. -/
theorem monadOmegaSoundRowNotConvertibleLeftUnitAssoc :
    ¬ SaturatedConvOverWithId monadOmegaComputad MonadOmegaSoundRow
        monadOmegaLeftUnitAssocLeftLeg monadOmegaLeftUnitAssocRightLeg :=
  fun conv => monadOmegaMatrixSeparatesLeftUnitAssoc (monadOmegaMatrixSoundOverSound conv)

/-- `rightUnitAssoc` legs are NOT convertible over the genuine-law sub-theory. -/
theorem monadOmegaSoundRowNotConvertibleRightUnitAssoc :
    ¬ SaturatedConvOverWithId monadOmegaComputad MonadOmegaSoundRow
        monadOmegaRightUnitAssocLeftLeg monadOmegaRightUnitAssocRightLeg :=
  fun conv => monadOmegaMatrixSeparatesRightUnitAssoc (monadOmegaMatrixSoundOverSound conv)

/-- ★★ **THE r1 MONAD PRESENTATION STRICTLY OVER-QUOTIENTS THE GENUINE-LAW SUB-THEORY.**  There exist two
2-cells convertible under `monadOmegaBaseRel` (the r1 5-row congruence) yet PROVABLY NOT convertible under
`MonadOmegaSoundRow` (the 2 respected composites + 3 genuine monad laws) — witnessed by the `unitUnit` row.  The
genuine-law sub-theory keeps the two legs apart (restored soundness + the map separation); the r1 relation
collapses them (via `MonadCriticalRow.unitUnit`).  Machine-airtight and zero-axiom; the extension of the
sub-theory by the strict 2-cat laws is the NAMED Fubini wall. -/
theorem monadOmegaBaseRelStrictlyOverQuotientsSound :
    ∃ (leftLeg rightLeg : CellExpr monadOmegaComputad 2),
      SaturatedConvOverWithId monadOmegaComputad monadOmegaBaseRel leftLeg rightLeg ∧
      ¬ SaturatedConvOverWithId monadOmegaComputad MonadOmegaSoundRow leftLeg rightLeg :=
  ⟨monadOmegaUnitUnitLeftLeg, monadOmegaUnitUnitRightLeg,
    monadOmegaUnitUnitResolved.legsConvertible, monadOmegaSoundRowNotConvertibleUnitUnit⟩

/-! # =========================================================================================
    # B1 (F) — THE IDENTIFICATION MECHANISM: the unit laws close THROUGH `mu`, not by bare whisker
    # =========================================================================================

★ **The correct house style post-composes with `mu`.**  The bare-whisker rows are NOT genuinely identified as
stated (`eta |> t != t <| eta`); the CORRECT theory relates the unit laws only after post-composing with the
multiplication — `(eta |> t) . mu ~ id_t` — landing on an identity.  These closed corrections live in
`MonadOmegaSoundRow`, so they ARE convertible there and (by restored soundness) share their matrix — while the
DIRECT bare-whisker rows are provably NOT convertible.  `mu` is the identification mechanism the r1 rows tried
to bypass; with no swap on `t`, there is no other repair. -/

/-- ★ The **closed correction of the left unit** is convertible over the genuine-law sub-theory —
`(eta |> t) . mu ~ id_t`, the genuine left-unit law fired through `ofRelation`. -/
theorem monadOmegaGenuineLeftUnitConvertibleOverSound :
    SaturatedConvOverWithId monadOmegaComputad MonadOmegaSoundRow
      monadOmegaGenuineLeftUnitLeftLeg monadOmegaGenuineLeftUnitRightLeg :=
  SaturatedConvOverWithId.ofRelation MonadOmegaSoundRow.genuineLeftUnit

/-- ★ **DERIVED (not assumed): the closed left-unit correction's legs share their matrix** — from the
convertibility via restored soundness (both `[[1]]`). -/
theorem monadOmegaGenuineLeftUnitMatrixSharedOverSound :
    monadOmegaEvalCell monadOmegaGenuineLeftUnitLeftLeg
      = monadOmegaEvalCell monadOmegaGenuineLeftUnitRightLeg :=
  monadOmegaMatrixSoundOverSound monadOmegaGenuineLeftUnitConvertibleOverSound

/-- ★★ **THE IDENTIFICATION MECHANISM IS `mu` (both-ways).**  The unit law is related in the genuine-law
sub-theory ONLY through `mu`: the mu-mediated closed correction IS convertible
(`...GenuineLeftUnitConvertibleOverSound`) but the DIRECT `eta |> t ~ t <| eta` is provably NOT
(`monadOmegaSoundRowNotConvertibleUnitUnit`).  So `mu` is the identification mechanism the r1 row tried (and
failed) to bypass — the walking monad's version of the walking-equivalence house style (state the law at a
closed composite landing on an identity), stated as a mechanism, not a bare non-identity. -/
theorem monadOmegaMuIsTheUnitIdentificationMechanism :
    SaturatedConvOverWithId monadOmegaComputad MonadOmegaSoundRow
        monadOmegaGenuineLeftUnitLeftLeg monadOmegaGenuineLeftUnitRightLeg
      ∧ ¬ SaturatedConvOverWithId monadOmegaComputad MonadOmegaSoundRow
          monadOmegaUnitUnitLeftLeg monadOmegaUnitUnitRightLeg :=
  ⟨monadOmegaGenuineLeftUnitConvertibleOverSound, monadOmegaSoundRowNotConvertibleUnitUnit⟩

/-- ★★ **THE GENUINE MONOID LAWS ARE MODELLED YET THE BARE ROW IS SEPARATED.**  `Mat(N)`-monoid respects the
`pentagon` (the strict associativity interchange) AND separates the `unitUnit` legs — so it is a model of the
genuine monoid that refutes the bare-whisker row.  With no swap on `t`, the 3 bare-whisker rows have NO
categorical repair; they are the over-quotient, retracted from the decided (monad-LAW) congruence. -/
theorem monadOmegaGenuineLawModelledRowSeparated :
    (monadOmegaEvalCell monadOmegaPentagonLeftLeg = monadOmegaEvalCell monadOmegaPentagonRightLeg)
      ∧ (monadOmegaEvalCell monadOmegaUnitUnitLeftLeg ≠ monadOmegaEvalCell monadOmegaUnitUnitRightLeg) :=
  ⟨monadOmegaMatrixRespectsPentagon, monadOmegaMatrixSeparatesUnitUnit⟩

/-! # =========================================================================================
    # B3 — THE DECISION RE-AUDIT: the shipped Delta decision is monad-LAW-congruence-scoped (CLEAN)
    # =========================================================================================

★ **The walking-monad 2-cell decision re-checked against this outcome.**  The shipped Delta decision
(`monadDecideSaturatedConvViaMonotoneMap`, cross-lane `TwoCategory/WalkingMonad/MonadDeltaModel`, NAMED not
imported) is sound+complete over `MonadSaturatedTwoCellConv`, whose generators are exactly the THREE monad LAWS
— `leftUnit : mu . (eta |> t) ~ id_t`, `rightUnit : mu . (t <| eta) ~ id_t`, `assoc : mu . (mu |> t) ~ mu . (t
<| mu)` — plus `ofFull` (strict-2-cat laws) and congruences.  It does NOT contain the bare-whisker rows
`unitUnit / leftUnitAssoc / rightUnitAssoc`.  In the Delta model `eta` = coface, `mu` = codegeneracy, so `eta
|> t` = delta_0 and `t <| eta` = delta_1 are DIFFERENT monotone maps.  So the decision is LAW-congruence-scoped
CLEAN: the over-quotient lives in the PRESENTATION's `monadOmegaBaseRel` (which fires the bare-whisker
`MonadCriticalRow`s), never in the decision's congruence.  The three genuine monad LAWS ARE the sound
sub-theory `MonadOmegaSoundRow` content (the two units + assoc, machine-modelled here in-lane;
`monadOmegaMatrixRespectsGenuine{LeftUnit,RightUnit,Assoc}`), matching the Delta ground truth. -/

/-- ★★ **DECISION RE-AUDIT — the Delta decision is LAW-congruence-scoped, the 3 bare-whisker rows are
retracted.**  `= true` records the finding: the shipped Delta decision decides `MonadSaturatedTwoCellConv` (the
monad LAWS leftUnit / rightUnit / assoc), which does NOT contain the r1 bare-whisker rows `unitUnit /
leftUnitAssoc / rightUnitAssoc`; in fact Delta refutes them (delta_0 != delta_1), matching the in-lane
`Mat(N)`-monoid separation (`monadOmegaGenuineLawModelledRowSeparated`).  The three genuine monad LAWS are the
`MonadOmegaSoundRow` genuine content, machine-modelled in-lane
(`monadOmegaMatrixRespectsGenuine{LeftUnit,RightUnit,Assoc}`).  Delta model NOT imported (cross-lane —
`TwoCategory/WalkingMonad`); NAMED backing + in-lane matrix proof only. -/
def fxOmegaHouseStyle_monadDecisionIsLawCongruenceScopedClean : Bool := true

/-! # =========================================================================================
    # B4 — THE HOMOLOGY NO-IMPACT EVIDENCE (in-lane): the over-quotient rows are abelianization-invisible
    # =========================================================================================

★ **The over-quotient is abelianization-invisible — the H2-WALKERS homology is untouched.**  The homology lane
consumes only abelianized generator-firing COUNTS (`WalkerPresentationCarrier`: `d2` = target-minus-source
generator counts, `d3` = abelianized cofork firing counts), which are position-BLIND.  The two legs of each
bare-whisker over-quotient row differ ONLY in whisker POSITION (`op |> x` vs `x <| op`), which abelianization
forgets: both carry the same 2-generator multiset.  The in-lane witness is a 2-generator count on the legs. -/

/-- The **abelianized generator count** of a monad cell — `(#eta, #mu)`, the abelianization the homology lane
sees.  A TOTAL structural fold over all six constructors (the `cellSize` idiom, propext-clean): a `gen` counts
its `Bool` label (`false` = eta, `true` = mu); `vcomp` sums; `whiskerLeft` / `whiskerRight` / `id` descend into
the whiskered / sub-cell only (the whiskering 1-cell and the declared boundaries are dropped — exactly what
abelianization forgets).  Applied to a genuine 2-cell the only `gen` nodes reached at the top are its
2-generators, so it counts `(#eta, #mu)`; position-blind by construction (both whisker orders of a fixed 2-cell
carry the same count). -/
def monadOmegaTwoCellGenCount : {dim : Nat} → CellExpr monadOmegaComputad dim → Nat × Nat
  | _, .ofMode _ => (0, 0)
  | _, .gen label _ _ => match label with
      | false => (1, 0)
      | true => (0, 1)
  | _, .id _ => (0, 0)
  | _, .vcomp leftCell rightCell =>
      ((monadOmegaTwoCellGenCount leftCell).1 + (monadOmegaTwoCellGenCount rightCell).1,
       (monadOmegaTwoCellGenCount leftCell).2 + (monadOmegaTwoCellGenCount rightCell).2)
  | _, .whiskerLeft _ cell => monadOmegaTwoCellGenCount cell
  | _, .whiskerRight cell _ => monadOmegaTwoCellGenCount cell

/-- ★★ **HOMOLOGY NO-IMPACT (in-lane evidence): each over-quotient row's two legs have EQUAL abelianized
2-generator counts.**  The `unitUnit` legs both count `(1,0)` (one `eta`), `leftUnitAssoc` both `(0,1)`,
`rightUnitAssoc` both `(1,0)` — so the abelianized image of every over-quotient row is EQUAL.  The homology
boundary maps `d2` / `d3` (abelianized counts) therefore do not distinguish the two legs: whether or not the
presentation over-quotients, the boundary maps are UNCHANGED — the over-quotient is abelianization-invisible, so
the H2-WALKERS homology is untouched.  (Only a user-gated row RETRACTION — dropping rows from the critical-pair
list — could recompute H2; the Homology lane maintains its own list independently.) -/
theorem monadOmegaOverQuotientRowsAbelianizationEqual :
    monadOmegaTwoCellGenCount monadOmegaUnitUnitLeftLeg
        = monadOmegaTwoCellGenCount monadOmegaUnitUnitRightLeg
      ∧ monadOmegaTwoCellGenCount monadOmegaLeftUnitAssocLeftLeg
        = monadOmegaTwoCellGenCount monadOmegaLeftUnitAssocRightLeg
      ∧ monadOmegaTwoCellGenCount monadOmegaRightUnitAssocLeftLeg
        = monadOmegaTwoCellGenCount monadOmegaRightUnitAssocRightLeg :=
  ⟨rfl, rfl, rfl⟩

/-! # =========================================================================================
    # B2 / B5 — THE r4 VERDICT MARKERS + THE FAMILY-FLAG + THE HONEST WALLS
    # ========================================================================================= -/

/-- ★★ **THE VERDICT (O) — the walking-monad r1 presentation OVER-QUOTIENTS on THREE bare-whisker rows,
machine-decided.**  `= true` records `monadOmegaBaseRelRelatesMatrixDistinctLegs` and
`monadOmegaBaseRelStrictlyOverQuotientsSound`: the r1 base relation `monadOmegaBaseRel` identifies the legs of
`unitUnit / leftUnitAssoc / rightUnitAssoc` (the 3 bare-whisker rows) that the faithful `Mat(N)`-monoid model
separates and the genuine-law sub-theory `MonadOmegaSoundRow` keeps apart.  Corrects the r3 flag (which named
only `unitUnit`) from ONE row to THREE. -/
def fxOmegaHouseStyle_monadPresentationOverQuotientsThreeRows : Bool := true

/-- ★★ **THE r3 CROSS-LANE FLAG IS MADE GOOD (this file).**  `= true` records that the bunched-r3 warning
`fxBunchedBimonoid_monadHouseStyleCarriesSameLatentOverQuotient` (NAME-only there) is here MACHINE-BACKED: the
`Mat(N)`-monoid separates the 3 bare-whisker rows and the genuine-law sub-theory restores soundness.  The
bunched m-generator IS the walking monad transported verbatim, so the two separations are the same fact at the
two lanes. -/
def fxOmegaHouseStyle_monadR3FlagMadeGood : Bool := true

/-- ★ **THE SOUND SUB-THEORY: 2 respected composites + 3 genuine monad LAWS = 5 genuine rows.**  `= true`
records that `MonadOmegaSoundRow` (pentagon + rootUnitAssoc from the presentation, plus the two units and assoc
in closed-composite form) is the SOUND sub-congruence — the honest replacement for the r1 5-row presentation.
Matrix completeness (spider NF) extends it to the full faithful presentation later. -/
def fxOmegaHouseStyle_monadSoundSubTheoryIsTwoPlusThree : Bool := true

/-- ★ **THE MONAD IS IRREPARABLE BY BRAIDING (no swap).**  `= true` records
`monadOmegaGenuineLawModelledRowSeparated` and `monadOmegaMuIsTheUnitIdentificationMechanism`: the walking monad
carries NO `sigma`, so the 3 bare-whisker rows have NO braiding repair; the ONLY identification mechanism is
post-composition with `mu` (the house-style-correct closed composite), which relates the genuine unit laws but
NOT the bare whisker legs.  Mirrors the bunched m-side's `fxBunchedBimonoid_multiplicativeRowsHaveNoSigmaRepair`
(the bunched m-generator is this walking monad). -/
def fxOmegaHouseStyle_monadIrreparableNoSwap : Bool := true

/-- ★ **THE HOMOLOGY VERDICT (in-lane): NO IMPACT — the over-quotient rows are abelianization-invisible.**
`= true` records `monadOmegaOverQuotientRowsAbelianizationEqual`: the two legs of each over-quotient row carry
EQUAL abelianized 2-generator counts (`unitUnit` both `(1,0)`, `leftUnitAssoc` both `(0,1)`, `rightUnitAssoc`
both `(1,0)`), so the homology boundary maps `d2` / `d3` (abelianized counts, position-blind) do not
distinguish the legs.  The H2-WALKERS homology is untouched by the over-quotient; only a user-gated row
retraction could recompute it (Homology lane owns its own critical-pair list). -/
def fxOmegaHouseStyle_monadHomologyNoImpactAbelianizationInvisible : Bool := true

/-- ★ **WALL (honest) — the FULL isolation over `StrictAxiomRel union MonadOmegaSoundRow` needs the Fubini
kit.**  `= false` records that lifting restored soundness from `MonadOmegaSoundRow` to `StrictAxiomRel union
MonadOmegaSoundRow` (so the 3 bare-whisker rows are provably non-convertible even in the presence of the strict
2-cat laws, isolating them as the SOLE over-quotient cause) requires proving matMul associativity / the
identity unit laws / block interchange in `Mat(N)` — the finite-sum Fubini matrix-algebra kit, the same wall as
the bunched `fxBunchedBimonoid_matrixStrictLawExtensionReached`.  This file ships the sub-theory lower bound;
the strict-law extension is the next round. -/
def fxOmegaHouseStyle_monadFullIsolationNeedsStrictLawFubiniKit : Bool := false

/-- ★ **ESTABLISHED (B5) — the walking-monad over-quotient adjudication ledger.**  `= true` records the
scoreboard: the OUTCOME is (O) machine-decided (the r1 presentation over-quotients on THREE bare-whisker rows,
correcting the r3 flag from one); restored soundness over `MonadOmegaSoundRow` (2 composites + 3 genuine monad
laws); the identification mechanism is `mu` (no swap repair); the Delta decision re-audited LAW-congruence-scoped
CLEAN (the over-quotient is presentation-only); the homology verdict NO IMPACT (abelianization-invisible,
in-lane witness).  Every wall NAMED: the strict-law Fubini isolation, matrix completeness (spider NF). -/
def fxOmegaHouseStyle_monadOverQuotientAdjudicationLedgerShipped : Bool := true

/-! ## The r4 truth-probe outputs (the over-quotient witness + the genuine-law model) -/

#eval monadOmegaEvalCell monadOmegaGenuineLeftUnitLeftLeg
#eval monadOmegaEvalCell monadOmegaGenuineLeftUnitRightLeg
#eval monadOmegaEvalCell monadOmegaGenuineAssocLeftLeg
#eval monadOmegaEvalCell monadOmegaGenuineAssocRightLeg
#eval monadOmegaTwoCellGenCount monadOmegaUnitUnitLeftLeg
#eval monadOmegaTwoCellGenCount monadOmegaUnitUnitRightLeg

end FX1Poly.Polygraph.Omega

-- TODO: DELETE THIS GARBAGE -- defective bunchedBimonoid star (refuted r29/r30/r31); superseded by the LafontProp re-founding
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarAssembly

/-! # Polygraph/Omega/WalkingBunchedBimonoidStarColourMislabelRefutation — ★★★ THE #2033 STAR IS DECIDED:
`bunchedBimonoidStarStatementAdditiveWellTyped` is FALSE, machine-refuted zero-axiom (WP-PROP r29, #2033)

★★★ **THE DECISION.**  The corrected well-typed star (`StarAssembly`, r7) — open through twenty-four rounds of
siege — is REFUTED, not proven: `bunchedBimonoidStarStatementAdditiveWellTypedRefuted` inhabits its NEGATION with
a kernel-checked, axiom-free proof.  The leak is NOT in the dim-2 bimonoid mathematics the siege ground on; it is
in the statement's DIMENSION QUANTIFIER: the star ranges over `{dim : Nat}` cells, and the well-typedness guard
(`bunchedBimonoidCellWellTyped`, r7 B3) constrains ONLY label-dimension-1 generators
(`bunchedBimonoidGenWidthAgreement` is `True` at label-dimension 0).  Because the computad's label family is
CONSTANT (all nine labels available at every dimension), the 1-cell generator
`bunchedBimonoidColourMislabeledMuOneCell := CellExpr.gen (dim := 0) addMult point point` — a COLOUR-position gen
node carrying the 2-cell OPERATION label `addMult` — is

  * **additive** (`addMult` is an additive-family label, `rfl`),
  * **well-typed** (the width-agreement is vacuous at label-dimension 0),
  * **width-equal to the genuine colour `a`** (`bunchedBimonoidGenWidth` is the constant `fun _ => 1`, `rfl`),

yet **NOT convertible to `a`** over the star scope: at dimension 1 the only applicable scope rows are the three
dim-0-parameter `vcomp` strict laws (every sound / hexagon row sits at dimension 2 —
`bunchedBimonoid{Sound,Hexagon}RowDimIsTwo`; every whisker-shaped strict row at dimension >= 2), and those
preserve the count of `addMult`-labeled gen nodes (`bunchedBimonoidStrictRowPreservesAddMultCountAtDimOne`).
The dim-gated count-agreement relation `bunchedBimonoidAddMultCountAgreementRel` therefore absorbs the whole
star-scope congruence (`bunchedBimonoidAddMultCountAbsorbsStarScope`, an `IsSaturatedCongruenceWithId` instance
— NO well-typedness threading needed, so the r27 Node-A trans-wall is bypassed), and the count separates the
pair: `1 != 0`.  The refutation instantiates the star at the pair and lands the contradiction.

## What the decision means (honest re-grading, no content overclaim)

  * The star Prop `bunchedBimonoidStarStatementAdditiveWellTyped` is CLOSED — negatively.  The owner marker
    `fxBunchedBimonoid_correctedWellTypedStarStillOpen = false` (`StarAssembly`, frozen) recorded "not proven";
    that record stays byte-intact and literally true — this file SUPERSEDES its content with the stronger
    `fxBunchedBimonoid_correctedWellTypedStarDecidedFalse = true` (the r55-Brauer new-file superseding-marker
    vehicle): the star is not OPEN, it is DISPROVEN.  NO owner flip: the flip law reserved `= true` for the star
    PROVEN, which will never happen.
  * The refutation is an OFF-DIMENSION artifact, not a defeat of the dim-2 content
    (`fxBunchedBimonoid_starRefutedByOffDimensionMislabelNotDimTwoContent`): the dim-1 leak (colour-position gen
    nodes carrying operation labels) and the dim->=3 triviality (`bunchedBimonoidEvalCell` is constantly `()`
    above dimension 2, witnessed by `bunchedBimonoidDimThreeEvalTriviallyEqual` on the structurally unrelated
    `id mu_a` / `id delta_a`) both live OUTSIDE the matrix dimension.  The genuine Lafont / Pirashvili / Fox
    completeness content — dimension-2 cells, colour labels at colour positions — remains the live target and
    must be RE-STATED with a label-placement guard at the pinned dimension 2 (the next brick).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Zero-axiom absolute: the row-family eliminations use
full-enumeration binder-form matches (never `cases` on the term-indexed families, whose index unification drags
`propext` through the `injEq` simp lemmas — the r29 lesson pinned here).  Per-declaration `#assert_no_axioms`
AND independent `#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # THE REFUTATION DATUM — a colour-position gen node carrying an operation label
    # =========================================================================================
-/

/-- ★★ **THE REFUTATION DATUM** — the 1-cell generator node carrying the 2-cell OPERATION label `addMult` in a
COLOUR position (`CellExpr.gen` at label-dimension 0).  The constant label family admits it; the r7
well-typedness guard does not see it (`bunchedBimonoidGenWidthAgreement` is `True` at label-dimension 0); the
constant `bunchedBimonoidGenWidth = fun _ => 1` makes it width-indistinguishable from the genuine colour `a`. -/
def bunchedBimonoidColourMislabeledMuOneCell : CellExpr bunchedBimonoidOmegaComputad 1 :=
  CellExpr.gen (dim := 0) BunchedBIGenLabel.addMult bunchedBimonoidPoint bunchedBimonoidPoint

/-- The mislabeled datum is ADDITIVE — `addMult` is an additive-family label and both boundary 0-cells are
`ofMode` (`rfl`).  The additivity guard does not exclude it. -/
theorem bunchedBimonoidColourMislabeledMuOneCellIsAdditive :
    bunchedBimonoidCellUsesOnlyAdditive bunchedBimonoidColourMislabeledMuOneCell = true := rfl

/-- The mislabeled datum is WELL-TYPED — the generator width-agreement is vacuous (`True`) at label-dimension 0,
and the two `ofMode` boundary cells are trivially well-typed.  The r7 well-typedness guard does not exclude it
either: BOTH r7 guards pass. -/
theorem bunchedBimonoidColourMislabeledMuOneCellWellTyped :
    bunchedBimonoidCellWellTyped bunchedBimonoidColourMislabeledMuOneCell :=
  ⟨True.intro, True.intro, True.intro⟩

/-- The genuine additive colour `a` is well-typed (the star's second premise pair). -/
theorem bunchedBimonoidAdditiveGenWellTypedForRefutation :
    bunchedBimonoidCellWellTyped bunchedBimonoidAdditiveGen :=
  ⟨True.intro, True.intro, True.intro⟩

/-- ★ **The equal-evaluation premise HOLDS** — `bunchedBimonoidGenWidth` is the constant `fun _ => 1`, so the
mislabeled datum and the genuine colour `a` share their dimension-1 evaluation (width `1`), on the nose. -/
theorem bunchedBimonoidColourMislabeledMuOneCellWidthMatchesAdditiveGen :
    bunchedBimonoidEvalCell bunchedBimonoidColourMislabeledMuOneCell
      = bunchedBimonoidEvalCell bunchedBimonoidAdditiveGen := rfl

#eval (bunchedBimonoidEvalCell bunchedBimonoidColourMislabeledMuOneCell : Nat)

/-! # =========================================================================================
    # THE SEPARATING INVARIANT — the addMult-label count, dim-gated
    # =========================================================================================
-/

/-- The **count of `addMult`-labeled generator nodes** in a cell — a total structural fold over all six carrier
constructors with a full nine-arm label split (propext-clean).  At dimension 1 this is the separating invariant:
the mislabeled datum counts `1`, every genuine 1-cell word counts `0`. -/
def bunchedBimonoidAddMultLabelCount : {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim → Nat
  | _, .ofMode _ => 0
  | _, .gen label source target =>
      (match label with
        | .addMult => 1
        | .additiveColour => 0
        | .multColour => 0
        | .addUnit => 0
        | .addComult => 0
        | .addCounit => 0
        | .addSwap => 0
        | .multMult => 0
        | .multUnit => 0)
        + bunchedBimonoidAddMultLabelCount source + bunchedBimonoidAddMultLabelCount target
  | _, .id cell => bunchedBimonoidAddMultLabelCount cell
  | _, .vcomp left right =>
      bunchedBimonoidAddMultLabelCount left + bunchedBimonoidAddMultLabelCount right
  | _, .whiskerLeft whisker cell =>
      bunchedBimonoidAddMultLabelCount whisker + bunchedBimonoidAddMultLabelCount cell
  | _, .whiskerRight cell whisker =>
      bunchedBimonoidAddMultLabelCount cell + bunchedBimonoidAddMultLabelCount whisker

/-- Every dimension-0 cell is an `ofMode` node (the only constructor at index 0), hence counts zero — the fact
that keeps the two dim-0-boundary unit rows count-preserving at dimension 1. -/
theorem bunchedBimonoidAddMultLabelCountAtDimZero (cell : CellExpr bunchedBimonoidOmegaComputad 0) :
    bunchedBimonoidAddMultLabelCount cell = 0 := by
  cases cell with
  | ofMode _ => rfl

/-- `d + 2 = 1` is absurd — the two-`noConfusion` chain (NEVER `cases` on the `Nat` equation, which drags
`propext`; the r29 lesson). -/
theorem bunchedBimonoidSuccSuccNeOne (anyDim : Nat) (hclash : anyDim + 2 = 1) : False :=
  Nat.noConfusion hclash (fun hSuccEqZero => Nat.noConfusion hSuccEqZero)

/-- `1 = 2` is absurd — the dual two-`noConfusion` chain for the sound / hexagon row dimension clash. -/
theorem bunchedBimonoidOneNeTwoClash (hclash : (1 : Nat) = 2) : False :=
  Nat.noConfusion hclash (fun hZeroEqOne => Nat.noConfusion hZeroEqOne)

/-! # =========================================================================================
    # THE ROW-FAMILY DIMENSION CENSUS (full-enumeration binder-form matches, propext-free)
    # =========================================================================================
-/

/-- **Every sound row sits at dimension 2** — full-enumeration binder-form match over all fifteen constructors
(the propext-free elimination; `cases` on the term-indexed family would drag `injEq`/`propext`). -/
theorem bunchedBimonoidSoundRowDimIsTwo :
    ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim},
      BunchedBimonoidSoundRow cellAlpha cellBeta → dim = 2
  | _, _, _, .multMonadPentagon => rfl
  | _, _, _, .multMonadRootUnitAssoc => rfl
  | _, _, _, .addMonadPentagon => rfl
  | _, _, _, .addMonadRootUnitAssoc => rfl
  | _, _, _, .comonoidCopentagon => rfl
  | _, _, _, .comonoidRootCounitCoassoc => rfl
  | _, _, _, .bialgebraProduct => rfl
  | _, _, _, .bialgebraCounit => rfl
  | _, _, _, .bialgebraUnit => rfl
  | _, _, _, .bialgebraBone => rfl
  | _, _, _, .commutativity => rfl
  | _, _, _, .cocommutativity => rfl
  | _, _, _, .sigmaInvolution => rfl
  | _, _, _, .sigmaEtaNaturality => rfl
  | _, _, _, .sigmaEpsNaturality => rfl

/-- **Every hexagon row sits at dimension 2** — full-enumeration binder-form match over the three width-3
braiding rows. -/
theorem bunchedBimonoidHexagonRowDimIsTwo :
    ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim},
      BunchedBimonoidHexagonRow cellAlpha cellBeta → dim = 2
  | _, _, _, .yangBaxter => rfl
  | _, _, _, .muNaturality => rfl
  | _, _, _, .deltaNaturality => rfl

/-- ★ **Every strict row preserves the addMult count at dimension 1** — the three dim-0-parameter `vcomp` rows
preserve it (associativity re-brackets a `Nat` sum; the two unit rows insert an identity on a dim-0 boundary,
which counts zero), and the eight whisker-shaped rows live at dimension >= 2 (vacuous under the dimension gate).
Full-enumeration binder-form match over all eleven constructors. -/
theorem bunchedBimonoidStrictRowPreservesAddMultCountAtDimOne :
    ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim},
      StrictAxiomRel bunchedBimonoidOmegaComputad cellAlpha cellBeta → dim = 1 →
        bunchedBimonoidAddMultLabelCount cellAlpha = bunchedBimonoidAddMultLabelCount cellBeta
  | _, _, _, .vcompAssoc _ _ _, _ => Nat.add_assoc _ _ _
  | _, _, _, .vcompUnitLeft cellA, hdim => by
      have hdimZero := Nat.succ.inj hdim
      subst hdimZero
      show bunchedBimonoidAddMultLabelCount (boundarySource cellA)
          + bunchedBimonoidAddMultLabelCount cellA
        = bunchedBimonoidAddMultLabelCount cellA
      rw [bunchedBimonoidAddMultLabelCountAtDimZero (boundarySource cellA)]
      exact Nat.zero_add _
  | _, _, _, .vcompUnitRight cellA, hdim => by
      have hdimZero := Nat.succ.inj hdim
      subst hdimZero
      show bunchedBimonoidAddMultLabelCount cellA
          + bunchedBimonoidAddMultLabelCount (boundaryTarget cellA)
        = bunchedBimonoidAddMultLabelCount cellA
      rw [bunchedBimonoidAddMultLabelCountAtDimZero (boundaryTarget cellA)]
      rfl
  | _, _, _, .whiskerLeftUnit (dim := innerDim) _ _, hdim =>
      absurd hdim (fun hclash => bunchedBimonoidSuccSuccNeOne innerDim hclash)
  | _, _, _, .whiskerRightUnit (dim := innerDim) _ _, hdim =>
      absurd hdim (fun hclash => bunchedBimonoidSuccSuccNeOne innerDim hclash)
  | _, _, _, .whiskerLeftFunctorial (dim := innerDim) _ _ _, hdim =>
      absurd hdim (fun hclash => bunchedBimonoidSuccSuccNeOne innerDim hclash)
  | _, _, _, .whiskerRightFunctorial (dim := innerDim) _ _ _, hdim =>
      absurd hdim (fun hclash => bunchedBimonoidSuccSuccNeOne innerDim hclash)
  | _, _, _, .interchange (dim := innerDim) _ _, hdim =>
      absurd hdim (fun hclash => bunchedBimonoidSuccSuccNeOne innerDim hclash)
  | _, _, _, .whiskerAssocLeft (dim := innerDim) _ _ _, hdim =>
      absurd hdim (fun hclash => bunchedBimonoidSuccSuccNeOne innerDim hclash)
  | _, _, _, .whiskerAssocRight (dim := innerDim) _ _ _, hdim =>
      absurd hdim (fun hclash => bunchedBimonoidSuccSuccNeOne innerDim hclash)
  | _, _, _, .whiskerLeftRightCommute (dim := innerDim) _ _ _, hdim =>
      absurd hdim (fun hclash => bunchedBimonoidSuccSuccNeOne innerDim hclash)

/-! # =========================================================================================
    # THE ABSORBER — the dim-gated count agreement absorbs the star-scope congruence
    # =========================================================================================
-/

/-- The **dim-gated addMult-count agreement relation** — at dimension 1 the two cells share their addMult-label
count; at every other dimension the claim is vacuous.  The separating target the star-scope congruence folds
into.  NO well-typedness is threaded (the invariant is purely syntactic), so the r27 Node-A `trans` wall does not
arise: transitivity composes two count equations with no demand on the middle cell. -/
def bunchedBimonoidAddMultCountAgreementRel : CellRelOver bunchedBimonoidOmegaComputad :=
  fun {dim} cellAlpha cellBeta =>
    dim = 1 → bunchedBimonoidAddMultLabelCount cellAlpha = bunchedBimonoidAddMultLabelCount cellBeta

/-- ★★★ **THE ABSORBER — the dim-gated count agreement absorbs the FULL star-scope congruence.**  An
`IsSaturatedCongruenceWithId` instance over `bunchedBimonoidStarCongruenceScope`: strict rows by the dimension-1
census, sound / hexagon rows by their dimension-2 clash, the two vcomp congruences by `Nat` sum rewriting, the
four whisker congruences vacuously (dimension >= 2), `idCongr` by the dim-0 zero count, `refl`/`symm`/`trans` by
`Eq`.  This is the machine adjudicator: NO derivation over the star scope can relate two dimension-1 cells with
different addMult counts. -/
def bunchedBimonoidAddMultCountAbsorbsStarScope :
    IsSaturatedCongruenceWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      bunchedBimonoidAddMultCountAgreementRel where
  ofRelation := by
    intro dim cellAlpha cellBeta row
    cases row with
    | inl strictRow => exact bunchedBimonoidStrictRowPreservesAddMultCountAtDimOne strictRow
    | inr presentedRow =>
        cases presentedRow with
        | inl soundRow =>
            intro hdim
            exact absurd (hdim.symm.trans (bunchedBimonoidSoundRowDimIsTwo soundRow))
              bunchedBimonoidOneNeTwoClash
        | inr hexRow =>
            intro hdim
            exact absurd (hdim.symm.trans (bunchedBimonoidHexagonRowDimIsTwo hexRow))
              bunchedBimonoidOneNeTwoClash
  vcompCongrLeft := by
    intro dim cellAlpha cellAlpha' cellBeta ih hdim
    have countEq := ih hdim
    show bunchedBimonoidAddMultLabelCount cellAlpha + bunchedBimonoidAddMultLabelCount cellBeta
      = bunchedBimonoidAddMultLabelCount cellAlpha' + bunchedBimonoidAddMultLabelCount cellBeta
    rw [countEq]
  vcompCongrRight := by
    intro dim cellAlpha cellBeta cellBeta' ih hdim
    have countEq := ih hdim
    show bunchedBimonoidAddMultLabelCount cellAlpha + bunchedBimonoidAddMultLabelCount cellBeta
      = bunchedBimonoidAddMultLabelCount cellAlpha + bunchedBimonoidAddMultLabelCount cellBeta'
    rw [countEq]
  whiskerLeftCongr := by
    intro dim _ _ _ _ hdim
    exact absurd hdim (fun hclash => bunchedBimonoidSuccSuccNeOne dim hclash)
  whiskerRightCongr := by
    intro dim _ _ _ _ hdim
    exact absurd hdim (fun hclash => bunchedBimonoidSuccSuccNeOne dim hclash)
  idCongr := by
    intro dim cellAlpha cellBeta _ hdim
    have hdimZero : dim = 0 := Nat.succ.inj hdim
    subst hdimZero
    show bunchedBimonoidAddMultLabelCount cellAlpha = bunchedBimonoidAddMultLabelCount cellBeta
    rw [bunchedBimonoidAddMultLabelCountAtDimZero cellAlpha,
      bunchedBimonoidAddMultLabelCountAtDimZero cellBeta]
  whiskerLeftWhiskerCongr := by
    intro dim _ _ _ _ hdim
    exact absurd hdim (fun hclash => bunchedBimonoidSuccSuccNeOne dim hclash)
  whiskerRightWhiskerCongr := by
    intro dim _ _ _ _ hdim
    exact absurd hdim (fun hclash => bunchedBimonoidSuccSuccNeOne dim hclash)
  refl := by
    intro dim cell _
    rfl
  symm := by
    intro dim cellAlpha cellBeta ih hdim
    exact (ih hdim).symm
  trans := by
    intro dim cellAlpha cellBeta cellGamma ihLeft ihRight hdim
    exact (ihLeft hdim).trans (ihRight hdim)

/-! # =========================================================================================
    # THE DECISION — the star Prop is FALSE
    # =========================================================================================
-/

/-- ★★ **The refutation pair is NOT convertible** over the star scope — the standalone non-convertibility: any
derivation would fold through the absorber into a count agreement `1 = 0`. -/
theorem bunchedBimonoidColourMislabeledMuNotConvToAdditiveGen :
    ¬ SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      bunchedBimonoidColourMislabeledMuOneCell bunchedBimonoidAdditiveGen :=
  fun hconv =>
    Nat.noConfusion (SaturatedConvOverWithId.recInto bunchedBimonoidAddMultCountAbsorbsStarScope hconv rfl)

/-- ★★★ **THE #2033 STAR IS DECIDED — FALSE.**  `bunchedBimonoidStarStatementAdditiveWellTyped` (the r7
corrected star, `StarAssembly`) is refuted: the colour-mislabeled 1-cell datum satisfies ALL five premises
(additive x2, well-typed x2, equal evaluation) against the genuine colour `a`, yet the pair is not convertible.
Zero-axiom, kernel-checked.  Twenty-four rounds of siege end here: the statement, not the dim-2 mathematics,
was the obstruction. -/
theorem bunchedBimonoidStarStatementAdditiveWellTypedRefuted :
    ¬ bunchedBimonoidStarStatementAdditiveWellTyped :=
  fun hstar =>
    bunchedBimonoidColourMislabeledMuNotConvToAdditiveGen
      (hstar (dim := 1) bunchedBimonoidColourMislabeledMuOneCell bunchedBimonoidAdditiveGen
        rfl rfl
        bunchedBimonoidColourMislabeledMuOneCellWellTyped
        bunchedBimonoidAdditiveGenWellTypedForRefutation
        rfl)

/-! # =========================================================================================
    # THE dim >= 3 TRIVIALITY WITNESS (why the corrected target must pin dimension 2)
    # =========================================================================================
-/

/-- ★ **The dim-3 evaluation triviality** — `bunchedBimonoidEvalCell` is constantly `()` above dimension 2, so
the structurally unrelated 3-cells `id mu_a` and `id delta_a` (both additive, both well-typed) satisfy the
equal-evaluation premise on the nose.  Any all-dimension restatement therefore asserts mutual convertibility of
essentially arbitrary higher cells — the corrected completeness target must PIN dimension 2 (where the matrix
semantics is faithful), not merely repair the label guard. -/
theorem bunchedBimonoidDimThreeEvalTriviallyEqual :
    bunchedBimonoidEvalCell (CellExpr.id bunchedBimonoidAddMuGen)
      = bunchedBimonoidEvalCell (CellExpr.id bunchedBimonoidAddDeltaGen) := rfl

/-! # =========================================================================================
    # THE MARKERS — the decision ledger (supersession, not owner-flip)
    # =========================================================================================
-/

/-- ★★★ **THE DECISION MARKER — the corrected well-typed star is DECIDED FALSE.**  `= true` records
`bunchedBimonoidStarStatementAdditiveWellTypedRefuted`: the r7 star Prop is disproven zero-axiom.  This is the
new-file superseding-content vehicle (the Brauer-r55 precedent) for the frozen owner
`fxBunchedBimonoid_correctedWellTypedStarStillOpen` (`StarAssembly`, `= false` byte-intact): its recorded content
("not proven in r7") remains literally true and is now STRENGTHENED — the star is not open, it is CLOSED
NEGATIVELY.  The owner never flips to `true`: the flip law reserved that for a proof, and the Prop is false. -/
def fxBunchedBimonoid_correctedWellTypedStarDecidedFalse : Bool := true

/-- ★★ **THE HONESTY MARKER — the refutation is an off-dimension artifact, NOT a defeat of the dim-2 content.**
`= true` records that the refutation datum lives at dimension 1 (a colour-position gen node carrying an
operation label, invisible to the r7 width-agreement) and that dimension >= 3 trivializes the evaluation
(`bunchedBimonoidDimThreeEvalTriviallyEqual`).  The dim-2 bimonoid completeness content the siege actually
ground on (the retract, the block-threading, the recComb middle) is NOT refuted; it needs a RE-STATED target:
dimension pinned to 2 PLUS a label-placement guard (colour labels at label-dimension 0, operation labels at
label-dimension 1) — the corrected statement is the next brick, with the r28-designed block-threading induction
as its `vcomp` engine. -/
def fxBunchedBimonoid_starRefutedByOffDimensionMislabelNotDimTwoContent : Bool := true

/-- ★★★ **ESTABLISHED — the WP-PROP r29 star-decision ledger (the honest scoreboard).**  `= true` records the
complete decision: the refutation datum with all five star premises machine-checked
(`bunchedBimonoidColourMislabeledMuOneCell{IsAdditive,WellTyped,WidthMatchesAdditiveGen}`), the propext-free
row-family dimension census (`bunchedBimonoid{Sound,Hexagon}RowDimIsTwo`,
`bunchedBimonoidStrictRowPreservesAddMultCountAtDimOne`), the star-scope absorber
(`bunchedBimonoidAddMultCountAbsorbsStarScope`), the standalone non-convertibility
(`bunchedBimonoidColourMislabeledMuNotConvToAdditiveGen`), and THE DECISION
(`bunchedBimonoidStarStatementAdditiveWellTypedRefuted`).  Every frozen upstream marker keeps its name and value
byte-intact (`fxBunchedBimonoid_correctedWellTypedStarStillOpen` and all r7-r28 walls — cross-file, not edited);
zero-axiom (per-decl `#assert_no_axioms` + independent `#print axioms` in the twin); STRUCTURAL only. -/
def fxBunchedBimonoid_starColourMislabelRefutationLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega

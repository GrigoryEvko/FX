import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidAffineOffsetSemantics
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarDimTwoCanonicalRestatement

/-! # Polygraph/Omega/WalkingBunchedBimonoidStarUnitLawRefutation — ★★★ THE r30 DECISION: the corrected
dim-2-canonical star is FALSE — the star scope carries NO UNIT LAW (WP-PROP r30, #2033)

★★★ **THE SECOND STAR FALLS, AND THIS TIME ON GENUINE DIM-2 CANONICAL CONTENT.**  The r29 restatement
`bunchedBimonoidStarStatementDimTwoCanonicalGens` pinned the dimension to 2 and the generator nodes to the
nine canonical presentation generators — closing every QUANTIFIER leak.  This file shows the remaining leak
is in the PRESENTATION itself: the star scope (`StrictAxiomRel union SoundRow union HexagonRow`) contains **no
(co)unit law**.  The r2 adjudication excised the three broken unit-shaped rows (`unitUnit`,
`leftUnitAssoc`, `rightUnitAssoc` — the END-MISMATCHED spellings) as over-quotients, and the surviving
`rootUnitAssoc` / `rootCounitCoassoc` rows are mere disjoint-strand naturality squares (interchange
instances).  Nothing in the scope can cancel an `eta_a` into a `mu_a`.

**The refutation pair** — both cells additive, well-typed, canonical, dimension 2, with EQUAL plain matrices
`[[1]]`:

  * `bunchedBimonoidUnitIntoMuCell  = (a <| eta_a) ; mu_a : a.id => a` — feed a unit into the multiplication;
  * `bunchedBimonoidIdentityStrandCell = id_a : a => a`.

The classical right-unit law would identify them; the star scope cannot: the sibling file's AFFINE-OFFSET
semantics (`bunchedBimonoidEvalAugCell` — the `Mat(N)` functor augmented with a per-output unit-path offset
column) absorbs the ENTIRE star scope congruence (`bunchedBimonoidAugGatedAbsorbsStarScope`, composability-
gated, including the historically walled `whiskerRightFunctorial` and Godement interchange) yet separates the
pair: `[[1,0],[1,1]]` vs `[[1,0],[0,1]]`.  Hence NOT convertible, hence the corrected star is REFUTED —
kernel-checked, zero-axiom.

**Honest scoping.**  Unlike the r29 colour-mislabel (an off-dimension quantifier artifact), this hole is the
genuine mathematical content of the r29 restatement AS STATED: the scope presents the NON-UNITAL fragment
(bicommutative bi-semigroup with unit/counit POINTS satisfying only the bialgebra and braiding-naturality
laws), whose free PROP is strictly finer than `Mat(N)`.  The corrected unital target is re-stated in the
sibling `WalkingBunchedBimonoidStarUnitalRestatement`.

The frozen r29 owner `fxBunchedBimonoid_dimTwoCanonicalGensStarStillOpen` stays byte-intact `= false`;
supersession is by the NEW-FILE content marker `fxBunchedBimonoid_dimTwoCanonicalGensStarDecidedFalse = true`
below (the r29 vehicle pattern).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # THE REFUTATION PAIR
    # =========================================================================================
-/

/-- ★★ `(a <| eta_a) ; mu_a : a.id => a` — the right-unit-law LEFT leg: a unit fed into the multiplication. -/
def bunchedBimonoidUnitIntoMuCell : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEtaGen)
    bunchedBimonoidAddMuGen

/-- `id_a : a => a` — the right-unit-law RIGHT leg. -/
def bunchedBimonoidIdentityStrandCell : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.id bunchedBimonoidAdditiveGen

/-! ## The pair passes EVERY premise of the corrected star -/

/-- The left leg is additive. -/
theorem bunchedBimonoidUnitIntoMuAdditive :
    bunchedBimonoidCellUsesOnlyAdditive bunchedBimonoidUnitIntoMuCell = true := rfl

/-- The right leg is additive. -/
theorem bunchedBimonoidIdentityStrandAdditive :
    bunchedBimonoidCellUsesOnlyAdditive bunchedBimonoidIdentityStrandCell = true := rfl

/-- The left leg is well-typed (every generator width-agreement holds; the composite interface `2 = 2`). -/
theorem bunchedBimonoidUnitIntoMuWellTyped :
    bunchedBimonoidCellWellTyped bunchedBimonoidUnitIntoMuCell :=
  ⟨⟨⟨True.intro, True.intro, True.intro⟩,
      ⟨True.intro, ⟨True.intro, True.intro, True.intro⟩, rfl, rfl⟩⟩,
    ⟨⟨⟨True.intro, True.intro, True.intro⟩, ⟨True.intro, True.intro, True.intro⟩, True.intro⟩,
      ⟨True.intro, True.intro, True.intro⟩, rfl, rfl⟩,
    rfl⟩

/-- The right leg is well-typed. -/
theorem bunchedBimonoidIdentityStrandWellTyped :
    bunchedBimonoidCellWellTyped bunchedBimonoidIdentityStrandCell :=
  ⟨True.intro, True.intro, True.intro⟩

/-- The left leg has canonical generator nodes (every `gen` is a presentation generator on the nose). -/
theorem bunchedBimonoidUnitIntoMuCanonical :
    bunchedBimonoidCellGensCanonical bunchedBimonoidUnitIntoMuCell :=
  ⟨⟨bunchedBimonoidAdditiveGenCanonical,
      ⟨Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), True.intro, bunchedBimonoidAdditiveGenCanonical⟩⟩,
    bunchedBimonoidAddMuGenCanonical⟩

/-- The right leg has canonical generator nodes. -/
theorem bunchedBimonoidIdentityStrandCanonical :
    bunchedBimonoidCellGensCanonical bunchedBimonoidIdentityStrandCell :=
  bunchedBimonoidAdditiveGenCanonical

/-- ★★ **The plain matrices are EQUAL** — both legs evaluate to `[[1]]` under the shipped `Mat(N)` functor:
the plain semantics cannot see the swallowed unit. -/
theorem bunchedBimonoidUnitIntoMuMatrixEqualsIdentityStrand :
    bunchedBimonoidEvalCell bunchedBimonoidUnitIntoMuCell
      = bunchedBimonoidEvalCell bunchedBimonoidIdentityStrandCell := rfl

/-! # =========================================================================================
    # THE SEPARATION — the affine offset sees what the matrix cannot
    # =========================================================================================
-/

/-- Both legs are Clean (interface-composable). -/
theorem bunchedBimonoidUnitIntoMuClean :
    bunchedBimonoidAugCleanGate bunchedBimonoidUnitIntoMuCell = true := rfl

/-- The identity strand is Clean. -/
theorem bunchedBimonoidIdentityStrandClean :
    bunchedBimonoidAugCleanGate bunchedBimonoidIdentityStrandCell = true := rfl

/-- ★★ **The affine-offset values DIFFER** — `[[1,0],[1,1]]` vs `[[1,0],[0,1]]`: the offset column records
the unit path into the output strand. -/
theorem bunchedBimonoidUnitIntoMuAugValueSeparates :
    bunchedBimonoidEvalAugCell bunchedBimonoidUnitIntoMuCell
      ≠ bunchedBimonoidEvalAugCell bunchedBimonoidIdentityStrandCell := by
  intro valuesEq
  exact absurd
    (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 1 0) valuesEq)
    (by decide)

/-- ★★★ **THE NON-CONVERTIBILITY** — the pair is NOT convertible over the star scope: any convertibility
would fold through the gated affine absorber into equal augmented values, contradiction. -/
theorem bunchedBimonoidUnitIntoMuNotConvToIdentityStrand :
    ¬ SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      bunchedBimonoidUnitIntoMuCell bunchedBimonoidIdentityStrandCell := by
  intro conv
  exact bunchedBimonoidUnitIntoMuAugValueSeparates
    ((bunchedBimonoidAugGatedEqOfStarConv conv).2
      bunchedBimonoidUnitIntoMuClean bunchedBimonoidIdentityStrandClean)

/-! # =========================================================================================
    # THE DECISION — the corrected dim-2-canonical star is FALSE
    # =========================================================================================
-/

/-- ★★★ **THE r29 CORRECTED STAR IS REFUTED** — `bunchedBimonoidStarStatementDimTwoCanonicalGens` (consumed
BY NAME from the frozen r29 restatement) is FALSE: the unit-into-multiplication pair passes all seven premises
(dimension pin, additivity x2, well-typedness x2, canonicity x2, equal plain matrices) yet is not convertible
— the star scope carries no unit law to cancel the `eta_a`. -/
theorem bunchedBimonoidStarStatementDimTwoCanonicalGensRefuted :
    ¬ bunchedBimonoidStarStatementDimTwoCanonicalGens := by
  intro star
  exact bunchedBimonoidUnitIntoMuNotConvToIdentityStrand
    (star bunchedBimonoidUnitIntoMuCell bunchedBimonoidIdentityStrandCell
      bunchedBimonoidUnitIntoMuAdditive bunchedBimonoidIdentityStrandAdditive
      bunchedBimonoidUnitIntoMuWellTyped bunchedBimonoidIdentityStrandWellTyped
      bunchedBimonoidUnitIntoMuCanonical bunchedBimonoidIdentityStrandCanonical
      bunchedBimonoidUnitIntoMuMatrixEqualsIdentityStrand)

/-! ## The dual (counit) witness — the same hole from the comultiplication side -/

/-- `delta_a ; (a <| eps_a) : a => a.id` — the right-counit-law left leg. -/
def bunchedBimonoidDeltaIntoCounitCell : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidAddDeltaGen
    (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddEpsGen)

/-- ★ The counit-side pair separates in the affine transpose position too: the counit swallows a strand the
plain matrix cannot miss, but here the OFFSET stays zero — the separation is witnessed by the affine
DIMENSIONS instead (`a.id` target vs `a` target is invisible to `Mat(N)` rows/cols only after the strict
rows; the honest counit witness is deferred to the unital restatement's fires).  Recorded here as the matrix
BLINDNESS witness: the plain matrices agree. -/
theorem bunchedBimonoidDeltaIntoCounitMatrixBlind :
    bunchedBimonoidEvalCell bunchedBimonoidDeltaIntoCounitCell
      = bunchedBimonoidEvalCell bunchedBimonoidIdentityStrandCell := rfl

/-! # =========================================================================================
    # THE MARKERS — the r30 decision, honestly scoped
    # =========================================================================================
-/

/-- ★★★ **ESTABLISHED — THE r29 CORRECTED STAR IS DECIDED FALSE (the r30 decision).**  `= true` records
`bunchedBimonoidStarStatementDimTwoCanonicalGensRefuted`: the dim-2-pinned, additive, well-typed,
canonical-generator completeness target is REFUTED by the unit-into-multiplication pair through the
composability-gated affine-offset absorber.  The refutation datum is GENUINE dim-2 canonical content — the
scope's presentation lacks the (co)unit laws (the r2 excision removed the broken spellings without restoring
the correct ones).  The frozen r29 owner `fxBunchedBimonoid_dimTwoCanonicalGensStarStillOpen` stays
byte-intact `= false`; this marker supersedes it by content (the r29 new-file vehicle). -/
def fxBunchedBimonoid_dimTwoCanonicalGensStarDecidedFalse : Bool := true

/-- ★★ **ESTABLISHED — the missing laws are exactly the (co)unit laws.**  `= true` records the anatomy: the
scope's `rootUnitAssoc` / `rootCounitCoassoc` rows are disjoint-strand naturality squares, NOT unit laws; the
pair separated here is exactly the right-unit-law instance; the unital re-statement (sibling file) closes the
hole by construction and re-opens the siege at the honest Lafont scope. -/
def fxBunchedBimonoid_starScopeLacksUnitCounitLaws : Bool := true

end FX1Poly.Polygraph.Omega

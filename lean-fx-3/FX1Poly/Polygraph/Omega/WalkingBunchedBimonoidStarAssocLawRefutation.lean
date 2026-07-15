-- TODO: DELETE THIS GARBAGE -- defective bunchedBimonoid star (refuted r29/r30/r31); superseded by the LafontProp re-founding
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidBracketMagmaSemantics

/-! # Polygraph/Omega/WalkingBunchedBimonoidStarAssocLawRefutation — ★★★ THE r31 DECISION: the UNITAL star is
FALSE — the unital scope carries NO ASSOCIATIVITY LAW (WP-PROP r31, #2033)

★★★ **THE THIRD STAR FALLS.**  The r30 restatement `bunchedBimonoidStarStatementDimTwoCanonicalGensUnital`
restored the four (co)unit laws the r2 excision dropped.  This file shows the presentation has a SECOND
excision hole of exactly the same anatomy: the scope's `pentagon` / `copentagon` rows are DISJOINT-STRAND
Godement squares (`(mu |> aa) ; (a <| mu) ~ (aa <| mu) ; (mu |> a)` — literally `interchange(mu, mu)`
instances), NOT the monoid associativity `(mu |> a) ; mu ~ (a <| mu) ; mu`.  Nothing in
`StrictAxiomRel ∪ SoundRow ∪ HexagonRow ∪ UnitCounitRow` reassociates a fold.

**The refutation pair** — both cells additive, well-typed, canonical, dimension 2:

  * `bunchedBimonoidLeftAssocCell  = (mu_a |> a) ; mu_a : (a.a).a => a` — the left association;
  * `bunchedBimonoidRightAssocCell = (a <| mu_a) ; mu_a : a.(a.a) => a` — the right association.

The plain matrices agree (`[[1,1,1]]`) AND — decisively — the r30 AFFINE-OFFSET values agree
(`[[1,0,0,0],[0,1,1,1]]`): the r30 invariant is BLIND to association orders, so a genuinely NEW invariant was
required.  The sibling `WalkingBunchedBimonoidBracketMagmaSemantics` supplies it: evaluation into the free
commutative unital magma (canonical bracket trees), which gated-absorbs the ENTIRE unital scope — every
strict, sound, hexagon AND (co)unit row — yet assigns `(x0 * x1) * x2` to the left association and
`x0 * (x1 * x2)` to the right.  Hence NOT convertible, hence the unital star is REFUTED — kernel-checked,
zero-axiom.

**Honest scoping.**  Like the r30 unit hole (and unlike the r29 quantifier leak), this is genuine dim-2
canonical content: the unital scope presents unital bicommutative MAGMA-bialgebra structure — its free PROP
is strictly finer than `Mat(N)` because matrices cannot see brackets.  The corrected associative target is
re-stated in the sibling `WalkingBunchedBimonoidStarAssociativeRestatement`.

The frozen r30 owner `fxBunchedBimonoid_dimTwoCanonicalGensUnitalStarStillOpen` stays byte-intact `= false`;
supersession is by the NEW-FILE content marker `fxBunchedBimonoid_dimTwoCanonicalGensUnitalStarDecidedFalse
= true` below (the r29/r30 vehicle pattern).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # THE PAIR PASSES EVERY PREMISE OF THE UNITAL STAR
    # =========================================================================================
-/

/-- The left association is additive. -/
theorem bunchedBimonoidLeftAssocAdditive :
    bunchedBimonoidCellUsesOnlyAdditive bunchedBimonoidLeftAssocCell = true := rfl

/-- The right association is additive. -/
theorem bunchedBimonoidRightAssocAdditive :
    bunchedBimonoidCellUsesOnlyAdditive bunchedBimonoidRightAssocCell = true := rfl

/-- The left association is well-typed (`2 x 3` whisker block into the `1 x 2` fold: interface `2 = 2`). -/
theorem bunchedBimonoidLeftAssocWellTyped :
    bunchedBimonoidCellWellTyped bunchedBimonoidLeftAssocCell :=
  ⟨⟨bunchedBimonoidAddMuGenWellTyped, ⟨True.intro, True.intro, True.intro⟩⟩,
    bunchedBimonoidAddMuGenWellTyped, rfl⟩

/-- The right association is well-typed. -/
theorem bunchedBimonoidRightAssocWellTyped :
    bunchedBimonoidCellWellTyped bunchedBimonoidRightAssocCell :=
  ⟨⟨⟨True.intro, True.intro, True.intro⟩, bunchedBimonoidAddMuGenWellTyped⟩,
    bunchedBimonoidAddMuGenWellTyped, rfl⟩

/-- The left association has canonical generator nodes. -/
theorem bunchedBimonoidLeftAssocCanonical :
    bunchedBimonoidCellGensCanonical bunchedBimonoidLeftAssocCell :=
  ⟨⟨bunchedBimonoidAddMuGenCanonical, bunchedBimonoidAdditiveGenCanonical⟩,
    bunchedBimonoidAddMuGenCanonical⟩

/-- The right association has canonical generator nodes. -/
theorem bunchedBimonoidRightAssocCanonical :
    bunchedBimonoidCellGensCanonical bunchedBimonoidRightAssocCell :=
  ⟨⟨bunchedBimonoidAdditiveGenCanonical, bunchedBimonoidAddMuGenCanonical⟩,
    bunchedBimonoidAddMuGenCanonical⟩

/-- ★★ **The plain matrices are EQUAL** — both associations evaluate to `[[1,1,1]]`: `Mat(N)` cannot see
brackets. -/
theorem bunchedBimonoidAssocPairMatricesEqual :
    bunchedBimonoidEvalCell bunchedBimonoidLeftAssocCell
      = bunchedBimonoidEvalCell bunchedBimonoidRightAssocCell := rfl

/-! # =========================================================================================
    # THE r30 AFFINE INVARIANT IS BLIND — a genuinely NEW invariant was required
    # =========================================================================================
-/

/-- ★★ **The r30 AFFINE-OFFSET values are EQUAL too** — both associations evaluate to
`[[1,0,0,0],[0,1,1,1]]` under the augmented functor: the invariant that decided the r30 star cannot decide
this one.  The refutation genuinely required the third (bracket-magma) semantics. -/
theorem bunchedBimonoidAssocPairAugValuesEqual :
    bunchedBimonoidEvalAugCell bunchedBimonoidLeftAssocCell
      = bunchedBimonoidEvalAugCell bunchedBimonoidRightAssocCell :=
  bunchedBimonoidMatEqOfEntries _ _ (by decide) (by decide) (by decide)

/-! # =========================================================================================
    # THE SEPARATION — the bracket magma sees the association order
    # =========================================================================================
-/

/-- Both associations are Clean (interface-composable). -/
theorem bunchedBimonoidLeftAssocClean :
    bunchedBimonoidAugCleanCell bunchedBimonoidLeftAssocCell = true := rfl

/-- The right association is Clean. -/
theorem bunchedBimonoidRightAssocClean :
    bunchedBimonoidAugCleanCell bunchedBimonoidRightAssocCell = true := rfl

/-- ★★ **The bracket values DIFFER** — `(x0 * x1) * x2` versus `x0 * (x1 * x2)` as canonical trees (the
comparator separates them: the left value's head compares `.gt` against the right value, never `.eq`;
propext-free via `congrArg` + `noConfusion`, no wildcard match). -/
theorem bunchedBimonoidAssocPairBracketSeparates :
    bunchedBimonoidBracketEval bunchedBimonoidLeftAssocCell bunchedBimonoidBracketThreeVars
      ≠ bunchedBimonoidBracketEval bunchedBimonoidRightAssocCell bunchedBimonoidBracketThreeVars := by
  intro valuesEq
  rw [bunchedBimonoidLeftAssocBracketValue, bunchedBimonoidRightAssocBracketValue] at valuesEq
  have headsEq :
      BunchedBimonoidBracketTree.pairNode (.varLeaf 2) (.pairNode (.varLeaf 0) (.varLeaf 1))
        = BunchedBimonoidBracketTree.pairNode (.varLeaf 0) (.pairNode (.varLeaf 1) (.varLeaf 2)) :=
    congrArg (fun trees => bunchedBimonoidBracketGet trees 0) valuesEq
  have comparedEq := congrArg
    (fun tree => bunchedBimonoidBracketTreeCompare tree
      (BunchedBimonoidBracketTree.pairNode (.varLeaf 0) (.pairNode (.varLeaf 1) (.varLeaf 2))))
    headsEq
  exact Ordering.noConfusion (show Ordering.gt = Ordering.eq from comparedEq)

/-- ★★★ **THE NON-CONVERTIBILITY** — the two associations are NOT convertible over the UNITAL scope: any
convertibility would fold through the gated bracket absorber into equal bracket values at `[x0, x1, x2]`,
contradiction. -/
theorem bunchedBimonoidAssocPairNotConvUnital :
    ¬ SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidUnitalStarCongruenceScope
      bunchedBimonoidLeftAssocCell bunchedBimonoidRightAssocCell := by
  intro conv
  have gated := bunchedBimonoidBracketGatedEqOfUnitalConv conv
  exact bunchedBimonoidAssocPairBracketSeparates
    (gated.2.2.2 bunchedBimonoidLeftAssocClean bunchedBimonoidRightAssocClean
      bunchedBimonoidBracketThreeVars rfl)

/-! # =========================================================================================
    # THE DECISION — the unital star is FALSE
    # =========================================================================================
-/

/-- ★★★ **THE r30 UNITAL STAR IS REFUTED** — `bunchedBimonoidStarStatementDimTwoCanonicalGensUnital`
(consumed BY NAME from the frozen r30 restatement) is FALSE: the association pair passes all seven premises
(dimension pin, additivity x2, well-typedness x2, canonicity x2, equal plain matrices) yet is not
convertible — the unital scope carries no associativity law to reassociate a fold. -/
theorem bunchedBimonoidStarStatementDimTwoCanonicalGensUnitalRefuted :
    ¬ bunchedBimonoidStarStatementDimTwoCanonicalGensUnital := by
  intro star
  exact bunchedBimonoidAssocPairNotConvUnital
    (star bunchedBimonoidLeftAssocCell bunchedBimonoidRightAssocCell
      bunchedBimonoidLeftAssocAdditive bunchedBimonoidRightAssocAdditive
      bunchedBimonoidLeftAssocWellTyped bunchedBimonoidRightAssocWellTyped
      bunchedBimonoidLeftAssocCanonical bunchedBimonoidRightAssocCanonical
      bunchedBimonoidAssocPairMatricesEqual)

/-! ## The anatomy — the surviving `pentagon` rows are Godement squares, not associativity -/

/-- ★ The scope's `addMonadPentagon` row is EXACTLY the `interchange(mu_a, mu_a)` instance — its left leg is
the strict interchange's left leg on the nose (`rfl`): the transported "pentagon" is a disjoint-strand
naturality square, so the presentation never carried the 3-strand reassociation. -/
theorem bunchedBimonoidPentagonIsInterchangeInstance :
    bunchedBimonoidAddMonadPentagonLeftLeg
      = CellExpr.vcomp
          (CellExpr.whiskerRight bunchedBimonoidAddMuGen (boundarySource bunchedBimonoidAddMuGen))
          (CellExpr.whiskerLeft (boundaryTarget bunchedBimonoidAddMuGen) bunchedBimonoidAddMuGen) := rfl

/-! # =========================================================================================
    # THE MARKERS — the r31 decision, honestly scoped
    # =========================================================================================
-/

/-- ★★★ **ESTABLISHED — THE r30 UNITAL STAR IS DECIDED FALSE (the r31 decision).**  `= true` records
`bunchedBimonoidStarStatementDimTwoCanonicalGensUnitalRefuted`: the unital completeness target is REFUTED by
the association pair through the composability-gated bracket-magma absorber.  The refutation datum is GENUINE
dim-2 canonical content — the presentation lacks the (co)associativity laws (the transported pentagon /
copentagon rows are Godement interchange squares).  The frozen r30 owner
`fxBunchedBimonoid_dimTwoCanonicalGensUnitalStarStillOpen` stays byte-intact `= false`; this marker
supersedes it by content (the r29/r30 new-file vehicle). -/
def fxBunchedBimonoid_dimTwoCanonicalGensUnitalStarDecidedFalse : Bool := true

/-- ★★ **ESTABLISHED — the missing laws are exactly the (co)associativity laws.**  `= true` records the
anatomy: the scope's pentagon / copentagon rows are `interchange` instances
(`bunchedBimonoidPentagonIsInterchangeInstance`); the pair separated here is exactly the associativity-law
instance; the plain matrix AND the r30 affine invariant are both blind to it
(`bunchedBimonoidAssocPairAugValuesEqual`) — the decision required the bracket-magma semantics.  The
associative re-statement (sibling file) closes the hole by construction and re-opens the siege. -/
def fxBunchedBimonoid_unitalStarScopeLacksAssociativity : Bool := true

end FX1Poly.Polygraph.Omega

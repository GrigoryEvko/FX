-- TODO: DELETE THIS GARBAGE -- defective bunchedBimonoid star (refuted r29/r30/r31); superseded by the LafontProp re-founding
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarAssocLawRefutation

/-! # Polygraph/Omega/WalkingBunchedBimonoidStarAssociativeRestatement — the completeness target re-stated
over the ASSOCIATIVE unital scope: the (co)associativity laws restored (WP-PROP r31, #2033)

★★ **THE CORRECTED^3 TARGET.**  The r31 sibling refuted the r30 unital star through the missing
(co)associativity laws.  This file restores them: `BunchedBimonoidAssocRow` carries the two honest rows
(monoid associativity `(mu |> a) ; mu ~ (a <| mu) ; mu` and comonoid coassociativity
`delta ; (delta |> a) ~ delta ; (a <| delta)` — each MATRIX-SOUND, machine-checked `rfl`), the star scope
widens by them, and the completeness target is re-stated over the widened scope — at last the FULL Lafont
row census: associativity + commutativity + units, coassociativity + cocommutativity + counits, the four
bialgebra rows, the braiding involution + Yang-Baxter + all four naturality rows, over the strict omega-laws.
Honesty fires:

  * the exact r31 refutation pair IS convertible over the associative scope (a one-row fire) — the
    correction closes precisely the exposed hole; the whiskered pair converts by congruence transport;
  * the coassociativity pair converts too;
  * the bracket-magma separation is DEAD against the associative scope: the `muAssoc` row relates cells with
    DIFFERENT bracket values (machine-checked), so the r31 refutation invariant cannot re-fire.

★ **THE FLAGGED RESIDUAL RISK (the successor's first adjudication duty).**  The strict axiom set carries the
whisker-action ASSOCIATOR laws but no whisker-action UNIT law (`idOne <| X ~ X` / `X |> idOne ~ X` is NOT a
row).  For `X` in the (co)unit-bearing fragment the widened scope now DERIVES it — e.g. `mu |> idOne ~ mu`
via `rootUnitAssoc`, the `rightUnit` row, and the NEW `muAssoc` row — but for `X := sigma_a` no derivation is
known and no shipped invariant separates (`sigma |> idOne` vs `sigma`: equal matrices, equal affine values,
equal bracket values).  The successor must either derive the sigma case (hexagon + involution routes) or
decide it and re-widen with the sesquicategory unit-action rows.  The owner stays `= false` until the star is
genuinely proven.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # THE TWO (CO)ASSOCIATIVITY ROWS
    # =========================================================================================
-/

/-- The coassociativity LEFT leg `delta_a ; (delta_a |> a) : a => (a.a).a`. -/
def bunchedBimonoidCoassocLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidAddDeltaGen bunchedBimonoidDeltaWhiskerRight

/-- The coassociativity RIGHT leg `delta_a ; (a <| delta_a) : a => a.(a.a)`. -/
def bunchedBimonoidCoassocRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidAddDeltaGen bunchedBimonoidDeltaWhiskerLeft

/-- ★★ **The two (co)associativity rows** — the honest monoid / comonoid reassociation laws the transported
pentagon / copentagon rows (Godement squares) never carried.  Each row is matrix-sound (`rfl`, below). -/
inductive BunchedBimonoidAssocRow :
    {d : Nat} → CellExpr bunchedBimonoidOmegaComputad d → CellExpr bunchedBimonoidOmegaComputad d →
      Prop where
  /-- Monoid associativity `(mu |> a) ; mu ~ (a <| mu) ; mu`. -/
  | muAssoc : BunchedBimonoidAssocRow bunchedBimonoidLeftAssocCell bunchedBimonoidRightAssocCell
  /-- Comonoid coassociativity `delta ; (delta |> a) ~ delta ; (a <| delta)`. -/
  | deltaCoassoc : BunchedBimonoidAssocRow bunchedBimonoidCoassocLeftLeg
      bunchedBimonoidCoassocRightLeg

/-- ★ **Every (co)associativity row is matrix-sound** — the legs share their plain `Mat(N)` value
(`[[1,1,1]]` for the fold reassociation, `[[1],[1],[1]]` for the fan; full-enumeration match, no wildcard). -/
theorem bunchedBimonoidAssocRowMatrixSound {d : Nat}
    {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad d}
    (row : BunchedBimonoidAssocRow cellAlpha cellBeta) :
    bunchedBimonoidEvalCell cellAlpha = bunchedBimonoidEvalCell cellBeta := by
  match row with
  | .muAssoc => rfl
  | .deltaCoassoc => rfl

/-! # =========================================================================================
    # THE ASSOCIATIVE SCOPE + THE RE-STATED TARGET
    # =========================================================================================
-/

/-- ★★ **The associative unital star scope** — the r30 unital scope widened by the two (co)associativity
rows: the FULL Lafont / Pirashvili / Fox row census for the additive bicommutative-bimonoid PROP. -/
def bunchedBimonoidAssociativeStarCongruenceScope : CellRelOver bunchedBimonoidOmegaComputad :=
  unionCellRel bunchedBimonoidOmegaComputad bunchedBimonoidUnitalStarCongruenceScope
    (fun {d} cellAlpha cellBeta => @BunchedBimonoidAssocRow d cellAlpha cellBeta)

/-- Unital-scope convertibility embeds into the associative scope (monotonicity). -/
theorem bunchedBimonoidUnitalConvEmbedsIntoAssociative {dim : Nat}
    {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim}
    (conv : SaturatedConvOverWithId bunchedBimonoidOmegaComputad
      bunchedBimonoidUnitalStarCongruenceScope cellAlpha cellBeta) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad
      bunchedBimonoidAssociativeStarCongruenceScope cellAlpha cellBeta := by
  induction conv with
  | ofRelation row => exact SaturatedConvOverWithId.ofRelation (Or.inl row)
  | vcompCongrLeft cellBetaFixed _ ih => exact SaturatedConvOverWithId.vcompCongrLeft cellBetaFixed ih
  | vcompCongrRight cellAlphaFixed _ ih =>
      exact SaturatedConvOverWithId.vcompCongrRight cellAlphaFixed ih
  | whiskerLeftCongr whiskeringCell _ ih =>
      exact SaturatedConvOverWithId.whiskerLeftCongr whiskeringCell ih
  | whiskerRightCongr whiskeringCell _ ih =>
      exact SaturatedConvOverWithId.whiskerRightCongr whiskeringCell ih
  | idCongr _ ih => exact SaturatedConvOverWithId.idCongr ih
  | whiskerLeftWhiskerCongr innerCell _ ih =>
      exact SaturatedConvOverWithId.whiskerLeftWhiskerCongr innerCell ih
  | whiskerRightWhiskerCongr innerCell _ ih =>
      exact SaturatedConvOverWithId.whiskerRightWhiskerCongr innerCell ih
  | refl cell => exact SaturatedConvOverWithId.refl cell
  | symm _ ih => exact SaturatedConvOverWithId.symm ih
  | trans _ _ ihLeft ihRight => exact SaturatedConvOverWithId.trans ihLeft ihRight

/-- ★★★ **THE ASSOCIATIVE UNITAL COMPLETENESS TARGET, NAMED (NOT proven).**  Dimension pinned to 2;
additivity, well-typedness, canonical generator nodes; equal plain `Mat(N)` matrices imply convertibility
over the ASSOCIATIVE UNITAL scope.  Every decided refutation datum is excluded by a machine-checked lever:
the r6/r7/r29 leaks by the premises, the r30 unit pair by the unital rows, and the r31 association pair by
the new rows themselves (`bunchedBimonoidAssocPairConvertsAssociative`). -/
def bunchedBimonoidStarStatementDimTwoCanonicalGensUnitalAssoc : Prop :=
  ∀ (cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad 2),
    bunchedBimonoidCellUsesOnlyAdditive cellAlpha = true →
    bunchedBimonoidCellUsesOnlyAdditive cellBeta = true →
    bunchedBimonoidCellWellTyped cellAlpha →
    bunchedBimonoidCellWellTyped cellBeta →
    bunchedBimonoidCellGensCanonical cellAlpha →
    bunchedBimonoidCellGensCanonical cellBeta →
    bunchedBimonoidEvalCell cellAlpha = bunchedBimonoidEvalCell cellBeta →
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad
      bunchedBimonoidAssociativeStarCongruenceScope cellAlpha cellBeta

/-! # =========================================================================================
    # THE HONESTY FIRES
    # =========================================================================================
-/

/-- ★★ **The r31 refutation pair CONVERTS over the associative scope** — a one-row fire. -/
theorem bunchedBimonoidAssocPairConvertsAssociative :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad
      bunchedBimonoidAssociativeStarCongruenceScope
      bunchedBimonoidLeftAssocCell bunchedBimonoidRightAssocCell :=
  SaturatedConvOverWithId.ofRelation (Or.inr BunchedBimonoidAssocRow.muAssoc)

/-- The coassociativity pair converts too. -/
theorem bunchedBimonoidCoassocPairConvertsAssociative :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad
      bunchedBimonoidAssociativeStarCongruenceScope
      bunchedBimonoidCoassocLeftLeg bunchedBimonoidCoassocRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr BunchedBimonoidAssocRow.deltaCoassoc)

/-- The whiskered association pair converts by congruence transport (the new row fires under context). -/
theorem bunchedBimonoidWhiskeredAssocPairConvertsAssociative :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad
      bunchedBimonoidAssociativeStarCongruenceScope
      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidLeftAssocCell)
      (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidRightAssocCell) :=
  SaturatedConvOverWithId.whiskerLeftCongr bunchedBimonoidAdditiveGen
    bunchedBimonoidAssocPairConvertsAssociative

/-- ★★ **The r31 bracket-magma invariant is DEAD against the associative scope** — the `muAssoc` row relates
cells with DIFFERENT bracket values, so the gated bracket absorber cannot extend to the widened scope: the
associative siege is genuinely open, not re-refutable by the r31 separator. -/
theorem bunchedBimonoidAssocRowBreaksBracketInvariant :
    bunchedBimonoidBracketEval bunchedBimonoidLeftAssocCell bunchedBimonoidBracketThreeVars
      ≠ bunchedBimonoidBracketEval bunchedBimonoidRightAssocCell bunchedBimonoidBracketThreeVars :=
  bunchedBimonoidAssocPairBracketSeparates

/-! # =========================================================================================
    # THE MARKERS — the associative siege opens honestly
    # =========================================================================================
-/

/-- ★★★ **ESTABLISHED — the associative re-statement.**  `= true` records the two matrix-sound
(co)associativity rows, the widened scope with the monotone embedding of every shipped unital-scope
convertibility, the re-stated target `bunchedBimonoidStarStatementDimTwoCanonicalGensUnitalAssoc`, the
closure fires on the exact r31 refutation pair (bare and whiskered) and the coassociativity pair, and the
death of the r31 separator against the widened scope. -/
def fxBunchedBimonoid_starAssociativeRestatementShipped : Bool := true

/-- ★ **THE ASSOCIATIVE STAR IS NAMED, NOT PROVEN — the new owner (no flip).**  `= false` records that
`bunchedBimonoidStarStatementDimTwoCanonicalGensUnitalAssoc` is NOT proven.  The bill: (i) FIRST adjudicate
the flagged width-0-whisker residual (`sigma |> idOne` vs `sigma` — derive it over the widened scope or
decide it and re-widen with the sesquicategory unit-action rows; the mu/eta/delta/eps cases are now
derivable through the unit + associativity rows); (ii) the total retract to the unit-free comb normal form
on the (offset, length) lexicographic measure (the r25/r26 comb machinery + the r29 block threading embed
through the two monotone embeddings); (iii) the r26 recComb perm middle; (iv) the assembly.  This marker
flips ONLY with the associative star genuinely proven. -/
def fxBunchedBimonoid_dimTwoCanonicalGensUnitalAssocStarStillOpen : Bool := false

end FX1Poly.Polygraph.Omega

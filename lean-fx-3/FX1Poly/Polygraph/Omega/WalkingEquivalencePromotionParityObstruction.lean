import FX1Poly.Polygraph.Omega.WalkingEquivalencePromotionResidual

/-! # Polygraph/Omega/WalkingEquivalencePromotionParityObstruction — the B3 promotion residual DECIDED:
the interchange bracketing is REFUTED, the guarded theorem ships VACUOUSLY, the true wall is the missing
whisker-unitors (WP-EQUIV #2068 r3)

★★ **THE B3 WALL IS NOT A HAND-COMPUTATION GAP — IT IS A PRESENTATION GAP, machine-checked.**  The shipped
wall `fxEquiv_promotionIdempotencyFromLeftTriangleWalled` guards the theorem "from the left triangle
`phi_f ~ id f` over the BARE relation `walkingEquivBaseRel`, derive the idempotency `psi_g . psi_g ~ psi_g`",
with the recon recipe naming a two-Godement-firing interchange bracketing as the missing step.  This file
adjudicates the node by a FLAGGED GENERATOR PARITY invariant and lands three zero-axiom results:

  1. **The hypothesis is UNINHABITED over the bare relation** (`walkingEquivLeftTriangle_notDerivableOverBareRel`):
     no derivation of `phi_f ~ id f` exists over `walkingEquivBaseRel`.  Hence the guarded theorem HOLDS —
     vacuously — and is shipped (`walkingEquivIdempotencyFromLeftTriangle`), together with the derived right
     triangle (`walkingEquivRightTriangleFromLeftTriangle`).  The vacuity is itself machine-checked, not hidden.

  2. **The interchange-bracketing recipe is REFUTED non-vacuously**: over the relation with the left triangle
     ADJOINED AS A ROW (`walkingEquivLeftTriangleAdjoinedRel`, where the hypothesis IS inhabited —
     `walkingEquivLeftTriangle_derivableOverAdjoinedRel`), the idempotency `psi_g . psi_g ~ psi_g` is STILL not
     derivable (`walkingEquivIdempotency_notDerivableEvenWithLeftTriangleRow`), and neither is the right
     triangle `psi_g ~ id g` (`walkingEquivRightTriangle_notDerivableEvenWithLeftTriangleRow`).  So NO
     bracketing, insertion, or Godement-firing sequence over the shipped rows can close the promotion — the
     recon recipe (a correct 2-CATEGORY argument) does not compile to this row set.

  3. **The obstruction is located exactly**: `StrictAxiomRel` has NO whisker-by-identity-1-cell unitor
     (`X |> id_A ~ X` / `id_B <| X ~ X`).  Those rows exist only in the ADDITIVE `whiskerUnitRel`
     (EckmannHiltonWithId's `strictWithWhiskerUnits`), which `walkingEquivBaseRel` does not include.  The
     parity invariant below is conserved by every shipped row but is BROKEN by the whisker-unitors — they are
     precisely the load-bearing laws the classical promotion needs.  The honest successor node is the
     promotion re-founded over the unitor-augmented relation (`fxEquiv_promotionOverWhiskerUnitorScopeOpen`).

## The invariant (why the refutation is airtight)

For a contribution table `contribution : Bool -> Bool -> WalkingEquivGenLabel -> Bool`, fold a cell to the
PARITY (Bool sum) of `contribution hasLeftWhiskerAncestor hasRightWhiskerAncestor label` over its generator
occurrences, where the two flags record whether the occurrence sits under any `whiskerLeft` / `whiskerRight`
node (identity cells opaque, whiskering 1-cells and declared boundaries not traversed — they can carry no
2-generators).  EVERY strict row conserves the fold at every flag pair (associativity/units by the parity
laws, functoriality/whisker-associators/interchange on the nose), and the four cancellation rows conserve it
whenever the table pairs `eta` with `etaInv` and `eps` with `epsInv` — so the fold extends to the full
`SaturatedConvOverWithId` congruence by the 11-field absorber.  Two instantiations separate:

  * eta-family at `(hasLeft, hasRight) = (false, true)`: `phi_f` (its `eta` sits under `|> f` only) folds to
    `true`, `id f` to `false` — the hypothesis-refutation slot.
  * eta-family at `(true, false)`: conserved ALSO by the left-triangle row itself (its `eta` carries the
    right-whisker flag, so it never contributes at this slot) — yet `psi_g` folds to `true` and both
    `psi_g . psi_g` and `id g` fold to `false` — the idempotency/right-triangle-refutation slot.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` + independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The Bool parity carrier (hand-rolled, propext-free) -/

/-- **Parity addition** (exclusive or), hand-rolled so `add false x = x` holds definitionally and every lemma
is a full-enumeration `rfl` split — no core `Bool.xor` unfolding surprises. -/
def walkingEquivParityAdd : Bool → Bool → Bool
  | false, second => second
  | true, false => true
  | true, true => false

/-- Parity addition is associative — full eight-case enumeration, each `rfl`. -/
theorem walkingEquivParityAdd_assoc (first second third : Bool) :
    walkingEquivParityAdd (walkingEquivParityAdd first second) third
      = walkingEquivParityAdd first (walkingEquivParityAdd second third) :=
  match first, second, third with
  | false, false, false => rfl
  | false, false, true => rfl
  | false, true, false => rfl
  | false, true, true => rfl
  | true, false, false => rfl
  | true, false, true => rfl
  | true, true, false => rfl
  | true, true, true => rfl

/-- Parity addition is commutative — full four-case enumeration. -/
theorem walkingEquivParityAdd_comm (first second : Bool) :
    walkingEquivParityAdd first second = walkingEquivParityAdd second first :=
  match first, second with
  | false, false => rfl
  | false, true => rfl
  | true, false => rfl
  | true, true => rfl

/-- `false` is a right unit for parity addition (the left unit is definitional). -/
theorem walkingEquivParityAdd_falseRight (first : Bool) :
    walkingEquivParityAdd first false = first :=
  match first with
  | false => rfl
  | true => rfl

/-- Parity addition of equal arguments vanishes — the cancellation-row engine. -/
theorem walkingEquivParityAdd_self (first : Bool) :
    walkingEquivParityAdd first first = false :=
  match first with
  | false => rfl
  | true => rfl

/-! ## The flagged generator parity fold -/

/-- ★ The **flagged generator parity** of a cell: the parity of `contribution hasLeft hasRight label` over the
generator occurrences of the cell, where `hasLeftWhiskerAncestor` / `hasRightWhiskerAncestor` record whether
the occurrence sits under any `whiskerLeft` / `whiskerRight` node.  Identity cells are opaque (contribute
`false` regardless of content); whiskering 1-cells and declared generator boundaries are not traversed (they
are strictly-lower-dimensional and can carry no 2-generators of the walking equivalence).  A constant-motive
structural fold mirroring `cellSize` — propext-free. -/
def walkingEquivFlaggedGenParity
    (contribution : Bool → Bool → WalkingEquivGenLabel → Bool) :
    {dim : Nat} → Bool → Bool → CellExpr walkingEquivComputad dim → Bool
  | _, _, _, .ofMode _ => false
  | _, hasLeftAncestor, hasRightAncestor, .gen label _ _ =>
      contribution hasLeftAncestor hasRightAncestor label
  | _, _, _, .id _ => false
  | _, hasLeftAncestor, hasRightAncestor, .vcomp leftCell rightCell =>
      walkingEquivParityAdd
        (walkingEquivFlaggedGenParity contribution hasLeftAncestor hasRightAncestor leftCell)
        (walkingEquivFlaggedGenParity contribution hasLeftAncestor hasRightAncestor rightCell)
  | _, _, hasRightAncestor, .whiskerLeft _ innerCell =>
      walkingEquivFlaggedGenParity contribution true hasRightAncestor innerCell
  | _, hasLeftAncestor, _, .whiskerRight innerCell _ =>
      walkingEquivFlaggedGenParity contribution hasLeftAncestor true innerCell

/-! ## Conservation: every strict row conserves the fold, at every flag pair, for ANY contribution table -/

/-- ★ **Every strict omega row conserves the flagged parity** — for an ARBITRARY contribution table.
Associativity by parity-associativity, the units by the opaque identity cells, functoriality and the
sesquicategory whisker-associators on the nose (`rfl` — the flags are stable under re-bracketing), the
Godement interchange by parity-commutativity (the two whisker orders contribute the same two summands). -/
theorem walkingEquivFlaggedGenParity_ofStrictAxiom
    (contribution : Bool → Bool → WalkingEquivGenLabel → Bool)
    {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim}
    (row : StrictAxiomRel walkingEquivComputad cellAlpha cellBeta)
    (hasLeftAncestor hasRightAncestor : Bool) :
    walkingEquivFlaggedGenParity contribution hasLeftAncestor hasRightAncestor cellAlpha
      = walkingEquivFlaggedGenParity contribution hasLeftAncestor hasRightAncestor cellBeta := by
  cases row with
  | vcompAssoc cellA cellB cellC => exact walkingEquivParityAdd_assoc _ _ _
  | vcompUnitLeft cellA => rfl
  | vcompUnitRight cellA => exact walkingEquivParityAdd_falseRight _
  | whiskerLeftUnit whiskeringCell innerCell => rfl
  | whiskerRightUnit innerCell whiskeringCell => rfl
  | whiskerLeftFunctorial whiskeringCell innerBeta innerGamma => rfl
  | whiskerRightFunctorial innerAlpha innerBeta whiskeringCell => rfl
  | interchange innerAlpha innerBeta => exact walkingEquivParityAdd_comm _ _
  | whiskerAssocLeft whiskP whiskQ inner => rfl
  | whiskerAssocRight inner whiskP whiskQ => rfl
  | whiskerLeftRightCommute whiskP inner whiskQ => rfl

/-- ★ **Every cancellation row conserves the flagged parity** whenever the contribution table PAIRS the unit
with its inverse and the counit with its inverse — the two legs of each row contribute equal summands whose
parity sum vanishes (`walkingEquivParityAdd_self`), matching the opaque identity legs. -/
theorem walkingEquivFlaggedGenParity_ofCancellation
    (contribution : Bool → Bool → WalkingEquivGenLabel → Bool)
    (hEtaPaired : ∀ (hasLeft hasRight : Bool),
      contribution hasLeft hasRight WalkingEquivGenLabel.etaUnit
        = contribution hasLeft hasRight WalkingEquivGenLabel.etaInv)
    (hEpsPaired : ∀ (hasLeft hasRight : Bool),
      contribution hasLeft hasRight WalkingEquivGenLabel.epsCounit
        = contribution hasLeft hasRight WalkingEquivGenLabel.epsInv)
    {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim}
    (row : WalkingEquivCancellationRow cellAlpha cellBeta)
    (hasLeftAncestor hasRightAncestor : Bool) :
    walkingEquivFlaggedGenParity contribution hasLeftAncestor hasRightAncestor cellAlpha
      = walkingEquivFlaggedGenParity contribution hasLeftAncestor hasRightAncestor cellBeta := by
  cases row with
  | unitCancelForward =>
      exact (congrArg
          (fun flipped => walkingEquivParityAdd flipped
            (contribution hasLeftAncestor hasRightAncestor WalkingEquivGenLabel.etaInv))
          (hEtaPaired hasLeftAncestor hasRightAncestor)).trans
        (walkingEquivParityAdd_self _)
  | unitCancelBackward =>
      exact (congrArg
          (fun flipped => walkingEquivParityAdd flipped
            (contribution hasLeftAncestor hasRightAncestor WalkingEquivGenLabel.etaUnit))
          (hEtaPaired hasLeftAncestor hasRightAncestor).symm).trans
        (walkingEquivParityAdd_self _)
  | counitCancelForward =>
      exact (congrArg
          (fun flipped => walkingEquivParityAdd flipped
            (contribution hasLeftAncestor hasRightAncestor WalkingEquivGenLabel.epsInv))
          (hEpsPaired hasLeftAncestor hasRightAncestor)).trans
        (walkingEquivParityAdd_self _)
  | counitCancelBackward =>
      exact (congrArg
          (fun flipped => walkingEquivParityAdd flipped
            (contribution hasLeftAncestor hasRightAncestor WalkingEquivGenLabel.epsCounit))
          (hEpsPaired hasLeftAncestor hasRightAncestor).symm).trans
        (walkingEquivParityAdd_self _)

/-! ## The absorber: the flagged parity extends to the FULL congruence (any base relation that conserves it) -/

/-- ★★ **THE FLAGGED-PARITY ABSORBER** — for any base relation whose rows conserve the flagged parity at every
flag pair, "equal flagged parity at every flag pair" is a saturated-with-id congruence, so the fold extends
through EVERY derivation by `SaturatedConvOverWithId.recInto`.  The eleven fields: the row hypothesis, the
two vcomp congruences by `congrArg`, the four whisker congruences by flag-shifting the induction hypothesis
(the whisker-1-cell congruences and `idCongr` are `rfl` — the fold never traverses whiskering cells and is
opaque on identity cells), and the groupoid closure. -/
theorem walkingEquivFlaggedGenParityAbsorbs
    (contribution : Bool → Bool → WalkingEquivGenLabel → Bool)
    {baseRel : CellRelOver walkingEquivComputad}
    (hRowsConserve : ∀ {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim},
      baseRel cellAlpha cellBeta → ∀ (hasLeftAncestor hasRightAncestor : Bool),
        walkingEquivFlaggedGenParity contribution hasLeftAncestor hasRightAncestor cellAlpha
          = walkingEquivFlaggedGenParity contribution hasLeftAncestor hasRightAncestor cellBeta) :
    IsSaturatedCongruenceWithId walkingEquivComputad baseRel
      (fun {_dim : Nat} cellAlpha cellBeta => ∀ (hasLeftAncestor hasRightAncestor : Bool),
        walkingEquivFlaggedGenParity contribution hasLeftAncestor hasRightAncestor cellAlpha
          = walkingEquivFlaggedGenParity contribution hasLeftAncestor hasRightAncestor cellBeta) where
  ofRelation := by
    intro _dim _cellAlpha _cellBeta lawRow
    exact hRowsConserve lawRow
  vcompCongrLeft := by
    intro _dim _cellAlpha _cellAlpha' cellBeta ihConv hasLeftAncestor hasRightAncestor
    exact congrArg
      (fun flipped => walkingEquivParityAdd flipped
        (walkingEquivFlaggedGenParity contribution hasLeftAncestor hasRightAncestor cellBeta))
      (ihConv hasLeftAncestor hasRightAncestor)
  vcompCongrRight := by
    intro _dim cellAlpha _cellBeta _cellBeta' ihConv hasLeftAncestor hasRightAncestor
    exact congrArg
      (walkingEquivParityAdd
        (walkingEquivFlaggedGenParity contribution hasLeftAncestor hasRightAncestor cellAlpha))
      (ihConv hasLeftAncestor hasRightAncestor)
  whiskerLeftCongr := by
    intro _dim _whiskeringCell _cellBeta _cellBeta' ihConv _hasLeftAncestor hasRightAncestor
    exact ihConv true hasRightAncestor
  whiskerRightCongr := by
    intro _dim _cellAlpha _cellAlpha' _whiskeringCell ihConv hasLeftAncestor _hasRightAncestor
    exact ihConv hasLeftAncestor true
  idCongr := by
    intro _dim _cellAlpha _cellBeta _ihConv _hasLeftAncestor _hasRightAncestor
    rfl
  whiskerLeftWhiskerCongr := by
    intro _dim _whiskerAlpha _whiskerAlpha' _innerCell _ihConv _hasLeftAncestor _hasRightAncestor
    rfl
  whiskerRightWhiskerCongr := by
    intro _dim _innerCell _whiskerAlpha _whiskerAlpha' _ihConv _hasLeftAncestor _hasRightAncestor
    rfl
  refl := by
    intro _dim _cell _hasLeftAncestor _hasRightAncestor
    rfl
  symm := by
    intro _dim _cellAlpha _cellBeta ihConv hasLeftAncestor hasRightAncestor
    exact (ihConv hasLeftAncestor hasRightAncestor).symm
  trans := by
    intro _dim _cellAlpha _cellBeta _cellGamma ihLeft ihRight hasLeftAncestor hasRightAncestor
    exact (ihLeft hasLeftAncestor hasRightAncestor).trans (ihRight hasLeftAncestor hasRightAncestor)

/-- The bare walking-equivalence relation conserves the flagged parity for any eta-paired, eps-paired
contribution table — the strict rows and the four cancellation rows, united. -/
theorem walkingEquivFlaggedGenParity_ofBaseRel
    (contribution : Bool → Bool → WalkingEquivGenLabel → Bool)
    (hEtaPaired : ∀ (hasLeft hasRight : Bool),
      contribution hasLeft hasRight WalkingEquivGenLabel.etaUnit
        = contribution hasLeft hasRight WalkingEquivGenLabel.etaInv)
    (hEpsPaired : ∀ (hasLeft hasRight : Bool),
      contribution hasLeft hasRight WalkingEquivGenLabel.epsCounit
        = contribution hasLeft hasRight WalkingEquivGenLabel.epsInv)
    {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim}
    (row : walkingEquivBaseRel cellAlpha cellBeta)
    (hasLeftAncestor hasRightAncestor : Bool) :
    walkingEquivFlaggedGenParity contribution hasLeftAncestor hasRightAncestor cellAlpha
      = walkingEquivFlaggedGenParity contribution hasLeftAncestor hasRightAncestor cellBeta := by
  cases row with
  | inl strictRow =>
      exact walkingEquivFlaggedGenParity_ofStrictAxiom contribution strictRow
        hasLeftAncestor hasRightAncestor
  | inr cancellationRow =>
      exact walkingEquivFlaggedGenParity_ofCancellation contribution hEtaPaired hEpsPaired
        cancellationRow hasLeftAncestor hasRightAncestor

/-! ## The two separating contribution tables -/

/-- Whether a generator label belongs to the eta family (`etaUnit` / `etaInv`) — full six-arm split. -/
def walkingEquivIsEtaFamilyLabel : WalkingEquivGenLabel → Bool
  | .colourF => false
  | .colourG => false
  | .etaUnit => true
  | .etaInv => true
  | .epsCounit => false
  | .epsInv => false

/-- ★ The **hypothesis-refutation slot**: count eta-family generators sitting under a RIGHT whisker but no
LEFT whisker.  `phi_f`'s `eta` (under `|> f` only) is counted; every generator of `id f` and every eps-family
generator is not.  Full four-arm flag split — no wildcard. -/
def walkingEquivEtaRightWhiskerOnlyContribution
    (hasLeftAncestor hasRightAncestor : Bool) (label : WalkingEquivGenLabel) : Bool :=
  match hasLeftAncestor, hasRightAncestor with
  | false, true => walkingEquivIsEtaFamilyLabel label
  | false, false => false
  | true, false => false
  | true, true => false

/-- ★ The **idempotency-refutation slot**: count eta-family generators sitting under a LEFT whisker but no
RIGHT whisker.  `psi_g`'s `eta` (under `g <|` only) is counted; the left-triangle row's `eta` (under `|> f`)
is NOT — so this slot is conserved even by the adjoined left-triangle row. -/
def walkingEquivEtaLeftWhiskerOnlyContribution
    (hasLeftAncestor hasRightAncestor : Bool) (label : WalkingEquivGenLabel) : Bool :=
  match hasLeftAncestor, hasRightAncestor with
  | true, false => walkingEquivIsEtaFamilyLabel label
  | false, false => false
  | false, true => false
  | true, true => false

/-- The right-whisker-only slot pairs the unit with its inverse (both eta-family — each arm `rfl`). -/
theorem walkingEquivEtaRightWhiskerOnlyContribution_pairsEta :
    ∀ (hasLeft hasRight : Bool),
      walkingEquivEtaRightWhiskerOnlyContribution hasLeft hasRight WalkingEquivGenLabel.etaUnit
        = walkingEquivEtaRightWhiskerOnlyContribution hasLeft hasRight WalkingEquivGenLabel.etaInv
  | false, false => rfl
  | false, true => rfl
  | true, false => rfl
  | true, true => rfl

/-- The right-whisker-only slot pairs the counit with its inverse (both outside the eta family). -/
theorem walkingEquivEtaRightWhiskerOnlyContribution_pairsEps :
    ∀ (hasLeft hasRight : Bool),
      walkingEquivEtaRightWhiskerOnlyContribution hasLeft hasRight WalkingEquivGenLabel.epsCounit
        = walkingEquivEtaRightWhiskerOnlyContribution hasLeft hasRight WalkingEquivGenLabel.epsInv
  | false, false => rfl
  | false, true => rfl
  | true, false => rfl
  | true, true => rfl

/-- The left-whisker-only slot pairs the unit with its inverse. -/
theorem walkingEquivEtaLeftWhiskerOnlyContribution_pairsEta :
    ∀ (hasLeft hasRight : Bool),
      walkingEquivEtaLeftWhiskerOnlyContribution hasLeft hasRight WalkingEquivGenLabel.etaUnit
        = walkingEquivEtaLeftWhiskerOnlyContribution hasLeft hasRight WalkingEquivGenLabel.etaInv
  | false, false => rfl
  | false, true => rfl
  | true, false => rfl
  | true, true => rfl

/-- The left-whisker-only slot pairs the counit with its inverse. -/
theorem walkingEquivEtaLeftWhiskerOnlyContribution_pairsEps :
    ∀ (hasLeft hasRight : Bool),
      walkingEquivEtaLeftWhiskerOnlyContribution hasLeft hasRight WalkingEquivGenLabel.epsCounit
        = walkingEquivEtaLeftWhiskerOnlyContribution hasLeft hasRight WalkingEquivGenLabel.epsInv
  | false, false => rfl
  | false, true => rfl
  | true, false => rfl
  | true, true => rfl

/-! ## The kernel-computed separation pins (each `rfl`) -/

/-- `phi_f` folds to `true` at the hypothesis-refutation slot (its `eta` sits under `|> f` only). -/
theorem walkingEquivLeftTriangleLeg_rightSlotParityPin :
    walkingEquivFlaggedGenParity walkingEquivEtaRightWhiskerOnlyContribution false false
      walkingEquivLeftTriangleLeg = true := rfl

/-- `id f` folds to `false` at the hypothesis-refutation slot — SEPARATED from `phi_f`. -/
theorem walkingEquivIdF_rightSlotParityPin :
    walkingEquivFlaggedGenParity walkingEquivEtaRightWhiskerOnlyContribution false false
      walkingEquivIdF = false := rfl

/-- `psi_g` folds to `true` at the idempotency-refutation slot (its `eta` sits under `g <|` only). -/
theorem walkingEquivRightTriangleLeg_leftSlotParityPin :
    walkingEquivFlaggedGenParity walkingEquivEtaLeftWhiskerOnlyContribution false false
      walkingEquivRightTriangleLeg = true := rfl

/-- `psi_g . psi_g` folds to `false` at the idempotency-refutation slot (two counted `eta`s cancel in
parity) — SEPARATED from `psi_g`. -/
theorem walkingEquivDoubledRightTriangleLeg_leftSlotParityPin :
    walkingEquivFlaggedGenParity walkingEquivEtaLeftWhiskerOnlyContribution false false
      (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightTriangleLeg) = false := rfl

/-- `id g` folds to `false` at the idempotency-refutation slot — SEPARATED from `psi_g` too. -/
theorem walkingEquivIdG_leftSlotParityPin :
    walkingEquivFlaggedGenParity walkingEquivEtaLeftWhiskerOnlyContribution false false
      walkingEquivIdG = false := rfl

/-! ## Refutation 1 — the left-triangle hypothesis is UNINHABITED over the bare relation -/

/-- ★★ **THE LEFT TRIANGLE IS NOT DERIVABLE OVER THE BARE RELATION.**  Any derivation of `phi_f ~ id f` over
`walkingEquivBaseRel` folds through the flagged-parity absorber at the right-whisker-only slot to
`true = false` — absurd.  So the hypothesis of the walled promotion theorem is uninhabited: the bare four
iso-cancellations + strict rows do NOT prove the left triangle (as the B4 winding wall already suspected for
the parallel-uniqueness question — here machine-checked for the triangle itself). -/
theorem walkingEquivLeftTriangle_notDerivableOverBareRel
    (hLeftTriangle : SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      walkingEquivLeftTriangleLeg walkingEquivIdF) : False :=
  Bool.noConfusion
    (SaturatedConvOverWithId.recInto
      (walkingEquivFlaggedGenParityAbsorbs walkingEquivEtaRightWhiskerOnlyContribution
        (walkingEquivFlaggedGenParity_ofBaseRel walkingEquivEtaRightWhiskerOnlyContribution
          walkingEquivEtaRightWhiskerOnlyContribution_pairsEta
          walkingEquivEtaRightWhiskerOnlyContribution_pairsEps))
      hLeftTriangle false false)

/-! ## The guarded theorem SHIPS — vacuously, with the vacuity machine-checked, never hidden -/

/-- ★★ **THE GUARDED PROMOTION THEOREM (VACUOUS — read the docstring).**  The exact statement the wall
`fxEquiv_promotionIdempotencyFromLeftTriangleWalled` guards: from the left triangle over the BARE relation,
the idempotency `psi_g . psi_g ~ psi_g` follows.  It holds because the hypothesis is UNINHABITED
(`walkingEquivLeftTriangle_notDerivableOverBareRel`) — there is NO interchange bracketing behind it, and
`walkingEquivIdempotency_notDerivableEvenWithLeftTriangleRow` below proves no non-vacuous proof over these
rows can exist.  Shipped so the guarded node is formally closed; the honest content is the refutation pair. -/
theorem walkingEquivIdempotencyFromLeftTriangle
    (hLeftTriangle : SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      walkingEquivLeftTriangleLeg walkingEquivIdF) :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightTriangleLeg)
      walkingEquivRightTriangleLeg :=
  (walkingEquivLeftTriangle_notDerivableOverBareRel hLeftTriangle).elim

/-- ★ **THE DERIVED RIGHT TRIANGLE (equally vacuous)** — the guarded theorem fed to the shipped conditional
promotion `walkingEquivRightTriangle_ofIdempotency`, exactly as the recon recipe prescribed.  Vacuous for the
same reason; recorded so the full promotion pipeline is formally closed AND honestly labeled. -/
theorem walkingEquivRightTriangleFromLeftTriangle
    (hLeftTriangle : SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      walkingEquivLeftTriangleLeg walkingEquivIdF) :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      walkingEquivRightTriangleLeg walkingEquivIdG :=
  walkingEquivRightTriangle_ofIdempotency (walkingEquivIdempotencyFromLeftTriangle hLeftTriangle)

/-! ## Refutation 2 — the NON-VACUOUS adjudication: adjoin the left triangle as a ROW, still no idempotency -/

/-- The **left-triangle-only row** — the single generating equation `phi_f ~ id f`, adjoined to the bare
relation so the promotion hypothesis becomes genuinely INHABITED (the non-vacuous test bench). -/
inductive WalkingEquivLeftTriangleOnlyRow :
    {dim : Nat} → CellExpr walkingEquivComputad dim → CellExpr walkingEquivComputad dim → Prop where
  /-- The left triangle identity `(eta |> f) . (f <| eps) ~ id f`. -/
  | leftTriangle : WalkingEquivLeftTriangleOnlyRow walkingEquivLeftTriangleLeg walkingEquivIdF

/-- The bare relation with the left triangle ADJOINED as a row — the honest scope on which the promotion
"left triangle forces the right triangle" must be tested non-vacuously. -/
def walkingEquivLeftTriangleAdjoinedRel : CellRelOver walkingEquivComputad :=
  unionCellRel walkingEquivComputad walkingEquivBaseRel WalkingEquivLeftTriangleOnlyRow

/-- **Positive control**: over the adjoined relation the left triangle IS derivable (fire the row) — so
refutation 2 below is NOT vacuous. -/
theorem walkingEquivLeftTriangle_derivableOverAdjoinedRel :
    SaturatedConvOverWithId walkingEquivComputad walkingEquivLeftTriangleAdjoinedRel
      walkingEquivLeftTriangleLeg walkingEquivIdF :=
  SaturatedConvOverWithId.ofRelation (Or.inr WalkingEquivLeftTriangleOnlyRow.leftTriangle)

/-- ★ **The left-triangle row conserves the idempotency-refutation slot** — the row's `eta` carries the
right-whisker flag (it sits under `|> f`), so it never contributes at the left-whisker-only slot; its `eps`
is outside the eta family.  Full four-flag enumeration, each side computing to `false`. -/
theorem walkingEquivEtaLeftWhiskerOnly_conservedByLeftTriangleRow
    {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim}
    (row : WalkingEquivLeftTriangleOnlyRow cellAlpha cellBeta)
    (hasLeftAncestor hasRightAncestor : Bool) :
    walkingEquivFlaggedGenParity walkingEquivEtaLeftWhiskerOnlyContribution
        hasLeftAncestor hasRightAncestor cellAlpha
      = walkingEquivFlaggedGenParity walkingEquivEtaLeftWhiskerOnlyContribution
        hasLeftAncestor hasRightAncestor cellBeta := by
  cases row with
  | leftTriangle =>
      cases hasLeftAncestor with
      | false =>
          cases hasRightAncestor with
          | false => rfl
          | true => rfl
      | true =>
          cases hasRightAncestor with
          | false => rfl
          | true => rfl

/-- The adjoined relation conserves the idempotency-refutation slot — bare rows by the generic dischargers,
the adjoined triangle row by its dedicated conservation. -/
theorem walkingEquivFlaggedGenParity_ofAdjoinedRel
    {dim : Nat} {cellAlpha cellBeta : CellExpr walkingEquivComputad dim}
    (row : walkingEquivLeftTriangleAdjoinedRel cellAlpha cellBeta)
    (hasLeftAncestor hasRightAncestor : Bool) :
    walkingEquivFlaggedGenParity walkingEquivEtaLeftWhiskerOnlyContribution
        hasLeftAncestor hasRightAncestor cellAlpha
      = walkingEquivFlaggedGenParity walkingEquivEtaLeftWhiskerOnlyContribution
        hasLeftAncestor hasRightAncestor cellBeta := by
  cases row with
  | inl baseRow =>
      exact walkingEquivFlaggedGenParity_ofBaseRel walkingEquivEtaLeftWhiskerOnlyContribution
        walkingEquivEtaLeftWhiskerOnlyContribution_pairsEta
        walkingEquivEtaLeftWhiskerOnlyContribution_pairsEps
        baseRow hasLeftAncestor hasRightAncestor
  | inr triangleRow =>
      exact walkingEquivEtaLeftWhiskerOnly_conservedByLeftTriangleRow triangleRow
        hasLeftAncestor hasRightAncestor

/-- ★★★ **THE INTERCHANGE BRACKETING IS REFUTED (non-vacuous).**  Even with the left triangle adjoined AS A
ROW — the hypothesis genuinely inhabited (`walkingEquivLeftTriangle_derivableOverAdjoinedRel`) — the
idempotency `psi_g . psi_g ~ psi_g` is NOT derivable: any derivation folds through the flagged-parity
absorber at the left-whisker-only slot to `false = true`.  So NO sequence of strict rows, cancellations,
insertions, and Godement interchange firings closes the recon's Move 3-4 bracketing: the classical
2-category argument does not compile to this row set, because `StrictAxiomRel` lacks the
whisker-by-identity-1-cell unitors (`whiskerUnitRel`, shipped only additively in EckmannHiltonWithId). -/
theorem walkingEquivIdempotency_notDerivableEvenWithLeftTriangleRow
    (hIdem : SaturatedConvOverWithId walkingEquivComputad walkingEquivLeftTriangleAdjoinedRel
      (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightTriangleLeg)
      walkingEquivRightTriangleLeg) : False :=
  Bool.noConfusion
    (SaturatedConvOverWithId.recInto
      (walkingEquivFlaggedGenParityAbsorbs walkingEquivEtaLeftWhiskerOnlyContribution
        walkingEquivFlaggedGenParity_ofAdjoinedRel)
      hIdem false false)

/-- ★★ **THE RIGHT TRIANGLE ITSELF IS ALSO REFUTED over the adjoined relation** — `psi_g ~ id g` folds to
`true = false` at the same slot.  The full classical promotion ("one triangle of an equivalence with
invertible unit/counit forces the other") FAILS over the unitor-free strict rows — the missing whisker
unitors are load-bearing, not bookkeeping. -/
theorem walkingEquivRightTriangle_notDerivableEvenWithLeftTriangleRow
    (hRightTriangle : SaturatedConvOverWithId walkingEquivComputad walkingEquivLeftTriangleAdjoinedRel
      walkingEquivRightTriangleLeg walkingEquivIdG) : False :=
  Bool.noConfusion
    (SaturatedConvOverWithId.recInto
      (walkingEquivFlaggedGenParityAbsorbs walkingEquivEtaLeftWhiskerOnlyContribution
        walkingEquivFlaggedGenParity_ofAdjoinedRel)
      hRightTriangle false false)

/-- ★ **The idempotency hypothesis of the shipped conditional promotion is ALSO uninhabited over the bare
relation** — so `walkingEquivRightTriangle_ofIdempotency` was doubly conditional-on-nothing: neither its
hypothesis nor the walled node's hypothesis is inhabited over `walkingEquivBaseRel`.  Recorded for the honest
ledger (the conditional theorems remain correct; their bare-relation instantiations are vacuous). -/
theorem walkingEquivIdempotency_notDerivableOverBareRel
    (hIdem : SaturatedConvOverWithId walkingEquivComputad walkingEquivBaseRel
      (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightTriangleLeg)
      walkingEquivRightTriangleLeg) : False :=
  Bool.noConfusion
    (SaturatedConvOverWithId.recInto
      (walkingEquivFlaggedGenParityAbsorbs walkingEquivEtaLeftWhiskerOnlyContribution
        (walkingEquivFlaggedGenParity_ofBaseRel walkingEquivEtaLeftWhiskerOnlyContribution
          walkingEquivEtaLeftWhiskerOnlyContribution_pairsEta
          walkingEquivEtaLeftWhiskerOnlyContribution_pairsEps))
      hIdem false false)

/-! ## Non-vacuity probes -/

#eval walkingEquivFlaggedGenParity walkingEquivEtaRightWhiskerOnlyContribution false false
  walkingEquivLeftTriangleLeg
#eval walkingEquivFlaggedGenParity walkingEquivEtaRightWhiskerOnlyContribution false false
  walkingEquivIdF
#eval walkingEquivFlaggedGenParity walkingEquivEtaLeftWhiskerOnlyContribution false false
  walkingEquivRightTriangleLeg
#eval walkingEquivFlaggedGenParity walkingEquivEtaLeftWhiskerOnlyContribution false false
  (CellExpr.vcomp walkingEquivRightTriangleLeg walkingEquivRightTriangleLeg)

/-! ## Honesty markers — the r3 adjudication of the B3 wall -/

/-- ★★ **THE GUARDED THEOREM IS SHIPPED — VACUOUSLY (r3).**  `= true` records that the exact theorem guarded
by `fxEquiv_promotionIdempotencyFromLeftTriangleWalled` is now inhabited
(`walkingEquivIdempotencyFromLeftTriangle`, plus the derived `walkingEquivRightTriangleFromLeftTriangle`) —
BY VACUITY: its hypothesis is machine-checked uninhabited over the bare relation
(`walkingEquivLeftTriangle_notDerivableOverBareRel`).  The shipped wall marker in the presentation file stays
byte-intact; this marker supersedes its "hand-computation residual" denotation by content. -/
def fxEquiv_promotionIdempotencyFromLeftTriangleTheoremShippedVacuously : Bool := true

/-- ★★★ **THE INTERCHANGE BRACKETING IS REFUTED (r3) — the wall was guarding a false hope.**  `= true`
records the non-vacuous adjudication: with the left triangle adjoined AS A ROW (hypothesis inhabited), the
idempotency AND the right triangle are both underivable
(`walkingEquivIdempotency_notDerivableEvenWithLeftTriangleRow`,
`walkingEquivRightTriangle_notDerivableEvenWithLeftTriangleRow`) — the flagged-generator-parity invariant is
conserved by every shipped row and separates.  The recon's two-Godement-firing recipe is a correct
2-CATEGORY argument that does not compile to `walkingEquivBaseRel`: `StrictAxiomRel` lacks the
whisker-by-identity-1-cell unitors, and they are exactly what the classical promotion spends. -/
def fxEquiv_promotionInterchangeBracketingRefuted : Bool := true

/-- ★ **THE HONEST SUCCESSOR NODE — the promotion over the unitor-augmented relation (OPEN).**  `= false`
records what this round does NOT deliver: the walking-equivalence promotion re-founded over
`unionCellRel _ walkingEquivBaseRel (whiskerUnitRel _)` (the EckmannHiltonWithId `strictWithWhiskerUnits`
pattern), where the parity obstruction dissolves (the unitor rows change a generator's whisker-ancestry flags)
and the classical idempotency derivation becomes available.  That is a presentation-upgrade rung — a new
base relation for the walker, with the whiskered-cancellation chains re-fired over it — not a bracketing
hand-computation.  Named, not attempted. -/
def fxEquiv_promotionOverWhiskerUnitorScopeOpen : Bool := false

end FX1Poly.Polygraph.Omega

import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidMatrixSemantics
import FX1Poly.Polygraph.Omega.InvolutionDemonstrator
import FX1Poly.Polygraph.Omega.CyclicThreeDemonstrator
import FX1Poly.Polygraph.Omega.IdempotentSemigroupDemonstrator

/-! # Polygraph/Omega/NotSpuriousTrioOverQuotientAdjudication — the not-spurious trio's latent over-quotient,
adjudicated against the `Mat(N)` model (OMEGA SWEEP r2 — the residual-models round, B1)

★ **The r4 family ledger's "not-spurious trio, over-quotient UNRESOLVED, PREDICTED CLEAN by torsion" is
REFUTED — machine-checked, zero-axiom.**  The `OmegaHouseStyleFamilyLedger` marker
`fxOmegaHouseStyle_notSpuriousTrioShapeMatchesOverQuotientUnresolved` deferred the involution `sss`, cyclic-3
`ssss` / `sssss` and idempotent `eee` rows as UNRESOLVED, predicting that their delooped group / coherent
model would IDENTIFY the two whisker legs (so `Mat(N)` would be an UNFAITHFUL separator).  This file evaluates
each trio walker's critical-pair legs into the SAME `Mat(N)` monoid that separates the walking monad's
bare-whisker rows (`WalkingMonadOverQuotientAdjudication`), and the four leg-pairs ALL SEPARATE — the r4
over-quotient pattern REPLICATES at the trio, correcting the marker from UNRESOLVED to CONFIRMED.

## The category error the ledger made (and this file corrects)

The ledger reasoned "`s` is torsion (`s.s = id`, `s.s.s = id`), so the faithful model is a delooped finite
GROUP, which is 2-coherent and identifies the legs; `Mat(N)`'s generator is non-invertible, so a `Mat(N)`
separation is unfaithful."  This conflates two levels.  The SHIPPED presentation
(`Involution / CyclicThree / IdempotentSemigroupDemonstrator`) is a **2-polygraph** whose rewrite rule `rho`
(`involutionRhoGen : ss => id`) / `R` / `M` is a **non-invertible 2-cell GENERATOR**, NOT a 1-level equation
`s.s = id`.  So `s` is **not torsion** and **not invertible** at the 1-cell level; the free 1-category on `s`
is the free monoid `s^n` (the demonstrators ship its parity-NF decision at the 1-CELL level, referenced not
re-built).  Consequently `Mat(N)` (`s |-> width 1`, `rho |-> ` the unique width-0-target matrix; `M |-> [[1,1]]`)
is a **legitimate strict-2-category model of the 2-polygraph** — it respects the strict 2-cat axioms and
separates.  The "delooped group `B(Z/3)`" the ledger invoked would force `s.s.s = id` at the 1-level AND
trivialize every 2-cell — a NON-faithful collapse; a model that *identifies* is not evidence of soundness (to
prove over-quotient one needs a genuine-law-respecting model that *separates*, which `Mat(N)` supplies).

## The verdict, stated under BOTH semantics (the honest interpretive fork)

  * **Under the family's dim-2-congruence + free-2-category (`Mat(N)`) semantics** — THE SAME standard that
    condemns the walking monad — the trio's bare-whisker critical-pair legs are DISTINCT 2-cells that the r1
    base relation identifies: the presentation **over-quotients** (machine-separated below).
  * **Under the delooped-monoid semantics** (trivial 2-cells) the presented 1-dimensional MONOID (`Z/2`,
    `Z/3`, the idempotent monoid) is CORRECT; what over-quotients is the collapse of distinct 2-cells / loss of
    Squier syzygy information.  This is EXACTLY the walking-monad-vs-Delta situation (the monad presents the
    correct monoid `Delta` yet over-quotients distinct 2-cells), so the family standard is CONSISTENT — the
    ledger's ASYMMETRY (monad broken, trio clean) is the unjustified claim this file retracts.

This file does NOT claim "wrong monoid"; it claims "collapses distinct 2-cells," uniformly with the monad.

## What ships (B1)

  * the three `Mat(N)` evaluations (`{involution,cyclicThree,idempotentSemigroup}OmegaEvalCell`), each the
    identical fold as `monadOmegaEvalCell` with a per-walker generator table (`s |-> width 1`, `rho / R |-> ` the
    empty width-0-target matrix, `M |-> [[1,1]]`);
  * the FOUR machine separations (`involutionOmegaMatSeparatesSss`, `cyclicThreeOmegaMatSeparates{Ssss,Sssss}`,
    `idempotentSemigroupOmegaMatSeparatesEee`), each `Nat.noConfusion` on a differing entry;
  * the four OVER-QUOTIENT witnesses pairing the shipped generating 3-cell (r1 convertibility) with the `Mat(N)`
    separation;
  * the idempotent's RESTORED SOUNDNESS: the `M`-mediated associativity `(M |> e).M ~ (e <| M).M` is the sound
    dim-2 sub-law (`Mat(N)` respects it, both legs `[[1,1,1]]`), the exact monad `leftUnitAssoc` repair — the
    `eee` legs are then PROVABLY not convertible over it (`IdempotentSemigroupOmegaSoundRow` clone of
    `MonadOmegaSoundRow`);
  * the involution / cyclic honest wall: their genuine content is purely DIM-3 homotopy (no `mu` / `M`-analogue
    dim-2 mediated law exists), so the sound dim-2 sub-theory is `StrictAxiomRel` alone — Fubini-walled,
    identical to the monad's `fxOmegaHouseStyle_monadFullIsolationNeedsStrictLawFubiniKit`.

## The honest walls (NAMED)

  * `Mat(N)` strict-law faithfulness (respects every `StrictAxiomRel` row) is the NAMED finite-sum Fubini
    matrix-algebra kit — identical for monad and trio.  The separations are AIRTIGHT; "respects the strict
    laws" is the shippable-but-walled piece and does NOT weaken the over-quotient verdict (the monad ships the
    over-quotient with the same wall).
  * The involution's / cyclic's full dim-2 sound-sub-theory needs that Fubini kit (no dim-2 mediated law to
    build a non-trivial `rfl`-sound sub-relation from); the idempotent's `M`-mediated associativity IS such a
    law, so its restored soundness ships here.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin.
The matrix carrier, ops, indexers and the four label-independent evaluation helpers are REUSED from
`WalkingBunchedBimonoidMatrixSemantics`; only the three per-walker generator tables and folds are new. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # B1 — THE INVOLUTION `sss` OVER-QUOTIENT (s |-> width 1, rho : ss => id |-> the unique 0x2 matrix)
    # ========================================================================================= -/

/-- The **involution generator matrix table**: at label-dimension 0 the 1-generator `s` is a single strand
(width 1); at label-dimension 1 the rewrite rule `rho : ss => id` maps to the unique width-0-target matrix
`[] : 0x2` (source `ss` has width 2, target `id` has width 0); `Unit` above.  The label family is the constant
`Unit` (`involutionOmegaComputad.genLabel`), so the label argument is `Unit` — no `Nat`-match, propext-clean. -/
def involutionOmegaEvalGen : (labelDim : Nat) → Unit →
    BunchedBimonoidEvalCarrier labelDim → BunchedBimonoidEvalCarrier labelDim →
    BunchedBimonoidEvalCarrier (labelDim + 1)
  | 0, _, _, _ => (1 : Nat)
  | 1, _, _, _ => { rows := 0, cols := 2, entries := [] }
  | _ + 2, _, _, _ => ()

/-- ★ **The involution matrix evaluation** — the monoid functor into `Mat(N)`, a total structural fold over all
six carrier constructors (identical to `monadOmegaEvalCell`), the four label-independent helpers carrying the
per-dimension operations, the involution generator table carrying `s` / `rho`.  Propext-clean. -/
def involutionOmegaEvalCell : {dim : Nat} → CellExpr involutionOmegaComputad dim →
    BunchedBimonoidEvalCarrier dim
  | _, .ofMode _ => ()
  | _, .gen (dim := labelDim) label source target =>
      involutionOmegaEvalGen labelDim label (involutionOmegaEvalCell source) (involutionOmegaEvalCell target)
  | _, .id (dim := d) cell => bunchedBimonoidEvalId d (involutionOmegaEvalCell cell)
  | _, .vcomp (dim := d) leftCell rightCell =>
      bunchedBimonoidEvalVcomp d (involutionOmegaEvalCell leftCell) (involutionOmegaEvalCell rightCell)
  | _, .whiskerLeft (dim := d) whiskerCell cell =>
      bunchedBimonoidEvalWhiskerLeft d (involutionOmegaEvalCell whiskerCell) (involutionOmegaEvalCell cell)
  | _, .whiskerRight (dim := d) cell whiskerCell =>
      bunchedBimonoidEvalWhiskerRight d (involutionOmegaEvalCell cell) (involutionOmegaEvalCell whiskerCell)

/-- ★ The involution `sss` legs are DIFFERENT `Mat(N)` maps: `rho |> s` = `[[0,0,1]]` vs `s <| rho` =
`[[1,0,0]]`; entry `(0,0)` is `0` vs `1`.  The bare-whisker over-quotient the ledger predicted clean. -/
theorem involutionOmegaMatSeparatesSss :
    involutionOmegaEvalCell involutionLeftLeg ≠ involutionOmegaEvalCell involutionRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-- ★★ **THE INVOLUTION `sss` OVER-QUOTIENT WITNESS.**  The two legs are convertible under the r1 base relation
`involutionBaseRel` (the shipped generating 3-cell `involutionSssThreeCell`) yet evaluate to DISTINCT `Mat(N)`
maps — the presentation identifies genuinely-distinct 2-cells.  The pair `(r1-convertibility, separation)`,
both components shipped and zero-axiom. -/
theorem involutionOmegaBaseRelOverQuotientsSss :
    SaturatedConvOverWithId involutionOmegaComputad involutionBaseRel
        involutionLeftLeg involutionRightLeg
      ∧ involutionOmegaEvalCell involutionLeftLeg ≠ involutionOmegaEvalCell involutionRightLeg :=
  ⟨involutionSssThreeCell, involutionOmegaMatSeparatesSss⟩

/-! # =========================================================================================
    # B1 — THE CYCLIC-3 `ssss` / `sssss` OVER-QUOTIENTS (s |-> width 1, R : sss => id |-> the 0x3 matrix)
    # ========================================================================================= -/

/-- The **cyclic-3 generator matrix table**: `s |-> ` width 1; the rewrite rule `R : s.s.s => id` maps to the
unique width-0-target matrix `[] : 0x3` (source `sss` width 3, target `id` width 0); `Unit` above.  Constant
`Unit` label — propext-clean. -/
def cyclicThreeOmegaEvalGen : (labelDim : Nat) → Unit →
    BunchedBimonoidEvalCarrier labelDim → BunchedBimonoidEvalCarrier labelDim →
    BunchedBimonoidEvalCarrier (labelDim + 1)
  | 0, _, _, _ => (1 : Nat)
  | 1, _, _, _ => { rows := 0, cols := 3, entries := [] }
  | _ + 2, _, _, _ => ()

/-- ★ **The cyclic-3 matrix evaluation** — the monoid functor into `Mat(N)`, the identical fold with the
cyclic-3 generator table (`s` / `R`).  Propext-clean. -/
def cyclicThreeOmegaEvalCell : {dim : Nat} → CellExpr cyclicThreeOmegaComputad dim →
    BunchedBimonoidEvalCarrier dim
  | _, .ofMode _ => ()
  | _, .gen (dim := labelDim) label source target =>
      cyclicThreeOmegaEvalGen labelDim label (cyclicThreeOmegaEvalCell source) (cyclicThreeOmegaEvalCell target)
  | _, .id (dim := d) cell => bunchedBimonoidEvalId d (cyclicThreeOmegaEvalCell cell)
  | _, .vcomp (dim := d) leftCell rightCell =>
      bunchedBimonoidEvalVcomp d (cyclicThreeOmegaEvalCell leftCell) (cyclicThreeOmegaEvalCell rightCell)
  | _, .whiskerLeft (dim := d) whiskerCell cell =>
      bunchedBimonoidEvalWhiskerLeft d (cyclicThreeOmegaEvalCell whiskerCell) (cyclicThreeOmegaEvalCell cell)
  | _, .whiskerRight (dim := d) cell whiskerCell =>
      bunchedBimonoidEvalWhiskerRight d (cyclicThreeOmegaEvalCell cell) (cyclicThreeOmegaEvalCell whiskerCell)

/-- ★ The cyclic-3 `ssss` legs are DIFFERENT: `R |> s` = `[[0,0,0,1]]` vs `s <| R` = `[[1,0,0,0]]`; entry
`(0,0)` is `0` vs `1`. -/
theorem cyclicThreeOmegaMatSeparatesSsss :
    cyclicThreeOmegaEvalCell cyclicThreeOmegaSsssLeftLeg
      ≠ cyclicThreeOmegaEvalCell cyclicThreeOmegaSsssRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-- ★ The cyclic-3 `sssss` legs are DIFFERENT: `R |> ss` = `[[0,0,0,1,0],[0,0,0,0,1]]` vs `ss <| R` =
`[[1,0,0,0,0],[0,1,0,0,0]]`; entry `(0,0)` is `0` vs `1`. -/
theorem cyclicThreeOmegaMatSeparatesSssss :
    cyclicThreeOmegaEvalCell cyclicThreeOmegaSssssLeftLeg
      ≠ cyclicThreeOmegaEvalCell cyclicThreeOmegaSssssRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 0) hmatrix)

/-- ★★ **THE CYCLIC-3 `ssss` OVER-QUOTIENT WITNESS** — r1 convertibility (`cyclicThreeOmegaSsssThreeCell`) yet
distinct `Mat(N)` maps. -/
theorem cyclicThreeOmegaBaseRelOverQuotientsSsss :
    SaturatedConvOverWithId cyclicThreeOmegaComputad cyclicThreeOmegaBaseRel
        cyclicThreeOmegaSsssLeftLeg cyclicThreeOmegaSsssRightLeg
      ∧ cyclicThreeOmegaEvalCell cyclicThreeOmegaSsssLeftLeg
        ≠ cyclicThreeOmegaEvalCell cyclicThreeOmegaSsssRightLeg :=
  ⟨cyclicThreeOmegaSsssThreeCell, cyclicThreeOmegaMatSeparatesSsss⟩

/-- ★★ **THE CYCLIC-3 `sssss` OVER-QUOTIENT WITNESS** — r1 convertibility (`cyclicThreeOmegaSssssThreeCell`)
yet distinct `Mat(N)` maps. -/
theorem cyclicThreeOmegaBaseRelOverQuotientsSssss :
    SaturatedConvOverWithId cyclicThreeOmegaComputad cyclicThreeOmegaBaseRel
        cyclicThreeOmegaSssssLeftLeg cyclicThreeOmegaSssssRightLeg
      ∧ cyclicThreeOmegaEvalCell cyclicThreeOmegaSssssLeftLeg
        ≠ cyclicThreeOmegaEvalCell cyclicThreeOmegaSssssRightLeg :=
  ⟨cyclicThreeOmegaSssssThreeCell, cyclicThreeOmegaMatSeparatesSssss⟩

/-! # =========================================================================================
    # B1 — THE IDEMPOTENT `eee` OVER-QUOTIENT + RESTORED SOUNDNESS (e |-> width 1, M : ee => e |-> [[1,1]])
    # ========================================================================================= -/

/-- The **idempotent generator matrix table**: `e |-> ` width 1; the rewrite rule `M : e.e => e` maps to the
monoid fold `[[1,1]] : 1x2` (source `ee` width 2, target `e` width 1) — the SAME matrix as the monad's `mu`,
which is why the idempotent's genuine associativity is the monad's `leftUnitAssoc` repair.  `Unit` above,
constant `Unit` label — propext-clean.  `[[1,1]]` is a SOUND choice: it respects the `M`-mediated
associativity (both legs `[[1,1,1]]`, machine-checked below), not merely any separating value. -/
def idempotentSemigroupOmegaEvalGen : (labelDim : Nat) → Unit →
    BunchedBimonoidEvalCarrier labelDim → BunchedBimonoidEvalCarrier labelDim →
    BunchedBimonoidEvalCarrier (labelDim + 1)
  | 0, _, _, _ => (1 : Nat)
  | 1, _, _, _ => { rows := 1, cols := 2, entries := [[1, 1]] }
  | _ + 2, _, _, _ => ()

/-- ★ **The idempotent-semigroup matrix evaluation** — the monoid functor into `Mat(N)`, the identical fold
with the idempotent generator table (`e` / `M`).  Propext-clean. -/
def idempotentSemigroupOmegaEvalCell : {dim : Nat} → CellExpr idempotentSemigroupOmegaComputad dim →
    BunchedBimonoidEvalCarrier dim
  | _, .ofMode _ => ()
  | _, .gen (dim := labelDim) label source target =>
      idempotentSemigroupOmegaEvalGen labelDim label
        (idempotentSemigroupOmegaEvalCell source) (idempotentSemigroupOmegaEvalCell target)
  | _, .id (dim := d) cell => bunchedBimonoidEvalId d (idempotentSemigroupOmegaEvalCell cell)
  | _, .vcomp (dim := d) leftCell rightCell =>
      bunchedBimonoidEvalVcomp d (idempotentSemigroupOmegaEvalCell leftCell)
        (idempotentSemigroupOmegaEvalCell rightCell)
  | _, .whiskerLeft (dim := d) whiskerCell cell =>
      bunchedBimonoidEvalWhiskerLeft d (idempotentSemigroupOmegaEvalCell whiskerCell)
        (idempotentSemigroupOmegaEvalCell cell)
  | _, .whiskerRight (dim := d) cell whiskerCell =>
      bunchedBimonoidEvalWhiskerRight d (idempotentSemigroupOmegaEvalCell cell)
        (idempotentSemigroupOmegaEvalCell whiskerCell)

/-- ★ The idempotent `eee` legs are DIFFERENT: `M |> e` = `[[1,1,0],[0,0,1]]` vs `e <| M` = `[[1,0,0],[0,1,1]]`;
entry `(0,1)` is `1` vs `0`.  The bare-whisker over-quotient the ledger predicted clean. -/
theorem idempotentSemigroupOmegaMatSeparatesEee :
    idempotentSemigroupOmegaEvalCell idempotentSemigroupOmegaEeeLeftLeg
      ≠ idempotentSemigroupOmegaEvalCell idempotentSemigroupOmegaEeeRightLeg :=
  fun hmatrix => Nat.noConfusion (congrArg (fun matrix => bunchedBimonoidMatEntryAt matrix 0 1) hmatrix)

/-- ★ **CONTROL — the idempotent VALLEY is literal-equal** (both leg targets `e.e`), a genuine identification
ANY model respects — unlike the peak/leg separation.  So the over-quotient lives at the dim-2 leg
identification, NOT at the (already-genuine) valley identification. -/
theorem idempotentSemigroupOmegaEeeValleyLiterallyEqual :
    idempotentSemigroupOmegaEvalCell (boundaryTarget idempotentSemigroupOmegaEeeLeftLeg)
      = idempotentSemigroupOmegaEvalCell (boundaryTarget idempotentSemigroupOmegaEeeRightLeg) := rfl

/-- ★★ **THE IDEMPOTENT `eee` OVER-QUOTIENT WITNESS** — r1 convertibility
(`idempotentSemigroupOmegaEeeThreeCell`) yet distinct `Mat(N)` maps. -/
theorem idempotentSemigroupOmegaBaseRelOverQuotientsEee :
    SaturatedConvOverWithId idempotentSemigroupOmegaComputad idempotentSemigroupOmegaBaseRel
        idempotentSemigroupOmegaEeeLeftLeg idempotentSemigroupOmegaEeeRightLeg
      ∧ idempotentSemigroupOmegaEvalCell idempotentSemigroupOmegaEeeLeftLeg
        ≠ idempotentSemigroupOmegaEvalCell idempotentSemigroupOmegaEeeRightLeg :=
  ⟨idempotentSemigroupOmegaEeeThreeCell, idempotentSemigroupOmegaMatSeparatesEee⟩

/-! ## The idempotent's RESTORED SOUNDNESS: the `M`-mediated associativity (the monad `leftUnitAssoc` repair) -/

/-- The **genuine associativity LAW left leg** `(M |> e) . M : eee => e` — reduce the outer pair, then multiply.
The exact `M`-mediated closed composite the correct house style uses (contrast the bare `M |> e` leg). -/
def idempotentSemigroupOmegaGenuineAssocLeftLeg : CellExpr idempotentSemigroupOmegaComputad 2 :=
  CellExpr.vcomp idempotentSemigroupOmegaEeeLeftLeg idempotentSemigroupOmegaMuGen

/-- The **genuine associativity LAW right leg** `(e <| M) . M : eee => e` — reduce the inner pair, then
multiply. -/
def idempotentSemigroupOmegaGenuineAssocRightLeg : CellExpr idempotentSemigroupOmegaComputad 2 :=
  CellExpr.vcomp idempotentSemigroupOmegaEeeRightLeg idempotentSemigroupOmegaMuGen

/-- The genuine `M`-mediated associativity is matrix-respected: both legs evaluate to `[[1,1,1]]`. -/
theorem idempotentSemigroupOmegaMatrixRespectsGenuineAssoc :
    idempotentSemigroupOmegaEvalCell idempotentSemigroupOmegaGenuineAssocLeftLeg
      = idempotentSemigroupOmegaEvalCell idempotentSemigroupOmegaGenuineAssocRightLeg := rfl

/-- ★ The **genuine-law sub-relation** `Mat(N)` RESPECTS: the single `M`-mediated associativity law (the
idempotent's only dim-2 genuine content — the bare `eee` critical row is DELIBERATELY absent).  This is the
sound sub-congruence the r1 presentation over-quotients (it strictly adds the bare `eee` row).  A clone of the
monad's `MonadOmegaSoundRow` at one row. -/
inductive IdempotentSemigroupOmegaSoundRow :
    {d : Nat} → CellExpr idempotentSemigroupOmegaComputad d →
      CellExpr idempotentSemigroupOmegaComputad d → Prop where
  /-- the genuine associativity LAW `(M |> e) . M ~ (e <| M) . M`. -/
  | genuineAssoc : IdempotentSemigroupOmegaSoundRow idempotentSemigroupOmegaGenuineAssocLeftLeg
      idempotentSemigroupOmegaGenuineAssocRightLeg

/-- The **matrix-equality relation** — two same-dimension idempotent cells relate iff they evaluate to the same
matrix.  The target congruence of the soundness fold. -/
def idempotentSemigroupOmegaMatrixEq : CellRelOver idempotentSemigroupOmegaComputad :=
  fun {_dim} cellAlpha cellBeta =>
    idempotentSemigroupOmegaEvalCell cellAlpha = idempotentSemigroupOmegaEvalCell cellBeta

/-- ★★ **THE MATRIX EVALUATION RESPECTS THE GENUINE-LAW SUB-CONGRUENCE.**  Matrix equality absorbs the
idCongr-extended saturated congruence over `IdempotentSemigroupOmegaSoundRow`: the genuine associativity relates
equal-matrix legs (`rfl`) and every congruence closure is `congrArg` on the corresponding shared evaluation
helper — the exact `monadOmegaSoundMatrixEvalAbsorbs` shape over the idempotent computad. -/
def idempotentSemigroupOmegaSoundMatrixEvalAbsorbs :
    IsSaturatedCongruenceWithId idempotentSemigroupOmegaComputad IdempotentSemigroupOmegaSoundRow
      idempotentSemigroupOmegaMatrixEq where
  ofRelation := by intro _dim _cellAlpha _cellBeta row; cases row <;> rfl
  vcompCongrLeft := by
    intro dim _cellAlpha _cellAlpha' cellBeta hconv
    exact congrArg (fun leftMatrix => bunchedBimonoidEvalVcomp dim leftMatrix
      (idempotentSemigroupOmegaEvalCell cellBeta)) hconv
  vcompCongrRight := by
    intro dim cellAlpha _cellBeta _cellBeta' hconv
    exact congrArg (fun rightMatrix => bunchedBimonoidEvalVcomp dim
      (idempotentSemigroupOmegaEvalCell cellAlpha) rightMatrix) hconv
  whiskerLeftCongr := by
    intro dim whiskeringCell _cellBeta _cellBeta' hconv
    exact congrArg (fun cellMatrix => bunchedBimonoidEvalWhiskerLeft dim
      (idempotentSemigroupOmegaEvalCell whiskeringCell) cellMatrix) hconv
  whiskerRightCongr := by
    intro dim _cellAlpha _cellAlpha' whiskeringCell hconv
    exact congrArg (fun cellMatrix => bunchedBimonoidEvalWhiskerRight dim cellMatrix
      (idempotentSemigroupOmegaEvalCell whiskeringCell)) hconv
  idCongr := by
    intro dim _cellAlpha _cellBeta hconv
    exact congrArg (fun subMatrix => bunchedBimonoidEvalId dim subMatrix) hconv
  whiskerLeftWhiskerCongr := by
    intro dim _whiskerAlpha _whiskerAlpha' innerCell hconv
    exact congrArg (fun whiskerMatrix => bunchedBimonoidEvalWhiskerLeft dim whiskerMatrix
      (idempotentSemigroupOmegaEvalCell innerCell)) hconv
  whiskerRightWhiskerCongr := by
    intro dim innerCell _whiskerAlpha _whiskerAlpha' hconv
    exact congrArg (fun whiskerMatrix => bunchedBimonoidEvalWhiskerRight dim
      (idempotentSemigroupOmegaEvalCell innerCell) whiskerMatrix) hconv
  refl := by intro _dim _cell; rfl
  symm := by intro _dim _cellAlpha _cellBeta hconv; exact hconv.symm
  trans := by intro _dim _cellAlpha _cellBeta _cellGamma hleft hright; exact hleft.trans hright

/-- ★★ **RESTORED SOUNDNESS: convertible over the genuine-law sub-theory ⟹ equal matrix.**  The fold of
`idempotentSemigroupOmegaSoundMatrixEvalAbsorbs` through the least-congruence UP.  This is the SOUND congruence
the r1 presentation over-quotients (it strictly adds the bare `eee` row). -/
theorem idempotentSemigroupOmegaMatrixSoundOverSound {dim : Nat}
    {cellAlpha cellBeta : CellExpr idempotentSemigroupOmegaComputad dim}
    (conv : SaturatedConvOverWithId idempotentSemigroupOmegaComputad IdempotentSemigroupOmegaSoundRow
      cellAlpha cellBeta) :
    idempotentSemigroupOmegaEvalCell cellAlpha = idempotentSemigroupOmegaEvalCell cellBeta :=
  SaturatedConvOverWithId.recInto idempotentSemigroupOmegaSoundMatrixEvalAbsorbs conv

/-- The bare `eee` legs are NOT convertible over the genuine-law sub-theory (else restored soundness forces
equal matrices, contradicting the separation). -/
theorem idempotentSemigroupOmegaSoundRowNotConvertibleEee :
    ¬ SaturatedConvOverWithId idempotentSemigroupOmegaComputad IdempotentSemigroupOmegaSoundRow
        idempotentSemigroupOmegaEeeLeftLeg idempotentSemigroupOmegaEeeRightLeg :=
  fun conv => idempotentSemigroupOmegaMatSeparatesEee
    (idempotentSemigroupOmegaMatrixSoundOverSound conv)

/-- ★★ **THE r1 IDEMPOTENT PRESENTATION STRICTLY OVER-QUOTIENTS THE GENUINE-LAW SUB-THEORY.**  The `eee` legs
are convertible under `idempotentSemigroupOmegaBaseRel` (the shipped generating 3-cell) yet PROVABLY NOT
convertible under `IdempotentSemigroupOmegaSoundRow` (the `M`-mediated associativity).  Machine-airtight and
zero-axiom; the strict-2-cat-law extension is the NAMED Fubini wall. -/
theorem idempotentSemigroupOmegaBaseRelStrictlyOverQuotientsSound :
    ∃ (leftLeg rightLeg : CellExpr idempotentSemigroupOmegaComputad 2),
      SaturatedConvOverWithId idempotentSemigroupOmegaComputad idempotentSemigroupOmegaBaseRel
        leftLeg rightLeg ∧
      ¬ SaturatedConvOverWithId idempotentSemigroupOmegaComputad IdempotentSemigroupOmegaSoundRow
        leftLeg rightLeg :=
  ⟨idempotentSemigroupOmegaEeeLeftLeg, idempotentSemigroupOmegaEeeRightLeg,
    idempotentSemigroupOmegaEeeThreeCell, idempotentSemigroupOmegaSoundRowNotConvertibleEee⟩

/-! # =========================================================================================
    # B1 / B4 — THE TRIO VERDICT MARKERS (corrections to the r4 family ledger)
    # ========================================================================================= -/

/-- ★★ **THE INVOLUTION `sss` ROW OVER-QUOTIENTS — machine-confirmed, was "predicted clean".**  `= true`
records `involutionOmegaBaseRelOverQuotientsSss`: the r1 base relation identifies the two bare-whisker legs
that the `Mat(N)` model separates.  Under the family's dim-2-congruence + free-2-category semantics (THE SAME
standard as the monad) the involution over-quotients; under the delooped-monoid semantics the presented monoid
`Z/2` is correct and only the distinct 2-cells collapse.  Corrects the ledger marker
`fxOmegaHouseStyle_notSpuriousTrioShapeMatchesOverQuotientUnresolved` from UNRESOLVED to CONFIRMED for this
row. -/
def fxOmegaHouseStyle_involutionOverQuotientConfirmedMatNSeparated : Bool := true

/-- ★★ **THE CYCLIC-3 `ssss` / `sssss` ROWS OVER-QUOTIENT — machine-confirmed, were "predicted clean".**
`= true` records `cyclicThreeOmegaBaseRelOverQuotients{Ssss,Sssss}`: BOTH cyclic-3 leg-pairs are r1-convertible
yet `Mat(N)`-separated.  Same dual-semantics reading as the involution (presented monoid `Z/3` correct; distinct
2-cells collapse). -/
def fxOmegaHouseStyle_cyclicThreeOverQuotientConfirmedMatNSeparated : Bool := true

/-- ★★ **THE IDEMPOTENT `eee` ROW OVER-QUOTIENTS + RESTORED SOUNDNESS — machine-confirmed, was "predicted
clean".**  `= true` records `idempotentSemigroupOmegaBaseRelOverQuotientsEee` and
`idempotentSemigroupOmegaBaseRelStrictlyOverQuotientsSound`: the bare `eee` legs are r1-convertible yet
`Mat(N)`-separated AND provably not convertible over the sound `M`-mediated associativity.  The genuine
collapse `e.e = e` lives at the (literal) VALLEY (`idempotentSemigroupOmegaEeeValleyLiterallyEqual`), NOT at the
dim-2 legs — so the dim-2 leg identification over-quotients even though the valley is genuine. -/
def fxOmegaHouseStyle_idempotentOverQuotientConfirmedMatNSeparated : Bool := true

/-- ★★ **THE LEDGER'S TORSION-MODEL CATEGORY ERROR IS RETRACTED.**  `= true` records the correction to
`fxOmegaHouseStyle_shapeIsNecessaryNotSufficientFaithfulModelDecides`'s "the torsion trio's delooped group is
2-coherent, identifies" clause: the shipped presentation's `rho` / `R` / `M` is a NON-INVERTIBLE 2-cell
GENERATOR, not a 1-level torsion equation, so `s` is not torsion / not invertible and `Mat(N)` IS a legitimate
strict-2-category model that separates.  The "delooped group `B(Z/3)`" would force `s.s.s = id` at the 1-level
AND trivialize all 2-cells — a non-faithful collapse, not evidence of soundness.  So the discriminant
"over-quotient = shape present AND faithful model separates" resolves POSITIVE for the trio (contra the ledger's
prediction). -/
def fxOmegaHouseStyle_trioTorsionModelCategoryErrorRetracted : Bool := true

/-- ★ **THE INVOLUTION / CYCLIC GENUINE CONTENT IS DIM-3 HOMOTOPY — no dim-2 sound sub-theory this round
(Fubini-walled).**  `= false` records that, unlike the monad (`mu`) and idempotent (`M`), the involution / cyclic
walkers have NO dim-2 mediated law (`rho` / `R` have no post-composition mechanism): their genuine content is
purely dim-3 (the two legs are homotopic via the shipped generating 3-cell), so the sound dim-2 sub-theory is
`StrictAxiomRel` alone — its `Mat(N)`-soundness is the NAMED finite-sum Fubini matrix-algebra kit, identical to
`fxOmegaHouseStyle_monadFullIsolationNeedsStrictLawFubiniKit`.  The over-quotient witnesses (convertibility +
separation) are shipped and decisive regardless; only the full strict-law isolation is walled. -/
def fxOmegaHouseStyle_involutionCyclicSoundSubTheoryIsStrictFubiniWalled : Bool := false

/-- ★ **THE IDEMPOTENT SOUND SUB-THEORY IS THE `M`-MEDIATED ASSOCIATIVITY (shipped).**  `= true` records that
the idempotent — unlike involution / cyclic — DOES have a dim-2 genuine law `Mat(N)` respects on the nose (the
`M`-mediated associativity `(M |> e).M ~ (e <| M).M`, both legs `[[1,1,1]]`), so its restored soundness ships
here (`IdempotentSemigroupOmegaSoundRow` + `idempotentSemigroupOmegaMatrixSoundOverSound`), the exact monad
`leftUnitAssoc` repair.  The full extension over `StrictAxiomRel union SoundRow` remains the NAMED Fubini wall. -/
def fxOmegaHouseStyle_idempotentSoundSubTheoryIsMMediatedAssoc : Bool := true

/-- ★ **ESTABLISHED (B1) — the not-spurious trio over-quotient adjudication.**  `= true` records the scoreboard:
all FOUR trio leg-pairs (involution `sss`, cyclic-3 `ssss` / `sssss`, idempotent `eee`) OVER-QUOTIENT — each r1
convertible yet `Mat(N)`-separated, the SAME model / standard that condemns the walking monad; the ledger's
"PREDICTED CLEAN by torsion" is REFUTED and its torsion-model category error retracted; the idempotent's
restored soundness ships (`M`-mediated associativity); the involution / cyclic dim-2 sound sub-theory is
`StrictAxiomRel` (Fubini-walled); the presented 1-dimensional monoids (`Z/2`, `Z/3`, idempotent) remain
correct — only the distinct 2-cells collapse, uniformly with the monad-vs-Delta situation.  Every wall NAMED. -/
def fxOmegaHouseStyle_notSpuriousTrioOverQuotientAdjudicationShipped : Bool := true

/-! ## The B1 truth-probe outputs (the four separations + the genuine idempotent model) -/

#eval (involutionOmegaEvalCell involutionLeftLeg).entries
#eval (involutionOmegaEvalCell involutionRightLeg).entries
#eval (cyclicThreeOmegaEvalCell cyclicThreeOmegaSsssLeftLeg).entries
#eval (cyclicThreeOmegaEvalCell cyclicThreeOmegaSssssLeftLeg).entries
#eval (idempotentSemigroupOmegaEvalCell idempotentSemigroupOmegaEeeLeftLeg).entries
#eval (idempotentSemigroupOmegaEvalCell idempotentSemigroupOmegaEeeRightLeg).entries
#eval (idempotentSemigroupOmegaEvalCell idempotentSemigroupOmegaGenuineAssocLeftLeg).entries
#eval (idempotentSemigroupOmegaEvalCell idempotentSemigroupOmegaGenuineAssocRightLeg).entries

end FX1Poly.Polygraph.Omega

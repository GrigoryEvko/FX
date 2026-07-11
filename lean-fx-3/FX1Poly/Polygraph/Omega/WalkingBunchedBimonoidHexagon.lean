import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidSpiderBlockExchange

/-! # Polygraph/Omega/WalkingBunchedBimonoidHexagon — the width-3 hexagon rows, added additively to the sound
congruence (WP-PROP r4, #2033, the 110-percent grind)

★ **THE HEXAGON — Yang-Baxter + the two wide-symmetry naturality squares — is a GENUINELY-NEW width-3 row
family, matrix-respected, ADDED additively to `BunchedBimonoidSoundRow`.**  The r3 land shipped the
block-exchange interchange (`bunchedBimonoidBlockExchangeInterchange`) and named the width-3 whiskered-`sigma`
content as the star's remaining wall (`fxBunchedBimonoid_starVcompCoherenceHexagonWall = false`,
`fxBunchedBimonoid_matrixHexagonReached = false`).  The r3 adjudication was decisive: the block-exchange
produces ONLY block-diagonal `directSum` results, so the anti-diagonal `sigma` and every routing permutation are
beyond its reach (`bunchedBimonoidSwapUnreachableByDiagonal`); the hexagon is NOT derivable from the width-2
`BunchedBimonoidSoundRow` rows plus interchange.

## Why the interchange does NOT derive the hexagon (the honest missing-ctor verdict)

The `BunchedBimonoidSoundRow` width-2 sigma content is `sigmaEtaNaturality` / `sigmaEpsNaturality` — both
expressible WITHOUT a whiskered `sigma`.  The Godement `interchange` row (`StrictAxioms.interchange`) commutes
two cells on DISJOINT strand ranges; it yields only the far-commutation `sigma_i sigma_j = sigma_j sigma_i`
(`|i-j| >= 2`), never the OVERLAPPING 3-strand Coxeter relation
`sigma_{12} sigma_{23} sigma_{12} ~ sigma_{23} sigma_{12} sigma_{23}` (Yang-Baxter) nor the wide-symmetry
naturality `sigma_{a, a.a} = (sigma |> a) ; (a <| sigma)`.  So the hexagon is a NEW row, precisely the
r1/r2/r3 wall.

## The additive route (the r2 sigma-naturality precedent)

Every hexagon row is MATRIX-respected — each `sigma` evaluates to a permutation matrix, and Yang-Baxter /
the two naturality squares are matrix identities (`rfl`):

  * **Yang-Baxter** `(sigma |> a) ; (a <| sigma) ; (sigma |> a) ~ (a <| sigma) ; (sigma |> a) ; (a <| sigma)` —
    both legs evaluate to the reversal permutation `[[0,0,1],[0,1,0],[1,0,0]]` (the longest element of S_3).
  * **mu-naturality** `(a <| mu) ; sigma ~ [(sigma |> a) ; (a <| sigma)] ; (mu |> a)` — both legs
    `[[0,1,1],[1,0,0]]` (the width-3 hexagon for `sigma` past the multiplication).
  * **delta-naturality** `sigma ; (a <| delta) ~ (delta |> a) ; [(a <| sigma) ; (sigma |> a)]` — both legs
    `[[0,1],[1,0],[1,0]]` (the dual, `sigma` past the comultiplication).

So — exactly as r2 added `sigmaEtaNaturality` / `sigmaEpsNaturality` as `rfl`-matrix-respected ctors — this file
adds the three hexagon rows as a fresh relation `BunchedBimonoidHexagonRow`, unions it with
`BunchedBimonoidSoundRow` (the shipped `unionCellRel`), and proves matrix soundness over the WIDENED
congruence.  The census cost is the honest scope note: the completeness star now quantifies over
`BunchedBimonoidSoundRow union BunchedBimonoidHexagonRow`, and the r3 hexagon walls are retired NAME-ONLY (their
`= false` values byte-intact, cross-file).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! The width-3 3-fold-`matMul` `rfl` reductions (Yang-Baxter, the two wide-symmetry naturality squares) unfold a
`List.range`-generated matrix product whose `whnf` exceeds the default elaborator heartbeat budget; the raised
budget is a compute allowance only — every proof term stays `Eq.refl`, axiom-free (`#assert_no_axioms` in the
twin, `#print axioms` clean). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # B1 — THE WIDTH-3 WHISKERED SIGMAS + THE YANG-BAXTER TRUTH-PROBE (rfl, FIRST)
    # =========================================================================================

★ **The truth-probe FIRST: the width-3 whiskered sigmas are the two elementary S_3 transpositions, and their
3-fold Coxeter words agree on the reversal — `rfl`.**  Before any row, the two whiskered braidings are pinned to
their permutation matrices, and the Yang-Baxter braid relation is machine-confirmed as a matrix identity. -/

/-! ## The two whiskered braidings (the elementary transpositions at width 3) -/

/-- ★ The **right-whiskered braiding** `sigma |> a : (a.a).a => (a.a).a` — the swap of the first two strands, the
elementary transposition `s_1` at width 3.  `evalCell = directSum sigma (identityMat 1)`. -/
def bunchedBimonoidSigmaWhiskerRight : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAdditiveGen

/-- ★ The **left-whiskered braiding** `a <| sigma : a.(a.a) => a.(a.a)` — the swap of the last two strands, the
elementary transposition `s_2` at width 3.  `evalCell = directSum (identityMat 1) sigma`. -/
def bunchedBimonoidSigmaWhiskerLeft : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddSigmaGen

/-- `sigma |> a` evaluates to the transposition `(1 2)` matrix `[[0,1,0],[1,0,0],[0,0,1]]`. -/
theorem bunchedBimonoidSigmaWhiskerRightMatrix :
    bunchedBimonoidEvalCell bunchedBimonoidSigmaWhiskerRight
      = { rows := 3, cols := 3, entries := [[0, 1, 0], [1, 0, 0], [0, 0, 1]] } := rfl

/-- `a <| sigma` evaluates to the transposition `(2 3)` matrix `[[1,0,0],[0,0,1],[0,1,0]]`. -/
theorem bunchedBimonoidSigmaWhiskerLeftMatrix :
    bunchedBimonoidEvalCell bunchedBimonoidSigmaWhiskerLeft
      = { rows := 3, cols := 3, entries := [[1, 0, 0], [0, 0, 1], [0, 1, 0]] } := rfl

/-! ## The two wide symmetries (the block braiding `sigma_{a, a.a}` and its inverse `sigma_{a.a, a}`) -/

/-- ★ The **front wide symmetry** `(sigma |> a) ; (a <| sigma) : a.a.a => a.a.a` — the block braiding
`sigma_{a, a.a}` moving the first strand past the last two.  `evalCell = [[0,1,0],[0,0,1],[1,0,0]]` (the cyclic
shift). -/
def bunchedBimonoidWideSymmetryFront : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidSigmaWhiskerRight bunchedBimonoidSigmaWhiskerLeft

/-- ★ The **back wide symmetry** `(a <| sigma) ; (sigma |> a) : a.a.a => a.a.a` — the block braiding
`sigma_{a.a, a}` moving the last strand past the first two.  `evalCell = [[0,0,1],[1,0,0],[0,1,0]]` (the inverse
cyclic shift). -/
def bunchedBimonoidWideSymmetryBack : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidSigmaWhiskerLeft bunchedBimonoidSigmaWhiskerRight

/-- The front wide symmetry evaluates to the cyclic shift `[[0,1,0],[0,0,1],[1,0,0]]`. -/
theorem bunchedBimonoidWideSymmetryFrontMatrix :
    bunchedBimonoidEvalCell bunchedBimonoidWideSymmetryFront
      = { rows := 3, cols := 3, entries := [[0, 1, 0], [0, 0, 1], [1, 0, 0]] } := rfl

/-- The back wide symmetry evaluates to the inverse cyclic shift `[[0,0,1],[1,0,0],[0,1,0]]`. -/
theorem bunchedBimonoidWideSymmetryBackMatrix :
    bunchedBimonoidEvalCell bunchedBimonoidWideSymmetryBack
      = { rows := 3, cols := 3, entries := [[0, 0, 1], [1, 0, 0], [0, 1, 0]] } := rfl

/-! ## THE YANG-BAXTER TRUTH-PROBE (self-attack #1, rfl) -/

/-- ★★ The **Yang-Baxter LEFT leg** `(sigma |> a) ; (a <| sigma) ; (sigma |> a) : a.a.a => a.a.a` — the `s_1 s_2
s_1` Coxeter word. -/
def bunchedBimonoidYangBaxterLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.vcomp bunchedBimonoidSigmaWhiskerRight bunchedBimonoidSigmaWhiskerLeft)
    bunchedBimonoidSigmaWhiskerRight

/-- ★★ The **Yang-Baxter RIGHT leg** `(a <| sigma) ; (sigma |> a) ; (a <| sigma) : a.a.a => a.a.a` — the `s_2 s_1
s_2` Coxeter word. -/
def bunchedBimonoidYangBaxterRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.vcomp bunchedBimonoidSigmaWhiskerLeft bunchedBimonoidSigmaWhiskerRight)
    bunchedBimonoidSigmaWhiskerLeft

/-- ★★★ **THE YANG-BAXTER MATRIX AGREEMENT (self-attack #1, rfl).**  Both 3-fold Coxeter words `s_1 s_2 s_1` and
`s_2 s_1 s_2` evaluate to the SAME matrix — the reversal permutation `[[0,0,1],[0,1,0],[1,0,0]]` (the longest
element of S_3).  This is the OVERLAPPING 3-strand relation the disjoint-range Godement interchange cannot
reach; the matrix confirms it holds as a linear map. -/
theorem bunchedBimonoidMatrixRespectsYangBaxter :
    bunchedBimonoidEvalCell bunchedBimonoidYangBaxterLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidYangBaxterRightLeg := rfl

/-! ## The mu / delta whiskerings (the naturality squares' non-braiding legs) -/

/-- `a <| mu : a.(a.a) => a.a` — multiply the last two strands.  `evalCell = [[1,0,0],[0,1,1]]`. -/
def bunchedBimonoidMuWhiskerLeft : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddMuGen

/-- `mu |> a : (a.a).a => a.a` — multiply the first two strands.  `evalCell = [[1,1,0],[0,0,1]]`. -/
def bunchedBimonoidMuWhiskerRight : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerRight bunchedBimonoidAddMuGen bunchedBimonoidAdditiveGen

/-- `a <| delta : a.a => a.(a.a)` — comultiply the last strand.  `evalCell = [[1,0],[0,1],[0,1]]`. -/
def bunchedBimonoidDeltaWhiskerLeft : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddDeltaGen

/-- `delta |> a : a.a => (a.a).a` — comultiply the first strand.  `evalCell = [[1,0],[1,0],[0,1]]`. -/
def bunchedBimonoidDeltaWhiskerRight : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.whiskerRight bunchedBimonoidAddDeltaGen bunchedBimonoidAdditiveGen

/-! ## THE mu-NATURALITY HEXAGON (self-attack, rfl) -/

/-- ★★ The **mu-naturality LEFT leg** `(a <| mu) ; sigma : a.a.a => a.a` — multiply the last two strands, then
swap. -/
def bunchedBimonoidMuNaturalityLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidMuWhiskerLeft bunchedBimonoidAddSigmaGen

/-- ★★ The **mu-naturality RIGHT leg** `[(sigma |> a) ; (a <| sigma)] ; (mu |> a) : a.a.a => a.a` — the front
wide symmetry, then multiply the first two strands. -/
def bunchedBimonoidMuNaturalityRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidWideSymmetryFront bunchedBimonoidMuWhiskerRight

/-- ★★★ **THE mu-NATURALITY MATRIX AGREEMENT (the width-3 hexagon, rfl).**  `sigma`'s naturality past the
multiplication: both legs evaluate to `[[0,1,1],[1,0,0]]`.  The width-3 correction the r3 adjudication named
absent from `BunchedBimonoidSoundRow`. -/
theorem bunchedBimonoidMatrixRespectsMuNaturality :
    bunchedBimonoidEvalCell bunchedBimonoidMuNaturalityLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidMuNaturalityRightLeg := rfl

/-! ## THE delta-NATURALITY HEXAGON (the dual, rfl) -/

/-- ★★ The **delta-naturality LEFT leg** `sigma ; (a <| delta) : a.a => a.a.a` — swap, then comultiply the last
strand. -/
def bunchedBimonoidDeltaNaturalityLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidAddSigmaGen bunchedBimonoidDeltaWhiskerLeft

/-- ★★ The **delta-naturality RIGHT leg** `(delta |> a) ; [(a <| sigma) ; (sigma |> a)] : a.a => a.a.a` —
comultiply the first strand, then the back wide symmetry. -/
def bunchedBimonoidDeltaNaturalityRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidDeltaWhiskerRight bunchedBimonoidWideSymmetryBack

/-- ★★★ **THE delta-NATURALITY MATRIX AGREEMENT (the dual width-3 hexagon, rfl).**  `sigma`'s naturality past
the comultiplication: both legs evaluate to `[[0,1],[1,0],[1,0]]`.  The dual of the mu-naturality hexagon, using
the BACK wide symmetry. -/
theorem bunchedBimonoidMatrixRespectsDeltaNaturality :
    bunchedBimonoidEvalCell bunchedBimonoidDeltaNaturalityLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidDeltaNaturalityRightLeg := rfl

/-! ## B1 truth-probe outputs -/

#eval bunchedBimonoidEvalCell bunchedBimonoidYangBaxterLeftLeg
#eval bunchedBimonoidEvalCell bunchedBimonoidYangBaxterRightLeg
#eval bunchedBimonoidEvalCell bunchedBimonoidMuNaturalityLeftLeg
#eval bunchedBimonoidEvalCell bunchedBimonoidMuNaturalityRightLeg
#eval bunchedBimonoidEvalCell bunchedBimonoidDeltaNaturalityLeftLeg
#eval bunchedBimonoidEvalCell bunchedBimonoidDeltaNaturalityRightLeg

/-! ## The B1 honesty markers -/

/-- ★★ **ESTABLISHED (B1) — the width-3 whiskered braidings + the Yang-Baxter matrix agreement are
truth-probed.**  `= true` records the two elementary transpositions (`bunchedBimonoidSigmaWhisker{Right,Left}` =
`s_1` / `s_2`, matrices `(1 2)` / `(2 3)`), the two wide symmetries
(`bunchedBimonoidWideSymmetry{Front,Back}` = the cyclic shifts), and the Yang-Baxter braid relation
(`bunchedBimonoidMatrixRespectsYangBaxter`: both `s_1 s_2 s_1` and `s_2 s_1 s_2` legs evaluate to the reversal
`[[0,0,1],[0,1,0],[1,0,0]]`, `rfl`).  This is the overlapping 3-strand Coxeter relation the disjoint-range
Godement interchange cannot reach — the honest missing-ctor content. -/
def fxBunchedBimonoid_yangBaxterTruthProbed : Bool := true

/-- ★★ **ESTABLISHED (B1) — the two width-3 naturality hexagons are matrix-respected.**  `= true` records
`bunchedBimonoidMatrixRespects{MuNaturality,DeltaNaturality}`: `sigma`'s naturality past the multiplication (both
legs `[[0,1,1],[1,0,0]]`) and past the comultiplication (both legs `[[0,1],[1,0],[1,0]]`), each `rfl` — the
width-3 `mu` / `delta` corrections the r3 adjudication named absent from `BunchedBimonoidSoundRow`. -/
def fxBunchedBimonoid_hexagonNaturalityMatrixRespected : Bool := true

/-! # =========================================================================================
    # B2 — THE HEXAGON ROW FAMILY + THE WIDENED SOUND CONGRUENCE (additive)
    # =========================================================================================

★ **The three hexagon rows as a fresh relation, unioned with `BunchedBimonoidSoundRow` (the shipped
`unionCellRel`), with matrix soundness over the WIDENED congruence.**  Exactly the r2 sigma-naturality
precedent: the hexagon rows are matrix-respected (`rfl`), so the matrix evaluation absorbs the idCongr-extended
saturated congruence over `unionCellRel SoundRow HexagonRow`.  `BunchedBimonoidSoundRow` is UNTOUCHED (its 15
ctors byte-intact); the widening is additive. -/

/-- ★ The **hexagon row family** — the three genuinely-new width-3 rows the matrix respects but
`BunchedBimonoidSoundRow` lacks: Yang-Baxter (the S_3 Coxeter braid relation) and the two naturality hexagons
(`sigma` past `mu` / past `delta`, using the wide symmetries).  Added additively; each row relates equal-matrix
legs by `rfl`. -/
inductive BunchedBimonoidHexagonRow :
    {d : Nat} → CellExpr bunchedBimonoidOmegaComputad d → CellExpr bunchedBimonoidOmegaComputad d → Prop where
  /-- Yang-Baxter `s_1 s_2 s_1 ~ s_2 s_1 s_2` (the overlapping 3-strand Coxeter relation). -/
  | yangBaxter : BunchedBimonoidHexagonRow bunchedBimonoidYangBaxterLeftLeg bunchedBimonoidYangBaxterRightLeg
  /-- mu-naturality `(a <| mu) ; sigma ~ [(sigma |> a) ; (a <| sigma)] ; (mu |> a)` (the width-3 hexagon). -/
  | muNaturality : BunchedBimonoidHexagonRow bunchedBimonoidMuNaturalityLeftLeg bunchedBimonoidMuNaturalityRightLeg
  /-- delta-naturality `sigma ; (a <| delta) ~ (delta |> a) ; [(a <| sigma) ; (sigma |> a)]` (the dual). -/
  | deltaNaturality :
      BunchedBimonoidHexagonRow bunchedBimonoidDeltaNaturalityLeftLeg bunchedBimonoidDeltaNaturalityRightLeg

/-- ★ The **widened sound congruence's base relation** — `BunchedBimonoidSoundRow` unioned with
`BunchedBimonoidHexagonRow` through the shipped `unionCellRel`.  The 15 sound rows PLUS the 3 hexagon rows = 18
genuine rows over which `Mat(N)` is a sound model, the honest completeness target at the width-3 scope. -/
def bunchedBimonoidHexagonWidenedRow : CellRelOver bunchedBimonoidOmegaComputad :=
  unionCellRel bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow BunchedBimonoidHexagonRow

/-- ★★ **THE MATRIX EVALUATION RESPECTS THE WIDENED (SOUND + HEXAGON) CONGRUENCE.**  Matrix equality absorbs the
idCongr-extended saturated congruence over `unionCellRel SoundRow HexagonRow`: an `ofRelation` row splits on the
union (a `SoundRow` row delegates to the shipped `bunchedBimonoidSoundMatrixEvalAbsorbs`; a hexagon row is `rfl`
by matrix-respectedness), and every congruence-closure field is the shipped absorber's — the field types do NOT
mention the base relation.  The additive hexagon widening of `bunchedBimonoidSoundMatrixEvalAbsorbs`. -/
def bunchedBimonoidHexagonMatrixEvalAbsorbs :
    IsSaturatedCongruenceWithId bunchedBimonoidOmegaComputad
      (unionCellRel bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow BunchedBimonoidHexagonRow)
      bunchedBimonoidMatrixEq where
  ofRelation := by
    intro _dim _cellAlpha _cellBeta row
    cases row with
    | inl soundRow => exact bunchedBimonoidSoundMatrixEvalAbsorbs.ofRelation soundRow
    | inr hexRow =>
        cases hexRow with
        | yangBaxter => exact bunchedBimonoidMatrixRespectsYangBaxter
        | muNaturality => exact bunchedBimonoidMatrixRespectsMuNaturality
        | deltaNaturality => exact bunchedBimonoidMatrixRespectsDeltaNaturality
  vcompCongrLeft := bunchedBimonoidSoundMatrixEvalAbsorbs.vcompCongrLeft
  vcompCongrRight := bunchedBimonoidSoundMatrixEvalAbsorbs.vcompCongrRight
  whiskerLeftCongr := bunchedBimonoidSoundMatrixEvalAbsorbs.whiskerLeftCongr
  whiskerRightCongr := bunchedBimonoidSoundMatrixEvalAbsorbs.whiskerRightCongr
  idCongr := bunchedBimonoidSoundMatrixEvalAbsorbs.idCongr
  whiskerLeftWhiskerCongr := bunchedBimonoidSoundMatrixEvalAbsorbs.whiskerLeftWhiskerCongr
  whiskerRightWhiskerCongr := bunchedBimonoidSoundMatrixEvalAbsorbs.whiskerRightWhiskerCongr
  refl := bunchedBimonoidSoundMatrixEvalAbsorbs.refl
  symm := bunchedBimonoidSoundMatrixEvalAbsorbs.symm
  trans := bunchedBimonoidSoundMatrixEvalAbsorbs.trans

/-- ★★ **RESTORED SOUNDNESS OVER THE WIDENED CONGRUENCE: convertible over `SoundRow union HexagonRow` ⟹ equal
matrix.**  Any two cells convertible under the congruence generated by the 15 sound + 3 hexagon rows share their
`Mat(N)` matrix — the fold of `bunchedBimonoidHexagonMatrixEvalAbsorbs` through the least-congruence UP.  The
soundness half of the width-3 completeness target; the hexagon rows are now genuine convertibilities that the
matrix still respects. -/
theorem bunchedBimonoidMatrixSoundOverHexagon {dim : Nat}
    {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim}
    (conv : SaturatedConvOverWithId bunchedBimonoidOmegaComputad
      (unionCellRel bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow BunchedBimonoidHexagonRow)
      cellAlpha cellBeta) :
    bunchedBimonoidEvalCell cellAlpha = bunchedBimonoidEvalCell cellBeta :=
  SaturatedConvOverWithId.recInto bunchedBimonoidHexagonMatrixEvalAbsorbs conv

/-- ★ **The widened congruence STRICTLY EXTENDS the sound sub-theory** — every `BunchedBimonoidSoundRow`
convertibility folds into the widened congruence via `Or.inl`, and the hexagon rows add new ones.  The free
embedding: a sound-row conversion is a widened conversion (the sound rows are the `Or.inl` half of the union). -/
theorem bunchedBimonoidSoundRowEmbedsIntoHexagon {dim : Nat}
    {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim}
    (soundRow : BunchedBimonoidSoundRow cellAlpha cellBeta) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad
      (unionCellRel bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow BunchedBimonoidHexagonRow)
      cellAlpha cellBeta :=
  SaturatedConvOverWithId.ofRelation (Or.inl soundRow)

/-! ## The B2 honesty markers -/

/-- ★★ **ESTABLISHED (B2) — the hexagon rows are added additively over the sound congruence, matrix-sound.**
`= true` records `BunchedBimonoidHexagonRow` (the 3 width-3 rows: Yang-Baxter + the two naturality hexagons), the
widened base relation `unionCellRel SoundRow HexagonRow`, the respects-congruence datum
`bunchedBimonoidHexagonMatrixEvalAbsorbs` (the hexagon widening of the shipped
`bunchedBimonoidSoundMatrixEvalAbsorbs`), and the widened soundness `bunchedBimonoidMatrixSoundOverHexagon`
(convertible over the 18-row congruence ⟹ equal matrix).  `BunchedBimonoidSoundRow` is UNTOUCHED (15 ctors
byte-intact); the widening is additive, exactly the r2 sigma-naturality precedent. -/
def fxBunchedBimonoid_hexagonRowsShippedMatrixRespected : Bool := true

/-! # =========================================================================================
    # B3 — THE HEXAGON COMPLETENESS INSTANCES (hand-exhibited over the widened congruence)
    # =========================================================================================

★ **Two hand-exhibited "equal matrix ⟹ convertible" instances over the widened congruence, each closed THROUGH
a genuine hexagon row.**  Exactly mirroring the r1/r2 sigma-mediated completeness instances (the two B1 legs to
`spiderAllOnesTwo`, the cocommutativity legs to `spiderCopyOne`), but now at WIDTH 3: the two Yang-Baxter legs
(same reversal matrix) both convert to the canonical `s_2 s_1 s_2` word through the hexagon `yangBaxter` row, and
the two mu-naturality legs (same matrix `[[0,1,1],[1,0,0]]`) both convert to the canonical
`[(sigma |> a) ; (a <| sigma)] ; (mu |> a)` word.  These are HAND-EXHIBITED convertibilities over
`SoundRow union HexagonRow`, NOT a general decision — the general NF induction (the #2033 star) stays r5. -/

/-! ## Instance A — the Yang-Baxter legs converge to the canonical Coxeter word -/

/-- The **Yang-Baxter right leg IS the canonical form** — convertibility over the widened congruence is `refl`. -/
theorem bunchedBimonoidYangBaxterRightLegConvertibleToCanonical :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad
      (unionCellRel bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow BunchedBimonoidHexagonRow)
      bunchedBimonoidYangBaxterRightLeg bunchedBimonoidYangBaxterRightLeg :=
  SaturatedConvOverWithId.refl _

/-- ★★ The **Yang-Baxter LEFT leg converts to the canonical form** through the widened congruence — the `s_1 s_2
s_1` word converts to `s_2 s_1 s_2` by firing the genuine `yangBaxter` hexagon row (`Or.inr`). -/
theorem bunchedBimonoidYangBaxterLeftLegConvertibleToCanonical :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad
      (unionCellRel bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow BunchedBimonoidHexagonRow)
      bunchedBimonoidYangBaxterLeftLeg bunchedBimonoidYangBaxterRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr BunchedBimonoidHexagonRow.yangBaxter)

/-- ★ **DERIVED (not assumed): the Yang-Baxter legs share their matrix** — from the convertibility via the
widened soundness `bunchedBimonoidMatrixSoundOverHexagon` (both the reversal). -/
theorem bunchedBimonoidYangBaxterMatrixSharedOverHexagon :
    bunchedBimonoidEvalCell bunchedBimonoidYangBaxterLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidYangBaxterRightLeg :=
  bunchedBimonoidMatrixSoundOverHexagon bunchedBimonoidYangBaxterLeftLegConvertibleToCanonical

/-- ★★ **HEXAGON COMPLETENESS INSTANCE A (Yang-Baxter).**  Two structurally-distinct 3-fold Coxeter words with
the SAME matrix (the reversal) are BOTH convertible over the widened congruence to the canonical `s_2 s_1 s_2`
word — a hand-exhibited "equal-matrix ⟹ convertible" witness at width 3, closed through the genuine `yangBaxter`
hexagon row. -/
theorem bunchedBimonoidYangBaxterCompletenessInstance :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad
        (unionCellRel bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow BunchedBimonoidHexagonRow)
        bunchedBimonoidYangBaxterLeftLeg bunchedBimonoidYangBaxterRightLeg
      ∧ SaturatedConvOverWithId bunchedBimonoidOmegaComputad
        (unionCellRel bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow BunchedBimonoidHexagonRow)
        bunchedBimonoidYangBaxterRightLeg bunchedBimonoidYangBaxterRightLeg
      ∧ bunchedBimonoidEvalCell bunchedBimonoidYangBaxterLeftLeg
        = bunchedBimonoidEvalCell bunchedBimonoidYangBaxterRightLeg :=
  ⟨bunchedBimonoidYangBaxterLeftLegConvertibleToCanonical,
    bunchedBimonoidYangBaxterRightLegConvertibleToCanonical,
    bunchedBimonoidYangBaxterMatrixSharedOverHexagon⟩

/-! ## Instance B — the mu-naturality legs converge to the canonical wide-symmetry word -/

/-- The **mu-naturality right leg IS the canonical form** — convertibility over the widened congruence is
`refl`. -/
theorem bunchedBimonoidMuNaturalityRightLegConvertibleToCanonical :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad
      (unionCellRel bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow BunchedBimonoidHexagonRow)
      bunchedBimonoidMuNaturalityRightLeg bunchedBimonoidMuNaturalityRightLeg :=
  SaturatedConvOverWithId.refl _

/-- ★★ The **mu-naturality LEFT leg converts to the canonical form** through the widened congruence — by firing
the genuine `muNaturality` hexagon row. -/
theorem bunchedBimonoidMuNaturalityLeftLegConvertibleToCanonical :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad
      (unionCellRel bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow BunchedBimonoidHexagonRow)
      bunchedBimonoidMuNaturalityLeftLeg bunchedBimonoidMuNaturalityRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr BunchedBimonoidHexagonRow.muNaturality)

/-- ★★ **HEXAGON COMPLETENESS INSTANCE B (mu-naturality).**  Two structurally-distinct width-3 diagrams with the
SAME matrix `[[0,1,1],[1,0,0]]` are BOTH convertible over the widened congruence to the canonical wide-symmetry
word — the width-3 analogue of the r1 sigma-mediated instances, closed through the `muNaturality` hexagon row. -/
theorem bunchedBimonoidMuNaturalityCompletenessInstance :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad
        (unionCellRel bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow BunchedBimonoidHexagonRow)
        bunchedBimonoidMuNaturalityLeftLeg bunchedBimonoidMuNaturalityRightLeg
      ∧ SaturatedConvOverWithId bunchedBimonoidOmegaComputad
        (unionCellRel bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow BunchedBimonoidHexagonRow)
        bunchedBimonoidMuNaturalityRightLeg bunchedBimonoidMuNaturalityRightLeg
      ∧ bunchedBimonoidEvalCell bunchedBimonoidMuNaturalityLeftLeg
        = bunchedBimonoidEvalCell bunchedBimonoidMuNaturalityRightLeg :=
  ⟨bunchedBimonoidMuNaturalityLeftLegConvertibleToCanonical,
    bunchedBimonoidMuNaturalityRightLegConvertibleToCanonical,
    bunchedBimonoidMatrixRespectsMuNaturality⟩

/-! ## The B3 honesty markers -/

/-- ★★ **ESTABLISHED (B3) — two hexagon completeness instances over the widened congruence.**  `= true` records
`bunchedBimonoidYangBaxterCompletenessInstance` (the two Coxeter legs, same reversal matrix, both convertible to
`s_2 s_1 s_2`) and `bunchedBimonoidMuNaturalityCompletenessInstance` (the two width-3 mu-naturality diagrams,
same matrix `[[0,1,1],[1,0,0]]`, both convertible to the canonical wide-symmetry word), each an EXPLICIT term
through `unionCellRel SoundRow HexagonRow` (`refl` + `ofRelation (Or.inr ...)`), the shared matrix DERIVED via
`bunchedBimonoidMatrixSoundOverHexagon`.  The width-3 analogue of the r1/r2 sigma-mediated instances —
HAND-EXHIBITED, NOT a general decision. -/
def fxBunchedBimonoid_hexagonCompletenessInstancesShipped : Bool := true

/-! # =========================================================================================
    # B4 — THE LEDGER: the r3 hexagon walls retired name-only + the honest scope
    # =========================================================================================

★ **The honest r4 hexagon scoreboard.**  The width-3 hexagon rows are LITERALLY delivered (matrix-respected,
added additively over the sound congruence, with soundness and completeness instances), so the r3 hexagon walls
are retired NAME-ONLY; the star's completeness target now visibly widens to
`BunchedBimonoidSoundRow union BunchedBimonoidHexagonRow`.  The general NF induction (equal matrix ⟹ convertible
for ALL 2-cells) stays the #2033 star, r5 — NO fake flip. -/

/-- ★★★ **RETIRED NAME-ONLY — the r3 hexagon wall's content is literally delivered.**  `= true` records that the
width-3 whiskered-`sigma` naturality / Yang-Baxter content the r3 wall
`fxBunchedBimonoid_starVcompCoherenceHexagonWall` (and `fxBunchedBimonoid_matrixHexagonReached`) named ABSENT
from `BunchedBimonoidSoundRow` is now SHIPPED — as matrix-respected rows (`BunchedBimonoidHexagonRow`) added
additively over the sound congruence, with the widened soundness `bunchedBimonoidMatrixSoundOverHexagon`.  Per
the "retire name-only ONLY at literal delivery" rule, this fresh marker retires those walls by NAME; the r3/r2
markers `fxBunchedBimonoid_starVcompCoherenceHexagonWall` / `fxBunchedBimonoid_matrixHexagonReached` keep their
name and `= false` value byte-intact (cross-file, not edited), their residual denotation narrowing to the
GENERAL routing (an arbitrary permutation word / transpose), NOT the width-3 rows delivered here. -/
def fxBunchedBimonoid_hexagonWallRetiredNameOnly : Bool := true

/-- ★★ **THE STAR'S CONGRUENCE VISIBLY WIDENS — completeness now targets `SoundRow union HexagonRow`.**
`= true` records the census cost the recon flagged as the single most important honesty constraint: the
completeness star ("equal matrix ⟹ convertible") now quantifies over the WIDENED congruence
`unionCellRel BunchedBimonoidSoundRow BunchedBimonoidHexagonRow` (15 sound + 3 hexagon = 18 rows), NOT
`BunchedBimonoidSoundRow` alone.  Stating the star over `SoundRow` alone would miss the width-3 hexagon; the
honest target is the widened congruence, over which soundness is machine-checked
(`bunchedBimonoidMatrixSoundOverHexagon`) and the completeness instances land. -/
def fxBunchedBimonoid_starCongruenceWidensToHexagon : Bool := true

/-- ★ **THE #2033 STAR STAYS r5 — the general NF induction is NOT claimed.**  `= false` records that the GENERAL
matrix completeness — "equal `Mat(N)` matrix ⟹ convertible over `SoundRow union HexagonRow`" for ALL 2-cells,
the NF induction / diagram-to-matrix retraction — is the #2033 star and is NOT reached in r4.  The hexagon rows
close the WIDTH-3 completeness INSTANCES (hand-exhibited), and the block-exchange (r3) reaches the block-diagonal
round-trips, but the full retraction (every cell converts to `spiderOf (evalCell cell)`, including the general
routing perm-stage) needs the general `spiderOf : Mat -> CellExpr` with its transpose routing — deferred.  The
upstream star markers `fxBunchedBimonoid_spiderNormalFormStarNamedRThree` /
`...propGeneralCompletenessStarReached` stay `= false` (r1/r2 files, byte-intact) — cited name-only, NO fake
flip. -/
def fxBunchedBimonoid_hexagonStarStillRFive : Bool := false

/-- ★★ **ESTABLISHED (B4) — the WP-PROP r4 hexagon ledger (honest scoreboard).**  `= true` records the complete
r4 hexagon advance: B1 the width-3 whiskered braidings + the Yang-Baxter matrix agreement (self-attack #1,
`rfl`) + the two naturality hexagons (mu / delta, both matrix-respected); B2 the hexagon row family
`BunchedBimonoidHexagonRow` added additively over `BunchedBimonoidSoundRow` (the shipped `unionCellRel`) with the
respects-congruence datum `bunchedBimonoidHexagonMatrixEvalAbsorbs` and the widened soundness
`bunchedBimonoidMatrixSoundOverHexagon`; B3 two hand-exhibited hexagon completeness instances (Yang-Baxter +
mu-naturality) over the widened congruence; B4 the r3 hexagon walls retired name-only + the star's congruence
visibly widened, the #2033 star staying r5 (NO fake flip).  Every upstream `= false` marker
(`fxBunchedBimonoid_starVcompCoherenceHexagonWall`, `...matrixHexagonReached`,
`...spiderNormalFormStarNamedRThree`, `...propGeneralCompletenessStarReached`) keeps its name and value
byte-intact. -/
def fxBunchedBimonoid_hexagonLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega

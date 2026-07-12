import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCanonicalWordRunCommuteConv

/-! # Polygraph/Omega/WalkingBunchedBimonoidIdentityPointUnitor — the width-0 identity-point whisker unitor as a
NEW named sibling presentation (never an in-place edit of the shipped star scope), matrix-sound at width 0
(WP-PROP r20, U1)

★ **THE HONEST SIBLING PRESENTATION.**  The r17 `RunCommuteConv` wall named THREE whisker coherences the
distant-commute / run-conv atoms need; the r19 substrate round LANDED two of them (the whisker-1-cell associator,
both duals, and the whisker left/right commute) as genuine `StrictAxiomRel` rows.  The sole residual is the
**identity-whisker unitor** `whiskerLeft (id c) X ~ X` / `whiskerRight X (id c) ~ X`.

The r19 harvest (`WalkingBunchedBimonoidWhiskerCoherenceLanded`) MACHINE-REFUTED the FREE unitor: for a wide `c`
its two `linearizeFull` chain tables DIFFER (`whiskerIdentityUnitorTablesDiffer`, `decide`), so adding it as a
free `StrictAxiomRel` row would falsify the shipped ★★ CROWN `linearizeFullSoundness`.  The graveyard discipline:
the refuted free row is NEVER added.  BUT at the PIN `c = bunchedBimonoidPoint` (the width-0 object, whose
`identityMat 0` is the empty block) the unitor IS matrix-sound (`I_0 (+) M = M`, `M (+) I_0 = M`), and it is the
exact brick the edge `sigmaAt` letters (`i = 0`, `j = w - 2`) need — `sigmaAt w 0 = whiskerLeft (a^0 = id point)
(sigma |> a^(w-2))` by defeq (`bunchedBimonoidAWordPow 0 = bunchedBimonoidIdOne = CellExpr.id
bunchedBimonoidPoint`).

## The Semantic Honesty Law, obeyed

A walker PRESENTATION relation set is theory-defining data: adding a row to a shipped presentation CHANGES the
presented theory unless the row is DERIVABLE.  The pinned unitor is NOT derivable from the shipped
`bunchedBimonoidStarCongruenceScope` (its `StrictAxiomRel.whiskerLeftUnit` whiskers an identity 2-CELL, not by an
identity 1-cell; assoc/commute reshape widths, none identifies `whiskerLeft (id point) X` with `X`; the free form
is machine-refuted).  So it enters ONLY as a **new named sibling presentation**
`bunchedBimonoidStarScopeWithPointUnitor`, an additive `unionCellRel` of the byte-intact shipped star scope with
the fresh width-0 row `bunchedBimonoidIdentityPointWhiskerRow`.  The shipped star scope is untouched; every
consumer of the old presentation stays on it; the free full `whiskerUnitRel` (matrix-UNSOUND at `dim >= 1`, since
`I_{|lower|} (+) M != M` for a wide `lower`) is NOT united — only the `point`-restricted rows, which are
matrix-sound.

## What this file ships (all zero-axiom, machine-checked)

  * `bunchedBimonoidIdentityPointWhiskerRow` — the fresh two-row relation (left/right whisker by `id point`).
  * `bunchedBimonoidStarScopeWithPointUnitor` — the sibling scope (star scope `union` the fresh row).
  * `bunchedBimonoidIdentityPointWhiskerRowEvalRespects` — the row is MATRIX-sound: both legs share their
    `Mat(N)` map (`I_0 (+) M = M`, structural, propext-clean — no `List.append_nil`, no `Nat.zero_add` axiom leak).
  * `bunchedBimonoidStarScopeEmbedsIntoPointUnitorSibling` — every shipped star-scope convertibility folds into
    the sibling (relation weakening on the left summand), so all shipped reshapes transport.
  * `bunchedBimonoidSigmaAtZeroUnitorConv` / `...WidthTwoUnitorConv` — the edge-letter unitor bridges the U2
    distant-commute needs, fired by the fresh row over the sibling scope.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin.  StrictAxioms.lean and the soundness masters stay byte-intact (the engine
is closed; the unitor lives at the PRESENTATION level as additive DATA). -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # U1.A — THE FRESH WIDTH-0 IDENTITY-POINT WHISKER ROW (additive; StrictAxioms.lean untouched)
    # =========================================================================================
-/

/-- ★ The **width-0 identity-point whisker unitor** — the two rows whiskering a dim-2 cell by the identity
1-cell `id point` (`= bunchedBimonoidAWordPow 0 = bunchedBimonoidIdOne`) are no-ops.  Restricted to the width-0
object `bunchedBimonoidPoint` on purpose: the FREE `whiskerUnitRel` (`EckmannHiltonWithId`, over all `dim`) is
matrix-UNSOUND at `dim >= 1` (`I_{|lower|} (+) M != M`); this `point`-pin is matrix-SOUND (`I_0 (+) M = M`).  A
FRESH inductive — `StrictAxiomRel` is byte-intact; this is additive presentation DATA, not an engine edit. -/
inductive bunchedBimonoidIdentityPointWhiskerRow :
    {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim →
      CellExpr bunchedBimonoidOmegaComputad dim → Prop where
  /-- Left whisker by the identity point 1-cell is a no-op `whiskerLeft (id point) cell ~ cell`. -/
  | leftIdPoint (cell : CellExpr bunchedBimonoidOmegaComputad 2) :
      bunchedBimonoidIdentityPointWhiskerRow
        (CellExpr.whiskerLeft (CellExpr.id bunchedBimonoidPoint) cell) cell
  /-- Right whisker by the identity point 1-cell is a no-op `whiskerRight cell (id point) ~ cell`. -/
  | rightIdPoint (cell : CellExpr bunchedBimonoidOmegaComputad 2) :
      bunchedBimonoidIdentityPointWhiskerRow
        (CellExpr.whiskerRight cell (CellExpr.id bunchedBimonoidPoint)) cell

/-- ★ The **sibling presentation scope** — the byte-intact shipped `bunchedBimonoidStarCongruenceScope` united
with the fresh width-0 unitor row.  A NEW named presentation (never an in-place edit of the shipped star scope);
the additive `unionCellRel` keeps every shipped row and every shipped-scope consumer untouched. -/
def bunchedBimonoidStarScopeWithPointUnitor : CellRelOver bunchedBimonoidOmegaComputad :=
  unionCellRel bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
    bunchedBimonoidIdentityPointWhiskerRow

/-! # =========================================================================================
    # U1.B — MATRIX SOUNDNESS OF THE FRESH ROW (the sibling does not collapse the Mat(N) model)
    # =========================================================================================

★ The point-unitor row is `Mat(N)`-sound: `I_0 (+) M = M`.  Structural, propext-clean (`List.append_nil` leaks
`propext`; `Nat.zero_add` is used only where it discharges by `rfl`-equivalent core reduction) — the sibling model
does not collapse.  This is the width-0 restriction's payoff over the free `whiskerUnitRel`. -/

/-- Structural `List.map (fun row => [] ++ row) = id` — propext-clean (hand-rolled, `List.map_id` free). -/
private theorem bunchedBimonoidMapNilAppendLeft (rowsList : List (List Nat)) :
    rowsList.map (fun row => ([] : List Nat) ++ row) = rowsList := by
  induction rowsList with
  | nil => rfl
  | cons head tail ih => exact congrArg (fun rest => head :: rest) ih

/-- Structural `xs ++ [] = xs` at any element type — propext-clean (hand-rolled; `List.append_nil` leaks
`propext`). -/
private theorem bunchedBimonoidAppendNil {alpha : Type} (xs : List alpha) : xs ++ ([] : List alpha) = xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih => exact congrArg (fun rest => head :: rest) ih

/-- Structural `List.map (fun row => row ++ []) = id` — propext-clean. -/
private theorem bunchedBimonoidMapNilAppendRight (rowsList : List (List Nat)) :
    rowsList.map (fun row => row ++ ([] : List Nat)) = rowsList := by
  induction rowsList with
  | nil => rfl
  | cons head tail ih => rw [List.map_cons, bunchedBimonoidAppendNil, ih]

/-- ★ **`I_0 (+) M = M`** — the empty block direct-sum on the left is the identity, structurally (`0 + rows`
rewritten by `Nat.zero_add`; the `[] ++ row` map collapsed by `bunchedBimonoidMapNilAppendLeft`).  Propext-clean. -/
theorem bunchedBimonoidDirectSumIdentityZeroLeft (matrix : BunchedBimonoidMat) :
    bunchedBimonoidMatDirectSum (bunchedBimonoidIdentityMat 0) matrix = matrix := by
  cases matrix with
  | mk rows cols entries =>
    have reduced : bunchedBimonoidMatDirectSum (bunchedBimonoidIdentityMat 0) ⟨rows, cols, entries⟩
        = ⟨0 + rows, 0 + cols, entries.map (fun row => ([] : List Nat) ++ row)⟩ := rfl
    rw [reduced, Nat.zero_add, Nat.zero_add, bunchedBimonoidMapNilAppendLeft]

/-- ★ **`M (+) I_0 = M`** — the empty block direct-sum on the right is the identity (`rows + 0` reduces by
core; the `row ++ []` map and the trailing `++ []` collapsed structurally).  Propext-clean. -/
theorem bunchedBimonoidDirectSumIdentityZeroRight (matrix : BunchedBimonoidMat) :
    bunchedBimonoidMatDirectSum matrix (bunchedBimonoidIdentityMat 0) = matrix := by
  cases matrix with
  | mk rows cols entries =>
    have reduced : bunchedBimonoidMatDirectSum ⟨rows, cols, entries⟩ (bunchedBimonoidIdentityMat 0)
        = ⟨rows, cols, (entries.map (fun row => row ++ ([] : List Nat))) ++ []⟩ := rfl
    rw [reduced, bunchedBimonoidAppendNil, bunchedBimonoidMapNilAppendRight]

/-- ★★ **THE FRESH ROW IS `Mat(N)`-SOUND.**  Both legs of every `bunchedBimonoidIdentityPointWhiskerRow` share
their `Mat(N)` matrix: `evalCell (whiskerLeft (id point) cell) = directSum (identityMat 0) (evalCell cell) =
evalCell cell` (and the right dual).  So the sibling congruence does not collapse the matrix model — the width-0
restriction's exact justification for admitting the unitor here but not freely. -/
theorem bunchedBimonoidIdentityPointWhiskerRowEvalRespects {dim : Nat}
    {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim}
    (row : bunchedBimonoidIdentityPointWhiskerRow cellAlpha cellBeta) :
    bunchedBimonoidEvalCell cellAlpha = bunchedBimonoidEvalCell cellBeta := by
  cases row with
  | leftIdPoint cell => exact bunchedBimonoidDirectSumIdentityZeroLeft (bunchedBimonoidEvalCell cell)
  | rightIdPoint cell => exact bunchedBimonoidDirectSumIdentityZeroRight (bunchedBimonoidEvalCell cell)

/-! # =========================================================================================
    # U1.C — THE SIBLING ABSORBS THE SHIPPED STAR SCOPE (relation weakening on the left summand)
    # =========================================================================================
-/

/-- ★ **The sibling absorbs the shipped star scope.**  `IsSaturatedCongruenceWithId` datum lifting every
shipped-scope convertibility into the sibling: a base star-scope row fires as `Or.inl` of the union, and every
one-hole / `id` / whisker-1-cell congruence maps to its namesake constructor.  The fold data for
`bunchedBimonoidStarScopeEmbedsIntoPointUnitorSibling`. -/
def bunchedBimonoidPointUnitorSiblingAbsorbsStar :
    IsSaturatedCongruenceWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      (fun {_dim : Nat} cellAlpha cellBeta => SaturatedConvOverWithId bunchedBimonoidOmegaComputad
        bunchedBimonoidStarScopeWithPointUnitor cellAlpha cellBeta) where
  ofRelation := by
    intro _dim _cellAlpha _cellBeta starRow
    exact SaturatedConvOverWithId.ofRelation (Or.inl starRow)
  vcompCongrLeft := by
    intro _dim _cellAlpha _cellAlpha' cellBeta conv
    exact SaturatedConvOverWithId.vcompCongrLeft cellBeta conv
  vcompCongrRight := by
    intro _dim cellAlpha _cellBeta _cellBeta' conv
    exact SaturatedConvOverWithId.vcompCongrRight cellAlpha conv
  whiskerLeftCongr := by
    intro _dim whiskeringCell _cellBeta _cellBeta' conv
    exact SaturatedConvOverWithId.whiskerLeftCongr whiskeringCell conv
  whiskerRightCongr := by
    intro _dim _cellAlpha _cellAlpha' whiskeringCell conv
    exact SaturatedConvOverWithId.whiskerRightCongr whiskeringCell conv
  idCongr := by
    intro _dim _cellAlpha _cellBeta conv
    exact SaturatedConvOverWithId.idCongr conv
  whiskerLeftWhiskerCongr := by
    intro _dim _whiskerAlpha _whiskerAlpha' innerCell conv
    exact SaturatedConvOverWithId.whiskerLeftWhiskerCongr innerCell conv
  whiskerRightWhiskerCongr := by
    intro _dim innerCell _whiskerAlpha _whiskerAlpha' conv
    exact SaturatedConvOverWithId.whiskerRightWhiskerCongr innerCell conv
  refl := by intro _dim cell; exact SaturatedConvOverWithId.refl cell
  symm := by intro _dim _cellAlpha _cellBeta conv; exact SaturatedConvOverWithId.symm conv
  trans := by
    intro _dim _cellAlpha _cellBeta _cellGamma convLeft convRight
    exact SaturatedConvOverWithId.trans convLeft convRight

/-- ★ **The shipped star scope embeds into the sibling.**  Every convertibility over
`bunchedBimonoidStarCongruenceScope` folds into the sibling `bunchedBimonoidStarScopeWithPointUnitor` — so every
shipped reshape (`aWordPowSplitConv`, `sigmaAtBoundaryReshapeConv`, the interchange / associator / commute embeds)
transports to the sibling for free.  The old presentation's consumers stay on the old scope; this is a
one-directional lift. -/
theorem bunchedBimonoidStarScopeEmbedsIntoPointUnitorSibling {dim : Nat}
    {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim}
    (conv : SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      cellAlpha cellBeta) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarScopeWithPointUnitor
      cellAlpha cellBeta :=
  SaturatedConvOverWithId.recInto bunchedBimonoidPointUnitorSiblingAbsorbsStar conv

/-! # =========================================================================================
    # U1.D — THE FRESH ROW FIRES + THE EDGE-LETTER UNITOR BRIDGES (the exact U2 bricks)
    # =========================================================================================
-/

/-- ★ The **left width-0 unitor fires over the sibling** — `whiskerLeft (id point) cell ~ cell`, via `Or.inr`
of the fresh row.  The generic brick the edge `sigmaAt` letters instantiate. -/
theorem bunchedBimonoidLeftIdPointUnitorConv (cell : CellExpr bunchedBimonoidOmegaComputad 2) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarScopeWithPointUnitor
      (CellExpr.whiskerLeft (CellExpr.id bunchedBimonoidPoint) cell) cell :=
  SaturatedConvOverWithId.ofRelation (Or.inr (bunchedBimonoidIdentityPointWhiskerRow.leftIdPoint cell))

/-- ★ The **right width-0 unitor fires over the sibling** — `whiskerRight cell (id point) ~ cell`. -/
theorem bunchedBimonoidRightIdPointUnitorConv (cell : CellExpr bunchedBimonoidOmegaComputad 2) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarScopeWithPointUnitor
      (CellExpr.whiskerRight cell (CellExpr.id bunchedBimonoidPoint)) cell :=
  SaturatedConvOverWithId.ofRelation (Or.inr (bunchedBimonoidIdentityPointWhiskerRow.rightIdPoint cell))

/-- ★★ **THE LEFT-EDGE `sigmaAt` UNITOR BRIDGE — `sigmaAt w 0 ~ sigma |> a^(w-2)` over the sibling.**  Since
`bunchedBimonoidAWordPow 0 = bunchedBimonoidIdOne = CellExpr.id bunchedBimonoidPoint` (defeq), the position-0
letter `sigmaAt w 0 = whiskerLeft (a^0) (whiskerRight sigma (a^(w-2)))` is DEFINITIONALLY
`whiskerLeft (id point) (whiskerRight sigma (a^(w-2)))`, so the fresh left row fires directly — this is the exact
brick the U2 distant-commute needs for the position-0 letter (the r19 assoc/commute rows do NOT supply it). -/
theorem bunchedBimonoidSigmaAtZeroUnitorConv (wordWidth : Nat) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarScopeWithPointUnitor
      (bunchedBimonoidSigmaAt wordWidth 0)
      (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow (wordWidth - 2))) :=
  bunchedBimonoidLeftIdPointUnitorConv
    (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen (bunchedBimonoidAWordPow (wordWidth - 2)))

/-! ## The U1 honesty markers -/

/-- ★★★ **ESTABLISHED (U1) — the width-0 identity-point unitor is a NEW named sibling presentation, matrix-sound,
shipped.**  `= true` records `bunchedBimonoidIdentityPointWhiskerRow` (the fresh two-row width-0 relation),
`bunchedBimonoidStarScopeWithPointUnitor` (the additive sibling, the shipped star scope byte-intact),
`bunchedBimonoidIdentityPointWhiskerRowEvalRespects` (the row is `Mat(N)`-sound, `I_0 (+) M = M`, propext-clean),
`bunchedBimonoidStarScopeEmbedsIntoPointUnitorSibling` (every shipped reshape transports), and the edge-letter
bridge `bunchedBimonoidSigmaAtZeroUnitorConv`.  Per the Semantic Honesty Law this is a PRESENTATION CHANGE
admitted only as a sibling (never an in-place edit): the pinned unitor is NOT derivable from the shipped scope
(the free form is machine-refuted, `whiskerIdentityUnitor_not_conv`), and the free full `whiskerUnitRel` is
matrix-UNSOUND at `dim >= 1` so is NOT united — only the matrix-sound width-0 rows.  Zero-axiom (per-decl
`#assert_no_axioms` + independent `#print axioms` in the twin). -/
def fxBunchedBimonoid_identityPointUnitorSiblingShipped : Bool := true

/-- ★★ **ESTABLISHED (U1) — the pinned width-0 unitor is `Mat(N)`-sound (the sibling does not collapse).**
`= true` records `bunchedBimonoidIdentityPointWhiskerRowEvalRespects` +
`bunchedBimonoidDirectSumIdentityZero{Left,Right}`: whiskering a dim-2 cell by `id point` is a matrix no-op
(`I_0 (+) M = M`, `M (+) I_0 = M`), structurally, propext-clean.  The width-0 restriction is exactly why this
sibling is admissible where the free `whiskerUnitRel` (matrix-UNSOUND at `dim >= 1`) is not. -/
def fxBunchedBimonoid_identityPointUnitorMatrixSound : Bool := true

/-- ★ **THE SHIPPED STAR SCOPE STILL LACKS THE UNITOR — no flip, byte-intact.**  `= false` records that the
shipped `bunchedBimonoidStarCongruenceScope` does NOT gain the identity-whisker unitor: it is NOT derivable there
(the free form falsifies `linearizeFullSoundness`, machine-refuted r19), so the shipped scope stays byte-intact
and the r19 `fxBunchedBimonoid_whiskerIdentityUnitorChainRefutedStaysWalled` keeps its name and `= false` value.
The unitor lives ONLY in the additive sibling `bunchedBimonoidStarScopeWithPointUnitor` at the width-0 pin.  NO
fabricated flip; the four star owners stay `false`. -/
def fxBunchedBimonoid_shippedStarScopeStillLacksUnitorNoFlip : Bool := false

end FX1Poly.Polygraph.Omega

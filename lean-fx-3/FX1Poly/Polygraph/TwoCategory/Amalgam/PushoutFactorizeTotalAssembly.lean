import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeVcompCase
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeWhiskerCase
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutEndoModeTransport
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutRightImageDecision
import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedDispatch

/-! # Polygraph/TwoCategory/Amalgam/PushoutFactorizeTotalAssembly — the TOTAL factorization reader assembled from the
five case-builders; the two-sided decision's both verdicts; the purification adjudication (WP-AMALG-2 r15, Brick B4)

The four preceding bricks shipped the five per-case single-block builders: `pushoutFactorizeId` (r8), the `gen` case
`pushoutFactorizeGen` (B1), the `whisker` cases `pushoutFactorizeWhiskerLeftGap` / `RightGap` (B2), and the `vcomp`
base case `pushoutFactorizeVcompSingleGap` (B3).  Because each builder is NON-recursive (it discharges its case with a
single block, never descending), the five assemble into a TOTAL factorization reader by a plain 5-way match — no
structural recursion, no fuel.  The whisker arms pin their free middle mode by `pushoutModeUnique` (the pushout is
`modeCount = 1`).

## What `pushoutFactorizeTotal` IS — and is NOT

`pushoutFactorizeTotal` is the EXISTENCE reader: every pushout 2-cell IS convertible to a wall/gap layout (`∀ cell,
PushoutLayoutFactorization crossPairRealPushoutRel cell`, total, zero-axiom).  This SETTLES the existence question the
recon flagged (self-attacks 5b/5c): a factorization always exists.

It is NOT the CANONICAL firing-block reader.  Each case places the whole subterm in ONE gap (the `vcomp` halves in
one gap's split, the whisker frame as one wall) — a SHALLOW one-level layout, NOT the per-firing-region canonical
decomposition with walls at per-letter positions.  So `pushoutFactorizeTotal` does NOT canonicalize the gap payloads,
hence does NOT feed the arbitrary-pair decision (which needs comparable canonical skeletons) and does NOT provide the
NF reflection purification needs.  The wall is CANONICALITY, not existence — exactly the recon's §4/§5 distinction.

## The decision + the purification adjudication

The two-sided per-gap decision (`pushoutRightImageTwoSidedDecision`, shipped) DECIDES both verdicts on concrete pairs
with extraction: `true` on the associativity foldings, `false` on the two monad faces (`pushoutDecisionBothVerdicts`).
The purification adjudication (recon §4): the total EXISTENCE reader gives cell-level projection (essential-surjectivity,
via the shipped round-trip) but NOT derivation-level purification — that needs the NF reflection (conv-of-images ⟹
equal-layouts), which shallow existence does not supply.  `fxAmalg_hasSaturatedDispatchTheorem` STAYS `false`
(`pushoutPurificationStaysOpenWithTotalReader`).

## What STAYS WALLED (no flip)

`fxAmalg_topFactorizationInductionStaysWalled` (the CANONICAL reader + decider wiring) STAYS `true`;
`fxAmalg_hasFullSaturatedPushoutDispatch` / `fxAmalg_hasGeneralPushoutDispatch` STAY `false`; #2043 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The total factorization reader — all five cases, non-recursive, mode-pinned whisker arms -/

/-- ★★★ **THE TOTAL FACTORIZATION READER (existence).**  Every pushout 2-cell factors into a `VcompGapPair` layout
with a saturated convertibility to it — a TOTAL function `∀ cell, PushoutLayoutFactorization crossPairRealPushoutRel
cell`, assembled by a plain 5-way match over the cell (no recursion — each case-builder discharges its case with a
single block): `id → pushoutFactorizeId`, `gen → pushoutFactorizeGen`, `vcomp → pushoutFactorizeVcompSingleGap`,
`whiskerLeft/Right → pushoutFactorizeWhiskerLeftGap / RightGap` (their free middle mode pinned by `pushoutModeUnique`,
the pushout being `modeCount = 1`).  This settles EXISTENCE of layout factorizations; it is the SHALLOW (one-level)
reader, NOT the canonical firing-block reader the decision needs. -/
def pushoutFactorizeTotal :
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode} →
    (cell : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath) →
    PushoutLayoutFactorization crossPairRealPushoutRel cell
  | _, _, .id path => pushoutFactorizeId crossPairRealPushoutRel path
  | _, _, .gen g => pushoutFactorizeGen crossPairRealPushoutRel g
  | _, _, .vcomp cellUpper cellLower =>
      pushoutFactorizeVcompSingleGap crossPairRealPushoutRel cellUpper cellLower
  | _, _, @RawTwoCellExpr.whiskerLeft _ _ middleMode _ oneCell _ _ body => by
      obtain rfl := pushoutModeUnique middleMode
      exact pushoutFactorizeWhiskerLeftGap crossPairRealPushoutRel oneCell body
  | _, _, @RawTwoCellExpr.whiskerRight _ _ middleMode _ _ _ oneCell body => by
      obtain rfl := pushoutModeUnique middleMode
      exact pushoutFactorizeWhiskerRightGap crossPairRealPushoutRel oneCell body

/-- ★ **The total reader on a `gen` produces a SINGLE slot** — `pushoutFactorizeTotal (gen mu)` has exactly one gap
(`pairs.length = 1`): the atomic firing occupies one slot, the base observability of the reader. -/
theorem pushoutFactorizeTotal_gen_slotCount :
    (pushoutFactorizeTotal (RawTwoCellExpr.gen pushoutMonadMult)).pairs.length = 1 := rfl

/-- ★ **The total reader on a `vcomp` produces a SINGLE shared slot** — `pushoutFactorizeTotal (vcomp eta delta_1)`
has exactly one gap: the two halves share the gap's vertical split (SHALLOW — not re-sliced per firing region). -/
theorem pushoutFactorizeTotal_vcomp_slotCount :
    (pushoutFactorizeTotal (RawTwoCellExpr.vcomp pushoutEta pushoutFaceDeltaOne)).pairs.length = 1 := rfl

/-! ## The two-sided decision — both verdicts on concrete pairs, with extraction -/

/-- ★★ **The two-sided per-gap decision DECIDES both verdicts on concrete pairs.**  Extracting
`pushoutRightImageTwoSidedDecision` (the shipped genuine `Decidable`): `true` on the associativity foldings'
right-images (a genuinely-different convertible pair) and `false` on the two monad faces' right-images (the
separating δ₁ / δ₀).  The per-gap decision the canonical reader WOULD feed. -/
theorem pushoutDecisionBothVerdicts :
    pushoutRightImageDecidesTwoSided reconAssocLeftCell reconAssocRightCell = true
      ∧ pushoutRightImageDecidesTwoSided reconFaceDeltaOne reconFaceDeltaZero = false :=
  ⟨pushoutRightImageDecidesTwoSided_assoc, pushoutRightImageDecidesTwoSided_faces⟩

/-! ## The purification adjudication -/

/-- ★★ **Purification STAYS OPEN even with the total reader shipped (recon §4).**  The total EXISTENCE reader
`pushoutFactorizeTotal` gives cell-level projection (essential-surjectivity, via the shipped wall-free round-trip) but
NOT derivation-level purification: that needs the NF reflection (conv-of-images ⟹ equal-layouts), which a SHALLOW
existence reader does not supply (its layouts are not canonical normal forms).  So `fxAmalg_hasSaturatedDispatchTheorem`
STAYS `false` — machine-checked `rfl`. -/
theorem pushoutPurificationStaysOpenWithTotalReader :
    fxAmalg_hasSaturatedDispatchTheorem = false := rfl

/-- ★★ **The top factorization induction STAYS WALLED even with the total reader shipped.**  The named node is the
CANONICAL firing-block reader + decider wiring, NOT mere existence; the shallow `pushoutFactorizeTotal` does not
discharge it.  `fxAmalg_topFactorizationInductionStaysWalled = true` — machine-checked `rfl`. -/
theorem pushoutTopInductionStaysWalledWithTotalReader :
    fxAmalg_topFactorizationInductionStaysWalled = true := rfl

/-! ## Observability -/

-- The total reader's slot count on a `gen` (expect `1`) and on a `vcomp` (expect `1`) — shallow one-level layouts.
#eval (pushoutFactorizeTotal (RawTwoCellExpr.gen pushoutMonadMult)).pairs.length
#eval (pushoutFactorizeTotal (RawTwoCellExpr.vcomp pushoutEta pushoutFaceDeltaOne)).pairs.length
-- The two-sided decision: `true` on the assoc foldings, `false` on the faces.
#eval pushoutRightImageDecidesTwoSided reconAssocLeftCell reconAssocRightCell
#eval pushoutRightImageDecidesTwoSided reconFaceDeltaOne reconFaceDeltaZero

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the TOTAL (existence) factorization reader SHIPS; it is SHALLOW, not canonical; the decision
+ purification adjudicated; #2043 does NOT close (WP-AMALG-2 r15, B4).**  `= true`.  `pushoutFactorizeTotal` is a
TOTAL zero-axiom function `∀ cell, PushoutLayoutFactorization crossPairRealPushoutRel cell` — every pushout 2-cell
factors into a wall/gap layout, assembled by a plain 5-way match (no recursion, no fuel; the whisker arms mode-pinned
by `pushoutModeUnique`).  This SETTLES EXISTENCE (self-attacks 5b/5c).  It is the SHALLOW one-level reader
(`pushoutFactorizeTotal_gen_slotCount` / `_vcomp_slotCount`: one slot each — the subterm sits undivided), NOT the
CANONICAL firing-block reader: it does not re-slice gaps to per-firing-region granularity, so it does not feed the
arbitrary-pair decision nor supply the NF reflection.

The two-sided per-gap decision DECIDES both verdicts on concrete pairs with extraction (`pushoutDecisionBothVerdicts`:
`true` on the assoc foldings, `false` on the faces).  The purification adjudication (recon §4): the total EXISTENCE
reader gives cell-level projection but NOT derivation-level purification (the NF reflection), so
`fxAmalg_hasSaturatedDispatchTheorem` STAYS `false` (`pushoutPurificationStaysOpenWithTotalReader`).

FLIPPED NO master: the wall is CANONICALITY, not existence.  `fxAmalg_topFactorizationInductionStaysWalled` STAYS
`true` (`pushoutTopInductionStaysWalledWithTotalReader`); `fxAmalg_hasFullSaturatedPushoutDispatch` /
`fxAmalg_hasGeneralPushoutDispatch` STAY `false`.  #2043 does NOT close.  No fabricated flip.  `= true`. -/
def fxAmalg_totalFactorizeReaderShips : Bool := true

end FX1Poly.Polygraph.Amalgam

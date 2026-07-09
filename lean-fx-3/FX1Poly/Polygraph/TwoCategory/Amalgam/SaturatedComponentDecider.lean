import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedOver
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadFullNormalizer

/-! # Polygraph/TwoCategory/Amalgam/SaturatedComponentDecider — the REAL-relation saturated component decider
(WP-AMALG r3, piece 2a)

`SaturatedOver.lean` shipped the generic saturated congruence + the empty-relation (thin) decider.  A thin
decider covers only the no-2-generator fragment — a component contributing NO generating 2-cell, hence NO laws.
This file ships the FIRST GENUINE real-relation instance of `DecidableSaturatedConvForRel`: a decider of the
generic saturated conv over a NON-EMPTY law relation (the four walking-idempotent-monad laws), UNCONDITIONAL and
zero-axiom.

## Why the idempotent monad, and why unconditional (correcting the recon)

The recon ranked the idempotent monad the cheapest real instance but flagged it "conditional on an uninhabited
posetality residual".  That estimate was STALE: `WalkingIdempotent/IdempotentMonadFullNormalizer` ships
`idempotentLocalPosetality` as a REAL closed term (zero hypotheses, via the boundary-determined normalizer
`normalizeFull`) and hence `decideIdempotentConv : IdempotentMonadDecidableSaturatedTwoCellConvFor` as a TOTAL
zero-axiom decision (both machine-verified axiom-free in the audit twin).  The walking idempotent monad is
locally posetal (Lack, *A 2-Categories Companion* §1.5): every hom is a poset, so its saturated conv is decided
`isTrue` on every parallel pair — a genuine decider of a genuine NON-EMPTY relation (the idempotence law does
real work, not only the free structure).

Crucially the idempotent decision lives NATIVELY over `monadModeSignature` (the same signature the generic uses),
so no ModeComputad-carrier transport is needed — sidestepping the carrier-mismatch wall the recon flagged for the
adjunction.  The only bridge required is the iso `IdempotentMonadSaturatedTwoCellConv a b <-> SaturatedConvOver
monadModeSignature IdempotentLawRel a b`, along which the decision transports.

## What ships here (each piece zero-axiom, structural, ASCII-only)

  * **`IdempotentLawRel`** — the four walking-idempotent-monad laws as a `CellRel` (three monad laws + idempotence).
  * **`idempotentSaturated_to_generic`** / **`generic_to_idempotentSaturated`** / **`idempotentSaturated_iff_generic`**
    — the two-way iso, the forward direction by induction on the walker conv (the two-level `ofMonad` nesting
    flattened by the `monadSaturated_to_genericIdempotent` helper), the backward direction by the universal
    property `recInto` with the idempotent absorbing congruence.
  * **`decideSaturatedConvOverIdempotent`** — the REAL, UNCONDITIONAL decider: `decideIdempotentConv` transported
    along the iso.  A genuine `DecidableSaturatedConvForRel monadModeSignature IdempotentLawRel`.
  * **`idempotenceRowConv`** + **`idempotentGenericDecidesTrue_smoke`** — non-vacuity: a real law row fires
    directly (`ofRelation IdempotentLawRel.idempotence`), and the transported decider `#eval`s a genuine size-4
    parallel pair to `true`.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The four walking-idempotent-monad laws as a `CellRel` -/

/-- The **walking idempotent monad's four laws as a `CellRel`** — the three monad laws (left unit, right unit,
associativity) plus the idempotence law `eta |> t ~ t <| eta`.  The base relation for which
`SaturatedConvOver monadModeSignature IdempotentLawRel = IdempotentMonadSaturatedTwoCellConv` (proven below). -/
inductive IdempotentLawRel :
    {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    RawTwoCellExpr monadModeSignature sourcePath targetPath →
    RawTwoCellExpr monadModeSignature sourcePath targetPath → Prop where
  /-- The left-unit law `mu . (eta |> t) ~ id_t`. -/
  | leftUnit : IdempotentLawRel monadLeftUnitCell monadIdTCell
  /-- The right-unit law `mu . (t <| eta) ~ id_t`. -/
  | rightUnit : IdempotentLawRel monadRightUnitCell monadIdTCell
  /-- The associativity law `mu . (mu |> t) ~ mu . (t <| mu)`. -/
  | assoc : IdempotentLawRel monadAssocLeftCell monadAssocRightCell
  /-- The idempotence law `eta |> t ~ t <| eta` (well-pointedness). -/
  | idempotence : IdempotentLawRel monadEtaTCell monadTEtaCell

/-! ## The iso: forward -/

/-- The walking monad's saturated conv maps into the generic at `IdempotentLawRel` (whose four rows contain the
three monad rows), by induction on the monad conv; the three laws land as `ofRelation`.  Flattens the `ofMonad`
nesting for the forward iso. -/
theorem monadSaturated_to_genericIdempotent {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : MonadSaturatedTwoCellConv cellAlpha cellBeta) :
    SaturatedConvOver monadModeSignature IdempotentLawRel cellAlpha cellBeta := by
  induction conv with
  | ofFull full => exact SaturatedConvOver.ofFull full
  | leftUnit => exact SaturatedConvOver.ofRelation IdempotentLawRel.leftUnit
  | rightUnit => exact SaturatedConvOver.ofRelation IdempotentLawRel.rightUnit
  | assoc => exact SaturatedConvOver.ofRelation IdempotentLawRel.assoc
  | vcompCongrLeft cellBeta _ ih => exact SaturatedConvOver.vcompCongrLeft cellBeta ih
  | vcompCongrRight cellAlpha _ ih => exact SaturatedConvOver.vcompCongrRight cellAlpha ih
  | whiskerLeftCongr oneCell _ ih => exact SaturatedConvOver.whiskerLeftCongr oneCell ih
  | whiskerRightCongr oneCell _ ih => exact SaturatedConvOver.whiskerRightCongr oneCell ih
  | refl cell => exact SaturatedConvOver.refl cell
  | symm _ ih => exact SaturatedConvOver.symm ih
  | trans _ _ ihLeft ihRight => exact SaturatedConvOver.trans ihLeft ihRight

/-- ★ Forward direction of the idempotent iso: the walking-idempotent-monad saturated conv maps into the generic
at `IdempotentLawRel`.  The `ofMonad` case flattens via the monad helper; `idempotence` lands as `ofRelation`. -/
theorem idempotentSaturated_to_generic {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : IdempotentMonadSaturatedTwoCellConv cellAlpha cellBeta) :
    SaturatedConvOver monadModeSignature IdempotentLawRel cellAlpha cellBeta := by
  induction conv with
  | ofMonad monadConv => exact monadSaturated_to_genericIdempotent monadConv
  | idempotence => exact SaturatedConvOver.ofRelation IdempotentLawRel.idempotence
  | vcompCongrLeft cellBeta _ ih => exact SaturatedConvOver.vcompCongrLeft cellBeta ih
  | vcompCongrRight cellAlpha _ ih => exact SaturatedConvOver.vcompCongrRight cellAlpha ih
  | whiskerLeftCongr oneCell _ ih => exact SaturatedConvOver.whiskerLeftCongr oneCell ih
  | whiskerRightCongr oneCell _ ih => exact SaturatedConvOver.whiskerRightCongr oneCell ih
  | refl cell => exact SaturatedConvOver.refl cell
  | symm _ ih => exact SaturatedConvOver.symm ih
  | trans _ _ ihLeft ihRight => exact SaturatedConvOver.trans ihLeft ihRight

/-! ## The iso: backward (via the universal property) -/

/-- The walking-idempotent-monad saturated conv absorbs the generic congruence at `IdempotentLawRel` — the
`ofRelation` field cases each of the four law rows into the matching idempotent-conv ctor (monad rows via
`ofMonad`, the fourth via `idempotence`); every other field is a same-named ctor.  The backward-direction witness
for `recInto`. -/
def idempotentIsCongruence :
    IsSaturatedCongruence monadModeSignature IdempotentLawRel
      (fun cellAlpha cellBeta => IdempotentMonadSaturatedTwoCellConv cellAlpha cellBeta) where
  ofFull full := IdempotentMonadSaturatedTwoCellConv.ofMonad (MonadSaturatedTwoCellConv.ofFull full)
  ofRelation row :=
    match row with
    | IdempotentLawRel.leftUnit =>
        IdempotentMonadSaturatedTwoCellConv.ofMonad MonadSaturatedTwoCellConv.leftUnit
    | IdempotentLawRel.rightUnit =>
        IdempotentMonadSaturatedTwoCellConv.ofMonad MonadSaturatedTwoCellConv.rightUnit
    | IdempotentLawRel.assoc =>
        IdempotentMonadSaturatedTwoCellConv.ofMonad MonadSaturatedTwoCellConv.assoc
    | IdempotentLawRel.idempotence => IdempotentMonadSaturatedTwoCellConv.idempotence
  vcompCongrLeft {_ _ _ _ _ _ _ cellBeta} ih :=
    IdempotentMonadSaturatedTwoCellConv.vcompCongrLeft cellBeta ih
  vcompCongrRight {_ _ _ _ _ cellAlpha _ _} ih :=
    IdempotentMonadSaturatedTwoCellConv.vcompCongrRight cellAlpha ih
  whiskerLeftCongr {_ _ _ oneCell _ _ _ _} ih :=
    IdempotentMonadSaturatedTwoCellConv.whiskerLeftCongr oneCell ih
  whiskerRightCongr {_ _ _ _ _ oneCell _ _} ih :=
    IdempotentMonadSaturatedTwoCellConv.whiskerRightCongr oneCell ih
  refl cell := IdempotentMonadSaturatedTwoCellConv.refl cell
  symm ih := IdempotentMonadSaturatedTwoCellConv.symm ih
  trans ihLeft ihRight := IdempotentMonadSaturatedTwoCellConv.trans ihLeft ihRight

/-- ★ Backward direction of the idempotent iso: the generic at `IdempotentLawRel` maps back into the
walking-idempotent-monad saturated conv (via the universal property `recInto`). -/
theorem generic_to_idempotentSaturated {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : SaturatedConvOver monadModeSignature IdempotentLawRel cellAlpha cellBeta) :
    IdempotentMonadSaturatedTwoCellConv cellAlpha cellBeta :=
  SaturatedConvOver.recInto idempotentIsCongruence conv

/-- ★ **The idempotent iso** — the walking-idempotent-monad saturated conv IS the generic saturated conv at its
four-law relation `IdempotentLawRel`.  Logically identical; the decision transports across it. -/
theorem idempotentSaturated_iff_generic {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    IdempotentMonadSaturatedTwoCellConv cellAlpha cellBeta
      ↔ SaturatedConvOver monadModeSignature IdempotentLawRel cellAlpha cellBeta :=
  ⟨idempotentSaturated_to_generic, generic_to_idempotentSaturated⟩

/-! ## The REAL-relation decider — the idempotent decision transported along the iso -/

/-- ★★ **The REAL-relation saturated decider** — the FIRST genuine `DecidableSaturatedConvForRel` over a
NON-EMPTY law relation: `decideIdempotentConv` (the total zero-axiom walking-idempotent-monad decision)
transported along the iso `idempotentSaturated_iff_generic`.  UNCONDITIONAL (no posetality hypothesis — local
posetality is a shipped closed term) and zero-axiom.  Decides `SaturatedConvOver monadModeSignature
IdempotentLawRel` on every parallel pair. -/
def decideSaturatedConvOverIdempotent :
    DecidableSaturatedConvForRel monadModeSignature IdempotentLawRel :=
  fun cellAlpha cellBeta =>
    match decideIdempotentConv cellAlpha cellBeta with
    | isTrue idempotentConv => isTrue (idempotentSaturated_to_generic idempotentConv)
    | isFalse notIdempotentConv =>
        isFalse (fun genericConv => notIdempotentConv (generic_to_idempotentSaturated genericConv))

/-! ## Non-vacuity -/

/-- A real law row fires directly — the idempotence law `eta |> t ~ t <| eta` holds in the generic saturated conv
via `ofRelation IdempotentLawRel.idempotence` (NOT derivable from the free structure or the monad laws alone), so
the base relation is genuinely non-empty and idempotence does real work. -/
theorem idempotenceRowConv :
    SaturatedConvOver monadModeSignature IdempotentLawRel monadEtaTCell monadTEtaCell :=
  SaturatedConvOver.ofRelation IdempotentLawRel.idempotence

/-- The transported decider on a GENUINE size-4 parallel pair — `mu . (eta |> t)` (`vcomp mu (eta |> t)`) and its
`t <| eta` twin — read off as a `Bool`.  Expect `true`: the pair is decided saturated-convertible by the real
decider, non-vacuously (the walker's own smoke `idempotentDecidesTrue_smoke` is transported). -/
def idempotentGenericDecidesTrue_smoke : Bool :=
  match decideSaturatedConvOverIdempotent (RawTwoCellExpr.vcomp monadMulTwoCell monadEtaTCell)
      (RawTwoCellExpr.vcomp monadMulTwoCell monadTEtaCell) with
  | isTrue _ => true
  | isFalse _ => false

/-- Smoke value: the real decider returns `true` on the genuine size-4 parallel pair (non-vacuous, by `rfl`). -/
theorem idempotentGenericDecidesTrue_smoke_holds : idempotentGenericDecidesTrue_smoke = true := rfl

-- The real-relation saturated decision on the size-4 pair: expect `true`.
#eval idempotentGenericDecidesTrue_smoke

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — the REAL-relation saturated component decider SHIPS, UNCONDITIONAL (r3 piece 2a).**  The
four walking-idempotent-monad laws as a `CellRel` (`IdempotentLawRel`), the two-way iso
(`idempotentSaturated_iff_generic`: forward by induction on the walker conv flattening the `ofMonad` nesting,
backward by the universal property `recInto`), and the decision transport `decideSaturatedConvOverIdempotent` — a
genuine `DecidableSaturatedConvForRel monadModeSignature IdempotentLawRel` over a NON-EMPTY relation, with NO
open premise (local posetality is the shipped closed term `idempotentLocalPosetality`, machine-verified
axiom-free).  Corrects the recon's stale "uninhabited posetality" estimate.  Non-vacuous: `idempotenceRowConv`
fires the real idempotence row directly and `idempotentGenericDecidesTrue_smoke` decides a genuine size-4 pair
`true`.  `= true`. -/
def fxAmalg_hasSaturatedComponentDecider : Bool := true

end FX1Poly.Polygraph.Amalgam

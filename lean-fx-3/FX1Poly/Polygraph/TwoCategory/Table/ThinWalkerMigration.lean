import FX1Poly.Polygraph.TwoCategory.Table.WalkerMigration
import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedRelationFamily

/-! # Polygraph/TwoCategory/Table/ThinWalkerMigration — the thin-class walker migrations as table VALUES
(POLY-TAB r1, P3)

`Table/WalkerMigration.lean` (r0, T4) demonstrated the RETIREMENT bridge at the smallest law count — a one-row
bespoke walker proved logically identical to the generic `SaturatedConvOver`.  This file promotes the SHIPPED
thin-class walkers to that same pattern as table VALUES: the walking IDEMPOTENT monad and the walking INVOLUTION,
each carried by its `SaturatedRelationFamily` (`Amalgam/SaturatedRelationFamily.lean`), with the two-way bridge iff
to its bespoke congruence RE-EXPOSED at the Table layer, and a REGRESSION verdict on one concrete pair confirming
the bespoke decider and the family-generic route agree.  The walking MONAD is included as the SEPARATING precedent.

## The two directions over the SAME base relation (the r0 pattern)

Each walker's bridge is `walkerConv a b <-> SaturatedConvOver signature baseRel a b`, over the SAME `baseRel` both
ways — exactly `frobeniusSpecialWalker_iff_generic`'s shape at r0, but for the shipped walkers:

  * **Walking idempotent monad** (`baseRel = IdempotentLawRel`, four laws over `monadModeSignature`): the bespoke
    `IdempotentMonadSaturatedTwoCellConv` bridges to the generic via `idempotentSaturated_iff_generic` — a genuine
    RETIREMENT bridge (the bespoke inductive exists, the iff logically identifies it with the generic).
  * **Walking involution** (`baseRel = emptyCellRel`, thin/no-2-generator over `involutionComputad.toModeSignature`):
    BORN GENERIC — its family's `walkerConv` IS the generic carrier itself, so the bridge is `Iff.rfl` (nothing to
    retire, the identity migration, as `Table/FrobeniusSeed`'s spider is born generic).
  * **Walking monad** (`baseRel = MonadLawRel`, three laws): the SEPARATING precedent — its bridge
    `monadSaturated_iff_generic` IS the family's `walkerIffGeneric` field directly (`= by rfl`), the interface field
    the brick names.

## The regression verdicts (bespoke route = generic route, one concrete pair per walker)

The full-hom DEFINITIONAL agreement `family.decider = shippedDecider` is already proved in
`SaturatedRelationFamily.lean` (`idempotentRelationFamily_decider_eq_shipped` /
`involutionRelationFamily_decider_eq_thin` / `monadRelationFamily_decider_eq_walker`).  This file adds the CONCRETE
regression: on one sample pair per walker, running BOTH the bespoke decider and the family-generic `.decider` and
checking they return the SAME verdict — `true` by `rfl`, all four `Decidable`-outcome cases enumerated (no wildcard,
propext-free per the match recipe).  The monad's sample is a SEPARATING pair (the two unit faces), so its agreement
witnesses the `isFalse` verdict transports too, not merely `isTrue`.

## KZ banked (the walking lax-idempotent monad is NOT cheap)

The lock's deletion-target list flags `KZTwoCellLE` as "needs an oriented / preorder-valued base relation"
(`DesignLock.lean` decision 1).  The generic `SaturatedConvOver` carrier is SYMMETRIC (it has `symm`); the walking
KZ monad's `KZTwoCellLE` is a DIRECTED preorder (`t <| eta => eta |> t`, `WalkingKZ/KZMonadPresentation.lean`).
A born-generic KZ migration would need the symmetric CLOSURE `kzEq` (via `KZMonadDecision.kzEq_iff_mapEq`) as the
walker conv, and a proof that the symmetric closure's generic carrier agrees with the directed decision — genuine
POLY-TAB-2 design work (a directed base relation the symmetric fold does not model), NOT a mechanical re-exposure.
So KZ is banked, marked honestly `false`, and left to POLY-TAB-2.

Raw Lean 4 + Init; every declaration is a re-exposed bridge or a concrete-pair regression closed by `rfl`, so it is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Additive: nothing in `Amalgam/` or the
walker lanes is edited (the bridges and families are cited, not re-proved).  Per-declaration `#assert_no_axioms` in
the audit twin. -/

namespace FX1Poly.Polygraph

open FX1Poly.Polygraph.Amalgam

/-! ## Migration ONE — the walking idempotent monad (a genuine retirement bridge) -/

/-- ★ **The walking-idempotent-monad migration, re-exposed at the Table layer** — BORN GENERIC (POLY-TAB r5): after
the bespoke `IdempotentMonadSaturatedTwoCellConv` lane's RETIREMENT, the family's `walkerConv` IS the generic
saturated carrier `SaturatedConvOver monadModeSignature IdempotentLawRel` itself, so the migration bridge is
`Iff.rfl` — the identity migration, exactly as the walking involution's.  The retirement executed: the once-genuine
retirement bridge collapsed to the born-generic shape, its decision content preserved in the native
`IdempotentSaturated*` lane. -/
theorem idempotentWalker_iff_generic {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    SaturatedConvOver monadModeSignature IdempotentLawRel cellAlpha cellBeta
      ↔ SaturatedConvOver monadModeSignature IdempotentLawRel cellAlpha cellBeta :=
  Iff.rfl

/-- ★ **Regression ONE — the family-generic and the native route AGREE on the idempotent sample pair.**  Runs the
family-generic `idempotentRelationFamily.decider` and the shipped native `decideSaturatedConvOverIdempotentNative`
on the size-4 pair `mu . (eta |> t)` vs `mu . (t <| eta)` (convertible in the idempotent hom — it is posetal) and
checks they return the same verdict.  Post-retirement (POLY-TAB r5) the family decider IS the native decider, so
this is a native-vs-native self-consistency check.  All four `Decidable`-outcome cases enumerated (propext-free). -/
def idempotentRouteAgreement : Bool :=
  match idempotentRelationFamily.decider (RawTwoCellExpr.vcomp monadMulTwoCell monadEtaTCell)
          (RawTwoCellExpr.vcomp monadMulTwoCell monadTEtaCell),
        decideSaturatedConvOverIdempotentNative (RawTwoCellExpr.vcomp monadMulTwoCell monadEtaTCell)
          (RawTwoCellExpr.vcomp monadMulTwoCell monadTEtaCell) with
  | isTrue _, isTrue _ => true
  | isTrue _, isFalse _ => false
  | isFalse _, isTrue _ => false
  | isFalse _, isFalse _ => true

/-- ★ The idempotent route agreement COMPUTES to `true` by `rfl` — bespoke and generic decide the sample identically
(both `isTrue`). -/
theorem idempotentRouteAgreement_holds : idempotentRouteAgreement = true := rfl

/-! ## Migration TWO — the walking involution (born generic, the identity migration) -/

/-- ★ **The walking-involution migration bridge, re-exposed** — BORN GENERIC: the family's `walkerConv` IS the
generic saturated carrier at the empty law relation, so the bridge is `Iff.rfl`.  There is no bespoke inductive to
retire; the migration is the identity, exactly as `Table/FrobeniusSeed`'s spider is born generic. -/
theorem involutionWalker_iff_generic {sourceMode targetMode : involutionComputad.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath involutionComputad.toModeSignature.graph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr involutionComputad.toModeSignature sourcePath targetPath) :
    SaturatedConvOver involutionComputad.toModeSignature
        (emptyCellRel involutionComputad.toModeSignature) cellAlpha cellBeta
      ↔ SaturatedConvOver involutionComputad.toModeSignature
        (emptyCellRel involutionComputad.toModeSignature) cellAlpha cellBeta :=
  Iff.rfl

/-- ★ **Regression TWO — the bespoke thin and the generic route AGREE on the involution sample pair.**  Runs the
shipped `involutionSaturatedThinDecider` and the family-generic `involutionRelationFamily.decider` on the reflexive
identity pair and checks they agree (both `isTrue`, thin: every parallel pair is convertible). -/
def involutionRouteAgreement : Bool :=
  match involutionRelationFamily.decider involutionIdentityCell involutionIdentityCell,
        involutionSaturatedThinDecider involutionIdentityCell involutionIdentityCell with
  | isTrue _, isTrue _ => true
  | isTrue _, isFalse _ => false
  | isFalse _, isTrue _ => false
  | isFalse _, isFalse _ => true

/-- ★ The involution route agreement COMPUTES to `true` by `rfl`. -/
theorem involutionRouteAgreement_holds : involutionRouteAgreement = true := rfl

/-! ## The precedent — the walking monad's bridge IS the family's `walkerIffGeneric` field -/

/-- ★ **The monad precedent, formalized as the family's interface field.**  The brick's "formalize
`monadSaturated_iff_generic` as a `SaturatedRelationFamily` instance if the interface field admits it directly": it
DOES — `monadRelationFamily.walkerIffGeneric` IS `monadSaturated_iff_generic` by `rfl`.  So the monad is already a
family instance whose bridge field is precisely the shipped precedent. -/
theorem monadRelationFamily_bridge_is_precedent {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    monadRelationFamily.walkerIffGeneric cellAlpha cellBeta = monadSaturated_iff_generic cellAlpha cellBeta :=
  rfl

/-- ★ **Regression THREE — the bespoke and the generic route AGREE on the monad SEPARATING sample pair.**  The two
unit faces `t <| eta` (`whiskerRight`) vs `eta |> t` (`whiskerLeft`) are distinct monotone maps; the shipped
`monadWalkerSaturatedDecider` and the family-generic `monadRelationFamily.decider` BOTH decide them `isFalse` —
agreement on a SEPARATING verdict, so the regression witnesses `isFalse` transport, not merely `isTrue`. -/
def monadSeparatingRouteAgreement : Bool :=
  match monadRelationFamily.decider
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell),
        monadWalkerSaturatedDecider
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell) with
  | isTrue _, isTrue _ => false
  | isTrue _, isFalse _ => false
  | isFalse _, isTrue _ => false
  | isFalse _, isFalse _ => true

/-- ★ The monad separating route agreement COMPUTES to `true` by `rfl` — both routes decide the unit faces
`isFalse`. -/
theorem monadSeparatingRouteAgreement_holds : monadSeparatingRouteAgreement = true := rfl

/-! ## Observability -/

-- The idempotent route agreement (bespoke vs generic on the size-4 pair): expect `true`.
#eval idempotentRouteAgreement
-- The involution route agreement (thin vs generic on the identity pair): expect `true`.
#eval involutionRouteAgreement
-- The monad separating route agreement (both isFalse on the unit faces): expect `true`.
#eval monadSeparatingRouteAgreement

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the thin-class walker migrations SHIP as table values (POLY-TAB r1, P3).**  The walking
idempotent monad (`idempotentWalker_iff_generic`, born generic over `IdempotentLawRel` post-retirement — `Iff.rfl`) and the
walking involution (`involutionWalker_iff_generic`, born generic over `emptyCellRel`, `Iff.rfl`) are surfaced as
Table migration values with the two-way bridge iff over the SAME base relation, plus the monad SEPARATING precedent
(`monadRelationFamily_bridge_is_precedent`: `monadSaturated_iff_generic` IS the family's `walkerIffGeneric` field).
Each carries a CONCRETE regression verdict confirming the bespoke decider and the family-generic route agree on one
sample pair (`idempotentRouteAgreement_holds` / `involutionRouteAgreement_holds` /
`monadSeparatingRouteAgreement_holds`, the last on a separating `isFalse` pair), on top of the shipped full-hom
definitional agreements.  `= true`. -/
def fxTab_hasThinClassWalkerMigrations : Bool := true

/-- ★ **Honesty marker (`false`) — the walking KZ monad migration is NOT shipped (banked to POLY-TAB-2).**  The
generic `SaturatedConvOver` carrier is symmetric; the walking lax-idempotent (KZ) monad's `KZTwoCellLE` is a
DIRECTED preorder (`t <| eta => eta |> t`).  A born-generic migration needs the symmetric closure `kzEq` as the
walker conv and a proof it agrees with the directed decision over a preorder-valued base relation the symmetric
fold does not model — genuine POLY-TAB-2 design work (the lock's decision 1 flags KZ as "needs an oriented /
preorder-valued base relation"), not a mechanical re-exposure like the two thin-class walkers above.  `= false`.

  UPDATE (POLY-TAB r7 r1): the WalkingKZ lane's `KZTwoCellLE.ofMonad` field is now re-pointed onto the generic
  `MonadSaturatedConvGen` carrier (`fxTab_hasKZMonadConvGenericRepoint`, below), severing the KZ lane's dependency
  on the bespoke monad conv at the PROOF level.  This marker STAYS `false` regardless: that re-point migrates only
  the SYMMETRIC monad-law embedding; the directed `KZTwoCellLE` preorder (its `kzGen` generator) is native
  by-design, NOT a bespoke-conv migration target, so the full walker-onto-generic migration remains unshipped. -/
def fxTab_hasKZWalkerMigration : Bool := false

/-- ★ **Honesty marker (`true`) — the WalkingKZ lane's monad-conv embedding is re-pointed born-generic (POLY-TAB r7
r1).**  `KZTwoCellLE.ofMonad` (the sole structural entry of a monad EQUALITY of 2-cells into the directed KZ order)
now stores `MonadSaturatedConvGen := SaturatedConvOver monadModeSignature MonadLawRel` instead of the bespoke
`MonadSaturatedTwoCellConv`, and every KZ consumption site (`kzLeftUnitEq`, the covering producers via
`wordMul_hcompGen`, `kzLE_sound`'s `ofMonad` case via `monadMonotoneMapOf_mapEqOfConvGen`, `kzLE_ofMapEq` /
`kzEq_iff_mapEq` via `monadConvOfMapEqGen_ofNormalizeGen monadNormalizeGen`) swapped bespoke→generic uniformly.  The
KZ deciders (`decideKZEq`, `decideKZLETotal`, `kz_strict`, `kzBaseCovering_isStrict`) are conv-independent and survive
UNCHANGED (the green build is the continuity tie).  This is the proof-level severance of the r7 KZ hard blocker; the
full DIRECTED walker migration (`fxTab_hasKZWalkerMigration`) stays `false` — the generic carrier is symmetric.
`= true`. -/
def fxTab_hasKZMonadConvGenericRepoint : Bool := true

end FX1Poly.Polygraph

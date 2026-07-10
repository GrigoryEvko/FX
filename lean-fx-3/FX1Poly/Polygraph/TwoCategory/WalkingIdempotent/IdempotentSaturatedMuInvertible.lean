import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentLawRelation
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedReps

/-! # WalkingIdempotent/IdempotentSaturatedMuInvertible — the mu-invertibility crux, GENERIC-NATIVE

This file re-founds the walking-idempotent-monad thinness crux DIRECTLY over the GENERIC saturated carrier
`SaturatedConvOver monadModeSignature IdempotentLawRel`, using ONLY the generic constructors — never the bespoke
`IdempotentMonadSaturatedTwoCellConv`.  It mirrors `IdempotentMonadMuInvertible` arm-for-arm (the ctor
correspondence: the four congruences / `refl` / `symm` / `trans` are the same-named `SaturatedConvOver` ctors;
`ofMonad (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep _))` becomes `SaturatedConvOver.ofConv
(TwoCellConv.ofStep _)`; `ofMonad (… .ofFull _)` becomes `SaturatedConvOver.ofFull _`; each monad law
`ofMonad MonadSaturatedTwoCellConv.leftUnit`/… becomes `ofRelation IdempotentLawRel.leftUnit`/…; and the
idempotence generator `idempotence` becomes `ofRelation IdempotentLawRel.idempotence`).

The conv-FREE representatives (`mulThenUnitRightWhisker`, `godementUnitMul`, and all the `t`-power boundary defs)
are REUSED verbatim from the bespoke lane — they never mention the convertibility relation, only `RawTwoCellExpr`.
Only the conv-PRODUCING theorems are re-proved here over the generic carrier, so the resulting local-posetality
term (built downstream) has NO `IdempotentMonadSaturatedTwoCellConv` in its provenance chain.

Raw Lean 4 + Init; every proof BUILDS conv values (never destructs one), so it is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph
open SaturatedConvOver

/-! ## The generic moves — the free-system lifts + the four law generators -/

/-- Lift a single strict-2-category rewrite step (`TwoCellStep`) into the GENERIC saturated conv over
`IdempotentLawRel` (through `ofConv`/`ofFull`).  The generic-native analog of `idempotentConvOfStep`. -/
theorem idemStep {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (step : TwoCellStep monadModeSignature cellAlpha cellBeta) :
    SaturatedConvOver monadModeSignature IdempotentLawRel cellAlpha cellBeta :=
  SaturatedConvOver.ofConv (TwoCellConv.ofStep step)

/-- Lift a completed free-strict-2-category convertibility (`TwoCellConvFull`) into the generic saturated conv.
The generic-native analog of `idempotentConvOfFull`. -/
theorem idemFull {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (convFull : TwoCellConvFull monadModeSignature cellAlpha cellBeta) :
    SaturatedConvOver monadModeSignature IdempotentLawRel cellAlpha cellBeta :=
  SaturatedConvOver.ofFull convFull

/-- The LEFT-unit monad law as a generic saturated conv row. -/
theorem idemLeftUnitLaw :
    SaturatedConvOver monadModeSignature IdempotentLawRel monadLeftUnitCell monadIdTCell :=
  SaturatedConvOver.ofRelation IdempotentLawRel.leftUnit

/-- The RIGHT-unit monad law as a generic saturated conv row. -/
theorem idemRightUnitLaw :
    SaturatedConvOver monadModeSignature IdempotentLawRel monadRightUnitCell monadIdTCell :=
  SaturatedConvOver.ofRelation IdempotentLawRel.rightUnit

/-- The associativity monad law as a generic saturated conv row. -/
theorem idemAssocLaw :
    SaturatedConvOver monadModeSignature IdempotentLawRel monadAssocLeftCell monadAssocRightCell :=
  SaturatedConvOver.ofRelation IdempotentLawRel.assoc

/-- The idempotence law `eta |> t ~ t <| eta` as a generic saturated conv row (the sole idempotence input). -/
theorem idemIdempotenceLaw :
    SaturatedConvOver monadModeSignature IdempotentLawRel monadEtaTCell monadTEtaCell :=
  SaturatedConvOver.ofRelation IdempotentLawRel.idempotence

/-! ## The mu-invertibility crux, generic-native -/

/-- **Naturality of `eta` at `mu`** — `mu . (eta |> t) ~ eta (X) mu`, generic-native (pure interchange, no
idempotence).  Mirrors `mulThenUnitRightWhisker_conv_godement`. -/
theorem mulThenUnitRightWhisker_conv_godement_gen :
    SaturatedConvOver monadModeSignature IdempotentLawRel mulThenUnitRightWhisker godementUnitMul := by
  unfold mulThenUnitRightWhisker godementUnitMul
  have interchangeStep := idemStep (TwoCellStep.interchange (signature := monadModeSignature)
    (cellAlpha := RawTwoCellExpr.id (ModalityPath.nil (graph := monadGraph) MonadMode.point))
    (cellAlphaUpper := monadUnitTwoCell)
    (cellBeta := monadMulTwoCell)
    (cellBetaUpper := RawTwoCellExpr.id (signature := monadModeSignature) monadT))
  dsimp only [RawTwoCellExpr.hcomp] at interchangeStep ⊢
  refine trans ?_ (trans (symm interchangeStep) ?_)
  · refine trans (vcompCongrLeft _ ?_) (vcompCongrRight _ ?_)
    · exact symm (trans (vcompCongrLeft _ (idemStep (TwoCellStep.whiskerRightId _ _)))
        (trans (vcompCongrRight _ (idemFull (TwoCellConvFull.whiskerLeftUnit monadMulTwoCell)))
          (idemStep (TwoCellStep.vcompIdLeft monadMulTwoCell))))
    · exact symm (trans
        (vcompCongrRight _
          (idemStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT monadT)))
        (idemStep (TwoCellStep.vcompIdRight
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell))))
  · refine trans (vcompCongrLeft _ (whiskerRightCongr _ ?_)) (vcompCongrRight _ (whiskerLeftCongr _ ?_))
    · exact idemStep (TwoCellStep.vcompIdLeft monadUnitTwoCell)
    · exact idemStep (TwoCellStep.vcompIdRight monadMulTwoCell)

/-- **Well-pointedness whiskered** — `eta |> t.t ~ t <| (eta |> t)`, generic-native (the sole idempotence use).
Mirrors `unitRightWhiskerSquare_conv_unitLeftWhisker`. -/
theorem unitRightWhiskerSquare_conv_unitLeftWhisker_gen :
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadTThenT monadUnitTwoCell)
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadEtaTCell) := by
  have whiskerSplit :=
    idemFull (TwoCellConvFull.whiskerRightComp (signature := monadModeSignature)
      monadT monadT monadUnitTwoCell)
  have whiskerCommute :=
    idemFull (TwoCellConvFull.whiskerExchange (signature := monadModeSignature)
      monadT monadT monadUnitTwoCell)
  exact trans whiskerSplit (trans (whiskerRightCongr _ idemIdempotenceLaw) (symm whiskerCommute))

/-- **The Godement composite collapses** — `eta (X) mu ~ id_{t.t}`, generic-native.  Mirrors
`godementUnitMul_conv_identity`. -/
theorem godementUnitMul_conv_identity_gen :
    SaturatedConvOver monadModeSignature IdempotentLawRel godementUnitMul
      (RawTwoCellExpr.id (signature := monadModeSignature) monadTThenT) := by
  unfold godementUnitMul
  dsimp only [RawTwoCellExpr.hcomp]
  refine trans (vcompCongrLeft _ unitRightWhiskerSquare_conv_unitLeftWhisker_gen) ?_
  refine trans (symm (idemStep
    (TwoCellStep.whiskerLeftVcomp monadT monadEtaTCell monadMulTwoCell))) ?_
  refine trans (whiskerLeftCongr _ idemLeftUnitLaw) ?_
  exact idemStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT monadT)

/-- ★★ **The multiplication's RIGHT inverse** — `mu . (eta |> t) ~ id_{t.t}`, generic-native.  Mirrors
`idempotentMulRightInverse`. -/
theorem idempotentMulRightInverse_gen :
    SaturatedConvOver monadModeSignature IdempotentLawRel mulThenUnitRightWhisker
      (RawTwoCellExpr.id (signature := monadModeSignature) monadTThenT) :=
  trans mulThenUnitRightWhisker_conv_godement_gen godementUnitMul_conv_identity_gen

/-- The multiplication's right inverse in the `t <| eta` presentation — `mu . (t <| eta) ~ id_{t.t}`,
generic-native.  Mirrors `idempotentMulRightInverse_leftWhisker`. -/
theorem idempotentMulRightInverse_leftWhisker_gen :
    SaturatedConvOver monadModeSignature IdempotentLawRel
      (RawTwoCellExpr.vcomp monadMulTwoCell monadTEtaCell)
      (RawTwoCellExpr.id (signature := monadModeSignature) monadTThenT) :=
  trans (vcompCongrRight monadMulTwoCell (symm idemIdempotenceLaw)) idempotentMulRightInverse_gen

end FX1Poly.Polygraph.Amalgam

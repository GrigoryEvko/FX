import LeanFX2.Reduction.ParRed.ParInductive.Inductive
import LeanFX2.Term.Inversion

/-! # LeanFX2.Term.PreservesTerm.EliminatorCubicalFamily

Cong-only lift theorem for the path-shaped homogeneous composition
eliminator `Term.hcompPath` — the one cubical cong lift that the
B.2e family did not yet cover.

* `lift_hcompPath_cong` — path-typed-sides hcomp (`Term.hcompPath`).

Takes raw parallel-reduction steps on the path-typed `sidesPath` and
carrier-typed `cap` subterms together with per-subterm typed-lift
callbacks, and assembles the typed `Step.par.hcompPathCong` cong
witness directly.  This is the cong-only variant for CONVTRANS-B.2e
(ticket #1726); typed cubical β arms targeting `hcompPath` (the
constant-path simplification rule and its deep variant) land in a
matching full lift in a future cascade.

## Structural notes

`Term.hcompPath` is the path-typed-sides redesign of `Term.hcomp`
(see `Term.lean:472` for the option-B docstring): its `sidesPath`
subterm is typed at `Ty.path carrierType leftEndpoint rightEndpoint`
rather than at the carrier type, so the constant-path β rule
becomes kernel-recognizable.  Raw projection is the same as
`Term.hcomp` — both project to `RawTerm.hcomp sidesPathRaw capRaw` —
so the raw cong step in this lift takes the form
`RawStep.par sidesPathRaw sidesPathTargetRaw` paired with
`RawStep.par capRaw capTargetRaw`.  The typed cong rule
`Step.par.hcompPathCong` (`ParInductive.lean:744`) takes the two
typed steps directly without inverting an opaque
`RawStep.par (RawTerm.hcomp _ _) _` head step.

This mirrors `lift_hcomp_cong` (`TierTwoBinary.lean:139`) which
covers the carrier-typed-sides `Term.hcomp` ctor; both share the
"raw-cong-step in, no inversion" shape because their respective
β arms (D2.5.2 `hcompBeta` / `hcompBetaDeep`) target the path-typed
representation only and have no typed mirror at the carrier-typed
ctor.

## Root status

Zero-axiom; mirrors the pattern in `EliminatorModalFamily.lean`
(commit 553532f) and the cong-only narrow form in
`lift_hcomp_cong` from `TierTwoBinary.lean`. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-- **CONVTRANS-B.2e — Term.hcompPath lift, cong arm only.**

Path-shaped homogeneous composition cong rule (`Step.par.hcompPathCong`,
`ParInductive.lean:744`).  Two subterms: `sidesPath` (typed at
`Ty.path carrierType leftEndpoint rightEndpoint`) and `cap` (typed
at `carrierType`).  Output type is preserved — both source and
target inhabit `Ty.path carrierType leftEndpoint rightEndpoint`
indexed at the same endpoints.

Cong-only because the typed cubical β arms targeting `hcompPath`
(constant-path simplification + deep variant) are pending; see
`AuditD252HcompBeta.lean` for the raw-level β rules that already
land at the underlying `RawTerm.hcomp` head. -/
theorem RawStep.par.lift_hcompPath_cong
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    (leftEndpoint rightEndpoint : RawTerm scope)
    {sidesPathRaw capRaw : RawTerm scope}
    (sidesPath :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw)
    (cap : Term context carrierType capRaw)
    (sidesPathLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par sidesPathRaw targetRawIH →
      ∃ sidesPathTarget :
          Term context (Ty.path carrierType leftEndpoint rightEndpoint)
                       targetRawIH,
        Step.par sidesPath sidesPathTarget)
    (capLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par capRaw targetRawIH →
      ∃ capTarget : Term context carrierType targetRawIH,
        Step.par cap capTarget)
    {sidesPathTargetRaw capTargetRaw : RawTerm scope}
    (sidesPathStep : RawStep.par sidesPathRaw sidesPathTargetRaw)
    (capStep : RawStep.par capRaw capTargetRaw) :
    ∃ targetTerm :
        Term context carrierType
                     (RawTerm.hcomp sidesPathTargetRaw capTargetRaw),
      Step.par
        (Term.hcompPath modeIsUnivalent leftEndpoint rightEndpoint
                        sidesPath cap)
        targetTerm := by
  obtain ⟨sidesPathTarget, sidesPathStepTyped⟩ := sidesPathLift sidesPathStep
  obtain ⟨capTarget, capStepTyped⟩ := capLift capStep
  exact ⟨Term.hcompPath modeIsUnivalent leftEndpoint rightEndpoint
                        sidesPathTarget capTarget,
         Step.par.hcompPathCong modeIsUnivalent leftEndpoint rightEndpoint
                                sidesPathStepTyped capStepTyped⟩

end LeanFX2

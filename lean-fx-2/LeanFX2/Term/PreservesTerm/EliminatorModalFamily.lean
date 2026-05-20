import LeanFX2.Reduction.ParRed.ParInductive.Inductive
import LeanFX2.Term.Inversion

/-! # LeanFX2.Term.PreservesTerm.EliminatorModalFamily

Cong-only lift theorems for the three modal-family eliminators:

* `lift_modIntro_cong` — modal introduction (`Term.modIntro`).
* `lift_modElim_cong` — modal elimination cong arm (`Term.modElim`).
* `lift_subsume_cong` — cumul subsumption (`Term.subsume`).

Each takes a raw parallel-reduction step on the single inner subterm
together with a typed-lift callback, and assembles the typed
`Step.par.<modIntro|modElim|subsume>` cong witness directly.  This is
the cong-only variant for CONVTRANS-B.2d (ticket #1725); the β-arm of
modElim (`betaModElimIntro` / `betaModElimIntroDeep`) lives in a
future full variant for `modElim`.  `modIntro` and `subsume` have no
β-arm — their cong-only lifts are the total raw inversion projections.

## Structural notes

All three modal eliminators are **single-subterm cong rules** — the
structurally simplest cong family in the kernel:

* Layer-1 raw scaffolding (`Term.lean`): `innerType` is preserved
  source → target for all three ctors.  No mode shift, no cumul
  witness on the ctor itself (those become live at Layer 6 when
  `Ty.modal` + cumul-witness redesign land).
* Typed cong rules `Step.par.modIntro` / `Step.par.modElim` /
  `Step.par.subsume` share an identical signature: `Step.par
  innerSource innerTarget → Step.par (Term.X innerSource)
  (Term.X innerTarget)`.
* Naming asymmetry vs identity family: BARE `Step.par.modIntro` (no
  `Cong` suffix) is the cong arm; β-arms are named `betaModElimIntro`
  / `betaModElimIntroDeep`.

## Root status

Zero-axiom; mirrors the pattern in `EliminatorIdentityFamily.lean`
(commit 534c2b6) with one inner subterm instead of three. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-- **CONVTRANS-B.2d — Term.modIntro lift, cong arm only.**  Modal
introduction; the only non-`refl` raw rule from `RawTerm.modIntro` is
the structural cong, so the cong-only lift is the total raw inversion
projection.  Output type is preserved (Layer-1 raw scaffolding;
`Ty.modal` wrapping arrives at Layer 6). -/
theorem RawStep.par.lift_modIntro_cong
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par innerRaw targetRawIH →
      ∃ innerTarget : Term context innerType targetRawIH,
        Step.par innerTerm innerTarget)
    {innerTargetRaw : RawTerm scope}
    (innerStep : RawStep.par innerRaw innerTargetRaw) :
    ∃ targetTerm :
        Term context innerType (RawTerm.modIntro innerTargetRaw),
      Step.par (Term.modIntro innerTerm) targetTerm := by
  obtain ⟨innerTarget, innerStepTyped⟩ := innerLift innerStep
  exact ⟨Term.modIntro innerTarget, Step.par.modIntro innerStepTyped⟩

/-- **CONVTRANS-B.2d — Term.modElim lift, cong arm only.**  Modal
elimination cong arm; the β-arm (`betaModElimIntro` /
`betaModElimIntroDeep`) fires when the inner value develops to a
`modIntro` and lives in a future full variant.  The cong-only variant
assumes the caller has already projected the cong arm of the raw
inversion. -/
theorem RawStep.par.lift_modElim_cong
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par innerRaw targetRawIH →
      ∃ innerTarget : Term context innerType targetRawIH,
        Step.par innerTerm innerTarget)
    {innerTargetRaw : RawTerm scope}
    (innerStep : RawStep.par innerRaw innerTargetRaw) :
    ∃ targetTerm :
        Term context innerType (RawTerm.modElim innerTargetRaw),
      Step.par (Term.modElim innerTerm) targetTerm := by
  obtain ⟨innerTarget, innerStepTyped⟩ := innerLift innerStep
  exact ⟨Term.modElim innerTarget, Step.par.modElim innerStepTyped⟩

/-- **CONVTRANS-B.2d — Term.subsume lift, cong arm only.**  Cumul
subsumption; structurally identical to `lift_modIntro_cong` — single
inner subterm, output type preserved, no β-arm.  The eventual
cumul-witness redesign (Layer 6+) will attach a cumul proof to the
ctor; until then the lift is the cleanest one in the cascade. -/
theorem RawStep.par.lift_subsume_cong
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw)
    (innerLift : ∀ {targetRawIH : RawTerm scope},
      RawStep.par innerRaw targetRawIH →
      ∃ innerTarget : Term context innerType targetRawIH,
        Step.par innerTerm innerTarget)
    {innerTargetRaw : RawTerm scope}
    (innerStep : RawStep.par innerRaw innerTargetRaw) :
    ∃ targetTerm :
        Term context innerType (RawTerm.subsume innerTargetRaw),
      Step.par (Term.subsume innerTerm) targetTerm := by
  obtain ⟨innerTarget, innerStepTyped⟩ := innerLift innerStep
  exact ⟨Term.subsume innerTarget, Step.par.subsume innerStepTyped⟩

end LeanFX2

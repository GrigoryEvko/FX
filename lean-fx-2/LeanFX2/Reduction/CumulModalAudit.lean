import LeanFX2.Reduction.Cumul

/-! # Reduction/CumulModalAudit — CUMUL-7.5 modal cumul regression baseline

Closes tracker #1431 CUMUL-7.5 (Smoke audit modal cumul across all
five modal-fragment modes).  Exercises the four mode-polymorphic
modal cumul rules at every modal-fragment mode, producing twenty
zero-axiom theorems that establish a regression baseline against
modeIs* gate slippage.

## What this file ships

For each of the five modal-fragment modes
(`strict`, `observational`, `univalent`, `cohesiveFlat`,
`cohesiveSharp`):

* `modIntroCong_at_M` — applies `ConvCumul.modIntroCong` to a
  `ConvCumul.refl` seed at mode `M`.
* `modElimCong_at_M` — same shape via `ConvCumul.modElimCong`.
* `subsumeCong_at_M` — same shape via `ConvCumul.subsumeCong`.
* `modalBeta_at_M` — `ConvCumul (modElim (modIntro witness)) witness`
  via `ConvCumul.betaModElimIntroCumul`.

Witness throughout: `Term.boolTrue` at the empty `Ctx` in the
requested mode at level 1 (the smallest level admitting `Ty.bool`).
The witness is mode-polymorphic; per-mode instantiation is the
substantive content of the smoke.

## Why per-mode smoke matters

The four target cumul rules in `Reduction/Cumul.lean` carry an
implicit `{mode : Mode}` parameter.  Lean 4 v4.29.1's match
compiler can leak `propext` when an implicit-mode pattern is
partially matched at one mode and dispatched-through at another —
see `feedback_lean_zero_axiom_match.md` for the recipe and
`feedback_lean_universe_constructor_block.md` for the
constraint-shape variant.

Per-mode named theorems pin the elaboration at every mode-fragment
ctor and let `#audit_namespace LeanFX2` (auto-gated; this file
lives outside `LeanFX2.Smoke`) catch any leak immediately.

## Architectural commitment

The four target cumul rules are HOMOGENEOUS in mode (the cong
rules require `innerFirst` and `innerSecond` to share a `Ctx mode
level scope`; β does not change mode either).  Cross-mode cumul
rules ship in CUMUL-7.1–7.4 once the cross-mode `Modality`
infrastructure (Phase 12.A.6 prerequisites — see
`Modal/Cohesive.lean` and `Modal/Adjunction.lean` docstrings)
lands.  This file establishes the homogeneous baseline first.

## Dependencies

* `Reduction/Cumul.lean` — provides `ConvCumul` and the four
  cumul rules referenced here.

## Downstream consumers

* `Smoke/AuditPhase12AB19CumulModal.lean` — reviewer-facing
  `#print axioms` log over every theorem in this file.
-/

namespace LeanFX2
namespace CumulModalAudit

/-- Mode-polymorphic boolean witness.  `Term.boolTrue` at the empty
context at level 1 in the requested mode.  The Term ctor is
mode-polymorphic — `mode` is an implicit parameter on `Term.boolTrue`
that gets instantiated at the call site. -/
def witnessTrue (whichMode : Mode) :
    Term (Ctx.empty whichMode 1) Ty.bool RawTerm.boolTrue :=
  Term.boolTrue

/-! ## Mode strict — four homogeneous cumul rules instantiated -/

/-- modIntro cong rule lifts to refl at `Mode.strict`. -/
theorem modIntroCong_at_strict :
    ConvCumul (Term.modIntro (witnessTrue Mode.strict))
              (Term.modIntro (witnessTrue Mode.strict)) :=
  ConvCumul.modIntroCong (ConvCumul.refl (witnessTrue Mode.strict))

/-- modElim cong rule lifts to refl at `Mode.strict`. -/
theorem modElimCong_at_strict :
    ConvCumul (Term.modElim (witnessTrue Mode.strict))
              (Term.modElim (witnessTrue Mode.strict)) :=
  ConvCumul.modElimCong (ConvCumul.refl (witnessTrue Mode.strict))

/-- subsume cong rule lifts to refl at `Mode.strict`. -/
theorem subsumeCong_at_strict :
    ConvCumul (Term.subsume (witnessTrue Mode.strict))
              (Term.subsume (witnessTrue Mode.strict)) :=
  ConvCumul.subsumeCong (ConvCumul.refl (witnessTrue Mode.strict))

/-- Modal β-reduction at `Mode.strict`:
`modElim (modIntro witness) cumul-relates to witness`. -/
theorem modalBeta_at_strict :
    ConvCumul (Term.modElim (Term.modIntro (witnessTrue Mode.strict)))
              (witnessTrue Mode.strict) :=
  ConvCumul.betaModElimIntroCumul (witnessTrue Mode.strict)

/-! ## Mode observational — four homogeneous cumul rules instantiated -/

/-- modIntro cong rule lifts to refl at `Mode.observational`. -/
theorem modIntroCong_at_observational :
    ConvCumul (Term.modIntro (witnessTrue Mode.observational))
              (Term.modIntro (witnessTrue Mode.observational)) :=
  ConvCumul.modIntroCong (ConvCumul.refl (witnessTrue Mode.observational))

/-- modElim cong rule lifts to refl at `Mode.observational`. -/
theorem modElimCong_at_observational :
    ConvCumul (Term.modElim (witnessTrue Mode.observational))
              (Term.modElim (witnessTrue Mode.observational)) :=
  ConvCumul.modElimCong (ConvCumul.refl (witnessTrue Mode.observational))

/-- subsume cong rule lifts to refl at `Mode.observational`. -/
theorem subsumeCong_at_observational :
    ConvCumul (Term.subsume (witnessTrue Mode.observational))
              (Term.subsume (witnessTrue Mode.observational)) :=
  ConvCumul.subsumeCong (ConvCumul.refl (witnessTrue Mode.observational))

/-- Modal β-reduction at `Mode.observational`. -/
theorem modalBeta_at_observational :
    ConvCumul (Term.modElim (Term.modIntro (witnessTrue Mode.observational)))
              (witnessTrue Mode.observational) :=
  ConvCumul.betaModElimIntroCumul (witnessTrue Mode.observational)

/-! ## Mode univalent — four homogeneous cumul rules instantiated -/

/-- modIntro cong rule lifts to refl at `Mode.univalent`. -/
theorem modIntroCong_at_univalent :
    ConvCumul (Term.modIntro (witnessTrue Mode.univalent))
              (Term.modIntro (witnessTrue Mode.univalent)) :=
  ConvCumul.modIntroCong (ConvCumul.refl (witnessTrue Mode.univalent))

/-- modElim cong rule lifts to refl at `Mode.univalent`. -/
theorem modElimCong_at_univalent :
    ConvCumul (Term.modElim (witnessTrue Mode.univalent))
              (Term.modElim (witnessTrue Mode.univalent)) :=
  ConvCumul.modElimCong (ConvCumul.refl (witnessTrue Mode.univalent))

/-- subsume cong rule lifts to refl at `Mode.univalent`. -/
theorem subsumeCong_at_univalent :
    ConvCumul (Term.subsume (witnessTrue Mode.univalent))
              (Term.subsume (witnessTrue Mode.univalent)) :=
  ConvCumul.subsumeCong (ConvCumul.refl (witnessTrue Mode.univalent))

/-- Modal β-reduction at `Mode.univalent`. -/
theorem modalBeta_at_univalent :
    ConvCumul (Term.modElim (Term.modIntro (witnessTrue Mode.univalent)))
              (witnessTrue Mode.univalent) :=
  ConvCumul.betaModElimIntroCumul (witnessTrue Mode.univalent)

/-! ## Mode cohesiveFlat — four homogeneous cumul rules instantiated -/

/-- modIntro cong rule lifts to refl at `Mode.cohesiveFlat`. -/
theorem modIntroCong_at_cohesiveFlat :
    ConvCumul (Term.modIntro (witnessTrue Mode.cohesiveFlat))
              (Term.modIntro (witnessTrue Mode.cohesiveFlat)) :=
  ConvCumul.modIntroCong (ConvCumul.refl (witnessTrue Mode.cohesiveFlat))

/-- modElim cong rule lifts to refl at `Mode.cohesiveFlat`. -/
theorem modElimCong_at_cohesiveFlat :
    ConvCumul (Term.modElim (witnessTrue Mode.cohesiveFlat))
              (Term.modElim (witnessTrue Mode.cohesiveFlat)) :=
  ConvCumul.modElimCong (ConvCumul.refl (witnessTrue Mode.cohesiveFlat))

/-- subsume cong rule lifts to refl at `Mode.cohesiveFlat`. -/
theorem subsumeCong_at_cohesiveFlat :
    ConvCumul (Term.subsume (witnessTrue Mode.cohesiveFlat))
              (Term.subsume (witnessTrue Mode.cohesiveFlat)) :=
  ConvCumul.subsumeCong (ConvCumul.refl (witnessTrue Mode.cohesiveFlat))

/-- Modal β-reduction at `Mode.cohesiveFlat`. -/
theorem modalBeta_at_cohesiveFlat :
    ConvCumul (Term.modElim (Term.modIntro (witnessTrue Mode.cohesiveFlat)))
              (witnessTrue Mode.cohesiveFlat) :=
  ConvCumul.betaModElimIntroCumul (witnessTrue Mode.cohesiveFlat)

/-! ## Mode cohesiveSharp — four homogeneous cumul rules instantiated -/

/-- modIntro cong rule lifts to refl at `Mode.cohesiveSharp`. -/
theorem modIntroCong_at_cohesiveSharp :
    ConvCumul (Term.modIntro (witnessTrue Mode.cohesiveSharp))
              (Term.modIntro (witnessTrue Mode.cohesiveSharp)) :=
  ConvCumul.modIntroCong (ConvCumul.refl (witnessTrue Mode.cohesiveSharp))

/-- modElim cong rule lifts to refl at `Mode.cohesiveSharp`. -/
theorem modElimCong_at_cohesiveSharp :
    ConvCumul (Term.modElim (witnessTrue Mode.cohesiveSharp))
              (Term.modElim (witnessTrue Mode.cohesiveSharp)) :=
  ConvCumul.modElimCong (ConvCumul.refl (witnessTrue Mode.cohesiveSharp))

/-- subsume cong rule lifts to refl at `Mode.cohesiveSharp`. -/
theorem subsumeCong_at_cohesiveSharp :
    ConvCumul (Term.subsume (witnessTrue Mode.cohesiveSharp))
              (Term.subsume (witnessTrue Mode.cohesiveSharp)) :=
  ConvCumul.subsumeCong (ConvCumul.refl (witnessTrue Mode.cohesiveSharp))

/-- Modal β-reduction at `Mode.cohesiveSharp`. -/
theorem modalBeta_at_cohesiveSharp :
    ConvCumul (Term.modElim (Term.modIntro (witnessTrue Mode.cohesiveSharp)))
              (witnessTrue Mode.cohesiveSharp) :=
  ConvCumul.betaModElimIntroCumul (witnessTrue Mode.cohesiveSharp)

end CumulModalAudit
end LeanFX2

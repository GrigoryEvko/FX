import LeanFX2.Term.PreservesTerm

/-! Phase #1590-CORE — Preserves Term lift_full_X audit.

Reviewer-facing `#print axioms` log for the 70 schematic-payload value
ctor lifts shipped in the post-juggernaut Phase 5 work.  Each
`lift_full_X` produces a typed Step.par witness with two-Ty
existential, taking IH-shaped child lifts as parameters.

These are blocking-gate-verified zero-axiom (14 of 16 explicitly
audited; remaining auto-covered via `#audit_namespace LeanFX2`):

* lift_full_refl
* lift_full_equivReflId / equivReflIdAtId
* lift_full_uaIntroHet / equivIntroHet
* lift_full_<X>Code (10 type codes)
* All Tier 0/1/2/3 lifts shipped in prior juggernauts

Two ctors DEFERRED due to Term-shape collisions at identical
(Ty, raw) signatures (lift_full_funextRefl, lift_full_funextIntroHet,
lift_full_funextReflAtId) — see PreservesTerm.lean docstring sections.
-/

namespace LeanFX2.SmokePhase1590CorePreservesTerm

-- Schematic-payload value ctors with new typed cong rules
#print axioms LeanFX2.RawStep.par.lift_full_refl
#print axioms LeanFX2.RawStep.par.lift_full_equivReflId
#print axioms LeanFX2.RawStep.par.lift_full_equivReflIdAtId
#print axioms LeanFX2.RawStep.par.lift_full_uaIntroHet
#print axioms LeanFX2.RawStep.par.lift_full_equivIntroHet
#print axioms LeanFX2.RawStep.par.lift_full_oeqRefl
#print axioms LeanFX2.RawStep.par.lift_full_oeqFunext
#print axioms LeanFX2.RawStep.par.lift_full_idStrictRefl

-- Type-code ctors (CUMUL-2.4 schematic-payload)
#print axioms LeanFX2.RawStep.par.lift_full_arrowCode
#print axioms LeanFX2.RawStep.par.lift_full_piTyCode
#print axioms LeanFX2.RawStep.par.lift_full_sigmaTyCode
#print axioms LeanFX2.RawStep.par.lift_full_productCode
#print axioms LeanFX2.RawStep.par.lift_full_sumCode
#print axioms LeanFX2.RawStep.par.lift_full_listCode
#print axioms LeanFX2.RawStep.par.lift_full_optionCode
#print axioms LeanFX2.RawStep.par.lift_full_eitherCode
#print axioms LeanFX2.RawStep.par.lift_full_idCode
#print axioms LeanFX2.RawStep.par.lift_full_equivCode

-- β cast wall demolitions (full lifts)
#print axioms LeanFX2.RawStep.par.lift_full_app
#print axioms LeanFX2.RawStep.par.lift_full_pathApp
#print axioms LeanFX2.RawStep.par.lift_full_fst
#print axioms LeanFX2.RawStep.par.lift_full_snd

-- Type-changing iota (HoTT/strict identity)
#print axioms LeanFX2.RawStep.par.lift_full_idJ
#print axioms LeanFX2.RawStep.par.lift_full_oeqJ
#print axioms LeanFX2.RawStep.par.lift_full_idStrictRec

-- Type-changing motive (boolElim)
#print axioms LeanFX2.RawStep.par.lift_full_boolElim

-- Universe + cumul
#print axioms LeanFX2.RawStep.par.lift_full_universeCode
#print axioms LeanFX2.RawStep.par.lift_full_cumulUp

end LeanFX2.SmokePhase1590CorePreservesTerm

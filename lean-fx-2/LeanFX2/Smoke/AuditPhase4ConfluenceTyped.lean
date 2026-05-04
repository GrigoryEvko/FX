import LeanFX2.Confluence.Cd
import LeanFX2.Confluence.CdLemma
import LeanFX2.Confluence.Diamond
import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Confluence.CanonicalForm

/-! # AuditPhase4ConfluenceTyped — zero-axiom gates for typed confluence wrappers

Verifies the typed-input/raw-output confluence corollaries shipped
in `LeanFX2/Confluence/{Cd,CdLemma,Diamond,ChurchRosser,
CanonicalForm}.lean` are zero-axiom under the strict policy.

These lift the already-shipped raw confluence chain (RawCd,
RawCdLemma, RawDiamond, RawConfluence — all shipped fully zero-
axiom) to typed inputs via `Step.par.toRawBridge` and
`Conv.toRawJoin`.

A typed-output confluence (raw common reduct lifted back to a
typed Term) requires subject reduction for `Step` / `Step.par`,
which is M05/M06 work (Phase 7).  Until SR ships, these raw-
output corollaries are sufficient for Layer 9 (decidable
conversion) and elaborator coherence proofs.
-/

#print axioms LeanFX2.Term.cdRaw
#print axioms LeanFX2.Term.cdRaw_eq
#print axioms LeanFX2.Term.cdRaw_unit
#print axioms LeanFX2.Term.cdRaw_boolTrue
#print axioms LeanFX2.Term.cdRaw_boolFalse
#print axioms LeanFX2.Term.cdRaw_natZero
#print axioms LeanFX2.Term.cdRaw_listNil
#print axioms LeanFX2.Term.cdRaw_optionNone

#print axioms LeanFX2.Step.par.cdLemmaRaw
#print axioms LeanFX2.Step.par.cdDominatesRaw
#print axioms LeanFX2.Step.par.cdLemmaRaw_refl
#print axioms LeanFX2.Step.parStar.cdDominatesRawSingle

#print axioms LeanFX2.Step.par.diamondRaw
#print axioms LeanFX2.Step.par.diamondRawCd

#print axioms LeanFX2.Step.parStar.churchRosserRaw
#print axioms LeanFX2.StepStar.churchRosserRaw
#print axioms LeanFX2.Conv.canonicalRaw
#print axioms LeanFX2.Conv.transRaw

#print axioms LeanFX2.Conv.canonicalForm
#print axioms LeanFX2.Conv.canonicalForm_self
#print axioms LeanFX2.Conv.canonicalForm_fromStepStar

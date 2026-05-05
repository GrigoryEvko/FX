import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawDiamond
import LeanFX2.Confluence.Cd
import LeanFX2.Confluence.CdLemma
import LeanFX2.Confluence.Diamond
import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Confluence.CanonicalForm

/-! # AuditPhase12A3Day3 — Day 3 (Phase 12.A.3) zero-axiom audit.

Day 3 of the cubical+2LTT+HOTT sprint:
* D3.1 — Confluence/RawCd.lean: D1.6 cong cases plus D2.5 raw
  path-application and Glue beta complete development — verified by
  extension
* D3.2 — Confluence/RawCdLemma.lean: congruence plus raw cubical beta
  cases — verified by extension
* D3.3 — Diamond property: RAW-side diamond + parStar.confluence DONE
  via parametric proof in cd_lemma; typed-input/raw-output
  `Step.par.diamondRaw` and `Step.par.diamondRawCd` ship through
  `Step.par.toRawBridge`.
* D3.4 — Church-Rosser: RAW-side `RawStep.parStar.confluence` DONE;
  typed-input/raw-output `Step.parStar.churchRosserRaw`,
  `StepStar.churchRosserRaw`, `Conv.canonicalRaw`,
  `Conv.transRaw`, and `Conv.canonicalForm` ship as raw-join
  corollaries.
* D3.5 — HoTT/Equivalence (DONE separately)
* D3.6–D3.9 — HoTT/HIT specifications (separate work)
* D3.10 — HoTT/Path/Groupoid (DONE separately)

This audit anchors the RAW Confluence machinery and its typed-input /
raw-output bridge against the extended RawTerm infrastructure.  Every theorem MUST report
"does not depend on any axioms".

Full typed-output confluence still requires subject reduction strong
enough to construct typed common reducts.  The current load-bearing
surface is deliberately typed-input/raw-output: it is what the
decidable-conversion and canonical-form layers consume.
-/

-- D3.1: cd extends through new ctors and raw cubical beta rules
#print axioms LeanFX2.RawTerm.cd
#print axioms LeanFX2.RawTerm.cdPathAppCase
#print axioms LeanFX2.RawTerm.cdGlueElimCase
#print axioms LeanFX2.RawTerm.cdRefineElimCase
#print axioms LeanFX2.RawTerm.cdRecordProjCase

-- D3.2: cd_lemma extends through cong and raw cubical beta rules
#print axioms LeanFX2.RawStep.par.cd_lemma

-- D3.3: diamond + cd_dominates (parametric in cd_lemma)
#print axioms LeanFX2.RawStep.par.diamond
#print axioms LeanFX2.RawStep.par.cd_dominates

-- D3.4: Church-Rosser raw chain
#print axioms LeanFX2.RawStep.par.toStar
#print axioms LeanFX2.RawStep.parStar.snoc
#print axioms LeanFX2.RawStep.parStar.append
#print axioms LeanFX2.RawStep.par.strip
#print axioms LeanFX2.RawStep.parStar.confluence

-- D3 typed-input/raw-output confluence bridge
#print axioms LeanFX2.Term.cdRaw
#print axioms LeanFX2.Term.cdRaw_eq
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

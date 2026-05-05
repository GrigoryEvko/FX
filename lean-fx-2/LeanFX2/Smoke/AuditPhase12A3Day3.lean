import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawDiamond

/-! # AuditPhase12A3Day3 — Day 3 (Phase 12.A.3) zero-axiom audit.

Day 3 of the cubical+2LTT+HOTT sprint:
* D3.1 — Confluence/RawCd.lean: D1.6 cong cases plus D2.5 raw
  path-application and Glue beta complete development — verified by
  extension
* D3.2 — Confluence/RawCdLemma.lean: congruence plus raw cubical beta
  cases — verified by extension
* D3.3 — Diamond property: RAW-side diamond + parStar.confluence DONE
  via parametric proof in cd_lemma; typed-side `Step.par.diamond` is
  scaffolded as a stub awaiting typed Term ctors (D1.9 deferred)
* D3.4 — Church-Rosser: RAW-side `RawStep.parStar.confluence` DONE;
  typed-side scaffolded
* D3.5 — HoTT/Equivalence (DONE separately)
* D3.6–D3.9 — HoTT/HIT specifications (separate work)
* D3.10 — HoTT/Path/Groupoid (DONE separately)

This audit anchors the RAW Confluence machinery against the extended
RawTerm infrastructure.  Every theorem MUST report
"does not depend on any axioms".

The typed-side bridge from raw confluence to typed confluence
(D3.3/D3.4 typed-half) lands when typed Term ctors arrive per-need.
Until then, raw confluence + the rfl-bridge `Term.toRaw` deliver
typed confluence as an immediate corollary at usage sites.
-/

-- D3.1: cd extends through new ctors and raw cubical beta rules
#print axioms LeanFX2.RawTerm.cd
#print axioms LeanFX2.RawTerm.cdPathAppCase
#print axioms LeanFX2.RawTerm.cdGlueElimCase

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

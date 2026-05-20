import LeanFX2.Reduction.Step.Inductive
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawDiamond

/-! # Smoke/AuditD36S4IdToEquivRefl — D3.6-S4 idToEquiv refl β.

Reviewer-facing audit log for Phase D3.6-S4 (#1685): the headline
kernel-internal univalence-β rule

```
idToEquiv (oeqRefl _ _ witness)
  ⟶ equivIntro (lam (var 0)) (lam (var 0))
```

ships at zero axioms across the kernel cascade:

* `RawTerm.idToEquiv proofRaw` — new unary raw ctor enabling
  `idToEquiv` at the kernel layer.  Cascaded through 16 kernel
  files (RawTerm + RawSubst + rename / partial-rename / cd-rename /
  pointwise / SubstActsOnTy / RenameIdentity, RawPar / RawParInversion /
  RawParRename / RawParCompatible / RawParWeakenInv, Confluence
  cd / cdLemma / cdDominates / cdRename, Algo Eval / Infer / Check /
  RawWHNF / RawWHNFCorrect).
* `RawStep.par.idToEquivCong` — cong rule for parallel reduction
  through the new unary ctor.
* `RawStep.par.idToEquivRefl` — the headline shallow β rule firing
  when the proof argument is structurally `oeqRefl`.
* `RawStep.par.idToEquivReflDeep` — confluence-closure deep variant
  (proof develops to oeqRefl via parallel reduction).
* `RawStep.par.idToEquiv_inv` — inversion lemma backing the cd
  cascade's deep arm.

Typed mirror (`Step.idToEquivCong` etc.) deferred to v1.1 — typed
`Term.idToEquiv` requires the proof to be typed at `Ty.id` which
forces a follow-up D3.10-PATH-COMPOSE-HOTT closure first.  Until
then, the four raw-only ctors live in `isDocumentedRawOnlyParity`
Section F. -/

namespace LeanFX2

-- ============================
-- Section A: D3.6-S4 raw cascade — the headline β rule
-- ============================

#print axioms LeanFX2.RawStep.par.idToEquivCong
#print axioms LeanFX2.RawStep.par.idToEquivRefl
#print axioms LeanFX2.RawStep.par.idToEquivReflDeep
#print axioms LeanFX2.RawStep.par.idToEquiv_inv

-- ============================
-- Section B: surrounding cascade infrastructure remains zero-axiom
-- (proves S4 extension does not regress S1/S2/S3 or earlier ctors)
-- ============================

#print axioms LeanFX2.RawStep.par.cd_lemma
#print axioms LeanFX2.RawStep.par.diamond
#print axioms LeanFX2.RawStep.par.cd_dominates

-- ============================
-- Section C: surrounding D3.6 cascade remains zero-axiom
-- ============================

#print axioms LeanFX2.RawStep.par.uaBeta
#print axioms LeanFX2.RawStep.par.uaBetaDeep
#print axioms LeanFX2.RawStep.par.uaToEquiv_inv
#print axioms LeanFX2.RawStep.par.transpCompose
#print axioms LeanFX2.RawStep.par.transpComposeDeep
#print axioms LeanFX2.RawStep.par.pathCompose_inv
#print axioms LeanFX2.RawStep.par.transpReflBeta
#print axioms LeanFX2.RawStep.par.transpReflBetaDeep
#print axioms LeanFX2.Step.transpReflBeta

end LeanFX2

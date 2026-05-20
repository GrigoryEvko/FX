import LeanFX2.Reduction.Step.Inductive
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawDiamond

/-! # Smoke/AuditD36S5IdToEquivCompose — D3.6-S5 idToEquiv compose β.

Reviewer-facing audit log for Phase D3.6-S5 (#1686): the headline
kernel-internal univalence-compose-β rule

```
idToEquiv (oeqTrans first second)
  ⟶ equivCompose (idToEquiv first) (idToEquiv second)
```

ships at zero axioms across the kernel cascade:

* `RawTerm.oeqTrans firstProof secondProof` — new binary raw ctor
  representing observational-equality transitivity composition.
* `RawTerm.equivCompose firstEquiv secondEquiv` — new binary raw
  ctor representing equivalence composition (the contractum target
  of the headline rule).  Both ctors cascaded through 16 kernel
  files (RawTerm + RawSubst + rename / partial-rename / cd-rename /
  pointwise / SubstActsOnTy / RenameIdentity, RawPar /
  RawParInversion / RawParRename / RawParCompatible /
  RawParWeakenInv, Confluence cd / cdLemma / cdDominates / cdRename,
  Algo Eval / Infer / Check / RawWHNF / RawWHNFCorrect).
* `RawStep.par.oeqTransCong` — binary cong rule for oeqTrans.
* `RawStep.par.equivComposeCong` — binary cong rule for equivCompose.
* `RawStep.par.idToEquivCompose` — the headline shallow β rule
  firing when the proof argument is structurally `oeqTrans first
  second`.
* `RawStep.par.idToEquivComposeDeep` — confluence-closure deep
  variant (proof develops to `oeqTrans ...` via parallel reduction).
* `RawStep.par.oeqTrans_inv` — inversion lemma: par-step landing
  at `oeqTrans X Y` admits only the `oeqTransCong` rule (or refl).
* `RawStep.par.equivCompose_inv` — inversion lemma: par-step
  landing at `equivCompose X Y` admits only the `equivComposeCong`
  rule (or refl).

Typed mirrors (`Term.oeqTrans`, `Term.equivCompose`,
`Term.idToEquiv`) deferred to v1.1 — typed ctors require typed
`Ty.id` proof which forces a follow-up D3.10-PATH-COMPOSE-HOTT
closure first.  Until then, the four raw-only arms
(`oeqTransCong`, `equivComposeCong`, `idToEquivCompose`,
`idToEquivComposeDeep`) live in `isDocumentedRawOnlyParity`
Section G. -/

namespace LeanFX2

-- ============================
-- Section A: D3.6-S5 raw cascade — the headline compose-β rule
-- ============================

#print axioms LeanFX2.RawStep.par.oeqTransCong
#print axioms LeanFX2.RawStep.par.equivComposeCong
#print axioms LeanFX2.RawStep.par.idToEquivCompose
#print axioms LeanFX2.RawStep.par.idToEquivComposeDeep
#print axioms LeanFX2.RawStep.par.oeqTrans_inv
#print axioms LeanFX2.RawStep.par.equivCompose_inv

-- ============================
-- Section B: surrounding cascade infrastructure remains zero-axiom
-- (proves S5 extension does not regress S1/S2/S3/S4 or earlier ctors)
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
#print axioms LeanFX2.RawStep.par.idToEquivCong
#print axioms LeanFX2.RawStep.par.idToEquivRefl
#print axioms LeanFX2.RawStep.par.idToEquivReflDeep
#print axioms LeanFX2.RawStep.par.idToEquiv_inv
#print axioms LeanFX2.RawStep.par.transpReflBeta
#print axioms LeanFX2.RawStep.par.transpReflBetaDeep
#print axioms LeanFX2.Step.transpReflBeta

end LeanFX2

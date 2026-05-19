import LeanFX2.Reduction.Step
import LeanFX2.Reduction.RawParInversion
import LeanFX2.Reduction.RawParRename
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Confluence.RawDiamond

/-! # Smoke/AuditD36S6UaReflEquivApply — D3.6-S6 univalence-refl round-trip β.

Reviewer-facing audit log for Phase D3.6-S6 (#1687): the headline
kernel-internal univalence-refl-roundtrip-β rule

```
equivApply (uaToEquiv (oeqRefl witness)) source ⟶ source
```

ships at zero axioms across the kernel cascade.

The rule encodes the cubical fact that the equivalence obtained by
`uaToEquiv` from the observational-equality refl proof is the
identity equivalence; applying it to a value yields the value
unchanged.  This is the dual to S4's `idToEquiv (refl _) ⟶
equivIntro id id` round-trip — together S4 + S6 close the round-
trip semantics for the closed identity-equiv on both sides
(idToEquiv-of-refl AND uaToEquiv-of-oeqRefl).

Cascade landed in two atomic commits:

* `2cd91f3` Reduction/RawPar: par ctors `uaReflEquivApply` (shallow)
  + `uaReflEquivApplyDeep` (deep) plus their RawParInversion +
  RawParRename + RawParCompatible + RawParWeakenInv arms.
* `91ddd9a` Confluence/RawCd: dispatchers `cdEquivApplyCase` outer +
  `cdUaToEquivApplyCase` inner with full 67-arm enumeration; cd
  arm for `equivApply` updated to dispatch through the new outer
  case + `cdEquivApplyCong` rename arm.
* This commit (D3.6-S6 cd_lemma close-out): two new
  `RawCdLemma.cd_lemma` arms for `uaReflEquivApply` (shallow,
  closed by `simp only [RawTerm.cd, cdEquivApplyCase,
  cdUaToEquivApplyCase]` + `sourceIH`) and `uaReflEquivApplyDeep`
  (deep, closed by `uaToEquiv_inv` + `oeqRefl_inv` on `equivIH`,
  then the same simp chain + `sourceIH`).

Typed mirrors `Term.{uaToEquiv, oeqRefl, equivApply}` exist
upstream from D3.6-P3/P4 cascades, but typed `Term.equivApply`
cannot have an equiv-raw of `RawTerm.uaToEquiv (RawTerm.oeqRefl
witness)` because typed `Term.uaToEquiv proofTerm` requires
`proofTerm : Term ctx (Ty.id ...) ...` while typed `Term.oeqRefl`
produces `Term ctx (Ty.oeqType ...) ...` — different typed-Ty
heads, no typed bridge possible without first unifying `Ty.id` and
`Ty.oeqType` (the v1.1 D3.10 follow-up).  Therefore both
`uaReflEquivApply` and `uaReflEquivApplyDeep` ship raw-only,
listed in `isDocumentedRawOnlyParity` Section H.

## Connection to meta-level rule

At the meta-level, `Univalence.uaToEquivMeta_oeqRefl` proves that
the identity-typed witness collapses to `Equiv.refl _` and
`Equiv.refl.apply x = x` is a direct unfold.  The kernel-syntactic
raw rule shipped here is the cubical analog firing through the cd
cascade. -/

namespace LeanFX2

-- ============================
-- Section A: D3.6-S6 raw cascade — the headline round-trip-β rule
-- ============================

#print axioms LeanFX2.RawStep.par.uaReflEquivApply
#print axioms LeanFX2.RawStep.par.uaReflEquivApplyDeep

-- ============================
-- Section B: cd dispatchers for the outer + inner uaToEquiv-of-oeqRefl
-- shape (defined in Confluence/RawCd.lean) remain zero-axiom.
-- ============================

#print axioms LeanFX2.RawTerm.cdEquivApplyCase
#print axioms LeanFX2.RawTerm.cdUaToEquivApplyCase

-- ============================
-- Section C: surrounding cascade infrastructure remains zero-axiom
-- (proves S6 extension does not regress S1/S2/S3/S4/S5 or earlier
-- ctors — the load-bearing Tait–Martin-Löf pillars must stay clean
-- across the new arms).
-- ============================

#print axioms LeanFX2.RawStep.par.cd_lemma
#print axioms LeanFX2.RawStep.par.diamond
#print axioms LeanFX2.RawStep.par.cd_dominates

-- ============================
-- Section D: surrounding D3.6 cascade remains zero-axiom
-- ============================

#print axioms LeanFX2.RawStep.par.uaBeta
#print axioms LeanFX2.RawStep.par.uaBetaDeep
#print axioms LeanFX2.RawStep.par.uaToEquiv_inv
#print axioms LeanFX2.RawStep.par.oeqRefl_inv
#print axioms LeanFX2.RawStep.par.transpCompose
#print axioms LeanFX2.RawStep.par.transpComposeDeep
#print axioms LeanFX2.RawStep.par.pathCompose_inv
#print axioms LeanFX2.RawStep.par.idToEquivCong
#print axioms LeanFX2.RawStep.par.idToEquivRefl
#print axioms LeanFX2.RawStep.par.idToEquivReflDeep
#print axioms LeanFX2.RawStep.par.idToEquivCompose
#print axioms LeanFX2.RawStep.par.idToEquivComposeDeep
#print axioms LeanFX2.RawStep.par.idToEquiv_inv
#print axioms LeanFX2.RawStep.par.transpReflBeta
#print axioms LeanFX2.RawStep.par.transpReflBetaDeep
#print axioms LeanFX2.Step.transpReflBeta

end LeanFX2

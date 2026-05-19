import LeanFX2.Term.Rename
import LeanFX2.Term.Subst
import LeanFX2.Term.SubstHet
import LeanFX2.Term.Pointwise
import LeanFX2.Term.ToRaw
import LeanFX2.Algo.Eval
import LeanFX2.Algo.WHNF
import LeanFX2.Algo.Soundness
import LeanFX2.Algo.Progress
import LeanFX2.Reduction.Cumul
import LeanFX2.Reduction.CumulAllais
import LeanFX2.Reduction.CumulPairedEnv
import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.ConvBridge
import LeanFX2.Bridge

/-! # Smoke/AuditD36P3TermUaToEquiv — D3.6-P3 typed univalence-β extractor.

Phase D3.6-P3 ships the typed mirror of D3.6-P1's raw
`RawTerm.uaToEquiv`: `Term.uaToEquiv` is the typed univalence-β
extractor that produces `Ty.equiv leftTy rightTy` from a path-at-the-
universe `proof : Term context (Ty.id (Ty.universe innerLevel
innerLevelLt) leftTyRaw rightTyRaw) proofRaw`.  P3 is the typed-layer
counterpart — different files but same cascade discipline as P1's raw
layer.

## What this audit proves

* `Term.uaToEquiv` zero-axiom (new typed ctor with single typed
  subterm `proof`).
* `Term.toRaw_uaToEquiv` zero-axiom — the bridge `(Term.uaToEquiv ...
  proof).toRaw = RawTerm.uaToEquiv proof.toRaw` is `rfl` by the
  type-level index discipline.
* `Step.par.uaToEquivCong` zero-axiom (typed mirror of
  `RawStep.par.uaToEquivCong` — single-subterm parallel-cong rule).
* `Step.uaToEquivProof` zero-axiom (typed Step cong rule lifted to
  `Step.par.uaToEquivCong` via `Step.toPar`).
* `ConvCumul.uaToEquivCong` zero-axiom (Cumul cong rule).
* `ConvCumul.subst_compatible_uaToEquiv_allais` zero-axiom (Allais
  helper for substHet-compat of `Term.uaToEquiv`).
* The Algo cascade: `Term.HeadCtor.uaToEquiv`, `Term.headCtor`
  (re-exported), `Term.isWHNF` (re-exported) all preserve zero-axiom
  status with the new ctor's enumeration arm.
* `Step.par.toRawBridge` retains zero-axiom across the new
  `uaToEquivCong` arm.

## Architectural payoff

`Term.uaToEquiv` carries a single typed subterm `proof` and projects
to `RawTerm.uaToEquiv proof.toRaw` by construction.  Its rename /
subst / substHet / pointwise / Allais arms are the standard single-
subterm-cong shape (mirror of `Term.uaIntroHet`).  No type-equality
cast is needed because `Ty.equiv`, `Ty.universe`, and `Ty.id` are all
non-binder Ty constructors.  The strict-harness raw-only allowlist
entry for `RawStep.par.uaToEquivCong` is REMOVED in P3 since the
typed mirror `Step.par.uaToEquivCong` now ships.
-/

namespace LeanFX2

/-! ## Smoke: the new typed ctor and Step.par cong construct trivially. -/

example {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level scope)
    (leftTyRaw rightTyRaw : RawTerm scope)
    {proofRaw : RawTerm scope}
    (proof : Term context
               (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
               proofRaw) :
    Term context (Ty.equiv leftTy rightTy) (RawTerm.uaToEquiv proofRaw) :=
  Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
                 leftTyRaw rightTyRaw proof

example {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level scope)
    (leftTyRaw rightTyRaw : RawTerm scope)
    {proofRaw : RawTerm scope}
    (proof : Term context
               (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
               proofRaw) :
    Step.par (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
                             leftTyRaw rightTyRaw proof)
             (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
                             leftTyRaw rightTyRaw proof) :=
  Step.par.uaToEquivCong innerLevel innerLevelLt leftTy rightTy
                         leftTyRaw rightTyRaw (Step.par.refl proof)

/-! ## Audit declarations — all zero-axiom for D3.6-P3. -/

#print axioms LeanFX2.Term.uaToEquiv
#print axioms LeanFX2.Term.toRaw_uaToEquiv
#print axioms LeanFX2.Term.HeadCtor
#print axioms LeanFX2.Term.headCtor
#print axioms LeanFX2.Term.isWHNF
#print axioms LeanFX2.Term.rename
#print axioms LeanFX2.Term.subst
#print axioms LeanFX2.Term.substHet
#print axioms LeanFX2.Term.subst_pointwise
#print axioms LeanFX2.Step.par.uaToEquivCong
#print axioms LeanFX2.Step.uaToEquivProof
#print axioms LeanFX2.ConvCumul.uaToEquivCong
#print axioms LeanFX2.ConvCumul.subst_compatible_uaToEquiv_allais
#print axioms LeanFX2.Step.par.toRawBridge
#print axioms LeanFX2.Step.toConvCumul

end LeanFX2

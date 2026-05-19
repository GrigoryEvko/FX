import LeanFX2.Term.SubstHet
import LeanFX2.Term.Pointwise
import LeanFX2.Algo.Eval
import LeanFX2.Algo.WHNF
import LeanFX2.Algo.Soundness
import LeanFX2.Algo.Progress
import LeanFX2.Reduction.Cumul
import LeanFX2.Reduction.CumulAllais
import LeanFX2.Reduction.CumulPairedEnv
import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.ConvBridge
import LeanFX2.Reduction.Compat.HoTT
import LeanFX2.Bridge

/-! # Smoke/AuditD36P6Foundation — D3.6-P5+P6 univalence-β compat foundation rollup.

Phase D3.6-P5 closes the deferral from D3.6-P3+P4: the four
`Reduction.Compat.HoTT` lemmas that thread the typed univalence-β
extractor / application cong rules through `Term.rename` and
`Term.subst`.

Phase D3.6-P6 is the audit + smoke rollup: a single audit file
holding `#print axioms` for the entire D3.6 univalence-β foundation
(P1-P4 pre-existing, P5 new), plus the `step.par compat coverage`
budget tightening from 2 → 0 in `Tools/AuditAll/GatesBroad.lean`.

## What P5 ships (new in this commit)

* `Step.par.uaToEquivCong.rename_compatible` — single-subterm cong
  rule's rename arm.  Lifts a typed `Step.par` on the renamed inner
  `proof` subterm to a typed `Step.par` on the renamed
  `Term.uaToEquiv` ctor.  No `Ty.weaken_*_commute` cast needed —
  `Ty.equiv`, `Ty.universe`, and `Ty.id` are all non-binder Ty
  constructors.

* `Step.par.uaToEquivCong.subst_compatible` — same shape, subst
  variant.  Lifts a typed `Step.par` on the substituted inner
  `proof` to a typed `Step.par` on the substituted ctor.

* `Step.par.equivApplyCong.rename_compatible` — binary-subterm cong
  rule's rename arm.  Lifts two typed `Step.par`s (one on the
  renamed `equivTerm`, one on the renamed `argumentTerm`) to a
  typed `Step.par` on the renamed `Term.equivApply` ctor.  Mirror
  of `equivAppCong.rename_compatible`.

* `Step.par.equivApplyCong.subst_compatible` — same shape, subst
  variant.  Mirror of `equivAppCong.subst_compatible`.

## What P6 ships (audit + budget)

* This audit file `Smoke/AuditD36P6Foundation.lean` — the entire
  univalence-β foundation pinned to zero-axiom by `#print axioms`
  on every load-bearing decl spanning P1-P5.

* `Tools/AuditAll/GatesBroad.lean` — `step.par compat coverage`
  budget ratchets 2 → 0; the two cong rules introduced by P3+P4
  (`uaToEquivCong`, `equivApplyCong`) now have full
  `{rename,subst}_compatible` coverage.

## Architectural payoff

The deferral from D3.6-P3+P4 was a one-cong-rule budget bump
explicitly tracked in `GatesBroad.lean`'s ratchet log; P5+P6
closes the loop.  The compat lemmas are exactly the
substitution-stability witnesses that make confluence and the
typed → raw bridge go through across `Term.rename`/`Term.subst` —
without them, parallel reduction can step a term but the renamed/
substituted form does not, breaking the cd_lemma cascade.

The proof shapes are ~5-10 lines each because the underlying
ctor result types (`Ty.equiv carrierA carrierB` for `uaToEquiv`,
`carrierB` for `equivApply`) are non-binder, so the rename/subst
arms recurse structurally without `Ty.weaken_*_commute` casts.
-/

namespace LeanFX2

/-! ## Smoke: the four new compat lemmas typecheck trivially.

These smoke examples confirm the lemma signatures match the
expected callers (cd_lemma, Step.par.toRawBridge, the typed-confluence
infrastructure) — i.e. given a typed `Step.par` on the inner
subterm(s) post-rename / post-subst, we get a typed `Step.par` on
the post-rename / post-subst ctor application. -/

example {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    {proofRaw : RawTerm sourceScope}
    (proof : Term sourceCtx
               (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
               proofRaw) :
    Step.par
      (Term.rename termRenaming
        (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
                        leftTyRaw rightTyRaw proof))
      (Term.rename termRenaming
        (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
                        leftTyRaw rightTyRaw proof)) :=
  Step.par.uaToEquivCong.rename_compatible termRenaming
    innerLevel innerLevelLt leftTy rightTy leftTyRaw rightTyRaw
    (Step.par.refl (Term.rename termRenaming proof))

example {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    {proofRaw : RawTerm sourceScope}
    (proof : Term sourceCtx
               (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw rightTyRaw)
               proofRaw) :
    Step.par
      (Term.subst termSubst
        (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
                        leftTyRaw rightTyRaw proof))
      (Term.subst termSubst
        (Term.uaToEquiv innerLevel innerLevelLt leftTy rightTy
                        leftTyRaw rightTyRaw proof)) :=
  Step.par.uaToEquivCong.subst_compatible termSubst
    innerLevel innerLevelLt leftTy rightTy leftTyRaw rightTyRaw
    (Step.par.refl (Term.subst termSubst proof))

example {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    (equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw) :
    Step.par
      (Term.rename termRenaming (Term.equivApply equivTerm argumentTerm))
      (Term.rename termRenaming (Term.equivApply equivTerm argumentTerm)) :=
  Step.par.equivApplyCong.rename_compatible termRenaming
    (Step.par.refl (Term.rename termRenaming equivTerm))
    (Step.par.refl (Term.rename termRenaming argumentTerm))

example {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx sigma)
    {carrierA carrierB : Ty level sourceScope}
    {equivRaw argumentRaw : RawTerm sourceScope}
    (equivTerm : Term sourceCtx (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term sourceCtx carrierA argumentRaw) :
    Step.par
      (Term.subst termSubst (Term.equivApply equivTerm argumentTerm))
      (Term.subst termSubst (Term.equivApply equivTerm argumentTerm)) :=
  Step.par.equivApplyCong.subst_compatible termSubst
    (Step.par.refl (Term.subst termSubst equivTerm))
    (Step.par.refl (Term.subst termSubst argumentTerm))

/-! ## Audit declarations — all zero-axiom across the D3.6 foundation.

This is the comprehensive D3.6-P1..P5 zero-axiom rollup.  Each
`#print axioms` MUST report "does not depend on any axioms" or the
entire D3.6 foundation is compromised. -/

/-! ### D3.6-P1: raw `RawTerm.uaToEquiv` + raw cong + Raw foundation. -/

#print axioms LeanFX2.RawTerm.uaToEquiv
#print axioms LeanFX2.RawStep.par.uaToEquivCong

/-! ### D3.6-P2: raw `RawTerm.equivApply` + raw cong. -/

#print axioms LeanFX2.RawTerm.equivApply
#print axioms LeanFX2.RawStep.par.equivApplyCong

/-! ### D3.6-P3: typed `Term.uaToEquiv` + typed cong + cascade. -/

#print axioms LeanFX2.Term.uaToEquiv
#print axioms LeanFX2.Term.toRaw_uaToEquiv
#print axioms LeanFX2.Step.par.uaToEquivCong
#print axioms LeanFX2.Step.uaToEquivProof
#print axioms LeanFX2.ConvCumul.uaToEquivCong
#print axioms LeanFX2.ConvCumul.subst_compatible_uaToEquiv_allais

/-! ### D3.6-P4: typed `Term.equivApply` + typed cong + cascade. -/

#print axioms LeanFX2.Term.equivApply
#print axioms LeanFX2.Term.toRaw_equivApply
#print axioms LeanFX2.Step.par.equivApplyCong
#print axioms LeanFX2.Step.equivApplyEquiv
#print axioms LeanFX2.Step.equivApplyArgument
#print axioms LeanFX2.ConvCumul.equivApplyCong
#print axioms LeanFX2.ConvCumul.subst_compatible_equivApply_allais

/-! ### D3.6-P5: Reduction.Compat lemmas (NEW).

These are the two cong rules' four compat lemmas, closing the
deferral logged in `GatesBroad.lean`'s `step.par compat coverage`
ratchet (budget 2 → 0). -/

#print axioms LeanFX2.Step.par.uaToEquivCong.rename_compatible
#print axioms LeanFX2.Step.par.uaToEquivCong.subst_compatible
#print axioms LeanFX2.Step.par.equivApplyCong.rename_compatible
#print axioms LeanFX2.Step.par.equivApplyCong.subst_compatible

/-! ### D3.6 foundation: unchanged Term cascade decls cross-referenced.

These are the four cascade endpoints (`Term.rename`, `Term.subst`,
`Term.substHet`, `Term.subst_pointwise`) plus the typed → raw
bridge (`Step.par.toRawBridge`) and the cumul → step adapter
(`Step.toConvCumul`).  All must remain zero-axiom across the
P5 compat additions; the gates here are regression checks
catching any audit-time elaboration drift. -/

#print axioms LeanFX2.Term.HeadCtor
#print axioms LeanFX2.Term.headCtor
#print axioms LeanFX2.Term.isWHNF
#print axioms LeanFX2.Term.rename
#print axioms LeanFX2.Term.subst
#print axioms LeanFX2.Term.substHet
#print axioms LeanFX2.Term.subst_pointwise
#print axioms LeanFX2.Step.par.toRawBridge
#print axioms LeanFX2.Step.toConvCumul

end LeanFX2

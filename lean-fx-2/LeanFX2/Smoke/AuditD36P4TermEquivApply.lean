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

/-! # Smoke/AuditD36P4TermEquivApply — D3.6-P4 typed univalence-β application.

Phase D3.6-P4 ships the typed mirror of D3.6-P2's raw
`RawTerm.equivApply`: `Term.equivApply` is the typed univalence-β
application that produces the target carrier inhabitant from a
packaged equivalence and a source-side argument.  P4 is the typed-
layer counterpart — different files but same cascade discipline as
P2's raw layer.

## What this audit proves

* `Term.equivApply` zero-axiom (new typed binary ctor with two typed
  subterms `equivTerm, argumentTerm`).
* `Term.toRaw_equivApply` zero-axiom — the bridge `(Term.equivApply
  equivTerm argumentTerm).toRaw = RawTerm.equivApply equivTerm.toRaw
  argumentTerm.toRaw` is `rfl` by the type-level index discipline.
* `Step.par.equivApplyCong` zero-axiom (typed mirror of
  `RawStep.par.equivApplyCong` — binary-subterm parallel-cong rule).
* `Step.equivApplyEquiv` and `Step.equivApplyArgument` zero-axiom
  (typed Step cong rules lifted to `Step.par.equivApplyCong` via
  `Step.toPar`, mirroring `equivAppEquiv`/`equivAppArgument`).
* `ConvCumul.equivApplyCong` zero-axiom (Cumul cong rule).
* `ConvCumul.subst_compatible_equivApply_allais` zero-axiom (Allais
  helper for substHet-compat of `Term.equivApply`).
* The Algo cascade: `Term.HeadCtor.equivApply`, `Term.headCtor`
  (re-exported), `Term.isWHNF` (re-exported) all preserve zero-axiom
  status with the new ctor's enumeration arm.
* `Step.par.toRawBridge` retains zero-axiom across the new
  `equivApplyCong` arm.

## Architectural payoff

`Term.equivApply` carries two typed subterms `equivTerm,
argumentTerm` and projects to `RawTerm.equivApply equivTerm.toRaw
argumentTerm.toRaw` by construction.  Its rename / subst / substHet /
pointwise / Allais arms are the standard binary-subterm-cong shape
(mirror of `Term.equivApp`).  No type-equality cast is needed because
`Ty.equiv` and `carrierB` are non-binder Ty constructors.  The
strict-harness raw-only allowlist entry for
`RawStep.par.equivApplyCong` is REMOVED in P4 since the typed mirror
`Step.par.equivApplyCong` now ships.
-/

namespace LeanFX2

/-! ## Smoke: the new typed ctor and Step.par cong construct trivially. -/

example {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term context carrierA argumentRaw) :
    Term context carrierB (RawTerm.equivApply equivRaw argumentRaw) :=
  Term.equivApply equivTerm argumentTerm

example {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term context carrierA argumentRaw) :
    Step.par (Term.equivApply equivTerm argumentTerm)
             (Term.equivApply equivTerm argumentTerm) :=
  Step.par.equivApplyCong (Step.par.refl equivTerm) (Step.par.refl argumentTerm)

/-! ## Audit declarations — all zero-axiom for D3.6-P4. -/

#print axioms LeanFX2.Term.equivApply
#print axioms LeanFX2.Term.toRaw_equivApply
#print axioms LeanFX2.Term.HeadCtor
#print axioms LeanFX2.Term.headCtor
#print axioms LeanFX2.Term.isWHNF
#print axioms LeanFX2.Term.rename
#print axioms LeanFX2.Term.subst
#print axioms LeanFX2.Term.substHet
#print axioms LeanFX2.Term.subst_pointwise
#print axioms LeanFX2.Step.par.equivApplyCong
#print axioms LeanFX2.Step.equivApplyEquiv
#print axioms LeanFX2.Step.equivApplyArgument
#print axioms LeanFX2.ConvCumul.equivApplyCong
#print axioms LeanFX2.ConvCumul.subst_compatible_equivApply_allais
#print axioms LeanFX2.Step.par.toRawBridge
#print axioms LeanFX2.Step.toConvCumul

end LeanFX2

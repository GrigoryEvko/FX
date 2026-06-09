import FX1Poly.Typed.ReducibleEnvOfWfContext
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Typed.WfContextDescPi

/-! # FX1Poly/Typed/GrownWfOpenStronglyNormalizing — open SN under GROWN context well-formedness

The shipped unconditional open SN (`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`) is keyed on
the FORMATION well-formedness `WfContextDesc` (binding types typed by the formation engine).  The
pinned-reflection motive (`PinnedReflectionConclusion`) carries the GROWN well-formedness
`WfContextDescPi` instead — and grown wf does NOT imply formation wf (a grown-typed binding type,
e.g. an application typed by `piElim`, has no formation derivation).  The piElim-residual whnf
dispatcher needs SN of the target-side function under exactly the grown premise, so this file
ships the grown-wf twins:

  * `reducibleEnvOfWfContextDescPi` — mirror of `reducibleEnvOfWfContextDesc` where the head
    binding's grown typing reads DIRECTLY off the grown wf's cons component
    (`WfContextDescPi.headIsType`), with the formation→grown embedding step deleted; everything
    downstream (`BoundExceedsPi.existsBound`, `subjectReducibleAsTypeUnderEnv`, the var-0 head,
    SUM bounds) already operates on grown derivations.
  * `HasTypeDescPi.stronglyNormalizingOfWfContextDescPi` — the open SN assembly over it,
    verbatim the `stronglyNormalizingOfWfContextDesc` wire.

Same zero-axiom discipline as the formation versions: SUM bounds via `Nat.le_add_*` (NOT `max` —
`Nat.le_max_*` leak `propext`), telescope induction on `TypingContext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **The reducible closing environment for a GROWN-well-formed context.**  Mirror of
`reducibleEnvOfWfContextDesc` over `WfContextDescPi`: each binding's grown universe typing is the
wf's own cons component (`WfContextDescPi.headIsType`) — no formation→grown embedding — and the
rest is the identical telescope induction with the var-0 head and propext-free SUM bounds. -/
theorem reducibleEnvOfWfContextDescPi {profile : PolyProfile} (env : Nat → Nat) :
    ∀ {scope : Nat} (context : TypingContext profile scope), WfContextDescPi context →
      ∃ bound : Nat, ∃ substitution : RawTermSubst scope 1,
        ReducibleEnvAtBounded env bound context substitution := by
  intro scope context
  induction context with
  | empty =>
      intro _wf
      exact ⟨0, Fin.elim0, ReducibleEnvAtBounded.empty (Fin.elim0 : RawTermSubst 0 1)⟩
  | cons restContext bindingType ih =>
      intro wf
      obtain ⟨boundRest, substRest, envRest⟩ := ih (WfContextDescPi.tailWellFormed wf)
      obtain ⟨levelExpr, flag, bindingTyped⟩ := WfContextDescPi.headIsType wf
      obtain ⟨boundBinding, budget⟩ := BoundExceedsPi.existsBound (env := env) bindingTyped
      have envRestLifted :
          ReducibleEnvAtBounded env (boundRest + boundBinding) restContext substRest :=
        fun index => (envRest index).cumulative (Nat.le_add_right boundRest boundBinding)
      have budgetLifted : BoundExceedsPi env (boundRest + boundBinding) bindingTyped :=
        BoundExceedsPi.monotoneInBound (Nat.le_add_left boundBinding boundRest) budget
      have typeReducible : IsReducibleTypeAtBounded env (boundRest + boundBinding)
          (RawTerm.subst substRest bindingType) :=
        bindingTyped.subjectReducibleAsTypeUnderEnv budgetLifted envRestLifted
      have headMember : IsReducibleMemberAtBounded env (boundRest + boundBinding)
          (RawTerm.subst substRest bindingType)
          (.mkGen .gen_var ⟨0, Nat.zero_lt_one⟩ .childNil) :=
        IsReducibleMemberAtBounded.ofVariable ⟨0, Nat.zero_lt_one⟩ typeReducible
      exact ⟨boundRest + boundBinding,
        RawTermSubst.cons (.mkGen .gen_var ⟨0, Nat.zero_lt_one⟩ .childNil) substRest,
        ReducibleEnvAtBounded.cons envRestLifted headMember⟩

/-- **Open strong normalization under GROWN context well-formedness**: for any grown-well-formed
context, every grown-typed subject is strongly normalizing.  The `WfContextDesc`-keyed wire
(`stronglyNormalizingOfWfContextDesc`) verbatim, over `reducibleEnvOfWfContextDescPi`.  The SN
supply for the pinned-reflection whnf dispatcher, whose motive carries exactly this wf. -/
theorem HasTypeDescPi.stronglyNormalizingOfWfContextDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDescPi context)
    (d : HasTypeDescPi profile context subject classifier) :
    StepStar.IsStronglyNormalizing subject := by
  obtain ⟨boundDerivation, budgetDerivation⟩ := BoundExceedsPi.existsBound (env := fun _ => 0) d
  obtain ⟨boundEnvironment, substitution, environmentReducible⟩ :=
    reducibleEnvOfWfContextDescPi (fun _ => 0) context contextWellFormed
  exact d.stronglyNormalizingOfReducibleEnv
    (BoundExceedsPi.monotoneInBound (Nat.le_add_right boundDerivation boundEnvironment) budgetDerivation)
    (fun index => (environmentReducible index).cumulative
      (Nat.le_add_left boundEnvironment boundDerivation))

end FX1Poly.Typed

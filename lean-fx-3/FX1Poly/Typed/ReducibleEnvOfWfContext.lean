import FX1Poly.Typed.BoundedBindingTypeReducible
import FX1Poly.Typed.BoundedNeutralMember
import FX1Poly.Typed.BoundExceedsPiDischarge
import FX1Poly.Typed.WfContextDesc

/-! # FX1Poly/Typed/ReducibleEnvOfWfContext
    — the reducible closing environment for a well-formed context (toward open strong normalization)

`reducibleEnvOfWfContextDesc`: every formation-well-formed context `Γ` admits a bound and a closing substitution
under which it is a bound-reducible environment.  This is the env half of the `OpenStronglyNormalizing.lean`
residual — the classical reducible-substitution lemma — built by induction on the context telescope, over the
`HasTypeDesc`-defined `WfContextDesc`.

## The "var 0 head" trick (sidesteps all renaming closure)

The closing substitution sends EVERY context variable to `var 0 ∈ scope 1` (a neutral).  Because:
  * `IsReducibleMemberAtBounded.ofVariable` admits ANY variable as a member of any bounded-reducible type,
  * and SN reflects through ANY substitution (`stronglyNormalizing_of_subst`),
the substitution need not be a renaming/weakening — so NO bounded reducibility-under-renaming is required.  The
substitution is the nested `RawTermSubst.cons (var 0) (cons (var 0) … Fin.elim0)`, landing in `scope 1`
(`targetScope = 0`, matching the FT's `targetScope + 1` motive).

## The induction (one global SUM bound)

Telescope induction via `ReducibleEnvAtBounded.cons`.  At each `Γ'.cons T` step:
  * the IH gives `⟨boundRest, substRest, envRest⟩` for `Γ'`;
  * `WfContextDesc.headIsTypeDesc` reads the binding's `IsTypeDesc` derivation directly off the description
    engine, and the native formation→grown embedding `HasTypeDesc.toHasTypeDescPi` grows it; then
    `BoundExceedsPi.existsBound` budgets it at `boundBinding`;
  * the global bound is the SUM `boundRest + boundBinding` (NOT `max` — `Nat.le_max_left/right` depend on
    `propext`; `Nat.le_add_right/left` are axiom-free, the same discipline `existsBound` itself uses);
  * the IH env lifts to the sum bound (`IsReducibleMemberAtBounded.cumulative`, pointwise), the budget lifts
    (`BoundExceedsPi.monotoneInBound`);
  * `subjectReducibleAsTypeUnderEnv` makes `subst substRest T` bound-reducible-as-type, and
    `IsReducibleMemberAtBounded.ofVariable` puts `var 0` in it; `.cons` extends the environment.

## Zero-axiom verification

`induction` on `TypingContext` (clean recursor; the scope-dependent goal generalizes without a propext cast),
the variable-membership and binding-type-reducibility leaves, cumulativity/monotonicity lifts, and SUM bounds
via `Nat.le_add_*`.  Checked to depend on NO axioms — `propext`-clean (a `max`-based formulation leaks `propext`
purely through `Nat.le_max_*`).  No `sorry`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **The reducible closing environment for a formation-well-formed context, over `WfContextDesc`.**
Every formation-well-formed `context` admits a bound and a closing substitution (the "every variable to
`var 0`" substitution) under which it is a bound-reducible environment.  Telescope induction:
`subjectReducibleAsTypeUnderEnv` makes each binding type reducible, `IsReducibleMemberAtBounded.ofVariable`
puts the variable in it, `.cons` extends, and a SUM bound (`Nat.le_add_*`, propext-free) coordinates the
per-entry budgets.  Each binding's type-hood is read off `WfContextDesc.headIsTypeDesc` (`= wellFormed.2`, an
`IsTypeDesc` the description engine supplies) and grown through the formation→grown embedding
`HasTypeDesc.toHasTypeDescPi`.  Since the grown context-validity presupposition provably FAILS
(`HasTypeDescPi Γ t T → WfContextDesc Γ` is false — there are ill-formed contexts that still type a subject,
`ContextValidityFails`), the wf-hypothesis is genuinely external rather than derivable.  The env half of the
`OpenStronglyNormalizing` residual; the target the open-SN consumers compose with. -/
theorem reducibleEnvOfWfContextDesc {profile : PolyProfile} (env : Nat → Nat) :
    ∀ {scope : Nat} (context : TypingContext profile scope), WfContextDesc context →
      ∃ bound : Nat, ∃ substitution : RawTermSubst scope 1,
        ReducibleEnvAtBounded env bound context substitution := by
  intro scope context
  induction context with
  | empty =>
      intro _wf
      exact ⟨0, Fin.elim0, ReducibleEnvAtBounded.empty (Fin.elim0 : RawTermSubst 0 1)⟩
  | cons restContext bindingType ih =>
      intro wf
      obtain ⟨boundRest, substRest, envRest⟩ := ih (WfContextDesc.tailWellFormed wf)
      obtain ⟨levelExpr, flag, hasTypeDescDeriv⟩ := WfContextDesc.headIsTypeDesc wf
      have descPiDeriv : HasTypeDescPi profile restContext bindingType (universeCodeCell levelExpr flag) :=
        hasTypeDescDeriv.toHasTypeDescPi
      obtain ⟨boundBinding, budget⟩ := BoundExceedsPi.existsBound (env := env) descPiDeriv
      have envRestLifted :
          ReducibleEnvAtBounded env (boundRest + boundBinding) restContext substRest :=
        fun index => (envRest index).cumulative (Nat.le_add_right boundRest boundBinding)
      have budgetLifted : BoundExceedsPi env (boundRest + boundBinding) descPiDeriv :=
        BoundExceedsPi.monotoneInBound (Nat.le_add_left boundBinding boundRest) budget
      have typeReducible : IsReducibleTypeAtBounded env (boundRest + boundBinding)
          (RawTerm.subst substRest bindingType) :=
        descPiDeriv.subjectReducibleAsTypeUnderEnv budgetLifted envRestLifted
      have headMember : IsReducibleMemberAtBounded env (boundRest + boundBinding)
          (RawTerm.subst substRest bindingType)
          (.mkGen .gen_var ⟨0, Nat.zero_lt_one⟩ .childNil) :=
        IsReducibleMemberAtBounded.ofVariable ⟨0, Nat.zero_lt_one⟩ typeReducible
      exact ⟨boundRest + boundBinding,
        RawTermSubst.cons (.mkGen .gen_var ⟨0, Nat.zero_lt_one⟩ .childNil) substRest,
        ReducibleEnvAtBounded.cons envRestLifted headMember⟩

end FX1Poly.Typed

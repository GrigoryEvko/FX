import FX1Poly.Typed.BoundedBindingTypeReducible
import FX1Poly.Typed.BoundedNeutralMember
import FX1Poly.Typed.BoundExceedsPiDischarge
import FX1Poly.Typed.WfContext
import FX1Poly.Typed.HasTypeDescClosedForms

/-! # FX1Poly/Typed/ReducibleEnvOfWfContext
    — the reducible closing environment for a well-formed context (OB-3, toward OPEN SN-043)

`reducibleEnvOfWfContext`: every well-formed context `Γ` admits a bound and a closing substitution under which
it is a bound-reducible environment.  This is the env half of the `OpenStronglyNormalizing.lean` residual — the
classical reducible-substitution lemma — built by induction on the context telescope.

## The "var 0 head" trick (sidesteps all renaming closure)

The closing substitution sends EVERY context variable to `var 0 ∈ scope 1` (a neutral).  Because:
  * OB-1 (`IsReducibleMemberAtBounded.ofVariable`) admits ANY variable as a member of any bounded-reducible type,
  * and SN reflects through ANY substitution (`stronglyNormalizing_of_subst`, used downstream in OB-5),
the substitution need not be a renaming/weakening — so NO bounded reducibility-under-renaming (the SN-040
analogue) is required.  The substitution is the nested `RawTermSubst.cons (var 0) (cons (var 0) … Fin.elim0)`,
landing in `scope 1` (`targetScope = 0`, matching the FT's `targetScope + 1` motive).

## The induction (one global SUM bound)

Telescope induction via `ReducibleEnvAtBounded.cons`.  At each `Γ'.cons T` step:
  * the IH gives `⟨boundRest, substRest, envRest⟩` for `Γ'`;
  * `WfContext.headIsType` + `HasType.toHasTypeDesc`/`.toHasTypeDescPi` grow the binding's `IsType` derivation,
    and `BoundExceedsPi.existsBound` budgets it at `boundBinding`;
  * the global bound is the SUM `boundRest + boundBinding` (NOT `max` — `Nat.le_max_left/right` depend on
    `propext`; `Nat.le_add_right/left` are axiom-free, the same discipline `existsBound` itself uses);
  * the IH env lifts to the sum bound (`IsReducibleMemberAtBounded.cumulative`, pointwise), the budget lifts
    (`BoundExceedsPi.monotoneInBound`);
  * OB-2 (`subjectReducibleAsTypeUnderEnv`) makes `subst substRest T` bound-reducible-as-type, and OB-1 puts
    `var 0` in it; `.cons` extends the environment.

## Zero-axiom verification

`induction` on `TypingContext` (clean recursor; the scope-dependent goal generalizes without a propext cast),
the shipped OB-1/OB-2 leaves, cumulativity/monotonicity lifts, and SUM bounds via `Nat.le_add_*`.  Checked to
depend on NO axioms — `propext`-clean (the original `max`-based attempt leaked `propext` purely through
`Nat.le_max_*`).  No `sorry`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **OB-3: the reducible closing environment for a well-formed context.**  Every well-formed `context` admits a
bound and a closing substitution (the "every variable to `var 0`" substitution) under which it is a
bound-reducible environment.  Telescope induction: OB-2 makes each binding type reducible, OB-1 puts the variable
in it, `.cons` extends, and a SUM bound (`Nat.le_add_*`, propext-free) coordinates the per-entry budgets.  The env
half of `reducibleEnvOfWfContext` (the `OpenStronglyNormalizing` residual); OB-4 bundles the main derivation's
budget at the same bound. -/
theorem reducibleEnvOfWfContext {profile : PolyProfile} (env : Nat → Nat) :
    ∀ {scope : Nat} (context : TypingContext profile scope), WfContext context →
      ∃ bound : Nat, ∃ substitution : RawTermSubst scope 1,
        ReducibleEnvAtBounded env bound context substitution := by
  intro scope context
  induction context with
  | empty =>
      intro _wf
      exact ⟨0, Fin.elim0, ReducibleEnvAtBounded.empty (Fin.elim0 : RawTermSubst 0 1)⟩
  | cons restContext bindingType ih =>
      intro wf
      obtain ⟨boundRest, substRest, envRest⟩ := ih (WfContext.tailWellFormed wf)
      obtain ⟨levelExpr, flag, hasTypeDeriv⟩ := WfContext.headIsType wf
      have descPiDeriv : HasTypeDescPi profile restContext bindingType (universeCodeCell levelExpr flag) :=
        (HasType.toHasTypeDesc hasTypeDeriv).toHasTypeDescPi
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

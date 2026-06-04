import FX1Poly.Typed.DenoteKeyedBoundedReducibility
import FX1Poly.Typed.ReducibleEnvAt

/-! # FX1Poly/Typed/DenoteKeyedBoundedReducibleEnv
    — the bound-carrying reducible member predicate + closing-substitution environment
      (the foundational layer of the bounded fundamental theorem; #753 toward SN-043)

The bound-carrying analogue of `DenoteKeyedReducibleEnv.lean` (`IsReducibleMemberAtDenote` /
`ReducibleEnvAtDenote`): where the denote environment rides on `IsReducibleMemberAtDenote env level`, this one
rides on `IsReducibleMemberAtBounded env bound` — whose underlying type relation is the universe-label-AWARE
`ReducibleTypeAtBounded` (the gated relation whose cumulativity is FREE, `stepBounded_cumulative`, and whose
reducibility-candidate bundle is UNCONDITIONAL, `ReducibleTypeAtBounded.isReducibilityCandidate`).

This is the closing-substitution environment the bounded fundamental theorem will consume to discharge the
non-uniform `genFormationPi` `piReducibleAsType` that the denote relation leaves MODEL-OBSTRUCTED
(`DenoteKeyedCumulativityObstruction.gapUniverseDomainPiVacuouslyReducibleAtLowLevel`: a gap-universe-domain Π is
codomain-blindly reducible at low denote levels, so it carries no information to lift up).  In the gated relation
the obstruction evaporates — `Type@gapLevel` is simply not bound-reducible at bounds ≤ `denote gapLevel`, so the
vacuous low-bound derivation never exists.

`ReducibleEnvAtBounded env bound context substitution` says the substitution sends each context variable to a
bound-reducible member (at `bound`) of that variable's looked-up type, itself closed by the same substitution:

  `∀ index, IsReducibleMemberAtBounded env bound (subst substitution (context.lookup index)) (substitution index)`.

## Zero-axiom verification

Character-identical to `DenoteKeyedReducibleEnv.lean` with `bound` riding where `level` rode and the bounded
member predicate replacing the denote one: a `∀`-quantified `def`; `lookupReducible` is the projection; `empty`
is `Fin.elim0`; `cons` is the `Fin`-position split (`⟨0,_⟩` / `⟨k+1,_⟩`, the propext-free structure match) whose
lookups are rewritten by `TypingContext.lookup_cons_zero` / `lookup_cons_succ` and the weakening cancellation
`RawTerm.weaken_subst_cons`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation

/-- **Semantic member (bound-carrying).**  `term` is a bound-reducible member of `typeCode` at `bound` when
`typeCode` is bound-reducible there with some candidate and `term` lies in it.  The bounded analogue of
`IsReducibleMemberAtDenote`; its candidate is an UNCONDITIONAL reducibility candidate
(`ReducibleTypeAtBounded.isReducibilityCandidate`, at `scope + 1`), unlike the denote member whose CR1 carried a
predicative caveat. -/
def IsReducibleMemberAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (typeCode term : RawTerm scope) : Prop :=
  ∃ candidate : RawTerm scope → Prop, ReducibleTypeAtBounded env bound typeCode candidate ∧ candidate term

/-- The bound-carrying level-indexed reducible closing-substitution environment: `substitution` sends each
context variable to a bound-reducible member (at `bound`) of that variable's looked-up type, itself closed by
the same substitution.  The bounded analogue of `ReducibleEnvAtDenote`, riding on `IsReducibleMemberAtBounded`
so each type variable's candidate is a member of the universe-label-aware bounded relation. -/
def ReducibleEnvAtBounded {profile : PolyProfile} {scope targetScope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope)
    (substitution : RawTermSubst scope targetScope) : Prop :=
  ∀ index : Fin scope,
    IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution (context.lookup index)) (substitution index)

/-- The `var` case of the bounded fundamental theorem: a bound-reducible environment sends each variable to a
bound-reducible member (at `bound`) of its looked-up (closed) type. -/
theorem ReducibleEnvAtBounded.lookupReducible {profile : PolyProfile} {scope targetScope : Nat}
    {env : Nat → Nat} {bound : Nat}
    {context : TypingContext profile scope} {substitution : RawTermSubst scope targetScope}
    (envReducible : ReducibleEnvAtBounded env bound context substitution) (index : Fin scope) :
    IsReducibleMemberAtBounded env bound
      (RawTerm.subst substitution (context.lookup index)) (substitution index) :=
  envReducible index

/-- Every substitution is bound-reducible at every bound for the empty context (vacuous: `Fin 0` is
uninhabited) — the base environment turning the bounded fundamental theorem into the closed-term bound-
reducibility corollary. -/
theorem ReducibleEnvAtBounded.empty {profile : PolyProfile} {targetScope : Nat}
    {env : Nat → Nat} {bound : Nat} (substitution : RawTermSubst 0 targetScope) :
    ReducibleEnvAtBounded env bound (TypingContext.empty : TypingContext profile 0) substitution :=
  fun index => index.elim0

/-- Extend a bound-reducible environment at a binder (the Π-introduction step): given a bound-reducible
environment for `context` and a bound-reducible member (at `bound`) `headTerm` of the new binding's closed type,
the `cons`-extended substitution is bound-reducible for `context.cons bindingType`.  Variable 0 lands on
`headTerm` (its weakened lookup of `bindingType` cancels to `subst tailSubst bindingType`); variable `k+1`
recurses into the tail.  Character-identical to `ReducibleEnvAtDenote.cons`, the `env`/`bound` riding along. -/
theorem ReducibleEnvAtBounded.cons {profile : PolyProfile} {scope targetScope : Nat}
    {env : Nat → Nat} {bound : Nat}
    {context : TypingContext profile scope} {bindingType : RawTerm scope}
    {tailSubst : RawTermSubst scope targetScope} {headTerm : RawTerm targetScope}
    (tailReducible : ReducibleEnvAtBounded env bound context tailSubst)
    (headReducible : IsReducibleMemberAtBounded env bound (RawTerm.subst tailSubst bindingType) headTerm) :
    ReducibleEnvAtBounded env bound (context.cons bindingType) (RawTermSubst.cons headTerm tailSubst) := by
  intro index
  match index with
  | ⟨0, isLt⟩ =>
      rw [TypingContext.lookup_cons_zero context bindingType isLt,
        RawTerm.weaken_subst_cons bindingType headTerm tailSubst]
      exact headReducible
  | ⟨position + 1, isLtSucc⟩ =>
      rw [TypingContext.lookup_cons_succ context bindingType position isLtSucc,
        RawTerm.weaken_subst_cons
          (context.lookup ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩) headTerm tailSubst]
      exact tailReducible ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩

end FX1Poly.Typed

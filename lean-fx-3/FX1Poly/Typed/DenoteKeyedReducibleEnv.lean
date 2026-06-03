import FX1Poly.Typed.DenoteKeyedReducibility
import FX1Poly.Typed.ReducibleEnvAt

/-! # FX1Poly/Typed/DenoteKeyedReducibleEnv
    — the denote-keyed reducible closing-substitution environment (route C toward the denote fundamental theorem)

The denote analogue of `ReducibleEnvAt`: where the fuel env rides on `IsReducibleMemberAt level`, this one
rides on `IsReducibleMemberAtDenote env level` — whose universe arm decodes each type variable's candidate at
the FIXED classifier level `denote levelExpr env` rather than at ambient-fuel-minus-one.  It is the closing-
substitution environment the denote fundamental theorem (the non-fuel re-basing toward SN-043, route D) will
consume: the `var` arm reads `lookupReducible`, the Π-introduction binder arm extends via `cons`, and the
empty context turns the theorem into the closed-term denote-reducibility corollary via `empty`.

`ReducibleEnvAtDenote env level context substitution` says the substitution sends each context variable to a
denote-reducible member (at `level`) of that variable's looked-up type, itself closed by the same substitution:

  `∀ index, IsReducibleMemberAtDenote env level (subst substitution (context.lookup index)) (substitution index)`.

## Zero-axiom verification

A `∀`-quantified `def`; `lookupReducible` is the projection; `empty` is `Fin.elim0`; `cons` is the `Fin`-
position split (`⟨0,_⟩` / `⟨k+1,_⟩`, the propext-free structure match) whose lookups are rewritten by
`TypingContext.lookup_cons_zero` / `lookup_cons_succ` and the weakening cancellation `RawTerm.weaken_subst_cons`
— the `env`/`level` ride along untouched, so the proofs are character-identical to `ReducibleEnvAt`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation

/-- The denote-keyed level-indexed reducible closing-substitution environment: `substitution` sends each
context variable to a denote-reducible member (at `level`) of that variable's looked-up type, itself closed by
the same substitution.  The denote analogue of `ReducibleEnvAt`, riding on `IsReducibleMemberAtDenote` so each
type variable's candidate decodes at the fixed classifier level. -/
def ReducibleEnvAtDenote {profile : PolyProfile} {scope targetScope : Nat} (env : Nat → Nat) (level : Nat)
    (context : TypingContext profile scope)
    (substitution : RawTermSubst scope targetScope) : Prop :=
  ∀ index : Fin scope,
    IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution (context.lookup index)) (substitution index)

/-- The `var` case of the denote fundamental theorem: a denote-reducible environment sends each variable to a
denote-reducible member (at `level`) of its looked-up (closed) type. -/
theorem ReducibleEnvAtDenote.lookupReducible {profile : PolyProfile} {scope targetScope : Nat}
    {env : Nat → Nat} {level : Nat}
    {context : TypingContext profile scope} {substitution : RawTermSubst scope targetScope}
    (envReducible : ReducibleEnvAtDenote env level context substitution) (index : Fin scope) :
    IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution (context.lookup index)) (substitution index) :=
  envReducible index

/-- Every substitution is denote-reducible at every level for the empty context (vacuous: `Fin 0` is
uninhabited) — the base environment turning the denote fundamental theorem into the closed-term denote-
reducibility corollary. -/
theorem ReducibleEnvAtDenote.empty {profile : PolyProfile} {targetScope : Nat}
    {env : Nat → Nat} {level : Nat} (substitution : RawTermSubst 0 targetScope) :
    ReducibleEnvAtDenote env level (TypingContext.empty : TypingContext profile 0) substitution :=
  fun index => index.elim0

/-- Extend a denote-reducible environment at a binder (the Π-introduction step): given a denote-reducible
environment for `context` and a denote-reducible member (at `level`) `headTerm` of the new binding's closed
type, the `cons`-extended substitution is denote-reducible for `context.cons bindingType`.  Variable 0 lands on
`headTerm` (its weakened lookup of `bindingType` cancels to `subst tailSubst bindingType`); variable `k+1`
recurses into the tail.  Character-identical to `ReducibleEnvAt.cons`, the `env`/`level` riding along. -/
theorem ReducibleEnvAtDenote.cons {profile : PolyProfile} {scope targetScope : Nat}
    {env : Nat → Nat} {level : Nat}
    {context : TypingContext profile scope} {bindingType : RawTerm scope}
    {tailSubst : RawTermSubst scope targetScope} {headTerm : RawTerm targetScope}
    (tailReducible : ReducibleEnvAtDenote env level context tailSubst)
    (headReducible : IsReducibleMemberAtDenote env level (RawTerm.subst tailSubst bindingType) headTerm) :
    ReducibleEnvAtDenote env level (context.cons bindingType) (RawTermSubst.cons headTerm tailSubst) := by
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

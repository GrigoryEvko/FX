import FX1Poly.Typed.DenoteKeyedReducibility
import FX1Poly.Typed.ReducibleEnvAt

/-! Scratch C: the denote-keyed reducible closing-substitution environment — the denote analogue of
`ReducibleEnvAt`, riding on `IsReducibleMemberAtDenote env level` instead of `IsReducibleMemberAt level`. The
`cons` proof is character-identical to the fuel version (the rewrites touch only the looked-up type and the
substituted term; the denote member predicate's env/level ride along untouched). Foundation for the denote
fundamental theorem (route D). -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Foundation

/-- The denote-keyed level-indexed reducible closing-substitution environment: `substitution` sends each
context variable to a denote-reducible member (at `level`) of that variable's looked-up type, itself closed by
the same substitution.  The denote analogue of `ReducibleEnvAt`. -/
def ReducibleEnvAtDenote {profile : PolyProfile} {scope targetScope : Nat} (env : Nat → Nat) (level : Nat)
    (context : TypingContext profile scope)
    (substitution : RawTermSubst scope targetScope) : Prop :=
  ∀ index : Fin scope,
    IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution (context.lookup index)) (substitution index)

/-- The `var` case: a denote-reducible environment sends each variable to a denote-reducible member of its
looked-up (closed) type. -/
theorem ReducibleEnvAtDenote.lookupReducible {profile : PolyProfile} {scope targetScope : Nat}
    {env : Nat → Nat} {level : Nat}
    {context : TypingContext profile scope} {substitution : RawTermSubst scope targetScope}
    (envReducible : ReducibleEnvAtDenote env level context substitution) (index : Fin scope) :
    IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution (context.lookup index)) (substitution index) :=
  envReducible index

/-- Every substitution is denote-reducible at every level for the empty context (vacuous: `Fin 0` is
uninhabited) — the base environment turning the denote fundamental theorem into the closed-term corollary. -/
theorem ReducibleEnvAtDenote.empty {profile : PolyProfile} {targetScope : Nat}
    {env : Nat → Nat} {level : Nat} (substitution : RawTermSubst 0 targetScope) :
    ReducibleEnvAtDenote env level (TypingContext.empty : TypingContext profile 0) substitution :=
  fun index => index.elim0

/-- Extend a denote-reducible environment at a binder (the Π-introduction step): given a denote-reducible
environment for `context` and a denote-reducible member (at `level`) `headTerm` of the new binding's closed
type, the `cons`-extended substitution is denote-reducible for `context.cons bindingType`.  Character-identical
to `ReducibleEnvAt.cons`: variable 0 lands on `headTerm`, variable `k+1` recurses into the tail. -/
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

#print axioms FX1Poly.Typed.ReducibleEnvAtDenote.lookupReducible
#print axioms FX1Poly.Typed.ReducibleEnvAtDenote.empty
#print axioms FX1Poly.Typed.ReducibleEnvAtDenote.cons

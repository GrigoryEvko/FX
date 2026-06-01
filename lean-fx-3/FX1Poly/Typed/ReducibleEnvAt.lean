import FX1Poly.Core.StratifiedReducibleMember
import FX1Poly.Core.RawTermSubstConsCommute
import FX1Poly.Typed.TypingContext

/-! # FX1Poly/Typed/ReducibleEnvAt
    — the level-indexed reducible closing-substitution environment for the fundamental theorem (#425)

The stratified (Tarski-universe) port of `ReducibleEnv`.  Where the pure-SN `ReducibleEnv` rides on
`IsReducibleMember` — whose interpretation dispatches on the syntactic head and so collapses a redex-typed
variable to bare strong normalization (the conv-invariance gap at type variables) — `ReducibleEnvAt level`
rides on the level-indexed `IsReducibleMemberAt level`, whose universe arm carries each type variable's
candidate ONE LEVEL DOWN.  That is precisely the structure the fundamental theorem's `conv` arm needs to
close at a type variable `x : Type@k`: the environment entry `IsReducibleMemberAt level (universeCode k)
(γ x)` unfolds to `SN (γ x) ∧ ∃ candidate, ReducibleTypeAt (level - 1) (γ x) candidate`, handing the
reclassifier the lower-level candidate the conv arm transports.

`ReducibleEnvAt level context substitution` says the substitution sends EACH context variable to a
reducible member (at `level`) of that variable's looked-up type, itself closed by the same substitution:

  `∀ index, IsReducibleMemberAt level (subst substitution (context.lookup index)) (substitution index)`.

The ∀-form keeps the fundamental theorem's `var` case IMMEDIATE (`lookupReducible`) and avoids any
function-extensionality on the substitution.  The `level` index is INERT through the `cons` binder
extension — its rewrites touch only the looked-up TYPE and the SUBSTITUTED TERM, never the membership
predicate's level — so the proofs are character-identical to the pure-SN `ReducibleEnv`, modulo the carried
level.

The two operations the fundamental theorem performs:

  * **`empty`** — every substitution is reducible at every level for the empty context (vacuously: `Fin 0`
    is uninhabited).  The base case turning the theorem into the closed-term reducibility corollary.
  * **`cons`** — extend a reducible environment at a binder (the Π-introduction step): given a reducible
    environment for `context` and a reducible member (at `level`) of the new binding's closed type, the
    `cons`-extended substitution is reducible for `context.cons bindingType`.  Variable 0 hits the fresh
    head (its weakened lookup of `bindingType` cancels to `subst tailSubst bindingType`); variable `k+1`
    recurses into the tail (its weakened lookup cancels likewise).

## Zero-axiom verification

A `∀`-quantified `def`; `empty` is `Fin.elim0`; `cons` is a `Fin`-position split (`⟨0,_⟩` / `⟨k+1,_⟩`,
the propext-free structure match) whose lookups are rewritten by `TypingContext.lookup_cons_zero` /
`lookup_cons_succ` and the weakening cancellation `RawTerm.weaken_subst_cons` — the level rides along
untouched.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation

/-- The level-indexed reducible closing-substitution environment: `substitution` sends each context
variable to a reducible member (at `level`) of that variable's looked-up type, itself closed by the same
substitution.  The stratified analogue of `ReducibleEnv`, closing the conv-invariance gap at type
variables (the universe arm of `IsReducibleMemberAt` supplies the lower-level candidate). -/
def ReducibleEnvAt {profile : PolyProfile} {scope targetScope : Nat} (level : Nat)
    (context : TypingContext profile scope)
    (substitution : RawTermSubst scope targetScope) : Prop :=
  ∀ index : Fin scope,
    IsReducibleMemberAt level (RawTerm.subst substitution (context.lookup index)) (substitution index)

/-- The `var` case of the fundamental theorem: a reducible environment sends each variable to a reducible
member (at `level`) of its looked-up (closed) type. -/
theorem ReducibleEnvAt.lookupReducible {profile : PolyProfile} {scope targetScope : Nat} {level : Nat}
    {context : TypingContext profile scope} {substitution : RawTermSubst scope targetScope}
    (envReducible : ReducibleEnvAt level context substitution) (index : Fin scope) :
    IsReducibleMemberAt level
      (RawTerm.subst substitution (context.lookup index)) (substitution index) :=
  envReducible index

/-- Every substitution is reducible at every level for the empty context — the base environment (vacuous:
`Fin 0` is uninhabited), turning the fundamental theorem into the closed-term reducibility corollary. -/
theorem ReducibleEnvAt.empty {profile : PolyProfile} {targetScope : Nat} {level : Nat}
    (substitution : RawTermSubst 0 targetScope) :
    ReducibleEnvAt level (TypingContext.empty : TypingContext profile 0) substitution :=
  fun index => index.elim0

/-- Extend a reducible environment at a binder (the Π-introduction step): given a reducible environment for
`context` and a reducible member (at `level`) `headTerm` of the new binding's closed type, the
`cons`-extended substitution is reducible for `context.cons bindingType`.  Variable 0 lands on `headTerm`
(its weakened lookup of `bindingType` cancels to `subst tailSubst bindingType`); variable `k+1` recurses
into the tail environment (its weakened lookup cancels likewise). -/
theorem ReducibleEnvAt.cons {profile : PolyProfile} {scope targetScope : Nat} {level : Nat}
    {context : TypingContext profile scope} {bindingType : RawTerm scope}
    {tailSubst : RawTermSubst scope targetScope} {headTerm : RawTerm targetScope}
    (tailReducible : ReducibleEnvAt level context tailSubst)
    (headReducible : IsReducibleMemberAt level (RawTerm.subst tailSubst bindingType) headTerm) :
    ReducibleEnvAt level (context.cons bindingType) (RawTermSubst.cons headTerm tailSubst) := by
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

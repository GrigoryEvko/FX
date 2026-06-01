import FX1Poly.Typed.ReducibleEnvAt

/-! # FX1Poly/Typed/ReducibleEnvAtAllLevels
    — the ∀-level (Kripke) reducible closing-substitution environment for the dependent fundamental theorem

The dependent fundamental theorem's `var` arm hits a genuine OFF-BY-ONE at TYPE VARIABLES when stated over a
FIXED level.  A fixed-level environment `ReducibleEnvAt (predLevel + 1)` certifies each variable at exactly
`predLevel + 1`, but the binder steps that build the environment (Π-introduction, and the Π/Σ-FORMATION
premise telescope) deposit each fresh binding at the level its classifier supplies — `predLevel` for a domain
obtained by `tarskiDecode` (which drops `member@(n+1)` to `type@n`).  And the universe candidate genuinely
CHANGES with the fuel level (the `universeCode` arm of `ReducibleTypeStep` denotes
`universeReducibilityPredicate lowerReducible`, which references the relation one level down), so there is NO
level-monotonic cast to reconcile `predLevel` with `predLevel + 1`.  A per-variable environment
(`ReducibleEnvVec`) merely relocates the mismatch: `var` then needs `envLevels index = predLevel + 1`, which a
universally-quantified motive cannot force.

The resolution is the KRIPKE formulation already visible in `TelescopeReducible`: there the premise head is
reducible at ALL levels (`∀ level, IsReducibleMemberAt (level + 1) …`) and the bound argument is quantified at
`∀ memberLevel`.  Lifting that discipline to the whole environment dissolves the off-by-one:

  `ReducibleEnvAtAllLevels context substitution := ∀ level, ReducibleEnvAt (level + 1) context substitution`

— every variable is a reducible member of its looked-up type at EVERY positive level.  The `var` arm then
instantiates the family at the conclusion level (`lookupReducible` at `predLevel`), and a binder extension
threads through because the fresh binding is itself reducible at all positive levels (the telescope supplies
exactly that), so `ReducibleEnvAtAllLevels.cons` is the level-wise lift of `ReducibleEnvAt.cons`.

This file ships the ∀-level environment and its three fundamental-theorem operations
(`lookupReducible` / `empty` / `cons`), each the trivial level-wise wrapper of its `ReducibleEnvAt`
counterpart.  Positive levels only (`level + 1`): at level `0` the lower relation is empty, so a type
variable's universe candidate would be the empty predicate — the Tarski model has no genuine reducibility
candidate at the bottom (see `ReducibleTypeAt` level-`0` discussion), exactly as the telescope already
restricts to `level + 1`.

## Zero-axiom verification

Each operation is `fun level => <ReducibleEnvAt operation at (level + 1)>` — a universally-quantified lift of
the shipped, zero-axiom `ReducibleEnvAt.{lookupReducible,empty,cons}`.  No new induction, no `propext`, no
`Quot.sound`, no `Classical`, no `sorry`, no `native_decide`, no `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation

/-- The ∀-level (Kripke) reducible closing-substitution environment: `substitution` sends each context
variable to a reducible member of its looked-up (closed) type at EVERY positive level `level + 1`.  The
all-levels strengthening of `ReducibleEnvAt` that closes the dependent fundamental theorem's `var` arm at type
variables (instantiate the family at the conclusion level) without the fixed-level off-by-one. -/
def ReducibleEnvAtAllLevels {profile : PolyProfile} {scope targetScope : Nat}
    (context : TypingContext profile scope)
    (substitution : RawTermSubst scope targetScope) : Prop :=
  ∀ level : Nat, ReducibleEnvAt (level + 1) context substitution

/-- **The `var` arm of the dependent fundamental theorem (∀-level).**  The ∀-level environment sends each
variable to a reducible member of its looked-up type at every positive level; the fundamental theorem reads
it at the conclusion level `predLevel + 1`. -/
theorem ReducibleEnvAtAllLevels.lookupReducible {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {substitution : RawTermSubst scope targetScope}
    (envReducible : ReducibleEnvAtAllLevels context substitution) (predLevel : Nat) (index : Fin scope) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution (context.lookup index)) (substitution index) :=
  envReducible predLevel index

/-- Every substitution is ∀-level reducible for the empty context (vacuously: `Fin 0` is uninhabited at every
level) — the base environment that turns the dependent fundamental theorem into the closed-term reducibility
corollary. -/
theorem ReducibleEnvAtAllLevels.empty {profile : PolyProfile} {targetScope : Nat}
    (substitution : RawTermSubst 0 targetScope) :
    ReducibleEnvAtAllLevels (TypingContext.empty : TypingContext profile 0) substitution :=
  fun level => ReducibleEnvAt.empty (level := level + 1) substitution

/-- **The binder-extension of the ∀-level environment (the Π-introduction / formation-telescope step).**
Given a ∀-level reducible environment for `context` and a binding `headTerm` reducible at EVERY positive level
of the new binding's closed type, the `cons`-extended substitution is ∀-level reducible for
`context.cons bindingType`.  The level-wise lift of `ReducibleEnvAt.cons`: at each level the all-levels head
witness supplies the fixed-level head witness `ReducibleEnvAt.cons` consumes.  Because the head is required at
ALL positive levels — exactly what the premise telescope's `∀ level` head reducibility delivers — the fresh
variable lands at whatever level the `var` arm later reads it, dissolving the fixed-level off-by-one. -/
theorem ReducibleEnvAtAllLevels.cons {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {bindingType : RawTerm scope}
    {tailSubst : RawTermSubst scope targetScope} {headTerm : RawTerm targetScope}
    (tailReducible : ReducibleEnvAtAllLevels context tailSubst)
    (headReducible : ∀ level : Nat,
      IsReducibleMemberAt (level + 1) (RawTerm.subst tailSubst bindingType) headTerm) :
    ReducibleEnvAtAllLevels (context.cons bindingType) (RawTermSubst.cons headTerm tailSubst) :=
  fun level => ReducibleEnvAt.cons (tailReducible level) (headReducible level)

end FX1Poly.Typed

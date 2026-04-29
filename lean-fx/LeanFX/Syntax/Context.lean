import LeanFX.Syntax.Subst

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Contexts

`Ctx mode level scope` is a typed context at the given mode containing
`scope`-many bindings.  Each binding carries its type *at the scope
that existed when it was bound* — so `cons context bindingType` extends
a `Ctx mode level scope` with a `Ty level scope`, and the result has scope
`scope + 1`. -/

/-- Typed contexts at a fixed mode, indexed by the number of bindings.
v1.0 is single-mode: every binding lives at the context's mode.  v1.5+
will introduce `lock` to cross modes via modalities. -/
inductive Ctx : Mode → Nat → Nat → Type
  /-- The empty context at any mode and any level. -/
  | nil  : (mode : Mode) → {level : Nat} → Ctx mode level 0
  /-- Extend a context by binding a type at the same level.  Uniform-
  level discipline: every binding in a single context lives at the
  same universe level. -/
  | cons : {mode : Mode} → {level scope : Nat} →
           (context : Ctx mode level scope) →
           (bindingType : Ty level scope) →
           Ctx mode level (scope + 1)
  /-- Lock a context behind a modality. -/
  | lock : {sourceMode targetMode : Mode} → {level scope : Nat} →
           (modality : Modality sourceMode targetMode) →
           (context : Ctx targetMode level scope) →
           Ctx sourceMode level scope

namespace Ctx

/-- Axiom-free propositional laws for context locking.

These are not Lean equality: reducing identity/composed locks by
definitional equality would require dependent pattern matching on the
indexed `Modality` family, which pulls `propext` into the kernel
footprint.  The explicit relation keeps the zero-axiom commitment and
lets later modal typing rules consume lock laws deliberately.
-/
inductive LockEquiv :
    {mode : Mode} → {level scope : Nat} →
      Ctx mode level scope → Ctx mode level scope → Prop
  /-- Reflexivity for lock equivalence. -/
  | refl :
      {mode : Mode} → {level scope : Nat} →
      (context : Ctx mode level scope) →
        LockEquiv context context
  /-- Identity lock is equivalent to the original context. -/
  | identity :
      {mode : Mode} → {level scope : Nat} →
      (context : Ctx mode level scope) →
        LockEquiv (Ctx.lock (Modality.identity mode) context) context
  /-- Locking by a composed modality is equivalent to nested locking. -/
  | compose :
      {firstMode secondMode thirdMode : Mode} → {level scope : Nat} →
      (firstModality : Modality firstMode secondMode) →
      (secondModality : Modality secondMode thirdMode) →
      (context : Ctx thirdMode level scope) →
        LockEquiv
          (Ctx.lock (Modality.compose firstModality secondModality) context)
          (Ctx.lock firstModality (Ctx.lock secondModality context))

end Ctx

/-! ## Variable resolution — v1.9 Fin-indexed.

The earlier `Lookup` family carried both the position and the looked-up
type as inductive indices, which forced `Term.rename` to pattern-match
on a `Lookup (Γ.cons newType) T` scrutinee — a cons-specialised Ctx
index.  Lean 4's match compiler emits `Ctx.noConfusion` for that shape,
which transitively pulls in `propext`.

The v1.9 design replaces `Lookup` with a `Fin scope` position plus a
type-computing function `varType`.  Pattern matches on `Fin` use the
direct `⟨0, _⟩` / `⟨k+1, h⟩` structural form (axiom-free per the project
binder-form discipline), and `varType`'s definition is itself
binder-form recursive over `Ctx` so it stays propext-free.  The type
the `Term.var` constructor produces is `varType context i`, computed by
the kernel definitionally rather than carried by an indexed inductive
witness. -/

/-- The type of variable `i` in context `Γ`.  Written as a binder-form
recursive function: each cons of `Γ` weakens its bound type by one to
live in the extended scope.  Variable `0` returns the head's weakened
type; variable `k + 1` recurses into the prefix.  Marked
`@[reducible]` so Lean's unifier unfolds it eagerly when checking
`Term.var` constructions and pattern matches. -/
@[reducible]
def varType :
    {mode : Mode} → {level scope : Nat} →
    (context : Ctx mode level scope) → Fin scope → Ty level scope
  | _, _, _, .cons _ bindingType, ⟨0, _⟩      => bindingType.weaken
  | _, _, _, .cons prefixCtx _,   ⟨k + 1, h⟩  =>
      (varType prefixCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩).weaken
  | _, _, _, .lock _ context, position => varType context position

namespace SmokeTestCtxLock

/-- Empty software context locked into ghost mode. -/
example : Ctx Mode.ghost 0 0 :=
  Ctx.lock Modality.eraseGhost (Ctx.nil Mode.software)

/-- Identity locking has an explicit lock-equivalence law. -/
example (context : Ctx Mode.software 0 0) :
    Ctx.LockEquiv (Ctx.lock (Modality.identity Mode.software) context) context :=
  Ctx.LockEquiv.identity context

/-- Composed locking has an explicit lock-equivalence law. -/
example (context : Ctx Mode.wire 0 0) :
    Ctx.LockEquiv
      (Ctx.lock (Modality.compose Modality.deserialize Modality.serialize) context)
      (Ctx.lock Modality.deserialize (Ctx.lock Modality.serialize context)) :=
  Ctx.LockEquiv.compose Modality.deserialize Modality.serialize context

end SmokeTestCtxLock

end LeanFX.Syntax

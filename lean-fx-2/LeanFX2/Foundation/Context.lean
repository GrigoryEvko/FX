import LeanFX2.Foundation.Mode
import LeanFX2.Foundation.Ty

/-! # Context — Layer 0 typing environments.

`Ctx mode level scope` is the typing context: a sequence of
`Ty level scope`-like values for `scope` positions, paired with a
fixed `Mode` for the whole context.

## Definition

```lean
inductive Ctx : Mode → Nat → Nat → Type
  | empty : ∀ (mode : Mode) (level : Nat), Ctx mode level 0
  | cons {mode level scope}
      (priorContext : Ctx mode level scope)
      (newType : Ty level scope) :
      Ctx mode level (scope + 1)
```

## Mode discipline

Per CLAUDE.md commitment: a whole `Ctx` carries a single `Mode`.
Modal effects (e.g., `ghost x`) are encoded at the `Ty` level
(`Ty.modal`, Layer 6), not the context level — cleaner than
per-binding mode tags.

## varType lookup

`varType ctx position` returns the type of the variable at `position`
in `ctx`, weakened to the full scope size.  Each step through `cons`
weakens the looked-up type by one (per `Ty.weaken`).

## Why Mode at Ctx level (not Term/Ty)

See README "mode-place reasoning": Ty is mode-polymorphic, Term auto-
infers mode from Ctx.  Putting Mode here keeps mode tracking visible
at typing-rule level without parameter explosion at every Term ctor.
-/

namespace LeanFX2

/-- Typing context: a sequence of types under a fixed mode.  Each
binding stores a `Ty` at its position; `varType` looks up + weakens. -/
inductive Ctx : Mode → Nat → Nat → Type
  | empty (mode : Mode) (level : Nat) : Ctx mode level 0
  | cons {mode : Mode} {level scope : Nat}
      (priorContext : Ctx mode level scope)
      (newType : Ty level scope) :
      Ctx mode level (scope + 1)

/-- Look up the type at a position, weakening past every binding
between the position and the current scope.  Each `cons` step adds
one weakening layer.

Per `feedback_lean_match_arity_axioms.md`: `mode` and `level` are
hoisted to the function header to keep pattern arity at 1 Nat index
(scope, plus the Ctx + Fin patterns). -/
def varType {mode : Mode} {level : Nat} : ∀ {scope : Nat},
    Ctx mode level scope → Fin scope → Ty level scope
  | _, .cons _ newType, ⟨0, _⟩ => newType.weaken
  | _, .cons priorContext _, ⟨k + 1, isWithinScope⟩ =>
      (varType priorContext ⟨k, Nat.lt_of_succ_lt_succ isWithinScope⟩).weaken

end LeanFX2

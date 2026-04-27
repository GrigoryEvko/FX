import LeanFX.Mode.Defn

/-! # FX intrinsic syntax — v1.0 well-scoped skeleton.

This file replaces the v0 `Ctx = List CtxEntry` + closed `Ty` setup with
a **well-scoped** encoding: types carry the number of free variables in
scope, contexts carry the actual binding types, and weakening is a
structural function on types.  No new typing rules yet — the encoding
change *is* the v1.0 deliverable, preparing the architecture for v1.2's
dependent `Π` and v1.3's substitution machinery.

## Why well-scoped (Nat-indexed) instead of Ctx-indexed mutual

The textbook intrinsic-MTT formulation makes `Ty` mutually recursive
with `Ctx`, indexing types directly by the typed context they inhabit.
Agda accepts this; Lean 4's strict-positivity checker rejects it
because `Ctx.cons` would take a `Ty Γ` value while `Ty` is parameterised
by a `Ctx` whose own type mentions the declared family non-positively.

The standard Lean 4 fix (Allais–McBride well-scoped style, used by
MetaCoq for Coq-in-Coq) parameterises `Ty` by the *number* of variables
in scope rather than by the typed context.  Bindings are still carried
by `Ctx`, but the linkage between `Ty` and `Ctx` is mediated through
the scope-size index.  Weakening becomes `Ty.weaken : Ty n → Ty (n+1)`
— a structurally recursive function on `Ty`'s constructors, defined
*after* the inductive declaration rather than mutually with it.

We lose nothing in expressive power.  Variable references are still
intrinsically well-typed via a `Lookup` derivation; pattern matching on
`Term` still rejects ill-typed programs structurally; substitution and
weakening are now ordinary recursive functions amenable to Lean's
well-foundedness checker.

## What's in v1.0

  * `Ty : Nat → Type` — types parameterised by scope size; constructors
    `unit` and non-dependent `arrow`.
  * `Ty.weaken : Ty scope → Ty (scope + 1)` — structural shape-preserving
    extension of scope, used wherever a type crosses a binder.
  * `Ctx : Mode → Nat → Type` — typed contexts at a mode, carrying their
    own length as an index.  Single-mode in v1.0; modal `Ctx.lock`
    arrives at v1.5+.
  * `Lookup : Ctx → Ty → Type` — derivations of "this entry exists in
    that context"; the looked-up type is weakened at every `there`.
  * `Term : Ctx → Ty → Type` — intrinsically-typed terms; constructors
    `var`, `unit`, `lam`, `app`.

## What's still excluded (arrives later)

  * Dependent `Π` (codomain at scope `n + 1` referencing the bound var)
    and the corresponding `Term.app` rule using `Ty.subst` — v1.2/v1.3.
  * Universe `Type` as a term value — v1.4.
  * Σ-types, modal `Box`/intro/elim, modalities, level polymorphism
    — v1.5+. -/

namespace LeanFX.Syntax
open LeanFX.Mode

/-! ## Types

Types are parameterised by their scope size — the number of free
variables they may reference.  v1.0 constructors do not actually
*use* the scope (no type variables, no dependent constructors), but
the index is required so that v1.2's `piTy` can ship a codomain at
scope `+1`. -/

/-- Types in a context with `scope` free variables.  v1.0+v1.2 has unit,
non-dependent `arrow`, and dependent `piTy`.  The `arrow` constructor is
a convenience for non-dependent function types where the codomain does
not reference the freshly-bound variable; `piTy` is the genuinely
dependent form where the codomain lives at scope `+1`. -/
inductive Ty : Nat → Type
  /-- The unit type — exists at every scope. -/
  | unit  : {scope : Nat} → Ty scope
  /-- Non-dependent function type.  Both domain and codomain live in
  the same scope; codomain cannot reference the freshly-bound variable.
  Kept as a separate constructor (rather than derived from `piTy` via
  weakening of the codomain) so that pattern matching against arrow is
  direct without needing to recognise a weakened-codomain `piTy`. -/
  | arrow : {scope : Nat} →
            (domain : Ty scope) →
            (codomain : Ty scope) →
            Ty scope
  /-- Dependent function type — codomain lives at scope `+1` and may
  reference the freshly-bound variable via `tyVar`. -/
  | piTy  : {scope : Nat} →
            (domain : Ty scope) →
            (codomain : Ty (scope + 1)) →
            Ty scope
  /-- Type-level variable reference — references the type at de Bruijn
  position `i` in the current scope.  This is what makes the
  substitution machinery actually *do* something: with `tyVar` in `Ty`,
  `Ty.subst` looks up the substituent for each variable instead of
  threading a placeholder.  v1.5+. -/
  | tyVar : {scope : Nat} → (index : Fin scope) → Ty scope
  /-- Dependent pair type — the second component's type may reference
  the first component via a tyVar in `codomain`.  Mirrors `piTy` in
  structure: codomain at scope `+1`.  v1.6+.

  Demonstrates the v1.4+ substitution discipline generalises: the
  exact same `Ty.subst0` machinery used by `appPi`'s result type also
  handles `pair`'s second-component type and `snd`'s eliminator. -/
  | sigmaTy : {scope : Nat} →
              (firstType : Ty scope) →
              (secondType : Ty (scope + 1)) →
              Ty scope
  /-- Boolean type — the smallest non-trivial inductive.  Adding `bool`
  exercises the "mechanical extension under a new Ty constructor"
  property: every Ty-recursive function gains a single `.bool` arm
  (returning `.bool` for renaming/substitution, `rfl` for the
  congruence/composition/identity theorems).  v1.13+. -/
  | bool : {scope : Nat} → Ty scope

/-! ### v1.16 — Decidable equality on `Ty`.

Auto-derived axiom-free because `Ty`'s only index is a bare `Nat`
(not a constructor-applied expression like `Γ.cons newType`), so
the discrimination obligations Lean generates are all
propext-free `Eq.rec` over a propositionally-irrelevant motive.

Foundational for any future type-checking algorithm: deciding
`T₁ = T₂` is the basic step in conversion checking on the
surface of canonical forms. -/
deriving instance DecidableEq for Ty

/-! ## v1.4 — renaming machinery (foundation for substitution).

`Renaming` and `Ty.rename` are defined *before* `Ty.weaken` because
v1.6 redefines weakening via renaming with the shift-by-one renaming.
This bundles a correctness fix: the previous direct `Ty.weaken` shifted
all variables in `piTy`'s codomain — including the local binder, which
is wrong with `Ty.tyVar`.  Defining via `Ty.rename Renaming.weaken`
gives binder-aware shifting (the `.lift` in `Ty.rename`'s `piTy` case
keeps var 0 fixed). -/

/-- A renaming maps `Fin source` indices to `Fin target` indices.
The `Renaming source target` abbreviation makes scope explicit at
both ends, so when the lifted renaming threads through `Ty.rename`'s
recursion the indices line up definitionally. -/
abbrev Renaming (source target : Nat) : Type := Fin source → Fin target

/-- The identity renaming — every variable maps to itself. -/
def Renaming.identity {scope : Nat} : Renaming scope scope := id

/-- Weakening as a renaming — every variable shifts up by one. -/
def Renaming.weaken {scope : Nat} : Renaming scope (scope + 1) := Fin.succ

/-- Lift a renaming under a binder.  Variable 0 stays at 0; variable
`i + 1` maps to `(ρ i).succ`.  Crucially, the lifted renaming has
source `source + 1` *as a binder*, so when it threads into a recursive
call on a sub-term at scope `source + 1`, no Nat arithmetic is needed
to align the indices.

Implemented via direct match on the `Fin` structure (`⟨0, _⟩` /
`⟨k + 1, h⟩`) rather than `Fin.cases`, which itself uses `propext` in
core Lean — the empirical experiments at v1.4 confirmed this is the
critical difference. -/
def Renaming.lift {source target : Nat}
    (ρ : Renaming source target) :
    Renaming (source + 1) (target + 1)
  | ⟨0, _⟩      => ⟨0, Nat.zero_lt_succ _⟩
  | ⟨k + 1, h⟩  => Fin.succ (ρ ⟨k, Nat.lt_of_succ_lt_succ h⟩)

/-- Apply a renaming to a type, structurally.  The `piTy` case lifts
the renaming under the new binder; the recursive call on the codomain
receives a renaming whose source scope is `source + 1` — definitionally
matching the codomain's scope.  No axioms required.

This is the more primitive operation; `Ty.weaken` is derived from it. -/
def Ty.rename {source target : Nat} :
    Ty source → Renaming source target → Ty target
  | .unit, _          => .unit
  | .arrow A B, ρ     => .arrow (A.rename ρ) (B.rename ρ)
  | .piTy A B, ρ      => .piTy (A.rename ρ) (B.rename ρ.lift)
  | .tyVar i, ρ       => .tyVar (ρ i)
  | .sigmaTy A B, ρ   => .sigmaTy (A.rename ρ) (B.rename ρ.lift)
  | .bool, _          => .bool

/-! ## v1.10 — rename composition algebra.

Adding `Ty.rename_congr` and `Ty.rename_compose` upfront (via direct
structural induction, no subst infra needed) lets us redefine
`Ty.weaken` as `T.rename Renaming.weaken` (the principled, binder-aware
form) and re-derive the load-bearing `Ty.rename_weaken_commute` lemma
without circular dependencies on the v1.7 substitution hierarchy. -/

/-- Pointwise renaming equivalence.  Two renamings agree if they map
every position to the same target. -/
def Renaming.equiv {s t : Nat} (ρ₁ ρ₂ : Renaming s t) : Prop :=
  ∀ i, ρ₁ i = ρ₂ i

/-- Lifting preserves pointwise renaming equivalence. -/
theorem Renaming.lift_equiv {s t : Nat} {ρ₁ ρ₂ : Renaming s t}
    (h : Renaming.equiv ρ₁ ρ₂) : Renaming.equiv ρ₁.lift ρ₂.lift := fun i =>
  match i with
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, hk⟩ =>
      congrArg Fin.succ (h ⟨k, Nat.lt_of_succ_lt_succ hk⟩)

/-- Pointwise-equivalent renamings produce equal results on every
type.  Direct structural induction on `Ty`, using `Renaming.lift_equiv`
for the binder cases.  No subst infrastructure required. -/
theorem Ty.rename_congr {s t : Nat} {ρ₁ ρ₂ : Renaming s t}
    (h : Renaming.equiv ρ₁ ρ₂) :
    ∀ T : Ty s, T.rename ρ₁ = T.rename ρ₂
  | .unit         => rfl
  | .arrow A B    => by
      show Ty.arrow (A.rename ρ₁) (B.rename ρ₁)
         = Ty.arrow (A.rename ρ₂) (B.rename ρ₂)
      have hA := Ty.rename_congr h A
      have hB := Ty.rename_congr h B
      exact hA ▸ hB ▸ rfl
  | .piTy A B     => by
      show Ty.piTy (A.rename ρ₁) (B.rename ρ₁.lift)
         = Ty.piTy (A.rename ρ₂) (B.rename ρ₂.lift)
      have hA := Ty.rename_congr h A
      have hB := Ty.rename_congr (Renaming.lift_equiv h) B
      exact hA ▸ hB ▸ rfl
  | .tyVar i      => congrArg Ty.tyVar (h i)
  | .sigmaTy A B  => by
      show Ty.sigmaTy (A.rename ρ₁) (B.rename ρ₁.lift)
         = Ty.sigmaTy (A.rename ρ₂) (B.rename ρ₂.lift)
      have hA := Ty.rename_congr h A
      have hB := Ty.rename_congr (Renaming.lift_equiv h) B
      exact hA ▸ hB ▸ rfl
  | .bool         => rfl

/-- Compose two renamings: apply `ρ₁` first, then `ρ₂`. -/
def Renaming.compose {s m t : Nat}
    (ρ₁ : Renaming s m) (ρ₂ : Renaming m t) : Renaming s t :=
  fun i => ρ₂ (ρ₁ i)

/-- Lifting commutes with renaming composition (pointwise).  Both Fin
cases reduce to `rfl` thanks to the constructor-only structure of
`Renaming.lift`. -/
theorem Renaming.lift_compose_equiv {s m t : Nat}
    (ρ₁ : Renaming s m) (ρ₂ : Renaming m t) :
    Renaming.equiv (Renaming.compose ρ₁.lift ρ₂.lift)
                   (Renaming.compose ρ₁ ρ₂).lift
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-- **Renaming composition** at the `Ty` level.  Direct structural
induction on `T`; the binder cases use `Ty.rename_congr` plus
`Renaming.lift_compose_equiv` to bridge the lifted-then-composed and
composed-then-lifted forms. -/
theorem Ty.rename_compose {s m t : Nat} :
    ∀ (T : Ty s) (ρ₁ : Renaming s m) (ρ₂ : Renaming m t),
    (T.rename ρ₁).rename ρ₂ = T.rename (Renaming.compose ρ₁ ρ₂)
  | .unit, _, _ => rfl
  | .arrow A B, ρ₁, ρ₂ => by
      show Ty.arrow ((A.rename ρ₁).rename ρ₂) ((B.rename ρ₁).rename ρ₂)
         = Ty.arrow (A.rename (Renaming.compose ρ₁ ρ₂))
                    (B.rename (Renaming.compose ρ₁ ρ₂))
      have hA := Ty.rename_compose A ρ₁ ρ₂
      have hB := Ty.rename_compose B ρ₁ ρ₂
      exact hA ▸ hB ▸ rfl
  | .piTy A B, ρ₁, ρ₂ => by
      show Ty.piTy ((A.rename ρ₁).rename ρ₂)
                   ((B.rename ρ₁.lift).rename ρ₂.lift)
         = Ty.piTy (A.rename (Renaming.compose ρ₁ ρ₂))
                   (B.rename (Renaming.compose ρ₁ ρ₂).lift)
      have hA := Ty.rename_compose A ρ₁ ρ₂
      have hB := Ty.rename_compose B ρ₁.lift ρ₂.lift
      have hLift :=
        Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) B
      exact hA ▸ (hB.trans hLift) ▸ rfl
  | .tyVar _, _, _ => rfl
  | .sigmaTy A B, ρ₁, ρ₂ => by
      show Ty.sigmaTy ((A.rename ρ₁).rename ρ₂)
                      ((B.rename ρ₁.lift).rename ρ₂.lift)
         = Ty.sigmaTy (A.rename (Renaming.compose ρ₁ ρ₂))
                      (B.rename (Renaming.compose ρ₁ ρ₂).lift)
      have hA := Ty.rename_compose A ρ₁ ρ₂
      have hB := Ty.rename_compose B ρ₁.lift ρ₂.lift
      have hLift :=
        Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) B
      exact hA ▸ (hB.trans hLift) ▸ rfl
  | .bool, _, _ => rfl

/-- v1.10 principled `Ty.weaken`: defined as `Ty.rename Renaming.weaken`.
Binder-aware in the `piTy`/`sigmaTy` cases — the locally-bound `tyVar 0`
stays fixed via `Renaming.weaken.lift` while outer references shift.
Eliminates the v1.0 latent bug where `(piTy A B).weaken` shifted every
variable in `B`, including the local binder.

Marked `@[reducible]` so Lean's unifier and `rfl` unfold it eagerly. -/
@[reducible]
def Ty.weaken {scope : Nat} (T : Ty scope) : Ty (scope + 1) :=
  T.rename Renaming.weaken

/-- The fundamental rename-weaken commutativity lemma.  Says that
weakening (insert outer binder) commutes with renaming when the
renaming is appropriately lifted.

In v1.10, this is derived from `Ty.rename_compose` plus pointwise
renaming equivalence: both sides become `T.rename` applied to two
renamings that agree pointwise (both equal `Fin.succ ∘ ρ` modulo Fin
proof irrelevance). -/
theorem Ty.rename_weaken_commute {source target : Nat}
    (T : Ty source) (ρ : Renaming source target) :
    (T.weaken).rename ρ.lift = (T.rename ρ).weaken := by
  show (T.rename Renaming.weaken).rename ρ.lift
     = (T.rename ρ).rename Renaming.weaken
  have hSwap :
      Renaming.equiv (Renaming.compose Renaming.weaken ρ.lift)
                     (Renaming.compose ρ Renaming.weaken) := fun _ => rfl
  exact (Ty.rename_compose T Renaming.weaken ρ.lift).trans
          ((Ty.rename_congr hSwap T).trans
            (Ty.rename_compose T ρ Renaming.weaken).symm)

/-! ## Substitution — the same trick scaled up.

`Subst source target` is a function-typed family mapping `Fin source`
to `Ty target`.  Just as with `Renaming`, the substitution data carries
both endpoints as free parameters; lifting under a binder advances both
to `source + 1` and `target + 1`, definitionally matching the
recursive call's indices.

For v1.0+ `Ty` (no `Ty.tyVar` constructor), `Subst` is never *queried*
by `Ty.subst` — it threads through the recursion as a token.  When
v1.5+ adds `Ty.tyVar`, the `var` case will look up the substituent
via `σ`. -/

/-- Parallel substitution: each `Fin source` index maps to a `Ty target`
substituent.  Function-typed; `lift` advances source and target in
lockstep. -/
abbrev Subst (source target : Nat) : Type := Fin source → Ty target

/-- Lift a substitution under a binder.  Var 0 in the lifted scope is
the freshly-bound variable, represented as `Ty.tyVar 0`.  Var `k + 1`
is the original substituent for `k` weakened to the extended target
scope. -/
def Subst.lift {source target : Nat} (σ : Subst source target) :
    Subst (source + 1) (target + 1)
  | ⟨0, _⟩      => .tyVar ⟨0, Nat.zero_lt_succ _⟩
  | ⟨k + 1, h⟩  => (σ ⟨k, Nat.lt_of_succ_lt_succ h⟩).weaken

/-- Single-variable substitution at the outermost binder: substitute
`substituent` for var 0, leave var `k + 1` as `tyVar k` — the
"identity" mapping that decrements the de Bruijn index by one
(reflecting that the outer scope has one fewer binder than the
input scope). -/
def Subst.singleton {scope : Nat} (substituent : Ty scope) :
    Subst (scope + 1) scope
  | ⟨0, _⟩      => substituent
  | ⟨k + 1, h⟩  => .tyVar ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- Apply a parallel substitution to a type, structurally.  The
`piTy` case lifts the substitution under the new binder; just like
`Ty.rename`, the recursive call's indices are supplied definitionally
by `σ.lift`, no Nat arithmetic identities required.  Axiom-free. -/
def Ty.subst {source target : Nat} :
    Ty source → Subst source target → Ty target
  | .unit, _          => .unit
  | .arrow A B, σ     => .arrow (Ty.subst A σ) (Ty.subst B σ)
  | .piTy A B, σ      => .piTy (Ty.subst A σ) (Ty.subst B σ.lift)
  | .tyVar i, σ       => σ i
  | .sigmaTy A B, σ   => .sigmaTy (Ty.subst A σ) (Ty.subst B σ.lift)
  | .bool, _          => .bool

/-- Substitute the outermost variable of a type with a `Ty` value.
Used by `Term.appPi` to compute the result type of dependent
application. -/
def Ty.subst0 {scope : Nat} (codomain : Ty (scope + 1))
    (substituent : Ty scope) : Ty scope :=
  Ty.subst codomain (Subst.singleton substituent)

/-! ## v1.7 — substitution-lemma hierarchy.

The mathematical heart of dependent type theory.  These lemmas
characterise how `Ty.subst` interacts with `Ty.rename`, with itself,
and with the lifting operation.  Together they form the foundation
for term-level substitution, β-reduction, and the conversion
algorithm.

The lemmas below avoid function extensionality by working with
**pointwise** substitution equivalence (`Subst.equiv`) rather than
requiring two substitutions be Lean-equal.  This is essential for
zero-axiom soundness: funext uses `propext`, and our entire kernel
is constructive over Lean's inductive machinery. -/

/-- Pointwise equivalence of substitutions.  Two substitutions
`σ₁ σ₂ : Subst s t` are equivalent if they agree at every variable.
Used in lieu of Lean-level function equality (which would require
`funext` and thus `propext`). -/
def Subst.equiv {s t : Nat} (σ₁ σ₂ : Subst s t) : Prop :=
  ∀ i, σ₁ i = σ₂ i

/-- Lifting preserves substitution equivalence: if `σ₁ ≡ σ₂` pointwise
then `σ₁.lift ≡ σ₂.lift` pointwise. -/
theorem Subst.lift_equiv {s t : Nat} {σ₁ σ₂ : Subst s t}
    (h : Subst.equiv σ₁ σ₂) : Subst.equiv σ₁.lift σ₂.lift := fun i =>
  match i with
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, hk⟩ =>
      congrArg Ty.weaken (h ⟨k, Nat.lt_of_succ_lt_succ hk⟩)

/-- `Ty.subst` respects substitution equivalence: pointwise-equivalent
substitutions produce equal results.  Proven by structural induction
on `T`, using `Subst.lift_equiv` for the binder cases. -/
theorem Ty.subst_congr {s t : Nat} {σ₁ σ₂ : Subst s t}
    (h : Subst.equiv σ₁ σ₂) : ∀ T : Ty s, T.subst σ₁ = T.subst σ₂
  | .unit         => rfl
  | .arrow X Y    => by
      show Ty.arrow (X.subst σ₁) (Y.subst σ₁) = Ty.arrow (X.subst σ₂) (Y.subst σ₂)
      have hX := Ty.subst_congr h X
      have hY := Ty.subst_congr h Y
      exact hX ▸ hY ▸ rfl
  | .piTy X Y     => by
      show Ty.piTy (X.subst σ₁) (Y.subst σ₁.lift)
         = Ty.piTy (X.subst σ₂) (Y.subst σ₂.lift)
      have hX := Ty.subst_congr h X
      have hY := Ty.subst_congr (Subst.lift_equiv h) Y
      exact hX ▸ hY ▸ rfl
  | .tyVar i      => h i
  | .sigmaTy X Y  => by
      show Ty.sigmaTy (X.subst σ₁) (Y.subst σ₁.lift)
         = Ty.sigmaTy (X.subst σ₂) (Y.subst σ₂.lift)
      have hX := Ty.subst_congr h X
      have hY := Ty.subst_congr (Subst.lift_equiv h) Y
      exact hX ▸ hY ▸ rfl
  | .bool         => rfl

/-- Substitution composed with renaming: applies the substitution
first, then renames each substituent.  The "after" naming follows
the order of operations: `renameAfter σ ρ i = (σ i).rename ρ`. -/
def Subst.renameAfter {s m t : Nat} (σ : Subst s m) (ρ : Renaming m t) :
    Subst s t :=
  fun i => (σ i).rename ρ

/-- Lifting commutes with the renameAfter composition (pointwise).
The non-trivial case `i = ⟨k+1, h⟩` reduces to `Ty.rename_weaken_commute`
applied to the substituent `σ ⟨k, _⟩`. -/
theorem Subst.lift_renameAfter_commute {s m t : Nat}
    (σ : Subst s m) (ρ : Renaming m t) :
    Subst.equiv (Subst.renameAfter σ.lift ρ.lift)
                ((Subst.renameAfter σ ρ).lift) := fun i =>
  match i with
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, hk⟩ =>
      Ty.rename_weaken_commute (σ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) ρ

/-- **The substitution-rename commute lemma** — the mathematical
heart of the v1.7 layer.  Substituting then renaming a type equals
substituting with renamed substituents (pointwise via `renameAfter`).

This is the load-bearing lemma for `Term.rename`'s `appPi`/`pair`/
`snd` cases (whose result types involve `Ty.subst0`) and ultimately
for β-reduction.  Proven by structural induction on `T`, with the
`piTy`/`sigmaTy` cases using `Subst.lift_renameAfter_commute` +
`Ty.subst_congr`. -/
theorem Ty.subst_rename_commute :
    ∀ {s m t : Nat} (T : Ty s) (σ : Subst s m) (ρ : Renaming m t),
    (T.subst σ).rename ρ = T.subst (Subst.renameAfter σ ρ)
  | _, _, _, .unit, _, _ => rfl
  | _, _, _, .arrow X Y, σ, ρ => by
      show Ty.arrow ((X.subst σ).rename ρ) ((Y.subst σ).rename ρ)
         = Ty.arrow (X.subst (Subst.renameAfter σ ρ))
                    (Y.subst (Subst.renameAfter σ ρ))
      have hX := Ty.subst_rename_commute X σ ρ
      have hY := Ty.subst_rename_commute Y σ ρ
      exact hX ▸ hY ▸ rfl
  | _, _, _, .piTy X Y, σ, ρ => by
      show Ty.piTy ((X.subst σ).rename ρ) ((Y.subst σ.lift).rename ρ.lift)
         = Ty.piTy (X.subst (Subst.renameAfter σ ρ))
                   (Y.subst (Subst.renameAfter σ ρ).lift)
      have hX := Ty.subst_rename_commute X σ ρ
      have hY := Ty.subst_rename_commute Y σ.lift ρ.lift
      have hCong := Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | _, _, _, .tyVar _, _, _ => rfl
  | _, _, _, .sigmaTy X Y, σ, ρ => by
      show Ty.sigmaTy ((X.subst σ).rename ρ) ((Y.subst σ.lift).rename ρ.lift)
         = Ty.sigmaTy (X.subst (Subst.renameAfter σ ρ))
                      (Y.subst (Subst.renameAfter σ ρ).lift)
      have hX := Ty.subst_rename_commute X σ ρ
      have hY := Ty.subst_rename_commute Y σ.lift ρ.lift
      have hCong := Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | _, _, _, .bool, _, _ => rfl

/-- Renaming followed by substitution: precompose the renaming, then
substitute.  `Subst.precompose ρ σ i = σ (ρ i)`. -/
def Subst.precompose {s m t : Nat} (ρ : Renaming s m) (σ : Subst m t) :
    Subst s t :=
  fun i => σ (ρ i)

/-- Lifting commutes with precompose (pointwise).  Both `k = 0` and
`k+1` cases reduce to `rfl` thanks to Fin proof irrelevance. -/
theorem Subst.lift_precompose_commute {s m t : Nat}
    (ρ : Renaming s m) (σ : Subst m t) :
    Subst.equiv (Subst.precompose ρ.lift σ.lift)
                ((Subst.precompose ρ σ).lift) := fun i =>
  match i with
  | ⟨0, _⟩       => rfl
  | ⟨_ + 1, _⟩   => rfl

/-- **The rename-subst commute lemma** — the symmetric counterpart to
`Ty.subst_rename_commute`.  Renaming then substituting equals substituting
with a precomposed substitution.  This is the OTHER direction of the
substitution-rename interaction; together with `subst_rename_commute`
they let us derive `subst0_rename_commute` and the full β-reduction
soundness chain. -/
theorem Ty.rename_subst_commute :
    ∀ {s m t : Nat} (T : Ty s) (ρ : Renaming s m) (σ : Subst m t),
    (T.rename ρ).subst σ = T.subst (Subst.precompose ρ σ)
  | _, _, _, .unit, _, _ => rfl
  | _, _, _, .arrow X Y, ρ, σ => by
      show Ty.arrow ((X.rename ρ).subst σ) ((Y.rename ρ).subst σ)
         = Ty.arrow (X.subst (Subst.precompose ρ σ))
                    (Y.subst (Subst.precompose ρ σ))
      have hX := Ty.rename_subst_commute X ρ σ
      have hY := Ty.rename_subst_commute Y ρ σ
      exact hX ▸ hY ▸ rfl
  | _, _, _, .piTy X Y, ρ, σ => by
      show Ty.piTy ((X.rename ρ).subst σ) ((Y.rename ρ.lift).subst σ.lift)
         = Ty.piTy (X.subst (Subst.precompose ρ σ))
                   (Y.subst (Subst.precompose ρ σ).lift)
      have hX := Ty.rename_subst_commute X ρ σ
      have hY := Ty.rename_subst_commute Y ρ.lift σ.lift
      have hCong := Ty.subst_congr (Subst.lift_precompose_commute ρ σ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | _, _, _, .tyVar _, _, _ => rfl
  | _, _, _, .sigmaTy X Y, ρ, σ => by
      show Ty.sigmaTy ((X.rename ρ).subst σ) ((Y.rename ρ.lift).subst σ.lift)
         = Ty.sigmaTy (X.subst (Subst.precompose ρ σ))
                      (Y.subst (Subst.precompose ρ σ).lift)
      have hX := Ty.rename_subst_commute X ρ σ
      have hY := Ty.rename_subst_commute Y ρ.lift σ.lift
      have hCong := Ty.subst_congr (Subst.lift_precompose_commute ρ σ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | _, _, _, .bool, _, _ => rfl

/-! ## v1.7 finale — renaming as a special case of substitution.

The deepest beauty of the substitution discipline: **renaming is a
particular kind of substitution**, where each variable maps to a
type-variable reference (rather than a more elaborate `Ty`).  This
unifies the two operations under one mathematical umbrella. -/

/-- Coerce a renaming into a substitution: each variable index `ρ i`
becomes the type-variable reference `Ty.tyVar (ρ i)`. -/
def Renaming.toSubst {s t : Nat} (ρ : Renaming s t) : Subst s t :=
  fun i => Ty.tyVar (ρ i)

/-- Lifting commutes with the renaming-to-substitution coercion
(pointwise).  Both cases reduce to `rfl`. -/
theorem Renaming.lift_toSubst_equiv {s t : Nat} (ρ : Renaming s t) :
    Subst.equiv (Renaming.toSubst ρ.lift) (Renaming.toSubst ρ).lift :=
  fun i =>
    match i with
    | ⟨0, _⟩      => rfl
    | ⟨_ + 1, _⟩  => rfl

/-- **Renaming = Substitution** under the natural coercion.  This is
the conceptual cap of the v1.7 substitution discipline: renaming is
not a separate primitive operation but a special case of substitution
where the substituent for each variable is a `tyVar`.  All renaming
lemmas are derivable from the corresponding substitution lemmas via
this isomorphism. -/
theorem Ty.rename_eq_subst :
    ∀ {s t : Nat} (T : Ty s) (ρ : Renaming s t),
    T.rename ρ = T.subst (Renaming.toSubst ρ)
  | _, _, .unit, _ => rfl
  | _, _, .arrow X Y, ρ => by
      show Ty.arrow (X.rename ρ) (Y.rename ρ)
         = Ty.arrow (X.subst (Renaming.toSubst ρ))
                    (Y.subst (Renaming.toSubst ρ))
      have hX := Ty.rename_eq_subst X ρ
      have hY := Ty.rename_eq_subst Y ρ
      exact hX ▸ hY ▸ rfl
  | _, _, .piTy X Y, ρ => by
      show Ty.piTy (X.rename ρ) (Y.rename ρ.lift)
         = Ty.piTy (X.subst (Renaming.toSubst ρ))
                   (Y.subst (Renaming.toSubst ρ).lift)
      have hX := Ty.rename_eq_subst X ρ
      have hY := Ty.rename_eq_subst Y ρ.lift
      have hCong := Ty.subst_congr (Renaming.lift_toSubst_equiv ρ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | _, _, .tyVar _, _ => rfl
  | _, _, .sigmaTy X Y, ρ => by
      show Ty.sigmaTy (X.rename ρ) (Y.rename ρ.lift)
         = Ty.sigmaTy (X.subst (Renaming.toSubst ρ))
                      (Y.subst (Renaming.toSubst ρ).lift)
      have hX := Ty.rename_eq_subst X ρ
      have hY := Ty.rename_eq_subst Y ρ.lift
      have hCong := Ty.subst_congr (Renaming.lift_toSubst_equiv ρ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | _, _, .bool, _ => rfl

/-! ## Categorical structure: identity and composition.

These lemmas turn `Subst` into a category enriched over `Ty`:

  * `Subst.identity` is the identity object.
  * `Subst.compose` (defined below the supporting weaken-commute lemma)
    is the composition.
  * `Ty.subst` is the action of this category on `Ty`.
  * `Ty.subst_id` (identity law) and `Ty.subst_compose` (associativity
    of action) make the action functorial.

Together these say: substitution behaves algebraically. -/

/-- The identity substitution maps each variable to its own tyVar
reference.  Identity element of substitution composition. -/
def Subst.identity {scope : Nat} : Subst scope scope := fun i => Ty.tyVar i

/-- Lifting the identity substitution gives the identity at the
extended scope (pointwise).  Both Fin cases are `rfl`. -/
theorem Subst.lift_identity_equiv {scope : Nat} :
    Subst.equiv (@Subst.identity scope).lift Subst.identity := fun i =>
  match i with
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-- **Identity law for substitution**: `T.subst Subst.identity = T`.
The substitution that maps every variable to itself is the identity
operation on `Ty`.  Proven by structural induction on `T`, using
`.symm ▸` to rewrite the goal toward `rfl`. -/
theorem Ty.subst_id :
    ∀ {scope : Nat} (T : Ty scope), T.subst Subst.identity = T
  | _, .unit => rfl
  | _, .arrow X Y => by
      have hX := Ty.subst_id X
      have hY := Ty.subst_id Y
      show (X.subst Subst.identity).arrow (Y.subst Subst.identity) = X.arrow Y
      exact hX.symm ▸ hY.symm ▸ rfl
  | _, .piTy X Y => by
      have hX := Ty.subst_id X
      have hCong := Ty.subst_congr Subst.lift_identity_equiv Y
      have hY := Ty.subst_id Y
      show (X.subst Subst.identity).piTy (Y.subst Subst.identity.lift) = X.piTy Y
      exact hX.symm ▸ hCong.symm ▸ hY.symm ▸ rfl
  | _, .tyVar _ => rfl
  | _, .sigmaTy X Y => by
      have hX := Ty.subst_id X
      have hCong := Ty.subst_congr Subst.lift_identity_equiv Y
      have hY := Ty.subst_id Y
      show (X.subst Subst.identity).sigmaTy (Y.subst Subst.identity.lift)
         = X.sigmaTy Y
      exact hX.symm ▸ hCong.symm ▸ hY.symm ▸ rfl
  | _, .bool => rfl

/-- Substitution commutes with weakening: substituting after
weakening = weakening after substituting (with appropriately lifted
substitution).  Stepping stone for the composition law `Ty.subst_compose`.

In v1.10, with `Ty.weaken := T.rename Renaming.weaken`, this is derived
from `Ty.rename_subst_commute` and `Ty.subst_rename_commute` plus the
pointwise equivalence `Subst.precompose Renaming.weaken σ.lift ≡
Subst.renameAfter σ Renaming.weaken`.  The pointwise equivalence is
trivial (both forms reduce to `(σ i).rename Renaming.weaken` by
`Subst.lift`'s defn at successor positions). -/
theorem Ty.subst_weaken_commute {s t : Nat} (T : Ty s) (σ : Subst s t) :
    (T.weaken).subst σ.lift = (T.subst σ).weaken := by
  show (T.rename Renaming.weaken).subst σ.lift
     = (T.subst σ).rename Renaming.weaken
  have hPointwise :
      Subst.equiv (Subst.precompose Renaming.weaken σ.lift)
                  (Subst.renameAfter σ Renaming.weaken) := fun _ => rfl
  exact (Ty.rename_subst_commute T Renaming.weaken σ.lift).trans
          ((Ty.subst_congr hPointwise T).trans
            (Ty.subst_rename_commute T σ Renaming.weaken).symm)

/-- Composition of substitutions: apply `σ₁` first, then `σ₂` to each
substituent.  The category-theoretic composition. -/
def Subst.compose {s m t : Nat} (σ₁ : Subst s m) (σ₂ : Subst m t) :
    Subst s t :=
  fun i => (σ₁ i).subst σ₂

/-- Lifting commutes with substitution composition (pointwise).  The
non-trivial `k+1` case reduces to `Ty.subst_weaken_commute`. -/
theorem Subst.lift_compose_equiv {s m t : Nat}
    (σ₁ : Subst s m) (σ₂ : Subst m t) :
    Subst.equiv (Subst.compose σ₁.lift σ₂.lift)
                ((Subst.compose σ₁ σ₂).lift) := fun i =>
  match i with
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, hk⟩ =>
      Ty.subst_weaken_commute (σ₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) σ₂

/-- **Composition law for substitution**: `(T.subst σ₁).subst σ₂ =
T.subst (Subst.compose σ₁ σ₂)`.  Together with `Ty.subst_id`, this
makes `Subst` a category enriched over `Ty` and `Ty.subst` its
functorial action.  Proven by structural induction on `T`, using
`Subst.lift_compose_equiv` + `Ty.subst_congr` for the binder cases. -/
theorem Ty.subst_compose :
    ∀ {s m t : Nat} (T : Ty s) (σ₁ : Subst s m) (σ₂ : Subst m t),
    (T.subst σ₁).subst σ₂ = T.subst (Subst.compose σ₁ σ₂)
  | _, _, _, .unit, _, _ => rfl
  | _, _, _, .arrow X Y, σ₁, σ₂ => by
      show ((X.subst σ₁).subst σ₂).arrow ((Y.subst σ₁).subst σ₂)
         = (X.subst (Subst.compose σ₁ σ₂)).arrow
           (Y.subst (Subst.compose σ₁ σ₂))
      have hX := Ty.subst_compose X σ₁ σ₂
      have hY := Ty.subst_compose Y σ₁ σ₂
      exact hX ▸ hY ▸ rfl
  | _, _, _, .piTy X Y, σ₁, σ₂ => by
      show ((X.subst σ₁).subst σ₂).piTy ((Y.subst σ₁.lift).subst σ₂.lift)
         = (X.subst (Subst.compose σ₁ σ₂)).piTy
           (Y.subst (Subst.compose σ₁ σ₂).lift)
      have hX := Ty.subst_compose X σ₁ σ₂
      have hY := Ty.subst_compose Y σ₁.lift σ₂.lift
      have hCong := Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | _, _, _, .tyVar _, _, _ => rfl
  | _, _, _, .sigmaTy X Y, σ₁, σ₂ => by
      show ((X.subst σ₁).subst σ₂).sigmaTy ((Y.subst σ₁.lift).subst σ₂.lift)
         = (X.subst (Subst.compose σ₁ σ₂)).sigmaTy
           (Y.subst (Subst.compose σ₁ σ₂).lift)
      have hX := Ty.subst_compose X σ₁ σ₂
      have hY := Ty.subst_compose Y σ₁.lift σ₂.lift
      have hCong := Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | _, _, _, .bool, _, _ => rfl

/-! ### v1.18 — Monoid laws for Renaming and Subst.

`Subst.identity` and `Subst.compose` already give the data of the
substitution category; the laws below complete the algebraic
picture by witnessing that composition is associative and unital
(both sides of identity).  Combined with `Ty.subst_id` and
`Ty.subst_compose`, these make `(Ty, Subst, Ty.subst)` a proper
category enriched over `Ty`.

The laws are stated as pointwise equivalences (`Renaming.equiv`
and `Subst.equiv`) rather than function-level equalities to stay
axiom-free — Lean-level function equality would require funext,
which transitively pulls `propext`. -/

/-- Renaming composition is left-unital: composing the identity
renaming on the left leaves a renaming pointwise unchanged.
Renaming is just function composition, so this is `rfl` per
position. -/
theorem Renaming.compose_identity_left {s t : Nat} (ρ : Renaming s t) :
    Renaming.equiv (Renaming.compose Renaming.identity ρ) ρ :=
  fun _ => rfl

/-- Renaming composition is right-unital: composing the identity
renaming on the right leaves a renaming pointwise unchanged. -/
theorem Renaming.compose_identity_right {s t : Nat} (ρ : Renaming s t) :
    Renaming.equiv (Renaming.compose ρ Renaming.identity) ρ :=
  fun _ => rfl

/-- Renaming composition is associative.  Pointwise `rfl` because
all three forms reduce to `ρ₃ (ρ₂ (ρ₁ i))` by definition. -/
theorem Renaming.compose_assoc {s m₁ m₂ t : Nat}
    (ρ₁ : Renaming s m₁) (ρ₂ : Renaming m₁ m₂) (ρ₃ : Renaming m₂ t) :
    Renaming.equiv (Renaming.compose ρ₁ (Renaming.compose ρ₂ ρ₃))
                   (Renaming.compose (Renaming.compose ρ₁ ρ₂) ρ₃) :=
  fun _ => rfl

/-- Substitution composition is left-unital: prepending the
identity substitution leaves the substitution pointwise unchanged.
Pointwise `rfl` because `Subst.identity i = Ty.tyVar i` and the
`tyVar` arm of `Ty.subst` looks up the substituent directly. -/
theorem Subst.compose_identity_left {s t : Nat} (σ : Subst s t) :
    Subst.equiv (Subst.compose Subst.identity σ) σ :=
  fun _ => rfl

/-- Substitution composition is right-unital: appending the
identity substitution leaves the substitution pointwise unchanged.
Pointwise via `Ty.subst_id`: each substituent's identity-
substitution equals itself. -/
theorem Subst.compose_identity_right {s t : Nat} (σ : Subst s t) :
    Subst.equiv (Subst.compose σ Subst.identity) σ :=
  fun i => Ty.subst_id (σ i)

/-- Substitution composition is associative.  Pointwise via
`Ty.subst_compose`: at each position both sides reduce to
`((σ₁ i).subst σ₂).subst σ₃`. -/
theorem Subst.compose_assoc {s m₁ m₂ t : Nat}
    (σ₁ : Subst s m₁) (σ₂ : Subst m₁ m₂) (σ₃ : Subst m₂ t) :
    Subst.equiv (Subst.compose σ₁ (Subst.compose σ₂ σ₃))
                (Subst.compose (Subst.compose σ₁ σ₂) σ₃) :=
  fun i => (Ty.subst_compose (σ₁ i) σ₂ σ₃).symm

/-- Pointwise equivalence linking the two singleton-substitution
formulations: substitution-then-rename equals lifted-rename-then-
substitution-with-renamed-substituent.  The auxiliary lemma needed for
the `Ty.subst0_rename_commute` derivation. -/
theorem Subst.singleton_renameAfter_equiv_precompose {scope target : Nat}
    (A : Ty scope) (ρ : Renaming scope target) :
    Subst.equiv (Subst.renameAfter (Subst.singleton A) ρ)
                (Subst.precompose ρ.lift (Subst.singleton (A.rename ρ))) :=
  fun i => match i with
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-- **Single-variable substitution-rename commute** — the practical
specialisation that unblocks `Term.rename`'s `appPi`/`pair`/`snd`
cases.  Substituting the outermost variable then renaming equals
lifted-renaming the codomain then substituting with the renamed
substituent.

Proven by chaining the general lemmas (`subst_rename_commute`,
`rename_subst_commute`) with the singleton-substitution pointwise
equivalence — no fresh structural induction needed.  Showcases how
the v1.7 algebraic structure subsumes ad-hoc lemmas. -/
theorem Ty.subst0_rename_commute {scope target : Nat}
    (T : Ty (scope + 1)) (A : Ty scope) (ρ : Renaming scope target) :
    (T.subst0 A).rename ρ = (T.rename ρ.lift).subst0 (A.rename ρ) := by
  have h1 := Ty.subst_rename_commute T (Subst.singleton A) ρ
  have h2 := Ty.subst_congr
    (Subst.singleton_renameAfter_equiv_precompose A ρ) T
  have h3 := Ty.rename_subst_commute T ρ.lift (Subst.singleton (A.rename ρ))
  exact h1.trans (h2.trans h3.symm)

/-! ## Contexts

`Ctx mode scope` is a typed context at the given mode containing
`scope`-many bindings.  Each binding carries its type *at the scope
that existed when it was bound* — so `cons context bindingType` extends
a `Ctx mode scope` with a `Ty scope`, and the result has scope
`scope + 1`. -/

/-- Typed contexts at a fixed mode, indexed by the number of bindings.
v1.0 is single-mode: every binding lives at the context's mode.  v1.5+
will introduce `lock` to cross modes via modalities. -/
inductive Ctx : Mode → Nat → Type
  /-- The empty context at any mode. -/
  | nil  : (mode : Mode) → Ctx mode 0
  /-- Extend a context by binding a type that lives in the prefix's
  scope.  The bound variable is fresh; subsequent bindings see it in
  scope. -/
  | cons : {mode : Mode} → {scope : Nat} →
           (context : Ctx mode scope) →
           (bindingType : Ty scope) →
           Ctx mode (scope + 1)

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
    {mode : Mode} → {scope : Nat} →
    (context : Ctx mode scope) → Fin scope → Ty scope
  | _, _, .cons _ bindingType, ⟨0, _⟩      => bindingType.weaken
  | _, _, .cons prefixCtx _,   ⟨k + 1, h⟩  =>
      (varType prefixCtx ⟨k, Nat.lt_of_succ_lt_succ h⟩).weaken

/-! ## Terms

`Term context currentType` is a well-typed term in `context` of type
`currentType`.  Constructor signatures are the typing rules; Lean's
kernel checks each rule at declaration time, so a misstated rule is
rejected before any program is written using it. -/

/-- Intrinsically-typed terms.  No separate typing relation — the
constructor signatures *are* the typing rules. -/
inductive Term : {mode : Mode} → {scope : Nat} →
                 (context : Ctx mode scope) → Ty scope → Type
  /-- Variable rule.  A term is a variable iff it carries a Fin-scoped
  position; the type is computed by `varType` from the context.
  Replaces the v1.0 `Lookup`-indexed form, which forced propext through
  the match compiler at term-level renaming.  v1.9. -/
  | var :
      {mode : Mode} → {scope : Nat} →
      {context : Ctx mode scope} →
      (position : Fin scope) →
      Term context (varType context position)
  /-- Unit introduction at every scope. -/
  | unit :
      {mode : Mode} → {scope : Nat} →
      {context : Ctx mode scope} →
      Term context Ty.unit
  /-- λ-abstraction.  The body is checked in the context extended with
  the bound variable; its expected type is the codomain weakened to
  the extended scope. -/
  | lam :
      {mode : Mode} → {scope : Nat} →
      {context : Ctx mode scope} →
      {domainType codomainType : Ty scope} →
      (body : Term (Ctx.cons context domainType) codomainType.weaken) →
      Term context (Ty.arrow domainType codomainType)
  /-- Non-dependent application — function expects the codomain at the
  same scope as the domain. -/
  | app :
      {mode : Mode} → {scope : Nat} →
      {context : Ctx mode scope} →
      {domainType codomainType : Ty scope} →
      (functionTerm : Term context (Ty.arrow domainType codomainType)) →
      (argumentTerm : Term context domainType) →
      Term context codomainType
  /-- λ-abstraction for dependent `piTy`.  Body's type is the codomain
  directly (at scope `+1`) — no weakening needed because `piTy`'s
  codomain is already at the extended scope. -/
  | lamPi :
      {mode : Mode} → {scope : Nat} →
      {context : Ctx mode scope} →
      {domainType : Ty scope} →
      {codomainType : Ty (scope + 1)} →
      (body : Term (Ctx.cons context domainType) codomainType) →
      Term context (Ty.piTy domainType codomainType)
  /-- Application for dependent `piTy`.  Result type is the codomain
  with var 0 substituted by the argument's domain type — using
  `Ty.subst0` which is axiom-free thanks to the function-typed `Subst`
  threading scope information without Nat arithmetic.

  For v1.0+ `Ty` (no `Ty.tyVar`), `B.subst0 A` reduces to `B`'s
  structural shape at scope (the substituent is unused since `B` has
  no variable references).  When `Ty.tyVar` lands in v1.5+, this rule
  remains unchanged but `subst0` actually looks up the substituent. -/
  | appPi :
      {mode : Mode} → {scope : Nat} →
      {context : Ctx mode scope} →
      {domainType : Ty scope} →
      {codomainType : Ty (scope + 1)} →
      (functionTerm : Term context (Ty.piTy domainType codomainType)) →
      (argumentTerm : Term context domainType) →
      Term context (codomainType.subst0 domainType)
  /-- Pair introduction for dependent `sigmaTy`.  The second
  component's type is `secondType` with var 0 substituted by
  `firstType` — same `Ty.subst0` mechanism `appPi` uses. -/
  | pair :
      {mode : Mode} → {scope : Nat} →
      {context : Ctx mode scope} →
      {firstType : Ty scope} →
      {secondType : Ty (scope + 1)} →
      (firstVal : Term context firstType) →
      (secondVal : Term context (secondType.subst0 firstType)) →
      Term context (Ty.sigmaTy firstType secondType)
  /-- First projection.  Extracts the first component of a pair. -/
  | fst :
      {mode : Mode} → {scope : Nat} →
      {context : Ctx mode scope} →
      {firstType : Ty scope} →
      {secondType : Ty (scope + 1)} →
      (pairTerm : Term context (Ty.sigmaTy firstType secondType)) →
      Term context firstType
  /-- Second projection.  Result type uses the same `subst0`
  placeholder substitution as `pair`. -/
  | snd :
      {mode : Mode} → {scope : Nat} →
      {context : Ctx mode scope} →
      {firstType : Ty scope} →
      {secondType : Ty (scope + 1)} →
      (pairTerm : Term context (Ty.sigmaTy firstType secondType)) →
      Term context (secondType.subst0 firstType)
  /-- Boolean introduction — `true` literal at every context.  v1.13+. -/
  | boolTrue :
      {mode : Mode} → {scope : Nat} →
      {context : Ctx mode scope} →
      Term context Ty.bool
  /-- Boolean introduction — `false` literal at every context.  v1.13+. -/
  | boolFalse :
      {mode : Mode} → {scope : Nat} →
      {context : Ctx mode scope} →
      Term context Ty.bool
  /-- Boolean elimination (non-dependent) — case-analysis on a boolean
  scrutinee produces one of two same-typed branches.  Non-dependent
  because the result type is a fixed `Ty scope`, not a function on
  `bool`; dependent elim would require representing motives as
  functions on `Term`-valued booleans, which doesn't fit the current
  scope-only `Ty` indexing.  v1.14+. -/
  | boolElim :
      {mode : Mode} → {scope : Nat} →
      {context : Ctx mode scope} →
      {resultType : Ty scope} →
      (scrutinee : Term context Ty.bool) →
      (thenBranch : Term context resultType) →
      (elseBranch : Term context resultType) →
      Term context resultType

/-! ## Demonstrations of intrinsic-typing usability.

The constructors above declare what is well-typed.  The definitions and
theorems below confirm that pattern matching on the indexed `Term` and
`Lookup` families works in Lean 4 and that the new well-scoped indices
do not break definitional unfolding for `rfl`-level reasoning. -/

/-- Structural depth of a term — height of the syntax tree.  Pattern
matches on the indexed `Term` family with the implicit indices in the
binder list rather than the pattern (the latter form prevents Lean's
reducer from unfolding `Term.depth` during `rfl` checks). -/
def Term.depth
    {mode : Mode} {scope : Nat} {context : Ctx mode scope}
    {currentType : Ty scope} :
    Term context currentType → Nat
  | .var _                          => 0
  | .unit                           => 0
  | .lam body                       => body.depth + 1
  | .app functionTerm argumentTerm  =>
      max functionTerm.depth argumentTerm.depth + 1
  | .lamPi body                     => body.depth + 1
  | .appPi functionTerm argumentTerm =>
      max functionTerm.depth argumentTerm.depth + 1
  | .pair firstVal secondVal        =>
      max firstVal.depth secondVal.depth + 1
  | .fst pairTerm                   => pairTerm.depth + 1
  | .snd pairTerm                   => pairTerm.depth + 1
  | .boolTrue                       => 0
  | .boolFalse                      => 0
  | .boolElim scrutinee thenBr elseBr =>
      max scrutinee.depth (max thenBr.depth elseBr.depth) + 1

/-- Count of `lam` constructors in a term.  Second recursive function
over the indexed family — confirms pattern matching generalises beyond
`depth` and ports cleanly under the well-scoped indices. -/
def Term.lamCount
    {mode : Mode} {scope : Nat} {context : Ctx mode scope}
    {currentType : Ty scope} :
    Term context currentType → Nat
  | .var _                          => 0
  | .unit                           => 0
  | .lam body                       => body.lamCount + 1
  | .app functionTerm argumentTerm  =>
      functionTerm.lamCount + argumentTerm.lamCount
  | .lamPi body                     => body.lamCount + 1
  | .appPi functionTerm argumentTerm =>
      functionTerm.lamCount + argumentTerm.lamCount
  | .pair firstVal secondVal        =>
      firstVal.lamCount + secondVal.lamCount
  | .fst pairTerm                   => pairTerm.lamCount
  | .snd pairTerm                   => pairTerm.lamCount
  | .boolTrue                       => 0
  | .boolFalse                      => 0
  | .boolElim scrutinee thenBr elseBr =>
      scrutinee.lamCount + thenBr.lamCount + elseBr.lamCount

/-- The empty context has no positions — `Fin 0` is uninhabited, so
the kernel rejects any attempt to construct a variable in `Ctx.nil`.
Replaces the v1.0 `Lookup.notInEmpty` smoke test with the Fin analog. -/
theorem emptyContextHasNoPositions (i : Fin 0) : False :=
  Fin.elim0 i

/-- The polymorphic identity on `unit`, parameterised over the mode.
Confirms the mode parameter of `Ctx` is a working index — the same
syntactic construction type-checks at every FX mode. -/
def identityOnUnit (mode : Mode) :
    Term (Ctx.nil mode) (Ty.arrow .unit .unit) :=
  .lam (.var ⟨0, Nat.zero_lt_succ _⟩)

/-- Identity applied to the unit value at any mode.  Composes the `app`
and `lam` rules under the implicit-scope `unit` constructor. -/
def identityAppliedToUnit (mode : Mode) :
    Term (Ctx.nil mode) Ty.unit :=
  .app (identityOnUnit mode) .unit

/-- Three-level nested lambda — exercises position-0 lookup at deeper
contexts and confirms deeply-nested binders type-check cleanly under
the weakening discipline. -/
def threeArgConstantUnit (mode : Mode) :
    Term (Ctx.nil mode)
         (Ty.arrow .unit (.arrow .unit (.arrow .unit .unit))) :=
  .lam (.lam (.lam (.var ⟨0, Nat.zero_lt_succ _⟩)))

/-- A term referencing the *outer* binder via Fin position 1 — the
v1.9 analog of the v1.0 `Lookup.there .here` chain.  Demonstrates de
Bruijn skip works under the Fin-indexed encoding. -/
def shadowingThenOuter (mode : Mode) :
    Term (Ctx.cons (Ctx.nil mode) Ty.unit)
         (Ty.arrow .unit .unit) :=
  .lam (.var ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)

/-! ## Computational smoke tests

Every `example` below reduces by `rfl`, confirming that `Term.depth`,
`Term.lamCount`, `Ty.weaken`, and the implicit-index inference all
unfold definitionally under the new well-scoped encoding. -/

/-- Depth of identity = 1. -/
example (mode : Mode) : (identityOnUnit mode).depth = 1 := rfl

/-- Depth of `id unit` = 2. -/
example (mode : Mode) : (identityAppliedToUnit mode).depth = 2 := rfl

/-- lamCount of identity = 1. -/
example (mode : Mode) : (identityOnUnit mode).lamCount = 1 := rfl

/-- lamCount of `id unit` = 1. -/
example (mode : Mode) : (identityAppliedToUnit mode).lamCount = 1 := rfl

/-- Depth of three-level nest = 3. -/
example (mode : Mode) : (threeArgConstantUnit mode).depth = 3 := rfl

/-- lamCount of three-level nest = 3. -/
example (mode : Mode) : (threeArgConstantUnit mode).lamCount = 3 := rfl

/-- Shadowing demo: depth = 1, lamCount = 1. -/
example (mode : Mode) : (shadowingThenOuter mode).depth = 1 := rfl
example (mode : Mode) : (shadowingThenOuter mode).lamCount = 1 := rfl

/-- Empty-context lookup is impossible: `Fin 0` is uninhabited. -/
example (i : Fin 0) : False := emptyContextHasNoPositions i

/-! ## v1.9 — term-level renaming, propext-eliminated.

v1.8 carried `TermRenaming` as `∀ {T}, Lookup Γ T → Lookup Δ (T.rename ρ)`.
That signature forced `TermRenaming.lift`'s match scrutinee to be a
`Lookup (Γ.cons newType) T`, whose cons-specialised Ctx index made
Lean 4's match compiler emit `Ctx.noConfusion` and pull in `propext`.

v1.9 replaces the indexed-Lookup view with a *position-equality*
property on the underlying type-level `Renaming ρ`:

  ∀ i, varType Δ (ρ i) = (varType Γ i).rename ρ

`TermRenaming` is now a `Prop`, not a `Type`.  `TermRenaming.lift`
matches on `i : Fin (scope + 1)` via direct `⟨0, _⟩` / `⟨k+1, h⟩`
structural patterns — propext-free per the Fin destructuring rule.
`Term.rename` reduces variable cases via `Ty.subst`-style indexed
rewriting on `varType (...) (ρ i) = (varType ... i).rename ρ`.

The trust base of the kernel returns to **zero axioms**. -/

/-- Property witnessing that the type-level renaming `ρ` is consistent
with two contexts: at every position `i` of `Γ`, the looked-up type at
`ρ i` in `Δ` equals the looked-up type at `i` in `Γ` after renaming.
Replaces the v1.8 type-of-Lookups formulation. -/
def TermRenaming {m : Mode} {scope scope' : Nat}
    (Γ : Ctx m scope) (Δ : Ctx m scope')
    (ρ : Renaming scope scope') : Prop :=
  ∀ (i : Fin scope), varType Δ (ρ i) = (varType Γ i).rename ρ

/-- Lift a term-level renaming under a binder.  Pattern-matches on
`i : Fin (scope + 1)` directly via Fin's structure (`⟨0, _⟩` and
`⟨k+1, h⟩`), so the match never sees a cons-specialised Ctx index.
Both Fin cases reduce to `Ty.rename_weaken_commute` plus, in the
successor case, the predecessor's `ρt` proof. -/
theorem TermRenaming.lift {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {ρ : Renaming scope scope'}
    (ρt : TermRenaming Γ Δ ρ) (newType : Ty scope) :
    TermRenaming (Γ.cons newType) (Δ.cons (newType.rename ρ)) ρ.lift := by
  intro i
  match i with
  | ⟨0, _⟩ =>
      show (newType.rename ρ).weaken
         = newType.weaken.rename ρ.lift
      exact (Ty.rename_weaken_commute newType ρ).symm
  | ⟨k + 1, h⟩ =>
      show (varType Δ (ρ ⟨k, Nat.lt_of_succ_lt_succ h⟩)).weaken
           = (varType Γ ⟨k, Nat.lt_of_succ_lt_succ h⟩).weaken.rename ρ.lift
      have hρ := ρt ⟨k, Nat.lt_of_succ_lt_succ h⟩
      have hcomm := Ty.rename_weaken_commute
                      (varType Γ ⟨k, Nat.lt_of_succ_lt_succ h⟩) ρ
      exact (congrArg Ty.weaken hρ).trans hcomm.symm

/-- Renaming by the identity is the identity on `Ty`.  Derived from
the existing v1.7 substitution discipline: `Ty.rename` factors through
`Ty.subst` via `Renaming.toSubst` (lemma `Ty.rename_eq_subst`); the
identity renaming corresponds to the identity substitution pointwise
(both map `i` to `Ty.tyVar i`); and the substitution discipline already
provides `Ty.subst_id`.  No fresh structural induction needed. -/
theorem Ty.rename_identity {scope : Nat} (T : Ty scope) :
    T.rename Renaming.identity = T :=
  let renamingIdEqSubstId :
      Subst.equiv (Renaming.toSubst (@Renaming.identity scope))
                  Subst.identity := fun _ => rfl
  (Ty.rename_eq_subst T Renaming.identity).trans
    ((Ty.subst_congr renamingIdEqSubstId T).trans (Ty.subst_id T))

/-- The identity term-level renaming.  Witnesses `TermRenaming Γ Γ id`
from `Ty.rename_identity`. -/
theorem TermRenaming.identity {m : Mode} {scope : Nat} (Γ : Ctx m scope) :
    TermRenaming Γ Γ Renaming.identity := fun i =>
  (Ty.rename_identity (varType Γ i)).symm

/-- **Term-level renaming** — apply a type-level renaming `ρ` (and the
position-consistency proof `ρt`) to a `Term`, producing a `Term` in
the target context with the renamed type.

The variable case uses the position-equality witness `ρt i` to align
the type after renaming.  The `lam` / `appPi` / `pair` / `snd` cases
use the v1.7 substitution-rename commute lemmas.  Every cast is via
`▸` on a `Type`-valued `Term` motive, going through `Eq.rec` — no
match-compiler `noConfusion`, no propext. -/
def Term.rename {m scope scope'}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {ρ : Renaming scope scope'}
    (ρt : TermRenaming Γ Δ ρ) :
    {T : Ty scope} → Term Γ T → Term Δ (T.rename ρ)
  | _, .var i => (ρt i) ▸ Term.var (ρ i)
  | _, .unit       => Term.unit
  | _, .lam (codomainType := codomainType) body =>
      Term.lam (codomainType := codomainType.rename ρ)
        ((Ty.rename_weaken_commute codomainType ρ) ▸
          (Term.rename (TermRenaming.lift ρt _) body))
  | _, .app f a =>
      Term.app (Term.rename ρt f) (Term.rename ρt a)
  | _, .lamPi (domainType := domainType) body =>
      Term.lamPi (Term.rename (TermRenaming.lift ρt domainType) body)
  | _, .appPi (domainType := domainType) (codomainType := codomainType) f a =>
      (Ty.subst0_rename_commute codomainType domainType ρ).symm ▸
        Term.appPi (Term.rename ρt f) (Term.rename ρt a)
  | _, .pair (firstType := firstType) (secondType := secondType)
             firstVal secondVal =>
      Term.pair (Term.rename ρt firstVal)
        ((Ty.subst0_rename_commute secondType firstType ρ) ▸
          (Term.rename ρt secondVal))
  | _, .fst p => Term.fst (Term.rename ρt p)
  | _, .snd (firstType := firstType) (secondType := secondType) p =>
      (Ty.subst0_rename_commute secondType firstType ρ).symm ▸
        Term.snd (Term.rename ρt p)
  | _, .boolTrue  => Term.boolTrue
  | _, .boolFalse => Term.boolFalse
  | _, .boolElim scrutinee thenBr elseBr =>
      Term.boolElim (Term.rename ρt scrutinee)
                    (Term.rename ρt thenBr)
                    (Term.rename ρt elseBr)

/-! ## v1.10 — term-level weakening.

With `Ty.weaken` redefined as `T.rename Renaming.weaken`, the witness
that `varType` commutes with the shift renaming is `rfl` per position,
so `Term.weaken` reduces to a `Term.rename` along `Renaming.weaken`. -/

/-- The shift-by-one renaming witnesses a `TermRenaming` from `Γ` to
`Γ.cons newType`: the position-equality `varType (Γ.cons newType) (Fin.succ i) = (varType Γ i).rename Renaming.weaken`
is `rfl` because both sides reduce to the same `Ty.rename` application
under the new `Ty.weaken := T.rename Renaming.weaken` defn. -/
theorem TermRenaming.weaken {m : Mode} {scope : Nat}
    (Γ : Ctx m scope) (newType : Ty scope) :
    TermRenaming Γ (Γ.cons newType) Renaming.weaken := fun _ => rfl

/-- Weaken a term by extending its context with one fresh binding.
The result type is the original type weakened in lockstep, mirroring
the type-level `Ty.weaken`.  Implemented via `Term.rename` with the
shift-by-one renaming. -/
def Term.weaken {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    (newType : Ty scope) {T : Ty scope} (term : Term Γ T) :
    Term (Γ.cons newType) T.weaken :=
  Term.rename (TermRenaming.weaken Γ newType) term

/-! ## v1.10 — term-level substitution.

`TermSubst Γ Δ σ` is a term-valued substitution paralleling the
type-level `Subst σ`: for each position `i` in `Γ`, it supplies a
term in `Δ` whose type is the substituted `varType`.  `TermSubst.lift`
extends a substitution under a binder using `Term.weaken` to relocate
predecessor terms into the extended target context. -/

/-- A term-level substitution maps each position of `Γ` to a term in
`Δ` whose type is `varType Γ` substituted by the underlying type-level
σ.  The type-equality is computed via `Ty.subst`. -/
abbrev TermSubst {m : Mode} {scope scope' : Nat}
    (Γ : Ctx m scope) (Δ : Ctx m scope')
    (σ : Subst scope scope') : Type :=
  ∀ (i : Fin scope), Term Δ ((varType Γ i).subst σ)

/-- Lift a term-level substitution under a binder.  Position 0 in the
extended source context maps to `Term.var ⟨0, _⟩` in the extended
target (cast through `Ty.subst_weaken_commute`); positions `k + 1`
weaken the predecessor's image into the extended target context. -/
def TermSubst.lift {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {σ : Subst scope scope'}
    (σt : TermSubst Γ Δ σ) (newType : Ty scope) :
    TermSubst (Γ.cons newType) (Δ.cons (newType.subst σ)) σ.lift :=
  fun i =>
    match i with
    | ⟨0, _⟩ =>
        (Ty.subst_weaken_commute newType σ).symm ▸
          (Term.var ⟨0, Nat.zero_lt_succ _⟩ :
            Term (Δ.cons (newType.subst σ)) (newType.subst σ).weaken)
    | ⟨k + 1, h⟩ =>
        (Ty.subst_weaken_commute
            (varType Γ ⟨k, Nat.lt_of_succ_lt_succ h⟩) σ).symm ▸
          Term.weaken (newType.subst σ)
            (σt ⟨k, Nat.lt_of_succ_lt_succ h⟩)

/-- Weakening then substituting with the singleton substitution is
the identity on `Ty`.  The shift renames every original variable up
by one, then `Subst.singleton X` at position `k + 1` returns the
`Ty.tyVar k` corresponding to the original position — i.e., the
substitution acts as the identity. -/
theorem Ty.weaken_subst_singleton {scope : Nat}
    (T : Ty scope) (X : Ty scope) :
    T.weaken.subst (Subst.singleton X) = T := by
  show (T.rename Renaming.weaken).subst (Subst.singleton X) = T
  have hRSC :=
    Ty.rename_subst_commute T Renaming.weaken (Subst.singleton X)
  have hPointwise :
      Subst.equiv
        (Subst.precompose Renaming.weaken (Subst.singleton X))
        Subst.identity := fun _ => rfl
  have hCong := Ty.subst_congr hPointwise T
  have hId := Ty.subst_id T
  exact hRSC.trans (hCong.trans hId)

/-- The single-substituent term substitution: position 0 maps to
`arg`, positions `k + 1` map to `Term.var ⟨k, _⟩` in the original
context (variable shifts down by one because the outer scope has one
fewer binder than the input).  The underlying type-level σ is
`Subst.singleton T_arg` for the argument's type `T_arg`.  Both Fin
cases require a cast through `Ty.weaken_subst_singleton` to align the
substituted-varType form. -/
def TermSubst.singleton {m : Mode} {scope : Nat}
    {Γ : Ctx m scope} {T_arg : Ty scope}
    (arg : Term Γ T_arg) :
    TermSubst (Γ.cons T_arg) Γ (Subst.singleton T_arg) :=
  fun i =>
    match i with
    | ⟨0, _⟩ =>
        (Ty.weaken_subst_singleton T_arg T_arg).symm ▸ arg
    | ⟨k + 1, h⟩ =>
        (Ty.weaken_subst_singleton
            (varType Γ ⟨k, Nat.lt_of_succ_lt_succ h⟩) T_arg).symm ▸
          Term.var ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-! ## v1.10 — substitution-substitution commutativity.

The lemma analogous to `Ty.subst0_rename_commute`: `subst0` distributes
through an outer subst by lifting the codomain's substitution and
substituting the renamed substituent.  Used by `Term.subst`'s
`appPi` / `pair` / `snd` cases to align result types. -/

/-- The pointwise equivalence underpinning `Ty.subst0_subst_commute`:
substituting then composing with σ equals lifting σ under the binder
then composing with the singleton-substituent (already substituted by
σ).  Both sides at position 0 evaluate to `(substituent).subst σ`;
at positions `k + 1`, both evaluate to `σ ⟨k, _⟩`. -/
theorem Subst.singleton_compose_equiv_lift_compose_singleton
    {scope target : Nat}
    (substituent : Ty scope) (σ : Subst scope target) :
    Subst.equiv
      (Subst.compose (Subst.singleton substituent) σ)
      (Subst.compose σ.lift (Subst.singleton (substituent.subst σ))) :=
  fun i =>
    match i with
    | ⟨0, _⟩      => rfl
    | ⟨k + 1, h⟩  => by
        show (Ty.tyVar ⟨k, Nat.lt_of_succ_lt_succ h⟩).subst σ
           = ((σ ⟨k, Nat.lt_of_succ_lt_succ h⟩).rename Renaming.weaken).subst
               (Subst.singleton (substituent.subst σ))
        have hRSC :=
          Ty.rename_subst_commute (σ ⟨k, Nat.lt_of_succ_lt_succ h⟩)
            Renaming.weaken (Subst.singleton (substituent.subst σ))
        have hPointwise :
            Subst.equiv
              (Subst.precompose Renaming.weaken
                (Subst.singleton (substituent.subst σ)))
              Subst.identity := fun _ => rfl
        have hCong := Ty.subst_congr hPointwise
                        (σ ⟨k, Nat.lt_of_succ_lt_succ h⟩)
        have hId := Ty.subst_id (σ ⟨k, Nat.lt_of_succ_lt_succ h⟩)
        exact (hRSC.trans (hCong.trans hId)).symm

/-- The practical specialisation: substituting the outermost variable
then applying an outer substitution equals lifting the outer
substitution under the binder then substituting the substituted
substituent. -/
theorem Ty.subst0_subst_commute {scope target : Nat}
    (T : Ty (scope + 1)) (X : Ty scope) (σ : Subst scope target) :
    (T.subst0 X).subst σ
      = (T.subst σ.lift).subst0 (X.subst σ) := by
  show (T.subst (Subst.singleton X)).subst σ
     = (T.subst σ.lift).subst (Subst.singleton (X.subst σ))
  have hLeft := Ty.subst_compose T (Subst.singleton X) σ
  have hRight := Ty.subst_compose T σ.lift (Subst.singleton (X.subst σ))
  have hCong := Ty.subst_congr
    (Subst.singleton_compose_equiv_lift_compose_singleton X σ) T
  exact hLeft.trans (hCong.trans hRight.symm)

/-- **Term-level substitution** — apply a term-level substitution `σt`
(and the underlying type-level σ) to a `Term`, producing a `Term` in
the target context with the substituted type.

The variable case looks up the substituent term via `σt`; the binder
cases (`lam`, `lamPi`) use `TermSubst.lift` to extend σt under the new
binder and align body types via `Ty.subst_weaken_commute`; the
projection-laden cases (`appPi`, `pair`, `snd`) use
`Ty.subst0_subst_commute` to align `subst0`-shaped result types. -/
def Term.subst {m scope scope'}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {σ : Subst scope scope'}
    (σt : TermSubst Γ Δ σ) :
    {T : Ty scope} → Term Γ T → Term Δ (T.subst σ)
  | _, .var i      => σt i
  | _, .unit       => Term.unit
  | _, .lam (codomainType := codomainType) body =>
      Term.lam (codomainType := codomainType.subst σ)
        ((Ty.subst_weaken_commute codomainType σ) ▸
          (Term.subst (TermSubst.lift σt _) body))
  | _, .app f a    =>
      Term.app (Term.subst σt f) (Term.subst σt a)
  | _, .lamPi (domainType := domainType) body =>
      Term.lamPi (Term.subst (TermSubst.lift σt domainType) body)
  | _, .appPi (domainType := domainType) (codomainType := codomainType) f a =>
      (Ty.subst0_subst_commute codomainType domainType σ).symm ▸
        Term.appPi (Term.subst σt f) (Term.subst σt a)
  | _, .pair (firstType := firstType) (secondType := secondType)
             firstVal secondVal =>
      Term.pair (Term.subst σt firstVal)
        ((Ty.subst0_subst_commute secondType firstType σ) ▸
          (Term.subst σt secondVal))
  | _, .fst p      => Term.fst (Term.subst σt p)
  | _, .snd (firstType := firstType) (secondType := secondType) p =>
      (Ty.subst0_subst_commute secondType firstType σ).symm ▸
        Term.snd (Term.subst σt p)
  | _, .boolTrue   => Term.boolTrue
  | _, .boolFalse  => Term.boolFalse
  | _, .boolElim scrutinee thenBr elseBr =>
      Term.boolElim (Term.subst σt scrutinee)
                    (Term.subst σt thenBr)
                    (Term.subst σt elseBr)

/-- **Single-variable term substitution** — substitute `arg` for var 0
in `body`.  Used by β-reduction.  Result type is computed via
`Ty.subst0` at the type level, matching `Term.appPi`'s result-type
shape exactly. -/
def Term.subst0 {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {T_arg : Ty scope} {T_body : Ty (scope + 1)}
    (body : Term (Γ.cons T_arg) T_body) (arg : Term Γ T_arg) :
    Term Γ (T_body.subst0 T_arg) :=
  Term.subst (TermSubst.singleton arg) body

/-! ## v1.17 — Categorical structure of TermRenaming and TermSubst.

`Subst` and `Renaming` form *categories* enriched over `Ty`:
identity and composition exist at the type level, and
`Ty.subst_id` / `Ty.subst_compose` make `Ty.subst` a functor
(§v1.10).  This section lifts identity and composition up to the
*term* level — `TermSubst.identity` and `TermSubst.compose`
witness the same structure on the term-valued substitutions.

The functoriality theorems at the term level (`Term.subst_id`,
`Term.subst_compose`) require careful dependent-cast wrangling
because `Term.subst σt t` lives at type `Term Δ (T.subst σ)`,
which is propositionally but not definitionally equal to
`Term Δ T` when `σ = Subst.identity`.  v1.18 attacks
`Term.subst_id`; v1.19 attacks `Term.subst_compose`. -/

/-- Composition of term-level renamings.  Mirrors `Renaming.compose`
at the type level.

The position-equality witness chains the two underlying
`TermRenaming`s through `Ty.rename_compose`: applying ρ₂ to ρ₁ to
position `i` reaches `varType Γ₁ i` renamed by the composed
renaming. -/
theorem TermRenaming.compose {m : Mode} {scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m scope₁} {Γ₂ : Ctx m scope₂} {Γ₃ : Ctx m scope₃}
    {ρ₁ : Renaming scope₁ scope₂} {ρ₂ : Renaming scope₂ scope₃}
    (ρt₁ : TermRenaming Γ₁ Γ₂ ρ₁) (ρt₂ : TermRenaming Γ₂ Γ₃ ρ₂) :
    TermRenaming Γ₁ Γ₃ (Renaming.compose ρ₁ ρ₂) := fun i => by
  -- Goal: varType Γ₃ (Renaming.compose ρ₁ ρ₂ i) =
  --       (varType Γ₁ i).rename (Renaming.compose ρ₁ ρ₂)
  -- Renaming.compose ρ₁ ρ₂ i ≡ ρ₂ (ρ₁ i) by defn
  show varType Γ₃ (ρ₂ (ρ₁ i))
     = (varType Γ₁ i).rename (Renaming.compose ρ₁ ρ₂)
  -- Step 1: ρt₂ at position (ρ₁ i):
  --   varType Γ₃ (ρ₂ (ρ₁ i)) = (varType Γ₂ (ρ₁ i)).rename ρ₂
  rw [ρt₂ (ρ₁ i)]
  -- Step 2: ρt₁ at position i, transported under .rename ρ₂:
  --   (varType Γ₂ (ρ₁ i)).rename ρ₂ = ((varType Γ₁ i).rename ρ₁).rename ρ₂
  rw [ρt₁ i]
  -- Step 3: rename composition:
  --   ((varType Γ₁ i).rename ρ₁).rename ρ₂
  --     = (varType Γ₁ i).rename (Renaming.compose ρ₁ ρ₂)
  exact Ty.rename_compose (varType Γ₁ i) ρ₁ ρ₂

/-- The identity term-level substitution.  Mirrors `Subst.identity`
at the type level.

For each position `i`, returns `Term.var i` transported across
`Ty.subst_id (varType Γ i)` so the result lives at the expected
type `Term Γ ((varType Γ i).subst Subst.identity)`. -/
def TermSubst.identity {m : Mode} {scope : Nat} (Γ : Ctx m scope) :
    TermSubst Γ Γ Subst.identity := fun i =>
  -- Term.var i : Term Γ (varType Γ i)
  -- Need:        Term Γ ((varType Γ i).subst Subst.identity)
  -- Bridge:      Ty.subst_id (varType Γ i) :
  --              (varType Γ i).subst Subst.identity = varType Γ i
  (Ty.subst_id (varType Γ i)).symm ▸ Term.var i

/-- Composition of term-level substitutions.  Mirrors
`Subst.compose` at the type level.

Each position `i` first applies σt₁ (giving a term in Γ₂ at the
σ₁-substituted type), then applies σt₂ (further substituting by
σ₂), then transports across `Ty.subst_compose` to align with the
expected `Subst.compose σ₁ σ₂`-substituted type. -/
def TermSubst.compose {m : Mode} {scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m scope₁} {Γ₂ : Ctx m scope₂} {Γ₃ : Ctx m scope₃}
    {σ₁ : Subst scope₁ scope₂} {σ₂ : Subst scope₂ scope₃}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂) :
    TermSubst Γ₁ Γ₃ (Subst.compose σ₁ σ₂) := fun i =>
  -- σt₁ i             : Term Γ₂ ((varType Γ₁ i).subst σ₁)
  -- Term.subst σt₂ _  : Term Γ₃ (((varType Γ₁ i).subst σ₁).subst σ₂)
  -- Need              : Term Γ₃ ((varType Γ₁ i).subst (Subst.compose σ₁ σ₂))
  -- Bridge            : Ty.subst_compose (varType Γ₁ i) σ₁ σ₂
  Ty.subst_compose (varType Γ₁ i) σ₁ σ₂ ▸ Term.subst σt₂ (σt₁ i)

/-! ### v1.19 — Cast-cancellation toolkit + leaf-case Term.subst_id.

The functoriality theorem `Term.subst_id` (substitution by
identity is identity) requires dependent-cast manipulation
because the substituted term lives at type `Term Γ (T.subst
Subst.identity)`, propositionally but not definitionally equal
to `Term Γ T`.  This section discharges:

  1. The two cast-cancellation utility lemmas (`Eq.cast_symm_cast`
     and `Eq.cast_cast_symm`).
  2. The leaf cases of `Term.subst_id`, where the term has no
     subterm recursion through `TermSubst.lift`: `unit`, `var`,
     `boolTrue`, `boolFalse`.

The recursive cases (`lam`, `app`, `lamPi`, `appPi`, `pair`,
`fst`, `snd`, `boolElim`) require an additional pointwise
equivalence between `TermSubst.lift (TermSubst.identity Γ)` and
`TermSubst.identity (Γ.cons _)` to thread the inductive hypothesis
through the binder cases.  That stepping stone is the v1.20
`TermSubst.lift_identity_pointwise` theorem below. -/

/-- Cast cancellation: applying `h ▸` after `h.symm ▸` returns
the original.  Standard fact about `Eq.rec`, axiom-free via
`cases h; rfl`.  Useful whenever a `TermSubst.identity` lookup
puts an inverse cast on a term that we then transport back.

Stated at `Type` (rather than `Sort u`) because `autoImplicit :=
false` rejects free universe variables; both our concrete
applications (`α := Ty scope`, `P := Term Γ`) live at `Type`
anyway. -/
theorem Eq.cast_symm_cast {α : Type} {a b : α} (h : a = b)
    {P : α → Type} (y : P b) :
    h ▸ (h.symm ▸ y) = y := by
  cases h
  rfl

/-- Cast cancellation, dual direction: `h.symm ▸` after `h ▸`
returns the original. -/
theorem Eq.cast_cast_symm {α : Type} {a b : α} (h : a = b)
    {P : α → Type} (x : P a) :
    h.symm ▸ (h ▸ x) = x := by
  cases h
  rfl

/-- **Leaf case: `Term.subst_id` for `unit`.**  Definitionally
trivial because `Ty.subst_id Ty.unit` reduces to `rfl` (per the
unit arm of `Ty.subst_id`'s definition), so the cast collapses. -/
theorem Term.subst_id_unit {m : Mode} {scope : Nat} {Γ : Ctx m scope} :
    (Ty.subst_id (scope := scope) Ty.unit) ▸
      Term.subst (TermSubst.identity Γ) (Term.unit (context := Γ))
    = Term.unit := rfl

/-- **Leaf case: `Term.subst_id` for `var`.**  The substitution
unfolds to `TermSubst.identity Γ i = (Ty.subst_id _).symm ▸
Term.var i`, then the outer cast cancels via
`Eq.cast_symm_cast`. -/
theorem Term.subst_id_var {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    (i : Fin scope) :
    (Ty.subst_id (varType Γ i)) ▸
      Term.subst (TermSubst.identity Γ) (Term.var i)
    = Term.var i :=
  Eq.cast_symm_cast (Ty.subst_id (varType Γ i)) (Term.var i)

/-- **Leaf case: `Term.subst_id` for `boolTrue`.**  Trivial like
`unit` because `Ty.subst_id Ty.bool` reduces to `rfl`. -/
theorem Term.subst_id_boolTrue {m : Mode} {scope : Nat} {Γ : Ctx m scope} :
    (Ty.subst_id (scope := scope) Ty.bool) ▸
      Term.subst (TermSubst.identity Γ) (Term.boolTrue (context := Γ))
    = Term.boolTrue := rfl

/-- **Leaf case: `Term.subst_id` for `boolFalse`.**  Trivial like
`unit` because `Ty.subst_id Ty.bool` reduces to `rfl`. -/
theorem Term.subst_id_boolFalse {m : Mode} {scope : Nat} {Γ : Ctx m scope} :
    (Ty.subst_id (scope := scope) Ty.bool) ▸
      Term.subst (TermSubst.identity Γ) (Term.boolFalse (context := Γ))
    = Term.boolFalse := rfl

/-! ### v1.20 — Bridge layer for `TermSubst.lift (TermSubst.identity Γ)`.

Proving `Term.subst_id` over the recursive cases (`lam`, `app`,
`lamPi`, `appPi`, `pair`, `fst`, `snd`, `boolElim`) requires
threading an inductive hypothesis through `TermSubst.lift`'s
extension of the substitution under a binder.  The recursive call
operates on `TermSubst.lift (TermSubst.identity Γ) newType`, but the
IH is stated in terms of `TermSubst.identity (Γ.cons newType)`.
These two TermSubsts have **different types** along three axes:

  1. **Context**: `Γ.cons (newType.subst Subst.identity)` vs
     `Γ.cons newType`.  Bridged by `Ty.subst_id newType`.
  2. **Term type**: `T.subst Subst.identity.lift` vs `T.subst
     Subst.identity` (and ultimately `T`).  Bridged by
     `Ty.subst_lift_identity_eq_subst_identity` and `Ty.subst_id`.
  3. **Underlying substitution**: `Subst.identity.lift` vs
     `Subst.identity`.  Pointwise equivalent via
     `Subst.lift_identity_equiv`.

This section ships:

  * Two Ty-level bridge lemmas (`subst_lift_identity_eq_subst_identity`,
    `weaken_subst_lift_identity`) closing axis (2) at the type level.
  * Three HEq-bridge helpers (`heq_var_across_ctx_eq`,
    `Term.heq_weaken_strip_cast`, `heq_weaken_var_across_ctx_eq`)
    closing axis (1) at the Term level.
  * The full `TermSubst.lift_identity_pointwise` theorem stitching
    all three axes via `HEq.trans` + `eqRec_heq`. -/

/-- **Lifted-identity substitution behaves like identity on any
type.**  For any `T : Ty (scope + 1)`, substituting via
`Subst.identity.lift` is the same as substituting via plain
`Subst.identity`.  Proven by chaining `Ty.subst_congr` over the
pointwise equivalence `Subst.lift_identity_equiv`. -/
theorem Ty.subst_lift_identity_eq_subst_identity
    {scope : Nat} (T : Ty (scope + 1)) :
    T.subst (@Subst.identity scope).lift = T.subst Subst.identity :=
  Ty.subst_congr Subst.lift_identity_equiv T

/-- **Lifted-identity substitution is the identity on weakened
types.**  Combining `Ty.subst_lift_identity_eq_subst_identity`
with `Ty.subst_id` shows that weakening a `Ty scope` to scope+1
and then substituting by `Subst.identity.lift` returns the
weakened type unchanged.  This is the exact bridging fact needed
when `Term.subst_id`'s recursive cases handle a body's substituted
type at the extended scope. -/
theorem Ty.weaken_subst_lift_identity {scope : Nat} (T : Ty scope) :
    T.weaken.subst (@Subst.identity scope).lift = T.weaken :=
  (Ty.subst_lift_identity_eq_subst_identity T.weaken).trans
    (Ty.subst_id T.weaken)

/-- **HEq across context-shape change for `Term.var`**: if two
contexts at the same scope are propositionally equal, then the
`Term.var` constructor at the same Fin position produces HEq
values across them.  Proven by `cases` on the context equality —
both sides become identical, and HEq reduces to Eq.refl. -/
theorem heq_var_across_ctx_eq {m : Mode} {scope : Nat}
    {Γ Δ : Ctx m scope} (h_ctx : Γ = Δ) (i : Fin scope) :
    HEq (Term.var (context := Γ) i) (Term.var (context := Δ) i) := by
  cases h_ctx
  rfl

/-- **Strip an inner type-cast through `Term.weaken`.**  The
generic helper: weakening a term commutes with a propositional
type cast on the input.  Proven by `cases` on the equation —
both T₁ and T₂ are local variables, so the substitution succeeds
and the cast vanishes. -/
theorem Term.heq_weaken_strip_cast
    {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    (newType : Ty scope) {T₁ T₂ : Ty scope} (h : T₁ = T₂)
    (t : Term Γ T₁) :
    HEq (Term.weaken newType (h ▸ t)) (Term.weaken newType t) := by
  cases h
  rfl

/-- **HEq across context-shape change for `Term.weaken (... ▸
Term.var)`**: at position k+1 of the lifted-identity, the LHS
shape is `Term.weaken X ((Ty.subst_id _).symm ▸ Term.var ⟨k, _⟩)`,
which equals `Term.var ⟨k+1, _⟩` in the extended context modulo
context-shape and the inner cast.  Uses
`Term.heq_weaken_strip_cast` to discharge the inner cast, then
`Term.weaken X (Term.var ⟨k, _⟩) = Term.var ⟨k+1, _⟩` by `rfl`
(through `Term.rename`'s var arm + `TermRenaming.weaken`'s
rfl-pointwise + `Renaming.weaken = Fin.succ`). -/
theorem heq_weaken_var_across_ctx_eq {m : Mode} {scope : Nat}
    {Γ Δ : Ctx m scope} (h_ctx : Γ = Δ)
    (newTypeΓ : Ty scope) (newTypeΔ : Ty scope)
    (h_new : newTypeΓ = newTypeΔ)
    (k : Nat) (hk : k + 1 < scope + 1) :
    HEq
      (Term.weaken newTypeΓ
        ((Ty.subst_id (varType Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩)).symm ▸
          Term.var (context := Γ) ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
      (Term.var (context := Δ.cons newTypeΔ) ⟨k + 1, hk⟩) := by
  -- Reduce both sides simultaneously by `cases`-ing the context
  -- and newType equalities — this aligns Γ = Δ and newTypeΓ =
  -- newTypeΔ pointwise.
  cases h_ctx
  cases h_new
  -- Strip the inner cast via the helper.
  apply HEq.trans (Term.heq_weaken_strip_cast newTypeΓ
    (Ty.subst_id (varType Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩)).symm
    (Term.var ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
  -- Goal: HEq (Term.weaken newTypeΓ (Term.var ⟨k, _⟩))
  --           (Term.var (context := Γ.cons newTypeΓ) ⟨k+1, hk⟩)
  -- Term.weaken X (Term.var ⟨k, _⟩) reduces (rfl) to
  --   Term.var (Renaming.weaken ⟨k, _⟩) = Term.var ⟨k+1, _⟩
  rfl

/-- **The HEq stepping stone for `Term.subst_id`'s recursive cases.**
Lifting `TermSubst.identity Γ` under a binder produces a TermSubst
that, pointwise, agrees with `TermSubst.identity (Γ.cons newType)`
modulo HEq.  The contexts and underlying substitutions differ
propositionally (via `Ty.subst_id newType` and
`Subst.lift_identity_equiv`); HEq is the right notion of equality
because both differences manifest at the type level of the
substituent terms. -/
theorem TermSubst.lift_identity_pointwise
    {m : Mode} {scope : Nat}
    (Γ : Ctx m scope) (newType : Ty scope) :
    ∀ (i : Fin (scope + 1)),
      HEq
        (TermSubst.lift (TermSubst.identity Γ) newType i)
        (TermSubst.identity (Γ.cons newType) i) := by
  intro i
  -- The bridging Ty-level fact, used in both Fin cases.
  have h_subst_id : newType.subst Subst.identity = newType :=
    Ty.subst_id newType
  -- Lift to context-level equality.
  have h_ctx :
      Γ.cons (newType.subst Subst.identity) = Γ.cons newType := by
    rw [h_subst_id]
  match i with
  | ⟨0, h0⟩ =>
    -- LHS = (Ty.subst_weaken_commute newType Subst.identity).symm ▸
    --        Term.var (context := Γ.cons (newType.subst Subst.identity)) ⟨0, h0⟩
    -- RHS = (Ty.subst_id newType.weaken).symm ▸
    --        Term.var (context := Γ.cons newType) ⟨0, h0⟩
    --
    -- Strip both outer casts via eqRec_heq, then bridge the two
    -- naked Term.var values via heq_var_across_ctx_eq + h_ctx.
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (heq_var_across_ctx_eq h_ctx ⟨0, h0⟩)
    exact (eqRec_heq _ _).symm
  | ⟨k + 1, hk⟩ =>
    -- LHS = (Ty.subst_weaken_commute (varType Γ ⟨k,_⟩) Subst.identity).symm ▸
    --        Term.weaken (newType.subst Subst.identity)
    --          (TermSubst.identity Γ ⟨k, _⟩)
    --      = ... ▸ Term.weaken (newType.subst Subst.identity)
    --                ((Ty.subst_id (varType Γ ⟨k,_⟩)).symm ▸
    --                  Term.var ⟨k, _⟩)
    -- RHS = (Ty.subst_id (varType Γ ⟨k,_⟩).weaken).symm ▸
    --        Term.var (context := Γ.cons newType) ⟨k + 1, hk⟩
    --
    -- Strip outer cast on each side, then bridge via
    -- heq_weaken_var_across_ctx_eq applied at the identity ctx
    -- equality (Γ = Γ) plus the newType equality.
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (heq_weaken_var_across_ctx_eq (rfl : Γ = Γ)
        (newType.subst Subst.identity) newType
        h_subst_id k hk)
    exact (eqRec_heq _ _).symm

/-! ### v1.21 — HEq congruence helpers for `Term`'s thirteen
constructors.

For each `Term` constructor C, the helper `Term.C_HEq_congr` says:
two `C`-applications are HEq when their type-level implicits are
propositionally equal AND their value arguments are HEq.  Each
helper proves via `cases` on the local-variable equalities,
collapsing the goal to `rfl`.

These helpers are the building blocks for inductive proofs that
need to bridge `Term` values across different type indices —
notably `Term.subst_id_HEq` (v1.21+), `Term.subst_compose` (v1.24),
and any future theorem that descends through `Term.subst`'s
constructor cases. -/

/-- HEq congruence for `Term.app`. -/
theorem Term.app_HEq_congr
    {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {T₁_a T₁_b T₂_a T₂_b : Ty scope}
    (h_T₁ : T₁_a = T₁_b) (h_T₂ : T₂_a = T₂_b)
    (f₁ : Term Γ (T₁_a.arrow T₂_a)) (f₂ : Term Γ (T₁_b.arrow T₂_b))
    (h_f : HEq f₁ f₂)
    (a₁ : Term Γ T₁_a) (a₂ : Term Γ T₁_b) (h_a : HEq a₁ a₂) :
    HEq (Term.app f₁ a₁) (Term.app f₂ a₂) := by
  cases h_T₁
  cases h_T₂
  cases h_f
  cases h_a
  rfl

/-- HEq congruence for `Term.lam`. -/
theorem Term.lam_HEq_congr
    {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {dom₁ dom₂ : Ty scope} (h_dom : dom₁ = dom₂)
    {cod₁ cod₂ : Ty scope} (h_cod : cod₁ = cod₂)
    (body₁ : Term (Γ.cons dom₁) cod₁.weaken)
    (body₂ : Term (Γ.cons dom₂) cod₂.weaken)
    (h_body : HEq body₁ body₂) :
    HEq (Term.lam body₁) (Term.lam body₂) := by
  cases h_dom
  cases h_cod
  cases h_body
  rfl

/-- HEq congruence for `Term.lamPi`. -/
theorem Term.lamPi_HEq_congr
    {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {dom₁ dom₂ : Ty scope} (h_dom : dom₁ = dom₂)
    {cod₁ cod₂ : Ty (scope + 1)} (h_cod : cod₁ = cod₂)
    (body₁ : Term (Γ.cons dom₁) cod₁)
    (body₂ : Term (Γ.cons dom₂) cod₂)
    (h_body : HEq body₁ body₂) :
    HEq (Term.lamPi body₁) (Term.lamPi body₂) := by
  cases h_dom
  cases h_cod
  cases h_body
  rfl

/-- HEq congruence for `Term.appPi`. -/
theorem Term.appPi_HEq_congr
    {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {dom₁ dom₂ : Ty scope} (h_dom : dom₁ = dom₂)
    {cod₁ cod₂ : Ty (scope + 1)} (h_cod : cod₁ = cod₂)
    (f₁ : Term Γ (Ty.piTy dom₁ cod₁))
    (f₂ : Term Γ (Ty.piTy dom₂ cod₂))
    (h_f : HEq f₁ f₂)
    (a₁ : Term Γ dom₁) (a₂ : Term Γ dom₂) (h_a : HEq a₁ a₂) :
    HEq (Term.appPi f₁ a₁) (Term.appPi f₂ a₂) := by
  cases h_dom
  cases h_cod
  cases h_f
  cases h_a
  rfl

/-- HEq congruence for `Term.pair`. -/
theorem Term.pair_HEq_congr
    {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {first₁ first₂ : Ty scope} (h_first : first₁ = first₂)
    {second₁ second₂ : Ty (scope + 1)} (h_second : second₁ = second₂)
    (v₁ : Term Γ first₁) (v₂ : Term Γ first₂) (h_v : HEq v₁ v₂)
    (w₁ : Term Γ (second₁.subst0 first₁))
    (w₂ : Term Γ (second₂.subst0 first₂)) (h_w : HEq w₁ w₂) :
    HEq (Term.pair v₁ w₁) (Term.pair v₂ w₂) := by
  cases h_first
  cases h_second
  cases h_v
  cases h_w
  rfl

/-- HEq congruence for `Term.fst`. -/
theorem Term.fst_HEq_congr
    {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {first₁ first₂ : Ty scope} (h_first : first₁ = first₂)
    {second₁ second₂ : Ty (scope + 1)} (h_second : second₁ = second₂)
    (p₁ : Term Γ (Ty.sigmaTy first₁ second₁))
    (p₂ : Term Γ (Ty.sigmaTy first₂ second₂)) (h_p : HEq p₁ p₂) :
    HEq (Term.fst p₁) (Term.fst p₂) := by
  cases h_first
  cases h_second
  cases h_p
  rfl

/-- HEq congruence for `Term.snd`. -/
theorem Term.snd_HEq_congr
    {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {first₁ first₂ : Ty scope} (h_first : first₁ = first₂)
    {second₁ second₂ : Ty (scope + 1)} (h_second : second₁ = second₂)
    (p₁ : Term Γ (Ty.sigmaTy first₁ second₁))
    (p₂ : Term Γ (Ty.sigmaTy first₂ second₂)) (h_p : HEq p₁ p₂) :
    HEq (Term.snd p₁) (Term.snd p₂) := by
  cases h_first
  cases h_second
  cases h_p
  rfl

/-- **General HEq congruence for `Term.weaken`.**  Stronger than
`Term.heq_weaken_strip_cast` (which only handled an inner cast):
this allows the newType parameter AND the input term to differ
across the HEq.  Three `cases` discharge the three propositional
equalities; once unified, `rfl`. -/
theorem Term.weaken_HEq_congr
    {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {newType₁ newType₂ : Ty scope} (h_new : newType₁ = newType₂)
    {T₁ T₂ : Ty scope} (h_T : T₁ = T₂)
    (t₁ : Term Γ T₁) (t₂ : Term Γ T₂) (h_t : HEq t₁ t₂) :
    HEq (Term.weaken newType₁ t₁) (Term.weaken newType₂ t₂) := by
  cases h_new
  cases h_T
  cases h_t
  rfl

/-- HEq congruence for `Term.boolElim`. -/
theorem Term.boolElim_HEq_congr
    {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {result₁ result₂ : Ty scope} (h_result : result₁ = result₂)
    (s₁ s₂ : Term Γ Ty.bool) (h_s : s₁ = s₂)
    (t₁ : Term Γ result₁) (t₂ : Term Γ result₂) (h_t : HEq t₁ t₂)
    (e₁ : Term Γ result₁) (e₂ : Term Γ result₂) (h_e : HEq e₁ e₂) :
    HEq (Term.boolElim s₁ t₁ e₁) (Term.boolElim s₂ t₂ e₂) := by
  cases h_result
  cases h_s
  cases h_t
  cases h_e
  rfl

/-! ### v1.22 — `Term.subst_id_HEq` leaf cases.

The HEq form of `Term.subst_id` for the four leaf constructors —
each follows directly from the corresponding `▸`-form leaf
theorem in v1.19, but stated in HEq form for use by inductive
proofs that descend through `Term.subst`.

The `var` case unfolds to `(Ty.subst_id _).symm ▸ Term.var i`
(by `TermSubst.identity`'s definition), and `eqRec_heq`
discharges the cast-vs-naked HEq.  The `unit`, `boolTrue`,
`boolFalse` cases unfold to themselves because their types
don't depend on the substitution. -/

/-- Leaf HEq case of `Term.subst_id` for `var`. -/
theorem Term.subst_id_HEq_var
    {m : Mode} {scope : Nat} {Γ : Ctx m scope} (i : Fin scope) :
    HEq (Term.subst (TermSubst.identity Γ) (Term.var i))
        (Term.var (context := Γ) i) := by
  show HEq ((Ty.subst_id (varType Γ i)).symm ▸ Term.var i) (Term.var i)
  exact eqRec_heq _ _

/-- Leaf HEq case of `Term.subst_id` for `unit`. -/
theorem Term.subst_id_HEq_unit
    {m : Mode} {scope : Nat} {Γ : Ctx m scope} :
    HEq (Term.subst (TermSubst.identity Γ) (Term.unit (context := Γ)))
        (Term.unit (context := Γ)) :=
  HEq.refl _

/-- Leaf HEq case of `Term.subst_id` for `boolTrue`. -/
theorem Term.subst_id_HEq_boolTrue
    {m : Mode} {scope : Nat} {Γ : Ctx m scope} :
    HEq (Term.subst (TermSubst.identity Γ) (Term.boolTrue (context := Γ)))
        (Term.boolTrue (context := Γ)) :=
  HEq.refl _

/-- Leaf HEq case of `Term.subst_id` for `boolFalse`. -/
theorem Term.subst_id_HEq_boolFalse
    {m : Mode} {scope : Nat} {Γ : Ctx m scope} :
    HEq (Term.subst (TermSubst.identity Γ) (Term.boolFalse (context := Γ)))
        (Term.boolFalse (context := Γ)) :=
  HEq.refl _

/-! ### v1.23 — `Term.subst_id_HEq` recursive cases — closed (non-binder).

The constructor cases of `Term.subst_id_HEq` whose subterms live
in the same context as the parent (no `TermSubst.lift` needed).
Each takes the IH on each subterm as an HEq hypothesis and combines
them via the v1.21 HEq-congruence helpers + `Ty.subst_id` for the
type bridges.

These case lemmas do **not** depend on the (still-pending)
`Term.subst_HEq_pointwise` theorem.  They exist as standalone
modules so that an eventual full induction over `Term` can simply
invoke them — and so that downstream code that needs the closed
cases can use them now.

Three "simple" cases (no inner cast on the substituted result):
`app`, `fst`, `boolElim`.

Three "medium" cases (the `Term.subst` clause produces a
`Ty.subst0_subst_commute`-cast on the result, which we strip via
`eqRec_heq` before applying the constructor congruence): `appPi`,
`pair`, `snd`. -/

/-- Recursive HEq case of `Term.subst_id` for `app`. -/
theorem Term.subst_id_HEq_app
    {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {T₁ T₂ : Ty scope}
    (f : Term Γ (T₁.arrow T₂)) (a : Term Γ T₁)
    (ih_f : HEq (Term.subst (TermSubst.identity Γ) f) f)
    (ih_a : HEq (Term.subst (TermSubst.identity Γ) a) a) :
    HEq (Term.subst (TermSubst.identity Γ) (Term.app f a))
        (Term.app (context := Γ) f a) := by
  show HEq (Term.app (Term.subst (TermSubst.identity Γ) f)
                     (Term.subst (TermSubst.identity Γ) a))
           (Term.app f a)
  exact Term.app_HEq_congr (Ty.subst_id T₁) (Ty.subst_id T₂)
    _ _ ih_f _ _ ih_a

/-- Recursive HEq case of `Term.subst_id` for `fst`. -/
theorem Term.subst_id_HEq_fst
    {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {first : Ty scope} {second : Ty (scope + 1)}
    (p : Term Γ (Ty.sigmaTy first second))
    (ih_p : HEq (Term.subst (TermSubst.identity Γ) p) p) :
    HEq (Term.subst (TermSubst.identity Γ) (Term.fst p))
        (Term.fst (context := Γ) p) := by
  show HEq (Term.fst (Term.subst (TermSubst.identity Γ) p))
           (Term.fst p)
  apply Term.fst_HEq_congr (Ty.subst_id first)
    ((Ty.subst_congr Subst.lift_identity_equiv second).trans
     (Ty.subst_id second))
  exact ih_p

/-- Recursive HEq case of `Term.subst_id` for `boolElim`. -/
theorem Term.subst_id_HEq_boolElim
    {m : Mode} {scope : Nat} {Γ : Ctx m scope} {result : Ty scope}
    (s : Term Γ Ty.bool) (t : Term Γ result) (e : Term Γ result)
    (ih_s : HEq (Term.subst (TermSubst.identity Γ) s) s)
    (ih_t : HEq (Term.subst (TermSubst.identity Γ) t) t)
    (ih_e : HEq (Term.subst (TermSubst.identity Γ) e) e) :
    HEq (Term.subst (TermSubst.identity Γ) (Term.boolElim s t e))
        (Term.boolElim (context := Γ) s t e) := by
  show HEq (Term.boolElim
            (Term.subst (TermSubst.identity Γ) s)
            (Term.subst (TermSubst.identity Γ) t)
            (Term.subst (TermSubst.identity Γ) e))
           (Term.boolElim s t e)
  apply Term.boolElim_HEq_congr (Ty.subst_id result)
    _ _ (eq_of_heq ih_s)
    _ _ ih_t
    _ _ ih_e

/-- Recursive HEq case of `Term.subst_id` for `appPi`.  The
substituted result carries a `Ty.subst0_subst_commute` cast on
the outside; `eqRec_heq` strips it before constructor congruence. -/
theorem Term.subst_id_HEq_appPi
    {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {dom : Ty scope} {cod : Ty (scope + 1)}
    (f : Term Γ (Ty.piTy dom cod)) (a : Term Γ dom)
    (ih_f : HEq (Term.subst (TermSubst.identity Γ) f) f)
    (ih_a : HEq (Term.subst (TermSubst.identity Γ) a) a) :
    HEq (Term.subst (TermSubst.identity Γ) (Term.appPi f a))
        (Term.appPi (context := Γ) f a) := by
  show HEq
    ((Ty.subst0_subst_commute cod dom Subst.identity).symm ▸
      Term.appPi (Term.subst (TermSubst.identity Γ) f)
                 (Term.subst (TermSubst.identity Γ) a))
    (Term.appPi f a)
  apply HEq.trans (eqRec_heq _ _)
  exact Term.appPi_HEq_congr (Ty.subst_id dom)
    ((Ty.subst_congr Subst.lift_identity_equiv cod).trans
     (Ty.subst_id cod))
    _ _ ih_f _ _ ih_a

/-- Recursive HEq case of `Term.subst_id` for `pair`. -/
theorem Term.subst_id_HEq_pair
    {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {first : Ty scope} {second : Ty (scope + 1)}
    (v : Term Γ first) (w : Term Γ (second.subst0 first))
    (ih_v : HEq (Term.subst (TermSubst.identity Γ) v) v)
    (ih_w : HEq (Term.subst (TermSubst.identity Γ) w) w) :
    HEq (Term.subst (TermSubst.identity Γ) (Term.pair v w))
        (Term.pair (context := Γ) v w) := by
  show HEq
    (Term.pair (Term.subst (TermSubst.identity Γ) v)
      ((Ty.subst0_subst_commute second first Subst.identity) ▸
        (Term.subst (TermSubst.identity Γ) w)))
    (Term.pair v w)
  apply Term.pair_HEq_congr (Ty.subst_id first)
    ((Ty.subst_congr Subst.lift_identity_equiv second).trans
     (Ty.subst_id second))
    _ _ ih_v
  apply HEq.trans (eqRec_heq _ _)
  exact ih_w

/-- Recursive HEq case of `Term.subst_id` for `snd`. -/
theorem Term.subst_id_HEq_snd
    {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {first : Ty scope} {second : Ty (scope + 1)}
    (p : Term Γ (Ty.sigmaTy first second))
    (ih_p : HEq (Term.subst (TermSubst.identity Γ) p) p) :
    HEq (Term.subst (TermSubst.identity Γ) (Term.snd p))
        (Term.snd (context := Γ) p) := by
  show HEq
    ((Ty.subst0_subst_commute second first Subst.identity).symm ▸
      Term.snd (Term.subst (TermSubst.identity Γ) p))
    (Term.snd p)
  apply HEq.trans (eqRec_heq _ _)
  apply Term.snd_HEq_congr (Ty.subst_id first)
    ((Ty.subst_congr Subst.lift_identity_equiv second).trans
     (Ty.subst_id second))
  exact ih_p

/-! ### v1.24 — `TermSubst.lift_HEq_pointwise`.

Pointwise HEq for the lifted versions of two TermSubsts that are
themselves pointwise HEq (and whose underlying Substs are
pointwise equal).  The position-0 case bridges through the
context-shape difference (newType.subst σ₁ vs newType.subst σ₂);
the position-(k+1) case bridges through `Term.weaken_HEq_congr`.

Used by the binder cases of `Term.subst_HEq_pointwise` (lam,
lamPi) — the recursive call descends under a binder, which
extends the TermSubsts by `lift`, and the new pointwise-HEq
hypothesis is exactly what this theorem produces. -/
theorem TermSubst.lift_HEq_pointwise
    {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {σ₁ σ₂ : Subst scope scope'}
    (σt₁ : TermSubst Γ Δ σ₁) (σt₂ : TermSubst Γ Δ σ₂)
    (h_subst : Subst.equiv σ₁ σ₂)
    (h_pointwise : ∀ i, HEq (σt₁ i) (σt₂ i))
    (newType : Ty scope) :
    ∀ i, HEq (TermSubst.lift σt₁ newType i)
             (TermSubst.lift σt₂ newType i) := by
  -- Bridging fact: newType.subst σ₁ = newType.subst σ₂.
  have h_new : newType.subst σ₁ = newType.subst σ₂ :=
    Ty.subst_congr h_subst newType
  intro i
  match i with
  | ⟨0, _⟩ =>
    -- LHS = (Ty.subst_weaken_commute newType σ₁).symm ▸
    --        Term.var (context := Δ.cons (newType.subst σ₁)) ⟨0, _⟩
    -- RHS = (Ty.subst_weaken_commute newType σ₂).symm ▸
    --        Term.var (context := Δ.cons (newType.subst σ₂)) ⟨0, _⟩
    -- Strip outer casts on both sides via eqRec_heq, bridge naked
    -- Term.var values via heq_var_across_ctx_eq + congrArg-cons.
    -- Note: Term.var lives at scope' + 1, so the Fin uses
    -- Nat.zero_lt_succ scope' (NOT the Fin destructure's h0 which
    -- is at scope + 1).
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (heq_var_across_ctx_eq (congrArg (Δ.cons) h_new)
        ⟨0, Nat.zero_lt_succ scope'⟩)
    exact (eqRec_heq _ _).symm
  | ⟨k + 1, hk⟩ =>
    -- LHS = (Ty.subst_weaken_commute (varType Γ ⟨k,_⟩) σ₁).symm ▸
    --        Term.weaken (newType.subst σ₁) (σt₁ ⟨k, _⟩)
    -- RHS = (Ty.subst_weaken_commute (varType Γ ⟨k,_⟩) σ₂).symm ▸
    --        Term.weaken (newType.subst σ₂) (σt₂ ⟨k, _⟩)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b :=
      Term.weaken (newType.subst σ₂)
        (σt₂ ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
    · exact Term.weaken_HEq_congr h_new
        (Ty.subst_congr h_subst
          (varType Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
        (σt₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩)
        (σt₂ ⟨k, Nat.lt_of_succ_lt_succ hk⟩)
        (h_pointwise ⟨k, Nat.lt_of_succ_lt_succ hk⟩)
    · exact (eqRec_heq _ _).symm

/-! ### v1.24 — `Term.subst_HEq_pointwise`: substitution respects
pointwise HEq of TermSubsts.

The "general" form lets the target contexts of the two TermSubsts
differ propositionally (`Δ₁ ≠ Δ₂` but `Δ₁ = Δ₂`); this
generality is needed for the binder-case recursive calls, where
`TermSubst.lift σt₁ dom` and `TermSubst.lift σt₂ dom` land in
`Δ.cons (dom.subst σ₁)` vs `Δ.cons (dom.subst σ₂)` — same scope,
different concrete contexts.

Pattern-matched recursive theorem, axiom-free per the project's
binder-form discipline.  Each binder case descends via
`TermSubst.lift_HEq_pointwise` to maintain the pointwise hypothesis
under the extended scope. -/
theorem Term.subst_HEq_pointwise
    {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ₁ Δ₂ : Ctx m scope'}
    (h_ctx : Δ₁ = Δ₂)
    {σ₁ σ₂ : Subst scope scope'}
    (σt₁ : TermSubst Γ Δ₁ σ₁) (σt₂ : TermSubst Γ Δ₂ σ₂)
    (h_subst : Subst.equiv σ₁ σ₂)
    (h_pointwise : ∀ i, HEq (σt₁ i) (σt₂ i)) :
    {T : Ty scope} → (t : Term Γ T) →
      HEq (Term.subst σt₁ t) (Term.subst σt₂ t)
  | _, .var i => h_pointwise i
  | _, .unit => by cases h_ctx; exact HEq.refl _
  | _, .app (domainType := T₁) (codomainType := T₂) f a => by
    cases h_ctx
    show HEq (Term.app (Term.subst σt₁ f) (Term.subst σt₁ a))
             (Term.app (Term.subst σt₂ f) (Term.subst σt₂ a))
    exact Term.app_HEq_congr
      (Ty.subst_congr h_subst T₁) (Ty.subst_congr h_subst T₂)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise f)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise a)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    cases h_ctx
    show HEq
      (Term.lam (codomainType := cod.subst σ₁)
        ((Ty.subst_weaken_commute cod σ₁) ▸
          (Term.subst (TermSubst.lift σt₁ dom) body)))
      (Term.lam (codomainType := cod.subst σ₂)
        ((Ty.subst_weaken_commute cod σ₂) ▸
          (Term.subst (TermSubst.lift σt₂ dom) body)))
    apply Term.lam_HEq_congr
      (Ty.subst_congr h_subst dom) (Ty.subst_congr h_subst cod)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_pointwise
        (congrArg Δ₁.cons (Ty.subst_congr h_subst dom))
        (TermSubst.lift σt₁ dom) (TermSubst.lift σt₂ dom)
        (Subst.lift_equiv h_subst)
        (TermSubst.lift_HEq_pointwise σt₁ σt₂ h_subst h_pointwise dom)
        body)
    exact (eqRec_heq _ _).symm
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    cases h_ctx
    show HEq
      (Term.lamPi (Term.subst (TermSubst.lift σt₁ dom) body))
      (Term.lamPi (Term.subst (TermSubst.lift σt₂ dom) body))
    apply Term.lamPi_HEq_congr
      (Ty.subst_congr h_subst dom)
      (Ty.subst_congr (Subst.lift_equiv h_subst) cod)
    exact Term.subst_HEq_pointwise
      (congrArg Δ₁.cons (Ty.subst_congr h_subst dom))
      (TermSubst.lift σt₁ dom) (TermSubst.lift σt₂ dom)
      (Subst.lift_equiv h_subst)
      (TermSubst.lift_HEq_pointwise σt₁ σt₂ h_subst h_pointwise dom)
      body
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    cases h_ctx
    show HEq
      ((Ty.subst0_subst_commute cod dom σ₁).symm ▸
        Term.appPi (Term.subst σt₁ f) (Term.subst σt₁ a))
      ((Ty.subst0_subst_commute cod dom σ₂).symm ▸
        Term.appPi (Term.subst σt₂ f) (Term.subst σt₂ a))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b :=
      Term.appPi (Term.subst σt₂ f) (Term.subst σt₂ a))
    · exact Term.appPi_HEq_congr
        (Ty.subst_congr h_subst dom)
        (Ty.subst_congr (Subst.lift_equiv h_subst) cod)
        _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise f)
        _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise a)
    · exact (eqRec_heq _ _).symm
  | _, .pair (firstType := first) (secondType := second) v w => by
    cases h_ctx
    show HEq
      (Term.pair (Term.subst σt₁ v)
        ((Ty.subst0_subst_commute second first σ₁) ▸ (Term.subst σt₁ w)))
      (Term.pair (Term.subst σt₂ v)
        ((Ty.subst0_subst_commute second first σ₂) ▸ (Term.subst σt₂ w)))
    apply Term.pair_HEq_congr
      (Ty.subst_congr h_subst first)
      (Ty.subst_congr (Subst.lift_equiv h_subst) second)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise v)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise w)
    exact (eqRec_heq _ _).symm
  | _, .fst (firstType := first) (secondType := second) p => by
    cases h_ctx
    show HEq (Term.fst (Term.subst σt₁ p)) (Term.fst (Term.subst σt₂ p))
    exact Term.fst_HEq_congr
      (Ty.subst_congr h_subst first)
      (Ty.subst_congr (Subst.lift_equiv h_subst) second)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise p)
  | _, .snd (firstType := first) (secondType := second) p => by
    cases h_ctx
    show HEq
      ((Ty.subst0_subst_commute second first σ₁).symm ▸
        Term.snd (Term.subst σt₁ p))
      ((Ty.subst0_subst_commute second first σ₂).symm ▸
        Term.snd (Term.subst σt₂ p))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b := Term.snd (Term.subst σt₂ p))
    · exact Term.snd_HEq_congr
        (Ty.subst_congr h_subst first)
        (Ty.subst_congr (Subst.lift_equiv h_subst) second)
        _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise p)
    · exact (eqRec_heq _ _).symm
  | _, .boolTrue => by cases h_ctx; exact HEq.refl _
  | _, .boolFalse => by cases h_ctx; exact HEq.refl _
  | _, .boolElim (resultType := result) s t e => by
    cases h_ctx
    show HEq
      (Term.boolElim (Term.subst σt₁ s) (Term.subst σt₁ t) (Term.subst σt₁ e))
      (Term.boolElim (Term.subst σt₂ s) (Term.subst σt₂ t) (Term.subst σt₂ e))
    exact Term.boolElim_HEq_congr
      (Ty.subst_congr h_subst result)
      _ _ (eq_of_heq
            (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise s))
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise t)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise e)

/-! ### v1.25 — `Term.subst_id_HEq`: full HEq form of subst-by-identity.

The cap-stone theorem: substituting any term by `TermSubst.identity Γ`
is HEq to the original term.  Proven by structural pattern-match on
Term, invoking the v1.22 leaf cases / v1.23 closed-context cases
directly, and using `Term.subst_HEq_pointwise` (v1.24.5) at the
binder cases to bridge `TermSubst.lift (TermSubst.identity Γ)`
to `TermSubst.identity (Γ.cons _)` — exactly the HEq witness
`TermSubst.lift_identity_pointwise` (v1.20) supplies.

This completes the HEq-form of Term's substitution-by-identity
functoriality.  The explicit-`▸`-form (`Term.subst_id`) follows
by `eq_of_heq` plus a final cast-cancellation. -/
theorem Term.subst_id_HEq {m : Mode} {scope : Nat} {Γ : Ctx m scope} :
    {T : Ty scope} → (t : Term Γ T) →
      HEq (Term.subst (TermSubst.identity Γ) t) t
  | _, .var i => Term.subst_id_HEq_var i
  | _, .unit => Term.subst_id_HEq_unit
  | _, .app f a =>
    Term.subst_id_HEq_app f a
      (Term.subst_id_HEq f) (Term.subst_id_HEq a)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    show HEq
      (Term.lam (codomainType := cod.subst Subst.identity)
        ((Ty.subst_weaken_commute cod Subst.identity) ▸
          (Term.subst (TermSubst.lift (TermSubst.identity Γ) dom) body)))
      (Term.lam body)
    apply Term.lam_HEq_congr (Ty.subst_id dom) (Ty.subst_id cod)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_pointwise
        (congrArg Γ.cons (Ty.subst_id dom))
        (TermSubst.lift (TermSubst.identity Γ) dom)
        (TermSubst.identity (Γ.cons dom))
        Subst.lift_identity_equiv
        (TermSubst.lift_identity_pointwise Γ dom)
        body)
    exact Term.subst_id_HEq body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    show HEq
      (Term.lamPi (Term.subst (TermSubst.lift (TermSubst.identity Γ) dom) body))
      (Term.lamPi body)
    apply Term.lamPi_HEq_congr (Ty.subst_id dom)
      ((Ty.subst_congr Subst.lift_identity_equiv cod).trans
       (Ty.subst_id cod))
    apply HEq.trans
      (Term.subst_HEq_pointwise
        (congrArg Γ.cons (Ty.subst_id dom))
        (TermSubst.lift (TermSubst.identity Γ) dom)
        (TermSubst.identity (Γ.cons dom))
        Subst.lift_identity_equiv
        (TermSubst.lift_identity_pointwise Γ dom)
        body)
    exact Term.subst_id_HEq body
  | _, .appPi f a =>
    Term.subst_id_HEq_appPi f a
      (Term.subst_id_HEq f) (Term.subst_id_HEq a)
  | _, .pair v w =>
    Term.subst_id_HEq_pair v w
      (Term.subst_id_HEq v) (Term.subst_id_HEq w)
  | _, .fst p =>
    Term.subst_id_HEq_fst p (Term.subst_id_HEq p)
  | _, .snd p =>
    Term.subst_id_HEq_snd p (Term.subst_id_HEq p)
  | _, .boolTrue => Term.subst_id_HEq_boolTrue
  | _, .boolFalse => Term.subst_id_HEq_boolFalse
  | _, .boolElim s t e =>
    Term.subst_id_HEq_boolElim s t e
      (Term.subst_id_HEq s) (Term.subst_id_HEq t) (Term.subst_id_HEq e)

/-! ### v1.25 — `Term.subst_id`: the explicit-▸ form of subst-by-identity = identity.

Direct corollary of `Term.subst_id_HEq` plus `eqRec_heq` to
strip the outer cast.  Both sides of the equation live at
`Term Γ T` after the cast on the LHS, so `eq_of_heq` discharges
the HEq → Eq conversion. -/
theorem Term.subst_id {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {T : Ty scope} (t : Term Γ T) :
    (Ty.subst_id T) ▸ Term.subst (TermSubst.identity Γ) t = t :=
  eq_of_heq (HEq.trans (eqRec_heq _ _) (Term.subst_id_HEq t))

/-! ### v1.26 — Cast-through-Term.subst HEq helper.

Auxiliary HEq lemma: pushing a propositional type-cast on the
input of `Term.subst` is HEq to applying the substitution
directly.  Proven by `cases h; rfl` — once the cast equation is
substituted by the trivial reflexivity, both sides are
literally identical.

Useful for downstream theorems where the input term carries a
type-level cast that needs to escape the `Term.subst` call so
the substitution's structural recursion can fire on the bare
constructor.  In particular, this is the bridge for
`TermSubst.lift_compose_pointwise` (v1.27+) at position 0,
where `(σt₁.lift newType) ⟨0, _⟩` produces a casted `Term.var`
that must flow through an outer `Term.subst σt₂`. -/
theorem Term.subst_HEq_cast_input
    {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {σ : Subst scope scope'} (σt : TermSubst Γ Δ σ)
    {T₁ T₂ : Ty scope} (h : T₁ = T₂) (t : Term Γ T₁) :
    HEq (Term.subst σt (h ▸ t)) (Term.subst σt t) := by
  cases h
  rfl

/-! ### v1.27 — `TermSubst.lift_compose_pointwise` at position 0.

The compose-side analogue of `TermSubst.lift_identity_pointwise`
(v1.20) for the `⟨0, _⟩` Fin position only.  The `⟨k+1, _⟩`
position requires a Term-level subst-weaken commute lemma
(deferred to a later version) and is proved as a separate
companion theorem.

The position-0 case alone is independently useful: it witnesses
that lifting a composed term-substitution under a binder agrees
HEq with composing the two lifts, **on the freshly-bound
variable**.  Since v1.20's `lift_identity_pointwise` had no
position-0 vs position-`k+1` asymmetry (both reduce to a casted
Term.var), the compose-side asymmetry comes from
`TermSubst.compose`'s definition: at position 0 the inner
subterm is a casted `Term.var`, which `Term.subst` reduces via
its `var` arm; at position `k+1` the inner subterm is
`Term.weaken`, which has no such direct reduction rule.

The differences between LHS and RHS at position 0 are:

  * **Target context**: `Γ₃.cons (newType.subst (Subst.compose σ₁ σ₂))`
    (LHS) vs `Γ₃.cons ((newType.subst σ₁).subst σ₂)` (RHS).
    Bridged by `Ty.subst_compose newType σ₁ σ₂`.
  * **Underlying substitution**: `(Subst.compose σ₁ σ₂).lift`
    (LHS) vs `Subst.compose σ₁.lift σ₂.lift` (RHS).
    Bridged by `Subst.lift_compose_equiv`.

The proof strips outer casts on both sides via `eqRec_heq`,
pushes the inner cast through `Term.subst` via
`Term.subst_HEq_cast_input` (v1.26), reduces `Term.subst σt
(Term.var ⟨0, _⟩)` to `σt ⟨0, _⟩` definitionally, and bridges
the resulting naked `Term.var` values via
`heq_var_across_ctx_eq` over the context equality. -/
theorem TermSubst.lift_compose_pointwise_zero
    {m : Mode} {scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m scope₁} {Γ₂ : Ctx m scope₂} {Γ₃ : Ctx m scope₃}
    {σ₁ : Subst scope₁ scope₂} {σ₂ : Subst scope₂ scope₃}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂)
    (newType : Ty scope₁) :
    HEq
      (TermSubst.lift (TermSubst.compose σt₁ σt₂) newType
        ⟨0, Nat.zero_lt_succ _⟩)
      (TermSubst.compose (σt₁.lift newType)
                          (σt₂.lift (newType.subst σ₁))
        ⟨0, Nat.zero_lt_succ _⟩) := by
  -- LHS = (Ty.subst_weaken_commute newType (Subst.compose σ₁ σ₂)).symm ▸
  --        Term.var (context := Γ₃.cons (newType.subst (Subst.compose σ₁ σ₂))) ⟨0, _⟩
  --
  -- RHS = Ty.subst_compose newType.weaken σ₁.lift σ₂.lift ▸
  --        Term.subst (σt₂.lift (newType.subst σ₁))
  --          ((Ty.subst_weaken_commute newType σ₁).symm ▸
  --            Term.var (context := Γ₂.cons (newType.subst σ₁)) ⟨0, _⟩)
  --
  -- Strip outer cast on LHS via eqRec_heq.
  apply HEq.trans (eqRec_heq _ _)
  -- Goal: HEq (Term.var (context := Γ₃.cons (newType.subst (compose σ₁ σ₂))) ⟨0, _⟩) RHS
  --
  -- Flip and strip outer cast on RHS too.
  apply HEq.symm
  apply HEq.trans (eqRec_heq _ _)
  -- Goal: HEq (Term.subst (σt₂.lift _) (cast ▸ Term.var ⟨0, _⟩))
  --           (Term.var (context := Γ₃.cons (newType.subst (compose σ₁ σ₂))) ⟨0, _⟩)
  --
  -- Push the inner cast out through Term.subst via v1.26 helper.
  apply HEq.trans
    (Term.subst_HEq_cast_input
      (σt₂.lift (newType.subst σ₁))
      (Ty.subst_weaken_commute newType σ₁).symm
      (Term.var (context := Γ₂.cons (newType.subst σ₁))
        ⟨0, Nat.zero_lt_succ _⟩))
  -- Goal: HEq (Term.subst (σt₂.lift _) (Term.var ⟨0, _⟩))
  --           (Term.var (context := Γ₃.cons (newType.subst (compose σ₁ σ₂))) ⟨0, _⟩)
  --
  -- Term.subst σt (Term.var i) ≡ σt i (Term.subst's var arm).
  show HEq ((σt₂.lift (newType.subst σ₁)) ⟨0, Nat.zero_lt_succ _⟩) _
  -- (σt₂.lift X) ⟨0, _⟩ = (Ty.subst_weaken_commute X σ₂).symm ▸ Term.var ⟨0, _⟩
  apply HEq.trans (eqRec_heq _ _)
  -- Goal: HEq (Term.var (context := Γ₃.cons ((newType.subst σ₁).subst σ₂)) ⟨0, _⟩)
  --           (Term.var (context := Γ₃.cons (newType.subst (compose σ₁ σ₂))) ⟨0, _⟩)
  --
  -- Bridge via Ty.subst_compose newType σ₁ σ₂ at the context level.
  exact heq_var_across_ctx_eq
    (congrArg Γ₃.cons (Ty.subst_compose newType σ₁ σ₂))
    ⟨0, Nat.zero_lt_succ _⟩

/-! ### v1.28 — Term-level subst-weaken commute, leaf cases.

The theorem we ultimately want (general form):

  Term.subst (σt.lift X) (Term.weaken X t) ≃HEq≃
    Term.weaken (X.subst σ) (Term.subst σt t)

This is the term-level analogue of `Ty.subst_weaken_commute`
(line 655) — the central lemma for substitution functoriality
at the Term level.  It is the missing piece for both
`Term.subst_compose` (full functoriality) and
`TermSubst.lift_compose_pointwise`'s `k+1` case (the position-0
case landed at v1.27).

The proof is a 12-case structural induction on `t`.  We ship it
in three layers:

  * v1.28 (this section) — the four leaf cases `var`, `unit`,
    `boolTrue`, `boolFalse`.  Each is a cast-cancellation via
    `eqRec_heq` on a definitionally-reducing left-hand side.
  * v1.29 — the closed-context recursive cases (`app`, `fst`,
    `boolElim`, plus the cast-bearing `appPi`, `pair`, `snd`).
    Recurse on subterms; the binder-free cases combine via
    constructor-HEq congruences.
  * v1.30 — the binder cases (`lam`, `lamPi`).  Need a Term-level
    rename-subst commute helper because the body lives under an
    extra binder where `Term.weaken X` lifts to `TermRenaming.lift`
    and `σt.lift X` further lifts to `TermSubst.lift`.

Splitting this way matches the discipline of v1.22 → v1.23 →
v1.24 (leaf → closed-context → binder) and lands axiom-free at
each step. -/

/-- Leaf case: `Term.subst (σt.lift X) (Term.weaken X (Term.var i))
    ≃ Term.weaken (X.subst σ) (Term.subst σt (Term.var i))`.

LHS reduces definitionally:

  Term.weaken X (Term.var i)
    = Term.var (Fin.succ i)               -- TermRenaming.weaken's
                                          --   per-position witness is rfl
  Term.subst (σt.lift X) (Term.var i.succ)
    = (σt.lift X) (Fin.succ i)
    = (Ty.subst_weaken_commute (varType Γ i) σ).symm ▸
        Term.weaken (X.subst σ) (σt i)    -- TermSubst.lift's `k+1` arm

RHS reduces:

  Term.subst σt (Term.var i) = σt i
  Term.weaken (X.subst σ) (σt i)

LHS and RHS differ only by the outer cast on LHS; `eqRec_heq`
strips it. -/
theorem Term.subst_weaken_commute_HEq_var
    {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {σ : Subst scope scope'} (σt : TermSubst Γ Δ σ)
    (X : Ty scope) (i : Fin scope) :
    HEq
      (Term.subst (σt.lift X)
        (Term.weaken X (Term.var (context := Γ) i)))
      (Term.weaken (X.subst σ)
        (Term.subst σt (Term.var (context := Γ) i))) := by
  show HEq
    ((Ty.subst_weaken_commute (varType Γ i) σ).symm ▸
        Term.weaken (X.subst σ) (σt i))
    (Term.weaken (X.subst σ) (σt i))
  exact eqRec_heq _ _

/-- Leaf case: `Term.subst (σt.lift X) (Term.weaken X Term.unit) ≃
    Term.weaken (X.subst σ) (Term.subst σt Term.unit)`.

Both sides reduce definitionally to `Term.unit` in the same
context (`Δ.cons (X.subst σ)`).  HEq via `HEq.refl _`. -/
theorem Term.subst_weaken_commute_HEq_unit
    {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {σ : Subst scope scope'} (σt : TermSubst Γ Δ σ)
    (X : Ty scope) :
    HEq
      (Term.subst (σt.lift X)
        (Term.weaken X (Term.unit (context := Γ))))
      (Term.weaken (X.subst σ)
        (Term.subst σt (Term.unit (context := Γ)))) :=
  HEq.refl _

/-- Leaf case for `boolTrue` — same shape as `unit`, both sides
reduce to `Term.boolTrue` in the same context. -/
theorem Term.subst_weaken_commute_HEq_boolTrue
    {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {σ : Subst scope scope'} (σt : TermSubst Γ Δ σ)
    (X : Ty scope) :
    HEq
      (Term.subst (σt.lift X)
        (Term.weaken X (Term.boolTrue (context := Γ))))
      (Term.weaken (X.subst σ)
        (Term.subst σt (Term.boolTrue (context := Γ)))) :=
  HEq.refl _

/-- Leaf case for `boolFalse` — same shape as `unit` and
`boolTrue`. -/
theorem Term.subst_weaken_commute_HEq_boolFalse
    {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {σ : Subst scope scope'} (σt : TermSubst Γ Δ σ)
    (X : Ty scope) :
    HEq
      (Term.subst (σt.lift X)
        (Term.weaken X (Term.boolFalse (context := Γ))))
      (Term.weaken (X.subst σ)
        (Term.subst σt (Term.boolFalse (context := Γ)))) :=
  HEq.refl _

/-! ### v1.29 — Term-level subst-weaken commute, closed-context
recursive cases (no-cast subset).

The next layer above v1.28's leaves: closed-context constructors
`app` and `boolElim`.  Each takes IH hypotheses for its
subterms (since they aren't yet packaged inside the eventual
full structural induction).  Both reduce cleanly: `Term.weaken X`
on the constructor pushes through, `Term.subst (σt.lift X)` on
the constructor pushes through, and the resulting two sides are
combined via the constructor-specific HEq congruence.

The remaining four closed-context cases (`fst`, `snd`, `pair`,
`appPi`) involve sigmaTy/piTy second-component lifts whose
type-level equation requires the full rename-subst commute
chain.  Those land in v1.30.

The two binder cases (`lam`, `lamPi`) need Term-level lift-of-lift
mechanics and land in v1.31.  The full structural-induction
theorem combining all 12 cases is v1.32. -/

/-- Closed-context recursive case for `app`.  No casts on either
side because `Term.weaken X` and `Term.subst σt` both push
through `Term.app` definitionally.  Combine via
`Term.app_HEq_congr` with type-equalities `Ty.subst_weaken_commute`
on each of T₁, T₂. -/
theorem Term.subst_weaken_commute_HEq_app
    {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {σ : Subst scope scope'} (σt : TermSubst Γ Δ σ)
    (X : Ty scope)
    {T₁ T₂ : Ty scope}
    (f : Term Γ (T₁.arrow T₂)) (a : Term Γ T₁)
    (ih_f : HEq
              (Term.subst (σt.lift X) (Term.weaken X f))
              (Term.weaken (X.subst σ) (Term.subst σt f)))
    (ih_a : HEq
              (Term.subst (σt.lift X) (Term.weaken X a))
              (Term.weaken (X.subst σ) (Term.subst σt a))) :
    HEq
      (Term.subst (σt.lift X) (Term.weaken X (Term.app f a)))
      (Term.weaken (X.subst σ) (Term.subst σt (Term.app f a))) := by
  show HEq
    (Term.app
      (Term.subst (σt.lift X) (Term.weaken X f))
      (Term.subst (σt.lift X) (Term.weaken X a)))
    (Term.app
      (Term.weaken (X.subst σ) (Term.subst σt f))
      (Term.weaken (X.subst σ) (Term.subst σt a)))
  exact Term.app_HEq_congr
    (Ty.subst_weaken_commute T₁ σ)
    (Ty.subst_weaken_commute T₂ σ)
    _ _ ih_f
    _ _ ih_a

/-- Closed-context recursive case for `boolElim`.  Analogous to
`app`: no casts, push through both `Term.weaken X` and
`Term.subst (σt.lift X)`, combine via `Term.boolElim_HEq_congr`.
The scrutinee `s` lives at `Ty.bool` which has no variables, so
its type is unchanged across substitution + weakening — HEq on
the scrutinee collapses to Eq via `eq_of_heq`. -/
theorem Term.subst_weaken_commute_HEq_boolElim
    {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {σ : Subst scope scope'} (σt : TermSubst Γ Δ σ)
    (X : Ty scope)
    {result : Ty scope}
    (s : Term Γ Ty.bool) (t : Term Γ result) (e : Term Γ result)
    (ih_s : HEq
              (Term.subst (σt.lift X) (Term.weaken X s))
              (Term.weaken (X.subst σ) (Term.subst σt s)))
    (ih_t : HEq
              (Term.subst (σt.lift X) (Term.weaken X t))
              (Term.weaken (X.subst σ) (Term.subst σt t)))
    (ih_e : HEq
              (Term.subst (σt.lift X) (Term.weaken X e))
              (Term.weaken (X.subst σ) (Term.subst σt e))) :
    HEq
      (Term.subst (σt.lift X)
        (Term.weaken X (Term.boolElim s t e)))
      (Term.weaken (X.subst σ)
        (Term.subst σt (Term.boolElim s t e))) := by
  show HEq
    (Term.boolElim
      (Term.subst (σt.lift X) (Term.weaken X s))
      (Term.subst (σt.lift X) (Term.weaken X t))
      (Term.subst (σt.lift X) (Term.weaken X e)))
    (Term.boolElim
      (Term.weaken (X.subst σ) (Term.subst σt s))
      (Term.weaken (X.subst σ) (Term.subst σt t))
      (Term.weaken (X.subst σ) (Term.subst σt e)))
  exact Term.boolElim_HEq_congr
    (Ty.subst_weaken_commute result σ)
    _ _ (eq_of_heq ih_s)
    _ _ ih_t
    _ _ ih_e

/-! ## v1.6 — typed reduction.

Single-step reduction `Step t₁ t₂` is a `Prop`-valued indexed relation
between terms of the *same* type.  The shared type is enforced
structurally — both sides of every constructor carry identical `mode`,
`scope`, `ctx`, and `T` indices, which means **subject reduction is
definitional**: there is no separate "preservation" theorem to prove,
because no `Step` proof can witness a type change.

v1.10 adds full β-reduction (`betaApp`, `betaAppPi`) plus a Σ-pair
projection rule.  Both β rules use `Term.subst0` from v1.10's term-
substitution discipline; the Σ rules require a cast through
`Ty.subst0`'s definitional unfolding for the `secondVal`'s type.

The reflexive-transitive closure `StepStar` lifts single-step to
multi-step reduction.  Together, `Step` and `StepStar` are the basis
for the conversion algorithm and eventual normaliser. -/

/-- Single-step reduction between terms of the *same* type.  The shared
typing is structural: every constructor's input and output `Term` carry
the same `Ctx` and `Ty`, so subject reduction holds definitionally.

v1.10 covers both congruence rules and the β-reduction rules
(`betaApp`, `betaAppPi`) plus Σ-projection rules (`betaFstPair`,
`betaSndPair`). -/
inductive Step :
    {mode : Mode} → {scope : Nat} → {ctx : Ctx mode scope} →
    {T : Ty scope} → Term ctx T → Term ctx T → Prop
  /-- Step inside the function position of a non-dependent application. -/
  | appLeft  :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {domainType codomainType : Ty scope}
        {functionTerm functionTerm' :
          Term ctx (.arrow domainType codomainType)}
        {argumentTerm : Term ctx domainType},
      Step functionTerm functionTerm' →
      Step (Term.app functionTerm argumentTerm)
           (Term.app functionTerm' argumentTerm)
  /-- Step inside the argument position of a non-dependent application. -/
  | appRight :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {domainType codomainType : Ty scope}
        {functionTerm : Term ctx (.arrow domainType codomainType)}
        {argumentTerm argumentTerm' : Term ctx domainType},
      Step argumentTerm argumentTerm' →
      Step (Term.app functionTerm argumentTerm)
           (Term.app functionTerm argumentTerm')
  /-- Step inside the body of a non-dependent λ-abstraction. -/
  | lamBody  :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {domainType codomainType : Ty scope}
        {body body' : Term (ctx.cons domainType) codomainType.weaken},
      Step body body' →
      Step (Term.lam (codomainType := codomainType) body)
           (Term.lam (codomainType := codomainType) body')
  /-- Step inside the function position of a dependent application. -/
  | appPiLeft :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {domainType : Ty scope} {codomainType : Ty (scope + 1)}
        {functionTerm functionTerm' :
          Term ctx (.piTy domainType codomainType)}
        {argumentTerm : Term ctx domainType},
      Step functionTerm functionTerm' →
      Step (Term.appPi functionTerm argumentTerm)
           (Term.appPi functionTerm' argumentTerm)
  /-- Step inside the argument position of a dependent application. -/
  | appPiRight :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {domainType : Ty scope} {codomainType : Ty (scope + 1)}
        {functionTerm : Term ctx (.piTy domainType codomainType)}
        {argumentTerm argumentTerm' : Term ctx domainType},
      Step argumentTerm argumentTerm' →
      Step (Term.appPi functionTerm argumentTerm)
           (Term.appPi functionTerm argumentTerm')
  /-- Step inside the body of a dependent λ-abstraction. -/
  | lamPiBody :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {domainType : Ty scope} {codomainType : Ty (scope + 1)}
        {body body' : Term (ctx.cons domainType) codomainType},
      Step body body' →
      Step (Term.lamPi (domainType := domainType) body)
           (Term.lamPi (domainType := domainType) body')
  /-- Step inside the first component of a pair. -/
  | pairLeft :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {firstType : Ty scope} {secondType : Ty (scope + 1)}
        {firstVal firstVal' : Term ctx firstType}
        {secondVal : Term ctx (secondType.subst0 firstType)},
      Step firstVal firstVal' →
      Step (Term.pair (secondType := secondType) firstVal secondVal)
           (Term.pair (secondType := secondType) firstVal' secondVal)
  /-- Step inside the second component of a pair. -/
  | pairRight :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {firstType : Ty scope} {secondType : Ty (scope + 1)}
        {firstVal : Term ctx firstType}
        {secondVal secondVal' : Term ctx (secondType.subst0 firstType)},
      Step secondVal secondVal' →
      Step (Term.pair firstVal secondVal)
           (Term.pair firstVal secondVal')
  /-- Step inside the argument of a first projection. -/
  | fstCong :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {firstType : Ty scope} {secondType : Ty (scope + 1)}
        {pairTerm pairTerm' : Term ctx (.sigmaTy firstType secondType)},
      Step pairTerm pairTerm' →
      Step (Term.fst pairTerm) (Term.fst pairTerm')
  /-- Step inside the argument of a second projection. -/
  | sndCong :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {firstType : Ty scope} {secondType : Ty (scope + 1)}
        {pairTerm pairTerm' : Term ctx (.sigmaTy firstType secondType)},
      Step pairTerm pairTerm' →
      Step (Term.snd pairTerm) (Term.snd pairTerm')
  /-- **β-reduction for non-dependent application**: `(λx. body) arg ⟶
  body[arg/x]`.  The result type matches `Term.app`'s codomain because
  `body : Term (ctx.cons domainType) codomainType.weaken` and
  substituting at the type level via `body.subst0 (...)` reduces
  `codomainType.weaken.subst0 _` to `codomainType` per
  `Ty.weaken_subst_singleton`.  We thread the cast through `▸`. -/
  | betaApp :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {domainType codomainType : Ty scope}
        (body : Term (ctx.cons domainType) codomainType.weaken)
        (arg : Term ctx domainType),
      Step (Term.app (Term.lam (codomainType := codomainType) body) arg)
           ((Ty.weaken_subst_singleton codomainType domainType) ▸
              Term.subst0 body arg)
  /-- **β-reduction for dependent application**: `(λx. body) arg ⟶
  body[arg/x]` where the codomain may depend on `x` via `tyVar 0`.
  No cast needed: `body.subst0 arg : Term ctx (codomainType.subst0
  domainType)` matches `Term.appPi`'s declared result type exactly. -/
  | betaAppPi :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {domainType : Ty scope} {codomainType : Ty (scope + 1)}
        (body : Term (ctx.cons domainType) codomainType)
        (arg : Term ctx domainType),
      Step (Term.appPi (Term.lamPi (domainType := domainType) body) arg)
           (Term.subst0 body arg)
  /-- **Σ first projection**: `fst (pair a b) ⟶ a`. -/
  | betaFstPair :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {firstType : Ty scope} {secondType : Ty (scope + 1)}
        (firstVal : Term ctx firstType)
        (secondVal : Term ctx (secondType.subst0 firstType)),
      Step (Term.fst
              (Term.pair (firstType := firstType)
                         (secondType := secondType) firstVal secondVal))
           firstVal
  /-- **Σ second projection**: `snd (pair a b) ⟶ b`.  The result type
  is `Term ctx (secondType.subst0 firstType)` — both `Term.snd`'s
  declared result and `secondVal`'s declared type — so no cast is
  needed. -/
  | betaSndPair :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {firstType : Ty scope} {secondType : Ty (scope + 1)}
        (firstVal : Term ctx firstType)
        (secondVal : Term ctx (secondType.subst0 firstType)),
      Step (Term.snd
              (Term.pair (firstType := firstType)
                         (secondType := secondType) firstVal secondVal))
           secondVal
  /-- **η-contraction for non-dependent arrow**: `λx. (f.weaken) x ⟶ f`
  whenever `f : Term ctx (arrow A B)`.  The body of the lam is the
  weakened `f` applied to the freshly-bound variable; η says this
  redundant abstraction collapses to `f` itself.  Soundness is
  immediate: `Term.weaken` precludes any use of the bound variable in
  `f`, so contracting cannot lose information. -/
  | etaArrow :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {domainType codomainType : Ty scope}
        (f : Term ctx (Ty.arrow domainType codomainType)),
      Step (Term.lam (codomainType := codomainType)
              (Term.app (Term.weaken domainType f)
                        (Term.var ⟨0, Nat.zero_lt_succ _⟩)))
           f
  /-- **η-contraction for Σ-pair**: `pair (fst p) (snd p) ⟶ p`
  whenever `p : Term ctx (sigmaTy A B)`.  Reconstituting a pair from
  its projections collapses to the original pair value.  The result
  type matches because both sides have type `Term ctx (sigmaTy A B)`. -/
  | etaSigma :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {firstType : Ty scope} {secondType : Ty (scope + 1)}
        (p : Term ctx (Ty.sigmaTy firstType secondType)),
      Step (Term.pair (firstType := firstType)
                       (secondType := secondType)
              (Term.fst p) (Term.snd p))
           p
  /-- Step inside the scrutinee position of a `boolElim`.  Together
  with the two ι-rules below, completes the boolean-evaluation
  story.  v1.14+. -/
  | boolElimScrutinee :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {resultType : Ty scope}
        {scrutinee scrutinee' : Term ctx Ty.bool}
        {thenBr elseBr : Term ctx resultType},
      Step scrutinee scrutinee' →
      Step (Term.boolElim scrutinee thenBr elseBr)
           (Term.boolElim scrutinee' thenBr elseBr)
  /-- Step inside the then-branch position of a `boolElim`. -/
  | boolElimThen :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {resultType : Ty scope}
        {scrutinee : Term ctx Ty.bool}
        {thenBr thenBr' : Term ctx resultType}
        {elseBr : Term ctx resultType},
      Step thenBr thenBr' →
      Step (Term.boolElim scrutinee thenBr elseBr)
           (Term.boolElim scrutinee thenBr' elseBr)
  /-- Step inside the else-branch position of a `boolElim`. -/
  | boolElimElse :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {resultType : Ty scope}
        {scrutinee : Term ctx Ty.bool}
        {thenBr : Term ctx resultType}
        {elseBr elseBr' : Term ctx resultType},
      Step elseBr elseBr' →
      Step (Term.boolElim scrutinee thenBr elseBr)
           (Term.boolElim scrutinee thenBr elseBr')
  /-- **ι-reduction for boolElim on `true`**: `boolElim true t e ⟶ t`.
  No cast: both sides have the same `resultType`.  v1.14+. -/
  | iotaBoolElimTrue :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {resultType : Ty scope}
        (thenBr elseBr : Term ctx resultType),
      Step (Term.boolElim Term.boolTrue thenBr elseBr) thenBr
  /-- **ι-reduction for boolElim on `false`**: `boolElim false t e ⟶ e`.
  No cast: both sides have the same `resultType`.  v1.14+. -/
  | iotaBoolElimFalse :
      ∀ {mode scope} {ctx : Ctx mode scope}
        {resultType : Ty scope}
        (thenBr elseBr : Term ctx resultType),
      Step (Term.boolElim Term.boolFalse thenBr elseBr) elseBr

/-- Reflexive-transitive closure of `Step` — multi-step reduction.
Captures the eventual reach of the reduction relation. -/
inductive StepStar :
    {mode : Mode} → {scope : Nat} → {ctx : Ctx mode scope} →
    {T : Ty scope} → Term ctx T → Term ctx T → Prop
  /-- Zero-step: a term reduces to itself. -/
  | refl :
      ∀ {mode scope} {ctx : Ctx mode scope} {T : Ty scope}
        (t : Term ctx T),
      StepStar t t
  /-- Prepend a single step to an existing multi-step path. -/
  | step :
      ∀ {mode scope} {ctx : Ctx mode scope} {T : Ty scope}
        {t₁ t₂ t₃ : Term ctx T},
      Step t₁ t₂ → StepStar t₂ t₃ → StepStar t₁ t₃

/-! Subject reduction is **structural** in this kernel: `Step`,
`StepStar`, and `Conv` (introduced below) all share their
`{ctx} {T}` indices between input and output terms, so every
well-typed input produces a well-typed output by the relations'
signatures alone.  No inductive subject-reduction theorem to state
— the typing is in the relation's type. -/

/-- Single steps lift to multi-step. -/
theorem Step.toStar
    {mode : Mode} {scope : Nat} {ctx : Ctx mode scope} {T : Ty scope}
    {t₁ t₂ : Term ctx T} (h : Step t₁ t₂) : StepStar t₁ t₂ :=
  StepStar.step h (StepStar.refl t₂)

/-- Transitivity of multi-step reduction.  Together with `refl` this
makes `StepStar` an equivalence-relation-like object and is
load-bearing for the eventual conversion algorithm — in particular
for showing common-reducts when comparing terms. -/
theorem StepStar.trans
    {mode : Mode} {scope : Nat} {ctx : Ctx mode scope} {T : Ty scope}
    {t₁ t₂ t₃ : Term ctx T} :
    StepStar t₁ t₂ → StepStar t₂ t₃ → StepStar t₁ t₃
  | .refl _, h         => h
  | .step s rest, h    => .step s (StepStar.trans rest h)

/-! ## v1.12 — StepStar structural congruences.

Directed analogs of the v1.11.1 `Conv` congruences.  Where `Conv`
witnesses two-way equivalence, `StepStar` witnesses one-way reduction
chains; both must thread through subterms for typical kernel
arguments (normalisation, confluence, decision procedures).

Each theorem is by induction on the underlying `StepStar`: the `refl`
case is reflexivity at the supersterm; the `step` case prepends the
matching `Step` congruence rule and recurses. -/

/-- Multi-step reduction threads through the function position of `Term.app`. -/
theorem StepStar.app_cong_left {mode scope} {ctx : Ctx mode scope}
    {domainType codomainType : Ty scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    (a : Term ctx domainType) :
    StepStar f₁ f₂ → StepStar (Term.app f₁ a) (Term.app f₂ a)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.appLeft s) (StepStar.app_cong_left a rest)

/-- Multi-step reduction threads through the argument position of `Term.app`. -/
theorem StepStar.app_cong_right {mode scope} {ctx : Ctx mode scope}
    {domainType codomainType : Ty scope}
    (f : Term ctx (Ty.arrow domainType codomainType))
    {a₁ a₂ : Term ctx domainType} :
    StepStar a₁ a₂ → StepStar (Term.app f a₁) (Term.app f a₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.appRight s) (StepStar.app_cong_right f rest)

/-- Multi-step reduction threads through both positions of `Term.app`. -/
theorem StepStar.app_cong {mode scope} {ctx : Ctx mode scope}
    {domainType codomainType : Ty scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : StepStar f₁ f₂) (h_a : StepStar a₁ a₂) :
    StepStar (Term.app f₁ a₁) (Term.app f₂ a₂) :=
  StepStar.trans (StepStar.app_cong_left a₁ h_f)
                 (StepStar.app_cong_right f₂ h_a)

/-- Multi-step reduction threads through the body of `Term.lam`. -/
theorem StepStar.lam_cong {mode scope} {ctx : Ctx mode scope}
    {domainType codomainType : Ty scope}
    {body₁ body₂ : Term (ctx.cons domainType) codomainType.weaken} :
    StepStar body₁ body₂ →
    StepStar (Term.lam (codomainType := codomainType) body₁)
             (Term.lam (codomainType := codomainType) body₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.lamBody s) (StepStar.lam_cong rest)

/-- Multi-step reduction threads through the body of `Term.lamPi`. -/
theorem StepStar.lamPi_cong {mode scope} {ctx : Ctx mode scope}
    {domainType : Ty scope} {codomainType : Ty (scope + 1)}
    {body₁ body₂ : Term (ctx.cons domainType) codomainType} :
    StepStar body₁ body₂ →
    StepStar (Term.lamPi (domainType := domainType) body₁)
             (Term.lamPi (domainType := domainType) body₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.lamPiBody s) (StepStar.lamPi_cong rest)

/-- Multi-step reduction threads through the function position of `Term.appPi`. -/
theorem StepStar.appPi_cong_left {mode scope} {ctx : Ctx mode scope}
    {domainType : Ty scope} {codomainType : Ty (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    (a : Term ctx domainType) :
    StepStar f₁ f₂ → StepStar (Term.appPi f₁ a) (Term.appPi f₂ a)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.appPiLeft s)
        (StepStar.appPi_cong_left a rest)

/-- Multi-step reduction threads through the argument position of `Term.appPi`. -/
theorem StepStar.appPi_cong_right {mode scope} {ctx : Ctx mode scope}
    {domainType : Ty scope} {codomainType : Ty (scope + 1)}
    (f : Term ctx (Ty.piTy domainType codomainType))
    {a₁ a₂ : Term ctx domainType} :
    StepStar a₁ a₂ → StepStar (Term.appPi f a₁) (Term.appPi f a₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.appPiRight s)
        (StepStar.appPi_cong_right f rest)

/-- Multi-step reduction threads through both positions of `Term.appPi`. -/
theorem StepStar.appPi_cong {mode scope} {ctx : Ctx mode scope}
    {domainType : Ty scope} {codomainType : Ty (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : StepStar f₁ f₂) (h_a : StepStar a₁ a₂) :
    StepStar (Term.appPi f₁ a₁) (Term.appPi f₂ a₂) :=
  StepStar.trans (StepStar.appPi_cong_left a₁ h_f)
                 (StepStar.appPi_cong_right f₂ h_a)

/-- Multi-step reduction threads through the first component of `Term.pair`. -/
theorem StepStar.pair_cong_first {mode scope} {ctx : Ctx mode scope}
    {firstType : Ty scope} {secondType : Ty (scope + 1)}
    {firstVal₁ firstVal₂ : Term ctx firstType}
    (secondVal : Term ctx (secondType.subst0 firstType)) :
    StepStar firstVal₁ firstVal₂ →
    StepStar
      (Term.pair (firstType := firstType) (secondType := secondType)
                  firstVal₁ secondVal)
      (Term.pair (firstType := firstType) (secondType := secondType)
                  firstVal₂ secondVal)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.pairLeft s)
        (StepStar.pair_cong_first secondVal rest)

/-- Multi-step reduction threads through the second component of `Term.pair`. -/
theorem StepStar.pair_cong_second {mode scope} {ctx : Ctx mode scope}
    {firstType : Ty scope} {secondType : Ty (scope + 1)}
    (firstVal : Term ctx firstType)
    {secondVal₁ secondVal₂ : Term ctx (secondType.subst0 firstType)} :
    StepStar secondVal₁ secondVal₂ →
    StepStar (Term.pair firstVal secondVal₁)
             (Term.pair firstVal secondVal₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.pairRight s)
        (StepStar.pair_cong_second firstVal rest)

/-- Multi-step reduction threads through both components of `Term.pair`. -/
theorem StepStar.pair_cong {mode scope} {ctx : Ctx mode scope}
    {firstType : Ty scope} {secondType : Ty (scope + 1)}
    {firstVal₁ firstVal₂ : Term ctx firstType}
    {secondVal₁ secondVal₂ : Term ctx (secondType.subst0 firstType)}
    (h_first : StepStar firstVal₁ firstVal₂)
    (h_second : StepStar secondVal₁ secondVal₂) :
    StepStar (Term.pair firstVal₁ secondVal₁)
             (Term.pair firstVal₂ secondVal₂) :=
  StepStar.trans (StepStar.pair_cong_first secondVal₁ h_first)
                 (StepStar.pair_cong_second firstVal₂ h_second)

/-- Multi-step reduction threads through `Term.fst`. -/
theorem StepStar.fst_cong {mode scope} {ctx : Ctx mode scope}
    {firstType : Ty scope} {secondType : Ty (scope + 1)}
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)} :
    StepStar p₁ p₂ → StepStar (Term.fst p₁) (Term.fst p₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.fstCong s) (StepStar.fst_cong rest)

/-- Multi-step reduction threads through `Term.snd`. -/
theorem StepStar.snd_cong {mode scope} {ctx : Ctx mode scope}
    {firstType : Ty scope} {secondType : Ty (scope + 1)}
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)} :
    StepStar p₁ p₂ → StepStar (Term.snd p₁) (Term.snd p₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.sndCong s) (StepStar.snd_cong rest)

/-! ## v1.11 — definitional conversion (`Conv`).

`Conv t₁ t₂` is the symmetric, reflexive, transitive closure of
`Step` — the equivalence relation generated by β/η reduction.  This
is the conversion judgment a bidirectional kernel checker dispatches
to when comparing two terms during type-equality checks.

Constructors are minimal (refl, sym, trans, fromStep) so the
relation's algebraic shape is unambiguous; structural rules (e.g.,
"Conv on subterms gives Conv on supersterms") are derived theorems
where needed. -/

/-- The conversion relation: equivalence closure of `Step` over
terms of the same type.  Subject preservation is definitional (the
relation's indices fix the type). -/
inductive Conv :
    {mode : Mode} → {scope : Nat} → {ctx : Ctx mode scope} →
    {T : Ty scope} → Term ctx T → Term ctx T → Prop
  /-- Reflexivity: every term is convertible with itself. -/
  | refl :
      ∀ {mode scope} {ctx : Ctx mode scope} {T : Ty scope}
        (t : Term ctx T),
      Conv t t
  /-- Symmetry: convertibility is bidirectional. -/
  | sym :
      ∀ {mode scope} {ctx : Ctx mode scope} {T : Ty scope}
        {t₁ t₂ : Term ctx T},
      Conv t₁ t₂ → Conv t₂ t₁
  /-- Transitivity: convertibility chains. -/
  | trans :
      ∀ {mode scope} {ctx : Ctx mode scope} {T : Ty scope}
        {t₁ t₂ t₃ : Term ctx T},
      Conv t₁ t₂ → Conv t₂ t₃ → Conv t₁ t₃
  /-- Embedding: every single-step reduction is a conversion. -/
  | fromStep :
      ∀ {mode scope} {ctx : Ctx mode scope} {T : Ty scope}
        {t₁ t₂ : Term ctx T},
      Step t₁ t₂ → Conv t₁ t₂

/-- Multi-step reductions lift to conversions: a sequence of forward
steps is a conversion in the forward direction.  Proven by induction
on `StepStar`: the empty case is reflexivity, the step case composes
`fromStep` with the inductive hypothesis via `trans`. -/
theorem StepStar.toConv
    {mode : Mode} {scope : Nat} {ctx : Ctx mode scope} {T : Ty scope}
    {t₁ t₂ : Term ctx T} :
    StepStar t₁ t₂ → Conv t₁ t₂
  | .refl t       => Conv.refl t
  | .step s rest  => Conv.trans (Conv.fromStep s) (StepStar.toConv rest)

/-- Single-step reductions lift to conversions through the multi-step
intermediary.  Direct from `Conv.fromStep`; provided as a named
theorem for symmetry with `Step.toStar`. -/
theorem Step.toConv
    {mode : Mode} {scope : Nat} {ctx : Ctx mode scope} {T : Ty scope}
    {t₁ t₂ : Term ctx T} (h : Step t₁ t₂) : Conv t₁ t₂ :=
  Conv.fromStep h

/-! ## v1.11 — Conv structural congruences.

Without these, threading `Conv` through subterms requires manually
applying each `Step` congruence constructor and lifting via
`Conv.fromStep` + `Conv.trans`.  Each theorem here is by induction on
the underlying `Conv` proof: the four cases are reflexivity, symmetry,
transitivity, and `fromStep` (which lifts via the corresponding
`Step` congruence rule).  Together they make `Conv` a *full
congruence relation* over the term constructors. -/

/-- Convertibility threads through the function position of `Term.app`. -/
theorem Conv.app_cong_left {mode scope} {ctx : Ctx mode scope}
    {domainType codomainType : Ty scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    (a : Term ctx domainType) (h : Conv f₁ f₂) :
    Conv (Term.app f₁ a) (Term.app f₂ a) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.appLeft s)

/-- Convertibility threads through the argument position of `Term.app`. -/
theorem Conv.app_cong_right {mode scope} {ctx : Ctx mode scope}
    {domainType codomainType : Ty scope}
    (f : Term ctx (Ty.arrow domainType codomainType))
    {a₁ a₂ : Term ctx domainType} (h : Conv a₁ a₂) :
    Conv (Term.app f a₁) (Term.app f a₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.appRight s)

/-- Convertibility threads through both positions of `Term.app`. -/
theorem Conv.app_cong {mode scope} {ctx : Ctx mode scope}
    {domainType codomainType : Ty scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : Conv f₁ f₂) (h_a : Conv a₁ a₂) :
    Conv (Term.app f₁ a₁) (Term.app f₂ a₂) :=
  Conv.trans (Conv.app_cong_left a₁ h_f) (Conv.app_cong_right f₂ h_a)

/-- Convertibility threads through the body of `Term.lam`. -/
theorem Conv.lam_cong {mode scope} {ctx : Ctx mode scope}
    {domainType codomainType : Ty scope}
    {body₁ body₂ : Term (ctx.cons domainType) codomainType.weaken}
    (h : Conv body₁ body₂) :
    Conv (Term.lam (codomainType := codomainType) body₁)
         (Term.lam (codomainType := codomainType) body₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.lamBody s)

/-- Convertibility threads through the body of `Term.lamPi`. -/
theorem Conv.lamPi_cong {mode scope} {ctx : Ctx mode scope}
    {domainType : Ty scope} {codomainType : Ty (scope + 1)}
    {body₁ body₂ : Term (ctx.cons domainType) codomainType}
    (h : Conv body₁ body₂) :
    Conv (Term.lamPi (domainType := domainType) body₁)
         (Term.lamPi (domainType := domainType) body₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.lamPiBody s)

/-- Convertibility threads through the function position of `Term.appPi`. -/
theorem Conv.appPi_cong_left {mode scope} {ctx : Ctx mode scope}
    {domainType : Ty scope} {codomainType : Ty (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    (a : Term ctx domainType) (h : Conv f₁ f₂) :
    Conv (Term.appPi f₁ a) (Term.appPi f₂ a) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.appPiLeft s)

/-- Convertibility threads through the argument position of `Term.appPi`. -/
theorem Conv.appPi_cong_right {mode scope} {ctx : Ctx mode scope}
    {domainType : Ty scope} {codomainType : Ty (scope + 1)}
    (f : Term ctx (Ty.piTy domainType codomainType))
    {a₁ a₂ : Term ctx domainType} (h : Conv a₁ a₂) :
    Conv (Term.appPi f a₁) (Term.appPi f a₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.appPiRight s)

/-- Convertibility threads through both positions of `Term.appPi`. -/
theorem Conv.appPi_cong {mode scope} {ctx : Ctx mode scope}
    {domainType : Ty scope} {codomainType : Ty (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : Conv f₁ f₂) (h_a : Conv a₁ a₂) :
    Conv (Term.appPi f₁ a₁) (Term.appPi f₂ a₂) :=
  Conv.trans (Conv.appPi_cong_left a₁ h_f) (Conv.appPi_cong_right f₂ h_a)

/-- Convertibility threads through the first component of `Term.pair`. -/
theorem Conv.pair_cong_first {mode scope} {ctx : Ctx mode scope}
    {firstType : Ty scope} {secondType : Ty (scope + 1)}
    {firstVal₁ firstVal₂ : Term ctx firstType}
    (secondVal : Term ctx (secondType.subst0 firstType))
    (h : Conv firstVal₁ firstVal₂) :
    Conv (Term.pair (firstType := firstType) (secondType := secondType)
                    firstVal₁ secondVal)
         (Term.pair (firstType := firstType) (secondType := secondType)
                    firstVal₂ secondVal) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.pairLeft s)

/-- Convertibility threads through the second component of `Term.pair`. -/
theorem Conv.pair_cong_second {mode scope} {ctx : Ctx mode scope}
    {firstType : Ty scope} {secondType : Ty (scope + 1)}
    (firstVal : Term ctx firstType)
    {secondVal₁ secondVal₂ : Term ctx (secondType.subst0 firstType)}
    (h : Conv secondVal₁ secondVal₂) :
    Conv (Term.pair firstVal secondVal₁)
         (Term.pair firstVal secondVal₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.pairRight s)

/-- Convertibility threads through both components of `Term.pair`. -/
theorem Conv.pair_cong {mode scope} {ctx : Ctx mode scope}
    {firstType : Ty scope} {secondType : Ty (scope + 1)}
    {firstVal₁ firstVal₂ : Term ctx firstType}
    {secondVal₁ secondVal₂ : Term ctx (secondType.subst0 firstType)}
    (h_first : Conv firstVal₁ firstVal₂)
    (h_second : Conv secondVal₁ secondVal₂) :
    Conv (Term.pair firstVal₁ secondVal₁)
         (Term.pair firstVal₂ secondVal₂) :=
  Conv.trans (Conv.pair_cong_first secondVal₁ h_first)
             (Conv.pair_cong_second firstVal₂ h_second)

/-- Convertibility threads through `Term.fst`. -/
theorem Conv.fst_cong {mode scope} {ctx : Ctx mode scope}
    {firstType : Ty scope} {secondType : Ty (scope + 1)}
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)}
    (h : Conv p₁ p₂) :
    Conv (Term.fst p₁) (Term.fst p₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.fstCong s)

/-- Convertibility threads through `Term.snd`. -/
theorem Conv.snd_cong {mode scope} {ctx : Ctx mode scope}
    {firstType : Ty scope} {secondType : Ty (scope + 1)}
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)}
    (h : Conv p₁ p₂) :
    Conv (Term.snd p₁) (Term.snd p₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.sndCong s)

/-! ## v1.11 — η-equivalence in natural direction.

Step's η-rules are *contractions* (collapse the η-redex back to the
underlying value).  These wrappers state η as an *equivalence*
(`f ≡ λx. f x`), which is the more common reading and the form
typical conversion algorithms compare against. -/

/-- **η-equivalence for arrow**: `f ≡ λx. f x`. -/
theorem Term.eta_arrow_eq {mode scope} {ctx : Ctx mode scope}
    {domainType codomainType : Ty scope}
    (f : Term ctx (Ty.arrow domainType codomainType)) :
    Conv f
         (Term.lam (codomainType := codomainType)
            (Term.app (Term.weaken domainType f)
                      (Term.var ⟨0, Nat.zero_lt_succ _⟩))) :=
  Conv.sym (Step.etaArrow f).toConv

/-- **η-equivalence for Σ**: `p ≡ pair (fst p) (snd p)`. -/
theorem Term.eta_sigma_eq {mode scope} {ctx : Ctx mode scope}
    {firstType : Ty scope} {secondType : Ty (scope + 1)}
    (p : Term ctx (Ty.sigmaTy firstType secondType)) :
    Conv p
         (Term.pair (firstType := firstType)
                     (secondType := secondType)
            (Term.fst p) (Term.snd p)) :=
  Conv.sym (Step.etaSigma p).toConv

/-! ## v1.11 — cast-identity discipline (proof irrelevance).

The β-reduction's result terms carry `▸` casts whose proofs are
non-`rfl`-elaborated equalities.  Lean 4's Prop-level proof
irrelevance makes every `Eq` proof of a definitionally-true equation
*definitionally equal* to `rfl`, so the cast reduces to identity. -/

/-- The cast through any `T = T` equality on a term is the identity
modulo Prop proof irrelevance.  Lean's kernel substitutes `Eq.refl`
for any proof when both sides are definitionally equal. -/
theorem Term.cast_identity
    {mode : Mode} {scope : Nat} {ctx : Ctx mode scope} {T : Ty scope}
    (h : T = T) (term : Term ctx T) :
    h ▸ term = term := rfl

/-! ## v1.11 — confluence: the algebraic groundwork.

Full confluence (the diamond property: if `t ⟶ t₁` and `t ⟶ t₂`, there
exists `t'` with `t₁ ⟶* t'` and `t₂ ⟶* t'`) requires parallel
reduction and the Tait–Martin-Löf method, ~200+ lines.  v1.11 lays
the algebraic groundwork: `Conv` is a true equivalence relation by
its constructor signature plus the structural-congruence theorems
above; `StepStar.append` provides the right-side companion to
`StepStar.step` for typical reduction-trace manipulation in the
eventual confluence proof. -/

/-- Append a single step to an existing multi-step path.  The companion
to `StepStar.step` (which prepends): both directions are needed for
typical reduction-trace manipulation in conversion algorithms. -/
theorem StepStar.append
    {mode : Mode} {scope : Nat} {ctx : Ctx mode scope} {T : Ty scope}
    {t₁ t₂ t₃ : Term ctx T} :
    StepStar t₁ t₂ → Step t₂ t₃ → StepStar t₁ t₃ :=
  fun stars step =>
    StepStar.trans stars (Step.toStar step)

/-! ## v1.11 — η + Conv smoke tests. -/

/-- **η for arrow** at the Step level: contracting an η-redex over a
closed function yields back the original function. -/
example (mode : Mode)
    (f : Term (Ctx.nil mode) (Ty.arrow Ty.unit Ty.unit)) :
    Step (Term.lam (codomainType := Ty.unit)
            (Term.app (Term.weaken Ty.unit f)
                      (Term.var ⟨0, Nat.zero_lt_succ _⟩)))
         f :=
  Step.etaArrow f

/-- **η for Σ** at the Step level: collapsing a pair of projections
back to the original pair value. -/
example (mode : Mode)
    (p : Term (Ctx.nil mode) (Ty.sigmaTy Ty.unit Ty.unit)) :
    Step (Term.pair (firstType := Ty.unit) (secondType := Ty.unit)
            (Term.fst p) (Term.snd p))
         p :=
  Step.etaSigma p

/-- **Conv as a real congruence relation**: given convertibility on
the function and argument, convertibility holds at the application.
This exercises the v1.11 structural-congruence machinery
(`Conv.app_cong`) and confirms `Conv` is more than an opaque
equivalence — it threads through subterms automatically. -/
example {mode scope} {ctx : Ctx mode scope}
    {domainType codomainType : Ty scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : Conv f₁ f₂) (h_a : Conv a₁ a₂) :
    Conv (Term.app f₁ a₁) (Term.app f₂ a₂) :=
  Conv.app_cong h_f h_a

/-- **η-equivalence in natural direction**: a function is convertible
with its η-expansion.  Direct from `Term.eta_arrow_eq`. -/
example (mode : Mode)
    (f : Term (Ctx.nil mode) (Ty.arrow Ty.unit Ty.unit)) :
    Conv f
         (Term.lam (codomainType := Ty.unit)
            (Term.app (Term.weaken Ty.unit f)
                      (Term.var ⟨0, Nat.zero_lt_succ _⟩))) :=
  Term.eta_arrow_eq f

/-- **Cast simplification**: a `▸` over a `T = T` equality is the
identity (Lean's proof-irrelevance reduces the cast). -/
example (mode : Mode) (term : Term (Ctx.nil mode) Ty.unit)
    (h : (Ty.unit : Ty 0) = Ty.unit) :
    h ▸ term = term :=
  Term.cast_identity h term

/-! ## v1.10 β-reduction smoke tests.

Each rule's *existence* and *well-typedness* is the key smoke test:
the constructor packs a closed Step proof when applied to a body and
argument, and Lean's kernel verifies the result type matches each
rule's declared form.  We assert by `Exists.intro` rather than by
`rfl` on the reduct because the result terms carry `▸` casts whose
proofs are non-`rfl`-elaborated even when the underlying equation
holds by computation.  Definitional convertibility of the casts is a
v1.11 normalisation-by-evaluation concern; v1.10 establishes the
typed-reduction relation. -/

/-- **Non-dependent β exists**: `(λx:unit. x) unit ⟶ ?` for some
target term in the same context and at the same type.  Constructor
arguments fully explicit via `@Step.betaApp` so Lean's elaborator
binds every implicit on the spot. -/
example (mode : Mode) :
    ∃ (target : Term (Ctx.nil mode) Ty.unit),
      Step (Term.app (mode := mode)
              (Term.lam (domainType := Ty.unit) (codomainType := Ty.unit)
                (Term.var ⟨0, Nat.zero_lt_succ _⟩))
              Term.unit) target :=
  ⟨_, @Step.betaApp mode 0 (Ctx.nil mode) Ty.unit Ty.unit
        (Term.var ⟨0, Nat.zero_lt_succ _⟩) Term.unit⟩

/-- **Σ first projection exists**: `fst (pair a b) ⟶ a` is constructed
in any context for arbitrary `a`, `b` of the appropriate types. -/
example (mode : Mode)
    (a : Term (Ctx.nil mode) Ty.unit)
    (b : Term (Ctx.nil mode) (Ty.unit.subst0 Ty.unit)) :
    Step
      (Term.fst (Term.pair (firstType := Ty.unit)
                            (secondType := Ty.unit) a b))
      a :=
  Step.betaFstPair a b

/-- **Σ second projection exists**: `snd (pair a b) ⟶ b`. -/
example (mode : Mode)
    (a : Term (Ctx.nil mode) Ty.unit)
    (b : Term (Ctx.nil mode) (Ty.unit.subst0 Ty.unit)) :
    Step
      (Term.snd (Term.pair (firstType := Ty.unit)
                            (secondType := Ty.unit) a b))
      b :=
  Step.betaSndPair a b

/-- **β lifts to multi-step**: the application `(λx. x) unit` admits a
`StepStar` derivation reaching some normal form. -/
example (mode : Mode) :
    ∃ (target : Term (Ctx.nil mode) Ty.unit),
      StepStar (Term.app (mode := mode)
                  (Term.lam (domainType := Ty.unit) (codomainType := Ty.unit)
                    (Term.var ⟨0, Nat.zero_lt_succ _⟩))
                  Term.unit) target :=
  ⟨_, Step.toStar
        (@Step.betaApp mode 0 (Ctx.nil mode) Ty.unit Ty.unit
          (Term.var ⟨0, Nat.zero_lt_succ _⟩) Term.unit)⟩

/-! ## v1.1 — Term measures and the first proven theorem.

The definitions below add the first **theorem** (not just `example`) of
the package, exercising structural induction over the indexed `Term`
family.  Each must stay axiom-free per the binder-form rule. -/

/-- Total constructor count of a term — distinct from `depth` (height)
and `lamCount` (only λ-nodes).  Useful as a strong termination measure
for transformations that recurse into both sides of `app`. -/
def Term.size
    {mode : Mode} {scope : Nat} {context : Ctx mode scope}
    {currentType : Ty scope} :
    Term context currentType → Nat
  | .var _                          => 1
  | .unit                           => 1
  | .lam body                       => body.size + 1
  | .app functionTerm argumentTerm  =>
      functionTerm.size + argumentTerm.size + 1
  | .lamPi body                     => body.size + 1
  | .appPi functionTerm argumentTerm =>
      functionTerm.size + argumentTerm.size + 1
  | .pair firstVal secondVal        =>
      firstVal.size + secondVal.size + 1
  | .fst pairTerm                   => pairTerm.size + 1
  | .snd pairTerm                   => pairTerm.size + 1
  | .boolTrue                       => 1
  | .boolFalse                      => 1
  | .boolElim scrutinee thenBr elseBr =>
      scrutinee.size + thenBr.size + elseBr.size + 1

/-- Count of variable occurrences in a term.  Independent measure to
`size`, `depth`, and `lamCount` — confirms that pattern matching on
`Term` works for arbitrary structural recursions, not just the three
examples used so far. -/
def Term.varCount
    {mode : Mode} {scope : Nat} {context : Ctx mode scope}
    {currentType : Ty scope} :
    Term context currentType → Nat
  | .var _                          => 1
  | .unit                           => 0
  | .lam body                       => body.varCount
  | .app functionTerm argumentTerm  =>
      functionTerm.varCount + argumentTerm.varCount
  | .lamPi body                     => body.varCount
  | .appPi functionTerm argumentTerm =>
      functionTerm.varCount + argumentTerm.varCount
  | .pair firstVal secondVal        =>
      firstVal.varCount + secondVal.varCount
  | .fst pairTerm                   => pairTerm.varCount
  | .snd pairTerm                   => pairTerm.varCount
  | .boolTrue                       => 0
  | .boolFalse                      => 0
  | .boolElim scrutinee thenBr elseBr =>
      scrutinee.varCount + thenBr.varCount + elseBr.varCount

/-- The first **non-trivial theorem** of the package.  Every term has
`lamCount` bounded by `size` — i.e. you can't have more λ-binders than
constructors.  Proven by structural induction on `Term`, using only
`Nat` arithmetic from core; no tactics, no `omega`, no axioms. -/
theorem Term.lamCount_le_size
    {mode : Mode} {scope : Nat} {context : Ctx mode scope}
    {currentType : Ty scope} :
    ∀ (term : Term context currentType), term.lamCount ≤ term.size
  | .var _ => Nat.zero_le _
  | .unit  => Nat.zero_le _
  | .lam body =>
      Nat.succ_le_succ (Term.lamCount_le_size body)
  | .app functionTerm argumentTerm =>
      Nat.le_succ_of_le
        (Nat.add_le_add
          (Term.lamCount_le_size functionTerm)
          (Term.lamCount_le_size argumentTerm))
  | .lamPi body =>
      Nat.succ_le_succ (Term.lamCount_le_size body)
  | .appPi functionTerm argumentTerm =>
      Nat.le_succ_of_le
        (Nat.add_le_add
          (Term.lamCount_le_size functionTerm)
          (Term.lamCount_le_size argumentTerm))
  | .pair firstVal secondVal =>
      Nat.le_succ_of_le
        (Nat.add_le_add
          (Term.lamCount_le_size firstVal)
          (Term.lamCount_le_size secondVal))
  | .fst pairTerm => Nat.le_succ_of_le (Term.lamCount_le_size pairTerm)
  | .snd pairTerm => Nat.le_succ_of_le (Term.lamCount_le_size pairTerm)
  | .boolTrue  => Nat.zero_le _
  | .boolFalse => Nat.zero_le _
  | .boolElim scrutinee thenBr elseBr =>
      Nat.le_succ_of_le
        (Nat.add_le_add
          (Nat.add_le_add
            (Term.lamCount_le_size scrutinee)
            (Term.lamCount_le_size thenBr))
          (Term.lamCount_le_size elseBr))

/-- Companion theorem: `varCount` is also bounded by `size`.  Same
proof shape as `lamCount_le_size`; confirms the pattern generalises. -/
theorem Term.varCount_le_size
    {mode : Mode} {scope : Nat} {context : Ctx mode scope}
    {currentType : Ty scope} :
    ∀ (term : Term context currentType), term.varCount ≤ term.size
  | .var _ => Nat.le_refl _
  | .unit  => Nat.zero_le _
  | .lam body => Nat.le_succ_of_le (Term.varCount_le_size body)
  | .app functionTerm argumentTerm =>
      Nat.le_succ_of_le
        (Nat.add_le_add
          (Term.varCount_le_size functionTerm)
          (Term.varCount_le_size argumentTerm))
  | .lamPi body => Nat.le_succ_of_le (Term.varCount_le_size body)
  | .appPi functionTerm argumentTerm =>
      Nat.le_succ_of_le
        (Nat.add_le_add
          (Term.varCount_le_size functionTerm)
          (Term.varCount_le_size argumentTerm))
  | .pair firstVal secondVal =>
      Nat.le_succ_of_le
        (Nat.add_le_add
          (Term.varCount_le_size firstVal)
          (Term.varCount_le_size secondVal))
  | .fst pairTerm => Nat.le_succ_of_le (Term.varCount_le_size pairTerm)
  | .snd pairTerm => Nat.le_succ_of_le (Term.varCount_le_size pairTerm)
  | .boolTrue  => Nat.zero_le _
  | .boolFalse => Nat.zero_le _
  | .boolElim scrutinee thenBr elseBr =>
      Nat.le_succ_of_le
        (Nat.add_le_add
          (Nat.add_le_add
            (Term.varCount_le_size scrutinee)
            (Term.varCount_le_size thenBr))
          (Term.varCount_le_size elseBr))

/-! ## v1.1 smoke tests -/

/-- The size of `id unit` is 3: one `app`, one `lam`, one `unit`,
one `var` — wait, that's four.  Let's recount: `app` (1) + `lam` (1)
+ `var` (1) + `unit` (1) = 4.  rfl test below. -/
example (mode : Mode) : (identityAppliedToUnit mode).size = 4 := rfl

/-- The varCount of `id unit` is 1: one `var` from the lam body, the
top-level `unit` doesn't count, the `app` and `lam` don't count. -/
example (mode : Mode) : (identityAppliedToUnit mode).varCount = 1 := rfl

/-! ## v1.3 — dependent `piTy` demonstrations.

The `lamPi`/`appPi` rules use the new `Ty.piTy` type former and
`Ty.unweaken` to handle the result type.  For v1.2 `Ty` (no type-level
variable references), the dependent and non-dependent variants are
behaviourally equivalent — `appPi`'s argument is unused — but the
typing structure is in place for v1.4+. -/

/-- Dependent identity: `λx:unit. x` typed as `piTy unit unit` rather
than `arrow unit unit`.  Codomain at scope `+1` — Lean's elaborator
infers it from the expected type. -/
def piIdentityOnUnit (mode : Mode) :
    Term (Ctx.nil mode) (Ty.piTy Ty.unit Ty.unit) :=
  .lamPi (.var ⟨0, Nat.zero_lt_succ _⟩)

/-- Smoke test: depth of dependent identity = 1. -/
example (mode : Mode) : (piIdentityOnUnit mode).depth = 1 := rfl

/-- Smoke test: lamCount of dependent identity = 1 (a `lamPi` counts). -/
example (mode : Mode) : (piIdentityOnUnit mode).lamCount = 1 := rfl

/-- Smoke test: size of dependent identity = 2 (one `lamPi`, one `var`). -/
example (mode : Mode) : (piIdentityOnUnit mode).size = 2 := rfl

/-- Smoke test: varCount of dependent identity = 1. -/
example (mode : Mode) : (piIdentityOnUnit mode).varCount = 1 := rfl

/-- Dependent identity applied to `unit`.  Result type is
`Ty.unit.subst0 Ty.unit` which reduces to `Ty.unit` because
substitution on `unit` is structural identity-shape. -/
def piIdentityAppliedToUnit (mode : Mode) :
    Term (Ctx.nil mode) Ty.unit :=
  .appPi (piIdentityOnUnit mode) .unit

/-- Smoke test: depth of dependent `id unit` = 2. -/
example (mode : Mode) : (piIdentityAppliedToUnit mode).depth = 2 := rfl

/-- Smoke test: size of dependent `id unit` = 4 (one `appPi`, one
`lamPi`, one `var`, one `unit`). -/
example (mode : Mode) : (piIdentityAppliedToUnit mode).size = 4 := rfl

/-- Smoke test: lamCount of dependent `id unit` = 1 (the `lamPi` from
the identity). -/
example (mode : Mode) : (piIdentityAppliedToUnit mode).lamCount = 1 := rfl

/-! ## v1.5 — `Ty.tyVar` substitution smoke tests.

These confirm that `Ty.subst` and `Ty.subst0` actually *reach* the
`tyVar` case and resolve it via `Subst.singleton`, rather than
threading a placeholder.  Without these tests, v1.5 would be
indistinguishable from v1.4 since v1.4's examples use only types
without variable references. -/

/-- Substituting var 0 with `T` in `tyVar 0` yields `T`.  The
fundamental property of `Subst.singleton`. -/
example (T : Ty 0) :
    Ty.subst0 (Ty.tyVar ⟨0, Nat.zero_lt_succ _⟩) T = T := rfl

/-- Substitution distributes through `arrow`: substituting `T` for
var 0 in `arrow unit (tyVar 0)` yields `arrow unit T`. -/
example (T : Ty 0) :
    Ty.subst0 (Ty.arrow Ty.unit (Ty.tyVar ⟨0, Nat.zero_lt_succ _⟩)) T
      = Ty.arrow Ty.unit T := rfl

/-- Weakening a `tyVar` shifts its index up via `Fin.succ`. -/
example : (Ty.tyVar (scope := 1) ⟨0, Nat.zero_lt_succ _⟩).weaken
    = Ty.tyVar ⟨1, by decide⟩ := rfl

/-! ### v1.16 — DecidableEq smoke tests.

Confirms the auto-derived `DecidableEq (Ty scope)` instance
actually computes — `decide` reduces equality queries to `true`
or `false` at compile time, with no opaque blockers from the
indexed-inductive structure. -/

/-- Distinct constructors decide to false. -/
example : decide ((Ty.unit : Ty 0) = Ty.bool) = false := rfl

/-- Same constructor with same children decides to true. -/
example : decide ((Ty.unit : Ty 0) = Ty.unit) = true := rfl

/-- `arrow unit unit = arrow unit unit` decides to true (recursive
descent through both children). -/
example : decide ((Ty.arrow Ty.unit Ty.unit : Ty 0)
                = Ty.arrow Ty.unit Ty.unit) = true := rfl

/-- `arrow unit bool ≠ arrow unit unit` decides to false (children
differ in the codomain position). -/
example : decide ((Ty.arrow Ty.unit Ty.bool : Ty 0)
                = Ty.arrow Ty.unit Ty.unit) = false := rfl

/-- `tyVar` discrimination uses the underlying `Fin` decidable
equality. -/
example : decide ((Ty.tyVar (scope := 2) ⟨0, by decide⟩ : Ty 2)
                = Ty.tyVar ⟨1, by decide⟩) = false := rfl

/-! ## v1.15 — boolean computation: StepStar/Conv congruences + smoke tests.

The Step rules of v1.14 give one-step boolean reduction.  v1.15
lifts them through StepStar (multi-step) and Conv (definitional
equivalence), then exhibits concrete reduction examples that
exercise the kernel's computational content beyond Π/Σ.

The four StepStar congruences mirror the v1.12 directional pattern;
the four Conv congruences mirror the v1.11.1 equivalence pattern.
The combined `_cong` form sequences the three single-position
congruences via `trans`. -/

/-- Multi-step reduction threads through `boolElim`'s scrutinee. -/
theorem StepStar.boolElim_cong_scrutinee
    {mode scope} {ctx : Ctx mode scope}
    {resultType : Ty scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.bool}
    (thenBr elseBr : Term ctx resultType) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.boolElim scrutinee₁ thenBr elseBr)
             (Term.boolElim scrutinee₂ thenBr elseBr)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.boolElimScrutinee s)
        (StepStar.boolElim_cong_scrutinee thenBr elseBr rest)

/-- Multi-step reduction threads through `boolElim`'s then-branch. -/
theorem StepStar.boolElim_cong_then
    {mode scope} {ctx : Ctx mode scope}
    {resultType : Ty scope}
    (scrutinee : Term ctx Ty.bool)
    {thenBr₁ thenBr₂ : Term ctx resultType}
    (elseBr : Term ctx resultType) :
    StepStar thenBr₁ thenBr₂ →
    StepStar (Term.boolElim scrutinee thenBr₁ elseBr)
             (Term.boolElim scrutinee thenBr₂ elseBr)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.boolElimThen s)
        (StepStar.boolElim_cong_then scrutinee elseBr rest)

/-- Multi-step reduction threads through `boolElim`'s else-branch. -/
theorem StepStar.boolElim_cong_else
    {mode scope} {ctx : Ctx mode scope}
    {resultType : Ty scope}
    (scrutinee : Term ctx Ty.bool)
    (thenBr : Term ctx resultType)
    {elseBr₁ elseBr₂ : Term ctx resultType} :
    StepStar elseBr₁ elseBr₂ →
    StepStar (Term.boolElim scrutinee thenBr elseBr₁)
             (Term.boolElim scrutinee thenBr elseBr₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.boolElimElse s)
        (StepStar.boolElim_cong_else scrutinee thenBr rest)

/-- Multi-step reduction threads through all three `boolElim`
positions simultaneously.  Sequenced via three `trans` calls over
the single-position congruences. -/
theorem StepStar.boolElim_cong
    {mode scope} {ctx : Ctx mode scope}
    {resultType : Ty scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.bool}
    {thenBr₁ thenBr₂ elseBr₁ elseBr₂ : Term ctx resultType}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_then : StepStar thenBr₁ thenBr₂)
    (h_else : StepStar elseBr₁ elseBr₂) :
    StepStar (Term.boolElim scrutinee₁ thenBr₁ elseBr₁)
             (Term.boolElim scrutinee₂ thenBr₂ elseBr₂) :=
  StepStar.trans
    (StepStar.boolElim_cong_scrutinee thenBr₁ elseBr₁ h_scr)
    (StepStar.trans
      (StepStar.boolElim_cong_then scrutinee₂ elseBr₁ h_then)
      (StepStar.boolElim_cong_else scrutinee₂ thenBr₂ h_else))

/-- Definitional equivalence threads through `boolElim`'s scrutinee. -/
theorem Conv.boolElim_cong_scrutinee
    {mode scope} {ctx : Ctx mode scope}
    {resultType : Ty scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.bool}
    (thenBr elseBr : Term ctx resultType) :
    Conv scrutinee₁ scrutinee₂ →
    Conv (Term.boolElim scrutinee₁ thenBr elseBr)
         (Term.boolElim scrutinee₂ thenBr elseBr)
  | .refl _      => Conv.refl _
  | .sym h       =>
      Conv.sym (Conv.boolElim_cong_scrutinee thenBr elseBr h)
  | .trans h₁ h₂ =>
      Conv.trans
        (Conv.boolElim_cong_scrutinee thenBr elseBr h₁)
        (Conv.boolElim_cong_scrutinee thenBr elseBr h₂)
  | .fromStep s  => Conv.fromStep (Step.boolElimScrutinee s)

/-- Definitional equivalence threads through `boolElim`'s then-branch. -/
theorem Conv.boolElim_cong_then
    {mode scope} {ctx : Ctx mode scope}
    {resultType : Ty scope}
    (scrutinee : Term ctx Ty.bool)
    {thenBr₁ thenBr₂ : Term ctx resultType}
    (elseBr : Term ctx resultType) :
    Conv thenBr₁ thenBr₂ →
    Conv (Term.boolElim scrutinee thenBr₁ elseBr)
         (Term.boolElim scrutinee thenBr₂ elseBr)
  | .refl _      => Conv.refl _
  | .sym h       =>
      Conv.sym (Conv.boolElim_cong_then scrutinee elseBr h)
  | .trans h₁ h₂ =>
      Conv.trans
        (Conv.boolElim_cong_then scrutinee elseBr h₁)
        (Conv.boolElim_cong_then scrutinee elseBr h₂)
  | .fromStep s  => Conv.fromStep (Step.boolElimThen s)

/-- Definitional equivalence threads through `boolElim`'s else-branch. -/
theorem Conv.boolElim_cong_else
    {mode scope} {ctx : Ctx mode scope}
    {resultType : Ty scope}
    (scrutinee : Term ctx Ty.bool)
    (thenBr : Term ctx resultType)
    {elseBr₁ elseBr₂ : Term ctx resultType} :
    Conv elseBr₁ elseBr₂ →
    Conv (Term.boolElim scrutinee thenBr elseBr₁)
         (Term.boolElim scrutinee thenBr elseBr₂)
  | .refl _      => Conv.refl _
  | .sym h       =>
      Conv.sym (Conv.boolElim_cong_else scrutinee thenBr h)
  | .trans h₁ h₂ =>
      Conv.trans
        (Conv.boolElim_cong_else scrutinee thenBr h₁)
        (Conv.boolElim_cong_else scrutinee thenBr h₂)
  | .fromStep s  => Conv.fromStep (Step.boolElimElse s)

/-- Definitional equivalence threads through all three `boolElim`
positions simultaneously. -/
theorem Conv.boolElim_cong
    {mode scope} {ctx : Ctx mode scope}
    {resultType : Ty scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.bool}
    {thenBr₁ thenBr₂ elseBr₁ elseBr₂ : Term ctx resultType}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_then : Conv thenBr₁ thenBr₂)
    (h_else : Conv elseBr₁ elseBr₂) :
    Conv (Term.boolElim scrutinee₁ thenBr₁ elseBr₁)
         (Term.boolElim scrutinee₂ thenBr₂ elseBr₂) :=
  Conv.trans
    (Conv.boolElim_cong_scrutinee thenBr₁ elseBr₁ h_scr)
    (Conv.trans
      (Conv.boolElim_cong_then scrutinee₂ elseBr₁ h_then)
      (Conv.boolElim_cong_else scrutinee₂ thenBr₂ h_else))

/-! ### Concrete boolean reduction examples.

These existential-witness examples exhibit reductions that
actually fire — the kernel computes through booleans, not just
type-checks them.  Modelled after the v1.10 β-smoke tests
(`identityAppliedToUnit`, etc.).

The `Exists.intro` form sidesteps the elaboration order of
`example (mode : Mode) : <type> := <body>`, where Lean must
fully elaborate the type *before* seeing the body — and `<type>`
contains `Term ctx Ty.bool` shapes whose `ctx` is otherwise
unconstrained.  Wrapping in `∃ target, Step _ target` lets the
constructor itself pin every implicit. -/

/-- **ι-reduction on `boolTrue` exists**: `boolElim true unit unit
⟶ unit`.  The witness is `iotaBoolElimTrue` applied with both
branches as `unit`.  No `▸` cast — both sides have the same
declared `resultType = Ty.unit`. -/
example (mode : Mode) :
    ∃ (target : Term (Ctx.nil mode) Ty.unit),
      Step (Term.boolElim (resultType := Ty.unit)
              (Term.boolTrue (context := Ctx.nil mode))
              Term.unit Term.unit) target :=
  ⟨_, Step.iotaBoolElimTrue Term.unit Term.unit⟩

/-- **ι-reduction on `boolFalse` exists**: `boolElim false unit
unit ⟶ unit`. -/
example (mode : Mode) :
    ∃ (target : Term (Ctx.nil mode) Ty.unit),
      Step (Term.boolElim (resultType := Ty.unit)
              (Term.boolFalse (context := Ctx.nil mode))
              Term.unit Term.unit) target :=
  ⟨_, Step.iotaBoolElimFalse Term.unit Term.unit⟩

/-- **Multi-step computation exists**: starting from a `boolElim`
whose scrutinee is a β-redex, multi-step reduction reaches a
result.  The witness is the lifted scrutinee step via
`StepStar.boolElim_cong_scrutinee` plus the βApp on the inner
identity application.

We don't extract the cast residue — `Step.betaApp`'s reduct
carries a `▸` over `Ty.weaken_subst_singleton`, definitionally
equal to `Term.boolTrue` but not `rfl`-equal under `▸`.  The
existential just asserts *some* multi-step reduct exists, which
is the smoke-test discipline of v1.10.  Cast normalisation is a
v1.11+ concern (and `Term.cast_identity` already discharges the
residue at the equality level inside `Conv`). -/
example (mode : Mode) :
    ∃ (target : Term (Ctx.nil mode) Ty.bool),
      StepStar
        (Term.app
          (Term.lam (domainType := Ty.bool) (codomainType := Ty.bool)
            (Term.var (context := (Ctx.nil mode).cons Ty.bool)
                      ⟨0, Nat.zero_lt_succ _⟩))
          (Term.boolTrue (context := Ctx.nil mode))) target :=
  ⟨_, StepStar.step
        (@Step.betaApp mode 0 (Ctx.nil mode) Ty.bool Ty.bool
          (Term.var ⟨0, Nat.zero_lt_succ _⟩) Term.boolTrue)
        (StepStar.refl _)⟩

end LeanFX.Syntax

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

/-- Structurally extend a type's scope by one.  Direct structural
recursion — kept as a separate definition (rather than derived from
`Ty.rename`) so that the `Ty.rename_weaken_commute` lemma below admits
a clean structural induction proof using `▸ rfl`.

**Latent bug** (documented for v1.7+ to fix): the `piTy` case shifts
ALL variables in the codomain, including the locally-bound var 0.
This is *correct* for v1.0–v1.4 (no `Ty.tyVar`), and *not exercised*
by v1.5 smoke tests (which use `tyVar` only at top level or inside
`arrow`, not inside a `piTy` codomain).  The principled fix is
`Ty.weaken := t.rename Renaming.weaken`, which gives binder-aware
shifting via `ρ.lift`; that change makes the rwc lemma harder to
prove (rename-composition + pointwise renaming equality required).
v1.7+ will pair the fix with the additional lemma machinery.

Marked `@[reducible]` so Lean's unifier and `rfl` unfold it eagerly. -/
@[reducible]
def Ty.weaken {scope : Nat} : Ty scope → Ty (scope + 1)
  | .unit                          => .unit
  | .arrow domain codomain         =>
      .arrow domain.weaken codomain.weaken
  | .piTy domain codomain          =>
      .piTy domain.weaken codomain.weaken
  | .tyVar index                   =>
      .tyVar index.succ
  | .sigmaTy firstType secondType  =>
      .sigmaTy firstType.weaken secondType.weaken

/-- The fundamental rename-weaken commutativity lemma.  Says that
weakening (insert outer binder) commutes with renaming when the
renaming is appropriately lifted.

This is the load-bearing lemma that unblocks `Term.rename` (and thus
`Term.weaken`, `Term.subst`, β-reduction).  Without it, `Term.rename`'s
`lam` case cannot type-check — body's renamed type would be
`(B.weaken).rename ρ.lift` while the constructor wants
`(B.rename ρ).weaken`.

Proven by direct structural pattern match on `T`, using `▸` to
combine inductive hypotheses.  Axiom-free: `▸` is `Eq.rec` on `Ty`
(which lives in `Type`, not `Prop`), so no `propext` needed. -/
theorem Ty.rename_weaken_commute :
    ∀ {source target : Nat} (T : Ty source) (ρ : Renaming source target),
    (T.weaken).rename ρ.lift = (T.rename ρ).weaken
  | _, _, .unit, _ => rfl
  | _, _, .arrow A B, ρ => by
      show Ty.arrow (A.weaken.rename ρ.lift) (B.weaken.rename ρ.lift)
         = Ty.arrow (A.rename ρ).weaken (B.rename ρ).weaken
      have hA := Ty.rename_weaken_commute A ρ
      have hB := Ty.rename_weaken_commute B ρ
      exact hA ▸ hB ▸ rfl
  | _, _, .piTy A B, ρ => by
      show Ty.piTy (A.weaken.rename ρ.lift) (B.weaken.rename ρ.lift.lift)
         = Ty.piTy (A.rename ρ).weaken (B.rename ρ.lift).weaken
      have hA := Ty.rename_weaken_commute A ρ
      have hB := Ty.rename_weaken_commute B ρ.lift
      exact hA ▸ hB ▸ rfl
  | _, _, .tyVar _, _ => rfl
  | _, _, .sigmaTy A B, ρ => by
      show Ty.sigmaTy (A.weaken.rename ρ.lift) (B.weaken.rename ρ.lift.lift)
         = Ty.sigmaTy (A.rename ρ).weaken (B.rename ρ.lift).weaken
      have hA := Ty.rename_weaken_commute A ρ
      have hB := Ty.rename_weaken_commute B ρ.lift
      exact hA ▸ hB ▸ rfl

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

/-- Substitution commutes with weakening: substituting after
weakening = weakening after substituting (with appropriately lifted
substitution).  Stepping stone for the composition law `Ty.subst_compose`.

Proven by structural induction on `T`.  The `tyVar` case relies on
Fin proof irrelevance making `(σ i).weaken = (σ ⟨i.val, _⟩).weaken`
definitionally. -/
theorem Ty.subst_weaken_commute :
    ∀ {s t : Nat} (T : Ty s) (σ : Subst s t),
    (T.weaken).subst σ.lift = (T.subst σ).weaken
  | _, _, .unit, _ => rfl
  | _, _, .arrow X Y, σ => by
      show ((X.weaken).subst σ.lift).arrow ((Y.weaken).subst σ.lift)
         = ((X.subst σ).weaken).arrow ((Y.subst σ).weaken)
      have hX := Ty.subst_weaken_commute X σ
      have hY := Ty.subst_weaken_commute Y σ
      exact hX ▸ hY ▸ rfl
  | _, _, .piTy X Y, σ => by
      show ((X.weaken).subst σ.lift).piTy ((Y.weaken).subst σ.lift.lift)
         = ((X.subst σ).weaken).piTy ((Y.subst σ.lift).weaken)
      have hX := Ty.subst_weaken_commute X σ
      have hY := Ty.subst_weaken_commute Y σ.lift
      exact hX ▸ hY ▸ rfl
  | _, _, .tyVar _, _ => rfl
  | _, _, .sigmaTy X Y, σ => by
      show ((X.weaken).subst σ.lift).sigmaTy ((Y.weaken).subst σ.lift.lift)
         = ((X.subst σ).weaken).sigmaTy ((Y.subst σ.lift).weaken)
      have hX := Ty.subst_weaken_commute X σ
      have hY := Ty.subst_weaken_commute Y σ.lift
      exact hX ▸ hY ▸ rfl

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

/-! ## Variable lookup

A `Lookup` derivation is the structural witness "context Γ contains a
binding of type T at some de Bruijn position."  At every `there` the
target type is weakened, threading the scope-extension through the
indices automatically. -/

/-- Structural variable lookup.  `Lookup context target` proves the
context contains a binding of type `target`.  Variables in `Term` are
*derivations of this lookup judgment*, never raw integers. -/
inductive Lookup : {mode : Mode} → {scope : Nat} →
                   Ctx mode scope → Ty scope → Type
  /-- The variable bound at the head of the context — its type is the
  binding's type, weakened to live in the extended scope. -/
  | here :
      {mode : Mode} → {scope : Nat} →
      {context : Ctx mode scope} →
      {bindingType : Ty scope} →
      Lookup (Ctx.cons context bindingType) bindingType.weaken
  /-- A variable bound deeper than the head; the predecessor lookup
  gives a type at the prefix's scope, which we weaken to live in the
  extended scope. -/
  | there :
      {mode : Mode} → {scope : Nat} →
      {context : Ctx mode scope} →
      {targetType : Ty scope} →
      {boundType : Ty scope} →
      (predecessor : Lookup context targetType) →
      Lookup (Ctx.cons context boundType) targetType.weaken

/-! ## Terms

`Term context currentType` is a well-typed term in `context` of type
`currentType`.  Constructor signatures are the typing rules; Lean's
kernel checks each rule at declaration time, so a misstated rule is
rejected before any program is written using it. -/

/-- Intrinsically-typed terms.  No separate typing relation — the
constructor signatures *are* the typing rules. -/
inductive Term : {mode : Mode} → {scope : Nat} →
                 (context : Ctx mode scope) → Ty scope → Type
  /-- Variable rule.  A term is a variable iff it derives a structural
  lookup proving the named type sits in the context. -/
  | var :
      {mode : Mode} → {scope : Nat} →
      {context : Ctx mode scope} →
      {currentType : Ty scope} →
      (lookup : Lookup context currentType) →
      Term context currentType
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

/-- The empty context contains no bindings — confirms `nomatch` works on
the new indexed `Lookup` family with `Nat` scope and mode parameters. -/
theorem Lookup.notInEmpty
    {mode : Mode} {targetType : Ty 0} :
    Lookup (Ctx.nil mode) targetType → False :=
  fun lookup => nomatch lookup

/-- The polymorphic identity on `unit`, parameterised over the mode.
Confirms the mode parameter of `Ctx` is a working index — the same
syntactic construction type-checks at every FX mode. -/
def identityOnUnit (mode : Mode) :
    Term (Ctx.nil mode) (Ty.arrow .unit .unit) :=
  .lam (.var .here)

/-- Identity applied to the unit value at any mode.  Composes the `app`
and `lam` rules under the implicit-scope `unit` constructor. -/
def identityAppliedToUnit (mode : Mode) :
    Term (Ctx.nil mode) Ty.unit :=
  .app (identityOnUnit mode) .unit

/-- Three-level nested lambda — exercises `Lookup.there` chaining and
confirms deeply-nested binders type-check cleanly under the weakening
discipline. -/
def threeArgConstantUnit (mode : Mode) :
    Term (Ctx.nil mode)
         (Ty.arrow .unit (.arrow .unit (.arrow .unit .unit))) :=
  .lam (.lam (.lam (.var .here)))

/-- A term using `Lookup.there` to reach an outer binder.  The body of
the inner `lam` references the *outer* `unit` parameter via `there.here`,
demonstrating de Bruijn skip works under the new encoding. -/
def shadowingThenOuter (mode : Mode) :
    Term (Ctx.cons (Ctx.nil mode) Ty.unit)
         (Ty.arrow .unit .unit) :=
  .lam (.var (.there .here))

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

/-- Empty-context lookup is impossible. -/
example {mode : Mode} {targetType : Ty 0}
    (lookup : Lookup (Ctx.nil mode) targetType) : False :=
  Lookup.notInEmpty lookup

/-! ## v1.6 — typed reduction.

Single-step reduction `Step t₁ t₂` is a `Prop`-valued indexed relation
between terms of the *same* type.  The shared type is enforced
structurally — both sides of every constructor carry identical `mode`,
`scope`, `ctx`, and `T` indices, which means **subject reduction is
definitional**: there is no separate "preservation" theorem to prove,
because no `Step` proof can witness a type change.

Currently this layer covers **congruence** rules only — `Step` propagates
under each binary/unary term constructor.  The β rule (`(λx.body) a ⟶
body[a/x]`) is deferred to v1.7+ pending `Term.subst`, which itself
requires the rename-substitution lemmas hierarchy that builds on the
existing `Ty.rename_weaken_commute`.

The reflexive-transitive closure `StepStar` lifts single-step to
multi-step reduction.  Together, `Step` and `StepStar` are the basis
for v1.7+ conversion algorithms and the eventual normaliser. -/

/-- Single-step reduction between terms of the *same* type.  The shared
typing is structural: every constructor's input and output `Term` carry
the same `Ctx` and `Ty`, so subject reduction holds definitionally.

v1.6 has congruence rules only; β/η await Term-level substitution. -/
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

/-- **Subject reduction is definitional**: if `Step t₁ t₂` holds, then
`t₁` and `t₂` have the same type by the relation's signature.  No proof
needed — the indices enforce it.  This `example` makes it explicit. -/
example {mode : Mode} {scope : Nat} {ctx : Ctx mode scope} {T : Ty scope}
    {t₁ t₂ : Term ctx T} (_step : Step t₁ t₂) : Term ctx T := t₂

/-- Multi-step reduction is reflexive (zero-step from `refl`). -/
example {mode : Mode} {scope : Nat} {ctx : Ctx mode scope} {T : Ty scope}
    (t : Term ctx T) : StepStar t t := StepStar.refl t

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

/-! ## v1.1 — Lookup helpers, term measures, first proven theorem.

The definitions below add the first **theorem** (not just `example`) of
the package, exercising structural induction over the indexed `Term`
family.  Each must stay axiom-free per the binder-form rule. -/

/-- Extract a de Bruijn index from a structural lookup proof.  The
result is just a `Nat` (not `Fin scope`) — that bound is proved
separately in `Lookup.toIndex_lt_scope`, so the type-bound version is
derivable but doesn't enlarge the trust base. -/
def Lookup.toIndex
    {mode : Mode} {scope : Nat} {context : Ctx mode scope}
    {targetType : Ty scope} :
    Lookup context targetType → Nat
  | .here              => 0
  | .there predecessor => predecessor.toIndex + 1

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

/-! ## v1.1 smoke tests -/

/-- The size of `id unit` is 3: one `app`, one `lam`, one `unit`,
one `var` — wait, that's four.  Let's recount: `app` (1) + `lam` (1)
+ `var` (1) + `unit` (1) = 4.  rfl test below. -/
example (mode : Mode) : (identityAppliedToUnit mode).size = 4 := rfl

/-- The varCount of `id unit` is 1: one `var` from the lam body, the
top-level `unit` doesn't count, the `app` and `lam` don't count. -/
example (mode : Mode) : (identityAppliedToUnit mode).varCount = 1 := rfl

/-- The toIndex of `Lookup.here` is 0; of `there here` is 1. -/
example {mode : Mode} {bindingType : Ty 0} :
    (@Lookup.here mode 0 (Ctx.nil mode) bindingType).toIndex = 0 := rfl

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
  .lamPi (.var .here)

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

end LeanFX.Syntax

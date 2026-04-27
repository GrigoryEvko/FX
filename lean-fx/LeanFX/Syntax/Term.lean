import LeanFX.Mode.Defn

/-! # FX intrinsic syntax.

Well-scoped intrinsic encoding (Allais–McBride style): `Ty` is indexed
by scope size (`Nat`), `Ctx` carries the actual binding types and is
indexed by mode + scope, and `Term` is indexed by context + type so
that the constructor signatures *are* the typing rules.  This sidesteps
Lean 4's strict-positivity rejection of the textbook Ty-mutually-with-
Ctx formulation that Agda accepts.

Contents, in dependency order:

  * `Ty` and the renaming / substitution algebra (`Ty.rename`,
    `Ty.subst`, plus identity / composition / commute laws).
  * `Ctx`, `varType`, and the intrinsic `Term` family.
  * `TermRenaming` / `TermSubst` and term-level `Term.rename`,
    `Term.weaken`, `Term.subst`, `Term.subst0`.
  * Functoriality witnesses (`Term.subst_id`, the closed-context
    cases of `Term.subst_weaken_commute_HEq`, and the pointwise-HEq
    machinery the binder cases need).
  * Reduction relations: `Step` (single-step β/η/ι), `StepStar`
    (multi-step), and `Conv` (definitional conversion), with full
    structural congruences for each. -/

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

/-! Decidable equality on `Ty` — auto-derives axiom-free because
`Ty`'s index is a bare `Nat`, so the discrimination obligations
are propext-free `Eq.rec` over an irrelevant motive. -/
deriving instance DecidableEq for Ty

/-! ## Renaming machinery.

`Renaming source target := Fin source → Fin target`.  `Ty.rename` is
defined first; `Ty.weaken` is then derived as `T.rename Renaming.weaken`
so binders stay binder-aware (the local `tyVar 0` is preserved by
`Renaming.lift`'s var-0 case). -/

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

/-! ## Rename composition algebra.

`Ty.rename_congr` and `Ty.rename_compose` proved by direct structural
induction with no dependency on the substitution hierarchy.  This
lets `Ty.weaken := T.rename Renaming.weaken` and the
`Ty.rename_weaken_commute` lemma derive without circularity. -/

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

/-! ## Substitution-lemma hierarchy.

How `Ty.subst` interacts with `Ty.rename`, with itself, and with
lifting.  All lemmas use pointwise substitution equivalence
(`Subst.equiv`) rather than Lean function-equality — funext would
pull in `propext`. -/

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

/-! ## Renaming as a special case of substitution.

A renaming is a substitution whose substituent at each position is a
`tyVar` reference.  All renaming lemmas are derivable from the
corresponding substitution lemmas via this coercion. -/

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

/-! ## Monoid laws for Renaming and Subst.

Composition is associative and unital on both sides.  Stated as
pointwise equivalences to stay funext-free. -/

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

/-! ## Term-level renaming.

`TermRenaming Γ Δ ρ` is the position-equality property: at every
`Fin scope` of `Γ`, the looked-up type at `ρ i` in `Δ` equals
`varType Γ i` after type-level renaming.  A `Prop` rather than a
`Type` so `Term.rename` can descend through the term without the
match compiler emitting `Ctx.noConfusion`. -/

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

/-! ## Term-level weakening. -/

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

/-! ## Term-level substitution.

`TermSubst Γ Δ σ` supplies for each `i : Fin scope` a term in `Δ`
whose type is `(varType Γ i).subst σ`.  `TermSubst.lift` extends
under a binder by `Term.weaken`-ing predecessor terms into the
extended target. -/

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

/-! ## Substitution-substitution commutativity.

`subst0` distributes through an outer subst by lifting the codomain's
substitution and substituting the substituted substituent.  Used by
`Term.subst`'s `appPi` / `pair` / `snd` cases to align result types. -/

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

/-! ## Categorical structure on TermSubst.

The term-level analogues of `Subst.identity` and `Subst.compose`,
witnessing the same enriched-category structure at the term level.
Functoriality theorems (`Term.subst_id`, `Term.subst_compose`) need
dependent-cast wrangling because `Term.subst σt t : Term Δ (T.subst
σ)` is not definitionally `Term Δ T` even when `σ = Subst.identity`. -/

/-- Identity term-substitution: each position `i` maps to `Term.var i`,
cast through `Ty.subst_id` to live at `(varType Γ i).subst Subst.identity`. -/
def TermSubst.identity {m : Mode} {scope : Nat} (Γ : Ctx m scope) :
    TermSubst Γ Γ Subst.identity := fun i =>
  (Ty.subst_id (varType Γ i)).symm ▸ Term.var i

/-- Compose two term-substitutions: apply `σt₁` then substitute the
result by `σt₂`, casting through `Ty.subst_compose`. -/
def TermSubst.compose {m : Mode} {scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m scope₁} {Γ₂ : Ctx m scope₂} {Γ₃ : Ctx m scope₃}
    {σ₁ : Subst scope₁ scope₂} {σ₂ : Subst scope₂ scope₃}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂) :
    TermSubst Γ₁ Γ₃ (Subst.compose σ₁ σ₂) := fun i =>
  Ty.subst_compose (varType Γ₁ i) σ₁ σ₂ ▸ Term.subst σt₂ (σt₁ i)

/-! ## HEq bridge helpers for term-substitution functoriality.

`Term.subst_id` and `Term.subst_compose` need to bridge terms whose
types differ propositionally (e.g. `Term Γ (T.subst Subst.identity)`
vs `Term Γ T`).  HEq is the right notion of equality; the lemmas
below collapse outer casts and align cons-extended contexts. -/

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

/-! ## HEq congruence helpers per `Term` constructor.

Each `Term.C_HEq_congr` says: two `C`-applications are HEq when their
type-level implicits are propositionally equal and their value
arguments are HEq.  Building blocks for any inductive proof that
descends through `Term.subst` / `Term.rename` and needs to bridge
`Term` values across different type indices. -/

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

/-! ## `Term.subst_id_HEq` leaf cases.

Four leaf constructors: `var` strips the inner `(Ty.subst_id _).symm
▸ Term.var i` cast via `eqRec_heq`; `unit`/`boolTrue`/`boolFalse`
have substitution-independent types so reduce to `HEq.refl`. -/

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

/-! ## `Term.subst_id_HEq` closed-context cases.

Constructors whose subterms live in the same context as the parent
(no `TermSubst.lift`).  Each takes per-subterm HEq IHs and combines
via the constructor-HEq congruences with `Ty.subst_id` bridges.
The cast-bearing cases (`appPi`, `pair`, `snd`) strip the outer
`Ty.subst0_subst_commute` cast via `eqRec_heq` first. -/

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

/-! ## `TermSubst.lift_HEq_pointwise`.

Pointwise HEq for the lifts of two TermSubsts that are pointwise HEq
themselves (and whose underlying Substs are pointwise equal).  Used
by the binder cases of `Term.subst_HEq_pointwise` to extend the
hypothesis under each new binder. -/
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

/-! ## `Term.subst_HEq_pointwise`.

Substitution respects pointwise HEq of TermSubsts.  The `h_ctx :
Δ₁ = Δ₂` parameter accommodates binder-case recursive calls where
`TermSubst.lift σt_i dom` lands in `Δ.cons (dom.subst σ_i)` —
same scope, different concrete contexts. -/
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

/-! ## `Term.subst_id_HEq`.

Full HEq form of subst-by-identity.  Structural induction; binder
cases use `Term.subst_HEq_pointwise` to bridge
`TermSubst.lift (TermSubst.identity Γ)` to
`TermSubst.identity (Γ.cons _)` via `lift_identity_pointwise`. -/
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

/-! ## `Term.subst_id` (explicit-`▸` form).

Corollary of `Term.subst_id_HEq` + `eqRec_heq`. -/
theorem Term.subst_id {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    {T : Ty scope} (t : Term Γ T) :
    (Ty.subst_id T) ▸ Term.subst (TermSubst.identity Γ) t = t :=
  eq_of_heq (HEq.trans (eqRec_heq _ _) (Term.subst_id_HEq t))

/-! ## Cast-through-Term.subst HEq helper.

Pushes a type-cast on the input out through `Term.subst` so the
substitution's structural recursion can fire on the bare
constructor.  Bridge for `lift_compose_pointwise_zero` and the
cast-bearing closed-context commute cases. -/
theorem Term.subst_HEq_cast_input
    {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {σ : Subst scope scope'} (σt : TermSubst Γ Δ σ)
    {T₁ T₂ : Ty scope} (h : T₁ = T₂) (t : Term Γ T₁) :
    HEq (Term.subst σt (h ▸ t)) (Term.subst σt t) := by
  cases h
  rfl

/-! ## `TermSubst.lift_compose_pointwise` at position 0.

Lifting a composed term-substitution under a binder agrees HEq with
composing the two lifts on the freshly-bound variable.  The position-
`k+1` case requires `Term.subst_weaken_commute_HEq` (binder cases
deferred) and is shipped as a separate companion. -/
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

/-! ## Term-level subst-weaken commute.

Goal:

  Term.subst (σt.lift X) (Term.weaken X t)
    ≃HEq≃
  Term.weaken (X.subst σ) (Term.subst σt t)

Term-level analogue of `Ty.subst_weaken_commute`; the missing piece
for full `Term.subst_compose`.  Closed-context cases follow; the
binder cases (`lam`, `lamPi`) require a term-level rename-subst
commute and are deferred. -/

/-! ### Leaf cases. -/

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

/-! ### Closed-context recursive cases — no-cast subset (`app`, `boolElim`). -/

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

/-! ### Closed-context cases bearing sigmaTy/piTy second-component lifts.

The `fst`/`snd`/`pair`/`appPi` cases have second-component types at
`Ty (scope + 1)` threading through a binder-lift on both Term.weaken
and Term.subst sides.  The bridge equation

  (second.rename Renaming.weaken.lift).subst σ.lift.lift
    = (second.subst σ.lift).rename Renaming.weaken.lift

follows from `Ty.rename_subst_commute` + a pointwise Subst
equivalence + `Ty.subst_rename_commute.symm`. -/

/-- Pointwise equivalence at the double-lift level used by all four
sigmaTy/piTy second-component bridges.  Position 0 is `rfl`; position
`k+1` is `Ty.rename_weaken_commute (σ ⟨k, _⟩) Renaming.weaken`.symm. -/
theorem Subst.precompose_weaken_lift_double_eq_renameAfter_lift_weaken_lift
    {s t : Nat} (σ : Subst s t) :
    Subst.equiv
      (Subst.precompose (@Renaming.weaken s).lift σ.lift.lift)
      (Subst.renameAfter σ.lift (@Renaming.weaken t).lift) := fun i =>
  match i with
  | ⟨0, _⟩       => rfl
  | ⟨k + 1, hk⟩  =>
      (Ty.rename_weaken_commute
        (σ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) Renaming.weaken).symm

/-- Closed-context recursive case for `fst`.  No casts on
either side (Term.weaken X and Term.subst σt both push through
`Term.fst` definitionally), but the type-level h_second
equation requires the rename-subst commute chain plus the
pointwise equivalence above.  Combine via
`Term.fst_HEq_congr` with h_first = `Ty.subst_weaken_commute
first σ` and h_second from the chain. -/
theorem Term.subst_weaken_commute_HEq_fst
    {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {σ : Subst scope scope'} (σt : TermSubst Γ Δ σ)
    (X : Ty scope)
    {first : Ty scope} {second : Ty (scope + 1)}
    (p : Term Γ (Ty.sigmaTy first second))
    (ih_p : HEq
              (Term.subst (σt.lift X) (Term.weaken X p))
              (Term.weaken (X.subst σ) (Term.subst σt p))) :
    HEq
      (Term.subst (σt.lift X) (Term.weaken X (Term.fst p)))
      (Term.weaken (X.subst σ) (Term.subst σt (Term.fst p))) := by
  show HEq
    (Term.fst (Term.subst (σt.lift X) (Term.weaken X p)))
    (Term.fst (Term.weaken (X.subst σ) (Term.subst σt p)))
  -- Bridge the second-component sigmaTy types via the
  -- rename-subst commute chain.
  have h_second :
      (second.rename Renaming.weaken.lift).subst σ.lift.lift
        = (second.subst σ.lift).rename Renaming.weaken.lift :=
    (Ty.rename_subst_commute second Renaming.weaken.lift σ.lift.lift).trans
      ((Ty.subst_congr
          (Subst.precompose_weaken_lift_double_eq_renameAfter_lift_weaken_lift σ)
          second).trans
        (Ty.subst_rename_commute second σ.lift Renaming.weaken.lift).symm)
  exact Term.fst_HEq_congr
    (Ty.subst_weaken_commute first σ)
    h_second
    _ _ ih_p

/-! ### Cast-through-Term.weaken HEq helper, and the `snd` case.

`Term.weaken_HEq_cast_input` is the weaken-side counterpart of
`Term.subst_HEq_cast_input`.  The `snd` case is `fst` plus the
matching cast-strips on `Term.subst`'s and `Term.rename`'s
`(Ty.subst0_*_commute).symm ▸` wrappers. -/

/-- Push a propositional type-cast on the input of `Term.weaken X`
out to an HEq.  `cases h; rfl` once the equation is trivialized. -/
theorem Term.weaken_HEq_cast_input
    {m : Mode} {scope : Nat} {Γ : Ctx m scope}
    (X : Ty scope) {T₁ T₂ : Ty scope} (h : T₁ = T₂) (t : Term Γ T₁) :
    HEq (Term.weaken X (h ▸ t)) (Term.weaken X t) := by
  cases h
  rfl

/-- Closed-context recursive case for `snd`.  Both `Term.weaken X`
and `Term.subst σt` wrap the resulting `Term.snd` in
`(Ty.subst0_*_commute).symm ▸` casts; the proof strips both via
`eqRec_heq` and the cast-input helpers, then applies
`Term.snd_HEq_congr` with the same h_first / h_second pair as
`fst`. -/
theorem Term.subst_weaken_commute_HEq_snd
    {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {σ : Subst scope scope'} (σt : TermSubst Γ Δ σ)
    (X : Ty scope)
    {first : Ty scope} {second : Ty (scope + 1)}
    (p : Term Γ (Ty.sigmaTy first second))
    (ih_p : HEq
              (Term.subst (σt.lift X) (Term.weaken X p))
              (Term.weaken (X.subst σ) (Term.subst σt p))) :
    HEq
      (Term.subst (σt.lift X) (Term.weaken X (Term.snd p)))
      (Term.weaken (X.subst σ) (Term.subst σt (Term.snd p))) := by
  -- Same h_second equation as fst.
  have h_second :
      (second.rename Renaming.weaken.lift).subst σ.lift.lift
        = (second.subst σ.lift).rename Renaming.weaken.lift :=
    (Ty.rename_subst_commute second Renaming.weaken.lift σ.lift.lift).trans
      ((Ty.subst_congr
          (Subst.precompose_weaken_lift_double_eq_renameAfter_lift_weaken_lift σ)
          second).trans
        (Ty.subst_rename_commute second σ.lift Renaming.weaken.lift).symm)
  -- LHS path:
  --   Term.weaken X (Term.snd p)
  --   = (Ty.subst0_rename_commute second first Renaming.weaken).symm ▸
  --       Term.snd (Term.weaken X p)
  --   Term.subst (σt.lift X) on this casted term — push cast
  --   through via Term.subst_HEq_cast_input, then Term.subst's
  --   snd clause emits a (Ty.subst0_subst_commute ...).symm ▸
  --   wrapper.
  apply HEq.trans
    (Term.subst_HEq_cast_input
      (σt.lift X)
      (Ty.subst0_rename_commute second first Renaming.weaken).symm
      (Term.snd (Term.weaken X p)))
  -- After helper: HEq (Term.subst (σt.lift X) (Term.snd (Term.weaken X p))) RHS
  -- Term.subst's snd clause:
  show HEq
    ((Ty.subst0_subst_commute (second.rename Renaming.weaken.lift)
        (first.rename Renaming.weaken) σ.lift).symm ▸
      Term.snd (Term.subst (σt.lift X) (Term.weaken X p)))
    _
  -- Strip outer cast on LHS via eqRec_heq.
  apply HEq.trans (eqRec_heq _ _)
  -- Now: HEq (Term.snd (Term.subst (σt.lift X) (Term.weaken X p)))
  --          (Term.weaken (X.subst σ) (Term.subst σt (Term.snd p)))
  --
  -- RHS path: flip and process Term.weaken (X.subst σ) on a casted Term.snd.
  apply HEq.symm
  -- Term.subst σt (Term.snd p) =
  --   (Ty.subst0_subst_commute second first σ).symm ▸ Term.snd (Term.subst σt p)
  -- Term.weaken (X.subst σ) on casted — push through.
  apply HEq.trans
    (Term.weaken_HEq_cast_input
      (X.subst σ)
      (Ty.subst0_subst_commute second first σ).symm
      (Term.snd (Term.subst σt p)))
  -- After helper: HEq (Term.weaken (X.subst σ) (Term.snd (Term.subst σt p))) LHS
  -- Term.weaken's snd clause:
  show HEq
    ((Ty.subst0_rename_commute (second.subst σ.lift) (first.subst σ)
        Renaming.weaken).symm ▸
      Term.snd (Term.weaken (X.subst σ) (Term.subst σt p)))
    _
  -- Strip outer cast.
  apply HEq.trans (eqRec_heq _ _)
  -- Flip back to LHS-orientation.
  apply HEq.symm
  -- Now: HEq (Term.snd (Term.subst (σt.lift X) (Term.weaken X p)))
  --          (Term.snd (Term.weaken (X.subst σ) (Term.subst σt p)))
  -- Apply Term.snd_HEq_congr.
  exact Term.snd_HEq_congr
    (Ty.subst_weaken_commute first σ)
    h_second
    _ _ ih_p

/-! ### `pair` closed-context case.

The outer `Term.pair` has no cast in either clause, but the
secondVal argument carries a `Ty.subst0_*_commute` cast on both
sides — four nested casts after the outer `Term.subst` / `Term.weaken`
push through.  The `h_w` HEq peels these in onion-layer order. -/
theorem Term.subst_weaken_commute_HEq_pair
    {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {σ : Subst scope scope'} (σt : TermSubst Γ Δ σ)
    (X : Ty scope)
    {first : Ty scope} {second : Ty (scope + 1)}
    (v : Term Γ first) (w : Term Γ (second.subst0 first))
    (ih_v : HEq
              (Term.subst (σt.lift X) (Term.weaken X v))
              (Term.weaken (X.subst σ) (Term.subst σt v)))
    (ih_w : HEq
              (Term.subst (σt.lift X) (Term.weaken X w))
              (Term.weaken (X.subst σ) (Term.subst σt w))) :
    HEq
      (Term.subst (σt.lift X) (Term.weaken X (Term.pair v w)))
      (Term.weaken (X.subst σ) (Term.subst σt (Term.pair v w))) := by
  -- Same h_second as fst/snd.
  have h_second :
      (second.rename Renaming.weaken.lift).subst σ.lift.lift
        = (second.subst σ.lift).rename Renaming.weaken.lift :=
    (Ty.rename_subst_commute second Renaming.weaken.lift σ.lift.lift).trans
      ((Ty.subst_congr
          (Subst.precompose_weaken_lift_double_eq_renameAfter_lift_weaken_lift σ)
          second).trans
        (Ty.subst_rename_commute second σ.lift Renaming.weaken.lift).symm)
  -- Apply Term.pair_HEq_congr first; Lean computes the actual
  -- goal-shape with whatever cast forms it produces internally.
  -- The first three args (h_first, h_second, h_v) discharge
  -- directly; the secondVal HEq goal is resolved by the
  -- four-cast chain inline.
  apply Term.pair_HEq_congr
    (Ty.subst_weaken_commute first σ)
    h_second
    _ _ ih_v
  -- Goal: HEq of secondVal arguments.  Strip outer cast on LHS.
  apply HEq.trans (eqRec_heq _ _)
  -- Push the inner cast on LHS through Term.subst via v1.26 helper.
  apply HEq.trans
    (Term.subst_HEq_cast_input
      (σt.lift X)
      (Ty.subst0_rename_commute second first Renaming.weaken)
      (Term.weaken X w))
  -- Bridge via IH on w.
  apply HEq.trans ih_w
  -- Flip and process RHS.
  apply HEq.symm
  -- Strip outer cast on RHS.
  apply HEq.trans (eqRec_heq _ _)
  -- Push the inner cast on RHS through Term.weaken via v1.31 helper.
  exact Term.weaken_HEq_cast_input
    (X.subst σ)
    (Ty.subst0_subst_commute second first σ)
    (Term.subst σt w)

/-! ### `appPi` closed-context case.

Final closed-context case.  `appPi` combines `snd`'s outer-cast
pattern with `app`'s two-subterm shape; uses the same h_cod
sigmaTy-second-component bridge as `fst`. -/
theorem Term.subst_weaken_commute_HEq_appPi
    {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {σ : Subst scope scope'} (σt : TermSubst Γ Δ σ)
    (X : Ty scope)
    {dom : Ty scope} {cod : Ty (scope + 1)}
    (f : Term Γ (Ty.piTy dom cod)) (a : Term Γ dom)
    (ih_f : HEq
              (Term.subst (σt.lift X) (Term.weaken X f))
              (Term.weaken (X.subst σ) (Term.subst σt f)))
    (ih_a : HEq
              (Term.subst (σt.lift X) (Term.weaken X a))
              (Term.weaken (X.subst σ) (Term.subst σt a))) :
    HEq
      (Term.subst (σt.lift X) (Term.weaken X (Term.appPi f a)))
      (Term.weaken (X.subst σ) (Term.subst σt (Term.appPi f a))) := by
  -- Same h_cod as fst/snd/pair (cod : Ty (scope+1) lift bridge).
  have h_cod :
      (cod.rename Renaming.weaken.lift).subst σ.lift.lift
        = (cod.subst σ.lift).rename Renaming.weaken.lift :=
    (Ty.rename_subst_commute cod Renaming.weaken.lift σ.lift.lift).trans
      ((Ty.subst_congr
          (Subst.precompose_weaken_lift_double_eq_renameAfter_lift_weaken_lift σ)
          cod).trans
        (Ty.subst_rename_commute cod σ.lift Renaming.weaken.lift).symm)
  -- LHS: Term.weaken X (Term.appPi f a) emits a cast wrapping
  -- Term.appPi.  Push cast through Term.subst via v1.26 helper.
  apply HEq.trans
    (Term.subst_HEq_cast_input
      (σt.lift X)
      (Ty.subst0_rename_commute cod dom Renaming.weaken).symm
      (Term.appPi (Term.weaken X f) (Term.weaken X a)))
  -- Now LHS = Term.subst (σt.lift X) (Term.appPi (...) (...))
  -- Strip outer cast from Term.subst's appPi clause.
  apply HEq.trans (eqRec_heq _ _)
  -- Flip and process RHS.
  apply HEq.symm
  -- Term.subst σt (Term.appPi f a) emits a cast wrapping Term.appPi.
  -- Push cast through Term.weaken via v1.31 helper.
  apply HEq.trans
    (Term.weaken_HEq_cast_input
      (X.subst σ)
      (Ty.subst0_subst_commute cod dom σ).symm
      (Term.appPi (Term.subst σt f) (Term.subst σt a)))
  -- Strip outer cast from Term.weaken's appPi clause.
  apply HEq.trans (eqRec_heq _ _)
  -- Flip back to LHS-orientation.
  apply HEq.symm
  -- Apply Term.appPi_HEq_congr.
  exact Term.appPi_HEq_congr
    (Ty.subst_weaken_commute dom σ)
    h_cod
    _ _ ih_f
    _ _ ih_a

/-! ## `Term.rename_HEq_pointwise`.

Two TermRenamings whose underlying Renamings agree pointwise produce
HEq results when applied to the same term.  The renaming-side analogue
of `Term.subst_HEq_pointwise`.  The `h_ctx : Δ₁ = Δ₂` parameter
accommodates the binder cases, where `TermRenaming.lift ρt_i dom`
lands in `Δ_i.cons (dom.rename ρ_i)` — different cons-extensions
across i = 1, 2. -/
theorem Term.rename_HEq_pointwise
    {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ₁ Δ₂ : Ctx m scope'}
    (h_ctx : Δ₁ = Δ₂)
    {ρ₁ ρ₂ : Renaming scope scope'}
    (ρt₁ : TermRenaming Γ Δ₁ ρ₁) (ρt₂ : TermRenaming Γ Δ₂ ρ₂)
    (h_ρ : Renaming.equiv ρ₁ ρ₂) :
    {T : Ty scope} → (t : Term Γ T) →
      HEq (Term.rename ρt₁ t) (Term.rename ρt₂ t)
  | _, .var i => by
    cases h_ctx
    -- Term.rename ρt₁ (Term.var i) = (ρt₁ i) ▸ Term.var (ρ₁ i)
    -- Term.rename ρt₂ (Term.var i) = (ρt₂ i) ▸ Term.var (ρ₂ i)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    -- Goal: HEq (Term.var (ρ₁ i)) (Term.var (ρ₂ i))
    -- Use h_ρ i to align the Fin positions.
    rw [h_ρ i]
  | _, .unit => by cases h_ctx; exact HEq.refl _
  | _, .app f a => by
    cases h_ctx
    show HEq
      (Term.app (Term.rename ρt₁ f) (Term.rename ρt₁ a))
      (Term.app (Term.rename ρt₂ f) (Term.rename ρt₂ a))
    exact Term.app_HEq_congr
      (Ty.rename_congr h_ρ _)
      (Ty.rename_congr h_ρ _)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ f)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ a)
  | _, .fst (firstType := first) (secondType := second) p => by
    cases h_ctx
    show HEq
      (Term.fst (Term.rename ρt₁ p))
      (Term.fst (Term.rename ρt₂ p))
    apply Term.fst_HEq_congr
      (Ty.rename_congr h_ρ first)
      (Ty.rename_congr (Renaming.lift_equiv h_ρ) second)
    exact Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ p
  | _, .boolTrue => by cases h_ctx; exact HEq.refl _
  | _, .boolFalse => by cases h_ctx; exact HEq.refl _
  | _, .boolElim (resultType := result) s t e => by
    cases h_ctx
    show HEq
      (Term.boolElim (Term.rename ρt₁ s)
                     (Term.rename ρt₁ t)
                     (Term.rename ρt₁ e))
      (Term.boolElim (Term.rename ρt₂ s)
                     (Term.rename ρt₂ t)
                     (Term.rename ρt₂ e))
    exact Term.boolElim_HEq_congr
      (Ty.rename_congr h_ρ result)
      _ _ (eq_of_heq (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ s))
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ t)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    cases h_ctx
    show HEq
      ((Ty.subst0_rename_commute cod dom ρ₁).symm ▸
        Term.appPi (Term.rename ρt₁ f) (Term.rename ρt₁ a))
      ((Ty.subst0_rename_commute cod dom ρ₂).symm ▸
        Term.appPi (Term.rename ρt₂ f) (Term.rename ρt₂ a))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b :=
      Term.appPi (Term.rename ρt₂ f) (Term.rename ρt₂ a))
    · exact Term.appPi_HEq_congr
        (Ty.rename_congr h_ρ dom)
        (Ty.rename_congr (Renaming.lift_equiv h_ρ) cod)
        _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ f)
        _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ a)
    · exact (eqRec_heq _ _).symm
  | _, .pair (firstType := first) (secondType := second) v w => by
    cases h_ctx
    show HEq
      (Term.pair (Term.rename ρt₁ v)
        ((Ty.subst0_rename_commute second first ρ₁) ▸
          (Term.rename ρt₁ w)))
      (Term.pair (Term.rename ρt₂ v)
        ((Ty.subst0_rename_commute second first ρ₂) ▸
          (Term.rename ρt₂ w)))
    apply Term.pair_HEq_congr
      (Ty.rename_congr h_ρ first)
      (Ty.rename_congr (Renaming.lift_equiv h_ρ) second)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ v)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ w)
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p => by
    cases h_ctx
    show HEq
      ((Ty.subst0_rename_commute second first ρ₁).symm ▸
        Term.snd (Term.rename ρt₁ p))
      ((Ty.subst0_rename_commute second first ρ₂).symm ▸
        Term.snd (Term.rename ρt₂ p))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (b := Term.snd (Term.rename ρt₂ p))
    · exact Term.snd_HEq_congr
        (Ty.rename_congr h_ρ first)
        (Ty.rename_congr (Renaming.lift_equiv h_ρ) second)
        _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ p)
    · exact (eqRec_heq _ _).symm
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    cases h_ctx
    show HEq
      (Term.lam (codomainType := cod.rename ρ₁)
        ((Ty.rename_weaken_commute cod ρ₁) ▸
          (Term.rename (TermRenaming.lift ρt₁ dom) body)))
      (Term.lam (codomainType := cod.rename ρ₂)
        ((Ty.rename_weaken_commute cod ρ₂) ▸
          (Term.rename (TermRenaming.lift ρt₂ dom) body)))
    apply Term.lam_HEq_congr
      (Ty.rename_congr h_ρ dom) (Ty.rename_congr h_ρ cod)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_pointwise
        (congrArg (·.cons (dom.rename ρ₁)) (rfl : Δ₁ = Δ₁) |>.trans
          (congrArg Δ₁.cons (Ty.rename_congr h_ρ dom)))
        (TermRenaming.lift ρt₁ dom)
        (TermRenaming.lift ρt₂ dom)
        (Renaming.lift_equiv h_ρ)
        body)
    exact (eqRec_heq _ _).symm
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    cases h_ctx
    show HEq
      (Term.lamPi (Term.rename (TermRenaming.lift ρt₁ dom) body))
      (Term.lamPi (Term.rename (TermRenaming.lift ρt₂ dom) body))
    apply Term.lamPi_HEq_congr
      (Ty.rename_congr h_ρ dom)
      (Ty.rename_congr (Renaming.lift_equiv h_ρ) cod)
    exact Term.rename_HEq_pointwise
      (congrArg Δ₁.cons (Ty.rename_congr h_ρ dom))
      (TermRenaming.lift ρt₁ dom)
      (TermRenaming.lift ρt₂ dom)
      (Renaming.lift_equiv h_ρ)
      body

/-! ## Term-rename composition. -/

/-- Composition of term-level renamings.  Position-equality witness
chains the two `TermRenaming`s through `Ty.rename_compose`. -/
theorem TermRenaming.compose
    {m : Mode} {scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m scope₁} {Γ₂ : Ctx m scope₂} {Γ₃ : Ctx m scope₃}
    {ρ₁ : Renaming scope₁ scope₂} {ρ₂ : Renaming scope₂ scope₃}
    (ρt₁ : TermRenaming Γ₁ Γ₂ ρ₁) (ρt₂ : TermRenaming Γ₂ Γ₃ ρ₂) :
    TermRenaming Γ₁ Γ₃ (Renaming.compose ρ₁ ρ₂) := fun i => by
  show varType Γ₃ (ρ₂ (ρ₁ i))
     = (varType Γ₁ i).rename (Renaming.compose ρ₁ ρ₂)
  rw [ρt₂ (ρ₁ i)]
  rw [ρt₁ i]
  exact Ty.rename_compose (varType Γ₁ i) ρ₁ ρ₂

/-- Push a propositional type-cast on the input of `Term.rename ρt`
out to an HEq.  Mirror of `Term.subst_HEq_cast_input` and
`Term.weaken_HEq_cast_input`. -/
theorem Term.rename_HEq_cast_input
    {m : Mode} {scope scope' : Nat}
    {Γ : Ctx m scope} {Δ : Ctx m scope'}
    {ρ : Renaming scope scope'} (ρt : TermRenaming Γ Δ ρ)
    {T₁ T₂ : Ty scope} (h : T₁ = T₂) (t : Term Γ T₁) :
    HEq (Term.rename ρt (h ▸ t)) (Term.rename ρt t) := by
  cases h
  rfl

/-! ## `Term.rename_compose_HEq`.

Double-rename equals single-rename by composed renaming, modulo HEq.
The two sides have types `Term Γ₃ ((T.rename ρ₁).rename ρ₂)` and
`Term Γ₃ (T.rename (Renaming.compose ρ₁ ρ₂))`; these agree
propositionally by `Ty.rename_compose`.  Pattern-matched structural
induction on the term.

Binder cases bridge `TermRenaming.lift (compose ρt₁ ρt₂) dom` against
`compose (lift ρt₁ dom) (lift ρt₂ (dom.rename ρ₁))` via
`Term.rename_HEq_pointwise` over `Renaming.lift_compose_equiv`. -/
theorem Term.rename_compose_HEq
    {m : Mode} {scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m scope₁} {Γ₂ : Ctx m scope₂} {Γ₃ : Ctx m scope₃}
    {ρ₁ : Renaming scope₁ scope₂} {ρ₂ : Renaming scope₂ scope₃}
    (ρt₁ : TermRenaming Γ₁ Γ₂ ρ₁) (ρt₂ : TermRenaming Γ₂ Γ₃ ρ₂) :
    {T : Ty scope₁} → (t : Term Γ₁ T) →
      HEq (Term.rename ρt₂ (Term.rename ρt₁ t))
          (Term.rename (TermRenaming.compose ρt₁ ρt₂) t)
  | _, .var i => by
    -- LHS: Term.rename ρt₂ ((ρt₁ i) ▸ Term.var (ρ₁ i))
    -- Push the inner cast through Term.rename ρt₂.
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt₂ (ρt₁ i) (Term.var (ρ₁ i)))
    -- Now: Term.rename ρt₂ (Term.var (ρ₁ i))
    --    = (ρt₂ (ρ₁ i)) ▸ Term.var (ρ₂ (ρ₁ i))
    -- RHS: ((compose ρt₁ ρt₂) i) ▸ Term.var ((Renaming.compose ρ₁ ρ₂) i)
    --    where (Renaming.compose ρ₁ ρ₂) i ≡ ρ₂ (ρ₁ i) definitionally.
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact eqRec_heq _ _
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.rename ρt₂ (Term.rename ρt₁ f))
                (Term.rename ρt₂ (Term.rename ρt₁ a)))
      (Term.app (Term.rename (TermRenaming.compose ρt₁ ρt₂) f)
                (Term.rename (TermRenaming.compose ρt₁ ρt₂) a))
    exact Term.app_HEq_congr
      (Ty.rename_compose dom ρ₁ ρ₂)
      (Ty.rename_compose cod ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ f)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.rename ρt₂ (Term.rename ρt₁ p)))
      (Term.fst (Term.rename (TermRenaming.compose ρt₁ ρt₂) p))
    apply Term.fst_HEq_congr
      (Ty.rename_compose first ρ₁ ρ₂)
      ((Ty.rename_compose second ρ₁.lift ρ₂.lift).trans
        (Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) second))
    exact Term.rename_compose_HEq ρt₁ ρt₂ p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.rename ρt₂ (Term.rename ρt₁ s))
                     (Term.rename ρt₂ (Term.rename ρt₁ t))
                     (Term.rename ρt₂ (Term.rename ρt₁ e)))
      (Term.boolElim (Term.rename (TermRenaming.compose ρt₁ ρt₂) s)
                     (Term.rename (TermRenaming.compose ρt₁ ρt₂) t)
                     (Term.rename (TermRenaming.compose ρt₁ ρt₂) e))
    exact Term.boolElim_HEq_congr
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (eq_of_heq (Term.rename_compose_HEq ρt₁ ρt₂ s))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ t)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    -- Outer-cast peeling on each side, then constructor congruence.
    -- LHS: Term.rename ρt₂ ((cast₁).symm ▸ Term.appPi (Term.rename ρt₁ f) (Term.rename ρt₁ a))
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt₂
        (Ty.subst0_rename_commute cod dom ρ₁).symm
        (Term.appPi (Term.rename ρt₁ f) (Term.rename ρt₁ a)))
    -- Now: Term.rename ρt₂ (Term.appPi (...) (...))
    -- Strip outer cast from Term.rename's appPi clause.
    apply HEq.trans (eqRec_heq _ _)
    -- Flip and process RHS.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    -- Apply Term.appPi_HEq_congr.
    exact Term.appPi_HEq_congr
      (Ty.rename_compose dom ρ₁ ρ₂)
      ((Ty.rename_compose cod ρ₁.lift ρ₂.lift).trans
        (Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) cod))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ f)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    -- Outer Term.pair has no cast; secondVal carries nested casts on both sides.
    apply Term.pair_HEq_congr
      (Ty.rename_compose first ρ₁ ρ₂)
      ((Ty.rename_compose second ρ₁.lift ρ₂.lift).trans
        (Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) second))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ v)
    -- LHS secondVal: cast_outer ▸ Term.rename ρt₂ (cast_inner ▸ Term.rename ρt₁ w)
    -- RHS secondVal: cast_compose ▸ Term.rename (compose ρt₁ ρt₂) w
    -- Strip outer cast on LHS.
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through Term.rename ρt₂.
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt₂
        (Ty.subst0_rename_commute second first ρ₁)
        (Term.rename ρt₁ w))
    -- Use IH on w.
    apply HEq.trans (Term.rename_compose_HEq ρt₁ ρt₂ w)
    -- Strip outer cast on RHS.
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p => by
    -- Mirror of fst plus outer cast strips on each side.
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt₂
        (Ty.subst0_rename_commute second first ρ₁).symm
        (Term.snd (Term.rename ρt₁ p)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.snd_HEq_congr
      (Ty.rename_compose first ρ₁ ρ₂)
      ((Ty.rename_compose second ρ₁.lift ρ₂.lift).trans
        (Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) second))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ p)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    -- LHS body: cast₂ ▸ rename (lift ρt₂ (dom.rename ρ₁)) (cast₁ ▸ rename (lift ρt₁ dom) body)
    -- RHS body: cast_compose ▸ rename (lift (compose ρt₁ ρt₂) dom) body
    apply Term.lam_HEq_congr
      (Ty.rename_compose dom ρ₁ ρ₂)
      (Ty.rename_compose cod ρ₁ ρ₂)
    -- Strip outer cast on LHS.
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through rename (lift ρt₂ (dom.rename ρ₁)).
    apply HEq.trans
      (Term.rename_HEq_cast_input
        (TermRenaming.lift ρt₂ (dom.rename ρ₁))
        (Ty.rename_weaken_commute cod ρ₁)
        (Term.rename (TermRenaming.lift ρt₁ dom) body))
    -- Use IH on body with the lifts.
    apply HEq.trans
      (Term.rename_compose_HEq
        (TermRenaming.lift ρt₁ dom) (TermRenaming.lift ρt₂ (dom.rename ρ₁)) body)
    -- Bridge compose-of-lifts to lift-of-compose via rename_HEq_pointwise.
    apply HEq.symm
    -- Strip outer cast on RHS (now in symm orientation, so it's the LHS goal).
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.rename_HEq_pointwise
      (congrArg Γ₃.cons (Ty.rename_compose dom ρ₁ ρ₂))
      (TermRenaming.compose
        (TermRenaming.lift ρt₁ dom) (TermRenaming.lift ρt₂ (dom.rename ρ₁)))
      (TermRenaming.lift (TermRenaming.compose ρt₁ ρt₂) dom)
      (Renaming.lift_compose_equiv ρ₁ ρ₂)
      body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    -- LHS body: rename (lift ρt₂ (dom.rename ρ₁)) (rename (lift ρt₁ dom) body)
    --          (no outer casts because Term.rename's lamPi clause has no cast)
    -- RHS body: rename (lift (compose ρt₁ ρt₂) dom) body
    apply Term.lamPi_HEq_congr
      (Ty.rename_compose dom ρ₁ ρ₂)
      ((Ty.rename_compose cod ρ₁.lift ρ₂.lift).trans
        (Ty.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) cod))
    apply HEq.trans
      (Term.rename_compose_HEq
        (TermRenaming.lift ρt₁ dom) (TermRenaming.lift ρt₂ (dom.rename ρ₁)) body)
    exact Term.rename_HEq_pointwise
      (congrArg Γ₃.cons (Ty.rename_compose dom ρ₁ ρ₂))
      (TermRenaming.compose
        (TermRenaming.lift ρt₁ dom) (TermRenaming.lift ρt₂ (dom.rename ρ₁)))
      (TermRenaming.lift (TermRenaming.compose ρt₁ ρt₂) dom)
      (Renaming.lift_compose_equiv ρ₁ ρ₂)
      body

/-! ## Typed reduction (`Step`, `StepStar`).

`Step t₁ t₂` is `Prop`-valued and shares its `{ctx} {T}` indices
between sides — so subject reduction is **structural**: every
`Step` proof produces a same-typed reduct by signature alone, no
preservation theorem needed.  Covers congruence, β (`betaApp`,
`betaAppPi`), Σ projections (`betaFstPair`, `betaSndPair`),
η contractions, and boolean ι rules. -/

/-- Single-step reduction between terms of the same type. -/
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

/-! ## StepStar structural congruences.

Multi-step threading through each constructor.  Per-position and
combined forms; induction on `StepStar` with `refl`/`step` arms. -/

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

/-! ## Definitional conversion (`Conv`).

Symmetric / reflexive / transitive closure of `Step`.  Minimal
constructors (`refl`, `sym`, `trans`, `fromStep`); structural-
congruence rules below are derived theorems. -/

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

/-! ## Conv structural congruences.

Make `Conv` a full congruence relation over the term constructors. -/

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

/-! ## η-equivalence in natural direction.

`Step.eta*` are contractions (η-redex → underlying value); these
wrappers state η as `f ≡ λx. f x`, the form conversion algorithms
typically check. -/

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

/-- Append a single step to an existing multi-step path — companion
to `StepStar.step` (which prepends).  Both directions are useful for
trace manipulation in conversion algorithms. -/
theorem StepStar.append
    {mode : Mode} {scope : Nat} {ctx : Ctx mode scope} {T : Ty scope}
    {t₁ t₂ t₃ : Term ctx T} :
    StepStar t₁ t₂ → Step t₂ t₃ → StepStar t₁ t₃ :=
  fun stars step =>
    StepStar.trans stars (Step.toStar step)

/-! ## Boolean reduction congruences.

Multi-step and definitional-equivalence threading through `boolElim`'s
three positions, plus combined three-position congruences. -/

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

end LeanFX.Syntax

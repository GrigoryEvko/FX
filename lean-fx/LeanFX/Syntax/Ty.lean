import LeanFX.Syntax.RawTerm

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

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
inductive Ty : Nat → Nat → Type
  /-- The unit type — polymorphic at any level / scope. -/
  | unit  : {level scope : Nat} → Ty level scope
  /-- Non-dependent function type — domain and codomain at the same
  level and scope. -/
  | arrow : {level scope : Nat} →
            (domain : Ty level scope) →
            (codomain : Ty level scope) →
            Ty level scope
  /-- Dependent function type — codomain at scope `+1`, all parts at
  the same level (uniform-level discipline; v1.30+ adds polymorphic
  levels via universe `max`). -/
  | piTy  : {level scope : Nat} →
            (domain : Ty level scope) →
            (codomain : Ty level (scope + 1)) →
            Ty level scope
  /-- Type-level variable reference. -/
  | tyVar : {level scope : Nat} → (index : Fin scope) → Ty level scope
  /-- Dependent pair type. -/
  | sigmaTy : {level scope : Nat} →
              (firstType : Ty level scope) →
              (secondType : Ty level (scope + 1)) →
              Ty level scope
  /-- Boolean type. -/
  | bool : {level scope : Nat} → Ty level scope
  /-- Universe of small types — `Type<u>` lives at level `u + 1`,
  matching the standard MLTT rule `Type u : Type (u+1)`.

  Encoded with a *level-polymorphic* signature plus a propositional
  witness `levelEq : level = u + 1`.  This sidesteps a Lean pattern-
  elaborator limitation: a constructor whose type rigidly fixes the
  level (e.g. `Ty (u + 1) scope` directly) blocks pattern-form matches
  in any theorem whose goal involves the matched scrutinee through
  `T.subst` / `T.rename`, because the elaborator cannot refine the
  rigid `level` header binder.  Carrying the equation as a propositional
  argument keeps the constructor's level polymorphic; the proposition
  is consumed at use-site (typically `rfl`).

  Cumulativity (`Ty (u+1) → Ty (u+2)`) lands in v1.28; polymorphic Π
  over `Type<u>` lands in v1.29. -/
  | universe : {level scope : Nat} → (u : Nat) → (levelEq : level = u + 1) →
               Ty level scope
  /-- The natural numbers — level-polymorphic since `Nat` makes sense
  at any universe.  Comes with `Term.natZero` (`0`) and `Term.natSucc`
  (`succ`); the case-analysis eliminator `Term.natElim` and ι
  reductions land in the next slice.  No constraints on scope — this
  is a base type. -/
  | nat : {level scope : Nat} → Ty level scope
  /-- Lists over an arbitrary element type.  The first *parametric*
  type constructor in the kernel: the element type `elementType` lives
  at the same level and scope as the resulting list type.  This
  uniform-level discipline keeps substitution well-defined (no
  cumulativity-mismatch issue from v1.29).  Comes with `Term.listNil`
  / `Term.listCons` / `Term.listElim` (and ι rules) in successor
  slices; this commit ships only the type. -/
  | list : {level scope : Nat} → (elementType : Ty level scope) → Ty level scope
  /-- Optional values over an arbitrary element type.  Second
  parametric type — same uniform-level discipline as `list`.  Comes
  with `Term.optionNone` / `Term.optionSome` (single arg) /
  `Term.optionMatch` and ι rules in successor slices. -/
  | option : {level scope : Nat} → (elementType : Ty level scope) → Ty level scope
  /-- Tagged sum (disjoint union) of two element types.  First *binary*
  parametric type in the kernel: both `leftType` and `rightType` live
  at the same level and scope as the result.  Same uniform-level
  discipline as `list` / `option` extended to two indices.  Comes with
  `Term.eitherInl` / `Term.eitherInr` / `Term.eitherMatch` and ι rules
  in successor slices. -/
  | either : {level scope : Nat} →
             (leftType : Ty level scope) →
             (rightType : Ty level scope) →
             Ty level scope
  /-- **Identity type** — propositional equality between two raw
  terms.  The endpoints `lhs` and `rhs` are `RawTerm 0` (closed) in
  this slice; the open-endpoint extension `(lhs rhs : RawTerm scope)`
  requires the joint Subst refactor (v2.3+) since substitution must
  thread through endpoint variable references.

  Closed-endpoint identity types cover canonical examples
  (`Id Bool true true`, `Id Nat (succ zero) (succ zero)`,
  `Id (Bool → Bool) (λx.x) (λx.x)`).  Identity types over bound
  variables (`λ(x y : A). Id A x y`) need the open extension.

  The constructor reuses RawTerm — the substrate landed in v2.2a —
  in argument position, sequentially after RawTerm's full
  declaration.  No mutual block is required: RawTerm is fully
  defined before Ty's inductive declaration begins, so this
  reference is syntactically a forward citation of an existing
  type. -/
  | id : {level scope : Nat} →
         (carrier : Ty level scope) →
         (lhs : RawTerm 0) →
         (rhs : RawTerm 0) →
         Ty level scope

/-! Decidable equality on `Ty` — auto-derives axiom-free because
`Ty`'s indices are bare `Nat`s.  The new `Ty.id` constructor adds
a `RawTerm 0` field which also has decidable equality (auto-derived
below via `deriving instance DecidableEq for RawTerm`). -/
deriving instance DecidableEq for RawTerm
deriving instance DecidableEq for Ty

/-! ## Renaming machinery.

`Renaming source target := Fin source → Fin target`.  `Ty.rename` is
defined first; `Ty.weaken` is then derived as `T.rename Renaming.weaken`
so binders stay binder-aware (the local `tyVar 0` is preserved by
`Renaming.lift`'s var-0 case). -/

/-- A rawRenaming maps `Fin source` indices to `Fin target` indices.
The `Renaming source target` abbreviation makes scope explicit at
both ends, so when the lifted rawRenaming threads through `Ty.rename`'s
recursion the indices line up definitionally. -/
abbrev Renaming (source target : Nat) : Type := Fin source → Fin target

/-- The identity rawRenaming — every variable maps to itself. -/
def Renaming.identity {scope : Nat} : Renaming scope scope := id

/-- Weakening as a rawRenaming — every variable shifts up by one. -/
def Renaming.weaken {scope : Nat} : Renaming scope (scope + 1) := Fin.succ

/-- Lift a rawRenaming under a binder.  Variable 0 stays at 0; variable
`i + 1` maps to `(ρ i).succ`.  Crucially, the lifted rawRenaming has
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

/-- Apply a rawRenaming to a type, structurally.  The `piTy` case lifts
the rawRenaming under the new binder; the recursive call on the codomain
receives a rawRenaming whose source scope is `source + 1` — definitionally
matching the codomain's scope.  No axioms required.

This is the more primitive operation; `Ty.weaken` is derived from it. -/
def Ty.rename {level source target : Nat} :
    Ty level source → Renaming source target → Ty level target
  | .unit, _          => .unit
  | .arrow A B, ρ     => .arrow (A.rename ρ) (B.rename ρ)
  | .piTy A B, ρ      => .piTy (A.rename ρ) (B.rename ρ.lift)
  | .tyVar i, ρ       => .tyVar (ρ i)
  | .sigmaTy A B, ρ   => .sigmaTy (A.rename ρ) (B.rename ρ.lift)
  | .bool, _          => .bool
  | .universe u h, _  => .universe u h
  | .nat, _           => .nat
  | .list elemType, ρ => .list (elemType.rename ρ)
  | .option elemType, ρ => .option (elemType.rename ρ)
  | .either leftType rightType, ρ =>
      .either (leftType.rename ρ) (rightType.rename ρ)
  | .id carrier lhs rhs, ρ => .id (carrier.rename ρ) lhs rhs

/-! ## Rename composition algebra.

`Ty.rename_congr` and `Ty.rename_compose` proved by direct structural
induction with no dependency on the substitution hierarchy.  This
lets `Ty.weaken := T.rename Renaming.weaken` and the
`Ty.rename_weaken_commute` lemma derive without circularity. -/

/-- Pointwise rawRenaming equivalence.  Two renamings agree if they map
every position to the same target. -/
def Renaming.equiv {s t : Nat} (ρ₁ ρ₂ : Renaming s t) : Prop :=
  ∀ i, ρ₁ i = ρ₂ i

/-- Lifting preserves pointwise rawRenaming equivalence. -/
theorem Renaming.lift_equiv {s t : Nat} {ρ₁ ρ₂ : Renaming s t}
    (h : Renaming.equiv ρ₁ ρ₂) : Renaming.equiv ρ₁.lift ρ₂.lift := fun i =>
  match i with
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, hk⟩ =>
      congrArg Fin.succ (h ⟨k, Nat.lt_of_succ_lt_succ hk⟩)

/-- Pointwise-equivalent renamings produce equal results on every
type.  Direct structural induction on `Ty`, using `Renaming.lift_equiv`
for the binder cases.  No subst infrastructure required. -/
theorem Ty.rename_congr {level s t : Nat} {ρ₁ ρ₂ : Renaming s t}
    (h : Renaming.equiv ρ₁ ρ₂) :
    ∀ T : Ty level s, T.rename ρ₁ = T.rename ρ₂
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
  | .universe _ _ => rfl
  | .nat          => rfl
  | .list elemType => by
      show Ty.list (elemType.rename ρ₁) = Ty.list (elemType.rename ρ₂)
      have hElem := Ty.rename_congr h elemType
      exact hElem ▸ rfl
  | .option elemType => by
      show Ty.option (elemType.rename ρ₁) = Ty.option (elemType.rename ρ₂)
      have hElem := Ty.rename_congr h elemType
      exact hElem ▸ rfl
  | .either leftType rightType => by
      show Ty.either (leftType.rename ρ₁) (rightType.rename ρ₁)
         = Ty.either (leftType.rename ρ₂) (rightType.rename ρ₂)
      have hLeft  := Ty.rename_congr h leftType
      have hRight := Ty.rename_congr h rightType
      exact hLeft ▸ hRight ▸ rfl
  | .id carrier lhs rhs => by
      show Ty.id (carrier.rename ρ₁) lhs rhs
         = Ty.id (carrier.rename ρ₂) lhs rhs
      have hCarrier := Ty.rename_congr h carrier
      exact hCarrier ▸ rfl

/-- Compose two renamings: apply `ρ₁` first, then `ρ₂`. -/
def Renaming.compose {s m t : Nat}
    (ρ₁ : Renaming s m) (ρ₂ : Renaming m t) : Renaming s t :=
  fun i => ρ₂ (ρ₁ i)

/-- Lifting commutes with rawRenaming composition (pointwise).  Both Fin
cases reduce to `rfl` thanks to the constructor-only structure of
`Renaming.lift`. -/
theorem Renaming.lift_compose_equiv {s m t : Nat}
    (ρ₁ : Renaming s m) (ρ₂ : Renaming m t) :
    Renaming.equiv (Renaming.compose ρ₁.lift ρ₂.lift)
                   (Renaming.compose ρ₁ ρ₂).lift
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-- Lifting the identity rawRenaming gives the identity at the extended
scope (pointwise).  Renaming-side analogue of `Subst.lift_identity_equiv`.
Both Fin cases reduce to `rfl`: at `⟨0, _⟩` both sides are `⟨0, _⟩`;
at `⟨k+1, h⟩`, `lift Renaming.identity ⟨k+1, h⟩ = Fin.succ (id ⟨k, _⟩) =
⟨k+1, _⟩ = Renaming.identity ⟨k+1, h⟩` modulo Fin proof-irrelevance. -/
theorem Renaming.lift_identity_equiv {scope : Nat} :
    Renaming.equiv (@Renaming.identity scope).lift Renaming.identity
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-- **Renaming composition** at the `Ty` level.  Direct structural
induction on `T`; the binder cases use `Ty.rename_congr` plus
`Renaming.lift_compose_equiv` to bridge the lifted-then-composed and
composed-then-lifted forms. -/
theorem Ty.rename_compose {level s m t : Nat} :
    ∀ (T : Ty level s) (ρ₁ : Renaming s m) (ρ₂ : Renaming m t),
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
  | .universe _ _, _, _ => rfl
  | .nat, _, _ => rfl
  | .list elemType, ρ₁, ρ₂ => by
      show Ty.list ((elemType.rename ρ₁).rename ρ₂)
         = Ty.list (elemType.rename (Renaming.compose ρ₁ ρ₂))
      have hElem := Ty.rename_compose elemType ρ₁ ρ₂
      exact hElem ▸ rfl
  | .option elemType, ρ₁, ρ₂ => by
      show Ty.option ((elemType.rename ρ₁).rename ρ₂)
         = Ty.option (elemType.rename (Renaming.compose ρ₁ ρ₂))
      have hElem := Ty.rename_compose elemType ρ₁ ρ₂
      exact hElem ▸ rfl
  | .either leftType rightType, ρ₁, ρ₂ => by
      show Ty.either ((leftType.rename ρ₁).rename ρ₂)
                     ((rightType.rename ρ₁).rename ρ₂)
         = Ty.either (leftType.rename (Renaming.compose ρ₁ ρ₂))
                     (rightType.rename (Renaming.compose ρ₁ ρ₂))
      have hLeft  := Ty.rename_compose leftType ρ₁ ρ₂
      have hRight := Ty.rename_compose rightType ρ₁ ρ₂
      exact hLeft ▸ hRight ▸ rfl
  | .id carrier lhs rhs, ρ₁, ρ₂ => by
      show Ty.id ((carrier.rename ρ₁).rename ρ₂) lhs rhs
         = Ty.id (carrier.rename (Renaming.compose ρ₁ ρ₂)) lhs rhs
      have hCarrier := Ty.rename_compose carrier ρ₁ ρ₂
      exact hCarrier ▸ rfl

/-- v1.10 principled `Ty.weaken`: defined as `Ty.rename Renaming.weaken`.
Binder-aware in the `piTy`/`sigmaTy` cases — the locally-bound `tyVar 0`
stays fixed via `Renaming.weaken.lift` while outer references shift.
Eliminates the v1.0 latent bug where `(piTy A B).weaken` shifted every
variable in `B`, including the local binder.

Marked `@[reducible]` so Lean's unifier and `rfl` unfold it eagerly. -/
@[reducible]
def Ty.weaken {level scope : Nat} (T : Ty level scope) : Ty level (scope + 1) :=
  T.rename Renaming.weaken

/-- The fundamental rename-weaken commutativity lemma.  Says that
weakening (insert outer binder) commutes with rawRenaming when the
rawRenaming is appropriately lifted.

In v1.10, this is derived from `Ty.rename_compose` plus pointwise
rawRenaming equivalence: both sides become `T.rename` applied to two
renamings that agree pointwise (both equal `Fin.succ ∘ ρ` modulo Fin
proof irrelevance). -/
theorem Ty.rename_weaken_commute {level source target : Nat}
    (T : Ty level source) (ρ : Renaming source target) :
    (T.weaken).rename ρ.lift = (T.rename ρ).weaken := by
  show (T.rename Renaming.weaken).rename ρ.lift
     = (T.rename ρ).rename Renaming.weaken
  have hSwap :
      Renaming.equiv (Renaming.compose Renaming.weaken ρ.lift)
                     (Renaming.compose ρ Renaming.weaken) := fun _ => rfl
  exact (Ty.rename_compose T Renaming.weaken ρ.lift).trans
          ((Ty.rename_congr hSwap T).trans
            (Ty.rename_compose T ρ Renaming.weaken).symm)

/-! ## RawTerm rawRenaming.

`RawTerm` uses the same `Renaming` machinery as `Ty` — purely
positional remapping `Fin source → Fin target`.  Every constructor's
arm just recurses (with `Renaming.lift` under the `lam` binder).
Categorical laws — `rename_congr`, `rename_compose`, `rename_identity`,
`rename_weaken_commute` — mirror their `Ty` counterparts exactly.

Used by the upcoming `Ty.id` arm of `Ty.rename` (v2.2c) to thread
rawRenaming through identity-type endpoints. -/

/-- Apply a rawRenaming to a raw term.  Pattern-form match over each of
the 25 RawTerm constructors; under `lam`'s binder we lift the
rawRenaming so the body's free variables shift correctly. -/
def RawTerm.rename {source target : Nat} :
    RawTerm source → Renaming source target → RawTerm target
  | .var position, ρ        => .var (ρ position)
  | .unit, _                => .unit
  | .boolTrue, _            => .boolTrue
  | .boolFalse, _           => .boolFalse
  | .natZero, _             => .natZero
  | .natSucc predecessor, ρ => .natSucc (RawTerm.rename predecessor ρ)
  | .lam body, ρ            => .lam (RawTerm.rename body ρ.lift)
  | .app function argument, ρ =>
      .app (RawTerm.rename function ρ) (RawTerm.rename argument ρ)
  | .pair first second, ρ =>
      .pair (RawTerm.rename first ρ) (RawTerm.rename second ρ)
  | .fst pairTerm, ρ        => .fst (RawTerm.rename pairTerm ρ)
  | .snd pairTerm, ρ        => .snd (RawTerm.rename pairTerm ρ)
  | .boolElim scrutinee thenBranch elseBranch, ρ =>
      .boolElim
        (RawTerm.rename scrutinee ρ)
        (RawTerm.rename thenBranch ρ)
        (RawTerm.rename elseBranch ρ)
  | .natElim scrutinee zeroBranch succBranch, ρ =>
      .natElim
        (RawTerm.rename scrutinee ρ)
        (RawTerm.rename zeroBranch ρ)
        (RawTerm.rename succBranch ρ)
  | .natRec scrutinee zeroBranch succBranch, ρ =>
      .natRec
        (RawTerm.rename scrutinee ρ)
        (RawTerm.rename zeroBranch ρ)
        (RawTerm.rename succBranch ρ)
  | .listNil, _             => .listNil
  | .listCons head tail, ρ =>
      .listCons (RawTerm.rename head ρ) (RawTerm.rename tail ρ)
  | .listElim scrutinee nilBranch consBranch, ρ =>
      .listElim
        (RawTerm.rename scrutinee ρ)
        (RawTerm.rename nilBranch ρ)
        (RawTerm.rename consBranch ρ)
  | .optionNone, _          => .optionNone
  | .optionSome value, ρ    => .optionSome (RawTerm.rename value ρ)
  | .optionMatch scrutinee noneBranch someBranch, ρ =>
      .optionMatch
        (RawTerm.rename scrutinee ρ)
        (RawTerm.rename noneBranch ρ)
        (RawTerm.rename someBranch ρ)
  | .eitherInl value, ρ     => .eitherInl (RawTerm.rename value ρ)
  | .eitherInr value, ρ     => .eitherInr (RawTerm.rename value ρ)
  | .eitherMatch scrutinee leftBranch rightBranch, ρ =>
      .eitherMatch
        (RawTerm.rename scrutinee ρ)
        (RawTerm.rename leftBranch ρ)
        (RawTerm.rename rightBranch ρ)
  | .refl term, ρ           => .refl (RawTerm.rename term ρ)
  | .idJ baseCase witness, ρ =>
      .idJ (RawTerm.rename baseCase ρ) (RawTerm.rename witness ρ)

/-- Pointwise-equivalent renamings produce equal results on every
raw term.  Same pattern as `Ty.rename_congr` — direct structural
induction with `Renaming.lift_equiv` for the binder case. -/
theorem RawTerm.rename_congr {s t : Nat} {ρ₁ ρ₂ : Renaming s t}
    (h : Renaming.equiv ρ₁ ρ₂) :
    ∀ rawTerm : RawTerm s, rawTerm.rename ρ₁ = rawTerm.rename ρ₂
  | .var position => congrArg RawTerm.var (h position)
  | .unit         => rfl
  | .boolTrue     => rfl
  | .boolFalse    => rfl
  | .natZero      => rfl
  | .natSucc predecessor => by
      have hPred := RawTerm.rename_congr h predecessor
      show RawTerm.natSucc (RawTerm.rename predecessor ρ₁)
         = RawTerm.natSucc (RawTerm.rename predecessor ρ₂)
      exact hPred ▸ rfl
  | .lam body => by
      have hBody := RawTerm.rename_congr (Renaming.lift_equiv h) body
      show RawTerm.lam (RawTerm.rename body ρ₁.lift)
         = RawTerm.lam (RawTerm.rename body ρ₂.lift)
      exact hBody ▸ rfl
  | .app function argument => by
      have hFunc := RawTerm.rename_congr h function
      have hArg  := RawTerm.rename_congr h argument
      show RawTerm.app (RawTerm.rename function ρ₁)
                       (RawTerm.rename argument ρ₁)
         = RawTerm.app (RawTerm.rename function ρ₂)
                       (RawTerm.rename argument ρ₂)
      exact hFunc ▸ hArg ▸ rfl
  | .pair first second => by
      have hFirst  := RawTerm.rename_congr h first
      have hSecond := RawTerm.rename_congr h second
      show RawTerm.pair (RawTerm.rename first ρ₁)
                        (RawTerm.rename second ρ₁)
         = RawTerm.pair (RawTerm.rename first ρ₂)
                        (RawTerm.rename second ρ₂)
      exact hFirst ▸ hSecond ▸ rfl
  | .fst pairTerm => by
      have hPair := RawTerm.rename_congr h pairTerm
      show RawTerm.fst (RawTerm.rename pairTerm ρ₁)
         = RawTerm.fst (RawTerm.rename pairTerm ρ₂)
      exact hPair ▸ rfl
  | .snd pairTerm => by
      have hPair := RawTerm.rename_congr h pairTerm
      show RawTerm.snd (RawTerm.rename pairTerm ρ₁)
         = RawTerm.snd (RawTerm.rename pairTerm ρ₂)
      exact hPair ▸ rfl
  | .boolElim scrutinee thenBranch elseBranch => by
      have hScr  := RawTerm.rename_congr h scrutinee
      have hThen := RawTerm.rename_congr h thenBranch
      have hElse := RawTerm.rename_congr h elseBranch
      show RawTerm.boolElim
             (RawTerm.rename scrutinee ρ₁)
             (RawTerm.rename thenBranch ρ₁)
             (RawTerm.rename elseBranch ρ₁)
         = RawTerm.boolElim
             (RawTerm.rename scrutinee ρ₂)
             (RawTerm.rename thenBranch ρ₂)
             (RawTerm.rename elseBranch ρ₂)
      exact hScr ▸ hThen ▸ hElse ▸ rfl
  | .natElim scrutinee zeroBranch succBranch => by
      have hScr  := RawTerm.rename_congr h scrutinee
      have hZero := RawTerm.rename_congr h zeroBranch
      have hSucc := RawTerm.rename_congr h succBranch
      show RawTerm.natElim
             (RawTerm.rename scrutinee ρ₁)
             (RawTerm.rename zeroBranch ρ₁)
             (RawTerm.rename succBranch ρ₁)
         = RawTerm.natElim
             (RawTerm.rename scrutinee ρ₂)
             (RawTerm.rename zeroBranch ρ₂)
             (RawTerm.rename succBranch ρ₂)
      exact hScr ▸ hZero ▸ hSucc ▸ rfl
  | .natRec scrutinee zeroBranch succBranch => by
      have hScr  := RawTerm.rename_congr h scrutinee
      have hZero := RawTerm.rename_congr h zeroBranch
      have hSucc := RawTerm.rename_congr h succBranch
      show RawTerm.natRec
             (RawTerm.rename scrutinee ρ₁)
             (RawTerm.rename zeroBranch ρ₁)
             (RawTerm.rename succBranch ρ₁)
         = RawTerm.natRec
             (RawTerm.rename scrutinee ρ₂)
             (RawTerm.rename zeroBranch ρ₂)
             (RawTerm.rename succBranch ρ₂)
      exact hScr ▸ hZero ▸ hSucc ▸ rfl
  | .listNil => rfl
  | .listCons head tail => by
      have hHead := RawTerm.rename_congr h head
      have hTail := RawTerm.rename_congr h tail
      show RawTerm.listCons (RawTerm.rename head ρ₁)
                            (RawTerm.rename tail ρ₁)
         = RawTerm.listCons (RawTerm.rename head ρ₂)
                            (RawTerm.rename tail ρ₂)
      exact hHead ▸ hTail ▸ rfl
  | .listElim scrutinee nilBranch consBranch => by
      have hScr  := RawTerm.rename_congr h scrutinee
      have hNil  := RawTerm.rename_congr h nilBranch
      have hCons := RawTerm.rename_congr h consBranch
      show RawTerm.listElim
             (RawTerm.rename scrutinee ρ₁)
             (RawTerm.rename nilBranch ρ₁)
             (RawTerm.rename consBranch ρ₁)
         = RawTerm.listElim
             (RawTerm.rename scrutinee ρ₂)
             (RawTerm.rename nilBranch ρ₂)
             (RawTerm.rename consBranch ρ₂)
      exact hScr ▸ hNil ▸ hCons ▸ rfl
  | .optionNone => rfl
  | .optionSome value => by
      have hValue := RawTerm.rename_congr h value
      show RawTerm.optionSome (RawTerm.rename value ρ₁)
         = RawTerm.optionSome (RawTerm.rename value ρ₂)
      exact hValue ▸ rfl
  | .optionMatch scrutinee noneBranch someBranch => by
      have hScr  := RawTerm.rename_congr h scrutinee
      have hNone := RawTerm.rename_congr h noneBranch
      have hSome := RawTerm.rename_congr h someBranch
      show RawTerm.optionMatch
             (RawTerm.rename scrutinee ρ₁)
             (RawTerm.rename noneBranch ρ₁)
             (RawTerm.rename someBranch ρ₁)
         = RawTerm.optionMatch
             (RawTerm.rename scrutinee ρ₂)
             (RawTerm.rename noneBranch ρ₂)
             (RawTerm.rename someBranch ρ₂)
      exact hScr ▸ hNone ▸ hSome ▸ rfl
  | .eitherInl value => by
      have hValue := RawTerm.rename_congr h value
      show RawTerm.eitherInl (RawTerm.rename value ρ₁)
         = RawTerm.eitherInl (RawTerm.rename value ρ₂)
      exact hValue ▸ rfl
  | .eitherInr value => by
      have hValue := RawTerm.rename_congr h value
      show RawTerm.eitherInr (RawTerm.rename value ρ₁)
         = RawTerm.eitherInr (RawTerm.rename value ρ₂)
      exact hValue ▸ rfl
  | .eitherMatch scrutinee leftBranch rightBranch => by
      have hScr   := RawTerm.rename_congr h scrutinee
      have hLeft  := RawTerm.rename_congr h leftBranch
      have hRight := RawTerm.rename_congr h rightBranch
      show RawTerm.eitherMatch
             (RawTerm.rename scrutinee ρ₁)
             (RawTerm.rename leftBranch ρ₁)
             (RawTerm.rename rightBranch ρ₁)
         = RawTerm.eitherMatch
             (RawTerm.rename scrutinee ρ₂)
             (RawTerm.rename leftBranch ρ₂)
             (RawTerm.rename rightBranch ρ₂)
      exact hScr ▸ hLeft ▸ hRight ▸ rfl
  | .refl term => by
      have hTerm := RawTerm.rename_congr h term
      show RawTerm.refl (RawTerm.rename term ρ₁)
         = RawTerm.refl (RawTerm.rename term ρ₂)
      exact hTerm ▸ rfl
  | .idJ baseCase witness => by
      have hBase    := RawTerm.rename_congr h baseCase
      have hWitness := RawTerm.rename_congr h witness
      show RawTerm.idJ (RawTerm.rename baseCase ρ₁)
                       (RawTerm.rename witness ρ₁)
         = RawTerm.idJ (RawTerm.rename baseCase ρ₂)
                       (RawTerm.rename witness ρ₂)
      exact hBase ▸ hWitness ▸ rfl

/-- Renaming composition law for raw terms.  Same shape as
`Ty.rename_compose`; `lam` arm uses `Renaming.lift_compose_equiv` to
bridge `(lift ρ₁; lift ρ₂)` with `lift (ρ₁; ρ₂)`. -/
theorem RawTerm.rename_compose {s m t : Nat} :
    ∀ (rawTerm : RawTerm s) (ρ₁ : Renaming s m) (ρ₂ : Renaming m t),
      (rawTerm.rename ρ₁).rename ρ₂
        = rawTerm.rename (Renaming.compose ρ₁ ρ₂)
  | .var _, _, _   => rfl
  | .unit, _, _    => rfl
  | .boolTrue, _, _ => rfl
  | .boolFalse, _, _ => rfl
  | .natZero, _, _ => rfl
  | .natSucc predecessor, ρ₁, ρ₂ => by
      have hPred := RawTerm.rename_compose predecessor ρ₁ ρ₂
      show RawTerm.natSucc ((RawTerm.rename predecessor ρ₁).rename ρ₂)
         = RawTerm.natSucc
             (RawTerm.rename predecessor (Renaming.compose ρ₁ ρ₂))
      exact hPred ▸ rfl
  | .lam body, ρ₁, ρ₂ => by
      have hBody := RawTerm.rename_compose body ρ₁.lift ρ₂.lift
      have hLift :=
        RawTerm.rename_congr (Renaming.lift_compose_equiv ρ₁ ρ₂) body
      show RawTerm.lam ((RawTerm.rename body ρ₁.lift).rename ρ₂.lift)
         = RawTerm.lam
             (RawTerm.rename body (Renaming.compose ρ₁ ρ₂).lift)
      exact (hBody.trans hLift) ▸ rfl
  | .app function argument, ρ₁, ρ₂ => by
      have hFunc := RawTerm.rename_compose function ρ₁ ρ₂
      have hArg  := RawTerm.rename_compose argument ρ₁ ρ₂
      show RawTerm.app
             ((RawTerm.rename function ρ₁).rename ρ₂)
             ((RawTerm.rename argument ρ₁).rename ρ₂)
         = RawTerm.app
             (RawTerm.rename function (Renaming.compose ρ₁ ρ₂))
             (RawTerm.rename argument (Renaming.compose ρ₁ ρ₂))
      exact hFunc ▸ hArg ▸ rfl
  | .pair first second, ρ₁, ρ₂ => by
      have hFirst  := RawTerm.rename_compose first ρ₁ ρ₂
      have hSecond := RawTerm.rename_compose second ρ₁ ρ₂
      show RawTerm.pair
             ((RawTerm.rename first ρ₁).rename ρ₂)
             ((RawTerm.rename second ρ₁).rename ρ₂)
         = RawTerm.pair
             (RawTerm.rename first (Renaming.compose ρ₁ ρ₂))
             (RawTerm.rename second (Renaming.compose ρ₁ ρ₂))
      exact hFirst ▸ hSecond ▸ rfl
  | .fst pairTerm, ρ₁, ρ₂ => by
      have hPair := RawTerm.rename_compose pairTerm ρ₁ ρ₂
      show RawTerm.fst ((RawTerm.rename pairTerm ρ₁).rename ρ₂)
         = RawTerm.fst
             (RawTerm.rename pairTerm (Renaming.compose ρ₁ ρ₂))
      exact hPair ▸ rfl
  | .snd pairTerm, ρ₁, ρ₂ => by
      have hPair := RawTerm.rename_compose pairTerm ρ₁ ρ₂
      show RawTerm.snd ((RawTerm.rename pairTerm ρ₁).rename ρ₂)
         = RawTerm.snd
             (RawTerm.rename pairTerm (Renaming.compose ρ₁ ρ₂))
      exact hPair ▸ rfl
  | .boolElim scrutinee thenBranch elseBranch, ρ₁, ρ₂ => by
      have hScr  := RawTerm.rename_compose scrutinee ρ₁ ρ₂
      have hThen := RawTerm.rename_compose thenBranch ρ₁ ρ₂
      have hElse := RawTerm.rename_compose elseBranch ρ₁ ρ₂
      show RawTerm.boolElim
             ((RawTerm.rename scrutinee ρ₁).rename ρ₂)
             ((RawTerm.rename thenBranch ρ₁).rename ρ₂)
             ((RawTerm.rename elseBranch ρ₁).rename ρ₂)
         = RawTerm.boolElim
             (RawTerm.rename scrutinee (Renaming.compose ρ₁ ρ₂))
             (RawTerm.rename thenBranch (Renaming.compose ρ₁ ρ₂))
             (RawTerm.rename elseBranch (Renaming.compose ρ₁ ρ₂))
      exact hScr ▸ hThen ▸ hElse ▸ rfl
  | .natElim scrutinee zeroBranch succBranch, ρ₁, ρ₂ => by
      have hScr  := RawTerm.rename_compose scrutinee ρ₁ ρ₂
      have hZero := RawTerm.rename_compose zeroBranch ρ₁ ρ₂
      have hSucc := RawTerm.rename_compose succBranch ρ₁ ρ₂
      show RawTerm.natElim
             ((RawTerm.rename scrutinee ρ₁).rename ρ₂)
             ((RawTerm.rename zeroBranch ρ₁).rename ρ₂)
             ((RawTerm.rename succBranch ρ₁).rename ρ₂)
         = RawTerm.natElim
             (RawTerm.rename scrutinee (Renaming.compose ρ₁ ρ₂))
             (RawTerm.rename zeroBranch (Renaming.compose ρ₁ ρ₂))
             (RawTerm.rename succBranch (Renaming.compose ρ₁ ρ₂))
      exact hScr ▸ hZero ▸ hSucc ▸ rfl
  | .natRec scrutinee zeroBranch succBranch, ρ₁, ρ₂ => by
      have hScr  := RawTerm.rename_compose scrutinee ρ₁ ρ₂
      have hZero := RawTerm.rename_compose zeroBranch ρ₁ ρ₂
      have hSucc := RawTerm.rename_compose succBranch ρ₁ ρ₂
      show RawTerm.natRec
             ((RawTerm.rename scrutinee ρ₁).rename ρ₂)
             ((RawTerm.rename zeroBranch ρ₁).rename ρ₂)
             ((RawTerm.rename succBranch ρ₁).rename ρ₂)
         = RawTerm.natRec
             (RawTerm.rename scrutinee (Renaming.compose ρ₁ ρ₂))
             (RawTerm.rename zeroBranch (Renaming.compose ρ₁ ρ₂))
             (RawTerm.rename succBranch (Renaming.compose ρ₁ ρ₂))
      exact hScr ▸ hZero ▸ hSucc ▸ rfl
  | .listNil, _, _ => rfl
  | .listCons head tail, ρ₁, ρ₂ => by
      have hHead := RawTerm.rename_compose head ρ₁ ρ₂
      have hTail := RawTerm.rename_compose tail ρ₁ ρ₂
      show RawTerm.listCons
             ((RawTerm.rename head ρ₁).rename ρ₂)
             ((RawTerm.rename tail ρ₁).rename ρ₂)
         = RawTerm.listCons
             (RawTerm.rename head (Renaming.compose ρ₁ ρ₂))
             (RawTerm.rename tail (Renaming.compose ρ₁ ρ₂))
      exact hHead ▸ hTail ▸ rfl
  | .listElim scrutinee nilBranch consBranch, ρ₁, ρ₂ => by
      have hScr  := RawTerm.rename_compose scrutinee ρ₁ ρ₂
      have hNil  := RawTerm.rename_compose nilBranch ρ₁ ρ₂
      have hCons := RawTerm.rename_compose consBranch ρ₁ ρ₂
      show RawTerm.listElim
             ((RawTerm.rename scrutinee ρ₁).rename ρ₂)
             ((RawTerm.rename nilBranch ρ₁).rename ρ₂)
             ((RawTerm.rename consBranch ρ₁).rename ρ₂)
         = RawTerm.listElim
             (RawTerm.rename scrutinee (Renaming.compose ρ₁ ρ₂))
             (RawTerm.rename nilBranch (Renaming.compose ρ₁ ρ₂))
             (RawTerm.rename consBranch (Renaming.compose ρ₁ ρ₂))
      exact hScr ▸ hNil ▸ hCons ▸ rfl
  | .optionNone, _, _ => rfl
  | .optionSome value, ρ₁, ρ₂ => by
      have hValue := RawTerm.rename_compose value ρ₁ ρ₂
      show RawTerm.optionSome ((RawTerm.rename value ρ₁).rename ρ₂)
         = RawTerm.optionSome
             (RawTerm.rename value (Renaming.compose ρ₁ ρ₂))
      exact hValue ▸ rfl
  | .optionMatch scrutinee noneBranch someBranch, ρ₁, ρ₂ => by
      have hScr  := RawTerm.rename_compose scrutinee ρ₁ ρ₂
      have hNone := RawTerm.rename_compose noneBranch ρ₁ ρ₂
      have hSome := RawTerm.rename_compose someBranch ρ₁ ρ₂
      show RawTerm.optionMatch
             ((RawTerm.rename scrutinee ρ₁).rename ρ₂)
             ((RawTerm.rename noneBranch ρ₁).rename ρ₂)
             ((RawTerm.rename someBranch ρ₁).rename ρ₂)
         = RawTerm.optionMatch
             (RawTerm.rename scrutinee (Renaming.compose ρ₁ ρ₂))
             (RawTerm.rename noneBranch (Renaming.compose ρ₁ ρ₂))
             (RawTerm.rename someBranch (Renaming.compose ρ₁ ρ₂))
      exact hScr ▸ hNone ▸ hSome ▸ rfl
  | .eitherInl value, ρ₁, ρ₂ => by
      have hValue := RawTerm.rename_compose value ρ₁ ρ₂
      show RawTerm.eitherInl ((RawTerm.rename value ρ₁).rename ρ₂)
         = RawTerm.eitherInl
             (RawTerm.rename value (Renaming.compose ρ₁ ρ₂))
      exact hValue ▸ rfl
  | .eitherInr value, ρ₁, ρ₂ => by
      have hValue := RawTerm.rename_compose value ρ₁ ρ₂
      show RawTerm.eitherInr ((RawTerm.rename value ρ₁).rename ρ₂)
         = RawTerm.eitherInr
             (RawTerm.rename value (Renaming.compose ρ₁ ρ₂))
      exact hValue ▸ rfl
  | .eitherMatch scrutinee leftBranch rightBranch, ρ₁, ρ₂ => by
      have hScr   := RawTerm.rename_compose scrutinee ρ₁ ρ₂
      have hLeft  := RawTerm.rename_compose leftBranch ρ₁ ρ₂
      have hRight := RawTerm.rename_compose rightBranch ρ₁ ρ₂
      show RawTerm.eitherMatch
             ((RawTerm.rename scrutinee ρ₁).rename ρ₂)
             ((RawTerm.rename leftBranch ρ₁).rename ρ₂)
             ((RawTerm.rename rightBranch ρ₁).rename ρ₂)
         = RawTerm.eitherMatch
             (RawTerm.rename scrutinee (Renaming.compose ρ₁ ρ₂))
             (RawTerm.rename leftBranch (Renaming.compose ρ₁ ρ₂))
             (RawTerm.rename rightBranch (Renaming.compose ρ₁ ρ₂))
      exact hScr ▸ hLeft ▸ hRight ▸ rfl
  | .refl term, ρ₁, ρ₂ => by
      have hTerm := RawTerm.rename_compose term ρ₁ ρ₂
      show RawTerm.refl ((RawTerm.rename term ρ₁).rename ρ₂)
         = RawTerm.refl
             (RawTerm.rename term (Renaming.compose ρ₁ ρ₂))
      exact hTerm ▸ rfl
  | .idJ baseCase witness, ρ₁, ρ₂ => by
      have hBase    := RawTerm.rename_compose baseCase ρ₁ ρ₂
      have hWitness := RawTerm.rename_compose witness ρ₁ ρ₂
      show RawTerm.idJ ((RawTerm.rename baseCase ρ₁).rename ρ₂)
                       ((RawTerm.rename witness ρ₁).rename ρ₂)
         = RawTerm.idJ
             (RawTerm.rename baseCase (Renaming.compose ρ₁ ρ₂))
             (RawTerm.rename witness (Renaming.compose ρ₁ ρ₂))
      exact hBase ▸ hWitness ▸ rfl

/-- v2.2b weakening on raw terms — derived from rename. -/
@[reducible]
def RawTerm.weaken {scope : Nat}
    (rawTerm : RawTerm scope) : RawTerm (scope + 1) :=
  rawTerm.rename Renaming.weaken

/-- Weakening commutes with rawRenaming on raw terms — same proof
shape as `Ty.rename_weaken_commute`. -/
theorem RawTerm.rename_weaken_commute {source target : Nat}
    (rawTerm : RawTerm source) (ρ : Renaming source target) :
    (rawTerm.weaken).rename ρ.lift = (rawTerm.rename ρ).weaken := by
  show (rawTerm.rename Renaming.weaken).rename ρ.lift
     = (rawTerm.rename ρ).rename Renaming.weaken
  have hSwap :
      Renaming.equiv (Renaming.compose Renaming.weaken ρ.lift)
                     (Renaming.compose ρ Renaming.weaken) := fun _ => rfl
  exact (RawTerm.rename_compose rawTerm Renaming.weaken ρ.lift).trans
          ((RawTerm.rename_congr hSwap rawTerm).trans
            (RawTerm.rename_compose rawTerm ρ Renaming.weaken).symm)

/-- **Iterated weakening of a closed raw term** — embed `RawTerm 0` into
`RawTerm target` for any target scope.  Used by `Term.toRaw` (v2.2j) to
lift `Term.refl`'s closed-endpoint `rawTerm` into the surrounding
context's scope.

Semantically a no-op (`RawTerm 0` has no free variables to shift), but
required as a constructive function because Lean's type system insists
on an explicit witness.  Iterates `RawTerm.weaken` exactly `target`
times via structural recursion on `target` — zero axioms. -/
def RawTerm.weakenToScope : (target : Nat) → RawTerm 0 → RawTerm target
  | 0,         rawTerm => rawTerm
  | step + 1,  rawTerm => (RawTerm.weakenToScope step rawTerm).weaken

end LeanFX.Syntax

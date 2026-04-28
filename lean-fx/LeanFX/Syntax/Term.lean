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

/-! Section-scope universe-level variable.  Auto-injected as an
implicit binder into theorems whose signatures lexically mention
`level` (which, after the v1.27 refactor, includes most theorems
about `Ty`, `Subst`, `Ctx`, `Term`, `TermRenaming`, or `TermSubst`). -/
variable {level : Nat}

/-! ## Raw syntax — well-scoped, type-erased terms.

`RawTerm` is the substrate for identity types.  Defined here, BEFORE
`Ty`, so the upcoming `Ty.id` constructor (v2.2c) can reference it
in *constructor argument position* — Lean 4's elaborator admits this
sequential pattern without requiring a mutual block (see
`feedback_lean_mutual_index_rule.md`).

## Why raw, not intrinsic, endpoints

Identity types `Id A a b : Type` need `a` and `b` to inhabit the
SAME Ty constructor as the carrier `A`.  In Lean 4's intrinsic kernel
this would require `Ty` to mention `Term`, which would require
mutual elaboration — and Lean's mutual-index rule blocks
`Term : (Γ : Ctx) → Ty Γ → Type` siblings of `Ty`.  Defining
`RawTerm : Nat → Type` independently (no `Ty` index) sidesteps this:
`Ty.id` can carry raw endpoints, and the bridge `Term.toRaw : Term Γ T →
RawTerm scope` (v2.2j) makes the raw-vs-intrinsic distinction
invisible at the surface.

This is the standard pattern in MLTT formalisations: identity types'
endpoints live in raw syntax stratified from the intrinsic-typing
discipline of the rest of the kernel.  Coq, Agda, and prior Lean 4
formalisations (lean4-tt-in-lean4, the BiSikkel reference) all
follow this design.

## Constructor parity with intrinsic `Term`

Every intrinsic-`Term` constructor has a raw counterpart, modulo
type erasure: `lam`/`lamPi` collapse into a single Curry-style
`RawTerm.lam` (no domain annotation); `app`/`appPi` likewise unify
into `RawTerm.app`.  This means `Term.toRaw` (v2.2j) is a
syntactic walk that loses only the Ty-level annotations, not
the behavioural shape.

Variable references use the same de-Bruijn `Fin scope` discipline
as the intrinsic kernel; `RawTerm.rename` and `RawTerm.subst`
(v2.2b/v2.2f) operate via the existing `Renaming` / `Subst`
machinery extended jointly with the Ty side. -/
inductive RawTerm : Nat → Type
  /-- Variable reference (de Bruijn). -/
  | var : {scope : Nat} → (position : Fin scope) → RawTerm scope
  /-- Unit value `()`. -/
  | unit : {scope : Nat} → RawTerm scope
  /-- Boolean `true`. -/
  | boolTrue : {scope : Nat} → RawTerm scope
  /-- Boolean `false`. -/
  | boolFalse : {scope : Nat} → RawTerm scope
  /-- Natural-number `0`. -/
  | natZero : {scope : Nat} → RawTerm scope
  /-- Natural-number `succ predecessor`. -/
  | natSucc : {scope : Nat} → (predecessor : RawTerm scope) → RawTerm scope
  /-- λ-abstraction (Curry-style — no domain annotation; intrinsic
  `Term.lam` and `Term.lamPi` both translate here via `Term.toRaw`). -/
  | lam : {scope : Nat} → (body : RawTerm (scope + 1)) → RawTerm scope
  /-- Application (covers both arrow and Π applications). -/
  | app : {scope : Nat} →
          (function : RawTerm scope) →
          (argument : RawTerm scope) →
          RawTerm scope
  /-- Σ-pair construction. -/
  | pair : {scope : Nat} →
           (first : RawTerm scope) →
           (second : RawTerm scope) →
           RawTerm scope
  /-- First projection of a Σ-pair. -/
  | fst : {scope : Nat} → (pair : RawTerm scope) → RawTerm scope
  /-- Second projection of a Σ-pair. -/
  | snd : {scope : Nat} → (pair : RawTerm scope) → RawTerm scope
  /-- Boolean elimination (case on `true` / `false`). -/
  | boolElim : {scope : Nat} →
               (scrutinee : RawTerm scope) →
               (thenBranch : RawTerm scope) →
               (elseBranch : RawTerm scope) →
               RawTerm scope
  /-- Natural-number case-analysis eliminator. -/
  | natElim : {scope : Nat} →
              (scrutinee : RawTerm scope) →
              (zeroBranch : RawTerm scope) →
              (succBranch : RawTerm scope) →
              RawTerm scope
  /-- Natural-number primitive recursion (succBranch sees both
  predecessor and IH). -/
  | natRec : {scope : Nat} →
             (scrutinee : RawTerm scope) →
             (zeroBranch : RawTerm scope) →
             (succBranch : RawTerm scope) →
             RawTerm scope
  /-- Empty list. -/
  | listNil : {scope : Nat} → RawTerm scope
  /-- List cons. -/
  | listCons : {scope : Nat} →
               (head : RawTerm scope) →
               (tail : RawTerm scope) →
               RawTerm scope
  /-- List case-analysis eliminator. -/
  | listElim : {scope : Nat} →
               (scrutinee : RawTerm scope) →
               (nilBranch : RawTerm scope) →
               (consBranch : RawTerm scope) →
               RawTerm scope
  /-- Empty option (`none`). -/
  | optionNone : {scope : Nat} → RawTerm scope
  /-- Option wrap (`some value`). -/
  | optionSome : {scope : Nat} → (value : RawTerm scope) → RawTerm scope
  /-- Option case-analysis eliminator. -/
  | optionMatch : {scope : Nat} →
                  (scrutinee : RawTerm scope) →
                  (noneBranch : RawTerm scope) →
                  (someBranch : RawTerm scope) →
                  RawTerm scope
  /-- Sum left-injection (`inl value`). -/
  | eitherInl : {scope : Nat} → (value : RawTerm scope) → RawTerm scope
  /-- Sum right-injection (`inr value`). -/
  | eitherInr : {scope : Nat} → (value : RawTerm scope) → RawTerm scope
  /-- Sum case-analysis eliminator. -/
  | eitherMatch : {scope : Nat} →
                  (scrutinee : RawTerm scope) →
                  (leftBranch : RawTerm scope) →
                  (rightBranch : RawTerm scope) →
                  RawTerm scope
  /-- Reflexivity witness — the introduction form for identity types.
  `RawTerm.refl rt` is the raw form of `Term.refl` (v2.2h); it
  inhabits the Ty.id type whose endpoints are both `rt`. -/
  | refl : {scope : Nat} → (term : RawTerm scope) → RawTerm scope

/-! ### RawTerm smoke tests — every constructor instantiable at scope 0
or scope 1 (for `lam` / `varRef`).  No theorems yet; just constructor
sanity. -/

namespace SmokeTestRaw

/-- `()` at scope 0. -/
example : RawTerm 0 := RawTerm.unit
/-- `true`. -/
example : RawTerm 0 := RawTerm.boolTrue
/-- `false`. -/
example : RawTerm 0 := RawTerm.boolFalse
/-- `0`. -/
example : RawTerm 0 := RawTerm.natZero
/-- `succ 0`. -/
example : RawTerm 0 := RawTerm.natSucc RawTerm.natZero
/-- `λx. x` (Curry; the inner `var` references position 0 of scope 1). -/
example : RawTerm 0 := RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩)
/-- `(λx. x) true`. -/
example : RawTerm 0 :=
  RawTerm.app
    (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
    RawTerm.boolTrue
/-- `(true, 0)`. -/
example : RawTerm 0 := RawTerm.pair RawTerm.boolTrue RawTerm.natZero
/-- `fst (true, 0)`. -/
example : RawTerm 0 :=
  RawTerm.fst (RawTerm.pair RawTerm.boolTrue RawTerm.natZero)
/-- Boolean elimination on `true` returning the `then` branch. -/
example : RawTerm 0 :=
  RawTerm.boolElim RawTerm.boolTrue RawTerm.unit RawTerm.unit
/-- `natElim 0 unit (λn. unit)`. -/
example : RawTerm 0 :=
  RawTerm.natElim RawTerm.natZero RawTerm.unit
    (RawTerm.lam RawTerm.unit)
/-- `natRec` — same shape as `natElim` at the raw level. -/
example : RawTerm 0 :=
  RawTerm.natRec RawTerm.natZero RawTerm.unit
    (RawTerm.lam (RawTerm.lam RawTerm.unit))
/-- Empty list. -/
example : RawTerm 0 := RawTerm.listNil
/-- `[true]`. -/
example : RawTerm 0 := RawTerm.listCons RawTerm.boolTrue RawTerm.listNil
/-- `none`. -/
example : RawTerm 0 := RawTerm.optionNone
/-- `some true`. -/
example : RawTerm 0 := RawTerm.optionSome RawTerm.boolTrue
/-- `inl unit`. -/
example : RawTerm 0 := RawTerm.eitherInl RawTerm.unit
/-- `inr unit`. -/
example : RawTerm 0 := RawTerm.eitherInr RawTerm.unit
/-- `refl(true)` — the load-bearing identity-type substrate.
`RawTerm.refl` is what `Ty.id` (v2.2c) uses as endpoint values. -/
example : RawTerm 0 := RawTerm.refl RawTerm.boolTrue
/-- `refl(refl(true))` — iterated identity. -/
example : RawTerm 0 := RawTerm.refl (RawTerm.refl RawTerm.boolTrue)

end SmokeTestRaw

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

/-- Lifting the identity renaming gives the identity at the extended
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
weakening (insert outer binder) commutes with renaming when the
renaming is appropriately lifted.

In v1.10, this is derived from `Ty.rename_compose` plus pointwise
renaming equivalence: both sides become `T.rename` applied to two
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

/-! ## Substitution — the same trick scaled up.

`Subst level source target` is a function-typed family mapping `Fin source`
to `Ty level target`.  Just as with `Renaming`, the substitution data carries
both endpoints as free parameters; lifting under a binder advances both
to `source + 1` and `target + 1`, definitionally matching the
recursive call's indices.

For v1.0+ `Ty` (no `Ty.tyVar` constructor), `Subst` is never *queried*
by `Ty.subst` — it threads through the recursion as a token.  When
v1.5+ adds `Ty.tyVar`, the `var` case will look up the substituent
via `σ`. -/

/-- Parallel substitution: each `Fin source` index maps to a `Ty level target`
substituent.  Function-typed; `lift` advances source and target in
lockstep. -/
abbrev Subst (level source target : Nat) : Type := Fin source → Ty level target

/-- Lift a substitution under a binder.  Var 0 in the lifted scope is
the freshly-bound variable, represented as `Ty.tyVar 0`.  Var `k + 1`
is the original substituent for `k` weakened to the extended target
scope. -/
def Subst.lift {level source target : Nat} (σ : Subst level source target) :
    Subst level (source + 1) (target + 1)
  | ⟨0, _⟩      => .tyVar ⟨0, Nat.zero_lt_succ _⟩
  | ⟨k + 1, h⟩  => (σ ⟨k, Nat.lt_of_succ_lt_succ h⟩).weaken

/-- Single-variable substitution at the outermost binder: substitute
`substituent` for var 0, leave var `k + 1` as `tyVar k` — the
"identity" mapping that decrements the de Bruijn index by one
(reflecting that the outer scope has one fewer binder than the
input scope). -/
def Subst.singleton {level scope : Nat} (substituent : Ty level scope) :
    Subst level (scope + 1) scope
  | ⟨0, _⟩      => substituent
  | ⟨k + 1, h⟩  => .tyVar ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- Apply a parallel substitution to a type, structurally.  The
`piTy` case lifts the substitution under the new binder; just like
`Ty.rename`, the recursive call's indices are supplied definitionally
by `σ.lift`, no Nat arithmetic identities required.  Axiom-free. -/
def Ty.subst {level source target : Nat} :
    Ty level source → Subst level source target → Ty level target
  | .unit, _          => .unit
  | .arrow A B, σ     => .arrow (Ty.subst A σ) (Ty.subst B σ)
  | .piTy A B, σ      => .piTy (Ty.subst A σ) (Ty.subst B σ.lift)
  | .tyVar i, σ       => σ i
  | .sigmaTy A B, σ   => .sigmaTy (Ty.subst A σ) (Ty.subst B σ.lift)
  | .bool, _          => .bool
  | .universe u h, _  => .universe u h
  | .nat, _           => .nat
  | .list elemType, σ => .list (Ty.subst elemType σ)
  | .option elemType, σ => .option (Ty.subst elemType σ)
  | .either leftType rightType, σ =>
      .either (Ty.subst leftType σ) (Ty.subst rightType σ)

/-- Substitute the outermost variable of a type with a `Ty` value.
Used by `Term.appPi` to compute the result type of dependent
application. -/
def Ty.subst0 {level scope : Nat} (codomain : Ty level (scope + 1))
    (substituent : Ty level scope) : Ty level scope :=
  Ty.subst codomain (Subst.singleton substituent)

/-! ## Substitution-lemma hierarchy.

How `Ty.subst` interacts with `Ty.rename`, with itself, and with
lifting.  All lemmas use pointwise substitution equivalence
(`Subst.equiv`) rather than Lean function-equality — funext would
pull in `propext`. -/

/-- Pointwise equivalence of substitutions.  Two substitutions
`σ₁ σ₂ : Subst level s t` are equivalent if they agree at every variable.
Used in lieu of Lean-level function equality (which would require
`funext` and thus `propext`). -/
def Subst.equiv {level s t : Nat} (σ₁ σ₂ : Subst level s t) : Prop :=
  ∀ i, σ₁ i = σ₂ i

/-- Lifting preserves substitution equivalence: if `σ₁ ≡ σ₂` pointwise
then `σ₁.lift ≡ σ₂.lift` pointwise. -/
theorem Subst.lift_equiv {level s t : Nat} {σ₁ σ₂ : Subst level s t}
    (h : Subst.equiv σ₁ σ₂) : Subst.equiv σ₁.lift σ₂.lift := fun i =>
  match i with
  | ⟨0, _⟩      => rfl
  | ⟨k + 1, hk⟩ =>
      congrArg Ty.weaken (h ⟨k, Nat.lt_of_succ_lt_succ hk⟩)

/-- `Ty.subst` respects substitution equivalence: pointwise-equivalent
substitutions produce equal results.  Proven by structural induction
on `T`, using `Subst.lift_equiv` for the binder cases. -/
theorem Ty.subst_congr {level s t : Nat} {σ₁ σ₂ : Subst level s t}
    (h : Subst.equiv σ₁ σ₂) : ∀ T : Ty level s, T.subst σ₁ = T.subst σ₂
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
  | .universe _ _ => rfl
  | .nat          => rfl
  | .list elemType => by
      show Ty.list (elemType.subst σ₁) = Ty.list (elemType.subst σ₂)
      have hElem := Ty.subst_congr h elemType
      exact hElem ▸ rfl
  | .option elemType => by
      show Ty.option (elemType.subst σ₁) = Ty.option (elemType.subst σ₂)
      have hElem := Ty.subst_congr h elemType
      exact hElem ▸ rfl
  | .either leftType rightType => by
      show Ty.either (leftType.subst σ₁) (rightType.subst σ₁)
         = Ty.either (leftType.subst σ₂) (rightType.subst σ₂)
      have hLeft  := Ty.subst_congr h leftType
      have hRight := Ty.subst_congr h rightType
      exact hLeft ▸ hRight ▸ rfl

/-- Substitution composed with renaming: applies the substitution
first, then renames each substituent.  The "after" naming follows
the order of operations: `renameAfter σ ρ i = (σ i).rename ρ`. -/
def Subst.renameAfter {level s m t : Nat} (σ : Subst level s m) (ρ : Renaming m t) :
    Subst level s t :=
  fun i => (σ i).rename ρ

/-- Lifting commutes with the renameAfter composition (pointwise).
The non-trivial case `i = ⟨k+1, h⟩` reduces to `Ty.rename_weaken_commute`
applied to the substituent `σ ⟨k, _⟩`. -/
theorem Subst.lift_renameAfter_commute {level s m t : Nat}
    (σ : Subst level s m) (ρ : Renaming m t) :
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
theorem Ty.subst_rename_commute {level s m t : Nat} :
    ∀ (T : Ty level s) (σ : Subst level s m) (ρ : Renaming m t),
    (T.subst σ).rename ρ = T.subst (Subst.renameAfter σ ρ)
  | .unit, _, _ => rfl
  | .arrow X Y, σ, ρ => by
      show Ty.arrow ((X.subst σ).rename ρ) ((Y.subst σ).rename ρ)
         = Ty.arrow (X.subst (Subst.renameAfter σ ρ))
                    (Y.subst (Subst.renameAfter σ ρ))
      have hX := Ty.subst_rename_commute X σ ρ
      have hY := Ty.subst_rename_commute Y σ ρ
      exact hX ▸ hY ▸ rfl
  | .piTy X Y, σ, ρ => by
      show Ty.piTy ((X.subst σ).rename ρ) ((Y.subst σ.lift).rename ρ.lift)
         = Ty.piTy (X.subst (Subst.renameAfter σ ρ))
                   (Y.subst (Subst.renameAfter σ ρ).lift)
      have hX := Ty.subst_rename_commute X σ ρ
      have hY := Ty.subst_rename_commute Y σ.lift ρ.lift
      have hCong := Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | .tyVar _, _, _ => rfl
  | .sigmaTy X Y, σ, ρ => by
      show Ty.sigmaTy ((X.subst σ).rename ρ) ((Y.subst σ.lift).rename ρ.lift)
         = Ty.sigmaTy (X.subst (Subst.renameAfter σ ρ))
                      (Y.subst (Subst.renameAfter σ ρ).lift)
      have hX := Ty.subst_rename_commute X σ ρ
      have hY := Ty.subst_rename_commute Y σ.lift ρ.lift
      have hCong := Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | .bool, _, _ => rfl
  | .universe _ _, _, _ => rfl
  | .nat, _, _ => rfl
  | .list elemType, σ, ρ => by
      show Ty.list ((elemType.subst σ).rename ρ)
         = Ty.list (elemType.subst (Subst.renameAfter σ ρ))
      have hElem := Ty.subst_rename_commute elemType σ ρ
      exact hElem ▸ rfl
  | .option elemType, σ, ρ => by
      show Ty.option ((elemType.subst σ).rename ρ)
         = Ty.option (elemType.subst (Subst.renameAfter σ ρ))
      have hElem := Ty.subst_rename_commute elemType σ ρ
      exact hElem ▸ rfl
  | .either leftType rightType, σ, ρ => by
      show Ty.either ((leftType.subst σ).rename ρ)
                     ((rightType.subst σ).rename ρ)
         = Ty.either (leftType.subst (Subst.renameAfter σ ρ))
                     (rightType.subst (Subst.renameAfter σ ρ))
      have hLeft  := Ty.subst_rename_commute leftType σ ρ
      have hRight := Ty.subst_rename_commute rightType σ ρ
      exact hLeft ▸ hRight ▸ rfl

/-- Renaming followed by substitution: precompose the renaming, then
substitute.  `Subst.precompose ρ σ i = σ (ρ i)`. -/
def Subst.precompose {level s m t : Nat} (ρ : Renaming s m) (σ : Subst level m t) :
    Subst level s t :=
  fun i => σ (ρ i)

/-- Lifting commutes with precompose (pointwise).  Both `k = 0` and
`k+1` cases reduce to `rfl` thanks to Fin proof irrelevance. -/
theorem Subst.lift_precompose_commute {level s m t : Nat}
    (ρ : Renaming s m) (σ : Subst level m t) :
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
theorem Ty.rename_subst_commute {level s m t : Nat} :
    ∀ (T : Ty level s) (ρ : Renaming s m) (σ : Subst level m t),
    (T.rename ρ).subst σ = T.subst (Subst.precompose ρ σ)
  | .unit, _, _ => rfl
  | .arrow X Y, ρ, σ => by
      show Ty.arrow ((X.rename ρ).subst σ) ((Y.rename ρ).subst σ)
         = Ty.arrow (X.subst (Subst.precompose ρ σ))
                    (Y.subst (Subst.precompose ρ σ))
      have hX := Ty.rename_subst_commute X ρ σ
      have hY := Ty.rename_subst_commute Y ρ σ
      exact hX ▸ hY ▸ rfl
  | .piTy X Y, ρ, σ => by
      show Ty.piTy ((X.rename ρ).subst σ) ((Y.rename ρ.lift).subst σ.lift)
         = Ty.piTy (X.subst (Subst.precompose ρ σ))
                   (Y.subst (Subst.precompose ρ σ).lift)
      have hX := Ty.rename_subst_commute X ρ σ
      have hY := Ty.rename_subst_commute Y ρ.lift σ.lift
      have hCong := Ty.subst_congr (Subst.lift_precompose_commute ρ σ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | .tyVar _, _, _ => rfl
  | .sigmaTy X Y, ρ, σ => by
      show Ty.sigmaTy ((X.rename ρ).subst σ) ((Y.rename ρ.lift).subst σ.lift)
         = Ty.sigmaTy (X.subst (Subst.precompose ρ σ))
                      (Y.subst (Subst.precompose ρ σ).lift)
      have hX := Ty.rename_subst_commute X ρ σ
      have hY := Ty.rename_subst_commute Y ρ.lift σ.lift
      have hCong := Ty.subst_congr (Subst.lift_precompose_commute ρ σ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | .bool, _, _ => rfl
  | .universe _ _, _, _ => rfl
  | .nat, _, _ => rfl
  | .list elemType, ρ, σ => by
      show Ty.list ((elemType.rename ρ).subst σ)
         = Ty.list (elemType.subst (Subst.precompose ρ σ))
      have hElem := Ty.rename_subst_commute elemType ρ σ
      exact hElem ▸ rfl
  | .option elemType, ρ, σ => by
      show Ty.option ((elemType.rename ρ).subst σ)
         = Ty.option (elemType.subst (Subst.precompose ρ σ))
      have hElem := Ty.rename_subst_commute elemType ρ σ
      exact hElem ▸ rfl
  | .either leftType rightType, ρ, σ => by
      show Ty.either ((leftType.rename ρ).subst σ)
                     ((rightType.rename ρ).subst σ)
         = Ty.either (leftType.subst (Subst.precompose ρ σ))
                     (rightType.subst (Subst.precompose ρ σ))
      have hLeft  := Ty.rename_subst_commute leftType ρ σ
      have hRight := Ty.rename_subst_commute rightType ρ σ
      exact hLeft ▸ hRight ▸ rfl

/-! ## Renaming as a special case of substitution.

A renaming is a substitution whose substituent at each position is a
`tyVar` reference.  All renaming lemmas are derivable from the
corresponding substitution lemmas via this coercion. -/

/-- Coerce a renaming into a substitution: each variable index `ρ i`
becomes the type-variable reference `Ty.tyVar (ρ i)`. -/
def Renaming.toSubst {s t : Nat} (ρ : Renaming s t) : Subst level s t :=
  fun i => Ty.tyVar (ρ i)

/-- Lifting commutes with the renaming-to-substitution coercion
(pointwise).  Both cases reduce to `rfl`. -/
theorem Renaming.lift_toSubst_equiv {s t : Nat} (ρ : Renaming s t) :
    Subst.equiv (Renaming.toSubst (level := level) ρ.lift)
                (Renaming.toSubst (level := level) ρ).lift :=
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
theorem Ty.rename_eq_subst {level s t : Nat} :
    ∀ (T : Ty level s) (ρ : Renaming s t),
    T.rename ρ = T.subst (Renaming.toSubst ρ)
  | .unit, _ => rfl
  | .arrow X Y, ρ => by
      show Ty.arrow (X.rename ρ) (Y.rename ρ)
         = Ty.arrow (X.subst (Renaming.toSubst ρ))
                    (Y.subst (Renaming.toSubst ρ))
      have hX := Ty.rename_eq_subst X ρ
      have hY := Ty.rename_eq_subst Y ρ
      exact hX ▸ hY ▸ rfl
  | .piTy X Y, ρ => by
      show Ty.piTy (X.rename ρ) (Y.rename ρ.lift)
         = Ty.piTy (X.subst (Renaming.toSubst ρ))
                   (Y.subst (Renaming.toSubst ρ).lift)
      have hX := Ty.rename_eq_subst X ρ
      have hY := Ty.rename_eq_subst Y ρ.lift
      have hCong := Ty.subst_congr (Renaming.lift_toSubst_equiv ρ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | .tyVar _, _ => rfl
  | .sigmaTy X Y, ρ => by
      show Ty.sigmaTy (X.rename ρ) (Y.rename ρ.lift)
         = Ty.sigmaTy (X.subst (Renaming.toSubst ρ))
                      (Y.subst (Renaming.toSubst ρ).lift)
      have hX := Ty.rename_eq_subst X ρ
      have hY := Ty.rename_eq_subst Y ρ.lift
      have hCong := Ty.subst_congr (Renaming.lift_toSubst_equiv ρ) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | .bool, _ => rfl
  | .universe _ _, _ => rfl
  | .nat, _ => rfl
  | .list elemType, ρ => by
      show Ty.list (elemType.rename ρ) = Ty.list (elemType.subst (Renaming.toSubst ρ))
      have hElem := Ty.rename_eq_subst elemType ρ
      exact hElem ▸ rfl
  | .option elemType, ρ => by
      show Ty.option (elemType.rename ρ) = Ty.option (elemType.subst (Renaming.toSubst ρ))
      have hElem := Ty.rename_eq_subst elemType ρ
      exact hElem ▸ rfl
  | .either leftType rightType, ρ => by
      show Ty.either (leftType.rename ρ) (rightType.rename ρ)
         = Ty.either (leftType.subst (Renaming.toSubst ρ))
                     (rightType.subst (Renaming.toSubst ρ))
      have hLeft  := Ty.rename_eq_subst leftType ρ
      have hRight := Ty.rename_eq_subst rightType ρ
      exact hLeft ▸ hRight ▸ rfl

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
def Subst.identity {level scope : Nat} : Subst level scope scope := fun i => Ty.tyVar i

/-- Lifting the identity substitution gives the identity at the
extended scope (pointwise).  Both Fin cases are `rfl`. -/
theorem Subst.lift_identity_equiv {level scope : Nat} :
    Subst.equiv (@Subst.identity level scope).lift
                (@Subst.identity level (scope + 1)) := fun i =>
  match i with
  | ⟨0, _⟩      => rfl
  | ⟨_ + 1, _⟩  => rfl

/-- **Identity law for substitution**: `T.subst Subst.identity = T`.
The substitution that maps every variable to itself is the identity
operation on `Ty`.  Proven by structural induction on `T`, using
`.symm ▸` to rewrite the goal toward `rfl`. -/
theorem Ty.subst_id {level scope : Nat} :
    ∀ (T : Ty level scope), T.subst Subst.identity = T
  | .unit => rfl
  | .arrow X Y => by
      have hX := Ty.subst_id X
      have hY := Ty.subst_id Y
      show (X.subst Subst.identity).arrow (Y.subst Subst.identity) = X.arrow Y
      exact hX.symm ▸ hY.symm ▸ rfl
  | .piTy X Y => by
      have hX := Ty.subst_id X
      have hCong := Ty.subst_congr Subst.lift_identity_equiv Y
      have hY := Ty.subst_id Y
      show (X.subst Subst.identity).piTy (Y.subst Subst.identity.lift) = X.piTy Y
      exact hX.symm ▸ hCong.symm ▸ hY.symm ▸ rfl
  | .tyVar _ => rfl
  | .sigmaTy X Y => by
      have hX := Ty.subst_id X
      have hCong := Ty.subst_congr Subst.lift_identity_equiv Y
      have hY := Ty.subst_id Y
      show (X.subst Subst.identity).sigmaTy (Y.subst Subst.identity.lift)
         = X.sigmaTy Y
      exact hX.symm ▸ hCong.symm ▸ hY.symm ▸ rfl
  | .bool => rfl
  | .universe _ _ => rfl
  | .nat => rfl
  | .list elemType => by
      have hElem := Ty.subst_id elemType
      show (elemType.subst Subst.identity).list = elemType.list
      exact hElem.symm ▸ rfl
  | .option elemType => by
      have hElem := Ty.subst_id elemType
      show (elemType.subst Subst.identity).option = elemType.option
      exact hElem.symm ▸ rfl
  | .either leftType rightType => by
      have hLeft  := Ty.subst_id leftType
      have hRight := Ty.subst_id rightType
      show (leftType.subst Subst.identity).either
             (rightType.subst Subst.identity)
           = leftType.either rightType
      exact hLeft.symm ▸ hRight.symm ▸ rfl

/-- Substitution commutes with weakening: substituting after
weakening = weakening after substituting (with appropriately lifted
substitution).  Stepping stone for the composition law `Ty.subst_compose`.

In v1.10, with `Ty.weaken := T.rename Renaming.weaken`, this is derived
from `Ty.rename_subst_commute` and `Ty.subst_rename_commute` plus the
pointwise equivalence `Subst.precompose Renaming.weaken σ.lift ≡
Subst.renameAfter σ Renaming.weaken`.  The pointwise equivalence is
trivial (both forms reduce to `(σ i).rename Renaming.weaken` by
`Subst.lift`'s defn at successor positions). -/
theorem Ty.subst_weaken_commute {level s t : Nat} (T : Ty level s) (σ : Subst level s t) :
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
def Subst.compose {level s m t : Nat} (σ₁ : Subst level s m) (σ₂ : Subst level m t) :
    Subst level s t :=
  fun i => (σ₁ i).subst σ₂

/-- Lifting commutes with substitution composition (pointwise).  The
non-trivial `k+1` case reduces to `Ty.subst_weaken_commute`. -/
theorem Subst.lift_compose_equiv {level s m t : Nat}
    (σ₁ : Subst level s m) (σ₂ : Subst level m t) :
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
theorem Ty.subst_compose {level s m t : Nat} :
    ∀ (T : Ty level s) (σ₁ : Subst level s m) (σ₂ : Subst level m t),
    (T.subst σ₁).subst σ₂ = T.subst (Subst.compose σ₁ σ₂)
  | .unit, _, _ => rfl
  | .arrow X Y, σ₁, σ₂ => by
      show ((X.subst σ₁).subst σ₂).arrow ((Y.subst σ₁).subst σ₂)
         = (X.subst (Subst.compose σ₁ σ₂)).arrow
           (Y.subst (Subst.compose σ₁ σ₂))
      have hX := Ty.subst_compose X σ₁ σ₂
      have hY := Ty.subst_compose Y σ₁ σ₂
      exact hX ▸ hY ▸ rfl
  | .piTy X Y, σ₁, σ₂ => by
      show ((X.subst σ₁).subst σ₂).piTy ((Y.subst σ₁.lift).subst σ₂.lift)
         = (X.subst (Subst.compose σ₁ σ₂)).piTy
           (Y.subst (Subst.compose σ₁ σ₂).lift)
      have hX := Ty.subst_compose X σ₁ σ₂
      have hY := Ty.subst_compose Y σ₁.lift σ₂.lift
      have hCong := Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | .tyVar _, _, _ => rfl
  | .sigmaTy X Y, σ₁, σ₂ => by
      show ((X.subst σ₁).subst σ₂).sigmaTy ((Y.subst σ₁.lift).subst σ₂.lift)
         = (X.subst (Subst.compose σ₁ σ₂)).sigmaTy
           (Y.subst (Subst.compose σ₁ σ₂).lift)
      have hX := Ty.subst_compose X σ₁ σ₂
      have hY := Ty.subst_compose Y σ₁.lift σ₂.lift
      have hCong := Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) Y
      exact hX ▸ hY ▸ hCong ▸ rfl
  | .bool, _, _ => rfl
  | .universe _ _, _, _ => rfl
  | .nat, _, _ => rfl
  | .list elemType, σ₁, σ₂ => by
      show Ty.list ((elemType.subst σ₁).subst σ₂)
         = Ty.list (elemType.subst (Subst.compose σ₁ σ₂))
      have hElem := Ty.subst_compose elemType σ₁ σ₂
      exact hElem ▸ rfl
  | .option elemType, σ₁, σ₂ => by
      show Ty.option ((elemType.subst σ₁).subst σ₂)
         = Ty.option (elemType.subst (Subst.compose σ₁ σ₂))
      have hElem := Ty.subst_compose elemType σ₁ σ₂
      exact hElem ▸ rfl
  | .either leftType rightType, σ₁, σ₂ => by
      show Ty.either ((leftType.subst σ₁).subst σ₂)
                     ((rightType.subst σ₁).subst σ₂)
         = Ty.either (leftType.subst (Subst.compose σ₁ σ₂))
                     (rightType.subst (Subst.compose σ₁ σ₂))
      have hLeft  := Ty.subst_compose leftType σ₁ σ₂
      have hRight := Ty.subst_compose rightType σ₁ σ₂
      exact hLeft ▸ hRight ▸ rfl

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
theorem Subst.compose_identity_left {level s t : Nat} (σ : Subst level s t) :
    Subst.equiv (Subst.compose Subst.identity σ) σ :=
  fun _ => rfl

/-- Substitution composition is right-unital: appending the
identity substitution leaves the substitution pointwise unchanged.
Pointwise via `Ty.subst_id`: each substituent's identity-
substitution equals itself. -/
theorem Subst.compose_identity_right {level s t : Nat} (σ : Subst level s t) :
    Subst.equiv (Subst.compose σ Subst.identity) σ :=
  fun i => Ty.subst_id (σ i)

/-- Substitution composition is associative.  Pointwise via
`Ty.subst_compose`: at each position both sides reduce to
`((σ₁ i).subst σ₂).subst σ₃`. -/
theorem Subst.compose_assoc {level s m₁ m₂ t : Nat}
    (σ₁ : Subst level s m₁) (σ₂ : Subst level m₁ m₂) (σ₃ : Subst level m₂ t) :
    Subst.equiv (Subst.compose σ₁ (Subst.compose σ₂ σ₃))
                (Subst.compose (Subst.compose σ₁ σ₂) σ₃) :=
  fun i => (Ty.subst_compose (σ₁ i) σ₂ σ₃).symm

/-- Pointwise equivalence linking the two singleton-substitution
formulations: substitution-then-rename equals lifted-rename-then-
substitution-with-renamed-substituent.  The auxiliary lemma needed for
the `Ty.subst0_rename_commute` derivation. -/
theorem Subst.singleton_renameAfter_equiv_precompose {level scope target : Nat}
    (A : Ty level scope) (ρ : Renaming scope target) :
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
theorem Ty.subst0_rename_commute {level scope target : Nat}
    (T : Ty level (scope + 1)) (A : Ty level scope) (ρ : Renaming scope target) :
    (T.subst0 A).rename ρ = (T.rename ρ.lift).subst0 (A.rename ρ) := by
  have h1 := Ty.subst_rename_commute T (Subst.singleton A) ρ
  have h2 := Ty.subst_congr
    (Subst.singleton_renameAfter_equiv_precompose A ρ) T
  have h3 := Ty.rename_subst_commute T ρ.lift (Subst.singleton (A.rename ρ))
  exact h1.trans (h2.trans h3.symm)

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

/-! ## Terms

`Term context currentType` is a well-typed term in `context` of type
`currentType`.  Constructor signatures are the typing rules; Lean's
kernel checks each rule at declaration time, so a misstated rule is
rejected before any program is written using it. -/

/-- Intrinsically-typed terms.  No separate typing relation — the
constructor signatures *are* the typing rules. -/
inductive Term : {mode : Mode} → {level scope : Nat} →
                 (context : Ctx mode level scope) → Ty level scope → Type
  /-- Variable rule.  A term is a variable iff it carries a Fin-scoped
  position; the type is computed by `varType` from the context.
  Replaces the v1.0 `Lookup`-indexed form, which forced propext through
  the match compiler at term-level renaming.  v1.9. -/
  | var :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      (position : Fin scope) →
      Term context (varType context position)
  /-- Unit introduction at every scope. -/
  | unit :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      Term context Ty.unit
  /-- λ-abstraction.  The body is checked in the context extended with
  the bound variable; its expected type is the codomain weakened to
  the extended scope. -/
  | lam :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {domainType codomainType : Ty level scope} →
      (body : Term (Ctx.cons context domainType) codomainType.weaken) →
      Term context (Ty.arrow domainType codomainType)
  /-- Non-dependent application — function expects the codomain at the
  same scope as the domain. -/
  | app :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {domainType codomainType : Ty level scope} →
      (functionTerm : Term context (Ty.arrow domainType codomainType)) →
      (argumentTerm : Term context domainType) →
      Term context codomainType
  /-- λ-abstraction for dependent `piTy`.  Body's type is the codomain
  directly (at scope `+1`) — no weakening needed because `piTy`'s
  codomain is already at the extended scope. -/
  | lamPi :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {domainType : Ty level scope} →
      {codomainType : Ty level (scope + 1)} →
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
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {domainType : Ty level scope} →
      {codomainType : Ty level (scope + 1)} →
      (functionTerm : Term context (Ty.piTy domainType codomainType)) →
      (argumentTerm : Term context domainType) →
      Term context (codomainType.subst0 domainType)
  /-- Pair introduction for dependent `sigmaTy`.  The second
  component's type is `secondType` with var 0 substituted by
  `firstType` — same `Ty.subst0` mechanism `appPi` uses. -/
  | pair :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {firstType : Ty level scope} →
      {secondType : Ty level (scope + 1)} →
      (firstVal : Term context firstType) →
      (secondVal : Term context (secondType.subst0 firstType)) →
      Term context (Ty.sigmaTy firstType secondType)
  /-- First projection.  Extracts the first component of a pair. -/
  | fst :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {firstType : Ty level scope} →
      {secondType : Ty level (scope + 1)} →
      (pairTerm : Term context (Ty.sigmaTy firstType secondType)) →
      Term context firstType
  /-- Second projection.  Result type uses the same `subst0`
  placeholder substitution as `pair`. -/
  | snd :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {firstType : Ty level scope} →
      {secondType : Ty level (scope + 1)} →
      (pairTerm : Term context (Ty.sigmaTy firstType secondType)) →
      Term context (secondType.subst0 firstType)
  /-- Boolean introduction — `true` literal at every context.  v1.13+. -/
  | boolTrue :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      Term context Ty.bool
  /-- Boolean introduction — `false` literal at every context.  v1.13+. -/
  | boolFalse :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      Term context Ty.bool
  /-- Boolean elimination (non-dependent) — case-analysis on a boolean
  scrutinee produces one of two same-typed branches.  Non-dependent
  because the result type is a fixed `Ty level scope`, not a function on
  `bool`; dependent elim would require representing motives as
  functions on `Term`-valued booleans, which doesn't fit the current
  scope-only `Ty` indexing.  v1.14+. -/
  | boolElim :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {resultType : Ty level scope} →
      (scrutinee : Term context Ty.bool) →
      (thenBranch : Term context resultType) →
      (elseBranch : Term context resultType) →
      Term context resultType
  /-- Natural-number introduction — `0`. -/
  | natZero :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      Term context Ty.nat
  /-- Natural-number introduction — `succ n`. -/
  | natSucc :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      (predecessor : Term context Ty.nat) →
      Term context Ty.nat
  /-- Natural-number elimination (case-analysis form).  Cases on the
  scrutinee: zero produces `zeroBranch`, `succ n` applies the
  predecessor function `succBranch` to `n`.  Case-analysis only — the
  succ branch does NOT see a recursive result; primitive recursion
  with the IH lands in v1.32 as `Term.natRec`.

  Result type is fixed to `resultType : Ty level scope`, parallel to
  `Term.boolElim` — non-dependent.  Dependent elimination requires
  motives over Term-valued scrutinees, which the current scope-only
  Ty indexing doesn't accommodate. -/
  | natElim :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {resultType : Ty level scope} →
      (scrutinee : Term context Ty.nat) →
      (zeroBranch : Term context resultType) →
      (succBranch : Term context (Ty.arrow Ty.nat resultType)) →
      Term context resultType
  /-- Primitive recursion on naturals — Church-style recursor with
  induction hypothesis.  Strictly stronger than `natElim`
  (case-analysis): the succ-branch sees BOTH the predecessor `n` and
  the recursive result `natRec n z s : resultType`.

  Surface analogue:
      `natRec(scrutinee, z, fn n ih => …)` — `ih` is the recursion's
      result on the predecessor.  Primitive recursion captures
      addition, multiplication, factorial, fold/Foldr, etc.

  Reduction:
      `natRec 0       z s ⟶ z`
      `natRec (succ n) z s ⟶ s n (natRec n z s)`

  Result type is fixed (non-dependent), parallel to `natElim`.
  *True* dependent induction (`natInd`) — where the result type
  varies with the scrutinee — requires either universe codes
  (`El : Term Γ (Ty.universe u rfl) → Ty u scope`) or term-aware
  Ty indexing.  Both deferred until after v1.40 identity types,
  which supplies the cast machinery the dependent ι-rule needs. -/
  | natRec :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {resultType : Ty level scope} →
      (scrutinee : Term context Ty.nat) →
      (zeroBranch : Term context resultType) →
      (succBranch : Term context
         (Ty.arrow Ty.nat (Ty.arrow resultType resultType))) →
      Term context resultType
  /-- Empty list — `[]` at any element type.  The `elementType` is an
  implicit argument that callers supply via the expected return type
  (or `(elementType := T)`). -/
  | listNil :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {elementType : Ty level scope} →
      Term context (Ty.list elementType)
  /-- List cons — `head :: tail`.  Both head and tail share the same
  element type, propagated to the result. -/
  | listCons :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {elementType : Ty level scope} →
      (head : Term context elementType) →
      (tail : Term context (Ty.list elementType)) →
      Term context (Ty.list elementType)
  /-- List elimination (case-analysis form).  Cases on the scrutinee:
  empty list produces `nilBranch`, `cons head tail` applies the curried
  function `consBranch` to head and then tail.  Case-analysis only —
  no recursive-result IH (primitive recursion comes later via
  `Term.listRec`).  Result type fixed; non-dependent. -/
  | listElim :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {elementType : Ty level scope} →
      {resultType : Ty level scope} →
      (scrutinee : Term context (Ty.list elementType)) →
      (nilBranch : Term context resultType) →
      (consBranch : Term context
         (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))) →
      Term context resultType
  /-- Empty option — `none`.  ElementType is supplied via the expected
  return type or `(elementType := T)`. -/
  | optionNone :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {elementType : Ty level scope} →
      Term context (Ty.option elementType)
  /-- Option wrap — `some value`. -/
  | optionSome :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {elementType : Ty level scope} →
      (value : Term context elementType) →
      Term context (Ty.option elementType)
  /-- Option elimination (case-analysis form).  None case: `noneBranch`.
  Some case: apply `someBranch : elem → result` to the contained value.
  Mirror of `listElim` but with no tail in the some-case. -/
  | optionMatch :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {elementType : Ty level scope} →
      {resultType : Ty level scope} →
      (scrutinee : Term context (Ty.option elementType)) →
      (noneBranch : Term context resultType) →
      (someBranch : Term context (Ty.arrow elementType resultType)) →
      Term context resultType
  /-- Sum left-injection — `inl value` at element type `leftType`,
  with `rightType` carried implicitly via the expected return type. -/
  | eitherInl :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {leftType rightType : Ty level scope} →
      (value : Term context leftType) →
      Term context (Ty.either leftType rightType)
  /-- Sum right-injection — `inr value` at element type `rightType`,
  with `leftType` carried implicitly. -/
  | eitherInr :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {leftType rightType : Ty level scope} →
      (value : Term context rightType) →
      Term context (Ty.either leftType rightType)
  /-- Sum elimination (case-analysis form).  Left case: apply
  `leftBranch : leftType → resultType` to the contained value.
  Right case: apply `rightBranch : rightType → resultType`.
  Symmetric to `optionMatch` but with both branches function-shaped
  (since both carry payloads). -/
  | eitherMatch :
      {mode : Mode} → {level scope : Nat} →
      {context : Ctx mode level scope} →
      {leftType rightType : Ty level scope} →
      {resultType : Ty level scope} →
      (scrutinee : Term context (Ty.either leftType rightType)) →
      (leftBranch : Term context (Ty.arrow leftType resultType)) →
      (rightBranch : Term context (Ty.arrow rightType resultType)) →
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
def TermRenaming {m : Mode} {level scope scope' : Nat}
    (Γ : Ctx m level scope) (Δ : Ctx m level scope')
    (ρ : Renaming scope scope') : Prop :=
  ∀ (i : Fin scope), varType Δ (ρ i) = (varType Γ i).rename ρ

/-- Lift a term-level renaming under a binder.  Pattern-matches on
`i : Fin (scope + 1)` directly via Fin's structure (`⟨0, _⟩` and
`⟨k+1, h⟩`), so the match never sees a cons-specialised Ctx index.
Both Fin cases reduce to `Ty.rename_weaken_commute` plus, in the
successor case, the predecessor's `ρt` proof. -/
theorem TermRenaming.lift {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope'}
    (ρt : TermRenaming Γ Δ ρ) (newType : Ty level scope) :
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
theorem Ty.rename_identity {level scope : Nat} (T : Ty level scope) :
    T.rename Renaming.identity = T :=
  let renamingIdEqSubstId :
      Subst.equiv (Renaming.toSubst (@Renaming.identity scope))
                  Subst.identity := fun _ => rfl
  (Ty.rename_eq_subst T Renaming.identity).trans
    ((Ty.subst_congr renamingIdEqSubstId T).trans (Ty.subst_id T))

/-- The identity term-level renaming.  Witnesses `TermRenaming Γ Γ id`
from `Ty.rename_identity`. -/
theorem TermRenaming.identity {m : Mode} {level scope : Nat} (Γ : Ctx m level scope) :
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
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope'}
    (ρt : TermRenaming Γ Δ ρ) :
    {T : Ty level scope} → Term Γ T → Term Δ (T.rename ρ)
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
  | _, .natZero        => Term.natZero
  | _, .natSucc pred   => Term.natSucc (Term.rename ρt pred)
  | _, .natRec scrutinee zeroBranch succBranch =>
      Term.natRec (Term.rename ρt scrutinee)
                  (Term.rename ρt zeroBranch)
                  (Term.rename ρt succBranch)
  | _, .natElim scrutinee zeroBranch succBranch =>
      Term.natElim (Term.rename ρt scrutinee)
                   (Term.rename ρt zeroBranch)
                   (Term.rename ρt succBranch)
  | _, .listNil       => Term.listNil
  | _, .listCons hd tl =>
      Term.listCons (Term.rename ρt hd) (Term.rename ρt tl)
  | _, .listElim scrutinee nilBranch consBranch =>
      Term.listElim (Term.rename ρt scrutinee)
                    (Term.rename ρt nilBranch)
                    (Term.rename ρt consBranch)
  | _, .optionNone     => Term.optionNone
  | _, .optionSome v   => Term.optionSome (Term.rename ρt v)
  | _, .optionMatch scrutinee noneBranch someBranch =>
      Term.optionMatch (Term.rename ρt scrutinee)
                       (Term.rename ρt noneBranch)
                       (Term.rename ρt someBranch)
  | _, .eitherInl v    => Term.eitherInl (Term.rename ρt v)
  | _, .eitherInr v    => Term.eitherInr (Term.rename ρt v)
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      Term.eitherMatch (Term.rename ρt scrutinee)
                       (Term.rename ρt leftBranch)
                       (Term.rename ρt rightBranch)

/-! ## Term-level weakening. -/

/-- The shift-by-one renaming witnesses a `TermRenaming` from `Γ` to
`Γ.cons newType`: the position-equality `varType (Γ.cons newType) (Fin.succ i) = (varType Γ i).rename Renaming.weaken`
is `rfl` because both sides reduce to the same `Ty.rename` application
under the new `Ty.weaken := T.rename Renaming.weaken` defn. -/
theorem TermRenaming.weaken {m : Mode} {level scope : Nat}
    (Γ : Ctx m level scope) (newType : Ty level scope) :
    TermRenaming Γ (Γ.cons newType) Renaming.weaken := fun _ => rfl

/-- Weaken a term by extending its context with one fresh binding.
The result type is the original type weakened in lockstep, mirroring
the type-level `Ty.weaken`.  Implemented via `Term.rename` with the
shift-by-one renaming. -/
def Term.weaken {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    (newType : Ty level scope) {T : Ty level scope} (term : Term Γ T) :
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
abbrev TermSubst {m : Mode} {level scope scope' : Nat}
    (Γ : Ctx m level scope) (Δ : Ctx m level scope')
    (σ : Subst level scope scope') : Type :=
  ∀ (i : Fin scope), Term Δ ((varType Γ i).subst σ)

/-- Lift a term-level substitution under a binder.  Position 0 in the
extended source context maps to `Term.var ⟨0, _⟩` in the extended
target (cast through `Ty.subst_weaken_commute`); positions `k + 1`
weaken the predecessor's image into the extended target context. -/
def TermSubst.lift {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ : Subst level scope scope'}
    (σt : TermSubst Γ Δ σ) (newType : Ty level scope) :
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
theorem Ty.weaken_subst_singleton {level scope : Nat}
    (T : Ty level scope) (X : Ty level scope) :
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
def TermSubst.singleton {m : Mode} {level scope : Nat}
    {Γ : Ctx m level scope} {T_arg : Ty level scope}
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
    {level scope target : Nat}
    (substituent : Ty level scope) (σ : Subst level scope target) :
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
theorem Ty.subst0_subst_commute {level scope target : Nat}
    (T : Ty level (scope + 1)) (X : Ty level scope) (σ : Subst level scope target) :
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
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ : Subst level scope scope'}
    (σt : TermSubst Γ Δ σ) :
    {T : Ty level scope} → Term Γ T → Term Δ (T.subst σ)
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
  | _, .natZero      => Term.natZero
  | _, .natSucc pred => Term.natSucc (Term.subst σt pred)
  | _, .natRec scrutinee zeroBranch succBranch =>
      Term.natRec (Term.subst σt scrutinee)
                  (Term.subst σt zeroBranch)
                  (Term.subst σt succBranch)
  | _, .natElim scrutinee zeroBranch succBranch =>
      Term.natElim (Term.subst σt scrutinee)
                   (Term.subst σt zeroBranch)
                   (Term.subst σt succBranch)
  | _, .listNil       => Term.listNil
  | _, .listCons hd tl =>
      Term.listCons (Term.subst σt hd) (Term.subst σt tl)
  | _, .listElim scrutinee nilBranch consBranch =>
      Term.listElim (Term.subst σt scrutinee)
                    (Term.subst σt nilBranch)
                    (Term.subst σt consBranch)
  | _, .optionNone     => Term.optionNone
  | _, .optionSome v   => Term.optionSome (Term.subst σt v)
  | _, .optionMatch scrutinee noneBranch someBranch =>
      Term.optionMatch (Term.subst σt scrutinee)
                       (Term.subst σt noneBranch)
                       (Term.subst σt someBranch)
  | _, .eitherInl v    => Term.eitherInl (Term.subst σt v)
  | _, .eitherInr v    => Term.eitherInr (Term.subst σt v)
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      Term.eitherMatch (Term.subst σt scrutinee)
                       (Term.subst σt leftBranch)
                       (Term.subst σt rightBranch)

/-- **Single-variable term substitution** — substitute `arg` for var 0
in `body`.  Used by β-reduction.  Result type is computed via
`Ty.subst0` at the type level, matching `Term.appPi`'s result-type
shape exactly. -/
def Term.subst0 {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {T_arg : Ty level scope} {T_body : Ty level (scope + 1)}
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
def TermSubst.identity {m : Mode} {level scope : Nat} (Γ : Ctx m level scope) :
    TermSubst Γ Γ Subst.identity := fun i =>
  (Ty.subst_id (varType Γ i)).symm ▸ Term.var i

/-- Compose two term-substitutions: apply `σt₁` then substitute the
result by `σt₂`, casting through `Ty.subst_compose`. -/
def TermSubst.compose {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {σ₁ : Subst level scope₁ scope₂} {σ₂ : Subst level scope₂ scope₃}
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
theorem heq_var_across_ctx_eq {m : Mode} {level scope : Nat}
    {Γ Δ : Ctx m level scope} (h_ctx : Γ = Δ) (i : Fin scope) :
    HEq (Term.var (context := Γ) i) (Term.var (context := Δ) i) := by
  cases h_ctx
  rfl

/-- **Strip an inner type-cast through `Term.weaken`.**  The
generic helper: weakening a term commutes with a propositional
type cast on the input.  Proven by `cases` on the equation —
both T₁ and T₂ are local variables, so the substitution succeeds
and the cast vanishes. -/
theorem Term.heq_weaken_strip_cast
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    (newType : Ty level scope) {T₁ T₂ : Ty level scope} (h : T₁ = T₂)
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
theorem heq_weaken_var_across_ctx_eq {m : Mode} {level scope : Nat}
    {Γ Δ : Ctx m level scope} (h_ctx : Γ = Δ)
    (newTypeΓ : Ty level scope) (newTypeΔ : Ty level scope)
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
    {m : Mode} {level scope : Nat}
    (Γ : Ctx m level scope) (newType : Ty level scope) :
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
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {T₁_a T₁_b T₂_a T₂_b : Ty level scope}
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
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {dom₁ dom₂ : Ty level scope} (h_dom : dom₁ = dom₂)
    {cod₁ cod₂ : Ty level scope} (h_cod : cod₁ = cod₂)
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
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {dom₁ dom₂ : Ty level scope} (h_dom : dom₁ = dom₂)
    {cod₁ cod₂ : Ty level (scope + 1)} (h_cod : cod₁ = cod₂)
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
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {dom₁ dom₂ : Ty level scope} (h_dom : dom₁ = dom₂)
    {cod₁ cod₂ : Ty level (scope + 1)} (h_cod : cod₁ = cod₂)
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
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {first₁ first₂ : Ty level scope} (h_first : first₁ = first₂)
    {second₁ second₂ : Ty level (scope + 1)} (h_second : second₁ = second₂)
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
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {first₁ first₂ : Ty level scope} (h_first : first₁ = first₂)
    {second₁ second₂ : Ty level (scope + 1)} (h_second : second₁ = second₂)
    (p₁ : Term Γ (Ty.sigmaTy first₁ second₁))
    (p₂ : Term Γ (Ty.sigmaTy first₂ second₂)) (h_p : HEq p₁ p₂) :
    HEq (Term.fst p₁) (Term.fst p₂) := by
  cases h_first
  cases h_second
  cases h_p
  rfl

/-- HEq congruence for `Term.snd`. -/
theorem Term.snd_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {first₁ first₂ : Ty level scope} (h_first : first₁ = first₂)
    {second₁ second₂ : Ty level (scope + 1)} (h_second : second₁ = second₂)
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
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {newType₁ newType₂ : Ty level scope} (h_new : newType₁ = newType₂)
    {T₁ T₂ : Ty level scope} (h_T : T₁ = T₂)
    (t₁ : Term Γ T₁) (t₂ : Term Γ T₂) (h_t : HEq t₁ t₂) :
    HEq (Term.weaken newType₁ t₁) (Term.weaken newType₂ t₂) := by
  cases h_new
  cases h_T
  cases h_t
  rfl

/-- HEq congruence for `Term.boolElim`. -/
theorem Term.boolElim_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {result₁ result₂ : Ty level scope} (h_result : result₁ = result₂)
    (s₁ s₂ : Term Γ Ty.bool) (h_s : s₁ = s₂)
    (t₁ : Term Γ result₁) (t₂ : Term Γ result₂) (h_t : HEq t₁ t₂)
    (e₁ : Term Γ result₁) (e₂ : Term Γ result₂) (h_e : HEq e₁ e₂) :
    HEq (Term.boolElim s₁ t₁ e₁) (Term.boolElim s₂ t₂ e₂) := by
  cases h_result
  cases h_s
  cases h_t
  cases h_e
  rfl

/-- HEq congruence for `Term.natSucc`.  natSucc has no type-level
indices that vary, so this collapses to plain equality of the
predecessor-term — we accept HEq for symmetry with the other
constructor congruences. -/
theorem Term.natSucc_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    (p₁ p₂ : Term Γ Ty.nat) (h_p : HEq p₁ p₂) :
    HEq (Term.natSucc p₁) (Term.natSucc p₂) := by
  cases h_p
  rfl

/-- HEq congruence for `Term.natElim`. -/
theorem Term.natElim_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {result₁ result₂ : Ty level scope} (h_result : result₁ = result₂)
    (s₁ s₂ : Term Γ Ty.nat) (h_s : s₁ = s₂)
    (z₁ : Term Γ result₁) (z₂ : Term Γ result₂) (h_z : HEq z₁ z₂)
    (f₁ : Term Γ (Ty.arrow Ty.nat result₁))
    (f₂ : Term Γ (Ty.arrow Ty.nat result₂))
    (h_f : HEq f₁ f₂) :
    HEq (Term.natElim s₁ z₁ f₁) (Term.natElim s₂ z₂ f₂) := by
  cases h_result
  cases h_s
  cases h_z
  cases h_f
  rfl

/-- HEq congruence for `Term.natRec`.  Same shape as `natElim_HEq_congr`
but with succBranch typed `Ty.arrow Ty.nat (Ty.arrow result result)` —
the predecessor + IH curried form for primitive recursion. -/
theorem Term.natRec_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {result₁ result₂ : Ty level scope} (h_result : result₁ = result₂)
    (s₁ s₂ : Term Γ Ty.nat) (h_s : s₁ = s₂)
    (z₁ : Term Γ result₁) (z₂ : Term Γ result₂) (h_z : HEq z₁ z₂)
    (f₁ : Term Γ (Ty.arrow Ty.nat (Ty.arrow result₁ result₁)))
    (f₂ : Term Γ (Ty.arrow Ty.nat (Ty.arrow result₂ result₂)))
    (h_f : HEq f₁ f₂) :
    HEq (Term.natRec s₁ z₁ f₁) (Term.natRec s₂ z₂ f₂) := by
  cases h_result
  cases h_s
  cases h_z
  cases h_f
  rfl

/-- HEq congruence for `Term.listNil`.  Only the elementType varies
between sides; no value arguments. -/
theorem Term.listNil_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {elem₁ elem₂ : Ty level scope} (h_elem : elem₁ = elem₂) :
    HEq (Term.listNil (context := Γ) (elementType := elem₁))
        (Term.listNil (context := Γ) (elementType := elem₂)) := by
  cases h_elem
  rfl

/-- HEq congruence for `Term.listCons`. -/
theorem Term.listCons_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {elem₁ elem₂ : Ty level scope} (h_elem : elem₁ = elem₂)
    (h₁ : Term Γ elem₁) (h₂ : Term Γ elem₂) (h_h : HEq h₁ h₂)
    (t₁ : Term Γ (Ty.list elem₁)) (t₂ : Term Γ (Ty.list elem₂))
    (h_t : HEq t₁ t₂) :
    HEq (Term.listCons h₁ t₁) (Term.listCons h₂ t₂) := by
  cases h_elem
  cases h_h
  cases h_t
  rfl

/-- HEq congruence for `Term.listElim`.  Both `elementType` and
`resultType` may vary; the consBranch type
`elem → list elem → result` mentions `elementType` twice. -/
theorem Term.listElim_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {elem₁ elem₂ : Ty level scope} (h_elem : elem₁ = elem₂)
    {result₁ result₂ : Ty level scope} (h_result : result₁ = result₂)
    (s₁ : Term Γ (Ty.list elem₁)) (s₂ : Term Γ (Ty.list elem₂))
    (h_s : HEq s₁ s₂)
    (n₁ : Term Γ result₁) (n₂ : Term Γ result₂) (h_n : HEq n₁ n₂)
    (c₁ : Term Γ (Ty.arrow elem₁ (Ty.arrow (Ty.list elem₁) result₁)))
    (c₂ : Term Γ (Ty.arrow elem₂ (Ty.arrow (Ty.list elem₂) result₂)))
    (h_c : HEq c₁ c₂) :
    HEq (Term.listElim s₁ n₁ c₁) (Term.listElim s₂ n₂ c₂) := by
  cases h_elem
  cases h_result
  cases h_s
  cases h_n
  cases h_c
  rfl

/-- HEq congruence for `Term.optionNone` — only elementType varies. -/
theorem Term.optionNone_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {elem₁ elem₂ : Ty level scope} (h_elem : elem₁ = elem₂) :
    HEq (Term.optionNone (context := Γ) (elementType := elem₁))
        (Term.optionNone (context := Γ) (elementType := elem₂)) := by
  cases h_elem
  rfl

/-- HEq congruence for `Term.optionSome`. -/
theorem Term.optionSome_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {elem₁ elem₂ : Ty level scope} (h_elem : elem₁ = elem₂)
    (v₁ : Term Γ elem₁) (v₂ : Term Γ elem₂) (h_v : HEq v₁ v₂) :
    HEq (Term.optionSome v₁) (Term.optionSome v₂) := by
  cases h_elem
  cases h_v
  rfl

/-- HEq congruence for `Term.optionMatch`. -/
theorem Term.optionMatch_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {elem₁ elem₂ : Ty level scope} (h_elem : elem₁ = elem₂)
    {result₁ result₂ : Ty level scope} (h_result : result₁ = result₂)
    (s₁ : Term Γ (Ty.option elem₁)) (s₂ : Term Γ (Ty.option elem₂))
    (h_s : HEq s₁ s₂)
    (n₁ : Term Γ result₁) (n₂ : Term Γ result₂) (h_n : HEq n₁ n₂)
    (sm₁ : Term Γ (Ty.arrow elem₁ result₁))
    (sm₂ : Term Γ (Ty.arrow elem₂ result₂))
    (h_sm : HEq sm₁ sm₂) :
    HEq (Term.optionMatch s₁ n₁ sm₁) (Term.optionMatch s₂ n₂ sm₂) := by
  cases h_elem
  cases h_result
  cases h_s
  cases h_n
  cases h_sm
  rfl

/-- HEq congruence for `Term.eitherInl`.  Both `leftType` and
`rightType` may vary; only the `leftType` value is supplied. -/
theorem Term.eitherInl_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {left₁ left₂ : Ty level scope} (h_left : left₁ = left₂)
    {right₁ right₂ : Ty level scope} (h_right : right₁ = right₂)
    (v₁ : Term Γ left₁) (v₂ : Term Γ left₂) (h_v : HEq v₁ v₂) :
    HEq (Term.eitherInl (rightType := right₁) v₁)
        (Term.eitherInl (rightType := right₂) v₂) := by
  cases h_left
  cases h_right
  cases h_v
  rfl

/-- HEq congruence for `Term.eitherInr`.  Symmetric to `eitherInl_HEq_congr`. -/
theorem Term.eitherInr_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {left₁ left₂ : Ty level scope} (h_left : left₁ = left₂)
    {right₁ right₂ : Ty level scope} (h_right : right₁ = right₂)
    (v₁ : Term Γ right₁) (v₂ : Term Γ right₂) (h_v : HEq v₁ v₂) :
    HEq (Term.eitherInr (leftType := left₁) v₁)
        (Term.eitherInr (leftType := left₂) v₂) := by
  cases h_left
  cases h_right
  cases h_v
  rfl

/-- HEq congruence for `Term.eitherMatch`.  Three Ty-index equalities
(left, right, result) and three sub-term HEqs (scrutinee, leftBranch,
rightBranch). -/
theorem Term.eitherMatch_HEq_congr
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {left₁ left₂ : Ty level scope} (h_left : left₁ = left₂)
    {right₁ right₂ : Ty level scope} (h_right : right₁ = right₂)
    {result₁ result₂ : Ty level scope} (h_result : result₁ = result₂)
    (s₁ : Term Γ (Ty.either left₁ right₁))
    (s₂ : Term Γ (Ty.either left₂ right₂)) (h_s : HEq s₁ s₂)
    (lb₁ : Term Γ (Ty.arrow left₁ result₁))
    (lb₂ : Term Γ (Ty.arrow left₂ result₂)) (h_lb : HEq lb₁ lb₂)
    (rb₁ : Term Γ (Ty.arrow right₁ result₁))
    (rb₂ : Term Γ (Ty.arrow right₂ result₂)) (h_rb : HEq rb₁ rb₂) :
    HEq (Term.eitherMatch s₁ lb₁ rb₁) (Term.eitherMatch s₂ lb₂ rb₂) := by
  cases h_left
  cases h_right
  cases h_result
  cases h_s
  cases h_lb
  cases h_rb
  rfl

/-! ## `Term.subst_id_HEq` leaf cases.

Four leaf constructors: `var` strips the inner `(Ty.subst_id _).symm
▸ Term.var i` cast via `eqRec_heq`; `unit`/`boolTrue`/`boolFalse`
have substitution-independent types so reduce to `HEq.refl`. -/

/-- Leaf HEq case of `Term.subst_id` for `var`. -/
theorem Term.subst_id_HEq_var
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope} (i : Fin scope) :
    HEq (Term.subst (TermSubst.identity Γ) (Term.var i))
        (Term.var (context := Γ) i) := by
  show HEq ((Ty.subst_id (varType Γ i)).symm ▸ Term.var i) (Term.var i)
  exact eqRec_heq _ _

/-- Leaf HEq case of `Term.subst_id` for `unit`. -/
theorem Term.subst_id_HEq_unit
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope} :
    HEq (Term.subst (TermSubst.identity Γ) (Term.unit (context := Γ)))
        (Term.unit (context := Γ)) :=
  HEq.refl _

/-- Leaf HEq case of `Term.subst_id` for `boolTrue`. -/
theorem Term.subst_id_HEq_boolTrue
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope} :
    HEq (Term.subst (TermSubst.identity Γ) (Term.boolTrue (context := Γ)))
        (Term.boolTrue (context := Γ)) :=
  HEq.refl _

/-- Leaf HEq case of `Term.subst_id` for `boolFalse`. -/
theorem Term.subst_id_HEq_boolFalse
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope} :
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
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {T₁ T₂ : Ty level scope}
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
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {first : Ty level scope} {second : Ty level (scope + 1)}
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
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope} {result : Ty level scope}
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
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {dom : Ty level scope} {cod : Ty level (scope + 1)}
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
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {first : Ty level scope} {second : Ty level (scope + 1)}
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
    {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {first : Ty level scope} {second : Ty level (scope + 1)}
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
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ₁ σ₂ : Subst level scope scope'}
    (σt₁ : TermSubst Γ Δ σ₁) (σt₂ : TermSubst Γ Δ σ₂)
    (h_subst : Subst.equiv σ₁ σ₂)
    (h_pointwise : ∀ i, HEq (σt₁ i) (σt₂ i))
    (newType : Ty level scope) :
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
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ₁ Δ₂ : Ctx m level scope'}
    (h_ctx : Δ₁ = Δ₂)
    {σ₁ σ₂ : Subst level scope scope'}
    (σt₁ : TermSubst Γ Δ₁ σ₁) (σt₂ : TermSubst Γ Δ₂ σ₂)
    (h_subst : Subst.equiv σ₁ σ₂)
    (h_pointwise : ∀ i, HEq (σt₁ i) (σt₂ i)) :
    {T : Ty level scope} → (t : Term Γ T) →
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
  | _, .natZero => by cases h_ctx; exact HEq.refl _
  | _, .natSucc pred => by
    cases h_ctx
    show HEq (Term.natSucc (Term.subst σt₁ pred))
             (Term.natSucc (Term.subst σt₂ pred))
    exact Term.natSucc_HEq_congr _ _
      (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    cases h_ctx
    show HEq
      (Term.natElim (Term.subst σt₁ scrutinee)
                    (Term.subst σt₁ zeroBranch)
                    (Term.subst σt₁ succBranch))
      (Term.natElim (Term.subst σt₂ scrutinee)
                    (Term.subst σt₂ zeroBranch)
                    (Term.subst σt₂ succBranch))
    exact Term.natElim_HEq_congr
      (Ty.subst_congr h_subst result)
      _ _ (eq_of_heq
            (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise scrutinee))
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise zeroBranch)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch => by
    cases h_ctx
    exact Term.natRec_HEq_congr
      (Ty.subst_congr h_subst result)
      _ _ (eq_of_heq
            (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise scrutinee))
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise zeroBranch)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise succBranch)
  | _, .listNil (elementType := elem) => by
    cases h_ctx
    exact Term.listNil_HEq_congr (Ty.subst_congr h_subst elem)
  | _, .listCons (elementType := elem) hd tl => by
    cases h_ctx
    show HEq (Term.listCons (Term.subst σt₁ hd) (Term.subst σt₁ tl))
             (Term.listCons (Term.subst σt₂ hd) (Term.subst σt₂ tl))
    exact Term.listCons_HEq_congr
      (Ty.subst_congr h_subst elem)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise hd)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch => by
    cases h_ctx
    show HEq
      (Term.listElim (Term.subst σt₁ scrutinee)
                     (Term.subst σt₁ nilBranch)
                     (Term.subst σt₁ consBranch))
      (Term.listElim (Term.subst σt₂ scrutinee)
                     (Term.subst σt₂ nilBranch)
                     (Term.subst σt₂ consBranch))
    exact Term.listElim_HEq_congr
      (Ty.subst_congr h_subst elem)
      (Ty.subst_congr h_subst result)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise scrutinee)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise nilBranch)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise consBranch)
  | _, .optionNone (elementType := elem) => by
    cases h_ctx
    exact Term.optionNone_HEq_congr (Ty.subst_congr h_subst elem)
  | _, .optionSome (elementType := elem) v => by
    cases h_ctx
    show HEq (Term.optionSome (Term.subst σt₁ v))
             (Term.optionSome (Term.subst σt₂ v))
    exact Term.optionSome_HEq_congr
      (Ty.subst_congr h_subst elem)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch => by
    cases h_ctx
    show HEq
      (Term.optionMatch (Term.subst σt₁ scrutinee)
                        (Term.subst σt₁ noneBranch)
                        (Term.subst σt₁ someBranch))
      (Term.optionMatch (Term.subst σt₂ scrutinee)
                        (Term.subst σt₂ noneBranch)
                        (Term.subst σt₂ someBranch))
    exact Term.optionMatch_HEq_congr
      (Ty.subst_congr h_subst elem)
      (Ty.subst_congr h_subst result)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise scrutinee)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise noneBranch)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v => by
    cases h_ctx
    exact Term.eitherInl_HEq_congr
      (Ty.subst_congr h_subst lefT)
      (Ty.subst_congr h_subst righT)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v => by
    cases h_ctx
    exact Term.eitherInr_HEq_congr
      (Ty.subst_congr h_subst lefT)
      (Ty.subst_congr h_subst righT)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch => by
    cases h_ctx
    exact Term.eitherMatch_HEq_congr
      (Ty.subst_congr h_subst lefT)
      (Ty.subst_congr h_subst righT)
      (Ty.subst_congr h_subst result)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise scrutinee)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise leftBranch)
      _ _ (Term.subst_HEq_pointwise rfl σt₁ σt₂ h_subst h_pointwise rightBranch)

/-! ## `Term.subst_id_HEq`.

Full HEq form of subst-by-identity.  Structural induction; binder
cases use `Term.subst_HEq_pointwise` to bridge
`TermSubst.lift (TermSubst.identity Γ)` to
`TermSubst.identity (Γ.cons _)` via `lift_identity_pointwise`. -/
theorem Term.subst_id_HEq {m : Mode} {level scope : Nat} {Γ : Ctx m level scope} :
    {T : Ty level scope} → (t : Term Γ T) →
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
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.subst_id_HEq pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim (Term.subst (TermSubst.identity Γ) scrutinee)
                    (Term.subst (TermSubst.identity Γ) zeroBranch)
                    (Term.subst (TermSubst.identity Γ) succBranch))
      (Term.natElim scrutinee zeroBranch succBranch)
    exact Term.natElim_HEq_congr
      (Ty.subst_id result)
      _ _ (eq_of_heq (Term.subst_id_HEq scrutinee))
      _ _ (Term.subst_id_HEq zeroBranch)
      _ _ (Term.subst_id_HEq succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.subst_id result)
      _ _ (eq_of_heq (Term.subst_id_HEq scrutinee))
      _ _ (Term.subst_id_HEq zeroBranch)
      _ _ (Term.subst_id_HEq succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.subst_id elem)
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.subst_id elem)
      _ _ (Term.subst_id_HEq hd)
      _ _ (Term.subst_id_HEq tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.subst_id elem) (Ty.subst_id result)
      _ _ (Term.subst_id_HEq scrutinee)
      _ _ (Term.subst_id_HEq nilBranch)
      _ _ (Term.subst_id_HEq consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.subst_id elem)
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.subst_id elem)
      _ _ (Term.subst_id_HEq v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.subst_id elem) (Ty.subst_id result)
      _ _ (Term.subst_id_HEq scrutinee)
      _ _ (Term.subst_id_HEq noneBranch)
      _ _ (Term.subst_id_HEq someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.subst_id lefT) (Ty.subst_id righT)
      _ _ (Term.subst_id_HEq v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.subst_id lefT) (Ty.subst_id righT)
      _ _ (Term.subst_id_HEq v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.subst_id lefT) (Ty.subst_id righT) (Ty.subst_id result)
      _ _ (Term.subst_id_HEq scrutinee)
      _ _ (Term.subst_id_HEq leftBranch)
      _ _ (Term.subst_id_HEq rightBranch)

/-! ## `Term.subst_id` (explicit-`▸` form).

Corollary of `Term.subst_id_HEq` + `eqRec_heq`. -/
theorem Term.subst_id {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {T : Ty level scope} (t : Term Γ T) :
    (Ty.subst_id T) ▸ Term.subst (TermSubst.identity Γ) t = t :=
  eq_of_heq (HEq.trans (eqRec_heq _ _) (Term.subst_id_HEq t))

/-! ## Cast-through-Term.subst HEq helper.

Pushes a type-cast on the input out through `Term.subst` so the
substitution's structural recursion can fire on the bare
constructor.  Bridge for `lift_compose_pointwise_zero` and the
cast-bearing closed-context commute cases. -/
theorem Term.subst_HEq_cast_input
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ : Subst level scope scope'} (σt : TermSubst Γ Δ σ)
    {T₁ T₂ : Ty level scope} (h : T₁ = T₂) (t : Term Γ T₁) :
    HEq (Term.subst σt (h ▸ t)) (Term.subst σt t) := by
  cases h
  rfl

/-! ## `TermSubst.lift_compose_pointwise` at position 0.

Lifting a composed term-substitution under a binder agrees HEq with
composing the two lifts on the freshly-bound variable.  The position-
`k+1` case requires `Term.subst_weaken_commute_HEq` (binder cases
deferred) and is shipped as a separate companion. -/
theorem TermSubst.lift_compose_pointwise_zero
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {σ₁ : Subst level scope₁ scope₂} {σ₂ : Subst level scope₂ scope₃}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂)
    (newType : Ty level scope₁) :
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

/-! ## `Term.rename_HEq_pointwise`.

Two TermRenamings whose underlying Renamings agree pointwise produce
HEq results when applied to the same term.  The renaming-side analogue
of `Term.subst_HEq_pointwise`.  The `h_ctx : Δ₁ = Δ₂` parameter
accommodates the binder cases, where `TermRenaming.lift ρt_i dom`
lands in `Δ_i.cons (dom.rename ρ_i)` — different cons-extensions
across i = 1, 2. -/
theorem Term.rename_HEq_pointwise
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ₁ Δ₂ : Ctx m level scope'}
    (h_ctx : Δ₁ = Δ₂)
    {ρ₁ ρ₂ : Renaming scope scope'}
    (ρt₁ : TermRenaming Γ Δ₁ ρ₁) (ρt₂ : TermRenaming Γ Δ₂ ρ₂)
    (h_ρ : Renaming.equiv ρ₁ ρ₂) :
    {T : Ty level scope} → (t : Term Γ T) →
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
  | _, .natZero => by cases h_ctx; exact HEq.refl _
  | _, .natSucc pred => by
    cases h_ctx
    show HEq (Term.natSucc (Term.rename ρt₁ pred))
             (Term.natSucc (Term.rename ρt₂ pred))
    exact Term.natSucc_HEq_congr _ _
      (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    cases h_ctx
    show HEq
      (Term.natElim (Term.rename ρt₁ scrutinee)
                    (Term.rename ρt₁ zeroBranch)
                    (Term.rename ρt₁ succBranch))
      (Term.natElim (Term.rename ρt₂ scrutinee)
                    (Term.rename ρt₂ zeroBranch)
                    (Term.rename ρt₂ succBranch))
    exact Term.natElim_HEq_congr
      (Ty.rename_congr h_ρ result)
      _ _ (eq_of_heq (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ scrutinee))
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ zeroBranch)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch => by
    cases h_ctx
    exact Term.natRec_HEq_congr
      (Ty.rename_congr h_ρ result)
      _ _ (eq_of_heq (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ scrutinee))
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ zeroBranch)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ succBranch)
  | _, .listNil (elementType := elem) => by
    cases h_ctx
    exact Term.listNil_HEq_congr (Ty.rename_congr h_ρ elem)
  | _, .listCons (elementType := elem) hd tl => by
    cases h_ctx
    show HEq (Term.listCons (Term.rename ρt₁ hd) (Term.rename ρt₁ tl))
             (Term.listCons (Term.rename ρt₂ hd) (Term.rename ρt₂ tl))
    exact Term.listCons_HEq_congr
      (Ty.rename_congr h_ρ elem)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ hd)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch => by
    cases h_ctx
    show HEq
      (Term.listElim (Term.rename ρt₁ scrutinee)
                     (Term.rename ρt₁ nilBranch)
                     (Term.rename ρt₁ consBranch))
      (Term.listElim (Term.rename ρt₂ scrutinee)
                     (Term.rename ρt₂ nilBranch)
                     (Term.rename ρt₂ consBranch))
    exact Term.listElim_HEq_congr
      (Ty.rename_congr h_ρ elem) (Ty.rename_congr h_ρ result)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ scrutinee)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ nilBranch)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ consBranch)
  | _, .optionNone (elementType := elem) => by
    cases h_ctx
    exact Term.optionNone_HEq_congr (Ty.rename_congr h_ρ elem)
  | _, .optionSome (elementType := elem) v => by
    cases h_ctx
    show HEq (Term.optionSome (Term.rename ρt₁ v))
             (Term.optionSome (Term.rename ρt₂ v))
    exact Term.optionSome_HEq_congr
      (Ty.rename_congr h_ρ elem)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch => by
    cases h_ctx
    show HEq
      (Term.optionMatch (Term.rename ρt₁ scrutinee)
                        (Term.rename ρt₁ noneBranch)
                        (Term.rename ρt₁ someBranch))
      (Term.optionMatch (Term.rename ρt₂ scrutinee)
                        (Term.rename ρt₂ noneBranch)
                        (Term.rename ρt₂ someBranch))
    exact Term.optionMatch_HEq_congr
      (Ty.rename_congr h_ρ elem) (Ty.rename_congr h_ρ result)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ scrutinee)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ noneBranch)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v => by
    cases h_ctx
    exact Term.eitherInl_HEq_congr
      (Ty.rename_congr h_ρ lefT)
      (Ty.rename_congr h_ρ righT)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v => by
    cases h_ctx
    exact Term.eitherInr_HEq_congr
      (Ty.rename_congr h_ρ lefT)
      (Ty.rename_congr h_ρ righT)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch => by
    cases h_ctx
    exact Term.eitherMatch_HEq_congr
      (Ty.rename_congr h_ρ lefT)
      (Ty.rename_congr h_ρ righT)
      (Ty.rename_congr h_ρ result)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ scrutinee)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ leftBranch)
      _ _ (Term.rename_HEq_pointwise rfl ρt₁ ρt₂ h_ρ rightBranch)

/-! ## `Term.rename_id_HEq`.

Renaming-side identity, the companion to `Term.subst_id_HEq` (v1.25):

  HEq (Term.rename (TermRenaming.identity Γ) t) t

Mirrors `Term.subst_id_HEq`'s 12-case structural induction.  Simpler
than the subst version because `TermRenaming` is `Prop`-valued —
the binder cases bridge `TermRenaming.lift (identity Γ) dom` against
`TermRenaming.identity (Γ.cons dom)` directly via
`Term.rename_HEq_pointwise` over `Renaming.lift_identity_equiv`,
without needing a separate `lift_identity_pointwise` stepping stone
(those existed for subst because TermSubst is Type-valued and pointwise
HEq on the witness is non-trivial).

Closed-context cases use the constructor HEq congruences plus
`Ty.rename_identity` at each Ty level index.  Cast-bearing cases
(appPi/pair/snd) strip outer casts via `eqRec_heq`. -/
theorem Term.rename_id_HEq {m : Mode} {level scope : Nat} {Γ : Ctx m level scope} :
    {T : Ty level scope} → (t : Term Γ T) →
      HEq (Term.rename (TermRenaming.identity Γ) t) t
  | _, .var i => by
    -- LHS: (TermRenaming.identity Γ i) ▸ Term.var (Renaming.identity i)
    --    = (Ty.rename_identity (varType Γ i)).symm ▸ Term.var i
    show HEq ((Ty.rename_identity (varType Γ i)).symm ▸ Term.var i) (Term.var i)
    exact eqRec_heq _ _
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.rename (TermRenaming.identity Γ) f)
                (Term.rename (TermRenaming.identity Γ) a))
      (Term.app f a)
    exact Term.app_HEq_congr
      (Ty.rename_identity dom) (Ty.rename_identity cod)
      _ _ (Term.rename_id_HEq f)
      _ _ (Term.rename_id_HEq a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.rename (TermRenaming.identity Γ) p))
      (Term.fst p)
    apply Term.fst_HEq_congr
      (Ty.rename_identity first)
      ((Ty.rename_congr Renaming.lift_identity_equiv second).trans
        (Ty.rename_identity second))
    exact Term.rename_id_HEq p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.rename (TermRenaming.identity Γ) s)
                     (Term.rename (TermRenaming.identity Γ) t)
                     (Term.rename (TermRenaming.identity Γ) e))
      (Term.boolElim s t e)
    exact Term.boolElim_HEq_congr
      (Ty.rename_identity result)
      _ _ (eq_of_heq (Term.rename_id_HEq s))
      _ _ (Term.rename_id_HEq t)
      _ _ (Term.rename_id_HEq e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    -- LHS: (Ty.subst0_rename_commute cod dom Renaming.identity).symm ▸
    --        Term.appPi (Term.rename (identity Γ) f)
    --                   (Term.rename (identity Γ) a)
    show HEq
      ((Ty.subst0_rename_commute cod dom Renaming.identity).symm ▸
        Term.appPi (Term.rename (TermRenaming.identity Γ) f)
                   (Term.rename (TermRenaming.identity Γ) a))
      (Term.appPi f a)
    apply HEq.trans (eqRec_heq _ _)
    exact Term.appPi_HEq_congr
      (Ty.rename_identity dom)
      ((Ty.rename_congr Renaming.lift_identity_equiv cod).trans
        (Ty.rename_identity cod))
      _ _ (Term.rename_id_HEq f)
      _ _ (Term.rename_id_HEq a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    show HEq
      (Term.pair (Term.rename (TermRenaming.identity Γ) v)
        ((Ty.subst0_rename_commute second first Renaming.identity) ▸
          (Term.rename (TermRenaming.identity Γ) w)))
      (Term.pair v w)
    apply Term.pair_HEq_congr
      (Ty.rename_identity first)
      ((Ty.rename_congr Renaming.lift_identity_equiv second).trans
        (Ty.rename_identity second))
      _ _ (Term.rename_id_HEq v)
    apply HEq.trans (eqRec_heq _ _)
    exact Term.rename_id_HEq w
  | _, .snd (firstType := first) (secondType := second) p => by
    show HEq
      ((Ty.subst0_rename_commute second first Renaming.identity).symm ▸
        Term.snd (Term.rename (TermRenaming.identity Γ) p))
      (Term.snd p)
    apply HEq.trans (eqRec_heq _ _)
    apply Term.snd_HEq_congr
      (Ty.rename_identity first)
      ((Ty.rename_congr Renaming.lift_identity_equiv second).trans
        (Ty.rename_identity second))
    exact Term.rename_id_HEq p
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    show HEq
      (Term.lam (codomainType := cod.rename Renaming.identity)
        ((Ty.rename_weaken_commute cod Renaming.identity) ▸
          (Term.rename (TermRenaming.lift (TermRenaming.identity Γ) dom) body)))
      (Term.lam body)
    apply Term.lam_HEq_congr
      (Ty.rename_identity dom) (Ty.rename_identity cod)
    -- Strip outer cast.
    apply HEq.trans (eqRec_heq _ _)
    -- Bridge `TermRenaming.lift (identity Γ) dom` to
    -- `TermRenaming.identity (Γ.cons dom)` via rename_HEq_pointwise
    -- + Renaming.lift_identity_equiv, then recurse.
    apply HEq.trans
      (Term.rename_HEq_pointwise
        (congrArg Γ.cons (Ty.rename_identity dom))
        (TermRenaming.lift (TermRenaming.identity Γ) dom)
        (TermRenaming.identity (Γ.cons dom))
        Renaming.lift_identity_equiv
        body)
    exact Term.rename_id_HEq body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    show HEq
      (Term.lamPi
        (Term.rename (TermRenaming.lift (TermRenaming.identity Γ) dom) body))
      (Term.lamPi body)
    apply Term.lamPi_HEq_congr
      (Ty.rename_identity dom)
      ((Ty.rename_congr Renaming.lift_identity_equiv cod).trans
        (Ty.rename_identity cod))
    apply HEq.trans
      (Term.rename_HEq_pointwise
        (congrArg Γ.cons (Ty.rename_identity dom))
        (TermRenaming.lift (TermRenaming.identity Γ) dom)
        (TermRenaming.identity (Γ.cons dom))
        Renaming.lift_identity_equiv
        body)
    exact Term.rename_id_HEq body
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.rename_id_HEq pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.rename (TermRenaming.identity Γ) scrutinee)
        (Term.rename (TermRenaming.identity Γ) zeroBranch)
        (Term.rename (TermRenaming.identity Γ) succBranch))
      (Term.natElim scrutinee zeroBranch succBranch)
    exact Term.natElim_HEq_congr
      (Ty.rename_identity result)
      _ _ (eq_of_heq (Term.rename_id_HEq scrutinee))
      _ _ (Term.rename_id_HEq zeroBranch)
      _ _ (Term.rename_id_HEq succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.rename_identity result)
      _ _ (eq_of_heq (Term.rename_id_HEq scrutinee))
      _ _ (Term.rename_id_HEq zeroBranch)
      _ _ (Term.rename_id_HEq succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.rename_identity elem)
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.rename_identity elem)
      _ _ (Term.rename_id_HEq hd)
      _ _ (Term.rename_id_HEq tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.rename_identity elem) (Ty.rename_identity result)
      _ _ (Term.rename_id_HEq scrutinee)
      _ _ (Term.rename_id_HEq nilBranch)
      _ _ (Term.rename_id_HEq consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.rename_identity elem)
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.rename_identity elem)
      _ _ (Term.rename_id_HEq v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.rename_identity elem) (Ty.rename_identity result)
      _ _ (Term.rename_id_HEq scrutinee)
      _ _ (Term.rename_id_HEq noneBranch)
      _ _ (Term.rename_id_HEq someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.rename_identity lefT) (Ty.rename_identity righT)
      _ _ (Term.rename_id_HEq v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.rename_identity lefT) (Ty.rename_identity righT)
      _ _ (Term.rename_id_HEq v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.rename_identity lefT) (Ty.rename_identity righT)
      (Ty.rename_identity result)
      _ _ (Term.rename_id_HEq scrutinee)
      _ _ (Term.rename_id_HEq leftBranch)
      _ _ (Term.rename_id_HEq rightBranch)

/-- The explicit-`▸` form of `Term.rename_id`: `eq_of_heq` plus an
outer cast strip.  Mirrors v1.25's `Term.subst_id` derivation from
`Term.subst_id_HEq`. -/
theorem Term.rename_id {m : Mode} {level scope : Nat} {Γ : Ctx m level scope}
    {T : Ty level scope} (t : Term Γ T) :
    (Ty.rename_identity T) ▸ Term.rename (TermRenaming.identity Γ) t = t :=
  eq_of_heq (HEq.trans (eqRec_heq _ _) (Term.rename_id_HEq t))

/-! ## Term-rename composition. -/

/-- Composition of term-level renamings.  Position-equality witness
chains the two `TermRenaming`s through `Ty.rename_compose`. -/
theorem TermRenaming.compose
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
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
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope'} (ρt : TermRenaming Γ Δ ρ)
    {T₁ T₂ : Ty level scope} (h : T₁ = T₂) (t : Term Γ T₁) :
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
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {ρ₁ : Renaming scope₁ scope₂} {ρ₂ : Renaming scope₂ scope₃}
    (ρt₁ : TermRenaming Γ₁ Γ₂ ρ₁) (ρt₂ : TermRenaming Γ₂ Γ₃ ρ₂) :
    {T : Ty level scope₁} → (t : Term Γ₁ T) →
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
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.rename_compose_HEq ρt₁ ρt₂ pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.rename ρt₂ (Term.rename ρt₁ scrutinee))
        (Term.rename ρt₂ (Term.rename ρt₁ zeroBranch))
        (Term.rename ρt₂ (Term.rename ρt₁ succBranch)))
      (Term.natElim
        (Term.rename (TermRenaming.compose ρt₁ ρt₂) scrutinee)
        (Term.rename (TermRenaming.compose ρt₁ ρt₂) zeroBranch)
        (Term.rename (TermRenaming.compose ρt₁ ρt₂) succBranch))
    exact Term.natElim_HEq_congr
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (eq_of_heq (Term.rename_compose_HEq ρt₁ ρt₂ scrutinee))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ zeroBranch)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (eq_of_heq (Term.rename_compose_HEq ρt₁ ρt₂ scrutinee))
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ zeroBranch)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.rename_compose elem ρ₁ ρ₂)
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.rename_compose elem ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ hd)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.rename_compose elem ρ₁ ρ₂)
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ scrutinee)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ nilBranch)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.rename_compose elem ρ₁ ρ₂)
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.rename_compose elem ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.rename_compose elem ρ₁ ρ₂)
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ scrutinee)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ noneBranch)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.rename_compose lefT ρ₁ ρ₂)
      (Ty.rename_compose righT ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.rename_compose lefT ρ₁ ρ₂)
      (Ty.rename_compose righT ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.rename_compose lefT ρ₁ ρ₂)
      (Ty.rename_compose righT ρ₁ ρ₂)
      (Ty.rename_compose result ρ₁ ρ₂)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ scrutinee)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ leftBranch)
      _ _ (Term.rename_compose_HEq ρt₁ ρt₂ rightBranch)

/-! ## `Term.rename_weaken_commute_HEq`.

Term-level analogue of `Ty.rename_weaken_commute`:

  Term.rename (lift ρt X) (Term.weaken X t)
    ≃HEq≃
  Term.weaken (X.rename ρ) (Term.rename ρt t)

Both sides factor into double-rename forms because `Term.weaken X t`
is `Term.rename (TermRenaming.weaken Γ X) t`.  By v1.37 each side
collapses to a single rename along a composed TermRenaming; the two
underlying renamings (`compose Renaming.weaken ρ.lift` and `compose
ρ Renaming.weaken`) are pointwise equal — both reduce to `Fin.succ ∘ ρ`
modulo Fin proof-irrelevance.  The bridge is `Term.rename_HEq_pointwise`
(v1.36) over the trivial pointwise witness. -/
theorem Term.rename_weaken_commute_HEq
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope'} (ρt : TermRenaming Γ Δ ρ)
    (newType : Ty level scope) {T : Ty level scope} (t : Term Γ T) :
    HEq (Term.rename (TermRenaming.lift ρt newType) (Term.weaken newType t))
        (Term.weaken (newType.rename ρ) (Term.rename ρt t)) := by
  -- Unfold both Term.weaken applications into Term.rename.
  show HEq
    (Term.rename (TermRenaming.lift ρt newType)
      (Term.rename (TermRenaming.weaken Γ newType) t))
    (Term.rename (TermRenaming.weaken Δ (newType.rename ρ))
      (Term.rename ρt t))
  -- Collapse LHS via v1.37 to a single composed rename.
  apply HEq.trans
    (Term.rename_compose_HEq
      (TermRenaming.weaken Γ newType)
      (TermRenaming.lift ρt newType)
      t)
  -- Same for RHS, in symm orientation so it lands on the right of HEq.
  apply HEq.symm
  apply HEq.trans
    (Term.rename_compose_HEq
      ρt
      (TermRenaming.weaken Δ (newType.rename ρ))
      t)
  apply HEq.symm
  -- The two composed underlying renamings agree pointwise — `fun _ => rfl`.
  exact Term.rename_HEq_pointwise rfl
    (TermRenaming.compose
      (TermRenaming.weaken Γ newType)
      (TermRenaming.lift ρt newType))
    (TermRenaming.compose ρt
      (TermRenaming.weaken Δ (newType.rename ρ)))
    (fun _ => rfl)
    t

/-! ## Term-level `renameAfter` and its lift commute.

`TermSubst.renameAfter σt ρt` composes a subst with a downstream
rename, producing a subst along `Subst.renameAfter σ ρ`.  The
companion lemma `lift_renameAfter_pointwise` says lifting then
composing agrees with composing then lifting (pointwise HEq) —
the term-level analogue of `Subst.lift_renameAfter_commute`. -/

/-- Term-level `renameAfter`: subst σt then rename ρt to a downstream
context.  At each position, applies σt then renames the result via
ρt; the result type is bridged via `Ty.subst_rename_commute`. -/
def TermSubst.renameAfter
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope_m} {Δ' : Ctx m level scope'}
    {σ : Subst level scope scope_m} {ρ : Renaming scope_m scope'}
    (σt : TermSubst Γ Δ σ) (ρt : TermRenaming Δ Δ' ρ) :
    TermSubst Γ Δ' (Subst.renameAfter σ ρ) := fun i =>
  Ty.subst_rename_commute (varType Γ i) σ ρ ▸ Term.rename ρt (σt i)

/-- Lifting commutes with `renameAfter` pointwise (HEq).  Position 0
reduces both sides to a casted `Term.var ⟨0, _⟩` in propositionally-
distinct cons-extended targets, bridged by `heq_var_across_ctx_eq`
over `Ty.subst_rename_commute newType σ ρ`.  Position `k + 1`
reduces both sides to a `Term.weaken` of `Term.rename ρt (σt k)`
with propositionally-distinct `newType` and inner type — the v1.38
`rename_weaken_commute_HEq` collapses LHS to weaken-of-rename, then
`Term.weaken_HEq_congr` bridges the two `Term.weaken` shapes. -/
theorem TermSubst.lift_renameAfter_pointwise
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope_m} {Δ' : Ctx m level scope'}
    {σ : Subst level scope scope_m} {ρ : Renaming scope_m scope'}
    (σt : TermSubst Γ Δ σ) (ρt : TermRenaming Δ Δ' ρ)
    (newType : Ty level scope) :
    ∀ (i : Fin (scope + 1)),
      HEq
        (TermSubst.renameAfter (σt.lift newType)
          (ρt.lift (newType.subst σ)) i)
        ((TermSubst.renameAfter σt ρt).lift newType i) := by
  -- Bridge the cons-extended target contexts at the type level.
  have h_subst_rename :
      (newType.subst σ).rename ρ = newType.subst (Subst.renameAfter σ ρ) :=
    Ty.subst_rename_commute newType σ ρ
  have h_ctx :
      Δ'.cons ((newType.subst σ).rename ρ)
        = Δ'.cons (newType.subst (Subst.renameAfter σ ρ)) :=
    congrArg Δ'.cons h_subst_rename
  intro i
  match i with
  | ⟨0, h0⟩ =>
    -- LHS reduces to: outer_cast ▸ rename (ρt.lift (newType.subst σ))
    --                              (inner_cast.symm ▸ Term.var ⟨0, _⟩)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_cast_input
        (ρt.lift (newType.subst σ))
        (Ty.subst_weaken_commute newType σ).symm
        (Term.var (context := Δ.cons (newType.subst σ))
          ⟨0, Nat.zero_lt_succ _⟩))
    -- Now: rename (ρt.lift (newType.subst σ)) (Term.var ⟨0, _⟩)
    --    = ((ρt.lift (newType.subst σ)) ⟨0, _⟩) ▸ Term.var (ρ.lift ⟨0, _⟩)
    --    where ρ.lift ⟨0, _⟩ = ⟨0, _⟩ definitionally.
    apply HEq.trans (eqRec_heq _ _)
    -- Naked LHS: Term.var ⟨0, _⟩ in Δ'.cons ((newType.subst σ).rename ρ)
    -- Naked RHS: Term.var ⟨0, _⟩ in Δ'.cons (newType.subst (Subst.renameAfter σ ρ))
    apply HEq.trans
      (heq_var_across_ctx_eq h_ctx ⟨0, Nat.zero_lt_succ _⟩)
    -- RHS = (Ty.subst_weaken_commute newType (Subst.renameAfter σ ρ)).symm
    --        ▸ Term.var ⟨0, _⟩
    exact (eqRec_heq _ _).symm
  | ⟨k + 1, hk⟩ =>
    -- LHS = outer_cast ▸ rename (ρt.lift X)
    --                        (inner_cast.symm ▸ Term.weaken X (σt k'))
    -- where X = newType.subst σ, k' = ⟨k, Nat.lt_of_succ_lt_succ hk⟩.
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_cast_input
        (ρt.lift (newType.subst σ))
        (Ty.subst_weaken_commute
          (varType Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) σ).symm
        (Term.weaken (newType.subst σ)
          (σt ⟨k, Nat.lt_of_succ_lt_succ hk⟩)))
    -- Now: rename (ρt.lift X) (Term.weaken X (σt k'))
    --    ≃HEq≃ Term.weaken (X.rename ρ) (Term.rename ρt (σt k'))    [by v1.38]
    apply HEq.trans
      (Term.rename_weaken_commute_HEq ρt (newType.subst σ)
        (σt ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
    -- Now LHS = Term.weaken ((newType.subst σ).rename ρ)
    --             (Term.rename ρt (σt ⟨k, _⟩))
    -- in target context Δ'.cons ((newType.subst σ).rename ρ).
    --
    -- RHS at k+1 = outer_cast ▸ Term.weaken (newType.subst (renameAfter σ ρ))
    --                              ((renameAfter σt ρt) ⟨k, _⟩)
    --             where (renameAfter σt ρt) ⟨k, _⟩
    --                   = inner_cast ▸ Term.rename ρt (σt ⟨k, _⟩).
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    -- Now: HEq RHS_naked LHS_naked, where
    --   RHS_naked = Term.weaken (newType.subst (renameAfter σ ρ))
    --                 (inner_cast ▸ Term.rename ρt (σt ⟨k, _⟩))
    --   LHS_naked = Term.weaken ((newType.subst σ).rename ρ)
    --                 (Term.rename ρt (σt ⟨k, _⟩))
    -- Bridge via Term.weaken_HEq_congr.
    apply HEq.symm
    -- Use the cast-input helper to push the inner cast on RHS through
    -- Term.weaken — but actually Term.weaken_HEq_congr handles both
    -- newType differences AND a per-side type-cast difference, so we
    -- just supply the HEq.
    exact Term.weaken_HEq_congr
      h_subst_rename
      (Ty.subst_rename_commute
        (varType Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) σ ρ)
      (Term.rename ρt (σt ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
      (_)
      (eqRec_heq _ _).symm

/-! ## Term-level `precompose` and its lift commute.

`TermSubst.precompose ρt σt'` composes a rename with a downstream
subst, producing a subst along `Subst.precompose ρ σ'`.  Companion
lemma `lift_precompose_pointwise` is the structural mirror of
`lift_renameAfter_pointwise` (v1.39). -/

/-- Term-level `precompose`: rename ρt to a Γ' source, then subst σt'.
At each position i, looks up σt' at the renamed position ρ i; the
result type is bridged via the TermRenaming's witness lifted by
`congrArg (·.subst σ')` and chained with `Ty.rename_subst_commute`. -/
def TermSubst.precompose
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Γ' : Ctx m level scope_m} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope_m} {σ' : Subst level scope_m scope'}
    (ρt : TermRenaming Γ Γ' ρ) (σt' : TermSubst Γ' Δ σ') :
    TermSubst Γ Δ (Subst.precompose ρ σ') := fun i =>
  let h_witness : (varType Γ' (ρ i)).subst σ'
                    = ((varType Γ i).rename ρ).subst σ' :=
    congrArg (·.subst σ') (ρt i)
  let h_commute : ((varType Γ i).rename ρ).subst σ'
                    = (varType Γ i).subst (Subst.precompose ρ σ') :=
    Ty.rename_subst_commute (varType Γ i) ρ σ'
  (h_witness.trans h_commute) ▸ σt' (ρ i)

/-- Lifting commutes with `precompose` pointwise (HEq).  Position 0
reduces both sides to a casted `Term.var ⟨0, _⟩` in propositionally-
distinct cons-extended targets bridged by `Ty.rename_subst_commute
newType ρ σ'`.  Position `k + 1` reduces both sides to `Term.weaken`
forms that `Term.weaken_HEq_congr` collapses. -/
theorem TermSubst.lift_precompose_pointwise
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Γ' : Ctx m level scope_m} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope_m} {σ' : Subst level scope_m scope'}
    (ρt : TermRenaming Γ Γ' ρ) (σt' : TermSubst Γ' Δ σ')
    (newType : Ty level scope) :
    ∀ (i : Fin (scope + 1)),
      HEq
        (TermSubst.precompose (ρt.lift newType)
          (σt'.lift (newType.rename ρ)) i)
        ((TermSubst.precompose ρt σt').lift newType i) := by
  have h_rename_subst :
      (newType.rename ρ).subst σ' = newType.subst (Subst.precompose ρ σ') :=
    Ty.rename_subst_commute newType ρ σ'
  have h_ctx :
      Δ.cons ((newType.rename ρ).subst σ')
        = Δ.cons (newType.subst (Subst.precompose ρ σ')) :=
    congrArg Δ.cons h_rename_subst
  intro i
  match i with
  | ⟨0, _⟩ =>
    -- LHS: outer_witness_compose ▸ σt'.lift (newType.rename ρ) ((lift ρt newType) ⟨0, _⟩)
    -- (lift ρt newType) ⟨0, _⟩ = ⟨0, _⟩ definitionally; σt'.lift's 0 arm
    -- emits inner_cast.symm ▸ Term.var ⟨0, _⟩.
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (heq_var_across_ctx_eq h_ctx ⟨0, Nat.zero_lt_succ _⟩)
    exact (eqRec_heq _ _).symm
  | ⟨k + 1, hk⟩ =>
    -- LHS: outer_witness_compose ▸ σt'.lift (newType.rename ρ) (Fin.succ (ρ ⟨k, _⟩))
    --    = outer_witness_compose ▸ (inner_subst_weaken.symm ▸
    --        Term.weaken ((newType.rename ρ).subst σ') (σt' (ρ ⟨k, _⟩)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans (eqRec_heq _ _)
    -- Naked LHS: Term.weaken ((newType.rename ρ).subst σ') (σt' (ρ ⟨k, _⟩))
    -- RHS at k+1: outer ▸ Term.weaken (newType.subst (precompose ρ σ'))
    --                       ((precompose ρt σt') ⟨k, _⟩)
    -- where (precompose ρt σt') ⟨k, _⟩
    --     = (h_w.trans h_c) ▸ σt' (ρ ⟨k, _⟩).
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    -- Apply Term.weaken_HEq_congr.  The h_T equation chains
    -- `congrArg (·.subst σ') (ρt k')` (varType bridge from Γ' to Γ-renamed)
    -- with `Ty.rename_subst_commute` (rename-subst commute), matching the
    -- chain inside `TermSubst.precompose`'s definition.
    exact Term.weaken_HEq_congr
      h_rename_subst
      ((congrArg (·.subst σ')
          (ρt ⟨k, Nat.lt_of_succ_lt_succ hk⟩)).trans
        (Ty.rename_subst_commute
          (varType Γ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) ρ σ'))
      (σt' (ρ ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
      (_)
      (eqRec_heq _ _).symm

/-! ## `Term.subst_rename_commute_HEq`.

Term-level analogue of `Ty.subst_rename_commute`:

  Term.rename ρt (Term.subst σt t)
    ≃HEq≃
  Term.subst (TermSubst.renameAfter σt ρt) t

12-case structural induction on the term.  Closed-context cases
combine the constructor HEq congruence (v1.21) with
`Ty.subst_rename_commute` at each Ty level index.  Cast-bearing cases
(appPi/pair/snd) peel outer casts via `eqRec_heq` and push inner
casts through `Term.{rename,subst}_HEq_cast_input` (v1.26 / v1.37).
Binder cases (lam/lamPi) use the IH at lifted TermSubst/TermRenaming,
then bridge `renameAfter (lift σt dom) (lift ρt (dom.subst σ))`
against `lift (renameAfter σt ρt) dom` via `Term.subst_HEq_pointwise`
(v1.24) over `TermSubst.lift_renameAfter_pointwise` (v1.39). -/
theorem Term.subst_rename_commute_HEq
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope_m} {Δ' : Ctx m level scope'}
    {σ : Subst level scope scope_m} {ρ : Renaming scope_m scope'}
    (σt : TermSubst Γ Δ σ) (ρt : TermRenaming Δ Δ' ρ) :
    {T : Ty level scope} → (t : Term Γ T) →
      HEq (Term.rename ρt (Term.subst σt t))
          (Term.subst (TermSubst.renameAfter σt ρt) t)
  | _, .var i => by
    -- LHS: Term.rename ρt (σt i)
    -- RHS: (renameAfter σt ρt) i = (Ty.subst_rename_commute _ σ ρ) ▸ Term.rename ρt (σt i)
    show HEq (Term.rename ρt (σt i))
             ((Ty.subst_rename_commute (varType Γ i) σ ρ) ▸
                Term.rename ρt (σt i))
    exact (eqRec_heq _ _).symm
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.rename ρt (Term.subst σt f))
                (Term.rename ρt (Term.subst σt a)))
      (Term.app (Term.subst (TermSubst.renameAfter σt ρt) f)
                (Term.subst (TermSubst.renameAfter σt ρt) a))
    exact Term.app_HEq_congr
      (Ty.subst_rename_commute dom σ ρ)
      (Ty.subst_rename_commute cod σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt f)
      _ _ (Term.subst_rename_commute_HEq σt ρt a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.rename ρt (Term.subst σt p)))
      (Term.fst (Term.subst (TermSubst.renameAfter σt ρt) p))
    apply Term.fst_HEq_congr
      (Ty.subst_rename_commute first σ ρ)
      ((Ty.subst_rename_commute second σ.lift ρ.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) second))
    exact Term.subst_rename_commute_HEq σt ρt p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.rename ρt (Term.subst σt s))
                     (Term.rename ρt (Term.subst σt t))
                     (Term.rename ρt (Term.subst σt e)))
      (Term.boolElim (Term.subst (TermSubst.renameAfter σt ρt) s)
                     (Term.subst (TermSubst.renameAfter σt ρt) t)
                     (Term.subst (TermSubst.renameAfter σt ρt) e))
    exact Term.boolElim_HEq_congr
      (Ty.subst_rename_commute result σ ρ)
      _ _ (eq_of_heq (Term.subst_rename_commute_HEq σt ρt s))
      _ _ (Term.subst_rename_commute_HEq σt ρt t)
      _ _ (Term.subst_rename_commute_HEq σt ρt e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    -- LHS: Term.rename ρt (cast_subst.symm ▸ Term.appPi (subst f) (subst a))
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt
        (Ty.subst0_subst_commute cod dom σ).symm
        (Term.appPi (Term.subst σt f) (Term.subst σt a)))
    -- After helper: rename ρt (Term.appPi ...)
    -- Strip outer cast from rename's appPi clause.
    apply HEq.trans (eqRec_heq _ _)
    -- RHS side: (renameAfter σt ρt) on Term.appPi emits cast.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    -- Apply Term.appPi_HEq_congr.
    exact Term.appPi_HEq_congr
      (Ty.subst_rename_commute dom σ ρ)
      ((Ty.subst_rename_commute cod σ.lift ρ.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) cod))
      _ _ (Term.subst_rename_commute_HEq σt ρt f)
      _ _ (Term.subst_rename_commute_HEq σt ρt a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    apply Term.pair_HEq_congr
      (Ty.subst_rename_commute first σ ρ)
      ((Ty.subst_rename_commute second σ.lift ρ.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) second))
      _ _ (Term.subst_rename_commute_HEq σt ρt v)
    -- LHS secondVal: cast_outer_LHS ▸ rename ρt (cast_inner_LHS ▸ subst σt w)
    -- RHS secondVal: cast_compose ▸ subst (renameAfter σt ρt) w
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt
        (Ty.subst0_subst_commute second first σ)
        (Term.subst σt w))
    apply HEq.trans (Term.subst_rename_commute_HEq σt ρt w)
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p => by
    apply HEq.trans
      (Term.rename_HEq_cast_input ρt
        (Ty.subst0_subst_commute second first σ).symm
        (Term.snd (Term.subst σt p)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.snd_HEq_congr
      (Ty.subst_rename_commute first σ ρ)
      ((Ty.subst_rename_commute second σ.lift ρ.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) second))
      _ _ (Term.subst_rename_commute_HEq σt ρt p)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    -- LHS body lives at scope+1; double-traversed via lift σt then lift ρt.
    -- RHS body uses lift (renameAfter σt ρt) dom, pointwise HEq to
    -- renameAfter (lift σt dom) (lift ρt (dom.subst σ)) via v1.39.
    apply Term.lam_HEq_congr
      (Ty.subst_rename_commute dom σ ρ)
      (Ty.subst_rename_commute cod σ ρ)
    -- Strip outer cast on LHS (rename's lam clause).
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through rename (lift ρt (dom.subst σ)).
    apply HEq.trans
      (Term.rename_HEq_cast_input
        (TermRenaming.lift ρt (dom.subst σ))
        (Ty.subst_weaken_commute cod σ)
        (Term.subst (TermSubst.lift σt dom) body))
    -- Use IH on body with the lifts.
    apply HEq.trans
      (Term.subst_rename_commute_HEq
        (TermSubst.lift σt dom)
        (TermRenaming.lift ρt (dom.subst σ))
        body)
    -- Now LHS_naked = Term.subst (renameAfter (lift σt dom)
    --                              (lift ρt (dom.subst σ))) body
    -- Bridge to RHS_naked = Term.subst (lift (renameAfter σt ρt) dom) body
    -- via subst_HEq_pointwise + v1.39.
    apply HEq.symm
    -- Strip outer cast on RHS (subst's lam clause).
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.subst_HEq_pointwise
      (congrArg Δ'.cons (Ty.subst_rename_commute dom σ ρ))
      (TermSubst.renameAfter
        (TermSubst.lift σt dom)
        (TermRenaming.lift ρt (dom.subst σ)))
      ((TermSubst.renameAfter σt ρt).lift dom)
      (Subst.lift_renameAfter_commute σ ρ)
      (TermSubst.lift_renameAfter_pointwise σt ρt dom)
      body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    apply Term.lamPi_HEq_congr
      (Ty.subst_rename_commute dom σ ρ)
      ((Ty.subst_rename_commute cod σ.lift ρ.lift).trans
        (Ty.subst_congr (Subst.lift_renameAfter_commute σ ρ) cod))
    apply HEq.trans
      (Term.subst_rename_commute_HEq
        (TermSubst.lift σt dom)
        (TermRenaming.lift ρt (dom.subst σ))
        body)
    exact Term.subst_HEq_pointwise
      (congrArg Δ'.cons (Ty.subst_rename_commute dom σ ρ))
      (TermSubst.renameAfter
        (TermSubst.lift σt dom)
        (TermRenaming.lift ρt (dom.subst σ)))
      ((TermSubst.renameAfter σt ρt).lift dom)
      (Subst.lift_renameAfter_commute σ ρ)
      (TermSubst.lift_renameAfter_pointwise σt ρt dom)
      body
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.subst_rename_commute_HEq σt ρt pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.rename ρt (Term.subst σt scrutinee))
        (Term.rename ρt (Term.subst σt zeroBranch))
        (Term.rename ρt (Term.subst σt succBranch)))
      (Term.natElim
        (Term.subst (TermSubst.renameAfter σt ρt) scrutinee)
        (Term.subst (TermSubst.renameAfter σt ρt) zeroBranch)
        (Term.subst (TermSubst.renameAfter σt ρt) succBranch))
    exact Term.natElim_HEq_congr
      (Ty.subst_rename_commute result σ ρ)
      _ _ (eq_of_heq (Term.subst_rename_commute_HEq σt ρt scrutinee))
      _ _ (Term.subst_rename_commute_HEq σt ρt zeroBranch)
      _ _ (Term.subst_rename_commute_HEq σt ρt succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.subst_rename_commute result σ ρ)
      _ _ (eq_of_heq (Term.subst_rename_commute_HEq σt ρt scrutinee))
      _ _ (Term.subst_rename_commute_HEq σt ρt zeroBranch)
      _ _ (Term.subst_rename_commute_HEq σt ρt succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.subst_rename_commute elem σ ρ)
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.subst_rename_commute elem σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt hd)
      _ _ (Term.subst_rename_commute_HEq σt ρt tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.subst_rename_commute elem σ ρ)
      (Ty.subst_rename_commute result σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt scrutinee)
      _ _ (Term.subst_rename_commute_HEq σt ρt nilBranch)
      _ _ (Term.subst_rename_commute_HEq σt ρt consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.subst_rename_commute elem σ ρ)
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.subst_rename_commute elem σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.subst_rename_commute elem σ ρ)
      (Ty.subst_rename_commute result σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt scrutinee)
      _ _ (Term.subst_rename_commute_HEq σt ρt noneBranch)
      _ _ (Term.subst_rename_commute_HEq σt ρt someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.subst_rename_commute lefT σ ρ)
      (Ty.subst_rename_commute righT σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.subst_rename_commute lefT σ ρ)
      (Ty.subst_rename_commute righT σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.subst_rename_commute lefT σ ρ)
      (Ty.subst_rename_commute righT σ ρ)
      (Ty.subst_rename_commute result σ ρ)
      _ _ (Term.subst_rename_commute_HEq σt ρt scrutinee)
      _ _ (Term.subst_rename_commute_HEq σt ρt leftBranch)
      _ _ (Term.subst_rename_commute_HEq σt ρt rightBranch)

/-! ## `Term.rename_subst_commute_HEq`.

Term-level analogue of `Ty.rename_subst_commute`:

  Term.subst σt' (Term.rename ρt t)
    ≃HEq≃
  Term.subst (TermSubst.precompose ρt σt') t

Mirrors v1.40 (subst-rename commute) with rename and subst swapped.
12-case structural induction with constructor HEq congruences for
the closed-context cases, outer-cast strips + inner-cast pushes
for the cast-bearing cases, and `Term.subst_HEq_pointwise` over
`TermSubst.lift_precompose_pointwise` (v1.41) for the binder
cases. -/
theorem Term.rename_subst_commute_HEq
    {m : Mode} {level scope scope_m scope' : Nat}
    {Γ : Ctx m level scope} {Γ' : Ctx m level scope_m} {Δ : Ctx m level scope'}
    {ρ : Renaming scope scope_m} {σ' : Subst level scope_m scope'}
    (ρt : TermRenaming Γ Γ' ρ) (σt' : TermSubst Γ' Δ σ') :
    {T : Ty level scope} → (t : Term Γ T) →
      HEq (Term.subst σt' (Term.rename ρt t))
          (Term.subst (TermSubst.precompose ρt σt') t)
  | _, .var i => by
    -- LHS: Term.subst σt' ((ρt i) ▸ Term.var (ρ i)).
    -- Push inner cast through Term.subst.
    apply HEq.trans
      (Term.subst_HEq_cast_input σt' (ρt i)
        (Term.var (context := Γ') (ρ i)))
    -- LHS reduces to σt' (ρ i); RHS = (precompose ρt σt') i,
    -- which by precompose's definition is `chain ▸ σt' (ρ i)`.
    -- Stage the chained equation via `have` so Lean β-reduces the
    -- congrArg-on-lambda before checking the ▸ type alignment.
    have h_witness : (varType Γ' (ρ i)).subst σ'
                       = ((varType Γ i).rename ρ).subst σ' :=
      congrArg (fun T : Ty level scope_m => T.subst σ') (ρt i)
    have h_chain : (varType Γ' (ρ i)).subst σ'
                     = (varType Γ i).subst (Subst.precompose ρ σ') :=
      h_witness.trans
        (Ty.rename_subst_commute (varType Γ i) ρ σ')
    show HEq (σt' (ρ i)) (h_chain ▸ σt' (ρ i))
    exact (eqRec_heq _ _).symm
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.subst σt' (Term.rename ρt f))
                (Term.subst σt' (Term.rename ρt a)))
      (Term.app (Term.subst (TermSubst.precompose ρt σt') f)
                (Term.subst (TermSubst.precompose ρt σt') a))
    exact Term.app_HEq_congr
      (Ty.rename_subst_commute dom ρ σ')
      (Ty.rename_subst_commute cod ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' f)
      _ _ (Term.rename_subst_commute_HEq ρt σt' a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.subst σt' (Term.rename ρt p)))
      (Term.fst (Term.subst (TermSubst.precompose ρt σt') p))
    apply Term.fst_HEq_congr
      (Ty.rename_subst_commute first ρ σ')
      ((Ty.rename_subst_commute second ρ.lift σ'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute ρ σ') second))
    exact Term.rename_subst_commute_HEq ρt σt' p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.subst σt' (Term.rename ρt s))
                     (Term.subst σt' (Term.rename ρt t))
                     (Term.subst σt' (Term.rename ρt e)))
      (Term.boolElim (Term.subst (TermSubst.precompose ρt σt') s)
                     (Term.subst (TermSubst.precompose ρt σt') t)
                     (Term.subst (TermSubst.precompose ρt σt') e))
    exact Term.boolElim_HEq_congr
      (Ty.rename_subst_commute result ρ σ')
      _ _ (eq_of_heq (Term.rename_subst_commute_HEq ρt σt' s))
      _ _ (Term.rename_subst_commute_HEq ρt σt' t)
      _ _ (Term.rename_subst_commute_HEq ρt σt' e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    -- LHS: Term.subst σt' (cast_rename.symm ▸ Term.appPi (rename f) (rename a))
    apply HEq.trans
      (Term.subst_HEq_cast_input σt'
        (Ty.subst0_rename_commute cod dom ρ).symm
        (Term.appPi (Term.rename ρt f) (Term.rename ρt a)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.appPi_HEq_congr
      (Ty.rename_subst_commute dom ρ σ')
      ((Ty.rename_subst_commute cod ρ.lift σ'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute ρ σ') cod))
      _ _ (Term.rename_subst_commute_HEq ρt σt' f)
      _ _ (Term.rename_subst_commute_HEq ρt σt' a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    apply Term.pair_HEq_congr
      (Ty.rename_subst_commute first ρ σ')
      ((Ty.rename_subst_commute second ρ.lift σ'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute ρ σ') second))
      _ _ (Term.rename_subst_commute_HEq ρt σt' v)
    -- LHS secondVal: cast_outer_LHS ▸ subst σt' (cast_inner_LHS ▸ rename ρt w)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_cast_input σt'
        (Ty.subst0_rename_commute second first ρ)
        (Term.rename ρt w))
    apply HEq.trans (Term.rename_subst_commute_HEq ρt σt' w)
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p => by
    apply HEq.trans
      (Term.subst_HEq_cast_input σt'
        (Ty.subst0_rename_commute second first ρ).symm
        (Term.snd (Term.rename ρt p)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.snd_HEq_congr
      (Ty.rename_subst_commute first ρ σ')
      ((Ty.rename_subst_commute second ρ.lift σ'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute ρ σ') second))
      _ _ (Term.rename_subst_commute_HEq ρt σt' p)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    apply Term.lam_HEq_congr
      (Ty.rename_subst_commute dom ρ σ')
      (Ty.rename_subst_commute cod ρ σ')
    -- Strip outer cast on LHS (subst's lam clause).
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through subst (lift σt' (dom.rename ρ)).
    apply HEq.trans
      (Term.subst_HEq_cast_input
        (TermSubst.lift σt' (dom.rename ρ))
        (Ty.rename_weaken_commute cod ρ)
        (Term.rename (TermRenaming.lift ρt dom) body))
    -- Use IH on body with the lifts.
    apply HEq.trans
      (Term.rename_subst_commute_HEq
        (TermRenaming.lift ρt dom)
        (TermSubst.lift σt' (dom.rename ρ))
        body)
    -- Bridge via subst_HEq_pointwise + v1.41.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.subst_HEq_pointwise
      (congrArg Δ.cons (Ty.rename_subst_commute dom ρ σ'))
      (TermSubst.precompose
        (TermRenaming.lift ρt dom)
        (TermSubst.lift σt' (dom.rename ρ)))
      ((TermSubst.precompose ρt σt').lift dom)
      (Subst.lift_precompose_commute ρ σ')
      (TermSubst.lift_precompose_pointwise ρt σt' dom)
      body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    apply Term.lamPi_HEq_congr
      (Ty.rename_subst_commute dom ρ σ')
      ((Ty.rename_subst_commute cod ρ.lift σ'.lift).trans
        (Ty.subst_congr (Subst.lift_precompose_commute ρ σ') cod))
    apply HEq.trans
      (Term.rename_subst_commute_HEq
        (TermRenaming.lift ρt dom)
        (TermSubst.lift σt' (dom.rename ρ))
        body)
    exact Term.subst_HEq_pointwise
      (congrArg Δ.cons (Ty.rename_subst_commute dom ρ σ'))
      (TermSubst.precompose
        (TermRenaming.lift ρt dom)
        (TermSubst.lift σt' (dom.rename ρ)))
      ((TermSubst.precompose ρt σt').lift dom)
      (Subst.lift_precompose_commute ρ σ')
      (TermSubst.lift_precompose_pointwise ρt σt' dom)
      body
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.rename_subst_commute_HEq ρt σt' pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.subst σt' (Term.rename ρt scrutinee))
        (Term.subst σt' (Term.rename ρt zeroBranch))
        (Term.subst σt' (Term.rename ρt succBranch)))
      (Term.natElim
        (Term.subst (TermSubst.precompose ρt σt') scrutinee)
        (Term.subst (TermSubst.precompose ρt σt') zeroBranch)
        (Term.subst (TermSubst.precompose ρt σt') succBranch))
    exact Term.natElim_HEq_congr
      (Ty.rename_subst_commute result ρ σ')
      _ _ (eq_of_heq (Term.rename_subst_commute_HEq ρt σt' scrutinee))
      _ _ (Term.rename_subst_commute_HEq ρt σt' zeroBranch)
      _ _ (Term.rename_subst_commute_HEq ρt σt' succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.rename_subst_commute result ρ σ')
      _ _ (eq_of_heq (Term.rename_subst_commute_HEq ρt σt' scrutinee))
      _ _ (Term.rename_subst_commute_HEq ρt σt' zeroBranch)
      _ _ (Term.rename_subst_commute_HEq ρt σt' succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.rename_subst_commute elem ρ σ')
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.rename_subst_commute elem ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' hd)
      _ _ (Term.rename_subst_commute_HEq ρt σt' tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.rename_subst_commute elem ρ σ')
      (Ty.rename_subst_commute result ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' scrutinee)
      _ _ (Term.rename_subst_commute_HEq ρt σt' nilBranch)
      _ _ (Term.rename_subst_commute_HEq ρt σt' consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.rename_subst_commute elem ρ σ')
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.rename_subst_commute elem ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.rename_subst_commute elem ρ σ')
      (Ty.rename_subst_commute result ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' scrutinee)
      _ _ (Term.rename_subst_commute_HEq ρt σt' noneBranch)
      _ _ (Term.rename_subst_commute_HEq ρt σt' someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.rename_subst_commute lefT ρ σ')
      (Ty.rename_subst_commute righT ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.rename_subst_commute lefT ρ σ')
      (Ty.rename_subst_commute righT ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.rename_subst_commute lefT ρ σ')
      (Ty.rename_subst_commute righT ρ σ')
      (Ty.rename_subst_commute result ρ σ')
      _ _ (Term.rename_subst_commute_HEq ρt σt' scrutinee)
      _ _ (Term.rename_subst_commute_HEq ρt σt' leftBranch)
      _ _ (Term.rename_subst_commute_HEq ρt σt' rightBranch)

/-! ## `Term.subst_weaken_commute_HEq`.

Term-level analogue of `Ty.subst_weaken_commute`:

  Term.subst (σt.lift X) (Term.weaken X t)
    ≃HEq≃
  Term.weaken (X.subst σ) (Term.subst σt t)

Direct corollary of v1.40 + v1.42 — no fresh structural induction.
Both sides factor into rename/subst forms (since `Term.weaken X t`
is `Term.rename (TermRenaming.weaken Γ X) t`).  v1.42 collapses
LHS to `Term.subst (precompose (weaken Γ X) (σt.lift X)) t`; v1.40
collapses RHS to `Term.subst (renameAfter σt (weaken Δ (X.subst σ))) t`.
The two underlying Substs (`precompose Renaming.weaken σ.lift` and
`renameAfter σ Renaming.weaken`) are pointwise rfl-equal — both
reduce to `(σ i).weaken`.  `Term.subst_HEq_pointwise` (v1.24)
bridges them.

This subsumes the v1.28–v1.33 standalone closed-context case
lemmas (`Term.subst_weaken_commute_HEq_{var,unit,boolTrue,boolFalse,
app,boolElim,fst,snd,pair,appPi}`); the binder cases (`lam`,
`lamPi`) that were missing in those layered theorems are now
covered by the same corollary.  Mirrors v1.38 exactly. -/
theorem Term.subst_weaken_commute_HEq
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ : Subst level scope scope'} (σt : TermSubst Γ Δ σ)
    (newType : Ty level scope) {T : Ty level scope} (t : Term Γ T) :
    HEq (Term.subst (σt.lift newType) (Term.weaken newType t))
        (Term.weaken (newType.subst σ) (Term.subst σt t)) := by
  -- Unfold both Term.weaken applications into Term.rename.
  show HEq
    (Term.subst (σt.lift newType)
      (Term.rename (TermRenaming.weaken Γ newType) t))
    (Term.rename (TermRenaming.weaken Δ (newType.subst σ))
      (Term.subst σt t))
  -- Collapse LHS via v1.42 to a single composed subst.
  apply HEq.trans
    (Term.rename_subst_commute_HEq
      (TermRenaming.weaken Γ newType)
      (σt.lift newType)
      t)
  -- Same for RHS via v1.40, in symm orientation.
  apply HEq.symm
  apply HEq.trans
    (Term.subst_rename_commute_HEq
      σt
      (TermRenaming.weaken Δ (newType.subst σ))
      t)
  apply HEq.symm
  -- The two composed underlying Substs agree pointwise — `fun _ => rfl`.
  -- The pointwise HEq between the term-level composed TermSubsts
  -- follows from the cast-strip identity: at each i both reduce
  -- (modulo casts) to `Term.weaken (newType.subst σ) (σt i)`.
  exact Term.subst_HEq_pointwise rfl
    (TermSubst.precompose
      (TermRenaming.weaken Γ newType) (σt.lift newType))
    (TermSubst.renameAfter σt
      (TermRenaming.weaken Δ (newType.subst σ)))
    (fun _ => rfl)
    (fun _ => by
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.trans (eqRec_heq _ _)
      apply HEq.symm
      exact eqRec_heq _ _)
    t

/-! ## `TermSubst.lift_compose_pointwise` (full theorem).

Lifting commutes with TermSubst composition pointwise (HEq).  Position 0
delegates to the existing `lift_compose_pointwise_zero` fragment.
Position `k + 1` is the substantive case:

  * LHS at `k+1`: `outer_subst_weaken_commute.symm ▸ Term.weaken
    (newType.subst (Subst.compose σ₁ σ₂)) (Ty.subst_compose ...
    ▸ Term.subst σt₂ (σt₁ k'))`.

  * RHS at `k+1`: `outer_subst_compose ▸ Term.subst (σt₂.lift
    (newType.subst σ₁)) ((Ty.subst_weaken_commute ...).symm ▸
    Term.weaken (newType.subst σ₁) (σt₁ k'))`.

The RHS inner reduces, via `Term.subst_HEq_cast_input` + v1.43
`Term.subst_weaken_commute_HEq`, to `Term.weaken ((newType.subst
σ₁).subst σ₂) (Term.subst σt₂ (σt₁ k'))`.  The two `Term.weaken`
forms differ only by `Ty.subst_compose newType σ₁ σ₂` on the
`newType` and the per-position analogue on the inner type;
`Term.weaken_HEq_congr` closes via `eqRec_heq`. -/
theorem TermSubst.lift_compose_pointwise
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {σ₁ : Subst level scope₁ scope₂} {σ₂ : Subst level scope₂ scope₃}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂)
    (newType : Ty level scope₁) :
    ∀ (i : Fin (scope₁ + 1)),
      HEq
        (TermSubst.lift (TermSubst.compose σt₁ σt₂) newType i)
        (TermSubst.compose (σt₁.lift newType)
          (σt₂.lift (newType.subst σ₁)) i)
  | ⟨0, _⟩ =>
      TermSubst.lift_compose_pointwise_zero σt₁ σt₂ newType
  | ⟨k + 1, hk⟩ => by
    -- Strip outer cast on LHS.
    apply HEq.trans (eqRec_heq _ _)
    -- Flip and strip outer cast on RHS.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast on RHS through Term.subst.
    apply HEq.trans
      (Term.subst_HEq_cast_input
        (σt₂.lift (newType.subst σ₁))
        (Ty.subst_weaken_commute
          (varType Γ₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) σ₁).symm
        (Term.weaken (newType.subst σ₁)
          (σt₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩)))
    -- After helper: Term.subst (σt₂.lift X) (Term.weaken X (σt₁ k')).
    -- Apply v1.43 to get Term.weaken (X.subst σ₂) (Term.subst σt₂ (σt₁ k')).
    apply HEq.trans
      (Term.subst_weaken_commute_HEq
        σt₂ (newType.subst σ₁)
        (σt₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
    -- Flip back to LHS-orientation.
    apply HEq.symm
    -- Apply Term.weaken_HEq_congr.
    exact Term.weaken_HEq_congr
      (Ty.subst_compose newType σ₁ σ₂).symm
      (Ty.subst_compose
        (varType Γ₁ ⟨k, Nat.lt_of_succ_lt_succ hk⟩) σ₁ σ₂).symm
      _ _ (eqRec_heq _ _)

/-! ## `Term.subst_compose`.

The cap-stone of substitution functoriality at the term level:

  Term.subst σt₂ (Term.subst σt₁ t)
    ≃HEq≃
  Term.subst (TermSubst.compose σt₁ σt₂) t

Both sides have type `Term Γ₃ T'` for propositionally-equal `T'`s
(`((T.subst σ₁).subst σ₂)` vs `T.subst (Subst.compose σ₁ σ₂)`,
bridged by `Ty.subst_compose`).  HEq carries the difference.

12-case structural induction on the term.

  * Closed-context cases (var, unit/boolTrue/boolFalse, app, fst,
    boolElim) combine constructor HEq congruences with
    `Ty.subst_compose` at each Ty level index.
  * Cast-bearing cases (appPi/pair/snd) peel outer casts via
    `eqRec_heq` and push inner casts through
    `Term.subst_HEq_cast_input`.  The sigmaTy/piTy second-component
    bridge chains `Ty.subst_compose` at scope+1 with
    `Subst.lift_compose_equiv`.
  * Binder cases (lam, lamPi) recurse via the IH at lifted
    TermSubsts (`lift σt₁ dom` and `lift σt₂ (dom.subst σ₁)`),
    then bridge `compose (lift σt₁) (lift σt₂)` against
    `lift (compose σt₁ σt₂)` via `Term.subst_HEq_pointwise` (v1.24)
    over `TermSubst.lift_compose_pointwise` (v1.44).

Mirrors v1.40 / v1.42 with subst on both sides instead of mixed
subst+rename. -/
theorem Term.subst_compose_HEq
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {σ₁ : Subst level scope₁ scope₂} {σ₂ : Subst level scope₂ scope₃}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂) :
    {T : Ty level scope₁} → (t : Term Γ₁ T) →
      HEq (Term.subst σt₂ (Term.subst σt₁ t))
          (Term.subst (TermSubst.compose σt₁ σt₂) t)
  | _, .var i => by
    -- LHS: Term.subst σt₂ (σt₁ i).
    -- RHS: (compose σt₁ σt₂) i = (Ty.subst_compose ...) ▸ Term.subst σt₂ (σt₁ i).
    show HEq (Term.subst σt₂ (σt₁ i))
      ((Ty.subst_compose (varType Γ₁ i) σ₁ σ₂)
        ▸ Term.subst σt₂ (σt₁ i))
    exact (eqRec_heq _ _).symm
  | _, .unit => HEq.refl _
  | _, .boolTrue => HEq.refl _
  | _, .boolFalse => HEq.refl _
  | _, .app (domainType := dom) (codomainType := cod) f a => by
    show HEq
      (Term.app (Term.subst σt₂ (Term.subst σt₁ f))
                (Term.subst σt₂ (Term.subst σt₁ a)))
      (Term.app (Term.subst (TermSubst.compose σt₁ σt₂) f)
                (Term.subst (TermSubst.compose σt₁ σt₂) a))
    exact Term.app_HEq_congr
      (Ty.subst_compose dom σ₁ σ₂)
      (Ty.subst_compose cod σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ f)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ a)
  | _, .fst (firstType := first) (secondType := second) p => by
    show HEq
      (Term.fst (Term.subst σt₂ (Term.subst σt₁ p)))
      (Term.fst (Term.subst (TermSubst.compose σt₁ σt₂) p))
    apply Term.fst_HEq_congr
      (Ty.subst_compose first σ₁ σ₂)
      ((Ty.subst_compose second σ₁.lift σ₂.lift).trans
        (Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) second))
    exact Term.subst_compose_HEq σt₁ σt₂ p
  | _, .boolElim (resultType := result) s t e => by
    show HEq
      (Term.boolElim (Term.subst σt₂ (Term.subst σt₁ s))
                     (Term.subst σt₂ (Term.subst σt₁ t))
                     (Term.subst σt₂ (Term.subst σt₁ e)))
      (Term.boolElim (Term.subst (TermSubst.compose σt₁ σt₂) s)
                     (Term.subst (TermSubst.compose σt₁ σt₂) t)
                     (Term.subst (TermSubst.compose σt₁ σt₂) e))
    exact Term.boolElim_HEq_congr
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (eq_of_heq (Term.subst_compose_HEq σt₁ σt₂ s))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ t)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ e)
  | _, .appPi (domainType := dom) (codomainType := cod) f a => by
    apply HEq.trans
      (Term.subst_HEq_cast_input σt₂
        (Ty.subst0_subst_commute cod dom σ₁).symm
        (Term.appPi (Term.subst σt₁ f) (Term.subst σt₁ a)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.appPi_HEq_congr
      (Ty.subst_compose dom σ₁ σ₂)
      ((Ty.subst_compose cod σ₁.lift σ₂.lift).trans
        (Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) cod))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ f)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ a)
  | _, .pair (firstType := first) (secondType := second) v w => by
    apply Term.pair_HEq_congr
      (Ty.subst_compose first σ₁ σ₂)
      ((Ty.subst_compose second σ₁.lift σ₂.lift).trans
        (Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) second))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ v)
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.trans
      (Term.subst_HEq_cast_input σt₂
        (Ty.subst0_subst_commute second first σ₁)
        (Term.subst σt₁ w))
    apply HEq.trans (Term.subst_compose_HEq σt₁ σt₂ w)
    exact (eqRec_heq _ _).symm
  | _, .snd (firstType := first) (secondType := second) p => by
    apply HEq.trans
      (Term.subst_HEq_cast_input σt₂
        (Ty.subst0_subst_commute second first σ₁).symm
        (Term.snd (Term.subst σt₁ p)))
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.snd_HEq_congr
      (Ty.subst_compose first σ₁ σ₂)
      ((Ty.subst_compose second σ₁.lift σ₂.lift).trans
        (Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) second))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ p)
  | _, .lam (domainType := dom) (codomainType := cod) body => by
    apply Term.lam_HEq_congr
      (Ty.subst_compose dom σ₁ σ₂)
      (Ty.subst_compose cod σ₁ σ₂)
    -- Strip outer cast on LHS.
    apply HEq.trans (eqRec_heq _ _)
    -- Push inner cast through Term.subst.
    apply HEq.trans
      (Term.subst_HEq_cast_input
        (TermSubst.lift σt₂ (dom.subst σ₁))
        (Ty.subst_weaken_commute cod σ₁)
        (Term.subst (TermSubst.lift σt₁ dom) body))
    -- IH on body with the lifts.
    apply HEq.trans
      (Term.subst_compose_HEq
        (TermSubst.lift σt₁ dom)
        (TermSubst.lift σt₂ (dom.subst σ₁))
        body)
    -- Bridge compose-of-lifts to lift-of-compose.
    apply HEq.symm
    apply HEq.trans (eqRec_heq _ _)
    apply HEq.symm
    exact Term.subst_HEq_pointwise
      (congrArg Γ₃.cons (Ty.subst_compose dom σ₁ σ₂))
      (TermSubst.compose
        (TermSubst.lift σt₁ dom)
        (TermSubst.lift σt₂ (dom.subst σ₁)))
      (TermSubst.lift (TermSubst.compose σt₁ σt₂) dom)
      (Subst.lift_compose_equiv σ₁ σ₂)
      (fun i =>
        (TermSubst.lift_compose_pointwise σt₁ σt₂ dom i).symm)
      body
  | _, .lamPi (domainType := dom) (codomainType := cod) body => by
    apply Term.lamPi_HEq_congr
      (Ty.subst_compose dom σ₁ σ₂)
      ((Ty.subst_compose cod σ₁.lift σ₂.lift).trans
        (Ty.subst_congr (Subst.lift_compose_equiv σ₁ σ₂) cod))
    apply HEq.trans
      (Term.subst_compose_HEq
        (TermSubst.lift σt₁ dom)
        (TermSubst.lift σt₂ (dom.subst σ₁))
        body)
    exact Term.subst_HEq_pointwise
      (congrArg Γ₃.cons (Ty.subst_compose dom σ₁ σ₂))
      (TermSubst.compose
        (TermSubst.lift σt₁ dom)
        (TermSubst.lift σt₂ (dom.subst σ₁)))
      (TermSubst.lift (TermSubst.compose σt₁ σt₂) dom)
      (Subst.lift_compose_equiv σ₁ σ₂)
      (fun i =>
        (TermSubst.lift_compose_pointwise σt₁ σt₂ dom i).symm)
      body
  | _, .natZero => HEq.refl _
  | _, .natSucc pred =>
    Term.natSucc_HEq_congr _ _ (Term.subst_compose_HEq σt₁ σt₂ pred)
  | _, .natElim (resultType := result) scrutinee zeroBranch succBranch => by
    show HEq
      (Term.natElim
        (Term.subst σt₂ (Term.subst σt₁ scrutinee))
        (Term.subst σt₂ (Term.subst σt₁ zeroBranch))
        (Term.subst σt₂ (Term.subst σt₁ succBranch)))
      (Term.natElim
        (Term.subst (TermSubst.compose σt₁ σt₂) scrutinee)
        (Term.subst (TermSubst.compose σt₁ σt₂) zeroBranch)
        (Term.subst (TermSubst.compose σt₁ σt₂) succBranch))
    exact Term.natElim_HEq_congr
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (eq_of_heq (Term.subst_compose_HEq σt₁ σt₂ scrutinee))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ zeroBranch)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ succBranch)
  | _, .natRec (resultType := result) scrutinee zeroBranch succBranch =>
    Term.natRec_HEq_congr
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (eq_of_heq (Term.subst_compose_HEq σt₁ σt₂ scrutinee))
      _ _ (Term.subst_compose_HEq σt₁ σt₂ zeroBranch)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ succBranch)
  | _, .listNil (elementType := elem) =>
    Term.listNil_HEq_congr (Ty.subst_compose elem σ₁ σ₂)
  | _, .listCons (elementType := elem) hd tl =>
    Term.listCons_HEq_congr
      (Ty.subst_compose elem σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ hd)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ tl)
  | _, .listElim (elementType := elem) (resultType := result)
        scrutinee nilBranch consBranch =>
    Term.listElim_HEq_congr
      (Ty.subst_compose elem σ₁ σ₂)
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ scrutinee)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ nilBranch)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ consBranch)
  | _, .optionNone (elementType := elem) =>
    Term.optionNone_HEq_congr (Ty.subst_compose elem σ₁ σ₂)
  | _, .optionSome (elementType := elem) v =>
    Term.optionSome_HEq_congr
      (Ty.subst_compose elem σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ v)
  | _, .optionMatch (elementType := elem) (resultType := result)
        scrutinee noneBranch someBranch =>
    Term.optionMatch_HEq_congr
      (Ty.subst_compose elem σ₁ σ₂)
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ scrutinee)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ noneBranch)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ someBranch)
  | _, .eitherInl (leftType := lefT) (rightType := righT) v =>
    Term.eitherInl_HEq_congr
      (Ty.subst_compose lefT σ₁ σ₂)
      (Ty.subst_compose righT σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ v)
  | _, .eitherInr (leftType := lefT) (rightType := righT) v =>
    Term.eitherInr_HEq_congr
      (Ty.subst_compose lefT σ₁ σ₂)
      (Ty.subst_compose righT σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ v)
  | _, .eitherMatch (leftType := lefT) (rightType := righT) (resultType := result)
        scrutinee leftBranch rightBranch =>
    Term.eitherMatch_HEq_congr
      (Ty.subst_compose lefT σ₁ σ₂)
      (Ty.subst_compose righT σ₁ σ₂)
      (Ty.subst_compose result σ₁ σ₂)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ scrutinee)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ leftBranch)
      _ _ (Term.subst_compose_HEq σt₁ σt₂ rightBranch)

/-- The explicit-`▸` form of `Term.subst_compose`: `eq_of_heq` plus
the outer cast strip.  Mirrors the v1.25 derivation of `Term.subst_id`
from `Term.subst_id_HEq`. -/
theorem Term.subst_compose
    {m : Mode} {level scope₁ scope₂ scope₃ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂} {Γ₃ : Ctx m level scope₃}
    {σ₁ : Subst level scope₁ scope₂} {σ₂ : Subst level scope₂ scope₃}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂)
    {T : Ty level scope₁} (t : Term Γ₁ T) :
    Term.subst σt₂ (Term.subst σt₁ t)
      = (Ty.subst_compose T σ₁ σ₂).symm
          ▸ Term.subst (TermSubst.compose σt₁ σt₂) t :=
  eq_of_heq
    ((Term.subst_compose_HEq σt₁ σt₂ t).trans (eqRec_heq _ _).symm)

/-! ## Categorical-structure laws on TermSubst (pointwise HEq).

Term-level analogues of the Ty-level monoid laws (`Subst.compose_*`).
Together with `Term.subst_id` (v1.25) and `Term.subst_compose` (v1.45)
they establish `(Ty, TermSubst, Term.subst)` as a category enriched
over `Ty` at the term level — identity is unital on both sides and
composition is associative.  Stated as pointwise HEq (per Fin position)
because `TermSubst` is Type-valued and per-position values can have
propositionally-distinct types between LHS and RHS. -/

/-- Composing the identity TermSubst on the left leaves a TermSubst
pointwise unchanged.  At each position, LHS is
`outer_cast ▸ Term.subst σt (inner_cast.symm ▸ Term.var i)`; cast
through `Term.subst_HEq_cast_input` and the var arm of `Term.subst`
collapses to `σt i`. -/
theorem TermSubst.compose_identity_left_pointwise
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ : Subst level scope scope'} (σt : TermSubst Γ Δ σ) :
    ∀ i, HEq (TermSubst.compose (TermSubst.identity Γ) σt i) (σt i) := by
  intro i
  -- Strip outer cast from TermSubst.compose's definition.
  apply HEq.trans (eqRec_heq _ _)
  -- Push inner cast through Term.subst.
  apply HEq.trans
    (Term.subst_HEq_cast_input σt
      (Ty.subst_id (varType Γ i)).symm
      (Term.var (context := Γ) i))
  -- Term.subst σt (Term.var i) reduces definitionally to σt i.
  exact HEq.refl _

/-- Composing the identity TermSubst on the right leaves a TermSubst
pointwise unchanged.  At each position, the inner `Term.subst (identity
Δ) (σt i)` collapses via `Term.subst_id_HEq` (v1.25). -/
theorem TermSubst.compose_identity_right_pointwise
    {m : Mode} {level scope scope' : Nat}
    {Γ : Ctx m level scope} {Δ : Ctx m level scope'}
    {σ : Subst level scope scope'} (σt : TermSubst Γ Δ σ) :
    ∀ i, HEq (TermSubst.compose σt (TermSubst.identity Δ) i) (σt i) := by
  intro i
  apply HEq.trans (eqRec_heq _ _)
  exact Term.subst_id_HEq (σt i)

/-- TermSubst composition is associative pointwise.  At each position,
LHS naked is `Term.subst (compose σt₂ σt₃) (σt₁ i)`, which by
`Term.subst_compose_HEq` (v1.45, applied .symm) equals
`Term.subst σt₃ (Term.subst σt₂ (σt₁ i))`.  RHS naked is the same
expression after pushing its inner `Ty.subst_compose` cast through
the outer `Term.subst σt₃` via `Term.subst_HEq_cast_input`. -/
theorem TermSubst.compose_assoc_pointwise
    {m : Mode} {level scope₁ scope₂ scope₃ scope₄ : Nat}
    {Γ₁ : Ctx m level scope₁} {Γ₂ : Ctx m level scope₂}
    {Γ₃ : Ctx m level scope₃} {Γ₄ : Ctx m level scope₄}
    {σ₁ : Subst level scope₁ scope₂}
    {σ₂ : Subst level scope₂ scope₃}
    {σ₃ : Subst level scope₃ scope₄}
    (σt₁ : TermSubst Γ₁ Γ₂ σ₁) (σt₂ : TermSubst Γ₂ Γ₃ σ₂)
    (σt₃ : TermSubst Γ₃ Γ₄ σ₃) :
    ∀ i, HEq
      (TermSubst.compose σt₁ (TermSubst.compose σt₂ σt₃) i)
      (TermSubst.compose (TermSubst.compose σt₁ σt₂) σt₃ i) := by
  intro i
  -- Strip outer cast on LHS.
  apply HEq.trans (eqRec_heq _ _)
  -- LHS naked: Term.subst (compose σt₂ σt₃) (σt₁ i).
  -- By v1.45.symm: ≃HEq≃ Term.subst σt₃ (Term.subst σt₂ (σt₁ i)).
  apply HEq.trans
    (Term.subst_compose_HEq σt₂ σt₃ (σt₁ i)).symm
  -- Strip outer cast on RHS (via symm orientation).
  apply HEq.symm
  apply HEq.trans (eqRec_heq _ _)
  -- RHS naked: Term.subst σt₃ ((compose σt₁ σt₂) i)
  --          = Term.subst σt₃ (cast ▸ Term.subst σt₂ (σt₁ i)).
  -- Push the inner cast through Term.subst σt₃.
  exact Term.subst_HEq_cast_input σt₃
    (Ty.subst_compose (varType Γ₁ i) σ₁ σ₂)
    (Term.subst σt₂ (σt₁ i))

/-! ## Typed reduction (`Step`, `StepStar`).

`Step t₁ t₂` is `Prop`-valued and shares its `{ctx} {T}` indices
between sides — so subject reduction is **structural**: every
`Step` proof produces a same-typed reduct by signature alone, no
preservation theorem needed.  Covers congruence, β (`betaApp`,
`betaAppPi`), Σ projections (`betaFstPair`, `betaSndPair`),
η contractions, and boolean ι rules. -/

/-- Single-step reduction between terms of the same type. -/
inductive Step :
    {mode : Mode} → {level scope : Nat} → {ctx : Ctx mode level scope} →
    {T : Ty level scope} → Term ctx T → Term ctx T → Prop
  /-- Step inside the function position of a non-dependent application. -/
  | appLeft  :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {functionTerm functionTerm' :
          Term ctx (.arrow domainType codomainType)}
        {argumentTerm : Term ctx domainType},
      Step functionTerm functionTerm' →
      Step (Term.app functionTerm argumentTerm)
           (Term.app functionTerm' argumentTerm)
  /-- Step inside the argument position of a non-dependent application. -/
  | appRight :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {functionTerm : Term ctx (.arrow domainType codomainType)}
        {argumentTerm argumentTerm' : Term ctx domainType},
      Step argumentTerm argumentTerm' →
      Step (Term.app functionTerm argumentTerm)
           (Term.app functionTerm argumentTerm')
  /-- Step inside the body of a non-dependent λ-abstraction. -/
  | lamBody  :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {body body' : Term (ctx.cons domainType) codomainType.weaken},
      Step body body' →
      Step (Term.lam (codomainType := codomainType) body)
           (Term.lam (codomainType := codomainType) body')
  /-- Step inside the function position of a dependent application. -/
  | appPiLeft :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        {functionTerm functionTerm' :
          Term ctx (.piTy domainType codomainType)}
        {argumentTerm : Term ctx domainType},
      Step functionTerm functionTerm' →
      Step (Term.appPi functionTerm argumentTerm)
           (Term.appPi functionTerm' argumentTerm)
  /-- Step inside the argument position of a dependent application. -/
  | appPiRight :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        {functionTerm : Term ctx (.piTy domainType codomainType)}
        {argumentTerm argumentTerm' : Term ctx domainType},
      Step argumentTerm argumentTerm' →
      Step (Term.appPi functionTerm argumentTerm)
           (Term.appPi functionTerm argumentTerm')
  /-- Step inside the body of a dependent λ-abstraction. -/
  | lamPiBody :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        {body body' : Term (ctx.cons domainType) codomainType},
      Step body body' →
      Step (Term.lamPi (domainType := domainType) body)
           (Term.lamPi (domainType := domainType) body')
  /-- Step inside the first component of a pair. -/
  | pairLeft :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {firstVal firstVal' : Term ctx firstType}
        {secondVal : Term ctx (secondType.subst0 firstType)},
      Step firstVal firstVal' →
      Step (Term.pair (secondType := secondType) firstVal secondVal)
           (Term.pair (secondType := secondType) firstVal' secondVal)
  /-- Step inside the second component of a pair. -/
  | pairRight :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {firstVal : Term ctx firstType}
        {secondVal secondVal' : Term ctx (secondType.subst0 firstType)},
      Step secondVal secondVal' →
      Step (Term.pair firstVal secondVal)
           (Term.pair firstVal secondVal')
  /-- Step inside the argument of a first projection. -/
  | fstCong :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {pairTerm pairTerm' : Term ctx (.sigmaTy firstType secondType)},
      Step pairTerm pairTerm' →
      Step (Term.fst pairTerm) (Term.fst pairTerm')
  /-- Step inside the argument of a second projection. -/
  | sndCong :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
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
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
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
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        (body : Term (ctx.cons domainType) codomainType)
        (arg : Term ctx domainType),
      Step (Term.appPi (Term.lamPi (domainType := domainType) body) arg)
           (Term.subst0 body arg)
  /-- **Σ first projection**: `fst (pair a b) ⟶ a`. -/
  | betaFstPair :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
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
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
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
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
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
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        (p : Term ctx (Ty.sigmaTy firstType secondType)),
      Step (Term.pair (firstType := firstType)
                       (secondType := secondType)
              (Term.fst p) (Term.snd p))
           p
  /-- Step inside the scrutinee position of a `boolElim`.  Together
  with the two ι-rules below, completes the boolean-evaluation
  story.  v1.14+. -/
  | boolElimScrutinee :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx Ty.bool}
        {thenBr elseBr : Term ctx resultType},
      Step scrutinee scrutinee' →
      Step (Term.boolElim scrutinee thenBr elseBr)
           (Term.boolElim scrutinee' thenBr elseBr)
  /-- Step inside the then-branch position of a `boolElim`. -/
  | boolElimThen :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.bool}
        {thenBr thenBr' : Term ctx resultType}
        {elseBr : Term ctx resultType},
      Step thenBr thenBr' →
      Step (Term.boolElim scrutinee thenBr elseBr)
           (Term.boolElim scrutinee thenBr' elseBr)
  /-- Step inside the else-branch position of a `boolElim`. -/
  | boolElimElse :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.bool}
        {thenBr : Term ctx resultType}
        {elseBr elseBr' : Term ctx resultType},
      Step elseBr elseBr' →
      Step (Term.boolElim scrutinee thenBr elseBr)
           (Term.boolElim scrutinee thenBr elseBr')
  /-- **ι-reduction for boolElim on `true`**: `boolElim true t e ⟶ t`.
  No cast: both sides have the same `resultType`.  v1.14+. -/
  | iotaBoolElimTrue :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        (thenBr elseBr : Term ctx resultType),
      Step (Term.boolElim Term.boolTrue thenBr elseBr) thenBr
  /-- **ι-reduction for boolElim on `false`**: `boolElim false t e ⟶ e`.
  No cast: both sides have the same `resultType`.  v1.14+. -/
  | iotaBoolElimFalse :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        (thenBr elseBr : Term ctx resultType),
      Step (Term.boolElim Term.boolFalse thenBr elseBr) elseBr
  /-- Step inside the predecessor of a `Term.natSucc`. -/
  | natSuccPred :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {pred pred' : Term ctx Ty.nat},
      Step pred pred' →
      Step (Term.natSucc pred) (Term.natSucc pred')
  /-- Step inside `Term.natElim`'s scrutinee position. -/
  | natElimScrutinee :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx Ty.nat}
        {zeroBranch : Term ctx resultType}
        {succBranch : Term ctx (Ty.arrow Ty.nat resultType)},
      Step scrutinee scrutinee' →
      Step (Term.natElim scrutinee zeroBranch succBranch)
           (Term.natElim scrutinee' zeroBranch succBranch)
  /-- Step inside `Term.natElim`'s zero-branch position. -/
  | natElimZero :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        {succBranch : Term ctx (Ty.arrow Ty.nat resultType)},
      Step zeroBranch zeroBranch' →
      Step (Term.natElim scrutinee zeroBranch succBranch)
           (Term.natElim scrutinee zeroBranch' succBranch)
  /-- Step inside `Term.natElim`'s succ-branch position. -/
  | natElimSucc :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.nat}
        {zeroBranch : Term ctx resultType}
        {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)},
      Step succBranch succBranch' →
      Step (Term.natElim scrutinee zeroBranch succBranch)
           (Term.natElim scrutinee zeroBranch succBranch')
  /-- **ι-reduction for natElim on `0`**: `natElim 0 z f ⟶ z`.
  No cast: both sides have the same `resultType`. -/
  | iotaNatElimZero :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        (zeroBranch : Term ctx resultType)
        (succBranch : Term ctx (Ty.arrow Ty.nat resultType)),
      Step (Term.natElim Term.natZero zeroBranch succBranch) zeroBranch
  /-- **ι-reduction for natElim on `succ n`**: `natElim (succ n) z f ⟶ f n`.
  Result type matches because `f : Ty.nat → resultType` and we apply
  it to the predecessor. -/
  | iotaNatElimSucc :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        (predecessor : Term ctx Ty.nat)
        (zeroBranch : Term ctx resultType)
        (succBranch : Term ctx (Ty.arrow Ty.nat resultType)),
      Step (Term.natElim (Term.natSucc predecessor) zeroBranch succBranch)
           (Term.app succBranch predecessor)
  /-- Step inside `Term.natRec`'s scrutinee. -/
  | natRecScrutinee :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx Ty.nat}
        {zeroBranch : Term ctx resultType}
        {succBranch : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))},
      Step scrutinee scrutinee' →
      Step (Term.natRec scrutinee zeroBranch succBranch)
           (Term.natRec scrutinee' zeroBranch succBranch)
  /-- Step inside `Term.natRec`'s zero-branch. -/
  | natRecZero :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        {succBranch : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))},
      Step zeroBranch zeroBranch' →
      Step (Term.natRec scrutinee zeroBranch succBranch)
           (Term.natRec scrutinee zeroBranch' succBranch)
  /-- Step inside `Term.natRec`'s succ-branch. -/
  | natRecSucc :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.nat}
        {zeroBranch : Term ctx resultType}
        {succBranch succBranch' : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))},
      Step succBranch succBranch' →
      Step (Term.natRec scrutinee zeroBranch succBranch)
           (Term.natRec scrutinee zeroBranch succBranch')
  /-- **ι-reduction for natRec on `0`**: `natRec 0 z s ⟶ z`.  Same shape
  as `iotaNatElimZero` — the succ-branch is unused on the zero scrutinee. -/
  | iotaNatRecZero :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        (zeroBranch : Term ctx resultType)
        (succBranch : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))),
      Step (Term.natRec Term.natZero zeroBranch succBranch) zeroBranch
  /-- **ι-reduction for natRec on `succ n`**:
  `natRec (succ n) z s ⟶ s n (natRec n z s)`.  The reduct contains a
  recursive `natRec` call carrying the IH — this is what makes natRec
  primitive recursion rather than mere case-analysis. -/
  | iotaNatRecSucc :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        (predecessor : Term ctx Ty.nat)
        (zeroBranch : Term ctx resultType)
        (succBranch : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))),
      Step (Term.natRec (Term.natSucc predecessor) zeroBranch succBranch)
           (Term.app (Term.app succBranch predecessor)
                     (Term.natRec predecessor zeroBranch succBranch))
  /-- Step inside the head of a `Term.listCons`. -/
  | listConsHead :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType : Ty level scope}
        {hd hd' : Term ctx elementType}
        {tl : Term ctx (Ty.list elementType)},
      Step hd hd' →
      Step (Term.listCons hd tl) (Term.listCons hd' tl)
  /-- Step inside the tail of a `Term.listCons`. -/
  | listConsTail :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType : Ty level scope}
        {hd : Term ctx elementType}
        {tl tl' : Term ctx (Ty.list elementType)},
      Step tl tl' →
      Step (Term.listCons hd tl) (Term.listCons hd tl')
  /-- Step inside `Term.listElim`'s scrutinee. -/
  | listElimScrutinee :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx (Ty.list elementType)}
        {nilBranch : Term ctx resultType}
        {consBranch : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))},
      Step scrutinee scrutinee' →
      Step (Term.listElim scrutinee nilBranch consBranch)
           (Term.listElim scrutinee' nilBranch consBranch)
  /-- Step inside `Term.listElim`'s nil-branch. -/
  | listElimNil :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.list elementType)}
        {nilBranch nilBranch' : Term ctx resultType}
        {consBranch : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))},
      Step nilBranch nilBranch' →
      Step (Term.listElim scrutinee nilBranch consBranch)
           (Term.listElim scrutinee nilBranch' consBranch)
  /-- Step inside `Term.listElim`'s cons-branch. -/
  | listElimCons :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.list elementType)}
        {nilBranch : Term ctx resultType}
        {consBranch consBranch' : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))},
      Step consBranch consBranch' →
      Step (Term.listElim scrutinee nilBranch consBranch)
           (Term.listElim scrutinee nilBranch consBranch')
  /-- **ι-reduction for listElim on `[]`**: `listElim [] n c ⟶ n`. -/
  | iotaListElimNil :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        (nilBranch : Term ctx resultType)
        (consBranch : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))),
      Step (Term.listElim (elementType := elementType) Term.listNil
              nilBranch consBranch)
           nilBranch
  /-- **ι-reduction for listElim on `cons`**: `listElim (cons h t) n c ⟶
  c h t` — apply the curried consBranch to head and tail. -/
  | iotaListElimCons :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        (head : Term ctx elementType)
        (tail : Term ctx (Ty.list elementType))
        (nilBranch : Term ctx resultType)
        (consBranch : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))),
      Step (Term.listElim (Term.listCons head tail) nilBranch consBranch)
           (Term.app (Term.app consBranch head) tail)
  /-- Step inside `Term.optionSome`'s value. -/
  | optionSomeValue :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType : Ty level scope}
        {value value' : Term ctx elementType},
      Step value value' →
      Step (Term.optionSome value) (Term.optionSome value')
  /-- Step inside `Term.optionMatch`'s scrutinee. -/
  | optionMatchScrutinee :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx (Ty.option elementType)}
        {noneBranch : Term ctx resultType}
        {someBranch : Term ctx (Ty.arrow elementType resultType)},
      Step scrutinee scrutinee' →
      Step (Term.optionMatch scrutinee noneBranch someBranch)
           (Term.optionMatch scrutinee' noneBranch someBranch)
  /-- Step inside `Term.optionMatch`'s none-branch. -/
  | optionMatchNone :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.option elementType)}
        {noneBranch noneBranch' : Term ctx resultType}
        {someBranch : Term ctx (Ty.arrow elementType resultType)},
      Step noneBranch noneBranch' →
      Step (Term.optionMatch scrutinee noneBranch someBranch)
           (Term.optionMatch scrutinee noneBranch' someBranch)
  /-- Step inside `Term.optionMatch`'s some-branch. -/
  | optionMatchSome :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.option elementType)}
        {noneBranch : Term ctx resultType}
        {someBranch someBranch' : Term ctx (Ty.arrow elementType resultType)},
      Step someBranch someBranch' →
      Step (Term.optionMatch scrutinee noneBranch someBranch)
           (Term.optionMatch scrutinee noneBranch someBranch')
  /-- **ι-reduction for optionMatch on `none`**:
  `optionMatch none n s ⟶ n`. -/
  | iotaOptionMatchNone :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        (noneBranch : Term ctx resultType)
        (someBranch : Term ctx (Ty.arrow elementType resultType)),
      Step (Term.optionMatch (elementType := elementType) Term.optionNone
              noneBranch someBranch)
           noneBranch
  /-- **ι-reduction for optionMatch on `some`**:
  `optionMatch (some v) n s ⟶ s v`. -/
  | iotaOptionMatchSome :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        (value : Term ctx elementType)
        (noneBranch : Term ctx resultType)
        (someBranch : Term ctx (Ty.arrow elementType resultType)),
      Step (Term.optionMatch (Term.optionSome value) noneBranch someBranch)
           (Term.app someBranch value)
  /-- Step inside `Term.eitherInl`'s value. -/
  | eitherInlValue :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType : Ty level scope}
        {value value' : Term ctx leftType},
      Step value value' →
      Step (Term.eitherInl (rightType := rightType) value)
           (Term.eitherInl (rightType := rightType) value')
  /-- Step inside `Term.eitherInr`'s value. -/
  | eitherInrValue :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType : Ty level scope}
        {value value' : Term ctx rightType},
      Step value value' →
      Step (Term.eitherInr (leftType := leftType) value)
           (Term.eitherInr (leftType := leftType) value')
  /-- Step inside `Term.eitherMatch`'s scrutinee. -/
  | eitherMatchScrutinee :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx (Ty.either leftType rightType)}
        {leftBranch : Term ctx (Ty.arrow leftType resultType)}
        {rightBranch : Term ctx (Ty.arrow rightType resultType)},
      Step scrutinee scrutinee' →
      Step (Term.eitherMatch scrutinee leftBranch rightBranch)
           (Term.eitherMatch scrutinee' leftBranch rightBranch)
  /-- Step inside `Term.eitherMatch`'s left-branch. -/
  | eitherMatchLeft :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.either leftType rightType)}
        {leftBranch leftBranch' : Term ctx (Ty.arrow leftType resultType)}
        {rightBranch : Term ctx (Ty.arrow rightType resultType)},
      Step leftBranch leftBranch' →
      Step (Term.eitherMatch scrutinee leftBranch rightBranch)
           (Term.eitherMatch scrutinee leftBranch' rightBranch)
  /-- Step inside `Term.eitherMatch`'s right-branch. -/
  | eitherMatchRight :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.either leftType rightType)}
        {leftBranch : Term ctx (Ty.arrow leftType resultType)}
        {rightBranch rightBranch' : Term ctx (Ty.arrow rightType resultType)},
      Step rightBranch rightBranch' →
      Step (Term.eitherMatch scrutinee leftBranch rightBranch)
           (Term.eitherMatch scrutinee leftBranch rightBranch')
  /-- **ι-reduction for eitherMatch on `inl`**:
  `eitherMatch (inl v) lb rb ⟶ lb v`. -/
  | iotaEitherMatchInl :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        (value : Term ctx leftType)
        (leftBranch : Term ctx (Ty.arrow leftType resultType))
        (rightBranch : Term ctx (Ty.arrow rightType resultType)),
      Step (Term.eitherMatch (Term.eitherInl (rightType := rightType) value)
              leftBranch rightBranch)
           (Term.app leftBranch value)
  /-- **ι-reduction for eitherMatch on `inr`**:
  `eitherMatch (inr v) lb rb ⟶ rb v`. -/
  | iotaEitherMatchInr :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        (value : Term ctx rightType)
        (leftBranch : Term ctx (Ty.arrow leftType resultType))
        (rightBranch : Term ctx (Ty.arrow rightType resultType)),
      Step (Term.eitherMatch (Term.eitherInr (leftType := leftType) value)
              leftBranch rightBranch)
           (Term.app rightBranch value)

/-- Reflexive-transitive closure of `Step` — multi-step reduction.
Captures the eventual reach of the reduction relation. -/
inductive StepStar :
    {mode : Mode} → {level scope : Nat} → {ctx : Ctx mode level scope} →
    {T : Ty level scope} → Term ctx T → Term ctx T → Prop
  /-- Zero-step: a term reduces to itself. -/
  | refl :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        (t : Term ctx T),
      StepStar t t
  /-- Prepend a single step to an existing multi-step path. -/
  | step :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
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
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ : Term ctx T} (h : Step t₁ t₂) : StepStar t₁ t₂ :=
  StepStar.step h (StepStar.refl t₂)

/-- Transitivity of multi-step reduction.  Together with `refl` this
makes `StepStar` an equivalence-relation-like object and is
load-bearing for the eventual conversion algorithm — in particular
for showing common-reducts when comparing terms. -/
theorem StepStar.trans
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ t₃ : Term ctx T} :
    StepStar t₁ t₂ → StepStar t₂ t₃ → StepStar t₁ t₃
  | .refl _, h         => h
  | .step s rest, h    => .step s (StepStar.trans rest h)

/-! ## StepStar structural congruences.

Multi-step threading through each constructor.  Per-position and
combined forms; induction on `StepStar` with `refl`/`step` arms. -/

/-- Multi-step reduction threads through the function position of `Term.app`. -/
theorem StepStar.app_cong_left {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    (a : Term ctx domainType) :
    StepStar f₁ f₂ → StepStar (Term.app f₁ a) (Term.app f₂ a)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.appLeft s) (StepStar.app_cong_left a rest)

/-- Multi-step reduction threads through the argument position of `Term.app`. -/
theorem StepStar.app_cong_right {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    (f : Term ctx (Ty.arrow domainType codomainType))
    {a₁ a₂ : Term ctx domainType} :
    StepStar a₁ a₂ → StepStar (Term.app f a₁) (Term.app f a₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.appRight s) (StepStar.app_cong_right f rest)

/-- Multi-step reduction threads through both positions of `Term.app`. -/
theorem StepStar.app_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : StepStar f₁ f₂) (h_a : StepStar a₁ a₂) :
    StepStar (Term.app f₁ a₁) (Term.app f₂ a₂) :=
  StepStar.trans (StepStar.app_cong_left a₁ h_f)
                 (StepStar.app_cong_right f₂ h_a)

/-- Multi-step reduction threads through the body of `Term.lam`. -/
theorem StepStar.lam_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body₁ body₂ : Term (ctx.cons domainType) codomainType.weaken} :
    StepStar body₁ body₂ →
    StepStar (Term.lam (codomainType := codomainType) body₁)
             (Term.lam (codomainType := codomainType) body₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.lamBody s) (StepStar.lam_cong rest)

/-- Multi-step reduction threads through the body of `Term.lamPi`. -/
theorem StepStar.lamPi_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body₁ body₂ : Term (ctx.cons domainType) codomainType} :
    StepStar body₁ body₂ →
    StepStar (Term.lamPi (domainType := domainType) body₁)
             (Term.lamPi (domainType := domainType) body₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.lamPiBody s) (StepStar.lamPi_cong rest)

/-- Multi-step reduction threads through the function position of `Term.appPi`. -/
theorem StepStar.appPi_cong_left {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    (a : Term ctx domainType) :
    StepStar f₁ f₂ → StepStar (Term.appPi f₁ a) (Term.appPi f₂ a)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.appPiLeft s)
        (StepStar.appPi_cong_left a rest)

/-- Multi-step reduction threads through the argument position of `Term.appPi`. -/
theorem StepStar.appPi_cong_right {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    (f : Term ctx (Ty.piTy domainType codomainType))
    {a₁ a₂ : Term ctx domainType} :
    StepStar a₁ a₂ → StepStar (Term.appPi f a₁) (Term.appPi f a₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.appPiRight s)
        (StepStar.appPi_cong_right f rest)

/-- Multi-step reduction threads through both positions of `Term.appPi`. -/
theorem StepStar.appPi_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : StepStar f₁ f₂) (h_a : StepStar a₁ a₂) :
    StepStar (Term.appPi f₁ a₁) (Term.appPi f₂ a₂) :=
  StepStar.trans (StepStar.appPi_cong_left a₁ h_f)
                 (StepStar.appPi_cong_right f₂ h_a)

/-- Multi-step reduction threads through the first component of `Term.pair`. -/
theorem StepStar.pair_cong_first {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
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
theorem StepStar.pair_cong_second {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
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
theorem StepStar.pair_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal₁ firstVal₂ : Term ctx firstType}
    {secondVal₁ secondVal₂ : Term ctx (secondType.subst0 firstType)}
    (h_first : StepStar firstVal₁ firstVal₂)
    (h_second : StepStar secondVal₁ secondVal₂) :
    StepStar (Term.pair firstVal₁ secondVal₁)
             (Term.pair firstVal₂ secondVal₂) :=
  StepStar.trans (StepStar.pair_cong_first secondVal₁ h_first)
                 (StepStar.pair_cong_second firstVal₂ h_second)

/-- Multi-step reduction threads through `Term.fst`. -/
theorem StepStar.fst_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)} :
    StepStar p₁ p₂ → StepStar (Term.fst p₁) (Term.fst p₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.fstCong s) (StepStar.fst_cong rest)

/-- Multi-step reduction threads through `Term.snd`. -/
theorem StepStar.snd_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)} :
    StepStar p₁ p₂ → StepStar (Term.snd p₁) (Term.snd p₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.sndCong s) (StepStar.snd_cong rest)

/-! ## Parallel reduction (`Step.par`) — confluence groundwork.

The parallel-reduction relation is the standard Tait–Martin-Löf vehicle
for proving confluence of `Step`: rather than reduce one redex at a time,
`Step.par` allows simultaneous reduction in *all* subterms in a single
step.  Crucially it is reflexive, so any subterm may "reduce" by zero
steps.

Key properties (proved here / deferred):

  * `Step.par` is reflexive — `Step.par.refl t : Step.par t t`.  Direct
    constructor.
  * `Step → Step.par` — each single Step lifts trivially (this layer).
  * `Step.par → StepStar` — each parallel rule decomposes into a
    sequence of single Step's.  Substantial; deferred.
  * **Diamond property** for `Step.par`: if `Step.par t t₁` and
    `Step.par t t₂`, there exists `t'` with `Step.par t₁ t'` and
    `Step.par t₂ t'`.  This is the Tait–Martin-Löf "strip lemma"
    + confluence chain.  Deferred to a follow-on task; once proved,
    confluence of `StepStar` (and hence decidability of `Conv` over
    canonical forms) follows.

Subject preservation is structural: input and output share `{ctx} {T}`
indices, so every `Step.par` proof witnesses same-typed reduction. -/
inductive Step.par :
    {mode : Mode} → {level scope : Nat} → {ctx : Ctx mode level scope} →
    {T : Ty level scope} → Term ctx T → Term ctx T → Prop
  /-- Reflexivity — any term parallel-reduces to itself in zero steps. -/
  | refl :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        (t : Term ctx T),
      Step.par t t
  /-- Parallel reduction inside a non-dependent application. -/
  | app :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {f f' : Term ctx (.arrow domainType codomainType)}
        {a a' : Term ctx domainType},
      Step.par f f' → Step.par a a' →
      Step.par (Term.app f a) (Term.app f' a')
  /-- Parallel reduction inside a non-dependent λ-abstraction's body. -/
  | lam :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {body body' : Term (ctx.cons domainType) codomainType.weaken},
      Step.par body body' →
      Step.par (Term.lam (codomainType := codomainType) body)
               (Term.lam (codomainType := codomainType) body')
  /-- Parallel reduction inside a dependent λ-abstraction's body. -/
  | lamPi :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        {body body' : Term (ctx.cons domainType) codomainType},
      Step.par body body' →
      Step.par (Term.lamPi (domainType := domainType) body)
               (Term.lamPi (domainType := domainType) body')
  /-- Parallel reduction inside a dependent application. -/
  | appPi :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        {f f' : Term ctx (.piTy domainType codomainType)}
        {a a' : Term ctx domainType},
      Step.par f f' → Step.par a a' →
      Step.par (Term.appPi f a) (Term.appPi f' a')
  /-- Parallel reduction inside a Σ-pair's two components. -/
  | pair :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {firstVal firstVal' : Term ctx firstType}
        {secondVal secondVal' : Term ctx (secondType.subst0 firstType)},
      Step.par firstVal firstVal' → Step.par secondVal secondVal' →
      Step.par (Term.pair firstVal secondVal)
               (Term.pair firstVal' secondVal')
  /-- Parallel reduction inside a first projection. -/
  | fst :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {p p' : Term ctx (.sigmaTy firstType secondType)},
      Step.par p p' → Step.par (Term.fst p) (Term.fst p')
  /-- Parallel reduction inside a second projection. -/
  | snd :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {p p' : Term ctx (.sigmaTy firstType secondType)},
      Step.par p p' → Step.par (Term.snd p) (Term.snd p')
  /-- Parallel reduction inside all three positions of a `boolElim`. -/
  | boolElim :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx Ty.bool}
        {thenBr thenBr' : Term ctx resultType}
        {elseBr elseBr' : Term ctx resultType},
      Step.par scrutinee scrutinee' →
      Step.par thenBr thenBr' →
      Step.par elseBr elseBr' →
      Step.par (Term.boolElim scrutinee thenBr elseBr)
               (Term.boolElim scrutinee' thenBr' elseBr')
  /-- **Parallel β-reduction (non-dependent)**: `(λ. body) arg →
  body[arg/x]` with parallel reductions in body and arg before
  substitution.  This is the rule that makes confluence work — both the
  body and the argument may reduce in lockstep with the contraction. -/
  | betaApp :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {body body' : Term (ctx.cons domainType) codomainType.weaken}
        {arg arg' : Term ctx domainType},
      Step.par body body' → Step.par arg arg' →
      Step.par (Term.app (Term.lam (codomainType := codomainType) body) arg)
               ((Ty.weaken_subst_singleton codomainType domainType) ▸
                  Term.subst0 body' arg')
  /-- **Parallel β-reduction (dependent)**: `(λ. body) arg ⟶
  body[arg/x]` with parallel reductions in body and arg.  No cast
  needed because `body.subst0 arg : Term ctx (codomainType.subst0
  domainType)` matches `Term.appPi`'s declared result type exactly. -/
  | betaAppPi :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
        {body body' : Term (ctx.cons domainType) codomainType}
        {arg arg' : Term ctx domainType},
      Step.par body body' → Step.par arg arg' →
      Step.par (Term.appPi (Term.lamPi (domainType := domainType) body) arg)
               (Term.subst0 body' arg')
  /-- **Parallel Σ first projection**: `fst (pair a b) → a'` with
  `Step.par a a'`. -/
  | betaFstPair :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        {firstVal firstVal' : Term ctx firstType}
        (secondVal : Term ctx (secondType.subst0 firstType)),
      Step.par firstVal firstVal' →
      Step.par (Term.fst
                 (Term.pair (firstType := firstType)
                            (secondType := secondType) firstVal secondVal))
               firstVal'
  /-- **Parallel Σ second projection**: `snd (pair a b) → b'` with
  `Step.par b b'`. -/
  | betaSndPair :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        (firstVal : Term ctx firstType)
        {secondVal secondVal' : Term ctx (secondType.subst0 firstType)},
      Step.par secondVal secondVal' →
      Step.par (Term.snd
                 (Term.pair (firstType := firstType)
                            (secondType := secondType) firstVal secondVal))
               secondVal'
  /-- **Parallel ι-reduction on `boolTrue`**: `boolElim true t e → t'`
  with `Step.par t t'`. -/
  | iotaBoolElimTrue :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {thenBr thenBr' : Term ctx resultType}
        (elseBr : Term ctx resultType),
      Step.par thenBr thenBr' →
      Step.par (Term.boolElim Term.boolTrue thenBr elseBr) thenBr'
  /-- **Parallel ι-reduction on `boolFalse`**: `boolElim false t e →
  e'` with `Step.par e e'`. -/
  | iotaBoolElimFalse :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        (thenBr : Term ctx resultType)
        {elseBr elseBr' : Term ctx resultType},
      Step.par elseBr elseBr' →
      Step.par (Term.boolElim Term.boolFalse thenBr elseBr) elseBr'
  /-- Parallel reduction inside a `Term.natSucc`. -/
  | natSucc :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {pred pred' : Term ctx Ty.nat},
      Step.par pred pred' →
      Step.par (Term.natSucc pred) (Term.natSucc pred')
  /-- Parallel reduction inside all three positions of a `Term.natElim`. -/
  | natElim :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)},
      Step.par scrutinee scrutinee' →
      Step.par zeroBranch zeroBranch' →
      Step.par succBranch succBranch' →
      Step.par (Term.natElim scrutinee zeroBranch succBranch)
               (Term.natElim scrutinee' zeroBranch' succBranch')
  /-- **Parallel ι-reduction on `0`**: `natElim 0 z f → z'` with
  `Step.par z z'`. -/
  | iotaNatElimZero :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {zeroBranch zeroBranch' : Term ctx resultType}
        (succBranch : Term ctx (Ty.arrow Ty.nat resultType)),
      Step.par zeroBranch zeroBranch' →
      Step.par (Term.natElim Term.natZero zeroBranch succBranch) zeroBranch'
  /-- Parallel reduction inside all three positions of `Term.natRec`. -/
  | natRec :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        {succBranch succBranch' : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))},
      Step.par scrutinee scrutinee' →
      Step.par zeroBranch zeroBranch' →
      Step.par succBranch succBranch' →
      Step.par (Term.natRec scrutinee zeroBranch succBranch)
               (Term.natRec scrutinee' zeroBranch' succBranch')
  /-- **Parallel ι-reduction on `0`**: `natRec 0 z s → z'` with
  `Step.par z z'`. -/
  | iotaNatRecZero :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {zeroBranch zeroBranch' : Term ctx resultType}
        (succBranch : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))),
      Step.par zeroBranch zeroBranch' →
      Step.par (Term.natRec Term.natZero zeroBranch succBranch) zeroBranch'
  /-- **Parallel ι-reduction on `succ n`**:
  `natRec (succ n) z s → s' n' (natRec n' z' s')`.  All three
  subterms parallel-reduce because they all appear in the reduct
  (the IH is constructed from the reduced versions). -/
  | iotaNatRecSucc :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {predecessor predecessor' : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        {succBranch succBranch' : Term ctx
           (Ty.arrow Ty.nat (Ty.arrow resultType resultType))},
      Step.par predecessor predecessor' →
      Step.par zeroBranch zeroBranch' →
      Step.par succBranch succBranch' →
      Step.par (Term.natRec (Term.natSucc predecessor) zeroBranch succBranch)
               (Term.app (Term.app succBranch' predecessor')
                         (Term.natRec predecessor' zeroBranch' succBranch'))
  /-- **Parallel ι-reduction on `succ n`**: `natElim (succ n) z f → f' n'`
  with `Step.par n n'` and `Step.par f f'`. -/
  | iotaNatElimSucc :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {predecessor predecessor' : Term ctx Ty.nat}
        (zeroBranch : Term ctx resultType)
        {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)},
      Step.par predecessor predecessor' →
      Step.par succBranch succBranch' →
      Step.par (Term.natElim (Term.natSucc predecessor) zeroBranch succBranch)
               (Term.app succBranch' predecessor')
  /-- Parallel reduction inside both head and tail of a `Term.listCons`. -/
  | listCons :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType : Ty level scope}
        {hd hd' : Term ctx elementType}
        {tl tl' : Term ctx (Ty.list elementType)},
      Step.par hd hd' → Step.par tl tl' →
      Step.par (Term.listCons hd tl) (Term.listCons hd' tl')
  /-- Parallel reduction inside all three positions of a `Term.listElim`. -/
  | listElim :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx (Ty.list elementType)}
        {nilBranch nilBranch' : Term ctx resultType}
        {consBranch consBranch' : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))},
      Step.par scrutinee scrutinee' →
      Step.par nilBranch nilBranch' →
      Step.par consBranch consBranch' →
      Step.par (Term.listElim scrutinee nilBranch consBranch)
               (Term.listElim scrutinee' nilBranch' consBranch')
  /-- **Parallel ι-reduction on `[]`**: `listElim [] n c → n'`
  with `Step.par n n'`. -/
  | iotaListElimNil :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {nilBranch nilBranch' : Term ctx resultType}
        (consBranch : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))),
      Step.par nilBranch nilBranch' →
      Step.par (Term.listElim (elementType := elementType) Term.listNil
                  nilBranch consBranch)
               nilBranch'
  /-- **Parallel ι-reduction on `cons`**: `listElim (cons h t) n c →
  c' h' t'` with parallel reductions in head, tail, and consBranch. -/
  | iotaListElimCons :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {head head' : Term ctx elementType}
        {tail tail' : Term ctx (Ty.list elementType)}
        (nilBranch : Term ctx resultType)
        {consBranch consBranch' : Term ctx
           (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))},
      Step.par head head' →
      Step.par tail tail' →
      Step.par consBranch consBranch' →
      Step.par (Term.listElim (Term.listCons head tail) nilBranch consBranch)
               (Term.app (Term.app consBranch' head') tail')
  /-- Parallel reduction inside the value of `Term.optionSome`. -/
  | optionSome :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType : Ty level scope}
        {value value' : Term ctx elementType},
      Step.par value value' →
      Step.par (Term.optionSome value) (Term.optionSome value')
  /-- Parallel reduction inside all three positions of `Term.optionMatch`. -/
  | optionMatch :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx (Ty.option elementType)}
        {noneBranch noneBranch' : Term ctx resultType}
        {someBranch someBranch' : Term ctx (Ty.arrow elementType resultType)},
      Step.par scrutinee scrutinee' →
      Step.par noneBranch noneBranch' →
      Step.par someBranch someBranch' →
      Step.par (Term.optionMatch scrutinee noneBranch someBranch)
               (Term.optionMatch scrutinee' noneBranch' someBranch')
  /-- **Parallel ι-reduction on `none`**: `optionMatch none n s → n'`
  with `Step.par n n'`. -/
  | iotaOptionMatchNone :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {noneBranch noneBranch' : Term ctx resultType}
        (someBranch : Term ctx (Ty.arrow elementType resultType)),
      Step.par noneBranch noneBranch' →
      Step.par (Term.optionMatch (elementType := elementType) Term.optionNone
                  noneBranch someBranch)
               noneBranch'
  /-- **Parallel ι-reduction on `some`**: `optionMatch (some v) n s → s' v'`
  with parallel reductions in value and someBranch. -/
  | iotaOptionMatchSome :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {value value' : Term ctx elementType}
        (noneBranch : Term ctx resultType)
        {someBranch someBranch' : Term ctx (Ty.arrow elementType resultType)},
      Step.par value value' →
      Step.par someBranch someBranch' →
      Step.par (Term.optionMatch (Term.optionSome value) noneBranch someBranch)
               (Term.app someBranch' value')
  /-- Parallel reduction inside the value of `Term.eitherInl`. -/
  | eitherInl :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType : Ty level scope}
        {value value' : Term ctx leftType},
      Step.par value value' →
      Step.par (Term.eitherInl (rightType := rightType) value)
               (Term.eitherInl (rightType := rightType) value')
  /-- Parallel reduction inside the value of `Term.eitherInr`. -/
  | eitherInr :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType : Ty level scope}
        {value value' : Term ctx rightType},
      Step.par value value' →
      Step.par (Term.eitherInr (leftType := leftType) value)
               (Term.eitherInr (leftType := leftType) value')
  /-- Parallel reduction inside all three positions of `Term.eitherMatch`. -/
  | eitherMatch :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx (Ty.either leftType rightType)}
        {leftBranch leftBranch' : Term ctx (Ty.arrow leftType resultType)}
        {rightBranch rightBranch' : Term ctx (Ty.arrow rightType resultType)},
      Step.par scrutinee scrutinee' →
      Step.par leftBranch leftBranch' →
      Step.par rightBranch rightBranch' →
      Step.par (Term.eitherMatch scrutinee leftBranch rightBranch)
               (Term.eitherMatch scrutinee' leftBranch' rightBranch')
  /-- **Parallel ι-reduction on `inl`**: `eitherMatch (inl v) lb rb → lb' v'`
  with parallel reductions in value and leftBranch. -/
  | iotaEitherMatchInl :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {value value' : Term ctx leftType}
        {leftBranch leftBranch' : Term ctx (Ty.arrow leftType resultType)}
        (rightBranch : Term ctx (Ty.arrow rightType resultType)),
      Step.par value value' →
      Step.par leftBranch leftBranch' →
      Step.par (Term.eitherMatch (Term.eitherInl (rightType := rightType) value)
                  leftBranch rightBranch)
               (Term.app leftBranch' value')
  /-- **Parallel ι-reduction on `inr`**: `eitherMatch (inr v) lb rb → rb' v'`
  with parallel reductions in value and rightBranch. -/
  | iotaEitherMatchInr :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {value value' : Term ctx rightType}
        (leftBranch : Term ctx (Ty.arrow leftType resultType))
        {rightBranch rightBranch' : Term ctx (Ty.arrow rightType resultType)},
      Step.par value value' →
      Step.par rightBranch rightBranch' →
      Step.par (Term.eitherMatch (Term.eitherInr (leftType := leftType) value)
                  leftBranch rightBranch)
               (Term.app rightBranch' value')
  /-- **η-contraction for non-dependent arrow** at the parallel level.
  Same shape as `Step.etaArrow`: the η-redex `λx. f.weaken x` contracts
  to `f`.  No subterm-parallel rule because the redex shape is rigid
  (the body must be specifically `f.weaken x`); confluence with βι
  composes through this rule by post-applying the η-contraction. -/
  | etaArrow :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        (f : Term ctx (Ty.arrow domainType codomainType)),
      Step.par (Term.lam (codomainType := codomainType)
                  (Term.app (Term.weaken domainType f)
                            (Term.var ⟨0, Nat.zero_lt_succ _⟩)))
               f
  /-- **η-contraction for Σ-pair** at the parallel level. -/
  | etaSigma :
      ∀ {mode level scope} {ctx : Ctx mode level scope}
        {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
        (p : Term ctx (Ty.sigmaTy firstType secondType)),
      Step.par (Term.pair (firstType := firstType)
                           (secondType := secondType)
                  (Term.fst p) (Term.snd p))
               p

/-- Single-step reduction lifts to parallel reduction.  Each `Step`
constructor has a corresponding `Step.par` form where the non-changing
subterm reduces by reflexivity. -/
theorem Step.toPar
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ : Term ctx T} : Step t₁ t₂ → Step.par t₁ t₂
  | .appLeft s            => .app (Step.toPar s) (.refl _)
  | .appRight s           => .app (.refl _) (Step.toPar s)
  | .lamBody s            => .lam (Step.toPar s)
  | .appPiLeft s          => .appPi (Step.toPar s) (.refl _)
  | .appPiRight s         => .appPi (.refl _) (Step.toPar s)
  | .lamPiBody s          => .lamPi (Step.toPar s)
  | .pairLeft s           => .pair (Step.toPar s) (.refl _)
  | .pairRight s          => .pair (.refl _) (Step.toPar s)
  | .fstCong s            => .fst (Step.toPar s)
  | .sndCong s            => .snd (Step.toPar s)
  | .betaApp body arg     => .betaApp (.refl body) (.refl arg)
  | .betaAppPi body arg   => .betaAppPi (.refl body) (.refl arg)
  | .betaFstPair v w      => .betaFstPair w (.refl v)
  | .betaSndPair v w      => .betaSndPair v (.refl w)
  | .etaArrow f           => .etaArrow f
  | .etaSigma p           => .etaSigma p
  | .boolElimScrutinee s  => .boolElim (Step.toPar s) (.refl _) (.refl _)
  | .boolElimThen s       => .boolElim (.refl _) (Step.toPar s) (.refl _)
  | .boolElimElse s       => .boolElim (.refl _) (.refl _) (Step.toPar s)
  | .iotaBoolElimTrue t e => .iotaBoolElimTrue e (.refl t)
  | .iotaBoolElimFalse t e => .iotaBoolElimFalse t (.refl e)
  | .natSuccPred s        => .natSucc (Step.toPar s)
  | .natElimScrutinee s   => .natElim (Step.toPar s) (.refl _) (.refl _)
  | .natElimZero s        => .natElim (.refl _) (Step.toPar s) (.refl _)
  | .natElimSucc s        => .natElim (.refl _) (.refl _) (Step.toPar s)
  | .iotaNatElimZero z f  => .iotaNatElimZero f (.refl z)
  | .iotaNatElimSucc n _ f => .iotaNatElimSucc _ (.refl n) (.refl f)
  | .natRecScrutinee s    => .natRec (Step.toPar s) (.refl _) (.refl _)
  | .natRecZero s         => .natRec (.refl _) (Step.toPar s) (.refl _)
  | .natRecSucc s         => .natRec (.refl _) (.refl _) (Step.toPar s)
  | .iotaNatRecZero z s   => .iotaNatRecZero s (.refl z)
  | .iotaNatRecSucc n z s =>
      .iotaNatRecSucc (.refl n) (.refl z) (.refl s)
  | .listConsHead s       => .listCons (Step.toPar s) (.refl _)
  | .listConsTail s       => .listCons (.refl _) (Step.toPar s)
  | .listElimScrutinee s  => .listElim (Step.toPar s) (.refl _) (.refl _)
  | .listElimNil s        => .listElim (.refl _) (Step.toPar s) (.refl _)
  | .listElimCons s       => .listElim (.refl _) (.refl _) (Step.toPar s)
  | .iotaListElimNil n c  => .iotaListElimNil c (.refl n)
  | .iotaListElimCons h t _ c =>
      .iotaListElimCons _ (.refl h) (.refl t) (.refl c)
  | .optionSomeValue s    => .optionSome (Step.toPar s)
  | .optionMatchScrutinee s => .optionMatch (Step.toPar s) (.refl _) (.refl _)
  | .optionMatchNone s    => .optionMatch (.refl _) (Step.toPar s) (.refl _)
  | .optionMatchSome s    => .optionMatch (.refl _) (.refl _) (Step.toPar s)
  | .iotaOptionMatchNone n s => .iotaOptionMatchNone s (.refl n)
  | .iotaOptionMatchSome v _ s =>
      .iotaOptionMatchSome _ (.refl v) (.refl s)
  | .eitherInlValue s     => .eitherInl (Step.toPar s)
  | .eitherInrValue s     => .eitherInr (Step.toPar s)
  | .eitherMatchScrutinee s => .eitherMatch (Step.toPar s) (.refl _) (.refl _)
  | .eitherMatchLeft s    => .eitherMatch (.refl _) (Step.toPar s) (.refl _)
  | .eitherMatchRight s   => .eitherMatch (.refl _) (.refl _) (Step.toPar s)
  | .iotaEitherMatchInl v lb rb =>
      .iotaEitherMatchInl rb (.refl v) (.refl lb)
  | .iotaEitherMatchInr v lb rb =>
      .iotaEitherMatchInr lb (.refl v) (.refl rb)

/-! ## Definitional conversion (`Conv`).

Symmetric / reflexive / transitive closure of `Step`.  Minimal
constructors (`refl`, `sym`, `trans`, `fromStep`); structural-
congruence rules below are derived theorems. -/

/-- The conversion relation: equivalence closure of `Step` over
terms of the same type.  Subject preservation is definitional (the
relation's indices fix the type). -/
inductive Conv :
    {mode : Mode} → {level scope : Nat} → {ctx : Ctx mode level scope} →
    {T : Ty level scope} → Term ctx T → Term ctx T → Prop
  /-- Reflexivity: every term is convertible with itself. -/
  | refl :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        (t : Term ctx T),
      Conv t t
  /-- Symmetry: convertibility is bidirectional. -/
  | sym :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        {t₁ t₂ : Term ctx T},
      Conv t₁ t₂ → Conv t₂ t₁
  /-- Transitivity: convertibility chains. -/
  | trans :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        {t₁ t₂ t₃ : Term ctx T},
      Conv t₁ t₂ → Conv t₂ t₃ → Conv t₁ t₃
  /-- Embedding: every single-step reduction is a conversion. -/
  | fromStep :
      ∀ {mode level scope} {ctx : Ctx mode level scope} {T : Ty level scope}
        {t₁ t₂ : Term ctx T},
      Step t₁ t₂ → Conv t₁ t₂

/-- Multi-step reductions lift to conversions: a sequence of forward
steps is a conversion in the forward direction.  Proven by induction
on `StepStar`: the empty case is reflexivity, the step case composes
`fromStep` with the inductive hypothesis via `trans`. -/
theorem StepStar.toConv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ : Term ctx T} :
    StepStar t₁ t₂ → Conv t₁ t₂
  | .refl t       => Conv.refl t
  | .step s rest  => Conv.trans (Conv.fromStep s) (StepStar.toConv rest)

/-- Single-step reductions lift to conversions through the multi-step
intermediary.  Direct from `Conv.fromStep`; provided as a named
theorem for symmetry with `Step.toStar`. -/
theorem Step.toConv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ : Term ctx T} (h : Step t₁ t₂) : Conv t₁ t₂ :=
  Conv.fromStep h

/-! ## Conv structural congruences.

Make `Conv` a full congruence relation over the term constructors. -/

/-- Convertibility threads through the function position of `Term.app`. -/
theorem Conv.app_cong_left {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    (a : Term ctx domainType) (h : Conv f₁ f₂) :
    Conv (Term.app f₁ a) (Term.app f₂ a) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.appLeft s)

/-- Convertibility threads through the argument position of `Term.app`. -/
theorem Conv.app_cong_right {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    (f : Term ctx (Ty.arrow domainType codomainType))
    {a₁ a₂ : Term ctx domainType} (h : Conv a₁ a₂) :
    Conv (Term.app f a₁) (Term.app f a₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.appRight s)

/-- Convertibility threads through both positions of `Term.app`. -/
theorem Conv.app_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {f₁ f₂ : Term ctx (Ty.arrow domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : Conv f₁ f₂) (h_a : Conv a₁ a₂) :
    Conv (Term.app f₁ a₁) (Term.app f₂ a₂) :=
  Conv.trans (Conv.app_cong_left a₁ h_f) (Conv.app_cong_right f₂ h_a)

/-- Convertibility threads through the body of `Term.lam`. -/
theorem Conv.lam_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
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
theorem Conv.lamPi_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
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
theorem Conv.appPi_cong_left {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    (a : Term ctx domainType) (h : Conv f₁ f₂) :
    Conv (Term.appPi f₁ a) (Term.appPi f₂ a) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.appPiLeft s)

/-- Convertibility threads through the argument position of `Term.appPi`. -/
theorem Conv.appPi_cong_right {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    (f : Term ctx (Ty.piTy domainType codomainType))
    {a₁ a₂ : Term ctx domainType} (h : Conv a₁ a₂) :
    Conv (Term.appPi f a₁) (Term.appPi f a₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.appPiRight s)

/-- Convertibility threads through both positions of `Term.appPi`. -/
theorem Conv.appPi_cong {mode level scope} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {f₁ f₂ : Term ctx (Ty.piTy domainType codomainType)}
    {a₁ a₂ : Term ctx domainType}
    (h_f : Conv f₁ f₂) (h_a : Conv a₁ a₂) :
    Conv (Term.appPi f₁ a₁) (Term.appPi f₂ a₂) :=
  Conv.trans (Conv.appPi_cong_left a₁ h_f) (Conv.appPi_cong_right f₂ h_a)

/-- Convertibility threads through the first component of `Term.pair`. -/
theorem Conv.pair_cong_first {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
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
theorem Conv.pair_cong_second {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
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
theorem Conv.pair_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal₁ firstVal₂ : Term ctx firstType}
    {secondVal₁ secondVal₂ : Term ctx (secondType.subst0 firstType)}
    (h_first : Conv firstVal₁ firstVal₂)
    (h_second : Conv secondVal₁ secondVal₂) :
    Conv (Term.pair firstVal₁ secondVal₁)
         (Term.pair firstVal₂ secondVal₂) :=
  Conv.trans (Conv.pair_cong_first secondVal₁ h_first)
             (Conv.pair_cong_second firstVal₂ h_second)

/-- Convertibility threads through `Term.fst`. -/
theorem Conv.fst_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {p₁ p₂ : Term ctx (Ty.sigmaTy firstType secondType)}
    (h : Conv p₁ p₂) :
    Conv (Term.fst p₁) (Term.fst p₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.fstCong s)

/-- Convertibility threads through `Term.snd`. -/
theorem Conv.snd_cong {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
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
theorem Term.eta_arrow_eq {mode level scope} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    (f : Term ctx (Ty.arrow domainType codomainType)) :
    Conv f
         (Term.lam (codomainType := codomainType)
            (Term.app (Term.weaken domainType f)
                      (Term.var ⟨0, Nat.zero_lt_succ _⟩))) :=
  Conv.sym (Step.etaArrow f).toConv

/-- **η-equivalence for Σ**: `p ≡ pair (fst p) (snd p)`. -/
theorem Term.eta_sigma_eq {mode level scope} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
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
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ t₃ : Term ctx T} :
    StepStar t₁ t₂ → Step t₂ t₃ → StepStar t₁ t₃ :=
  fun stars step =>
    StepStar.trans stars (Step.toStar step)

/-! ## Boolean reduction congruences.

Multi-step and definitional-equivalence threading through `boolElim`'s
three positions, plus combined three-position congruences. -/

/-- Multi-step reduction threads through `boolElim`'s scrutinee. -/
theorem StepStar.boolElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
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
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
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
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
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
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
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
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
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
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
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
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
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
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
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

/-! ## Natural-number reduction congruences.

Multi-step and definitional-equivalence threading through `Term.natSucc`
and `Term.natElim`'s three positions, mirroring the boolean section. -/

/-- Definitional equivalence threads through `Term.natSucc`. -/
theorem Conv.natSucc_cong {mode level scope} {ctx : Ctx mode level scope}
    {pred₁ pred₂ : Term ctx Ty.nat}
    (h : Conv pred₁ pred₂) :
    Conv (Term.natSucc pred₁) (Term.natSucc pred₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natSuccPred s)

/-- Definitional equivalence threads through `natElim`'s scrutinee. -/
theorem Conv.natElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.natElim scrutinee₁ zeroBranch succBranch)
         (Term.natElim scrutinee₂ zeroBranch succBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natElimScrutinee s)

/-- Definitional equivalence threads through `natElim`'s zero-branch. -/
theorem Conv.natElim_cong_zero
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
    (h : Conv zeroBranch₁ zeroBranch₂) :
    Conv (Term.natElim scrutinee zeroBranch₁ succBranch)
         (Term.natElim scrutinee zeroBranch₂ succBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natElimZero s)

/-- Definitional equivalence threads through `natElim`'s succ-branch. -/
theorem Conv.natElim_cong_succ
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch₁ succBranch₂ : Term ctx (Ty.arrow Ty.nat resultType)}
    (h : Conv succBranch₁ succBranch₂) :
    Conv (Term.natElim scrutinee zeroBranch succBranch₁)
         (Term.natElim scrutinee zeroBranch succBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natElimSucc s)

/-- Definitional equivalence threads through all three `natElim` positions. -/
theorem Conv.natElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    {succBranch₁ succBranch₂ : Term ctx (Ty.arrow Ty.nat resultType)}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_zero : Conv zeroBranch₁ zeroBranch₂)
    (h_succ : Conv succBranch₁ succBranch₂) :
    Conv (Term.natElim scrutinee₁ zeroBranch₁ succBranch₁)
         (Term.natElim scrutinee₂ zeroBranch₂ succBranch₂) :=
  Conv.trans
    (Conv.natElim_cong_scrutinee zeroBranch₁ succBranch₁ h_scr)
    (Conv.trans
      (Conv.natElim_cong_zero scrutinee₂ succBranch₁ h_zero)
      (Conv.natElim_cong_succ scrutinee₂ zeroBranch₂ h_succ))

/-! ## natRec Conv congruences (parallel to natElim, with the richer
succBranch type `Ty.arrow Ty.nat (Ty.arrow resultType resultType)`). -/

/-- Definitional equivalence threads through `natRec`'s scrutinee. -/
theorem Conv.natRec_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.natRec scrutinee₁ zeroBranch succBranch)
         (Term.natRec scrutinee₂ zeroBranch succBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natRecScrutinee s)

/-- Definitional equivalence threads through `natRec`'s zero-branch. -/
theorem Conv.natRec_cong_zero
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    (succBranch : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
    (h : Conv zeroBranch₁ zeroBranch₂) :
    Conv (Term.natRec scrutinee zeroBranch₁ succBranch)
         (Term.natRec scrutinee zeroBranch₂ succBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natRecZero s)

/-- Definitional equivalence threads through `natRec`'s succ-branch. -/
theorem Conv.natRec_cong_succ
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch₁ succBranch₂ : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (h : Conv succBranch₁ succBranch₂) :
    Conv (Term.natRec scrutinee zeroBranch succBranch₁)
         (Term.natRec scrutinee zeroBranch succBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.natRecSucc s)

/-- Definitional equivalence threads through all three `natRec` positions. -/
theorem Conv.natRec_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    {succBranch₁ succBranch₂ : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_zero : Conv zeroBranch₁ zeroBranch₂)
    (h_succ : Conv succBranch₁ succBranch₂) :
    Conv (Term.natRec scrutinee₁ zeroBranch₁ succBranch₁)
         (Term.natRec scrutinee₂ zeroBranch₂ succBranch₂) :=
  Conv.trans
    (Conv.natRec_cong_scrutinee zeroBranch₁ succBranch₁ h_scr)
    (Conv.trans
      (Conv.natRec_cong_zero scrutinee₂ succBranch₁ h_zero)
      (Conv.natRec_cong_succ scrutinee₂ zeroBranch₂ h_succ))

/-! ## Natural-number Conv congruences end here.

The list-side congruences (Step / StepStar / Conv on listCons / listElim)
mirror the natElim layout but with `elementType` as an extra parametric
implicit. -/

/-- Multi-step reduction threads through `listCons`'s head. -/
theorem StepStar.listCons_cong_head {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {hd₁ hd₂ : Term ctx elementType}
    (tl : Term ctx (Ty.list elementType)) :
    StepStar hd₁ hd₂ →
    StepStar (Term.listCons hd₁ tl) (Term.listCons hd₂ tl)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.listConsHead s)
        (StepStar.listCons_cong_head tl rest)

/-- Multi-step reduction threads through `listCons`'s tail. -/
theorem StepStar.listCons_cong_tail {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    (hd : Term ctx elementType)
    {tl₁ tl₂ : Term ctx (Ty.list elementType)} :
    StepStar tl₁ tl₂ →
    StepStar (Term.listCons hd tl₁) (Term.listCons hd tl₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.listConsTail s)
        (StepStar.listCons_cong_tail hd rest)

/-- Multi-step reduction threads through both head and tail of `listCons`. -/
theorem StepStar.listCons_cong {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {hd₁ hd₂ : Term ctx elementType}
    {tl₁ tl₂ : Term ctx (Ty.list elementType)}
    (h_hd : StepStar hd₁ hd₂) (h_tl : StepStar tl₁ tl₂) :
    StepStar (Term.listCons hd₁ tl₁) (Term.listCons hd₂ tl₂) :=
  StepStar.trans (StepStar.listCons_cong_head tl₁ h_hd)
                 (StepStar.listCons_cong_tail hd₂ h_tl)

/-- Multi-step reduction threads through `listElim`'s scrutinee. -/
theorem StepStar.listElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.list elementType)}
    (nilBranch : Term ctx resultType)
    (consBranch : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.listElim scrutinee₁ nilBranch consBranch)
             (Term.listElim scrutinee₂ nilBranch consBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.listElimScrutinee s)
        (StepStar.listElim_cong_scrutinee nilBranch consBranch rest)

/-- Multi-step reduction threads through `listElim`'s nil-branch. -/
theorem StepStar.listElim_cong_nil
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.list elementType))
    {nilBranch₁ nilBranch₂ : Term ctx resultType}
    (consBranch : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))) :
    StepStar nilBranch₁ nilBranch₂ →
    StepStar (Term.listElim scrutinee nilBranch₁ consBranch)
             (Term.listElim scrutinee nilBranch₂ consBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.listElimNil s)
        (StepStar.listElim_cong_nil scrutinee consBranch rest)

/-- Multi-step reduction threads through `listElim`'s cons-branch. -/
theorem StepStar.listElim_cong_cons
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.list elementType))
    (nilBranch : Term ctx resultType)
    {consBranch₁ consBranch₂ : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))} :
    StepStar consBranch₁ consBranch₂ →
    StepStar (Term.listElim scrutinee nilBranch consBranch₁)
             (Term.listElim scrutinee nilBranch consBranch₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.listElimCons s)
        (StepStar.listElim_cong_cons scrutinee nilBranch rest)

/-- Multi-step reduction threads through all three `listElim` positions. -/
theorem StepStar.listElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.list elementType)}
    {nilBranch₁ nilBranch₂ : Term ctx resultType}
    {consBranch₁ consBranch₂ : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_nil : StepStar nilBranch₁ nilBranch₂)
    (h_cons : StepStar consBranch₁ consBranch₂) :
    StepStar (Term.listElim scrutinee₁ nilBranch₁ consBranch₁)
             (Term.listElim scrutinee₂ nilBranch₂ consBranch₂) :=
  StepStar.trans
    (StepStar.listElim_cong_scrutinee nilBranch₁ consBranch₁ h_scr)
    (StepStar.trans
      (StepStar.listElim_cong_nil scrutinee₂ consBranch₁ h_nil)
      (StepStar.listElim_cong_cons scrutinee₂ nilBranch₂ h_cons))

/-- Definitional equivalence threads through `listCons`'s head. -/
theorem Conv.listCons_cong_head {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {hd₁ hd₂ : Term ctx elementType}
    (tl : Term ctx (Ty.list elementType)) (h : Conv hd₁ hd₂) :
    Conv (Term.listCons hd₁ tl) (Term.listCons hd₂ tl) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.listConsHead s)

/-- Definitional equivalence threads through `listCons`'s tail. -/
theorem Conv.listCons_cong_tail {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    (hd : Term ctx elementType)
    {tl₁ tl₂ : Term ctx (Ty.list elementType)} (h : Conv tl₁ tl₂) :
    Conv (Term.listCons hd tl₁) (Term.listCons hd tl₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.listConsTail s)

/-- Definitional equivalence threads through both `listCons` positions. -/
theorem Conv.listCons_cong {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {hd₁ hd₂ : Term ctx elementType}
    {tl₁ tl₂ : Term ctx (Ty.list elementType)}
    (h_hd : Conv hd₁ hd₂) (h_tl : Conv tl₁ tl₂) :
    Conv (Term.listCons hd₁ tl₁) (Term.listCons hd₂ tl₂) :=
  Conv.trans (Conv.listCons_cong_head tl₁ h_hd)
             (Conv.listCons_cong_tail hd₂ h_tl)

/-- Definitional equivalence threads through `listElim`'s scrutinee. -/
theorem Conv.listElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.list elementType)}
    (nilBranch : Term ctx resultType)
    (consBranch : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType)))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.listElim scrutinee₁ nilBranch consBranch)
         (Term.listElim scrutinee₂ nilBranch consBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.listElimScrutinee s)

/-- Definitional equivalence threads through `listElim`'s nil-branch. -/
theorem Conv.listElim_cong_nil
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.list elementType))
    {nilBranch₁ nilBranch₂ : Term ctx resultType}
    (consBranch : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType)))
    (h : Conv nilBranch₁ nilBranch₂) :
    Conv (Term.listElim scrutinee nilBranch₁ consBranch)
         (Term.listElim scrutinee nilBranch₂ consBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.listElimNil s)

/-- Definitional equivalence threads through `listElim`'s cons-branch. -/
theorem Conv.listElim_cong_cons
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.list elementType))
    (nilBranch : Term ctx resultType)
    {consBranch₁ consBranch₂ : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))}
    (h : Conv consBranch₁ consBranch₂) :
    Conv (Term.listElim scrutinee nilBranch consBranch₁)
         (Term.listElim scrutinee nilBranch consBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.listElimCons s)

/-- Definitional equivalence threads through all three `listElim` positions. -/
theorem Conv.listElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.list elementType)}
    {nilBranch₁ nilBranch₂ : Term ctx resultType}
    {consBranch₁ consBranch₂ : Term ctx
       (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_nil : Conv nilBranch₁ nilBranch₂)
    (h_cons : Conv consBranch₁ consBranch₂) :
    Conv (Term.listElim scrutinee₁ nilBranch₁ consBranch₁)
         (Term.listElim scrutinee₂ nilBranch₂ consBranch₂) :=
  Conv.trans
    (Conv.listElim_cong_scrutinee nilBranch₁ consBranch₁ h_scr)
    (Conv.trans
      (Conv.listElim_cong_nil scrutinee₂ consBranch₁ h_nil)
      (Conv.listElim_cong_cons scrutinee₂ nilBranch₂ h_cons))

/-! ## Option Conv congruences (mirror the list versions). -/

/-- Definitional equivalence threads through `Term.optionSome`'s value. -/
theorem Conv.optionSome_cong {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {value₁ value₂ : Term ctx elementType} (h : Conv value₁ value₂) :
    Conv (Term.optionSome value₁) (Term.optionSome value₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.optionSomeValue s)

/-- Definitional equivalence threads through `optionMatch`'s scrutinee. -/
theorem Conv.optionMatch_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.option elementType)}
    (noneBranch : Term ctx resultType)
    (someBranch : Term ctx (Ty.arrow elementType resultType))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.optionMatch scrutinee₁ noneBranch someBranch)
         (Term.optionMatch scrutinee₂ noneBranch someBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.optionMatchScrutinee s)

/-- Definitional equivalence threads through `optionMatch`'s none-branch. -/
theorem Conv.optionMatch_cong_none
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    {noneBranch₁ noneBranch₂ : Term ctx resultType}
    (someBranch : Term ctx (Ty.arrow elementType resultType))
    (h : Conv noneBranch₁ noneBranch₂) :
    Conv (Term.optionMatch scrutinee noneBranch₁ someBranch)
         (Term.optionMatch scrutinee noneBranch₂ someBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.optionMatchNone s)

/-- Definitional equivalence threads through `optionMatch`'s some-branch. -/
theorem Conv.optionMatch_cong_some
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    (noneBranch : Term ctx resultType)
    {someBranch₁ someBranch₂ : Term ctx (Ty.arrow elementType resultType)}
    (h : Conv someBranch₁ someBranch₂) :
    Conv (Term.optionMatch scrutinee noneBranch someBranch₁)
         (Term.optionMatch scrutinee noneBranch someBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.optionMatchSome s)

/-- Definitional equivalence threads through all three `optionMatch` positions. -/
theorem Conv.optionMatch_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.option elementType)}
    {noneBranch₁ noneBranch₂ : Term ctx resultType}
    {someBranch₁ someBranch₂ : Term ctx (Ty.arrow elementType resultType)}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_none : Conv noneBranch₁ noneBranch₂)
    (h_some : Conv someBranch₁ someBranch₂) :
    Conv (Term.optionMatch scrutinee₁ noneBranch₁ someBranch₁)
         (Term.optionMatch scrutinee₂ noneBranch₂ someBranch₂) :=
  Conv.trans
    (Conv.optionMatch_cong_scrutinee noneBranch₁ someBranch₁ h_scr)
    (Conv.trans
      (Conv.optionMatch_cong_none scrutinee₂ someBranch₁ h_none)
      (Conv.optionMatch_cong_some scrutinee₂ noneBranch₂ h_some))

/-! ## Either Conv congruences (mirror the option versions). -/

/-- Definitional equivalence threads through `Term.eitherInl`'s value. -/
theorem Conv.eitherInl_cong {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value₁ value₂ : Term ctx leftType} (h : Conv value₁ value₂) :
    Conv (Term.eitherInl (rightType := rightType) value₁)
         (Term.eitherInl (rightType := rightType) value₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherInlValue s)

/-- Definitional equivalence threads through `Term.eitherInr`'s value. -/
theorem Conv.eitherInr_cong {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value₁ value₂ : Term ctx rightType} (h : Conv value₁ value₂) :
    Conv (Term.eitherInr (leftType := leftType) value₁)
         (Term.eitherInr (leftType := leftType) value₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherInrValue s)

/-- Definitional equivalence threads through `eitherMatch`'s scrutinee. -/
theorem Conv.eitherMatch_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.either leftType rightType)}
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    (rightBranch : Term ctx (Ty.arrow rightType resultType))
    (h : Conv scrutinee₁ scrutinee₂) :
    Conv (Term.eitherMatch scrutinee₁ leftBranch rightBranch)
         (Term.eitherMatch scrutinee₂ leftBranch rightBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherMatchScrutinee s)

/-- Definitional equivalence threads through `eitherMatch`'s left-branch. -/
theorem Conv.eitherMatch_cong_left
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    {leftBranch₁ leftBranch₂ : Term ctx (Ty.arrow leftType resultType)}
    (rightBranch : Term ctx (Ty.arrow rightType resultType))
    (h : Conv leftBranch₁ leftBranch₂) :
    Conv (Term.eitherMatch scrutinee leftBranch₁ rightBranch)
         (Term.eitherMatch scrutinee leftBranch₂ rightBranch) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherMatchLeft s)

/-- Definitional equivalence threads through `eitherMatch`'s right-branch. -/
theorem Conv.eitherMatch_cong_right
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    {rightBranch₁ rightBranch₂ : Term ctx (Ty.arrow rightType resultType)}
    (h : Conv rightBranch₁ rightBranch₂) :
    Conv (Term.eitherMatch scrutinee leftBranch rightBranch₁)
         (Term.eitherMatch scrutinee leftBranch rightBranch₂) := by
  induction h with
  | refl _              => exact Conv.refl _
  | sym _ ih            => exact Conv.sym ih
  | trans _ _ ih₁ ih₂   => exact Conv.trans ih₁ ih₂
  | fromStep s          => exact Conv.fromStep (Step.eitherMatchRight s)

/-- Definitional equivalence threads through all three `eitherMatch` positions. -/
theorem Conv.eitherMatch_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.either leftType rightType)}
    {leftBranch₁ leftBranch₂ : Term ctx (Ty.arrow leftType resultType)}
    {rightBranch₁ rightBranch₂ : Term ctx (Ty.arrow rightType resultType)}
    (h_scr : Conv scrutinee₁ scrutinee₂)
    (h_left : Conv leftBranch₁ leftBranch₂)
    (h_right : Conv rightBranch₁ rightBranch₂) :
    Conv (Term.eitherMatch scrutinee₁ leftBranch₁ rightBranch₁)
         (Term.eitherMatch scrutinee₂ leftBranch₂ rightBranch₂) :=
  Conv.trans
    (Conv.eitherMatch_cong_scrutinee leftBranch₁ rightBranch₁ h_scr)
    (Conv.trans
      (Conv.eitherMatch_cong_left scrutinee₂ rightBranch₁ h_left)
      (Conv.eitherMatch_cong_right scrutinee₂ leftBranch₂ h_right))

/-! ## StepStar congruences for nat (defined above the Conv versions
because Step.par.toStar consumes them). -/

/-- Multi-step reduction threads through `Term.natSucc`. -/
theorem StepStar.natSucc_cong {mode level scope} {ctx : Ctx mode level scope}
    {pred₁ pred₂ : Term ctx Ty.nat} :
    StepStar pred₁ pred₂ →
    StepStar (Term.natSucc pred₁) (Term.natSucc pred₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natSuccPred s)
        (StepStar.natSucc_cong rest)

/-- Multi-step reduction threads through `natElim`'s scrutinee. -/
theorem StepStar.natElim_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType)) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.natElim scrutinee₁ zeroBranch succBranch)
             (Term.natElim scrutinee₂ zeroBranch succBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natElimScrutinee s)
        (StepStar.natElim_cong_scrutinee zeroBranch succBranch rest)

/-- Multi-step reduction threads through `natElim`'s zero-branch. -/
theorem StepStar.natElim_cong_zero
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType)) :
    StepStar zeroBranch₁ zeroBranch₂ →
    StepStar (Term.natElim scrutinee zeroBranch₁ succBranch)
             (Term.natElim scrutinee zeroBranch₂ succBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natElimZero s)
        (StepStar.natElim_cong_zero scrutinee succBranch rest)

/-- Multi-step reduction threads through `natElim`'s succ-branch. -/
theorem StepStar.natElim_cong_succ
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch₁ succBranch₂ : Term ctx (Ty.arrow Ty.nat resultType)} :
    StepStar succBranch₁ succBranch₂ →
    StepStar (Term.natElim scrutinee zeroBranch succBranch₁)
             (Term.natElim scrutinee zeroBranch succBranch₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natElimSucc s)
        (StepStar.natElim_cong_succ scrutinee zeroBranch rest)

/-- Multi-step reduction threads through all three `natElim` positions. -/
theorem StepStar.natElim_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    {succBranch₁ succBranch₂ : Term ctx (Ty.arrow Ty.nat resultType)}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_zero : StepStar zeroBranch₁ zeroBranch₂)
    (h_succ : StepStar succBranch₁ succBranch₂) :
    StepStar (Term.natElim scrutinee₁ zeroBranch₁ succBranch₁)
             (Term.natElim scrutinee₂ zeroBranch₂ succBranch₂) :=
  StepStar.trans
    (StepStar.natElim_cong_scrutinee zeroBranch₁ succBranch₁ h_scr)
    (StepStar.trans
      (StepStar.natElim_cong_zero scrutinee₂ succBranch₁ h_zero)
      (StepStar.natElim_cong_succ scrutinee₂ zeroBranch₂ h_succ))

/-! ## natRec StepStar congruences (placed before Step.par.toStar
which consumes them, parallel to natElim). -/

/-- Multi-step reduction threads through `natRec`'s scrutinee. -/
theorem StepStar.natRec_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.natRec scrutinee₁ zeroBranch succBranch)
             (Term.natRec scrutinee₂ zeroBranch succBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natRecScrutinee s)
        (StepStar.natRec_cong_scrutinee zeroBranch succBranch rest)

/-- Multi-step reduction threads through `natRec`'s zero-branch. -/
theorem StepStar.natRec_cong_zero
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    (succBranch : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))) :
    StepStar zeroBranch₁ zeroBranch₂ →
    StepStar (Term.natRec scrutinee zeroBranch₁ succBranch)
             (Term.natRec scrutinee zeroBranch₂ succBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natRecZero s)
        (StepStar.natRec_cong_zero scrutinee succBranch rest)

/-- Multi-step reduction threads through `natRec`'s succ-branch. -/
theorem StepStar.natRec_cong_succ
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch₁ succBranch₂ : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))} :
    StepStar succBranch₁ succBranch₂ →
    StepStar (Term.natRec scrutinee zeroBranch succBranch₁)
             (Term.natRec scrutinee zeroBranch succBranch₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.natRecSucc s)
        (StepStar.natRec_cong_succ scrutinee zeroBranch rest)

/-- Multi-step reduction threads through all three `natRec` positions. -/
theorem StepStar.natRec_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx Ty.nat}
    {zeroBranch₁ zeroBranch₂ : Term ctx resultType}
    {succBranch₁ succBranch₂ : Term ctx
       (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_zero : StepStar zeroBranch₁ zeroBranch₂)
    (h_succ : StepStar succBranch₁ succBranch₂) :
    StepStar (Term.natRec scrutinee₁ zeroBranch₁ succBranch₁)
             (Term.natRec scrutinee₂ zeroBranch₂ succBranch₂) :=
  StepStar.trans
    (StepStar.natRec_cong_scrutinee zeroBranch₁ succBranch₁ h_scr)
    (StepStar.trans
      (StepStar.natRec_cong_zero scrutinee₂ succBranch₁ h_zero)
      (StepStar.natRec_cong_succ scrutinee₂ zeroBranch₂ h_succ))

/-! ## Option StepStar congruences (placed before Step.par.toStar
which consumes them). -/

/-- Multi-step reduction threads through `Term.optionSome`. -/
theorem StepStar.optionSome_cong {mode level scope} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {value₁ value₂ : Term ctx elementType} :
    StepStar value₁ value₂ →
    StepStar (Term.optionSome value₁) (Term.optionSome value₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.optionSomeValue s)
        (StepStar.optionSome_cong rest)

/-- Multi-step reduction threads through `optionMatch`'s scrutinee. -/
theorem StepStar.optionMatch_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.option elementType)}
    (noneBranch : Term ctx resultType)
    (someBranch : Term ctx (Ty.arrow elementType resultType)) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.optionMatch scrutinee₁ noneBranch someBranch)
             (Term.optionMatch scrutinee₂ noneBranch someBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.optionMatchScrutinee s)
        (StepStar.optionMatch_cong_scrutinee noneBranch someBranch rest)

/-- Multi-step reduction threads through `optionMatch`'s none-branch. -/
theorem StepStar.optionMatch_cong_none
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    {noneBranch₁ noneBranch₂ : Term ctx resultType}
    (someBranch : Term ctx (Ty.arrow elementType resultType)) :
    StepStar noneBranch₁ noneBranch₂ →
    StepStar (Term.optionMatch scrutinee noneBranch₁ someBranch)
             (Term.optionMatch scrutinee noneBranch₂ someBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.optionMatchNone s)
        (StepStar.optionMatch_cong_none scrutinee someBranch rest)

/-- Multi-step reduction threads through `optionMatch`'s some-branch. -/
theorem StepStar.optionMatch_cong_some
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    (noneBranch : Term ctx resultType)
    {someBranch₁ someBranch₂ : Term ctx (Ty.arrow elementType resultType)} :
    StepStar someBranch₁ someBranch₂ →
    StepStar (Term.optionMatch scrutinee noneBranch someBranch₁)
             (Term.optionMatch scrutinee noneBranch someBranch₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.optionMatchSome s)
        (StepStar.optionMatch_cong_some scrutinee noneBranch rest)

/-- Multi-step reduction threads through all three `optionMatch` positions. -/
theorem StepStar.optionMatch_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.option elementType)}
    {noneBranch₁ noneBranch₂ : Term ctx resultType}
    {someBranch₁ someBranch₂ : Term ctx (Ty.arrow elementType resultType)}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_none : StepStar noneBranch₁ noneBranch₂)
    (h_some : StepStar someBranch₁ someBranch₂) :
    StepStar (Term.optionMatch scrutinee₁ noneBranch₁ someBranch₁)
             (Term.optionMatch scrutinee₂ noneBranch₂ someBranch₂) :=
  StepStar.trans
    (StepStar.optionMatch_cong_scrutinee noneBranch₁ someBranch₁ h_scr)
    (StepStar.trans
      (StepStar.optionMatch_cong_none scrutinee₂ someBranch₁ h_none)
      (StepStar.optionMatch_cong_some scrutinee₂ noneBranch₂ h_some))

/-! ## Either StepStar congruences (placed before Step.par.toStar
which consumes them). -/

/-- Multi-step reduction threads through `Term.eitherInl`. -/
theorem StepStar.eitherInl_cong {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value₁ value₂ : Term ctx leftType} :
    StepStar value₁ value₂ →
    StepStar (Term.eitherInl (rightType := rightType) value₁)
             (Term.eitherInl (rightType := rightType) value₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherInlValue s)
        (StepStar.eitherInl_cong rest)

/-- Multi-step reduction threads through `Term.eitherInr`. -/
theorem StepStar.eitherInr_cong {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value₁ value₂ : Term ctx rightType} :
    StepStar value₁ value₂ →
    StepStar (Term.eitherInr (leftType := leftType) value₁)
             (Term.eitherInr (leftType := leftType) value₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherInrValue s)
        (StepStar.eitherInr_cong rest)

/-- Multi-step reduction threads through `eitherMatch`'s scrutinee. -/
theorem StepStar.eitherMatch_cong_scrutinee
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.either leftType rightType)}
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    (rightBranch : Term ctx (Ty.arrow rightType resultType)) :
    StepStar scrutinee₁ scrutinee₂ →
    StepStar (Term.eitherMatch scrutinee₁ leftBranch rightBranch)
             (Term.eitherMatch scrutinee₂ leftBranch rightBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherMatchScrutinee s)
        (StepStar.eitherMatch_cong_scrutinee leftBranch rightBranch rest)

/-- Multi-step reduction threads through `eitherMatch`'s left-branch. -/
theorem StepStar.eitherMatch_cong_left
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    {leftBranch₁ leftBranch₂ : Term ctx (Ty.arrow leftType resultType)}
    (rightBranch : Term ctx (Ty.arrow rightType resultType)) :
    StepStar leftBranch₁ leftBranch₂ →
    StepStar (Term.eitherMatch scrutinee leftBranch₁ rightBranch)
             (Term.eitherMatch scrutinee leftBranch₂ rightBranch)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherMatchLeft s)
        (StepStar.eitherMatch_cong_left scrutinee rightBranch rest)

/-- Multi-step reduction threads through `eitherMatch`'s right-branch. -/
theorem StepStar.eitherMatch_cong_right
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    {rightBranch₁ rightBranch₂ : Term ctx (Ty.arrow rightType resultType)} :
    StepStar rightBranch₁ rightBranch₂ →
    StepStar (Term.eitherMatch scrutinee leftBranch rightBranch₁)
             (Term.eitherMatch scrutinee leftBranch rightBranch₂)
  | .refl _      => StepStar.refl _
  | .step s rest =>
      StepStar.step (Step.eitherMatchRight s)
        (StepStar.eitherMatch_cong_right scrutinee leftBranch rest)

/-- Multi-step reduction threads through all three `eitherMatch` positions. -/
theorem StepStar.eitherMatch_cong
    {mode level scope} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee₁ scrutinee₂ : Term ctx (Ty.either leftType rightType)}
    {leftBranch₁ leftBranch₂ : Term ctx (Ty.arrow leftType resultType)}
    {rightBranch₁ rightBranch₂ : Term ctx (Ty.arrow rightType resultType)}
    (h_scr : StepStar scrutinee₁ scrutinee₂)
    (h_left : StepStar leftBranch₁ leftBranch₂)
    (h_right : StepStar rightBranch₁ rightBranch₂) :
    StepStar (Term.eitherMatch scrutinee₁ leftBranch₁ rightBranch₁)
             (Term.eitherMatch scrutinee₂ leftBranch₂ rightBranch₂) :=
  StepStar.trans
    (StepStar.eitherMatch_cong_scrutinee leftBranch₁ rightBranch₁ h_scr)
    (StepStar.trans
      (StepStar.eitherMatch_cong_left scrutinee₂ rightBranch₁ h_left)
      (StepStar.eitherMatch_cong_right scrutinee₂ leftBranch₂ h_right))

/-! ## `Step.par.toStar` — parallel reduction lifts to multi-step.

Each Step.par constructor decomposes into a sequence of single Step's
chained via StepStar congruences.  Subterm-parallel cases use the
corresponding StepStar congruence directly; β/Σ cases chain congruences
first then append a final Step.beta_* via StepStar.append; ι cases
similarly chain boolElim_cong with Step.iota_*; η cases lift directly
via Step.toStar.

Placed AFTER StepStar.append and the boolean StepStar congruences
(which v1.49 needs but were originally defined later in the file).

Together with Step.toPar (v1.48), this establishes the bridge between
StepStar and the reflexive-transitive closure of Step.par — the
Tait–Martin-Löf reformulation that makes confluence tractable. -/
theorem Step.par.toStar
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope} {T : Ty level scope}
    {t₁ t₂ : Term ctx T} : Step.par t₁ t₂ → StepStar t₁ t₂
  | .refl t                  => StepStar.refl t
  | .app par_f par_a         =>
      StepStar.app_cong (Step.par.toStar par_f) (Step.par.toStar par_a)
  | .lam par_body            =>
      StepStar.lam_cong (Step.par.toStar par_body)
  | .lamPi par_body          =>
      StepStar.lamPi_cong (Step.par.toStar par_body)
  | .appPi par_f par_a       =>
      StepStar.appPi_cong (Step.par.toStar par_f) (Step.par.toStar par_a)
  | .pair par_v par_w        =>
      StepStar.pair_cong (Step.par.toStar par_v) (Step.par.toStar par_w)
  | .fst par_p               => StepStar.fst_cong (Step.par.toStar par_p)
  | .snd par_p               => StepStar.snd_cong (Step.par.toStar par_p)
  | .boolElim par_s par_t par_e =>
      StepStar.boolElim_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_t)
        (Step.par.toStar par_e)
  | .betaApp (body' := body') (arg' := arg') par_body par_arg =>
      -- StepStar (app (lam body) arg) (app (lam body') arg')
      --   via app_cong of lam_cong (par_body.toStar) and par_arg.toStar
      -- then Step.betaApp body' arg' completes the β-step.
      StepStar.append
        (StepStar.app_cong
          (StepStar.lam_cong (Step.par.toStar par_body))
          (Step.par.toStar par_arg))
        (Step.betaApp body' arg')
  | .betaAppPi (body' := body') (arg' := arg') par_body par_arg =>
      StepStar.append
        (StepStar.appPi_cong
          (StepStar.lamPi_cong (Step.par.toStar par_body))
          (Step.par.toStar par_arg))
        (Step.betaAppPi body' arg')
  | .betaFstPair (firstVal' := v') secondVal par_v =>
      StepStar.append
        (StepStar.fst_cong
          (StepStar.pair_cong
            (Step.par.toStar par_v) (StepStar.refl secondVal)))
        (Step.betaFstPair v' secondVal)
  | .betaSndPair (secondVal' := w') firstVal par_w =>
      StepStar.append
        (StepStar.snd_cong
          (StepStar.pair_cong
            (StepStar.refl firstVal) (Step.par.toStar par_w)))
        (Step.betaSndPair firstVal w')
  | .iotaBoolElimTrue (thenBr' := t') elseBr par_t =>
      StepStar.append
        (StepStar.boolElim_cong
          (StepStar.refl Term.boolTrue)
          (Step.par.toStar par_t)
          (StepStar.refl elseBr))
        (Step.iotaBoolElimTrue t' elseBr)
  | .iotaBoolElimFalse (elseBr' := e') thenBr par_e =>
      StepStar.append
        (StepStar.boolElim_cong
          (StepStar.refl Term.boolFalse)
          (StepStar.refl thenBr)
          (Step.par.toStar par_e))
        (Step.iotaBoolElimFalse thenBr e')
  | .natSucc par_pred        =>
      StepStar.natSucc_cong (Step.par.toStar par_pred)
  | .natElim par_s par_z par_f =>
      StepStar.natElim_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_z)
        (Step.par.toStar par_f)
  | .iotaNatElimZero (zeroBranch' := z') succBranch par_z =>
      StepStar.append
        (StepStar.natElim_cong
          (StepStar.refl Term.natZero)
          (Step.par.toStar par_z)
          (StepStar.refl succBranch))
        (Step.iotaNatElimZero z' succBranch)
  | .iotaNatElimSucc
        (predecessor' := n') (succBranch' := f')
        zeroBranch par_n par_f =>
      StepStar.trans
        (StepStar.natElim_cong
          (StepStar.natSucc_cong (Step.par.toStar par_n))
          (StepStar.refl zeroBranch)
          (Step.par.toStar par_f))
        (Step.toStar (Step.iotaNatElimSucc n' zeroBranch f'))
  | .natRec par_s par_z par_f =>
      StepStar.natRec_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_z)
        (Step.par.toStar par_f)
  | .iotaNatRecZero (zeroBranch' := z') succBranch par_z =>
      StepStar.append
        (StepStar.natRec_cong
          (StepStar.refl Term.natZero)
          (Step.par.toStar par_z)
          (StepStar.refl succBranch))
        (Step.iotaNatRecZero z' succBranch)
  | .iotaNatRecSucc
        (predecessor' := n') (zeroBranch' := z') (succBranch' := s')
        par_n par_z par_s =>
      StepStar.trans
        (StepStar.natRec_cong
          (StepStar.natSucc_cong (Step.par.toStar par_n))
          (Step.par.toStar par_z)
          (Step.par.toStar par_s))
        (Step.toStar (Step.iotaNatRecSucc n' z' s'))
  | .listCons par_hd par_tl  =>
      StepStar.listCons_cong (Step.par.toStar par_hd) (Step.par.toStar par_tl)
  | .listElim par_s par_n par_c =>
      StepStar.listElim_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_n)
        (Step.par.toStar par_c)
  | .iotaListElimNil (nilBranch' := n') consBranch par_n =>
      StepStar.append
        (StepStar.listElim_cong
          (StepStar.refl Term.listNil)
          (Step.par.toStar par_n)
          (StepStar.refl consBranch))
        (Step.iotaListElimNil n' consBranch)
  | .iotaListElimCons
        (head' := h') (tail' := t') (consBranch' := c')
        nilBranch par_h par_t par_c =>
      StepStar.trans
        (StepStar.listElim_cong
          (StepStar.listCons_cong (Step.par.toStar par_h) (Step.par.toStar par_t))
          (StepStar.refl nilBranch)
          (Step.par.toStar par_c))
        (Step.toStar (Step.iotaListElimCons h' t' nilBranch c'))
  | .optionSome par_value    =>
      StepStar.optionSome_cong (Step.par.toStar par_value)
  | .optionMatch par_s par_n par_sm =>
      StepStar.optionMatch_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_n)
        (Step.par.toStar par_sm)
  | .iotaOptionMatchNone (noneBranch' := n') someBranch par_n =>
      StepStar.append
        (StepStar.optionMatch_cong
          (StepStar.refl Term.optionNone)
          (Step.par.toStar par_n)
          (StepStar.refl someBranch))
        (Step.iotaOptionMatchNone n' someBranch)
  | .iotaOptionMatchSome
        (value' := v') (someBranch' := sm')
        noneBranch par_value par_some =>
      StepStar.trans
        (StepStar.optionMatch_cong
          (StepStar.optionSome_cong (Step.par.toStar par_value))
          (StepStar.refl noneBranch)
          (Step.par.toStar par_some))
        (Step.toStar (Step.iotaOptionMatchSome v' noneBranch sm'))
  | .eitherInl par_value     =>
      StepStar.eitherInl_cong (Step.par.toStar par_value)
  | .eitherInr par_value     =>
      StepStar.eitherInr_cong (Step.par.toStar par_value)
  | .eitherMatch par_s par_l par_r =>
      StepStar.eitherMatch_cong
        (Step.par.toStar par_s)
        (Step.par.toStar par_l)
        (Step.par.toStar par_r)
  | .iotaEitherMatchInl
        (value' := v') (leftBranch' := lb')
        rightBranch par_value par_left =>
      StepStar.trans
        (StepStar.eitherMatch_cong
          (StepStar.eitherInl_cong (Step.par.toStar par_value))
          (Step.par.toStar par_left)
          (StepStar.refl rightBranch))
        (Step.toStar (Step.iotaEitherMatchInl v' lb' rightBranch))
  | .iotaEitherMatchInr
        (value' := v') (rightBranch' := rb')
        leftBranch par_value par_right =>
      StepStar.trans
        (StepStar.eitherMatch_cong
          (StepStar.eitherInr_cong (Step.par.toStar par_value))
          (StepStar.refl leftBranch)
          (Step.par.toStar par_right))
        (Step.toStar (Step.iotaEitherMatchInr v' leftBranch rb'))
  | .etaArrow f              => Step.toStar (Step.etaArrow f)
  | .etaSigma p              => Step.toStar (Step.etaSigma p)

/-! ## External identity proofs.

`IdProof t₁ t₂` witnesses that two terms of the same FX type are
intensionally equal at the kernel meta-level — a `Type`-valued
inductive family with the single constructor `refl`.

The family lives outside `Term` because the surface FX `Id A a b :
Type` requires universe codes (`El : Term Γ (Ty.universe u rfl) →
Ty u scope`) before it can be promoted into a Term-level type
former.  Until v1.51's El bridge lands, IdProof scaffolds FX-level
cast, transport, and conversion-witness reasoning at the metatheory
layer — the structural lemmas (symm, trans, cong, subst-commute,
rename-commute) are exactly the ones the bridge will translate
into Term-level operations.

Distinct from Lean's `Eq` because IdProof carries the FX type `T`
and the context `Γ` explicitly, and is intentionally `Type`-valued
so that a future J eliminator (v1.43+) can compute over its proof
content rather than collapsing into proof-irrelevance.  This is the
HoTT-friendly choice: the path between two terms is data, not a
mere proposition. -/
inductive IdProof : {mode : Mode} → {level scope : Nat} →
    {context : Ctx mode level scope} → {resultType : Ty level scope} →
    Term context resultType → Term context resultType → Type
  /-- Reflexivity — every term is identity-related to itself.  The
  unique constructor; pattern-matching on `refl` definitionally
  collapses both sides to the same term. -/
  | refl : {mode : Mode} → {level scope : Nat} →
           {context : Ctx mode level scope} →
           {resultType : Ty level scope} →
           (term : Term context resultType) → IdProof term term

namespace IdProof

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
         {resultType : Ty level scope}

/-- Symmetry — flip the sides of an identity proof.  Pattern-on-refl
collapses both sides to a single term, after which `refl` discharges
in the swapped orientation. -/
def symm {term₁ term₂ : Term context resultType} :
    IdProof term₁ term₂ → IdProof term₂ term₁
  | .refl _ => IdProof.refl _

/-- Transitivity — chain two identity proofs through a common
midpoint.  Pattern-matching on the first proof's `refl` collapses
`term₁ = term₂`, leaving the second proof witnessing
`IdProof term₂ term₃` — exactly what we return. -/
def trans {term₁ term₂ term₃ : Term context resultType} :
    IdProof term₁ term₂ → IdProof term₂ term₃ → IdProof term₁ term₃
  | .refl _, proof => proof

/-- Function congruence — apply an arbitrary `Term → Term` operation
to both sides of an identity proof.  Lean's `congrArg` analogue,
specialised to Term-valued functions on a single FX context. -/
def cong {sourceType targetType : Ty level scope}
    (function : Term context sourceType → Term context targetType)
    {term₁ term₂ : Term context sourceType} :
    IdProof term₁ term₂ → IdProof (function term₁) (function term₂)
  | .refl _ => IdProof.refl _

/-- Application congruence — both function and argument may differ.
Composition of two `cong` calls; provided directly because it's the
most common shape (`Term.app f a` propagates IdProof through both
positions). -/
def cong_app {domainType codomainType : Ty level scope}
    {function₁ function₂ : Term context (Ty.arrow domainType codomainType)}
    {argument₁ argument₂ : Term context domainType}
    (h_function : IdProof function₁ function₂)
    (h_argument : IdProof argument₁ argument₂) :
    IdProof (Term.app function₁ argument₁) (Term.app function₂ argument₂) :=
  match h_function, h_argument with
  | .refl _, .refl _ => IdProof.refl _

/-- Substitution-commute — applying a `TermSubst` to both sides of
an identity proof yields an identity proof on the substituted terms.
Pattern-on-refl collapses both sides; `IdProof.refl` on the
substituted term discharges. -/
def subst {scope' : Nat} {context' : Ctx mode level scope'}
    {σ : Subst level scope scope'} (σt : TermSubst context context' σ)
    {term₁ term₂ : Term context resultType} :
    IdProof term₁ term₂ →
    IdProof (Term.subst σt term₁) (Term.subst σt term₂)
  | .refl _ => IdProof.refl _

/-- Renaming-commute — analogue of `subst` for `TermRenaming`. -/
def rename {scope' : Nat} {context' : Ctx mode level scope'}
    {ρ : Renaming scope scope'} (ρt : TermRenaming context context' ρ)
    {term₁ term₂ : Term context resultType} :
    IdProof term₁ term₂ →
    IdProof (Term.rename ρt term₁) (Term.rename ρt term₂)
  | .refl _ => IdProof.refl _

/-- IdProof-to-equality bridge — every IdProof witnesses a Lean
`Eq` between the underlying terms.  Useful for stating metatheory
lemmas that mix the two notions; the reverse direction
(`Eq → IdProof`) is just `· ▸ IdProof.refl _`. -/
def toEq {term₁ term₂ : Term context resultType} :
    IdProof term₁ term₂ → term₁ = term₂
  | .refl _ => rfl

/-- Equality-to-IdProof bridge — promote a Lean `Eq` between Terms
of the same type into an IdProof.  The companion of `toEq`. -/
def ofEq {term₁ term₂ : Term context resultType} :
    term₁ = term₂ → IdProof term₁ term₂
  | rfl => IdProof.refl _

end IdProof

/-! ## Smoke tests.

Direct constructor exercises that verify the kernel accepts canonical
well-typed terms.  Compile-time only — every `example` below fails to
elaborate if a constructor signature is mis-stated, an index aligned
wrong, or a reduction rule mistyped.

Stratified by what they exercise:

  * `unit` and `bool` introductions at the empty context.
  * λ-abstraction and application — both non-dependent (`lam` / `app`)
    and dependent (`lamPi` / `appPi`).
  * Σ-pair construction and projection.
  * The `Term.var` / `varType` interaction at scope `+1`.
  * Single-step reductions: β for arrow, β for Π, fst/snd of pair,
    ι for boolElim, η for arrow.
  * Multi-step and parallel reduction lifts.

These are not exhaustive metatheory tests (the §23.6 conformance suite
will be); they are arity / signature regressions guards. -/

namespace SmokeTest

/-- The empty Software context at level 0. -/
private abbrev EmptyCtx : Ctx Mode.software 0 0 := .nil Mode.software

/-- `() : unit` in the empty context. -/
example : Term EmptyCtx Ty.unit := Term.unit

/-- `true : bool` in the empty context. -/
example : Term EmptyCtx Ty.bool := Term.boolTrue

/-- `λx:unit. x : unit → unit` — the identity on `unit`. -/
example : Term EmptyCtx (Ty.arrow Ty.unit Ty.unit) :=
  Term.lam (Term.var ⟨0, Nat.zero_lt_succ _⟩)

/-- `(λx:unit. x) () ⟶ subst…` — β-reduction at the kernel level.
The reduct type carries a `Ty.weaken_subst_singleton` cast; we don't
spell it out here, just verify the rule's signature accepts the term. -/
example
    (body : Term (EmptyCtx.cons Ty.unit) Ty.unit.weaken)
    (arg  : Term EmptyCtx Ty.unit) :
    Step (Term.app (codomainType := Ty.unit) (Term.lam body) arg)
         ((Ty.weaken_subst_singleton Ty.unit Ty.unit) ▸
            Term.subst0 body arg) :=
  Step.betaApp body arg

/-- `boolElim true t e ⟶ t` — ι-reduction. -/
example (t e : Term EmptyCtx Ty.bool) :
    Step (Term.boolElim Term.boolTrue t e) t :=
  Step.iotaBoolElimTrue t e

/-- `boolElim false t e ⟶ e` — ι-reduction. -/
example (t e : Term EmptyCtx Ty.bool) :
    Step (Term.boolElim Term.boolFalse t e) e :=
  Step.iotaBoolElimFalse t e

/-- η-contraction of the identity-application form. -/
example (f : Term EmptyCtx (Ty.arrow Ty.unit Ty.unit)) :
    Step (Term.lam
            (Term.app (Term.weaken Ty.unit f)
                      (Term.var ⟨0, Nat.zero_lt_succ _⟩)))
         f :=
  Step.etaArrow f

/-- η-contraction for Σ pairs. -/
example {firstType : Ty 0 0} {secondType : Ty 0 1}
    (p : Term EmptyCtx (Ty.sigmaTy firstType secondType)) :
    Step (Term.pair (Term.fst p) (Term.snd p)) p :=
  Step.etaSigma p

/-! ### IdProof — identity-proof scaffold (meta-level). -/

/-- Reflexivity at the unit constructor. -/
example : IdProof (Term.unit (context := EmptyCtx)) Term.unit :=
  IdProof.refl _

/-- Reflexivity at a boolean constructor. -/
example : IdProof (Term.boolTrue (context := EmptyCtx)) Term.boolTrue :=
  IdProof.refl _

/-- `IdProof.symm (refl t) ≡ refl t` definitionally. -/
example :
    IdProof.symm (IdProof.refl (Term.boolTrue (context := EmptyCtx)))
      = IdProof.refl Term.boolTrue := rfl

/-- `IdProof.trans` of two `refl`s on the same term is `refl`. -/
example :
    IdProof.trans
      (IdProof.refl (Term.boolTrue (context := EmptyCtx)))
      (IdProof.refl Term.boolTrue)
      = IdProof.refl Term.boolTrue := rfl

/-- `IdProof.cong` propagates through `Term.app` — use case for FX-level
function-application equational reasoning. -/
example (function : Term EmptyCtx (Ty.arrow Ty.bool Ty.bool))
        {arg₁ arg₂ : Term EmptyCtx Ty.bool} (h : IdProof arg₁ arg₂) :
    IdProof (Term.app function arg₁) (Term.app function arg₂) :=
  IdProof.cong (Term.app function) h

/-- `IdProof.cong_app` propagates through both function and argument
positions simultaneously. -/
example {function₁ function₂ : Term EmptyCtx (Ty.arrow Ty.bool Ty.bool)}
        {arg₁ arg₂ : Term EmptyCtx Ty.bool}
        (h_function : IdProof function₁ function₂)
        (h_argument : IdProof arg₁ arg₂) :
    IdProof (Term.app function₁ arg₁) (Term.app function₂ arg₂) :=
  IdProof.cong_app h_function h_argument

/-- `IdProof.toEq` of `refl` is `rfl` — bridge to Lean's propositional
equality is definitional at the canonical-form level. -/
example :
    IdProof.toEq (IdProof.refl (Term.boolTrue (context := EmptyCtx))) = rfl :=
  rfl

/-- `IdProof.ofEq rfl` is `IdProof.refl` — round-trip in the other
direction. -/
example :
    IdProof.ofEq (rfl : Term.boolTrue (context := EmptyCtx) = Term.boolTrue)
      = IdProof.refl Term.boolTrue := rfl

/-- `Type<0> : Ty 1 0` — the smallest universe lives at level 1.
Demonstrates the propositional-equation encoding (`Ty.universe u rfl`):
the `rfl : 1 = 0 + 1` is supplied at the use site to constrain the
otherwise-polymorphic level of the constructor. -/
example : Ty 1 0 := Ty.universe 0 rfl

/-- `Type<3> : Ty 4 0` — universe at an arbitrary level. -/
example : Ty 4 0 := Ty.universe 3 rfl

/-- The universe is preserved by renaming: `(Type<u>).rename ρ = Type<u>`. -/
example {scope target : Nat} (ρ : Renaming scope target) :
    (Ty.universe (level := 1) (scope := scope) 0 rfl).rename ρ
      = Ty.universe (level := 1) (scope := target) 0 rfl :=
  rfl

/-- The universe is preserved by substitution: `(Type<u>).subst σ = Type<u>`. -/
example {scope target : Nat} (σ : Subst 1 scope target) :
    (Ty.universe (level := 1) (scope := scope) 0 rfl).subst σ
      = Ty.universe (level := 1) (scope := target) 0 rfl :=
  rfl

/-- `Ty.nat` is level-polymorphic — exists at any universe level. -/
example : Ty 0 0 := Ty.nat
example : Ty 5 7 := Ty.nat

/-- The natural-number type is preserved by renaming. -/
example {level scope target : Nat} (ρ : Renaming scope target) :
    (Ty.nat (level := level) (scope := scope)).rename ρ
      = Ty.nat (level := level) (scope := target) :=
  rfl

/-- The natural-number type is preserved by substitution. -/
example {level scope target : Nat} (σ : Subst level scope target) :
    (Ty.nat (level := level) (scope := scope)).subst σ
      = Ty.nat (level := level) (scope := target) :=
  rfl

/-- `0 : Nat` in the empty context. -/
example : Term EmptyCtx Ty.nat := Term.natZero

/-- `1 : Nat` — `succ 0`. -/
example : Term EmptyCtx Ty.nat := Term.natSucc Term.natZero

/-- `3 : Nat` — three-fold succ application. -/
example : Term EmptyCtx Ty.nat :=
  Term.natSucc (Term.natSucc (Term.natSucc Term.natZero))

/-- `Term.natZero` is preserved by renaming. -/
example {level scope target : Nat}
    {Γ : Ctx Mode.software level scope}
    {Δ : Ctx Mode.software level target}
    {ρ : Renaming scope target}
    (ρt : TermRenaming Γ Δ ρ) :
    Term.rename ρt (Term.natZero (context := Γ))
      = Term.natZero (context := Δ) :=
  rfl

/-- `Term.natSucc` commutes with renaming. -/
example {level scope target : Nat}
    {Γ : Ctx Mode.software level scope}
    {Δ : Ctx Mode.software level target}
    {ρ : Renaming scope target}
    (ρt : TermRenaming Γ Δ ρ)
    (pred : Term Γ Ty.nat) :
    Term.rename ρt (Term.natSucc pred)
      = Term.natSucc (Term.rename ρt pred) :=
  rfl

/-- `Term.natElim` accepts a scrutinee, zero-branch, and succ-function.
A simple "is zero?" decision: `natElim n true (λ _. false) : bool`. -/
example (n : Term EmptyCtx Ty.nat) : Term EmptyCtx Ty.bool :=
  Term.natElim n
    Term.boolTrue
    -- λ _ : nat. boolFalse — succBranch is a function `nat → bool`.
    (Term.lam (codomainType := Ty.bool) (Term.weaken Ty.nat Term.boolFalse))

/-- `Term.natElim` commutes with renaming on each of its three positions. -/
example {level scope target : Nat}
    {Γ : Ctx Mode.software level scope}
    {Δ : Ctx Mode.software level target}
    {ρ : Renaming scope target}
    (ρt : TermRenaming Γ Δ ρ)
    {result : Ty level scope}
    (scrutinee : Term Γ Ty.nat)
    (zeroBranch : Term Γ result)
    (succBranch : Term Γ (Ty.arrow Ty.nat result)) :
    Term.rename ρt (Term.natElim scrutinee zeroBranch succBranch)
      = Term.natElim (Term.rename ρt scrutinee)
                     (Term.rename ρt zeroBranch)
                     (Term.rename ρt succBranch) :=
  rfl

/-- `Ty.list` is parametric over its element type — works at any level. -/
example : Ty 0 0 := Ty.list Ty.nat
example : Ty 0 0 := Ty.list Ty.bool
example : Ty 0 0 := Ty.list (Ty.list Ty.nat)  -- nested: list of lists of nat
example : Ty 0 0 := Ty.list (Ty.arrow Ty.nat Ty.bool)  -- list of nat→bool

/-- The list type commutes with renaming on its element type. -/
example {level scope target : Nat}
    (ρ : Renaming scope target) (elemType : Ty level scope) :
    (Ty.list elemType).rename ρ = Ty.list (elemType.rename ρ) :=
  rfl

/-- The list type commutes with substitution on its element type. -/
example {level scope target : Nat}
    (σ : Subst level scope target) (elemType : Ty level scope) :
    (Ty.list elemType).subst σ = Ty.list (elemType.subst σ) :=
  rfl

/-- Empty list of nat: `[] : list nat`. -/
example : Term EmptyCtx (Ty.list Ty.nat) :=
  Term.listNil

/-- Singleton list: `[0] : list nat`. -/
example : Term EmptyCtx (Ty.list Ty.nat) :=
  Term.listCons Term.natZero Term.listNil

/-- Three-element list: `[0, 1, 2] : list nat`. -/
example : Term EmptyCtx (Ty.list Ty.nat) :=
  Term.listCons Term.natZero
    (Term.listCons (Term.natSucc Term.natZero)
      (Term.listCons (Term.natSucc (Term.natSucc Term.natZero))
        Term.listNil))

/-- `Term.listNil` is preserved by renaming. -/
example {level scope target : Nat}
    {Γ : Ctx Mode.software level scope}
    {Δ : Ctx Mode.software level target}
    {ρ : Renaming scope target}
    (ρt : TermRenaming Γ Δ ρ)
    {elem : Ty level scope} :
    Term.rename ρt (Term.listNil (context := Γ) (elementType := elem))
      = Term.listNil (context := Δ) (elementType := elem.rename ρ) :=
  rfl

/-- `Term.listCons` commutes with renaming on head and tail. -/
example {level scope target : Nat}
    {Γ : Ctx Mode.software level scope}
    {Δ : Ctx Mode.software level target}
    {ρ : Renaming scope target}
    (ρt : TermRenaming Γ Δ ρ)
    {elem : Ty level scope}
    (hd : Term Γ elem) (tl : Term Γ (Ty.list elem)) :
    Term.rename ρt (Term.listCons hd tl)
      = Term.listCons (Term.rename ρt hd) (Term.rename ρt tl) :=
  rfl

/-- `Term.listElim` accepts scrutinee + nilBranch + consBranch (a
curried `elem → list elem → result` function).  A simple "is empty?"
program: `listElim xs true (λ _ _. false) : bool`. -/
example (xs : Term EmptyCtx (Ty.list Ty.nat)) : Term EmptyCtx Ty.bool :=
  Term.listElim (elementType := Ty.nat) (resultType := Ty.bool)
    xs
    Term.boolTrue
    -- λ_:nat. λ_:list nat. boolFalse — succBranch is curried.
    (Term.lam (codomainType := Ty.arrow (Ty.list Ty.nat) Ty.bool)
      (Term.weaken Ty.nat
        (Term.lam (codomainType := Ty.bool)
          (Term.weaken (Ty.list Ty.nat) Term.boolFalse))))

/-- `Term.listElim` commutes with renaming on each of its three positions. -/
example {level scope target : Nat}
    {Γ : Ctx Mode.software level scope}
    {Δ : Ctx Mode.software level target}
    {ρ : Renaming scope target}
    (ρt : TermRenaming Γ Δ ρ)
    {elem result : Ty level scope}
    (scrutinee : Term Γ (Ty.list elem))
    (nilBranch : Term Γ result)
    (consBranch : Term Γ (Ty.arrow elem (Ty.arrow (Ty.list elem) result))) :
    Term.rename ρt (Term.listElim scrutinee nilBranch consBranch)
      = Term.listElim (Term.rename ρt scrutinee)
                      (Term.rename ρt nilBranch)
                      (Term.rename ρt consBranch) :=
  rfl

/-- ι-reduction on `[]`: `listElim [] n c ⟶ n`. -/
example {elem result : Ty 0 0}
    (n : Term EmptyCtx result)
    (c : Term EmptyCtx (Ty.arrow elem (Ty.arrow (Ty.list elem) result))) :
    Step (Term.listElim (elementType := elem) Term.listNil n c) n :=
  Step.iotaListElimNil n c

/-- ι-reduction on `cons`: `listElim (cons h t) n c ⟶ c h t`. -/
example {elem result : Ty 0 0}
    (h : Term EmptyCtx elem) (t : Term EmptyCtx (Ty.list elem))
    (n : Term EmptyCtx result)
    (c : Term EmptyCtx (Ty.arrow elem (Ty.arrow (Ty.list elem) result))) :
    Step (Term.listElim (Term.listCons h t) n c)
         (Term.app (Term.app c h) t) :=
  Step.iotaListElimCons h t n c

/-- A single-step list ι lifts to multi-step. -/
example {elem result : Ty 0 0}
    (n : Term EmptyCtx result)
    (c : Term EmptyCtx (Ty.arrow elem (Ty.arrow (Ty.list elem) result))) :
    StepStar (Term.listElim (elementType := elem) Term.listNil n c) n :=
  Step.toStar (Step.iotaListElimNil n c)

/-- Step.par lifts: list ι reaches multi-step via the parallel bridge. -/
example {elem result : Ty 0 0}
    (n : Term EmptyCtx result)
    (c : Term EmptyCtx (Ty.arrow elem (Ty.arrow (Ty.list elem) result))) :
    StepStar (Term.listElim (elementType := elem) Term.listNil n c) n :=
  Step.par.toStar (Step.toPar (Step.iotaListElimNil n c))

/-- ι-reduction on zero: `natElim 0 z f ⟶ z`. -/
example {result : Ty 0 0}
    (z : Term EmptyCtx result)
    (f : Term EmptyCtx (Ty.arrow Ty.nat result)) :
    Step (Term.natElim Term.natZero z f) z :=
  Step.iotaNatElimZero z f

/-- ι-reduction on succ: `natElim (succ n) z f ⟶ f n`. -/
example {result : Ty 0 0}
    (n : Term EmptyCtx Ty.nat)
    (z : Term EmptyCtx result)
    (f : Term EmptyCtx (Ty.arrow Ty.nat result)) :
    Step (Term.natElim (Term.natSucc n) z f) (Term.app f n) :=
  Step.iotaNatElimSucc n z f

/-- A single Step lifts to multi-step: `natElim 0 z f ⟶* z`. -/
example {result : Ty 0 0}
    (z : Term EmptyCtx result)
    (f : Term EmptyCtx (Ty.arrow Ty.nat result)) :
    StepStar (Term.natElim Term.natZero z f) z :=
  Step.toStar (Step.iotaNatElimZero z f)

/-- Step.par lifts: `natElim 0 z f ⟶ z` reaches multi-step via the
parallel-reduction bridge. -/
example {result : Ty 0 0}
    (z : Term EmptyCtx result)
    (f : Term EmptyCtx (Ty.arrow Ty.nat result)) :
    StepStar (Term.natElim Term.natZero z f) z :=
  Step.par.toStar (Step.toPar (Step.iotaNatElimZero z f))

/-- A single Step lifts to multi-step. -/
example (t e : Term EmptyCtx Ty.bool) :
    StepStar (Term.boolElim Term.boolTrue t e) t :=
  Step.toStar (Step.iotaBoolElimTrue t e)

/-- A single Step lifts to parallel reduction (which then lifts back). -/
example (t e : Term EmptyCtx Ty.bool) :
    StepStar (Term.boolElim Term.boolTrue t e) t :=
  Step.par.toStar (Step.toPar (Step.iotaBoolElimTrue t e))

/-- Identity-renaming of `unit` collapses to `unit` (modulo a cast on
the type-level identity of `Ty.rename_identity`).  Exercises
`Term.rename_id` at the empty context.  Stated with the expected
`Term.unit (context := EmptyCtx)` on both sides; the universe-polymorphic
implicit context is pinned by the expected type. -/
example :
    (Ty.rename_identity (level := 0) (scope := 0) Ty.unit) ▸
      Term.rename (TermRenaming.identity EmptyCtx)
        (Term.unit (context := EmptyCtx))
      = Term.unit (context := EmptyCtx) :=
  Term.rename_id (Term.unit (context := EmptyCtx))

end SmokeTest

end LeanFX.Syntax

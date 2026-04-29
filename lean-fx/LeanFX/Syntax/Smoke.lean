import LeanFX.Syntax.Identity

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

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

/-- Empty Software context at an arbitrary universe level. -/
private abbrev EmptyCtxAt (ambientLevel : Nat) : Ctx Mode.software ambientLevel 0 :=
  .nil Mode.software

/-- `() : unit` in the empty context. -/
example : Term EmptyCtx Ty.unit := Term.unit

/-- `true : bool` in the empty context. -/
example : Term EmptyCtx Ty.bool := Term.boolTrue

/-- `λx:unit. x : unit → unit` — the identity on `unit`. -/
example : Term EmptyCtx (Ty.arrow Ty.unit Ty.unit) :=
  Term.lam (Term.var ⟨0, Nat.zero_lt_succ _⟩)

/-- The unit identity term exists uniformly at every universe level. -/
def unitIdentityAtLevel (ambientLevel : Nat) :
    Term (EmptyCtxAt ambientLevel) (Ty.arrow Ty.unit Ty.unit) :=
  Term.lam (Term.var ⟨0, Nat.zero_lt_succ _⟩)

/-- A universe-polymorphic compose type, specialized to unit arrows as
a compact smoke test for repeated arrow formation at arbitrary level. -/
def unitComposeTypeAtLevel (ambientLevel : Nat) : Ty ambientLevel 0 :=
  Ty.arrow (Ty.arrow Ty.unit Ty.unit)
    (Ty.arrow (Ty.arrow Ty.unit Ty.unit) (Ty.arrow Ty.unit Ty.unit))

/-- Reflexivity over a reflexivity raw endpoint exercises the identity
ladder one step above ordinary value equality. -/
def reflOfRefl :
    Term EmptyCtx
      (Ty.id (Ty.id Ty.bool RawTerm.boolTrue RawTerm.boolTrue)
        (RawTerm.refl RawTerm.boolTrue)
        (RawTerm.refl RawTerm.boolTrue)) :=
  Term.refl (carrier := Ty.id Ty.bool RawTerm.boolTrue RawTerm.boolTrue)
    (RawTerm.refl RawTerm.boolTrue)

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
Demonstrates the cumulative-bound encoding: the proof `1 ≤ 1` is
supplied at the use site, and larger ambient universe levels can use
the same constructor. -/
example : Ty 1 0 := Ty.universe 0 (Nat.le_refl 1)

/-- Cumulativity: `Type<0>` is also available at higher levels. -/
example : Ty 2 0 := Ty.universe 0 (Nat.succ_le_succ (Nat.zero_le 1))

/-- `Type<3> : Ty 4 0` — universe at an arbitrary level. -/
example : Ty 4 0 := Ty.universe 3 (Nat.le_refl 4)

/-- The universe is preserved by rawRenaming: `(Type<u>).rename ρ = Type<u>`. -/
example {scope target : Nat} (ρ : Renaming scope target) :
    (Ty.universe (level := 1) (scope := scope) 0 (Nat.le_refl 1)).rename ρ
      = Ty.universe (level := 1) (scope := target) 0 (Nat.le_refl 1) :=
  rfl

/-- The universe is preserved by substitution: `(Type<u>).subst σ = Type<u>`. -/
example {scope target : Nat} (σ : Subst 1 scope target) :
    (Ty.universe (level := 1) (scope := scope) 0 (Nat.le_refl 1)).subst σ
      = Ty.universe (level := 1) (scope := target) 0 (Nat.le_refl 1) :=
  rfl

/-- General level lifting sends a lower-level type into a higher ambient level. -/
example : Ty 3 0 :=
  Ty.liftLevel (lowerLevel := 1) (upperLevel := 3) (scope := 0)
    (Nat.succ_le_succ (Nat.zero_le 2))
    (Ty.universe 0 (Nat.le_refl 1))

/-- Universe-polymorphic Π formation lifts domain and codomain into `max`. -/
example : Ty 2 0 :=
  Ty.piTyLevel
    (domainLevel := 1)
    (codomainLevel := 2)
    (scope := 0)
    (Ty.universe 0 (Nat.le_refl 1))
    (Ty.universe 1 (Nat.le_refl 2))

/-- Universe-polymorphic Σ formation follows the same level discipline as Π. -/
example : Ty 2 0 :=
  Ty.sigmaTyLevel
    (firstLevel := 1)
    (secondLevel := 2)
    (scope := 0)
    (Ty.universe 0 (Nat.le_refl 1))
    (Ty.universe 1 (Nat.le_refl 2))

/-- `Ty.nat` is level-polymorphic — exists at any universe level. -/
example : Ty 0 0 := Ty.nat
example : Ty 5 7 := Ty.nat

/-- The natural-number type is preserved by rawRenaming. -/
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

/-- `Term.natZero` is preserved by rawRenaming. -/
example {level scope target : Nat}
    {Γ : Ctx Mode.software level scope}
    {Δ : Ctx Mode.software level target}
    {ρ : Renaming scope target}
    (ρt : TermRenaming Γ Δ ρ) :
    Term.rename ρt (Term.natZero (context := Γ))
      = Term.natZero (context := Δ) :=
  rfl

/-- `Term.natSucc` commutes with rawRenaming. -/
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

/-- `Term.natElim` commutes with rawRenaming on each of its three positions. -/
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

/-! ### Length-indexed vectors. -/

/-- `Ty.vec` is indexed by a closed natural length. -/
example : Ty 0 0 := Ty.vec Ty.nat 0
example : Ty 0 0 := Ty.vec Ty.bool 4

/-- Vector rename only affects the element type; the length is stable. -/
example {level scope target : Nat}
    (rawRenaming : Renaming scope target)
    (elementType : Ty level scope)
    (length : Nat) :
    (Ty.vec elementType length).rename rawRenaming =
      Ty.vec (elementType.rename rawRenaming) length :=
  rfl

/-- Vector substitution only affects the element type; the length is stable. -/
example {level scope target : Nat}
    (substitution : Subst level scope target)
    (elementType : Ty level scope)
    (length : Nat) :
    (Ty.vec elementType length).subst substitution =
      Ty.vec (elementType.subst substitution) length :=
  rfl

/-- The list type commutes with rawRenaming on its element type. -/
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

/-- `Term.listNil` is preserved by rawRenaming. -/
example {level scope target : Nat}
    {Γ : Ctx Mode.software level scope}
    {Δ : Ctx Mode.software level target}
    {ρ : Renaming scope target}
    (ρt : TermRenaming Γ Δ ρ)
    {elem : Ty level scope} :
    Term.rename ρt (Term.listNil (context := Γ) (elementType := elem))
      = Term.listNil (context := Δ) (elementType := elem.rename ρ) :=
  rfl

/-- `Term.listCons` commutes with rawRenaming on head and tail. -/
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

/-- `Term.listElim` commutes with rawRenaming on each of its three positions. -/
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

/-- Identity-rawRenaming of `unit` collapses to `unit` (modulo a cast on
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

/-! ### Term.refl — identity-type introduction. -/

/-- `Term.refl true_raw : Id Bool true_raw true_raw` — the simplest
identity witness, with carrier `Ty.bool` and both endpoints the closed
raw boolean `true`. -/
example :
    Term EmptyCtx (Ty.id Ty.bool RawTerm.boolTrue RawTerm.boolTrue) :=
  Term.refl RawTerm.boolTrue

/-- `Term.refl 0_raw : Id Nat 0 0`. -/
example :
    Term EmptyCtx (Ty.id Ty.nat RawTerm.natZero RawTerm.natZero) :=
  Term.refl RawTerm.natZero

/-- `Term.refl unit_raw : Id Unit () ()`. -/
example :
    Term EmptyCtx (Ty.id Ty.unit RawTerm.unit RawTerm.unit) :=
  Term.refl RawTerm.unit

/-- Open endpoint identity under a binder: in `x : Unit`, `refl x`
inhabits `Id Unit x x`. -/
example :
    Term (EmptyCtx.cons Ty.unit)
      (Ty.id Ty.unit
        (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩)
        (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩)) :=
  Term.refl (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩)

/-- Iterated identity at the term level — `refl(refl(true)) :
Id (Id Bool true true) refl(true) refl(true)`.  Carrier is itself a
`Ty.id`; endpoints are `RawTerm.refl RawTerm.boolTrue`.  This
exercises `Ty.id` carrying a `Ty.id` and `Term.refl` carrying a
`RawTerm.refl`. -/
example :
    Term EmptyCtx
      (Ty.id (Ty.id Ty.bool RawTerm.boolTrue RawTerm.boolTrue)
             (RawTerm.refl RawTerm.boolTrue)
             (RawTerm.refl RawTerm.boolTrue)) :=
  Term.refl (RawTerm.refl RawTerm.boolTrue)

/-- `Term.refl` is preserved by rawRenaming: `rename ρt (refl rt) = refl rt`
modulo the carrier rawRenaming.  At scope 0 the rawRenaming has no effect on
the carrier (closed type), so the equation reduces to `rfl`. -/
example {target : Nat}
    {Δ : Ctx Mode.software 0 target}
    {ρ : Renaming 0 target}
    (ρt : TermRenaming EmptyCtx Δ ρ) :
    Term.rename ρt
      (Term.refl (context := EmptyCtx)
                 (carrier := Ty.bool) RawTerm.boolTrue)
      = Term.refl (context := Δ) (carrier := Ty.bool) RawTerm.boolTrue :=
  rfl

/-- `Term.refl` is preserved by substitution. -/
example {target : Nat}
    {Δ : Ctx Mode.software 0 target}
    {σ : Subst 0 0 target}
    (σt : TermSubst EmptyCtx Δ σ) :
    Term.subst σt
      (Term.refl (context := EmptyCtx)
                 (carrier := Ty.bool) RawTerm.boolTrue)
      = Term.refl (context := Δ) (carrier := Ty.bool) RawTerm.boolTrue :=
  rfl

/-! ### Term.toRaw — intrinsic-to-raw bridge.

`Term.toRaw` erases the typing information from an intrinsic Term to
produce the corresponding RawTerm.  Each test pins a specific Term
constructor and verifies the raw counterpart. -/

/-- `Term.unit.toRaw = RawTerm.unit`. -/
example : (Term.unit (context := EmptyCtx)).toRaw = RawTerm.unit := rfl

/-- `Term.boolTrue.toRaw = RawTerm.boolTrue`. -/
example :
    (Term.boolTrue (context := EmptyCtx)).toRaw = RawTerm.boolTrue := rfl

/-- `Term.boolFalse.toRaw = RawTerm.boolFalse`. -/
example :
    (Term.boolFalse (context := EmptyCtx)).toRaw = RawTerm.boolFalse := rfl

/-- `Term.natZero.toRaw = RawTerm.natZero`. -/
example :
    (Term.natZero (context := EmptyCtx)).toRaw = RawTerm.natZero := rfl

/-- `(succ 0).toRaw = succ_raw 0_raw`. -/
example :
    (Term.natSucc (Term.natZero (context := EmptyCtx))).toRaw
      = RawTerm.natSucc RawTerm.natZero := rfl

/-- The `lam`/`lamPi` collapse: both produce `RawTerm.lam`. -/
example :
    (Term.lam (codomainType := Ty.unit)
        (Term.var (context := EmptyCtx.cons Ty.unit)
                  ⟨0, Nat.zero_lt_succ _⟩)).toRaw
      = RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩) := rfl

/-- `(true, 0).toRaw = pair_raw boolTrue_raw natZero_raw`. -/
example :
    (Term.pair (firstType := Ty.bool) (secondType := Ty.nat.weaken)
       (Term.boolTrue (context := EmptyCtx))
       (Term.natZero (context := EmptyCtx))).toRaw
      = RawTerm.pair RawTerm.boolTrue RawTerm.natZero := rfl

/-- `(refl true).toRaw = refl_raw true_raw` — the bridge erases the
identity-type annotation but preserves the reflexivity content,
preserving the raw endpoint in its current scope. -/
example :
    (Term.refl (context := EmptyCtx) (carrier := Ty.bool)
        RawTerm.boolTrue).toRaw
      = RawTerm.refl RawTerm.boolTrue := rfl

/-- Open refl endpoints survive `toRaw` without closed-scope embedding. -/
example :
    (Term.refl (context := EmptyCtx.cons Ty.unit) (carrier := Ty.unit)
        (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩)).toRaw
      = RawTerm.refl (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩) := rfl

/-- `weakenToScope 0 rt = rt` — the base case is the identity. -/
example (rt : RawTerm 0) : RawTerm.weakenToScope 0 rt = rt := rfl

/-- `weakenToScope 2 boolTrue = (boolTrue.weaken).weaken` —
demonstrates iteration. -/
example :
    RawTerm.weakenToScope 2 RawTerm.boolTrue
      = (RawTerm.boolTrue (scope := 0)).weaken.weaken := rfl

/-! ### Term.refl in Step / StepStar / Step.par / Conv.

`Term.refl` is a value — no β/η reductions apply to it.  The ι-rule
for J (the Id eliminator) lands in v2.2m and introduces
`Step.iotaIdJRefl`.  The existing reflexivity constructors of every
reduction relation accept `Term.refl` directly. -/

/-- `Term.refl` is multi-step-related to itself by zero steps. -/
example :
    StepStar
      (Term.refl (context := EmptyCtx)
                 (carrier := Ty.bool) RawTerm.boolTrue)
      (Term.refl (context := EmptyCtx)
                 (carrier := Ty.bool) RawTerm.boolTrue) :=
  StepStar.refl _

/-- `Term.refl` parallel-reduces to itself in zero steps. -/
example :
    Step.par
      (Term.refl (context := EmptyCtx)
                 (carrier := Ty.bool) RawTerm.boolTrue)
      (Term.refl (context := EmptyCtx)
                 (carrier := Ty.bool) RawTerm.boolTrue) :=
  Step.par.refl _

/-- `Term.refl` is convertible with itself. -/
example :
    Conv
      (Term.refl (context := EmptyCtx)
                 (carrier := Ty.bool) RawTerm.boolTrue)
      (Term.refl (context := EmptyCtx)
                 (carrier := Ty.bool) RawTerm.boolTrue) :=
  Conv.refl _

/-! ### Term.idJ — J eliminator (closed-endpoint, non-dependent motive). -/

/-- `idJ baseCase witness : resultType` — given a base case and a
witness of an identity, produce a result of the same motive type.
Here: `idJ true (refl true) : Bool`. -/
example :
    Term EmptyCtx Ty.bool :=
  Term.idJ (carrier := Ty.bool) (resultType := Ty.bool)
    Term.boolTrue
    (Term.refl (context := EmptyCtx) (carrier := Ty.bool)
               RawTerm.boolTrue)

/-- `Term.idJ` is preserved by rawRenaming. -/
example {target : Nat}
    {Δ : Ctx Mode.software 0 target}
    {ρ : Renaming 0 target}
    (ρt : TermRenaming EmptyCtx Δ ρ) :
    Term.rename ρt
      (Term.idJ (carrier := Ty.bool) (resultType := Ty.bool)
        Term.boolTrue
        (Term.refl (context := EmptyCtx) (carrier := Ty.bool)
                   RawTerm.boolTrue))
      = Term.idJ (context := Δ) (carrier := Ty.bool)
                 (resultType := Ty.bool)
        Term.boolTrue
        (Term.refl (context := Δ) (carrier := Ty.bool)
                   RawTerm.boolTrue) :=
  rfl

/-- `Term.idJ` is preserved by substitution. -/
example {target : Nat}
    {Δ : Ctx Mode.software 0 target}
    {σ : Subst 0 0 target}
    (σt : TermSubst EmptyCtx Δ σ) :
    Term.subst σt
      (Term.idJ (carrier := Ty.bool) (resultType := Ty.bool)
        Term.boolTrue
        (Term.refl (context := EmptyCtx) (carrier := Ty.bool)
                   RawTerm.boolTrue))
      = Term.idJ (context := Δ) (carrier := Ty.bool)
                 (resultType := Ty.bool)
        Term.boolTrue
        (Term.refl (context := Δ) (carrier := Ty.bool)
                   RawTerm.boolTrue) :=
  rfl

/-- `Term.idJ.toRaw = RawTerm.idJ baseCase.toRaw witness.toRaw`. -/
example :
    (Term.idJ (carrier := Ty.bool) (resultType := Ty.bool)
       (Term.boolTrue (context := EmptyCtx))
       (Term.refl (context := EmptyCtx) (carrier := Ty.bool)
                  RawTerm.boolTrue)).toRaw
      = RawTerm.idJ RawTerm.boolTrue (RawTerm.refl RawTerm.boolTrue) := rfl

/-- **ι-reduction for J at refl**: `J base (refl rt) ⟶ base`. -/
example :
    Step
      (Term.idJ (context := EmptyCtx) (carrier := Ty.bool)
                (resultType := Ty.bool) Term.boolTrue
        (Term.refl (carrier := Ty.bool) RawTerm.boolTrue))
      Term.boolTrue :=
  Step.iotaIdJRefl Term.boolTrue

/-- The ι-rule lifts to multi-step. -/
example :
    StepStar
      (Term.idJ (context := EmptyCtx) (carrier := Ty.bool)
                (resultType := Ty.bool) Term.boolTrue
        (Term.refl (carrier := Ty.bool) RawTerm.boolTrue))
      Term.boolTrue :=
  Step.toStar (Step.iotaIdJRefl Term.boolTrue)

/-- The ι-rule lifts via the parallel-reduction bridge. -/
example :
    StepStar
      (Term.idJ (context := EmptyCtx) (carrier := Ty.bool)
                (resultType := Ty.bool) Term.boolTrue
        (Term.refl (carrier := Ty.bool) RawTerm.boolTrue))
      Term.boolTrue :=
  Step.par.toStar (Step.toPar (Step.iotaIdJRefl Term.boolTrue))

/-- ι at refl is a definitional equivalence. -/
example :
    Conv
      (Term.idJ (context := EmptyCtx) (carrier := Ty.bool)
                (resultType := Ty.bool) Term.boolTrue
        (Term.refl (carrier := Ty.bool) RawTerm.boolTrue))
      Term.boolTrue :=
  (Step.iotaIdJRefl Term.boolTrue).toConv

end SmokeTest

end LeanFX.Syntax

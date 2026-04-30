import LeanFX.Mode.Defn

/-! # FX intrinsic syntax.

Well-scoped intrinsic encoding (Allais–McBride style): `Ty` is indexed
by scope size (`Nat`), `Ctx` carries the actual binding types and is
indexed by mode + scope, and `Term` is indexed by context + type so
that the constructor signatures *are* the typing rules.  This sidesteps
Lean 4's strict-positivity rejection of the textbook Ty-mutually-with-
Ctx formulation that Agda accepts.

Contents, in dependency order:

  * `Ty` and the rawRenaming / substitution algebra (`Ty.rename`,
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
  /-- J eliminator at the raw level — `idJ baseCase witness`.  Mirror
  of the intrinsic `Term.idJ` (v2.2m).  The closed-endpoint regime
  doesn't need separate type-level annotations on the raw side; the
  bridge `Term.toRaw` erases the carrier/leftEnd/rightEnd/resultType
  annotations and ships just the data. -/
  | idJ : {scope : Nat} →
          (baseCase : RawTerm scope) →
          (witness : RawTerm scope) →
          RawTerm scope
  deriving DecidableEq

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

end LeanFX.Syntax

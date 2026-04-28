import LeanFX.Mode.Defn

/-! # KernelMTT — extrinsic well-scoped MLTT kernel for FX.

The second kernel.  Coexists with `LeanFX.Syntax.Term` (KernelV1, the
intrinsic kernel) until KernelMTT reaches feature parity, at which
point the v1 kernel is deprecated per the FX paper's R1-R5 plan.

## Why a second kernel

The intrinsic kernel `Term : Ctx → Ty → Type` cannot reference Term
values from inside Ty constructors — Lean 4's mutual elaborator
forbids cross-mutual references in *index family signatures* (see
`feedback_lean_mutual_index_rule.md`).  The FX paper §6 requires
identity types `Id A a b : Type`, dependent J, and parametricity
modalities — all of which need Ty constructors that mention Term.

KernelMTT works around this by adopting the **well-scoped extrinsic**
discipline: `Term : Nat → Type` (raw syntax, no Ty index) mutual with
`Ty : Nat → Nat → Type`.  Type-correctness is enforced by a separate
`HasType : Term scope → Ty level scope → Prop` predicate (in
`Typing.lean`).  Subject reduction becomes an explicit theorem chain
rather than an implicit kernel invariant.

This is the standard pattern in Coq/Agda formalizations of MLTT
(Allais–McBride well-scoped + typing relation).  Less compile-time
discipline than intrinsic typing, but admits the full MTT spine.

## Architectural commitments

  * Mutual `Ty` and `Term` references each other only via constructor
    arguments.  Neither's index family signature mentions the other.
    This is the maximal mutuality Lean 4 admits (per the
    `feedback_lean_mutual_index_rule.md` investigation).

  * `Ty.tyId` carries two raw `Term` values as the equated endpoints.
    Type-correctness — `HasType term carrier` for both endpoints — is
    enforced by `HasType` rules, not by Ty's structure.

  * `Ctx` lives outside the mutual block.  In KernelMTT, `Ctx` is a
    list of types built post-block (analogous to KernelV1's `Ctx`,
    but without the recursive Ctx-cons-Ty problem).

  * Function-typed Subst per the existing `feedback_lean_function_typed_subst`
    discipline.  Avoids funext.

## Migration status (v2.0 series)

  * v2.0a (this file) — mutual block, minimal constructor set,
    smoke tests for `Ty.tyId` + `Term.reflEq`.
  * v2.0b — Substitution.lean (Renaming, Subst, Ty.subst, Term.subst).
  * v2.0c — Reduction.lean (Step, StepStar, Step.par, Conv).
  * v2.0d — Typing.lean (HasType inductive predicate).
  * v2.0e — SubjectReduction.lean (explicit preservation theorems).
  * v2.0f — IdRules.lean (Term.idJ + ι-rule + congruences).

## Constructor parity with KernelV1

This file ports a minimal core (unit, bool, nat, arrow, var, lam,
app, refl, plus the new `tyId` constructor).  Successor slices port
piTy / sigmaTy / universe / list / option / either / boolElim /
natElim / natRec / pair / fst / snd / weaken in v2.0b–v2.0c.  The
ported constructor signatures are simplified (no Ctx/Ty index on
Term) — the typing discipline moves to `HasType`. -/

namespace LeanFX.KernelMTT

open LeanFX.Mode (Mode)

/-! ## The mutual block.

`Ty` indexed by `(level, scope)` — universe level and de Bruijn
scope.  `Term` indexed by `scope` only (raw syntax).  The two
inductives mention each other ONLY via constructor argument types:

  * `Ty.arrow domain codomain` references `Ty` (the same family —
    OK, allowed).
  * `Ty.tyId carrier leftEnd rightEnd` references `Term` (sibling —
    must be in argument position, never in index).
  * `Term.lamFn domainType body` references `Ty` (sibling, in arg
    position — OK).

Lean 4 v4.29.1 admits exactly this shape.  Index families must be
self-contained. -/

mutual

/-- Well-scoped types at universe level `level` with `scope` free
type variables.  Mirrors `Ty` from KernelV1 but loses the intrinsic
typing of Term arguments — that moves to `HasType`. -/
inductive Ty : Nat → Nat → Type
  /-- The unit type. -/
  | unitTy : {level scope : Nat} → Ty level scope
  /-- Booleans. -/
  | boolTy : {level scope : Nat} → Ty level scope
  /-- Naturals. -/
  | natTy : {level scope : Nat} → Ty level scope
  /-- Non-dependent function type `domain → codomain`. -/
  | arrowTy : {level scope : Nat} →
              (domain : Ty level scope) →
              (codomain : Ty level scope) →
              Ty level scope
  /-- Type variable, indexed into the surrounding scope. -/
  | tyVar : {level scope : Nat} → (position : Fin scope) → Ty level scope
  /-- Universe — `Type<u>` lives at level `u + 1`.  Propositional
  equation pattern per `feedback_lean_universe_constructor_block`:
  level stays polymorphic, the `levelEq` witness pins the relation
  at use site. -/
  | universeTy : {level scope : Nat} →
                 (universeLevel : Nat) →
                 (levelEq : level = universeLevel + 1) →
                 Ty level scope
  /-- Identity type — the load-bearing constructor.  Carries the
  shared FX type `carrier` plus two raw `Term` values witnessing the
  endpoints.  Type-correctness (`HasType leftEnd carrier` and
  `HasType rightEnd carrier`) is enforced by `HasType.tyIdTyped`,
  NOT by Ty's structure. -/
  | tyId : {level scope : Nat} →
           (carrier : Ty level scope) →
           (leftEnd : Term scope) →
           (rightEnd : Term scope) →
           Ty level scope

/-- Well-scoped raw terms in `scope` free term variables.  NOT
indexed by `Ty` — type correctness is captured by the separate
`HasType` predicate (in v2.0d).

Constructors are deliberately Church-style: λ-abstractions annotate
their domain type so `HasType` can be reconstructed without
backward-search inference.  This is the same trade-off Lean's own
`Expr` makes for closures. -/
inductive Term : Nat → Type
  /-- Variable reference (de Bruijn, indexed into scope). -/
  | varRef : {scope : Nat} → (position : Fin scope) → Term scope
  /-- Unit value `()`. -/
  | unitVal : {scope : Nat} → Term scope
  /-- Boolean `true`. -/
  | boolTrue : {scope : Nat} → Term scope
  /-- Boolean `false`. -/
  | boolFalse : {scope : Nat} → Term scope
  /-- Natural-number `0`. -/
  | natZero : {scope : Nat} → Term scope
  /-- Natural-number `succ predecessor`. -/
  | natSucc : {scope : Nat} → (predecessor : Term scope) → Term scope
  /-- Non-dependent λ-abstraction.  Annotates the domain type
  (Church-style); body lives at `scope + 1`. -/
  | lamFn : {level scope : Nat} →
            (domainType : Ty level scope) →
            (body : Term (scope + 1)) →
            Term scope
  /-- Application.  Function and argument shapes carry no annotation
  here; their typing is reconstructed by `HasType` matching against
  the function's `arrowTy` head. -/
  | appFn : {scope : Nat} →
            (function : Term scope) →
            (argument : Term scope) →
            Term scope
  /-- Reflexivity witness — proof of `Id carrier term term`.  The
  type `tyId carrier term term` is reconstructed by `HasType` from
  the term's own structure plus the carrier inferred at use site. -/
  | reflEq : {scope : Nat} → (term : Term scope) → Term scope

end

/-! ## Smoke tests — minimal exercise of the mutual block.

These tests confirm:

  * `Ty` and `Term` mutually elaborate without `Unknown identifier`
    errors (the cross-mutual barrier from
    `feedback_lean_mutual_index_rule.md` is dodged because Term
    appears only in argument positions of Ty).
  * `Ty.tyId carrier left right` typechecks at `Ty level scope`
    despite carrying raw Term endpoints.
  * `Term.reflEq term` typechecks at `Term scope`.
  * The propositional-equation pattern on `universeTy` works
    identically to KernelV1's intrinsic version.
  * Zero axioms across the entire mutual block.

Smoke tests live in their own namespace so they don't pollute the
public API. -/

namespace SmokeTest

/-- `unit` type at level 0, scope 0. -/
def unitAtZero : Ty 0 0 := Ty.unitTy

/-- `bool` type at level 0, scope 0. -/
def boolAtZero : Ty 0 0 := Ty.boolTy

/-- `bool → bool` arrow type. -/
def boolArrowBool : Ty 0 0 := Ty.arrowTy Ty.boolTy Ty.boolTy

/-- `Type<0>` at level 1.  Propositional-equation pattern: the
`levelEq` witness `rfl : 1 = 0 + 1` constrains the otherwise-
polymorphic level. -/
def universeZero : Ty 1 0 := Ty.universeTy 0 rfl

/-- `Type<3>` at level 4. -/
def universeThree : Ty 4 0 := Ty.universeTy 3 rfl

/-- `()` term in scope 0. -/
def unitTermAtZero : Term 0 := Term.unitVal

/-- `true` term in scope 0. -/
def trueTermAtZero : Term 0 := Term.boolTrue

/-- `succ (succ zero) = 2` term in scope 0. -/
def twoTerm : Term 0 := Term.natSucc (Term.natSucc Term.natZero)

/-- The load-bearing smoke test: `Id Bool true true` is a `Ty`,
even though it carries two raw `Term` endpoints.  This is what
KernelV1 cannot express. -/
def identityBoolTrueTrue : Ty 0 0 :=
  Ty.tyId Ty.boolTy Term.boolTrue Term.boolTrue

/-- `refl(true)` is a raw `Term`.  Its type — `Id Bool true true` —
is established by `HasType.reflEqTyped` in v2.0d. -/
def reflTrueTerm : Term 0 := Term.reflEq Term.boolTrue

/-- Iterated identity: `Id (Id Bool true true) refl(true) refl(true)`
— witnesses that the identity-type former composes.  Important
because path induction in MLTT routinely reasons about identities-
of-identities. -/
def doubleIdentityTy : Ty 0 0 :=
  Ty.tyId
    (Ty.tyId Ty.boolTy Term.boolTrue Term.boolTrue)
    (Term.reflEq Term.boolTrue)
    (Term.reflEq Term.boolTrue)

/-- `refl(refl(true))` — the term inhabiting `doubleIdentityTy`. -/
def doubleReflTerm : Term 0 := Term.reflEq (Term.reflEq Term.boolTrue)

/-- `λ x : bool. x` — non-dep identity on bool, scope-0 closed.
The `Ty.boolTy` annotation pins the universe level (otherwise
`Term.lamFn`'s implicit `level` is unconstrained).  Same idiom
appears in KernelV1 smoke tests. -/
def boolIdentityLambda : Term 0 :=
  Term.lamFn (level := 0) Ty.boolTy
             (Term.varRef ⟨0, Nat.zero_lt_succ _⟩)

/-- Application: `(λ x : bool. x) true`.  Demonstrates Term-arrow
composition with raw Term arguments. -/
def boolIdentityAppliedToTrue : Term 0 :=
  Term.appFn boolIdentityLambda Term.boolTrue

/-- `Id (bool → bool) (λx. x) (λx. x)` — identity of two non-dep
λ-abstractions.  Both endpoints are λ-terms, exercising the full
Term-in-Ty machinery. -/
def lambdaIdentityType : Ty 0 0 :=
  Ty.tyId
    (Ty.arrowTy Ty.boolTy Ty.boolTy)
    boolIdentityLambda
    boolIdentityLambda

end SmokeTest

end LeanFX.KernelMTT

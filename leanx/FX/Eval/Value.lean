import FX.Kernel.Term
import FX.Kernel.Level

/-!
# Runtime values

Per `fx_design.md` §22 (sketch mode bytecode VM — the design
intent) and §31 (kernel calculus — what the evaluator reduces).

A `Value` is the result of evaluating a closed `Term` under an
environment.  Unlike `Term`, which is a syntactic representation
with de Bruijn indices, `Value` is an in-memory form that
explicitly captures closures (lambda + environment), constructor
applications (tagged + runtime args), and neutral terms (stuck
applications / eliminations that can't reduce without more
information).

## Phase 2.2 (task C1) scope

Covered:

  * `closure` — lambda-term + captured environment.  Applied via beta.
  * `ctor` — fully-applied inductive constructor, e.g.
    `Nat.succ (Nat.zero)` as `ctor "Nat" 1 [] [ctor "Nat" 0 [] []]`.
  * `indType` — applied inductive type.
  * `universe` — a type-universe value (`type<u>` at runtime).
  * `piType` / `sigmaType` — Pi/Sigma types carrying a closure
    over the codomain/cofield binder.
  * `neutral` / `neutralRec` — stuck forms for open terms and
    eliminators whose scrutinee is not yet canonical.
  * `idType` / `quotType` — type-former values for Id / Quot.

Covered as of A3/A4: Id refl values (`reflVal`) + stuck J form
(`neutralIdJ`), and quotient-class values (`quotMkVal`) + stuck
Quot.lift form (`neutralQuotLift`).  Each pair is the
introduction and the stuck-eliminator fallback needed when the
scrutinee hasn't reduced to its canonical form.

Deferred: codata (A2), effect actions (C4), numeric primitives
(D2).

## Why `List Value` works without a mutual block

`closure` captures an environment (`List Value`).  Lean 4.29
accepts `List Value` as a nested positive occurrence inside the
`Value` inductive — same pattern as `Term.ind`'s `args : List
Term`.  No mutual block needed.
-/

namespace FX.Eval

open FX.Kernel

/-- A runtime value produced by the evaluator. -/
inductive Value : Type where
  /-- A lambda closure: body term + captured environment (de Bruijn
      index 0 of the body references head of `captured`).  The
      param type is kept for pretty-printing. -/
  | closure
      (paramType : Term)
      (body : Term)
      (captured : List Value) : Value

  /-- A Pi-type value: `Pi(x :_g paramType). codomain` with
      `codomain`'s free vars bound by `captured`. -/
  | piType
      (paramType : Term)
      (codomain : Term)
      (captured : List Value) : Value

  /-- A Sigma-type value, analogous to `piType`. -/
  | sigmaType
      (paramType : Term)
      (codomain : Term)
      (captured : List Value) : Value

  /-- Fully-applied inductive constructor.  `typeArgs` are the
      type parameters at the application site; `args` are the
      constructor's value arguments. -/
  | ctor
      (typeName : String)
      (ctorIndex : Nat)
      (typeArgs : List Value)
      (args : List Value) : Value

  /-- Applied inductive type: e.g. `Nat` is `indType "Nat" []`. -/
  | indType
      (typeName : String)
      (args : List Value) : Value

  /-- Universe value `type<u>`. -/
  | universe (level : Level) : Value

  /-- Universe-polymorphic quantifier value `∀ k. body`.
      Mirrors `piType` in shape (body term + captured local
      env) but has no domain — levels are erased at runtime
      per §1.5 compile-time erasure, so the value representation
      is type-level metadata only.  Per A10 / §31.4 U-poly. -/
  | forallLevelType
      (body : Term)
      (captured : List Value) : Value

  /-- Identity type value `Id T a b`. -/
  | idType
      (baseType : Value)
      (left : Value)
      (right : Value) : Value

  /-- Identity-type introduction value `refl v`.  The witness `v`
      is the value of the reflected term; the type is recovered
      from `v`'s type at the typing layer.  Per A3 / H.6. -/
  | reflVal (witness : Value) : Value

  /-- A J-eliminator whose equality proof has not reduced to a
      canonical `reflVal` — e.g., the proof is itself a stuck
      neutral.  Preserves the shape for pretty-printing.  Iota
      reduction at the Value layer is handled by `idJValue` in
      `FX/Eval/Interp.lean`; when it sees a `reflVal` it
      applies the base directly, otherwise it returns a
      `neutralIdJ`. -/
  | neutralIdJ
      (motive : Value)
      (base   : Value)
      (eq     : Value) : Value

  /-- Quotient type value `Quot T R`. -/
  | quotType
      (carrier : Value)
      (relation : Value) : Value

  /-- Quotient-class value `quotMk R w` — the representative
      witness paired with the equivalence relation, mirroring
      Lean's `Quot.mk r a`.  Per A4 / H.7. -/
  | quotMkVal
      (relation : Value)
      (witness  : Value) : Value

  /-- A Quot.lift whose target has not reduced to a canonical
      `quotMkVal` — e.g., the target is itself a stuck neutral.
      Preserves the shape for pretty-printing.  Iota at the
      Value layer is handled by `quotLiftValue` in
      `FX/Eval/Interp.lean`; when it sees a `quotMkVal` it
      applies the lifted function directly, otherwise it returns
      a `neutralQuotLift`. -/
  | neutralQuotLift
      (lifted   : Value)
      (respects : Value)
      (target   : Value) : Value

  /-- A neutral term — a stuck head (free variable) with an
      application spine.  `head` is the de Bruijn index of the
      free var.  Spine is outermost-first. -/
  | neutral
      (head : Nat)
      (spine : List Value) : Value

  /-- Eliminator against a stuck scrutinee.  Preserves the
      eliminator shape for pretty-printing. -/
  | neutralRec
      (typeName : String)
      (motive : Value)
      (methods : List Value)
      (target : Value) : Value
  deriving Repr, Inhabited

namespace Value

/-- Is this value canonical (fully reduced, no stuck heads)? -/
def isCanonical : Value → Bool
  | .closure _ _ _      => true
  | .piType _ _ _       => true
  | .sigmaType _ _ _    => true
  | .ctor _ _ _ _       => true
  | .indType _ _        => true
  | .universe _         => true
  | .forallLevelType _ _ => true
  | .idType _ _ _       => true
  | .reflVal _          => true
  | .neutralIdJ _ _ _   => false
  | .quotType _ _       => true
  | .quotMkVal _ _      => true
  | .neutralQuotLift _ _ _ => false
  | .neutral _ _        => false
  | .neutralRec _ _ _ _ => false

/-- True when a value is a constructor of `typeName`.  Used by
    the iota reducer at indRec time. -/
def isCtorOf (name : String) : Value → Bool
  | .ctor ctorTypeName _ _ _ => ctorTypeName == name
  | _                        => false

/-- A sentinel "not yet evaluated" value.  Matches `Inhabited`
    default. -/
def placeholder : Value := .universe .zero

end Value

end FX.Eval

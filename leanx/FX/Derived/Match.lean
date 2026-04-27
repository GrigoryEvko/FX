import FX.Kernel.Inductive
import FX.Kernel.Term
import FX.Kernel.Reduction

/-!
# Derived spec — Pattern compilation (§4.3, D5)

Pattern matching desugars to iterated `Term.indRec` — the
kernel's inductive-family eliminator (Appendix H.4
Ind-elim).  This module documents the translation and pins
the expected shape via `example` blocks.  UNTRUSTED (L3 per
`SPEC.md` §5) — the load-bearing work is in
`FX/Elab/Elaborate.lean` (`elabMatch`) and
`FX/Elab/MatchHelpers.lean` (resolveArmCtor?, scopeAndDepth
ForCtor, wrapCtorMethod).

## Surface syntax (§4.3)

```
match scrutinee;
  Red             => value_red;
  Green           => value_green;
  Blue            => value_blue;
end match
```

## Translation to kernel (§31.7 pattern)

For a match on `scrutinee : Term.ind specName []`:

```
Term.indRec specName
  motive       -- λ (_ :_ghost spec). returnType
  methods      -- [method_0, method_1, ...] in CTOR-DECLARATION order
  scrutinee
```

Key invariants enforced by `elabMatch`:

  1. **Spec resolved via arm patterns.**  The match compiler
     walks the arm patterns to find a ctor-reference it
     recognizes — that ctor's spec determines the scrutinee's
     inductive type.  If no arm resolves, emit E010.

  2. **Exactly one arm per ctor.**  Surface arms must
     enumerate every ctor of the scrutinee's spec (no
     wildcard catch-all in Phase 2).  Arms may appear in any
     order; the compiler reorders them to spec-declaration
     order before wrapping into methods.  Missing ctor =
     E010; extra arm = E010.

  3. **Method shape per ctor.**  Each method is a `λ`-chain
     wrapping the arm body with one binder per ctor argument,
     in declared order.  For nullary ctors, the method is
     just the arm body.  For `Succ(p)` (one Nat arg), the
     method is `λ (_p :_default Nat). body[p/var 0]`.

  4. **Motive shape.**  A non-dependent `λ (_ :_ghost specHead).
     returnType`.  The `returnType` comes from `expected`;
     `elabMatch` requires a known return type (same
     constraint as if/else per B6).

## Ctor resolution

`resolveArmCtor?` (`MatchHelpers.lean`) maps a pattern node
to `(specName, ctorIndex, IndCtor)`:

  * Qualified pattern `color.Red` → `resolveQualCtor?`.
  * Unqualified pattern `Red` → sweep user specs + prelude
    specs in declaration order (first match wins).
  * Non-ctor patterns (var, wildcard, literal, tuple) → none;
    those arms are out of Phase-2 scope.

## Method binder scope

`scopeAndDepthForCtor` sets up the body-elab scope for an
arm's body.  For `Succ(p) => body`:

  1. Push `_arg` as the method parameter (positional match
     at the recursion point of the ctor).
  2. For each ctor arg position, push either the declared
     pattern-variable name OR a synthetic `_arg_N` binder.
  3. The body elaborates under this extended scope; its
     de Bruijn indices reference the arm's bound pattern vars.

`wrapCtorMethod` then folds the ctor's arg-type list into
`λ` chain, shifting the body up one per binder to align
indices.

## Iota reduction (runtime)

Runtime match reduction fires iota per `Reduction.iotaStep?`
(kernel) and `Interp.iotaValue` (eval) — a
`Term.indRec spec motive methods (Term.ctor spec k _ args)`
reduces to `methods[k]` applied to `args` via
`Reduction.iotaArgs`.  Recursive calls on inductive-valued
args are produced by the iota-expansion rule per
`fx_design.md` §H.4 Ind-ι.

## Deferred — match on parameterized scrutinee

Match against `opt : option(Nat)` currently emits E010 in
`elabMatch`.  The match compiler requires knowing the
scrutinee's type parameters to:

  1. Build the motive with correct type arguments for
     substitution via `substParams`.
  2. Thread the `typeArgs` into each method's ctor-arg
     bindings (the ctor's declared arg types reference the
     type params via `Term.var i`).

Phase-2 scope has this blocked until the elaborator can
compute the scrutinee's type — either by threading typed
scope (currently Scope carries names only) or by running the
kernel's `infer` on the elaborated term.

## Deferred — wildcard / variable patterns

`_ => ...` catch-all arms and bare variable arms (`n =>
body` where `n` binds the whole scrutinee) are rejected at
E010 today.  The match compiler requires a ctor per arm
because wildcard desugaring produces N identical arms (one
per remaining ctor), which needs a closed-form substitution
pass the Phase-2 compiler doesn't have.
-/

namespace FX.Derived.Match

open FX.Kernel

/-! ## Pinning example — nullary-ctor match

Surface:
```
match c;
  Red   => Nat.Zero;
  Green => Nat.Succ(Nat.Zero);
  Blue  => Nat.Succ(Nat.Succ(Nat.Zero));
end match
```

Kernel output shape (for a match on a `color`-typed scrutinee
named `c` at de Bruijn 0):
```
Term.indRec "color"
  motive
  [Nat.Zero, Nat.Succ(Nat.Zero), Nat.Succ(Nat.Succ(Nat.Zero))]
  (Term.var 0)
```

Where `motive` is non-dependent: `λ (_ :_ghost color). Nat`.
-/

/-- Kernel shape of a match on color, per the translation
    above.  Concrete value shown here so a regression in
    `elabMatch` producing (e.g.) wrong `motive` shape or
    out-of-order methods surfaces at this definition's
    elaboration. -/
def colorMatchShape (scrutinee : Term) : Term :=
  let motive : Term :=
    -- λ (_ :_ghost color). Nat
    Term.lam Grade.ghost (Term.ind "color" []) (Term.ind "Nat" [])
  let methodRed   : Term := Term.ctor "Nat" 0 [] []
  let methodGreen : Term := Term.ctor "Nat" 1 [] [Term.ctor "Nat" 0 [] []]
  let methodBlue  : Term :=
    Term.ctor "Nat" 1 []
      [Term.ctor "Nat" 1 [] [Term.ctor "Nat" 0 [] []]]
  Term.indRec "color" motive [methodRed, methodGreen, methodBlue] scrutinee

/-- Method count of a match kernel-shape — 3 for color (one
    method per ctor).  `native_decide` pins the count so a
    regression that dropped/duplicated an arm surfaces here. -/
def colorMatchMethodCount (scrutinee : Term) : Nat :=
  match colorMatchShape scrutinee with
  | .indRec _ _ methods _ => methods.length
  | _                     => 0

example : colorMatchMethodCount (Term.var 0) = 3 := by native_decide

/-- Extract the ctor-index of method 0 (the Red case).  Red
    compiles to `Nat.Zero` → ctor index 0 in the Nat spec.  A
    regression that reordered methods (spec-decl vs arm-source
    order) would flip this. -/
def colorMatchMethodRedIndex (scrutinee : Term) : Option Nat :=
  match colorMatchShape scrutinee with
  | .indRec _ _ methods _ =>
    match methods[0]? with
    | some t =>
      match t with
      | Term.ctor _ k _ _ => some k
      | _                 => none
    | none => none
  | _                     => none

example : colorMatchMethodRedIndex (Term.var 0) = some 0 := by native_decide

/-! ## Pinning example — payload-binding match

Surface:
```
match n;
  Zero    => Nat.Zero;
  Succ(p) => p;
end match
```

The `Succ(p) => p` arm binds `p` to the Succ ctor's Nat payload.
The compiler wraps the arm body (`p`) in a λ that binds `p`
under its own binder — so the body's `p` reference compiles
to `Term.var 0`. -/

/-- Kernel shape for the pred-via-match pattern.  Pinned so
    the lambda-chain wrapping logic in `wrapCtorMethod` stays
    correct. -/
def predMatchShape (scrutinee : Term) : Term :=
  let motive : Term :=
    Term.lam Grade.ghost (Term.ind "Nat" []) (Term.ind "Nat" [])
  let methodZero : Term := Term.ctor "Nat" 0 [] []
  -- Succ arm: λ (_p :_default Nat). var 0
  -- (var 0 refers to the arm's `p` binder)
  let methodSucc : Term :=
    Term.lam Grade.default (Term.ind "Nat" []) (Term.var 0)
  Term.indRec "Nat" motive [methodZero, methodSucc] scrutinee

/-- Method count pinning for the pred-match shape.  Two ctors
    (Zero, Succ) → two methods. -/
def predMatchMethodCount (scrutinee : Term) : Nat :=
  match predMatchShape scrutinee with
  | .indRec _ _ methods _ => methods.length
  | _                     => 0

example : predMatchMethodCount (Term.var 0) = 2 := by native_decide

/-! ## Iota reduction

When the scrutinee is a concrete ctor registered in the
globalEnv's userSpecs (or in the hardcoded prelude
registry), iota fires under `whnf`:

```
Term.indRec "Bool" _ [mFalse, mTrue] Term.ctor "Bool" 1 [] []
  → mTrue                                               (True branch)
```

The reduction lives in `Reduction.iotaStep?` and is covered
extensively in `tests/Tests/Kernel/ReductionTests.lean`.  We
don't duplicate that coverage here — iota's pin is
`ReductionTests.lean`, not this file.  The shapes above
(colorMatchShape, predMatchShape) are for documentation of
the elab's output, not for direct whnf reduction (user
specs like `color` aren't in the default `globalEnv.empty`
used by `Term.whnf ... {}`, so iota would stay stuck at
the elab-produced shape). -/

end FX.Derived.Match

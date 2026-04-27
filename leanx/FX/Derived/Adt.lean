import FX.Kernel.Inductive
import FX.Kernel.Term

/-!
# Derived spec — ADT translation (§3.3, D4)

Algebraic data types (variants) are the direct surface form for
the kernel's `Ind` family (Appendix H.4).  The translation is
mostly 1:1 — the elaborator elabs constructor arguments' types
against the spec's param telescope and emits an `IndSpec`.

This module documents the translation and pins the expected
shape via `example` blocks so elaboration-time regressions
surface at build, not at runtime conformance.  UNTRUSTED (L3
per `SPEC.md` §5) — the load-bearing work is in
`FX/Kernel/Inductive.lean` (the kernel spec + strict-positivity
checker) and `FX/Elab/Elaborate.lean` (elabTypeDeclSpec and
elabVariantCtor).

## Surface syntax (§3.3)

Three forms, covered by §5.9 of fx_grammar.md:

```
-- Nullary ctors:
type color
  Red;
  Green;
  Blue;
end type;

-- Ctors with positional payload:
type shape
  Circle(Nat);
  Rect(Nat, Nat);
end type;

-- Ctors with named payload (record-in-variant):
type expr
  Lit(value: Nat);
  Var(name: Nat);
  Add(left: expr, right: expr);
end type;
```

## Translation to kernel

Each surface type decl produces one `IndSpec`:

  * `name` — the surface type name.
  * `params` — the type parameter telescope (each `a: type` →
    `Term.type Level.zero`).  Empty for non-parameterized types.
  * `ctors` — one `IndCtor` per surface variant, in declaration
    order.
  * Each `IndCtor` carries `args : List Term` (positional
    argument types elaborated under the spec's `paramScope`)
    and `argNames : List String` (declared field names for
    named-payload variants; synthetic `_arg_N` for positional).

The `ctorIndex` stored in `Term.ctor` and `Term.indRec` is the
positional index into this list.

## Construction

A surface ctor call `Red` (nullary) or `Some(42)` (applied) is
emitted as:

```
Term.ctor "color" 0 [] []               -- Red
Term.ctor "option" 1 [typeArgs] [42]    -- Some(42)
```

Type args come from:
  * The expected type at elab time (B9 landing) — used for
    nullary ctor references in typed positions.
  * The positional `[]` for non-parameterized specs.

Resolution of the ctor reference (surface `Red` → `(color,
0, RedCtor)`) goes through `resolveCtorRef?` in
`FX/Elab/MatchHelpers.lean`:

  1. Qualified form `color.Red` → `resolveQualCtor?`
  2. Unqualified sweep `Red` → `resolveUnqualCtor?` (finds the
     first spec with a matching ctor name)

## Pattern matching (elimination)

`match c; Red => ...; end match` elaborates to
`Term.indRec "color" motive methods c`.  The match compiler in
`FX/Elab/Elaborate.lean` builds:

  * `motive` — a constant `λ (_ :_ghost color). returnType`
  * `methods` — one per ctor in spec-declaration order; each
    method is a lambda chain binding the ctor's args.  The
    compiler walks arms to find each ctor's body, then wraps
    it in the right lambda chain via `wrapCtorMethod`.

Match exhaustiveness is enforced by ctor-count check: the
match arm count must equal `spec.ctorCount`, one arm per ctor.
Arms are reordered to ctor-declaration order before wrapping.

## Strict positivity

The kernel's `StrictPositivity.isSatisfied` walks each ctor's
arg-type tree and rejects self-references in contravariant
positions (under a `pi` domain).  Canonical pass: `Nat.Succ(Nat)`
— `Nat` appears in final-codomain position.  Canonical reject:
`type bad Mk(bad -> bad); end type;` — `bad` on the left of
an arrow.

## Parameterized ADTs (B9 landing)

```
type option<a: type>
  None;
  Some(a);
end type;
```

Elaborates to:

```
IndSpec {
  name   := "option"
  params := [Term.type Level.zero]
  ctors  := [
    { name := "None", args := [], argNames := [] },
    { name := "Some", args := [Term.var 0], argNames := ["_arg_0"] }
  ]
}
```

The `Term.var 0` in `Some`'s arg refers to the spec's sole
type param `a` in the ctor-arg scope (elaborator pushes param
names onto `paramScope` before elabing each ctor's args).

Type-arg inference at ctor use sites reads the expected type
via `elabExpr`'s `expected : Option Term` parameter.  When
expected is `Term.ind specName [typeArgs]` and specName matches,
the elaborator threads typeArgs into `Term.ctor specName ctorIndex
typeArgs ctorArgs` — Typing's `substParams` then resolves the
ctor's arg types at check time.

## Known limitations (deferred)

  * Match against a parameterized scrutinee — rejected at E010
    in the match compiler.  Needs scope-threaded type info or
    kernel-level infer-on-elaborated-term; deferred to M2+.
  * GADT return-type refinement per fx_grammar.md §5.9's
    `upper_ident ":" type ";"` variant_ctor form — parsed but
    not elaborated (§31 H.4 supports it structurally; surface
    wiring is an A10-follow-up).
-/

namespace FX.Derived.Adt

open FX.Kernel

/-! ## Non-parameterized ADT: `type color Red; Green; Blue; end type;` -/

/-- Nullary-ctor color enum.  Matches what `elabTypeDeclSpec`
    produces on the surface `type color Red; Green; Blue;
    end type;`.  All three ctors are nullary (no payload). -/
def colorSpec : IndSpec :=
  { name   := "color"
  , params := []
  , ctors  := [
      { name := "Red",   args := [] },
      { name := "Green", args := [] },
      { name := "Blue",  args := [] }
    ]
  }

example : colorSpec.ctorCount = 3 := by decide
example : colorSpec.paramCount = 0 := by decide
example : colorSpec.ctors.map (·.name) = ["Red", "Green", "Blue"] := by decide

-- Findctor? returns positional index — pin all three positions.
example : (colorSpec.findCtor? "Red").map Prod.fst   = some 0 := by decide
example : (colorSpec.findCtor? "Green").map Prod.fst = some 1 := by decide
example : (colorSpec.findCtor? "Blue").map Prod.fst  = some 2 := by decide
example : colorSpec.findCtor? "Purple"               = none   := by decide

/-! ## ADT with payload: `type natbox Empty; One(Nat); end type;` -/

/-- Two-ctor spec where one ctor carries a Nat payload.  Pins
    that the payload's arg type is preserved positionally. -/
def natboxSpec : IndSpec :=
  { name   := "natbox"
  , params := []
  , ctors  := [
      { name := "Empty", args := [] },
      { name := "One",   args := [Term.ind "Nat" []] }
    ]
  }

example : natboxSpec.ctorCount = 2 := by decide
example : (natboxSpec.ctorAt? 1).map (·.args.length) = some 1 := by decide

/-! ## Parameterized ADT: `type option<a: type> None; Some(a); end type;` -/

/-- Canonical parameterized spec — the shape `elabTypeDeclSpec`
    produces post-B9.  `a` lives at de Bruijn index 0 inside
    the ctor-arg scope (single spec param = single scope entry). -/
def optionSpec : IndSpec :=
  { name   := "option"
  , params := [Term.type Level.zero]
  , ctors  := [
      { name := "None", args := [] },
      { name := "Some", args := [Term.var 0] }
    ]
  }

example : optionSpec.ctorCount = 2  := by decide
example : optionSpec.paramCount = 1 := by decide

-- The `Some` ctor's payload references the type param via var 0.
-- (Term doesn't derive DecidableEq, so check via head element.)
example :
    (optionSpec.ctorAt? 1 |>.bind (·.args.head?) |>.map
      (fun t => match t with | .var i => i | _ => 999))
      = some 0 := by decide

/-! ## Construction shapes -/

/-- `color.Red` surface → `Term.ctor "color" 0 [] []`.  Zero-arg
    ctor, zero type-args (non-parameterized spec), ctorIndex 0
    (positional in declaration order). -/
example : Term.structEq
    (Term.ctor "color" 0 [] [])
    (Term.ctor "color" 0 [] []) = true := by native_decide

/-- `natbox.One(Nat.Succ(Nat.Zero))` surface → ctorIndex 1 with
    a single Nat value arg.  Pins the positional-payload emit. -/
def natboxOne : Term :=
  Term.ctor "natbox" 1 []
    [Term.ctor "Nat" 1 [] [Term.ctor "Nat" 0 [] []]]

example : Term.structEq natboxOne
    (Term.ctor "natbox" 1 []
      [Term.ctor "Nat" 1 [] [Term.ctor "Nat" 0 [] []]])
    = true := by native_decide

/-- `option(Nat).Some(Nat.Zero)` surface — B9's parameterized
    construction with inferred type args.  Elab reads the
    expected type `option(Nat)` and threads `[Nat]` as the
    typeArgs position.  Pinned here to catch regression in
    either the elab's expected-type-read path OR the kernel's
    substParams arg-substitution. -/
def someNatZero : Term :=
  Term.ctor "option" 1 [Term.ind "Nat" []]
    [Term.ctor "Nat" 0 [] []]

example : Term.structEq someNatZero
    (Term.ctor "option" 1 [Term.ind "Nat" []]
      [Term.ctor "Nat" 0 [] []])
    = true := by native_decide

end FX.Derived.Adt

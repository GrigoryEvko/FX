import FX.Kernel.Coinductive
import FX.Kernel.Term

/-!
# Derived spec — Codata translation (§3.5, D10)

Codata types are the direct surface form for the kernel's `Coind`
family (Appendix H.5).  A `codata` declaration lists its
DESTRUCTORS rather than constructors — observations rather than
introductions — matching the duality between `Ind` (constructors
+ `indRec` eliminator) and `Coind` (destructors + `unfold`
coeliminator).

This module documents the translation and pins the expected
shape via `example` blocks so a regression in `CoindSpec`
construction or in the Coind-ν guardedness check surfaces at
build, not at runtime conformance.  UNTRUSTED (L3 per SPEC.md
§5) — the load-bearing work lives in:

  * `FX/Kernel/Coinductive.lean` — the `CoindSpec` structure,
    `findDestructor?` resolver, and `Guarded.isSatisfied`
    conservative Coind-ν checker (A2 landing).
  * `FX/Kernel/Term.lean` — the `Term.coind typeName typeArgs`
    form keyed by name (parallel to `Term.ind` for inductives).
  * `FX/Elab/Elaborate.lean` — the `codata` / `unfold`
    elaborator arrives with E-5 / Phase-6 once Coind-form /
    Coind-intro / Coind-elim axioms land.  Phase-2 rejects
    surface `codata` at E010 and kernel `Term.coind` at T100.

## Surface syntax (§3.5)

Three forms, all listed destructor-first:

```
-- Simplest infinite stream:
codata stream<a: type>
  fn head(self) : a;
  fn tail(self) : stream(a);
end codata;

-- Multi-destructor codata — observing more than one facet:
codata queue_view<a: type>
  fn peek(self)  : a;
  fn next(self)  : queue_view(a);
  fn length(self): nat;     -- secondary observation — no self-ref
end codata;

-- Codata can freely combine regular types + sibling codatas
-- (nested final-codomain position is still guarded):
codata tagged_stream<a: type, tag: type>
  fn value(self) : a;
  fn label(self) : tag;
  fn rest(self)  : tagged_stream(a, tag);
end codata;
```

Every destructor has exactly one parameter named `self`, typed
by the codata being declared; this is enforced by the
elaborator per §5.14 of fx_grammar.md.

## Translation to kernel

Each surface `codata` declaration produces one `CoindSpec`:

  * `name : String` — the surface codata name.
  * `params : List Term` — the type-parameter telescope.  Each
    entry's type (typically `Term.type Level.zero`) plus de
    Bruijn discipline (`var i` references earlier params)
    matches the `IndSpec.params` convention.
  * `destructors : List CoindDestructor` — one per surface
    destructor in declaration order.  Each destructor carries
    a `name` and a `resultType` expressed over the spec's
    param scope.
  * `sized : Bool` — true iff the spec carries an implicit
    size index `s : size` (§3.5, dim 20 per §6.3).  Default
    `true` since every surface `codata` carries a size
    parameter.  Phase-2 the flag is informational; the full
    size arithmetic lands with the copattern elaborator.

The `Term.coind typeName typeArgs` constructor references the
spec by name; resolution goes through `CoindSpec.byName?`
(currently returns `none` — Phase-6 A5 wiring).

## Observation (destructor application)

Surface `s.head` / `s.tail` desugar — once the Phase-6 coind
typing rules land — to one of two kernel shapes:

```
Coind-elim "stream" 0 <typeArgs> scrutinee   -- head
Coind-elim "stream" 1 <typeArgs> scrutinee   -- tail
```

Phase-2 elaborator has no surface syntax for destructor
invocation yet; it arrives alongside the kernel elim rule.
Phase-2 `.field` access on a codata scrutinee fails at resolver
time (no matching record).

## Construction (`unfold`)

Surface construction from destructor-result equations:

```
fn nats_from<s: size>(n: i64) : stream<s>(i64)
  with Productive;
  sized s;
= unfold<s>
    head => n;
    tail => nats_from<s>(n + 1);
  end unfold;
```

Kernel translation (Phase-6 plan):

```
Coind-intro "stream" [Term.ind "i64" []]
  [ <head result>; <tail result> ]
```

Each `unfold` arm supplies a term whose type matches the
declared destructor's `resultType` after substituting the spec
params.  The arms are reordered to destructor-declaration order
by the elaborator (same mechanism as match arms reorder to
constructor order per D5).

## Guardedness check (Coind-ν, Appendix H.5)

`Guarded.isSatisfied` decides the conservative Coppo-Dezani /
Abel-Pientka rule: self-reference to the codata being declared
is legal only in FINAL-CODOMAIN position of a destructor's
result type.  Concretely:

  * `head : self -> a` — `stream` does not appear in result.
    Always guarded.
  * `tail : self -> stream(a)` — `stream` appears at the
    result's top — guarded (producing more of the same codata).
  * `bad : self -> (stream(a) -> stream(a))` — `stream`
    appears under a `pi` DOMAIN — contravariant, REJECTED.
  * `weird : self -> (other_codata(stream(a)))` — nested
    sibling-codata wraps our self-ref.  Rejected conservatively
    by Phase-2 since the guardedness check is an under-
    approximation that stays on the safe side; fully-general
    positivity on arbitrary codata args is deferred.

`absent` / `absentList` / `guardedResultType` are mutual
helpers walking the `Term` structure; `destructorsOk` folds
over the spec's destructors and reports `false` on the first
violation.

## Size index (§3.5, §6.3 dim 20)

Every sized codata admits a size parameter `s : size`.  The
size tracks observation depth: `head(x : stream<s>(a)) : a`
costs 0 size units; `tail(x : stream<s>(a)) : stream<s-1>(a)`
consumes one.  Unfold at size `s` requires `s >= 1` and each
recursive call stays at `s` (or lower) under the destructor.

Phase-2's `CoindSpec.sized : Bool` records only whether the
size index is present; the actual arithmetic lives in the
`Size` grade (A8) and will be checked at `unfold<s>` +
destructor-call sites when Coind-form/intro/elim land.

## Deferred — surface codata decl elaboration (E010)

`codata stream<a> ... end codata;` is parsed per
fx_grammar.md §5.14, but `elabDecl` rejects codata decls
at E010 (Phase-6 deferred per SPEC.md).  Landing path:

  1. Extend `elabTypeDeclSpec` with a `codata` branch building
     a `CoindSpec` rather than an `IndSpec`.
  2. Thread user-declared codata into `GlobalEnv` via
     `CoindSpec.byName?` resolution.
  3. Add Coind-form / Coind-intro / Coind-elim to `Typing`
     (removing T100).
  4. Register prelude codatas (`stream`, `colist`, `colazy`).
  5. Extend `Reduction.whnf` with ν (destructor-on-unfold)
     reduction per Appendix H.5 Coind-ν.

Each step is isolated — Phase-2 can stub-out codata without
affecting inductive or graded-type work.
-/

namespace FX.Derived.Codata

open FX.Kernel

/-! ## Non-parameterized codata — `codata ticker head; tail; end codata;`

The simplest well-formed codata spec: no type parameters, two
destructors (`head : ticker -> Nat`, `tail : ticker -> ticker`).
Used here to pin the CoindSpec shape without the extra noise
of type-parameter scoping. -/

/-- Kernel shape for a parameterless codata with two
    destructors.  `head`'s result type is a fixed base type;
    `tail`'s result is the self-reference `coind "ticker" []`. -/
def tickerSpec : CoindSpec :=
  { name        := "ticker"
  , params      := []
  , destructors := [
      { name       := "head"
      , resultType := Term.ind "Nat" [] }
    , { name       := "tail"
      , resultType := Term.coind "ticker" [] }
    ]
  , sized       := true
  }

example : tickerSpec.destructorCount = 2 := by decide
example : tickerSpec.paramCount = 0      := by decide
example : tickerSpec.sized = true        := by decide

-- Destructor lookup is positional per declaration order —
-- `head` at 0, `tail` at 1.
example : (tickerSpec.findDestructor? "head").map Prod.fst = some 0 := by decide
example : (tickerSpec.findDestructor? "tail").map Prod.fst = some 1 := by decide
example : tickerSpec.findDestructor? "unknown"             = none   := by decide

-- Guardedness: `head`'s result has no self-ref (trivially OK);
-- `tail`'s self-ref is in final-codomain position.  Both pass.
example : Guarded.isSatisfied tickerSpec = true := by decide

/-! ## Parameterized codata — `codata stream<a: type> head; tail; end codata;`

The canonical stream.  `stream<a>` has one type parameter and
two destructors.  `head : stream(a) -> a` extracts an element
from the stream's front; `tail : stream(a) -> stream(a)`
produces the rest.  The pinning examples below mirror what the
D10 codata elaborator emits when it lands. -/

/-- Canonical stream spec.  The `head` destructor's result is
    `Term.var 0` — the spec's sole type param `a` in the
    destructor-arg scope.  The `tail` destructor's result
    `coind "stream" [var 0]` carries the same type param
    through the self-reference. -/
def streamSpec : CoindSpec :=
  { name        := "stream"
  , params      := [Term.type Level.zero]
  , destructors := [
      { name       := "head"
      , resultType := Term.var 0 }
    , { name       := "tail"
      , resultType := Term.coind "stream" [Term.var 0] }
    ]
  , sized       := true
  }

example : streamSpec.destructorCount = 2 := by decide
example : streamSpec.paramCount = 1      := by decide

-- Extract the head destructor's resultType — should be `var 0`
-- (reference to the spec's sole param).  Scalar extraction
-- avoids DecidableEq-on-Term.
example :
    (streamSpec.destructorAt? 0 |>.map (fun destructor =>
      match destructor.resultType with
      | .var i => i
      | _      => 999))
      = some 0 := by decide

-- `tail`'s resultType head is `coind "stream" _`.  Extract the
-- top-level constructor tag to pin the self-reference shape.
example :
    (streamSpec.destructorAt? 1 |>.map (fun destructor =>
      match destructor.resultType with
      | .coind coindName _ => coindName
      | _                  => "other"))
      = some "stream" := by decide

-- Guardedness passes: `head`'s result is the bare param (no
-- self-ref); `tail`'s self-ref is in final-codomain position
-- without any enclosing contravariant binder.
example : Guarded.isSatisfied streamSpec = true := by decide

/-! ## Multi-destructor codata — `codata queue_view<a> peek; next; length; end codata;`

Demonstrates a codata with MORE than two destructors and a
mix of self-referencing (`next`) + non-self (`peek`, `length`)
result types.  Useful as a regression test against
implementations that accidentally hardcode "exactly two
destructors" or "every destructor is self-referential." -/

/-- Queue-like codata: three destructors, one is self-ref,
    two are plain observations.  `length : queue_view -> Nat`
    shows that a destructor may have a non-parameter, non-self-
    ref result type. -/
def queueViewSpec : CoindSpec :=
  { name        := "queue_view"
  , params      := [Term.type Level.zero]
  , destructors := [
      { name       := "peek"
      , resultType := Term.var 0 }
    , { name       := "next"
      , resultType := Term.coind "queue_view" [Term.var 0] }
    , { name       := "length"
      , resultType := Term.ind "Nat" [] }
    ]
  , sized       := true
  }

example : queueViewSpec.destructorCount = 3 := by decide

-- Three destructors at three positions; lookup each.
example : (queueViewSpec.findDestructor? "peek").map   Prod.fst = some 0 := by decide
example : (queueViewSpec.findDestructor? "next").map   Prod.fst = some 1 := by decide
example : (queueViewSpec.findDestructor? "length").map Prod.fst = some 2 := by decide

-- All three destructor result types are guarded.  `peek` and
-- `length` have no self-ref (trivially absent per §H.5); `next`
-- places self in final-codomain position.
example : Guarded.isSatisfied queueViewSpec = true := by decide

/-! ## Guardedness — rejection examples

Coind-ν requires that the codata being defined not appear
under a `pi` domain in any destructor's result type.  The specs
below intentionally violate this and `Guarded.isSatisfied`
returns `false`.  Pinning the REJECT cases guards against
regressions that accidentally weaken the check.  -/

/-- REJECT: `weird`'s result puts the self-reference under a
    pi DOMAIN (contravariant position).  A consumer of this
    destructor would receive a function TAKING a `bad` value —
    exactly the consume-the-codata-contravariantly shape that
    breaks productivity.  Guardedness check rejects.

    The Term-level shape: `pi _ <self-ref> Nat` — the pi's
    domain is `coind "bad" []`. -/
def badContravariantSpec : CoindSpec :=
  { name        := "bad"
  , params      := []
  , destructors := [
      { name       := "weird"
      , resultType :=
          Term.pi Grade.default
            (Term.coind "bad" [])      -- ← self in domain = REJECT
            (Term.ind "Nat" [])
            Effect.tot }
    ]
  , sized       := true
  }

example : Guarded.isSatisfied badContravariantSpec = false := by decide

/-- REJECT: `hidden`'s result nests the self-reference inside
    an inductive-type argument (`List(also_bad)`).  Conservative
    guardedness also rejects this — deciding whether an
    arbitrary `Ind` family preserves positivity of its args
    is a separate check (deferred); Phase-2 guardedness is an
    under-approximation that stays on the safe side. -/
def badNestedSpec : CoindSpec :=
  { name        := "also_bad"
  , params      := []
  , destructors := [
      { name       := "hidden"
      , resultType := Term.ind "List" [Term.coind "also_bad" []] }
    ]
  , sized       := true
  }

example : Guarded.isSatisfied badNestedSpec = false := by decide

/-! ## Shape pinning — `Term.coind` constructor

Pins that `Term.coind` is a first-class term constructor with
a String name + typeArgs list.  `structEq` reflects that the
kernel distinguishes coind terms by name + positional type
arguments.  A regression that dropped the name from the
coind constructor would break these equalities. -/

/-- `stream(Nat)` shape — `coind "stream" [Term.ind "Nat" []]`. -/
def streamOfNat : Term :=
  Term.coind "stream" [Term.ind "Nat" []]

example : Term.structEq streamOfNat
    (Term.coind "stream" [Term.ind "Nat" []])
    = true := by native_decide

-- Distinct spec names — different coind term even with same
-- type args (the spec identity is the name, not the args).
example : Term.structEq
    (Term.coind "stream" [Term.ind "Nat" []])
    (Term.coind "colist" [Term.ind "Nat" []])
    = false := by native_decide

-- Distinct type args — different coind term even with same
-- spec name.  Parallel to how `ind` distinguishes `option(Nat)`
-- from `option(Bool)` via typeArgs.
example : Term.structEq
    (Term.coind "stream" [Term.ind "Nat" []])
    (Term.coind "stream" [Term.ind "Bool" []])
    = false := by native_decide

/-! ## Registry status

`Coinductive.specByName?` currently returns `none` uniformly
(Phase-2 placeholder — see `FX/Kernel/Coinductive.lean`
section "Spec registry").  This is the hook the D10 codata
elaborator fills in: user-declared codatas land in
`GlobalEnv` and `specByName?` threads through them at each
Coind-form / Coind-elim typing site.  Until then, every
`Term.coind` reference at typing time falls through to T100
(`codata rejected — Phase-6 deferred`). -/

example : Coinductive.specByName? "stream"     = none := rfl
example : Coinductive.specByName? "queue_view" = none := rfl
example : Coinductive.specByName? ""            = none := rfl

end FX.Derived.Codata

import FX.Kernel.Term

/-!
# Inductive family specs (Appendix H.4)

`IndSpec` carries everything the kernel needs to type-check and
reduce the `Term.ind` / `Term.ctor` / `Term.indRec` forms.  The
spec is keyed by a string name; `Term` references the spec by
name, and `specByName?` resolves the reference at each typing or
reduction site.

## Why name indirection

The alternative — embedding `IndSpec` directly inside `Term`
constructors — creates a mutual inductive dependency between
`Term` and `IndSpec`.  Lean 4.29 handles this but (a) the
derivation of `Repr`/`Inhabited` becomes finicky, (b) `structEq`
grows nontrivially, and (c) every elaborator/evaluator that walks
`Term` has to cross the mutual boundary.  Keeping the spec
outside `Term` and looking it up by name is what both Lean and
Coq do internally; the kernel stays syntactically pure and the
spec lives in a classic environment.

## Phase 2.2 scope (task A1 from the interpreter plan)

Real structure with:

  * `name : String` — globally unique identifier
  * `params : List Term` — parameter telescope (each entry's
    type).  Phase 2.2's prelude inductives (Bool, Nat, Unit,
    Empty) use `params = []`; parameterized families
    (Option, List, Pair) land in M2+ but the shape is ready.
  * `ctors : List IndCtor` — constructors in declaration order.
    `ctorIndex` in `Term.ctor` / `Term.indRec` indexes into this list.

Each `IndCtor` carries its `args : List Term` — the telescope of
argument types.  Inside an arg type, `var i` references prior
params + earlier args per the standard de Bruijn discipline.

Self-reference (the recursive occurrence of the type being
defined) uses `ind spec.name typeArgs` by name.  The
strict-positivity checker ensures these occurrences are legal.

## Strict positivity

`StrictPositivity.isSatisfied` rejects constructor argument types where
the spec-name occurs in a negative position.  The canonical bad
example: `type U Bad(U -> U); end type` — here `U` appears to
the left of an arrow, which is contravariant.  Allowed patterns:
as the final codomain (`U`), under a `List U` or similar positive
nested constructor, or not at all.

Phase 2.2 implements a conservative checker: an occurrence of
`spec.name` is rejected if it appears under any `pi` binder on
the LEFT of the arrow.  Nested inductives (`List U`) and
parameters (`var i`) pass through unaffected.  Future phases may
relax to allow more patterns per Dybjer / Abel-Altenkirch-Uustalu.
-/

namespace FX.Kernel

/-- A single constructor in an inductive family.  `args` is the
    telescope of argument types; each entry can reference earlier
    args + the enclosing spec's params via de Bruijn indices. -/
structure IndCtor where
  name : String
  args : List Term
  /-- Optional declared field names, one per entry in `args`.
      Empty means anonymous / positional.  Records (B8) populate
      this from their declared field list so `.field` projection
      can map a surface name to its positional index.  Kernel
      doesn't reason about names — it preserves them through
      substitution + reduction unchanged. -/
  argNames : List String := []
  deriving Repr, Inhabited

/-- An inductive family spec.  Keyed by name; referenced by
    `Term.ind`, `Term.ctor`, `Term.indRec` through `typeName`.

    `isCopy` records whether the surface declaration carried the
    `@[copy]` attribute (§7.8): when true, the elaborator treats
    every parameter or let-binding of this type as grade-ω on the
    usage dimension (multi-use admitted without explicit `ref`
    annotation).  Defaults to false — linear-by-default remains
    the kernel's resource discipline for user-declared types. -/
structure IndSpec where
  name   : String
  params : List Term
  ctors  : List IndCtor
  isCopy : Bool := false
  deriving Repr, Inhabited

namespace IndSpec

/-- Number of constructors. -/
def ctorCount (spec : IndSpec) : Nat := spec.ctors.length

/-- Number of type parameters. -/
def paramCount (spec : IndSpec) : Nat := spec.params.length

/-- Lookup a constructor by name, returning its index + entry. -/
def findCtor? (spec : IndSpec) (ctorName : String) : Option (Nat × IndCtor) :=
  let rec aux (currentIdx : Nat) : List IndCtor → Option (Nat × IndCtor)
    | []              => none
    | ctor :: rest    =>
      if ctor.name == ctorName then some (currentIdx, ctor)
      else aux (currentIdx + 1) rest
  aux 0 spec.ctors

/-- Lookup a constructor by index. -/
def ctorAt? (spec : IndSpec) (ctorIndex : Nat) : Option IndCtor :=
  spec.ctors[ctorIndex]?

/-- Find a named field's positional index within `spec.ctors[0]`.
    Meaningful for record specs (B8) — single-ctor ADTs whose ctor
    has `argNames` populated.  Returns `none` when the spec has no
    ctors, the first ctor has no named fields, or the name isn't
    declared.  Used by field-projection elaboration (`.field`). -/
def findFieldIndex? (spec : IndSpec) (fieldName : String) : Option Nat :=
  match spec.ctors with
  | firstCtor :: _ =>
    let rec aux (currentIndex : Nat) : List String → Option Nat
      | []               => none
      | name :: restNames =>
        if name == fieldName then some currentIndex
        else aux (currentIndex + 1) restNames
    aux 0 firstCtor.argNames
  | []             => none

end IndSpec

/-! ## Strict positivity check -/

namespace StrictPositivity

/- True iff the term `t` contains no occurrence of `ind name _`
   anywhere.  Used to verify a constructor argument's type is
   free of the spec being defined (the simplest legal pattern).
   Mutually recursive with `absentList` for structural reduction
   so the check is usable with `by decide`. -/

mutual

def absent (specName : String) : Term → Bool
  | .var _        => true
  | .type _       => true
  | .const _      => true
  | .forallLevel body => absent specName body
  | .coind _ coindArgs => absentList specName coindArgs
  | .app func arg => absent specName func && absent specName arg
  | .lam _ domain body    => absent specName domain && absent specName body
  | .pi _ domain body _   => absent specName domain && absent specName body
  | .sigma _ domain body  => absent specName domain && absent specName body
  | .id eqType lhs rhs    => absent specName eqType && absent specName lhs && absent specName rhs
  | .refl witness         => absent specName witness
  | .idJ motive base eq   =>
    absent specName motive && absent specName base && absent specName eq
  | .quot baseType relation => absent specName baseType && absent specName relation
  | .quotMk relation witness =>
    absent specName relation && absent specName witness
  | .quotLift lifted respects target =>
    absent specName lifted && absent specName respects && absent specName target
  | .ind inductiveName constructorArgs   =>
    inductiveName != specName && absentList specName constructorArgs
  | .ctor inductiveName _ typeArgs ctorArgs =>
    inductiveName != specName && absentList specName typeArgs && absentList specName ctorArgs
  | .indRec inductiveName motive methods target =>
    inductiveName != specName
      && absent specName motive
      && absentList specName methods
      && absent specName target
  | .coindUnfold _ coindArgs arms =>
    -- Coinductive value forms carry no inductive spec
    -- reference themselves; we only need to recurse into
    -- their sub-terms to catch any embedded `ind` references.
    absentList specName coindArgs && absentList specName arms
  | .coindDestruct _ _ targetTerm =>
    absent specName targetTerm

def absentList (specName : String) : List Term → Bool
  | []             => true
  | term :: rest   => absent specName term && absentList specName rest

end

/- Conservative positive-occurrence check: the term is a legal
   argument-type shape for a constructor of the inductive named
   `name` — either the final codomain is `ind name _` with earlier
   args strictly-positive, or the term is a simple non-self-
   referential type.  Rejects self-reference at any left-of-arrow
   position. -/
def strictlyPositive (specName : String) : Term → Bool
  | .pi _ domain codomain _ =>
    absent specName domain && strictlyPositive specName codomain
  | .ind inductiveName constructorArgs =>
    -- At the final codomain: either another type-name (absent),
    -- or a self-application whose sub-args themselves contain no
    -- self-reference.
    if inductiveName = specName then absentList specName constructorArgs
    else absent specName (.ind inductiveName constructorArgs)
  | term => absent specName term

/-- True iff every constructor argument type in `spec` passes
    the strictly-positive check with respect to `spec.name`. -/
def ctorArgsOk (specName : String) : List Term → Bool
  | []               => true
  | argType :: rest  => strictlyPositive specName argType && ctorArgsOk specName rest

def ctorsOk (specName : String) : List IndCtor → Bool
  | []                => true
  | ctor :: rest      => ctorArgsOk specName ctor.args && ctorsOk specName rest

def isSatisfied (spec : IndSpec) : Bool :=
  ctorsOk spec.name spec.ctors

end StrictPositivity

/-! ## Spec registry

Phase 2.2 provides a small hardcoded registry holding Bool, Nat,
Unit, and Empty specs.  Stream A11 will replace this with a real
`GlobalEnv` threaded through `Typing`/`Reduction`/`Eval`.  Until
then, every kernel site calling `specByName?` consults this
registry.
-/

namespace Inductive

/-- Bool spec — `type Bool False; True; end type`.  Both ctors
    nullary, no params.  Marked `isCopy` (§7.8): pure value type
    with no linear resources, so bindings carry usage = ω. -/
def boolSpec : IndSpec :=
  { name   := "Bool"
  , params := []
  , ctors  := [
      { name := "False", args := [] },
      { name := "True",  args := [] }
    ]
  , isCopy := true
  }

/-- Nat spec — `type Nat Zero; Succ(Nat); end type`.  Self-
    reference in `Succ` passes strict positivity because the
    occurrence is in final-codomain position.  Marked `isCopy`:
    self-reference is permitted for recursive pure data because
    the type as a whole carries no linear payload — every Succ
    layer wraps another Nat of the same grade. -/
def natSpec : IndSpec :=
  { name   := "Nat"
  , params := []
  , ctors  := [
      { name := "Zero", args := [] },
      { name := "Succ", args := [.ind "Nat" []] }
    ]
  , isCopy := true
  }

/-- Unit spec — `type Unit tt; end type`.  Single nullary ctor.
    Marked `isCopy`: carries no data, trivially duplicable. -/
def unitSpec : IndSpec :=
  { name   := "Unit"
  , params := []
  , ctors  := [
      { name := "tt", args := [] }
    ]
  , isCopy := true
  }

/-- Empty spec — `type Empty; end type`.  Zero constructors.
    Encodes `never` per `fx_design.md` §3.9.  Vacuously `isCopy`:
    no values exist, so any grade holds for a binding of this
    type (including ω). -/
def emptySpec : IndSpec :=
  { name   := "Empty"
  , params := []
  , ctors  := []
  , isCopy := true
  }

/-! ## D2 — `Std.Prelude.Primitive` (fixed-width + char + string)

Per `fx_design.md` §3.1, FX's primitive types are refinement
aliases with representation annotations:

  * `u8`  = `nat { x < 256 }` with `repr(bits(8))`
  * `i32` = `int { -2^31 <= x and x < 2^31 }` with `repr(bits(32))`
  * ... and so on for every fixed-width integer, decimal, float,
    fraction, char, and string.

### Phase-2 rendering: opaque zero-constructor inductives

Phase-2's kernel does NOT yet expose refinement types.  The
Stream-E pipeline (SMT encoder + Z3 oracle, tasks E1-E4) will
discharge the refinement obligations once it lands; until then,
the primitive types are represented as **zero-constructor
inductives**:

  * The type is well-formed and can appear in every signature
    position — `fn f(x: i64) : u32 = ...`, `type R { bytes:
    u8 }`, etc.
  * No values can be constructed from a literal yet — the
    kernel has no rule to elaborate `42 : u8` into a
    concrete representation.  A Phase-2 program binding `fn
    f(x: u8) : u8 = x` type-checks, but cannot be called
    successfully from another Phase-2 function.
  * Once refinement types land, each primitive's ctor surface
    populates with the arithmetic operations (widen, narrow,
    literal-in, op) that §3.1 specifies.

### Why zero-ctor instead of aliases to `Nat`

Aliasing `i64 := Nat` would lose type distinction across the
surface grammar — `fn f(x: u8) : i64 = x` would slip through,
hiding sign and width mismatches from the type-checker.  The
zero-constructor approach preserves those distinctions without
committing to a specific representation choice before Stream E.

### Membership

Every primitive name enumerated in §3.1 is added to
`primitiveNumericNames` below.  The registration flows through
`primitiveSpecs` → `preludeSpecs` so `Inductive.specByName?` and
`Inductive.knownName` recognize them uniformly alongside Bool /
Nat / Unit / Empty.

Note on `nat` vs `Nat`: §3.1's lowercase `nat` is the arbitrary-
precision natural the spec uses in signatures; Phase-2's `Nat`
(capital N, in `preludeSpecs`) is the finite-ctor inductive
used for literal elaboration.  The two are DIFFERENT types at
the kernel — `nat` is added below as an opaque primitive to
preserve the spec's naming, with migration to a single
representation deferred to the refinement-types layer.  Same
remark applies to `int`, which has no Nat-like counterpart. -/

/-- Fixed-width and arbitrary-precision primitive type names per
    §3.1.  Each name becomes a zero-constructor opaque `IndSpec`
    via `primitiveSpecs`.  Ordering: sign groups first, then
    exact-decimal, then float, then fraction, then character /
    string. -/
def primitiveNumericNames : List String :=
  -- Signed fixed-width (§3.1 row 1)
  [ "i8", "i16", "i32", "i64", "i128", "i256", "i512", "i1024"
  -- Unsigned fixed-width (§3.1 row 2)
  , "u8", "u16", "u32", "u64", "u128", "u256", "u512", "u1024"
  -- Platform-width pointer sizes (§3.1 row 3)
  , "isize", "usize"
  -- Arbitrary-precision integer + nat-alias (§3.1 rows 4, 5).
  -- `nat`, `int` are lowercase per spec; `Nat` is the capital-N
  -- inductive in `natSpec` used for literal elaboration.
  , "int", "nat"
  -- Primitive character + string (§3.1 rows 6, 7).
  , "char", "string"
  -- Exact decimals (§3.1 row 8).
  , "decimal"
  , "dec32", "dec64", "dec96", "dec128", "dec256", "dec512", "dec1024"
  -- Exact fractions (§3.1 row 9).
  , "frac", "frac64", "frac128", "frac256"
  -- IEEE 754 floats (§3.1 row 10).
  , "f32", "f64" ]

/-- One opaque zero-constructor `IndSpec` per primitive name.
    Strict positivity is trivially satisfied (no constructors to
    inspect).  Kernel reference implementation detail: this
    representation IS the refinement-aliases-without-refinements
    phase-2 compromise documented in `primitiveNumericNames`'s
    docstring.

    All primitives are marked `isCopy := true` (§7.8): they
    represent plain-old-data numeric / character / string
    values.  The refinement layer (Stream E) will narrow the
    predicates without changing the copy-compatibility — a `u8`
    constrained to `{ x < 256 }` remains byte-sized POD. -/
def primitiveSpecs : List IndSpec :=
  primitiveNumericNames.map fun primitiveName =>
    { name := primitiveName, params := [], ctors := []
    , isCopy := true }

/-- `List<a>` spec — `Nil` / `Cons(a, List<a>)`.  One type
    parameter; recursive via `ind "List" [var 0]`.  Registered
    in `preludeSpecs` below (Q71) specifically to support
    surface list literals `[a, b, c]` — the elaborator bakes
    the concrete element type into `Term.ctor "List"
    [elementType] [...]` directly, sidestepping the A10 gap
    (elaborator-side type-arg inference on `var 0` ctor args).

    Polymorphic functions over `List` (`fn length<a>(xs :
    List<a>) : Nat`) still require A10 and remain blocked. -/
def listSpec : IndSpec :=
  { name   := "List"
  , params := [.type .zero]
  , ctors  := [
      { name := "Nil",  args := [] },
      { name := "Cons", args := [.var 0, .ind "List" [.var 0]] }
    ]
  }

/-- Optional value spec — `type Option<a> None; Some(a); end
    type` per `fx_design.md` §3.3.  One type parameter `a`; two
    constructors:

      * `None` — nullary.
      * `Some(a)` — single arg of type `var 0` (the parameter).

    Q75 promotes Option from `experimentalSpecs` into
    `preludeSpecs` alongside `listSpec`.  The kernel's
    `Term.substParams` (Typing.lean's ctor-arg check) already
    substitutes `typeArgs` into the ctor's `var i` placeholders,
    so `Term.ctor "Option" 1 [Nat] [Nat.Zero]` typechecks
    cleanly without needing full A10 (elaborator-side type-arg
    unification).

    The elaborator's existing type-arg inference in the `.app`
    ctor path (`inferredTypeArgs`) pulls the `T` from an
    expected `Option(T)` Pi and threads it into the emitted
    Term.  Without an expected type, the nullary `None` path
    still emits `Term.ctor "Option" 0 [] []` (empty typeArgs)
    and the kernel's T111 "expected N type params" surfaces as
    the diagnostic. -/
def optionSpec : IndSpec :=
  { name   := "Option"
  , params := [.type .zero]
  , ctors  := [
      { name := "None", args := [] },
      { name := "Some", args := [.var 0] }
    ]
  }

/-- Pair spec — `type Pair<a, b> MkPair(a, b); end type` per
    `fx_design.md` §3.3.  Two type parameters; one two-arg
    constructor `MkPair(a, b)`.  Parameter ordering: `a = var 1`,
    `b = var 0` at the ctor-arg scope.

    Q79 promotes Pair from `experimentalSpecs` into
    `preludeSpecs` alongside Option (Q75) and List (Q71).  The
    kernel's `Term.substParams` correctly handles multi-param
    substitution — `typeArgs = [a, b]` becomes `openWith b`
    (consumes var 0) then `openWith a` (consumes the shifted var
    0 which was the original var 1), producing the right
    assignments. -/
def pairSpec : IndSpec :=
  { name   := "Pair"
  , params := [.type .zero, .type .zero]
  , ctors  := [
      { name := "MkPair", args := [.var 1, .var 0] }
    ]
  }

/-- The Phase 2.2 hardcoded registry.  `listSpec` (Q71),
    `optionSpec` (Q75), and `pairSpec` (Q79) are parameterized
    specs registered in the main prelude; all three work because
    `Term.substParams` handles typeArg substitution.

    `resultSpec` remains in `Experimental` for now — its two
    ctors `Ok(a)` and `Err(e)` each use only ONE of the two
    type parameters, so the expected-type-threading pattern
    alone doesn't suffice to recover `e` from an `Ok(x)` or
    `a` from an `Err(y)`.  Full A10 type-arg unification would
    let `Ok(x) : Result(Nat, String)` infer `e = String` from
    the outer expected type — that's the missing piece.

    Primitives (D2, 36 names) append at the end so core
    inductives (Bool, Nat, Unit, Empty, List, Option, Pair)
    take lookup precedence. -/
def preludeSpecs : List IndSpec :=
  [boolSpec, natSpec, unitSpec, emptySpec, listSpec, optionSpec, pairSpec]
    ++ primitiveSpecs

/-- Look up an `IndSpec` by name, trying `userSpecs` first, then
    the hardcoded `preludeSpecs`.  User specs shadow prelude —
    `userSpecs = [boolSpec']` with a custom `Bool` overrides the
    built-in `Bool` at this lookup.  Default `userSpecs = []`
    gives the old prelude-only behavior for call sites that don't
    yet thread a `GlobalEnv`.  B9 added the user-specs path;
    `GlobalEnv.specByName?` in `Env.lean` is the convenience
    overload for callers that hold a `GlobalEnv`. -/
def specByName? (name : String) (userSpecs : List IndSpec := [])
    : Option IndSpec :=
  match userSpecs.find? (·.name == name) with
  | some userSpec => some userSpec
  | none          => preludeSpecs.find? (·.name == name)

/-- True iff a spec with this name is registered (prelude only by
    default; pass `userSpecs` to also consult user-declared ADTs). -/
def knownName (name : String) (userSpecs : List IndSpec := []) : Bool :=
  (specByName? name userSpecs).isSome

end Inductive

/-! ## Experimental parameterized specs (NOT registered)

The following specs are parameterized by a type argument and are
shipped alongside the prelude as design fixtures only — they are
intentionally absent from `preludeSpecs` because Phase 2.2's
typing / reduction layer does NOT yet thread spec parameters
through constructor argument types.  Unblocks on task A10
(universe polymorphism + dependent spec params) — see
`/root/iprit/FX/fx_design.md` §3.13 (higher-kinded types) and
Appendix H.4 (Ind-form / Ind-intro / Ind-elim).

Each spec below uses the de-Bruijn convention that `var 0` inside
a constructor arg type references the left-most spec parameter.
A future phase (A10 / "real typing for parameterized inductives")
will substitute the actual type arguments supplied at every
`ctor`/`indRec` site into the corresponding `var` positions
before running the current checks.  Until then, building a
`ctor "Option" 1 [Nat] [.ctor "Nat" 0 [] []]` fails the arg-type
check because the expected type is literally `var 0` — the
unshifted parameter reference — and `var 0` does not convert to
`ind "Nat" []`.

These fixtures are useful for:

  * Writing failing tests that document the exact shape of the
    gap (see `ParameterizedSpecGapTests.lean`).
  * Checking that `StrictPositivity.isSatisfied` treats parameter
    references (`var i`) as positive regardless of where they
    appear in the telescope.
  * Exercising `findCtor?` / `ctorAt?` on multi-parameter
    specs to confirm the accessors work regardless of the
    parameter telescope's length.

Do NOT add these to `preludeSpecs` until the typing layer
threads `typeArgs` into `ctorSpec.args` — registering them
prematurely would surface `T002` (type mismatch) on every
otherwise-correct construction site and fail the whole build.
-/

namespace Experimental

/-- Experimental Result spec — `type Result<a, e> Ok(a); Err(e);
    end type`.  Two parameters, two unary constructors (one each
    for each parameter).  The classic tagged union pattern. -/
def resultSpec : IndSpec :=
  { name   := "Result"
  , params := [.type .zero, .type .zero]
  , ctors  := [
      { name := "Ok",  args := [.var 1] },
      { name := "Err", args := [.var 0] }
    ]
  }

/-- The experimental registry — parameterized specs NOT in the
    main prelude.  Tests can enumerate this list to verify each
    spec's shape, run `StrictPositivity.isSatisfied` on each, and
    document the gap between spec declaration and full typing
    support. -/
def experimentalSpecs : List IndSpec :=
  -- `listSpec` moved to `Inductive.listSpec` (Q71); `optionSpec`
  -- (Q75); `pairSpec` (Q79).  Only `resultSpec` remains here —
  -- its asymmetric ctors (each ctor uses only one of the two
  -- type params) need full A10 type-arg unification to land.
  [resultSpec]

end Experimental

end FX.Kernel

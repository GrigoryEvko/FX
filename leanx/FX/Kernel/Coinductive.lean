import FX.Kernel.Term

/-!
# Coinductive family specs (Appendix H.5)

`CoindSpec` carries everything the kernel needs to type-check and
reduce the `Term.coind` / unfold / destructor forms.  The spec is
keyed by a string name; `Term.coind typeName typeArgs` references
the spec by name, and `CoindSpec.byName?` resolves the reference
at each typing or reduction site.  This is the dual of
`IndSpec` / `Inductive.specByName?` for codata per §3.5.

## Why name indirection

Embedding `CoindSpec` inside `Term.coind` directly creates a
mutual cycle: `CoindSpec` needs `Term` for destructor result types,
and `Term.coind` would then need `CoindSpec`.  Keeping the spec
outside `Term` and looking it up by name matches both `IndSpec`
and the pattern Lean 4 and Coq use internally for their own
kernel.  See `FX/Kernel/CLAUDE.md` for the shared design rationale.

## Phase-2 scope (task A2)

Real structure with:

  * `name : String` — globally unique identifier.
  * `params : List Term` — parameter telescope.  Each entry's type
    follows the standard de Bruijn discipline (`var i` references
    earlier params).  The canonical surface example `codata
    stream<a: type>` corresponds to `params = [Type<0>]`.
  * `destructors : List CoindDestructor` — destructor list in
    declaration order.  A destructor is a named projection from a
    value of this codata type.  Per §3.5, every `codata` declares
    its destructors (`head`, `tail`, …) and values are constructed
    via `unfold` supplying one result per destructor.
  * `sized : Bool` — whether the spec carries a size index
    `s : size` per §3.5.  Dimension 20 (Size) tracks observation
    depth; sized codata admits `stream<s>(a)` where each `tail`
    consumes one size unit.  Phase-2 the flag is informational.
    The full sized-index typing rule (Coind-elim consuming one
    size unit per destructor call) lands with the copattern
    elaborator in Phase 6.

Each `CoindDestructor` carries:

  * `name : String` — destructor name (`head`, `tail`, etc.).
  * `resultType : Term` — type of what this destructor returns.
    Inside the type, `var 0 …` references the coind spec's
    params; self-reference uses `coind spec.name paramArgs` —
    identical to how `IndSpec` uses `ind spec.name …`.

## Guardedness check (Coind-ν)

`Guarded.isSatisfied` rejects destructor result types where
the co-recursive occurrence of the spec-name appears in an
unguarded position.  Per Abel-Pientka POPL 2013 extended from
Coppo-Dezani guardedness to copatterns:

  * Self-reference in final-codomain position (the destructor
    returns a fresh observation of the same codata) is LEGAL.
    Example: `stream.tail : self -> stream<a>` has `stream` in
    final-codomain position.

  * Self-reference under a left-of-arrow (contravariant) position
    is REJECTED.  Example: `bad.weird : self -> (stream<a> ->
    stream<a>)` would let consumers observe `stream` under an
    arrow — dangerous because it breaks the positivity discipline
    that makes productivity decidable.

Phase-2 implements a conservative checker: an occurrence of
`spec.name` is rejected inside a destructor's `resultType` if it
appears under any `pi` binder on the LEFT of the arrow.  Nested
codata / inductives on the right pass through; parameters do too.
This mirrors `StrictPositivity.isSatisfied` for `IndSpec`.

## Spec registry (Phase-2 stub)

Phase 2 has no surface codata prelude — `stream` and friends land
with the D10 codata elaborator and the Phase 6 coind typing rule.
`CoindSpec.byName?` currently consults a per-elaboration list of
user-declared specs (threaded via `GlobalEnv` in future work) and
returns `none` for built-in codata until the prelude catalog grows.
Typing rejects `Term.coind` at T100 until the kernel gains
Coind-form / Coind-intro / Coind-elim (Phase 6, A5).
-/

namespace FX.Kernel

/-- A single destructor on a coinductive family — the dual of
    `IndCtor` for codata.  A destructor is a named projection
    out of the coind value.  The `resultType` tells the type
    system what observing this destructor produces.

    For `codata stream<a: type>`:

    ```
    { name := "head", resultType := .var 0 }  -- the a param
    { name := "tail", resultType := .coind "stream" [.var 0] }
    ```

    `resultType` references the spec's params via de Bruijn
    indices: in a spec with `params = [T_1, ..., T_n]`, `var (n
    - 1 - i)` refers to `T_i`.  Self-reference uses `coind
    spec.name [applied-params]`. -/
structure CoindDestructor where
  name       : String
  resultType : Term
  deriving Repr, Inhabited

/-- A coinductive family spec.  Keyed by name; referenced by
    `Term.coind typeName typeArgs` through `typeName`.

    Fields:

      * `name` — globally unique identifier.
      * `params` — parameter telescope (each entry is a type).
      * `destructors` — declaration-order list; index in surface
        `unfold` binds each arm to a destructor slot by name.
      * `sized` — whether the spec carries a size index per §3.5
        dim 20.  Default `true` because every surface `codata`
        carries an implicit size parameter; the full arithmetic
        lives in the `Size` grade (A8) and is checked at
        `unfold<s>` + destructor-call sites in Phase 6. -/
structure CoindSpec where
  name        : String
  params      : List Term
  destructors : List CoindDestructor
  sized       : Bool := true
  deriving Repr, Inhabited

namespace CoindSpec

/-- Number of destructors. -/
def destructorCount (spec : CoindSpec) : Nat := spec.destructors.length

/-- Number of type parameters. -/
def paramCount (spec : CoindSpec) : Nat := spec.params.length

/-- Lookup a destructor by name, returning its positional index
    + entry.  `index` is needed because the surface `unfold`
    may supply arms in arbitrary order but the kernel elim-time
    pattern picks by position. -/
def findDestructor? (spec : CoindSpec) (destructorName : String)
    : Option (Nat × CoindDestructor) :=
  let rec aux (currentIndex : Nat) : List CoindDestructor
               → Option (Nat × CoindDestructor)
    | []                      => none
    | destructor :: rest      =>
      if destructor.name == destructorName then
        some (currentIndex, destructor)
      else
        aux (currentIndex + 1) rest
  aux 0 spec.destructors

/-- Lookup a destructor by positional index. -/
def destructorAt? (spec : CoindSpec) (destructorIndex : Nat)
    : Option CoindDestructor :=
  spec.destructors[destructorIndex]?

end CoindSpec

/-! ## Guardedness check (Coind-ν, Appendix H.5)

Mirrors `StrictPositivity.absent` / `strictlyPositive` for
`IndSpec`.  The check is local to each destructor's result type:

  * self-reference in final-codomain position is OK (producing
    more of the same codata),
  * self-reference under a left-of-arrow position is REJECTED
    (would let consumers introspect the codata contravariantly),
  * nested codata / inductive types pass through unaffected.

`isSatisfied` walks the destructors, asserting each `resultType`
is `guardedResultType spec.name`.
-/

namespace Guarded

/- True iff the term contains no occurrence of `coind name _`
   anywhere — i.e., this sub-term is free of the spec being
   defined.  Dual to `StrictPositivity.absent`: it's the
   "absent" check used for contravariant positions.  Mutually
   recursive with `absentList` for structural reduction. -/

mutual

def absent (specName : String) : Term → Bool
  | .var _        => true
  | .type _       => true
  | .const _      => true
  | .forallLevel body => absent specName body
  | .ind _ typeArgs   => absentList specName typeArgs
  | .ctor _ _ typeArgs valueArgs =>
    absentList specName typeArgs && absentList specName valueArgs
  | .indRec _ motive methods target =>
    absent specName motive
      && absentList specName methods
      && absent specName target
  | .coind coindName coindArgs =>
    coindName != specName && absentList specName coindArgs
  | .coindUnfold coindName coindArgs arms =>
    -- Unfold expressions may create a value of the same codata
    -- type being defined — that's not a guardedness violation
    -- at the unfold site.  The arm bodies, however, are walked
    -- for absence: if an arm references the spec's destructor
    -- chain unguardedly inside its OWN sub-term structure, the
    -- destructor signatures' guardedness check (§H.5 Coind-ν)
    -- already rejected it.  Here we only check that the arm
    -- bodies don't ALSO introduce the spec in an irregular
    -- way (e.g., as the domain of a nested Pi).  Following the
    -- conservative `ctor` treatment: walk every sub-term.
    coindName != specName
      && absentList specName coindArgs
      && absentList specName arms
  | .coindDestruct coindName _destructorIndex targetTerm =>
    -- A destructor observation on a value of the same spec is
    -- NOT guarded — consuming the codata in a contravariant
    -- position would let the definition observe itself during
    -- construction.  Parallel to `ind`'s treatment above.
    coindName != specName && absent specName targetTerm
  | .app func arg => absent specName func && absent specName arg
  | .lam _ domain body    => absent specName domain && absent specName body
  | .pi _ domain body _   => absent specName domain && absent specName body
  | .sigma _ domain body  => absent specName domain && absent specName body
  | .id eqType lhs rhs    =>
    absent specName eqType && absent specName lhs && absent specName rhs
  | .refl witness         => absent specName witness
  | .idJ motive base eq   =>
    absent specName motive && absent specName base && absent specName eq
  | .quot baseType relation =>
    absent specName baseType && absent specName relation
  | .quotMk relation witness =>
    absent specName relation && absent specName witness
  | .quotLift lifted respects target =>
    absent specName lifted && absent specName respects && absent specName target

def absentList (specName : String) : List Term → Bool
  | []             => true
  | term :: rest   => absent specName term && absentList specName rest

end

/-- Conservative guardedness check on a destructor result type.
    The self-reference `coind specName _` is LEGAL only at the
    final-codomain position (the "head" of a right-spine through
    `pi` binders).  Under any `pi` domain, self-reference is
    REJECTED — it would place the codata in a contravariant
    position, breaking productivity guarantees. -/
def guardedResultType (specName : String) : Term → Bool
  | .pi _ domain codomain _ =>
    absent specName domain && guardedResultType specName codomain
  | .coind coindName coindArgs =>
    if coindName = specName then
      -- Self-reference in final-codomain position: each
      -- nested arg must not itself unguardedly reference self.
      absentList specName coindArgs
    else
      absent specName (.coind coindName coindArgs)
  | term => absent specName term

/-- True iff every destructor's result type passes the guardedness
    check with respect to the spec's name. -/
def destructorsOk (specName : String) : List CoindDestructor → Bool
  | []                     => true
  | destructor :: rest     =>
    guardedResultType specName destructor.resultType
      && destructorsOk specName rest

/-- The spec satisfies Coind-ν iff every destructor result type
    is guarded.  Phase-2 uses this as a decidable compile-time
    check; Phase 6's full `unfold<s> body` typing rule
    additionally verifies size-decreasing structure per §3.5. -/
def isSatisfied (spec : CoindSpec) : Bool :=
  destructorsOk spec.name spec.destructors

end Guarded

/-! ## Spec registry (Phase-2 stub)

Phase-2 has no hardcoded coinductive prelude.  Real resolution
arrives with D10 (codata elaborator, surface syntax) and the
Phase-6 coind typing rule (Coind-form / Coind-intro / Coind-
elim).  Until then `byName?` returns `none` uniformly; `Typing`
still rejects `Term.coind` at T100.
-/

namespace Coinductive

/-- Resolve a coinductive spec by name.  Phase-2 returns `none`
    — the real lookup threads through `GlobalEnv` once codata
    elaboration lands.  Kept here so future wiring is a
    single-line change. -/
def specByName? (_name : String) : Option CoindSpec := none

end Coinductive

end FX.Kernel

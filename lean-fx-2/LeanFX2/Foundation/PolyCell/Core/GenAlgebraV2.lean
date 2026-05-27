import LeanFX2.Foundation.PolyCell.Core.RawTermSubstV2

/-! # Foundation/PolyCell/Core/GenAlgebraV2 — fold algebra (Allais Semantics)

This file ships `GenAlgebraV2`: the per-generator semantic algebra
that foldV2 (#177) consumes for non-variable generators.  Together
with `ActsOnRawTermV2Var` (#175, handling the variable case), this
completes the typeclass + record input shape for the Allais-style
fold engine.

Direct analog of Allais et al. ICFP'18's "Semantics" record's `alg`
field — the per-constructor children-combination function.  Other
Semantics fields (`var`, `th^V`) are handled separately in v2 by
`ActsOnRawTermV2Var` (variable bridge) and `Action.liftForRaw` /
`Action.liftForTy` (Container binder lift).

## Why a record + one field rather than a typeclass

A typeclass would tie the algebra to its `Container`, but the
canonical "rebuild .mkGen" algebra is INDEPENDENT of the Container —
it works equally well for renaming, substitution, and any other
Container shape.  A bare record decouples the algebra from the
Container: ONE algebra value (`GenAlgebraV2.canonical`) reused
across all foldV2 instantiations.

For future variants (NbE eval producing a value-form type instead of
`RawTermV2`, term-size computation producing `Nat`, etc.), the
record's `algebra` field shape generalizes uniformly — the result
type just changes from `RawTermV2 scope` to whatever.  For now (L2
shipping), the result is fixed at `RawTermV2 scope` to keep #176
focused on the rename/subst use case.

## The clean architectural property — uniform algebra signature

The algebra's signature uses ONE scope (not source/target distinct):

```
algebra : ∀ {scope : Nat}
            (generator : Generator)
            (payload : generator.payload scope)
            (foldedChildren : RawTermChildrenV2 generator.binderShifts scope)
            → RawTermV2 scope
```

This is THE KEY DESIGN CHOICE.  At single-scope, `.mkGen generator
payload foldedChildren` typechecks UNIFORMLY for all 194 generators
— including `.gen_var` (where payload is `Fin scope` and children is
`.childNil`).  No per-generator dispatch needed in the canonical
algebra body.

Container threading (variable lookup, binder lifting) lives at the
foldV2 layer (#177), NOT here.  When foldV2 hits a non-variable
generator at scope S, it has:
* Already recursively folded the children spine at the (possibly
  bumped) target scope S
* Already applied the Container's binder-lift at each child crossing
* Now ready to combine: call `algebra.algebra generator payload
  foldedChildren` to get the result at scope S

The variable case (`.gen_var`) is dispatched separately at foldV2 to
`ActsOnRawTermV2Var.varToRawTermV2 container pos`.

## The cascade-tax killer made concrete (L2 architectural payoff)

The canonical algebra body is **ONE LINE**:

```
canonical.algebra generator payload foldedChildren :=
  .mkGen generator payload foldedChildren
```

In v1's dim-indexed era, the analog work for a single traversal
operation (e.g. `RawTerm.rename`) required a 74-arm pattern match
over the term inductive's 74 constructors — and each NEW operation
(`subst`, `weaken`, ...) duplicated the same 74-arm cascade.

In v2, the SAME canonical algebra serves rename, subst, weaken, and
any future "rebuild .mkGen with the same generator + payload + folded
children" traversal.  Each new traversal becomes ONE foldV2 call with
its own Container; the algebra is reusable.

This is the architectural promise of L2 made concrete in #176:
"ONE generic recursion replaces N per-operation cascades."

## Zero-axiom verification

All declarations propext-free:
* `GenAlgebraV2` is a single-field record (no equation lemmas)
* `GenAlgebraV2.canonical` is a closed lambda body
* Smoke theorem closes by `rfl` (definitional reduction)

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- The Allais-style "Semantics" algebra for the v2 fold engine.

Captures the per-generator children-combination function foldV2
(#177) consumes when traversing a `RawTermV2`.  The `algebra` field
operates at a SINGLE scope (the result scope, where children have
already been folded via foldV2's recursive descent) and returns a
`RawTermV2 scope`.

Container threading (variable lookup, binder lifting) is foldV2's
responsibility, NOT the algebra's.  The algebra is purely a
combinator: take a generator + its payload + folded children, produce
a result term.

For the canonical use case (rename, subst, weaken), the algebra is
`.mkGen generator payload foldedChildren` — uniform rebuild for all
194 generators.  Future variants (NbE eval, term-size, ...) can
supply custom algebras with the same field shape but different
internal logic. -/
structure GenAlgebraV2 where
  /-- Combine recursively-folded children into a target `RawTermV2`.
  All inputs and the output live at the SAME scope; foldV2 handles
  scope shifting at binder crossings before invoking this. -/
  algebra : {scope : Nat} →
              (generator : Generator) →
              (payload : generator.payload scope) →
              (foldedChildren : RawTermChildrenV2 generator.binderShifts scope) →
              RawTermV2 scope

/-- The canonical "rebuild .mkGen" algebra — the universal recipe for
traversals that preserve term shape (rename, subst, weaken).  Applies
uniformly to all 194 generators in ONE line: rebuild the input
generator with its payload and the folded children spine.

This is the L2 cascade-tax killer made concrete: ONE line replaces
what would have been a 74-arm pattern match per traversal in v1's
dim-indexed era.  Each new traversal (rename, subst, weaken, ...)
will plug in via foldV2 (#177) with its own Container — the algebra
itself is reusable across all of them. -/
def GenAlgebraV2.canonical : GenAlgebraV2 where
  algebra := fun generator payload foldedChildren =>
    .mkGen generator payload foldedChildren

/-- Definitional unfolding theorem for the canonical algebra: the
algebra reduces by `rfl` to a literal `.mkGen` constructor
application.

Closes by `rfl` since `GenAlgebraV2.canonical.algebra` is a closed
lambda body returning a constructor application; both sides reduce
to the same term definitionally. -/
theorem GenAlgebraV2.canonical_algebra_eq_mkGen {scope : Nat}
    (generator : Generator)
    (payload : generator.payload scope)
    (foldedChildren : RawTermChildrenV2 generator.binderShifts scope) :
    GenAlgebraV2.canonical.algebra generator payload foldedChildren =
      .mkGen generator payload foldedChildren := rfl

/-- Smoke check: the canonical algebra applied to an empty-payload
empty-children generator (gen_unit at scope 0) reduces to the
`.mkGen .gen_unit () .childNil` literal.

Closes by `rfl`.  Verifies the canonical algebra evaluates cleanly
on a concrete fixture — the kind of input foldV2's variable-free
recursion paths will produce. -/
theorem GenAlgebraV2.canonical_algebra_gen_unit_smoke :
    GenAlgebraV2.canonical.algebra .gen_unit () .childNil =
      (.mkGen .gen_unit () .childNil : RawTermV2 0) := rfl

end LeanFX2.Foundation.PolyCell.Core

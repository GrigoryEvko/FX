import LeanFX2.Foundation.PolyCell.Core.GenAlgebraV2
import LeanFX2.Foundation.PolyCell.Core.LiftsRaw

/-! # Foundation/PolyCell/Core/FoldV2 — the generic fold engine (L2 workhorse)

This file ships **the substantial L2 piece**: the mutual recursive
engine that consumes the inputs shipped at #175 (`ActsOnRawTermV2Var`,
`RawTermSubstV2`) + #176 (`GenAlgebraV2`) and traverses a `RawTermV2`,
producing a target `RawTermV2` at a (possibly different) scope.

This is the architectural payoff of L2: ONE generic recursion that
subsequent tasks (#178 rename, #179 weaken, #180 subst) instantiate
without re-introducing a per-Generator cascade.

## The engine — mutual structural recursion

`foldV2` recurses on a `RawTermV2`'s `.mkGen` payload-children pair.
The recursion is MUTUAL with `foldChildrenV2`, which walks the
`RawTermChildrenV2` spine.  Because `RawTermV2` and
`RawTermChildrenV2` were defined in the same mutual inductive block
(see `RawTermV2.lean`), Lean's structural-recursion mechanism handles
termination automatically — no fuel parameter needed (unlike #162's
certifier, which had to cross a non-mutual inductive boundary).

## The variable-vs-non-variable dispatch

At each `.mkGen generator payload children` node, foldV2:

1. **Variable case (generator = .gen_var)**: dispatch to the
   Container's `ActsOnRawTermV2Var.varToRawTermV2`.  This is where the
   Container's domain semantics differ:
   * For `RawRenaming`: wrap the renamed Fin in `.mkGen .gen_var
     (renamedPos) .childNil`.
   * For `RawTermSubstV2`: return the substituent directly.

2. **Non-variable case (generator ≠ .gen_var)**: recursively fold
   children (lifting the Container at each binder crossing), then
   invoke `algebra.algebra generator payloadAtTarget foldedChildren`.
   The canonical algebra (#176) rebuilds `.mkGen` — uniform across
   all 193 non-variable generators.

The dispatch uses `if hVar : generator = .gen_var then ... else ...`
via `DecidableEq Generator` (#122).  No wildcard match, no 194-arm
enumeration in the recursion body itself.

## The scope-invariance helper (one-place 194-arm enumeration)

In the non-variable arm, foldV2 needs to convert `payload` from
`generator.payload sourceScope` to `generator.payload targetScope` to
invoke the algebra at the target scope.  For non-variable generators,
the payload type is scope-INVARIANT (Unit, Nat, etc. — all the
generators that aren't `gen_var`).

The helper `Generator.payload_scope_invariant_of_not_var` makes this
explicit:

```
theorem ... :
    generator.payload srcS = generator.payload tgtS := by
  cases generator
  case gen_var => exact absurd rfl hNotVar
  all_goals rfl
```

Three tactic lines that auto-discharge 194 goals (1 absurd + 193
rfls).  This is the L2 architectural promise made concrete: the
194-arm enumeration lives in ONE place (this helper), and every
downstream traversal reuses it without re-enumerating.

In v1's era, the analog work would require enumeration in every
traversal operation (rename, subst, weaken, ...).  L2 pays the cost
once.

## What this engine ENABLES (downstream tasks #178-#180)

* **`rename` via foldV2 (#178)**: instantiate `foldV2` with `Container :=
  RawRenaming` and the canonical algebra.  ONE LINE.

* **`weaken` via foldV2 (#179)**: special case of rename where the
  renaming is `Fin.succ`.  Composes via Container.

* **`subst` via foldV2 (#180)**: instantiate `foldV2` with `Container :=
  RawTermSubstV2` and the canonical algebra.  ONE LINE.

Each of these would be a 74-arm pattern match in v1's era.  In v2,
they reduce to one-line foldV2 instantiations because the cascade-tax
is amortized into this engine.

## Zero-axiom verification

All declarations propext-free:
* `iterateLiftRaw` — structural recursion on Nat
* `payload_scope_invariant_of_not_var` — cases over closed enum +
  rfl (per memory `feedback_lean_zero_axiom_match`: full enum on
  non-dep = clean)
* `foldV2` / `foldChildrenV2` — mutual structural recursion on the
  RawTermV2 / RawTermChildrenV2 inductives, dispatching via `if h :
  _ then _ else _` with `DecidableEq Generator`

Audit-gated in `Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

open LeanFX2

/-- Iterate `LiftsRaw.liftForRaw` N times.  Threads a Container
under N successive binder crossings — used by foldV2 to lift the
Container at each child of a binder-introducing generator.

For example, when foldV2 recurses into the body of a `gen_lam`
(binderShift `[1]` for the body child), the body lives at scope
`parentScope + 1`, so the Container must be lifted once via
`LiftsRaw.liftForRaw`.

This generalizes to arbitrary binder depths (any non-negative
shift).

The `[LiftsRaw Container]` constraint replaces an earlier `[Action
Container]` (per V2-L2.6 / #180 refactor).  `LiftsRaw` is the
minimal typeclass providing `liftForRaw` alone — sufficient for
foldV2 and avoids the chicken-and-egg with `Action.compose` which
would require `RawTermV2.subst` for the `RawTermSubstV2` instance. -/
def iterateLiftRaw {Container : Nat → Nat → Type} [LiftsRaw Container]
    {sourceScope targetScope : Nat}
    (someAction : Container sourceScope targetScope) (binderDepth : Nat) :
    Container (sourceScope + binderDepth) (targetScope + binderDepth) :=
  match binderDepth with
  | 0 => someAction
  | priorDepth + 1 => LiftsRaw.liftForRaw (iterateLiftRaw someAction priorDepth)

/-- The 194-arm enumeration in ONE place: for any non-variable
generator, its `payload` type does not depend on scope.

The `.gen_var` case is impossible (it carries payload `Fin scope`, the
ONE scope-dependent payload).  The 193 non-var cases all have
scope-invariant payload types (Unit, Nat, etc.) — these reduce
uniformly by `rfl`.

This helper is the architectural unlock for foldV2's non-variable
arm: given a `payload : generator.payload sourceScope` in the
non-variable branch, we cast to `generator.payload targetScope` via
this equality.  The 194 generators are enumerated once HERE; every
downstream traversal reuses this lemma. -/
theorem Generator.payload_scope_invariant_of_not_var
    {generator : Generator} (hNotVar : generator ≠ .gen_var)
    (sourceScope targetScope : Nat) :
    generator.payload sourceScope = generator.payload targetScope := by
  cases generator
  case gen_var => exact absurd rfl hNotVar
  all_goals rfl

-- The mutual fold engine.  Traverses a source term (foldV2) and its
-- children spine (foldChildrenV2), applying the Container at variable
-- positions and the algebra at non-variable generators.
--
-- Structural mutual recursion: foldV2 recurses into a term's children
-- via foldChildrenV2; foldChildrenV2 recurses into each child via
-- foldV2 and the rest of the spine via itself.  Both terminate because
-- RawTermV2 and RawTermChildrenV2 are mutual structural sub-parts of
-- each other.
mutual

/-- Fold a `RawTermV2`: traverse the term, dispatching variables to
the Container (via ActsOnRawTermV2Var) and non-variable generators
to the algebra (after recursively folding children).

The `[LiftsRaw Container]` constraint (formerly `[Action Container]`,
per #180 refactor) suffices: foldV2 only invokes the binder lift,
not `Action.compose` / `Action.identity` / the law fields.  See
`LiftsRaw.lean` for the architectural rationale. -/
def foldV2
    {Container : Nat → Nat → Type} [LiftsRaw Container]
    [ActsOnRawTermV2Var Container]
    (algebra : GenAlgebraV2)
    {sourceScope targetScope : Nat}
    (someAction : Container sourceScope targetScope)
    (sourceTerm : RawTermV2 sourceScope) :
    RawTermV2 targetScope :=
  match sourceTerm with
  | .mkGen generator payload children =>
    if hVar : generator = .gen_var then
      -- Variable case: dispatch to Container via the variable bridge.
      -- payload : generator.payload sourceScope, cast to Fin sourceScope
      -- via the equality `generator = .gen_var`.  We use explicit
      -- Eq.rec rather than `▸` because `▸` cannot find a motive when
      -- neither side of the equality is syntactically the target type.
      let varPosition : Fin sourceScope :=
        Eq.rec (motive := fun targetGenerator _hSubst =>
                  Generator.payload targetGenerator sourceScope)
               payload hVar
      ActsOnRawTermV2Var.varToRawTermV2 someAction varPosition
    else
      -- Non-variable case: recursively fold children, then apply
      -- algebra.  The payload type is scope-invariant for non-var
      -- generators (via the helper theorem), so we cast from source
      -- scope to target scope.
      let foldedChildren := foldChildrenV2 algebra someAction children
      let payloadEquality :=
        Generator.payload_scope_invariant_of_not_var hVar sourceScope targetScope
      let payloadAtTarget : generator.payload targetScope :=
        payloadEquality ▸ payload
      algebra.algebra generator payloadAtTarget foldedChildren

/-- Fold a `RawTermChildrenV2` spine: walk each child, lifting the
Container under binders as needed (per the child's binder shift).

Same `[LiftsRaw Container]` constraint as `foldV2` (per #180
refactor). -/
def foldChildrenV2
    {Container : Nat → Nat → Type} [LiftsRaw Container]
    [ActsOnRawTermV2Var Container]
    (algebra : GenAlgebraV2)
    {parentSourceScope parentTargetScope : Nat}
    {binderShifts : List Nat}
    (someAction : Container parentSourceScope parentTargetScope)
    (children : RawTermChildrenV2 binderShifts parentSourceScope) :
    RawTermChildrenV2 binderShifts parentTargetScope :=
  match binderShifts, children with
  | [], .childNil => .childNil
  | headShift :: _, .childCons childHead childTail =>
    -- Lift the Container under headShift binders, fold the head at
    -- the lifted scope, then recursively fold the rest of the spine.
    let liftedAction := iterateLiftRaw someAction headShift
    let foldedHead := foldV2 algebra liftedAction childHead
    let foldedTail := foldChildrenV2 algebra someAction childTail
    .childCons foldedHead foldedTail

end -- mutual

end LeanFX2.Foundation.PolyCell.Core

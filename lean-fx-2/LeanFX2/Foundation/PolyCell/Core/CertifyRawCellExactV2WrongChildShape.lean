import LeanFX2.Foundation.PolyCell.Core.CertifyRawCellExactV2

/-! # Foundation/PolyCell/Core/CertifyRawCellExactV2WrongChildShape

V2-fix-6 (2026-05-27).  Ships **reachability witnesses for the
`.wrongChildShape` rejection branch**.

## Why this file is needed

The negative-probe suite at
`CertifyRawCellExactV2NegativeProbes.lean` documents that
`.wrongChildShape` is, under fxProfile, "**reachable only under
future profiles with cross-sort spine semantics**" — i.e., the
branch is unreachable from public ingress.  Under fxProfile, every
`Generator.childSpecs` entry uses `.term` sort and `cellDimension 0`,
and every termBase head certifies to `.term` / `cellDimension 0`, so
the dispatcher's two checks at
`certifyChildrenInlineV2Fueled?:192-195` always succeed:

```
if hSort : headSort = headSpec.cellSort then
  subst hSort
  if hDim : headSpec.cellDimension = 0 then
    ... ok ...
  else
    exact .error .wrongChildShape    -- (dim mismatch)
else
  exact .error .wrongChildShape    -- (sort mismatch)
```

Agent 3 of the V2 falsification audit observed that the lack of any
test fixture activating either of these `.error` branches left the
behavioral content of `.wrongChildShape` rejection unwitnessed.  The
soundness-completeness triangulation is incomplete without showing
the rejection branch fires at all under SOME constructed input.

## What this file ships

Two reachability witnesses that invoke `certifyChildrenInlineV2Fueled?`
DIRECTLY (bypassing the generator dispatcher) with handcrafted
ChildSpecs that mismatch the head's inferred sort or dimension.

* **`_typeSort_rejects_termChild`** — passes a `typeSameScope`
  childSpec (demanding `.type` sort) with a unit-termBase child
  (certifying to `.term` sort).  Triggers the OUTER `hSort` failure.

* **`_nonZeroDim_rejects_termChild`** — passes a childSpec with
  `cellDimension := 1` (any non-zero dim) with a unit-termBase child
  (certifying to `cellDimension 0`).  Triggers the INNER `hDim`
  failure after the sort check succeeds.

Together they cover BOTH legs of the dispatch.

## Why this is "internal API" coverage

The probes call `certifyChildrenInlineV2Fueled?` directly with
manually-constructed (childSpecs, binderShifts, coherence, children)
tuples — inputs that fxProfile's `Generator.childSpecs` never
produces.  This is intentional: the goal is to witness the rejection
branch's REACHABILITY, not to demonstrate a regression in the
fxProfile public ingress.

A future ProfileExtension that introduces cross-sort childSpecs
(e.g., adding `.gen_lamWithTypeAnnotation` whose first child is
`.type`) would automatically activate the public-ingress reachability
of `_typeSort_rejects_termChild` without modifying these probes.

## Why `rfl` closes

Both probes are CONCRETE computations: given closed inputs, the
fueled walker reduces via Fin/Nat decidable equality to a definite
`Except.error .wrongChildShape` value.

For the sort probe:
1. `fuel = 8 = Nat.succ _`, hits the `fuel' + 1` arm.
2. `childSpecs = [typeMismatchSpec]`, `children = .childCons unit .childNil`
   — hits the `headSpec :: restSpecs` arm.
3. Recursively certifies `(.termBase unit)` to
   `headCert : CertifiedRawCellV2 ... 0 unit` with `sort = .term`.
4. `hSort : headSort = headSpec.cellSort` evaluates to `.term = .type`
   → `false` → `exact .error .wrongChildShape`.

For the dim probe:
1-3. Same as above (sort matches now: `.term = .term`).
4. `hSort` succeeds, subst happens.
5. `hDim : headSpec.cellDimension = 0` evaluates to `1 = 0` → `false`
   → `exact .error .wrongChildShape`.

No tactic gymnastics, no propext, no axioms.

## Forward-compat: where the public-ingress reachability lands

The V2 generator metadata currently has no cross-sort `Generator`
(every `Generator.childSpecs` entry uses `.term` sort, dim 0).  When
the V2-VORACIOUS or a future ProfileExtension introduces cross-sort
children, these probes' inputs become representable through public
generators, and the public-ingress reachability of
`.wrongChildShape` activates automatically.

Specifically: V2-L1.13 (SiteOpenness enum + compatibility on
ProfileExtension) is the natural follow-up that would extend the
generator metadata to allow cross-sort children.

## Zero-axiom verification

Both witness theorems pass `#assert_no_axioms`.  Audit-gated in
`Tools/AuditAll/AuditPolyCell.lean`.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- **`.wrongChildShape` reachability witness (sort mismatch).**

Invokes `certifyChildrenInlineV2Fueled?` directly with a
`typeSameScope` childSpec (demanding `.type` sort) and a unit-termBase
child (certifying to `.term` sort).  Triggers the dispatcher's
outer `hSort` check failure, returning `.error .wrongChildShape`.

This is the FIRST shipped witness that the `.wrongChildShape`
rejection branch is reachable at all — Agent 3 of the V2 falsification
audit observed it was unwitnessed under public ingress, and this
probe discharges that finding via direct-call coverage. -/
theorem certifyChildrenInlineV2Fueled?_typeSort_rejects_termChild :
    let unitChild : RawTermV2 0 := .mkGen .gen_unit () .childNil
    let typeMismatchSpec : ChildSpecV2 := ChildSpecV2.typeSameScope
    let coherence : ([0] : List Nat) = [typeMismatchSpec].map (·.scopeShift) := rfl
    certifyChildrenInlineV2Fueled? (profile := fxProfile)
        (fuel := 8) (parentScope := 0)
        (childSpecs := [typeMismatchSpec])
        (binderShifts := [0])
        (coherence := coherence)
        (children := .childCons unitChild .childNil) =
      Except.error .wrongChildShape := rfl

/-- **`.wrongChildShape` reachability witness (dimension mismatch).**

Invokes `certifyChildrenInlineV2Fueled?` directly with a childSpec
demanding `cellDimension 1` (any non-zero dim) and a unit-termBase
child (certifying to `cellDimension 0`).  Triggers the dispatcher's
inner `hDim` check failure AFTER the sort check succeeds, returning
`.error .wrongChildShape`.

Pair with `_typeSort_rejects_termChild`: the two probes cover BOTH
legs of the dispatch (outer sort check + inner dim check), discharging
the structural reachability of `.wrongChildShape` from both routes. -/
theorem certifyChildrenInlineV2Fueled?_nonZeroDim_rejects_termChild :
    let unitChild : RawTermV2 0 := .mkGen .gen_unit () .childNil
    let dimMismatchSpec : ChildSpecV2 :=
      { cellSort := .term, cellDimension := 1, scopeShift := 0 }
    let coherence : ([0] : List Nat) = [dimMismatchSpec].map (·.scopeShift) := rfl
    certifyChildrenInlineV2Fueled? (profile := fxProfile)
        (fuel := 8) (parentScope := 0)
        (childSpecs := [dimMismatchSpec])
        (binderShifts := [0])
        (coherence := coherence)
        (children := .childCons unitChild .childNil) =
      Except.error .wrongChildShape := rfl

end LeanFX2.Foundation.PolyCell.Core

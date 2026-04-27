import FX.Kernel.Conversion

/-!
# Subtyping — rule catalog and re-export

The kernel's subtyping check, `Term.subOrConv`, lives in
`FX/Kernel/Conversion.lean` because it is implemented on top of
`convEq` (structural equality is always subtyping, and the two
checks share the same whnf+match scaffolding).  This file is the
spec-side catalog of which Appendix H.9 `T-sub` composite rules
are landed and which remain pending, plus a re-export downstream
modules can use when their intent is specifically
"subtyping-aware check".

## Landed rules (task A7)

  * **U-cumul** (§31.4): `Type<u> <: Type<v>` when `u ≤ v` in
    the level preorder.  Landed alongside A11.
  * **Pi-subtype**: `Pi g A B <: Pi g A' B'` when grades are
    equal, `A' <: A` (domain contravariant), and `B <: B'`
    (codomain covariant).  Landed in A7.
  * **Sigma-subtype**: `Sigma g A B <: Sigma g A' B'` when
    grades are equal and both components are covariant
    (`A <: A'` and `B <: B'`).  Landed in A7.
  * **convEq fallback**: every convertible pair is trivially in
    the subtyping relation.  Landed since day one.

## Pending rules (deferred)

  * **Grade subsumption on binders** — strict grade equality is
    required on Pi/Sigma binders for now.  §6.2 allows
    `r ≤ s` to promote "value at r" to "expected s", but the
    direction on Pi BINDERS (how a function consumes its
    argument) is not self-evident from the spec text and
    interacts with Wood-Atkey context division in ways that
    need a worked-out example before landing.  A7-followup.
  * **Refinement weakening** (§10).  Blocks on first-class
    refinement predicates in `Term`.
  * **Effect-row inclusion** (§9.3).  Blocks on effect threading
    through typing (A12).
  * **Universe polymorphism subtyping**.  Blocks on A10.
  * **Ind / Coind positional variance**.  Would require
    recording variance metadata per parameter.

## Module-level re-export

Callers that want the subtyping check by its "intent" name can
import `FX.Kernel.Subtyping` and call `FX.Kernel.Term.sub`,
which aliases `Term.subOrConv`.  The implementation-site name
may change in a future refactor; the `Term.sub` alias here will
not.
-/

namespace FX.Kernel

namespace Term

/-- Subtyping-or-conversion check: returns `true` when a value
    typed `leftTerm` may be used where `rightTerm` is expected.
    Alias for `Term.subOrConv` in `Conversion.lean`.  See the
    module docstring above for the landed rule catalog. -/
def sub (fuel : Nat) (leftTerm rightTerm : Term)
    (globalEnv : GlobalEnv := {}) : Bool :=
  subOrConv fuel leftTerm rightTerm globalEnv

end Term

end FX.Kernel

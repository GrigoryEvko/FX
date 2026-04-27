import FX.Kernel.Grade.Provenance

/-!
# Provenance dimension tests

Covers `fx_design.md` §6.3 dim 8.

`Provenance` carries `List Provenance` recursively, so it does
not derive `DecidableEq` — tests use `rfl` for structural
equalities and constructor applications for `LessEq` proofs.

Key Phase-1 invariants exercised:

  * `unknown` is the top of the lattice (absorbing under `add`).
  * `add` on a pair of non-unknown provenances produces a
    two-element `aggregated` list — **no flattening, no
    idempotence** (see Provenance.lean docstring).  The kernel
    treats structurally-distinct-but-semantically-equivalent
    results as equal only via `LessEq`, not via `=`.
  * `mul = add`.
-/

namespace Tests.Kernel.Grade.Provenance

open FX.Kernel
open FX.Kernel.Provenance

/-! ## `add` — `unknown` absorbs -/

example : add unknown unknown = unknown := rfl
example : add unknown (source 0) = unknown := rfl
example : add (source 0) unknown = unknown := rfl
example : add (source 1) unknown = unknown := rfl
example : add unknown (derived (source 0)) = unknown := rfl
example : add (derived (source 0)) unknown = unknown := rfl
example : add unknown (aggregated []) = unknown := rfl
example : add (aggregated [source 0, source 1]) unknown = unknown := rfl

/-! ## `add` — two non-`unknown` operands always aggregate

This is the Phase-1 behavior: no equality test, no flattening.
`add x y = aggregated [x, y]` for every non-unknown pair. -/

example : add (source 0) (source 1) = aggregated [source 0, source 1] := rfl

example : add (source 42) (derived (source 7)) =
    aggregated [source 42, derived (source 7)] := rfl

example : add (derived (source 1)) (derived (source 2)) =
    aggregated [derived (source 1), derived (source 2)] := rfl

example : add (source 0) (aggregated [source 1, source 2]) =
    aggregated [source 0, aggregated [source 1, source 2]] := rfl

example : add (aggregated [source 0]) (aggregated [source 1]) =
    aggregated [aggregated [source 0], aggregated [source 1]] := rfl

/-! ## `add` is NOT idempotent on equal operands (by design)

Equal-origin inputs produce a two-element aggregate rather than
collapsing — `DecidableEq` is unavailable on `Provenance`, so
the kernel cannot cheaply compare operands.  An elaboration-
time normalization pass is expected to perform dedup. -/

example : add (source 0) (source 0) = aggregated [source 0, source 0] := rfl
example : add (source 5) (source 5) = aggregated [source 5, source 5] := rfl
example : add (derived (source 1)) (derived (source 1)) =
    aggregated [derived (source 1), derived (source 1)] := rfl

/-! ## `mul = add` -/

example : mul unknown (source 0) = unknown := rfl
example : mul (source 0) (source 1) = aggregated [source 0, source 1] := rfl
example : mul (derived (source 2)) unknown = unknown := rfl
example : ∀ a b : Provenance, mul a b = add a b := fun _ _ => rfl

/-! ## Absorption laws — `unknown` is the top -/

example : ∀ n : Nat, add unknown (source n) = unknown :=
  fun _ => rfl

example : ∀ n : Nat, add (source n) unknown = unknown :=
  fun _ => rfl

example : ∀ n : Nat, mul unknown (source n) = unknown :=
  fun _ => rfl

example : ∀ n : Nat, mul (source n) unknown = unknown :=
  fun _ => rfl

/-! ## Nested aggregates are not flattened

The kernel preserves nesting — a normalization pass at a higher
layer is responsible for flattening.  This test pins the
current behavior as an explicit spec. -/

example : add (aggregated [source 0, source 1])
              (aggregated [source 2, source 3]) =
    aggregated [ aggregated [source 0, source 1]
               , aggregated [source 2, source 3] ] := rfl

/-! ## `LessEq` — `unknown` is the top, proved via constructors -/

example : LessEq unknown unknown := LessEq.refl _
example : LessEq (source 0) unknown := LessEq.leTop _
example : LessEq (source 99) unknown := LessEq.leTop _
example : LessEq (derived (source 1)) unknown := LessEq.leTop _
example : LessEq (aggregated [source 0, source 1]) unknown := LessEq.leTop _
example : LessEq (aggregated []) unknown := LessEq.leTop _

/-! ## `LessEq` — reflexive on concrete values -/

example : LessEq (source 0) (source 0) := LessEq.refl _
example : LessEq (source 1) (source 1) := LessEq.refl _
example : LessEq (derived (source 3)) (derived (source 3)) := LessEq.refl _
example : LessEq (aggregated [source 0, source 1])
             (aggregated [source 0, source 1]) := LessEq.refl _

/-! ## `LessEq.trans` — all four legal combinations -/

-- refl ∘ refl
example : LessEq (source 0) (source 0) → LessEq (source 0) (source 0)
        → LessEq (source 0) (source 0) := fun _ _ => LessEq.refl _

-- refl ∘ leTop
example : LessEq (source 0) (source 0) → LessEq (source 0) unknown
        → LessEq (source 0) unknown := fun _ _ => LessEq.leTop _

-- leTop ∘ refl
example : LessEq (source 0) unknown → LessEq unknown unknown
        → LessEq (source 0) unknown := fun _ _ => LessEq.leTop _

-- leTop ∘ leTop
example : LessEq (source 0) unknown → LessEq unknown unknown
        → LessEq (source 0) unknown := fun _ _ => LessEq.leTop _

/-! ## `LessEq.trans` as a kernel theorem -/

example : ∀ x y z : Provenance, LessEq x y → LessEq y z → LessEq x z :=
  fun _ _ _ => LessEq.trans

/-! ## Universal `LessEq.leTop` -/

example : ∀ p : Provenance, LessEq p unknown := LessEq.leTop

/-! ## `unknown_add`, `add_unknown`, `unknown_mul`, `mul_unknown`
     lifted to theorem statements (kernel re-export). -/

example : ∀ x : Provenance, add unknown x = unknown := unknown_add
example : ∀ x : Provenance, add x unknown = unknown := add_unknown
example : ∀ x : Provenance, mul unknown x = unknown := unknown_mul
example : ∀ x : Provenance, mul x unknown = unknown := mul_unknown

end Tests.Kernel.Grade.Provenance

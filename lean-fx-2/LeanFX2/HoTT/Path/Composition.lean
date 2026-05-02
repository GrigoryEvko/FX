import LeanFX2.HoTT.J

/-! # HoTT/Path/Composition — meta-level path concatenation

Set-level (h-set) path concatenation built on Lean's `Eq`.  At
h-set, `Eq` is the canonical equality type; HOTT's path
distinctions (h-prop / h-set / h-groupoid / ...) collapse to
Lean Eq for v1.0.

## Why Lean Eq, not FX kernel `Ty.id`?

The kernel's `Term.idJ` is non-dependent — its motive is a
single `Ty`, not a function over endpoints.  Path composition
`Path A a b → Path A b c → Path A a c` needs a motive that
varies with the right endpoint.  With non-dep idJ, the
result type is fixed before the call, so we'd have to commit
to `Path A a c` upfront.  That works, but yields Path-level
operations that don't reduce by ι at the kernel level — they're
proven via `Step.par*` chains rather than definitional.

The internal-FX path operations land in v1.1 with dependent J
(see `HoTT/J.lean`'s "universe codes" plan).  For v1.0 we ship
the meta-level operations and a forthcoming bridge connecting
them to internal `Term.idJ` for closed motive types.

## What ships

* `Path A a b` — alias for `a = b` (Lean's Eq)
* `Path.refl  : Path A a a`
* `Path.trans : Path A a b → Path A b c → Path A a c`
* `Path.trans_assoc`, `Path.trans_refl_left`, `Path.trans_refl_right`

## Zero-axiom

Lean's `Eq.refl / Eq.trans` and pattern-matching via `subst`
on a path are propext-free.  The structural lemmas below are
all `rfl`-discharged once Lean's definitional equality unfolds
the underlying Eq operations.
-/

namespace LeanFX2

universe pathLevel

/-- Set-level path type — alias for Lean's `Eq`.  At h-set this
is the canonical equality; at higher truncation it would need
explicit treatment via `Ty.id` + path induction. -/
@[reducible] def Path {Carrier : Sort pathLevel}
    (leftEndpoint rightEndpoint : Carrier) : Prop :=
  leftEndpoint = rightEndpoint

/-- The reflexive path: every value is connected to itself. -/
@[reducible] def Path.refl {Carrier : Sort pathLevel}
    (someValue : Carrier) :
    Path someValue someValue :=
  Eq.refl someValue

/-- Path concatenation.  The operator analog of `Eq.trans`. -/
@[reducible] def Path.trans {Carrier : Sort pathLevel}
    {leftEndpoint middleEndpoint rightEndpoint : Carrier}
    (leftPath  : Path leftEndpoint  middleEndpoint)
    (rightPath : Path middleEndpoint rightEndpoint) :
    Path leftEndpoint rightEndpoint :=
  Eq.trans leftPath rightPath

/-- Associativity of path composition.  Definitional at h-set
since both sides reduce via `Eq.trans` associativity (which is
itself `rfl` once both paths are matched as `rfl`). -/
theorem Path.trans_assoc {Carrier : Sort pathLevel}
    {endpoint0 endpoint1 endpoint2 endpoint3 : Carrier}
    (leftPath  : Path endpoint0 endpoint1)
    (midPath   : Path endpoint1 endpoint2)
    (rightPath : Path endpoint2 endpoint3) :
    Path.trans (Path.trans leftPath midPath) rightPath
      = Path.trans leftPath (Path.trans midPath rightPath) := by
  cases leftPath
  cases midPath
  cases rightPath
  rfl

/-- Left identity: `refl · p = p`.  Definitional. -/
theorem Path.trans_refl_left {Carrier : Sort pathLevel}
    {leftEndpoint rightEndpoint : Carrier}
    (somePath : Path leftEndpoint rightEndpoint) :
    Path.trans (Path.refl leftEndpoint) somePath = somePath := by
  cases somePath
  rfl

/-- Right identity: `p · refl = p`.  Requires path induction
(case on the path), NOT definitional. -/
theorem Path.trans_refl_right {Carrier : Sort pathLevel}
    {leftEndpoint rightEndpoint : Carrier}
    (somePath : Path leftEndpoint rightEndpoint) :
    Path.trans somePath (Path.refl rightEndpoint) = somePath := by
  cases somePath
  rfl

/-! ## Computation lemmas — useful for unfolding in larger proofs -/

/-- `Path.refl` unfolds to `Eq.refl`. -/
theorem Path.refl_eq_eq_refl {Carrier : Sort pathLevel}
    (someValue : Carrier) :
    Path.refl someValue = Eq.refl someValue := rfl

/-- `Path.trans` unfolds to `Eq.trans`. -/
theorem Path.trans_eq_eq_trans {Carrier : Sort pathLevel}
    {leftEndpoint middleEndpoint rightEndpoint : Carrier}
    (leftPath  : Path leftEndpoint  middleEndpoint)
    (rightPath : Path middleEndpoint rightEndpoint) :
    Path.trans leftPath rightPath = Eq.trans leftPath rightPath := rfl

/-! ## Smoke samples -/

example : Path (1 : Nat) 1 := Path.refl 1
example : Path.trans (Path.refl (5 : Nat)) (Path.refl 5) = Path.refl 5 := rfl

end LeanFX2

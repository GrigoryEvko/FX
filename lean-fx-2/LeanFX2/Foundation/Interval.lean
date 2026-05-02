/-! # Foundation/Interval — cubical interval primitive

The interval type `Interval` with two endpoints `i0` and `i1`, plus three
algebraic operations: `opp` (involution), `meet` (∧, min), `join` (∨, max).

Used as the type-level domain of cubical "path lambdas":
`pathLam (body : Term ctx (... at I) ty)` where the body's free variable
ranges over the interval.

## Algebraic structure

`Interval` forms a **bounded distributive lattice with involution**:

* `(meet, i1)` is a commutative idempotent monoid (i1 is the meet identity)
* `(join, i0)` is a commutative idempotent monoid (i0 is the join identity)
* `meet` and `join` distribute mutually
* `opp` is the De Morgan involution: `opp (meet a b) = join (opp a) (opp b)`

This is the standard CCHM cubical interval algebra, with `i0`/`i1` the
two endpoints and `meet`/`join` the lattice operations.

## What this file ships (Day 1.1 of kernel-sprint.md)

* `Interval` inductive (2 ctors, decidable equality)
* `Interval.opp` involution
* `Interval.meet`, `Interval.join` lattice operations
* ~10 algebraic lemmas, all `cases <;> rfl` zero-axiom

## Downstream consumers

* `Foundation/Ty.lean` — `Ty.interval : Ty 0 scope` constructor
* `Foundation/RawTerm.lean` — `RawTerm.intervalLit`, `pathLam`, `pathApp`
* `Foundation/Cofib.lean` — boundary face cofibrations operate on intervals
* `Cubical/Path.lean` — path-as-function-from-interval
* `Cubical/Composition.lean` — comp/hcomp use cofibs on intervals
* `Cubical/Transport.lean` — transp at interval start point

## Pitfall awareness

* Every match must be a full enumeration (no wildcards) per
  `feedback_lean_match_propext_recipe`. Lean 4 v4.29.1's match compiler emits
  propext-using equation lemmas for wildcards over inductives.
* Decidable equality is auto-derivable for 2-ctor inductives without leaks.
-/

namespace LeanFX2

/-- The cubical interval: two endpoints. Operations (`opp`, `meet`, `join`)
are functions, not constructors — keeps the interval a true 2-element type. -/
inductive Interval : Type
  | i0 : Interval
  | i1 : Interval
  deriving DecidableEq, Repr

/-- De Morgan involution: 1 - i. -/
def Interval.opp : Interval → Interval
  | .i0 => .i1
  | .i1 => .i0

/-- Lattice meet (i ∧ j, min). -/
def Interval.meet : Interval → Interval → Interval
  | .i0, .i0 => .i0
  | .i0, .i1 => .i0
  | .i1, .i0 => .i0
  | .i1, .i1 => .i1

/-- Lattice join (i ∨ j, max). -/
def Interval.join : Interval → Interval → Interval
  | .i0, .i0 => .i0
  | .i0, .i1 => .i1
  | .i1, .i0 => .i1
  | .i1, .i1 => .i1

/-! ## Algebraic lemmas — all zero-axiom `cases <;> rfl` -/

/-- Involution: `opp (opp i) = i`. -/
theorem Interval.opp_opp (i : Interval) : i.opp.opp = i := by
  cases i <;> rfl

/-- Meet is commutative. -/
theorem Interval.meet_comm (i j : Interval) : i.meet j = j.meet i := by
  cases i <;> cases j <;> rfl

/-- Meet is associative. -/
theorem Interval.meet_assoc (i j k : Interval) :
    (i.meet j).meet k = i.meet (j.meet k) := by
  cases i <;> cases j <;> cases k <;> rfl

/-- Meet is idempotent: `i ∧ i = i`. -/
theorem Interval.meet_idem (i : Interval) : i.meet i = i := by
  cases i <;> rfl

/-- `i1` is the meet identity: `i ∧ i1 = i`. -/
theorem Interval.meet_idr (i : Interval) : i.meet .i1 = i := by
  cases i <;> rfl

/-- `i1` is the meet identity (left): `i1 ∧ i = i`. -/
theorem Interval.meet_idl (i : Interval) : (Interval.i1).meet i = i := by
  cases i <;> rfl

/-- Join is commutative. -/
theorem Interval.join_comm (i j : Interval) : i.join j = j.join i := by
  cases i <;> cases j <;> rfl

/-- Join is associative. -/
theorem Interval.join_assoc (i j k : Interval) :
    (i.join j).join k = i.join (j.join k) := by
  cases i <;> cases j <;> cases k <;> rfl

/-- Join is idempotent. -/
theorem Interval.join_idem (i : Interval) : i.join i = i := by
  cases i <;> rfl

/-- `i0` is the join identity: `i ∨ i0 = i`. -/
theorem Interval.join_idr (i : Interval) : i.join .i0 = i := by
  cases i <;> rfl

/-- `i0` is the join identity (left): `i0 ∨ i = i`. -/
theorem Interval.join_idl (i : Interval) : (Interval.i0).join i = i := by
  cases i <;> rfl

/-- Meet distributes over join. -/
theorem Interval.meet_join_distrib_l (i j k : Interval) :
    i.meet (j.join k) = (i.meet j).join (i.meet k) := by
  cases i <;> cases j <;> cases k <;> rfl

/-- Join distributes over meet. -/
theorem Interval.join_meet_distrib_l (i j k : Interval) :
    i.join (j.meet k) = (i.join j).meet (i.join k) := by
  cases i <;> cases j <;> cases k <;> rfl

/-- De Morgan: `opp (i ∧ j) = opp i ∨ opp j`. -/
theorem Interval.de_morgan_meet (i j : Interval) :
    (i.meet j).opp = i.opp.join j.opp := by
  cases i <;> cases j <;> rfl

/-- De Morgan: `opp (i ∨ j) = opp i ∧ opp j`. -/
theorem Interval.de_morgan_join (i j : Interval) :
    (i.join j).opp = i.opp.meet j.opp := by
  cases i <;> cases j <;> rfl

/-- Endpoints are distinct. -/
theorem Interval.i0_ne_i1 : (Interval.i0) ≠ Interval.i1 := by
  intro h
  cases h

end LeanFX2

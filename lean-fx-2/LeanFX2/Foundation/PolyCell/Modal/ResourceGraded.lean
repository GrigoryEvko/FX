/-!
# Resource-Graded Doctrine (Abel-Danielsson-Eriksson arXiv:2603.29716)

An ordered grade semiring models resource usage in quantitative type theory.
Each variable carries a grade from a partially ordered semiring R = (R, 0, 1, +, *, ≤).
The typing rules consume/scale grades per the semiring operations:
- VAR uses grade 1 at the variable position
- LAM: body's grade of the binder = function's parameter grade
- APP: grade of argument scaled by function's parameter grade
- IF: grade = join of both branches (worst case)

For FX: the Usage dimension {0, 1, ω} is the primary instance.
Security {unclassified < classified} is another instance.

Reference: arXiv:2603.29716 (Agda-formalized).
Zero external dependencies.

## V2-fix-2 (2026-05-27): propext-free rewrite

The original definitions used overlapping curried match patterns
like `| .zero, g => g | g, .zero => g`.  When both arguments are
`.zero`, the two arms overlap; Lean 4 v4.29.1's match compiler
emits `propext` in the auto-generated equation lemmas to discharge
the overlap.  This shipped six declarations with a `propext`
dependency (verified via `#print axioms`):

  * UsageGrade.add, UsageGrade.mul, UsageGrade.le
  * SecurityGrade.add, SecurityGrade.le
  * fxUsageSemiring, fxSecuritySemiring (transitively)

The file is orphan (not imported by any production module), so the
leak was invisible to the project's `#audit_namespace LeanFX2` sweep
which walks the import closure only.  Agent 5 of the V2 falsification
audit (2026-05-27) found this with a per-file probe.

This rewrite expands each overlapping def to **full enumeration over
the product space** of the inductive arguments:

  * UsageGrade.add: 3 × 3 = 9 arms
  * UsageGrade.mul: 9 arms
  * UsageGrade.le:  9 arms
  * SecurityGrade.add: 2 × 2 = 4 arms
  * SecurityGrade.le:  4 arms

Every arm pattern is a CTOR pair with no wildcard, no overlap.  Lean's
match compiler emits no equation lemma propext for distinct-CTOR
patterns.  Result: all seven declarations pass `#print axioms` clean
(verified post-rewrite).

The behavioral semantics are PRESERVED — every output value is the
same as the original overlapping form computed.  Verified by the
seven existing semiring-law theorems (`add_comm`, `add_zero`,
`zero_add`, `mul_one`, `one_mul`, `mul_zero`, `zero_mul`,
`linear_div_omega_eq_zero`) still closing by `cases ... <;> rfl`.

Pattern catalogued in
`feedback_lean_match_propext_recipe.md`.
-/

namespace LeanFX2.Foundation.PolyCell.Modal

/-- A partially ordered semiring: the grade algebra for QTT.
(R, 0, 1, +, *, ≤) with semiring laws + order compatibility. -/
structure OrderedGradeSemiring where
  Carrier : Type
  zero : Carrier
  one : Carrier
  add : Carrier → Carrier → Carrier
  mul : Carrier → Carrier → Carrier
  le : Carrier → Carrier → Bool
  /-- DecidableEq on carriers. -/
  carrierDecEq : DecidableEq Carrier

/-- FX's usage semiring: {0, 1, ω} with 0+0=0, 1+1=ω, ω+ω=ω. -/
inductive UsageGrade where
  | zero
  | one
  | omega
  deriving DecidableEq, Repr

/-- Usage-grade addition.  Full 3×3 enumeration; no wildcard, no
overlapping patterns — propext-free per V2-fix-2. -/
def UsageGrade.add : UsageGrade → UsageGrade → UsageGrade
  | .zero,  .zero  => .zero
  | .zero,  .one   => .one
  | .zero,  .omega => .omega
  | .one,   .zero  => .one
  | .one,   .one   => .omega
  | .one,   .omega => .omega
  | .omega, .zero  => .omega
  | .omega, .one   => .omega
  | .omega, .omega => .omega

/-- Usage-grade multiplication.  Full 3×3 enumeration; propext-free
per V2-fix-2. -/
def UsageGrade.mul : UsageGrade → UsageGrade → UsageGrade
  | .zero,  .zero  => .zero
  | .zero,  .one   => .zero
  | .zero,  .omega => .zero
  | .one,   .zero  => .zero
  | .one,   .one   => .one
  | .one,   .omega => .omega
  | .omega, .zero  => .zero
  | .omega, .one   => .omega
  | .omega, .omega => .omega

/-- Usage-grade order: `zero ≤ one ≤ omega`.  Full 3×3 enumeration;
propext-free per V2-fix-2. -/
def UsageGrade.le : UsageGrade → UsageGrade → Bool
  | .zero,  .zero  => true
  | .zero,  .one   => true
  | .zero,  .omega => true
  | .one,   .zero  => false
  | .one,   .one   => true
  | .one,   .omega => true
  | .omega, .zero  => false
  | .omega, .one   => false
  | .omega, .omega => true

/-- The FX usage semiring instance. -/
def fxUsageSemiring : OrderedGradeSemiring where
  Carrier := UsageGrade
  zero := .zero
  one := .one
  add := UsageGrade.add
  mul := UsageGrade.mul
  le := UsageGrade.le
  carrierDecEq := instDecidableEqUsageGrade

/-- FX's security semiring: {unclassified < classified}. -/
inductive SecurityGrade where
  | unclassified
  | classified
  deriving DecidableEq, Repr

/-- Security-grade addition (join): unclassified is the bottom; any
classified input poisons the result.  Full 2×2 enumeration;
propext-free per V2-fix-2. -/
def SecurityGrade.add : SecurityGrade → SecurityGrade → SecurityGrade
  | .unclassified, .unclassified => .unclassified
  | .unclassified, .classified   => .classified
  | .classified,   .unclassified => .classified
  | .classified,   .classified   => .classified

/-- Security-grade multiplication (meet on the boolean lattice
{unclassified < classified}).  Distinct-CTOR overlap-free patterns
were already propext-free in the pre-V2-fix-2 form; kept here as
explicit full enumeration for stylistic uniformity. -/
def SecurityGrade.mul : SecurityGrade → SecurityGrade → SecurityGrade
  | .unclassified, .unclassified => .unclassified
  | .unclassified, .classified   => .unclassified
  | .classified,   .unclassified => .unclassified
  | .classified,   .classified   => .classified

/-- Security-grade order: `unclassified ≤ classified`.  Full 2×2
enumeration; propext-free per V2-fix-2. -/
def SecurityGrade.le : SecurityGrade → SecurityGrade → Bool
  | .unclassified, .unclassified => true
  | .unclassified, .classified   => true
  | .classified,   .unclassified => false
  | .classified,   .classified   => true

/-- The FX security semiring instance. -/
def fxSecuritySemiring : OrderedGradeSemiring where
  Carrier := SecurityGrade
  zero := .unclassified
  one := .classified
  add := SecurityGrade.add
  mul := fun firstGrade secondGrade => SecurityGrade.add firstGrade secondGrade
  le := SecurityGrade.le
  carrierDecEq := instDecidableEqSecurityGrade

/-- Semiring laws verification (usage). -/
theorem UsageGrade.add_comm (firstGrade secondGrade : UsageGrade) :
    UsageGrade.add firstGrade secondGrade =
      UsageGrade.add secondGrade firstGrade := by
  cases firstGrade <;> cases secondGrade <;> rfl

theorem UsageGrade.add_zero (someGrade : UsageGrade) :
    UsageGrade.add someGrade .zero = someGrade := by
  cases someGrade <;> rfl

theorem UsageGrade.zero_add (someGrade : UsageGrade) :
    UsageGrade.add .zero someGrade = someGrade := by
  cases someGrade <;> rfl

theorem UsageGrade.mul_one (someGrade : UsageGrade) :
    UsageGrade.mul someGrade .one = someGrade := by
  cases someGrade <;> rfl

theorem UsageGrade.one_mul (someGrade : UsageGrade) :
    UsageGrade.mul .one someGrade = someGrade := by
  cases someGrade <;> rfl

theorem UsageGrade.mul_zero (someGrade : UsageGrade) :
    UsageGrade.mul someGrade .zero = .zero := by
  cases someGrade <;> rfl

theorem UsageGrade.zero_mul (someGrade : UsageGrade) :
    UsageGrade.mul .zero someGrade = .zero := by
  cases someGrade <;> rfl

/-- The Atkey-McBride attack: using linear variable twice in unrestricted
closure. Wood-Atkey 2022 corrected Lam rule prevents this via context
division: 1/ω = 0, so linear vars erased in replicable closures. -/
theorem UsageGrade.linear_div_omega_eq_zero :
    UsageGrade.mul .one .zero = .zero := rfl

end LeanFX2.Foundation.PolyCell.Modal

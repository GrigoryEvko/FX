import FX1Poly.Modal.OverflowLatticeDimension

/-! # FX1Poly/Modal/PrecisionOverflowCollision
    — the FIRST mechanized §6.8 CROSS-DIMENSION soundness collision: `decimal × overflow(wrap)`

The FX design's sharpest claim (§1.1, §6.8) is that the twenty-one graded dimensions are **NOT orthogonal**:
§6.8 catalogs the known cross-dimension soundness collisions (`classified × Fail`, `borrow × Async`,
`CT × Async`, `ghost × runtime`, `monotonic × concurrent`, `CT × Fail on secret`, **`decimal × overflow(wrap)`**,
`borrow × unscoped spawn`, `classified × async × session`).  The kernel already ships a §27.2 *known-unsoundness*
corpus (security / fractional-permission / session / CT / ML-value-restriction) — but §27.2 is a DIFFERENT
catalog: it collects single-dimension unsoundness *mechanisms* the type system must defend.  §6.8 is the
cross-dimension *collision* catalog — pairs of dimensions whose naive product is unsound.  This file opens the
§6.8-collision corpus with the cleanest algebraic member, **`decimal × overflow(wrap)`**.

## The collision

§3.1/§3.11: the default fractional type is `decimal`, which is **exact** — `0.1 + 0.2 == 0.3` is always true, no
rounding.  §6.3 Dim 16: `overflow(wrap)` grants wrapping (modular, `mod 2^n`) arithmetic on a fixed-width value.
These are jointly UNSATISFIABLE: wrapping silently produces a result that DIFFERS from the true mathematical value
whenever overflow occurs, so a value cannot be simultaneously graded `exact`-precision AND `wrap`-overflow.  The
collision is SPECIFIC to the non-exactness-preserving overflow modes: `exact` (arbitrary precision) and `trap`
(aborts on overflow rather than silently lie) DO preserve exactness, so they compose with exact precision; `wrap`
(silent modular) and `saturate` (silent clamp) do not.

This is the §6.8 thesis made concrete — the two dimensions cannot be chosen independently; the grade vector must
record a JOINT-consistency constraint that neither factor sees alone.

## What lands here (all zero-axiom)

  * `PrecisionGrade` — the precision dimension (§6.3 Dim 14) qualitative projection `{exactPrecision,
    inexactPrecision}` (the full dimension is the ULP-error semiring; `{exact, inexact}` is its
    collision-relevant 2-valued quotient).
  * `OverflowGrade.isExactnessPreserving` — does a shipped overflow mode never silently yield a wrong value?
    `exact`/`trap` ↦ `true`; `wrap`/`saturate`/`conflict` ↦ `false`.
  * `OverflowGrade.forcedPrecision` + `forcedPrecision_exactPrecision_iff_isExactnessPreserving` — the dual view
    (the minimum precision each mode forces) and its coherence with `isExactnessPreserving`.
  * `IsJointlyConsistent` — the §6.8 joint-consistency predicate: demanding exact precision is only consistent
    with an exactness-preserving overflow mode.
  * **`exactPrecisionCollidesWithWrapOverflow` (★)** + `exactPrecisionCollidesWithSaturateOverflow` — THE
    collision: exact precision is NOT jointly consistent with wrap (resp. saturate) overflow.
  * `exactPrecisionConsistentWithExactOverflow` / `…TrapOverflow` / `inexactPrecisionConsistentWithEveryOverflow`
    — the collision is SPECIFIC, not blanket: exact precision composes with the exactness-preserving modes, and
    inexact precision composes with everything (no exactness demand ⇒ no collision).
  * `exactPrecisionCollision_iff_notPreserving` / `isJointlyConsistent_iff` — the FULL decidable
    characterization: the exact-precision collision set is EXACTLY the non-exactness-preserving modes.

## Honest scope boundary

This models the COMBINE-time consistency constraint between the precision and overflow grades — the algebraic
heart of the §6.8 collision.  It does not wire `decimal`/`overflow` into the term-level grade-vector checker
(that is the dimension-vector engine's job, `GradeVector`); the joint-consistency predicate here IS the
constraint such a checker would enforce at a fixed-width arithmetic site.

## Zero-axiom verification

`PrecisionGrade` is a 2-element enum with derived `DecidableEq`; `isExactnessPreserving`/`forcedPrecision` are
pure-syntax `Bool`/enum tables; the collisions refute `consistent rfl : false = true` via `Bool.noConfusion`; the
positive consistencies are `fun _ => rfl` / `PrecisionGrade.noConfusion`; the characterizations are `cases` over
the 5 overflow modes / 2 precision grades with `rfl`/`noConfusion` leaves.  No `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- The PRECISION dimension (§6.3 Dim 14), qualitative projection: `exactPrecision` (0 ULP error, the bottom — the
`decimal` default) vs `inexactPrecision` (positive ULP error).  The full dimension tracks ULP error additively (a
semiring); this 2-valued quotient is what the `decimal × overflow(wrap)` collision turns on. -/
inductive PrecisionGrade where
  | exactPrecision
  | inexactPrecision
  deriving DecidableEq

/-- Does the overflow mode PRESERVE exactness — never silently yield a value differing from the true mathematical
result?  `exactGrade` (arbitrary precision) and `trapGrade` (aborts on overflow rather than lie) preserve it;
`wrapGrade` (silent modular `mod 2^n`), `saturateGrade` (silent clamp), and `conflictGrade` (the rejected mixing
state) do not. -/
def OverflowGrade.isExactnessPreserving : OverflowGrade → Bool
  | .exactGrade => true
  | .trapGrade => true
  | .wrapGrade => false
  | .saturateGrade => false
  | .conflictGrade => false

/-- The minimum precision each overflow mode FORCES: exactness-preserving modes admit `exactPrecision`; the silent
modes force `inexactPrecision`.  The dual view of `isExactnessPreserving`. -/
def OverflowGrade.forcedPrecision : OverflowGrade → PrecisionGrade
  | .exactGrade => .exactPrecision
  | .trapGrade => .exactPrecision
  | .wrapGrade => .inexactPrecision
  | .saturateGrade => .inexactPrecision
  | .conflictGrade => .inexactPrecision

/-- **Coherence of the two views**: a mode forces `exactPrecision` iff it is exactness-preserving. -/
theorem forcedPrecision_exactPrecision_iff_isExactnessPreserving (overflow : OverflowGrade) :
    overflow.forcedPrecision = PrecisionGrade.exactPrecision ↔ overflow.isExactnessPreserving = true := by
  cases overflow <;>
    first
      | exact ⟨fun _ => rfl, fun _ => rfl⟩
      | exact ⟨fun absurdEq => PrecisionGrade.noConfusion absurdEq, fun absurdEq => Bool.noConfusion absurdEq⟩

/-- The §6.8 JOINT-CONSISTENCY predicate for the (precision, overflow) grade pair: demanding `exactPrecision` is
only consistent with an overflow mode that preserves exactness.  When the precision demand is NOT exact, every
overflow mode is admissible (no constraint); the constraint bites exactly when exact precision is required. -/
def IsJointlyConsistent (precision : PrecisionGrade) (overflow : OverflowGrade) : Prop :=
  precision = PrecisionGrade.exactPrecision → overflow.isExactnessPreserving = true

/-- ★ **THE §6.8 COLLISION — `decimal × overflow(wrap)`.**  Exact precision (the `decimal` default) and wrapping
overflow are NOT jointly consistent: `wrap` silently produces a `mod 2^n` value differing from the true result, so
`isExactnessPreserving wrapGrade = false` refutes the exactness demand.  The first mechanized §6.8 cross-dimension
soundness collision: the precision and overflow dimensions cannot be chosen independently. -/
theorem exactPrecisionCollidesWithWrapOverflow :
    ¬ IsJointlyConsistent PrecisionGrade.exactPrecision OverflowGrade.wrapGrade :=
  fun consistent => Bool.noConfusion (consistent rfl)

/-- The `saturate` twin: exact precision also collides with saturating overflow (silent clamp is likewise
inexact). -/
theorem exactPrecisionCollidesWithSaturateOverflow :
    ¬ IsJointlyConsistent PrecisionGrade.exactPrecision OverflowGrade.saturateGrade :=
  fun consistent => Bool.noConfusion (consistent rfl)

/-- **The collision is SPECIFIC, not blanket (1/3): exact precision IS consistent with `exact` overflow.**
Arbitrary-precision arithmetic never overflows, so it preserves exactness. -/
theorem exactPrecisionConsistentWithExactOverflow :
    IsJointlyConsistent PrecisionGrade.exactPrecision OverflowGrade.exactGrade :=
  fun _ => rfl

/-- **Specific (2/3): exact precision IS consistent with `trap` overflow.**  Trapping aborts on overflow rather
than silently producing a wrong value, so within the representable range it is exact. -/
theorem exactPrecisionConsistentWithTrapOverflow :
    IsJointlyConsistent PrecisionGrade.exactPrecision OverflowGrade.trapGrade :=
  fun _ => rfl

/-- **Specific (3/3): inexact precision is consistent with EVERY overflow mode.**  When no exactness is demanded,
there is no constraint — the collision is purely a property of REQUIRING exact precision. -/
theorem inexactPrecisionConsistentWithEveryOverflow (overflow : OverflowGrade) :
    IsJointlyConsistent PrecisionGrade.inexactPrecision overflow :=
  fun absurdEq => PrecisionGrade.noConfusion absurdEq

/-- **Full characterization of the exact-precision collision set.**  Exact precision collides with an overflow
mode iff that mode is NOT exactness-preserving — i.e. the collision set is EXACTLY `{wrap, saturate, conflict}`. -/
theorem exactPrecisionCollision_iff_notPreserving (overflow : OverflowGrade) :
    ¬ IsJointlyConsistent PrecisionGrade.exactPrecision overflow ↔
      overflow.isExactnessPreserving = false := by
  constructor
  · intro collides
    cases hPreserve : overflow.isExactnessPreserving with
    | false => rfl
    | true => exact absurd (fun _ => hPreserve) collides
  · intro notPreserving consistent
    rw [consistent rfl] at notPreserving
    exact Bool.noConfusion notPreserving

/-- **The decidable joint-consistency law.**  `IsJointlyConsistent precision overflow` holds iff the precision
demand is inexact OR the overflow mode preserves exactness — the exhaustive characterization a grade-vector
checker would decide at a fixed-width arithmetic site. -/
theorem isJointlyConsistent_iff (precision : PrecisionGrade) (overflow : OverflowGrade) :
    IsJointlyConsistent precision overflow ↔
      (precision = PrecisionGrade.inexactPrecision ∨ overflow.isExactnessPreserving = true) := by
  constructor
  · intro consistent
    cases precision with
    | exactPrecision => exact Or.inr (consistent rfl)
    | inexactPrecision => exact Or.inl rfl
  · intro disjunct exactEq
    cases disjunct with
    | inl inexactEq => rw [exactEq] at inexactEq; exact PrecisionGrade.noConfusion inexactEq
    | inr preserving => exact preserving

end FX1Poly.Modal

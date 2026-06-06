import FX1Poly.Modal.ResourceGraded

/-! # FX1Poly/Modal/GradeVectorGeneric — the GENERIC grade-vector substrate (DIM5-2 + dims 6–21)

The usage dimension's `GradeVector` (`GradeVector.lean`, DIM2-2) is hardcoded to the usage carrier
`UsageGrade`.  But the §6.2 grade-vector algebra is the SAME for every dimension — it depends only on
the dimension's ordered semiring `R = (Carrier, 0, 1, +, *, ≤)`, never on which dimension it is.  This
file ships that algebra ONCE, generic over any `OrderedGradeSemiring`, with every law derived from the
`IsLawfulOrderedGradeSemiring` bundle (`ResourceGraded`).  The usage and security dimensions (and the
remaining 17) instantiate it for free — no per-dimension re-proof.

  * `GradeVectorOver R` — a cons-list of `R.Carrier`.  Unindexed (alignment with the scope-indexed
    `TypingContext` is by `length`), which keeps the binary pointwise `add` match propext-free: an
    indexed vector's two-scrutinee `add` must prove the `nil`/`cons` cross-cases impossible by index
    injectivity (the match compiler discharges that through `propext`); an unindexed list's `add` is a
    total match with no impossible arms.

  * `add` (pointwise `R.add` — context splitting / parallel use, §7.7), `scale` (pointwise `R.mul s` —
    the App rule's `r * p`, §6.2), `zero` (all-`R.zero` of a given length — additive identity), `single`
    (`grade` at a position, `R.zero` elsewhere — the var rule's vector), `tail` (drop the head — binder
    stripping).

The proved laws make `(GradeVectorOver R, add, zero)` a commutative monoid and `scale` a scalar action
distributing over both additions (a left SEMIMODULE over `R`), plus `IsPointwiseBelow` a partial order
under which `add`/`scale` are monotone, plus a Boolean decision procedure faithful to it.  Each law takes
the `IsLawfulOrderedGradeSemiring R` witness and rewrites with its fields pointwise; the dimension-specific
`contextDivide` (usage's Lam-capture residual, which needs a `div` op the bare semiring lacks) stays in the
per-dimension layer.

## Zero-axiom verification

`GradeVectorOver` is a plain (unindexed) inductive over the structure-field carrier `R.Carrier`; every
operation's match is total and propext-free; the laws close by `induction … <;>` + `simp only [<def>]` +
`rw [<lawful field>, restIH]` (the abstract carrier forces routing through the bundle rather than
`cases <;> rfl`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`
(probed with `#print axioms` before landing).  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- A grade vector generic over the ordered semiring `R`: one `R.Carrier` grade per binding, as a
cons-list.  Unindexed; alignment with the type context is by `length`. -/
inductive GradeVectorOver (R : OrderedGradeSemiring) where
  | nil : GradeVectorOver R
  | cons : R.Carrier → GradeVectorOver R → GradeVectorOver R

/-- The number of graded bindings. -/
def GradeVectorOver.length {R : OrderedGradeSemiring} : GradeVectorOver R → Nat
  | .nil => 0
  | .cons _ restGrades => restGrades.length + 1

/-- The all-`R.zero` grade vector of a given length: every binding erased.  Additive identity. -/
def GradeVectorOver.zero (R : OrderedGradeSemiring) : Nat → GradeVectorOver R
  | 0 => .nil
  | scope + 1 => .cons R.zero (GradeVectorOver.zero R scope)

/-- Pointwise addition — context splitting / parallel use (§7.7).  Truncates to the shorter operand. -/
def GradeVectorOver.add {R : OrderedGradeSemiring} :
    GradeVectorOver R → GradeVectorOver R → GradeVectorOver R
  | .nil, _ => .nil
  | .cons _ _, .nil => .nil
  | .cons firstHead firstRest, .cons secondHead secondRest =>
      .cons (R.add firstHead secondHead) (GradeVectorOver.add firstRest secondRest)

/-- Scalar multiplication: scale every binding's grade by `scaleGrade` (the App rule's `r * p`, §6.2). -/
def GradeVectorOver.scale {R : OrderedGradeSemiring} (scaleGrade : R.Carrier) :
    GradeVectorOver R → GradeVectorOver R
  | .nil => .nil
  | .cons headGrade restGrades =>
      .cons (R.mul scaleGrade headGrade) (GradeVectorOver.scale scaleGrade restGrades)

/-! ## Length coherence -/

/-- The zero vector at `scope` has exactly `scope` bindings. -/
theorem GradeVectorOver.zero_length (R : OrderedGradeSemiring) (scope : Nat) :
    (GradeVectorOver.zero R scope).length = scope := by
  induction scope with
  | zero => rfl
  | succ scope restIH => show (GradeVectorOver.zero R scope).length + 1 = scope + 1; rw [restIH]

/-- Scaling preserves the binding count. -/
theorem GradeVectorOver.scale_length {R : OrderedGradeSemiring} (scaleGrade : R.Carrier)
    (someVector : GradeVectorOver R) :
    (GradeVectorOver.scale scaleGrade someVector).length = someVector.length := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      show (GradeVectorOver.scale scaleGrade restGrades).length + 1 = restGrades.length + 1
      rw [restIH]

/-! ## Commutative-monoid laws for `(GradeVectorOver R, add, zero)` (need the lawful bundle) -/

/-- Pointwise addition is commutative (lifts `lawful.add_comm`; truncation is symmetric). -/
theorem GradeVectorOver.add_comm {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    (firstVector secondVector : GradeVectorOver R) :
    GradeVectorOver.add firstVector secondVector = GradeVectorOver.add secondVector firstVector := by
  induction firstVector generalizing secondVector with
  | nil => cases secondVector <;> rfl
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => rfl
      | cons secondHead secondRest =>
          simp only [GradeVectorOver.add]
          rw [lawful.add_comm firstHead secondHead, restIH secondRest]

/-- Pointwise addition is associative (lifts `lawful.add_assoc`). -/
theorem GradeVectorOver.add_assoc {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    (firstVector secondVector thirdVector : GradeVectorOver R) :
    GradeVectorOver.add (GradeVectorOver.add firstVector secondVector) thirdVector =
      GradeVectorOver.add firstVector (GradeVectorOver.add secondVector thirdVector) := by
  induction firstVector generalizing secondVector thirdVector with
  | nil => rfl
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => cases thirdVector <;> rfl
      | cons secondHead secondRest =>
          cases thirdVector with
          | nil => rfl
          | cons thirdHead thirdRest =>
              simp only [GradeVectorOver.add]
              rw [lawful.add_assoc firstHead secondHead thirdHead, restIH secondRest thirdRest]

/-- The zero vector (at the operand's own length) is a right identity for addition. -/
theorem GradeVectorOver.add_zero {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    (someVector : GradeVectorOver R) :
    GradeVectorOver.add someVector (GradeVectorOver.zero R someVector.length) = someVector := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      simp only [GradeVectorOver.length, GradeVectorOver.zero, GradeVectorOver.add]
      rw [lawful.add_zero headGrade, restIH]

/-- The zero vector (at the operand's own length) is a left identity for addition. -/
theorem GradeVectorOver.zero_add {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    (someVector : GradeVectorOver R) :
    GradeVectorOver.add (GradeVectorOver.zero R someVector.length) someVector = someVector := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      simp only [GradeVectorOver.length, GradeVectorOver.zero, GradeVectorOver.add]
      rw [lawful.zero_add headGrade, restIH]

/-! ## Scalar-action laws (the left-semimodule structure over `R`) -/

/-- Scaling by `R.zero` annihilates to the zero vector (`0 · p = 0`). -/
theorem GradeVectorOver.scale_zero_scalar {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) (someVector : GradeVectorOver R) :
    GradeVectorOver.scale R.zero someVector = GradeVectorOver.zero R someVector.length := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      simp only [GradeVectorOver.scale, GradeVectorOver.zero, GradeVectorOver.length]
      rw [lawful.zero_mul headGrade, restIH]

/-- Scaling by `R.one` is the identity (`1 · p = p`). -/
theorem GradeVectorOver.scale_one_scalar {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) (someVector : GradeVectorOver R) :
    GradeVectorOver.scale R.one someVector = someVector := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      simp only [GradeVectorOver.scale]
      rw [lawful.one_mul headGrade, restIH]

/-- A scalar distributes over a vector sum: `s · (p + q) = s · p + s · q`. -/
theorem GradeVectorOver.scale_add {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    (scaleGrade : R.Carrier) (firstVector secondVector : GradeVectorOver R) :
    GradeVectorOver.scale scaleGrade (GradeVectorOver.add firstVector secondVector) =
      GradeVectorOver.add (GradeVectorOver.scale scaleGrade firstVector)
        (GradeVectorOver.scale scaleGrade secondVector) := by
  induction firstVector generalizing secondVector with
  | nil => rfl
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => rfl
      | cons secondHead secondRest =>
          simp only [GradeVectorOver.add, GradeVectorOver.scale]
          rw [lawful.left_distrib scaleGrade firstHead secondHead, restIH secondRest]

/-- Scalar multiplication composes: `s · (t · p) = (s * t) · p`. -/
theorem GradeVectorOver.scale_scale {R : OrderedGradeSemiring} (lawful : IsLawfulOrderedGradeSemiring R)
    (firstScale secondScale : R.Carrier) (someVector : GradeVectorOver R) :
    GradeVectorOver.scale firstScale (GradeVectorOver.scale secondScale someVector) =
      GradeVectorOver.scale (R.mul firstScale secondScale) someVector := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      simp only [GradeVectorOver.scale]
      rw [lawful.mul_assoc firstScale secondScale headGrade, restIH]

/-- A scalar sum distributes over a vector: `(s + t) · p = s · p + t · p`. -/
theorem GradeVectorOver.scale_add_scalar {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) (firstScale secondScale : R.Carrier)
    (someVector : GradeVectorOver R) :
    GradeVectorOver.scale (R.add firstScale secondScale) someVector =
      GradeVectorOver.add (GradeVectorOver.scale firstScale someVector)
        (GradeVectorOver.scale secondScale someVector) := by
  induction someVector with
  | nil => rfl
  | cons headGrade restGrades restIH =>
      simp only [GradeVectorOver.scale, GradeVectorOver.add]
      rw [lawful.right_distrib firstScale secondScale headGrade, restIH]

/-! ## The element-level two-sided order lemma (derived from the one-sided bundle field)

`IsLawfulOrderedGradeSemiring` carries only the one-sided `add_le_add_left`; the two-sided
`a ≤ a' → b ≤ b' → a + b ≤ a' + b'` is DERIVED here (left-add `a` to `b≤b'`, then `add_comm` to reuse
`add_le_add_left` for the `a≤a'` leg, then `le_trans`).  Needed for vector `add` monotonicity. -/

/-- Two-sided additive monotonicity at the element level, derived from `add_le_add_left` + `add_comm`
+ `le_trans`. -/
theorem IsLawfulOrderedGradeSemiring.add_le_add {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) {firstGrade firstBound secondGrade secondBound : R.Carrier}
    (firstBelow : R.le firstGrade firstBound = true)
    (secondBelow : R.le secondGrade secondBound = true) :
    R.le (R.add firstGrade secondGrade) (R.add firstBound secondBound) = true := by
  have leftLeg : R.le (R.add firstGrade secondGrade) (R.add firstGrade secondBound) = true :=
    lawful.add_le_add_left firstGrade secondGrade secondBound secondBelow
  have rightLeg : R.le (R.add firstGrade secondBound) (R.add firstBound secondBound) = true := by
    rw [lawful.add_comm firstGrade secondBound, lawful.add_comm firstBound secondBound]
    exact lawful.add_le_add_left secondBound firstGrade firstBound firstBelow
  exact lawful.le_trans _ _ _ leftLeg rightLeg

/-! ## Grade-vector pointwise order: a partial order with `add`/`scale` monotone -/

/-- Pointwise order on equal-length grade vectors (via `R.le`).  Different lengths are incomparable
(`False`).  A local predicate (no global vector order needed). -/
def GradeVectorOver.IsPointwiseBelow {R : OrderedGradeSemiring} :
    GradeVectorOver R → GradeVectorOver R → Prop
  | .nil, .nil => True
  | .nil, .cons _ _ => False
  | .cons _ _, .nil => False
  | .cons firstHead firstRest, .cons secondHead secondRest =>
      (R.le firstHead secondHead = true) ∧
        GradeVectorOver.IsPointwiseBelow firstRest secondRest

/-- Reflexivity. -/
theorem GradeVectorOver.IsPointwiseBelow.refl {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) (someVector : GradeVectorOver R) :
    GradeVectorOver.IsPointwiseBelow someVector someVector := by
  induction someVector with
  | nil => exact True.intro
  | cons headGrade restGrades restIH => exact ⟨lawful.le_refl headGrade, restIH⟩

/-- Transitivity. -/
theorem GradeVectorOver.IsPointwiseBelow.trans {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R)
    {firstVector secondVector thirdVector : GradeVectorOver R}
    (firstBelowSecond : GradeVectorOver.IsPointwiseBelow firstVector secondVector)
    (secondBelowThird : GradeVectorOver.IsPointwiseBelow secondVector thirdVector) :
    GradeVectorOver.IsPointwiseBelow firstVector thirdVector := by
  induction firstVector generalizing secondVector thirdVector with
  | nil =>
      cases secondVector with
      | nil =>
          cases thirdVector with
          | nil => exact True.intro
          | cons _ _ => exact secondBelowThird.elim
      | cons _ _ => exact firstBelowSecond.elim
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => exact firstBelowSecond.elim
      | cons secondHead secondRest =>
          cases thirdVector with
          | nil => exact secondBelowThird.elim
          | cons thirdHead thirdRest =>
              exact ⟨lawful.le_trans _ _ _ firstBelowSecond.1 secondBelowThird.1,
                restIH firstBelowSecond.2 secondBelowThird.2⟩

/-- Antisymmetry — the pointwise order is a PARTIAL order. -/
theorem GradeVectorOver.IsPointwiseBelow.antisymm {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) {firstVector secondVector : GradeVectorOver R}
    (firstBelowSecond : GradeVectorOver.IsPointwiseBelow firstVector secondVector)
    (secondBelowFirst : GradeVectorOver.IsPointwiseBelow secondVector firstVector) :
    firstVector = secondVector := by
  induction firstVector generalizing secondVector with
  | nil =>
      cases secondVector with
      | nil => rfl
      | cons _ _ => exact firstBelowSecond.elim
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => exact firstBelowSecond.elim
      | cons secondHead secondRest =>
          have headEq : firstHead = secondHead :=
            lawful.le_antisymm _ _ firstBelowSecond.1 secondBelowFirst.1
          have restEq : firstRest = secondRest := restIH firstBelowSecond.2 secondBelowFirst.2
          rw [headEq, restEq]

/-- `scale` is monotone in the vector argument: `v ≤ w → scale b v ≤ scale b w`. -/
theorem GradeVectorOver.IsPointwiseBelow.scale_mono {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) (scaleGrade : R.Carrier)
    {firstVector secondVector : GradeVectorOver R}
    (below : GradeVectorOver.IsPointwiseBelow firstVector secondVector) :
    GradeVectorOver.IsPointwiseBelow (GradeVectorOver.scale scaleGrade firstVector)
      (GradeVectorOver.scale scaleGrade secondVector) := by
  induction firstVector generalizing secondVector with
  | nil =>
      cases secondVector with
      | nil => exact True.intro
      | cons _ _ => exact below.elim
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => exact below.elim
      | cons secondHead secondRest =>
          exact ⟨lawful.mul_le_mul_left scaleGrade firstHead secondHead below.1, restIH below.2⟩

/-- `add` is monotone in both vector arguments. -/
theorem GradeVectorOver.IsPointwiseBelow.add_mono {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R)
    {firstVector firstBound secondVector secondBound : GradeVectorOver R}
    (firstBelow : GradeVectorOver.IsPointwiseBelow firstVector firstBound)
    (secondBelow : GradeVectorOver.IsPointwiseBelow secondVector secondBound) :
    GradeVectorOver.IsPointwiseBelow (GradeVectorOver.add firstVector secondVector)
      (GradeVectorOver.add firstBound secondBound) := by
  induction firstVector generalizing firstBound secondVector secondBound with
  | nil =>
      cases firstBound with
      | nil => exact True.intro
      | cons _ _ => exact firstBelow.elim
  | cons firstHead firstRest restIH =>
      cases firstBound with
      | nil => exact firstBelow.elim
      | cons firstBoundHead firstBoundRest =>
          cases secondVector with
          | nil =>
              cases secondBound with
              | nil => exact True.intro
              | cons _ _ => exact secondBelow.elim
          | cons secondHead secondRest =>
              cases secondBound with
              | nil => exact secondBelow.elim
              | cons secondBoundHead secondBoundRest =>
                  exact ⟨lawful.add_le_add firstBelow.1 secondBelow.1,
                    restIH firstBelow.2 secondBelow.2⟩

/-! ## Decidable pointwise order — the computable grade-check decision procedure -/

/-- Computable pointwise-`≤` (truncating; `false` on length mismatch).  What a grade-checker runs. -/
def GradeVectorOver.isPointwiseBelowBool {R : OrderedGradeSemiring} :
    GradeVectorOver R → GradeVectorOver R → Bool
  | .nil, .nil => true
  | .nil, .cons _ _ => false
  | .cons _ _, .nil => false
  | .cons firstHead firstRest, .cons secondHead secondRest =>
      (R.le firstHead secondHead) && (GradeVectorOver.isPointwiseBelowBool firstRest secondRest)

/-- **Soundness + completeness of the Boolean check.**  Propext-free: explicit `Iff.intro`, `&&` split
by casing the head (rewriting WITH an `Iff` would pull `propext`). -/
theorem GradeVectorOver.isPointwiseBelowBool_correct {R : OrderedGradeSemiring}
    (firstVector secondVector : GradeVectorOver R) :
    GradeVectorOver.isPointwiseBelowBool firstVector secondVector = true ↔
      GradeVectorOver.IsPointwiseBelow firstVector secondVector := by
  induction firstVector generalizing secondVector with
  | nil =>
      cases secondVector with
      | nil => exact ⟨fun _ => True.intro, fun _ => rfl⟩
      | cons _ _ => exact ⟨fun contra => Bool.noConfusion contra, fun contra => contra.elim⟩
  | cons firstHead firstRest restIH =>
      cases secondVector with
      | nil => exact ⟨fun contra => Bool.noConfusion contra, fun contra => contra.elim⟩
      | cons secondHead secondRest =>
          show (R.le firstHead secondHead &&
                GradeVectorOver.isPointwiseBelowBool firstRest secondRest) = true ↔
              (R.le firstHead secondHead = true) ∧
                GradeVectorOver.IsPointwiseBelow firstRest secondRest
          constructor
          · intro hbool
            have headOk : R.le firstHead secondHead = true := by
              cases hle : R.le firstHead secondHead with
              | true => rfl
              | false => rw [hle] at hbool; exact Bool.noConfusion hbool
            have restBool : GradeVectorOver.isPointwiseBelowBool firstRest secondRest = true := by
              rw [headOk] at hbool; exact hbool
            exact ⟨headOk, (restIH secondRest).mp restBool⟩
          · intro hprop
            have restBool : GradeVectorOver.isPointwiseBelowBool firstRest secondRest = true :=
              (restIH secondRest).mpr hprop.2
            rw [hprop.1]
            exact restBool

/-! ## The var-rule vector and binder stripping (generic) -/

/-- A singleton grade vector of length `scope`: `grade` at `position`, `R.zero` elsewhere.  The var
rule's usage vector. -/
def GradeVectorOver.single (R : OrderedGradeSemiring) :
    (scope : Nat) → (position : Nat) → R.Carrier → GradeVectorOver R
  | 0, _, _ => .nil
  | scope + 1, 0, grade => .cons grade (GradeVectorOver.zero R scope)
  | scope + 1, pos + 1, grade => .cons R.zero (GradeVectorOver.single R scope pos grade)

/-- Drop the newest binding's grade: the outer-context grade of a binder from its body. -/
def GradeVectorOver.tail {R : OrderedGradeSemiring} : GradeVectorOver R → GradeVectorOver R
  | .nil => .nil
  | .cons _ restGrades => restGrades

/-- A singleton vector has exactly `scope` bindings. -/
theorem GradeVectorOver.single_length (R : OrderedGradeSemiring) (scope position : Nat)
    (grade : R.Carrier) : (GradeVectorOver.single R scope position grade).length = scope := by
  induction scope generalizing position with
  | zero => rfl
  | succ scope restIH =>
      cases position with
      | zero =>
          show (GradeVectorOver.zero R scope).length + 1 = scope + 1
          rw [GradeVectorOver.zero_length]
      | succ position =>
          show (GradeVectorOver.single R scope position grade).length + 1 = scope + 1
          rw [restIH]

/-! ## Per-dimension instantiation smokes — the substrate serves usage (DIM2) and security (DIM5) -/

/-- Usage-dimension instantiation: the generic semimodule law holds at `fxUsageSemiring`. -/
theorem usageGradeVector_scale_add (scaleGrade : UsageGrade)
    (firstVector secondVector : GradeVectorOver fxUsageSemiring) :
    GradeVectorOver.scale scaleGrade (GradeVectorOver.add firstVector secondVector) =
      GradeVectorOver.add (GradeVectorOver.scale scaleGrade firstVector)
        (GradeVectorOver.scale scaleGrade secondVector) :=
  GradeVectorOver.scale_add fxUsageSemiring_isLawful scaleGrade firstVector secondVector

/-- **DIM5-2: the security-dimension grade vector.**  The generic semimodule + order substrate
instantiated at `fxSecuritySemiring` (DIM5-1).  Security grade vectors form a left semimodule over the
security semiring with no per-dimension re-proof — the orthogonal-composition thesis at the grade-VECTOR
layer, for a second dimension. -/
theorem securityGradeVector_add_comm
    (firstVector secondVector : GradeVectorOver fxSecuritySemiring) :
    GradeVectorOver.add firstVector secondVector = GradeVectorOver.add secondVector firstVector :=
  GradeVectorOver.add_comm fxSecuritySemiring_isLawful firstVector secondVector

/-- DIM5-2: the security pointwise order is a genuine reflexive order (partial-order witness at
`fxSecuritySemiring`). -/
theorem securityGradeVector_below_refl (someVector : GradeVectorOver fxSecuritySemiring) :
    GradeVectorOver.IsPointwiseBelow someVector someVector :=
  GradeVectorOver.IsPointwiseBelow.refl fxSecuritySemiring_isLawful someVector

end FX1Poly.Modal

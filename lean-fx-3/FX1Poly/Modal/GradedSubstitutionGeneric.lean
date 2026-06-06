import FX1Poly.Modal.GradedWeakeningGeneric

/-! # FX1Poly/Modal/GradedSubstitutionGeneric — generic substInto grade-algebra (all graded dimensions)

The GRADE TRANSFORMATION that β performs — drop the substituted binding's grade, then add the argument
grades scaled by it — is the SAME for every dimension.  This file ships that grade-algebra ONCE,
generic over any `OrderedGradeSemiring`, on top of the generic vector.  It is the prerequisite for the generic substitution lemma; on its own it is
the "substitution grade-algebra" — how `removeAt` / `gradeAt` / `substInto` interact with the zero
vector, the var-rule singleton, scaling, and addition.

  * `removeTypeAtOver` / `GradeVectorOver.removeAt` — drop the type / grade at a de Bruijn cut.
  * `GradeVectorOver.gradeAt` — the grade at a cut (`R.zero` out of range).
  * `GradeVectorOver.substInto cutDepth argGrades bodyGrades` :=
    `add (removeAt cutDepth bodyGrades) (scale (gradeAt cutDepth bodyGrades) argGrades)` — exactly the
    grade β performs (the substituted variable's `gradeAt`-many uses each become a use of the argument).
  * **The λ-case identity** (`substInto_succ_cons`): under a binder the cut steps up, the argument is
    front-weakened (`cons R.zero`), and the head binder grade survives — `substInto (d+1) (cons 0 q)
    (cons bg p) = cons bg (substInto d q p)`.
  * **The var-case** (`substInto_single_self`/`_lt`/`_gt`): below the cut the singleton is unchanged,
    AT the cut it becomes the argument grades, above the cut it shifts down.
  * **The App-case** (`substInto_appGrade`): `substInto` distributes over `add (·) (scale binderGrade ·)`
    — the middle-four interchange (`add_interchange`) reorganizes the four summands.

The generic version diverges from the usage dimension's concrete proof exactly where the GRADE ARITHMETIC
must be COMPUTED: the usage `rfl`s rely on `UsageGrade.add zero zero` / `mul s zero` reducing; an abstract
`R.add R.zero R.zero` / `R.mul s R.zero` do not, so `substInto_succ_cons`, `gradeAt_scale`, `gradeAt_add`,
`add_interchange`, and the `substInto_single_*`/`substInto_appGrade` lemmas take an
`IsLawfulOrderedGradeSemiring` witness and route through its fields (and the generic vector laws).  The
`removeAt`/`gradeAt`/`lookup` structure that just relocates existing grades is lawfulness-free.

## Zero-axiom verification

The defs are structural recursion; the lemmas are structural inductions / pattern matches with
`Nat.noConfusion` / `Nat.not_succ_le_zero` on impossible arms (no `Nat.succ_ne_zero`, which pulls
`propext`); the lawful-dependent lemmas rewrite with the bundle fields and the generic vector laws.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega` (every declaration
probed with `#print axioms` before landing).  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- Remove the type at de Bruijn position `cutDepth` from a context. -/
def removeTypeAtOver {R : OrderedGradeSemiring} : Nat → List (GTypeOver R) → List (GTypeOver R)
  | 0, [] => []
  | 0, _ :: rest => rest
  | _ + 1, [] => []
  | depth + 1, headType :: restTypes => headType :: removeTypeAtOver depth restTypes

/-- Remove the grade at position `cutDepth` from a grade vector. -/
def GradeVectorOver.removeAt {R : OrderedGradeSemiring} : Nat → GradeVectorOver R → GradeVectorOver R
  | 0, .nil => .nil
  | 0, .cons _ rest => rest
  | _ + 1, .nil => .nil
  | depth + 1, .cons headGrade rest => .cons headGrade (GradeVectorOver.removeAt depth rest)

/-- The grade at position `cutDepth` (`R.zero` if out of range). -/
def GradeVectorOver.gradeAt {R : OrderedGradeSemiring} : Nat → GradeVectorOver R → R.Carrier
  | 0, .nil => R.zero
  | 0, .cons grade _ => grade
  | _ + 1, .nil => R.zero
  | depth + 1, .cons _ rest => GradeVectorOver.gradeAt depth rest

/-- The substituted grade vector: drop the cut binding's grade, add the argument grades scaled by it.
This is exactly the grade transformation β performs (the substituted variable's `gradeAt`-many uses
each become a use of the argument). -/
def GradeVectorOver.substInto {R : OrderedGradeSemiring} (cutDepth : Nat)
    (argGrades bodyGrades : GradeVectorOver R) : GradeVectorOver R :=
  GradeVectorOver.add (GradeVectorOver.removeAt cutDepth bodyGrades)
    (GradeVectorOver.scale (GradeVectorOver.gradeAt cutDepth bodyGrades) argGrades)

/-- The λ-case recursion: under a binder the cut steps up, the argument is front-weakened (`cons R.zero`),
and the head binder grade survives unchanged (needs `mul_zero` to clear the inserted slot and `add_zero`
to keep the binder grade). -/
theorem GradeVectorOver.substInto_succ_cons {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) (cutDepth : Nat) (binderGrade : R.Carrier)
    (argGrades outerGrades : GradeVectorOver R) :
    GradeVectorOver.substInto (cutDepth + 1) (GradeVectorOver.cons R.zero argGrades)
        (GradeVectorOver.cons binderGrade outerGrades) =
      GradeVectorOver.cons binderGrade (GradeVectorOver.substInto cutDepth argGrades outerGrades) := by
  show GradeVectorOver.add (GradeVectorOver.cons binderGrade
        (GradeVectorOver.removeAt cutDepth outerGrades))
      (GradeVectorOver.cons (R.mul (GradeVectorOver.gradeAt cutDepth outerGrades) R.zero)
        (GradeVectorOver.scale (GradeVectorOver.gradeAt cutDepth outerGrades) argGrades)) =
    GradeVectorOver.cons binderGrade
      (GradeVectorOver.add (GradeVectorOver.removeAt cutDepth outerGrades)
        (GradeVectorOver.scale (GradeVectorOver.gradeAt cutDepth outerGrades) argGrades))
  rw [lawful.mul_zero (GradeVectorOver.gradeAt cutDepth outerGrades)]
  show GradeVectorOver.cons (R.add binderGrade R.zero) _ = GradeVectorOver.cons binderGrade _
  rw [lawful.add_zero binderGrade]

/-! ## removeTypeAtOver: length + lookup -/

/-- Removal shrinks the context length by exactly one (when the cut is in range). -/
theorem removeTypeAtOver_length {R : OrderedGradeSemiring} :
    ∀ (cutDepth : Nat) (types : List (GTypeOver R)), cutDepth < types.length →
      (removeTypeAtOver cutDepth types).length + 1 = types.length
  | 0, [], lt => absurd lt (Nat.not_lt_zero _)
  | 0, _ :: _, _ => rfl
  | _ + 1, [], lt => absurd lt (Nat.not_lt_zero _)
  | depth + 1, _ :: restTypes, lt => by
      show (removeTypeAtOver depth restTypes).length + 1 + 1 = restTypes.length + 1
      rw [removeTypeAtOver_length depth restTypes (Nat.lt_of_succ_lt_succ lt)]

/-- Lookup below the cut is unaffected by removal. -/
theorem lookup_removeTypeAtOver_lt {R : OrderedGradeSemiring} :
    ∀ (cutDepth index : Nat) (types : List (GTypeOver R)), index < cutDepth →
      GTypeOver.lookup (removeTypeAtOver cutDepth types) index = GTypeOver.lookup types index
  | 0, _, _, lt => absurd lt (Nat.not_lt_zero _)
  | depth + 1, 0, types, _ => by cases types <;> rfl
  | depth + 1, index + 1, types, lt => by
      cases types with
      | nil => rfl
      | cons headType restTypes =>
          show GTypeOver.lookup (removeTypeAtOver depth restTypes) index =
            GTypeOver.lookup restTypes index
          exact lookup_removeTypeAtOver_lt depth index restTypes (Nat.lt_of_succ_lt_succ lt)

/-- Lookup at or above the cut shifts up by one across removal. -/
theorem lookup_removeTypeAtOver_ge {R : OrderedGradeSemiring} :
    ∀ (cutDepth index : Nat) (types : List (GTypeOver R)), cutDepth ≤ index →
      GTypeOver.lookup (removeTypeAtOver cutDepth types) index = GTypeOver.lookup types (index + 1)
  | 0, _, types, _ => by cases types <;> rfl
  | depth + 1, 0, _, le => absurd le (Nat.not_succ_le_zero _)
  | depth + 1, index + 1, types, le => by
      cases types with
      | nil => rfl
      | cons headType restTypes =>
          show GTypeOver.lookup (removeTypeAtOver depth restTypes) index =
            GTypeOver.lookup restTypes (index + 1)
          exact lookup_removeTypeAtOver_ge depth index restTypes (Nat.le_of_succ_le_succ le)

/-! ## gradeAt / removeAt on the zero vector -/

/-- The grade of the nil vector at any position is `R.zero`. -/
theorem GradeVectorOver.gradeAt_nil {R : OrderedGradeSemiring} (cutDepth : Nat) :
    GradeVectorOver.gradeAt cutDepth (GradeVectorOver.nil (R := R)) = R.zero := by
  cases cutDepth <;> rfl

/-- The grade of the zero vector at any position is `R.zero`. -/
theorem GradeVectorOver.gradeAt_zero {R : OrderedGradeSemiring} :
    ∀ (cutDepth scope : Nat),
      GradeVectorOver.gradeAt cutDepth (GradeVectorOver.zero R scope) = R.zero
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | _ + 1, 0 => rfl
  | cutDepth + 1, scope + 1 => GradeVectorOver.gradeAt_zero cutDepth scope

/-- Removing within the zero vector yields the one-shorter zero vector. -/
theorem GradeVectorOver.removeAt_zero {R : OrderedGradeSemiring} :
    ∀ (cutDepth scope : Nat), cutDepth ≤ scope →
      GradeVectorOver.removeAt cutDepth (GradeVectorOver.zero R (scope + 1)) =
        GradeVectorOver.zero R scope
  | 0, _, _ => rfl
  | _cutDepth + 1, 0, le => absurd le (Nat.not_succ_le_zero _)
  | cutDepth + 1, scope + 1, le =>
      congrArg (GradeVectorOver.cons R.zero)
        (GradeVectorOver.removeAt_zero cutDepth scope (Nat.le_of_succ_le_succ le))

/-! ## gradeAt / removeAt versus the var-rule singleton -/

/-- The grade of a singleton at its OWN marked position is the marked grade. -/
theorem GradeVectorOver.gradeAt_single_self {R : OrderedGradeSemiring} :
    ∀ (cutDepth scope : Nat) (grade : R.Carrier), cutDepth < scope →
      GradeVectorOver.gradeAt cutDepth (GradeVectorOver.single R scope cutDepth grade) = grade
  | 0, scope, grade, lt => by cases scope with
      | zero => exact absurd lt (Nat.not_lt_zero _)
      | succ _ => rfl
  | cutDepth + 1, scope, grade, lt => by cases scope with
      | zero => exact absurd lt (Nat.not_lt_zero _)
      | succ restScope =>
          show GradeVectorOver.gradeAt cutDepth (GradeVectorOver.single R restScope cutDepth grade) =
            grade
          exact GradeVectorOver.gradeAt_single_self cutDepth restScope grade
            (Nat.lt_of_succ_lt_succ lt)

/-- The grade of a singleton at an UNMARKED position is `R.zero`. -/
theorem GradeVectorOver.gradeAt_single_ne {R : OrderedGradeSemiring} :
    ∀ (cutDepth index scope : Nat) (grade : R.Carrier), index ≠ cutDepth →
      GradeVectorOver.gradeAt cutDepth (GradeVectorOver.single R scope index grade) = R.zero
  | cutDepth, _, 0, _, _ => GradeVectorOver.gradeAt_nil cutDepth
  | 0, 0, _ + 1, _, ne => (ne rfl).elim
  | 0, _ + 1, _ + 1, _, _ => rfl
  | cutDepth + 1, 0, scope + 1, _, _ => GradeVectorOver.gradeAt_zero cutDepth scope
  | cutDepth + 1, index + 1, scope + 1, grade, ne =>
      GradeVectorOver.gradeAt_single_ne cutDepth index scope grade (fun eq => ne (congrArg (· + 1) eq))

/-- Removing a singleton's OWN marked position yields the zero vector. -/
theorem GradeVectorOver.removeAt_single_self {R : OrderedGradeSemiring} :
    ∀ (cutDepth resultLen : Nat) (grade : R.Carrier), cutDepth ≤ resultLen →
      GradeVectorOver.removeAt cutDepth (GradeVectorOver.single R (resultLen + 1) cutDepth grade) =
        GradeVectorOver.zero R resultLen
  | 0, _, _, _ => rfl
  | _cutDepth + 1, 0, _, le => absurd le (Nat.not_succ_le_zero _)
  | cutDepth + 1, resultLen + 1, grade, le =>
      congrArg (GradeVectorOver.cons R.zero)
        (GradeVectorOver.removeAt_single_self cutDepth resultLen grade (Nat.le_of_succ_le_succ le))

/-- Removing ABOVE a singleton's marked position leaves the singleton (marked position unchanged). -/
theorem GradeVectorOver.removeAt_single_lt {R : OrderedGradeSemiring} :
    ∀ (cutDepth index resultLen : Nat) (grade : R.Carrier),
      index < cutDepth → cutDepth ≤ resultLen →
      GradeVectorOver.removeAt cutDepth (GradeVectorOver.single R (resultLen + 1) index grade) =
        GradeVectorOver.single R resultLen index grade
  | 0, _, _, _, idxLt, _ => absurd idxLt (Nat.not_lt_zero _)
  | cutDepth + 1, 0, resultLen, grade, _, cutLe => by
      cases resultLen with
      | zero => exact absurd cutLe (Nat.not_succ_le_zero _)
      | succ rl =>
          exact congrArg (GradeVectorOver.cons grade)
            (GradeVectorOver.removeAt_zero cutDepth rl (Nat.le_of_succ_le_succ cutLe))
  | cutDepth + 1, index + 1, resultLen, grade, idxLt, cutLe => by
      cases resultLen with
      | zero => exact absurd cutLe (Nat.not_succ_le_zero _)
      | succ rl =>
          exact congrArg (GradeVectorOver.cons R.zero)
            (GradeVectorOver.removeAt_single_lt cutDepth index rl grade
              (Nat.lt_of_succ_lt_succ idxLt) (Nat.le_of_succ_le_succ cutLe))

/-- Removing BELOW a singleton's marked position shifts the marked position down by one. -/
theorem GradeVectorOver.removeAt_single_gt {R : OrderedGradeSemiring} :
    ∀ (cutDepth idx resultLen : Nat) (grade : R.Carrier), cutDepth ≤ idx → idx < resultLen →
      GradeVectorOver.removeAt cutDepth (GradeVectorOver.single R (resultLen + 1) (idx + 1) grade) =
        GradeVectorOver.single R resultLen idx grade
  | 0, _, _, _, _, _ => rfl
  | cutDepth + 1, 0, _, _, cutLe, _ => absurd cutLe (Nat.not_succ_le_zero _)
  | cutDepth + 1, idx + 1, resultLen, grade, cutLe, idxLt => by
      cases resultLen with
      | zero => exact absurd idxLt (Nat.not_lt_zero _)
      | succ rl =>
          exact congrArg (GradeVectorOver.cons R.zero)
            (GradeVectorOver.removeAt_single_gt cutDepth idx rl grade (Nat.le_of_succ_le_succ cutLe)
              (Nat.lt_of_succ_lt_succ idxLt))

/-! ## removeAt / gradeAt distribute over add / scale (for the App case) -/

/-- Removal distributes over pointwise add (equal-length operands). -/
theorem GradeVectorOver.removeAt_add {R : OrderedGradeSemiring} :
    ∀ (cutDepth : Nat) (firstVector secondVector : GradeVectorOver R),
      firstVector.length = secondVector.length →
      GradeVectorOver.removeAt cutDepth (GradeVectorOver.add firstVector secondVector) =
        GradeVectorOver.add (GradeVectorOver.removeAt cutDepth firstVector)
          (GradeVectorOver.removeAt cutDepth secondVector)
  | 0, .nil, .nil, _ => rfl
  | 0, .nil, .cons _ _, h => Nat.noConfusion h
  | 0, .cons _ _, .nil, h => Nat.noConfusion h
  | 0, .cons _ _, .cons _ _, _ => rfl
  | _ + 1, .nil, .nil, _ => rfl
  | _ + 1, .nil, .cons _ _, h => Nat.noConfusion h
  | _ + 1, .cons _ _, .nil, h => Nat.noConfusion h
  | cutDepth + 1, .cons vh vr, .cons wh wr, h =>
      congrArg (GradeVectorOver.cons (R.add vh wh))
        (GradeVectorOver.removeAt_add cutDepth vr wr (Nat.succ.inj h))

/-- Removal distributes over scaling. -/
theorem GradeVectorOver.removeAt_scale {R : OrderedGradeSemiring} :
    ∀ (cutDepth : Nat) (scaleGrade : R.Carrier) (someVector : GradeVectorOver R),
      GradeVectorOver.removeAt cutDepth (GradeVectorOver.scale scaleGrade someVector) =
        GradeVectorOver.scale scaleGrade (GradeVectorOver.removeAt cutDepth someVector)
  | 0, _, .nil => rfl
  | 0, _, .cons _ _ => rfl
  | _ + 1, _, .nil => rfl
  | cutDepth + 1, scaleGrade, .cons vh vr =>
      congrArg (GradeVectorOver.cons (R.mul scaleGrade vh))
        (GradeVectorOver.removeAt_scale cutDepth scaleGrade vr)

/-- The grade at a cut of a scaled vector is the scaled grade (out-of-range arms need `mul_zero`). -/
theorem GradeVectorOver.gradeAt_scale {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) :
    ∀ (cutDepth : Nat) (scaleGrade : R.Carrier) (someVector : GradeVectorOver R),
      GradeVectorOver.gradeAt cutDepth (GradeVectorOver.scale scaleGrade someVector) =
        R.mul scaleGrade (GradeVectorOver.gradeAt cutDepth someVector)
  | 0, scaleGrade, .nil => (lawful.mul_zero scaleGrade).symm
  | 0, _, .cons _ _ => rfl
  | _ + 1, scaleGrade, .nil => (lawful.mul_zero scaleGrade).symm
  | cutDepth + 1, scaleGrade, .cons _ vr => GradeVectorOver.gradeAt_scale lawful cutDepth scaleGrade vr

/-- The grade at a cut of a sum is the sum of grades (out-of-range arms need `zero_add`). -/
theorem GradeVectorOver.gradeAt_add {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) :
    ∀ (cutDepth : Nat) (firstVector secondVector : GradeVectorOver R),
      firstVector.length = secondVector.length →
      GradeVectorOver.gradeAt cutDepth (GradeVectorOver.add firstVector secondVector) =
        R.add (GradeVectorOver.gradeAt cutDepth firstVector)
          (GradeVectorOver.gradeAt cutDepth secondVector)
  | 0, .nil, .nil, _ => (lawful.zero_add R.zero).symm
  | 0, .cons _ _, .nil, h => Nat.noConfusion h
  | 0, .nil, .cons _ _, h => Nat.noConfusion h
  | 0, .cons _ _, .cons _ _, _ => rfl
  | _ + 1, .nil, .nil, _ => (lawful.zero_add R.zero).symm
  | _ + 1, .cons _ _, .nil, h => Nat.noConfusion h
  | _ + 1, .nil, .cons _ _, h => Nat.noConfusion h
  | cutDepth + 1, .cons _ vr, .cons _ wr, h =>
      GradeVectorOver.gradeAt_add lawful cutDepth vr wr (Nat.succ.inj h)

/-- Commutative-monoid middle-four interchange — the App-case reassociation. -/
theorem GradeVectorOver.add_interchange {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R)
    (firstVector secondVector thirdVector fourthVector : GradeVectorOver R) :
    GradeVectorOver.add (GradeVectorOver.add firstVector secondVector)
        (GradeVectorOver.add thirdVector fourthVector) =
      GradeVectorOver.add (GradeVectorOver.add firstVector thirdVector)
        (GradeVectorOver.add secondVector fourthVector) := by
  rw [GradeVectorOver.add_assoc lawful firstVector secondVector
        (GradeVectorOver.add thirdVector fourthVector),
      ← GradeVectorOver.add_assoc lawful secondVector thirdVector fourthVector,
      GradeVectorOver.add_comm lawful secondVector thirdVector,
      GradeVectorOver.add_assoc lawful thirdVector secondVector fourthVector,
      ← GradeVectorOver.add_assoc lawful firstVector thirdVector
        (GradeVectorOver.add secondVector fourthVector)]

/-! ## substInto on a singleton (the var case) and over an App grade -/

/-- The var AT the cut: substituting yields the argument grades (`scale R.one · = ·`, `add 0 · = ·`). -/
theorem GradeVectorOver.substInto_single_self {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) (cutDepth resultLen : Nat)
    (argGrades : GradeVectorOver R) (cutLe : cutDepth ≤ resultLen)
    (argLen : argGrades.length = resultLen) :
    GradeVectorOver.substInto cutDepth argGrades
        (GradeVectorOver.single R (resultLen + 1) cutDepth R.one) = argGrades := by
  show GradeVectorOver.add
      (GradeVectorOver.removeAt cutDepth (GradeVectorOver.single R (resultLen + 1) cutDepth R.one))
      (GradeVectorOver.scale (GradeVectorOver.gradeAt cutDepth
        (GradeVectorOver.single R (resultLen + 1) cutDepth R.one)) argGrades) = argGrades
  rw [GradeVectorOver.removeAt_single_self cutDepth resultLen R.one cutLe,
      GradeVectorOver.gradeAt_single_self cutDepth (resultLen + 1) R.one (Nat.lt_succ_of_le cutLe),
      GradeVectorOver.scale_one_scalar lawful, ← argLen]
  exact GradeVectorOver.zero_add lawful argGrades

/-- The var BELOW the cut: substituting leaves the singleton unchanged (its grade is `0`, so the scaled
argument vanishes). -/
theorem GradeVectorOver.substInto_single_lt {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) (cutDepth index resultLen : Nat)
    (argGrades : GradeVectorOver R) (idxLt : index < cutDepth) (cutLe : cutDepth ≤ resultLen)
    (argLen : argGrades.length = resultLen) :
    GradeVectorOver.substInto cutDepth argGrades
        (GradeVectorOver.single R (resultLen + 1) index R.one) =
      GradeVectorOver.single R resultLen index R.one := by
  show GradeVectorOver.add
      (GradeVectorOver.removeAt cutDepth (GradeVectorOver.single R (resultLen + 1) index R.one))
      (GradeVectorOver.scale (GradeVectorOver.gradeAt cutDepth
        (GradeVectorOver.single R (resultLen + 1) index R.one)) argGrades) = _
  rw [GradeVectorOver.removeAt_single_lt cutDepth index resultLen R.one idxLt cutLe,
      GradeVectorOver.gradeAt_single_ne cutDepth index (resultLen + 1) R.one (Nat.ne_of_lt idxLt),
      GradeVectorOver.scale_zero_scalar lawful, argLen]
  have h := GradeVectorOver.add_zero lawful (GradeVectorOver.single R resultLen index R.one)
  rw [GradeVectorOver.single_length] at h
  exact h

/-- The var ABOVE the cut: substituting shifts the marked position down by one (grade `0`, argument
vanishes). -/
theorem GradeVectorOver.substInto_single_gt {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) (cutDepth idx resultLen : Nat)
    (argGrades : GradeVectorOver R) (cutLe : cutDepth ≤ idx) (idxLt : idx < resultLen)
    (argLen : argGrades.length = resultLen) :
    GradeVectorOver.substInto cutDepth argGrades
        (GradeVectorOver.single R (resultLen + 1) (idx + 1) R.one) =
      GradeVectorOver.single R resultLen idx R.one := by
  show GradeVectorOver.add
      (GradeVectorOver.removeAt cutDepth (GradeVectorOver.single R (resultLen + 1) (idx + 1) R.one))
      (GradeVectorOver.scale (GradeVectorOver.gradeAt cutDepth
        (GradeVectorOver.single R (resultLen + 1) (idx + 1) R.one)) argGrades) = _
  rw [GradeVectorOver.removeAt_single_gt cutDepth idx resultLen R.one cutLe idxLt,
      GradeVectorOver.gradeAt_single_ne cutDepth (idx + 1) (resultLen + 1) R.one
        (Nat.ne_of_lt (Nat.lt_succ_of_le cutLe)).symm,
      GradeVectorOver.scale_zero_scalar lawful, argLen]
  have h := GradeVectorOver.add_zero lawful (GradeVectorOver.single R resultLen idx R.one)
  rw [GradeVectorOver.single_length] at h
  exact h

/-- **The App-case grade identity**: `substInto` distributes over the App-scaled grade sum
`add (·) (scale binderGrade ·)`, via `removeAt`/`gradeAt` distribution + the middle-four interchange. -/
theorem GradeVectorOver.substInto_appGrade {R : OrderedGradeSemiring}
    (lawful : IsLawfulOrderedGradeSemiring R) (cutDepth : Nat) (binderGrade : R.Carrier)
    (argGrades functionGrades argumentGrades : GradeVectorOver R)
    (lenEq : functionGrades.length = argumentGrades.length) :
    GradeVectorOver.substInto cutDepth argGrades
        (GradeVectorOver.add functionGrades (GradeVectorOver.scale binderGrade argumentGrades)) =
      GradeVectorOver.add (GradeVectorOver.substInto cutDepth argGrades functionGrades)
        (GradeVectorOver.scale binderGrade
          (GradeVectorOver.substInto cutDepth argGrades argumentGrades)) := by
  have scaleLen : functionGrades.length =
      (GradeVectorOver.scale binderGrade argumentGrades).length := by
    rw [GradeVectorOver.scale_length]; exact lenEq
  simp only [GradeVectorOver.substInto]
  rw [GradeVectorOver.removeAt_add cutDepth functionGrades
        (GradeVectorOver.scale binderGrade argumentGrades) scaleLen,
      GradeVectorOver.removeAt_scale,
      GradeVectorOver.gradeAt_add lawful cutDepth functionGrades
        (GradeVectorOver.scale binderGrade argumentGrades) scaleLen,
      GradeVectorOver.gradeAt_scale lawful, GradeVectorOver.scale_add_scalar lawful,
      ← GradeVectorOver.scale_scale lawful, GradeVectorOver.scale_add lawful]
  exact GradeVectorOver.add_interchange lawful
    (GradeVectorOver.removeAt cutDepth functionGrades)
    (GradeVectorOver.scale binderGrade (GradeVectorOver.removeAt cutDepth argumentGrades))
    (GradeVectorOver.scale (GradeVectorOver.gradeAt cutDepth functionGrades) argGrades)
    (GradeVectorOver.scale binderGrade
      (GradeVectorOver.scale (GradeVectorOver.gradeAt cutDepth argumentGrades) argGrades))

end FX1Poly.Modal

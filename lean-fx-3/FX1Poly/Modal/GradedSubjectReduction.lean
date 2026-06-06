import FX1Poly.Modal.GradedTypingMetatheory

/-! # FX1Poly/Modal/GradedSubjectReduction — β subject reduction for the graded judgment (DIM2-3)

`UsageDiscipline.usage_check_fails_subject_reduction` showed the bare occurrence check is NOT
subject-reduction-closed: `(λx. x x) g` is well-graded yet its β-reduct `g g` is ill-graded.  This
file proves the type-coupled `HasUsage` judgment (`GradedTyping`) IS subject-reduction-closed, with
the grade vector preserved EXACTLY — the soundness payoff that motivates the corrected Wood/Atkey
discipline (§6.2, §27.1).

The result grade of substituting an argument (grades `q`) for the variable at `cutDepth` in a body
(grades `p`) is `removeAt cutDepth p + (gradeAt cutDepth p) · q` — drop the substituted binding's
grade, add the argument grades scaled by how many times that binding was used.  Packaged as
`GradeVector.substInto`.  Two facts make the induction go:

  * **λ-case** (`substInto_succ_cons`): under a binder the cut steps to `cutDepth + 1` with the
    argument front-weakened (`hasUsage_weakening` at cut 0, inserting a ghost `0`); the grade
    identity `substInto (d+1) (cons 0 q) (cons bg p) = cons bg (substInto d q p)` threads it.

  * **App-case** (`substInto_appGrade`): `substInto` distributes over `add (·) (scale binderGrade ·)`
    — `removeAt`/`gradeAt` distribute over `add`/`scale`, then a commutative-monoid middle-four
    interchange (`add_interchange`) reassociates the four resulting summands.

The **var-case** splits below / at / above the cut (`substInto_single_lt`/`_self`/`_gt`): below the
cut the grade is unchanged, at the cut the result is exactly the argument's grades (`scale 1 q`),
above the cut the marked position shifts down by one.

`hasUsage_betaPreservation` is the headline: `(λ.body) arg ↝ body[0 := arg]` preserves typing and
the exact grade vector — invert App + Lam, then the substitution lemma at cut 0, where
`substInto 0 q (cons binderGrade functionGrades)` is definitionally `functionGrades + binderGrade · q`
= the redex's grade.

## Zero-axiom verification

Every declaration is gated in `FX1PolyAudit/AuditModal.lean`.  Same trap-avoidance as
`GradedTypingMetatheory` (`Nat.succ_ne_zero`/`Nat.ne_of_lt` not field projections, `congrArg` leaves,
`nomatch` for the empty-context lookup) plus: the `Nat.sub` reduct `predIndex + 1 - 1` is stated
explicitly in the var>cut `show` so the rewrite closes syntactically; the App-grade distributes via
`simp only [GradeVector.substInto]` then a fixed `rw` chain.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.
-/

namespace FX1Poly.Modal

/-! ## Positional removal ops (mirror the insertion ops of `GradedTypingMetatheory`) -/

/-- Remove the type at de Bruijn position `cutDepth` from a context. -/
def removeTypeAt : Nat → List GType → List GType
  | 0, [] => []
  | 0, _ :: rest => rest
  | _ + 1, [] => []
  | depth + 1, headType :: restTypes => headType :: removeTypeAt depth restTypes

/-- Remove the grade at position `cutDepth` from a grade vector. -/
def GradeVector.removeAt : Nat → GradeVector → GradeVector
  | 0, .nil => .nil
  | 0, .cons _ rest => rest
  | _ + 1, .nil => .nil
  | depth + 1, .cons headGrade rest => .cons headGrade (GradeVector.removeAt depth rest)

/-- The grade at position `cutDepth` (`0` if out of range). -/
def GradeVector.gradeAt : Nat → GradeVector → UsageGrade
  | 0, .nil => UsageGrade.zero
  | 0, .cons grade _ => grade
  | _ + 1, .nil => UsageGrade.zero
  | depth + 1, .cons _ rest => GradeVector.gradeAt depth rest

/-- The substituted grade vector: drop the cut binding's grade, add the argument grades scaled by it.
This is exactly the grade transformation β performs (the substituted variable's `gradeAt`-many uses
each become a use of the argument). -/
def GradeVector.substInto (cutDepth : Nat) (argGrades bodyGrades : GradeVector) : GradeVector :=
  GradeVector.add (GradeVector.removeAt cutDepth bodyGrades)
    (GradeVector.scale (GradeVector.gradeAt cutDepth bodyGrades) argGrades)

/-- The λ-case recursion: under a binder the cut steps up, the argument is front-weakened (cons 0),
and the head binder grade survives unchanged. -/
theorem substInto_succ_cons (cutDepth : Nat) (binderGrade : UsageGrade)
    (argGrades outerGrades : GradeVector) :
    GradeVector.substInto (cutDepth + 1) (GradeVector.cons UsageGrade.zero argGrades)
        (GradeVector.cons binderGrade outerGrades) =
      GradeVector.cons binderGrade (GradeVector.substInto cutDepth argGrades outerGrades) := by
  show GradeVector.add (GradeVector.cons binderGrade (GradeVector.removeAt cutDepth outerGrades))
      (GradeVector.cons (UsageGrade.mul (GradeVector.gradeAt cutDepth outerGrades) UsageGrade.zero)
        (GradeVector.scale (GradeVector.gradeAt cutDepth outerGrades) argGrades)) =
    GradeVector.cons binderGrade
      (GradeVector.add (GradeVector.removeAt cutDepth outerGrades)
        (GradeVector.scale (GradeVector.gradeAt cutDepth outerGrades) argGrades))
  rw [UsageGrade.mul_zero (GradeVector.gradeAt cutDepth outerGrades)]
  show GradeVector.cons (UsageGrade.add binderGrade UsageGrade.zero) _ = GradeVector.cons binderGrade _
  rw [UsageGrade.add_zero binderGrade]

/-! ## removeTypeAt: length + lookup -/

theorem removeTypeAt_length :
    ∀ (cutDepth : Nat) (types : List GType), cutDepth < types.length →
      (removeTypeAt cutDepth types).length + 1 = types.length
  | 0, [], lt => absurd lt (Nat.not_lt_zero _)
  | 0, _ :: _, _ => rfl
  | _ + 1, [], lt => absurd lt (Nat.not_lt_zero _)
  | depth + 1, _ :: restTypes, lt => by
      show (removeTypeAt depth restTypes).length + 1 + 1 = restTypes.length + 1
      rw [removeTypeAt_length depth restTypes (Nat.lt_of_succ_lt_succ lt)]

theorem lookup_removeTypeAt_lt :
    ∀ (cutDepth index : Nat) (types : List GType), index < cutDepth →
      GType.lookup (removeTypeAt cutDepth types) index = GType.lookup types index
  | 0, _, _, lt => absurd lt (Nat.not_lt_zero _)
  | depth + 1, 0, types, _ => by cases types <;> rfl
  | depth + 1, index + 1, types, lt => by
      cases types with
      | nil => rfl
      | cons headType restTypes =>
          show GType.lookup (removeTypeAt depth restTypes) index = GType.lookup restTypes index
          exact lookup_removeTypeAt_lt depth index restTypes (Nat.lt_of_succ_lt_succ lt)

theorem lookup_removeTypeAt_ge :
    ∀ (cutDepth index : Nat) (types : List GType), cutDepth ≤ index →
      GType.lookup (removeTypeAt cutDepth types) index = GType.lookup types (index + 1)
  | 0, _, types, _ => by cases types <;> rfl
  | depth + 1, 0, _, le => absurd le (Nat.not_succ_le_zero _)
  | depth + 1, index + 1, types, le => by
      cases types with
      | nil => rfl
      | cons headType restTypes =>
          show GType.lookup (removeTypeAt depth restTypes) index = GType.lookup restTypes (index + 1)
          exact lookup_removeTypeAt_ge depth index restTypes (Nat.le_of_succ_le_succ le)

/-! ## gradeAt / removeAt on the zero vector -/

theorem gradeAt_nil (cutDepth : Nat) :
    GradeVector.gradeAt cutDepth GradeVector.nil = UsageGrade.zero := by
  cases cutDepth <;> rfl

theorem gradeAt_zero :
    ∀ (cutDepth scope : Nat), GradeVector.gradeAt cutDepth (GradeVector.zero scope) = UsageGrade.zero
  | 0, 0 => rfl
  | 0, _ + 1 => rfl
  | _ + 1, 0 => rfl
  | cutDepth + 1, scope + 1 => gradeAt_zero cutDepth scope

theorem removeAt_zero :
    ∀ (cutDepth scope : Nat), cutDepth ≤ scope →
      GradeVector.removeAt cutDepth (GradeVector.zero (scope + 1)) = GradeVector.zero scope
  | 0, _, _ => rfl
  | _cutDepth + 1, 0, le => absurd le (Nat.not_succ_le_zero _)
  | cutDepth + 1, scope + 1, le =>
      congrArg (GradeVector.cons UsageGrade.zero) (removeAt_zero cutDepth scope (Nat.le_of_succ_le_succ le))

/-! ## gradeAt / removeAt versus the var-rule singleton -/

theorem gradeAt_single_self :
    ∀ (cutDepth scope : Nat) (grade : UsageGrade), cutDepth < scope →
      GradeVector.gradeAt cutDepth (GradeVector.single scope cutDepth grade) = grade
  | 0, scope, grade, lt => by cases scope with
      | zero => exact absurd lt (Nat.not_lt_zero _)
      | succ _ => rfl
  | cutDepth + 1, scope, grade, lt => by cases scope with
      | zero => exact absurd lt (Nat.not_lt_zero _)
      | succ restScope =>
          show GradeVector.gradeAt cutDepth (GradeVector.single restScope cutDepth grade) = grade
          exact gradeAt_single_self cutDepth restScope grade (Nat.lt_of_succ_lt_succ lt)

theorem gradeAt_single_ne :
    ∀ (cutDepth index scope : Nat) (grade : UsageGrade), index ≠ cutDepth →
      GradeVector.gradeAt cutDepth (GradeVector.single scope index grade) = UsageGrade.zero
  | cutDepth, _, 0, _, _ => gradeAt_nil cutDepth
  | 0, 0, _ + 1, _, ne => (ne rfl).elim
  | 0, _ + 1, _ + 1, _, _ => rfl
  | cutDepth + 1, 0, scope + 1, _, _ => gradeAt_zero cutDepth scope
  | cutDepth + 1, index + 1, scope + 1, grade, ne =>
      gradeAt_single_ne cutDepth index scope grade (fun eq => ne (congrArg (· + 1) eq))

theorem removeAt_single_self :
    ∀ (cutDepth resultLen : Nat) (grade : UsageGrade), cutDepth ≤ resultLen →
      GradeVector.removeAt cutDepth (GradeVector.single (resultLen + 1) cutDepth grade) =
        GradeVector.zero resultLen
  | 0, _, _, _ => rfl
  | _cutDepth + 1, 0, _, le => absurd le (Nat.not_succ_le_zero _)
  | cutDepth + 1, resultLen + 1, grade, le =>
      congrArg (GradeVector.cons UsageGrade.zero)
        (removeAt_single_self cutDepth resultLen grade (Nat.le_of_succ_le_succ le))

theorem removeAt_single_lt :
    ∀ (cutDepth index resultLen : Nat) (grade : UsageGrade), index < cutDepth → cutDepth ≤ resultLen →
      GradeVector.removeAt cutDepth (GradeVector.single (resultLen + 1) index grade) =
        GradeVector.single resultLen index grade
  | 0, _, _, _, idxLt, _ => absurd idxLt (Nat.not_lt_zero _)
  | cutDepth + 1, 0, resultLen, grade, _, cutLe => by
      cases resultLen with
      | zero => exact absurd cutLe (Nat.not_succ_le_zero _)
      | succ rl =>
          exact congrArg (GradeVector.cons grade)
            (removeAt_zero cutDepth rl (Nat.le_of_succ_le_succ cutLe))
  | cutDepth + 1, index + 1, resultLen, grade, idxLt, cutLe => by
      cases resultLen with
      | zero => exact absurd cutLe (Nat.not_succ_le_zero _)
      | succ rl =>
          exact congrArg (GradeVector.cons UsageGrade.zero)
            (removeAt_single_lt cutDepth index rl grade (Nat.lt_of_succ_lt_succ idxLt)
              (Nat.le_of_succ_le_succ cutLe))

theorem removeAt_single_gt :
    ∀ (cutDepth idx resultLen : Nat) (grade : UsageGrade), cutDepth ≤ idx → idx < resultLen →
      GradeVector.removeAt cutDepth (GradeVector.single (resultLen + 1) (idx + 1) grade) =
        GradeVector.single resultLen idx grade
  | 0, _, _, _, _, _ => rfl
  | cutDepth + 1, 0, _, _, cutLe, _ => absurd cutLe (Nat.not_succ_le_zero _)
  | cutDepth + 1, idx + 1, resultLen, grade, cutLe, idxLt => by
      cases resultLen with
      | zero => exact absurd idxLt (Nat.not_lt_zero _)
      | succ rl =>
          exact congrArg (GradeVector.cons UsageGrade.zero)
            (removeAt_single_gt cutDepth idx rl grade (Nat.le_of_succ_le_succ cutLe)
              (Nat.lt_of_succ_lt_succ idxLt))

/-! ## removeAt / gradeAt distribute over add / scale (for the App case) -/

theorem removeAt_add : ∀ (cutDepth : Nat) (firstVector secondVector : GradeVector),
    firstVector.length = secondVector.length →
      GradeVector.removeAt cutDepth (GradeVector.add firstVector secondVector) =
        GradeVector.add (GradeVector.removeAt cutDepth firstVector)
          (GradeVector.removeAt cutDepth secondVector)
  | 0, .nil, .nil, _ => rfl
  | 0, .nil, .cons _ _, h => Nat.noConfusion h
  | 0, .cons _ _, .nil, h => Nat.noConfusion h
  | 0, .cons _ _, .cons _ _, _ => rfl
  | _ + 1, .nil, .nil, _ => rfl
  | _ + 1, .nil, .cons _ _, h => Nat.noConfusion h
  | _ + 1, .cons _ _, .nil, h => Nat.noConfusion h
  | cutDepth + 1, .cons vh vr, .cons wh wr, h =>
      congrArg (GradeVector.cons (UsageGrade.add vh wh)) (removeAt_add cutDepth vr wr (Nat.succ.inj h))

theorem removeAt_scale : ∀ (cutDepth : Nat) (scaleGrade : UsageGrade) (someVector : GradeVector),
    GradeVector.removeAt cutDepth (GradeVector.scale scaleGrade someVector) =
      GradeVector.scale scaleGrade (GradeVector.removeAt cutDepth someVector)
  | 0, _, .nil => rfl
  | 0, _, .cons _ _ => rfl
  | _ + 1, _, .nil => rfl
  | cutDepth + 1, scaleGrade, .cons vh vr =>
      congrArg (GradeVector.cons (UsageGrade.mul scaleGrade vh)) (removeAt_scale cutDepth scaleGrade vr)

theorem gradeAt_scale : ∀ (cutDepth : Nat) (scaleGrade : UsageGrade) (someVector : GradeVector),
    GradeVector.gradeAt cutDepth (GradeVector.scale scaleGrade someVector) =
      UsageGrade.mul scaleGrade (GradeVector.gradeAt cutDepth someVector)
  | 0, scaleGrade, .nil => (UsageGrade.mul_zero scaleGrade).symm
  | 0, _, .cons _ _ => rfl
  | _ + 1, scaleGrade, .nil => (UsageGrade.mul_zero scaleGrade).symm
  | cutDepth + 1, scaleGrade, .cons _ vr => gradeAt_scale cutDepth scaleGrade vr

theorem gradeAt_add :
    ∀ (cutDepth : Nat) (firstVector secondVector : GradeVector), firstVector.length = secondVector.length →
      GradeVector.gradeAt cutDepth (GradeVector.add firstVector secondVector) =
        UsageGrade.add (GradeVector.gradeAt cutDepth firstVector) (GradeVector.gradeAt cutDepth secondVector)
  | 0, .nil, .nil, _ => rfl
  | 0, .cons _ _, .nil, h => Nat.noConfusion h
  | 0, .nil, .cons _ _, h => Nat.noConfusion h
  | 0, .cons _ _, .cons _ _, _ => rfl
  | _ + 1, .nil, .nil, _ => rfl
  | _ + 1, .cons _ _, .nil, h => Nat.noConfusion h
  | _ + 1, .nil, .cons _ _, h => Nat.noConfusion h
  | cutDepth + 1, .cons _ vr, .cons _ wr, h => gradeAt_add cutDepth vr wr (Nat.succ.inj h)

/-- Commutative-monoid middle-four interchange — the App-case reassociation. -/
theorem add_interchange (firstVector secondVector thirdVector fourthVector : GradeVector) :
    GradeVector.add (GradeVector.add firstVector secondVector)
        (GradeVector.add thirdVector fourthVector) =
      GradeVector.add (GradeVector.add firstVector thirdVector)
        (GradeVector.add secondVector fourthVector) := by
  rw [GradeVector.add_assoc firstVector secondVector (GradeVector.add thirdVector fourthVector),
      ← GradeVector.add_assoc secondVector thirdVector fourthVector,
      GradeVector.add_comm secondVector thirdVector,
      GradeVector.add_assoc thirdVector secondVector fourthVector,
      ← GradeVector.add_assoc firstVector thirdVector (GradeVector.add secondVector fourthVector)]

/-! ## substInto on a singleton (the var case) and over an App grade -/

theorem substInto_single_self (cutDepth resultLen : Nat) (argGrades : GradeVector)
    (cutLe : cutDepth ≤ resultLen) (argLen : argGrades.length = resultLen) :
    GradeVector.substInto cutDepth argGrades (GradeVector.single (resultLen + 1) cutDepth UsageGrade.one) =
      argGrades := by
  show GradeVector.add (GradeVector.removeAt cutDepth (GradeVector.single (resultLen + 1) cutDepth UsageGrade.one))
      (GradeVector.scale (GradeVector.gradeAt cutDepth (GradeVector.single (resultLen + 1) cutDepth UsageGrade.one)) argGrades) = argGrades
  rw [removeAt_single_self cutDepth resultLen UsageGrade.one cutLe,
      gradeAt_single_self cutDepth (resultLen + 1) UsageGrade.one (Nat.lt_succ_of_le cutLe),
      GradeVector.scale_one_scalar, ← argLen]
  exact GradeVector.zero_add argGrades

theorem substInto_single_lt (cutDepth index resultLen : Nat) (argGrades : GradeVector)
    (idxLt : index < cutDepth) (cutLe : cutDepth ≤ resultLen) (argLen : argGrades.length = resultLen) :
    GradeVector.substInto cutDepth argGrades (GradeVector.single (resultLen + 1) index UsageGrade.one) =
      GradeVector.single resultLen index UsageGrade.one := by
  show GradeVector.add (GradeVector.removeAt cutDepth (GradeVector.single (resultLen + 1) index UsageGrade.one))
      (GradeVector.scale (GradeVector.gradeAt cutDepth (GradeVector.single (resultLen + 1) index UsageGrade.one)) argGrades) = _
  rw [removeAt_single_lt cutDepth index resultLen UsageGrade.one idxLt cutLe,
      gradeAt_single_ne cutDepth index (resultLen + 1) UsageGrade.one (Nat.ne_of_lt idxLt),
      GradeVector.scale_zero_scalar, argLen]
  have h := GradeVector.add_zero (GradeVector.single resultLen index UsageGrade.one)
  rw [GradeVector.single_length] at h
  exact h

theorem substInto_single_gt (cutDepth idx resultLen : Nat) (argGrades : GradeVector)
    (cutLe : cutDepth ≤ idx) (idxLt : idx < resultLen) (argLen : argGrades.length = resultLen) :
    GradeVector.substInto cutDepth argGrades (GradeVector.single (resultLen + 1) (idx + 1) UsageGrade.one) =
      GradeVector.single resultLen idx UsageGrade.one := by
  show GradeVector.add (GradeVector.removeAt cutDepth (GradeVector.single (resultLen + 1) (idx + 1) UsageGrade.one))
      (GradeVector.scale (GradeVector.gradeAt cutDepth (GradeVector.single (resultLen + 1) (idx + 1) UsageGrade.one)) argGrades) = _
  rw [removeAt_single_gt cutDepth idx resultLen UsageGrade.one cutLe idxLt,
      gradeAt_single_ne cutDepth (idx + 1) (resultLen + 1) UsageGrade.one
        (Nat.ne_of_lt (Nat.lt_succ_of_le cutLe)).symm,
      GradeVector.scale_zero_scalar, argLen]
  have h := GradeVector.add_zero (GradeVector.single resultLen idx UsageGrade.one)
  rw [GradeVector.single_length] at h
  exact h

theorem substInto_appGrade (cutDepth : Nat) (binderGrade : UsageGrade)
    (argGrades functionGrades argumentGrades : GradeVector)
    (lenEq : functionGrades.length = argumentGrades.length) :
    GradeVector.substInto cutDepth argGrades
        (GradeVector.add functionGrades (GradeVector.scale binderGrade argumentGrades)) =
      GradeVector.add (GradeVector.substInto cutDepth argGrades functionGrades)
        (GradeVector.scale binderGrade (GradeVector.substInto cutDepth argGrades argumentGrades)) := by
  have scaleLen : functionGrades.length = (GradeVector.scale binderGrade argumentGrades).length := by
    rw [GradeVector.scale_length]; exact lenEq
  simp only [GradeVector.substInto]
  rw [removeAt_add cutDepth functionGrades (GradeVector.scale binderGrade argumentGrades) scaleLen,
      removeAt_scale,
      gradeAt_add cutDepth functionGrades (GradeVector.scale binderGrade argumentGrades) scaleLen,
      gradeAt_scale, GradeVector.scale_add_scalar, ← GradeVector.scale_scale,
      GradeVector.scale_add]
  exact add_interchange (GradeVector.removeAt cutDepth functionGrades)
    (GradeVector.scale binderGrade (GradeVector.removeAt cutDepth argumentGrades))
    (GradeVector.scale (GradeVector.gradeAt cutDepth functionGrades) argGrades)
    (GradeVector.scale binderGrade (GradeVector.scale (GradeVector.gradeAt cutDepth argumentGrades) argGrades))

/-! ## The substitution lemma + β subject reduction -/

/-- **Graded substitution**: substituting `argTerm` (typed at grade vector `argGrades` in the context
with the cut binding removed) for the variable at `cutDepth` in `subject` preserves typing, with the
grade vector transformed by `substInto cutDepth argGrades`.  By induction on the derivation: the var
case trichotomizes below / at / above the cut; the λ-case threads via `substInto_succ_cons` and
front-weakening (`hasUsage_weakening` at cut 0); the App-case via `substInto_appGrade`. -/
theorem hasUsage_substitution {ctx : List GType} {bodyGrades : GradeVector} {subject : GradedLambda}
    {codomain : GType} (subjectTyped : HasUsage ctx bodyGrades subject codomain) :
    ∀ (cutDepth : Nat) (domain : GType) (argTerm : GradedLambda) (argGrades : GradeVector),
      GType.lookup ctx cutDepth = some domain →
      HasUsage (removeTypeAt cutDepth ctx) argGrades argTerm domain →
      HasUsage (removeTypeAt cutDepth ctx)
        (GradeVector.substInto cutDepth argGrades bodyGrades)
        (GradedLambda.substAt cutDepth argTerm subject) codomain := by
  induction subjectTyped with
  | var ctx index varType lookupOk =>
      intro cutDepth domain argTerm argGrades domainLookup argTyped
      have cutLt : cutDepth < ctx.length := lookup_some_lt ctx cutDepth domain domainLookup
      have argLen : argGrades.length = (removeTypeAt cutDepth ctx).length := hasUsage_length argTyped
      have ctxLenEq : (removeTypeAt cutDepth ctx).length + 1 = ctx.length :=
        removeTypeAt_length cutDepth ctx cutLt
      have cutLeRl : cutDepth ≤ (removeTypeAt cutDepth ctx).length := by
        have h := cutLt; rw [← ctxLenEq] at h; exact Nat.le_of_lt_succ h
      rcases Nat.lt_trichotomy index cutDepth with idxLt | idxEq | idxGt
      · have termEq : GradedLambda.substAt cutDepth argTerm (GradedLambda.var index) =
            GradedLambda.var index := by
          show (if index < cutDepth then GradedLambda.var index
                else if index = cutDepth then argTerm else GradedLambda.var (index - 1)) =
            GradedLambda.var index
          rw [if_pos idxLt]
        rw [termEq, show ctx.length = (removeTypeAt cutDepth ctx).length + 1 from ctxLenEq.symm,
            substInto_single_lt cutDepth index (removeTypeAt cutDepth ctx).length argGrades
              idxLt cutLeRl argLen]
        exact HasUsage.var (removeTypeAt cutDepth ctx) index varType
          (by rw [lookup_removeTypeAt_lt cutDepth index ctx idxLt]; exact lookupOk)
      · subst index
        have termEq : GradedLambda.substAt cutDepth argTerm (GradedLambda.var cutDepth) = argTerm := by
          show (if cutDepth < cutDepth then GradedLambda.var cutDepth
                else if cutDepth = cutDepth then argTerm else GradedLambda.var (cutDepth - 1)) = argTerm
          rw [if_neg (Nat.lt_irrefl cutDepth), if_pos rfl]
        have typeEq : varType = domain := Option.some.inj (lookupOk.symm.trans domainLookup)
        rw [termEq, show ctx.length = (removeTypeAt cutDepth ctx).length + 1 from ctxLenEq.symm,
            substInto_single_self cutDepth (removeTypeAt cutDepth ctx).length argGrades cutLeRl argLen,
            typeEq]
        exact argTyped
      · have pos : 0 < index := Nat.lt_of_le_of_lt (Nat.zero_le cutDepth) idxGt
        obtain ⟨predIndex, hpred⟩ : ∃ predIndex, index = predIndex + 1 :=
          ⟨index - 1, (Nat.succ_pred_eq_of_pos pos).symm⟩
        subst hpred
        have cutLePred : cutDepth ≤ predIndex := Nat.le_of_lt_succ idxGt
        have predLt : predIndex < (removeTypeAt cutDepth ctx).length := by
          have h := lookup_some_lt ctx (predIndex + 1) varType lookupOk
          rw [← ctxLenEq] at h; exact Nat.lt_of_succ_lt_succ h
        have termEq : GradedLambda.substAt cutDepth argTerm (GradedLambda.var (predIndex + 1)) =
            GradedLambda.var predIndex := by
          show (if predIndex + 1 < cutDepth then GradedLambda.var (predIndex + 1)
                else if predIndex + 1 = cutDepth then argTerm
                else GradedLambda.var (predIndex + 1 - 1)) = GradedLambda.var (predIndex + 1 - 1)
          rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt idxGt)),
              if_neg (Nat.ne_of_gt idxGt)]
        rw [termEq, show ctx.length = (removeTypeAt cutDepth ctx).length + 1 from ctxLenEq.symm,
            substInto_single_gt cutDepth predIndex (removeTypeAt cutDepth ctx).length argGrades
              cutLePred predLt argLen]
        exact HasUsage.var (removeTypeAt cutDepth ctx) predIndex varType
          (by rw [lookup_removeTypeAt_ge cutDepth predIndex ctx cutLePred]; exact lookupOk)
  | lam ctx binderGrade dom cod outerGrades innerBody _ innerIH =>
      intro cutDepth domain argTerm argGrades domainLookup argTyped
      show HasUsage (removeTypeAt cutDepth ctx) (GradeVector.substInto cutDepth argGrades outerGrades)
        (GradedLambda.lam (GradedLambda.substAt (cutDepth + 1) (GradedLambda.shift 0 argTerm) innerBody))
        (GType.arrow binderGrade dom cod)
      apply HasUsage.lam (removeTypeAt cutDepth ctx) binderGrade dom cod
        (GradeVector.substInto cutDepth argGrades outerGrades)
        (GradedLambda.substAt (cutDepth + 1) (GradedLambda.shift 0 argTerm) innerBody)
      rw [← substInto_succ_cons cutDepth binderGrade argGrades outerGrades]
      exact innerIH (cutDepth + 1) domain (GradedLambda.shift 0 argTerm)
        (GradeVector.cons UsageGrade.zero argGrades) domainLookup
        (hasUsage_weakening argTyped 0 dom (Nat.zero_le _))
  | app ctx binderGrade dom cod functionGrades argumentGrades function argument
      functionTyped argumentTyped functionIH argumentIH =>
      intro cutDepth domain argTerm argGrades domainLookup argTyped
      have lenEq : functionGrades.length = argumentGrades.length := by
        rw [hasUsage_length functionTyped, hasUsage_length argumentTyped]
      show HasUsage (removeTypeAt cutDepth ctx)
        (GradeVector.substInto cutDepth argGrades
          (GradeVector.add functionGrades (GradeVector.scale binderGrade argumentGrades)))
        (GradedLambda.app (GradedLambda.substAt cutDepth argTerm function)
          (GradedLambda.substAt cutDepth argTerm argument)) cod
      rw [substInto_appGrade cutDepth binderGrade argGrades functionGrades argumentGrades lenEq]
      exact HasUsage.app (removeTypeAt cutDepth ctx) binderGrade dom cod
        (GradeVector.substInto cutDepth argGrades functionGrades)
        (GradeVector.substInto cutDepth argGrades argumentGrades)
        (GradedLambda.substAt cutDepth argTerm function) (GradedLambda.substAt cutDepth argTerm argument)
        (functionIH cutDepth domain argTerm argGrades domainLookup argTyped)
        (argumentIH cutDepth domain argTerm argGrades domainLookup argTyped)

/-- **β subject reduction**: the type-coupled graded judgment is preserved under β, with the grade
vector preserved EXACTLY — closing the loop opened by `usage_check_fails_subject_reduction` (the
naive occurrence check fails this).  `(λ.body) arg ↝ body[0 := arg]`: invert App + Lam, then the
substitution lemma at cut 0, where `substInto 0 argGrades (cons binderGrade functionGrades)` is
definitionally `functionGrades + binderGrade · argGrades` = the redex's grade. -/
theorem hasUsage_betaPreservation {ctx : List GType} {grades : GradeVector}
    {body argTerm : GradedLambda} {resultType : GType}
    (typed : HasUsage ctx grades (.app (.lam body) argTerm) resultType) :
    HasUsage ctx grades (GradedLambda.substAt 0 argTerm body) resultType := by
  obtain ⟨binderGrade, domain, functionGrades, argGrades, functionTyped, argTyped, gradesEq⟩ :=
    HasUsage.invertApp typed
  obtain ⟨binderGrade', dom', cod', arrowEq, bodyTyped⟩ := HasUsage.invertLam functionTyped
  injection arrowEq with bgEq domEq codEq
  subst bgEq; subst domEq; subst codEq
  rw [gradesEq]
  exact hasUsage_substitution bodyTyped 0 domain argTerm argGrades rfl argTyped

end FX1Poly.Modal

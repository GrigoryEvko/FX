import FX1Poly.Modal.GradedTyping

/-! Scratch probe: the WEAKENING lemma for HasUsage (stable under `shift`, inserting a 0-grade at the
cut).  Helpers thread `cutDepth ≤ length` and the HasUsage length invariant. -/

namespace FX1Poly.Modal

def insertTypeAt : Nat → GType → List GType → List GType
  | 0, newType, types => newType :: types
  | _ + 1, newType, [] => [newType]
  | depth + 1, newType, headType :: restTypes => headType :: insertTypeAt depth newType restTypes

def GradeVector.insertAt : Nat → UsageGrade → GradeVector → GradeVector
  | 0, grade, vector => .cons grade vector
  | _ + 1, grade, .nil => .cons grade .nil
  | depth + 1, grade, .cons headGrade restGrades =>
      .cons headGrade (GradeVector.insertAt depth grade restGrades)

/-! ### Context-length + lookup helpers -/

theorem length_insertTypeAt (cutDepth : Nat) (newType : GType) (types : List GType) :
    (insertTypeAt cutDepth newType types).length = types.length + 1 := by
  induction cutDepth generalizing types with
  | zero => rfl
  | succ depth restIH =>
      cases types with
      | nil => rfl
      | cons headType restTypes =>
          show (insertTypeAt depth newType restTypes).length + 1 = restTypes.length + 1 + 1
          rw [restIH restTypes]

theorem lookup_some_lt :
    ∀ (types : List GType) (index : Nat) (foundType : GType),
      GType.lookup types index = some foundType → index < types.length
  | [], index, foundType, lookupEq => by
      have reduced : (none : Option GType) = some foundType := lookupEq
      nomatch reduced
  | _ :: _, 0, _, _ => Nat.succ_pos _
  | _ :: restTypes, index + 1, foundType, lookupEq =>
      Nat.succ_lt_succ (lookup_some_lt restTypes index foundType lookupEq)

theorem lookup_insertTypeAt_lt (newType : GType) :
    ∀ (cutDepth index : Nat) (types : List GType), index < cutDepth → cutDepth ≤ types.length →
      GType.lookup (insertTypeAt cutDepth newType types) index = GType.lookup types index
  | 0, _, _, indexLt, _ => absurd indexLt (Nat.not_lt_zero _)
  | depth + 1, 0, types, _, depthLe => by
      cases types with
      | nil => exact absurd depthLe (Nat.not_succ_le_zero _)
      | cons headType restTypes => rfl
  | depth + 1, index + 1, types, indexLt, depthLe => by
      cases types with
      | nil => exact absurd depthLe (Nat.not_succ_le_zero _)
      | cons headType restTypes =>
          show GType.lookup (insertTypeAt depth newType restTypes) index = GType.lookup restTypes index
          exact lookup_insertTypeAt_lt newType depth index restTypes
            (Nat.lt_of_succ_lt_succ indexLt) (Nat.le_of_succ_le_succ depthLe)

theorem lookup_insertTypeAt_ge (newType : GType) :
    ∀ (cutDepth index : Nat) (types : List GType), cutDepth ≤ index →
      GType.lookup (insertTypeAt cutDepth newType types) (index + 1) = GType.lookup types index
  | 0, _, _, _ => rfl
  | depth + 1, 0, _, depthLe => absurd depthLe (Nat.not_succ_le_zero _)
  | depth + 1, index + 1, types, depthLe => by
      cases types with
      | nil => rfl
      | cons headType restTypes =>
          show GType.lookup (insertTypeAt depth newType restTypes) (index + 1)
              = GType.lookup restTypes index
          exact lookup_insertTypeAt_ge newType depth index restTypes (Nat.le_of_succ_le_succ depthLe)

/-! ### Grade-vector insertion helpers -/

theorem insertAt_zero (cutDepth scope : Nat) :
    GradeVector.insertAt cutDepth UsageGrade.zero (GradeVector.zero scope) =
      GradeVector.zero (scope + 1) := by
  induction cutDepth generalizing scope with
  | zero => rfl
  | succ depth restIH =>
      cases scope with
      | zero => rfl
      | succ restScope =>
          exact congrArg (GradeVector.cons UsageGrade.zero) (restIH restScope)

/-- Singleton insertion, below the cut: marked position unchanged. -/
theorem single_insertAt_lt (grade : UsageGrade) :
    ∀ (cutDepth scope index : Nat), index < cutDepth → index < scope →
      GradeVector.insertAt cutDepth UsageGrade.zero (GradeVector.single scope index grade) =
        GradeVector.single (scope + 1) index grade
  | 0, _, index, indexLtCut, _ => absurd indexLtCut (Nat.not_lt_zero index)
  | _ + 1, 0, index, _, indexLtScope => absurd indexLtScope (Nat.not_lt_zero index)
  | cutDepth + 1, scope + 1, 0, _, _ =>
      congrArg (GradeVector.cons grade) (insertAt_zero cutDepth scope)
  | cutDepth + 1, scope + 1, index + 1, indexLtCut, indexLtScope =>
      congrArg (GradeVector.cons UsageGrade.zero)
        (single_insertAt_lt grade cutDepth scope index (Nat.lt_of_succ_lt_succ indexLtCut)
          (Nat.lt_of_succ_lt_succ indexLtScope))

/-- Singleton insertion, at or above the cut: marked position shifts by one. -/
theorem single_insertAt_ge (grade : UsageGrade) :
    ∀ (cutDepth scope index : Nat), cutDepth ≤ index → index < scope →
      GradeVector.insertAt cutDepth UsageGrade.zero (GradeVector.single scope index grade) =
        GradeVector.single (scope + 1) (index + 1) grade
  | 0, _, _, _, _ => rfl
  | _ + 1, 0, index, _, indexLtScope => absurd indexLtScope (Nat.not_lt_zero index)
  | cutDepth + 1, _ + 1, 0, cutLeIndex, _ => absurd cutLeIndex (Nat.not_succ_le_zero cutDepth)
  | cutDepth + 1, scope + 1, index + 1, cutLeIndex, indexLtScope =>
      congrArg (GradeVector.cons UsageGrade.zero)
        (single_insertAt_ge grade cutDepth scope index (Nat.le_of_succ_le_succ cutLeIndex)
          (Nat.lt_of_succ_lt_succ indexLtScope))

theorem insertAt_scale (cutDepth : Nat) (scaleGrade : UsageGrade) (someVector : GradeVector) :
    GradeVector.insertAt cutDepth UsageGrade.zero (GradeVector.scale scaleGrade someVector) =
      GradeVector.scale scaleGrade (GradeVector.insertAt cutDepth UsageGrade.zero someVector) := by
  induction cutDepth generalizing someVector with
  | zero =>
      show GradeVector.cons UsageGrade.zero (GradeVector.scale scaleGrade someVector) =
        GradeVector.cons (UsageGrade.mul scaleGrade UsageGrade.zero)
          (GradeVector.scale scaleGrade someVector)
      rw [UsageGrade.mul_zero scaleGrade]
  | succ depth restIH =>
      cases someVector with
      | nil =>
          show GradeVector.cons UsageGrade.zero GradeVector.nil =
            GradeVector.cons (UsageGrade.mul scaleGrade UsageGrade.zero) GradeVector.nil
          rw [UsageGrade.mul_zero scaleGrade]
      | cons headGrade restGrades =>
          exact congrArg (GradeVector.cons (UsageGrade.mul scaleGrade headGrade)) (restIH restGrades)

theorem insertAt_add (cutDepth : Nat) :
    ∀ (firstVector secondVector : GradeVector), firstVector.length = secondVector.length →
      GradeVector.insertAt cutDepth UsageGrade.zero (GradeVector.add firstVector secondVector) =
        GradeVector.add (GradeVector.insertAt cutDepth UsageGrade.zero firstVector)
          (GradeVector.insertAt cutDepth UsageGrade.zero secondVector) := by
  induction cutDepth with
  | zero =>
      intro firstVector secondVector _
      show GradeVector.cons UsageGrade.zero (GradeVector.add firstVector secondVector) =
        GradeVector.cons (UsageGrade.add UsageGrade.zero UsageGrade.zero)
          (GradeVector.add firstVector secondVector)
      rfl
  | succ depth restIH =>
      intro firstVector secondVector lengthEq
      cases firstVector with
      | nil =>
          cases secondVector with
          | nil => rfl
          | cons _ secondRest =>
              have contra : secondRest.length + 1 = 0 := lengthEq.symm
              exact Nat.noConfusion contra
      | cons firstHead firstRest =>
          cases secondVector with
          | nil =>
              have contra : firstRest.length + 1 = 0 := lengthEq
              exact Nat.noConfusion contra
          | cons secondHead secondRest =>
              have restLengthEq : firstRest.length = secondRest.length := Nat.succ.inj lengthEq
              exact congrArg (GradeVector.cons (UsageGrade.add firstHead secondHead))
                (restIH firstRest secondRest restLengthEq)

/-! ### The HasUsage length invariant -/

theorem add_length_eq :
    ∀ (firstVector secondVector : GradeVector), firstVector.length = secondVector.length →
      (GradeVector.add firstVector secondVector).length = firstVector.length
  | .nil, _, _ => rfl
  | .cons _ firstRest, .nil, lengthEq => by
      have contra : firstRest.length + 1 = 0 := lengthEq
      exact Nat.noConfusion contra
  | .cons _ firstRest, .cons _ secondRest, lengthEq => by
      show (GradeVector.add firstRest secondRest).length + 1 = firstRest.length + 1
      rw [add_length_eq firstRest secondRest (Nat.succ.inj lengthEq)]

theorem hasUsage_length {typeContext : List GType} {grades : GradeVector} {term : GradedLambda}
    {resultType : GType} (typed : HasUsage typeContext grades term resultType) :
    grades.length = typeContext.length := by
  induction typed with
  | var typeContext index varType _ => exact GradeVector.single_length _ _ _
  | lam typeContext binderGrade domain codomain outerGrades body _ bodyIH =>
      have step : outerGrades.length + 1 = typeContext.length + 1 := bodyIH
      exact Nat.succ.inj step
  | app typeContext binderGrade domain codomain functionGrades argumentGrades function argument
      _ _ functionIH argumentIH =>
      have lenScale : (GradeVector.scale binderGrade argumentGrades).length = typeContext.length := by
        rw [GradeVector.scale_length]; exact argumentIH
      rw [add_length_eq functionGrades (GradeVector.scale binderGrade argumentGrades)
            (by rw [functionIH, lenScale])]
      exact functionIH

/-! ### The weakening lemma -/

theorem hasUsage_shift {typeContext : List GType} {grades : GradeVector} {term : GradedLambda}
    {resultType : GType} (typed : HasUsage typeContext grades term resultType) :
    ∀ (cutDepth : Nat) (newBinding : GType), cutDepth ≤ typeContext.length →
      HasUsage (insertTypeAt cutDepth newBinding typeContext)
        (GradeVector.insertAt cutDepth UsageGrade.zero grades)
        (GradedLambda.shift cutDepth term) resultType := by
  induction typed with
  | var typeContext index varType lookupOk =>
      intro cutDepth newBinding cutLe
      rcases Nat.lt_or_ge index cutDepth with indexLtCut | indexGeCut
      · have shiftEq : GradedLambda.shift cutDepth (GradedLambda.var index) = GradedLambda.var index := by
          show (if index < cutDepth then GradedLambda.var index else GradedLambda.var (index + 1)) =
            GradedLambda.var index
          rw [if_pos indexLtCut]
        rw [shiftEq,
            single_insertAt_lt UsageGrade.one cutDepth typeContext.length index indexLtCut
              (Nat.lt_of_lt_of_le indexLtCut cutLe),
            ← length_insertTypeAt cutDepth newBinding typeContext]
        exact HasUsage.var (insertTypeAt cutDepth newBinding typeContext) index varType
          (by rw [lookup_insertTypeAt_lt newBinding cutDepth index typeContext indexLtCut cutLe];
              exact lookupOk)
      · have shiftEq : GradedLambda.shift cutDepth (GradedLambda.var index)
            = GradedLambda.var (index + 1) := by
          show (if index < cutDepth then GradedLambda.var index else GradedLambda.var (index + 1)) =
            GradedLambda.var (index + 1)
          rw [if_neg (Nat.not_lt.mpr indexGeCut)]
        rw [shiftEq,
            single_insertAt_ge UsageGrade.one cutDepth typeContext.length index indexGeCut
              (lookup_some_lt typeContext index varType lookupOk),
            ← length_insertTypeAt cutDepth newBinding typeContext]
        exact HasUsage.var (insertTypeAt cutDepth newBinding typeContext) (index + 1) varType
          (by rw [lookup_insertTypeAt_ge newBinding cutDepth index typeContext indexGeCut];
              exact lookupOk)
  | lam typeContext binderGrade domain codomain outerGrades body _ bodyIH =>
      intro cutDepth newBinding cutLe
      show HasUsage (insertTypeAt cutDepth newBinding typeContext)
        (GradeVector.insertAt cutDepth UsageGrade.zero outerGrades)
        (GradedLambda.lam (GradedLambda.shift (cutDepth + 1) body))
        (GType.arrow binderGrade domain codomain)
      exact HasUsage.lam (insertTypeAt cutDepth newBinding typeContext) binderGrade domain codomain
        (GradeVector.insertAt cutDepth UsageGrade.zero outerGrades)
        (GradedLambda.shift (cutDepth + 1) body)
        (bodyIH (cutDepth + 1) newBinding (Nat.succ_le_succ cutLe))
  | app typeContext binderGrade domain codomain functionGrades argumentGrades function argument
      functionTyped argumentTyped functionIH argumentIH =>
      intro cutDepth newBinding cutLe
      have lenScale : (GradeVector.scale binderGrade argumentGrades).length = typeContext.length := by
        rw [GradeVector.scale_length]; exact hasUsage_length argumentTyped
      have gradeEq : GradeVector.insertAt cutDepth UsageGrade.zero
          (GradeVector.add functionGrades (GradeVector.scale binderGrade argumentGrades)) =
            GradeVector.add (GradeVector.insertAt cutDepth UsageGrade.zero functionGrades)
              (GradeVector.scale binderGrade
                (GradeVector.insertAt cutDepth UsageGrade.zero argumentGrades)) := by
        rw [insertAt_add cutDepth functionGrades (GradeVector.scale binderGrade argumentGrades)
              (by rw [hasUsage_length functionTyped, lenScale]), insertAt_scale]
      show HasUsage (insertTypeAt cutDepth newBinding typeContext)
        (GradeVector.insertAt cutDepth UsageGrade.zero
          (GradeVector.add functionGrades (GradeVector.scale binderGrade argumentGrades)))
        (GradedLambda.app (GradedLambda.shift cutDepth function)
          (GradedLambda.shift cutDepth argument)) codomain
      rw [gradeEq]
      exact HasUsage.app (insertTypeAt cutDepth newBinding typeContext) binderGrade domain codomain
        (GradeVector.insertAt cutDepth UsageGrade.zero functionGrades)
        (GradeVector.insertAt cutDepth UsageGrade.zero argumentGrades)
        (GradedLambda.shift cutDepth function) (GradedLambda.shift cutDepth argument)
        (functionIH cutDepth newBinding cutLe) (argumentIH cutDepth newBinding cutLe)

#print axioms length_insertTypeAt
#print axioms lookup_some_lt
#print axioms lookup_insertTypeAt_lt
#print axioms lookup_insertTypeAt_ge
#print axioms insertAt_zero
#print axioms single_insertAt_lt
#print axioms single_insertAt_ge
#print axioms insertAt_scale
#print axioms insertAt_add
#print axioms add_length_eq
#print axioms hasUsage_length
#print axioms hasUsage_shift

end FX1Poly.Modal

import FX1Poly.Core.StratifiedReducibleUniverseDecode
import FX1Poly.Core.StrongNormalizationCodeFormers

namespace FX1Poly.Core

open FX1Poly.Foundation FX1Poly.Universe StepStar

-- 2-child eitherCode Step inversion (mirror of Step.from_arrowCode).
theorem Step.from_eitherCode_probe {scope : Nat} {leftCode rightCode target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_eitherCode () (.childCons leftCode (.childCons rightCode .childNil))) target) :
    (∃ leftAfter : RawTerm scope,
        target = .mkGen .gen_eitherCode () (.childCons leftAfter (.childCons rightCode .childNil)) ∧
        Step leftCode leftAfter)
    ∨ (∃ rightAfter : RawTerm scope,
        target = .mkGen .gen_eitherCode () (.childCons leftCode (.childCons rightAfter .childNil)) ∧
        Step rightCode rightAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ leftStep =>
          rename_i leftAfter
          exact Or.inl ⟨leftAfter, rfl, leftStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ rightStep =>
              rename_i rightAfter
              exact Or.inr ⟨rightAfter, rfl, rightStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

theorem eitherCode_isStronglyNormalizing_probe {scope : Nat} {leftCode rightCode : RawTerm scope}
    (leftTerminates : IsStronglyNormalizing leftCode)
    (rightTerminates : IsStronglyNormalizing rightCode) :
    IsStronglyNormalizing
      (.mkGen .gen_eitherCode () (.childCons leftCode (.childCons rightCode .childNil))) :=
  isStronglyNormalizing_of_twoChildCong
    (fun currentLeft currentRight =>
      (.mkGen .gen_eitherCode () (.childCons currentLeft (.childCons currentRight .childNil))))
    (fun parentStep => Step.from_eitherCode_probe parentStep)
    leftTerminates rightTerminates

theorem eitherCode_isReducibleMemberOfUniverse_probe {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) {leftCode rightCode : RawTerm scope}
    (leftNormalizing : IsStronglyNormalizing leftCode)
    (rightNormalizing : IsStronglyNormalizing rightCode) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_eitherCode () (.childCons leftCode (.childCons rightCode .childNil))) :=
  IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (eitherCode_isStronglyNormalizing_probe leftNormalizing rightNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

-- equivCode: same 2-child shape (leftTypeCode, rightTypeCode).
theorem Step.from_equivCode_probe {scope : Nat} {leftType rightType target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_equivCode () (.childCons leftType (.childCons rightType .childNil))) target) :
    (∃ leftAfter : RawTerm scope,
        target = .mkGen .gen_equivCode () (.childCons leftAfter (.childCons rightType .childNil)) ∧
        Step leftType leftAfter)
    ∨ (∃ rightAfter : RawTerm scope,
        target = .mkGen .gen_equivCode () (.childCons leftType (.childCons rightAfter .childNil)) ∧
        Step rightType rightAfter) := by
  cases reduction with
  | cong _ _ childStep =>
      cases childStep with
      | here _ leftStep =>
          rename_i leftAfter
          exact Or.inl ⟨leftAfter, rfl, leftStep⟩
      | there _ tailStep =>
          cases tailStep with
          | here _ rightStep =>
              rename_i rightAfter
              exact Or.inr ⟨rightAfter, rfl, rightStep⟩
          | there _ restStep =>
              exact absurd restStep StepChildren.no_step_at_empty_spine

theorem equivCode_isStronglyNormalizing_probe {scope : Nat} {leftType rightType : RawTerm scope}
    (leftTerminates : IsStronglyNormalizing leftType)
    (rightTerminates : IsStronglyNormalizing rightType) :
    IsStronglyNormalizing
      (.mkGen .gen_equivCode () (.childCons leftType (.childCons rightType .childNil))) :=
  isStronglyNormalizing_of_twoChildCong
    (fun currentLeft currentRight =>
      (.mkGen .gen_equivCode () (.childCons currentLeft (.childCons currentRight .childNil))))
    (fun parentStep => Step.from_equivCode_probe parentStep)
    leftTerminates rightTerminates

theorem equivCode_isReducibleMemberOfUniverse_probe {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) {leftType rightType : RawTerm scope}
    (leftNormalizing : IsStronglyNormalizing leftType)
    (rightNormalizing : IsStronglyNormalizing rightType) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_equivCode () (.childCons leftType (.childCons rightType .childNil))) :=
  IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (equivCode_isStronglyNormalizing_probe leftNormalizing rightNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

end FX1Poly.Core

#print axioms FX1Poly.Core.Step.from_eitherCode_probe
#print axioms FX1Poly.Core.eitherCode_isReducibleMemberOfUniverse_probe
#print axioms FX1Poly.Core.Step.from_equivCode_probe
#print axioms FX1Poly.Core.equivCode_isReducibleMemberOfUniverse_probe

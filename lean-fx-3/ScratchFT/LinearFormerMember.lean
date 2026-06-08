import FX1Poly.Core.StratifiedReducibleUniverseDecode
import FX1Poly.Core.StrongNormalizationLinearFormers

namespace FX1Poly.Core

open FX1Poly.Foundation FX1Poly.Universe StepStar

theorem linearArrow_isReducibleMemberOfUniverse_probe {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) {source target : RawTerm scope}
    (sourceNormalizing : IsStronglyNormalizing source)
    (targetNormalizing : IsStronglyNormalizing target) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_linearArrow () (.childCons source (.childCons target .childNil))) :=
  IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (linearArrow_isStronglyNormalizing_of_source_target sourceNormalizing targetNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

theorem tensorProduct_isReducibleMemberOfUniverse_probe {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) {leftFactor rightFactor : RawTerm scope}
    (leftNormalizing : IsStronglyNormalizing leftFactor)
    (rightNormalizing : IsStronglyNormalizing rightFactor) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_tensorProduct () (.childCons leftFactor (.childCons rightFactor .childNil))) :=
  IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (tensorProduct_isStronglyNormalizing_of_factors leftNormalizing rightNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

end FX1Poly.Core

#print axioms FX1Poly.Core.linearArrow_isReducibleMemberOfUniverse_probe
#print axioms FX1Poly.Core.tensorProduct_isReducibleMemberOfUniverse_probe

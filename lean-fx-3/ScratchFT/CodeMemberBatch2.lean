import FX1Poly.Core.StratifiedReducibleUniverseDecode
import FX1Poly.Core.StrongNormalizationCodeFormers

namespace FX1Poly.Core

open FX1Poly.Foundation FX1Poly.Universe StepStar

-- listCode is a reducible member of its universe (SN-071, one-child former).
theorem listCode_isReducibleMemberOfUniverse_probe {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) {elementCode : RawTerm scope}
    (elementNormalizing : IsStronglyNormalizing elementCode) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_listCode () (.childCons elementCode .childNil)) :=
  IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (listCode_isStronglyNormalizing_of_element elementNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

-- optionCode is a reducible member of its universe (SN-071, one-child former).
theorem optionCode_isReducibleMemberOfUniverse_probe {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) {elementCode : RawTerm scope}
    (elementNormalizing : IsStronglyNormalizing elementCode) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_optionCode () (.childCons elementCode .childNil)) :=
  IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (optionCode_isStronglyNormalizing_of_element elementNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

-- idCode is a reducible member of its universe (SN-071, three-child former).
theorem idCode_isReducibleMemberOfUniverse_probe {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) {typeCode leftRaw rightRaw : RawTerm scope}
    (typeNormalizing : IsStronglyNormalizing typeCode)
    (leftNormalizing : IsStronglyNormalizing leftRaw)
    (rightNormalizing : IsStronglyNormalizing rightRaw) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil)
      (.mkGen .gen_idCode ()
        (.childCons typeCode (.childCons leftRaw (.childCons rightRaw .childNil)))) :=
  IsReducibleMemberAt.dataFormerInUniverse levelExpr flag
    (idCode_isStronglyNormalizing_of_type_endpoints typeNormalizing leftNormalizing rightNormalizing)
    (fun _reduct weakHeadStep => by cases weakHeadStep with | rootIota iotaStep => cases iotaStep)
    (fun rootEquation => nomatch rootEquation)
    (fun rootEquation => nomatch rootEquation)

end FX1Poly.Core

#print axioms FX1Poly.Core.listCode_isReducibleMemberOfUniverse_probe
#print axioms FX1Poly.Core.optionCode_isReducibleMemberOfUniverse_probe
#print axioms FX1Poly.Core.idCode_isReducibleMemberOfUniverse_probe

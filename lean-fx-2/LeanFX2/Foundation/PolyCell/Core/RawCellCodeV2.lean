import LeanFX2.Foundation.PolyCell.Core.RawCellV2DecEq

/-! # Foundation/PolyCell/Core/RawCellCodeV2 — prefix-code serialization

Structural prefix serialization of RawTermV2/RawCellV2 to List Nat.
Backs the inputCode evidence field of CertifiedRawCellResult and
the FX0-PolyCell code-level bridge comparison fallback. -/

namespace LeanFX2.Foundation.PolyCell.Core

-- Tag bytes for cell constructors in the prefix code
def rawCellTagTermBase : Nat := 0
def rawCellTagGeneratingCell : Nat := 1
def rawCellTagVerticalComposite : Nat := 2
def rawCellTagHorizontalComposite : Nat := 3
def rawCellTagIdentityCell : Nat := 4

-- Generator id extraction (position in the enum via a total function)
-- For now just use the Generator's index via a match. This is a placeholder
-- that works; a proper toNat can be added later.
def Generator.toNat : Generator → Nat
  | .gen_var => 0 | .gen_unit => 1 | .gen_lam => 2 | .gen_app => 3
  | .gen_pair => 4 | .gen_fst => 5 | .gen_snd => 6
  | .gen_boolTrue => 7 | .gen_boolFalse => 8 | .gen_boolElim => 9
  | .gen_natZero => 10 | .gen_natSucc => 11 | .gen_natElim => 12 | .gen_natRec => 13
  | .gen_listNil => 14 | .gen_listCons => 15 | .gen_listElim => 16
  | .gen_optionNone => 17 | .gen_optionSome => 18 | .gen_optionMatch => 19
  | .gen_eitherInl => 20 | .gen_eitherInr => 21 | .gen_eitherMatch => 22
  | .gen_refl => 23 | .gen_idJ => 24
  | .gen_modIntro => 25 | .gen_modElim => 26 | .gen_subsume => 27
  | .gen_interval0 => 28 | .gen_interval1 => 29
  | .gen_intervalOpp => 30 | .gen_intervalMeet => 31 | .gen_intervalJoin => 32
  | .gen_pathLam => 33 | .gen_pathApp => 34
  | .gen_glueIntro => 35 | .gen_glueElim => 36
  | .gen_transp => 37 | .gen_hcomp => 38
  | .gen_oeqRefl => 39 | .gen_oeqJ => 40 | .gen_oeqFunext => 41
  | .gen_idStrictRefl => 42 | .gen_idStrictRec => 43
  | .gen_equivIntro => 44 | .gen_equivApp => 45
  | .gen_refineIntro => 46 | .gen_refineElim => 47
  | .gen_recordIntro => 48 | .gen_recordProj => 49
  | .gen_codataUnfold => 50 | .gen_codataDest => 51
  | .gen_sessionSend => 52 | .gen_sessionRecv => 53
  | .gen_effectPerform => 54 | .gen_universeCode => 55
  | .gen_arrowCode => 56 | .gen_piTyCode => 57 | .gen_sigmaTyCode => 58
  | .gen_productCode => 59 | .gen_sumCode => 60
  | .gen_listCode => 61 | .gen_optionCode => 62 | .gen_eitherCode => 63
  | .gen_idCode => 64 | .gen_equivCode => 65
  | .gen_cumulUpMarker => 66
  | .gen_uaToEquiv => 67 | .gen_equivApply => 68
  | .gen_pathCompose => 69 | .gen_idToEquiv => 70
  | .gen_oeqTrans => 71 | .gen_equivCompose => 72
  | .gen_transpFill => 73

-- Payload to Nat (for serialization)
def payloadToNat (generator : Generator) (scope : Nat)
    (payload : generator.payload scope) : Nat := by
  cases generator
  all_goals (first | exact payload.val | exact payload | exact 0)

mutual
  def RawTermV2.toCode {scope : Nat} : RawTermV2 scope → List Nat
    | .mkGen generator payload children =>
      [generator.toNat, payloadToNat generator scope payload]
        ++ children.toCode

  def RawTermChildrenV2.toCode {shifts : List Nat} {scope : Nat}
      : RawTermChildrenV2 shifts scope → List Nat
    | .childNil => []
    | .childCons head tail => head.toCode ++ tail.toCode
end

def RawCellV2.toCode {scope : Nat} : RawCellV2 scope → List Nat
  | .termBase term => rawCellTagTermBase :: term.toCode
  | .generatingCell ruleId source target =>
      rawCellTagGeneratingCell :: ruleId :: source.toCode ++ target.toCode
  | .verticalComposite first second =>
      rawCellTagVerticalComposite :: first.toCode ++ second.toCode
  | .horizontalComposite left right =>
      rawCellTagHorizontalComposite :: left.toCode ++ right.toCode
  | .identityCell base =>
      rawCellTagIdentityCell :: base.toCode

def hasSameNatList : List Nat → List Nat → Bool
  | [], [] => true
  | head1 :: tail1, head2 :: tail2 =>
    Nat.beq head1 head2 && hasSameNatList tail1 tail2
  | [], _ :: _ => false
  | _ :: _, [] => false

end LeanFX2.Foundation.PolyCell.Core

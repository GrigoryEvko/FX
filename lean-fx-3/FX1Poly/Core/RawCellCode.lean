import FX1Poly.Core.RawCellDecEq

/-! # Foundation/PolyCell/Core/RawCellCode — prefix-code serialization

Structural prefix serialization of RawTerm/RawCell to List Nat.
Backs the inputCode evidence field of CertifiedRawCellResult and
the FX0-PolyCell code-level bridge comparison fallback. -/

namespace FX1Poly.Core

-- Tag bytes for cell constructors in the prefix code
def rawCellTagTermBase : Nat := 0
def rawCellTagGeneratingCell : Nat := 1
def rawCellTagVerticalComposite : Nat := 2
def rawCellTagHorizontalComposite : Nat := 3
def rawCellTagIdentityCell : Nat := 4

-- Generator id extraction: a total injective tag assignment, one
-- distinct Nat per generator (injectivity proved in
-- GeneratorTagRoundTrip.lean).
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
  -- Tier ★★★★★ extensions (positions 74-101)
  | .gen_quotMk => 74 | .gen_quotEqAxiom => 75
  | .gen_quotRec => 76 | .gen_quotElim => 77
  | .gen_pushInl => 78 | .gen_pushInr => 79
  | .gen_pushGlue => 80 | .gen_pushRec => 81
  | .gen_truncIntro => 82 | .gen_truncCoh => 83 | .gen_truncRec => 84
  | .gen_polyFunctor => 85 | .gen_polyApply => 86
  | .gen_polyMu => 87 | .gen_polyNu => 88 | .gen_polyMap => 89
  | .gen_sigmaAlgebra => 90 | .gen_measureSpace => 91 | .gen_lebesgueInt => 92
  | .gen_nextT => 93 | .gen_alwaysT => 94 | .gen_eventuallyT => 95
  | .gen_untilT => 96 | .gen_sinceT => 97
  | .gen_infinitesimal => 98 | .gen_microcanc => 99
  | .gen_tangentSpace => 100 | .gen_diffOp => 101
  -- Tier ★★★★ extensions (positions 102-136)
  | .gen_sessionSelect => 102 | .gen_sessionOffer => 103
  | .gen_sessionClose => 104 | .gen_channelSplit => 105 | .gen_channelJoin => 106
  | .gen_regRead => 107 | .gen_regWrite => 108 | .gen_clockTick => 109
  | .gen_stageLatch => 110 | .gen_wireCombinational => 111
  | .gen_clockDomainCross => 112
  | .gen_realCauchy => 113 | .gen_realLimit => 114 | .gen_realCompare => 115
  | .gen_probSpace => 116 | .gen_sampleP => 117 | .gen_expectE => 118
  | .gen_padicNum => 119 | .gen_padicValuation => 120
  | .gen_localGlobalBridge => 121
  | .gen_idealFunctionality => 122 | .gen_realProtocol => 123
  | .gen_ucSimulator => 124 | .gen_ucCompose => 125
  | .gen_shannonEntropy => 126 | .gen_mutualInfo => 127
  | .gen_klDivergence => 128 | .gen_channelCapacity => 129
  | .gen_hilbertSpace => 130 | .gen_boundedOperator => 131
  | .gen_spectralDecomp => 132 | .gen_unitaryOp => 133
  | .gen_causalNet => 134 | .gen_doOperator => 135 | .gen_counterfactual => 136
  -- Tier ★★★ extensions (positions 137-163)
  | .gen_circleBase => 137 | .gen_circleLoop => 138 | .gen_circleRec => 139
  | .gen_pathInverse => 140
  | .gen_pathWhiskerLeft => 141 | .gen_pathWhiskerRight => 142
  | .gen_shapeModality => 143 | .gen_flatModality => 144
  | .gen_sharpModality => 145 | .gen_cohesiveAdjunctionUnit => 146
  | .gen_qiitIntro => 147 | .gen_qiitElim => 148
  | .gen_liftInnerToOuter => 149 | .gen_lowerOuterToInner => 150
  | .gen_modalityLayerMarker => 151
  | .gen_qubit => 152 | .gen_quantumGate => 153
  | .gen_quantumMeasure => 154 | .gen_quantumEntangle => 155
  | .gen_quantumDecohere => 156
  | .gen_game => 157 | .gen_strategy => 158 | .gen_playOut => 159
  | .gen_processCalc => 160 | .gen_parallelComp => 161
  | .gen_processCommit => 162 | .gen_bisimulationWitness => 163
  -- Tier ★★ extensions (positions 164-193)
  | .gen_compCubical => 164 | .gen_transpHigherDim => 165
  | .gen_groupAlg => 166 | .gen_ringAlg => 167 | .gen_moduleAlg => 168
  | .gen_containerDeriv => 169 | .gen_zipperType => 170 | .gen_plugOp => 171
  | .gen_diffLambda => 172 | .gen_diffApply => 173
  | .gen_differentialCategory => 174
  | .gen_bangModality => 175 | .gen_whyNotModality => 176
  | .gen_linearArrow => 177 | .gen_tensorProduct => 178
  | .gen_provabilityModality => 179 | .gen_dynamicLogic => 180
  | .gen_cpoStructure => 181 | .gen_bottomElem => 182
  | .gen_scottContinuous => 183 | .gen_fixedPoint => 184
  | .gen_hyperreal => 185 | .gen_starOp => 186 | .gen_standardPart => 187
  | .gen_cellularAutomaton => 188 | .gen_interactionNet => 189
  | .gen_reversibleOp => 190
  | .gen_bigOh => 191 | .gen_polyTimeWitness => 192 | .gen_npComplete => 193
  | .gen_emptyCode => 194
  | .gen_boolCode => 195

-- Payload to Nat (for serialization)
def payloadToNat (generator : Generator) (scope : Nat)
    (payload : generator.payload scope) : Nat := by
  cases generator
  all_goals (first | exact payload.val | exact payload | exact 0)

mutual
  def RawTerm.toCode {scope : Nat} : RawTerm scope → List Nat
    | .mkGen generator payload children =>
      [generator.toNat, payloadToNat generator scope payload]
        ++ children.toCode

  def RawTermChildren.toCode {shifts : List Nat} {scope : Nat}
      : RawTermChildren shifts scope → List Nat
    | .childNil => []
    | .childCons head tail => head.toCode ++ tail.toCode
end

def RawCell.toCode {scope : Nat} : RawCell scope → List Nat
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

end FX1Poly.Core

import FX1Poly.Core.RawCellCode

/-! # FX1Poly/Core/GeneratorTagRoundTrip
    — the §11.6.4 Generator-table validation: `Generator.toNat` is injective

`Generator.toNat` (RawCellCode.lean) assigns each of the 194 generators a tag
0–193; it is the head byte of the FX0 prefix-code serialization
(`RawTerm.toCode`).  For that serialization to be a faithful prefix code the tag
assignment MUST be collision-free — otherwise two distinct generators encode to
the same head byte and decoding is ambiguous.  This file proves it, the
§11.6.4 "Generator table round-trip witness":

```
Generator.toNat_injective : g₁.toNat = g₂.toNat → g₁ = g₂
```

## Method: an explicit left inverse

Injectivity of a hand-rolled enum→`Nat` is proved by exhibiting a left inverse
`Generator.fromTag : Nat → Option Generator` and the round-trip
`fromTag (toNat g) = some g` (checked per constructor by `rfl`, since `toNat g`
reduces to a literal and `fromTag` matches it back).  Injectivity then follows:
`toNat g₁ = toNat g₂` ⟹ `fromTag (toNat g₁) = fromTag (toNat g₂)` ⟹
`some g₁ = some g₂` ⟹ `g₁ = g₂`.  The inverse is the honest full table (no
shortcut); a mis-transcribed entry would fail the round-trip `rfl` at that
constructor.  (Named `fromTag` rather than the more obvious `ofNat`, which would
collide with the auto-derived `Generator.ofNat`.)

## Zero-axiom verification

`cases g <;> rfl` over the 194 constructors (each a definitional reduction of
the literal `Nat` match — no `decide`, no `omega`, no `simp`), plus
`Option.some.inj`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Audit-gated in `FX1PolyAudit`.
-/

namespace FX1Poly.Core

/-- Left inverse of `Generator.toNat`: map each tag 0–193 back to its generator,
out-of-range to `none`.  The faithful inversion of the `toNat` table; used only
to certify `toNat` injective (the FX0 decoder will reuse it). -/
def Generator.fromTag : Nat → Option Generator
  | 0 => some .gen_var | 1 => some .gen_unit | 2 => some .gen_lam | 3 => some .gen_app
  | 4 => some .gen_pair | 5 => some .gen_fst | 6 => some .gen_snd
  | 7 => some .gen_boolTrue | 8 => some .gen_boolFalse | 9 => some .gen_boolElim
  | 10 => some .gen_natZero | 11 => some .gen_natSucc | 12 => some .gen_natElim | 13 => some .gen_natRec
  | 14 => some .gen_listNil | 15 => some .gen_listCons | 16 => some .gen_listElim
  | 17 => some .gen_optionNone | 18 => some .gen_optionSome | 19 => some .gen_optionMatch
  | 20 => some .gen_eitherInl | 21 => some .gen_eitherInr | 22 => some .gen_eitherMatch
  | 23 => some .gen_refl | 24 => some .gen_idJ
  | 25 => some .gen_modIntro | 26 => some .gen_modElim | 27 => some .gen_subsume
  | 28 => some .gen_interval0 | 29 => some .gen_interval1
  | 30 => some .gen_intervalOpp | 31 => some .gen_intervalMeet | 32 => some .gen_intervalJoin
  | 33 => some .gen_pathLam | 34 => some .gen_pathApp
  | 35 => some .gen_glueIntro | 36 => some .gen_glueElim
  | 37 => some .gen_transp | 38 => some .gen_hcomp
  | 39 => some .gen_oeqRefl | 40 => some .gen_oeqJ | 41 => some .gen_oeqFunext
  | 42 => some .gen_idStrictRefl | 43 => some .gen_idStrictRec
  | 44 => some .gen_equivIntro | 45 => some .gen_equivApp
  | 46 => some .gen_refineIntro | 47 => some .gen_refineElim
  | 48 => some .gen_recordIntro | 49 => some .gen_recordProj
  | 50 => some .gen_codataUnfold | 51 => some .gen_codataDest
  | 52 => some .gen_sessionSend | 53 => some .gen_sessionRecv
  | 54 => some .gen_effectPerform | 55 => some .gen_universeCode
  | 56 => some .gen_arrowCode | 57 => some .gen_piTyCode | 58 => some .gen_sigmaTyCode
  | 59 => some .gen_productCode | 60 => some .gen_sumCode
  | 61 => some .gen_listCode | 62 => some .gen_optionCode | 63 => some .gen_eitherCode
  | 64 => some .gen_idCode | 65 => some .gen_equivCode
  | 66 => some .gen_cumulUpMarker
  | 67 => some .gen_uaToEquiv | 68 => some .gen_equivApply
  | 69 => some .gen_pathCompose | 70 => some .gen_idToEquiv
  | 71 => some .gen_oeqTrans | 72 => some .gen_equivCompose
  | 73 => some .gen_transpFill
  | 74 => some .gen_quotMk | 75 => some .gen_quotEqAxiom
  | 76 => some .gen_quotRec | 77 => some .gen_quotElim
  | 78 => some .gen_pushInl | 79 => some .gen_pushInr
  | 80 => some .gen_pushGlue | 81 => some .gen_pushRec
  | 82 => some .gen_truncIntro | 83 => some .gen_truncCoh | 84 => some .gen_truncRec
  | 85 => some .gen_polyFunctor | 86 => some .gen_polyApply
  | 87 => some .gen_polyMu | 88 => some .gen_polyNu | 89 => some .gen_polyMap
  | 90 => some .gen_sigmaAlgebra | 91 => some .gen_measureSpace | 92 => some .gen_lebesgueInt
  | 93 => some .gen_nextT | 94 => some .gen_alwaysT | 95 => some .gen_eventuallyT
  | 96 => some .gen_untilT | 97 => some .gen_sinceT
  | 98 => some .gen_infinitesimal | 99 => some .gen_microcanc
  | 100 => some .gen_tangentSpace | 101 => some .gen_diffOp
  | 102 => some .gen_sessionSelect | 103 => some .gen_sessionOffer
  | 104 => some .gen_sessionClose | 105 => some .gen_channelSplit | 106 => some .gen_channelJoin
  | 107 => some .gen_regRead | 108 => some .gen_regWrite | 109 => some .gen_clockTick
  | 110 => some .gen_stageLatch | 111 => some .gen_wireCombinational
  | 112 => some .gen_clockDomainCross
  | 113 => some .gen_realCauchy | 114 => some .gen_realLimit | 115 => some .gen_realCompare
  | 116 => some .gen_probSpace | 117 => some .gen_sampleP | 118 => some .gen_expectE
  | 119 => some .gen_padicNum | 120 => some .gen_padicValuation
  | 121 => some .gen_localGlobalBridge
  | 122 => some .gen_idealFunctionality | 123 => some .gen_realProtocol
  | 124 => some .gen_ucSimulator | 125 => some .gen_ucCompose
  | 126 => some .gen_shannonEntropy | 127 => some .gen_mutualInfo
  | 128 => some .gen_klDivergence | 129 => some .gen_channelCapacity
  | 130 => some .gen_hilbertSpace | 131 => some .gen_boundedOperator
  | 132 => some .gen_spectralDecomp | 133 => some .gen_unitaryOp
  | 134 => some .gen_causalNet | 135 => some .gen_doOperator | 136 => some .gen_counterfactual
  | 137 => some .gen_circleBase | 138 => some .gen_circleLoop | 139 => some .gen_circleRec
  | 140 => some .gen_pathInverse
  | 141 => some .gen_pathWhiskerLeft | 142 => some .gen_pathWhiskerRight
  | 143 => some .gen_shapeModality | 144 => some .gen_flatModality
  | 145 => some .gen_sharpModality | 146 => some .gen_cohesiveAdjunctionUnit
  | 147 => some .gen_qiitIntro | 148 => some .gen_qiitElim
  | 149 => some .gen_liftInnerToOuter | 150 => some .gen_lowerOuterToInner
  | 151 => some .gen_modalityLayerMarker
  | 152 => some .gen_qubit | 153 => some .gen_quantumGate
  | 154 => some .gen_quantumMeasure | 155 => some .gen_quantumEntangle
  | 156 => some .gen_quantumDecohere
  | 157 => some .gen_game | 158 => some .gen_strategy | 159 => some .gen_playOut
  | 160 => some .gen_processCalc | 161 => some .gen_parallelComp
  | 162 => some .gen_processCommit | 163 => some .gen_bisimulationWitness
  | 164 => some .gen_compCubical | 165 => some .gen_transpHigherDim
  | 166 => some .gen_groupAlg | 167 => some .gen_ringAlg | 168 => some .gen_moduleAlg
  | 169 => some .gen_containerDeriv | 170 => some .gen_zipperType | 171 => some .gen_plugOp
  | 172 => some .gen_diffLambda | 173 => some .gen_diffApply
  | 174 => some .gen_differentialCategory
  | 175 => some .gen_bangModality | 176 => some .gen_whyNotModality
  | 177 => some .gen_linearArrow | 178 => some .gen_tensorProduct
  | 179 => some .gen_provabilityModality | 180 => some .gen_dynamicLogic
  | 181 => some .gen_cpoStructure | 182 => some .gen_bottomElem
  | 183 => some .gen_scottContinuous | 184 => some .gen_fixedPoint
  | 185 => some .gen_hyperreal | 186 => some .gen_starOp | 187 => some .gen_standardPart
  | 188 => some .gen_cellularAutomaton | 189 => some .gen_interactionNet
  | 190 => some .gen_reversibleOp
  | 191 => some .gen_bigOh | 192 => some .gen_polyTimeWitness | 193 => some .gen_npComplete
  | 194 => some .gen_emptyCode
  | 195 => some .gen_boolCode
  | 196 => some .gen_natCode
  | _ => none

/-- Round-trip: `fromTag` recovers every generator from its `toNat` tag.  Each
constructor reduces definitionally (`toNat g` is a literal, `fromTag` matches it),
so `cases g <;> rfl` discharges all 194.  A mis-transcribed `fromTag` entry would
fail `rfl` at exactly that constructor. -/
theorem Generator.fromTag_toNat (generator : Generator) :
    Generator.fromTag generator.toNat = some generator := by
  cases generator <;> rfl

/-- §11.6.4 table validation: the `Generator.toNat` tag assignment is
collision-free.  The head byte of the FX0 prefix code therefore uniquely
identifies the generator, so the serialization is unambiguous at the tag level.
Proved via the left inverse `fromTag` and its round-trip. -/
theorem Generator.toNat_injective {firstGenerator secondGenerator : Generator}
    (tagsEqual : firstGenerator.toNat = secondGenerator.toNat) :
    firstGenerator = secondGenerator := by
  have firstRoundTrip : Generator.fromTag firstGenerator.toNat = some firstGenerator :=
    Generator.fromTag_toNat firstGenerator
  rw [tagsEqual] at firstRoundTrip
  exact Option.some.inj (firstRoundTrip.symm.trans (Generator.fromTag_toNat secondGenerator))

end FX1Poly.Core

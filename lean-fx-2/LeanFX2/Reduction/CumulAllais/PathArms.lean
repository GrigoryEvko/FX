import LeanFX2.Reduction.CumulAllais.DataIntroArms

/-! # LeanFX2.Reduction.CumulAllais.PathArms

Allais arms for the cubical path-fragment Term constructors:

* Interval values: `interval0`, `interval1`, `intervalOpp`,
  `intervalMeet`, `intervalJoin`.
* Path application / binder: `pathLam`, `pathApp`.
* Glue: `glueIntro`, `glueElim`.
* Composition primitives: `transp`, `hcomp`.

The typed D2.5 path mirror adds the same two shapes as ordinary
application/lambda: `pathLam` is a binder over `Ty.interval`, while
`pathApp` is a two-subterm eliminator.  The `pathLam` substitution
arm uses `Ty.weaken_substHet_commute`, so the body relation peels
the same cast on both sides before applying `ConvCumul.pathLamCong`.

## Root status

Layer 3 cumulativity-via-Allais helper. -/

namespace LeanFX2

/-! ### Cubical path-fragment Allais arms

The typed D2.5 path mirror adds the same two shapes as ordinary
application/lambda: `pathLam` is a binder over `Ty.interval`, while
`pathApp` is a two-subterm eliminator.  The `pathLam` substitution arm
uses `Ty.weaken_substHet_commute`, so the body relation peels the same
cast on both sides before applying `ConvCumul.pathLamCong`. -/

/-- Allais arm for `interval0`: closed-payload, refl. -/
theorem ConvCumul.subst_compatible_interval0_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma) :
    ConvCumul ((Term.interval0 (context := sourceCtx)).substHet termSubstA)
              ((Term.interval0 (context := sourceCtx)).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for `interval1`: closed-payload, refl. -/
theorem ConvCumul.subst_compatible_interval1_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma) :
    ConvCumul ((Term.interval1 (context := sourceCtx)).substHet termSubstA)
              ((Term.interval1 (context := sourceCtx)).substHet termSubstB) :=
  ConvCumul.refl _

/-- Allais arm for interval negation: one-subterm congruence. -/
theorem ConvCumul.subst_compatible_intervalOpp_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {innerRaw : RawTerm sourceScope}
    (innerValue : Term sourceCtx Ty.interval innerRaw)
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (innerCompat :
      ConvCumul (innerValue.substHet termSubstA)
                (innerValue.substHet termSubstB)) :
    ConvCumul ((Term.intervalOpp innerValue).substHet termSubstA)
              ((Term.intervalOpp innerValue).substHet termSubstB) :=
  ConvCumul.intervalOppCong innerCompat

/-- Allais arm for interval meet: two-subterm congruence. -/
theorem ConvCumul.subst_compatible_intervalMeet_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (leftCompat :
      ConvCumul (leftValue.substHet termSubstA)
                (leftValue.substHet termSubstB))
    (rightCompat :
      ConvCumul (rightValue.substHet termSubstA)
                (rightValue.substHet termSubstB)) :
    ConvCumul ((Term.intervalMeet leftValue rightValue).substHet termSubstA)
              ((Term.intervalMeet leftValue rightValue).substHet termSubstB) :=
  ConvCumul.intervalMeetCong leftCompat rightCompat

/-- Allais arm for interval join: two-subterm congruence. -/
theorem ConvCumul.subst_compatible_intervalJoin_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    (leftValue : Term sourceCtx Ty.interval leftRaw)
    (rightValue : Term sourceCtx Ty.interval rightRaw)
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (leftCompat :
      ConvCumul (leftValue.substHet termSubstA)
                (leftValue.substHet termSubstB))
    (rightCompat :
      ConvCumul (rightValue.substHet termSubstA)
                (rightValue.substHet termSubstB)) :
    ConvCumul ((Term.intervalJoin leftValue rightValue).substHet termSubstA)
              ((Term.intervalJoin leftValue rightValue).substHet termSubstB) :=
  ConvCumul.intervalJoinCong leftCompat rightCompat

/-- Allais arm for `pathLam`: interval-binder cong via
`pathLamCong`. -/
theorem ConvCumul.subst_compatible_pathLam_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    (carrierType : Ty sourceLevel sourceScope)
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {bodyRaw : RawTerm (sourceScope + 1)}
    (body : Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw)
    (bodyCompat :
      ConvCumul (body.substHet (termSubstA.lift Ty.interval))
                (body.substHet (termSubstB.lift Ty.interval))) :
    ConvCumul
      ((Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint body).substHet
        termSubstA)
      ((Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint body).substHet
        termSubstB) :=
  ConvCumul.pathLamCong modeIsUnivalent
    (ConvCumul.cast_eq_both_benton _ bodyCompat)

/-- Allais arm for `pathApp`: two-subterm cong via `pathAppCong`. -/
theorem ConvCumul.subst_compatible_pathApp_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty sourceLevel sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    (pathTerm :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRaw)
    (intervalTerm : Term sourceCtx Ty.interval intervalRaw)
    (pathCompat :
      ConvCumul (pathTerm.substHet termSubstA)
                (pathTerm.substHet termSubstB))
    (intervalCompat :
      ConvCumul (intervalTerm.substHet termSubstA)
                (intervalTerm.substHet termSubstB)) :
    ConvCumul ((Term.pathApp modeIsUnivalent pathTerm intervalTerm).substHet termSubstA)
              ((Term.pathApp modeIsUnivalent pathTerm intervalTerm).substHet termSubstB) :=
  ConvCumul.pathAppCong modeIsUnivalent pathCompat intervalCompat

/-- Allais arm for `glueIntro`: two-subterm cong via
`glueIntroCong`. -/
theorem ConvCumul.subst_compatible_glueIntro_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty sourceLevel sourceScope)
    (boundaryWitness : RawTerm sourceScope)
    {baseRaw partialRaw : RawTerm sourceScope}
    (baseValue : Term sourceCtx baseType baseRaw)
    (partialValue : Term sourceCtx baseType partialRaw)
    (baseCompat :
      ConvCumul (baseValue.substHet termSubstA)
                (baseValue.substHet termSubstB))
    (partialCompat :
      ConvCumul (partialValue.substHet termSubstA)
                (partialValue.substHet termSubstB)) :
    ConvCumul
      ((Term.glueIntro modeIsUnivalent baseType boundaryWitness
        baseValue partialValue).substHet
        termSubstA)
      ((Term.glueIntro modeIsUnivalent baseType boundaryWitness
        baseValue partialValue).substHet
        termSubstB) :=
  ConvCumul.glueIntroCong modeIsUnivalent baseCompat partialCompat

/-- Allais arm for `glueElim`: single-subterm cong via
`glueElimCong`. -/
theorem ConvCumul.subst_compatible_glueElim_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty sourceLevel sourceScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    (gluedValue : Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw)
    (gluedCompat :
      ConvCumul (gluedValue.substHet termSubstA)
                (gluedValue.substHet termSubstB)) :
    ConvCumul ((Term.glueElim modeIsUnivalent gluedValue).substHet termSubstA)
              ((Term.glueElim modeIsUnivalent gluedValue).substHet termSubstB) :=
  ConvCumul.glueElimCong modeIsUnivalent gluedCompat

/-- Allais arm for `transp`: two-subterm cong via `transpCong`. -/
theorem ConvCumul.subst_compatible_transp_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ sourceLevel)
    (sourceType targetType : Ty sourceLevel sourceScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    {pathRaw sourceRaw : RawTerm sourceScope}
    (typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw)
    (sourceValue : Term sourceCtx sourceType sourceRaw)
    (pathCompat :
      ConvCumul (typePath.substHet termSubstA)
                (typePath.substHet termSubstB))
    (sourceCompat :
      ConvCumul (sourceValue.substHet termSubstA)
                (sourceValue.substHet termSubstB)) :
    ConvCumul
      ((Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType
        sourceTypeRaw targetTypeRaw typePath sourceValue).substHet
        termSubstA)
      ((Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType
        sourceTypeRaw targetTypeRaw typePath sourceValue).substHet
        termSubstB) :=
  ConvCumul.transpCong modeIsUnivalent universeLevel
    (Nat.le_trans universeLevelLt sigma.cumulOk)
    (sourceType.substHet sigma)
    (targetType.substHet sigma)
    (sourceTypeRaw.subst sigma.forRaw)
    (targetTypeRaw.subst sigma.forRaw)
    pathCompat sourceCompat

/-- Allais arm for `hcomp`: two-subterm cong via `hcompCong`. -/
theorem ConvCumul.subst_compatible_hcomp_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty sourceLevel sourceScope}
    {sidesRaw capRaw : RawTerm sourceScope}
    (sidesValue : Term sourceCtx carrierType sidesRaw)
    (capValue : Term sourceCtx carrierType capRaw)
    (sidesCompat :
      ConvCumul (sidesValue.substHet termSubstA)
                (sidesValue.substHet termSubstB))
    (capCompat :
      ConvCumul (capValue.substHet termSubstA)
                (capValue.substHet termSubstB)) :
    ConvCumul ((Term.hcomp modeIsUnivalent sidesValue capValue).substHet
                termSubstA)
              ((Term.hcomp modeIsUnivalent sidesValue capValue).substHet
                termSubstB) :=
  ConvCumul.hcompCong modeIsUnivalent sidesCompat capCompat

/-- Allais arm for `hcompPath`: two-subterm cong via `hcompPathCong`. -/
theorem ConvCumul.subst_compatible_hcompPath_allais
    {mode : Mode}
    {sourceLevel targetLevel sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigma : SubstHet sourceLevel targetLevel sourceScope targetScope}
    {termSubstA termSubstB : TermSubstHet sourceCtx targetCtx sigma}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty sourceLevel sourceScope}
    (leftEndpoint rightEndpoint : RawTerm sourceScope)
    {sidesPathRaw capRaw : RawTerm sourceScope}
    (sidesPath :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        sidesPathRaw)
    (capValue : Term sourceCtx carrierType capRaw)
    (sidesCompat :
      ConvCumul (sidesPath.substHet termSubstA)
                (sidesPath.substHet termSubstB))
    (capCompat :
      ConvCumul (capValue.substHet termSubstA)
                (capValue.substHet termSubstB)) :
    ConvCumul ((Term.hcompPath modeIsUnivalent
                  leftEndpoint rightEndpoint sidesPath capValue).substHet
                termSubstA)
              ((Term.hcompPath modeIsUnivalent
                  leftEndpoint rightEndpoint sidesPath capValue).substHet
                termSubstB) :=
  ConvCumul.hcompPathCong modeIsUnivalent
    (leftEndpoint.subst sigma.forRaw) (rightEndpoint.subst sigma.forRaw)
    sidesCompat capCompat

end LeanFX2

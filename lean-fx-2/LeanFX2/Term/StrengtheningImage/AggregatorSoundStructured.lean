import LeanFX2.Term.StrengtheningImage.AggregatorSoundCore

/-! # Term/StrengtheningImage/AggregatorSoundStructured

Aggregator-soundness instances for Sigma, interval, list, codata, session, cubical, and binder constructors.
-/

namespace LeanFX2

namespace Term

/-- Headline aggregator soundness at the `Term.fst` arm.  1-IH
Σ-first-projection (with internal type-shape strengthening). -/
theorem isAggregatorSound_fst {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairAggregator : IsAggregatorSound pairTerm) :
    IsAggregatorSound (Term.fst pairTerm) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atFst_imp_sound strengthening
    (pairAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.snd` arm.  1-IH
Σ-second-projection (with internal type-shape strengthening). -/
theorem isAggregatorSound_snd {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {pairRaw : RawTerm sourceScope}
    {pairTerm : Term sourceCtx (Ty.sigmaTy firstType secondType) pairRaw}
    (pairAggregator : IsAggregatorSound pairTerm) :
    IsAggregatorSound (Term.snd pairTerm) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atSnd_imp_sound strengthening
    (pairAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.pair` arm.  2-IH
Σ-introduction over `(firstValue, secondValue)`.  `secondValue`'s
type is `secondType.subst0 firstType firstRaw`, threaded
transparently via the aggregator predicate. -/
theorem isAggregatorSound_pair {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {firstType : Ty level sourceScope}
    {secondType : Ty level (sourceScope + 1)}
    {firstRaw secondRaw : RawTerm sourceScope}
    {firstValue : Term sourceCtx firstType firstRaw}
    {secondValue :
      Term sourceCtx (secondType.subst0 firstType firstRaw) secondRaw}
    (firstAggregator : IsAggregatorSound firstValue)
    (secondAggregator : IsAggregatorSound secondValue) :
    IsAggregatorSound
      (Term.pair (secondType := secondType) firstValue secondValue) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atPair_imp_sound strengthening
    (firstAggregator strengthening) (secondAggregator strengthening)
    result success

/-- Headline aggregator soundness at the `Term.refineIntro` arm.
2-IH refinement introduction: the `predicate` raw rides
`strengthening.back.lift`; `baseValue` and `predicateProof` each
supply an aggregator. -/
theorem isAggregatorSound_refineIntro {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {baseType : Ty level sourceScope}
    (predicate : RawTerm (sourceScope + 1))
    {valueRaw proofRaw : RawTerm sourceScope}
    {baseValue : Term sourceCtx baseType valueRaw}
    {predicateProof : Term sourceCtx Ty.unit proofRaw}
    (baseAggregator : IsAggregatorSound baseValue)
    (proofAggregator : IsAggregatorSound predicateProof) :
    IsAggregatorSound
      (Term.refineIntro predicate baseValue predicateProof) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atRefineIntro_imp_sound strengthening
    (baseAggregator strengthening) (proofAggregator strengthening)
    result success

/-- Headline aggregator soundness at the `Term.intervalOpp` arm.
1-IH interval negation. -/
theorem isAggregatorSound_intervalOpp {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    (innerAggregator : IsAggregatorSound innerValue) :
    IsAggregatorSound
      (Term.intervalOpp (innerValue := innerValue)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atIntervalOpp_imp_sound strengthening
    (innerAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.intervalMeet` arm.
2-IH interval meet (min). -/
theorem isAggregatorSound_intervalMeet {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftAggregator : IsAggregatorSound leftValue)
    (rightAggregator : IsAggregatorSound rightValue) :
    IsAggregatorSound
      (Term.intervalMeet (leftValue := leftValue)
        (rightValue := rightValue)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atIntervalMeet_imp_sound strengthening
    (leftAggregator strengthening) (rightAggregator strengthening)
    result success

/-- Headline aggregator soundness at the `Term.intervalJoin` arm.
2-IH interval join (max). -/
theorem isAggregatorSound_intervalJoin {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftAggregator : IsAggregatorSound leftValue)
    (rightAggregator : IsAggregatorSound rightValue) :
    IsAggregatorSound
      (Term.intervalJoin (leftValue := leftValue)
        (rightValue := rightValue)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atIntervalJoin_imp_sound strengthening
    (leftAggregator strengthening) (rightAggregator strengthening)
    result success

/-- Headline aggregator soundness at the `Term.listCons` arm.
2-IH list cons (head + tail). -/
theorem isAggregatorSound_listCons {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType : Ty level sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    (headAggregator : IsAggregatorSound headTerm)
    (tailAggregator : IsAggregatorSound tailTerm) :
    IsAggregatorSound
      (Term.listCons (headTerm := headTerm) (tailTerm := tailTerm)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atListCons_imp_sound strengthening
    (headAggregator strengthening) (tailAggregator strengthening)
    result success

/-- Headline aggregator soundness at the `Term.codataDest` arm.
1-IH codata destruction. -/
theorem isAggregatorSound_codataDest {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {stateType outputType : Ty level sourceScope}
    {codataRaw : RawTerm sourceScope}
    {codataValue :
      Term sourceCtx (Ty.codata stateType outputType) codataRaw}
    (codataAggregator : IsAggregatorSound codataValue) :
    IsAggregatorSound (Term.codataDest codataValue) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atCodataDest_imp_sound strengthening
    (codataAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.codataUnfold` arm.
2-IH codata introduction (`initialState` + `transition`). -/
theorem isAggregatorSound_codataUnfold {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {stateType outputType : Ty level sourceScope}
    {stateRaw transitionRaw : RawTerm sourceScope}
    {initialState : Term sourceCtx stateType stateRaw}
    {transition :
      Term sourceCtx (Ty.arrow stateType outputType) transitionRaw}
    (stateAggregator : IsAggregatorSound initialState)
    (transitionAggregator : IsAggregatorSound transition) :
    IsAggregatorSound
      (Term.codataUnfold initialState transition) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atCodataUnfold_imp_sound strengthening
    (stateAggregator strengthening) (transitionAggregator strengthening)
    result success

/-- Headline aggregator soundness at the `Term.pathApp` arm.  2-IH
cubical path application (`pathTerm` + `intervalTerm`); also threads
the `modeIsUnivalent` mode-eq witness. -/
theorem isAggregatorSound_pathApp {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {modeIsUnivalent : mode = Mode.univalent}
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {pathRaw intervalRaw : RawTerm sourceScope}
    {pathTerm :
      Term sourceCtx (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRaw}
    {intervalTerm : Term sourceCtx Ty.interval intervalRaw}
    (pathAggregator : IsAggregatorSound pathTerm)
    (intervalAggregator : IsAggregatorSound intervalTerm) :
    IsAggregatorSound
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atPathApp_imp_sound strengthening
    (pathAggregator strengthening) (intervalAggregator strengthening)
    result success

/-- Headline aggregator soundness at the `Term.glueElim` arm.
1-IH cubical glue elimination, threading `modeIsUnivalent`. -/
theorem isAggregatorSound_glueElim {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {modeIsUnivalent : mode = Mode.univalent}
    {baseType : Ty level sourceScope}
    {boundaryWitness gluedRaw : RawTerm sourceScope}
    {gluedValue :
      Term sourceCtx (Ty.glue baseType boundaryWitness) gluedRaw}
    (gluedAggregator : IsAggregatorSound gluedValue) :
    IsAggregatorSound (Term.glueElim modeIsUnivalent gluedValue) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atGlueElim_imp_sound strengthening
    (gluedAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.uaToEquiv` arm.
1-IH (proof of type identity) with positional universe-level data
(`innerLevel`/`innerLevelLt`), two carrier types, two raw type
witnesses. -/
theorem isAggregatorSound_uaToEquiv {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level sourceScope)
    (leftTyRaw rightTyRaw : RawTerm sourceScope)
    {proofRaw : RawTerm sourceScope}
    {proof :
      Term sourceCtx
        (Ty.id (Ty.universe innerLevel innerLevelLt) leftTyRaw
          rightTyRaw) proofRaw}
    (proofAggregator : IsAggregatorSound proof) :
    IsAggregatorSound
      (Term.uaToEquiv (context := sourceCtx) innerLevel innerLevelLt
        leftTy rightTy leftTyRaw rightTyRaw proof) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atUaToEquiv_imp_sound innerLevel
    innerLevelLt leftTy rightTy leftTyRaw rightTyRaw strengthening
    (proofAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.transp` arm.  2-IH
cubical transport: `typePath` (universe-valued path) + `sourceValue`
(input at sourceType); positional `modeIsUnivalent` /
`universeLevel` / `universeLevelLt` / `sourceType` / `targetType` /
`sourceTypeRaw` / `targetTypeRaw`. -/
theorem isAggregatorSound_transp {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level sourceScope)
    (sourceTypeRaw targetTypeRaw : RawTerm sourceScope)
    {pathRaw sourceRaw : RawTerm sourceScope}
    {typePath :
      Term sourceCtx
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw) pathRaw}
    {sourceValue : Term sourceCtx sourceType sourceRaw}
    (pathAggregator : IsAggregatorSound typePath)
    (sourceAggregator : IsAggregatorSound sourceValue) :
    IsAggregatorSound
      (Term.transp (context := sourceCtx) modeIsUnivalent universeLevel
        universeLevelLt sourceType targetType sourceTypeRaw
        targetTypeRaw typePath sourceValue) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atTransp_imp_sound modeIsUnivalent
    universeLevel universeLevelLt sourceType targetType sourceTypeRaw
    targetTypeRaw strengthening (pathAggregator strengthening)
    (sourceAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.app` arm.  2-IH
non-dependent application (function + argument). -/
theorem isAggregatorSound_app {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType codomainType : Ty level sourceScope}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {functionTerm :
      Term sourceCtx (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionAggregator : IsAggregatorSound functionTerm)
    (argumentAggregator : IsAggregatorSound argumentTerm) :
    IsAggregatorSound
      (Term.app (codomainType := codomainType) functionTerm
        argumentTerm) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atApp_imp_sound strengthening
    (functionAggregator strengthening)
    (argumentAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.appPi` arm.  2-IH
dependent application; codomain rides under the binder. -/
theorem isAggregatorSound_appPi {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {functionRaw argumentRaw : RawTerm sourceScope}
    {functionTerm :
      Term sourceCtx (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term sourceCtx domainType argumentRaw}
    (functionAggregator : IsAggregatorSound functionTerm)
    (argumentAggregator : IsAggregatorSound argumentTerm) :
    IsAggregatorSound
      (Term.appPi (codomainType := codomainType) functionTerm
        argumentTerm) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atAppPi_imp_sound strengthening
    (functionAggregator strengthening)
    (argumentAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.sessionSend` arm.
2-IH session send (`channel` + `payload`); `protocolStep` is a raw
witness threading through the leaf. -/
theorem isAggregatorSound_sessionSend {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (protocolStep : RawTerm sourceScope)
    {payloadType : Ty level sourceScope}
    {channelRaw payloadRaw : RawTerm sourceScope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    {payload : Term sourceCtx payloadType payloadRaw}
    (channelAggregator : IsAggregatorSound channel)
    (payloadAggregator : IsAggregatorSound payload) :
    IsAggregatorSound
      (Term.sessionSend protocolStep channel payload) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atSessionSend_imp_sound strengthening
    (channelAggregator strengthening)
    (payloadAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.sessionRecv` arm.
1-IH session receive (`channel` only); `protocolStep` carries the
raw witness through. -/
theorem isAggregatorSound_sessionRecv {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {protocolStep : RawTerm sourceScope}
    {channelRaw : RawTerm sourceScope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (channelAggregator : IsAggregatorSound channel) :
    IsAggregatorSound (Term.sessionRecv channel) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atSessionRecv_imp_sound strengthening
    (channelAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.glueIntro` arm.  2-IH
cubical glue introduction (`baseValue` + `partialValue`, both at
`baseType`); `modeIsUnivalent` is positional, `baseType` and
`boundaryWitness` are implicit (inferred from `baseValue`'s type). -/
theorem isAggregatorSound_glueIntro {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level sourceScope}
    {boundaryWitness : RawTerm sourceScope}
    {baseRaw partialRaw : RawTerm sourceScope}
    {baseValue : Term sourceCtx baseType baseRaw}
    {partialValue : Term sourceCtx baseType partialRaw}
    (baseAggregator : IsAggregatorSound baseValue)
    (partialAggregator : IsAggregatorSound partialValue) :
    IsAggregatorSound
      (Term.glueIntro (context := sourceCtx) modeIsUnivalent baseType
        boundaryWitness baseValue partialValue) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atGlueIntro_imp_sound modeIsUnivalent
    strengthening (baseAggregator strengthening)
    (partialAggregator strengthening) result success

/-- Headline aggregator soundness at the `Term.lam` arm.  Lambda
binder: body lives under `sourceCtx.cons domainType`.  The body
aggregator must absorb the strengthening through the lift; the
wrapper threads `bodyAggregator (strengthening.lift domainType ...)`. -/
theorem isAggregatorSound_lam {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType codomainType : Ty level sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body :
      Term (sourceCtx.cons domainType) codomainType.weaken bodyRaw}
    (bodyAggregator : IsAggregatorSound body) :
    IsAggregatorSound
      (Term.lam (context := sourceCtx) (domainType := domainType)
        (codomainType := codomainType) body) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atLam_imp_sound strengthening
    (fun targetDomainType domainSuccess bodyResult bodyRecurse =>
      bodyAggregator
        (strengthening.lift domainType targetDomainType domainSuccess)
        bodyResult bodyRecurse)
    result success

/-- Headline aggregator soundness at the `Term.lamPi` arm.
Dependent-Π lambda: body lives at codomain inside the binder. -/
theorem isAggregatorSound_lamPi {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body : Term (sourceCtx.cons domainType) codomainType bodyRaw}
    (bodyAggregator : IsAggregatorSound body) :
    IsAggregatorSound
      (Term.lamPi (context := sourceCtx) (domainType := domainType)
        (codomainType := codomainType) body) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atLamPi_imp_sound strengthening
    (fun targetDomainType domainSuccess bodyResult bodyRecurse =>
      bodyAggregator
        (strengthening.lift domainType targetDomainType domainSuccess)
        bodyResult bodyRecurse)
    result success

/-- Headline aggregator soundness at the `Term.pathLam` arm.  Cubical
path-lambda binder: body lives under `sourceCtx.cons Ty.interval`.
The interval slot is fixed (no domain strengthening), so the body
aggregator threads against `strengthening.lift Ty.interval
Ty.interval rfl`. -/
theorem isAggregatorSound_pathLam {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level sourceScope}
    {leftEndpoint rightEndpoint : RawTerm sourceScope}
    {bodyRaw : RawTerm (sourceScope + 1)}
    {body :
      Term (sourceCtx.cons Ty.interval) carrierType.weaken bodyRaw}
    (bodyAggregator : IsAggregatorSound body) :
    IsAggregatorSound
      (Term.pathLam (context := sourceCtx) modeIsUnivalent carrierType
        leftEndpoint rightEndpoint body) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atPathLam_imp_sound modeIsUnivalent
    strengthening
    (fun bodyResult bodyRecurse =>
      bodyAggregator
        (strengthening.lift Ty.interval Ty.interval rfl)
        bodyResult bodyRecurse)
    result success

end Term

end LeanFX2

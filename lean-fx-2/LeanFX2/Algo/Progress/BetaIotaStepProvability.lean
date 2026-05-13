import LeanFX2.Algo.WHNF
import LeanFX2.Term.Inversion
import LeanFX2.Reduction.Step

/-! # LeanFX2.Algo.Progress.BetaIotaStepProvability

Step-provability atoms for non-canonical β/ι forms (M05.B).
Each theorem packages an existing `Step` β/ι constructor as an
existential-result theorem: "if a typed term has the shape of a
β/ι-redex, then it can take a Step." Covers Π/Σ β, closed-type ι
(bool/nat/list/option/either elim/match), J-on-refl, modal β,
cubical β (pathApp/glueElim/transp), record/refine/codata/cumul β.

## Root status

β/ι step-provability atoms; feed the headline Progress theorem.
Zero-axiom under strict policy. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-! ## Step-provability for non-canonical β/ι forms (M05.B)

These atoms package the existing Step β/ι constructors as
existential-result theorems: "if a typed term has the shape
of a non-canonical β-redex, then it can take a Step."  Each
atom is mechanical Step-witness packaging — the load-bearing
work lives in `Reduction/Step.lean` (the β/ι ctor).  These
existentials feed the headline Progress theorem's β/ι cases.
-/

/-- β-app step provability: a non-dep β-redex `(λ. body) arg`
can take a Step.  Packages `Step.betaApp` as an existential.
First atom of the M05.B.1 Π/Σ β cohort. -/
theorem Term.app_lam_steps {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)} {argumentRaw : RawTerm scope}
    (bodyTerm :
      Term (context.cons domainType) codomainType.weaken bodyRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.app (Term.lam (codomainType := codomainType) bodyTerm)
                     argumentTerm) target :=
  ⟨_, _, _, Step.betaApp bodyTerm argumentTerm⟩

/-- β-appPi step provability: a dependent Π β-redex
`(λ. body) arg` at the dependent Π type can take a Step.
Packages `Step.betaAppPi` as an existential.  The dependent
codomain `codomainType : Ty level (scope + 1)` distinguishes
this from the non-dep `app_lam_steps`; same witness shape via
`Step.betaAppPi`.  Second atom of the M05.B.1 Π/Σ β cohort. -/
theorem Term.appPi_lamPi_steps {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)} {argumentRaw : RawTerm scope}
    (bodyTerm : Term (context.cons domainType) codomainType bodyRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.appPi (Term.lamPi (domainType := domainType) bodyTerm)
                       argumentTerm) target :=
  ⟨_, _, _, Step.betaAppPi bodyTerm argumentTerm⟩

/-- β-fst step provability: a Σ first-projection of a pair
`fst (pair fv sv)` can take a Step.  Packages `Step.betaFstPair`
as an existential.  First atom of the M05.B.2 Σ projection cohort. -/
theorem Term.fst_pair_steps {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (firstValue : Term context firstType firstRaw)
    (secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.fst (Term.pair (secondType := secondType)
                                firstValue secondValue)) target :=
  ⟨_, _, _, Step.betaFstPair firstValue secondValue⟩

/-- β-snd step provability: a Σ second-projection of a pair
`snd (pair fv sv)` can take a Step.  Packages `Step.betaSndPair`
as an existential.  Second atom of the M05.B.2 Σ projection cohort. -/
theorem Term.snd_pair_steps {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (firstValue : Term context firstType firstRaw)
    (secondValue :
      Term context (secondType.subst0 firstType firstRaw) secondRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.snd (Term.pair (secondType := secondType)
                                firstValue secondValue)) target :=
  ⟨_, _, _, Step.betaSndPair firstValue secondValue⟩

/-! ## Closed-type ι-rule step provability (M05.B.3 cohort) -/

/-- ι-boolElim-true step provability: `boolElim true t e` reduces.
Packages `Step.iotaBoolElimTrue`. -/
theorem Term.boolElim_boolTrue_steps {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {thenRaw elseRaw : RawTerm scope}
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.boolElim (motiveType := motiveType)
              Term.boolTrue thenBranch elseBranch) target :=
  ⟨_, _, _, Step.iotaBoolElimTrue thenBranch elseBranch⟩

/-- ι-boolElim-false step provability: `boolElim false t e` reduces.
Packages `Step.iotaBoolElimFalse`. -/
theorem Term.boolElim_boolFalse_steps {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {thenRaw elseRaw : RawTerm scope}
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.boolElim (motiveType := motiveType)
              Term.boolFalse thenBranch elseBranch) target :=
  ⟨_, _, _, Step.iotaBoolElimFalse thenBranch elseBranch⟩

/-- ι-natElim-zero step provability: `natElim zero z s` reduces.
Packages `Step.iotaNatElimZero`. -/
theorem Term.natElim_natZero_steps {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.natElim Term.natZero zeroBranch succBranch) target :=
  ⟨_, _, _, Step.iotaNatElimZero zeroBranch succBranch⟩

/-- ι-natElim-succ step provability: `natElim (succ n) z s` reduces.
Packages `Step.iotaNatElimSucc`. -/
theorem Term.natElim_natSucc_steps {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {predecessorRaw zeroRaw succRaw : RawTerm scope}
    (predecessor : Term context Ty.nat predecessorRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.natElim (Term.natSucc predecessor) zeroBranch succBranch)
           target :=
  ⟨_, _, _, Step.iotaNatElimSucc predecessor zeroBranch succBranch⟩

/-- ι-natRec-zero step provability: `natRec zero z s` reduces.
Packages `Step.iotaNatRecZero`. -/
theorem Term.natRec_natZero_steps {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.natRec Term.natZero zeroBranch succBranch) target :=
  ⟨_, _, _, Step.iotaNatRecZero zeroBranch succBranch⟩

/-- ι-natRec-succ step provability: `natRec (succ n) z s` reduces.
Packages `Step.iotaNatRecSucc`. -/
theorem Term.natRec_natSucc_steps {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {predecessorRaw zeroRaw succRaw : RawTerm scope}
    (predecessor : Term context Ty.nat predecessorRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.natRec (Term.natSucc predecessor) zeroBranch succBranch)
           target :=
  ⟨_, _, _, Step.iotaNatRecSucc predecessor zeroBranch succBranch⟩

/-- ι-listElim-nil step provability: `listElim nil n c` reduces.
Packages `Step.iotaListElimNil`. -/
theorem Term.listElim_listNil_steps {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {nilRaw consRaw : RawTerm scope}
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.listElim (elementType := elementType) Term.listNil
              nilBranch consBranch) target :=
  ⟨_, _, _, Step.iotaListElimNil nilBranch consBranch⟩

/-- ι-listElim-cons step provability: `listElim (cons h t) n c` reduces.
Packages `Step.iotaListElimCons`. -/
theorem Term.listElim_listCons_steps {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {headRaw tailRaw nilRaw consRaw : RawTerm scope}
    (headTerm : Term context elementType headRaw)
    (tailTerm : Term context (Ty.listType elementType) tailRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.listElim (Term.listCons headTerm tailTerm)
              nilBranch consBranch) target :=
  ⟨_, _, _, Step.iotaListElimCons headTerm tailTerm nilBranch consBranch⟩

/-- ι-optionMatch-none step provability: `optionMatch none n s` reduces.
Packages `Step.iotaOptionMatchNone`. -/
theorem Term.optionMatch_optionNone_steps {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {noneRaw someRaw : RawTerm scope}
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.optionMatch (elementType := elementType) Term.optionNone
              noneBranch someBranch) target :=
  ⟨_, _, _, Step.iotaOptionMatchNone noneBranch someBranch⟩

/-- ι-optionMatch-some step provability: `optionMatch (some v) n s` reduces.
Packages `Step.iotaOptionMatchSome`. -/
theorem Term.optionMatch_optionSome_steps {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {valueRaw noneRaw someRaw : RawTerm scope}
    (valueTerm : Term context elementType valueRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.optionMatch (Term.optionSome valueTerm)
              noneBranch someBranch) target :=
  ⟨_, _, _, Step.iotaOptionMatchSome valueTerm noneBranch someBranch⟩

/-- ι-eitherMatch-inl step provability: `eitherMatch (inl v) lb rb` reduces.
Packages `Step.iotaEitherMatchInl`. -/
theorem Term.eitherMatch_eitherInl_steps {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {valueRaw leftRaw rightRaw : RawTerm scope}
    (valueTerm : Term context leftType valueRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.eitherMatch (Term.eitherInl (rightType := rightType) valueTerm)
              leftBranch rightBranch) target :=
  ⟨_, _, _, Step.iotaEitherMatchInl valueTerm leftBranch rightBranch⟩

/-- ι-eitherMatch-inr step provability: `eitherMatch (inr v) lb rb` reduces.
Packages `Step.iotaEitherMatchInr`. -/
theorem Term.eitherMatch_eitherInr_steps {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {valueRaw leftRaw rightRaw : RawTerm scope}
    (valueTerm : Term context rightType valueRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.eitherMatch (Term.eitherInr (leftType := leftType) valueTerm)
              leftBranch rightBranch) target :=
  ⟨_, _, _, Step.iotaEitherMatchInr valueTerm leftBranch rightBranch⟩

/-! ## J-on-refl step provability (M05.B.4 cohort) -/

/-- ι-idJ-refl step provability: `idJ base (refl rt)` reduces to `base`.
Packages `Step.iotaIdJRefl`. -/
theorem Term.idJ_refl_steps {context : Ctx mode level scope}
    {carrier : Ty level scope} {endpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.idJ (carrier := carrier)
                     (leftEndpoint := endpoint)
                     (rightEndpoint := endpoint)
              baseCase
              (Term.refl carrier endpoint)) target :=
  ⟨_, _, _, Step.iotaIdJRefl carrier endpoint baseCase⟩

-- BLOCKED: M05.B.4.2 `Term.oeqJ_oeqRefl_steps` requires Step ctor
-- `Step.iotaOeqJRefl` for `oeqJ base (oeqRefl rt) ⟶ base` which does
-- not exist in the typed kernel today; only the cong rules
-- `Step.oeqJBase` and `Step.oeqJWitness` are shipped at the typed
-- layer.  Adding `Step.iotaOeqJRefl` is out of scope for M05.B
-- (spec rule).  Atom skipped pending typed observational-equality ι
-- ratchet.

/-- ι-idStrictRec-refl step provability: `idStrictRec base
(idStrictRefl rt)` reduces to `base`.  Packages
`Step.iotaIdStrictRecRefl`. -/
theorem Term.idStrictRec_idStrictRefl_steps {context : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope} {endpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.idStrictRec (carrier := carrier)
                             (leftEndpoint := endpoint)
                             (rightEndpoint := endpoint)
              modeIsStrict
              baseCase
              (Term.idStrictRefl modeIsStrict carrier endpoint)) target :=
  ⟨_, _, _, Step.iotaIdStrictRecRefl modeIsStrict carrier endpoint baseCase⟩

/-! ## Modal β step provability (M05.B.5 cohort) -/

/-- β-modElim-modIntro step provability: `modElim (modIntro v)` reduces.
Packages `Step.betaModElimIntro`. -/
theorem Term.modElim_modIntro_steps {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.modElim (Term.modIntro innerTerm)) target :=
  ⟨_, _, _, Step.betaModElimIntro innerTerm⟩

-- BLOCKED: M05.B.5.2 `Term.subsume_modIntro_steps` requires Step ctor
-- `Step.betaSubsumeIntro` for `subsume (modIntro v) ⟶ ...` which does
-- not exist in the typed kernel today; only the cong rule
-- `Step.subsumeInner` is shipped at the typed layer.  Adding
-- `Step.betaSubsumeIntro` is out of scope for M05.B (spec rule).
-- Atom skipped pending typed subsumption-β ratchet.

/-! ## Cubical β step provability (M05.B.6 cohort) -/

/-- β-pathApp-pathLam step provability: `(pathLam body) @ i` reduces.
Packages `Step.betaPathApp`. -/
theorem Term.pathApp_pathLam_steps {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {bodyRaw : RawTerm (scope + 1)}
    {intervalRaw : RawTerm scope}
    (bodyTerm :
      Term (context.cons Ty.interval) carrierType.weaken bodyRaw)
    (intervalTerm : Term context Ty.interval intervalRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step
        (Term.pathApp modeIsUnivalent
          (Term.pathLam modeIsUnivalent carrierType leftEndpoint rightEndpoint
            bodyTerm)
          intervalTerm) target :=
  ⟨_, _, _, Step.betaPathApp modeIsUnivalent bodyTerm intervalTerm⟩

/-- β-glueElim-glueIntro step provability: `glueElim (glueIntro ...)`
reduces.  Packages `Step.betaGlueElimIntro`. -/
theorem Term.glueElim_glueIntro_steps {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {baseRaw partialRaw : RawTerm scope}
    (baseValue : Term context baseType baseRaw)
    (partialValue : Term context baseType partialRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step
        (Term.glueElim modeIsUnivalent
          (Term.glueIntro modeIsUnivalent baseType boundaryWitness
            baseValue partialValue)) target :=
  ⟨_, _, _, Step.betaGlueElimIntro modeIsUnivalent baseValue partialValue⟩

/-- β-transp-pathRefl step provability: `transp (pathLam typeRaw.weaken)
v` reduces (transport along constant type path is identity).
Packages `Step.transpReflBeta`. -/
theorem Term.transp_pathRefl_steps {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType : Ty level scope)
    {typeRaw sourceRaw : RawTerm scope}
    (typePath :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          typeRaw typeRaw)
        (RawTerm.pathLam typeRaw.weaken))
    (sourceValue : Term context sourceType sourceRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step
        (Term.transp modeIsUnivalent universeLevel universeLevelLt
          sourceType sourceType
          typeRaw typeRaw typePath sourceValue) target :=
  ⟨_, _, _,
    Step.transpReflBeta modeIsUnivalent universeLevel universeLevelLt
      sourceType typePath sourceValue⟩

/-! ## Record/Refine/Codata/Equiv/Cumul β step provability
(M05.B.7 cohort) -/

/-- β-recordProj-recordIntro step provability: `recordProj
(recordIntro f)` reduces.  Packages `Step.betaRecordProjIntro`. -/
theorem Term.recordProj_recordIntro_steps {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (firstField : Term context singleFieldType firstRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.recordProj (Term.recordIntro firstField)) target :=
  ⟨_, _, _, Step.betaRecordProjIntro firstField⟩

/-- β-refineElim-refineIntro step provability: `refineElim
(refineIntro p v proof)` reduces.  Packages `Step.betaRefineElimIntro`. -/
theorem Term.refineElim_refineIntro_steps {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    (baseValue : Term context baseType valueRaw)
    (predicateProof : Term context Ty.unit proofRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.refineElim
              (Term.refineIntro predicate baseValue predicateProof))
           target :=
  ⟨_, _, _, Step.betaRefineElimIntro predicate baseValue predicateProof⟩

/-- β-codataDest-codataUnfold step provability: `codataDest
(codataUnfold s t)` reduces to `t s`.  Packages
`Step.betaCodataDestUnfold`. -/
theorem Term.codataDest_codataUnfold_steps {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (initialState : Term context stateType stateRaw)
    (transition :
      Term context (Ty.arrow stateType outputType) transitionRaw) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.codataDest (Term.codataUnfold initialState transition))
           target :=
  ⟨_, _, _, Step.betaCodataDestUnfold initialState transition⟩

-- BLOCKED: M05.B.7.4 `Term.equivApp_equivIntroHet_steps` requires
-- Step ctor `Step.betaEquivAppIntro` for `equivApp (equivIntroHet
-- f b lInv rInv) arg ⟶ f arg` which does not exist in the typed
-- kernel today; only the cong rules `Step.equivAppEquiv` and
-- `Step.equivAppArgument` are shipped at the typed layer.  Adding
-- `Step.betaEquivAppIntro` is out of scope for M05.B (spec rule).
-- Atom skipped pending typed equivalence-β ratchet.

/-- cumulUp-inner step provability (cong-rule packaging): given
an inner Step `Step typeCodeSource typeCodeTarget` between two
type codes at the lower universe, the wrapping `cumulUp` lifts.
Packages `Step.cumulUpInner`.  Unlike the β/ι atoms above, this
atom takes the inner Step as an explicit hypothesis — `cumulUp`
has no β rule (it's the cumulativity injection, not an
elim/intro pair) so this atom captures the cong rule's existential
shape rather than a redex-firing shape.  Last atom of the M05.B
batch. -/
theorem Term.cumulUp_inner_steps {context : Ctx mode level scope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeSourceRaw codeTargetRaw : RawTerm scope}
    {typeCodeSource :
      Term context (Ty.universe lowerLevel levelLeLow) codeSourceRaw}
    {typeCodeTarget :
      Term context (Ty.universe lowerLevel levelLeLow) codeTargetRaw}
    (innerStep : Step typeCodeSource typeCodeTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.cumulUp (context := context)
                         lowerLevel higherLevel cumulMonotone
                         levelLeLow levelLeHigh typeCodeSource) target :=
  ⟨_, _, _,
    Step.cumulUpInner lowerLevel higherLevel cumulMonotone
      levelLeLow levelLeHigh innerStep⟩


end LeanFX2

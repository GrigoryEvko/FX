import LeanFX2.Algo.WHNF
import LeanFX2.Term.Inversion
import LeanFX2.Reduction.Step

/-! # LeanFX2.Algo.Progress.CongRuleLifters

Eliminator-eliminand cong-rule lifters (M05.C, #1644). For every
typed eliminator whose eliminand position is reducible, package
the corresponding `Step.<elim>{Scrutinee/Cong/Path/Value/...}`
cong constructor as an existential-result theorem: given an inner
Step on the eliminand, produce an existential Step on the outer
eliminator term.

## Root status

Cong-rule completeness audit atoms; feed the headline Progress
theorem. Zero-axiom under strict policy. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-! ## M05.C — eliminator-eliminand cong-rule lifters (#1644)

Cong-rule completeness audit: for every typed eliminator whose
eliminand position is reducible, package the corresponding
`Step.<elim>{Scrutinee/Cong/Path/Value/...}` cong constructor as
an existential-result theorem.  Each atom takes an inner Step on
the eliminand and returns an existential Step on the outer
eliminator term.

These atoms are the "scrutinee-step lifters" that complete the
M05.B step-provability cohort: M05.B handles the
ELIMINATOR-ON-CANONICAL case (β/ι firing); M05.C handles the
ELIMINATOR-ON-REDUCING-ELIMINAND case (cong rule lifting an
inner Step to the outer eliminator).

Each lifter is a one-line cong-rule packaging — the load-bearing
work lives in `Reduction/Step.lean` (the cong ctor).  The atom
captures the cong rule's existential shape for use by callers
that need to step an eliminator whose eliminand is itself
reducing.

Note on the "audit completeness" interpretation: the headline
M05.D `Term.progress_or_step` does NOT directly invoke these
lifters because `Term.isWHNF` is shallow — an eliminator with a
non-canonical (e.g. variable, neutral, or itself-an-eliminator)
eliminand reports `isWHNF = true` regardless of whether the
eliminand could itself take a Step.  M05.C exists as
infrastructure for downstream consumers (e.g. an eventual
`headStep?` totality lemma or a "reduce-to-WHNF" function) that
need to recurse INTO the eliminand to fire its inner Step.
-/

/-- Cong-rule lifter: a Step inside the function position of a
non-dep application lifts to a Step on the outer `Term.app`.
Packages `Step.appLeft`. -/
theorem Term.app_function_steps_lift {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRawSource functionRawTarget argumentRaw : RawTerm scope}
    {functionTermSource :
      Term context (Ty.arrow domainType codomainType) functionRawSource}
    {functionTermTarget :
      Term context (Ty.arrow domainType codomainType) functionRawTarget}
    (argumentTerm : Term context domainType argumentRaw)
    (innerStep : Step functionTermSource functionTermTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.app functionTermSource argumentTerm) target :=
  ⟨_, _, _, Step.appLeft (argumentTerm := argumentTerm) innerStep⟩

/-- Cong-rule lifter: a Step inside the function position of a
dependent Π application lifts to a Step on the outer `Term.appPi`.
Packages `Step.appPiLeft`. -/
theorem Term.appPi_function_steps_lift {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {functionRawSource functionRawTarget argumentRaw : RawTerm scope}
    {functionTermSource :
      Term context (Ty.piTy domainType codomainType) functionRawSource}
    {functionTermTarget :
      Term context (Ty.piTy domainType codomainType) functionRawTarget}
    (argumentTerm : Term context domainType argumentRaw)
    (innerStep : Step functionTermSource functionTermTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.appPi functionTermSource argumentTerm) target :=
  ⟨_, _, _, Step.appPiLeft (argumentTerm := argumentTerm) innerStep⟩

/-- Cong-rule lifter: a Step inside a Σ first-projection's pair
position lifts to a Step on the outer `Term.fst`.  Packages
`Step.fstCong`. -/
theorem Term.fst_pair_steps_lift {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRawSource pairRawTarget : RawTerm scope}
    {pairTermSource :
      Term context (Ty.sigmaTy firstType secondType) pairRawSource}
    {pairTermTarget :
      Term context (Ty.sigmaTy firstType secondType) pairRawTarget}
    (innerStep : Step pairTermSource pairTermTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.fst (secondType := secondType) pairTermSource) target :=
  ⟨_, _, _, Step.fstCong innerStep⟩

/-- Cong-rule lifter: a Step inside a Σ second-projection's pair
position lifts to a Step on the outer `Term.snd`.  Packages
`Step.sndCong`. -/
theorem Term.snd_pair_steps_lift {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRawSource pairRawTarget : RawTerm scope}
    {pairTermSource :
      Term context (Ty.sigmaTy firstType secondType) pairRawSource}
    {pairTermTarget :
      Term context (Ty.sigmaTy firstType secondType) pairRawTarget}
    (innerStep : Step pairTermSource pairTermTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.snd (secondType := secondType) pairTermSource) target :=
  ⟨_, _, _, Step.sndCong innerStep⟩

/-- Cong-rule lifter: a Step inside a `boolElim` scrutinee lifts
to a Step on the outer `Term.boolElim`.  Packages
`Step.boolElimScrutinee`. -/
theorem Term.boolElim_scrutinee_steps_lift {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRawSource scrutineeRawTarget thenRaw elseRaw : RawTerm scope}
    {scrutineeSource : Term context Ty.bool scrutineeRawSource}
    {scrutineeTarget : Term context Ty.bool scrutineeRawTarget}
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw)
    (innerStep : Step scrutineeSource scrutineeTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.boolElim (motiveType := motiveType)
              scrutineeSource thenBranch elseBranch) target :=
  ⟨_, _, _,
    Step.boolElimScrutinee (thenBranch := thenBranch)
      (elseBranch := elseBranch) innerStep⟩

/-- Cong-rule lifter: a Step inside a `natElim` scrutinee lifts
to a Step on the outer `Term.natElim`.  Packages
`Step.natElimScrutinee`. -/
theorem Term.natElim_scrutinee_steps_lift {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRawSource scrutineeRawTarget zeroRaw succRaw : RawTerm scope}
    {scrutineeSource : Term context Ty.nat scrutineeRawSource}
    {scrutineeTarget : Term context Ty.nat scrutineeRawTarget}
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
    (innerStep : Step scrutineeSource scrutineeTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.natElim scrutineeSource zeroBranch succBranch) target :=
  ⟨_, _, _,
    Step.natElimScrutinee (zeroBranch := zeroBranch)
      (succBranch := succBranch) innerStep⟩

/-- Cong-rule lifter: a Step inside a `natRec` scrutinee lifts
to a Step on the outer `Term.natRec`.  Packages
`Step.natRecScrutinee`. -/
theorem Term.natRec_scrutinee_steps_lift {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRawSource scrutineeRawTarget zeroRaw succRaw : RawTerm scope}
    {scrutineeSource : Term context Ty.nat scrutineeRawSource}
    {scrutineeTarget : Term context Ty.nat scrutineeRawTarget}
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    (innerStep : Step scrutineeSource scrutineeTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.natRec scrutineeSource zeroBranch succBranch) target :=
  ⟨_, _, _,
    Step.natRecScrutinee (zeroBranch := zeroBranch)
      (succBranch := succBranch) innerStep⟩

/-- Cong-rule lifter: a Step inside a `listElim` scrutinee lifts
to a Step on the outer `Term.listElim`.  Packages
`Step.listElimScrutinee`. -/
theorem Term.listElim_scrutinee_steps_lift {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRawSource scrutineeRawTarget nilRaw consRaw : RawTerm scope}
    {scrutineeSource :
      Term context (Ty.listType elementType) scrutineeRawSource}
    {scrutineeTarget :
      Term context (Ty.listType elementType) scrutineeRawTarget}
    (nilBranch : Term context motiveType nilRaw)
    (consBranch :
      Term context (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw)
    (innerStep : Step scrutineeSource scrutineeTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.listElim scrutineeSource nilBranch consBranch) target :=
  ⟨_, _, _,
    Step.listElimScrutinee (nilBranch := nilBranch)
      (consBranch := consBranch) innerStep⟩

/-- Cong-rule lifter: a Step inside an `optionMatch` scrutinee
lifts to a Step on the outer `Term.optionMatch`.  Packages
`Step.optionMatchScrutinee`. -/
theorem Term.optionMatch_scrutinee_steps_lift
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRawSource scrutineeRawTarget noneRaw someRaw : RawTerm scope}
    {scrutineeSource :
      Term context (Ty.optionType elementType) scrutineeRawSource}
    {scrutineeTarget :
      Term context (Ty.optionType elementType) scrutineeRawTarget}
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    (innerStep : Step scrutineeSource scrutineeTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.optionMatch scrutineeSource noneBranch someBranch) target :=
  ⟨_, _, _,
    Step.optionMatchScrutinee (noneBranch := noneBranch)
      (someBranch := someBranch) innerStep⟩

/-- Cong-rule lifter: a Step inside an `eitherMatch` scrutinee
lifts to a Step on the outer `Term.eitherMatch`.  Packages
`Step.eitherMatchScrutinee`. -/
theorem Term.eitherMatch_scrutinee_steps_lift
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRawSource scrutineeRawTarget leftRaw rightRaw : RawTerm scope}
    {scrutineeSource :
      Term context (Ty.eitherType leftType rightType) scrutineeRawSource}
    {scrutineeTarget :
      Term context (Ty.eitherType leftType rightType) scrutineeRawTarget}
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw)
    (innerStep : Step scrutineeSource scrutineeTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.eitherMatch scrutineeSource leftBranch rightBranch) target :=
  ⟨_, _, _,
    Step.eitherMatchScrutinee (leftBranch := leftBranch)
      (rightBranch := rightBranch) innerStep⟩

/-- Cong-rule lifter: a Step inside an `idJ` witness lifts to a
Step on the outer `Term.idJ`.  Packages `Step.idJWitness`. -/
theorem Term.idJ_witness_steps_lift {context : Ctx mode level scope}
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRawSource witnessRawTarget : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    {witnessSource :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRawSource}
    {witnessTarget :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRawTarget}
    (innerStep : Step witnessSource witnessTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.idJ baseCase witnessSource) target :=
  ⟨_, _, _, Step.idJWitness baseCase innerStep⟩

/-- Cong-rule lifter: a Step inside a `modElim` payload lifts to
a Step on the outer `Term.modElim`.  Packages
`Step.modElimInner`. -/
theorem Term.modElim_inner_steps_lift {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRawSource innerRawTarget : RawTerm scope}
    {innerSource : Term context innerType innerRawSource}
    {innerTarget : Term context innerType innerRawTarget}
    (innerStep : Step innerSource innerTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.modElim innerSource) target :=
  ⟨_, _, _, Step.modElimInner innerStep⟩

/-- Cong-rule lifter: a Step inside a `pathApp` path-position
lifts to a Step on the outer `Term.pathApp`.  Packages
`Step.pathAppPath`. -/
theorem Term.pathApp_path_steps_lift {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRawSource pathRawTarget intervalRaw : RawTerm scope}
    {pathSource :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRawSource}
    {pathTarget :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRawTarget}
    (intervalTerm : Term context Ty.interval intervalRaw)
    (innerStep : Step pathSource pathTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.pathApp modeIsUnivalent pathSource intervalTerm) target :=
  ⟨_, _, _,
    Step.pathAppPath modeIsUnivalent (intervalTerm := intervalTerm) innerStep⟩

/-- Cong-rule lifter: a Step inside a `glueElim` glued value lifts
to a Step on the outer `Term.glueElim`.  Packages
`Step.glueElimValue`. -/
theorem Term.glueElim_value_steps_lift {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness : RawTerm scope}
    {gluedRawSource gluedRawTarget : RawTerm scope}
    {gluedSource :
      Term context (Ty.glue baseType boundaryWitness) gluedRawSource}
    {gluedTarget :
      Term context (Ty.glue baseType boundaryWitness) gluedRawTarget}
    (innerStep : Step gluedSource gluedTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.glueElim modeIsUnivalent gluedSource) target :=
  ⟨_, _, _, Step.glueElimValue modeIsUnivalent innerStep⟩

/-- Cong-rule lifter: a Step inside a `recordProj` record value
lifts to a Step on the outer `Term.recordProj`.  Packages
`Step.recordProjRecord`. -/
theorem Term.recordProj_record_steps_lift
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRawSource recordRawTarget : RawTerm scope}
    {recordSource :
      Term context (Ty.record singleFieldType) recordRawSource}
    {recordTarget :
      Term context (Ty.record singleFieldType) recordRawTarget}
    (innerStep : Step recordSource recordTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.recordProj recordSource) target :=
  ⟨_, _, _, Step.recordProjRecord innerStep⟩

/-- Cong-rule lifter: a Step inside a `refineElim` refined value
lifts to a Step on the outer `Term.refineElim`.  Packages
`Step.refineElimValue`. -/
theorem Term.refineElim_value_steps_lift {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRawSource refinedRawTarget : RawTerm scope}
    {refinedSource :
      Term context (Ty.refine baseType predicate) refinedRawSource}
    {refinedTarget :
      Term context (Ty.refine baseType predicate) refinedRawTarget}
    (innerStep : Step refinedSource refinedTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.refineElim refinedSource) target :=
  ⟨_, _, _, Step.refineElimValue innerStep⟩

/-- Cong-rule lifter: a Step inside a `codataDest` codata value
lifts to a Step on the outer `Term.codataDest`.  Packages
`Step.codataDestValue`. -/
theorem Term.codataDest_value_steps_lift {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRawSource codataRawTarget : RawTerm scope}
    {codataSource :
      Term context (Ty.codata stateType outputType) codataRawSource}
    {codataTarget :
      Term context (Ty.codata stateType outputType) codataRawTarget}
    (innerStep : Step codataSource codataTarget) :
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.codataDest codataSource) target :=
  ⟨_, _, _, Step.codataDestValue innerStep⟩


end LeanFX2

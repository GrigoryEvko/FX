import LeanFX2.Reduction.Step
import LeanFX2.Reduction.StepStar
import LeanFX2.Reduction.RawPar

/-! # Reduction/ParRed — Tait-Martin-Löf parallel reduction.

`Step.par source target : Prop` reduces all subterms simultaneously,
including any contracted redex.  Reflexive (zero parallel-steps =
identity) and the standard vehicle for proving confluence: the
diamond property holds for `Step.par`, and `Step.par`'s transitive
closure equals `StepStar`'s.

## Two-Ty + two-RawTerm signature

Mirrors `Step` / `StepStar`: source/target Ty + raw indices are
free.  This handles dep-position cong rules (`pair`, `appPi`,
`snd`, etc.) where parallel reduction in one position changes the
required type of another.

## Constructors (overview)

* **Reflexivity**: `refl t : Step.par t t`
* **Cong rules**: every Term constructor admits a parallel-cong
  rule that reduces every position simultaneously.
* **β rules** (shallow): `betaApp`, `betaAppPi`, `betaFstPair`,
  `betaSndPair` — reducing-with-substitution.
* **β rules** (deep): `betaAppDeep`, `betaAppPiDeep`, `betaFstPairDeep`,
  `betaSndPairDeep` — function/pair parallel-reduces *to* a redex,
  then contracts.
* **ι rules** (shallow): per eliminator, fire on canonical scrutinee.
* **ι rules** (deep): scrutinee parallel-reduces to canonical, then
  fire.

## η deliberately omitted

Stays in opt-in `Reduction/Eta.lean` (when added).  βι confluence
proof should not carry η weight per architectural commitment.

## Step.toPar

Each `Step` constructor lifts to `Step.par` by inserting `refl` at
unchanging positions.  Used in `StepStar → Step.parStar` lifting
(Layer 3).
-/

namespace LeanFX2

/-- Parallel reduction.  Two-Ty + two-RawTerm signature; each ctor
reduces all subterms simultaneously.  Source/target indices are
fully independent. -/
inductive Step.par :
    ∀ {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {sourceType targetType : Ty level scope}
      {sourceRaw targetRaw : RawTerm scope},
      Term context sourceType sourceRaw →
      Term context targetType targetRaw →
      Prop
  /-- Reflexivity: zero parallel reductions. -/
  | refl {mode level scope} {context : Ctx mode level scope}
      {someType : Ty level scope} {someRaw : RawTerm scope}
      (someTerm : Term context someType someRaw) :
      Step.par someTerm someTerm
  /-- Parallel-cong: non-dep application reduces in both positions. -/
  | app {mode level scope} {context : Ctx mode level scope}
      {domainType codomainType : Ty level scope}
      {functionRawSource functionRawTarget
       argumentRawSource argumentRawTarget : RawTerm scope}
      {functionTermSource :
        Term context (Ty.arrow domainType codomainType) functionRawSource}
      {functionTermTarget :
        Term context (Ty.arrow domainType codomainType) functionRawTarget}
      {argumentTermSource : Term context domainType argumentRawSource}
      {argumentTermTarget : Term context domainType argumentRawTarget} :
      Step.par functionTermSource functionTermTarget →
      Step.par argumentTermSource argumentTermTarget →
      Step.par (Term.app functionTermSource argumentTermSource)
               (Term.app functionTermTarget argumentTermTarget)
  /-- Parallel-cong: lam reduces in body. -/
  | lam {mode level scope} {context : Ctx mode level scope}
      {domainType codomainType : Ty level scope}
      {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
      {bodySource :
        Term (context.cons domainType) codomainType.weaken bodyRawSource}
      {bodyTarget :
        Term (context.cons domainType) codomainType.weaken bodyRawTarget} :
      Step.par bodySource bodyTarget →
      Step.par (Term.lam (codomainType := codomainType) bodySource)
               (Term.lam (codomainType := codomainType) bodyTarget)
  /-- Parallel-cong: lamPi reduces in body. -/
  | lamPi {mode level scope} {context : Ctx mode level scope}
      {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
      {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
      {bodySource :
        Term (context.cons domainType) codomainType bodyRawSource}
      {bodyTarget :
        Term (context.cons domainType) codomainType bodyRawTarget} :
      Step.par bodySource bodyTarget →
      Step.par (Term.lamPi (domainType := domainType) bodySource)
               (Term.lamPi (domainType := domainType) bodyTarget)
  /-- Parallel-cong: appPi reduces in both positions. -/
  | appPi {mode level scope} {context : Ctx mode level scope}
      {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
      {functionRawSource functionRawTarget
       argumentRawSource argumentRawTarget : RawTerm scope}
      {functionTermSource :
        Term context (Ty.piTy domainType codomainType) functionRawSource}
      {functionTermTarget :
        Term context (Ty.piTy domainType codomainType) functionRawTarget}
      {argumentTermSource : Term context domainType argumentRawSource}
      {argumentTermTarget : Term context domainType argumentRawTarget} :
      Step.par functionTermSource functionTermTarget →
      Step.par argumentTermSource argumentTermTarget →
      Step.par (Term.appPi functionTermSource argumentTermSource)
               (Term.appPi functionTermTarget argumentTermTarget)
  /-- Parallel-cong: pair reduces in both components.  secondTarget's
  Ty adjusts to firstTarget's raw form. -/
  | pair {mode level scope} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {firstRawSource firstRawTarget
       secondRawSource secondRawTarget : RawTerm scope}
      {firstValueSource : Term context firstType firstRawSource}
      {firstValueTarget : Term context firstType firstRawTarget}
      {secondValueSource :
        Term context (secondType.subst0 firstType firstRawSource) secondRawSource}
      {secondValueTarget :
        Term context (secondType.subst0 firstType firstRawTarget) secondRawTarget} :
      Step.par firstValueSource firstValueTarget →
      Step.par secondValueSource secondValueTarget →
      Step.par (Term.pair (secondType := secondType) firstValueSource secondValueSource)
               (Term.pair (secondType := secondType) firstValueTarget secondValueTarget)
  /-- Parallel-cong: fst reduces in argument. -/
  | fst {mode level scope} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {pairRawSource pairRawTarget : RawTerm scope}
      {pairTermSource :
        Term context (Ty.sigmaTy firstType secondType) pairRawSource}
      {pairTermTarget :
        Term context (Ty.sigmaTy firstType secondType) pairRawTarget} :
      Step.par pairTermSource pairTermTarget →
      Step.par (Term.fst (secondType := secondType) pairTermSource)
               (Term.fst (secondType := secondType) pairTermTarget)
  /-- Parallel-cong: snd reduces in argument.  Source/target Ty differ
  via `RawTerm.fst pairRawSource` vs `RawTerm.fst pairRawTarget` —
  accommodated by two-Ty signature. -/
  | snd {mode level scope} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {pairRawSource pairRawTarget : RawTerm scope}
      {pairTermSource :
        Term context (Ty.sigmaTy firstType secondType) pairRawSource}
      {pairTermTarget :
        Term context (Ty.sigmaTy firstType secondType) pairRawTarget} :
      Step.par pairTermSource pairTermTarget →
      Step.par (Term.snd (secondType := secondType) pairTermSource)
               (Term.snd (secondType := secondType) pairTermTarget)
  /-- Parallel-cong: boolElim reduces in all three positions. -/
  | boolElim {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRawSource scrutineeRawTarget
       thenRawSource thenRawTarget
       elseRawSource elseRawTarget : RawTerm scope}
      {scrutineeSource : Term context Ty.bool scrutineeRawSource}
      {scrutineeTarget : Term context Ty.bool scrutineeRawTarget}
      {thenSource : Term context motiveType thenRawSource}
      {thenTarget : Term context motiveType thenRawTarget}
      {elseSource : Term context motiveType elseRawSource}
      {elseTarget : Term context motiveType elseRawTarget} :
      Step.par scrutineeSource scrutineeTarget →
      Step.par thenSource thenTarget →
      Step.par elseSource elseTarget →
      Step.par (Term.boolElim scrutineeSource thenSource elseSource)
               (Term.boolElim scrutineeTarget thenTarget elseTarget)
  /-- Parallel-cong: natSucc reduces in predecessor. -/
  | natSucc {mode level scope} {context : Ctx mode level scope}
      {predecessorRawSource predecessorRawTarget : RawTerm scope}
      {predecessorSource : Term context Ty.nat predecessorRawSource}
      {predecessorTarget : Term context Ty.nat predecessorRawTarget} :
      Step.par predecessorSource predecessorTarget →
      Step.par (Term.natSucc predecessorSource) (Term.natSucc predecessorTarget)
  /-- Parallel-cong: natElim reduces in all three positions. -/
  | natElim {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRawSource scrutineeRawTarget
       zeroRawSource zeroRawTarget
       succRawSource succRawTarget : RawTerm scope}
      {scrutineeSource : Term context Ty.nat scrutineeRawSource}
      {scrutineeTarget : Term context Ty.nat scrutineeRawTarget}
      {zeroSource : Term context motiveType zeroRawSource}
      {zeroTarget : Term context motiveType zeroRawTarget}
      {succSource : Term context (Ty.arrow Ty.nat motiveType) succRawSource}
      {succTarget : Term context (Ty.arrow Ty.nat motiveType) succRawTarget} :
      Step.par scrutineeSource scrutineeTarget →
      Step.par zeroSource zeroTarget →
      Step.par succSource succTarget →
      Step.par (Term.natElim scrutineeSource zeroSource succSource)
               (Term.natElim scrutineeTarget zeroTarget succTarget)
  /-- Parallel-cong: natRec reduces in all three positions. -/
  | natRec {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRawSource scrutineeRawTarget
       zeroRawSource zeroRawTarget
       succRawSource succRawTarget : RawTerm scope}
      {scrutineeSource : Term context Ty.nat scrutineeRawSource}
      {scrutineeTarget : Term context Ty.nat scrutineeRawTarget}
      {zeroSource : Term context motiveType zeroRawSource}
      {zeroTarget : Term context motiveType zeroRawTarget}
      {succSource :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawSource}
      {succTarget :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawTarget} :
      Step.par scrutineeSource scrutineeTarget →
      Step.par zeroSource zeroTarget →
      Step.par succSource succTarget →
      Step.par (Term.natRec scrutineeSource zeroSource succSource)
               (Term.natRec scrutineeTarget zeroTarget succTarget)
  /-- Parallel-cong: listCons reduces in head and tail. -/
  | listCons {mode level scope} {context : Ctx mode level scope}
      {elementType : Ty level scope}
      {headRawSource headRawTarget tailRawSource tailRawTarget : RawTerm scope}
      {headSource : Term context elementType headRawSource}
      {headTarget : Term context elementType headRawTarget}
      {tailSource : Term context (Ty.listType elementType) tailRawSource}
      {tailTarget : Term context (Ty.listType elementType) tailRawTarget} :
      Step.par headSource headTarget →
      Step.par tailSource tailTarget →
      Step.par (Term.listCons headSource tailSource)
               (Term.listCons headTarget tailTarget)
  /-- Parallel-cong: listElim reduces in all three positions. -/
  | listElim {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutineeRawSource scrutineeRawTarget
       nilRawSource nilRawTarget
       consRawSource consRawTarget : RawTerm scope}
      {scrutineeSource :
        Term context (Ty.listType elementType) scrutineeRawSource}
      {scrutineeTarget :
        Term context (Ty.listType elementType) scrutineeRawTarget}
      {nilSource : Term context motiveType nilRawSource}
      {nilTarget : Term context motiveType nilRawTarget}
      {consSource :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consRawSource}
      {consTarget :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consRawTarget} :
      Step.par scrutineeSource scrutineeTarget →
      Step.par nilSource nilTarget →
      Step.par consSource consTarget →
      Step.par (Term.listElim scrutineeSource nilSource consSource)
               (Term.listElim scrutineeTarget nilTarget consTarget)
  /-- Parallel-cong: optionSome reduces in value. -/
  | optionSome {mode level scope} {context : Ctx mode level scope}
      {elementType : Ty level scope}
      {valueRawSource valueRawTarget : RawTerm scope}
      {valueSource : Term context elementType valueRawSource}
      {valueTarget : Term context elementType valueRawTarget} :
      Step.par valueSource valueTarget →
      Step.par (Term.optionSome valueSource) (Term.optionSome valueTarget)
  /-- Parallel-cong: optionMatch reduces in all three positions. -/
  | optionMatch {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutineeRawSource scrutineeRawTarget
       noneRawSource noneRawTarget
       someRawSource someRawTarget : RawTerm scope}
      {scrutineeSource :
        Term context (Ty.optionType elementType) scrutineeRawSource}
      {scrutineeTarget :
        Term context (Ty.optionType elementType) scrutineeRawTarget}
      {noneSource : Term context motiveType noneRawSource}
      {noneTarget : Term context motiveType noneRawTarget}
      {someSource : Term context (Ty.arrow elementType motiveType) someRawSource}
      {someTarget : Term context (Ty.arrow elementType motiveType) someRawTarget} :
      Step.par scrutineeSource scrutineeTarget →
      Step.par noneSource noneTarget →
      Step.par someSource someTarget →
      Step.par (Term.optionMatch scrutineeSource noneSource someSource)
               (Term.optionMatch scrutineeTarget noneTarget someTarget)
  /-- Parallel-cong: eitherInl reduces in value. -/
  | eitherInl {mode level scope} {context : Ctx mode level scope}
      {leftType rightType : Ty level scope}
      {valueRawSource valueRawTarget : RawTerm scope}
      {valueSource : Term context leftType valueRawSource}
      {valueTarget : Term context leftType valueRawTarget} :
      Step.par valueSource valueTarget →
      Step.par (Term.eitherInl (rightType := rightType) valueSource)
               (Term.eitherInl (rightType := rightType) valueTarget)
  /-- Parallel-cong: eitherInr reduces in value. -/
  | eitherInr {mode level scope} {context : Ctx mode level scope}
      {leftType rightType : Ty level scope}
      {valueRawSource valueRawTarget : RawTerm scope}
      {valueSource : Term context rightType valueRawSource}
      {valueTarget : Term context rightType valueRawTarget} :
      Step.par valueSource valueTarget →
      Step.par (Term.eitherInr (leftType := leftType) valueSource)
               (Term.eitherInr (leftType := leftType) valueTarget)
  /-- Parallel-cong: eitherMatch reduces in all three positions. -/
  | eitherMatch {mode level scope} {context : Ctx mode level scope}
      {leftType rightType motiveType : Ty level scope}
      {scrutineeRawSource scrutineeRawTarget
       leftRawSource leftRawTarget
       rightRawSource rightRawTarget : RawTerm scope}
      {scrutineeSource :
        Term context (Ty.eitherType leftType rightType) scrutineeRawSource}
      {scrutineeTarget :
        Term context (Ty.eitherType leftType rightType) scrutineeRawTarget}
      {leftSource : Term context (Ty.arrow leftType motiveType) leftRawSource}
      {leftTarget : Term context (Ty.arrow leftType motiveType) leftRawTarget}
      {rightSource : Term context (Ty.arrow rightType motiveType) rightRawSource}
      {rightTarget : Term context (Ty.arrow rightType motiveType) rightRawTarget} :
      Step.par scrutineeSource scrutineeTarget →
      Step.par leftSource leftTarget →
      Step.par rightSource rightTarget →
      Step.par (Term.eitherMatch scrutineeSource leftSource rightSource)
               (Term.eitherMatch scrutineeTarget leftTarget rightTarget)
  /-- Parallel-cong: idJ reduces in baseCase and witness. -/
  | idJ {mode level scope} {context : Ctx mode level scope}
      {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
      {motiveType : Ty level scope}
      {baseRawSource baseRawTarget
       witnessRawSource witnessRawTarget : RawTerm scope}
      {baseSource : Term context motiveType baseRawSource}
      {baseTarget : Term context motiveType baseRawTarget}
      {witnessSource :
        Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRawSource}
      {witnessTarget :
        Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRawTarget} :
      Step.par baseSource baseTarget →
      Step.par witnessSource witnessTarget →
      Step.par (Term.idJ baseSource witnessSource)
               (Term.idJ baseTarget witnessTarget)
  /-- Parallel-cong: OEq refl reduces in its raw witness. -/
  | oeqReflCong {mode level scope} {context : Ctx mode level scope}
      {carrier : Ty level scope}
      {witnessRawSource witnessRawTarget : RawTerm scope} :
      RawStep.par witnessRawSource witnessRawTarget →
      Step.par
        (Term.oeqRefl (context := context) carrier witnessRawSource)
        (Term.oeqRefl (context := context) carrier witnessRawTarget)
  /-- Parallel-cong: OEq J reduces in baseCase and witness. -/
  | oeqJCong {mode level scope} {context : Ctx mode level scope}
      {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
      {motiveType : Ty level scope}
      {baseRawSource baseRawTarget
       witnessRawSource witnessRawTarget : RawTerm scope}
      {baseSource : Term context motiveType baseRawSource}
      {baseTarget : Term context motiveType baseRawTarget}
      {witnessSource :
        Term context (Ty.oeq carrier leftEndpoint rightEndpoint)
          witnessRawSource}
      {witnessTarget :
        Term context (Ty.oeq carrier leftEndpoint rightEndpoint)
          witnessRawTarget} :
      Step.par baseSource baseTarget →
      Step.par witnessSource witnessTarget →
      Step.par (Term.oeqJ baseSource witnessSource)
               (Term.oeqJ baseTarget witnessTarget)
  /-- Parallel-cong: OEq funext reduces in its proof-erased pointwise
      certificate. -/
  | oeqFunextCong {mode level scope}
      {context : Ctx mode level scope}
      (domainType codomainType : Ty level scope)
      (leftFunctionRaw rightFunctionRaw : RawTerm scope)
      {pointwiseRawSource pointwiseRawTarget : RawTerm scope}
      {pointwiseSource : Term context Ty.unit pointwiseRawSource}
      {pointwiseTarget : Term context Ty.unit pointwiseRawTarget} :
      Step.par pointwiseSource pointwiseTarget →
      Step.par
        (Term.oeqFunext domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseSource)
        (Term.oeqFunext domainType codomainType
          leftFunctionRaw rightFunctionRaw pointwiseTarget)
  /-- Parallel-cong: strict identity refl reduces in its raw witness. -/
  | idStrictReflCong {mode level scope} {context : Ctx mode level scope}
      {carrier : Ty level scope}
      {witnessRawSource witnessRawTarget : RawTerm scope} :
      RawStep.par witnessRawSource witnessRawTarget →
      Step.par
        (Term.idStrictRefl (context := context) carrier witnessRawSource)
        (Term.idStrictRefl (context := context) carrier witnessRawTarget)
  /-- Parallel-cong: strict identity rec reduces in baseCase and witness. -/
  | idStrictRecCong {mode level scope} {context : Ctx mode level scope}
      {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
      {motiveType : Ty level scope}
      {baseRawSource baseRawTarget
       witnessRawSource witnessRawTarget : RawTerm scope}
      {baseSource : Term context motiveType baseRawSource}
      {baseTarget : Term context motiveType baseRawTarget}
      {witnessSource :
        Term context (Ty.idStrict carrier leftEndpoint rightEndpoint)
          witnessRawSource}
      {witnessTarget :
        Term context (Ty.idStrict carrier leftEndpoint rightEndpoint)
          witnessRawTarget} :
      Step.par baseSource baseTarget →
      Step.par witnessSource witnessTarget →
      Step.par (Term.idStrictRec baseSource witnessSource)
               (Term.idStrictRec baseTarget witnessTarget)
  /-- Parallel-cong: modIntro reduces in inner. -/
  | modIntro {mode level scope} {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerRawSource innerRawTarget : RawTerm scope}
      {innerSource : Term context innerType innerRawSource}
      {innerTarget : Term context innerType innerRawTarget} :
      Step.par innerSource innerTarget →
      Step.par (Term.modIntro innerSource) (Term.modIntro innerTarget)
  /-- Parallel-cong: modElim reduces in inner. -/
  | modElim {mode level scope} {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerRawSource innerRawTarget : RawTerm scope}
      {innerSource : Term context innerType innerRawSource}
      {innerTarget : Term context innerType innerRawTarget} :
      Step.par innerSource innerTarget →
      Step.par (Term.modElim innerSource) (Term.modElim innerTarget)
  /-- Parallel-cong: subsume reduces in inner. -/
  | subsume {mode level scope} {context : Ctx mode level scope}
      {innerType : Ty level scope}
      {innerRawSource innerRawTarget : RawTerm scope}
      {innerSource : Term context innerType innerRawSource}
      {innerTarget : Term context innerType innerRawTarget} :
      Step.par innerSource innerTarget →
      Step.par (Term.subsume innerSource) (Term.subsume innerTarget)
  /-- Parallel-cong: pathLam reduces in its interval-indexed body. -/
  | pathLam {mode level scope} {context : Ctx mode level scope}
      {carrierType : Ty level scope}
      {leftEndpoint rightEndpoint : RawTerm scope}
      {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
      {bodySource :
        Term (context.cons Ty.interval) carrierType.weaken bodyRawSource}
      {bodyTarget :
        Term (context.cons Ty.interval) carrierType.weaken bodyRawTarget} :
      Step.par bodySource bodyTarget →
      Step.par
        (Term.pathLam carrierType leftEndpoint rightEndpoint bodySource)
        (Term.pathLam carrierType leftEndpoint rightEndpoint bodyTarget)
  /-- Parallel-cong: pathApp reduces in path and interval positions. -/
  | pathApp {mode level scope} {context : Ctx mode level scope}
      {carrierType : Ty level scope}
      {leftEndpoint rightEndpoint : RawTerm scope}
      {pathRawSource pathRawTarget intervalRawSource intervalRawTarget :
        RawTerm scope}
      {pathSource :
        Term context (Ty.path carrierType leftEndpoint rightEndpoint)
          pathRawSource}
      {pathTarget :
        Term context (Ty.path carrierType leftEndpoint rightEndpoint)
          pathRawTarget}
      {intervalSource : Term context Ty.interval intervalRawSource}
      {intervalTarget : Term context Ty.interval intervalRawTarget} :
      Step.par pathSource pathTarget →
      Step.par intervalSource intervalTarget →
      Step.par (Term.pathApp pathSource intervalSource)
               (Term.pathApp pathTarget intervalTarget)
  /-- Parallel-cong: glueIntro reduces in base and partial positions. -/
  | glueIntro {mode level scope} {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {boundaryWitness : RawTerm scope}
      {baseRawSource baseRawTarget partialRawSource partialRawTarget :
        RawTerm scope}
      {baseSource : Term context baseType baseRawSource}
      {baseTarget : Term context baseType baseRawTarget}
      {partialSource : Term context baseType partialRawSource}
      {partialTarget : Term context baseType partialRawTarget} :
      Step.par baseSource baseTarget →
      Step.par partialSource partialTarget →
      Step.par
        (Term.glueIntro baseType boundaryWitness baseSource partialSource)
        (Term.glueIntro baseType boundaryWitness baseTarget partialTarget)
  /-- Parallel-cong: glueElim reduces in the glued value. -/
  | glueElim {mode level scope} {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {boundaryWitness : RawTerm scope}
      {gluedRawSource gluedRawTarget : RawTerm scope}
      {gluedSource :
        Term context (Ty.glue baseType boundaryWitness) gluedRawSource}
      {gluedTarget :
        Term context (Ty.glue baseType boundaryWitness) gluedRawTarget} :
      Step.par gluedSource gluedTarget →
      Step.par (Term.glueElim gluedSource)
               (Term.glueElim gluedTarget)
  /-- Parallel-cong: transport reduces in its type path and source value. -/
  | transp {mode level scope} {context : Ctx mode level scope}
      (universeLevel : UniverseLevel)
      (universeLevelLt : universeLevel.toNat + 1 ≤ level)
      (sourceType targetType : Ty level scope)
      (sourceTypeRaw targetTypeRaw : RawTerm scope)
      {pathRawSource pathRawTarget sourceRawSource sourceRawTarget :
        RawTerm scope}
      {typePathSource :
        Term context
          (Ty.path (Ty.universe universeLevel universeLevelLt)
            sourceTypeRaw targetTypeRaw)
          pathRawSource}
      {typePathTarget :
        Term context
          (Ty.path (Ty.universe universeLevel universeLevelLt)
            sourceTypeRaw targetTypeRaw)
          pathRawTarget}
      {sourceValueSource : Term context sourceType sourceRawSource}
      {sourceValueTarget : Term context sourceType sourceRawTarget} :
      Step.par typePathSource typePathTarget →
      Step.par sourceValueSource sourceValueTarget →
      Step.par
        (Term.transp universeLevel universeLevelLt sourceType targetType
          sourceTypeRaw targetTypeRaw typePathSource sourceValueSource)
        (Term.transp universeLevel universeLevelLt sourceType targetType
          sourceTypeRaw targetTypeRaw typePathTarget sourceValueTarget)
  /-- Parallel-cong: homogeneous composition reduces in sides and cap. -/
  | hcomp {mode level scope} {context : Ctx mode level scope}
      {carrierType : Ty level scope}
      {sidesRawSource sidesRawTarget capRawSource capRawTarget :
        RawTerm scope}
      {sidesSource : Term context carrierType sidesRawSource}
      {sidesTarget : Term context carrierType sidesRawTarget}
      {capSource : Term context carrierType capRawSource}
      {capTarget : Term context carrierType capRawTarget} :
      Step.par sidesSource sidesTarget →
      Step.par capSource capTarget →
      Step.par (Term.hcomp sidesSource capSource)
               (Term.hcomp sidesTarget capTarget)
  /-- Raw-name parity: interval negation reduces in its inner value. -/
  | intervalOppCong {mode level scope} {context : Ctx mode level scope}
      {innerRawSource innerRawTarget : RawTerm scope}
      {innerSource : Term context Ty.interval innerRawSource}
      {innerTarget : Term context Ty.interval innerRawTarget} :
      Step.par innerSource innerTarget →
      Step.par (Term.intervalOpp innerSource)
               (Term.intervalOpp innerTarget)
  /-- Raw-name parity: interval meet reduces in both arguments. -/
  | intervalMeetCong {mode level scope} {context : Ctx mode level scope}
      {leftRawSource leftRawTarget rightRawSource rightRawTarget :
        RawTerm scope}
      {leftSource : Term context Ty.interval leftRawSource}
      {leftTarget : Term context Ty.interval leftRawTarget}
      {rightSource : Term context Ty.interval rightRawSource}
      {rightTarget : Term context Ty.interval rightRawTarget} :
      Step.par leftSource leftTarget →
      Step.par rightSource rightTarget →
      Step.par (Term.intervalMeet leftSource rightSource)
               (Term.intervalMeet leftTarget rightTarget)
  /-- Raw-name parity: interval join reduces in both arguments. -/
  | intervalJoinCong {mode level scope} {context : Ctx mode level scope}
      {leftRawSource leftRawTarget rightRawSource rightRawTarget :
        RawTerm scope}
      {leftSource : Term context Ty.interval leftRawSource}
      {leftTarget : Term context Ty.interval leftRawTarget}
      {rightSource : Term context Ty.interval rightRawSource}
      {rightTarget : Term context Ty.interval rightRawTarget} :
      Step.par leftSource leftTarget →
      Step.par rightSource rightTarget →
      Step.par (Term.intervalJoin leftSource rightSource)
               (Term.intervalJoin leftTarget rightTarget)
  /-- Raw-name parity alias for `pathLam` congruence. -/
  | pathLamCong {mode level scope} {context : Ctx mode level scope}
      {carrierType : Ty level scope}
      {leftEndpoint rightEndpoint : RawTerm scope}
      {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
      {bodySource :
        Term (context.cons Ty.interval) carrierType.weaken bodyRawSource}
      {bodyTarget :
        Term (context.cons Ty.interval) carrierType.weaken bodyRawTarget} :
      Step.par bodySource bodyTarget →
      Step.par
        (Term.pathLam carrierType leftEndpoint rightEndpoint bodySource)
        (Term.pathLam carrierType leftEndpoint rightEndpoint bodyTarget)
  /-- Raw-name parity alias for `pathApp` congruence. -/
  | pathAppCong {mode level scope} {context : Ctx mode level scope}
      {carrierType : Ty level scope}
      {leftEndpoint rightEndpoint : RawTerm scope}
      {pathRawSource pathRawTarget intervalRawSource intervalRawTarget :
        RawTerm scope}
      {pathSource :
        Term context (Ty.path carrierType leftEndpoint rightEndpoint)
          pathRawSource}
      {pathTarget :
        Term context (Ty.path carrierType leftEndpoint rightEndpoint)
          pathRawTarget}
      {intervalSource : Term context Ty.interval intervalRawSource}
      {intervalTarget : Term context Ty.interval intervalRawTarget} :
      Step.par pathSource pathTarget →
      Step.par intervalSource intervalTarget →
      Step.par (Term.pathApp pathSource intervalSource)
               (Term.pathApp pathTarget intervalTarget)
  /-- Raw-name parity alias for `glueIntro` congruence. -/
  | glueIntroCong {mode level scope} {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {boundaryWitness : RawTerm scope}
      {baseRawSource baseRawTarget partialRawSource partialRawTarget :
        RawTerm scope}
      {baseSource : Term context baseType baseRawSource}
      {baseTarget : Term context baseType baseRawTarget}
      {partialSource : Term context baseType partialRawSource}
      {partialTarget : Term context baseType partialRawTarget} :
      Step.par baseSource baseTarget →
      Step.par partialSource partialTarget →
      Step.par
        (Term.glueIntro baseType boundaryWitness baseSource partialSource)
        (Term.glueIntro baseType boundaryWitness baseTarget partialTarget)
  /-- Raw-name parity alias for `glueElim` congruence. -/
  | glueElimCong {mode level scope} {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {boundaryWitness : RawTerm scope}
      {gluedRawSource gluedRawTarget : RawTerm scope}
      {gluedSource :
        Term context (Ty.glue baseType boundaryWitness) gluedRawSource}
      {gluedTarget :
        Term context (Ty.glue baseType boundaryWitness) gluedRawTarget} :
      Step.par gluedSource gluedTarget →
      Step.par (Term.glueElim gluedSource)
               (Term.glueElim gluedTarget)
  /-- Raw-name parity alias for `transp` congruence. -/
  | transpCong {mode level scope} {context : Ctx mode level scope}
      (universeLevel : UniverseLevel)
      (universeLevelLt : universeLevel.toNat + 1 ≤ level)
      (sourceType targetType : Ty level scope)
      (sourceTypeRaw targetTypeRaw : RawTerm scope)
      {pathRawSource pathRawTarget sourceRawSource sourceRawTarget :
        RawTerm scope}
      {typePathSource :
        Term context
          (Ty.path (Ty.universe universeLevel universeLevelLt)
            sourceTypeRaw targetTypeRaw)
          pathRawSource}
      {typePathTarget :
        Term context
          (Ty.path (Ty.universe universeLevel universeLevelLt)
            sourceTypeRaw targetTypeRaw)
          pathRawTarget}
      {sourceValueSource : Term context sourceType sourceRawSource}
      {sourceValueTarget : Term context sourceType sourceRawTarget} :
      Step.par typePathSource typePathTarget →
      Step.par sourceValueSource sourceValueTarget →
      Step.par
        (Term.transp universeLevel universeLevelLt sourceType targetType
          sourceTypeRaw targetTypeRaw typePathSource sourceValueSource)
        (Term.transp universeLevel universeLevelLt sourceType targetType
          sourceTypeRaw targetTypeRaw typePathTarget sourceValueTarget)
  /-- Raw-name parity alias for `hcomp` congruence. -/
  | hcompCong {mode level scope} {context : Ctx mode level scope}
      {carrierType : Ty level scope}
      {sidesRawSource sidesRawTarget capRawSource capRawTarget :
        RawTerm scope}
      {sidesSource : Term context carrierType sidesRawSource}
      {sidesTarget : Term context carrierType sidesRawTarget}
      {capSource : Term context carrierType capRawSource}
      {capTarget : Term context carrierType capRawTarget} :
      Step.par sidesSource sidesTarget →
      Step.par capSource capTarget →
      Step.par (Term.hcomp sidesSource capSource)
               (Term.hcomp sidesTarget capTarget)
  /-- Raw-name parity: single-field record intro reduces in its field. -/
  | recordIntroCong {mode level scope} {context : Ctx mode level scope}
      {singleFieldType : Ty level scope}
      {firstRawSource firstRawTarget : RawTerm scope}
      {firstSource : Term context singleFieldType firstRawSource}
      {firstTarget : Term context singleFieldType firstRawTarget} :
      Step.par firstSource firstTarget →
      Step.par (Term.recordIntro firstSource)
               (Term.recordIntro firstTarget)
  /-- Raw-name parity: single-field record projection reduces in its record. -/
  | recordProjCong {mode level scope} {context : Ctx mode level scope}
      {singleFieldType : Ty level scope}
      {recordRawSource recordRawTarget : RawTerm scope}
      {recordSource : Term context (Ty.record singleFieldType) recordRawSource}
      {recordTarget : Term context (Ty.record singleFieldType) recordRawTarget} :
      Step.par recordSource recordTarget →
      Step.par (Term.recordProj recordSource)
               (Term.recordProj recordTarget)
  /-- Raw-name parity: refinement intro reduces in value and proof. -/
  | refineIntroCong {mode level scope} {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {predicate : RawTerm (scope + 1)}
      {valueRawSource valueRawTarget proofRawSource proofRawTarget :
        RawTerm scope}
      {valueSource : Term context baseType valueRawSource}
      {valueTarget : Term context baseType valueRawTarget}
      {proofSource : Term context Ty.unit proofRawSource}
      {proofTarget : Term context Ty.unit proofRawTarget} :
      Step.par valueSource valueTarget →
      Step.par proofSource proofTarget →
      Step.par (Term.refineIntro predicate valueSource proofSource)
               (Term.refineIntro predicate valueTarget proofTarget)
  /-- Raw-name parity: refinement elimination reduces in its refined value. -/
  | refineElimCong {mode level scope} {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {predicate : RawTerm (scope + 1)}
      {refinedRawSource refinedRawTarget : RawTerm scope}
      {refinedSource : Term context (Ty.refine baseType predicate) refinedRawSource}
      {refinedTarget : Term context (Ty.refine baseType predicate) refinedRawTarget} :
      Step.par refinedSource refinedTarget →
      Step.par (Term.refineElim refinedSource)
               (Term.refineElim refinedTarget)
  /-- Shallow β: `(λx. body) arg ⟶ body[arg/x]` with parallel
  reduction in body and arg.  Source has Ty `cod`; target via
  `Term.subst0` has Ty `cod.weaken.subst0 dom argumentRawTarget` —
  two-Ty signature absorbs the gap. -/
  | betaApp {mode level scope} {context : Ctx mode level scope}
      {domainType codomainType : Ty level scope}
      {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
      {argumentRawSource argumentRawTarget : RawTerm scope}
      {bodySource :
        Term (context.cons domainType) codomainType.weaken bodyRawSource}
      {bodyTarget :
        Term (context.cons domainType) codomainType.weaken bodyRawTarget}
      {argumentSource : Term context domainType argumentRawSource}
      {argumentTarget : Term context domainType argumentRawTarget} :
      Step.par bodySource bodyTarget →
      Step.par argumentSource argumentTarget →
      Step.par (Term.app (Term.lam (codomainType := codomainType) bodySource)
                          argumentSource)
               (Term.subst0 bodyTarget argumentTarget)
  /-- Shallow β-Π: `(λx. body) arg ⟶ body[arg/x]` for dependent app. -/
  | betaAppPi {mode level scope} {context : Ctx mode level scope}
      {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
      {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
      {argumentRawSource argumentRawTarget : RawTerm scope}
      {bodySource :
        Term (context.cons domainType) codomainType bodyRawSource}
      {bodyTarget :
        Term (context.cons domainType) codomainType bodyRawTarget}
      {argumentSource : Term context domainType argumentRawSource}
      {argumentTarget : Term context domainType argumentRawTarget} :
      Step.par bodySource bodyTarget →
      Step.par argumentSource argumentTarget →
      Step.par (Term.appPi (Term.lamPi (domainType := domainType) bodySource)
                            argumentSource)
               (Term.subst0 bodyTarget argumentTarget)
  /-- Shallow cubical β: `(pathLam body) @ interval ⟶ body[interval]`. -/
  | betaPathApp {mode level scope} {context : Ctx mode level scope}
      {carrierType : Ty level scope}
      {leftEndpoint rightEndpoint : RawTerm scope}
      {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
      {intervalRawSource intervalRawTarget : RawTerm scope}
      {bodySource :
        Term (context.cons Ty.interval) carrierType.weaken bodyRawSource}
      {bodyTarget :
        Term (context.cons Ty.interval) carrierType.weaken bodyRawTarget}
      {intervalSource : Term context Ty.interval intervalRawSource}
      {intervalTarget : Term context Ty.interval intervalRawTarget} :
      Step.par bodySource bodyTarget →
      Step.par intervalSource intervalTarget →
      Step.par
        (Term.pathApp
          (Term.pathLam carrierType leftEndpoint rightEndpoint bodySource)
          intervalSource)
        (Term.subst0 bodyTarget intervalTarget)
  /-- Shallow cubical Glue β: `unglue (glue base partial) ⟶ base`. -/
  | betaGlueElimIntro {mode level scope} {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {boundaryWitness : RawTerm scope}
      {baseRawSource baseRawTarget partialRawSource partialRawTarget :
        RawTerm scope}
      {baseSource : Term context baseType baseRawSource}
      {baseTarget : Term context baseType baseRawTarget}
      {partialSource : Term context baseType partialRawSource}
      {partialTarget : Term context baseType partialRawTarget} :
      Step.par baseSource baseTarget →
      Step.par partialSource partialTarget →
      Step.par
        (Term.glueElim
          (Term.glueIntro baseType boundaryWitness baseSource partialSource))
        baseTarget
  /-- Shallow single-field record β: `recordProj (recordIntro field) ⟶ field'`. -/
  | betaRecordProjIntro {mode level scope} {context : Ctx mode level scope}
      {singleFieldType : Ty level scope}
      {firstRawSource firstRawTarget : RawTerm scope}
      {firstSource : Term context singleFieldType firstRawSource}
      {firstTarget : Term context singleFieldType firstRawTarget} :
      Step.par firstSource firstTarget →
      Step.par (Term.recordProj (Term.recordIntro firstSource)) firstTarget
  /-- Shallow refinement β: `refineElim (refineIntro value proof) ⟶ value'`. -/
  | betaRefineElimIntro {mode level scope} {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {predicate : RawTerm (scope + 1)}
      {valueRawSource valueRawTarget proofRawSource proofRawTarget :
        RawTerm scope}
      {valueSource : Term context baseType valueRawSource}
      {valueTarget : Term context baseType valueRawTarget}
      {proofSource : Term context Ty.unit proofRawSource}
      {proofTarget : Term context Ty.unit proofRawTarget} :
      Step.par valueSource valueTarget →
      Step.par proofSource proofTarget →
      Step.par
        (Term.refineElim (Term.refineIntro predicate valueSource proofSource))
        valueTarget
  /-- Raw-name parity: codata unfold reduces in state and transition. -/
  | codataUnfoldCong {mode level scope} {context : Ctx mode level scope}
      {stateType outputType : Ty level scope}
      {stateRawSource stateRawTarget transitionRawSource transitionRawTarget :
        RawTerm scope}
      {stateSource : Term context stateType stateRawSource}
      {stateTarget : Term context stateType stateRawTarget}
      {transitionSource :
        Term context (Ty.arrow stateType outputType) transitionRawSource}
      {transitionTarget :
        Term context (Ty.arrow stateType outputType) transitionRawTarget} :
      Step.par stateSource stateTarget →
      Step.par transitionSource transitionTarget →
      Step.par (Term.codataUnfold stateSource transitionSource)
               (Term.codataUnfold stateTarget transitionTarget)
  /-- Raw-name parity: codata destruction reduces in its codata value. -/
  | codataDestCong {mode level scope} {context : Ctx mode level scope}
      {stateType outputType : Ty level scope}
      {codataRawSource codataRawTarget : RawTerm scope}
      {codataSource :
        Term context (Ty.codata stateType outputType) codataRawSource}
      {codataTarget :
        Term context (Ty.codata stateType outputType) codataRawTarget} :
      Step.par codataSource codataTarget →
      Step.par (Term.codataDest codataSource)
               (Term.codataDest codataTarget)
  /-- Raw-name parity: session send reduces in channel and payload. -/
  | sessionSendCong {mode level scope} {context : Ctx mode level scope}
      {protocolStep : RawTerm scope}
      {payloadType : Ty level scope}
      {channelRawSource channelRawTarget payloadRawSource payloadRawTarget :
        RawTerm scope}
      {channelSource : Term context (Ty.session protocolStep) channelRawSource}
      {channelTarget : Term context (Ty.session protocolStep) channelRawTarget}
      {payloadSource : Term context payloadType payloadRawSource}
      {payloadTarget : Term context payloadType payloadRawTarget} :
      Step.par channelSource channelTarget →
      Step.par payloadSource payloadTarget →
      Step.par (Term.sessionSend protocolStep channelSource payloadSource)
               (Term.sessionSend protocolStep channelTarget payloadTarget)
  /-- Raw-name parity: session receive reduces in its channel. -/
  | sessionRecvCong {mode level scope} {context : Ctx mode level scope}
      {protocolStep : RawTerm scope}
      {channelRawSource channelRawTarget : RawTerm scope}
      {channelSource : Term context (Ty.session protocolStep) channelRawSource}
      {channelTarget : Term context (Ty.session protocolStep) channelRawTarget} :
      Step.par channelSource channelTarget →
      Step.par (Term.sessionRecv channelSource)
               (Term.sessionRecv channelTarget)
  /-- Raw-name parity: effect perform reduces in operation and arguments. -/
  | effectPerformCong {mode level scope} {context : Ctx mode level scope}
      {effectTag : RawTerm scope}
      {carrierType : Ty level scope}
      {operationRawSource operationRawTarget argumentsRawSource argumentsRawTarget :
        RawTerm scope}
      {operationSource : Term context Ty.unit operationRawSource}
      {operationTarget : Term context Ty.unit operationRawTarget}
      {argumentsSource : Term context carrierType argumentsRawSource}
      {argumentsTarget : Term context carrierType argumentsRawTarget} :
      Step.par operationSource operationTarget →
      Step.par argumentsSource argumentsTarget →
      Step.par (Term.effectPerform effectTag operationSource argumentsSource)
               (Term.effectPerform effectTag operationTarget argumentsTarget)
  /-- Shallow β-fst: `fst (pair a b) ⟶ a'` with `Step.par a a'`. -/
  | betaFstPair {mode level scope} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {firstRawSource firstRawTarget : RawTerm scope}
      {secondRawSource : RawTerm scope}
      {firstValueSource : Term context firstType firstRawSource}
      {firstValueTarget : Term context firstType firstRawTarget}
      (secondValueSource :
        Term context (secondType.subst0 firstType firstRawSource) secondRawSource) :
      Step.par firstValueSource firstValueTarget →
      Step.par (Term.fst (Term.pair (secondType := secondType)
                            firstValueSource secondValueSource))
               firstValueTarget
  /-- Shallow β-snd: `snd (pair a b) ⟶ b'` with `Step.par b b'`. -/
  | betaSndPair {mode level scope} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {firstRaw : RawTerm scope}
      {secondRawSource secondRawTarget : RawTerm scope}
      (firstValue : Term context firstType firstRaw)
      {secondValueSource :
        Term context (secondType.subst0 firstType firstRaw) secondRawSource}
      {secondValueTarget :
        Term context (secondType.subst0 firstType firstRaw) secondRawTarget} :
      Step.par secondValueSource secondValueTarget →
      Step.par (Term.snd (Term.pair (secondType := secondType)
                            firstValue secondValueSource))
               secondValueTarget
  /-- Shallow ι-boolElim-true: `boolElim true t e ⟶ t'`. -/
  | iotaBoolElimTrue {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {thenRawSource thenRawTarget elseRaw : RawTerm scope}
      {thenSource : Term context motiveType thenRawSource}
      {thenTarget : Term context motiveType thenRawTarget}
      (elseBranch : Term context motiveType elseRaw) :
      Step.par thenSource thenTarget →
      Step.par (Term.boolElim Term.boolTrue thenSource elseBranch)
               thenTarget
  /-- Shallow ι-boolElim-false: `boolElim false t e ⟶ e'`. -/
  | iotaBoolElimFalse {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {thenRaw elseRawSource elseRawTarget : RawTerm scope}
      (thenBranch : Term context motiveType thenRaw)
      {elseSource : Term context motiveType elseRawSource}
      {elseTarget : Term context motiveType elseRawTarget} :
      Step.par elseSource elseTarget →
      Step.par (Term.boolElim Term.boolFalse thenBranch elseSource)
               elseTarget
  /-- Shallow ι-natElim-zero: `natElim 0 z s ⟶ z'`. -/
  | iotaNatElimZero {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {zeroRawSource zeroRawTarget succRaw : RawTerm scope}
      {zeroSource : Term context motiveType zeroRawSource}
      {zeroTarget : Term context motiveType zeroRawTarget}
      (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
      Step.par zeroSource zeroTarget →
      Step.par (Term.natElim Term.natZero zeroSource succBranch)
               zeroTarget
  /-- Shallow ι-natElim-succ: `natElim (succ n) z s ⟶ s' n'`. -/
  | iotaNatElimSucc {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {predecessorRawSource predecessorRawTarget zeroRaw
       succRawSource succRawTarget : RawTerm scope}
      {predecessorSource : Term context Ty.nat predecessorRawSource}
      {predecessorTarget : Term context Ty.nat predecessorRawTarget}
      (zeroBranch : Term context motiveType zeroRaw)
      {succSource : Term context (Ty.arrow Ty.nat motiveType) succRawSource}
      {succTarget : Term context (Ty.arrow Ty.nat motiveType) succRawTarget} :
      Step.par predecessorSource predecessorTarget →
      Step.par succSource succTarget →
      Step.par (Term.natElim (Term.natSucc predecessorSource) zeroBranch succSource)
               (Term.app succTarget predecessorTarget)
  /-- Shallow ι-natRec-zero: `natRec 0 z s ⟶ z'`. -/
  | iotaNatRecZero {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {zeroRawSource zeroRawTarget succRaw : RawTerm scope}
      {zeroSource : Term context motiveType zeroRawSource}
      {zeroTarget : Term context motiveType zeroRawTarget}
      (succBranch :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
      Step.par zeroSource zeroTarget →
      Step.par (Term.natRec Term.natZero zeroSource succBranch)
               zeroTarget
  /-- Shallow ι-natRec-succ: `natRec (succ n) z s ⟶ s' n' (natRec n' z' s')`. -/
  | iotaNatRecSucc {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {predecessorRawSource predecessorRawTarget
       zeroRawSource zeroRawTarget
       succRawSource succRawTarget : RawTerm scope}
      {predecessorSource : Term context Ty.nat predecessorRawSource}
      {predecessorTarget : Term context Ty.nat predecessorRawTarget}
      {zeroSource : Term context motiveType zeroRawSource}
      {zeroTarget : Term context motiveType zeroRawTarget}
      {succSource :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawSource}
      {succTarget :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawTarget} :
      Step.par predecessorSource predecessorTarget →
      Step.par zeroSource zeroTarget →
      Step.par succSource succTarget →
      Step.par (Term.natRec (Term.natSucc predecessorSource) zeroSource succSource)
               (Term.app (Term.app succTarget predecessorTarget)
                         (Term.natRec predecessorTarget zeroTarget succTarget))
  /-- Shallow ι-listElim-nil: `listElim [] n c ⟶ n'`. -/
  | iotaListElimNil {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {nilRawSource nilRawTarget consRaw : RawTerm scope}
      {nilSource : Term context motiveType nilRawSource}
      {nilTarget : Term context motiveType nilRawTarget}
      (consBranch :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
      Step.par nilSource nilTarget →
      Step.par (Term.listElim (elementType := elementType) Term.listNil
                  nilSource consBranch)
               nilTarget
  /-- Shallow ι-listElim-cons: `listElim (cons h t) n c ⟶ c' h' t'`. -/
  | iotaListElimCons {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {headRawSource headRawTarget
       tailRawSource tailRawTarget
       nilRaw consRawSource consRawTarget : RawTerm scope}
      {headSource : Term context elementType headRawSource}
      {headTarget : Term context elementType headRawTarget}
      {tailSource : Term context (Ty.listType elementType) tailRawSource}
      {tailTarget : Term context (Ty.listType elementType) tailRawTarget}
      (nilBranch : Term context motiveType nilRaw)
      {consSource :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consRawSource}
      {consTarget :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consRawTarget} :
      Step.par headSource headTarget →
      Step.par tailSource tailTarget →
      Step.par consSource consTarget →
      Step.par (Term.listElim (Term.listCons headSource tailSource)
                              nilBranch consSource)
               (Term.app (Term.app consTarget headTarget) tailTarget)
  /-- Shallow ι-optionMatch-none: `optionMatch none n s ⟶ n'`. -/
  | iotaOptionMatchNone {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {noneRawSource noneRawTarget someRaw : RawTerm scope}
      {noneSource : Term context motiveType noneRawSource}
      {noneTarget : Term context motiveType noneRawTarget}
      (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
      Step.par noneSource noneTarget →
      Step.par (Term.optionMatch (elementType := elementType) Term.optionNone
                  noneSource someBranch)
               noneTarget
  /-- Shallow ι-optionMatch-some: `optionMatch (some v) n s ⟶ s' v'`. -/
  | iotaOptionMatchSome {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {valueRawSource valueRawTarget noneRaw
       someRawSource someRawTarget : RawTerm scope}
      {valueSource : Term context elementType valueRawSource}
      {valueTarget : Term context elementType valueRawTarget}
      (noneBranch : Term context motiveType noneRaw)
      {someSource : Term context (Ty.arrow elementType motiveType) someRawSource}
      {someTarget : Term context (Ty.arrow elementType motiveType) someRawTarget} :
      Step.par valueSource valueTarget →
      Step.par someSource someTarget →
      Step.par (Term.optionMatch (Term.optionSome valueSource) noneBranch someSource)
               (Term.app someTarget valueTarget)
  /-- Shallow ι-eitherMatch-inl: `eitherMatch (inl v) lb rb ⟶ lb' v'`. -/
  | iotaEitherMatchInl {mode level scope} {context : Ctx mode level scope}
      {leftType rightType motiveType : Ty level scope}
      {valueRawSource valueRawTarget
       leftRawSource leftRawTarget rightRaw : RawTerm scope}
      {valueSource : Term context leftType valueRawSource}
      {valueTarget : Term context leftType valueRawTarget}
      {leftSource : Term context (Ty.arrow leftType motiveType) leftRawSource}
      {leftTarget : Term context (Ty.arrow leftType motiveType) leftRawTarget}
      (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
      Step.par valueSource valueTarget →
      Step.par leftSource leftTarget →
      Step.par (Term.eitherMatch
                  (Term.eitherInl (rightType := rightType) valueSource)
                  leftSource rightBranch)
               (Term.app leftTarget valueTarget)
  /-- Shallow ι-eitherMatch-inr: `eitherMatch (inr v) lb rb ⟶ rb' v'`. -/
  | iotaEitherMatchInr {mode level scope} {context : Ctx mode level scope}
      {leftType rightType motiveType : Ty level scope}
      {valueRawSource valueRawTarget
       leftRaw rightRawSource rightRawTarget : RawTerm scope}
      {valueSource : Term context rightType valueRawSource}
      {valueTarget : Term context rightType valueRawTarget}
      (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
      {rightSource : Term context (Ty.arrow rightType motiveType) rightRawSource}
      {rightTarget : Term context (Ty.arrow rightType motiveType) rightRawTarget} :
      Step.par valueSource valueTarget →
      Step.par rightSource rightTarget →
      Step.par (Term.eitherMatch
                  (Term.eitherInr (leftType := leftType) valueSource)
                  leftBranch rightSource)
               (Term.app rightTarget valueTarget)
  /-- Shallow ι-idJ-refl: `J base (refl rt) ⟶ base'`. -/
  | iotaIdJRefl {mode level scope} {context : Ctx mode level scope}
      (carrier : Ty level scope) (endpoint : RawTerm scope)
      {motiveType : Ty level scope}
      {baseRawSource baseRawTarget : RawTerm scope}
      {baseSource : Term context motiveType baseRawSource}
      {baseTarget : Term context motiveType baseRawTarget} :
      Step.par baseSource baseTarget →
      Step.par (Term.idJ (carrier := carrier)
                          (leftEndpoint := endpoint)
                          (rightEndpoint := endpoint)
                          baseSource (Term.refl carrier endpoint))
               baseTarget
  /-- Deep β-app: function parallel-reduces *to* a literal lam, then
  the outer application contracts. -/
  | betaAppDeep {mode level scope} {context : Ctx mode level scope}
      {domainType codomainType : Ty level scope}
      {functionRawSource bodyRawTarget : RawTerm (scope + 1)}
      {argumentRawSource argumentRawTarget : RawTerm scope}
      {functionRawSourceOuter : RawTerm scope}
      {functionTermSource :
        Term context (Ty.arrow domainType codomainType) functionRawSourceOuter}
      {bodyTarget :
        Term (context.cons domainType) codomainType.weaken bodyRawTarget}
      {argumentSource : Term context domainType argumentRawSource}
      {argumentTarget : Term context domainType argumentRawTarget} :
      Step.par functionTermSource
               (Term.lam (codomainType := codomainType) bodyTarget) →
      Step.par argumentSource argumentTarget →
      Step.par (Term.app functionTermSource argumentSource)
               (Term.subst0 bodyTarget argumentTarget)
  /-- Deep β-appPi: dependent function parallel-reduces *to* a literal
  lamPi, then contracts. -/
  | betaAppPiDeep {mode level scope} {context : Ctx mode level scope}
      {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
      {bodyRawTarget : RawTerm (scope + 1)}
      {argumentRawSource argumentRawTarget : RawTerm scope}
      {functionRawSourceOuter : RawTerm scope}
      {functionTermSource :
        Term context (Ty.piTy domainType codomainType) functionRawSourceOuter}
      {bodyTarget :
        Term (context.cons domainType) codomainType bodyRawTarget}
      {argumentSource : Term context domainType argumentRawSource}
      {argumentTarget : Term context domainType argumentRawTarget} :
      Step.par functionTermSource
               (Term.lamPi (domainType := domainType) bodyTarget) →
      Step.par argumentSource argumentTarget →
      Step.par (Term.appPi functionTermSource argumentSource)
               (Term.subst0 bodyTarget argumentTarget)
  /-- Deep cubical β: path term develops to a `pathLam`, then applies. -/
  | betaPathAppDeep {mode level scope} {context : Ctx mode level scope}
      {carrierType : Ty level scope}
      {leftEndpoint rightEndpoint : RawTerm scope}
      {pathRawSource intervalRawSource intervalRawTarget : RawTerm scope}
      {bodyRawTarget : RawTerm (scope + 1)}
      {pathSource :
        Term context (Ty.path carrierType leftEndpoint rightEndpoint)
          pathRawSource}
      {bodyTarget :
        Term (context.cons Ty.interval) carrierType.weaken bodyRawTarget}
      {intervalSource : Term context Ty.interval intervalRawSource}
      {intervalTarget : Term context Ty.interval intervalRawTarget} :
      Step.par pathSource
        (Term.pathLam carrierType leftEndpoint rightEndpoint bodyTarget) →
      Step.par intervalSource intervalTarget →
      Step.par (Term.pathApp pathSource intervalSource)
               (Term.subst0 bodyTarget intervalTarget)
  /-- Deep cubical Glue β: glued value develops to a `glueIntro`. -/
  | betaGlueElimIntroDeep {mode level scope}
      {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {boundaryWitness : RawTerm scope}
      {gluedRawSource baseRawTarget partialRawTarget : RawTerm scope}
      {gluedSource :
        Term context (Ty.glue baseType boundaryWitness) gluedRawSource}
      {baseTarget : Term context baseType baseRawTarget}
      {partialTarget : Term context baseType partialRawTarget} :
      Step.par gluedSource
        (Term.glueIntro baseType boundaryWitness baseTarget partialTarget) →
      Step.par (Term.glueElim gluedSource) baseTarget
  /-- Deep single-field record β: record value develops to a record intro. -/
  | betaRecordProjIntroDeep {mode level scope}
      {context : Ctx mode level scope}
      {singleFieldType : Ty level scope}
      {recordRawSource firstRawTarget : RawTerm scope}
      {recordSource : Term context (Ty.record singleFieldType) recordRawSource}
      {firstTarget : Term context singleFieldType firstRawTarget} :
      Step.par recordSource (Term.recordIntro firstTarget) →
      Step.par (Term.recordProj recordSource) firstTarget
  /-- Deep refinement β: refined value develops to a refinement intro. -/
  | betaRefineElimIntroDeep {mode level scope}
      {context : Ctx mode level scope}
      {baseType : Ty level scope}
      {predicate : RawTerm (scope + 1)}
      {refinedRawSource valueRawTarget proofRawTarget : RawTerm scope}
      {refinedSource : Term context (Ty.refine baseType predicate) refinedRawSource}
      {valueTarget : Term context baseType valueRawTarget}
      {proofTarget : Term context Ty.unit proofRawTarget} :
      Step.par refinedSource (Term.refineIntro predicate valueTarget proofTarget) →
      Step.par (Term.refineElim refinedSource) valueTarget
  /-- Deep β-fst: pair-shaped target. -/
  | betaFstPairDeep {mode level scope} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {pairRawSource firstRawTarget secondRawTarget : RawTerm scope}
      {pairTermSource :
        Term context (Ty.sigmaTy firstType secondType) pairRawSource}
      {firstValueTarget : Term context firstType firstRawTarget}
      {secondValueTarget :
        Term context (secondType.subst0 firstType firstRawTarget) secondRawTarget} :
      Step.par pairTermSource
               (Term.pair (secondType := secondType)
                          firstValueTarget secondValueTarget) →
      Step.par (Term.fst (secondType := secondType) pairTermSource)
               firstValueTarget
  /-- Deep β-snd: pair-shaped target. -/
  | betaSndPairDeep {mode level scope} {context : Ctx mode level scope}
      {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
      {pairRawSource firstRawTarget secondRawTarget : RawTerm scope}
      {pairTermSource :
        Term context (Ty.sigmaTy firstType secondType) pairRawSource}
      {firstValueTarget : Term context firstType firstRawTarget}
      {secondValueTarget :
        Term context (secondType.subst0 firstType firstRawTarget) secondRawTarget} :
      Step.par pairTermSource
               (Term.pair (secondType := secondType)
                          firstValueTarget secondValueTarget) →
      Step.par (Term.snd (secondType := secondType) pairTermSource)
               secondValueTarget
  /-- Deep ι-boolElim-true. -/
  | iotaBoolElimTrueDeep {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRaw thenRawSource thenRawTarget elseRaw : RawTerm scope}
      {scrutinee : Term context Ty.bool scrutineeRaw}
      {thenSource : Term context motiveType thenRawSource}
      {thenTarget : Term context motiveType thenRawTarget}
      (elseBranch : Term context motiveType elseRaw) :
      Step.par scrutinee Term.boolTrue →
      Step.par thenSource thenTarget →
      Step.par (Term.boolElim scrutinee thenSource elseBranch)
               thenTarget
  /-- Deep ι-boolElim-false. -/
  | iotaBoolElimFalseDeep {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRaw thenRaw elseRawSource elseRawTarget : RawTerm scope}
      {scrutinee : Term context Ty.bool scrutineeRaw}
      (thenBranch : Term context motiveType thenRaw)
      {elseSource : Term context motiveType elseRawSource}
      {elseTarget : Term context motiveType elseRawTarget} :
      Step.par scrutinee Term.boolFalse →
      Step.par elseSource elseTarget →
      Step.par (Term.boolElim scrutinee thenBranch elseSource)
               elseTarget
  /-- Deep ι-natElim on natZero. -/
  | iotaNatElimZeroDeep {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRaw zeroRawSource zeroRawTarget succRaw : RawTerm scope}
      {scrutinee : Term context Ty.nat scrutineeRaw}
      {zeroSource : Term context motiveType zeroRawSource}
      {zeroTarget : Term context motiveType zeroRawTarget}
      (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
      Step.par scrutinee Term.natZero →
      Step.par zeroSource zeroTarget →
      Step.par (Term.natElim scrutinee zeroSource succBranch)
               zeroTarget
  /-- Deep ι-natElim on natSucc. -/
  | iotaNatElimSuccDeep {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRaw predecessorRaw zeroRaw
       succRawSource succRawTarget : RawTerm scope}
      {scrutinee : Term context Ty.nat scrutineeRaw}
      {predecessor : Term context Ty.nat predecessorRaw}
      (zeroBranch : Term context motiveType zeroRaw)
      {succSource : Term context (Ty.arrow Ty.nat motiveType) succRawSource}
      {succTarget : Term context (Ty.arrow Ty.nat motiveType) succRawTarget} :
      Step.par scrutinee (Term.natSucc predecessor) →
      Step.par succSource succTarget →
      Step.par (Term.natElim scrutinee zeroBranch succSource)
               (Term.app succTarget predecessor)
  /-- Deep ι-natRec on natZero. -/
  | iotaNatRecZeroDeep {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRaw zeroRawSource zeroRawTarget succRaw : RawTerm scope}
      {scrutinee : Term context Ty.nat scrutineeRaw}
      {zeroSource : Term context motiveType zeroRawSource}
      {zeroTarget : Term context motiveType zeroRawTarget}
      (succBranch :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
      Step.par scrutinee Term.natZero →
      Step.par zeroSource zeroTarget →
      Step.par (Term.natRec scrutinee zeroSource succBranch)
               zeroTarget
  /-- Deep ι-natRec on natSucc. -/
  | iotaNatRecSuccDeep {mode level scope} {context : Ctx mode level scope}
      {motiveType : Ty level scope}
      {scrutineeRaw predecessorRaw zeroRawSource zeroRawTarget
       succRawSource succRawTarget : RawTerm scope}
      {scrutinee : Term context Ty.nat scrutineeRaw}
      {predecessor : Term context Ty.nat predecessorRaw}
      {zeroSource : Term context motiveType zeroRawSource}
      {zeroTarget : Term context motiveType zeroRawTarget}
      {succSource :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawSource}
      {succTarget :
        Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRawTarget} :
      Step.par scrutinee (Term.natSucc predecessor) →
      Step.par zeroSource zeroTarget →
      Step.par succSource succTarget →
      Step.par (Term.natRec scrutinee zeroSource succSource)
               (Term.app (Term.app succTarget predecessor)
                         (Term.natRec predecessor zeroTarget succTarget))
  /-- Deep ι-listElim on listNil. -/
  | iotaListElimNilDeep {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutineeRaw nilRawSource nilRawTarget consRaw : RawTerm scope}
      {scrutinee : Term context (Ty.listType elementType) scrutineeRaw}
      {nilSource : Term context motiveType nilRawSource}
      {nilTarget : Term context motiveType nilRawTarget}
      (consBranch :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
      Step.par scrutinee (Term.listNil (elementType := elementType)) →
      Step.par nilSource nilTarget →
      Step.par (Term.listElim scrutinee nilSource consBranch)
               nilTarget
  /-- Deep ι-listElim on listCons. -/
  | iotaListElimConsDeep {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutineeRaw headRaw tailRaw nilRaw
       consRawSource consRawTarget : RawTerm scope}
      {scrutinee : Term context (Ty.listType elementType) scrutineeRaw}
      {headTerm : Term context elementType headRaw}
      {tailTerm : Term context (Ty.listType elementType) tailRaw}
      (nilBranch : Term context motiveType nilRaw)
      {consSource :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consRawSource}
      {consTarget :
        Term context (Ty.arrow elementType
                        (Ty.arrow (Ty.listType elementType) motiveType)) consRawTarget} :
      Step.par scrutinee (Term.listCons headTerm tailTerm) →
      Step.par consSource consTarget →
      Step.par (Term.listElim scrutinee nilBranch consSource)
               (Term.app (Term.app consTarget headTerm) tailTerm)
  /-- Deep ι-optionMatch on optionNone. -/
  | iotaOptionMatchNoneDeep {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutineeRaw noneRawSource noneRawTarget someRaw : RawTerm scope}
      {scrutinee : Term context (Ty.optionType elementType) scrutineeRaw}
      {noneSource : Term context motiveType noneRawSource}
      {noneTarget : Term context motiveType noneRawTarget}
      (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
      Step.par scrutinee (Term.optionNone (elementType := elementType)) →
      Step.par noneSource noneTarget →
      Step.par (Term.optionMatch scrutinee noneSource someBranch)
               noneTarget
  /-- Deep ι-optionMatch on optionSome. -/
  | iotaOptionMatchSomeDeep {mode level scope} {context : Ctx mode level scope}
      {elementType motiveType : Ty level scope}
      {scrutineeRaw valueRaw noneRaw
       someRawSource someRawTarget : RawTerm scope}
      {scrutinee : Term context (Ty.optionType elementType) scrutineeRaw}
      {valueTerm : Term context elementType valueRaw}
      (noneBranch : Term context motiveType noneRaw)
      {someSource : Term context (Ty.arrow elementType motiveType) someRawSource}
      {someTarget : Term context (Ty.arrow elementType motiveType) someRawTarget} :
      Step.par scrutinee (Term.optionSome valueTerm) →
      Step.par someSource someTarget →
      Step.par (Term.optionMatch scrutinee noneBranch someSource)
               (Term.app someTarget valueTerm)
  /-- Deep ι-eitherMatch on eitherInl. -/
  | iotaEitherMatchInlDeep {mode level scope} {context : Ctx mode level scope}
      {leftType rightType motiveType : Ty level scope}
      {scrutineeRaw valueRaw
       leftRawSource leftRawTarget rightRaw : RawTerm scope}
      {scrutinee : Term context (Ty.eitherType leftType rightType) scrutineeRaw}
      {valueTerm : Term context leftType valueRaw}
      {leftSource : Term context (Ty.arrow leftType motiveType) leftRawSource}
      {leftTarget : Term context (Ty.arrow leftType motiveType) leftRawTarget}
      (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
      Step.par scrutinee (Term.eitherInl (rightType := rightType) valueTerm) →
      Step.par leftSource leftTarget →
      Step.par (Term.eitherMatch scrutinee leftSource rightBranch)
               (Term.app leftTarget valueTerm)
  /-- Deep ι-eitherMatch on eitherInr. -/
  | iotaEitherMatchInrDeep {mode level scope} {context : Ctx mode level scope}
      {leftType rightType motiveType : Ty level scope}
      {scrutineeRaw valueRaw
       leftRaw rightRawSource rightRawTarget : RawTerm scope}
      {scrutinee : Term context (Ty.eitherType leftType rightType) scrutineeRaw}
      {valueTerm : Term context rightType valueRaw}
      (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
      {rightSource : Term context (Ty.arrow rightType motiveType) rightRawSource}
      {rightTarget : Term context (Ty.arrow rightType motiveType) rightRawTarget} :
      Step.par scrutinee (Term.eitherInr (leftType := leftType) valueTerm) →
      Step.par rightSource rightTarget →
      Step.par (Term.eitherMatch scrutinee leftBranch rightSource)
               (Term.app rightTarget valueTerm)
  /-- Deep ι-idJ on Term.refl. -/
  | iotaIdJReflDeep {mode level scope} {context : Ctx mode level scope}
      {carrier : Ty level scope} {endpoint : RawTerm scope}
      {motiveType : Ty level scope}
      {baseRawSource baseRawTarget witnessRawSource : RawTerm scope}
      {baseSource : Term context motiveType baseRawSource}
      {baseTarget : Term context motiveType baseRawTarget}
      {witnessSource :
        Term context (Ty.id carrier endpoint endpoint) witnessRawSource} :
      Step.par witnessSource (Term.refl carrier endpoint) →
      Step.par baseSource baseTarget →
      Step.par (Term.idJ (carrier := carrier)
                          (leftEndpoint := endpoint)
                          (rightEndpoint := endpoint)
                          baseSource witnessSource)
               baseTarget
  /-- Parallel-cong for `Term.cumulUp` — Phase CUMUL-2.6 Design D.
  A `Step.par` on the inner typed code lifts to a `Step.par` on the
  wrapping `cumulUp`.  Mirrors `Step.cumulUpInner` at the parallel
  level.  Single context throughout (Design D). -/
  | cumulUpInnerCong {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (lowerLevel higherLevel : UniverseLevel)
      (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
      (levelLeLow : lowerLevel.toNat + 1 ≤ level)
      (levelLeHigh : higherLevel.toNat + 1 ≤ level)
      {codeSourceRaw codeTargetRaw : RawTerm scope}
      {typeCodeSource :
        Term context (Ty.universe lowerLevel levelLeLow) codeSourceRaw}
      {typeCodeTarget :
        Term context (Ty.universe lowerLevel levelLeLow) codeTargetRaw} :
      Step.par typeCodeSource typeCodeTarget →
      Step.par (Term.cumulUp (context := context)
                             lowerLevel higherLevel cumulMonotone
                             levelLeLow levelLeHigh typeCodeSource)
               (Term.cumulUp (context := context)
                             lowerLevel higherLevel cumulMonotone
                             levelLeLow levelLeHigh typeCodeTarget)
  /-- **Univalence rfl-fragment at the parallel level.**  Mirrors
  `Step.eqType`: the canonical Id-typed identity-equivalence proof at
  the universe parallel-reduces in one step to the canonical identity
  equivalence.  Both project to the SAME raw form
  `RawTerm.equivIntro id id`, so `Step.par.toRawBridge` returns
  `RawStep.par.refl _`.
  Phase 12.A.B8.1 (CUMUL-8.3 part 1). -/
  | eqType {mode : Mode} {level scope : Nat}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      {context : Ctx mode level scope}
      (carrier : Ty level scope)
      (carrierRaw : RawTerm scope) :
      Step.par
        (Term.equivReflIdAtId (context := context)
                              innerLevel innerLevelLt carrier carrierRaw)
        (Term.equivReflId (context := context) carrier)
  /-- **Funext rfl-fragment at the parallel level.**  Mirrors
  `Step.eqArrow`: the canonical Id-typed funext witness at arrow types
  parallel-reduces to the canonical pointwise-refl funext witness.
  Both project to the SAME raw form `RawTerm.lam (RawTerm.refl
  applyRaw)`, so the toRawBridge arm is `RawStep.par.refl _`.
  Phase 12.A.B8.2 (CUMUL-8.3 part 2). -/
  | eqArrow {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (domainType codomainType : Ty level scope)
      (applyRaw : RawTerm (scope + 1)) :
      Step.par
        (Term.funextReflAtId (context := context)
                             domainType codomainType applyRaw)
        (Term.funextRefl (context := context)
                         domainType codomainType applyRaw)
  /-- Parallel-cong: heterogeneous equivIntroHet reduces in both
  subterms.  Phase 12.A.B8.5: two-subterm cong rule mirroring
  `Step.par.pair` / `Step.par.listCons` — forward + backward
  parallel-reduce simultaneously, the carrier types are fixed,
  the ctor reassembles. -/
  | equivIntroHetCong {mode level scope}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      {forwardRawSource forwardRawTarget
       backwardRawSource backwardRawTarget : RawTerm scope}
      {forwardSource :
        Term context (Ty.arrow carrierA carrierB) forwardRawSource}
      {forwardTarget :
        Term context (Ty.arrow carrierA carrierB) forwardRawTarget}
      {backwardSource :
        Term context (Ty.arrow carrierB carrierA) backwardRawSource}
      {backwardTarget :
        Term context (Ty.arrow carrierB carrierA) backwardRawTarget} :
      Step.par forwardSource forwardTarget →
      Step.par backwardSource backwardTarget →
      Step.par (Term.equivIntroHet forwardSource backwardSource)
               (Term.equivIntroHet forwardTarget backwardTarget)
  /-- Raw-name parity alias for heterogeneous equivalence introduction
  congruence.  The raw constructor is `RawStep.par.equivIntroCong`;
  the typed carrier is `Term.equivIntroHet`. -/
  | equivIntroCong {mode level scope}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      {forwardRawSource forwardRawTarget
       backwardRawSource backwardRawTarget : RawTerm scope}
      {forwardSource :
        Term context (Ty.arrow carrierA carrierB) forwardRawSource}
      {forwardTarget :
        Term context (Ty.arrow carrierA carrierB) forwardRawTarget}
      {backwardSource :
        Term context (Ty.arrow carrierB carrierA) backwardRawSource}
      {backwardTarget :
        Term context (Ty.arrow carrierB carrierA) backwardRawTarget} :
      Step.par forwardSource forwardTarget →
      Step.par backwardSource backwardTarget →
      Step.par (Term.equivIntroHet forwardSource backwardSource)
               (Term.equivIntroHet forwardTarget backwardTarget)
  /-- Raw-name parity: equivalence application reduces in the equivalence
  and argument positions. -/
  | equivAppCong {mode level scope}
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      {equivRawSource equivRawTarget argumentRawSource argumentRawTarget :
        RawTerm scope}
      {equivSource : Term context (Ty.equiv carrierA carrierB) equivRawSource}
      {equivTarget : Term context (Ty.equiv carrierA carrierB) equivRawTarget}
      {argumentSource : Term context carrierA argumentRawSource}
      {argumentTarget : Term context carrierA argumentRawTarget} :
      Step.par equivSource equivTarget →
      Step.par argumentSource argumentTarget →
      Step.par (Term.equivApp equivSource argumentSource)
               (Term.equivApp equivTarget argumentTarget)
  /-- Parallel-cong: heterogeneous uaIntroHet reduces in its single
  equivWitness subterm.  Phase 12.A.B8.5b: single-subterm cong rule
  mirroring `Step.par.optionSomeCong` / `Step.par.natSuccCong` — the
  packaged equivalence parallel-reduces, the carriers + carrier raws
  + universe level + cumul witness are fixed, the ctor reassembles
  with the new raw indices.  Note: the source and target equivWitness
  are at the SAME `Ty.equiv carrierA carrierB` type but with different
  `RawTerm.equivIntro` raws — exactly as `equivIntroHetCong`. -/
  | uaIntroHetCong {mode level scope}
      {context : Ctx mode level scope}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      {carrierA carrierB : Ty level scope}
      (carrierARaw carrierBRaw : RawTerm scope)
      {forwardRawSource forwardRawTarget
       backwardRawSource backwardRawTarget : RawTerm scope}
      {equivWitnessSource :
        Term context (Ty.equiv carrierA carrierB)
          (RawTerm.equivIntro forwardRawSource backwardRawSource)}
      {equivWitnessTarget :
        Term context (Ty.equiv carrierA carrierB)
          (RawTerm.equivIntro forwardRawTarget backwardRawTarget)} :
      Step.par equivWitnessSource equivWitnessTarget →
      Step.par (Term.uaIntroHet (context := context)
                                innerLevel innerLevelLt
                                carrierARaw carrierBRaw
                                equivWitnessSource)
               (Term.uaIntroHet (context := context)
                                innerLevel innerLevelLt
                                carrierARaw carrierBRaw
                                equivWitnessTarget)
  /-- **Heterogeneous Univalence at the parallel level.**  Mirrors
  `Step.eqTypeHet`: the heterogeneous-carrier path-from-equivalence
  proof at the universe parallel-reduces in one step to the underlying
  packaged equivalence.  Both project to the SAME raw form
  `RawTerm.equivIntro forwardRaw backwardRaw` (the architectural
  raw-alignment trick of `Term.uaIntroHet`), so
  `Step.par.toRawBridge` returns `RawStep.par.refl _`.
  Phase 12.A.B8.6 (heterogeneous Univalence at par level). -/
  | eqTypeHet {mode : Mode} {level scope : Nat}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      {context : Ctx mode level scope}
      {carrierA carrierB : Ty level scope}
      (carrierARaw carrierBRaw : RawTerm scope)
      {forwardRaw backwardRaw : RawTerm scope}
      (equivWitness : Term context (Ty.equiv carrierA carrierB)
                                   (RawTerm.equivIntro forwardRaw backwardRaw)) :
      Step.par
        (Term.uaIntroHet (context := context)
                         innerLevel innerLevelLt
                         carrierARaw carrierBRaw equivWitness)
        equivWitness
  /-- **Heterogeneous funext at the parallel level.**  Mirrors
  `Step.eqArrowHet`: the heterogeneous-carrier funext-introduction
  Term at Id-of-arrow parallel-reduces in one step to the canonical
  pointwise-refl funext witness instantiated at `applyARaw`.  Both
  project to the SAME raw form `RawTerm.lam (RawTerm.refl applyARaw)`
  (the architectural raw-alignment trick of `Term.funextIntroHet`),
  so `Step.par.toRawBridge` returns `RawStep.par.refl _`.
  Phase 12.A.B8.B (heterogeneous funext at par level). -/
  | eqArrowHet {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (domainType codomainType : Ty level scope)
      (applyARaw applyBRaw : RawTerm (scope + 1)) :
      Step.par
        (Term.funextIntroHet (context := context)
                             domainType codomainType applyARaw applyBRaw)
        (Term.funextRefl (context := context)
                         domainType codomainType applyARaw)

/-! ## Step.toPar — single-step ⇒ parallel.

Each `Step` ctor lifts to `Step.par` by inserting `Step.par.refl` at
positions left unchanged.  Used in Layer 3 to lift `StepStar` chains
into `Step.par` chains. -/

theorem Step.toPar
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (singleStep : Step sourceTerm targetTerm) :
    Step.par sourceTerm targetTerm := by
  induction singleStep with
  | appLeft singleStep singleStepIH =>
      exact Step.par.app singleStepIH (Step.par.refl _)
  | appRight singleStep singleStepIH =>
      exact Step.par.app (Step.par.refl _) singleStepIH
  | lamBody singleStep singleStepIH => exact Step.par.lam singleStepIH
  | appPiLeft singleStep singleStepIH =>
      exact Step.par.appPi singleStepIH (Step.par.refl _)
  | appPiRight singleStep singleStepIH =>
      exact Step.par.appPi (Step.par.refl _) singleStepIH
  | lamPiBody singleStep singleStepIH => exact Step.par.lamPi singleStepIH
  | pairRight singleStep singleStepIH =>
      exact Step.par.pair (Step.par.refl _) singleStepIH
  | fstCong singleStep singleStepIH => exact Step.par.fst singleStepIH
  | sndCong singleStep singleStepIH => exact Step.par.snd singleStepIH
  | betaApp body arg =>
      exact Step.par.betaApp (Step.par.refl body) (Step.par.refl arg)
  | betaAppPi body arg =>
      exact Step.par.betaAppPi (Step.par.refl body) (Step.par.refl arg)
  | betaFstPair fv sv =>
      exact Step.par.betaFstPair sv (Step.par.refl fv)
  | betaSndPair fv sv =>
      exact Step.par.betaSndPair fv (Step.par.refl sv)
  | boolElimScrutinee singleStep singleStepIH =>
      exact Step.par.boolElim singleStepIH (Step.par.refl _) (Step.par.refl _)
  | boolElimThen singleStep singleStepIH =>
      exact Step.par.boolElim (Step.par.refl _) singleStepIH (Step.par.refl _)
  | boolElimElse singleStep singleStepIH =>
      exact Step.par.boolElim (Step.par.refl _) (Step.par.refl _) singleStepIH
  | iotaBoolElimTrue thenBranch elseBranch =>
      exact Step.par.iotaBoolElimTrue elseBranch (Step.par.refl thenBranch)
  | iotaBoolElimFalse thenBranch elseBranch =>
      exact Step.par.iotaBoolElimFalse thenBranch (Step.par.refl elseBranch)
  | natSuccPred singleStep singleStepIH => exact Step.par.natSucc singleStepIH
  | natElimScrutinee singleStep singleStepIH =>
      exact Step.par.natElim singleStepIH (Step.par.refl _) (Step.par.refl _)
  | natElimZero singleStep singleStepIH =>
      exact Step.par.natElim (Step.par.refl _) singleStepIH (Step.par.refl _)
  | natElimSucc singleStep singleStepIH =>
      exact Step.par.natElim (Step.par.refl _) (Step.par.refl _) singleStepIH
  | iotaNatElimZero zeroBranch succBranch =>
      exact Step.par.iotaNatElimZero succBranch (Step.par.refl zeroBranch)
  | iotaNatElimSucc predecessor zeroBranch succBranch =>
      exact Step.par.iotaNatElimSucc zeroBranch
              (Step.par.refl predecessor) (Step.par.refl succBranch)
  | natRecScrutinee singleStep singleStepIH =>
      exact Step.par.natRec singleStepIH (Step.par.refl _) (Step.par.refl _)
  | natRecZero singleStep singleStepIH =>
      exact Step.par.natRec (Step.par.refl _) singleStepIH (Step.par.refl _)
  | natRecSucc singleStep singleStepIH =>
      exact Step.par.natRec (Step.par.refl _) (Step.par.refl _) singleStepIH
  | iotaNatRecZero zeroBranch succBranch =>
      exact Step.par.iotaNatRecZero succBranch (Step.par.refl zeroBranch)
  | iotaNatRecSucc predecessor zeroBranch succBranch =>
      exact Step.par.iotaNatRecSucc
              (Step.par.refl predecessor)
              (Step.par.refl zeroBranch)
              (Step.par.refl succBranch)
  | listConsHead singleStep singleStepIH =>
      exact Step.par.listCons singleStepIH (Step.par.refl _)
  | listConsTail singleStep singleStepIH =>
      exact Step.par.listCons (Step.par.refl _) singleStepIH
  | listElimScrutinee singleStep singleStepIH =>
      exact Step.par.listElim singleStepIH (Step.par.refl _) (Step.par.refl _)
  | listElimNil singleStep singleStepIH =>
      exact Step.par.listElim (Step.par.refl _) singleStepIH (Step.par.refl _)
  | listElimCons singleStep singleStepIH =>
      exact Step.par.listElim (Step.par.refl _) (Step.par.refl _) singleStepIH
  | iotaListElimNil nilBranch consBranch =>
      exact Step.par.iotaListElimNil consBranch (Step.par.refl nilBranch)
  | iotaListElimCons headTerm tailTerm nilBranch consBranch =>
      exact Step.par.iotaListElimCons nilBranch
              (Step.par.refl headTerm)
              (Step.par.refl tailTerm)
              (Step.par.refl consBranch)
  | optionSomeValue singleStep singleStepIH =>
      exact Step.par.optionSome singleStepIH
  | optionMatchScrutinee singleStep singleStepIH =>
      exact Step.par.optionMatch singleStepIH
              (Step.par.refl _) (Step.par.refl _)
  | optionMatchNone singleStep singleStepIH =>
      exact Step.par.optionMatch (Step.par.refl _) singleStepIH (Step.par.refl _)
  | optionMatchSome singleStep singleStepIH =>
      exact Step.par.optionMatch (Step.par.refl _) (Step.par.refl _) singleStepIH
  | iotaOptionMatchNone noneBranch someBranch =>
      exact Step.par.iotaOptionMatchNone someBranch (Step.par.refl noneBranch)
  | iotaOptionMatchSome valueTerm noneBranch someBranch =>
      exact Step.par.iotaOptionMatchSome noneBranch
              (Step.par.refl valueTerm)
              (Step.par.refl someBranch)
  | eitherInlValue singleStep singleStepIH =>
      exact Step.par.eitherInl singleStepIH
  | eitherInrValue singleStep singleStepIH =>
      exact Step.par.eitherInr singleStepIH
  | eitherMatchScrutinee singleStep singleStepIH =>
      exact Step.par.eitherMatch singleStepIH
              (Step.par.refl _) (Step.par.refl _)
  | eitherMatchLeft singleStep singleStepIH =>
      exact Step.par.eitherMatch (Step.par.refl _) singleStepIH (Step.par.refl _)
  | eitherMatchRight singleStep singleStepIH =>
      exact Step.par.eitherMatch (Step.par.refl _) (Step.par.refl _) singleStepIH
  | iotaEitherMatchInl valueTerm leftBranch rightBranch =>
      exact Step.par.iotaEitherMatchInl rightBranch
              (Step.par.refl valueTerm)
              (Step.par.refl leftBranch)
  | iotaEitherMatchInr valueTerm leftBranch rightBranch =>
      exact Step.par.iotaEitherMatchInr leftBranch
              (Step.par.refl valueTerm)
              (Step.par.refl rightBranch)
  | idJBase singleStep singleStepIH =>
      exact Step.par.idJ singleStepIH (Step.par.refl _)
  | idJWitness baseCase singleStep singleStepIH =>
      exact Step.par.idJ (Step.par.refl baseCase) singleStepIH
  | oeqJBase singleStep singleStepIH =>
      exact Step.par.oeqJCong singleStepIH (Step.par.refl _)
  | oeqJWitness baseCase singleStep singleStepIH =>
      exact Step.par.oeqJCong (Step.par.refl baseCase) singleStepIH
  | oeqFunextPointwise domainType codomainType
      leftFunctionRaw rightFunctionRaw singleStep singleStepIH =>
      exact Step.par.oeqFunextCong domainType codomainType
        leftFunctionRaw rightFunctionRaw singleStepIH
  | idStrictRecBase singleStep singleStepIH =>
      exact Step.par.idStrictRecCong singleStepIH (Step.par.refl _)
  | idStrictRecWitness baseCase singleStep singleStepIH =>
      exact Step.par.idStrictRecCong (Step.par.refl baseCase) singleStepIH
  | iotaIdJRefl carrier endpoint baseCase =>
      exact Step.par.iotaIdJRefl carrier endpoint (Step.par.refl baseCase)
  | modIntroInner singleStep singleStepIH =>
      exact Step.par.modIntro singleStepIH
  | modElimInner singleStep singleStepIH =>
      exact Step.par.modElim singleStepIH
  | subsumeInner singleStep singleStepIH =>
      exact Step.par.subsume singleStepIH
  | pathLamBody singleStep singleStepIH =>
      exact Step.par.pathLamCong singleStepIH
  | pathAppPath singleStep singleStepIH =>
      exact Step.par.pathAppCong singleStepIH (Step.par.refl _)
  | pathAppInterval singleStep singleStepIH =>
      exact Step.par.pathAppCong (Step.par.refl _) singleStepIH
  | betaPathApp bodyTerm intervalTerm =>
      exact Step.par.betaPathApp
        (Step.par.refl bodyTerm) (Step.par.refl intervalTerm)
  | glueIntroBase singleStep singleStepIH =>
      exact Step.par.glueIntroCong singleStepIH (Step.par.refl _)
  | glueIntroPartial singleStep singleStepIH =>
      exact Step.par.glueIntroCong (Step.par.refl _) singleStepIH
  | glueElimValue singleStep singleStepIH =>
      exact Step.par.glueElimCong singleStepIH
  | betaGlueElimIntro baseValue partialValue =>
      exact Step.par.betaGlueElimIntro
        (Step.par.refl baseValue) (Step.par.refl partialValue)
  | intervalOppInner singleStep singleStepIH =>
      exact Step.par.intervalOppCong singleStepIH
  | intervalMeetLeft singleStep singleStepIH =>
      exact Step.par.intervalMeetCong singleStepIH (Step.par.refl _)
  | intervalMeetRight singleStep singleStepIH =>
      exact Step.par.intervalMeetCong (Step.par.refl _) singleStepIH
  | intervalJoinLeft singleStep singleStepIH =>
      exact Step.par.intervalJoinCong singleStepIH (Step.par.refl _)
  | intervalJoinRight singleStep singleStepIH =>
      exact Step.par.intervalJoinCong (Step.par.refl _) singleStepIH
  | recordIntroField singleStep singleStepIH =>
      exact Step.par.recordIntroCong singleStepIH
  | recordProjRecord singleStep singleStepIH =>
      exact Step.par.recordProjCong singleStepIH
  | betaRecordProjIntro firstField =>
      exact Step.par.betaRecordProjIntro (Step.par.refl firstField)
  | refineIntroValue singleStep singleStepIH =>
      exact Step.par.refineIntroCong singleStepIH (Step.par.refl _)
  | refineIntroProof singleStep singleStepIH =>
      exact Step.par.refineIntroCong (Step.par.refl _) singleStepIH
  | refineElimValue singleStep singleStepIH =>
      exact Step.par.refineElimCong singleStepIH
  | betaRefineElimIntro predicate baseValue predicateProof =>
      exact Step.par.betaRefineElimIntro
        (Step.par.refl baseValue) (Step.par.refl predicateProof)
  | codataUnfoldState singleStep singleStepIH =>
      exact Step.par.codataUnfoldCong singleStepIH (Step.par.refl _)
  | codataUnfoldTransition singleStep singleStepIH =>
      exact Step.par.codataUnfoldCong (Step.par.refl _) singleStepIH
  | codataDestValue singleStep singleStepIH =>
      exact Step.par.codataDestCong singleStepIH
  | sessionSendChannel singleStep singleStepIH =>
      exact Step.par.sessionSendCong singleStepIH (Step.par.refl _)
  | sessionSendPayload singleStep singleStepIH =>
      exact Step.par.sessionSendCong (Step.par.refl _) singleStepIH
  | sessionRecvChannel singleStep singleStepIH =>
      exact Step.par.sessionRecvCong singleStepIH
  | effectPerformOperation singleStep singleStepIH =>
      exact Step.par.effectPerformCong singleStepIH (Step.par.refl _)
  | effectPerformArguments singleStep singleStepIH =>
      exact Step.par.effectPerformCong (Step.par.refl _) singleStepIH
  | transpPath universeLevel universeLevelLt sourceType targetType
      sourceTypeRaw targetTypeRaw singleStep singleStepIH =>
      exact Step.par.transpCong universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw
        singleStepIH (Step.par.refl _)
  | transpSource universeLevel universeLevelLt sourceType targetType
      sourceTypeRaw targetTypeRaw singleStep singleStepIH =>
      exact Step.par.transpCong universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw
        (Step.par.refl _) singleStepIH
  | hcompSides singleStep singleStepIH =>
      exact Step.par.hcompCong singleStepIH (Step.par.refl _)
  | hcompCap singleStep singleStepIH =>
      exact Step.par.hcompCong (Step.par.refl _) singleStepIH
  | equivIntroHetForward singleStep singleStepIH =>
      exact Step.par.equivIntroHetCong singleStepIH (Step.par.refl _)
  | equivIntroHetBackward singleStep singleStepIH =>
      exact Step.par.equivIntroHetCong (Step.par.refl _) singleStepIH
  | equivAppEquiv singleStep singleStepIH =>
      exact Step.par.equivAppCong singleStepIH (Step.par.refl _)
  | equivAppArgument equivTerm singleStep singleStepIH =>
      exact Step.par.equivAppCong (Step.par.refl equivTerm) singleStepIH
  | uaIntroHetWitness innerLevel innerLevelLt carrierARaw carrierBRaw
      singleStep singleStepIH =>
      exact Step.par.uaIntroHetCong innerLevel innerLevelLt
        carrierARaw carrierBRaw singleStepIH
  | cumulUpInner lowerLevel higherLevel cumulMonotone
                  levelLeLow levelLeHigh _ singleStepIH =>
      exact Step.par.cumulUpInnerCong lowerLevel higherLevel cumulMonotone
                                       levelLeLow levelLeHigh
                                       singleStepIH
  -- Univalence rfl-fragment lift to par: source has no inner steps
  -- (it's a leaf-canonical ctor), so we apply Step.par.eqType directly.
  | eqType innerLevel innerLevelLt carrier carrierRaw =>
      exact Step.par.eqType innerLevel innerLevelLt carrier carrierRaw
  -- Funext rfl-fragment lift to par: source has no inner steps; apply
  -- Step.par.eqArrow directly.
  | eqArrow domainType codomainType applyRaw =>
      exact Step.par.eqArrow domainType codomainType applyRaw
  -- Heterogeneous Univalence lift to par: source `Term.uaIntroHet
  -- ... equivWitness` has no inner steps relevant to this rule (the
  -- whole packaged Term reduces to its underlying equivWitness via a
  -- single par step), so apply `Step.par.eqTypeHet` directly.
  | eqTypeHet innerLevel innerLevelLt carrierARaw carrierBRaw equivWitness =>
      exact Step.par.eqTypeHet innerLevel innerLevelLt
                                carrierARaw carrierBRaw equivWitness
  -- Heterogeneous funext lift to par: source `Term.funextIntroHet
  -- ... applyARaw applyBRaw` has no inner steps (it's a leaf-
  -- canonical VALUE ctor, like `funextReflAtId`), so apply
  -- `Step.par.eqArrowHet` directly.
  | eqArrowHet domainType codomainType applyARaw applyBRaw =>
      exact Step.par.eqArrowHet domainType codomainType applyARaw applyBRaw

/-! ## Cast helpers — propositional transport for indices. -/

theorem Step.par.castSourceType
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceTypeOriginal sourceTypeReplacement targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : sourceTypeOriginal = sourceTypeReplacement)
    {sourceTerm : Term context sourceTypeOriginal sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (parallelStep : Step.par sourceTerm targetTerm) :
    Step.par (typeEquality ▸ sourceTerm) targetTerm := by
  cases typeEquality
  exact parallelStep

theorem Step.par.castTargetType
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetTypeOriginal targetTypeReplacement : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    (typeEquality : targetTypeOriginal = targetTypeReplacement)
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetTypeOriginal targetRaw}
    (parallelStep : Step.par sourceTerm targetTerm) :
    Step.par sourceTerm (typeEquality ▸ targetTerm) := by
  cases typeEquality
  exact parallelStep

theorem Step.par.castSourceTerm
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceOriginal sourceReplacement : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (sourceEquality : sourceOriginal = sourceReplacement)
    (parallelStep : Step.par sourceOriginal targetTerm) :
    Step.par sourceReplacement targetTerm := by
  cases sourceEquality
  exact parallelStep

theorem Step.par.castTargetTerm
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetOriginal targetReplacement : Term context targetType targetRaw}
    (targetEquality : targetOriginal = targetReplacement)
    (parallelStep : Step.par sourceTerm targetOriginal) :
    Step.par sourceTerm targetReplacement := by
  cases targetEquality
  exact parallelStep

end LeanFX2

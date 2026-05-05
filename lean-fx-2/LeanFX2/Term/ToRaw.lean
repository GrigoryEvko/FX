import LeanFX2.Term

/-! # Term/ToRaw — projection (collapses to rfl).

The architectural payoff of raw-aware Term: `Term.toRaw t = raw` is
**rfl** — the projection IS the type index.  No structural recursion,
no proof obligations, no bridge cascade.

Compare with lean-fx's `Term.toRaw : Term ctx ty → RawTerm scope`
which was a 53-line structural recursion plus ~10 supporting lemmas.

## Definition

```lean
@[reducible]
def Term.toRaw : Term ctx ty raw → RawTerm scope := fun _ => raw
```

Wait — this isn't quite right because `raw` is implicit.  The
correct form pulls `raw` out of the function via the implicit:

```lean
@[reducible]
def Term.toRaw {mode level scope ctx ty raw} (_ : @Term mode level scope ctx ty raw) :
    RawTerm scope := raw
```

## Lemmas (all rfl)

* `Term.toRaw_var` — toRaw of `Term.var i` is `RawTerm.var i`
* `Term.toRaw_unit` — toRaw of `Term.unit` is `RawTerm.unit`
* `Term.toRaw_lam` — toRaw of `Term.lam body` is `RawTerm.lam body.toRaw`
* ... (all current ctors)

Each lemma is proved by `rfl`.  These lemmas exist as named decls
(not just inline `rfl`) for:
1. **Discoverability** — searching for "toRaw_subst" finds the rule
2. **simp lemma usability** — `simp only [Term.toRaw_*]` rewrites in
   bridge proofs
3. **Documentation** — the file enumerates the projection's behavior
   on every constructor
-/

namespace LeanFX2

/-- The raw projection.  By construction it returns the type-index
`raw` directly, so `Term.toRaw t = t`'s third index is `rfl`. -/
@[reducible]
def Term.toRaw {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (_ : Term context ty raw) : RawTerm scope :=
  raw

/-! ## Per-ctor rfl lemmas. -/

theorem Term.toRaw_var {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} (position : Fin scope) :
    (Term.var (context := context) position).toRaw = RawTerm.var position := rfl

theorem Term.toRaw_unit {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    (Term.unit (context := context)).toRaw = RawTerm.unit := rfl

theorem Term.toRaw_lam {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope} {bodyRaw : RawTerm (scope + 1)}
    (body : Term (Ctx.cons context domainType) codomainType.weaken bodyRaw) :
    (Term.lam body).toRaw = RawTerm.lam body.toRaw := rfl

theorem Term.toRaw_app {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm : Term context (Ty.arrow domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    (Term.app functionTerm argumentTerm).toRaw =
      RawTerm.app functionTerm.toRaw argumentTerm.toRaw := rfl

theorem Term.toRaw_lamPi {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (Ctx.cons context domainType) codomainType bodyRaw) :
    (Term.lamPi body).toRaw = RawTerm.lam body.toRaw := rfl

theorem Term.toRaw_appPi {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    (functionTerm : Term context (Ty.piTy domainType codomainType) functionRaw)
    (argumentTerm : Term context domainType argumentRaw) :
    (Term.appPi functionTerm argumentTerm).toRaw =
      RawTerm.app functionTerm.toRaw argumentTerm.toRaw := rfl

theorem Term.toRaw_pair {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    (firstValue : Term context firstType firstRaw)
    (secondValue : Term context (secondType.subst0 firstType firstRaw) secondRaw) :
    (Term.pair firstValue secondValue).toRaw =
      RawTerm.pair firstValue.toRaw secondValue.toRaw := rfl

theorem Term.toRaw_fst {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    (Term.fst pairTerm).toRaw = RawTerm.fst pairTerm.toRaw := rfl

theorem Term.toRaw_snd {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw) :
    (Term.snd pairTerm).toRaw = RawTerm.snd pairTerm.toRaw := rfl

theorem Term.toRaw_refl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    (Term.refl (context := context) carrier rawWitness).toRaw =
      RawTerm.refl rawWitness := rfl

theorem Term.toRaw_idJ {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness : Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw) :
    (Term.idJ baseCase witness).toRaw =
      RawTerm.idJ baseCase.toRaw witness.toRaw := rfl

theorem Term.toRaw_idStrictRefl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrier : Ty level scope) (rawWitness : RawTerm scope) :
    (Term.idStrictRefl (context := context) carrier rawWitness).toRaw =
      RawTerm.idStrictRefl rawWitness := rfl

theorem Term.toRaw_idStrictRec {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier : Ty level scope} {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw)
    (witness :
      Term context (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw) :
    (Term.idStrictRec baseCase witness).toRaw =
      RawTerm.idStrictRec baseCase.toRaw witness.toRaw := rfl

theorem Term.toRaw_codataUnfold {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (initialState : Term context stateType stateRaw)
    (transition : Term context (Ty.arrow stateType outputType) transitionRaw) :
    (Term.codataUnfold initialState transition).toRaw =
      RawTerm.codataUnfold initialState.toRaw transition.toRaw := rfl

theorem Term.toRaw_codataDest {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    (codataValue : Term context (Ty.codata stateType outputType) codataRaw) :
    (Term.codataDest codataValue).toRaw =
      RawTerm.codataDest codataValue.toRaw := rfl

/-! ## Booleans, Naturals, Lists, Options, Eithers, Modal -/

theorem Term.toRaw_boolTrue {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    (Term.boolTrue (context := context)).toRaw = RawTerm.boolTrue := rfl

theorem Term.toRaw_boolFalse {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    (Term.boolFalse (context := context)).toRaw = RawTerm.boolFalse := rfl

theorem Term.toRaw_boolElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {motiveType : Ty level scope}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch : Term context motiveType thenRaw)
    (elseBranch : Term context motiveType elseRaw) :
    (Term.boolElim scrutinee thenBranch elseBranch).toRaw =
      RawTerm.boolElim scrutinee.toRaw thenBranch.toRaw elseBranch.toRaw := rfl

theorem Term.toRaw_natZero {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    (Term.natZero (context := context)).toRaw = RawTerm.natZero := rfl

theorem Term.toRaw_natSucc {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {predecessorRaw : RawTerm scope}
    (predecessor : Term context Ty.nat predecessorRaw) :
    (Term.natSucc predecessor).toRaw = RawTerm.natSucc predecessor.toRaw := rfl

theorem Term.toRaw_natElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
    (Term.natElim scrutinee zeroBranch succBranch).toRaw =
      RawTerm.natElim scrutinee.toRaw zeroBranch.toRaw succBranch.toRaw := rfl

theorem Term.toRaw_natRec {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
    (Term.natRec scrutinee zeroBranch succBranch).toRaw =
      RawTerm.natRec scrutinee.toRaw zeroBranch.toRaw succBranch.toRaw := rfl

theorem Term.toRaw_listNil {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {elementType : Ty level scope} :
    (Term.listNil (context := context) (elementType := elementType)).toRaw =
      RawTerm.listNil := rfl

theorem Term.toRaw_listCons {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    (headTerm : Term context elementType headRaw)
    (tailTerm : Term context (Ty.listType elementType) tailRaw) :
    (Term.listCons headTerm tailTerm).toRaw =
      RawTerm.listCons headTerm.toRaw tailTerm.toRaw := rfl

theorem Term.toRaw_listElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutineeRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch : Term context (Ty.arrow elementType
                                  (Ty.arrow (Ty.listType elementType) motiveType)) consRaw) :
    (Term.listElim scrutinee nilBranch consBranch).toRaw =
      RawTerm.listElim scrutinee.toRaw nilBranch.toRaw consBranch.toRaw := rfl

theorem Term.toRaw_optionNone {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {elementType : Ty level scope} :
    (Term.optionNone (context := context) (elementType := elementType)).toRaw =
      RawTerm.optionNone := rfl

theorem Term.toRaw_optionSome {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {elementType : Ty level scope}
    {valueRaw : RawTerm scope} (valueTerm : Term context elementType valueRaw) :
    (Term.optionSome valueTerm).toRaw = RawTerm.optionSome valueTerm.toRaw := rfl

theorem Term.toRaw_optionMatch {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutineeRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw) :
    (Term.optionMatch scrutinee noneBranch someBranch).toRaw =
      RawTerm.optionMatch scrutinee.toRaw noneBranch.toRaw someBranch.toRaw := rfl

theorem Term.toRaw_eitherInl {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope} {valueRaw : RawTerm scope}
    (valueTerm : Term context leftType valueRaw) :
    (Term.eitherInl (rightType := rightType) valueTerm).toRaw =
      RawTerm.eitherInl valueTerm.toRaw := rfl

theorem Term.toRaw_eitherInr {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType : Ty level scope} {valueRaw : RawTerm scope}
    (valueTerm : Term context rightType valueRaw) :
    (Term.eitherInr (leftType := leftType) valueTerm).toRaw =
      RawTerm.eitherInr valueTerm.toRaw := rfl

theorem Term.toRaw_eitherMatch {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    (scrutinee : Term context (Ty.eitherType leftType rightType) scrutineeRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw) :
    (Term.eitherMatch scrutinee leftBranch rightBranch).toRaw =
      RawTerm.eitherMatch scrutinee.toRaw leftBranch.toRaw rightBranch.toRaw := rfl

theorem Term.toRaw_modIntro {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope} {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    (Term.modIntro innerTerm).toRaw = RawTerm.modIntro innerTerm.toRaw := rfl

theorem Term.toRaw_modElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope} {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    (Term.modElim innerTerm).toRaw = RawTerm.modElim innerTerm.toRaw := rfl

theorem Term.toRaw_subsume {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope} {innerRaw : RawTerm scope}
    (innerTerm : Term context innerType innerRaw) :
    (Term.subsume innerTerm).toRaw = RawTerm.subsume innerTerm.toRaw := rfl

theorem Term.toRaw_interval0 {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    (Term.interval0 (context := context)).toRaw = RawTerm.interval0 := rfl

theorem Term.toRaw_interval1 {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    (Term.interval1 (context := context)).toRaw = RawTerm.interval1 := rfl

theorem Term.toRaw_intervalOpp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {innerRaw : RawTerm scope}
    (innerValue : Term context Ty.interval innerRaw) :
    (Term.intervalOpp innerValue).toRaw =
      RawTerm.intervalOpp innerValue.toRaw := rfl

theorem Term.toRaw_intervalMeet {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term context Ty.interval leftRaw)
    (rightValue : Term context Ty.interval rightRaw) :
    (Term.intervalMeet leftValue rightValue).toRaw =
      RawTerm.intervalMeet leftValue.toRaw rightValue.toRaw := rfl

theorem Term.toRaw_intervalJoin {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    (leftValue : Term context Ty.interval leftRaw)
    (rightValue : Term context Ty.interval rightRaw) :
    (Term.intervalJoin leftValue rightValue).toRaw =
      RawTerm.intervalJoin leftValue.toRaw rightValue.toRaw := rfl

theorem Term.toRaw_pathLam {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRaw : RawTerm (scope + 1)}
    (body : Term (context.cons Ty.interval) carrierType.weaken bodyRaw) :
    (Term.pathLam carrierType leftEndpoint rightEndpoint body).toRaw =
      RawTerm.pathLam body.toRaw := rfl

theorem Term.toRaw_pathApp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    (pathTerm : Term context
      (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw)
    (intervalTerm : Term context Ty.interval intervalRaw) :
    (Term.pathApp pathTerm intervalTerm).toRaw =
      RawTerm.pathApp pathTerm.toRaw intervalTerm.toRaw := rfl

theorem Term.toRaw_glueIntro {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (baseType : Ty level scope) (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    (baseValue : Term context baseType baseRaw)
    (partialValue : Term context baseType partialRaw) :
    (Term.glueIntro baseType boundaryWitness baseValue partialValue).toRaw =
      RawTerm.glueIntro baseValue.toRaw partialValue.toRaw := rfl

theorem Term.toRaw_glueElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    (gluedValue : Term context (Ty.glue baseType boundaryWitness) gluedRaw) :
    (Term.glueElim gluedValue).toRaw =
      RawTerm.glueElim gluedValue.toRaw := rfl

theorem Term.toRaw_transp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level scope)
    (sourceTypeRaw targetTypeRaw : RawTerm scope)
    {pathRaw sourceRaw : RawTerm scope}
    (typePath :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw)
    (sourceValue : Term context sourceType sourceRaw) :
    (Term.transp universeLevel universeLevelLt sourceType targetType
      sourceTypeRaw targetTypeRaw typePath sourceValue).toRaw =
      RawTerm.transp typePath.toRaw sourceValue.toRaw := rfl

theorem Term.toRaw_hcomp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    (sidesValue : Term context carrierType sidesRaw)
    (capValue : Term context carrierType capRaw) :
    (Term.hcomp sidesValue capValue).toRaw =
      RawTerm.hcomp sidesValue.toRaw capValue.toRaw := rfl

theorem Term.toRaw_recordIntro {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (firstField : Term context singleFieldType firstRaw) :
    (Term.recordIntro firstField).toRaw =
      RawTerm.recordIntro firstField.toRaw := rfl

theorem Term.toRaw_recordProj {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    (recordValue : Term context (Ty.record singleFieldType) recordRaw) :
    (Term.recordProj recordValue).toRaw =
      RawTerm.recordProj recordValue.toRaw := rfl

theorem Term.toRaw_refineIntro {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    (predicate : RawTerm (scope + 1))
    {valueRaw proofRaw : RawTerm scope}
    (baseValue : Term context baseType valueRaw)
    (predicateProof : Term context Ty.unit proofRaw) :
    (Term.refineIntro predicate baseValue predicateProof).toRaw =
      RawTerm.refineIntro baseValue.toRaw predicateProof.toRaw := rfl

theorem Term.toRaw_refineElim {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    (refinedValue : Term context (Ty.refine baseType predicate) refinedRaw) :
    (Term.refineElim refinedValue).toRaw =
      RawTerm.refineElim refinedValue.toRaw := rfl

theorem Term.toRaw_equivApp {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term context carrierA argumentRaw) :
    (Term.equivApp equivTerm argumentTerm).toRaw =
      RawTerm.equivApp equivTerm.toRaw argumentTerm.toRaw := rfl

end LeanFX2

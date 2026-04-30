import LeanFX.Syntax.Reduction.ParSubst
import LeanFX.Syntax.CdDominates
import LeanFX.Syntax.CompleteDevelopment

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Step.par.isBi` — βι-only restriction predicate.

A Prop-valued inductive predicate over `Step.par` proofs that
witnesses "this step does not use η-arrow or η-sigma anywhere".

Why a separate predicate rather than a separate inductive copy of
`Step.par`?  The key invariant is constructor-by-constructor: each
Bi case mirrors a Step.par βι constructor and recursively requires
its sub-proofs to be Bi.  η constructors have no Bi case, so a
typed cd_lemma proven by induction-on-step-with-Bi-hypothesis
discharges the η constructors via vacuous case match (no Bi
constructor matches `Step.par.etaArrow _` or `Step.par.etaSigma _`).

This unblocks `Step.par.cd_lemma_star` for βι-restricted parallel
reductions — the form the task list (#988) explicitly calls for. -/
inductive Step.par.isBi :
    ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
      {termType : Ty level scope}
      {sourceTerm targetTerm : Term ctx termType},
    Step.par sourceTerm targetTerm → Prop
  /-- Reflexivity is βι. -/
  | refl : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {termType : Ty level scope} (term : Term ctx termType),
      Step.par.isBi (Step.par.refl term)
  /-- Non-dependent application congruence is βι. -/
  | app : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {functionTerm functionTerm' :
            Term ctx (Ty.arrow domainType codomainType)}
        {argumentTerm argumentTerm' : Term ctx domainType}
        {functionStep : Step.par functionTerm functionTerm'}
        {argumentStep : Step.par argumentTerm argumentTerm'},
      Step.par.isBi functionStep → Step.par.isBi argumentStep →
      Step.par.isBi (Step.par.app functionStep argumentStep)
  /-- Non-dependent λ-body congruence is βι. -/
  | lam : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {body body' : Term (ctx.cons domainType) codomainType.weaken}
        {bodyStep : Step.par body body'},
      Step.par.isBi bodyStep →
      Step.par.isBi
        (Step.par.lam (codomainType := codomainType) bodyStep)
  /-- Dependent λ-body congruence is βι. -/
  | lamPi : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {domainType : Ty level scope}
        {codomainType : Ty level (scope + 1)}
        {body body' : Term (ctx.cons domainType) codomainType}
        {bodyStep : Step.par body body'},
      Step.par.isBi bodyStep →
      Step.par.isBi (Step.par.lamPi (domainType := domainType) bodyStep)
  /-- Dependent application congruence is βι. -/
  | appPi : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {domainType : Ty level scope}
        {codomainType : Ty level (scope + 1)}
        {functionTerm functionTerm' :
            Term ctx (Ty.piTy domainType codomainType)}
        {argumentTerm argumentTerm' : Term ctx domainType}
        {functionStep : Step.par functionTerm functionTerm'}
        {argumentStep : Step.par argumentTerm argumentTerm'},
      Step.par.isBi functionStep → Step.par.isBi argumentStep →
      Step.par.isBi (Step.par.appPi functionStep argumentStep)
  /-- Σ-pair congruence is βι. -/
  | pair : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {firstType : Ty level scope}
        {secondType : Ty level (scope + 1)}
        {firstVal firstVal' : Term ctx firstType}
        {secondVal secondVal' : Term ctx (secondType.subst0 firstType)}
        {firstStep : Step.par firstVal firstVal'}
        {secondStep : Step.par secondVal secondVal'},
      Step.par.isBi firstStep → Step.par.isBi secondStep →
      Step.par.isBi (Step.par.pair firstStep secondStep)
  /-- First-projection congruence is βι. -/
  | fst : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {firstType : Ty level scope}
        {secondType : Ty level (scope + 1)}
        {pairTerm pairTerm' : Term ctx (Ty.sigmaTy firstType secondType)}
        {pairStep : Step.par pairTerm pairTerm'},
      Step.par.isBi pairStep →
      Step.par.isBi (Step.par.fst pairStep)
  /-- Second-projection congruence is βι. -/
  | snd : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {firstType : Ty level scope}
        {secondType : Ty level (scope + 1)}
        {pairTerm pairTerm' : Term ctx (Ty.sigmaTy firstType secondType)}
        {pairStep : Step.par pairTerm pairTerm'},
      Step.par.isBi pairStep →
      Step.par.isBi (Step.par.snd pairStep)
  /-- `boolElim` three-position congruence is βι. -/
  | boolElim : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx Ty.bool}
        {thenBranch thenBranch' : Term ctx resultType}
        {elseBranch elseBranch' : Term ctx resultType}
        {scrutineeStep : Step.par scrutinee scrutinee'}
        {thenStep : Step.par thenBranch thenBranch'}
        {elseStep : Step.par elseBranch elseBranch'},
      Step.par.isBi scrutineeStep →
      Step.par.isBi thenStep →
      Step.par.isBi elseStep →
      Step.par.isBi (Step.par.boolElim scrutineeStep thenStep elseStep)
  /-- Non-dependent β-redex is βι. -/
  | betaApp : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {body body' : Term (ctx.cons domainType) codomainType.weaken}
        {arg arg' : Term ctx domainType}
        {bodyStep : Step.par body body'}
        {argStep : Step.par arg arg'},
      Step.par.isBi bodyStep → Step.par.isBi argStep →
      Step.par.isBi (Step.par.betaApp bodyStep argStep)
  /-- Dependent β-redex is βι. -/
  | betaAppPi : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {domainType : Ty level scope}
        {codomainType : Ty level (scope + 1)}
        {body body' : Term (ctx.cons domainType) codomainType}
        {arg arg' : Term ctx domainType}
        {bodyStep : Step.par body body'}
        {argStep : Step.par arg arg'},
      Step.par.isBi bodyStep → Step.par.isBi argStep →
      Step.par.isBi (Step.par.betaAppPi bodyStep argStep)
  /-- Σ first-projection β-redex is βι. -/
  | betaFstPair : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {firstType : Ty level scope}
        {secondType : Ty level (scope + 1)}
        {firstVal firstVal' : Term ctx firstType}
        {secondVal : Term ctx (secondType.subst0 firstType)}
        {firstStep : Step.par firstVal firstVal'},
      Step.par.isBi firstStep →
      Step.par.isBi (Step.par.betaFstPair (secondType := secondType)
                                          secondVal firstStep)
  /-- Σ second-projection β-redex is βι. -/
  | betaSndPair : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {firstType : Ty level scope}
        {secondType : Ty level (scope + 1)}
        {firstVal : Term ctx firstType}
        {secondVal secondVal' : Term ctx (secondType.subst0 firstType)}
        {secondStep : Step.par secondVal secondVal'},
      Step.par.isBi secondStep →
      Step.par.isBi (Step.par.betaSndPair (firstType := firstType)
                                          firstVal secondStep)
  /-- ι-rule on `boolTrue` is βι. -/
  | iotaBoolElimTrue : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope} {resultType : Ty level scope}
        {thenBranch thenBranch' : Term ctx resultType}
        (elseBranch : Term ctx resultType)
        {thenStep : Step.par thenBranch thenBranch'},
      Step.par.isBi thenStep →
      Step.par.isBi (Step.par.iotaBoolElimTrue elseBranch thenStep)
  /-- ι-rule on `boolFalse` is βι. -/
  | iotaBoolElimFalse : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope} {resultType : Ty level scope}
        (thenBranch : Term ctx resultType)
        {elseBranch elseBranch' : Term ctx resultType}
        {elseStep : Step.par elseBranch elseBranch'},
      Step.par.isBi elseStep →
      Step.par.isBi (Step.par.iotaBoolElimFalse thenBranch elseStep)
  /-- `natSucc` congruence is βι. -/
  | natSucc : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {pred pred' : Term ctx Ty.nat}
        {predStep : Step.par pred pred'},
      Step.par.isBi predStep →
      Step.par.isBi (Step.par.natSucc predStep)
  /-- `natElim` three-position congruence is βι. -/
  | natElim : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)}
        {scrutineeStep : Step.par scrutinee scrutinee'}
        {zeroStep : Step.par zeroBranch zeroBranch'}
        {succStep : Step.par succBranch succBranch'},
      Step.par.isBi scrutineeStep →
      Step.par.isBi zeroStep →
      Step.par.isBi succStep →
      Step.par.isBi (Step.par.natElim scrutineeStep zeroStep succStep)
  /-- ι-rule on `natElim` at `0` is βι. -/
  | iotaNatElimZero : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope} {resultType : Ty level scope}
        {zeroBranch zeroBranch' : Term ctx resultType}
        (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
        {zeroStep : Step.par zeroBranch zeroBranch'},
      Step.par.isBi zeroStep →
      Step.par.isBi (Step.par.iotaNatElimZero succBranch zeroStep)
  /-- `natRec` three-position congruence is βι. -/
  | natRec : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        {succBranch succBranch' : Term ctx
            (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
        {scrutineeStep : Step.par scrutinee scrutinee'}
        {zeroStep : Step.par zeroBranch zeroBranch'}
        {succStep : Step.par succBranch succBranch'},
      Step.par.isBi scrutineeStep →
      Step.par.isBi zeroStep →
      Step.par.isBi succStep →
      Step.par.isBi (Step.par.natRec scrutineeStep zeroStep succStep)
  /-- ι-rule on `natRec` at `0` is βι. -/
  | iotaNatRecZero : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope} {resultType : Ty level scope}
        {zeroBranch zeroBranch' : Term ctx resultType}
        (succBranch : Term ctx
            (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
        {zeroStep : Step.par zeroBranch zeroBranch'},
      Step.par.isBi zeroStep →
      Step.par.isBi (Step.par.iotaNatRecZero succBranch zeroStep)
  /-- ι-rule on `natRec` at `succ` is βι. -/
  | iotaNatRecSucc : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope} {resultType : Ty level scope}
        {predecessor predecessor' : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        {succBranch succBranch' : Term ctx
            (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
        {predStep : Step.par predecessor predecessor'}
        {zeroStep : Step.par zeroBranch zeroBranch'}
        {succStep : Step.par succBranch succBranch'},
      Step.par.isBi predStep →
      Step.par.isBi zeroStep →
      Step.par.isBi succStep →
      Step.par.isBi (Step.par.iotaNatRecSucc predStep zeroStep succStep)
  /-- ι-rule on `natElim` at `succ` is βι. -/
  | iotaNatElimSucc : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope} {resultType : Ty level scope}
        {predecessor predecessor' : Term ctx Ty.nat}
        (zeroBranch : Term ctx resultType)
        {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)}
        {predStep : Step.par predecessor predecessor'}
        {succStep : Step.par succBranch succBranch'},
      Step.par.isBi predStep → Step.par.isBi succStep →
      Step.par.isBi (Step.par.iotaNatElimSucc zeroBranch predStep succStep)
  /-- `listCons` two-position congruence is βι. -/
  | listCons : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {elementType : Ty level scope}
        {head head' : Term ctx elementType}
        {tail tail' : Term ctx (Ty.list elementType)}
        {headStep : Step.par head head'}
        {tailStep : Step.par tail tail'},
      Step.par.isBi headStep → Step.par.isBi tailStep →
      Step.par.isBi (Step.par.listCons headStep tailStep)
  /-- `listElim` three-position congruence is βι. -/
  | listElim : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx (Ty.list elementType)}
        {nilBranch nilBranch' : Term ctx resultType}
        {consBranch consBranch' : Term ctx
            (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))}
        {scrutineeStep : Step.par scrutinee scrutinee'}
        {nilStep : Step.par nilBranch nilBranch'}
        {consStep : Step.par consBranch consBranch'},
      Step.par.isBi scrutineeStep →
      Step.par.isBi nilStep →
      Step.par.isBi consStep →
      Step.par.isBi (Step.par.listElim scrutineeStep nilStep consStep)
  /-- ι-rule on `listElim` at `nil` is βι. -/
  | iotaListElimNil : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {nilBranch nilBranch' : Term ctx resultType}
        (consBranch : Term ctx
            (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType)))
        {nilStep : Step.par nilBranch nilBranch'},
      Step.par.isBi nilStep →
      Step.par.isBi (Step.par.iotaListElimNil
                       (elementType := elementType) consBranch nilStep)
  /-- ι-rule on `listElim` at `cons` is βι. -/
  | iotaListElimCons : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {head head' : Term ctx elementType}
        {tail tail' : Term ctx (Ty.list elementType)}
        (nilBranch : Term ctx resultType)
        {consBranch consBranch' : Term ctx
            (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))}
        {headStep : Step.par head head'}
        {tailStep : Step.par tail tail'}
        {consStep : Step.par consBranch consBranch'},
      Step.par.isBi headStep → Step.par.isBi tailStep → Step.par.isBi consStep →
      Step.par.isBi (Step.par.iotaListElimCons nilBranch headStep
                                                tailStep consStep)
  /-- `optionSome` congruence is βι. -/
  | optionSome : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {elementType : Ty level scope}
        {value value' : Term ctx elementType}
        {valueStep : Step.par value value'},
      Step.par.isBi valueStep →
      Step.par.isBi (Step.par.optionSome valueStep)
  /-- `optionMatch` three-position congruence is βι. -/
  | optionMatch : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx (Ty.option elementType)}
        {noneBranch noneBranch' : Term ctx resultType}
        {someBranch someBranch' : Term ctx (Ty.arrow elementType resultType)}
        {scrutineeStep : Step.par scrutinee scrutinee'}
        {noneStep : Step.par noneBranch noneBranch'}
        {someStep : Step.par someBranch someBranch'},
      Step.par.isBi scrutineeStep →
      Step.par.isBi noneStep →
      Step.par.isBi someStep →
      Step.par.isBi (Step.par.optionMatch scrutineeStep noneStep someStep)
  /-- ι-rule on `optionMatch` at `none` is βι. -/
  | iotaOptionMatchNone : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {noneBranch noneBranch' : Term ctx resultType}
        (someBranch : Term ctx (Ty.arrow elementType resultType))
        {noneStep : Step.par noneBranch noneBranch'},
      Step.par.isBi noneStep →
      Step.par.isBi (Step.par.iotaOptionMatchNone
                       (elementType := elementType) someBranch noneStep)
  /-- ι-rule on `optionMatch` at `some` is βι. -/
  | iotaOptionMatchSome : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {value value' : Term ctx elementType}
        (noneBranch : Term ctx resultType)
        {someBranch someBranch' : Term ctx (Ty.arrow elementType resultType)}
        {valueStep : Step.par value value'}
        {someStep : Step.par someBranch someBranch'},
      Step.par.isBi valueStep → Step.par.isBi someStep →
      Step.par.isBi (Step.par.iotaOptionMatchSome noneBranch valueStep someStep)
  /-- `eitherInl` congruence is βι. -/
  | eitherInl : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {leftType rightType : Ty level scope}
        {value value' : Term ctx leftType}
        {valueStep : Step.par value value'},
      Step.par.isBi valueStep →
      Step.par.isBi (Step.par.eitherInl (rightType := rightType) valueStep)
  /-- `eitherInr` congruence is βι. -/
  | eitherInr : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {leftType rightType : Ty level scope}
        {value value' : Term ctx rightType}
        {valueStep : Step.par value value'},
      Step.par.isBi valueStep →
      Step.par.isBi (Step.par.eitherInr (leftType := leftType) valueStep)
  /-- `eitherMatch` three-position congruence is βι. -/
  | eitherMatch : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {scrutinee scrutinee' : Term ctx (Ty.either leftType rightType)}
        {leftBranch leftBranch' : Term ctx (Ty.arrow leftType resultType)}
        {rightBranch rightBranch' : Term ctx (Ty.arrow rightType resultType)}
        {scrutineeStep : Step.par scrutinee scrutinee'}
        {leftStep : Step.par leftBranch leftBranch'}
        {rightStep : Step.par rightBranch rightBranch'},
      Step.par.isBi scrutineeStep →
      Step.par.isBi leftStep →
      Step.par.isBi rightStep →
      Step.par.isBi (Step.par.eitherMatch scrutineeStep leftStep rightStep)
  /-- ι-rule on `eitherMatch` at `inl` is βι. -/
  | iotaEitherMatchInl : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {value value' : Term ctx leftType}
        {leftBranch leftBranch' : Term ctx (Ty.arrow leftType resultType)}
        (rightBranch : Term ctx (Ty.arrow rightType resultType))
        {valueStep : Step.par value value'}
        {leftStep : Step.par leftBranch leftBranch'},
      Step.par.isBi valueStep → Step.par.isBi leftStep →
      Step.par.isBi (Step.par.iotaEitherMatchInl rightBranch valueStep leftStep)
  /-- ι-rule on `eitherMatch` at `inr` is βι. -/
  | iotaEitherMatchInr : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {value value' : Term ctx rightType}
        (leftBranch : Term ctx (Ty.arrow leftType resultType))
        {rightBranch rightBranch' : Term ctx (Ty.arrow rightType resultType)}
        {valueStep : Step.par value value'}
        {rightStep : Step.par rightBranch rightBranch'},
      Step.par.isBi valueStep → Step.par.isBi rightStep →
      Step.par.isBi (Step.par.iotaEitherMatchInr leftBranch valueStep rightStep)
  /-- `idJ` two-position congruence is βι. -/
  | idJ : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
        {resultType : Ty level scope}
        {baseCase baseCase' : Term ctx resultType}
        {witness witness' : Term ctx (Ty.id carrier leftEnd rightEnd)}
        {baseStep : Step.par baseCase baseCase'}
        {witnessStep : Step.par witness witness'},
      Step.par.isBi baseStep → Step.par.isBi witnessStep →
      Step.par.isBi (Step.par.idJ baseStep witnessStep)
  /-- ι-rule on `idJ` at `refl` is βι. -/
  | iotaIdJRefl : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {carrier : Ty level scope} {endpoint : RawTerm scope}
        {resultType : Ty level scope}
        {baseCase baseCase' : Term ctx resultType}
        {baseStep : Step.par baseCase baseCase'},
      Step.par.isBi baseStep →
      Step.par.isBi (Step.par.iotaIdJRefl
                       (carrier := carrier) (endpoint := endpoint) baseStep)
  /-- Deep non-dependent β-redex is βι. -/
  | betaAppDeep : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {functionTerm : Term ctx (Ty.arrow domainType codomainType)}
        {body : Term (ctx.cons domainType) codomainType.weaken}
        {arg arg' : Term ctx domainType}
        {functionStep : Step.par functionTerm
            (Term.lam (codomainType := codomainType) body)}
        {argStep : Step.par arg arg'},
      Step.par.isBi functionStep → Step.par.isBi argStep →
      Step.par.isBi (Step.par.betaAppDeep functionStep argStep)
  /-- Deep dependent β-redex is βι. -/
  | betaAppPiDeep : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {domainType : Ty level scope}
        {codomainType : Ty level (scope + 1)}
        {functionTerm : Term ctx (Ty.piTy domainType codomainType)}
        {body : Term (ctx.cons domainType) codomainType}
        {arg arg' : Term ctx domainType}
        {functionStep : Step.par functionTerm
            (Term.lamPi (domainType := domainType) body)}
        {argStep : Step.par arg arg'},
      Step.par.isBi functionStep → Step.par.isBi argStep →
      Step.par.isBi (Step.par.betaAppPiDeep functionStep argStep)
  /-- Deep Σ first-projection β-redex is βι. -/
  | betaFstPairDeep : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope}
        {firstType : Ty level scope}
        {secondType : Ty level (scope + 1)}
        {pairTerm : Term ctx (Ty.sigmaTy firstType secondType)}
        {firstVal : Term ctx firstType}
        {secondVal : Term ctx (secondType.subst0 firstType)}
        {pairStep : Step.par pairTerm
            (Term.pair (firstType := firstType) (secondType := secondType)
                       firstVal secondVal)},
      Step.par.isBi pairStep →
      Step.par.isBi (Step.par.betaFstPairDeep pairStep)
  /-- Deep Σ second-projection β-redex is βι. -/
  | betaSndPairDeep : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope}
        {firstType : Ty level scope}
        {secondType : Ty level (scope + 1)}
        {pairTerm : Term ctx (Ty.sigmaTy firstType secondType)}
        {firstVal : Term ctx firstType}
        {secondVal : Term ctx (secondType.subst0 firstType)}
        {pairStep : Step.par pairTerm
            (Term.pair (firstType := firstType) (secondType := secondType)
                       firstVal secondVal)},
      Step.par.isBi pairStep →
      Step.par.isBi (Step.par.betaSndPairDeep pairStep)
  /-- Deep ι-rule on `boolElim` at `boolTrue` is βι. -/
  | iotaBoolElimTrueDeep : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope} {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.bool}
        {thenBranch thenBranch' : Term ctx resultType}
        (elseBranch : Term ctx resultType)
        {scrutineeStep : Step.par scrutinee Term.boolTrue}
        {thenStep : Step.par thenBranch thenBranch'},
      Step.par.isBi scrutineeStep → Step.par.isBi thenStep →
      Step.par.isBi (Step.par.iotaBoolElimTrueDeep elseBranch scrutineeStep
                                                    thenStep)
  /-- Deep ι-rule on `boolElim` at `boolFalse` is βι. -/
  | iotaBoolElimFalseDeep : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope} {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.bool}
        (thenBranch : Term ctx resultType)
        {elseBranch elseBranch' : Term ctx resultType}
        {scrutineeStep : Step.par scrutinee Term.boolFalse}
        {elseStep : Step.par elseBranch elseBranch'},
      Step.par.isBi scrutineeStep → Step.par.isBi elseStep →
      Step.par.isBi (Step.par.iotaBoolElimFalseDeep thenBranch scrutineeStep
                                                     elseStep)
  /-- Deep ι-rule on `natElim` at `natZero` is βι. -/
  | iotaNatElimZeroDeep : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope} {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
        {scrutineeStep : Step.par scrutinee Term.natZero}
        {zeroStep : Step.par zeroBranch zeroBranch'},
      Step.par.isBi scrutineeStep → Step.par.isBi zeroStep →
      Step.par.isBi (Step.par.iotaNatElimZeroDeep succBranch scrutineeStep
                                                   zeroStep)
  /-- Deep ι-rule on `natElim` at `natSucc` is βι. -/
  | iotaNatElimSuccDeep : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope} {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.nat}
        {predecessor : Term ctx Ty.nat}
        (zeroBranch : Term ctx resultType)
        {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)}
        {scrutineeStep : Step.par scrutinee (Term.natSucc predecessor)}
        {succStep : Step.par succBranch succBranch'},
      Step.par.isBi scrutineeStep → Step.par.isBi succStep →
      Step.par.isBi (Step.par.iotaNatElimSuccDeep zeroBranch scrutineeStep
                                                   succStep)
  /-- Deep ι-rule on `natRec` at `natZero` is βι. -/
  | iotaNatRecZeroDeep : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope} {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        (succBranch : Term ctx
            (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
        {scrutineeStep : Step.par scrutinee Term.natZero}
        {zeroStep : Step.par zeroBranch zeroBranch'},
      Step.par.isBi scrutineeStep → Step.par.isBi zeroStep →
      Step.par.isBi (Step.par.iotaNatRecZeroDeep succBranch scrutineeStep
                                                  zeroStep)
  /-- Deep ι-rule on `natRec` at `natSucc` is βι. -/
  | iotaNatRecSuccDeep : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope} {resultType : Ty level scope}
        {scrutinee : Term ctx Ty.nat}
        {predecessor : Term ctx Ty.nat}
        {zeroBranch zeroBranch' : Term ctx resultType}
        {succBranch succBranch' : Term ctx
            (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
        {scrutineeStep : Step.par scrutinee (Term.natSucc predecessor)}
        {zeroStep : Step.par zeroBranch zeroBranch'}
        {succStep : Step.par succBranch succBranch'},
      Step.par.isBi scrutineeStep →
      Step.par.isBi zeroStep →
      Step.par.isBi succStep →
      Step.par.isBi (Step.par.iotaNatRecSuccDeep scrutineeStep zeroStep succStep)
  /-- Deep ι-rule on `listElim` at `listNil` is βι. -/
  | iotaListElimNilDeep : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.list elementType)}
        {nilBranch nilBranch' : Term ctx resultType}
        (consBranch : Term ctx
            (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType)))
        {scrutineeStep : Step.par scrutinee Term.listNil}
        {nilStep : Step.par nilBranch nilBranch'},
      Step.par.isBi scrutineeStep → Step.par.isBi nilStep →
      Step.par.isBi (Step.par.iotaListElimNilDeep consBranch scrutineeStep
                                                   nilStep)
  /-- Deep ι-rule on `listElim` at `listCons` is βι. -/
  | iotaListElimConsDeep : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.list elementType)}
        {head : Term ctx elementType}
        {tail : Term ctx (Ty.list elementType)}
        (nilBranch : Term ctx resultType)
        {consBranch consBranch' : Term ctx
            (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))}
        {scrutineeStep : Step.par scrutinee (Term.listCons head tail)}
        {consStep : Step.par consBranch consBranch'},
      Step.par.isBi scrutineeStep → Step.par.isBi consStep →
      Step.par.isBi (Step.par.iotaListElimConsDeep nilBranch scrutineeStep
                                                    consStep)
  /-- Deep ι-rule on `optionMatch` at `optionNone` is βι. -/
  | iotaOptionMatchNoneDeep : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.option elementType)}
        {noneBranch noneBranch' : Term ctx resultType}
        (someBranch : Term ctx (Ty.arrow elementType resultType))
        {scrutineeStep : Step.par scrutinee Term.optionNone}
        {noneStep : Step.par noneBranch noneBranch'},
      Step.par.isBi scrutineeStep → Step.par.isBi noneStep →
      Step.par.isBi (Step.par.iotaOptionMatchNoneDeep someBranch scrutineeStep
                                                       noneStep)
  /-- Deep ι-rule on `optionMatch` at `optionSome` is βι. -/
  | iotaOptionMatchSomeDeep : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope}
        {elementType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.option elementType)}
        {value : Term ctx elementType}
        (noneBranch : Term ctx resultType)
        {someBranch someBranch' :
            Term ctx (Ty.arrow elementType resultType)}
        {scrutineeStep : Step.par scrutinee (Term.optionSome value)}
        {someStep : Step.par someBranch someBranch'},
      Step.par.isBi scrutineeStep → Step.par.isBi someStep →
      Step.par.isBi (Step.par.iotaOptionMatchSomeDeep noneBranch scrutineeStep
                                                       someStep)
  /-- Deep ι-rule on `eitherMatch` at `eitherInl` is βι. -/
  | iotaEitherMatchInlDeep : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.either leftType rightType)}
        {value : Term ctx leftType}
        {leftBranch leftBranch' :
            Term ctx (Ty.arrow leftType resultType)}
        (rightBranch : Term ctx (Ty.arrow rightType resultType))
        {scrutineeStep : Step.par scrutinee
            (Term.eitherInl (rightType := rightType) value)}
        {leftStep : Step.par leftBranch leftBranch'},
      Step.par.isBi scrutineeStep → Step.par.isBi leftStep →
      Step.par.isBi (Step.par.iotaEitherMatchInlDeep rightBranch scrutineeStep
                                                      leftStep)
  /-- Deep ι-rule on `eitherMatch` at `eitherInr` is βι. -/
  | iotaEitherMatchInrDeep : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope}
        {leftType rightType resultType : Ty level scope}
        {scrutinee : Term ctx (Ty.either leftType rightType)}
        {value : Term ctx rightType}
        (leftBranch : Term ctx (Ty.arrow leftType resultType))
        {rightBranch rightBranch' :
            Term ctx (Ty.arrow rightType resultType)}
        {scrutineeStep : Step.par scrutinee
            (Term.eitherInr (leftType := leftType) value)}
        {rightStep : Step.par rightBranch rightBranch'},
      Step.par.isBi scrutineeStep → Step.par.isBi rightStep →
      Step.par.isBi (Step.par.iotaEitherMatchInrDeep leftBranch scrutineeStep
                                                      rightStep)
  /-- Deep ι-rule on `idJ` at `refl` is βι. -/
  | iotaIdJReflDeep : ∀ {mode : Mode} {level scope : Nat}
        {ctx : Ctx mode level scope}
        {carrier : Ty level scope} {endpoint : RawTerm scope}
        {resultType : Ty level scope}
        {baseCase baseCase' : Term ctx resultType}
        {witness : Term ctx (Ty.id carrier endpoint endpoint)}
        {witnessStep : Step.par witness
            (Term.refl (carrier := carrier) endpoint)}
        {baseStep : Step.par baseCase baseCase'},
      Step.par.isBi witnessStep → Step.par.isBi baseStep →
      Step.par.isBi (Step.par.iotaIdJReflDeep witnessStep baseStep)

/-! ## `Step.parStar.isBi` — chain-level βι predicate.

Mirrors `Step.par.isBi` at the `Step.parStar` level: a chain is βι
iff every step in it is βι.  Required so target-direction
inversions on lam/pair (which fail at plain `Step.parStar` because
of η-rules) hold under isBi-gating.

Inductive structure mirrors `Step.parStar`: `refl` is trivially βι,
`trans` requires the head step's isBi-ness AND the rest chain's. -/
inductive Step.parStar.isBi :
    ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
      {termType : Ty level scope}
      {sourceTerm targetTerm : Term ctx termType},
    Step.parStar sourceTerm targetTerm → Prop
  /-- The empty chain is βι. -/
  | refl : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {termType : Ty level scope} (term : Term ctx termType),
      Step.parStar.isBi (Step.parStar.refl term)
  /-- A cons chain is βι if its head step is βι and the rest is βι. -/
  | trans : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {termType : Ty level scope}
        {firstTerm secondTerm thirdTerm : Term ctx termType}
        {firstStep : Step.par firstTerm secondTerm}
        {restChain : Step.parStar secondTerm thirdTerm},
      Step.par.isBi firstStep →
      Step.parStar.isBi restChain →
      Step.parStar.isBi (Step.parStar.trans firstStep restChain)

/-- Lift a single βι step to a βι chain. -/
theorem Step.par.toParStar_isBi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    {parallelStep : Step.par sourceTerm targetTerm}
    (stepBi : Step.par.isBi parallelStep) :
    Step.parStar.isBi (Step.par.toParStar parallelStep) :=
  Step.parStar.isBi.trans stepBi (Step.parStar.isBi.refl targetTerm)

/-! ## End-to-end validation: cd_lemma_star prototype.

A miniature cd_lemma_star proven only for the `refl` and `lam`
cases of Step.par, gated by `Step.par.isBi`.  Proves the
end-to-end shape works:
  (a) the IH on a recursive call is properly extracted from
      the isBi hypothesis,
  (b) the `parStar` congruence rules from `ParSubst.lean`
      lift the IH conclusion through the enclosing constructor,
  (c) `cd_dominates` closes the `refl` case.

This validates that once all 54 isBi constructors land, the full
cd_lemma_star will compose.  η constructors don't appear — the
prototype's `cases bi` will fall through any added η constructor
case vacuously. -/
private theorem Step.par.cd_lemma_star_lam_only_proto
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body body' : Term (ctx.cons domainType) codomainType.weaken}
    (bodyStep : Step.par body body')
    (_bodyBi : Step.par.isBi bodyStep)
    (bodyIH : Step.parStar body' (Term.cd body)) :
    Step.parStar (Term.lam (codomainType := codomainType) body')
                 (Term.cd (Term.lam (codomainType := codomainType) body)) := by
  -- Term.cd reduces (Term.lam body) to (Term.lam (Term.cd body))
  -- Goal becomes: parStar (Term.lam body') (Term.lam (Term.cd body))
  -- which follows from bodyIH via lam_cong.
  simp only [Term.cd]
  exact Step.parStar.lam_cong bodyIH

private theorem Step.par.cd_lemma_star_refl_proto
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    (term : Term ctx termType) :
    Step.parStar term (Term.cd term) :=
  -- cd_dominates gives Step.par term (Term.cd term); lift to parStar.
  Step.par.toParStar (Step.par.cd_dominates term)

end LeanFX.Syntax

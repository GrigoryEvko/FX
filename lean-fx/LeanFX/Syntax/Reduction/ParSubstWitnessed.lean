import LeanFX.Syntax.Reduction.ParCompatibleIsBi
import LeanFX.Syntax.Reduction.ParSubstPointwise
import LeanFX.Syntax.Reduction.ParSubst

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! # Witnessed pointwise + joint substitution lemmas.

The parWithBi-valued versions of:
* `Term.subst_par_pointwise` — fix term, vary substituents pointwise
* `TermSubst.par_lift` — lift pointwise witness through binder
* `TermSubst.singleton_par_pointwise` — singleton pointwise lift
* `Step.par.subst_par_isBi` — joint subst (term varies along isBi step)
* `Step.par.subst0_par_isBi` — singleton joint subst

Each takes `Step.parWithBi` arguments (paired Step.par + Step.par.isBi)
and returns `Step.parWithBi`.

These power the 4 β shallow cases of `Step.par.cd_monotone` for typed
Church-Rosser (W8.3 / #885 / #1167).  Specifically, `subst0_par_witnessed`
produces a single par+isBi step from `cd_dominates_with_isBi` of body
and arg, which `cd_lemma_star_with_bi` then lifts to a parStarWithBi
chain — closing Step B of the strategy. -/

/-- Bridge: `Step.par.rename_compatible` preserves `Step.par.isBi`.
Derived from the witnessed version by extracting the isBi piece. -/
theorem Step.par.rename_compatible_isBi_helper
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType}
    {parallelStep : Step.par beforeTerm afterTerm}
    (stepBi : Step.par.isBi parallelStep) :
    Step.par.isBi (Step.par.rename_compatible termRenaming parallelStep) :=
  (Step.par.rename_compatible_witnessed termRenaming stepBi).toIsBi

/-- Lift `Step.par.isBi` pointwise through binder.  Mirror of
`TermSubst.par_lift` at the isBi level. -/
theorem TermSubst.par_lift_isBi_witness
    {mode : Mode} {scope sourceScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level sourceScope}
    {typeSubstitution : Subst level scope sourceScope}
    {firstSubstitution secondSubstitution :
      TermSubst sourceCtx targetCtx typeSubstitution}
    (related : ∀ position,
      Step.par (firstSubstitution position) (secondSubstitution position))
    (relatedBi : ∀ position, Step.par.isBi (related position))
    (newType : Ty level scope) :
    ∀ position,
      Step.par.isBi (TermSubst.par_lift related newType position) := by
  intro position
  match position with
  | ⟨0, _⟩ =>
      exact Step.par.isBi.castBoth_eq
        (Ty.subst_weaken_commute newType typeSubstitution).symm
        (Step.par.isBi.refl _)
  | ⟨index + 1, isWithinBound⟩ =>
      exact Step.par.isBi.castBoth_eq
        (Ty.subst_weaken_commute
          (varType sourceCtx ⟨index, Nat.lt_of_succ_lt_succ isWithinBound⟩)
          typeSubstitution).symm
        (Step.par.rename_compatible_isBi_helper
          (TermRenaming.weaken targetCtx (newType.subst typeSubstitution))
          (relatedBi ⟨index, Nat.lt_of_succ_lt_succ isWithinBound⟩))

/-- isBi side of `Term.subst_par_pointwise`. -/
theorem Term.subst_par_pointwise_isBi_witness
    {mode : Mode} {scope sourceScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level sourceScope}
    {typeSubstitution : Subst level scope sourceScope}
    {firstSubstitution secondSubstitution :
      TermSubst sourceCtx targetCtx typeSubstitution}
    (related : ∀ position,
      Step.par (firstSubstitution position) (secondSubstitution position))
    (relatedBi : ∀ position, Step.par.isBi (related position)) :
    {termType : Ty level scope} → (term : Term sourceCtx termType) →
      Step.par.isBi (Term.subst_par_pointwise related term)
  | _, .var position => relatedBi position
  | _, .unit => Step.par.isBi.refl _
  | _, .lam (codomainType := codomainType) body =>
      Step.par.isBi.lam
        (Step.par.isBi.castBoth_eq
          (Ty.subst_weaken_commute codomainType typeSubstitution)
          (Term.subst_par_pointwise_isBi_witness
            (TermSubst.par_lift related _)
            (TermSubst.par_lift_isBi_witness related relatedBi _)
            body))
  | _, .app function argument =>
      Step.par.isBi.app
        (Term.subst_par_pointwise_isBi_witness related relatedBi function)
        (Term.subst_par_pointwise_isBi_witness related relatedBi argument)
  | _, .lamPi body =>
      Step.par.isBi.lamPi
        (Term.subst_par_pointwise_isBi_witness
          (TermSubst.par_lift related _)
          (TermSubst.par_lift_isBi_witness related relatedBi _)
          body)
  | _, .appPi (domainType := domainType) (codomainType := codomainType)
        resultEq function argument => by
      -- W9.B1.1 — equation-bearing appPi.  Cases on resultEq normalises shape.
      cases resultEq
      simp only [Term.subst]
      exact Step.par.isBi.castBoth_eq
        (Ty.subst0_subst_commute codomainType domainType typeSubstitution).symm
        (Step.par.isBi.appPi
          (Term.subst_par_pointwise_isBi_witness related relatedBi function)
          (Term.subst_par_pointwise_isBi_witness related relatedBi argument))
  | _, .pair (firstType := firstType) (secondType := secondType)
        firstVal secondVal =>
      Step.par.isBi.pair
        (Term.subst_par_pointwise_isBi_witness related relatedBi firstVal)
        (Step.par.isBi.castBoth_eq
          (Ty.subst0_subst_commute secondType firstType typeSubstitution)
          (Term.subst_par_pointwise_isBi_witness related relatedBi secondVal))
  | _, .fst pairTerm =>
      Step.par.isBi.fst
        (Term.subst_par_pointwise_isBi_witness related relatedBi pairTerm)
  | _, .snd (firstType := firstType) (secondType := secondType)
        pairTerm resultEq => by
      -- W9.B1.2 — equation-bearing snd.  Cases on resultEq normalises shape.
      cases resultEq
      simp only [Term.subst]
      exact Step.par.isBi.castBoth_eq
        (Ty.subst0_subst_commute secondType firstType typeSubstitution).symm
        (Step.par.isBi.snd
          (Term.subst_par_pointwise_isBi_witness related relatedBi pairTerm))
  | _, .boolTrue => Step.par.isBi.refl _
  | _, .boolFalse => Step.par.isBi.refl _
  | _, .boolElim scrutinee thenBranch elseBranch =>
      Step.par.isBi.boolElim
        (Term.subst_par_pointwise_isBi_witness related relatedBi scrutinee)
        (Term.subst_par_pointwise_isBi_witness related relatedBi thenBranch)
        (Term.subst_par_pointwise_isBi_witness related relatedBi elseBranch)
  | _, .natZero => Step.par.isBi.refl _
  | _, .natSucc predecessor =>
      Step.par.isBi.natSucc
        (Term.subst_par_pointwise_isBi_witness related relatedBi predecessor)
  | _, .natElim scrutinee zeroBranch succBranch =>
      Step.par.isBi.natElim
        (Term.subst_par_pointwise_isBi_witness related relatedBi scrutinee)
        (Term.subst_par_pointwise_isBi_witness related relatedBi zeroBranch)
        (Term.subst_par_pointwise_isBi_witness related relatedBi succBranch)
  | _, .natRec scrutinee zeroBranch succBranch =>
      Step.par.isBi.natRec
        (Term.subst_par_pointwise_isBi_witness related relatedBi scrutinee)
        (Term.subst_par_pointwise_isBi_witness related relatedBi zeroBranch)
        (Term.subst_par_pointwise_isBi_witness related relatedBi succBranch)
  | _, .listNil => Step.par.isBi.refl _
  | _, .listCons head tail =>
      Step.par.isBi.listCons
        (Term.subst_par_pointwise_isBi_witness related relatedBi head)
        (Term.subst_par_pointwise_isBi_witness related relatedBi tail)
  | _, .listElim scrutinee nilBranch consBranch =>
      Step.par.isBi.listElim
        (Term.subst_par_pointwise_isBi_witness related relatedBi scrutinee)
        (Term.subst_par_pointwise_isBi_witness related relatedBi nilBranch)
        (Term.subst_par_pointwise_isBi_witness related relatedBi consBranch)
  | _, .optionNone => Step.par.isBi.refl _
  | _, .optionSome value =>
      Step.par.isBi.optionSome
        (Term.subst_par_pointwise_isBi_witness related relatedBi value)
  | _, .optionMatch scrutinee noneBranch someBranch =>
      Step.par.isBi.optionMatch
        (Term.subst_par_pointwise_isBi_witness related relatedBi scrutinee)
        (Term.subst_par_pointwise_isBi_witness related relatedBi noneBranch)
        (Term.subst_par_pointwise_isBi_witness related relatedBi someBranch)
  | _, .eitherInl value =>
      Step.par.isBi.eitherInl
        (Term.subst_par_pointwise_isBi_witness related relatedBi value)
  | _, .eitherInr value =>
      Step.par.isBi.eitherInr
        (Term.subst_par_pointwise_isBi_witness related relatedBi value)
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      Step.par.isBi.eitherMatch
        (Term.subst_par_pointwise_isBi_witness related relatedBi scrutinee)
        (Term.subst_par_pointwise_isBi_witness related relatedBi leftBranch)
        (Term.subst_par_pointwise_isBi_witness related relatedBi rightBranch)
  | _, .refl _ => Step.par.isBi.refl _
  | _, .idJ baseCase witness =>
      Step.par.isBi.idJ
        (Term.subst_par_pointwise_isBi_witness related relatedBi baseCase)
        (Term.subst_par_pointwise_isBi_witness related relatedBi witness)

/-- Witnessed pointwise lift: with pointwise parWithBi-related
substituents, applying both yields a parWithBi-related result on a
fixed term. -/
theorem Term.subst_par_pointwise_witnessed
    {mode : Mode} {scope sourceScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level sourceScope}
    {typeSubstitution : Subst level scope sourceScope}
    {firstSubstitution secondSubstitution :
      TermSubst sourceCtx targetCtx typeSubstitution}
    (relatedWitness : ∀ position,
      Step.parWithBi (firstSubstitution position) (secondSubstitution position))
    {termType : Ty level scope} (term : Term sourceCtx termType) :
    Step.parWithBi
      (Term.subst firstSubstitution term)
      (Term.subst secondSubstitution term) :=
  Step.parWithBi.mk
    (Term.subst_par_pointwise (fun position => (relatedWitness position).toStep) term)
    (Term.subst_par_pointwise_isBi_witness
      (fun position => (relatedWitness position).toStep)
      (fun position => (relatedWitness position).toIsBi)
      term)

/-- Witnessed lift through binder. -/
theorem TermSubst.par_lift_witnessed
    {mode : Mode} {scope sourceScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level sourceScope}
    {typeSubstitution : Subst level scope sourceScope}
    {firstSubstitution secondSubstitution :
      TermSubst sourceCtx targetCtx typeSubstitution}
    (relatedWitness : ∀ position,
      Step.parWithBi (firstSubstitution position) (secondSubstitution position))
    (newType : Ty level scope) :
    ∀ position,
      Step.parWithBi
        ((firstSubstitution.lift newType) position)
        ((secondSubstitution.lift newType) position) := by
  intro position
  exact Step.parWithBi.mk
    (TermSubst.par_lift (fun pos => (relatedWitness pos).toStep) newType position)
    (TermSubst.par_lift_isBi_witness
      (fun pos => (relatedWitness pos).toStep)
      (fun pos => (relatedWitness pos).toIsBi)
      newType position)

/-- isBi side of `TermSubst.singleton_par_pointwise`. -/
theorem TermSubst.singleton_par_isBi_witness
    {mode : Mode} {scope : Nat} {sourceCtx : Ctx mode level scope}
    {argumentType : Ty level scope}
    {firstArgument secondArgument : Term sourceCtx argumentType}
    {argumentStep : Step.par firstArgument secondArgument}
    (argumentBi : Step.par.isBi argumentStep) :
    ∀ position,
      Step.par.isBi (TermSubst.singleton_par_pointwise argumentStep position) := by
  intro position
  match position with
  | ⟨0, _⟩ =>
      exact Step.par.isBi.castBoth_eq
        (Ty.weaken_subst_singleton argumentType argumentType).symm
        argumentBi
  | ⟨index + 1, isWithinBound⟩ =>
      exact Step.par.isBi.castBoth_eq
        (Ty.weaken_subst_singleton
          (varType sourceCtx ⟨index, Nat.lt_of_succ_lt_succ isWithinBound⟩)
          argumentType).symm
        (Step.par.isBi.refl _)

/-- Witnessed singleton lift. -/
theorem TermSubst.singleton_par_witnessed
    {mode : Mode} {scope : Nat} {sourceCtx : Ctx mode level scope}
    {argumentType : Ty level scope}
    {firstArgument secondArgument : Term sourceCtx argumentType}
    (argumentWitness : Step.parWithBi firstArgument secondArgument) :
    ∀ position,
      Step.parWithBi
        ((TermSubst.singleton firstArgument) position)
        ((TermSubst.singleton secondArgument) position) := by
  intro position
  exact Step.parWithBi.mk
    (TermSubst.singleton_par_pointwise argumentWitness.toStep position)
    (TermSubst.singleton_par_isBi_witness argumentWitness.toIsBi position)

/-- **Witnessed joint substitution lemma.**  Given a βι-witnessed
parallel step on the term and a pointwise parWithBi witness on
substitutents (varying `firstSub` to `secondSub`), produces a joint
parWithBi step substituting BEFORE term with FIRST substitution and
AFTER term with SECOND.

Proof: induction on `stepBi`, building parWithBi.mk inline at each
case (mirroring `Step.par.subst_par_isBi`'s case structure with both
the par-step and the isBi-witness constructed via the same
let-bindings). -/
theorem Step.par.subst_par_witnessed
    {mode : Mode} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    {firstTermSubstitution secondTermSubstitution :
      TermSubst sourceCtx targetCtx typeSubstitution}
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType}
    {parallelStep : Step.par beforeTerm afterTerm}
    (stepBi : Step.par.isBi parallelStep)
    (pointwiseWitness : ∀ position,
      Step.parWithBi
        (firstTermSubstitution position)
        (secondTermSubstitution position)) :
    Step.parWithBi
      (Term.subst firstTermSubstitution beforeTerm)
      (Term.subst secondTermSubstitution afterTerm) := by
  induction stepBi generalizing targetScope targetCtx with
  | refl term =>
      exact Term.subst_par_pointwise_witnessed pointwiseWitness term
  | app _funBi _argBi funIH argIH =>
      let funWB := funIH pointwiseWitness
      let argWB := argIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.app funWB.toStep argWB.toStep)
        (Step.par.isBi.app funWB.toIsBi argWB.toIsBi)
  | lam _bodyBi bodyIH =>
      rename_i domainType codomainType _ _ _
      let bodyWB := bodyIH (TermSubst.par_lift_witnessed pointwiseWitness domainType)
      exact Step.parWithBi.mk
        (Step.par.lam
          (Step.par.castBoth (Ty.subst_weaken_commute codomainType typeSubstitution)
            bodyWB.toStep))
        (Step.par.isBi.lam
          (Step.par.isBi.castBoth_eq
            (Ty.subst_weaken_commute codomainType typeSubstitution)
            bodyWB.toIsBi))
  | lamPi _bodyBi bodyIH =>
      rename_i domainType _ _ _ _
      let bodyWB := bodyIH (TermSubst.par_lift_witnessed pointwiseWitness domainType)
      exact Step.parWithBi.mk
        (Step.par.lamPi bodyWB.toStep)
        (Step.par.isBi.lamPi bodyWB.toIsBi)
  | appPi _funBi _argBi funIH argIH =>
      rename_i domainType codomainType _ _ _ _ _ _
      let funWB := funIH pointwiseWitness
      let argWB := argIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.castBoth
          (Ty.subst0_subst_commute codomainType domainType typeSubstitution).symm
          (Step.par.appPi funWB.toStep argWB.toStep))
        (Step.par.isBi.castBoth_eq
          (Ty.subst0_subst_commute codomainType domainType typeSubstitution).symm
          (Step.par.isBi.appPi funWB.toIsBi argWB.toIsBi))
  | pair _firstBi _secondBi firstIH secondIH =>
      rename_i firstType secondType _ _ _ _ _ _
      let firstWB := firstIH pointwiseWitness
      let secondWB := secondIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.pair
          firstWB.toStep
          (Step.par.castBoth
            (Ty.subst0_subst_commute secondType firstType typeSubstitution)
            secondWB.toStep))
        (Step.par.isBi.pair
          firstWB.toIsBi
          (Step.par.isBi.castBoth_eq
            (Ty.subst0_subst_commute secondType firstType typeSubstitution)
            secondWB.toIsBi))
  | fst _pairBi pairIH =>
      let pairWB := pairIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.fst pairWB.toStep)
        (Step.par.isBi.fst pairWB.toIsBi)
  | snd _pairBi pairIH =>
      rename_i firstType secondType _ _ _
      let pairWB := pairIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.castBoth
          (Ty.subst0_subst_commute secondType firstType typeSubstitution).symm
          (Step.par.snd pairWB.toStep))
        (Step.par.isBi.castBoth_eq
          (Ty.subst0_subst_commute secondType firstType typeSubstitution).symm
          (Step.par.isBi.snd pairWB.toIsBi))
  | boolElim _scrutBi _thenBi _elseBi scrutIH thenIH elseIH =>
      let scrutWB := scrutIH pointwiseWitness
      let thenWB := thenIH pointwiseWitness
      let elseWB := elseIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.boolElim scrutWB.toStep thenWB.toStep elseWB.toStep)
        (Step.par.isBi.boolElim scrutWB.toIsBi thenWB.toIsBi elseWB.toIsBi)
  | natSucc _predBi predIH =>
      let predWB := predIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.natSucc predWB.toStep)
        (Step.par.isBi.natSucc predWB.toIsBi)
  | natElim _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      let scrutWB := scrutIH pointwiseWitness
      let zeroWB := zeroIH pointwiseWitness
      let succWB := succIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.natElim scrutWB.toStep zeroWB.toStep succWB.toStep)
        (Step.par.isBi.natElim scrutWB.toIsBi zeroWB.toIsBi succWB.toIsBi)
  | natRec _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      let scrutWB := scrutIH pointwiseWitness
      let zeroWB := zeroIH pointwiseWitness
      let succWB := succIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.natRec scrutWB.toStep zeroWB.toStep succWB.toStep)
        (Step.par.isBi.natRec scrutWB.toIsBi zeroWB.toIsBi succWB.toIsBi)
  | listCons _headBi _tailBi headIH tailIH =>
      let headWB := headIH pointwiseWitness
      let tailWB := tailIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.listCons headWB.toStep tailWB.toStep)
        (Step.par.isBi.listCons headWB.toIsBi tailWB.toIsBi)
  | listElim _scrutBi _nilBi _consBi scrutIH nilIH consIH =>
      let scrutWB := scrutIH pointwiseWitness
      let nilWB := nilIH pointwiseWitness
      let consWB := consIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.listElim scrutWB.toStep nilWB.toStep consWB.toStep)
        (Step.par.isBi.listElim scrutWB.toIsBi nilWB.toIsBi consWB.toIsBi)
  | optionSome _valueBi valueIH =>
      let valueWB := valueIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.optionSome valueWB.toStep)
        (Step.par.isBi.optionSome valueWB.toIsBi)
  | optionMatch _scrutBi _noneBi _someBi scrutIH noneIH someIH =>
      let scrutWB := scrutIH pointwiseWitness
      let noneWB := noneIH pointwiseWitness
      let someWB := someIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.optionMatch scrutWB.toStep noneWB.toStep someWB.toStep)
        (Step.par.isBi.optionMatch scrutWB.toIsBi noneWB.toIsBi someWB.toIsBi)
  | eitherInl _valueBi valueIH =>
      let valueWB := valueIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.eitherInl valueWB.toStep)
        (Step.par.isBi.eitherInl valueWB.toIsBi)
  | eitherInr _valueBi valueIH =>
      let valueWB := valueIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.eitherInr valueWB.toStep)
        (Step.par.isBi.eitherInr valueWB.toIsBi)
  | eitherMatch _scrutBi _leftBi _rightBi scrutIH leftIH rightIH =>
      let scrutWB := scrutIH pointwiseWitness
      let leftWB := leftIH pointwiseWitness
      let rightWB := rightIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.eitherMatch scrutWB.toStep leftWB.toStep rightWB.toStep)
        (Step.par.isBi.eitherMatch scrutWB.toIsBi leftWB.toIsBi rightWB.toIsBi)
  | idJ _baseBi _witnessBi baseIH witnessIH =>
      let baseWB := baseIH pointwiseWitness
      let witnessWB := witnessIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.idJ baseWB.toStep witnessWB.toStep)
        (Step.par.isBi.idJ baseWB.toIsBi witnessWB.toIsBi)
  -- Shallow ι cases (use firstSub on unchanged elseBranch / etc.).
  | iotaBoolElimTrue elseBranch _thenBi thenIH =>
      let thenWB := thenIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimTrue
          (Term.subst firstTermSubstitution elseBranch) thenWB.toStep)
        (Step.par.isBi.iotaBoolElimTrue
          (Term.subst firstTermSubstitution elseBranch) thenWB.toIsBi)
  | iotaBoolElimFalse thenBranch _elseBi elseIH =>
      let elseWB := elseIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimFalse
          (Term.subst firstTermSubstitution thenBranch) elseWB.toStep)
        (Step.par.isBi.iotaBoolElimFalse
          (Term.subst firstTermSubstitution thenBranch) elseWB.toIsBi)
  | iotaNatElimZero succBranch _zeroBi zeroIH =>
      let zeroWB := zeroIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimZero
          (Term.subst firstTermSubstitution succBranch) zeroWB.toStep)
        (Step.par.isBi.iotaNatElimZero
          (Term.subst firstTermSubstitution succBranch) zeroWB.toIsBi)
  | iotaNatElimSucc zeroBranch _predBi _succBi predIH succIH =>
      let predWB := predIH pointwiseWitness
      let succWB := succIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimSucc
          (Term.subst firstTermSubstitution zeroBranch)
          predWB.toStep succWB.toStep)
        (Step.par.isBi.iotaNatElimSucc
          (Term.subst firstTermSubstitution zeroBranch)
          predWB.toIsBi succWB.toIsBi)
  | iotaNatRecZero succBranch _zeroBi zeroIH =>
      let zeroWB := zeroIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecZero
          (Term.subst firstTermSubstitution succBranch) zeroWB.toStep)
        (Step.par.isBi.iotaNatRecZero
          (Term.subst firstTermSubstitution succBranch) zeroWB.toIsBi)
  | iotaNatRecSucc _predBi _zeroBi _succBi predIH zeroIH succIH =>
      let predWB := predIH pointwiseWitness
      let zeroWB := zeroIH pointwiseWitness
      let succWB := succIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecSucc predWB.toStep zeroWB.toStep succWB.toStep)
        (Step.par.isBi.iotaNatRecSucc predWB.toIsBi zeroWB.toIsBi succWB.toIsBi)
  | iotaListElimNil consBranch _nilBi nilIH =>
      let nilWB := nilIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaListElimNil
          (Term.subst firstTermSubstitution consBranch) nilWB.toStep)
        (Step.par.isBi.iotaListElimNil
          (Term.subst firstTermSubstitution consBranch) nilWB.toIsBi)
  | iotaListElimCons nilBranch _headBi _tailBi _consBi headIH tailIH consIH =>
      let headWB := headIH pointwiseWitness
      let tailWB := tailIH pointwiseWitness
      let consWB := consIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaListElimCons
          (Term.subst firstTermSubstitution nilBranch)
          headWB.toStep tailWB.toStep consWB.toStep)
        (Step.par.isBi.iotaListElimCons
          (Term.subst firstTermSubstitution nilBranch)
          headWB.toIsBi tailWB.toIsBi consWB.toIsBi)
  | iotaOptionMatchNone someBranch _noneBi noneIH =>
      let noneWB := noneIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchNone
          (Term.subst firstTermSubstitution someBranch) noneWB.toStep)
        (Step.par.isBi.iotaOptionMatchNone
          (Term.subst firstTermSubstitution someBranch) noneWB.toIsBi)
  | iotaOptionMatchSome noneBranch _valueBi _someBi valueIH someIH =>
      let valueWB := valueIH pointwiseWitness
      let someWB := someIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchSome
          (Term.subst firstTermSubstitution noneBranch)
          valueWB.toStep someWB.toStep)
        (Step.par.isBi.iotaOptionMatchSome
          (Term.subst firstTermSubstitution noneBranch)
          valueWB.toIsBi someWB.toIsBi)
  | iotaEitherMatchInl rightBranch _valueBi _leftBi valueIH leftIH =>
      let valueWB := valueIH pointwiseWitness
      let leftWB := leftIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInl
          (Term.subst firstTermSubstitution rightBranch)
          valueWB.toStep leftWB.toStep)
        (Step.par.isBi.iotaEitherMatchInl
          (Term.subst firstTermSubstitution rightBranch)
          valueWB.toIsBi leftWB.toIsBi)
  | iotaEitherMatchInr leftBranch _valueBi _rightBi valueIH rightIH =>
      let valueWB := valueIH pointwiseWitness
      let rightWB := rightIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInr
          (Term.subst firstTermSubstitution leftBranch)
          valueWB.toStep rightWB.toStep)
        (Step.par.isBi.iotaEitherMatchInr
          (Term.subst firstTermSubstitution leftBranch)
          valueWB.toIsBi rightWB.toIsBi)
  | iotaIdJRefl _baseBi baseIH =>
      let baseWB := baseIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaIdJRefl baseWB.toStep)
        (Step.par.isBi.iotaIdJRefl baseWB.toIsBi)
  -- Shallow β cases — HEq plumbing aligns subst over `subst0` with the
  -- castTarget shape.  Both par and isBi use the SAME targetEquality
  -- value, constructed inline.
  | betaApp _bodyBi _argBi bodyIH argIH =>
      rename_i domainType codomainType _ bodyAfter _ argumentAfter _ _
      let bodyWB := bodyIH (TermSubst.par_lift_witnessed pointwiseWitness domainType)
      let argWB := argIH pointwiseWitness
      let substitutedArgumentAfter : Term targetCtx (domainType.subst typeSubstitution) :=
        Term.subst secondTermSubstitution argumentAfter
      let substitutedBodyAfter :
          Term (targetCtx.cons (domainType.subst typeSubstitution))
            (codomainType.weaken.subst typeSubstitution.lift) :=
        Term.subst (TermSubst.lift secondTermSubstitution domainType) bodyAfter
      let substitutedBetaStep :=
        Step.par.betaApp
          (Step.par.castBoth (Ty.subst_weaken_commute codomainType typeSubstitution)
            bodyWB.toStep)
          argWB.toStep
      let substitutedBetaStepIsBi :=
        Step.par.isBi.betaApp
          (Step.par.isBi.castBoth_eq (Ty.subst_weaken_commute codomainType typeSubstitution)
            bodyWB.toIsBi)
          argWB.toIsBi
      let primitiveTarget : Term targetCtx (codomainType.subst typeSubstitution) :=
        (Ty.weaken_subst_singleton
            (codomainType.subst typeSubstitution)
            (domainType.subst typeSubstitution)) ▸
          Term.subst0
            ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸ substitutedBodyAfter)
            substitutedArgumentAfter
      let targetEquality :
          primitiveTarget =
          Term.subst secondTermSubstitution
            ((Ty.weaken_subst_singleton codomainType domainType) ▸
              Term.subst0 bodyAfter argumentAfter) :=
        eq_of_heq (HEq.symm (by
          apply HEq.trans
            (Term.subst_HEq_cast_input secondTermSubstitution
              (Ty.weaken_subst_singleton codomainType domainType)
              (Term.subst0 bodyAfter argumentAfter))
          apply HEq.trans
            (Term.subst0_subst_HEq secondTermSubstitution bodyAfter argumentAfter)
          apply HEq.trans
            (HEq.symm
              (Term.subst0_HEq_cast_input
                (Ty.subst_weaken_commute codomainType typeSubstitution)
                substitutedBodyAfter substitutedArgumentAfter))
          exact Term.castRight_HEq
            (Ty.weaken_subst_singleton
              (codomainType.subst typeSubstitution)
              (domainType.subst typeSubstitution))
            (Term.subst0
              ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸ substitutedBodyAfter)
              substitutedArgumentAfter)))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality substitutedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality substitutedBetaStepIsBi)
  | betaAppPi _bodyBi _argBi bodyIH argIH =>
      rename_i domainType codomainType _ bodyAfter _ argumentAfter _ _
      let bodyWB := bodyIH (TermSubst.par_lift_witnessed pointwiseWitness domainType)
      let argWB := argIH pointwiseWitness
      let resultTypeEquality :=
        Ty.subst0_subst_commute codomainType domainType typeSubstitution
      let substitutedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaAppPi bodyWB.toStep argWB.toStep)
      let substitutedBetaStepIsBi :=
        Step.par.isBi.castBoth_eq resultTypeEquality.symm
          (Step.par.isBi.betaAppPi bodyWB.toIsBi argWB.toIsBi)
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.subst (TermSubst.lift secondTermSubstitution domainType) bodyAfter)
                (Term.subst secondTermSubstitution argumentAfter)
            = Term.subst secondTermSubstitution (Term.subst0 bodyAfter argumentAfter) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.subst0_subst_HEq secondTermSubstitution bodyAfter argumentAfter)))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality substitutedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality substitutedBetaStepIsBi)
  | betaFstPair _firstBi firstIH =>
      rename_i firstType secondType _ _ secondVal _
      let firstWB := firstIH pointwiseWitness
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      simp only [Term.subst]
      exact Step.parWithBi.mk
        (Step.par.betaFstPair
          (resultTypeEquality ▸ Term.subst firstTermSubstitution secondVal)
          firstWB.toStep)
        (Step.par.isBi.betaFstPair
          (secondVal := resultTypeEquality ▸ Term.subst firstTermSubstitution secondVal)
          firstWB.toIsBi)
  | betaSndPair _secondBi secondIH =>
      rename_i firstType secondType firstVal _ secondAfter _
      let secondWB := secondIH pointwiseWitness
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      let substitutedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaSndPair
            (Term.subst firstTermSubstitution firstVal)
            (Step.par.castBoth resultTypeEquality secondWB.toStep))
      let substitutedBetaStepIsBi :=
        Step.par.isBi.castBoth_eq resultTypeEquality.symm
          (Step.par.isBi.betaSndPair
            (firstVal := Term.subst firstTermSubstitution firstVal)
            (Step.par.isBi.castBoth_eq resultTypeEquality secondWB.toIsBi))
      let targetEquality :
          resultTypeEquality.symm ▸
              (resultTypeEquality ▸ Term.subst secondTermSubstitution secondAfter)
            = Term.subst secondTermSubstitution secondAfter :=
        eq_of_heq (HEq.trans (eqRec_heq _ _) (eqRec_heq _ _))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality substitutedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality substitutedBetaStepIsBi)
  -- Deep β cases — same pattern as shallow β, IH provides `parWithBi`
  -- on the lam/pair child term.
  | betaAppDeep _funBi _argBi funIH argIH =>
      rename_i domainType codomainType _ body _ argAfter _ _
      let funWB := funIH pointwiseWitness
      let argWB := argIH pointwiseWitness
      let substitutedArgAfter : Term targetCtx (domainType.subst typeSubstitution) :=
        Term.subst secondTermSubstitution argAfter
      let substitutedBody :
          Term (targetCtx.cons (domainType.subst typeSubstitution))
            (codomainType.weaken.subst typeSubstitution.lift) :=
        Term.subst (TermSubst.lift secondTermSubstitution domainType) body
      let substitutedBetaStep :=
        Step.par.betaAppDeep funWB.toStep argWB.toStep
      let substitutedBetaStepIsBi :=
        Step.par.isBi.betaAppDeep funWB.toIsBi argWB.toIsBi
      let primitiveTarget : Term targetCtx (codomainType.subst typeSubstitution) :=
        (Ty.weaken_subst_singleton
            (codomainType.subst typeSubstitution)
            (domainType.subst typeSubstitution)) ▸
          Term.subst0
            ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸ substitutedBody)
            substitutedArgAfter
      let targetEquality :
          primitiveTarget =
          Term.subst secondTermSubstitution
            ((Ty.weaken_subst_singleton codomainType domainType) ▸
              Term.subst0 body argAfter) :=
        eq_of_heq (HEq.symm (by
          apply HEq.trans
            (Term.subst_HEq_cast_input secondTermSubstitution
              (Ty.weaken_subst_singleton codomainType domainType)
              (Term.subst0 body argAfter))
          apply HEq.trans
            (Term.subst0_subst_HEq secondTermSubstitution body argAfter)
          apply HEq.trans
            (HEq.symm
              (Term.subst0_HEq_cast_input
                (Ty.subst_weaken_commute codomainType typeSubstitution)
                substitutedBody substitutedArgAfter))
          exact Term.castRight_HEq
            (Ty.weaken_subst_singleton
              (codomainType.subst typeSubstitution)
              (domainType.subst typeSubstitution))
            (Term.subst0
              ((Ty.subst_weaken_commute codomainType typeSubstitution) ▸ substitutedBody)
              substitutedArgAfter)))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality substitutedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality substitutedBetaStepIsBi)
  | betaAppPiDeep _funBi _argBi funIH argIH =>
      rename_i domainType codomainType _ body _ argAfter _ _
      let funWB := funIH pointwiseWitness
      let argWB := argIH pointwiseWitness
      let resultTypeEquality :=
        Ty.subst0_subst_commute codomainType domainType typeSubstitution
      let substitutedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaAppPiDeep funWB.toStep argWB.toStep)
      let substitutedBetaStepIsBi :=
        Step.par.isBi.castBoth_eq resultTypeEquality.symm
          (Step.par.isBi.betaAppPiDeep funWB.toIsBi argWB.toIsBi)
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.subst (TermSubst.lift secondTermSubstitution domainType) body)
                (Term.subst secondTermSubstitution argAfter)
            = Term.subst secondTermSubstitution (Term.subst0 body argAfter) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.subst0_subst_HEq secondTermSubstitution body argAfter)))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality substitutedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality substitutedBetaStepIsBi)
  | betaFstPairDeep _pairBi pairIH =>
      let pairWB := pairIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.betaFstPairDeep pairWB.toStep)
        (Step.par.isBi.betaFstPairDeep pairWB.toIsBi)
  | betaSndPairDeep _pairBi pairIH =>
      rename_i firstType secondType _ _ secondVal _
      let pairWB := pairIH pointwiseWitness
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      let substitutedBetaStep :=
        Step.par.castBoth resultTypeEquality.symm
          (Step.par.betaSndPairDeep pairWB.toStep)
      let substitutedBetaStepIsBi :=
        Step.par.isBi.castBoth_eq resultTypeEquality.symm
          (Step.par.isBi.betaSndPairDeep pairWB.toIsBi)
      let targetEquality :
          resultTypeEquality.symm ▸
              ((Ty.subst0_subst_commute secondType firstType typeSubstitution) ▸
                Term.subst secondTermSubstitution secondVal)
            = Term.subst secondTermSubstitution secondVal :=
        eq_of_heq (HEq.trans (eqRec_heq _ _) (eqRec_heq _ _))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality substitutedBetaStep)
        (Step.par.isBi.castTarget_eq targetEquality substitutedBetaStepIsBi)
  -- Deep ι cases.
  | iotaBoolElimTrueDeep elseBranch _scrutBi _thenBi scrutIH thenIH =>
      let scrutWB := scrutIH pointwiseWitness
      let thenWB := thenIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimTrueDeep
          (Term.subst firstTermSubstitution elseBranch)
          scrutWB.toStep thenWB.toStep)
        (Step.par.isBi.iotaBoolElimTrueDeep
          (Term.subst firstTermSubstitution elseBranch)
          scrutWB.toIsBi thenWB.toIsBi)
  | iotaBoolElimFalseDeep thenBranch _scrutBi _elseBi scrutIH elseIH =>
      let scrutWB := scrutIH pointwiseWitness
      let elseWB := elseIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimFalseDeep
          (Term.subst firstTermSubstitution thenBranch)
          scrutWB.toStep elseWB.toStep)
        (Step.par.isBi.iotaBoolElimFalseDeep
          (Term.subst firstTermSubstitution thenBranch)
          scrutWB.toIsBi elseWB.toIsBi)
  | iotaNatElimZeroDeep succBranch _scrutBi _zeroBi scrutIH zeroIH =>
      let scrutWB := scrutIH pointwiseWitness
      let zeroWB := zeroIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimZeroDeep
          (Term.subst firstTermSubstitution succBranch)
          scrutWB.toStep zeroWB.toStep)
        (Step.par.isBi.iotaNatElimZeroDeep
          (Term.subst firstTermSubstitution succBranch)
          scrutWB.toIsBi zeroWB.toIsBi)
  | iotaNatElimSuccDeep zeroBranch _scrutBi _succBi scrutIH succIH =>
      let scrutWB := scrutIH pointwiseWitness
      let succWB := succIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimSuccDeep
          (Term.subst firstTermSubstitution zeroBranch)
          scrutWB.toStep succWB.toStep)
        (Step.par.isBi.iotaNatElimSuccDeep
          (Term.subst firstTermSubstitution zeroBranch)
          scrutWB.toIsBi succWB.toIsBi)
  | iotaNatRecZeroDeep succBranch _scrutBi _zeroBi scrutIH zeroIH =>
      let scrutWB := scrutIH pointwiseWitness
      let zeroWB := zeroIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecZeroDeep
          (Term.subst firstTermSubstitution succBranch)
          scrutWB.toStep zeroWB.toStep)
        (Step.par.isBi.iotaNatRecZeroDeep
          (Term.subst firstTermSubstitution succBranch)
          scrutWB.toIsBi zeroWB.toIsBi)
  | iotaNatRecSuccDeep _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      let scrutWB := scrutIH pointwiseWitness
      let zeroWB := zeroIH pointwiseWitness
      let succWB := succIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecSuccDeep scrutWB.toStep zeroWB.toStep succWB.toStep)
        (Step.par.isBi.iotaNatRecSuccDeep scrutWB.toIsBi zeroWB.toIsBi succWB.toIsBi)
  | iotaListElimNilDeep consBranch _scrutBi _nilBi scrutIH nilIH =>
      let scrutWB := scrutIH pointwiseWitness
      let nilWB := nilIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaListElimNilDeep
          (Term.subst firstTermSubstitution consBranch)
          scrutWB.toStep nilWB.toStep)
        (Step.par.isBi.iotaListElimNilDeep
          (Term.subst firstTermSubstitution consBranch)
          scrutWB.toIsBi nilWB.toIsBi)
  | iotaListElimConsDeep nilBranch _scrutBi _consBi scrutIH consIH =>
      let scrutWB := scrutIH pointwiseWitness
      let consWB := consIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaListElimConsDeep
          (Term.subst firstTermSubstitution nilBranch)
          scrutWB.toStep consWB.toStep)
        (Step.par.isBi.iotaListElimConsDeep
          (Term.subst firstTermSubstitution nilBranch)
          scrutWB.toIsBi consWB.toIsBi)
  | iotaOptionMatchNoneDeep someBranch _scrutBi _noneBi scrutIH noneIH =>
      let scrutWB := scrutIH pointwiseWitness
      let noneWB := noneIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchNoneDeep
          (Term.subst firstTermSubstitution someBranch)
          scrutWB.toStep noneWB.toStep)
        (Step.par.isBi.iotaOptionMatchNoneDeep
          (Term.subst firstTermSubstitution someBranch)
          scrutWB.toIsBi noneWB.toIsBi)
  | iotaOptionMatchSomeDeep noneBranch _scrutBi _someBi scrutIH someIH =>
      let scrutWB := scrutIH pointwiseWitness
      let someWB := someIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchSomeDeep
          (Term.subst firstTermSubstitution noneBranch)
          scrutWB.toStep someWB.toStep)
        (Step.par.isBi.iotaOptionMatchSomeDeep
          (Term.subst firstTermSubstitution noneBranch)
          scrutWB.toIsBi someWB.toIsBi)
  | iotaEitherMatchInlDeep rightBranch _scrutBi _leftBi scrutIH leftIH =>
      let scrutWB := scrutIH pointwiseWitness
      let leftWB := leftIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInlDeep
          (Term.subst firstTermSubstitution rightBranch)
          scrutWB.toStep leftWB.toStep)
        (Step.par.isBi.iotaEitherMatchInlDeep
          (Term.subst firstTermSubstitution rightBranch)
          scrutWB.toIsBi leftWB.toIsBi)
  | iotaEitherMatchInrDeep leftBranch _scrutBi _rightBi scrutIH rightIH =>
      let scrutWB := scrutIH pointwiseWitness
      let rightWB := rightIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInrDeep
          (Term.subst firstTermSubstitution leftBranch)
          scrutWB.toStep rightWB.toStep)
        (Step.par.isBi.iotaEitherMatchInrDeep
          (Term.subst firstTermSubstitution leftBranch)
          scrutWB.toIsBi rightWB.toIsBi)
  | iotaIdJReflDeep _witnessBi _baseBi witnessIH baseIH =>
      let witnessWB := witnessIH pointwiseWitness
      let baseWB := baseIH pointwiseWitness
      exact Step.parWithBi.mk
        (Step.par.iotaIdJReflDeep witnessWB.toStep baseWB.toStep)
        (Step.par.isBi.iotaIdJReflDeep witnessWB.toIsBi baseWB.toIsBi)

/-- **Singleton specialization of witnessed joint substitution.**
The β-workhorse for `Step.par.cd_monotone`'s shallow β cases.

Given parWithBi witnesses on body and argument, produces a single
parWithBi step on `subst0`.  Composed with `cd_dominates_with_isBi`
(body and arg) and `cd_lemma_star_with_bi`, this closes Step B of
the cd_monotone β strategy. -/
theorem Step.par.subst0_par_witnessed
    {mode : Mode} {scope : Nat} {ctx : Ctx mode level scope}
    {argumentType : Ty level scope} {bodyType : Ty level (scope + 1)}
    {bodyBefore bodyAfter : Term (ctx.cons argumentType) bodyType}
    {argumentBefore argumentAfter : Term ctx argumentType}
    (bodyWitness : Step.parWithBi bodyBefore bodyAfter)
    (argumentWitness : Step.parWithBi argumentBefore argumentAfter) :
    Step.parWithBi
      (Term.subst0 bodyBefore argumentBefore)
      (Term.subst0 bodyAfter argumentAfter) :=
  Step.par.subst_par_witnessed bodyWitness.toIsBi
    (TermSubst.singleton_par_witnessed argumentWitness)

end LeanFX.Syntax

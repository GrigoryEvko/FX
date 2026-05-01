import LeanFX.Syntax.Reduction.ParBi
import LeanFX.Syntax.Reduction.ParInversion

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Step.parStarWithBi` — paired chain + isBi witness.

A single-constructor cons-list inductive that bundles a
`Step.parStar` chain with a `Step.par.isBi` witness for each
link.  The corresponding `parStar` chain is recovered by
projection (`.toParStar`); the corresponding `Step.parStar.isBi`
witness on that chain is recovered by `.toIsBi`.

This predicate is the technical vehicle for the typed
`cd_lemma_star`: the aggregator must produce both a chain and
an isBi witness simultaneously, since the deep-βι case helpers
need the chain isBi-ness to invoke the βι-only target
inversions (`Step.parStar.lam_target_inv_isBi` and friends).
Pairing the two avoids returning a `Σ' (chain : parStar a b),
parStar.isBi chain` (which would land in `Type`, not `Prop`,
and obstruct propext-free reasoning). -/

inductive Step.parStarWithBi :
    ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
      {termType : Ty level scope},
    Term ctx termType → Term ctx termType → Prop
  /-- Empty chain. -/
  | refl :
      ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {termType : Ty level scope}
        (term : Term ctx termType),
      Step.parStarWithBi term term
  /-- Cons: prepend a single βι step to a chain-with-isBi. -/
  | trans :
      ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {termType : Ty level scope}
        {sourceTerm midTerm targetTerm : Term ctx termType}
        {firstStep : Step.par sourceTerm midTerm},
      Step.par.isBi firstStep →
      Step.parStarWithBi midTerm targetTerm →
      Step.parStarWithBi sourceTerm targetTerm

/-- Project to plain parStar. -/
theorem Step.parStarWithBi.toParStar
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType} :
    Step.parStarWithBi sourceTerm targetTerm →
      Step.parStar sourceTerm targetTerm
  | .refl term => Step.parStar.refl term
  | .trans (firstStep := step) _ rest =>
      Step.parStar.trans step rest.toParStar

/-- Project to chain isBi witness. -/
theorem Step.parStarWithBi.toIsBi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType} :
    (chainWithBi : Step.parStarWithBi sourceTerm targetTerm) →
      Step.parStar.isBi chainWithBi.toParStar
  | .refl term => Step.parStar.isBi.refl term
  | .trans firstBi rest =>
      Step.parStar.isBi.trans firstBi rest.toIsBi

/-! ## Lifting a single βι `Step.par` step to a `parStarWithBi`. -/

/-- Wrap a single βι step into a singleton chain-with-isBi. -/
theorem Step.par.isBi.toParStarWithBi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    {parStep : Step.par sourceTerm targetTerm}
    (stepBi : Step.par.isBi parStep) :
    Step.parStarWithBi sourceTerm targetTerm :=
  Step.parStarWithBi.trans stepBi (Step.parStarWithBi.refl targetTerm)

/-! ## Paired snoc, append, and casts. -/

/-- Append a single βι step to the end of a chain-with-isBi. -/
theorem Step.parStarWithBi.snoc
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm midTerm targetTerm : Term ctx termType}
    (chainWithBi : Step.parStarWithBi sourceTerm midTerm)
    {finalStep : Step.par midTerm targetTerm}
    (finalStepBi : Step.par.isBi finalStep) :
    Step.parStarWithBi sourceTerm targetTerm := by
  induction chainWithBi with
  | refl _ => exact finalStepBi.toParStarWithBi
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans firstBi (restIH finalStepBi)

/-- Concatenate two chain-with-isBi proofs. -/
theorem Step.parStarWithBi.append
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {sourceTerm midTerm targetTerm : Term ctx termType}
    (firstWithBi : Step.parStarWithBi sourceTerm midTerm)
    (secondWithBi : Step.parStarWithBi midTerm targetTerm) :
    Step.parStarWithBi sourceTerm targetTerm := by
  induction firstWithBi with
  | refl _ => exact secondWithBi
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans firstBi (restIH secondWithBi)

/-- Transport a chain-with-isBi across the same Ty equality on
both endpoints — analogue of `Step.parStar.castBoth`. -/
theorem Step.parStarWithBi.castBoth
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    (typeEquality : sourceType = targetType)
    {beforeTerm afterTerm : Term ctx sourceType}
    (chainWithBi : Step.parStarWithBi beforeTerm afterTerm) :
    Step.parStarWithBi (typeEquality ▸ beforeTerm)
                       (typeEquality ▸ afterTerm) := by
  cases typeEquality
  exact chainWithBi

/-! ## Paired single-position congruence rules.

Each paired cong rule mirrors its `parStar` counterpart by
induction on `parStarWithBi`.  The `refl` arm produces the
empty chain; the `trans` arm prepends `Step.par.<ctor> firstStep
(Step.par.refl _)` (or the appropriate constructor) and uses
`Step.par.isBi.<ctor>` to lift the head step's isBi witness. -/

/-- Paired λ-body congruence. -/
theorem Step.parStarWithBi.lam_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body body' : Term (ctx.cons domainType) codomainType.weaken}
    (bodyChainWithBi : Step.parStarWithBi body body') :
    Step.parStarWithBi
      (Term.lam (codomainType := codomainType) body)
      (Term.lam (codomainType := codomainType) body') := by
  induction bodyChainWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.lam firstBi) restIH

/-- Paired Π-λ-body congruence. -/
theorem Step.parStarWithBi.lamPi_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body body' : Term (ctx.cons domainType) codomainType}
    (bodyChainWithBi : Step.parStarWithBi body body') :
    Step.parStarWithBi
      (Term.lamPi (domainType := domainType) body)
      (Term.lamPi (domainType := domainType) body') := by
  induction bodyChainWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.lamPi firstBi) restIH

/-- Paired single-position `app` congruence on function. -/
theorem Step.parStarWithBi.app_cong_function
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionTerm functionTerm' : Term ctx (Ty.arrow domainType codomainType)}
    (argumentTerm : Term ctx domainType)
    (functionWithBi : Step.parStarWithBi functionTerm functionTerm') :
    Step.parStarWithBi (Term.app functionTerm argumentTerm)
                       (Term.app functionTerm' argumentTerm) := by
  induction functionWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.app firstBi (Step.par.isBi.refl argumentTerm)) restIH

/-- Paired single-position `app` congruence on argument. -/
theorem Step.parStarWithBi.app_cong_argument
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    (functionTerm : Term ctx (Ty.arrow domainType codomainType))
    {argumentTerm argumentTerm' : Term ctx domainType}
    (argumentWithBi : Step.parStarWithBi argumentTerm argumentTerm') :
    Step.parStarWithBi (Term.app functionTerm argumentTerm)
                       (Term.app functionTerm argumentTerm') := by
  induction argumentWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.app (Step.par.isBi.refl functionTerm) firstBi) restIH

/-- Paired non-dependent application congruence. -/
theorem Step.parStarWithBi.app_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionTerm functionTerm' : Term ctx (Ty.arrow domainType codomainType)}
    {argumentTerm argumentTerm' : Term ctx domainType}
    (functionWithBi : Step.parStarWithBi functionTerm functionTerm')
    (argumentWithBi : Step.parStarWithBi argumentTerm argumentTerm') :
    Step.parStarWithBi (Term.app functionTerm argumentTerm)
                       (Term.app functionTerm' argumentTerm') :=
  Step.parStarWithBi.append
    (Step.parStarWithBi.app_cong_function argumentTerm functionWithBi)
    (Step.parStarWithBi.app_cong_argument functionTerm' argumentWithBi)

/-- Paired single-position `appPi` congruence on function. -/
theorem Step.parStarWithBi.appPi_cong_function
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {functionTerm functionTerm' : Term ctx (Ty.piTy domainType codomainType)}
    (argumentTerm : Term ctx domainType)
    (functionWithBi : Step.parStarWithBi functionTerm functionTerm') :
    Step.parStarWithBi (Term.appPi functionTerm argumentTerm)
                       (Term.appPi functionTerm' argumentTerm) := by
  induction functionWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.appPi firstBi (Step.par.isBi.refl argumentTerm)) restIH

/-- Paired single-position `appPi` congruence on argument. -/
theorem Step.parStarWithBi.appPi_cong_argument
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    (functionTerm : Term ctx (Ty.piTy domainType codomainType))
    {argumentTerm argumentTerm' : Term ctx domainType}
    (argumentWithBi : Step.parStarWithBi argumentTerm argumentTerm') :
    Step.parStarWithBi (Term.appPi functionTerm argumentTerm)
                       (Term.appPi functionTerm argumentTerm') := by
  induction argumentWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.appPi (Step.par.isBi.refl functionTerm) firstBi) restIH

/-- Paired dependent application congruence. -/
theorem Step.parStarWithBi.appPi_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {functionTerm functionTerm' : Term ctx (Ty.piTy domainType codomainType)}
    {argumentTerm argumentTerm' : Term ctx domainType}
    (functionWithBi : Step.parStarWithBi functionTerm functionTerm')
    (argumentWithBi : Step.parStarWithBi argumentTerm argumentTerm') :
    Step.parStarWithBi (Term.appPi functionTerm argumentTerm)
                       (Term.appPi functionTerm' argumentTerm') :=
  Step.parStarWithBi.append
    (Step.parStarWithBi.appPi_cong_function argumentTerm functionWithBi)
    (Step.parStarWithBi.appPi_cong_argument functionTerm' argumentWithBi)

/-- Paired single-position `pair` congruence on first component. -/
theorem Step.parStarWithBi.pair_cong_first
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal firstVal' : Term ctx firstType}
    (secondVal : Term ctx (secondType.subst0 firstType))
    (firstWithBi : Step.parStarWithBi firstVal firstVal') :
    Step.parStarWithBi (Term.pair (secondType := secondType) firstVal secondVal)
                       (Term.pair (secondType := secondType) firstVal' secondVal) := by
  induction firstWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.pair firstBi (Step.par.isBi.refl secondVal)) restIH

/-- Paired single-position `pair` congruence on second component. -/
theorem Step.parStarWithBi.pair_cong_second
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    (firstVal : Term ctx firstType)
    {secondVal secondVal' : Term ctx (secondType.subst0 firstType)}
    (secondWithBi : Step.parStarWithBi secondVal secondVal') :
    Step.parStarWithBi (Term.pair (secondType := secondType) firstVal secondVal)
                       (Term.pair (secondType := secondType) firstVal secondVal') := by
  induction secondWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.pair (Step.par.isBi.refl firstVal) firstBi) restIH

/-- Paired Σ-pair congruence. -/
theorem Step.parStarWithBi.pair_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal firstVal' : Term ctx firstType}
    {secondVal secondVal' : Term ctx (secondType.subst0 firstType)}
    (firstWithBi : Step.parStarWithBi firstVal firstVal')
    (secondWithBi : Step.parStarWithBi secondVal secondVal') :
    Step.parStarWithBi (Term.pair firstVal secondVal)
                       (Term.pair firstVal' secondVal') :=
  Step.parStarWithBi.append
    (Step.parStarWithBi.pair_cong_first secondVal firstWithBi)
    (Step.parStarWithBi.pair_cong_second firstVal' secondWithBi)

/-- Paired first-projection congruence. -/
theorem Step.parStarWithBi.fst_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairTerm pairTerm' : Term ctx (Ty.sigmaTy firstType secondType)}
    (pairWithBi : Step.parStarWithBi pairTerm pairTerm') :
    Step.parStarWithBi (Term.fst pairTerm) (Term.fst pairTerm') := by
  induction pairWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans (Step.par.isBi.fst firstBi) restIH

/-- Paired second-projection congruence. -/
theorem Step.parStarWithBi.snd_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairTerm pairTerm' : Term ctx (Ty.sigmaTy firstType secondType)}
    (pairWithBi : Step.parStarWithBi pairTerm pairTerm') :
    Step.parStarWithBi (Term.snd pairTerm) (Term.snd pairTerm') := by
  induction pairWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans (Step.par.isBi.snd firstBi) restIH

/-! ### Eliminator congruence rules (paired). -/

/-- Paired single-position `boolElim` congruence on scrutinee. -/
theorem Step.parStarWithBi.boolElim_cong_scrutinee
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.bool}
    (thenBranch elseBranch : Term ctx resultType)
    (scrutineeWithBi : Step.parStarWithBi scrutinee scrutinee') :
    Step.parStarWithBi (Term.boolElim scrutinee thenBranch elseBranch)
                       (Term.boolElim scrutinee' thenBranch elseBranch) := by
  induction scrutineeWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.boolElim firstBi
          (Step.par.isBi.refl thenBranch) (Step.par.isBi.refl elseBranch))
        restIH

/-- Paired single-position `boolElim` congruence on then-branch. -/
theorem Step.parStarWithBi.boolElim_cong_then
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    {thenBranch thenBranch' : Term ctx resultType}
    (elseBranch : Term ctx resultType)
    (thenWithBi : Step.parStarWithBi thenBranch thenBranch') :
    Step.parStarWithBi (Term.boolElim scrutinee thenBranch elseBranch)
                       (Term.boolElim scrutinee thenBranch' elseBranch) := by
  induction thenWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.boolElim
          (Step.par.isBi.refl scrutinee) firstBi
          (Step.par.isBi.refl elseBranch))
        restIH

/-- Paired single-position `boolElim` congruence on else-branch. -/
theorem Step.parStarWithBi.boolElim_cong_else
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    (thenBranch : Term ctx resultType)
    {elseBranch elseBranch' : Term ctx resultType}
    (elseWithBi : Step.parStarWithBi elseBranch elseBranch') :
    Step.parStarWithBi (Term.boolElim scrutinee thenBranch elseBranch)
                       (Term.boolElim scrutinee thenBranch elseBranch') := by
  induction elseWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.boolElim
          (Step.par.isBi.refl scrutinee) (Step.par.isBi.refl thenBranch) firstBi)
        restIH

/-- Paired three-leg `boolElim` congruence. -/
theorem Step.parStarWithBi.boolElim_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.bool}
    {thenBranch thenBranch' : Term ctx resultType}
    {elseBranch elseBranch' : Term ctx resultType}
    (scrutineeWithBi : Step.parStarWithBi scrutinee scrutinee')
    (thenWithBi : Step.parStarWithBi thenBranch thenBranch')
    (elseWithBi : Step.parStarWithBi elseBranch elseBranch') :
    Step.parStarWithBi (Term.boolElim scrutinee thenBranch elseBranch)
                       (Term.boolElim scrutinee' thenBranch' elseBranch') :=
  Step.parStarWithBi.append
    (Step.parStarWithBi.boolElim_cong_scrutinee thenBranch elseBranch
      scrutineeWithBi)
    (Step.parStarWithBi.append
      (Step.parStarWithBi.boolElim_cong_then scrutinee' elseBranch thenWithBi)
      (Step.parStarWithBi.boolElim_cong_else scrutinee' thenBranch' elseWithBi))

/-- Paired `natSucc` congruence. -/
theorem Step.parStarWithBi.natSucc_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {predecessor predecessor' : Term ctx Ty.nat}
    (predWithBi : Step.parStarWithBi predecessor predecessor') :
    Step.parStarWithBi (Term.natSucc predecessor) (Term.natSucc predecessor') := by
  induction predWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans (Step.par.isBi.natSucc firstBi) restIH

/-- Paired single-position `natElim` congruence on scrutinee. -/
theorem Step.parStarWithBi.natElim_cong_scrutinee
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
    (scrutineeWithBi : Step.parStarWithBi scrutinee scrutinee') :
    Step.parStarWithBi (Term.natElim scrutinee zeroBranch succBranch)
                       (Term.natElim scrutinee' zeroBranch succBranch) := by
  induction scrutineeWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.natElim firstBi
          (Step.par.isBi.refl zeroBranch) (Step.par.isBi.refl succBranch))
        restIH

/-- Paired single-position `natElim` congruence on zero-branch. -/
theorem Step.parStarWithBi.natElim_cong_zero
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch zeroBranch' : Term ctx resultType}
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
    (zeroWithBi : Step.parStarWithBi zeroBranch zeroBranch') :
    Step.parStarWithBi (Term.natElim scrutinee zeroBranch succBranch)
                       (Term.natElim scrutinee zeroBranch' succBranch) := by
  induction zeroWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.natElim
          (Step.par.isBi.refl scrutinee) firstBi
          (Step.par.isBi.refl succBranch))
        restIH

/-- Paired single-position `natElim` congruence on succ-branch. -/
theorem Step.parStarWithBi.natElim_cong_succ
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)}
    (succWithBi : Step.parStarWithBi succBranch succBranch') :
    Step.parStarWithBi (Term.natElim scrutinee zeroBranch succBranch)
                       (Term.natElim scrutinee zeroBranch succBranch') := by
  induction succWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.natElim
          (Step.par.isBi.refl scrutinee) (Step.par.isBi.refl zeroBranch) firstBi)
        restIH

/-- Paired three-leg `natElim` congruence. -/
theorem Step.parStarWithBi.natElim_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.nat}
    {zeroBranch zeroBranch' : Term ctx resultType}
    {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)}
    (scrutineeWithBi : Step.parStarWithBi scrutinee scrutinee')
    (zeroWithBi : Step.parStarWithBi zeroBranch zeroBranch')
    (succWithBi : Step.parStarWithBi succBranch succBranch') :
    Step.parStarWithBi (Term.natElim scrutinee zeroBranch succBranch)
                       (Term.natElim scrutinee' zeroBranch' succBranch') :=
  Step.parStarWithBi.append
    (Step.parStarWithBi.natElim_cong_scrutinee zeroBranch succBranch
      scrutineeWithBi)
    (Step.parStarWithBi.append
      (Step.parStarWithBi.natElim_cong_zero scrutinee' succBranch zeroWithBi)
      (Step.parStarWithBi.natElim_cong_succ scrutinee' zeroBranch' succWithBi))

/-- Paired single-position `natRec` congruence on scrutinee. -/
theorem Step.parStarWithBi.natRec_cong_scrutinee
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch :
        Term ctx (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
    (scrutineeWithBi : Step.parStarWithBi scrutinee scrutinee') :
    Step.parStarWithBi (Term.natRec scrutinee zeroBranch succBranch)
                       (Term.natRec scrutinee' zeroBranch succBranch) := by
  induction scrutineeWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.natRec firstBi
          (Step.par.isBi.refl zeroBranch) (Step.par.isBi.refl succBranch))
        restIH

/-- Paired single-position `natRec` congruence on zero-branch. -/
theorem Step.parStarWithBi.natRec_cong_zero
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch zeroBranch' : Term ctx resultType}
    (succBranch :
        Term ctx (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
    (zeroWithBi : Step.parStarWithBi zeroBranch zeroBranch') :
    Step.parStarWithBi (Term.natRec scrutinee zeroBranch succBranch)
                       (Term.natRec scrutinee zeroBranch' succBranch) := by
  induction zeroWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.natRec
          (Step.par.isBi.refl scrutinee) firstBi
          (Step.par.isBi.refl succBranch))
        restIH

/-- Paired single-position `natRec` congruence on succ-branch. -/
theorem Step.parStarWithBi.natRec_cong_succ
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch succBranch' :
        Term ctx (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (succWithBi : Step.parStarWithBi succBranch succBranch') :
    Step.parStarWithBi (Term.natRec scrutinee zeroBranch succBranch)
                       (Term.natRec scrutinee zeroBranch succBranch') := by
  induction succWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.natRec
          (Step.par.isBi.refl scrutinee) (Step.par.isBi.refl zeroBranch) firstBi)
        restIH

/-- Paired three-leg `natRec` congruence. -/
theorem Step.parStarWithBi.natRec_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.nat}
    {zeroBranch zeroBranch' : Term ctx resultType}
    {succBranch succBranch' :
        Term ctx (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (scrutineeWithBi : Step.parStarWithBi scrutinee scrutinee')
    (zeroWithBi : Step.parStarWithBi zeroBranch zeroBranch')
    (succWithBi : Step.parStarWithBi succBranch succBranch') :
    Step.parStarWithBi (Term.natRec scrutinee zeroBranch succBranch)
                       (Term.natRec scrutinee' zeroBranch' succBranch') :=
  Step.parStarWithBi.append
    (Step.parStarWithBi.natRec_cong_scrutinee zeroBranch succBranch
      scrutineeWithBi)
    (Step.parStarWithBi.append
      (Step.parStarWithBi.natRec_cong_zero scrutinee' succBranch zeroWithBi)
      (Step.parStarWithBi.natRec_cong_succ scrutinee' zeroBranch' succWithBi))

/-- Paired single-position `listCons` congruence on head. -/
theorem Step.parStarWithBi.listCons_cong_head
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {head head' : Term ctx elementType}
    (tail : Term ctx (Ty.list elementType))
    (headWithBi : Step.parStarWithBi head head') :
    Step.parStarWithBi (Term.listCons head tail) (Term.listCons head' tail) := by
  induction headWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.listCons firstBi (Step.par.isBi.refl tail)) restIH

/-- Paired single-position `listCons` congruence on tail. -/
theorem Step.parStarWithBi.listCons_cong_tail
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    (head : Term ctx elementType)
    {tail tail' : Term ctx (Ty.list elementType)}
    (tailWithBi : Step.parStarWithBi tail tail') :
    Step.parStarWithBi (Term.listCons head tail) (Term.listCons head tail') := by
  induction tailWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.listCons (Step.par.isBi.refl head) firstBi) restIH

/-- Paired `listCons` congruence. -/
theorem Step.parStarWithBi.listCons_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {head head' : Term ctx elementType}
    {tail tail' : Term ctx (Ty.list elementType)}
    (headWithBi : Step.parStarWithBi head head')
    (tailWithBi : Step.parStarWithBi tail tail') :
    Step.parStarWithBi (Term.listCons head tail) (Term.listCons head' tail') :=
  Step.parStarWithBi.append
    (Step.parStarWithBi.listCons_cong_head tail headWithBi)
    (Step.parStarWithBi.listCons_cong_tail head' tailWithBi)

/-- Paired single-position `listElim` congruence on scrutinee. -/
theorem Step.parStarWithBi.listElim_cong_scrutinee
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.list elementType)}
    (nilBranch : Term ctx resultType)
    (consBranch :
        Term ctx (Ty.arrow elementType
                          (Ty.arrow (Ty.list elementType) resultType)))
    (scrutineeWithBi : Step.parStarWithBi scrutinee scrutinee') :
    Step.parStarWithBi (Term.listElim scrutinee nilBranch consBranch)
                       (Term.listElim scrutinee' nilBranch consBranch) := by
  induction scrutineeWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.listElim firstBi
          (Step.par.isBi.refl nilBranch) (Step.par.isBi.refl consBranch))
        restIH

/-- Paired single-position `listElim` congruence on nil-branch. -/
theorem Step.parStarWithBi.listElim_cong_nil
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.list elementType))
    {nilBranch nilBranch' : Term ctx resultType}
    (consBranch :
        Term ctx (Ty.arrow elementType
                          (Ty.arrow (Ty.list elementType) resultType)))
    (nilWithBi : Step.parStarWithBi nilBranch nilBranch') :
    Step.parStarWithBi (Term.listElim scrutinee nilBranch consBranch)
                       (Term.listElim scrutinee nilBranch' consBranch) := by
  induction nilWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.listElim
          (Step.par.isBi.refl scrutinee) firstBi
          (Step.par.isBi.refl consBranch))
        restIH

/-- Paired single-position `listElim` congruence on cons-branch. -/
theorem Step.parStarWithBi.listElim_cong_cons
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.list elementType))
    (nilBranch : Term ctx resultType)
    {consBranch consBranch' :
        Term ctx (Ty.arrow elementType
                          (Ty.arrow (Ty.list elementType) resultType))}
    (consWithBi : Step.parStarWithBi consBranch consBranch') :
    Step.parStarWithBi (Term.listElim scrutinee nilBranch consBranch)
                       (Term.listElim scrutinee nilBranch consBranch') := by
  induction consWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.listElim
          (Step.par.isBi.refl scrutinee) (Step.par.isBi.refl nilBranch) firstBi)
        restIH

/-- Paired three-leg `listElim` congruence. -/
theorem Step.parStarWithBi.listElim_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.list elementType)}
    {nilBranch nilBranch' : Term ctx resultType}
    {consBranch consBranch' :
        Term ctx (Ty.arrow elementType
                          (Ty.arrow (Ty.list elementType) resultType))}
    (scrutineeWithBi : Step.parStarWithBi scrutinee scrutinee')
    (nilWithBi : Step.parStarWithBi nilBranch nilBranch')
    (consWithBi : Step.parStarWithBi consBranch consBranch') :
    Step.parStarWithBi (Term.listElim scrutinee nilBranch consBranch)
                       (Term.listElim scrutinee' nilBranch' consBranch') :=
  Step.parStarWithBi.append
    (Step.parStarWithBi.listElim_cong_scrutinee nilBranch consBranch
      scrutineeWithBi)
    (Step.parStarWithBi.append
      (Step.parStarWithBi.listElim_cong_nil scrutinee' consBranch nilWithBi)
      (Step.parStarWithBi.listElim_cong_cons scrutinee' nilBranch' consWithBi))

/-- Paired `optionSome` congruence. -/
theorem Step.parStarWithBi.optionSome_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {value value' : Term ctx elementType}
    (valueWithBi : Step.parStarWithBi value value') :
    Step.parStarWithBi (Term.optionSome value) (Term.optionSome value') := by
  induction valueWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans (Step.par.isBi.optionSome firstBi) restIH

/-- Paired single-position `optionMatch` congruence on scrutinee. -/
theorem Step.parStarWithBi.optionMatch_cong_scrutinee
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.option elementType)}
    (noneBranch : Term ctx resultType)
    (someBranch : Term ctx (Ty.arrow elementType resultType))
    (scrutineeWithBi : Step.parStarWithBi scrutinee scrutinee') :
    Step.parStarWithBi (Term.optionMatch scrutinee noneBranch someBranch)
                       (Term.optionMatch scrutinee' noneBranch someBranch) := by
  induction scrutineeWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.optionMatch firstBi
          (Step.par.isBi.refl noneBranch) (Step.par.isBi.refl someBranch))
        restIH

/-- Paired single-position `optionMatch` congruence on none-branch. -/
theorem Step.parStarWithBi.optionMatch_cong_none
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    {noneBranch noneBranch' : Term ctx resultType}
    (someBranch : Term ctx (Ty.arrow elementType resultType))
    (noneWithBi : Step.parStarWithBi noneBranch noneBranch') :
    Step.parStarWithBi (Term.optionMatch scrutinee noneBranch someBranch)
                       (Term.optionMatch scrutinee noneBranch' someBranch) := by
  induction noneWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.optionMatch
          (Step.par.isBi.refl scrutinee) firstBi
          (Step.par.isBi.refl someBranch))
        restIH

/-- Paired single-position `optionMatch` congruence on some-branch. -/
theorem Step.parStarWithBi.optionMatch_cong_some
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    (noneBranch : Term ctx resultType)
    {someBranch someBranch' : Term ctx (Ty.arrow elementType resultType)}
    (someWithBi : Step.parStarWithBi someBranch someBranch') :
    Step.parStarWithBi (Term.optionMatch scrutinee noneBranch someBranch)
                       (Term.optionMatch scrutinee noneBranch someBranch') := by
  induction someWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.optionMatch
          (Step.par.isBi.refl scrutinee) (Step.par.isBi.refl noneBranch) firstBi)
        restIH

/-- Paired three-leg `optionMatch` congruence. -/
theorem Step.parStarWithBi.optionMatch_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.option elementType)}
    {noneBranch noneBranch' : Term ctx resultType}
    {someBranch someBranch' : Term ctx (Ty.arrow elementType resultType)}
    (scrutineeWithBi : Step.parStarWithBi scrutinee scrutinee')
    (noneWithBi : Step.parStarWithBi noneBranch noneBranch')
    (someWithBi : Step.parStarWithBi someBranch someBranch') :
    Step.parStarWithBi (Term.optionMatch scrutinee noneBranch someBranch)
                       (Term.optionMatch scrutinee' noneBranch' someBranch') :=
  Step.parStarWithBi.append
    (Step.parStarWithBi.optionMatch_cong_scrutinee noneBranch someBranch
      scrutineeWithBi)
    (Step.parStarWithBi.append
      (Step.parStarWithBi.optionMatch_cong_none scrutinee' someBranch noneWithBi)
      (Step.parStarWithBi.optionMatch_cong_some scrutinee' noneBranch'
        someWithBi))

/-- Paired `eitherInl` congruence. -/
theorem Step.parStarWithBi.eitherInl_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value value' : Term ctx leftType}
    (valueWithBi : Step.parStarWithBi value value') :
    Step.parStarWithBi (Term.eitherInl (rightType := rightType) value)
                       (Term.eitherInl (rightType := rightType) value') := by
  induction valueWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans (Step.par.isBi.eitherInl firstBi) restIH

/-- Paired `eitherInr` congruence. -/
theorem Step.parStarWithBi.eitherInr_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value value' : Term ctx rightType}
    (valueWithBi : Step.parStarWithBi value value') :
    Step.parStarWithBi (Term.eitherInr (leftType := leftType) value)
                       (Term.eitherInr (leftType := leftType) value') := by
  induction valueWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans (Step.par.isBi.eitherInr firstBi) restIH

/-- Paired single-position `eitherMatch` congruence on scrutinee. -/
theorem Step.parStarWithBi.eitherMatch_cong_scrutinee
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.either leftType rightType)}
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    (rightBranch : Term ctx (Ty.arrow rightType resultType))
    (scrutineeWithBi : Step.parStarWithBi scrutinee scrutinee') :
    Step.parStarWithBi (Term.eitherMatch scrutinee leftBranch rightBranch)
                       (Term.eitherMatch scrutinee' leftBranch rightBranch) := by
  induction scrutineeWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.eitherMatch firstBi
          (Step.par.isBi.refl leftBranch) (Step.par.isBi.refl rightBranch))
        restIH

/-- Paired single-position `eitherMatch` congruence on left-branch. -/
theorem Step.parStarWithBi.eitherMatch_cong_left
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    {leftBranch leftBranch' : Term ctx (Ty.arrow leftType resultType)}
    (rightBranch : Term ctx (Ty.arrow rightType resultType))
    (leftWithBi : Step.parStarWithBi leftBranch leftBranch') :
    Step.parStarWithBi (Term.eitherMatch scrutinee leftBranch rightBranch)
                       (Term.eitherMatch scrutinee leftBranch' rightBranch) := by
  induction leftWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.eitherMatch
          (Step.par.isBi.refl scrutinee) firstBi
          (Step.par.isBi.refl rightBranch))
        restIH

/-- Paired single-position `eitherMatch` congruence on right-branch. -/
theorem Step.parStarWithBi.eitherMatch_cong_right
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    {rightBranch rightBranch' : Term ctx (Ty.arrow rightType resultType)}
    (rightWithBi : Step.parStarWithBi rightBranch rightBranch') :
    Step.parStarWithBi (Term.eitherMatch scrutinee leftBranch rightBranch)
                       (Term.eitherMatch scrutinee leftBranch rightBranch') := by
  induction rightWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.eitherMatch
          (Step.par.isBi.refl scrutinee) (Step.par.isBi.refl leftBranch) firstBi)
        restIH

/-- Paired three-leg `eitherMatch` congruence. -/
theorem Step.parStarWithBi.eitherMatch_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.either leftType rightType)}
    {leftBranch leftBranch' : Term ctx (Ty.arrow leftType resultType)}
    {rightBranch rightBranch' : Term ctx (Ty.arrow rightType resultType)}
    (scrutineeWithBi : Step.parStarWithBi scrutinee scrutinee')
    (leftWithBi : Step.parStarWithBi leftBranch leftBranch')
    (rightWithBi : Step.parStarWithBi rightBranch rightBranch') :
    Step.parStarWithBi (Term.eitherMatch scrutinee leftBranch rightBranch)
                       (Term.eitherMatch scrutinee' leftBranch' rightBranch') :=
  Step.parStarWithBi.append
    (Step.parStarWithBi.eitherMatch_cong_scrutinee leftBranch rightBranch
      scrutineeWithBi)
    (Step.parStarWithBi.append
      (Step.parStarWithBi.eitherMatch_cong_left scrutinee' rightBranch
        leftWithBi)
      (Step.parStarWithBi.eitherMatch_cong_right scrutinee' leftBranch'
        rightWithBi))

/-- Paired single-position `idJ` congruence on base-case. -/
theorem Step.parStarWithBi.idJ_cong_base
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    {baseCase baseCase' : Term ctx resultType}
    (witness : Term ctx (Ty.id carrier leftEnd rightEnd))
    (baseWithBi : Step.parStarWithBi baseCase baseCase') :
    Step.parStarWithBi (Term.idJ baseCase witness)
                       (Term.idJ baseCase' witness) := by
  induction baseWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.idJ firstBi (Step.par.isBi.refl witness)) restIH

/-- Paired single-position `idJ` congruence on witness. -/
theorem Step.parStarWithBi.idJ_cong_witness
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    (baseCase : Term ctx resultType)
    {witness witness' : Term ctx (Ty.id carrier leftEnd rightEnd)}
    (witnessWithBi : Step.parStarWithBi witness witness') :
    Step.parStarWithBi (Term.idJ baseCase witness)
                       (Term.idJ baseCase witness') := by
  induction witnessWithBi with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restWithBi restIH =>
      exact Step.parStarWithBi.trans
        (Step.par.isBi.idJ (Step.par.isBi.refl baseCase) firstBi) restIH

/-- Paired two-leg `idJ` congruence. -/
theorem Step.parStarWithBi.idJ_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    {baseCase baseCase' : Term ctx resultType}
    {witness witness' : Term ctx (Ty.id carrier leftEnd rightEnd)}
    (baseWithBi : Step.parStarWithBi baseCase baseCase')
    (witnessWithBi : Step.parStarWithBi witness witness') :
    Step.parStarWithBi (Term.idJ baseCase witness)
                       (Term.idJ baseCase' witness') :=
  Step.parStarWithBi.append
    (Step.parStarWithBi.idJ_cong_base witness baseWithBi)
    (Step.parStarWithBi.idJ_cong_witness baseCase' witnessWithBi)

/-! ## isBi survives more cast variants. -/

/-- `Step.par.isBi` survives a Ty-equality cast on both endpoints. -/
theorem Step.par.isBi.castBoth
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    (typeEquality : sourceType = targetType)
    {beforeTerm afterTerm : Term ctx sourceType}
    {parallelStep : Step.par beforeTerm afterTerm}
    (stepBi : Step.par.isBi parallelStep) :
    Step.par.isBi (Step.par.castBoth typeEquality parallelStep) := by
  cases typeEquality
  exact stepBi

/-- `Step.par.isBi` survives a target-direction syntactic Eq cast. -/
theorem Step.par.isBi.castTarget
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {beforeTerm afterTerm afterTerm' : Term ctx termType}
    (targetEquality : afterTerm = afterTerm')
    {parallelStep : Step.par beforeTerm afterTerm}
    (stepBi : Step.par.isBi parallelStep) :
    Step.par.isBi (Step.par.castTarget targetEquality parallelStep) := by
  cases targetEquality
  exact stepBi

/-- `Step.par.isBi` survives a source-direction syntactic Eq cast. -/
theorem Step.par.isBi.castSource
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {beforeTerm beforeTerm' afterTerm : Term ctx termType}
    (sourceEquality : beforeTerm = beforeTerm')
    {parallelStep : Step.par beforeTerm afterTerm}
    (stepBi : Step.par.isBi parallelStep) :
    Step.par.isBi (Step.par.castSource sourceEquality parallelStep) := by
  cases sourceEquality
  exact stepBi

end LeanFX.Syntax

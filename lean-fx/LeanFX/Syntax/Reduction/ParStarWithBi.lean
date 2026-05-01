import LeanFX.Syntax.Reduction.ParBi
import LeanFX.Syntax.Reduction.ParInversion
import LeanFX.Syntax.Reduction.CdDominatesIsBi

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

/-! ## Single-step paired target inversions.

Strengthened versions of `Step.par.lam_target_inv_isBi`,
`Step.par.lamPi_target_inv_isBi`, and
`Step.par.pair_target_inv_isBi` that pair the inner Step.par with
its isBi witness as a single-step `Step.parWithBi`.  Built by
copying the existing inductions on `Step.par.isBi` but retaining
the `_bodyBi` / `_pairFirstBi` / `_pairSecondBi` hypotheses
instead of discarding them. -/

/-- Generalized single-step lam target inversion that retains the
sub-step's isBi witness. -/
theorem Step.par.lam_target_inv_with_bi_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body : Term (ctx.cons domainType) codomainType.weaken}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    (typeEq : termType = Ty.arrow domainType codomainType)
    {parStep : Step.par sourceTerm targetTerm}
    (stepBi : Step.par.isBi parStep) :
    HEq sourceTerm
        (@Term.lam mode level scope ctx domainType codomainType body) →
    ∃ (body' : Term (ctx.cons domainType) codomainType.weaken),
        HEq targetTerm
            (@Term.lam mode level scope ctx domainType codomainType body') ∧
        Step.parWithBi body body' := by
  induction stepBi with
  | refl term =>
      intro sourceHEq
      exact ⟨body, sourceHEq,
             Step.parWithBi.mk (Step.par.refl body) (Step.par.isBi.refl body)⟩
  | lam bodyBi _bodyIH =>
      intro sourceHEq
      cases typeEq
      cases (eq_of_heq sourceHEq)
      rename_i bodyStep
      exact ⟨_, HEq.rfl, Step.parWithBi.mk bodyStep bodyBi⟩
  | lamPi _bodyBi _bodyIH =>
      intro _
      cases typeEq
  | _ =>
      intro sourceHEq
      exfalso
      first
        | (cases typeEq; cases (eq_of_heq sourceHEq))
        | (apply refuteViaToRaw _ (Term.lam body) typeEq sourceHEq;
           intro h; simp only [Term.toRaw] at h; cases h)

/-- Single-step lam target inversion with isBi witness. -/
theorem Step.par.lam_target_inv_with_bi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body : Term (ctx.cons domainType) codomainType.weaken}
    {target : Term ctx (Ty.arrow domainType codomainType)}
    {parStep : Step.par
        (@Term.lam mode level scope ctx domainType codomainType body) target}
    (stepBi : Step.par.isBi parStep) :
    ∃ (body' : Term (ctx.cons domainType) codomainType.weaken),
        target = Term.lam body' ∧ Step.parWithBi body body' := by
  obtain ⟨body', targetHEq, innerWithBi⟩ :=
    Step.par.lam_target_inv_with_bi_general rfl stepBi HEq.rfl
  exact ⟨body', eq_of_heq targetHEq, innerWithBi⟩

/-- Generalized single-step Π-binder target inversion with isBi
witness. -/
theorem Step.par.lamPi_target_inv_with_bi_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body : Term (ctx.cons domainType) codomainType}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    (typeEq : termType = Ty.piTy domainType codomainType)
    {parStep : Step.par sourceTerm targetTerm}
    (stepBi : Step.par.isBi parStep) :
    HEq sourceTerm
        (@Term.lamPi mode level scope ctx domainType codomainType body) →
    ∃ (body' : Term (ctx.cons domainType) codomainType),
        HEq targetTerm
            (@Term.lamPi mode level scope ctx domainType codomainType body') ∧
        Step.parWithBi body body' := by
  induction stepBi with
  | refl term =>
      intro sourceHEq
      exact ⟨body, sourceHEq,
             Step.parWithBi.mk (Step.par.refl body) (Step.par.isBi.refl body)⟩
  | lamPi bodyBi _bodyIH =>
      intro sourceHEq
      cases typeEq
      cases (eq_of_heq sourceHEq)
      rename_i bodyStep
      exact ⟨_, HEq.rfl, Step.parWithBi.mk bodyStep bodyBi⟩
  | lam _bodyBi _bodyIH =>
      intro _
      cases typeEq
  | _ =>
      intro sourceHEq
      exfalso
      first
        | (cases typeEq; cases (eq_of_heq sourceHEq))
        | (apply refuteViaToRaw _ (Term.lamPi body) typeEq sourceHEq;
           intro h; simp only [Term.toRaw] at h; cases h)

/-- Single-step Π-binder target inversion with isBi witness. -/
theorem Step.par.lamPi_target_inv_with_bi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body : Term (ctx.cons domainType) codomainType}
    {target : Term ctx (Ty.piTy domainType codomainType)}
    {parStep : Step.par
        (@Term.lamPi mode level scope ctx domainType codomainType body) target}
    (stepBi : Step.par.isBi parStep) :
    ∃ (body' : Term (ctx.cons domainType) codomainType),
        target = Term.lamPi body' ∧ Step.parWithBi body body' := by
  obtain ⟨body', targetHEq, innerWithBi⟩ :=
    Step.par.lamPi_target_inv_with_bi_general rfl stepBi HEq.rfl
  exact ⟨body', eq_of_heq targetHEq, innerWithBi⟩

/-- Generalized single-step pair target inversion with isBi witnesses
on both first and second components. -/
theorem Step.par.pair_target_inv_with_bi_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal : Term ctx firstType}
    {secondVal : Term ctx (secondType.subst0 firstType)}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    (typeEq : termType = Ty.sigmaTy firstType secondType)
    {parStep : Step.par sourceTerm targetTerm}
    (stepBi : Step.par.isBi parStep) :
    HEq sourceTerm
        (@Term.pair mode level scope ctx firstType secondType
            firstVal secondVal) →
    ∃ (firstVal' : Term ctx firstType)
      (secondVal' : Term ctx (secondType.subst0 firstType)),
        HEq targetTerm
            (@Term.pair mode level scope ctx firstType secondType
                firstVal' secondVal') ∧
        Step.parWithBi firstVal firstVal' ∧
        Step.parWithBi secondVal secondVal' := by
  induction stepBi with
  | refl term =>
      intro sourceHEq
      exact ⟨firstVal, secondVal, sourceHEq,
             Step.parWithBi.mk (Step.par.refl firstVal)
               (Step.par.isBi.refl firstVal),
             Step.parWithBi.mk (Step.par.refl secondVal)
               (Step.par.isBi.refl secondVal)⟩
  | pair firstBi secondBi _firstIH _secondIH =>
      intro sourceHEq
      cases typeEq
      cases (eq_of_heq sourceHEq)
      rename_i firstStep secondStep
      exact ⟨_, _, HEq.rfl,
             Step.parWithBi.mk firstStep firstBi,
             Step.parWithBi.mk secondStep secondBi⟩
  | _ =>
      intro sourceHEq
      exfalso
      first
        | (cases typeEq; cases (eq_of_heq sourceHEq))
        | (apply refuteViaToRaw _ (Term.pair firstVal secondVal)
              typeEq sourceHEq;
           intro h; simp only [Term.toRaw] at h; cases h)

/-- Single-step pair target inversion with isBi witnesses. -/
theorem Step.par.pair_target_inv_with_bi
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal : Term ctx firstType}
    {secondVal : Term ctx (secondType.subst0 firstType)}
    {target : Term ctx (Ty.sigmaTy firstType secondType)}
    {parStep : Step.par
        (@Term.pair mode level scope ctx firstType secondType
            firstVal secondVal) target}
    (stepBi : Step.par.isBi parStep) :
    ∃ (firstVal' : Term ctx firstType)
      (secondVal' : Term ctx (secondType.subst0 firstType)),
        target = Term.pair firstVal' secondVal' ∧
        Step.parWithBi firstVal firstVal' ∧
        Step.parWithBi secondVal secondVal' := by
  obtain ⟨firstVal', secondVal', targetHEq, firstWithBi, secondWithBi⟩ :=
    Step.par.pair_target_inv_with_bi_general rfl stepBi HEq.rfl
  exact ⟨firstVal', secondVal', eq_of_heq targetHEq,
         firstWithBi, secondWithBi⟩

/-! ## Chain-level paired target inversions.

The chain-level versions induct on `parStarWithBi` directly,
threading the per-link isBi witness through both the chain
construction and the body's parStarWithBi result.  Each `trans`
arm uses the corresponding single-step paired inversion to peel
one link, then recurses on the rest. -/

/-- Generalized chain lam target inversion (paired). -/
theorem Step.parStarWithBi.lam_target_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    (typeEq : termType = Ty.arrow domainType codomainType)
    (chainPair : Step.parStarWithBi sourceTerm targetTerm) :
    ∀ (body : Term (ctx.cons domainType) codomainType.weaken),
    HEq sourceTerm
        (@Term.lam mode level scope ctx domainType codomainType body) →
    ∃ (body' : Term (ctx.cons domainType) codomainType.weaken),
        HEq targetTerm
            (@Term.lam mode level scope ctx domainType codomainType body') ∧
        Step.parStarWithBi body body' := by
  induction chainPair with
  | refl term =>
      intro body sourceHEq
      exact ⟨body, sourceHEq, Step.parStarWithBi.refl body⟩
  | trans firstBi _restPair restIH =>
      intro body sourceHEq
      obtain ⟨bodyMid, midHEq, midWithBi⟩ :=
        Step.par.lam_target_inv_with_bi_general typeEq firstBi sourceHEq
      obtain ⟨body', targetHEq, restWithBi⟩ :=
        restIH bodyMid midHEq
      exact ⟨body', targetHEq,
             Step.parStarWithBi.trans midWithBi.toIsBi restWithBi⟩

/-- Chain lam target inversion (paired). -/
theorem Step.parStarWithBi.lam_target_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body : Term (ctx.cons domainType) codomainType.weaken}
    {target : Term ctx (Ty.arrow domainType codomainType)}
    (chainPair : Step.parStarWithBi
        (@Term.lam mode level scope ctx domainType codomainType body) target) :
    ∃ (body' : Term (ctx.cons domainType) codomainType.weaken),
        target = Term.lam body' ∧ Step.parStarWithBi body body' := by
  obtain ⟨body', targetHEq, innerPair⟩ :=
    Step.parStarWithBi.lam_target_inv_general (chainPair := chainPair)
      rfl body HEq.rfl
  exact ⟨body', eq_of_heq targetHEq, innerPair⟩

/-- Generalized chain Π-binder target inversion (paired). -/
theorem Step.parStarWithBi.lamPi_target_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    (typeEq : termType = Ty.piTy domainType codomainType)
    (chainPair : Step.parStarWithBi sourceTerm targetTerm) :
    ∀ (body : Term (ctx.cons domainType) codomainType),
    HEq sourceTerm
        (@Term.lamPi mode level scope ctx domainType codomainType body) →
    ∃ (body' : Term (ctx.cons domainType) codomainType),
        HEq targetTerm
            (@Term.lamPi mode level scope ctx domainType codomainType body') ∧
        Step.parStarWithBi body body' := by
  induction chainPair with
  | refl term =>
      intro body sourceHEq
      exact ⟨body, sourceHEq, Step.parStarWithBi.refl body⟩
  | trans firstBi _restPair restIH =>
      intro body sourceHEq
      obtain ⟨bodyMid, midHEq, midWithBi⟩ :=
        Step.par.lamPi_target_inv_with_bi_general typeEq firstBi sourceHEq
      obtain ⟨body', targetHEq, restWithBi⟩ :=
        restIH bodyMid midHEq
      exact ⟨body', targetHEq,
             Step.parStarWithBi.trans midWithBi.toIsBi restWithBi⟩

/-- Chain Π-binder target inversion (paired). -/
theorem Step.parStarWithBi.lamPi_target_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body : Term (ctx.cons domainType) codomainType}
    {target : Term ctx (Ty.piTy domainType codomainType)}
    (chainPair : Step.parStarWithBi
        (@Term.lamPi mode level scope ctx domainType codomainType body) target) :
    ∃ (body' : Term (ctx.cons domainType) codomainType),
        target = Term.lamPi body' ∧ Step.parStarWithBi body body' := by
  obtain ⟨body', targetHEq, innerPair⟩ :=
    Step.parStarWithBi.lamPi_target_inv_general (chainPair := chainPair)
      rfl body HEq.rfl
  exact ⟨body', eq_of_heq targetHEq, innerPair⟩

/-- Generalized chain pair target inversion (paired). -/
theorem Step.parStarWithBi.pair_target_inv_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {termType : Ty level scope}
    {sourceTerm targetTerm : Term ctx termType}
    (typeEq : termType = Ty.sigmaTy firstType secondType)
    (chainPair : Step.parStarWithBi sourceTerm targetTerm) :
    ∀ (firstVal : Term ctx firstType)
      (secondVal : Term ctx (secondType.subst0 firstType)),
    HEq sourceTerm
        (@Term.pair mode level scope ctx firstType secondType
            firstVal secondVal) →
    ∃ (firstVal' : Term ctx firstType)
      (secondVal' : Term ctx (secondType.subst0 firstType)),
        HEq targetTerm
            (@Term.pair mode level scope ctx firstType secondType
                firstVal' secondVal') ∧
        Step.parStarWithBi firstVal firstVal' ∧
        Step.parStarWithBi secondVal secondVal' := by
  induction chainPair with
  | refl term =>
      intro firstVal secondVal sourceHEq
      exact ⟨firstVal, secondVal, sourceHEq,
             Step.parStarWithBi.refl firstVal,
             Step.parStarWithBi.refl secondVal⟩
  | trans firstBi _restPair restIH =>
      intro firstVal secondVal sourceHEq
      obtain ⟨firstMid, secondMid, midHEq, firstMidWithBi, secondMidWithBi⟩ :=
        Step.par.pair_target_inv_with_bi_general typeEq firstBi sourceHEq
      obtain ⟨firstVal', secondVal', targetHEq, firstRestWithBi, secondRestWithBi⟩ :=
        restIH firstMid secondMid midHEq
      exact ⟨firstVal', secondVal', targetHEq,
             Step.parStarWithBi.trans firstMidWithBi.toIsBi firstRestWithBi,
             Step.parStarWithBi.trans secondMidWithBi.toIsBi secondRestWithBi⟩

/-- Chain pair target inversion (paired). -/
theorem Step.parStarWithBi.pair_target_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal : Term ctx firstType}
    {secondVal : Term ctx (secondType.subst0 firstType)}
    {target : Term ctx (Ty.sigmaTy firstType secondType)}
    (chainPair : Step.parStarWithBi
        (@Term.pair mode level scope ctx firstType secondType
            firstVal secondVal) target) :
    ∃ (firstVal' : Term ctx firstType)
      (secondVal' : Term ctx (secondType.subst0 firstType)),
        target = Term.pair firstVal' secondVal' ∧
        Step.parStarWithBi firstVal firstVal' ∧
        Step.parStarWithBi secondVal secondVal' := by
  obtain ⟨firstVal', secondVal', targetHEq, firstWithBi, secondWithBi⟩ :=
    Step.parStarWithBi.pair_target_inv_general (chainPair := chainPair)
      rfl firstVal secondVal HEq.rfl
  exact ⟨firstVal', secondVal', eq_of_heq targetHEq,
         firstWithBi, secondWithBi⟩

/-! ## β-workhorse smoke: subst_compatible preserves isBi (refl case only).

Sanity-check the proof-irrelevance route to `subst_compatible_isBi`:
since `Step.par` lives in `Prop` and Lean 4 has definitional proof
irrelevance, `Step.par.isBi (Step.par.subst_compatible σ parStep)`
and `Step.par.isBi (any-other-Step.par-proof)` are the same type
whenever the underlying `Step.par a b` proposition matches.  This
means the 54-case proof can construct a *fresh* isBi witness at
each case via the corresponding constructor, and Lean will defEq-
align it with whatever opaque `subst_compatible` returned. -/

/-- **β-workhorse for the typed `cd_lemma_star_with_bi` aggregator.**
A `Step.parWithBi` (paired Step.par + isBi witness) commutes with
`Term.subst`.  Given an isBi-witnessed parallel step on `before`
and `after`, produces an isBi-witnessed parallel step on their
substitutions.

Implementation: induct on the underlying `isBi` witness.  At each
case, construct a *fresh* `Step.parWithBi` on the substituted
endpoints — by choosing both the underlying Step.par step and its
isBi witness ourselves, we sidestep the opaqueness of
`Step.par.subst_compatible` entirely.  The result type
`Step.parWithBi (subst σ a) (subst σ b)` only constrains the
endpoint Terms, not the inner step structure, so Lean only
needs to verify each constructor's *types* match, which the same
`Step.par.castBoth` / `Step.par.castSource` / `Step.par.castTarget`
casts as the original `subst_compatible` proof discharge.  The
isBi side rides along via the matching `Step.par.isBi.cast*` and
constructor witnesses.

Used by the parStarWithBi-valued chain workhorse
`subst_compatible_parStarWithBi` and downstream
`cd_lemma_star_with_bi` aggregator. -/
theorem Step.parWithBi.subst_compatible
    {mode : Mode} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    (termSubstitution : TermSubst sourceCtx targetCtx typeSubstitution)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType}
    {parPaired : Step.parWithBi beforeTerm afterTerm} :
    Step.parWithBi
      (Term.subst termSubstitution beforeTerm)
      (Term.subst termSubstitution afterTerm) := by
  obtain ⟨parallelStep, biWitness⟩ := parPaired
  induction biWitness generalizing targetScope targetCtx with
  | refl term =>
      exact Step.parWithBi.mk (Step.par.refl _) (Step.par.isBi.refl _)
  | app _functionBi _argumentBi functionIH argumentIH =>
      obtain ⟨fStep, fBi⟩ := functionIH termSubstitution
      obtain ⟨aStep, aBi⟩ := argumentIH termSubstitution
      exact Step.parWithBi.mk (Step.par.app fStep aStep)
                              (Step.par.isBi.app fBi aBi)
  | lam _bodyBi bodyIH =>
      rename_i domainType codomainType _ _ _
      obtain ⟨bStep, bBi⟩ := bodyIH (TermSubst.lift termSubstitution domainType)
      let castedStep := Step.par.castBoth
        (Ty.subst_weaken_commute codomainType typeSubstitution) bStep
      let castedBi := Step.par.isBi.castBoth
        (Ty.subst_weaken_commute codomainType typeSubstitution) bBi
      exact Step.parWithBi.mk
        (Step.par.lam castedStep) (Step.par.isBi.lam castedBi)
  | lamPi _bodyBi bodyIH =>
      rename_i domainType _ _ _ _
      obtain ⟨bStep, bBi⟩ := bodyIH (TermSubst.lift termSubstitution domainType)
      exact Step.parWithBi.mk
        (Step.par.lamPi bStep) (Step.par.isBi.lamPi bBi)
  | appPi _functionBi _argumentBi functionIH argumentIH =>
      rename_i domainType codomainType _ _ _ _ _ _
      obtain ⟨fStep, fBi⟩ := functionIH termSubstitution
      obtain ⟨aStep, aBi⟩ := argumentIH termSubstitution
      let typeEq :=
        (Ty.subst0_subst_commute codomainType domainType typeSubstitution).symm
      exact Step.parWithBi.mk
        (Step.par.castBoth typeEq (Step.par.appPi fStep aStep))
        (Step.par.isBi.castBoth typeEq (Step.par.isBi.appPi fBi aBi))
  | pair _firstBi _secondBi firstIH secondIH =>
      rename_i firstType secondType _ _ _ _ _ _
      obtain ⟨fStep, fBi⟩ := firstIH termSubstitution
      obtain ⟨sStep, sBi⟩ := secondIH termSubstitution
      let typeEq :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      exact Step.parWithBi.mk
        (Step.par.pair fStep (Step.par.castBoth typeEq sStep))
        (Step.par.isBi.pair fBi (Step.par.isBi.castBoth typeEq sBi))
  | fst _pairBi pairIH =>
      obtain ⟨pStep, pBi⟩ := pairIH termSubstitution
      exact Step.parWithBi.mk (Step.par.fst pStep) (Step.par.isBi.fst pBi)
  | snd _pairBi pairIH =>
      rename_i firstType secondType _ _ _
      obtain ⟨pStep, pBi⟩ := pairIH termSubstitution
      let typeEq :=
        (Ty.subst0_subst_commute secondType firstType typeSubstitution).symm
      exact Step.parWithBi.mk
        (Step.par.castBoth typeEq (Step.par.snd pStep))
        (Step.par.isBi.castBoth typeEq (Step.par.isBi.snd pBi))
  | boolElim _scrutBi _thenBi _elseBi scrutIH thenIH elseIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨tStep, tBi⟩ := thenIH termSubstitution
      obtain ⟨eStep, eBi⟩ := elseIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.boolElim sStep tStep eStep)
        (Step.par.isBi.boolElim sBi tBi eBi)
  | betaApp _bodyBi _argBi bodyIH argIH =>
      -- Endpoints match what subst_compatible.betaApp returns; reuse
      -- the existing typed-step output for both Step.par and isBi via
      -- subst_compatible (gives the same Prop as the goal here, by
      -- proof irrelevance) and `subst_compatible_isBi`'s sibling: for
      -- now, defer to the existing subst_compatible to get the step,
      -- then re-prove isBi by inducting on the step's structure.
      sorry
  | betaAppPi _bodyBi _argBi bodyIH argIH =>
      sorry
  | betaFstPair _firstBi firstIH =>
      -- TODO: rename_i ordering; same shape as subst_compatible.betaFstPair
      sorry
  | betaSndPair _secondBi secondIH =>
      sorry
  | iotaBoolElimTrue elseBranch _thenBi thenIH =>
      obtain ⟨tStep, tBi⟩ := thenIH termSubstitution
      let elseSubst := Term.subst termSubstitution elseBranch
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimTrue elseSubst tStep)
        (Step.par.isBi.iotaBoolElimTrue elseSubst tBi)
  | iotaBoolElimFalse thenBranch _elseBi elseIH =>
      obtain ⟨eStep, eBi⟩ := elseIH termSubstitution
      let thenSubst := Term.subst termSubstitution thenBranch
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimFalse thenSubst eStep)
        (Step.par.isBi.iotaBoolElimFalse thenSubst eBi)
  | natSucc _predBi predIH =>
      obtain ⟨pStep, pBi⟩ := predIH termSubstitution
      exact Step.parWithBi.mk (Step.par.natSucc pStep)
                              (Step.par.isBi.natSucc pBi)
  | natElim _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨zStep, zBi⟩ := zeroIH termSubstitution
      obtain ⟨ssStep, ssBi⟩ := succIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.natElim sStep zStep ssStep)
        (Step.par.isBi.natElim sBi zBi ssBi)
  | iotaNatElimZero succBranch _zeroBi zeroIH =>
      obtain ⟨zStep, zBi⟩ := zeroIH termSubstitution
      let succSubst := Term.subst termSubstitution succBranch
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimZero succSubst zStep)
        (Step.par.isBi.iotaNatElimZero succSubst zBi)
  | natRec _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨zStep, zBi⟩ := zeroIH termSubstitution
      obtain ⟨ssStep, ssBi⟩ := succIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.natRec sStep zStep ssStep)
        (Step.par.isBi.natRec sBi zBi ssBi)
  | iotaNatRecZero succBranch _zeroBi zeroIH =>
      obtain ⟨zStep, zBi⟩ := zeroIH termSubstitution
      let succSubst := Term.subst termSubstitution succBranch
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecZero succSubst zStep)
        (Step.par.isBi.iotaNatRecZero succSubst zBi)
  | iotaNatRecSucc _predBi _zeroBi _succBi predIH zeroIH succIH =>
      obtain ⟨pStep, pBi⟩ := predIH termSubstitution
      obtain ⟨zStep, zBi⟩ := zeroIH termSubstitution
      obtain ⟨ssStep, ssBi⟩ := succIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecSucc pStep zStep ssStep)
        (Step.par.isBi.iotaNatRecSucc pBi zBi ssBi)
  | iotaNatElimSucc zeroBranch _predBi _succBi predIH succIH =>
      obtain ⟨pStep, pBi⟩ := predIH termSubstitution
      obtain ⟨ssStep, ssBi⟩ := succIH termSubstitution
      let zeroSubst := Term.subst termSubstitution zeroBranch
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimSucc zeroSubst pStep ssStep)
        (Step.par.isBi.iotaNatElimSucc zeroSubst pBi ssBi)
  | listCons _headBi _tailBi headIH tailIH =>
      obtain ⟨hStep, hBi⟩ := headIH termSubstitution
      obtain ⟨tStep, tBi⟩ := tailIH termSubstitution
      exact Step.parWithBi.mk (Step.par.listCons hStep tStep)
                              (Step.par.isBi.listCons hBi tBi)
  | listElim _scrutBi _nilBi _consBi scrutIH nilIH consIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨nStep, nBi⟩ := nilIH termSubstitution
      obtain ⟨cStep, cBi⟩ := consIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.listElim sStep nStep cStep)
        (Step.par.isBi.listElim sBi nBi cBi)
  | iotaListElimNil consBranch _nilBi nilIH =>
      obtain ⟨nStep, nBi⟩ := nilIH termSubstitution
      let consSubst := Term.subst termSubstitution consBranch
      exact Step.parWithBi.mk
        (Step.par.iotaListElimNil consSubst nStep)
        (Step.par.isBi.iotaListElimNil consSubst nBi)
  | iotaListElimCons nilBranch _headBi _tailBi _consBi headIH tailIH consIH =>
      obtain ⟨hStep, hBi⟩ := headIH termSubstitution
      obtain ⟨tStep, tBi⟩ := tailIH termSubstitution
      obtain ⟨cStep, cBi⟩ := consIH termSubstitution
      let nilSubst := Term.subst termSubstitution nilBranch
      exact Step.parWithBi.mk
        (Step.par.iotaListElimCons nilSubst hStep tStep cStep)
        (Step.par.isBi.iotaListElimCons nilSubst hBi tBi cBi)
  | optionSome _valueBi valueIH =>
      obtain ⟨vStep, vBi⟩ := valueIH termSubstitution
      exact Step.parWithBi.mk (Step.par.optionSome vStep)
                              (Step.par.isBi.optionSome vBi)
  | optionMatch _scrutBi _noneBi _someBi scrutIH noneIH someIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨nStep, nBi⟩ := noneIH termSubstitution
      obtain ⟨smStep, smBi⟩ := someIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.optionMatch sStep nStep smStep)
        (Step.par.isBi.optionMatch sBi nBi smBi)
  | iotaOptionMatchNone someBranch _noneBi noneIH =>
      obtain ⟨nStep, nBi⟩ := noneIH termSubstitution
      let someSubst := Term.subst termSubstitution someBranch
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchNone someSubst nStep)
        (Step.par.isBi.iotaOptionMatchNone someSubst nBi)
  | iotaOptionMatchSome noneBranch _valueBi _someBi valueIH someIH =>
      obtain ⟨vStep, vBi⟩ := valueIH termSubstitution
      obtain ⟨smStep, smBi⟩ := someIH termSubstitution
      let noneSubst := Term.subst termSubstitution noneBranch
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchSome noneSubst vStep smStep)
        (Step.par.isBi.iotaOptionMatchSome noneSubst vBi smBi)
  | eitherInl _valueBi valueIH =>
      obtain ⟨vStep, vBi⟩ := valueIH termSubstitution
      exact Step.parWithBi.mk (Step.par.eitherInl vStep)
                              (Step.par.isBi.eitherInl vBi)
  | eitherInr _valueBi valueIH =>
      obtain ⟨vStep, vBi⟩ := valueIH termSubstitution
      exact Step.parWithBi.mk (Step.par.eitherInr vStep)
                              (Step.par.isBi.eitherInr vBi)
  | eitherMatch _scrutBi _leftBi _rightBi scrutIH leftIH rightIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨lStep, lBi⟩ := leftIH termSubstitution
      obtain ⟨rStep, rBi⟩ := rightIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.eitherMatch sStep lStep rStep)
        (Step.par.isBi.eitherMatch sBi lBi rBi)
  | iotaEitherMatchInl rightBranch _valueBi _leftBi valueIH leftIH =>
      obtain ⟨vStep, vBi⟩ := valueIH termSubstitution
      obtain ⟨lStep, lBi⟩ := leftIH termSubstitution
      let rightSubst := Term.subst termSubstitution rightBranch
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInl rightSubst vStep lStep)
        (Step.par.isBi.iotaEitherMatchInl rightSubst vBi lBi)
  | iotaEitherMatchInr leftBranch _valueBi _rightBi valueIH rightIH =>
      obtain ⟨vStep, vBi⟩ := valueIH termSubstitution
      obtain ⟨rStep, rBi⟩ := rightIH termSubstitution
      let leftSubst := Term.subst termSubstitution leftBranch
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInr leftSubst vStep rStep)
        (Step.par.isBi.iotaEitherMatchInr leftSubst vBi rBi)
  | idJ _baseBi _witnessBi baseIH witnessIH =>
      obtain ⟨bStep, bBi⟩ := baseIH termSubstitution
      obtain ⟨wStep, wBi⟩ := witnessIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.idJ bStep wStep)
        (Step.par.isBi.idJ bBi wBi)
  | iotaIdJRefl _baseBi baseIH =>
      obtain ⟨bStep, bBi⟩ := baseIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaIdJRefl bStep)
        (Step.par.isBi.iotaIdJRefl bBi)
  -- Deep cases — same approach + cast bookkeeping for binder/Σ.
  | betaAppDeep _functionBi _argBi functionIH argIH => sorry
  | betaAppPiDeep _functionBi _argBi functionIH argIH => sorry
  | betaFstPairDeep _pairBi pairIH =>
      obtain ⟨pStep, pBi⟩ := pairIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.betaFstPairDeep pStep)
        (Step.par.isBi.betaFstPairDeep pBi)
  | betaSndPairDeep _pairBi pairIH => sorry
  | iotaBoolElimTrueDeep elseBranch _scrutBi _thenBi scrutIH thenIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨tStep, tBi⟩ := thenIH termSubstitution
      let elseSubst := Term.subst termSubstitution elseBranch
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimTrueDeep elseSubst sStep tStep)
        (Step.par.isBi.iotaBoolElimTrueDeep elseSubst sBi tBi)
  | iotaBoolElimFalseDeep thenBranch _scrutBi _elseBi scrutIH elseIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨eStep, eBi⟩ := elseIH termSubstitution
      let thenSubst := Term.subst termSubstitution thenBranch
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimFalseDeep thenSubst sStep eStep)
        (Step.par.isBi.iotaBoolElimFalseDeep thenSubst sBi eBi)
  | iotaNatElimZeroDeep succBranch _scrutBi _zeroBi scrutIH zeroIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨zStep, zBi⟩ := zeroIH termSubstitution
      let succSubst := Term.subst termSubstitution succBranch
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimZeroDeep succSubst sStep zStep)
        (Step.par.isBi.iotaNatElimZeroDeep succSubst sBi zBi)
  | iotaNatElimSuccDeep zeroBranch _scrutBi _succBi scrutIH succIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨ssStep, ssBi⟩ := succIH termSubstitution
      let zeroSubst := Term.subst termSubstitution zeroBranch
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimSuccDeep zeroSubst sStep ssStep)
        (Step.par.isBi.iotaNatElimSuccDeep zeroSubst sBi ssBi)
  | iotaNatRecZeroDeep succBranch _scrutBi _zeroBi scrutIH zeroIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨zStep, zBi⟩ := zeroIH termSubstitution
      let succSubst := Term.subst termSubstitution succBranch
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecZeroDeep succSubst sStep zStep)
        (Step.par.isBi.iotaNatRecZeroDeep succSubst sBi zBi)
  | iotaNatRecSuccDeep _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨zStep, zBi⟩ := zeroIH termSubstitution
      obtain ⟨ssStep, ssBi⟩ := succIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecSuccDeep sStep zStep ssStep)
        (Step.par.isBi.iotaNatRecSuccDeep sBi zBi ssBi)
  | iotaListElimNilDeep consBranch _scrutBi _nilBi scrutIH nilIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨nStep, nBi⟩ := nilIH termSubstitution
      let consSubst := Term.subst termSubstitution consBranch
      exact Step.parWithBi.mk
        (Step.par.iotaListElimNilDeep consSubst sStep nStep)
        (Step.par.isBi.iotaListElimNilDeep consSubst sBi nBi)
  | iotaListElimConsDeep nilBranch _scrutBi _consBi scrutIH consIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨cStep, cBi⟩ := consIH termSubstitution
      let nilSubst := Term.subst termSubstitution nilBranch
      exact Step.parWithBi.mk
        (Step.par.iotaListElimConsDeep nilSubst sStep cStep)
        (Step.par.isBi.iotaListElimConsDeep nilSubst sBi cBi)
  | iotaOptionMatchNoneDeep someBranch _scrutBi _noneBi scrutIH noneIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨nStep, nBi⟩ := noneIH termSubstitution
      let someSubst := Term.subst termSubstitution someBranch
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchNoneDeep someSubst sStep nStep)
        (Step.par.isBi.iotaOptionMatchNoneDeep someSubst sBi nBi)
  | iotaOptionMatchSomeDeep noneBranch _scrutBi _someBi scrutIH someIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨smStep, smBi⟩ := someIH termSubstitution
      let noneSubst := Term.subst termSubstitution noneBranch
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchSomeDeep noneSubst sStep smStep)
        (Step.par.isBi.iotaOptionMatchSomeDeep noneSubst sBi smBi)
  | iotaEitherMatchInlDeep rightBranch _scrutBi _leftBi scrutIH leftIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨lStep, lBi⟩ := leftIH termSubstitution
      let rightSubst := Term.subst termSubstitution rightBranch
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInlDeep rightSubst sStep lStep)
        (Step.par.isBi.iotaEitherMatchInlDeep rightSubst sBi lBi)
  | iotaEitherMatchInrDeep leftBranch _scrutBi _rightBi scrutIH rightIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termSubstitution
      obtain ⟨rStep, rBi⟩ := rightIH termSubstitution
      let leftSubst := Term.subst termSubstitution leftBranch
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInrDeep leftSubst sStep rStep)
        (Step.par.isBi.iotaEitherMatchInrDeep leftSubst sBi rBi)
  | iotaIdJReflDeep _witnessBi _baseBi witnessIH baseIH =>
      obtain ⟨wStep, wBi⟩ := witnessIH termSubstitution
      obtain ⟨bStep, bBi⟩ := baseIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.iotaIdJReflDeep wStep bStep)
        (Step.par.isBi.iotaIdJReflDeep wBi bBi)

end LeanFX.Syntax

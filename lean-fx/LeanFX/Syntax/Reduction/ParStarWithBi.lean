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
`Step.par.isBi.<ctor>` to lift the head step's isBi witness.

For single-position cong rules (the bulk of this section), the
generic `Step.parStarWithBi.mapStep` packages this 4-line
induction, reducing each cong to a 1-line corollary.  Multi-
position cong rules (e.g. `app_cong`) compose two single-position
rules via `Step.parStarWithBi.append`. -/

/-- **Generic `parStarWithBi` lifter**: lift a paired chain through
any term-context-changing function `mapTerm` whose single-step
parallel reduction has both a Step.par lifter (`mapPar`) and a
matching isBi lifter (`mapBi`).  Source and target may live in
different contexts and at different scopes — needed by binder
cong rules whose source body is in `ctx.cons _`.  Reduces every
single-position parStarWithBi cong to a 1-line application. -/
theorem Step.parStarWithBi.mapStep
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sourceType : Ty level sourceScope}
    {targetType : Ty level targetScope}
    (mapTerm : Term sourceCtx sourceType → Term targetCtx targetType)
    (mapPar : ∀ {beforeTerm afterTerm : Term sourceCtx sourceType},
      Step.par beforeTerm afterTerm →
      Step.par (mapTerm beforeTerm) (mapTerm afterTerm))
    (mapBi : ∀ {beforeTerm afterTerm : Term sourceCtx sourceType}
        {parallelStep : Step.par beforeTerm afterTerm},
      Step.par.isBi parallelStep → Step.par.isBi (mapPar parallelStep)) :
    ∀ {beforeTerm afterTerm : Term sourceCtx sourceType},
      Step.parStarWithBi beforeTerm afterTerm →
      Step.parStarWithBi (mapTerm beforeTerm) (mapTerm afterTerm)
  | _, _, .refl _ => Step.parStarWithBi.refl _
  | _, _, .trans firstBi restWithBi =>
      Step.parStarWithBi.trans (mapBi firstBi)
        (Step.parStarWithBi.mapStep mapTerm mapPar mapBi restWithBi)

/-- Paired λ-body congruence. -/
theorem Step.parStarWithBi.lam_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body body' : Term (ctx.cons domainType) codomainType.weaken}
    (bodyChainWithBi : Step.parStarWithBi body body') :
    Step.parStarWithBi
      (Term.lam (codomainType := codomainType) body)
      (Term.lam (codomainType := codomainType) body') :=
  Step.parStarWithBi.mapStep (Term.lam (codomainType := codomainType))
    Step.par.lam Step.par.isBi.lam bodyChainWithBi

/-- Paired Π-λ-body congruence. -/
theorem Step.parStarWithBi.lamPi_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body body' : Term (ctx.cons domainType) codomainType}
    (bodyChainWithBi : Step.parStarWithBi body body') :
    Step.parStarWithBi
      (Term.lamPi (domainType := domainType) body)
      (Term.lamPi (domainType := domainType) body') :=
  Step.parStarWithBi.mapStep (Term.lamPi (domainType := domainType))
    Step.par.lamPi Step.par.isBi.lamPi bodyChainWithBi

/-- Paired single-position `app` congruence on function. -/
theorem Step.parStarWithBi.app_cong_function
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionTerm functionTerm' : Term ctx (Ty.arrow domainType codomainType)}
    (argumentTerm : Term ctx domainType)
    (functionWithBi : Step.parStarWithBi functionTerm functionTerm') :
    Step.parStarWithBi (Term.app functionTerm argumentTerm)
                       (Term.app functionTerm' argumentTerm) :=
  Step.parStarWithBi.mapStep
    (fun fnTerm => Term.app fnTerm argumentTerm)
    (fun fnPar => Step.par.app fnPar (Step.par.refl argumentTerm))
    (fun fnBi => Step.par.isBi.app fnBi (Step.par.isBi.refl argumentTerm))
    functionWithBi

/-- Paired single-position `app` congruence on argument. -/
theorem Step.parStarWithBi.app_cong_argument
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    (functionTerm : Term ctx (Ty.arrow domainType codomainType))
    {argumentTerm argumentTerm' : Term ctx domainType}
    (argumentWithBi : Step.parStarWithBi argumentTerm argumentTerm') :
    Step.parStarWithBi (Term.app functionTerm argumentTerm)
                       (Term.app functionTerm argumentTerm') :=
  Step.parStarWithBi.mapStep
    (fun argTerm => Term.app functionTerm argTerm)
    (fun argPar => Step.par.app (Step.par.refl functionTerm) argPar)
    (fun argBi => Step.par.isBi.app (Step.par.isBi.refl functionTerm) argBi)
    argumentWithBi

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
    Step.parStarWithBi (Term.appPi rfl functionTerm argumentTerm)
                       (Term.appPi rfl functionTerm' argumentTerm) :=
  Step.parStarWithBi.mapStep
    (fun fnTerm => Term.appPi rfl fnTerm argumentTerm)
    (fun fnPar => Step.par.appPi fnPar (Step.par.refl argumentTerm))
    (fun fnBi => Step.par.isBi.appPi fnBi (Step.par.isBi.refl argumentTerm))
    functionWithBi

/-- Paired single-position `appPi` congruence on argument. -/
theorem Step.parStarWithBi.appPi_cong_argument
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    (functionTerm : Term ctx (Ty.piTy domainType codomainType))
    {argumentTerm argumentTerm' : Term ctx domainType}
    (argumentWithBi : Step.parStarWithBi argumentTerm argumentTerm') :
    Step.parStarWithBi (Term.appPi rfl functionTerm argumentTerm)
                       (Term.appPi rfl functionTerm argumentTerm') :=
  Step.parStarWithBi.mapStep
    (fun argTerm => Term.appPi rfl functionTerm argTerm)
    (fun argPar => Step.par.appPi (Step.par.refl functionTerm) argPar)
    (fun argBi => Step.par.isBi.appPi (Step.par.isBi.refl functionTerm) argBi)
    argumentWithBi

/-- Paired dependent application congruence. -/
theorem Step.parStarWithBi.appPi_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {functionTerm functionTerm' : Term ctx (Ty.piTy domainType codomainType)}
    {argumentTerm argumentTerm' : Term ctx domainType}
    (functionWithBi : Step.parStarWithBi functionTerm functionTerm')
    (argumentWithBi : Step.parStarWithBi argumentTerm argumentTerm') :
    Step.parStarWithBi (Term.appPi rfl functionTerm argumentTerm)
                       (Term.appPi rfl functionTerm' argumentTerm') :=
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
                       (Term.pair (secondType := secondType) firstVal' secondVal) :=
  Step.parStarWithBi.mapStep
    (fun firstTerm => Term.pair (secondType := secondType) firstTerm secondVal)
    (fun firstPar => Step.par.pair firstPar (Step.par.refl secondVal))
    (fun firstBi => Step.par.isBi.pair firstBi (Step.par.isBi.refl secondVal))
    firstWithBi

/-- Paired single-position `pair` congruence on second component. -/
theorem Step.parStarWithBi.pair_cong_second
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    (firstVal : Term ctx firstType)
    {secondVal secondVal' : Term ctx (secondType.subst0 firstType)}
    (secondWithBi : Step.parStarWithBi secondVal secondVal') :
    Step.parStarWithBi (Term.pair (secondType := secondType) firstVal secondVal)
                       (Term.pair (secondType := secondType) firstVal secondVal') :=
  Step.parStarWithBi.mapStep
    (fun secondTerm => Term.pair (secondType := secondType) firstVal secondTerm)
    (fun secondPar => Step.par.pair (Step.par.refl firstVal) secondPar)
    (fun secondBi => Step.par.isBi.pair (Step.par.isBi.refl firstVal) secondBi)
    secondWithBi

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
    Step.parStarWithBi (Term.fst pairTerm) (Term.fst pairTerm') :=
  Step.parStarWithBi.mapStep
    (Term.fst (firstType := firstType) (secondType := secondType))
    Step.par.fst Step.par.isBi.fst pairWithBi

/-- Paired second-projection congruence.  W9.B1.2: `Term.snd` requires
`rfl` for resultEq. -/
theorem Step.parStarWithBi.snd_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairTerm pairTerm' : Term ctx (Ty.sigmaTy firstType secondType)}
    (pairWithBi : Step.parStarWithBi pairTerm pairTerm') :
    Step.parStarWithBi (Term.snd pairTerm rfl) (Term.snd pairTerm' rfl) :=
  Step.parStarWithBi.mapStep
    (fun pTerm => Term.snd (firstType := firstType)
      (secondType := secondType) pTerm rfl)
    Step.par.snd Step.par.isBi.snd pairWithBi

/-! ### Eliminator congruence rules (paired). -/

/-- Paired single-position `boolElim` congruence on scrutinee. -/
theorem Step.parStarWithBi.boolElim_cong_scrutinee
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.bool}
    (thenBranch elseBranch : Term ctx resultType)
    (scrutineeWithBi : Step.parStarWithBi scrutinee scrutinee') :
    Step.parStarWithBi (Term.boolElim scrutinee thenBranch elseBranch)
                       (Term.boolElim scrutinee' thenBranch elseBranch) :=
  Step.parStarWithBi.mapStep
    (fun scrutTerm => Term.boolElim scrutTerm thenBranch elseBranch)
    (fun scrutPar => Step.par.boolElim scrutPar
      (Step.par.refl thenBranch) (Step.par.refl elseBranch))
    (fun scrutBi => Step.par.isBi.boolElim scrutBi
      (Step.par.isBi.refl thenBranch) (Step.par.isBi.refl elseBranch))
    scrutineeWithBi

/-- Paired single-position `boolElim` congruence on then-branch. -/
theorem Step.parStarWithBi.boolElim_cong_then
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    {thenBranch thenBranch' : Term ctx resultType}
    (elseBranch : Term ctx resultType)
    (thenWithBi : Step.parStarWithBi thenBranch thenBranch') :
    Step.parStarWithBi (Term.boolElim scrutinee thenBranch elseBranch)
                       (Term.boolElim scrutinee thenBranch' elseBranch) :=
  Step.parStarWithBi.mapStep
    (fun thenTerm => Term.boolElim scrutinee thenTerm elseBranch)
    (fun thenPar => Step.par.boolElim
      (Step.par.refl scrutinee) thenPar (Step.par.refl elseBranch))
    (fun thenBi => Step.par.isBi.boolElim
      (Step.par.isBi.refl scrutinee) thenBi (Step.par.isBi.refl elseBranch))
    thenWithBi

/-- Paired single-position `boolElim` congruence on else-branch. -/
theorem Step.parStarWithBi.boolElim_cong_else
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.bool)
    (thenBranch : Term ctx resultType)
    {elseBranch elseBranch' : Term ctx resultType}
    (elseWithBi : Step.parStarWithBi elseBranch elseBranch') :
    Step.parStarWithBi (Term.boolElim scrutinee thenBranch elseBranch)
                       (Term.boolElim scrutinee thenBranch elseBranch') :=
  Step.parStarWithBi.mapStep
    (fun elseTerm => Term.boolElim scrutinee thenBranch elseTerm)
    (fun elsePar => Step.par.boolElim
      (Step.par.refl scrutinee) (Step.par.refl thenBranch) elsePar)
    (fun elseBi => Step.par.isBi.boolElim
      (Step.par.isBi.refl scrutinee) (Step.par.isBi.refl thenBranch) elseBi)
    elseWithBi

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
    Step.parStarWithBi (Term.natSucc predecessor) (Term.natSucc predecessor') :=
  Step.parStarWithBi.mapStep Term.natSucc Step.par.natSucc Step.par.isBi.natSucc
    predWithBi

/-- Paired single-position `natElim` congruence on scrutinee. -/
theorem Step.parStarWithBi.natElim_cong_scrutinee
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
    (scrutineeWithBi : Step.parStarWithBi scrutinee scrutinee') :
    Step.parStarWithBi (Term.natElim scrutinee zeroBranch succBranch)
                       (Term.natElim scrutinee' zeroBranch succBranch) :=
  Step.parStarWithBi.mapStep
    (fun scrutTerm => Term.natElim scrutTerm zeroBranch succBranch)
    (fun scrutPar => Step.par.natElim scrutPar
      (Step.par.refl zeroBranch) (Step.par.refl succBranch))
    (fun scrutBi => Step.par.isBi.natElim scrutBi
      (Step.par.isBi.refl zeroBranch) (Step.par.isBi.refl succBranch))
    scrutineeWithBi

/-- Paired single-position `natElim` congruence on zero-branch. -/
theorem Step.parStarWithBi.natElim_cong_zero
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    {zeroBranch zeroBranch' : Term ctx resultType}
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
    (zeroWithBi : Step.parStarWithBi zeroBranch zeroBranch') :
    Step.parStarWithBi (Term.natElim scrutinee zeroBranch succBranch)
                       (Term.natElim scrutinee zeroBranch' succBranch) :=
  Step.parStarWithBi.mapStep
    (fun zeroTerm => Term.natElim scrutinee zeroTerm succBranch)
    (fun zeroPar => Step.par.natElim
      (Step.par.refl scrutinee) zeroPar (Step.par.refl succBranch))
    (fun zeroBi => Step.par.isBi.natElim
      (Step.par.isBi.refl scrutinee) zeroBi (Step.par.isBi.refl succBranch))
    zeroWithBi

/-- Paired single-position `natElim` congruence on succ-branch. -/
theorem Step.parStarWithBi.natElim_cong_succ
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term ctx Ty.nat)
    (zeroBranch : Term ctx resultType)
    {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)}
    (succWithBi : Step.parStarWithBi succBranch succBranch') :
    Step.parStarWithBi (Term.natElim scrutinee zeroBranch succBranch)
                       (Term.natElim scrutinee zeroBranch succBranch') :=
  Step.parStarWithBi.mapStep
    (fun succTerm => Term.natElim scrutinee zeroBranch succTerm)
    (fun succPar => Step.par.natElim
      (Step.par.refl scrutinee) (Step.par.refl zeroBranch) succPar)
    (fun succBi => Step.par.isBi.natElim
      (Step.par.isBi.refl scrutinee) (Step.par.isBi.refl zeroBranch) succBi)
    succWithBi

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
                       (Term.natRec scrutinee' zeroBranch succBranch) :=
  Step.parStarWithBi.mapStep
    (fun scrutTerm => Term.natRec scrutTerm zeroBranch succBranch)
    (fun scrutPar => Step.par.natRec scrutPar
      (Step.par.refl zeroBranch) (Step.par.refl succBranch))
    (fun scrutBi => Step.par.isBi.natRec scrutBi
      (Step.par.isBi.refl zeroBranch) (Step.par.isBi.refl succBranch))
    scrutineeWithBi

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
                       (Term.natRec scrutinee zeroBranch' succBranch) :=
  Step.parStarWithBi.mapStep
    (fun zeroTerm => Term.natRec scrutinee zeroTerm succBranch)
    (fun zeroPar => Step.par.natRec
      (Step.par.refl scrutinee) zeroPar (Step.par.refl succBranch))
    (fun zeroBi => Step.par.isBi.natRec
      (Step.par.isBi.refl scrutinee) zeroBi (Step.par.isBi.refl succBranch))
    zeroWithBi

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
                       (Term.natRec scrutinee zeroBranch succBranch') :=
  Step.parStarWithBi.mapStep
    (fun succTerm => Term.natRec scrutinee zeroBranch succTerm)
    (fun succPar => Step.par.natRec
      (Step.par.refl scrutinee) (Step.par.refl zeroBranch) succPar)
    (fun succBi => Step.par.isBi.natRec
      (Step.par.isBi.refl scrutinee) (Step.par.isBi.refl zeroBranch) succBi)
    succWithBi

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
    Step.parStarWithBi (Term.listCons head tail) (Term.listCons head' tail) :=
  Step.parStarWithBi.mapStep
    (fun headTerm => Term.listCons headTerm tail)
    (fun headPar => Step.par.listCons headPar (Step.par.refl tail))
    (fun headBi => Step.par.isBi.listCons headBi (Step.par.isBi.refl tail))
    headWithBi

/-- Paired single-position `listCons` congruence on tail. -/
theorem Step.parStarWithBi.listCons_cong_tail
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    (head : Term ctx elementType)
    {tail tail' : Term ctx (Ty.list elementType)}
    (tailWithBi : Step.parStarWithBi tail tail') :
    Step.parStarWithBi (Term.listCons head tail) (Term.listCons head tail') :=
  Step.parStarWithBi.mapStep
    (fun tailTerm => Term.listCons head tailTerm)
    (fun tailPar => Step.par.listCons (Step.par.refl head) tailPar)
    (fun tailBi => Step.par.isBi.listCons (Step.par.isBi.refl head) tailBi)
    tailWithBi

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
                       (Term.listElim scrutinee' nilBranch consBranch) :=
  Step.parStarWithBi.mapStep
    (fun scrutTerm => Term.listElim scrutTerm nilBranch consBranch)
    (fun scrutPar => Step.par.listElim scrutPar
      (Step.par.refl nilBranch) (Step.par.refl consBranch))
    (fun scrutBi => Step.par.isBi.listElim scrutBi
      (Step.par.isBi.refl nilBranch) (Step.par.isBi.refl consBranch))
    scrutineeWithBi

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
                       (Term.listElim scrutinee nilBranch' consBranch) :=
  Step.parStarWithBi.mapStep
    (fun nilTerm => Term.listElim scrutinee nilTerm consBranch)
    (fun nilPar => Step.par.listElim
      (Step.par.refl scrutinee) nilPar (Step.par.refl consBranch))
    (fun nilBi => Step.par.isBi.listElim
      (Step.par.isBi.refl scrutinee) nilBi (Step.par.isBi.refl consBranch))
    nilWithBi

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
                       (Term.listElim scrutinee nilBranch consBranch') :=
  Step.parStarWithBi.mapStep
    (fun consTerm => Term.listElim scrutinee nilBranch consTerm)
    (fun consPar => Step.par.listElim
      (Step.par.refl scrutinee) (Step.par.refl nilBranch) consPar)
    (fun consBi => Step.par.isBi.listElim
      (Step.par.isBi.refl scrutinee) (Step.par.isBi.refl nilBranch) consBi)
    consWithBi

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
    Step.parStarWithBi (Term.optionSome value) (Term.optionSome value') :=
  Step.parStarWithBi.mapStep Term.optionSome
    Step.par.optionSome Step.par.isBi.optionSome valueWithBi

/-- Paired single-position `optionMatch` congruence on scrutinee. -/
theorem Step.parStarWithBi.optionMatch_cong_scrutinee
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.option elementType)}
    (noneBranch : Term ctx resultType)
    (someBranch : Term ctx (Ty.arrow elementType resultType))
    (scrutineeWithBi : Step.parStarWithBi scrutinee scrutinee') :
    Step.parStarWithBi (Term.optionMatch scrutinee noneBranch someBranch)
                       (Term.optionMatch scrutinee' noneBranch someBranch) :=
  Step.parStarWithBi.mapStep
    (fun scrutTerm => Term.optionMatch scrutTerm noneBranch someBranch)
    (fun scrutPar => Step.par.optionMatch scrutPar
      (Step.par.refl noneBranch) (Step.par.refl someBranch))
    (fun scrutBi => Step.par.isBi.optionMatch scrutBi
      (Step.par.isBi.refl noneBranch) (Step.par.isBi.refl someBranch))
    scrutineeWithBi

/-- Paired single-position `optionMatch` congruence on none-branch. -/
theorem Step.parStarWithBi.optionMatch_cong_none
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    {noneBranch noneBranch' : Term ctx resultType}
    (someBranch : Term ctx (Ty.arrow elementType resultType))
    (noneWithBi : Step.parStarWithBi noneBranch noneBranch') :
    Step.parStarWithBi (Term.optionMatch scrutinee noneBranch someBranch)
                       (Term.optionMatch scrutinee noneBranch' someBranch) :=
  Step.parStarWithBi.mapStep
    (fun noneTerm => Term.optionMatch scrutinee noneTerm someBranch)
    (fun nonePar => Step.par.optionMatch
      (Step.par.refl scrutinee) nonePar (Step.par.refl someBranch))
    (fun noneBi => Step.par.isBi.optionMatch
      (Step.par.isBi.refl scrutinee) noneBi (Step.par.isBi.refl someBranch))
    noneWithBi

/-- Paired single-position `optionMatch` congruence on some-branch. -/
theorem Step.parStarWithBi.optionMatch_cong_some
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.option elementType))
    (noneBranch : Term ctx resultType)
    {someBranch someBranch' : Term ctx (Ty.arrow elementType resultType)}
    (someWithBi : Step.parStarWithBi someBranch someBranch') :
    Step.parStarWithBi (Term.optionMatch scrutinee noneBranch someBranch)
                       (Term.optionMatch scrutinee noneBranch someBranch') :=
  Step.parStarWithBi.mapStep
    (fun someTerm => Term.optionMatch scrutinee noneBranch someTerm)
    (fun somePar => Step.par.optionMatch
      (Step.par.refl scrutinee) (Step.par.refl noneBranch) somePar)
    (fun someBi => Step.par.isBi.optionMatch
      (Step.par.isBi.refl scrutinee) (Step.par.isBi.refl noneBranch) someBi)
    someWithBi

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
                       (Term.eitherInl (rightType := rightType) value') :=
  Step.parStarWithBi.mapStep (Term.eitherInl (rightType := rightType))
    Step.par.eitherInl Step.par.isBi.eitherInl valueWithBi

/-- Paired `eitherInr` congruence. -/
theorem Step.parStarWithBi.eitherInr_cong
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value value' : Term ctx rightType}
    (valueWithBi : Step.parStarWithBi value value') :
    Step.parStarWithBi (Term.eitherInr (leftType := leftType) value)
                       (Term.eitherInr (leftType := leftType) value') :=
  Step.parStarWithBi.mapStep (Term.eitherInr (leftType := leftType))
    Step.par.eitherInr Step.par.isBi.eitherInr valueWithBi

/-- Paired single-position `eitherMatch` congruence on scrutinee. -/
theorem Step.parStarWithBi.eitherMatch_cong_scrutinee
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.either leftType rightType)}
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    (rightBranch : Term ctx (Ty.arrow rightType resultType))
    (scrutineeWithBi : Step.parStarWithBi scrutinee scrutinee') :
    Step.parStarWithBi (Term.eitherMatch scrutinee leftBranch rightBranch)
                       (Term.eitherMatch scrutinee' leftBranch rightBranch) :=
  Step.parStarWithBi.mapStep
    (fun scrutTerm => Term.eitherMatch scrutTerm leftBranch rightBranch)
    (fun scrutPar => Step.par.eitherMatch scrutPar
      (Step.par.refl leftBranch) (Step.par.refl rightBranch))
    (fun scrutBi => Step.par.isBi.eitherMatch scrutBi
      (Step.par.isBi.refl leftBranch) (Step.par.isBi.refl rightBranch))
    scrutineeWithBi

/-- Paired single-position `eitherMatch` congruence on left-branch. -/
theorem Step.parStarWithBi.eitherMatch_cong_left
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    {leftBranch leftBranch' : Term ctx (Ty.arrow leftType resultType)}
    (rightBranch : Term ctx (Ty.arrow rightType resultType))
    (leftWithBi : Step.parStarWithBi leftBranch leftBranch') :
    Step.parStarWithBi (Term.eitherMatch scrutinee leftBranch rightBranch)
                       (Term.eitherMatch scrutinee leftBranch' rightBranch) :=
  Step.parStarWithBi.mapStep
    (fun leftTerm => Term.eitherMatch scrutinee leftTerm rightBranch)
    (fun leftPar => Step.par.eitherMatch
      (Step.par.refl scrutinee) leftPar (Step.par.refl rightBranch))
    (fun leftBi => Step.par.isBi.eitherMatch
      (Step.par.isBi.refl scrutinee) leftBi (Step.par.isBi.refl rightBranch))
    leftWithBi

/-- Paired single-position `eitherMatch` congruence on right-branch. -/
theorem Step.parStarWithBi.eitherMatch_cong_right
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term ctx (Ty.either leftType rightType))
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    {rightBranch rightBranch' : Term ctx (Ty.arrow rightType resultType)}
    (rightWithBi : Step.parStarWithBi rightBranch rightBranch') :
    Step.parStarWithBi (Term.eitherMatch scrutinee leftBranch rightBranch)
                       (Term.eitherMatch scrutinee leftBranch rightBranch') :=
  Step.parStarWithBi.mapStep
    (fun rightTerm => Term.eitherMatch scrutinee leftBranch rightTerm)
    (fun rightPar => Step.par.eitherMatch
      (Step.par.refl scrutinee) (Step.par.refl leftBranch) rightPar)
    (fun rightBi => Step.par.isBi.eitherMatch
      (Step.par.isBi.refl scrutinee) (Step.par.isBi.refl leftBranch) rightBi)
    rightWithBi

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
                       (Term.idJ baseCase' witness) :=
  Step.parStarWithBi.mapStep
    (fun baseTerm => Term.idJ baseTerm witness)
    (fun basePar => Step.par.idJ basePar (Step.par.refl witness))
    (fun baseBi => Step.par.isBi.idJ baseBi (Step.par.isBi.refl witness))
    baseWithBi

/-- Paired single-position `idJ` congruence on witness. -/
theorem Step.parStarWithBi.idJ_cong_witness
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    (baseCase : Term ctx resultType)
    {witness witness' : Term ctx (Ty.id carrier leftEnd rightEnd)}
    (witnessWithBi : Step.parStarWithBi witness witness') :
    Step.parStarWithBi (Term.idJ baseCase witness)
                       (Term.idJ baseCase witness') :=
  Step.parStarWithBi.mapStep
    (fun witTerm => Term.idJ baseCase witTerm)
    (fun witPar => Step.par.idJ (Step.par.refl baseCase) witPar)
    (fun witBi => Step.par.isBi.idJ (Step.par.isBi.refl baseCase) witBi)
    witnessWithBi

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

/-! ## Paired source-inversions for typed-constructor sources.

For each constructor `C` whose source position is fixed (natSucc,
listCons, optionSome, eitherInl, eitherInr), provide:

  * `Step.par.<C>_source_inv_with_bi_general` — single-step paired
    source-inversion that extracts inner paired sub-steps.
  * `Step.parStarWithBi.<C>_source_inv` — chain version that
    extracts inner paired sub-chains.

Used by the deep-ι cases of `Step.par.cd_lemma_star_with_bi`
where the IH `parStarWithBi (Term.<C> args) (Term.cd scrutinee)`
must be decomposed into paired sub-chains on `args`. -/

/-- Single-step paired source-inversion for `Term.natSucc`. -/
theorem Step.par.natSucc_source_inv_with_bi_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {predecessor : Term ctx Ty.nat}
    {termType : Ty level scope}
    {source target : Term ctx termType}
    (typeEq : termType = Ty.nat)
    {parStep : Step.par source target}
    (stepBi : Step.par.isBi parStep) :
    HEq source (@Term.natSucc mode level scope ctx predecessor) →
    ∃ (predecessor' : Term ctx Ty.nat),
        HEq target (@Term.natSucc mode level scope ctx predecessor') ∧
        Step.parWithBi predecessor predecessor' := by
  induction stepBi with
  | refl term =>
      intro sourceHEq
      exact ⟨predecessor, sourceHEq,
             Step.parWithBi.refl _⟩
  | natSucc innerBi _innerIH =>
      intro sourceHEq
      cases typeEq
      cases (eq_of_heq sourceHEq)
      rename_i innerStep
      exact ⟨_, HEq.rfl, Step.parWithBi.mk innerStep innerBi⟩
  | _ =>
      intro sourceHEq
      first
        | (cases typeEq; cases (eq_of_heq sourceHEq))
        | (exfalso
           apply refuteViaToRaw _ (Term.natSucc predecessor) typeEq sourceHEq
           intro h; simp only [Term.toRaw] at h; cases h)

/-- Chain paired source-inversion for `Term.natSucc`. -/
theorem Step.parStarWithBi.natSucc_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {predecessor : Term ctx Ty.nat}
    {target : Term ctx Ty.nat}
    (chainPair : Step.parStarWithBi
        (@Term.natSucc mode level scope ctx predecessor) target) :
    ∃ (predecessor' : Term ctx Ty.nat),
        target = Term.natSucc predecessor' ∧
        Step.parStarWithBi predecessor predecessor' := by
  generalize sourceEq :
      (@Term.natSucc mode level scope ctx predecessor) = sourceTerm
      at chainPair
  induction chainPair generalizing predecessor with
  | refl _ =>
      cases sourceEq
      exact ⟨predecessor, rfl, Step.parStarWithBi.refl predecessor⟩
  | trans firstBi _restChain restIH =>
      cases sourceEq
      obtain ⟨pred₁, eq₁, pred₁Pair⟩ :=
        Step.par.natSucc_source_inv_with_bi_general rfl firstBi HEq.rfl
      obtain ⟨pred', eq', restPair⟩ := restIH (eq_of_heq eq₁).symm
      exact ⟨pred', eq',
             Step.parStarWithBi.trans pred₁Pair.toIsBi restPair⟩

/-- Single-step paired source-inversion for `Term.listCons`. -/
theorem Step.par.listCons_source_inv_with_bi_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {headTerm : Term ctx elementType}
    {tailTerm : Term ctx (Ty.list elementType)}
    {termType : Ty level scope}
    {source target : Term ctx termType}
    (typeEq : termType = Ty.list elementType)
    {parStep : Step.par source target}
    (stepBi : Step.par.isBi parStep) :
    HEq source
        (@Term.listCons mode level scope ctx elementType headTerm tailTerm) →
    ∃ (head' : Term ctx elementType)
      (tail' : Term ctx (Ty.list elementType)),
        HEq target
            (@Term.listCons mode level scope ctx elementType head' tail') ∧
        Step.parWithBi headTerm head' ∧
        Step.parWithBi tailTerm tail' := by
  induction stepBi with
  | refl term =>
      intro sourceHEq
      exact ⟨headTerm, tailTerm, sourceHEq,
             Step.parWithBi.refl _,
             Step.parWithBi.refl _⟩
  | listCons headBi tailBi _headIH _tailIH =>
      intro sourceHEq
      cases typeEq
      cases (eq_of_heq sourceHEq)
      rename_i headStep tailStep
      exact ⟨_, _, HEq.rfl,
             Step.parWithBi.mk headStep headBi,
             Step.parWithBi.mk tailStep tailBi⟩
  | _ =>
      intro sourceHEq
      first
        | (cases typeEq; cases (eq_of_heq sourceHEq))
        | (exfalso
           apply refuteViaToRaw _ (Term.listCons headTerm tailTerm) typeEq sourceHEq
           intro h; simp only [Term.toRaw] at h; cases h)

/-- Chain paired source-inversion for `Term.listCons`. -/
theorem Step.parStarWithBi.listCons_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {headTerm : Term ctx elementType}
    {tailTerm : Term ctx (Ty.list elementType)}
    {target : Term ctx (Ty.list elementType)}
    (chainPair : Step.parStarWithBi
        (@Term.listCons mode level scope ctx elementType headTerm tailTerm)
        target) :
    ∃ (head' : Term ctx elementType)
      (tail' : Term ctx (Ty.list elementType)),
        target = Term.listCons head' tail' ∧
        Step.parStarWithBi headTerm head' ∧
        Step.parStarWithBi tailTerm tail' := by
  generalize sourceEq :
      (@Term.listCons mode level scope ctx elementType headTerm tailTerm)
        = sourceTerm at chainPair
  induction chainPair generalizing headTerm tailTerm with
  | refl _ =>
      cases sourceEq
      exact ⟨headTerm, tailTerm, rfl,
             Step.parStarWithBi.refl headTerm,
             Step.parStarWithBi.refl tailTerm⟩
  | trans firstBi _restChain restIH =>
      cases sourceEq
      obtain ⟨head₁, tail₁, eq₁, headPair, tailPair⟩ :=
        Step.par.listCons_source_inv_with_bi_general rfl firstBi HEq.rfl
      obtain ⟨head', tail', eq', headRest, tailRest⟩ :=
        restIH (eq_of_heq eq₁).symm
      exact ⟨head', tail', eq',
             Step.parStarWithBi.trans headPair.toIsBi headRest,
             Step.parStarWithBi.trans tailPair.toIsBi tailRest⟩

/-- Single-step paired source-inversion for `Term.optionSome`. -/
theorem Step.par.optionSome_source_inv_with_bi_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueTerm : Term ctx elementType}
    {termType : Ty level scope}
    {source target : Term ctx termType}
    (typeEq : termType = Ty.option elementType)
    {parStep : Step.par source target}
    (stepBi : Step.par.isBi parStep) :
    HEq source
        (@Term.optionSome mode level scope ctx elementType valueTerm) →
    ∃ (value' : Term ctx elementType),
        HEq target
            (@Term.optionSome mode level scope ctx elementType value') ∧
        Step.parWithBi valueTerm value' := by
  induction stepBi with
  | refl term =>
      intro sourceHEq
      exact ⟨valueTerm, sourceHEq,
             Step.parWithBi.refl _⟩
  | optionSome valueBi _valueIH =>
      intro sourceHEq
      cases typeEq
      cases (eq_of_heq sourceHEq)
      rename_i valueStep
      exact ⟨_, HEq.rfl, Step.parWithBi.mk valueStep valueBi⟩
  | _ =>
      intro sourceHEq
      first
        | (cases typeEq; cases (eq_of_heq sourceHEq))
        | (exfalso
           apply refuteViaToRaw _ (Term.optionSome valueTerm) typeEq sourceHEq
           intro h; simp only [Term.toRaw] at h; cases h)

/-- Chain paired source-inversion for `Term.optionSome`. -/
theorem Step.parStarWithBi.optionSome_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueTerm : Term ctx elementType}
    {target : Term ctx (Ty.option elementType)}
    (chainPair : Step.parStarWithBi
        (@Term.optionSome mode level scope ctx elementType valueTerm)
        target) :
    ∃ (value' : Term ctx elementType),
        target = Term.optionSome value' ∧
        Step.parStarWithBi valueTerm value' := by
  generalize sourceEq :
      (@Term.optionSome mode level scope ctx elementType valueTerm)
        = sourceTerm at chainPair
  induction chainPair generalizing valueTerm with
  | refl _ =>
      cases sourceEq
      exact ⟨valueTerm, rfl, Step.parStarWithBi.refl valueTerm⟩
  | trans firstBi _restChain restIH =>
      cases sourceEq
      obtain ⟨value₁, eq₁, valuePair⟩ :=
        Step.par.optionSome_source_inv_with_bi_general rfl firstBi HEq.rfl
      obtain ⟨value', eq', valueRest⟩ := restIH (eq_of_heq eq₁).symm
      exact ⟨value', eq',
             Step.parStarWithBi.trans valuePair.toIsBi valueRest⟩

/-- Single-step paired source-inversion for `Term.eitherInl`. -/
theorem Step.par.eitherInl_source_inv_with_bi_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueTerm : Term ctx leftType}
    {termType : Ty level scope}
    {source target : Term ctx termType}
    (typeEq : termType = Ty.either leftType rightType)
    {parStep : Step.par source target}
    (stepBi : Step.par.isBi parStep) :
    HEq source
        (@Term.eitherInl mode level scope ctx leftType rightType valueTerm) →
    ∃ (value' : Term ctx leftType),
        HEq target
            (@Term.eitherInl mode level scope ctx leftType rightType value') ∧
        Step.parWithBi valueTerm value' := by
  induction stepBi with
  | refl term =>
      intro sourceHEq
      exact ⟨valueTerm, sourceHEq,
             Step.parWithBi.refl _⟩
  | eitherInl valueBi _valueIH =>
      intro sourceHEq
      cases typeEq
      cases (eq_of_heq sourceHEq)
      rename_i valueStep
      exact ⟨_, HEq.rfl, Step.parWithBi.mk valueStep valueBi⟩
  | _ =>
      intro sourceHEq
      first
        | (cases typeEq; cases (eq_of_heq sourceHEq))
        | (exfalso
           apply refuteViaToRaw _
             (Term.eitherInl (rightType := rightType) valueTerm)
             typeEq sourceHEq
           intro h; simp only [Term.toRaw] at h; cases h)

/-- Chain paired source-inversion for `Term.eitherInl`. -/
theorem Step.parStarWithBi.eitherInl_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueTerm : Term ctx leftType}
    {target : Term ctx (Ty.either leftType rightType)}
    (chainPair : Step.parStarWithBi
        (@Term.eitherInl mode level scope ctx leftType rightType valueTerm)
        target) :
    ∃ (value' : Term ctx leftType),
        target = Term.eitherInl value' ∧
        Step.parStarWithBi valueTerm value' := by
  generalize sourceEq :
      (@Term.eitherInl mode level scope ctx leftType rightType valueTerm)
        = sourceTerm at chainPair
  induction chainPair generalizing valueTerm with
  | refl _ =>
      cases sourceEq
      exact ⟨valueTerm, rfl, Step.parStarWithBi.refl valueTerm⟩
  | trans firstBi _restChain restIH =>
      cases sourceEq
      obtain ⟨value₁, eq₁, valuePair⟩ :=
        Step.par.eitherInl_source_inv_with_bi_general rfl firstBi HEq.rfl
      obtain ⟨value', eq', valueRest⟩ := restIH (eq_of_heq eq₁).symm
      exact ⟨value', eq',
             Step.parStarWithBi.trans valuePair.toIsBi valueRest⟩

/-- Single-step paired source-inversion for `Term.eitherInr`. -/
theorem Step.par.eitherInr_source_inv_with_bi_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueTerm : Term ctx rightType}
    {termType : Ty level scope}
    {source target : Term ctx termType}
    (typeEq : termType = Ty.either leftType rightType)
    {parStep : Step.par source target}
    (stepBi : Step.par.isBi parStep) :
    HEq source
        (@Term.eitherInr mode level scope ctx leftType rightType valueTerm) →
    ∃ (value' : Term ctx rightType),
        HEq target
            (@Term.eitherInr mode level scope ctx leftType rightType value') ∧
        Step.parWithBi valueTerm value' := by
  induction stepBi with
  | refl term =>
      intro sourceHEq
      exact ⟨valueTerm, sourceHEq,
             Step.parWithBi.refl _⟩
  | eitherInr valueBi _valueIH =>
      intro sourceHEq
      cases typeEq
      cases (eq_of_heq sourceHEq)
      rename_i valueStep
      exact ⟨_, HEq.rfl, Step.parWithBi.mk valueStep valueBi⟩
  | _ =>
      intro sourceHEq
      first
        | (cases typeEq; cases (eq_of_heq sourceHEq))
        | (exfalso
           apply refuteViaToRaw _
             (Term.eitherInr (leftType := leftType) valueTerm)
             typeEq sourceHEq
           intro h; simp only [Term.toRaw] at h; cases h)

/-- Chain paired source-inversion for `Term.eitherInr`. -/
theorem Step.parStarWithBi.eitherInr_source_inv
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueTerm : Term ctx rightType}
    {target : Term ctx (Ty.either leftType rightType)}
    (chainPair : Step.parStarWithBi
        (@Term.eitherInr mode level scope ctx leftType rightType valueTerm)
        target) :
    ∃ (value' : Term ctx rightType),
        target = Term.eitherInr value' ∧
        Step.parStarWithBi valueTerm value' := by
  generalize sourceEq :
      (@Term.eitherInr mode level scope ctx leftType rightType valueTerm)
        = sourceTerm at chainPair
  induction chainPair generalizing valueTerm with
  | refl _ =>
      cases sourceEq
      exact ⟨valueTerm, rfl, Step.parStarWithBi.refl valueTerm⟩
  | trans firstBi _restChain restIH =>
      cases sourceEq
      obtain ⟨value₁, eq₁, valuePair⟩ :=
        Step.par.eitherInr_source_inv_with_bi_general rfl firstBi HEq.rfl
      obtain ⟨value', eq', valueRest⟩ := restIH (eq_of_heq eq₁).symm
      exact ⟨value', eq',
             Step.parStarWithBi.trans valuePair.toIsBi valueRest⟩

/-! ## `Step.parWithBi` cast helpers — paired versions of
`Step.par.castBoth` / `castTarget` / `castSource` that thread
the cast through both Step.par and isBi simultaneously. -/

/-- `Step.parWithBi` survives a Ty-equality cast on both endpoints. -/
theorem Step.parWithBi.castBoth
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    (typeEquality : sourceType = targetType)
    {beforeTerm afterTerm : Term ctx sourceType}
    (paired : Step.parWithBi beforeTerm afterTerm) :
    Step.parWithBi (typeEquality ▸ beforeTerm) (typeEquality ▸ afterTerm) := by
  obtain ⟨step, bi⟩ := paired
  exact Step.parWithBi.mk
    (Step.par.castBoth typeEquality step)
    (Step.par.isBi.castBoth typeEquality bi)

/-- `Step.parWithBi` survives a target-direction Eq cast. -/
theorem Step.parWithBi.castTarget
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {beforeTerm afterTerm afterTerm' : Term ctx termType}
    (targetEquality : afterTerm = afterTerm')
    (paired : Step.parWithBi beforeTerm afterTerm) :
    Step.parWithBi beforeTerm afterTerm' := by
  obtain ⟨step, bi⟩ := paired
  exact Step.parWithBi.mk
    (Step.par.castTarget targetEquality step)
    (Step.par.isBi.castTarget targetEquality bi)

/-- `Step.parWithBi` survives a source-direction Eq cast. -/
theorem Step.parWithBi.castSource
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    {beforeTerm beforeTerm' afterTerm : Term ctx termType}
    (sourceEquality : beforeTerm = beforeTerm')
    (paired : Step.parWithBi beforeTerm afterTerm) :
    Step.parWithBi beforeTerm' afterTerm := by
  obtain ⟨step, bi⟩ := paired
  exact Step.parWithBi.mk
    (Step.par.castSource sourceEquality step)
    (Step.par.isBi.castSource sourceEquality bi)

/-! ## β-workhorse smoke: subst_compatible preserves isBi (refl case only).

Sanity-check the proof-irrelevance route to `subst_compatible_isBi`:
since `Step.par` lives in `Prop` and Lean 4 has definitional proof
irrelevance, `Step.par.isBi (Step.par.subst_compatible σ parStep)`
and `Step.par.isBi (any-other-Step.par-proof)` are the same type
whenever the underlying `Step.par a b` proposition matches.  This
means the 54-case proof can construct a *fresh* isBi witness at
each case via the corresponding constructor, and Lean will defEq-
align it with whatever opaque `subst_compatible` returned. -/

/-- **rename-compatibility for the paired predicate.**  A
`Step.parWithBi` (paired Step.par + isBi witness) commutes with
`Term.rename`.  Mirrors `Step.parWithBi.subst_compatible` exactly,
substituting `rename` for `subst` and the `Renaming` flavour of
each commute lemma.

Used by `TermSubst.parWithBi_lift` (the binder-position lift in the
paired analogue of `Term.subst_par_pointwise`); this in turn is
used by `Term.subst_parWithBi_pointwise` and
`Term.subst0_parStarWithBi_argument`. -/
theorem Step.parWithBi.rename_compatible
    {mode : Mode} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType}
    (parPaired : Step.parWithBi beforeTerm afterTerm) :
    Step.parWithBi
      (Term.rename termRenaming beforeTerm)
      (Term.rename termRenaming afterTerm) := by
  obtain ⟨parallelStep, biWitness⟩ := parPaired
  induction biWitness generalizing targetScope targetCtx with
  | refl term =>
      exact Step.parWithBi.refl _
  | app _functionBi _argumentBi functionIH argumentIH =>
      obtain ⟨fStep, fBi⟩ := functionIH termRenaming
      obtain ⟨aStep, aBi⟩ := argumentIH termRenaming
      exact Step.parWithBi.mk (Step.par.app fStep aStep)
                              (Step.par.isBi.app fBi aBi)
  | lam _bodyBi bodyIH =>
      rename_i domainType codomainType _ _ _
      obtain ⟨bStep, bBi⟩ := bodyIH (TermRenaming.lift termRenaming domainType)
      let castedStep := Step.par.castBoth
        (Ty.rename_weaken_commute codomainType rawRenaming) bStep
      let castedBi := Step.par.isBi.castBoth
        (Ty.rename_weaken_commute codomainType rawRenaming) bBi
      exact Step.parWithBi.mk
        (Step.par.lam castedStep) (Step.par.isBi.lam castedBi)
  | lamPi _bodyBi bodyIH =>
      rename_i domainType _ _ _ _
      obtain ⟨bStep, bBi⟩ := bodyIH (TermRenaming.lift termRenaming domainType)
      exact Step.parWithBi.mk
        (Step.par.lamPi bStep) (Step.par.isBi.lamPi bBi)
  | appPi _functionBi _argumentBi functionIH argumentIH =>
      rename_i domainType codomainType _ _ _ _ _ _
      obtain ⟨fStep, fBi⟩ := functionIH termRenaming
      obtain ⟨aStep, aBi⟩ := argumentIH termRenaming
      let typeEq :=
        (Ty.subst0_rename_commute codomainType domainType rawRenaming).symm
      exact Step.parWithBi.mk
        (Step.par.castBoth typeEq (Step.par.appPi fStep aStep))
        (Step.par.isBi.castBoth typeEq (Step.par.isBi.appPi fBi aBi))
  | pair _firstBi _secondBi firstIH secondIH =>
      rename_i firstType secondType _ _ _ _ _ _
      obtain ⟨fStep, fBi⟩ := firstIH termRenaming
      obtain ⟨sStep, sBi⟩ := secondIH termRenaming
      let typeEq :=
        Ty.subst0_rename_commute secondType firstType rawRenaming
      exact Step.parWithBi.mk
        (Step.par.pair fStep (Step.par.castBoth typeEq sStep))
        (Step.par.isBi.pair fBi (Step.par.isBi.castBoth typeEq sBi))
  | fst _pairBi pairIH =>
      obtain ⟨pStep, pBi⟩ := pairIH termRenaming
      exact Step.parWithBi.mk (Step.par.fst pStep) (Step.par.isBi.fst pBi)
  | snd _pairBi pairIH =>
      rename_i firstType secondType _ _ _
      obtain ⟨pStep, pBi⟩ := pairIH termRenaming
      let typeEq :=
        (Ty.subst0_rename_commute secondType firstType rawRenaming).symm
      exact Step.parWithBi.mk
        (Step.par.castBoth typeEq (Step.par.snd pStep))
        (Step.par.isBi.castBoth typeEq (Step.par.isBi.snd pBi))
  | boolElim _scrutBi _thenBi _elseBi scrutIH thenIH elseIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨tStep, tBi⟩ := thenIH termRenaming
      obtain ⟨eStep, eBi⟩ := elseIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.boolElim sStep tStep eStep)
        (Step.par.isBi.boolElim sBi tBi eBi)
  | betaApp _bodyBi _argBi bodyIH argIH =>
      rename_i _ domainType codomainType _ bodyAfter _ argumentAfter _ _
      obtain ⟨bStep, bBi⟩ := bodyIH (TermRenaming.lift termRenaming domainType)
      obtain ⟨aStep, aBi⟩ := argIH termRenaming
      let renamedArgumentAfter : Term targetCtx (domainType.rename rawRenaming) :=
        Term.rename termRenaming argumentAfter
      let renamedBodyAfter :
          Term (targetCtx.cons (domainType.rename rawRenaming))
            (codomainType.weaken.rename rawRenaming.lift) :=
        Term.rename (TermRenaming.lift termRenaming domainType) bodyAfter
      let bodyCastEq := Ty.rename_weaken_commute codomainType rawRenaming
      let primitiveTarget : Term targetCtx (codomainType.rename rawRenaming) :=
        (Ty.weaken_subst_singleton
            (codomainType.rename rawRenaming)
            (domainType.rename rawRenaming)) ▸
          Term.subst0 (bodyCastEq ▸ renamedBodyAfter)
                      renamedArgumentAfter
      let targetEquality :
          primitiveTarget =
          Term.rename termRenaming
            ((Ty.weaken_subst_singleton codomainType domainType) ▸
              Term.subst0 bodyAfter argumentAfter) :=
        eq_of_heq (HEq.symm (by
          apply HEq.trans
            (Term.rename_HEq_cast_input termRenaming
              (Ty.weaken_subst_singleton codomainType domainType)
              (Term.subst0 bodyAfter argumentAfter))
          apply HEq.trans
            (Term.rename_subst0_HEq termRenaming bodyAfter argumentAfter)
          apply HEq.trans
            (HEq.symm
              (Term.subst0_HEq_cast_input bodyCastEq
                renamedBodyAfter renamedArgumentAfter))
          exact Term.castRight_HEq
            (Ty.weaken_subst_singleton
              (codomainType.rename rawRenaming)
              (domainType.rename rawRenaming))
            (Term.subst0 (bodyCastEq ▸ renamedBodyAfter)
                          renamedArgumentAfter)))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality
          (Step.par.betaApp (Step.par.castBoth bodyCastEq bStep) aStep))
        (Step.par.isBi.castTarget targetEquality
          (Step.par.isBi.betaApp
            (Step.par.isBi.castBoth bodyCastEq bBi) aBi))
  | betaAppPi _bodyBi _argBi bodyIH argIH =>
      rename_i _ domainType codomainType _ bodyAfter _ argumentAfter _ _
      obtain ⟨bStep, bBi⟩ := bodyIH (TermRenaming.lift termRenaming domainType)
      obtain ⟨aStep, aBi⟩ := argIH termRenaming
      let resultTypeEquality :=
        Ty.subst0_rename_commute codomainType domainType rawRenaming
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.rename (TermRenaming.lift termRenaming domainType) bodyAfter)
                (Term.rename termRenaming argumentAfter)
            = Term.rename termRenaming (Term.subst0 bodyAfter argumentAfter) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.rename_subst0_HEq termRenaming bodyAfter argumentAfter)))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality
          (Step.par.castBoth resultTypeEquality.symm
            (Step.par.betaAppPi bStep aStep)))
        (Step.par.isBi.castTarget targetEquality
          (Step.par.isBi.castBoth resultTypeEquality.symm
            (Step.par.isBi.betaAppPi bBi aBi)))
  | betaFstPair _firstBi firstIH =>
      rename_i _ firstType secondType _ _ secondValOrig _
      obtain ⟨fStep, fBi⟩ := firstIH termRenaming
      let typeEq :=
        Ty.subst0_rename_commute secondType firstType rawRenaming
      let secondValRenamed : Term targetCtx _ :=
        typeEq ▸ Term.rename termRenaming secondValOrig
      exact Step.parWithBi.mk
        (Step.par.betaFstPair secondValRenamed fStep)
        (Step.par.isBi.betaFstPair fBi)
  | betaSndPair _secondBi secondIH =>
      rename_i _ firstType secondType firstVal _ secondAfter _
      obtain ⟨sStep, sBi⟩ := secondIH termRenaming
      let resultTypeEquality :=
        Ty.subst0_rename_commute secondType firstType rawRenaming
      let targetEquality :
          resultTypeEquality.symm ▸
              (resultTypeEquality ▸ Term.rename termRenaming secondAfter)
            = Term.rename termRenaming secondAfter :=
        eq_of_heq (HEq.trans (eqRec_heq _ _) (eqRec_heq _ _))
      exact Step.parWithBi.castTarget targetEquality
        (Step.parWithBi.castBoth resultTypeEquality.symm
          (Step.parWithBi.mk
            (Step.par.betaSndPair (Term.rename termRenaming firstVal)
              (Step.par.castBoth resultTypeEquality sStep))
            (Step.par.isBi.betaSndPair
              (Step.par.isBi.castBoth resultTypeEquality sBi))))
  | iotaBoolElimTrue elseBranch _thenBi thenIH =>
      obtain ⟨tStep, tBi⟩ := thenIH termRenaming
      let elseRenamed := Term.rename termRenaming elseBranch
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimTrue elseRenamed tStep)
        (Step.par.isBi.iotaBoolElimTrue elseRenamed tBi)
  | iotaBoolElimFalse thenBranch _elseBi elseIH =>
      obtain ⟨eStep, eBi⟩ := elseIH termRenaming
      let thenRenamed := Term.rename termRenaming thenBranch
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimFalse thenRenamed eStep)
        (Step.par.isBi.iotaBoolElimFalse thenRenamed eBi)
  | natSucc _predBi predIH =>
      obtain ⟨pStep, pBi⟩ := predIH termRenaming
      exact Step.parWithBi.mk (Step.par.natSucc pStep)
                              (Step.par.isBi.natSucc pBi)
  | natElim _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨zStep, zBi⟩ := zeroIH termRenaming
      obtain ⟨ssStep, ssBi⟩ := succIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.natElim sStep zStep ssStep)
        (Step.par.isBi.natElim sBi zBi ssBi)
  | iotaNatElimZero succBranch _zeroBi zeroIH =>
      obtain ⟨zStep, zBi⟩ := zeroIH termRenaming
      let succRenamed := Term.rename termRenaming succBranch
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimZero succRenamed zStep)
        (Step.par.isBi.iotaNatElimZero succRenamed zBi)
  | natRec _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨zStep, zBi⟩ := zeroIH termRenaming
      obtain ⟨ssStep, ssBi⟩ := succIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.natRec sStep zStep ssStep)
        (Step.par.isBi.natRec sBi zBi ssBi)
  | iotaNatRecZero succBranch _zeroBi zeroIH =>
      obtain ⟨zStep, zBi⟩ := zeroIH termRenaming
      let succRenamed := Term.rename termRenaming succBranch
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecZero succRenamed zStep)
        (Step.par.isBi.iotaNatRecZero succRenamed zBi)
  | iotaNatRecSucc _predBi _zeroBi _succBi predIH zeroIH succIH =>
      obtain ⟨pStep, pBi⟩ := predIH termRenaming
      obtain ⟨zStep, zBi⟩ := zeroIH termRenaming
      obtain ⟨ssStep, ssBi⟩ := succIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecSucc pStep zStep ssStep)
        (Step.par.isBi.iotaNatRecSucc pBi zBi ssBi)
  | iotaNatElimSucc zeroBranch _predBi _succBi predIH succIH =>
      obtain ⟨pStep, pBi⟩ := predIH termRenaming
      obtain ⟨ssStep, ssBi⟩ := succIH termRenaming
      let zeroRenamed := Term.rename termRenaming zeroBranch
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimSucc zeroRenamed pStep ssStep)
        (Step.par.isBi.iotaNatElimSucc zeroRenamed pBi ssBi)
  | listCons _headBi _tailBi headIH tailIH =>
      obtain ⟨hStep, hBi⟩ := headIH termRenaming
      obtain ⟨tStep, tBi⟩ := tailIH termRenaming
      exact Step.parWithBi.mk (Step.par.listCons hStep tStep)
                              (Step.par.isBi.listCons hBi tBi)
  | listElim _scrutBi _nilBi _consBi scrutIH nilIH consIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨nStep, nBi⟩ := nilIH termRenaming
      obtain ⟨cStep, cBi⟩ := consIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.listElim sStep nStep cStep)
        (Step.par.isBi.listElim sBi nBi cBi)
  | iotaListElimNil consBranch _nilBi nilIH =>
      obtain ⟨nStep, nBi⟩ := nilIH termRenaming
      let consRenamed := Term.rename termRenaming consBranch
      exact Step.parWithBi.mk
        (Step.par.iotaListElimNil consRenamed nStep)
        (Step.par.isBi.iotaListElimNil consRenamed nBi)
  | iotaListElimCons nilBranch _headBi _tailBi _consBi headIH tailIH consIH =>
      obtain ⟨hStep, hBi⟩ := headIH termRenaming
      obtain ⟨tStep, tBi⟩ := tailIH termRenaming
      obtain ⟨cStep, cBi⟩ := consIH termRenaming
      let nilRenamed := Term.rename termRenaming nilBranch
      exact Step.parWithBi.mk
        (Step.par.iotaListElimCons nilRenamed hStep tStep cStep)
        (Step.par.isBi.iotaListElimCons nilRenamed hBi tBi cBi)
  | optionSome _valueBi valueIH =>
      obtain ⟨vStep, vBi⟩ := valueIH termRenaming
      exact Step.parWithBi.mk (Step.par.optionSome vStep)
                              (Step.par.isBi.optionSome vBi)
  | optionMatch _scrutBi _noneBi _someBi scrutIH noneIH someIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨nStep, nBi⟩ := noneIH termRenaming
      obtain ⟨smStep, smBi⟩ := someIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.optionMatch sStep nStep smStep)
        (Step.par.isBi.optionMatch sBi nBi smBi)
  | iotaOptionMatchNone someBranch _noneBi noneIH =>
      obtain ⟨nStep, nBi⟩ := noneIH termRenaming
      let someRenamed := Term.rename termRenaming someBranch
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchNone someRenamed nStep)
        (Step.par.isBi.iotaOptionMatchNone someRenamed nBi)
  | iotaOptionMatchSome noneBranch _valueBi _someBi valueIH someIH =>
      obtain ⟨vStep, vBi⟩ := valueIH termRenaming
      obtain ⟨smStep, smBi⟩ := someIH termRenaming
      let noneRenamed := Term.rename termRenaming noneBranch
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchSome noneRenamed vStep smStep)
        (Step.par.isBi.iotaOptionMatchSome noneRenamed vBi smBi)
  | eitherInl _valueBi valueIH =>
      obtain ⟨vStep, vBi⟩ := valueIH termRenaming
      exact Step.parWithBi.mk (Step.par.eitherInl vStep)
                              (Step.par.isBi.eitherInl vBi)
  | eitherInr _valueBi valueIH =>
      obtain ⟨vStep, vBi⟩ := valueIH termRenaming
      exact Step.parWithBi.mk (Step.par.eitherInr vStep)
                              (Step.par.isBi.eitherInr vBi)
  | eitherMatch _scrutBi _leftBi _rightBi scrutIH leftIH rightIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨lStep, lBi⟩ := leftIH termRenaming
      obtain ⟨rStep, rBi⟩ := rightIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.eitherMatch sStep lStep rStep)
        (Step.par.isBi.eitherMatch sBi lBi rBi)
  | iotaEitherMatchInl rightBranch _valueBi _leftBi valueIH leftIH =>
      obtain ⟨vStep, vBi⟩ := valueIH termRenaming
      obtain ⟨lStep, lBi⟩ := leftIH termRenaming
      let rightRenamed := Term.rename termRenaming rightBranch
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInl rightRenamed vStep lStep)
        (Step.par.isBi.iotaEitherMatchInl rightRenamed vBi lBi)
  | iotaEitherMatchInr leftBranch _valueBi _rightBi valueIH rightIH =>
      obtain ⟨vStep, vBi⟩ := valueIH termRenaming
      obtain ⟨rStep, rBi⟩ := rightIH termRenaming
      let leftRenamed := Term.rename termRenaming leftBranch
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInr leftRenamed vStep rStep)
        (Step.par.isBi.iotaEitherMatchInr leftRenamed vBi rBi)
  | idJ _baseBi _witnessBi baseIH witnessIH =>
      obtain ⟨bStep, bBi⟩ := baseIH termRenaming
      obtain ⟨wStep, wBi⟩ := witnessIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.idJ bStep wStep)
        (Step.par.isBi.idJ bBi wBi)
  | iotaIdJRefl _baseBi baseIH =>
      obtain ⟨bStep, bBi⟩ := baseIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaIdJRefl bStep)
        (Step.par.isBi.iotaIdJRefl bBi)
  -- Deep cases — same approach + cast bookkeeping.
  | betaAppDeep _functionBi _argBi functionIH argIH =>
      rename_i _ domainType codomainType _ body _ argAfter _ _
      obtain ⟨fStep, fBi⟩ := functionIH termRenaming
      obtain ⟨aStep, aBi⟩ := argIH termRenaming
      let renamedArgAfter : Term targetCtx (domainType.rename rawRenaming) :=
        Term.rename termRenaming argAfter
      let renamedBody :
          Term (targetCtx.cons (domainType.rename rawRenaming))
            (codomainType.weaken.rename rawRenaming.lift) :=
        Term.rename (TermRenaming.lift termRenaming domainType) body
      let bodyCastEq := Ty.rename_weaken_commute codomainType rawRenaming
      let primitiveTarget : Term targetCtx (codomainType.rename rawRenaming) :=
        (Ty.weaken_subst_singleton
            (codomainType.rename rawRenaming)
            (domainType.rename rawRenaming)) ▸
          Term.subst0 (bodyCastEq ▸ renamedBody) renamedArgAfter
      let targetEquality :
          primitiveTarget =
          Term.rename termRenaming
            ((Ty.weaken_subst_singleton codomainType domainType) ▸
              Term.subst0 body argAfter) :=
        eq_of_heq (HEq.symm (by
          apply HEq.trans
            (Term.rename_HEq_cast_input termRenaming
              (Ty.weaken_subst_singleton codomainType domainType)
              (Term.subst0 body argAfter))
          apply HEq.trans
            (Term.rename_subst0_HEq termRenaming body argAfter)
          apply HEq.trans
            (HEq.symm
              (Term.subst0_HEq_cast_input bodyCastEq renamedBody renamedArgAfter))
          exact Term.castRight_HEq
            (Ty.weaken_subst_singleton
              (codomainType.rename rawRenaming)
              (domainType.rename rawRenaming))
            (Term.subst0 (bodyCastEq ▸ renamedBody) renamedArgAfter)))
      exact Step.parWithBi.castTarget targetEquality
        (Step.parWithBi.mk
          (Step.par.betaAppDeep fStep aStep)
          (Step.par.isBi.betaAppDeep fBi aBi))
  | betaAppPiDeep _functionBi _argBi functionIH argIH =>
      rename_i _ domainType codomainType _ body _ argAfter _ _
      obtain ⟨fStep, fBi⟩ := functionIH termRenaming
      obtain ⟨aStep, aBi⟩ := argIH termRenaming
      let resultTypeEquality :=
        Ty.subst0_rename_commute codomainType domainType rawRenaming
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.rename (TermRenaming.lift termRenaming domainType) body)
                (Term.rename termRenaming argAfter)
            = Term.rename termRenaming (Term.subst0 body argAfter) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.rename_subst0_HEq termRenaming body argAfter)))
      exact Step.parWithBi.castTarget targetEquality
        (Step.parWithBi.castBoth resultTypeEquality.symm
          (Step.parWithBi.mk
            (Step.par.betaAppPiDeep fStep aStep)
            (Step.par.isBi.betaAppPiDeep fBi aBi)))
  | betaFstPairDeep _pairBi pairIH =>
      obtain ⟨pStep, pBi⟩ := pairIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.betaFstPairDeep pStep)
        (Step.par.isBi.betaFstPairDeep pBi)
  | betaSndPairDeep _pairBi pairIH =>
      rename_i _ firstType secondType _ _ secondVal _
      obtain ⟨pStep, pBi⟩ := pairIH termRenaming
      let resultTypeEquality :=
        Ty.subst0_rename_commute secondType firstType rawRenaming
      let targetEquality :
          resultTypeEquality.symm ▸
              ((Ty.subst0_rename_commute secondType firstType rawRenaming) ▸
                Term.rename termRenaming secondVal)
            = Term.rename termRenaming secondVal :=
        eq_of_heq (HEq.trans (eqRec_heq _ _) (eqRec_heq _ _))
      exact Step.parWithBi.castTarget targetEquality
        (Step.parWithBi.castBoth resultTypeEquality.symm
          (Step.parWithBi.mk
            (Step.par.betaSndPairDeep pStep)
            (Step.par.isBi.betaSndPairDeep pBi)))
  | iotaBoolElimTrueDeep elseBranch _scrutBi _thenBi scrutIH thenIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨tStep, tBi⟩ := thenIH termRenaming
      let elseRenamed := Term.rename termRenaming elseBranch
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimTrueDeep elseRenamed sStep tStep)
        (Step.par.isBi.iotaBoolElimTrueDeep elseRenamed sBi tBi)
  | iotaBoolElimFalseDeep thenBranch _scrutBi _elseBi scrutIH elseIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨eStep, eBi⟩ := elseIH termRenaming
      let thenRenamed := Term.rename termRenaming thenBranch
      exact Step.parWithBi.mk
        (Step.par.iotaBoolElimFalseDeep thenRenamed sStep eStep)
        (Step.par.isBi.iotaBoolElimFalseDeep thenRenamed sBi eBi)
  | iotaNatElimZeroDeep succBranch _scrutBi _zeroBi scrutIH zeroIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨zStep, zBi⟩ := zeroIH termRenaming
      let succRenamed := Term.rename termRenaming succBranch
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimZeroDeep succRenamed sStep zStep)
        (Step.par.isBi.iotaNatElimZeroDeep succRenamed sBi zBi)
  | iotaNatElimSuccDeep zeroBranch _scrutBi _succBi scrutIH succIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨ssStep, ssBi⟩ := succIH termRenaming
      let zeroRenamed := Term.rename termRenaming zeroBranch
      exact Step.parWithBi.mk
        (Step.par.iotaNatElimSuccDeep zeroRenamed sStep ssStep)
        (Step.par.isBi.iotaNatElimSuccDeep zeroRenamed sBi ssBi)
  | iotaNatRecZeroDeep succBranch _scrutBi _zeroBi scrutIH zeroIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨zStep, zBi⟩ := zeroIH termRenaming
      let succRenamed := Term.rename termRenaming succBranch
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecZeroDeep succRenamed sStep zStep)
        (Step.par.isBi.iotaNatRecZeroDeep succRenamed sBi zBi)
  | iotaNatRecSuccDeep _scrutBi _zeroBi _succBi scrutIH zeroIH succIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨zStep, zBi⟩ := zeroIH termRenaming
      obtain ⟨ssStep, ssBi⟩ := succIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaNatRecSuccDeep sStep zStep ssStep)
        (Step.par.isBi.iotaNatRecSuccDeep sBi zBi ssBi)
  | iotaListElimNilDeep consBranch _scrutBi _nilBi scrutIH nilIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨nStep, nBi⟩ := nilIH termRenaming
      let consRenamed := Term.rename termRenaming consBranch
      exact Step.parWithBi.mk
        (Step.par.iotaListElimNilDeep consRenamed sStep nStep)
        (Step.par.isBi.iotaListElimNilDeep consRenamed sBi nBi)
  | iotaListElimConsDeep nilBranch _scrutBi _consBi scrutIH consIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨cStep, cBi⟩ := consIH termRenaming
      let nilRenamed := Term.rename termRenaming nilBranch
      exact Step.parWithBi.mk
        (Step.par.iotaListElimConsDeep nilRenamed sStep cStep)
        (Step.par.isBi.iotaListElimConsDeep nilRenamed sBi cBi)
  | iotaOptionMatchNoneDeep someBranch _scrutBi _noneBi scrutIH noneIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨nStep, nBi⟩ := noneIH termRenaming
      let someRenamed := Term.rename termRenaming someBranch
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchNoneDeep someRenamed sStep nStep)
        (Step.par.isBi.iotaOptionMatchNoneDeep someRenamed sBi nBi)
  | iotaOptionMatchSomeDeep noneBranch _scrutBi _someBi scrutIH someIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨smStep, smBi⟩ := someIH termRenaming
      let noneRenamed := Term.rename termRenaming noneBranch
      exact Step.parWithBi.mk
        (Step.par.iotaOptionMatchSomeDeep noneRenamed sStep smStep)
        (Step.par.isBi.iotaOptionMatchSomeDeep noneRenamed sBi smBi)
  | iotaEitherMatchInlDeep rightBranch _scrutBi _leftBi scrutIH leftIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨lStep, lBi⟩ := leftIH termRenaming
      let rightRenamed := Term.rename termRenaming rightBranch
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInlDeep rightRenamed sStep lStep)
        (Step.par.isBi.iotaEitherMatchInlDeep rightRenamed sBi lBi)
  | iotaEitherMatchInrDeep leftBranch _scrutBi _rightBi scrutIH rightIH =>
      obtain ⟨sStep, sBi⟩ := scrutIH termRenaming
      obtain ⟨rStep, rBi⟩ := rightIH termRenaming
      let leftRenamed := Term.rename termRenaming leftBranch
      exact Step.parWithBi.mk
        (Step.par.iotaEitherMatchInrDeep leftRenamed sStep rStep)
        (Step.par.isBi.iotaEitherMatchInrDeep leftRenamed sBi rBi)
  | iotaIdJReflDeep _witnessBi _baseBi witnessIH baseIH =>
      obtain ⟨wStep, wBi⟩ := witnessIH termRenaming
      obtain ⟨bStep, bBi⟩ := baseIH termRenaming
      exact Step.parWithBi.mk
        (Step.par.iotaIdJReflDeep wStep bStep)
        (Step.par.isBi.iotaIdJReflDeep wBi bBi)

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
    (parPaired : Step.parWithBi beforeTerm afterTerm) :
    Step.parWithBi
      (Term.subst termSubstitution beforeTerm)
      (Term.subst termSubstitution afterTerm) := by
  obtain ⟨parallelStep, biWitness⟩ := parPaired
  induction biWitness generalizing targetScope targetCtx with
  | refl term =>
      exact Step.parWithBi.refl _
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
      -- Implicits in declaration order (least-recent first under
      -- rename_i): ctx, domainType, codomainType, body, body', arg,
      -- arg', bodyStep, argStep — 9 implicits.
      rename_i _ domainType codomainType _ bodyAfter _ argumentAfter _ _
      obtain ⟨bStep, bBi⟩ := bodyIH (TermSubst.lift termSubstitution domainType)
      obtain ⟨aStep, aBi⟩ := argIH termSubstitution
      let substitutedArgumentAfter : Term targetCtx (domainType.subst typeSubstitution) :=
        Term.subst termSubstitution argumentAfter
      let substitutedBodyAfter :
          Term (targetCtx.cons (domainType.subst typeSubstitution))
            (codomainType.weaken.subst typeSubstitution.lift) :=
        Term.subst (TermSubst.lift termSubstitution domainType) bodyAfter
      let bodyCastEq := Ty.subst_weaken_commute codomainType typeSubstitution
      let primitiveTarget : Term targetCtx (codomainType.subst typeSubstitution) :=
        (Ty.weaken_subst_singleton
            (codomainType.subst typeSubstitution)
            (domainType.subst typeSubstitution)) ▸
          Term.subst0 (bodyCastEq ▸ substitutedBodyAfter)
                      substitutedArgumentAfter
      let targetEquality :
          primitiveTarget =
          Term.subst termSubstitution
            ((Ty.weaken_subst_singleton codomainType domainType) ▸
              Term.subst0 bodyAfter argumentAfter) :=
        eq_of_heq (HEq.symm (by
          apply HEq.trans
            (Term.subst_HEq_cast_input termSubstitution
              (Ty.weaken_subst_singleton codomainType domainType)
              (Term.subst0 bodyAfter argumentAfter))
          apply HEq.trans
            (Term.subst0_subst_HEq termSubstitution bodyAfter argumentAfter)
          apply HEq.trans
            (HEq.symm
              (Term.subst0_HEq_cast_input bodyCastEq
                substitutedBodyAfter substitutedArgumentAfter))
          exact Term.castRight_HEq
            (Ty.weaken_subst_singleton
              (codomainType.subst typeSubstitution)
              (domainType.subst typeSubstitution))
            (Term.subst0 (bodyCastEq ▸ substitutedBodyAfter)
                          substitutedArgumentAfter)))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality
          (Step.par.betaApp (Step.par.castBoth bodyCastEq bStep) aStep))
        (Step.par.isBi.castTarget targetEquality
          (Step.par.isBi.betaApp
            (Step.par.isBi.castBoth bodyCastEq bBi) aBi))
  | betaAppPi _bodyBi _argBi bodyIH argIH =>
      rename_i _ domainType codomainType _ bodyAfter _ argumentAfter _ _
      obtain ⟨bStep, bBi⟩ := bodyIH (TermSubst.lift termSubstitution domainType)
      obtain ⟨aStep, aBi⟩ := argIH termSubstitution
      let resultTypeEquality :=
        Ty.subst0_subst_commute codomainType domainType typeSubstitution
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.subst (TermSubst.lift termSubstitution domainType) bodyAfter)
                (Term.subst termSubstitution argumentAfter)
            = Term.subst termSubstitution (Term.subst0 bodyAfter argumentAfter) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.subst0_subst_HEq termSubstitution bodyAfter argumentAfter)))
      exact Step.parWithBi.mk
        (Step.par.castTarget targetEquality
          (Step.par.castBoth resultTypeEquality.symm
            (Step.par.betaAppPi bStep aStep)))
        (Step.par.isBi.castTarget targetEquality
          (Step.par.isBi.castBoth resultTypeEquality.symm
            (Step.par.isBi.betaAppPi bBi aBi)))
  | betaFstPair _firstBi firstIH =>
      -- `rename_i` orders LEAST RECENT first (declaration order):
      -- ctx, firstType, secondType, firstVal, firstVal', secondVal,
      -- firstStep.  Skip ctx; capture firstType, secondType; skip
      -- firstVal/firstVal'; capture secondVal; skip firstStep.
      rename_i _ firstType secondType _ _ secondValOrig _
      obtain ⟨fStep, fBi⟩ := firstIH termSubstitution
      let typeEq :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      let secondValSubst : Term targetCtx _ :=
        typeEq ▸ Term.subst termSubstitution secondValOrig
      exact Step.parWithBi.mk
        (Step.par.betaFstPair secondValSubst fStep)
        (Step.par.isBi.betaFstPair fBi)
  | betaSndPair _secondBi secondIH =>
      -- Implicits: ctx, firstType, secondType, firstVal, secondVal,
      -- secondVal', secondStep — 7.
      rename_i _ firstType secondType firstVal _ secondAfter _
      obtain ⟨sStep, sBi⟩ := secondIH termSubstitution
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      let targetEquality :
          resultTypeEquality.symm ▸
              (resultTypeEquality ▸ Term.subst termSubstitution secondAfter)
            = Term.subst termSubstitution secondAfter :=
        eq_of_heq (HEq.trans (eqRec_heq _ _) (eqRec_heq _ _))
      exact Step.parWithBi.castTarget targetEquality
        (Step.parWithBi.castBoth resultTypeEquality.symm
          (Step.parWithBi.mk
            (Step.par.betaSndPair (Term.subst termSubstitution firstVal)
              (Step.par.castBoth resultTypeEquality sStep))
            (Step.par.isBi.betaSndPair
              (Step.par.isBi.castBoth resultTypeEquality sBi))))
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
  | betaAppDeep _functionBi _argBi functionIH argIH =>
      -- Implicits in declaration order: ctx, domainType, codomainType,
      -- functionTerm, body, arg, arg', functionStep, argStep — 9.
      rename_i _ domainType codomainType _ body _ argAfter _ _
      obtain ⟨fStep, fBi⟩ := functionIH termSubstitution
      obtain ⟨aStep, aBi⟩ := argIH termSubstitution
      let substitutedArgAfter : Term targetCtx (domainType.subst typeSubstitution) :=
        Term.subst termSubstitution argAfter
      let substitutedBody :
          Term (targetCtx.cons (domainType.subst typeSubstitution))
            (codomainType.weaken.subst typeSubstitution.lift) :=
        Term.subst (TermSubst.lift termSubstitution domainType) body
      let bodyCastEq := Ty.subst_weaken_commute codomainType typeSubstitution
      let primitiveTarget : Term targetCtx (codomainType.subst typeSubstitution) :=
        (Ty.weaken_subst_singleton
            (codomainType.subst typeSubstitution)
            (domainType.subst typeSubstitution)) ▸
          Term.subst0 (bodyCastEq ▸ substitutedBody) substitutedArgAfter
      let targetEquality :
          primitiveTarget =
          Term.subst termSubstitution
            ((Ty.weaken_subst_singleton codomainType domainType) ▸
              Term.subst0 body argAfter) :=
        eq_of_heq (HEq.symm (by
          apply HEq.trans
            (Term.subst_HEq_cast_input termSubstitution
              (Ty.weaken_subst_singleton codomainType domainType)
              (Term.subst0 body argAfter))
          apply HEq.trans
            (Term.subst0_subst_HEq termSubstitution body argAfter)
          apply HEq.trans
            (HEq.symm
              (Term.subst0_HEq_cast_input bodyCastEq
                substitutedBody substitutedArgAfter))
          exact Term.castRight_HEq
            (Ty.weaken_subst_singleton
              (codomainType.subst typeSubstitution)
              (domainType.subst typeSubstitution))
            (Term.subst0 (bodyCastEq ▸ substitutedBody) substitutedArgAfter)))
      exact Step.parWithBi.castTarget targetEquality
        (Step.parWithBi.mk
          (Step.par.betaAppDeep fStep aStep)
          (Step.par.isBi.betaAppDeep fBi aBi))
  | betaAppPiDeep _functionBi _argBi functionIH argIH =>
      rename_i _ domainType codomainType _ body _ argAfter _ _
      obtain ⟨fStep, fBi⟩ := functionIH termSubstitution
      obtain ⟨aStep, aBi⟩ := argIH termSubstitution
      let resultTypeEquality :=
        Ty.subst0_subst_commute codomainType domainType typeSubstitution
      let targetEquality :
          resultTypeEquality.symm ▸
              Term.subst0
                (Term.subst (TermSubst.lift termSubstitution domainType) body)
                (Term.subst termSubstitution argAfter)
            = Term.subst termSubstitution (Term.subst0 body argAfter) :=
        eq_of_heq
          (HEq.trans (eqRec_heq _ _)
            (HEq.symm (Term.subst0_subst_HEq termSubstitution body argAfter)))
      exact Step.parWithBi.castTarget targetEquality
        (Step.parWithBi.castBoth resultTypeEquality.symm
          (Step.parWithBi.mk
            (Step.par.betaAppPiDeep fStep aStep)
            (Step.par.isBi.betaAppPiDeep fBi aBi)))
  | betaFstPairDeep _pairBi pairIH =>
      obtain ⟨pStep, pBi⟩ := pairIH termSubstitution
      exact Step.parWithBi.mk
        (Step.par.betaFstPairDeep pStep)
        (Step.par.isBi.betaFstPairDeep pBi)
  | betaSndPairDeep _pairBi pairIH =>
      -- Implicits: ctx, firstType, secondType, pairTerm, firstVal,
      -- secondVal, pairStep — 7.
      rename_i _ firstType secondType _ _ secondVal _
      obtain ⟨pStep, pBi⟩ := pairIH termSubstitution
      let resultTypeEquality :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      let targetEquality :
          resultTypeEquality.symm ▸
              ((Ty.subst0_subst_commute secondType firstType typeSubstitution) ▸
                Term.subst termSubstitution secondVal)
            = Term.subst termSubstitution secondVal :=
        eq_of_heq (HEq.trans (eqRec_heq _ _) (eqRec_heq _ _))
      exact Step.parWithBi.castTarget targetEquality
        (Step.parWithBi.castBoth resultTypeEquality.symm
          (Step.parWithBi.mk
            (Step.par.betaSndPairDeep pStep)
            (Step.par.isBi.betaSndPairDeep pBi)))
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

/-! ## Chain-level subst_compatible + β-workhorse for parStarWithBi.

Lifts the single-step `Step.parWithBi.subst_compatible` to chains
via `parStarWithBi.trans`.  Then specialises to `Term.subst0` to
give the β-case workhorse used by the typed
`cd_lemma_star_with_bi` aggregator. -/

/-- Chain-level subst-compatibility for parStarWithBi: a paired
chain on `before` / `after` lifts to a paired chain on their
substitutions. -/
theorem Step.parStarWithBi.subst_compatible
    {mode : Mode} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubstitution : Subst level sourceScope targetScope}
    (termSubstitution : TermSubst sourceCtx targetCtx typeSubstitution)
    {termType : Ty level sourceScope}
    {beforeTerm afterTerm : Term sourceCtx termType}
    (chain : Step.parStarWithBi beforeTerm afterTerm) :
    Step.parStarWithBi
      (Term.subst termSubstitution beforeTerm)
      (Term.subst termSubstitution afterTerm) := by
  induction chain with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restChain restIH =>
      exact Step.parStarWithBi.trans
        (Step.parWithBi.subst_compatible termSubstitution
          (Step.parWithBi.mk _ firstBi)).toIsBi
        restIH

/-- **Body-side multi-step subst0 (paired)**.  A `parStarWithBi`
chain on the body lifts through `Term.subst0 _ argument` (with the
argument fixed). -/
theorem Term.subst0_parStarWithBi_body
    {mode : Mode} {scope : Nat} {sourceCtx : Ctx mode level scope}
    {argType : Ty level scope} {bodyType : Ty level (scope + 1)}
    {firstBody secondBody : Term (sourceCtx.cons argType) bodyType}
    (bodyChain : Step.parStarWithBi firstBody secondBody)
    (argument : Term sourceCtx argType) :
    Step.parStarWithBi
      (Term.subst0 firstBody argument)
      (Term.subst0 secondBody argument) :=
  Step.parStarWithBi.subst_compatible (TermSubst.singleton argument) bodyChain

/-! ## Paired pointwise substitution.

Paired analogues of `TermSubst.par_lift`, `Term.subst_par_pointwise`,
and `TermSubst.singleton_par_pointwise` from `ParSubst.lean`.  Each
mirrors its plain (`Step.par`) counterpart, but constructs *paired*
witnesses (`Step.parWithBi`) so isBi propagates uniformly.

The lift case at non-zero positions uses `Step.parWithBi.rename_
compatible` (just landed) to push the user-supplied paired step
through `Term.weaken`.

Used by `Term.subst0_parStarWithBi_argument` to discharge the
single-link case of the argument-side workhorse.  -/

/-- Paired binder lift: two pointwise-paired `TermSubst`s remain
paired after lifting under a binder.  Position 0 produces
`Term.var 0` on both sides (refl); position `k+1` lifts the
original paired step via `Step.parWithBi.rename_compatible` on the
weakening renaming. -/
theorem TermSubst.parWithBi_lift
    {mode : Mode} {scope scope' : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level scope'}
    {typeSubstitution : Subst level scope scope'}
    {firstSubstitution secondSubstitution :
      TermSubst sourceCtx targetCtx typeSubstitution}
    (related : ∀ position,
      Step.parWithBi (firstSubstitution position) (secondSubstitution position))
    (newType : Ty level scope) :
    ∀ position,
      Step.parWithBi
        ((firstSubstitution.lift newType) position)
        ((secondSubstitution.lift newType) position) := by
  intro position
  match position with
  | ⟨0, _⟩ =>
      simp only [TermSubst.lift]
      exact Step.parWithBi.castBoth
        (Ty.subst_weaken_commute newType typeSubstitution).symm
        ⟨Step.par.refl _, Step.par.isBi.refl _⟩
  | ⟨index + 1, isWithinBound⟩ =>
      simp only [TermSubst.lift]
      exact Step.parWithBi.castBoth
        (Ty.subst_weaken_commute
          (varType sourceCtx ⟨index, Nat.lt_of_succ_lt_succ isWithinBound⟩)
          typeSubstitution).symm
        (Step.parWithBi.rename_compatible
          (TermRenaming.weaken targetCtx (newType.subst typeSubstitution))
          (related ⟨index, Nat.lt_of_succ_lt_succ isWithinBound⟩))

/-- **Paired pointwise substitution.**  When two TermSubsts are
pointwise-paired (Step.parWithBi at every position), substituting
the same term through them yields a paired Step.parWithBi result.

Structural induction on the term, mirroring
`Term.subst_par_pointwise`.  Each constructor's recursive arm
applies the corresponding paired cong rule (`Step.par.<ctor>` +
`Step.par.isBi.<ctor>`) to the paired IHs; binder cases use
`TermSubst.parWithBi_lift`. -/
theorem Term.subst_parWithBi_pointwise
    {mode : Mode} {scope scope' : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level scope'}
    {typeSubstitution : Subst level scope scope'}
    {firstSubstitution secondSubstitution :
      TermSubst sourceCtx targetCtx typeSubstitution}
    (related : ∀ position,
      Step.parWithBi (firstSubstitution position) (secondSubstitution position)) :
    {T : Ty level scope} → (term : Term sourceCtx T) →
      Step.parWithBi
        (Term.subst firstSubstitution term)
        (Term.subst secondSubstitution term)
  | _, .var position => by
      simp only [Term.subst]
      exact related position
  | _, .unit => ⟨Step.par.refl _, Step.par.isBi.refl _⟩
  | _, .lam (codomainType := codomainType) body => by
      simp only [Term.subst]
      obtain ⟨bStep, bBi⟩ :=
        Term.subst_parWithBi_pointwise
          (TermSubst.parWithBi_lift related _) body
      let castedStep := Step.par.castBoth
        (Ty.subst_weaken_commute codomainType typeSubstitution) bStep
      let castedBi := Step.par.isBi.castBoth
        (Ty.subst_weaken_commute codomainType typeSubstitution) bBi
      exact ⟨Step.par.lam castedStep, Step.par.isBi.lam castedBi⟩
  | _, .app function argument => by
      obtain ⟨fStep, fBi⟩ := Term.subst_parWithBi_pointwise related function
      obtain ⟨aStep, aBi⟩ := Term.subst_parWithBi_pointwise related argument
      exact ⟨Step.par.app fStep aStep, Step.par.isBi.app fBi aBi⟩
  | _, .lamPi body => by
      simp only [Term.subst]
      obtain ⟨bStep, bBi⟩ :=
        Term.subst_parWithBi_pointwise
          (TermSubst.parWithBi_lift related _) body
      exact ⟨Step.par.lamPi bStep, Step.par.isBi.lamPi bBi⟩
  | _, .appPi (domainType := domainType) (codomainType := codomainType)
        resultEq function argument => by
      -- W9.B1.1 — equation-bearing appPi.  Cases on resultEq normalises shape.
      cases resultEq
      simp only [Term.subst]
      obtain ⟨fStep, fBi⟩ := Term.subst_parWithBi_pointwise related function
      obtain ⟨aStep, aBi⟩ := Term.subst_parWithBi_pointwise related argument
      let typeEq :=
        (Ty.subst0_subst_commute codomainType domainType typeSubstitution).symm
      exact ⟨Step.par.castBoth typeEq (Step.par.appPi fStep aStep),
             Step.par.isBi.castBoth typeEq (Step.par.isBi.appPi fBi aBi)⟩
  | _, .pair (firstType := firstType) (secondType := secondType)
        firstVal secondVal => by
      simp only [Term.subst]
      obtain ⟨fStep, fBi⟩ := Term.subst_parWithBi_pointwise related firstVal
      obtain ⟨sStep, sBi⟩ := Term.subst_parWithBi_pointwise related secondVal
      let typeEq :=
        Ty.subst0_subst_commute secondType firstType typeSubstitution
      exact ⟨Step.par.pair fStep (Step.par.castBoth typeEq sStep),
             Step.par.isBi.pair fBi (Step.par.isBi.castBoth typeEq sBi)⟩
  | _, .fst pairTerm => by
      obtain ⟨pStep, pBi⟩ := Term.subst_parWithBi_pointwise related pairTerm
      exact ⟨Step.par.fst pStep, Step.par.isBi.fst pBi⟩
  | _, .snd (firstType := firstType) (secondType := secondType)
        pairTerm resultEq => by
      -- W9.B1.2 — equation-bearing snd.  Cases on resultEq normalises shape.
      cases resultEq
      simp only [Term.subst]
      obtain ⟨pStep, pBi⟩ := Term.subst_parWithBi_pointwise related pairTerm
      let typeEq :=
        (Ty.subst0_subst_commute secondType firstType typeSubstitution).symm
      exact ⟨Step.par.castBoth typeEq (Step.par.snd pStep),
             Step.par.isBi.castBoth typeEq (Step.par.isBi.snd pBi)⟩
  | _, .boolTrue => ⟨Step.par.refl _, Step.par.isBi.refl _⟩
  | _, .boolFalse => ⟨Step.par.refl _, Step.par.isBi.refl _⟩
  | _, .boolElim scrutinee thenBranch elseBranch => by
      obtain ⟨sStep, sBi⟩ := Term.subst_parWithBi_pointwise related scrutinee
      obtain ⟨tStep, tBi⟩ := Term.subst_parWithBi_pointwise related thenBranch
      obtain ⟨eStep, eBi⟩ := Term.subst_parWithBi_pointwise related elseBranch
      exact ⟨Step.par.boolElim sStep tStep eStep,
             Step.par.isBi.boolElim sBi tBi eBi⟩
  | _, .natZero => ⟨Step.par.refl _, Step.par.isBi.refl _⟩
  | _, .natSucc predecessor => by
      obtain ⟨pStep, pBi⟩ := Term.subst_parWithBi_pointwise related predecessor
      exact ⟨Step.par.natSucc pStep, Step.par.isBi.natSucc pBi⟩
  | _, .natElim scrutinee zeroBranch succBranch => by
      obtain ⟨sStep, sBi⟩ := Term.subst_parWithBi_pointwise related scrutinee
      obtain ⟨zStep, zBi⟩ := Term.subst_parWithBi_pointwise related zeroBranch
      obtain ⟨ssStep, ssBi⟩ := Term.subst_parWithBi_pointwise related succBranch
      exact ⟨Step.par.natElim sStep zStep ssStep,
             Step.par.isBi.natElim sBi zBi ssBi⟩
  | _, .natRec scrutinee zeroBranch succBranch => by
      obtain ⟨sStep, sBi⟩ := Term.subst_parWithBi_pointwise related scrutinee
      obtain ⟨zStep, zBi⟩ := Term.subst_parWithBi_pointwise related zeroBranch
      obtain ⟨ssStep, ssBi⟩ := Term.subst_parWithBi_pointwise related succBranch
      exact ⟨Step.par.natRec sStep zStep ssStep,
             Step.par.isBi.natRec sBi zBi ssBi⟩
  | _, .listNil => ⟨Step.par.refl _, Step.par.isBi.refl _⟩
  | _, .listCons head tail => by
      obtain ⟨hStep, hBi⟩ := Term.subst_parWithBi_pointwise related head
      obtain ⟨tStep, tBi⟩ := Term.subst_parWithBi_pointwise related tail
      exact ⟨Step.par.listCons hStep tStep, Step.par.isBi.listCons hBi tBi⟩
  | _, .listElim scrutinee nilBranch consBranch => by
      obtain ⟨sStep, sBi⟩ := Term.subst_parWithBi_pointwise related scrutinee
      obtain ⟨nStep, nBi⟩ := Term.subst_parWithBi_pointwise related nilBranch
      obtain ⟨cStep, cBi⟩ := Term.subst_parWithBi_pointwise related consBranch
      exact ⟨Step.par.listElim sStep nStep cStep,
             Step.par.isBi.listElim sBi nBi cBi⟩
  | _, .optionNone => ⟨Step.par.refl _, Step.par.isBi.refl _⟩
  | _, .optionSome value => by
      obtain ⟨vStep, vBi⟩ := Term.subst_parWithBi_pointwise related value
      exact ⟨Step.par.optionSome vStep, Step.par.isBi.optionSome vBi⟩
  | _, .optionMatch scrutinee noneBranch someBranch => by
      obtain ⟨sStep, sBi⟩ := Term.subst_parWithBi_pointwise related scrutinee
      obtain ⟨nStep, nBi⟩ := Term.subst_parWithBi_pointwise related noneBranch
      obtain ⟨smStep, smBi⟩ := Term.subst_parWithBi_pointwise related someBranch
      exact ⟨Step.par.optionMatch sStep nStep smStep,
             Step.par.isBi.optionMatch sBi nBi smBi⟩
  | _, .eitherInl value => by
      obtain ⟨vStep, vBi⟩ := Term.subst_parWithBi_pointwise related value
      exact ⟨Step.par.eitherInl vStep, Step.par.isBi.eitherInl vBi⟩
  | _, .eitherInr value => by
      obtain ⟨vStep, vBi⟩ := Term.subst_parWithBi_pointwise related value
      exact ⟨Step.par.eitherInr vStep, Step.par.isBi.eitherInr vBi⟩
  | _, .eitherMatch scrutinee leftBranch rightBranch => by
      obtain ⟨sStep, sBi⟩ := Term.subst_parWithBi_pointwise related scrutinee
      obtain ⟨lStep, lBi⟩ := Term.subst_parWithBi_pointwise related leftBranch
      obtain ⟨rStep, rBi⟩ := Term.subst_parWithBi_pointwise related rightBranch
      exact ⟨Step.par.eitherMatch sStep lStep rStep,
             Step.par.isBi.eitherMatch sBi lBi rBi⟩
  | _, .refl _ => ⟨Step.par.refl _, Step.par.isBi.refl _⟩
  | _, .idJ baseCase witness => by
      obtain ⟨bStep, bBi⟩ := Term.subst_parWithBi_pointwise related baseCase
      obtain ⟨wStep, wBi⟩ := Term.subst_parWithBi_pointwise related witness
      exact ⟨Step.par.idJ bStep wStep, Step.par.isBi.idJ bBi wBi⟩

/-- **Paired pointwise singleton.**  A paired Step.parWithBi on the
substituent lifts to a paired pointwise relation on
`TermSubst.singleton`s.  Position 0 carries the user-supplied
paired step (modulo a `Ty.weaken_subst_singleton` cast); positions
`k+1` are paired-refl on `Term.var ⟨k, _⟩`. -/
theorem TermSubst.singleton_parWithBi_pointwise
    {mode : Mode} {scope : Nat} {sourceCtx : Ctx mode level scope}
    {argType : Ty level scope}
    {firstArgument secondArgument : Term sourceCtx argType}
    (argumentPaired : Step.parWithBi firstArgument secondArgument) :
    ∀ position,
      Step.parWithBi
        ((TermSubst.singleton firstArgument) position)
        ((TermSubst.singleton secondArgument) position) := by
  intro position
  match position with
  | ⟨0, _⟩ =>
      simp only [TermSubst.singleton]
      exact Step.parWithBi.castBoth
        (Ty.weaken_subst_singleton argType argType).symm
        argumentPaired
  | ⟨index + 1, isWithinBound⟩ =>
      simp only [TermSubst.singleton]
      exact Step.parWithBi.castBoth
        (Ty.weaken_subst_singleton
          (varType sourceCtx ⟨index, Nat.lt_of_succ_lt_succ isWithinBound⟩)
          argType).symm
        ⟨Step.par.refl _, Step.par.isBi.refl _⟩

/-- **Argument-side multi-step subst0 (paired)**.  A
`parStarWithBi` chain on the argument lifts through
`Term.subst0 body _` (with the body fixed).  Proof: induct on the
chain; each link lifts via `Term.subst_parWithBi_pointwise` +
`TermSubst.singleton_parWithBi_pointwise`. -/
theorem Term.subst0_parStarWithBi_argument
    {mode : Mode} {scope : Nat} {sourceCtx : Ctx mode level scope}
    {argType : Ty level scope} {bodyType : Ty level (scope + 1)}
    (body : Term (sourceCtx.cons argType) bodyType)
    {firstArgument secondArgument : Term sourceCtx argType}
    (argumentChain : Step.parStarWithBi firstArgument secondArgument) :
    Step.parStarWithBi
      (Term.subst0 body firstArgument)
      (Term.subst0 body secondArgument) := by
  induction argumentChain with
  | refl _ => exact Step.parStarWithBi.refl _
  | trans firstBi _restChain restIH =>
      let linkPaired := Term.subst_parWithBi_pointwise
        (TermSubst.singleton_parWithBi_pointwise
          (Step.parWithBi.mk _ firstBi)) body
      exact Step.parStarWithBi.trans linkPaired.toIsBi restIH

/-- **The β-workhorse, paired form.**  Joint chain on body and
argument lifts to a chain on `Term.subst0`.  Used by the β cases
of the typed `cd_lemma_star_with_bi` aggregator. -/
theorem Step.parStarWithBi.subst0_parStarWithBi
    {mode : Mode} {scope : Nat} {sourceCtx : Ctx mode level scope}
    {argType : Ty level scope} {bodyType : Ty level (scope + 1)}
    {firstBody secondBody : Term (sourceCtx.cons argType) bodyType}
    {firstArgument secondArgument : Term sourceCtx argType}
    (bodyChain : Step.parStarWithBi firstBody secondBody)
    (argumentChain : Step.parStarWithBi firstArgument secondArgument) :
    Step.parStarWithBi
      (Term.subst0 firstBody firstArgument)
      (Term.subst0 secondBody secondArgument) :=
  Step.parStarWithBi.append
    (Term.subst0_parStarWithBi_body bodyChain firstArgument)
    (Term.subst0_parStarWithBi_argument secondBody argumentChain)

end LeanFX.Syntax

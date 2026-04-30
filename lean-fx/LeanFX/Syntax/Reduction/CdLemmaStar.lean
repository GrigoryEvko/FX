import LeanFX.Syntax.Reduction.ParBi
import LeanFX.Syntax.Reduction.ParInversion

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Step.par.cd_lemma_star` — typed complete-development lemma (βι-only).

Statement: every typed parallel step `Step.par sourceTerm targetTerm`
that is `Step.par.isBi`-witnessed (i.e., uses no η-rule anywhere)
satisfies `Step.parStar targetTerm (Term.cd sourceTerm)`.

Together with `Step.par.cd_dominates` (every term parallel-reduces to
its complete development), this is the typed Tait–Martin-Löf complete-
development pair restricted to βι.  The diamond property and
confluence of `Step.parStar` for βι follow immediately.

η is excluded: `Term.cd` deliberately does not η-contract (§
CompleteDevelopment.lean), so a parallel step that fires η produces a
target outside `Term.cd`'s reach.  This is why `Step.par.isBi` gates
the lemma: η constructors of `Step.par` have no `isBi` case, so the
proof's `induction isBi` skips them vacuously.

## Proof architecture

Direct typed-level induction on `isBi` discharges 37 of the 54 βι
cases cleanly:

  * **Refl**: `Step.par.cd_dominates` lifted to `parStar`.
  * **Pure-cong (no contraction inside `cd`)** — lam, lamPi, pair,
    natSucc, listCons, optionSome, eitherInl, eitherInr — `simp only
    [Term.cd]` + matching `Step.parStar.<ctor>_cong` rule applied to
    IHs.
  * **Eliminator-cong (cd may contract)** — app, appPi, fst, snd,
    boolElim, natElim, natRec, listElim, optionMatch, eitherMatch,
    idJ — `simp only [Term.cd]` + `split` on the inner match; redex
    arms append a single contracting `Step.par` step via `snoc`;
    wildcard arm uses the cong rule.
  * **Shallow β/ι** — betaApp, betaAppPi, betaFstPair, betaSndPair,
    iotaBoolElim{True,False}, iotaNatElim{Zero,Succ}, etc. — `simp
    only [Term.cd]` exposes the same redex on the developed source;
    `Step.parStar.subst0_parStar` (β) or the appropriate IH (ι)
    closes.

The 17 **deep β/ι** cases (betaAppDeep, betaAppPiDeep, etc.) need
typed parStar-inversion to extract the contracted shape from the IH
(e.g., `Step.parStar (Term.lam body) target → ∃ body', target =
Term.lam body'`).  Lean's dependent-elimination check rejects direct
`cases step` on such inversions because constructors like `betaAppPi`
have target types involving the non-injective `Ty.subst0`.

The architecturally clean unblock is the **typed→raw bridge**
(`Step.par.toRawBridge`, active at
`LeanFX/Syntax/Reduction/ParToRawBridge.lean`):

  1. Lift `Step.par s t` to `RawStep.par s.toRaw t.toRaw` via
     a 54-case structural translation, gated on `Step.par.isBi`
     so the two η constructors are excluded vacuously.
  2. Apply the already-proven raw `RawStep.par.lam_inv` (and
     companions) to extract structural information from the IH.
  3. Use the structural information to discharge the typed goal.

The bridge currently discharges 50 of 54 βι cases.  The four
dependent β cases (`betaApp`, `betaAppPi`, `betaAppDeep`,
`betaAppPiDeep`) carry `sorry` markers tagged for Wave 6
β-surgery (`Subst.singleton` → `Subst.termSingleton` migration,
tasks #1006-#1014).  Once Wave 6 lands, the bridge is fully
zero-sorry and the 17 Deep βι cases of `cd_lemma_star` become
direct corollaries of the typed parStar inversions derived
from the bridge. -/

/-- Smoke skeleton that proves cd_lemma_star for the refl case via
the `cd_dominates → parStar` lift. -/
theorem Step.par.cd_lemma_star_refl_only_smoke
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    (term : Term ctx termType) :
    Step.parStar term (Term.cd term) :=
  Step.par.toParStar (Step.par.cd_dominates term)

/-- Discharge of the `Step.par.isBi.refl` constructor case.  Pulled
out as a standalone helper so the eventual full `cd_lemma_star`
can reuse it without re-proving via `cd_dominates`. -/
theorem Step.par.cd_lemma_star_refl_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    (term : Term ctx termType) :
    Step.parStar term (Term.cd term) :=
  Step.par.toParStar (Step.par.cd_dominates term)

/-- Discharge of the `Step.par.isBi.lam` constructor case.  Given
the body-IH (Step.parStar on the body's reduct), `simp [Term.cd]`
unfolds `Term.cd (Term.lam body)` to `Term.lam (Term.cd body)`,
then `Step.parStar.lam_cong` lifts the IH through the binder. -/
theorem Step.par.cd_lemma_star_lam_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body body' : Term (ctx.cons domainType) codomainType.weaken}
    (bodyIH : Step.parStar body' (Term.cd body)) :
    Step.parStar (Term.lam (codomainType := codomainType) body')
                 (Term.cd (Term.lam (codomainType := codomainType) body)) := by
  simp only [Term.cd]
  exact Step.parStar.lam_cong bodyIH

/-- Discharge of the `Step.par.isBi.lamPi` constructor case. -/
theorem Step.par.cd_lemma_star_lamPi_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body body' : Term (ctx.cons domainType) codomainType}
    (bodyIH : Step.parStar body' (Term.cd body)) :
    Step.parStar (Term.lamPi (domainType := domainType) body')
                 (Term.cd (Term.lamPi (domainType := domainType) body)) := by
  simp only [Term.cd]
  exact Step.parStar.lamPi_cong bodyIH

/-! ### Pure congruence cases (no contraction inside `Term.cd`).

For constructors whose `Term.cd` arm just recurses on subterms
without contracting any redex, the cd_lemma_star case is simply
`simp only [Term.cd]` plus the matching `parStar.<ctor>_cong`
rule applied to the IHs. -/

/-- Discharge of the `Step.par.isBi.pair` constructor case. -/
theorem Step.par.cd_lemma_star_pair_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal firstVal' : Term ctx firstType}
    {secondVal secondVal' : Term ctx (secondType.subst0 firstType)}
    (firstIH : Step.parStar firstVal' (Term.cd firstVal))
    (secondIH : Step.parStar secondVal' (Term.cd secondVal)) :
    Step.parStar (Term.pair firstVal' secondVal')
                 (Term.cd (Term.pair firstVal secondVal)) := by
  simp only [Term.cd]
  exact Step.parStar.pair_cong firstIH secondIH

/-- Discharge of the `Step.par.isBi.natSucc` constructor case. -/
theorem Step.par.cd_lemma_star_natSucc_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {pred pred' : Term ctx Ty.nat}
    (predIH : Step.parStar pred' (Term.cd pred)) :
    Step.parStar (Term.natSucc pred') (Term.cd (Term.natSucc pred)) := by
  simp only [Term.cd]
  exact Step.parStar.natSucc_cong predIH

/-- Discharge of the `Step.par.isBi.listCons` constructor case. -/
theorem Step.par.cd_lemma_star_listCons_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {head head' : Term ctx elementType}
    {tail tail' : Term ctx (Ty.list elementType)}
    (headIH : Step.parStar head' (Term.cd head))
    (tailIH : Step.parStar tail' (Term.cd tail)) :
    Step.parStar (Term.listCons head' tail')
                 (Term.cd (Term.listCons head tail)) := by
  simp only [Term.cd]
  exact Step.parStar.listCons_cong headIH tailIH

/-- Discharge of the `Step.par.isBi.optionSome` constructor case. -/
theorem Step.par.cd_lemma_star_optionSome_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {value value' : Term ctx elementType}
    (valueIH : Step.parStar value' (Term.cd value)) :
    Step.parStar (Term.optionSome value')
                 (Term.cd (Term.optionSome value)) := by
  simp only [Term.cd]
  exact Step.parStar.optionSome_cong valueIH

/-- Discharge of the `Step.par.isBi.eitherInl` constructor case. -/
theorem Step.par.cd_lemma_star_eitherInl_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value value' : Term ctx leftType}
    (valueIH : Step.parStar value' (Term.cd value)) :
    Step.parStar (Term.eitherInl (rightType := rightType) value')
                 (Term.cd (Term.eitherInl (rightType := rightType) value)) := by
  simp only [Term.cd]
  exact Step.parStar.eitherInl_cong valueIH

/-- Discharge of the `Step.par.isBi.eitherInr` constructor case. -/
theorem Step.par.cd_lemma_star_eitherInr_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value value' : Term ctx rightType}
    (valueIH : Step.parStar value' (Term.cd value)) :
    Step.parStar (Term.eitherInr (leftType := leftType) value')
                 (Term.cd (Term.eitherInr (leftType := leftType) value)) := by
  simp only [Term.cd]
  exact Step.parStar.eitherInr_cong valueIH

/-! ### Eliminator congruence cases (`Term.cd` may contract a redex).

For elimination forms whose `Term.cd` arm splits on the developed
scrutinee shape, we `simp only [Term.cd]` to expose the inner
match, then `split` on the match arms.  Redex arms add a single
contracting `Step.par` step via `snoc`; wildcard arms apply the
matching congruence rule. -/

/-- Discharge of the `Step.par.isBi.app` constructor case.  Handles
the cd-split: when `Term.cd f` reduces to a literal `Term.lam`, an
extra β-step appends; otherwise plain app congruence. -/
theorem Step.par.cd_lemma_star_app_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionTerm functionTerm' : Term ctx (Ty.arrow domainType codomainType)}
    {argumentTerm argumentTerm' : Term ctx domainType}
    (functionIH : Step.parStar functionTerm' (Term.cd functionTerm))
    (argumentIH : Step.parStar argumentTerm' (Term.cd argumentTerm)) :
    Step.parStar (Term.app functionTerm' argumentTerm')
                 (Term.cd (Term.app functionTerm argumentTerm)) := by
  simp only [Term.cd]
  split
  case _ developedBody developedFunctionEq =>
      have functionIHcast : Step.parStar functionTerm' (Term.lam developedBody) :=
        developedFunctionEq ▸ functionIH
      exact Step.parStar.snoc
        (Step.parStar.app_cong functionIHcast argumentIH)
        (Step.par.betaApp (Step.par.refl _) (Step.par.refl _))
  case _ =>
      exact Step.parStar.app_cong functionIH argumentIH

/-- Discharge of the `Step.par.isBi.appPi` constructor case. -/
theorem Step.par.cd_lemma_star_appPi_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {functionTerm functionTerm' : Term ctx (Ty.piTy domainType codomainType)}
    {argumentTerm argumentTerm' : Term ctx domainType}
    (functionIH : Step.parStar functionTerm' (Term.cd functionTerm))
    (argumentIH : Step.parStar argumentTerm' (Term.cd argumentTerm)) :
    Step.parStar (Term.appPi functionTerm' argumentTerm')
                 (Term.cd (Term.appPi functionTerm argumentTerm)) := by
  simp only [Term.cd]
  split
  case _ developedBody developedFunctionEq =>
      have functionIHcast : Step.parStar functionTerm' (Term.lamPi developedBody) :=
        developedFunctionEq ▸ functionIH
      exact Step.parStar.snoc
        (Step.parStar.appPi_cong functionIHcast argumentIH)
        (Step.par.betaAppPi (Step.par.refl _) (Step.par.refl _))
  case _ =>
      exact Step.parStar.appPi_cong functionIH argumentIH

/-- Discharge of the `Step.par.isBi.fst` constructor case. -/
theorem Step.par.cd_lemma_star_fst_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairTerm pairTerm' : Term ctx (Ty.sigmaTy firstType secondType)}
    (pairIH : Step.parStar pairTerm' (Term.cd pairTerm)) :
    Step.parStar (Term.fst pairTerm') (Term.cd (Term.fst pairTerm)) := by
  simp only [Term.cd]
  split
  case _ developedFirst developedSecond developedPairEq =>
      have pairIHcast : Step.parStar pairTerm'
          (Term.pair (firstType := firstType) (secondType := secondType)
                     developedFirst developedSecond) :=
        developedPairEq ▸ pairIH
      exact Step.parStar.snoc
        (Step.parStar.fst_cong pairIHcast)
        (Step.par.betaFstPair _ (Step.par.refl _))
  case _ =>
      exact Step.parStar.fst_cong pairIH

/-- Discharge of the `Step.par.isBi.snd` constructor case. -/
theorem Step.par.cd_lemma_star_snd_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairTerm pairTerm' : Term ctx (Ty.sigmaTy firstType secondType)}
    (pairIH : Step.parStar pairTerm' (Term.cd pairTerm)) :
    Step.parStar (Term.snd pairTerm') (Term.cd (Term.snd pairTerm)) := by
  simp only [Term.cd]
  split
  case _ developedFirst developedSecond developedPairEq =>
      have pairIHcast : Step.parStar pairTerm'
          (Term.pair (firstType := firstType) (secondType := secondType)
                     developedFirst developedSecond) :=
        developedPairEq ▸ pairIH
      exact Step.parStar.snoc
        (Step.parStar.snd_cong pairIHcast)
        (Step.par.betaSndPair _ (Step.par.refl _))
  case _ =>
      exact Step.parStar.snd_cong pairIH

/-- Discharge of the `Step.par.isBi.boolElim` constructor case.
Three-arm split: boolTrue / boolFalse / wildcard. -/
theorem Step.par.cd_lemma_star_boolElim_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.bool}
    {thenBranch thenBranch' : Term ctx resultType}
    {elseBranch elseBranch' : Term ctx resultType}
    (scrutineeIH : Step.parStar scrutinee' (Term.cd scrutinee))
    (thenIH : Step.parStar thenBranch' (Term.cd thenBranch))
    (elseIH : Step.parStar elseBranch' (Term.cd elseBranch)) :
    Step.parStar (Term.boolElim scrutinee' thenBranch' elseBranch')
                 (Term.cd (Term.boolElim scrutinee thenBranch elseBranch)) := by
  simp only [Term.cd]
  split
  case _ developedScrutineeEq =>
      have scrutineeIHcast : Step.parStar scrutinee' Term.boolTrue :=
        developedScrutineeEq ▸ scrutineeIH
      exact Step.parStar.snoc
        (Step.parStar.boolElim_cong scrutineeIHcast thenIH elseIH)
        (Step.par.iotaBoolElimTrue _ (Step.par.refl _))
  case _ developedScrutineeEq =>
      have scrutineeIHcast : Step.parStar scrutinee' Term.boolFalse :=
        developedScrutineeEq ▸ scrutineeIH
      exact Step.parStar.snoc
        (Step.parStar.boolElim_cong scrutineeIHcast thenIH elseIH)
        (Step.par.iotaBoolElimFalse _ (Step.par.refl _))
  case _ =>
      exact Step.parStar.boolElim_cong scrutineeIH thenIH elseIH

/-- Discharge of the `Step.par.isBi.natElim` constructor case.
Three-arm split: natZero / natSucc / wildcard. -/
theorem Step.par.cd_lemma_star_natElim_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.nat}
    {zeroBranch zeroBranch' : Term ctx resultType}
    {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)}
    (scrutineeIH : Step.parStar scrutinee' (Term.cd scrutinee))
    (zeroIH : Step.parStar zeroBranch' (Term.cd zeroBranch))
    (succIH : Step.parStar succBranch' (Term.cd succBranch)) :
    Step.parStar (Term.natElim scrutinee' zeroBranch' succBranch')
                 (Term.cd (Term.natElim scrutinee zeroBranch succBranch)) := by
  simp only [Term.cd]
  split
  case _ developedScrutineeEq =>
      have scrutineeIHcast : Step.parStar scrutinee' Term.natZero :=
        developedScrutineeEq ▸ scrutineeIH
      exact Step.parStar.snoc
        (Step.parStar.natElim_cong scrutineeIHcast zeroIH succIH)
        (Step.par.iotaNatElimZero _ (Step.par.refl _))
  case _ developedPredecessor developedScrutineeEq =>
      have scrutineeIHcast : Step.parStar scrutinee'
          (Term.natSucc developedPredecessor) :=
        developedScrutineeEq ▸ scrutineeIH
      exact Step.parStar.snoc
        (Step.parStar.natElim_cong scrutineeIHcast zeroIH succIH)
        (Step.par.iotaNatElimSucc _ (Step.par.refl _) (Step.par.refl _))
  case _ =>
      exact Step.parStar.natElim_cong scrutineeIH zeroIH succIH

/-- Discharge of the `Step.par.isBi.natRec` constructor case.
Three-arm split: natZero / natSucc / wildcard. -/
theorem Step.par.cd_lemma_star_natRec_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx Ty.nat}
    {zeroBranch zeroBranch' : Term ctx resultType}
    {succBranch succBranch' : Term ctx
        (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (scrutineeIH : Step.parStar scrutinee' (Term.cd scrutinee))
    (zeroIH : Step.parStar zeroBranch' (Term.cd zeroBranch))
    (succIH : Step.parStar succBranch' (Term.cd succBranch)) :
    Step.parStar (Term.natRec scrutinee' zeroBranch' succBranch')
                 (Term.cd (Term.natRec scrutinee zeroBranch succBranch)) := by
  simp only [Term.cd]
  split
  case _ developedScrutineeEq =>
      have scrutineeIHcast : Step.parStar scrutinee' Term.natZero :=
        developedScrutineeEq ▸ scrutineeIH
      exact Step.parStar.snoc
        (Step.parStar.natRec_cong scrutineeIHcast zeroIH succIH)
        (Step.par.iotaNatRecZero _ (Step.par.refl _))
  case _ developedPredecessor developedScrutineeEq =>
      have scrutineeIHcast : Step.parStar scrutinee'
          (Term.natSucc developedPredecessor) :=
        developedScrutineeEq ▸ scrutineeIH
      exact Step.parStar.snoc
        (Step.parStar.natRec_cong scrutineeIHcast zeroIH succIH)
        (Step.par.iotaNatRecSucc (Step.par.refl _) (Step.par.refl _)
                                  (Step.par.refl _))
  case _ =>
      exact Step.parStar.natRec_cong scrutineeIH zeroIH succIH

/-- Discharge of the `Step.par.isBi.listElim` constructor case.
Three-arm split: listNil / listCons / wildcard. -/
theorem Step.par.cd_lemma_star_listElim_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.list elementType)}
    {nilBranch nilBranch' : Term ctx resultType}
    {consBranch consBranch' : Term ctx
        (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))}
    (scrutineeIH : Step.parStar scrutinee' (Term.cd scrutinee))
    (nilIH : Step.parStar nilBranch' (Term.cd nilBranch))
    (consIH : Step.parStar consBranch' (Term.cd consBranch)) :
    Step.parStar (Term.listElim scrutinee' nilBranch' consBranch')
                 (Term.cd (Term.listElim scrutinee nilBranch consBranch)) := by
  simp only [Term.cd]
  split
  case _ developedScrutineeEq =>
      have scrutineeIHcast : Step.parStar scrutinee' Term.listNil :=
        developedScrutineeEq ▸ scrutineeIH
      exact Step.parStar.snoc
        (Step.parStar.listElim_cong scrutineeIHcast nilIH consIH)
        (Step.par.iotaListElimNil _ (Step.par.refl _))
  case _ developedHead developedTail developedScrutineeEq =>
      have scrutineeIHcast : Step.parStar scrutinee'
          (Term.listCons developedHead developedTail) :=
        developedScrutineeEq ▸ scrutineeIH
      exact Step.parStar.snoc
        (Step.parStar.listElim_cong scrutineeIHcast nilIH consIH)
        (Step.par.iotaListElimCons _ (Step.par.refl _)
                                    (Step.par.refl _) (Step.par.refl _))
  case _ =>
      exact Step.parStar.listElim_cong scrutineeIH nilIH consIH

/-- Discharge of the `Step.par.isBi.optionMatch` constructor case.
Three-arm split: optionNone / optionSome / wildcard. -/
theorem Step.par.cd_lemma_star_optionMatch_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.option elementType)}
    {noneBranch noneBranch' : Term ctx resultType}
    {someBranch someBranch' : Term ctx (Ty.arrow elementType resultType)}
    (scrutineeIH : Step.parStar scrutinee' (Term.cd scrutinee))
    (noneIH : Step.parStar noneBranch' (Term.cd noneBranch))
    (someIH : Step.parStar someBranch' (Term.cd someBranch)) :
    Step.parStar (Term.optionMatch scrutinee' noneBranch' someBranch')
                 (Term.cd (Term.optionMatch scrutinee noneBranch someBranch)) := by
  simp only [Term.cd]
  split
  case _ developedScrutineeEq =>
      have scrutineeIHcast : Step.parStar scrutinee' Term.optionNone :=
        developedScrutineeEq ▸ scrutineeIH
      exact Step.parStar.snoc
        (Step.parStar.optionMatch_cong scrutineeIHcast noneIH someIH)
        (Step.par.iotaOptionMatchNone _ (Step.par.refl _))
  case _ developedValue developedScrutineeEq =>
      have scrutineeIHcast : Step.parStar scrutinee'
          (Term.optionSome developedValue) :=
        developedScrutineeEq ▸ scrutineeIH
      exact Step.parStar.snoc
        (Step.parStar.optionMatch_cong scrutineeIHcast noneIH someIH)
        (Step.par.iotaOptionMatchSome _ (Step.par.refl _) (Step.par.refl _))
  case _ =>
      exact Step.parStar.optionMatch_cong scrutineeIH noneIH someIH

/-- Discharge of the `Step.par.isBi.eitherMatch` constructor case.
Three-arm split: eitherInl / eitherInr / wildcard. -/
theorem Step.par.cd_lemma_star_eitherMatch_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee scrutinee' : Term ctx (Ty.either leftType rightType)}
    {leftBranch leftBranch' : Term ctx (Ty.arrow leftType resultType)}
    {rightBranch rightBranch' : Term ctx (Ty.arrow rightType resultType)}
    (scrutineeIH : Step.parStar scrutinee' (Term.cd scrutinee))
    (leftIH : Step.parStar leftBranch' (Term.cd leftBranch))
    (rightIH : Step.parStar rightBranch' (Term.cd rightBranch)) :
    Step.parStar (Term.eitherMatch scrutinee' leftBranch' rightBranch')
                 (Term.cd (Term.eitherMatch scrutinee leftBranch rightBranch)) := by
  simp only [Term.cd]
  split
  case _ developedValue developedScrutineeEq =>
      have scrutineeIHcast : Step.parStar scrutinee'
          (Term.eitherInl (rightType := rightType) developedValue) :=
        developedScrutineeEq ▸ scrutineeIH
      exact Step.parStar.snoc
        (Step.parStar.eitherMatch_cong scrutineeIHcast leftIH rightIH)
        (Step.par.iotaEitherMatchInl _ (Step.par.refl _) (Step.par.refl _))
  case _ developedValue developedScrutineeEq =>
      have scrutineeIHcast : Step.parStar scrutinee'
          (Term.eitherInr (leftType := leftType) developedValue) :=
        developedScrutineeEq ▸ scrutineeIH
      exact Step.parStar.snoc
        (Step.parStar.eitherMatch_cong scrutineeIHcast leftIH rightIH)
        (Step.par.iotaEitherMatchInr _ (Step.par.refl _) (Step.par.refl _))
  case _ =>
      exact Step.parStar.eitherMatch_cong scrutineeIH leftIH rightIH

/-- Discharge of the `Step.par.isBi.idJ` constructor case.  The
`Term.cd` arm goes through `Term.cd_idJ_redex`, which first splits on
endpoint equality (decidable, may evaluate to `false` for distinct
endpoints), then on the witness shape (`Term.refl` triggers ι;
otherwise idJ congruence).  Same-endpoint + refl-witness case
appends an `iotaIdJRefl` step; all others fall through to
`idJ_cong`. -/
theorem Step.par.cd_lemma_star_idJ_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {leftEnd rightEnd : RawTerm scope}
    {resultType : Ty level scope}
    {baseCase baseCase' : Term ctx resultType}
    {witness witness' : Term ctx (Ty.id carrier leftEnd rightEnd)}
    (baseIH : Step.parStar baseCase' (Term.cd baseCase))
    (witnessIH : Step.parStar witness' (Term.cd witness)) :
    Step.parStar (Term.idJ baseCase' witness')
                 (Term.cd (Term.idJ baseCase witness)) := by
  simp only [Term.cd, Term.cd_idJ_redex]
  split
  case _ endpointsEqual =>
      subst endpointsEqual
      simp only [Term.cd_idJ_redex_aligned]
      split
      next developedWitnessEq =>
          have witnessIHcast : Step.parStar witness' (Term.refl leftEnd) :=
            developedWitnessEq ▸ witnessIH
          exact Step.parStar.snoc
            (Step.parStar.idJ_cong baseIH witnessIHcast)
            (Step.par.iotaIdJRefl (Step.par.refl _))
      next =>
          exact Step.parStar.idJ_cong baseIH witnessIH
  case _ =>
      exact Step.parStar.idJ_cong baseIH witnessIH

/-! ### Shallow β/ι cases (literal redex source).

For these, `Term.cd` of the source contracts the same redex.  The
goal after `simp only [Term.cd]` matches the target up to a
developed-version substitution; either `Step.parStar.subst0_parStar`
(β) or the appropriate IH alone (ι) closes. -/

/-- Transport a `Step.parStar` chain across the same Ty equality on
both endpoints — analogue of `Step.par.castBoth`.  Used by the
shallow β cases where source and target carry matching
`Ty.weaken_subst_singleton` casts. -/
theorem Step.parStar.castBoth
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    (typeEquality : sourceType = targetType)
    {beforeTerm afterTerm : Term ctx sourceType}
    (chain : Step.parStar beforeTerm afterTerm) :
    Step.parStar (typeEquality ▸ beforeTerm) (typeEquality ▸ afterTerm) := by
  cases typeEquality
  exact chain

/-- Discharge of the `Step.par.isBi.betaApp` constructor case.
Source `Term.app (Term.lam body) arg`; target
`Ty.weaken_subst_singleton ▸ Term.subst0 body' arg'`.  `Term.cd`
of source: `Term.cd (Term.lam body)` = `Term.lam (Term.cd body)`,
so the lam arm of cd's app match fires deterministically, yielding
`Ty.weaken_subst_singleton ▸ Term.subst0 (Term.cd body) (Term.cd arg)`.
Closed by `subst0_parStar bodyIH argIH`. -/
theorem Step.par.cd_lemma_star_betaApp_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body body' : Term (ctx.cons domainType) codomainType.weaken}
    {arg arg' : Term ctx domainType}
    (bodyIH : Step.parStar body' (Term.cd body))
    (argIH : Step.parStar arg' (Term.cd arg)) :
    Step.parStar
        ((Ty.weaken_subst_singleton codomainType domainType) ▸
          Term.subst0 body' arg')
        (Term.cd
          (Term.app (Term.lam (codomainType := codomainType) body) arg)) := by
  simp only [Term.cd]
  exact Step.parStar.castBoth (Ty.weaken_subst_singleton codomainType domainType)
    (Step.parStar.subst0_parStar bodyIH argIH)

/-- Discharge of the `Step.par.isBi.betaAppPi` constructor case. -/
theorem Step.par.cd_lemma_star_betaAppPi_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {body body' : Term (ctx.cons domainType) codomainType}
    {arg arg' : Term ctx domainType}
    (bodyIH : Step.parStar body' (Term.cd body))
    (argIH : Step.parStar arg' (Term.cd arg)) :
    Step.parStar
        (Term.subst0 body' arg')
        (Term.cd
          (Term.appPi (Term.lamPi (domainType := domainType) body) arg)) := by
  simp only [Term.cd]
  exact Step.parStar.subst0_parStar bodyIH argIH

/-- Discharge of the `Step.par.isBi.betaFstPair` constructor case. -/
theorem Step.par.cd_lemma_star_betaFstPair_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {firstVal firstVal' : Term ctx firstType}
    (secondVal : Term ctx (secondType.subst0 firstType))
    (firstIH : Step.parStar firstVal' (Term.cd firstVal)) :
    Step.parStar firstVal'
                 (Term.cd
                   (Term.fst (Term.pair (firstType := firstType)
                                        (secondType := secondType)
                                        firstVal secondVal))) := by
  simp only [Term.cd]
  exact firstIH

/-- Discharge of the `Step.par.isBi.betaSndPair` constructor case. -/
theorem Step.par.cd_lemma_star_betaSndPair_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    (firstVal : Term ctx firstType)
    {secondVal secondVal' : Term ctx (secondType.subst0 firstType)}
    (secondIH : Step.parStar secondVal' (Term.cd secondVal)) :
    Step.parStar secondVal'
                 (Term.cd
                   (Term.snd (Term.pair (firstType := firstType)
                                        (secondType := secondType)
                                        firstVal secondVal))) := by
  simp only [Term.cd]
  exact secondIH

/-! ### Deep β cases (function/pair parallel-reduces to a redex shape).

These four cases were previously gated on either Wave 6 β-surgery
(raw bridge route) or the Wave 9 Term refactor.  W9.B1.7 unblocked
them without either prereq via the chain inversions
`Step.parStar.lam_target_inv_isBi` and `Step.parStar.pair_target_inv_isBi`,
which extract the contracted shape from an isBi-witnessed chain.

The case helpers take an additional `functionStarBi` (resp.
`pairStarBi`) hypothesis: the chain from the IH is itself
isBi-witnessed (it must be — the cd_lemma_star aggregator's
induction on isBi at the outer Step.par produces sub-chains whose
βι-only nature carries through, so the strengthened cd_lemma_star
will produce these witnesses for free).  Compare with the shallow
βι cases above, where the function/pair reduces to the redex via
`Step.par.refl`, so no inversion is needed. -/

/-- Discharge of the `Step.par.isBi.betaAppDeep` constructor case.
Source: `Term.app f arg`, where `Step.par f (Term.lam body)` —
i.e., `f` parallel-reduces to a literal lambda.  Target:
`Ty.weaken_subst_singleton ▸ Term.subst0 body arg'`.  The IH chain
`Step.parStar (Term.lam body) (Term.cd f)` together with its isBi
witness yields, via `lam_target_inv_isBi`, a body' s.t.
`Term.cd f = Term.lam body'` and `Step.parStar body body'`.
The lam arm of cd's app match then fires, and `subst0_parStar`
closes via `bodyStar` and `argIH`. -/
theorem Step.par.cd_lemma_star_betaAppDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionTerm : Term ctx (Ty.arrow domainType codomainType)}
    {body : Term (ctx.cons domainType) codomainType.weaken}
    {arg arg' : Term ctx domainType}
    {functionStar : Step.parStar
        (Term.lam (codomainType := codomainType) body) (Term.cd functionTerm)}
    (functionStarBi : Step.parStar.isBi functionStar)
    (argIH : Step.parStar arg' (Term.cd arg)) :
    Step.parStar
        ((Ty.weaken_subst_singleton codomainType domainType) ▸
            Term.subst0 body arg')
        (Term.cd (Term.app functionTerm arg)) := by
  obtain ⟨body', cdEq, bodyStar⟩ :=
    Step.parStar.lam_target_inv_isBi functionStarBi
  simp only [Term.cd, cdEq]
  exact Step.parStar.castBoth (Ty.weaken_subst_singleton codomainType domainType)
    (Step.parStar.subst0_parStar bodyStar argIH)

/-- Discharge of the `Step.par.isBi.betaAppPiDeep` constructor case.
Π-flavoured analogue of `betaAppDeep`: source `Term.appPi f arg`
with `Step.par f (Term.lamPi body)`; target `Term.subst0 body arg'`.
The IH chain `Step.parStar (Term.lamPi body) (Term.cd f)` together
with its isBi witness yields, via `lamPi_target_inv_isBi`, a body'
s.t. `Term.cd f = Term.lamPi body'` and `Step.parStar body body'`.
The lamPi arm of cd's appPi match then fires, and `subst0_parStar`
closes via `bodyStar` and `argIH`.  Note: no cast needed here
(unlike `betaAppDeep`) — Π-binder codomainType already has the
right scope. -/
theorem Step.par.cd_lemma_star_betaAppPiDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope} {codomainType : Ty level (scope + 1)}
    {functionTerm : Term ctx (Ty.piTy domainType codomainType)}
    {body : Term (ctx.cons domainType) codomainType}
    {arg arg' : Term ctx domainType}
    {functionStar : Step.parStar
        (Term.lamPi (domainType := domainType) body) (Term.cd functionTerm)}
    (functionStarBi : Step.parStar.isBi functionStar)
    (argIH : Step.parStar arg' (Term.cd arg)) :
    Step.parStar
        (Term.subst0 body arg')
        (Term.cd (Term.appPi functionTerm arg)) := by
  obtain ⟨body', cdEq, bodyStar⟩ :=
    Step.parStar.lamPi_target_inv_isBi functionStarBi
  simp only [Term.cd, cdEq]
  exact Step.parStar.subst0_parStar bodyStar argIH

/-- Discharge of the `Step.par.isBi.betaFstPairDeep` constructor case.
Source: `Term.fst pairTerm`, where `Step.par pairTerm (Term.pair fv sv)`.
Target: `fv`.  Pair chain inversion gives `firstVal'`, `secondVal'`
s.t. `Term.cd pairTerm = Term.pair firstVal' secondVal'`; the pair
arm of cd's fst match returns `firstVal'`.  Closed by `firstStar`. -/
theorem Step.par.cd_lemma_star_betaFstPairDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairTerm : Term ctx (Ty.sigmaTy firstType secondType)}
    {firstVal : Term ctx firstType}
    {secondVal : Term ctx (secondType.subst0 firstType)}
    {pairStar : Step.parStar
        (Term.pair (firstType := firstType) (secondType := secondType)
                   firstVal secondVal) (Term.cd pairTerm)}
    (pairStarBi : Step.parStar.isBi pairStar) :
    Step.parStar firstVal (Term.cd (Term.fst pairTerm)) := by
  obtain ⟨firstVal', _secondVal', cdEq, firstStar, _secondStar⟩ :=
    Step.parStar.pair_target_inv_isBi pairStarBi
  simp only [Term.cd, cdEq]
  exact firstStar

/-- Discharge of the `Step.par.isBi.betaSndPairDeep` constructor case. -/
theorem Step.par.cd_lemma_star_betaSndPairDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope} {secondType : Ty level (scope + 1)}
    {pairTerm : Term ctx (Ty.sigmaTy firstType secondType)}
    {firstVal : Term ctx firstType}
    {secondVal : Term ctx (secondType.subst0 firstType)}
    {pairStar : Step.parStar
        (Term.pair (firstType := firstType) (secondType := secondType)
                   firstVal secondVal) (Term.cd pairTerm)}
    (pairStarBi : Step.parStar.isBi pairStar) :
    Step.parStar secondVal (Term.cd (Term.snd pairTerm)) := by
  obtain ⟨_firstVal', _secondVal', cdEq, _firstStar, secondStar⟩ :=
    Step.parStar.pair_target_inv_isBi pairStarBi
  simp only [Term.cd, cdEq]
  exact secondStar

/-! ### Shallow ι cases (literal pattern-match redex source). -/

/-- Discharge of the `Step.par.isBi.iotaBoolElimTrue` case. -/
theorem Step.par.cd_lemma_star_iotaBoolElimTrue_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {thenBranch thenBranch' : Term ctx resultType}
    (elseBranch : Term ctx resultType)
    (thenIH : Step.parStar thenBranch' (Term.cd thenBranch)) :
    Step.parStar thenBranch'
                 (Term.cd (Term.boolElim Term.boolTrue thenBranch elseBranch)) := by
  simp only [Term.cd]
  exact thenIH

/-- Discharge of the `Step.par.isBi.iotaBoolElimFalse` case. -/
theorem Step.par.cd_lemma_star_iotaBoolElimFalse_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    (thenBranch : Term ctx resultType)
    {elseBranch elseBranch' : Term ctx resultType}
    (elseIH : Step.parStar elseBranch' (Term.cd elseBranch)) :
    Step.parStar elseBranch'
                 (Term.cd (Term.boolElim Term.boolFalse thenBranch elseBranch)) := by
  simp only [Term.cd]
  exact elseIH

/-- Discharge of the `Step.par.isBi.iotaNatElimZero` case. -/
theorem Step.par.cd_lemma_star_iotaNatElimZero_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {zeroBranch zeroBranch' : Term ctx resultType}
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
    (zeroIH : Step.parStar zeroBranch' (Term.cd zeroBranch)) :
    Step.parStar zeroBranch'
                 (Term.cd (Term.natElim Term.natZero zeroBranch succBranch)) := by
  simp only [Term.cd]
  exact zeroIH

/-- Discharge of the `Step.par.isBi.iotaNatElimSucc` case.  Source
`Term.natElim (Term.natSucc pred) zero succ`; target `Term.app
succ' pred'`.  cd of `natSucc pred` is `natSucc (cd pred)`, so the
`natSucc` arm of cd's natElim match fires, yielding `app (cd succ)
(cd pred)`.  Closed by `app_cong succIH predIH`. -/
theorem Step.par.cd_lemma_star_iotaNatElimSucc_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {predecessor predecessor' : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)}
    (predIH : Step.parStar predecessor' (Term.cd predecessor))
    (succIH : Step.parStar succBranch' (Term.cd succBranch)) :
    Step.parStar (Term.app succBranch' predecessor')
                 (Term.cd
                   (Term.natElim (Term.natSucc predecessor) zeroBranch succBranch)) := by
  simp only [Term.cd]
  exact Step.parStar.app_cong succIH predIH

/-- Discharge of the `Step.par.isBi.iotaNatRecZero` case. -/
theorem Step.par.cd_lemma_star_iotaNatRecZero_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {zeroBranch zeroBranch' : Term ctx resultType}
    (succBranch : Term ctx
        (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
    (zeroIH : Step.parStar zeroBranch' (Term.cd zeroBranch)) :
    Step.parStar zeroBranch'
                 (Term.cd (Term.natRec Term.natZero zeroBranch succBranch)) := by
  simp only [Term.cd]
  exact zeroIH

/-- Discharge of the `Step.par.isBi.iotaNatRecSucc` case.  Source
`Term.natRec (Term.natSucc pred) zero succ`; target `Term.app
(Term.app succ' pred') (Term.natRec pred' zero' succ')`.  cd of
`natSucc pred` is `natSucc (cd pred)`, so the `natSucc` arm fires,
yielding the developed-version of the same shape.  Closed by
chained `app_cong` + `natRec_cong`. -/
theorem Step.par.cd_lemma_star_iotaNatRecSucc_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {predecessor predecessor' : Term ctx Ty.nat}
    {zeroBranch zeroBranch' : Term ctx resultType}
    {succBranch succBranch' : Term ctx
        (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (predIH : Step.parStar predecessor' (Term.cd predecessor))
    (zeroIH : Step.parStar zeroBranch' (Term.cd zeroBranch))
    (succIH : Step.parStar succBranch' (Term.cd succBranch)) :
    Step.parStar
        (Term.app (Term.app succBranch' predecessor')
                  (Term.natRec predecessor' zeroBranch' succBranch'))
        (Term.cd
          (Term.natRec (Term.natSucc predecessor) zeroBranch succBranch)) := by
  simp only [Term.cd]
  exact Step.parStar.app_cong
    (Step.parStar.app_cong succIH predIH)
    (Step.parStar.natRec_cong predIH zeroIH succIH)

/-- Discharge of the `Step.par.isBi.iotaListElimNil` case. -/
theorem Step.par.cd_lemma_star_iotaListElimNil_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {nilBranch nilBranch' : Term ctx resultType}
    (consBranch : Term ctx
        (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType)))
    (nilIH : Step.parStar nilBranch' (Term.cd nilBranch)) :
    Step.parStar nilBranch'
                 (Term.cd
                   (Term.listElim (elementType := elementType) Term.listNil
                      nilBranch consBranch)) := by
  simp only [Term.cd]
  exact nilIH

/-- Discharge of the `Step.par.isBi.iotaListElimCons` case.  Source
`Term.listElim (Term.listCons head tail) nil cons`; target `Term.app
(Term.app cons' head') tail'`.  cd of `listCons head tail` is
`listCons (cd head) (cd tail)`, so the `listCons` arm fires. -/
theorem Step.par.cd_lemma_star_iotaListElimCons_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {head head' : Term ctx elementType}
    {tail tail' : Term ctx (Ty.list elementType)}
    (nilBranch : Term ctx resultType)
    {consBranch consBranch' : Term ctx
        (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))}
    (headIH : Step.parStar head' (Term.cd head))
    (tailIH : Step.parStar tail' (Term.cd tail))
    (consIH : Step.parStar consBranch' (Term.cd consBranch)) :
    Step.parStar
        (Term.app (Term.app consBranch' head') tail')
        (Term.cd
          (Term.listElim (Term.listCons head tail) nilBranch consBranch)) := by
  simp only [Term.cd]
  exact Step.parStar.app_cong (Step.parStar.app_cong consIH headIH) tailIH

/-- Discharge of the `Step.par.isBi.iotaOptionMatchNone` case. -/
theorem Step.par.cd_lemma_star_iotaOptionMatchNone_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {noneBranch noneBranch' : Term ctx resultType}
    (someBranch : Term ctx (Ty.arrow elementType resultType))
    (noneIH : Step.parStar noneBranch' (Term.cd noneBranch)) :
    Step.parStar noneBranch'
                 (Term.cd
                   (Term.optionMatch (elementType := elementType) Term.optionNone
                      noneBranch someBranch)) := by
  simp only [Term.cd]
  exact noneIH

/-- Discharge of the `Step.par.isBi.iotaOptionMatchSome` case. -/
theorem Step.par.cd_lemma_star_iotaOptionMatchSome_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {value value' : Term ctx elementType}
    (noneBranch : Term ctx resultType)
    {someBranch someBranch' : Term ctx (Ty.arrow elementType resultType)}
    (valueIH : Step.parStar value' (Term.cd value))
    (someIH : Step.parStar someBranch' (Term.cd someBranch)) :
    Step.parStar (Term.app someBranch' value')
                 (Term.cd
                   (Term.optionMatch (Term.optionSome value)
                      noneBranch someBranch)) := by
  simp only [Term.cd]
  exact Step.parStar.app_cong someIH valueIH

/-- Discharge of the `Step.par.isBi.iotaEitherMatchInl` case. -/
theorem Step.par.cd_lemma_star_iotaEitherMatchInl_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {value value' : Term ctx leftType}
    {leftBranch leftBranch' : Term ctx (Ty.arrow leftType resultType)}
    (rightBranch : Term ctx (Ty.arrow rightType resultType))
    (valueIH : Step.parStar value' (Term.cd value))
    (leftIH : Step.parStar leftBranch' (Term.cd leftBranch)) :
    Step.parStar (Term.app leftBranch' value')
                 (Term.cd
                   (Term.eitherMatch
                      (Term.eitherInl (rightType := rightType) value)
                      leftBranch rightBranch)) := by
  simp only [Term.cd]
  exact Step.parStar.app_cong leftIH valueIH

/-- Discharge of the `Step.par.isBi.iotaEitherMatchInr` case. -/
theorem Step.par.cd_lemma_star_iotaEitherMatchInr_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {value value' : Term ctx rightType}
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    {rightBranch rightBranch' : Term ctx (Ty.arrow rightType resultType)}
    (valueIH : Step.parStar value' (Term.cd value))
    (rightIH : Step.parStar rightBranch' (Term.cd rightBranch)) :
    Step.parStar (Term.app rightBranch' value')
                 (Term.cd
                   (Term.eitherMatch
                      (Term.eitherInr (leftType := leftType) value)
                      leftBranch rightBranch)) := by
  simp only [Term.cd]
  exact Step.parStar.app_cong rightIH valueIH

/-- Discharge of the `Step.par.isBi.iotaIdJRefl` case.  Source
`Term.idJ baseCase (Term.refl endpoint)`; target `baseCase'`.  cd
unfolds via `cd_idJ_redex` (decidable equality endpoint = endpoint
trivially holds), then `cd_idJ_redex_aligned` matches the literal
`Term.refl _` and yields `Term.cd baseCase`.  Closed by `baseIH`.

We avoid simp-reducing the decidable `if` (which pulls in
`propext`) and instead use explicit `split` matching `cd_idJ_redex`'s
two arms by hand. -/
theorem Step.par.cd_lemma_star_iotaIdJRefl_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {endpoint : RawTerm scope}
    {resultType : Ty level scope}
    {baseCase baseCase' : Term ctx resultType}
    (baseIH : Step.parStar baseCase' (Term.cd baseCase)) :
    Step.parStar baseCase'
                 (Term.cd (Term.idJ (carrier := carrier) (leftEnd := endpoint)
                                    (rightEnd := endpoint) baseCase
                                    (Term.refl (carrier := carrier) endpoint))) := by
  -- Same template as `idJ_case` for refl-witness with same endpoints.
  -- We use the shape-preserving `split` on `cd_idJ_redex`'s if-then-else;
  -- the endpoint=endpoint case fires deterministically at the
  -- `cd_idJ_redex_aligned` stage and matches the `Term.refl _` pattern.
  -- Establish the cd-equation as an auxiliary fact, then rewrite.
  -- The unfolding chain: Term.cd of idJ → cd_idJ_redex (cd base) (cd witness)
  --   → (cd witness = Term.refl endpoint) → cd_idJ_redex (cd base) (Term.refl endpoint)
  --   → if endpoint = endpoint then cd_idJ_redex_aligned (cd base) (rfl ▸ refl) else ...
  --   → (dif_pos with rfl) cd_idJ_redex_aligned (cd base) (refl endpoint)
  --   → (refl pattern fires) cd base.
  have cdEq : Term.cd (Term.idJ (carrier := carrier) (leftEnd := endpoint)
                                (rightEnd := endpoint) baseCase
                                (Term.refl (carrier := carrier) endpoint))
            = Term.cd baseCase := by
    simp only [Term.cd]
    unfold Term.cd_idJ_redex
    rw [dif_pos rfl]
    rfl
  rw [cdEq]
  exact baseIH

/-! ### Deep β/ι cases — typed source-inversion driven.

For ι constructors of `Step.par.isBi` whose scrutinee parallel-reduces
to a head normal form (e.g. `iotaBoolElimTrueDeep` reduces a `boolElim`
whose scrutinee parallel-steps to `Term.boolTrue`), `Term.cd` of the
elimination form must collapse to the matched branch.  The collapse
proof is exactly:

  1. `Step.parStar.<C>_source_inv` applied to the scrutinee IH proves
     `Term.cd scrutinee = Term.<C>` (the head NF the scrutinee
     parallel-reduces to).
  2. `simp only [Term.cd]` unfolds the elimination form's cd-arm,
     exposing a match on `Term.cd scrutinee`.
  3. `rw` with the source-inversion equation rewrites the match
     scrutinee to the head NF; the match then reduces to the matched
     branch's `Term.cd` arm.
  4. The matched branch's IH closes the goal. -/

/-- Discharge of the `Step.par.isBi.iotaBoolElimTrueDeep` case.  The
scrutinee parallel-steps to `Term.boolTrue`; the recursive
`cd_lemma_star` IH lifts that step to `Step.parStar Term.boolTrue
(Term.cd scrutinee)`.  `Step.parStar.boolTrue_source_inv` then forces
`Term.cd scrutinee = Term.boolTrue`, collapsing the cd-match's outer
scrutinee. -/
theorem Step.par.cd_lemma_star_iotaBoolElimTrueDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee : Term ctx Ty.bool}
    {thenBranch thenBranch' : Term ctx resultType}
    (elseBranch : Term ctx resultType)
    (scrutiIH : Step.parStar Term.boolTrue (Term.cd scrutinee))
    (thenIH : Step.parStar thenBranch' (Term.cd thenBranch)) :
    Step.parStar thenBranch'
                 (Term.cd (Term.boolElim scrutinee thenBranch elseBranch)) := by
  have cdEq : Term.cd scrutinee = Term.boolTrue :=
    Step.parStar.boolTrue_source_inv scrutiIH
  simp only [Term.cd, cdEq]
  exact thenIH

/-- Discharge of the `Step.par.isBi.iotaBoolElimFalseDeep` case. -/
theorem Step.par.cd_lemma_star_iotaBoolElimFalseDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee : Term ctx Ty.bool}
    (thenBranch : Term ctx resultType)
    {elseBranch elseBranch' : Term ctx resultType}
    (scrutiIH : Step.parStar Term.boolFalse (Term.cd scrutinee))
    (elseIH : Step.parStar elseBranch' (Term.cd elseBranch)) :
    Step.parStar elseBranch'
                 (Term.cd (Term.boolElim scrutinee thenBranch elseBranch)) := by
  have cdEq : Term.cd scrutinee = Term.boolFalse :=
    Step.parStar.boolFalse_source_inv scrutiIH
  simp only [Term.cd, cdEq]
  exact elseIH

/-- Discharge of the `Step.par.isBi.iotaNatElimZeroDeep` case. -/
theorem Step.par.cd_lemma_star_iotaNatElimZeroDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee : Term ctx Ty.nat}
    {zeroBranch zeroBranch' : Term ctx resultType}
    (succBranch : Term ctx (Ty.arrow Ty.nat resultType))
    (scrutiIH : Step.parStar Term.natZero (Term.cd scrutinee))
    (zeroIH : Step.parStar zeroBranch' (Term.cd zeroBranch)) :
    Step.parStar zeroBranch'
                 (Term.cd (Term.natElim scrutinee zeroBranch succBranch)) := by
  have cdEq : Term.cd scrutinee = Term.natZero :=
    Step.parStar.natZero_source_inv scrutiIH
  simp only [Term.cd, cdEq]
  exact zeroIH

/-- Discharge of the `Step.par.isBi.iotaNatRecZeroDeep` case. -/
theorem Step.par.cd_lemma_star_iotaNatRecZeroDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee : Term ctx Ty.nat}
    {zeroBranch zeroBranch' : Term ctx resultType}
    (succBranch : Term ctx
        (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
    (scrutiIH : Step.parStar Term.natZero (Term.cd scrutinee))
    (zeroIH : Step.parStar zeroBranch' (Term.cd zeroBranch)) :
    Step.parStar zeroBranch'
                 (Term.cd (Term.natRec scrutinee zeroBranch succBranch)) := by
  have cdEq : Term.cd scrutinee = Term.natZero :=
    Step.parStar.natZero_source_inv scrutiIH
  simp only [Term.cd, cdEq]
  exact zeroIH

/-- Discharge of the `Step.par.isBi.iotaListElimNilDeep` case. -/
theorem Step.par.cd_lemma_star_iotaListElimNilDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee : Term ctx (Ty.list elementType)}
    {nilBranch nilBranch' : Term ctx resultType}
    (consBranch : Term ctx
        (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType)))
    (scrutiIH : Step.parStar Term.listNil (Term.cd scrutinee))
    (nilIH : Step.parStar nilBranch' (Term.cd nilBranch)) :
    Step.parStar nilBranch'
                 (Term.cd (Term.listElim scrutinee nilBranch consBranch)) := by
  have cdEq : Term.cd scrutinee = Term.listNil :=
    Step.parStar.listNil_source_inv scrutiIH
  simp only [Term.cd, cdEq]
  exact nilIH

/-- Discharge of the `Step.par.isBi.iotaOptionMatchNoneDeep` case. -/
theorem Step.par.cd_lemma_star_iotaOptionMatchNoneDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee : Term ctx (Ty.option elementType)}
    {noneBranch noneBranch' : Term ctx resultType}
    (someBranch : Term ctx (Ty.arrow elementType resultType))
    (scrutiIH : Step.parStar Term.optionNone (Term.cd scrutinee))
    (noneIH : Step.parStar noneBranch' (Term.cd noneBranch)) :
    Step.parStar noneBranch'
                 (Term.cd
                   (Term.optionMatch scrutinee noneBranch someBranch)) := by
  have cdEq : Term.cd scrutinee = Term.optionNone :=
    Step.parStar.optionNone_source_inv scrutiIH
  simp only [Term.cd, cdEq]
  exact noneIH

/-- Discharge of the `Step.par.isBi.iotaIdJReflDeep` case.  The witness
parallel-reduces to `Term.refl endpoint`; the recursive cd_lemma_star
IH lifts that to `Step.parStar Term.refl (Term.cd witness)`.
`Step.parStar.refl_source_inv` then forces `Term.cd witness =
Term.refl endpoint`, and `Term.cd_idJ_redex`'s same-endpoints arm
fires.  Note: in this non-dependent J, the only ι rule is when
`leftEnd = rightEnd`, so cd_idJ_redex's `dif_pos rfl` discharges. -/
theorem Step.par.cd_lemma_star_iotaIdJReflDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {carrier : Ty level scope} {endpoint : RawTerm scope}
    {resultType : Ty level scope}
    {baseCase baseCase' : Term ctx resultType}
    {witness : Term ctx (Ty.id carrier endpoint endpoint)}
    (witnessIH : Step.parStar (Term.refl endpoint) (Term.cd witness))
    (baseIH : Step.parStar baseCase' (Term.cd baseCase)) :
    Step.parStar baseCase'
                 (Term.cd
                   (Term.idJ (carrier := carrier) (leftEnd := endpoint)
                             (rightEnd := endpoint) baseCase witness)) := by
  have cdEq : Term.cd witness = Term.refl endpoint :=
    Step.parStar.refl_source_inv witnessIH
  have cdIdJEq : Term.cd
        (Term.idJ (carrier := carrier) (leftEnd := endpoint)
                  (rightEnd := endpoint) baseCase witness)
      = Term.cd baseCase := by
    simp only [Term.cd, cdEq]
    unfold Term.cd_idJ_redex
    rw [dif_pos rfl]
    rfl
  rw [cdIdJEq]
  exact baseIH

/-! ### Deep ι cases with structural-extraction inversion.

For `iotaNatElimSuccDeep` etc., the scrutinee parallel-reduces to a
non-constant head (e.g. `Term.natSucc predecessor`).  The
corresponding source-inversion (`Step.parStar.natSucc_source_inv`)
gives:
  - `Term.cd scrutinee = Term.natSucc predecessor'` for some
    `predecessor'`,
  - `Step.parStar predecessor predecessor'`.

After rewriting `Term.cd (eliminator scrutinee ...)` via the cd-match,
the goal unfolds to the matched branch's app form.  The
`Step.parStar.app_cong` rule chains the IHs together. -/

/-- Discharge of the `Step.par.isBi.iotaNatElimSuccDeep` case. -/
theorem Step.par.cd_lemma_star_iotaNatElimSuccDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee : Term ctx Ty.nat}
    {predecessor : Term ctx Ty.nat}
    (zeroBranch : Term ctx resultType)
    {succBranch succBranch' : Term ctx (Ty.arrow Ty.nat resultType)}
    (scrutiIH :
        Step.parStar (Term.natSucc predecessor) (Term.cd scrutinee))
    (succIH : Step.parStar succBranch' (Term.cd succBranch)) :
    Step.parStar (Term.app succBranch' predecessor)
                 (Term.cd
                   (Term.natElim scrutinee zeroBranch succBranch)) := by
  obtain ⟨predecessor', cdEq, predChain⟩ :=
    Step.parStar.natSucc_source_inv scrutiIH
  simp only [Term.cd, cdEq]
  exact Step.parStar.app_cong succIH predChain

/-- Discharge of the `Step.par.isBi.iotaNatRecSuccDeep` case. -/
theorem Step.par.cd_lemma_star_iotaNatRecSuccDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {resultType : Ty level scope}
    {scrutinee : Term ctx Ty.nat}
    {predecessor : Term ctx Ty.nat}
    {zeroBranch zeroBranch' : Term ctx resultType}
    {succBranch succBranch' : Term ctx
        (Ty.arrow Ty.nat (Ty.arrow resultType resultType))}
    (scrutiIH :
        Step.parStar (Term.natSucc predecessor) (Term.cd scrutinee))
    (zeroIH : Step.parStar zeroBranch' (Term.cd zeroBranch))
    (succIH : Step.parStar succBranch' (Term.cd succBranch)) :
    Step.parStar
        (Term.app (Term.app succBranch' predecessor)
                  (Term.natRec predecessor zeroBranch' succBranch'))
        (Term.cd
          (Term.natRec scrutinee zeroBranch succBranch)) := by
  obtain ⟨predecessor', cdEq, predChain⟩ :=
    Step.parStar.natSucc_source_inv scrutiIH
  simp only [Term.cd, cdEq]
  exact Step.parStar.app_cong
    (Step.parStar.app_cong succIH predChain)
    (Step.parStar.natRec_cong predChain zeroIH succIH)

/-- Discharge of the `Step.par.isBi.iotaListElimConsDeep` case.  The
listCons inversion extracts both head and tail subterms with their
respective parStar chains. -/
theorem Step.par.cd_lemma_star_iotaListElimConsDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee : Term ctx (Ty.list elementType)}
    {headTerm : Term ctx elementType}
    {tailTerm : Term ctx (Ty.list elementType)}
    (nilBranch : Term ctx resultType)
    {consBranch consBranch' : Term ctx
        (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType))}
    (scrutiIH :
        Step.parStar (Term.listCons headTerm tailTerm) (Term.cd scrutinee))
    (consIH : Step.parStar consBranch' (Term.cd consBranch)) :
    Step.parStar
        (Term.app (Term.app consBranch' headTerm) tailTerm)
        (Term.cd (Term.listElim scrutinee nilBranch consBranch)) := by
  obtain ⟨head', tail', cdEq, headChain, tailChain⟩ :=
    Step.parStar.listCons_source_inv scrutiIH
  simp only [Term.cd, cdEq]
  exact Step.parStar.app_cong
    (Step.parStar.app_cong consIH headChain) tailChain

/-- Discharge of the `Step.par.isBi.iotaOptionMatchSomeDeep` case. -/
theorem Step.par.cd_lemma_star_iotaOptionMatchSomeDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    {scrutinee : Term ctx (Ty.option elementType)}
    {valueTerm : Term ctx elementType}
    (noneBranch : Term ctx resultType)
    {someBranch someBranch' : Term ctx (Ty.arrow elementType resultType)}
    (scrutiIH :
        Step.parStar (Term.optionSome valueTerm) (Term.cd scrutinee))
    (someIH : Step.parStar someBranch' (Term.cd someBranch)) :
    Step.parStar
        (Term.app someBranch' valueTerm)
        (Term.cd (Term.optionMatch scrutinee noneBranch someBranch)) := by
  obtain ⟨value', cdEq, valueChain⟩ :=
    Step.parStar.optionSome_source_inv scrutiIH
  simp only [Term.cd, cdEq]
  exact Step.parStar.app_cong someIH valueChain

/-- Discharge of the `Step.par.isBi.iotaEitherMatchInlDeep` case. -/
theorem Step.par.cd_lemma_star_iotaEitherMatchInlDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee : Term ctx (Ty.either leftType rightType)}
    {valueTerm : Term ctx leftType}
    {leftBranch leftBranch' : Term ctx (Ty.arrow leftType resultType)}
    (rightBranch : Term ctx (Ty.arrow rightType resultType))
    (scrutiIH :
        Step.parStar (Term.eitherInl (rightType := rightType) valueTerm)
                     (Term.cd scrutinee))
    (leftIH : Step.parStar leftBranch' (Term.cd leftBranch)) :
    Step.parStar
        (Term.app leftBranch' valueTerm)
        (Term.cd (Term.eitherMatch scrutinee leftBranch rightBranch)) := by
  obtain ⟨value', cdEq, valueChain⟩ :=
    Step.parStar.eitherInl_source_inv scrutiIH
  simp only [Term.cd, cdEq]
  exact Step.parStar.app_cong leftIH valueChain

/-- Discharge of the `Step.par.isBi.iotaEitherMatchInrDeep` case. -/
theorem Step.par.cd_lemma_star_iotaEitherMatchInrDeep_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    {scrutinee : Term ctx (Ty.either leftType rightType)}
    {valueTerm : Term ctx rightType}
    (leftBranch : Term ctx (Ty.arrow leftType resultType))
    {rightBranch rightBranch' : Term ctx (Ty.arrow rightType resultType)}
    (scrutiIH :
        Step.parStar (Term.eitherInr (leftType := leftType) valueTerm)
                     (Term.cd scrutinee))
    (rightIH : Step.parStar rightBranch' (Term.cd rightBranch)) :
    Step.parStar
        (Term.app rightBranch' valueTerm)
        (Term.cd (Term.eitherMatch scrutinee leftBranch rightBranch)) := by
  obtain ⟨value', cdEq, valueChain⟩ :=
    Step.parStar.eitherInr_source_inv scrutiIH
  simp only [Term.cd, cdEq]
  exact Step.parStar.app_cong rightIH valueChain

end LeanFX.Syntax

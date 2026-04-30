import LeanFX.Syntax.Reduction.ParBi

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
(`Step.par.toRawBridge`, Phase 4c, task #994):

  1. Lift `Step.par s t` to `RawStep.par s.toRaw t.toRaw` via
     a 56-case structural translation.
  2. Apply the already-proven raw `RawStep.par.lam_inv` (and
     companions) to extract structural information from the IH.
  3. Use the structural information to discharge the typed goal.

This file lands the smoke skeleton that confirms `induction isBi`'s
IH structure is correct.  Full cd_lemma_star awaits the bridge. -/

/-- Smoke skeleton that proves cd_lemma_star for the refl case via
the `cd_dominates → parStar` lift. -/
private theorem Step.par.cd_lemma_star_refl_only_smoke
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    (term : Term ctx termType) :
    Step.parStar term (Term.cd term) :=
  Step.par.toParStar (Step.par.cd_dominates term)

/-- Discharge of the `Step.par.isBi.refl` constructor case.  Pulled
out as a standalone helper so the eventual full `cd_lemma_star`
can reuse it without re-proving via `cd_dominates`. -/
private theorem Step.par.cd_lemma_star_refl_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {termType : Ty level scope}
    (term : Term ctx termType) :
    Step.parStar term (Term.cd term) :=
  Step.par.toParStar (Step.par.cd_dominates term)

/-- Discharge of the `Step.par.isBi.lam` constructor case.  Given
the body-IH (Step.parStar on the body's reduct), `simp [Term.cd]`
unfolds `Term.cd (Term.lam body)` to `Term.lam (Term.cd body)`,
then `Step.parStar.lam_cong` lifts the IH through the binder. -/
private theorem Step.par.cd_lemma_star_lam_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {body body' : Term (ctx.cons domainType) codomainType.weaken}
    (bodyIH : Step.parStar body' (Term.cd body)) :
    Step.parStar (Term.lam (codomainType := codomainType) body')
                 (Term.cd (Term.lam (codomainType := codomainType) body)) := by
  simp only [Term.cd]
  exact Step.parStar.lam_cong bodyIH

/-- Discharge of the `Step.par.isBi.lamPi` constructor case. -/
private theorem Step.par.cd_lemma_star_lamPi_case
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
private theorem Step.par.cd_lemma_star_pair_case
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
private theorem Step.par.cd_lemma_star_natSucc_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {pred pred' : Term ctx Ty.nat}
    (predIH : Step.parStar pred' (Term.cd pred)) :
    Step.parStar (Term.natSucc pred') (Term.cd (Term.natSucc pred)) := by
  simp only [Term.cd]
  exact Step.parStar.natSucc_cong predIH

/-- Discharge of the `Step.par.isBi.listCons` constructor case. -/
private theorem Step.par.cd_lemma_star_listCons_case
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
private theorem Step.par.cd_lemma_star_optionSome_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    {value value' : Term ctx elementType}
    (valueIH : Step.parStar value' (Term.cd value)) :
    Step.parStar (Term.optionSome value')
                 (Term.cd (Term.optionSome value)) := by
  simp only [Term.cd]
  exact Step.parStar.optionSome_cong valueIH

/-- Discharge of the `Step.par.isBi.eitherInl` constructor case. -/
private theorem Step.par.cd_lemma_star_eitherInl_case
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {value value' : Term ctx leftType}
    (valueIH : Step.parStar value' (Term.cd value)) :
    Step.parStar (Term.eitherInl (rightType := rightType) value')
                 (Term.cd (Term.eitherInl (rightType := rightType) value)) := by
  simp only [Term.cd]
  exact Step.parStar.eitherInl_cong valueIH

/-- Discharge of the `Step.par.isBi.eitherInr` constructor case. -/
private theorem Step.par.cd_lemma_star_eitherInr_case
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
private theorem Step.par.cd_lemma_star_app_case
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
private theorem Step.par.cd_lemma_star_appPi_case
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
private theorem Step.par.cd_lemma_star_fst_case
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
private theorem Step.par.cd_lemma_star_snd_case
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
private theorem Step.par.cd_lemma_star_boolElim_case
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
private theorem Step.par.cd_lemma_star_natElim_case
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
private theorem Step.par.cd_lemma_star_natRec_case
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
private theorem Step.par.cd_lemma_star_listElim_case
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
private theorem Step.par.cd_lemma_star_optionMatch_case
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
private theorem Step.par.cd_lemma_star_eitherMatch_case
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
private theorem Step.par.cd_lemma_star_idJ_case
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

end LeanFX.Syntax

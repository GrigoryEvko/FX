import LeanFX.Syntax.CompleteDevelopment
import LeanFX.Syntax.Reduction.ParRed

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `cd_dominates`: every term parallel-reduces to its complete development.

`Step.par.cd_dominates : Step.par t (Term.cd t)` is the first half of the
Tait–Martin-Löf complete-development pair.  Together with `cd_lemma`
(Phase 4) it gives the diamond property and confluence.

Each ctor case mirrors the corresponding `Term.cd` arm:

- Leaves with a free defeq reduction (var, unit, literals) — direct
  `Step.par.refl _`.
- Leaves where Term.cd's well-founded recursion blocks defeq (refl) —
  `unfold Term.cd; exact Step.par.refl _`.
- Constructor wrappers (lam/lamPi/pair/natSucc/optionSome/eitherInl/Inr/
  listCons) — `simp only [Term.cd]` fires the equation lemma, then
  `Step.par.<ctor>` cong with the IH on the subterm.
- Eliminators (app/appPi/fst/snd/boolElim/natElim/natRec/listElim/
  optionMatch/eitherMatch/idJ) — `simp only [Term.cd]` exposes the
  inner match between redex and cong shape; `split` decomposes the
  match into one goal per arm.  Redex arms get `heq` hypothesising
  `Term.cd scrutinee = Term.<targetCtor> ...`; we transport
  scrutineeParStep along heq and fire the corresponding deep β/ι rule.
  The wildcard arm receives a negation hypothesis ruling out target
  shapes; we ignore it and fall through via Step.par's shallow cong. -/

/-- Helper for the `idJ` case of `cd_dominates`.  Pulled out as a
non-recursive lemma so the `simp` + `split` + `subst` machinery (which
handles `Term.cd_idJ_redex`'s decidable-equality split and the inner
refl-pattern match) does not interfere with Lean's structural
recursion check on `cd_dominates` itself. -/
private theorem Step.par.cd_dominates_idJ
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrier resultType : Ty level scope}
    {leftEnd rightEnd : RawTerm scope}
    (baseCase : Term context resultType)
    (witness : Term context (Ty.id carrier leftEnd rightEnd))
    (baseParStep : Step.par baseCase (Term.cd baseCase))
    (witnessParStep : Step.par witness (Term.cd witness)) :
    Step.par (Term.idJ baseCase witness)
      (Term.cd (Term.idJ baseCase witness)) := by
  simp only [Term.cd, Term.cd_idJ_redex]
  split
  case _ endpointsEqual =>
      subst endpointsEqual
      simp only [Term.cd_idJ_redex_aligned]
      split
      case _ rawTerm heq =>
          exact Step.par.iotaIdJReflDeep
            (heq ▸ witnessParStep) baseParStep
      case _ =>
          exact Step.par.idJ baseParStep witnessParStep
  case _ =>
      exact Step.par.idJ baseParStep witnessParStep

theorem Step.par.cd_dominates :
    {mode : Mode} → {level scope : Nat} →
    {context : Ctx mode level scope} → {termType : Ty level scope} →
    (term : Term context termType) →
    Step.par term (Term.cd term)
  | _, _, _, _, _, .var _ => by
      unfold Term.cd
      exact Step.par.refl _
  | _, _, _, _, _, .unit => by
      unfold Term.cd
      exact Step.par.refl _
  | _, _, _, _, _, .lam body => by
      simp only [Term.cd]
      exact Step.par.lam (Step.par.cd_dominates body)
  | _, _, _, _, _, .app functionTerm argumentTerm => by
      let functionParStep := Step.par.cd_dominates functionTerm
      let argumentParStep := Step.par.cd_dominates argumentTerm
      simp only [Term.cd]
      split
      case _ body heq =>
          exact Step.par.betaAppDeep
            (heq ▸ functionParStep) argumentParStep
      case _ =>
          exact Step.par.app functionParStep argumentParStep
  | _, _, _, _, _, .lamPi body => by
      simp only [Term.cd]
      exact Step.par.lamPi (Step.par.cd_dominates body)
  | _, _, _, _, _, .appPi functionTerm argumentTerm => by
      let functionParStep := Step.par.cd_dominates functionTerm
      let argumentParStep := Step.par.cd_dominates argumentTerm
      simp only [Term.cd]
      split
      case _ body heq =>
          exact Step.par.betaAppPiDeep
            (heq ▸ functionParStep) argumentParStep
      case _ =>
          exact Step.par.appPi functionParStep argumentParStep
  | _, _, _, _, _, .pair firstVal secondVal => by
      simp only [Term.cd]
      exact Step.par.pair (Step.par.cd_dominates firstVal)
        (Step.par.cd_dominates secondVal)
  | _, _, _, _, _, .fst pairTerm => by
      let pairParStep := Step.par.cd_dominates pairTerm
      simp only [Term.cd]
      split
      case _ firstVal secondVal heq =>
          exact Step.par.betaFstPairDeep (heq ▸ pairParStep)
      case _ =>
          exact Step.par.fst pairParStep
  | _, _, _, _, _, .snd pairTerm => by
      let pairParStep := Step.par.cd_dominates pairTerm
      simp only [Term.cd]
      split
      case _ firstVal secondVal heq =>
          exact Step.par.betaSndPairDeep (heq ▸ pairParStep)
      case _ =>
          exact Step.par.snd pairParStep
  | _, _, _, _, _, .boolTrue => by
      unfold Term.cd
      exact Step.par.refl _
  | _, _, _, _, _, .boolFalse => by
      unfold Term.cd
      exact Step.par.refl _
  | _, _, _, _, _, .boolElim scrutinee thenBranch elseBranch => by
      let scrutineeParStep := Step.par.cd_dominates scrutinee
      let thenParStep := Step.par.cd_dominates thenBranch
      let elseParStep := Step.par.cd_dominates elseBranch
      simp only [Term.cd]
      split
      case _ heq =>
          exact Step.par.iotaBoolElimTrueDeep elseBranch
            (heq ▸ scrutineeParStep) thenParStep
      case _ heq =>
          exact Step.par.iotaBoolElimFalseDeep thenBranch
            (heq ▸ scrutineeParStep) elseParStep
      case _ =>
          exact Step.par.boolElim scrutineeParStep thenParStep elseParStep
  | _, _, _, _, _, .natZero => by
      unfold Term.cd
      exact Step.par.refl _
  | _, _, _, _, _, .natSucc predecessor => by
      simp only [Term.cd]
      exact Step.par.natSucc (Step.par.cd_dominates predecessor)
  | _, _, _, _, _, .natElim scrutinee zeroBranch succBranch => by
      let scrutineeParStep := Step.par.cd_dominates scrutinee
      let zeroParStep := Step.par.cd_dominates zeroBranch
      let succParStep := Step.par.cd_dominates succBranch
      simp only [Term.cd]
      split
      case _ heq =>
          exact Step.par.iotaNatElimZeroDeep succBranch
            (heq ▸ scrutineeParStep) zeroParStep
      case _ predecessor heq =>
          exact Step.par.iotaNatElimSuccDeep zeroBranch
            (heq ▸ scrutineeParStep) succParStep
      case _ =>
          exact Step.par.natElim scrutineeParStep zeroParStep succParStep
  | _, _, _, _, _, .natRec scrutinee zeroBranch succBranch => by
      let scrutineeParStep := Step.par.cd_dominates scrutinee
      let zeroParStep := Step.par.cd_dominates zeroBranch
      let succParStep := Step.par.cd_dominates succBranch
      simp only [Term.cd]
      split
      case _ heq =>
          exact Step.par.iotaNatRecZeroDeep succBranch
            (heq ▸ scrutineeParStep) zeroParStep
      case _ predecessor heq =>
          exact Step.par.iotaNatRecSuccDeep
            (heq ▸ scrutineeParStep) zeroParStep succParStep
      case _ =>
          exact Step.par.natRec scrutineeParStep zeroParStep succParStep
  | _, _, _, _, _, .listNil => by
      unfold Term.cd
      exact Step.par.refl _
  | _, _, _, _, _, .listCons head tail => by
      simp only [Term.cd]
      exact Step.par.listCons (Step.par.cd_dominates head)
        (Step.par.cd_dominates tail)
  | _, _, _, _, _, .listElim scrutinee nilBranch consBranch => by
      let scrutineeParStep := Step.par.cd_dominates scrutinee
      let nilParStep := Step.par.cd_dominates nilBranch
      let consParStep := Step.par.cd_dominates consBranch
      simp only [Term.cd]
      split
      case _ heq =>
          exact Step.par.iotaListElimNilDeep consBranch
            (heq ▸ scrutineeParStep) nilParStep
      case _ head tail heq =>
          exact Step.par.iotaListElimConsDeep nilBranch
            (heq ▸ scrutineeParStep) consParStep
      case _ =>
          exact Step.par.listElim scrutineeParStep nilParStep consParStep
  | _, _, _, _, _, .optionNone => by
      unfold Term.cd
      exact Step.par.refl _
  | _, _, _, _, _, .optionSome value => by
      simp only [Term.cd]
      exact Step.par.optionSome (Step.par.cd_dominates value)
  | _, _, _, _, _, .optionMatch scrutinee noneBranch someBranch => by
      let scrutineeParStep := Step.par.cd_dominates scrutinee
      let noneParStep := Step.par.cd_dominates noneBranch
      let someParStep := Step.par.cd_dominates someBranch
      simp only [Term.cd]
      split
      case _ heq =>
          exact Step.par.iotaOptionMatchNoneDeep someBranch
            (heq ▸ scrutineeParStep) noneParStep
      case _ value heq =>
          exact Step.par.iotaOptionMatchSomeDeep noneBranch
            (heq ▸ scrutineeParStep) someParStep
      case _ =>
          exact Step.par.optionMatch scrutineeParStep noneParStep someParStep
  | _, _, _, _, _, .eitherInl value => by
      simp only [Term.cd]
      exact Step.par.eitherInl (Step.par.cd_dominates value)
  | _, _, _, _, _, .eitherInr value => by
      simp only [Term.cd]
      exact Step.par.eitherInr (Step.par.cd_dominates value)
  | _, _, _, _, _, .eitherMatch scrutinee leftBranch rightBranch => by
      let scrutineeParStep := Step.par.cd_dominates scrutinee
      let leftParStep := Step.par.cd_dominates leftBranch
      let rightParStep := Step.par.cd_dominates rightBranch
      simp only [Term.cd]
      split
      case _ value heq =>
          exact Step.par.iotaEitherMatchInlDeep rightBranch
            (heq ▸ scrutineeParStep) leftParStep
      case _ value heq =>
          exact Step.par.iotaEitherMatchInrDeep leftBranch
            (heq ▸ scrutineeParStep) rightParStep
      case _ =>
          exact Step.par.eitherMatch scrutineeParStep leftParStep rightParStep
  | _, _, _, _, _, .refl _ => by
      unfold Term.cd
      exact Step.par.refl _
  | _, _, _, _, _, .idJ baseCase witness =>
      Step.par.cd_dominates_idJ baseCase witness
        (Step.par.cd_dominates baseCase)
        (Step.par.cd_dominates witness)

end LeanFX.Syntax

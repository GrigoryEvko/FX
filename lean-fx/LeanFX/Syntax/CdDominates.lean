import LeanFX.Syntax.CompleteDevelopment
import LeanFX.Syntax.Reduction.ParRed

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `cd_dominates`: every term parallel-reduces to its complete development.

`Step.par.cd_dominates : Step.par t (Term.cd t)` is the first half of the
Tait–Martin-Löf complete-development pair.  Together with `cd_lemma`
(Phase 4) it gives the diamond property and confluence.

## Architecture

cd_dominates' tactic-mode body would suppress equation-lemma generation
(Lean wraps tactic recursive defs in well-founded `_unary` form).  To
keep `cd_dominates` itself in pure term mode (each arm is a single
expression) we extract eliminator arms into separate non-recursive
helpers.  Leaf and cong arms remain inline using `Term.cd`'s
auto-generated equation lemmas via `simp only [Term.cd]`.

Helpers are tactic-mode `theorem`s that take the IH parallel-step
witnesses and produce the target step.  Each helper mirrors the
shape of `cd_dominates`' original arm — the same `simp + split`
pattern — but the structurally-recursive `cd_dominates` itself
remains in pure term mode that calls the helper. -/

/-- iotaIdJ helper.  Pulled out so the `simp + split + subst`
machinery handling `Term.cd_idJ_redex`'s decidable-equality split
plus the inner refl-pattern match doesn't interfere with Lean's
structural-recursion check on `cd_dominates` itself. -/
theorem Step.par.cd_dominates_idJ
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
          have cdEq : Term.cd witness = Term.refl leftEnd :=
            Term.eq_refl_of_toRaw_refl (Term.cd witness) heq
          exact Step.par.iotaIdJReflDeep
            (cdEq ▸ witnessParStep) baseParStep
      all_goals exact Step.par.idJ baseParStep witnessParStep
  case _ =>
      exact Step.par.idJ baseParStep witnessParStep

/-- Non-dependent application: cong by default, deep β when developed
function reduces to a `lam`. -/
theorem Step.par.cd_dominates_app
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    (functionTerm : Term context (Ty.arrow domainType codomainType))
    (argumentTerm : Term context domainType)
    (functionParStep : Step.par functionTerm (Term.cd functionTerm))
    (argumentParStep : Step.par argumentTerm (Term.cd argumentTerm)) :
    Step.par (Term.app functionTerm argumentTerm)
      (Term.cd (Term.app functionTerm argumentTerm)) := by
  simp only [Term.cd, Term.cd_app_redex]
  split
  case _ rawBody heq =>
      have cdEq : Term.cd functionTerm =
          Term.lam (Term.body_of_lam_general
            (Term.cd functionTerm) rfl heq) :=
        Term.eq_lam_of_toRaw_lam (Term.cd functionTerm) heq
      exact Step.par.betaAppDeep
        (cdEq ▸ functionParStep) argumentParStep
  all_goals exact Step.par.app functionParStep argumentParStep

/-- Dependent application — W9.B1.3a: `Term.cd` for appPi now
structurally rebuilds the appPi (no β-redex check; deferred to Phase C
subst0_term migration).  As a result, `cd_dominates_appPi` simplifies
to a pure cong via `Step.par.appPi`. -/
theorem Step.par.cd_dominates_appPi
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {argumentRaw : RawTerm scope}
    (functionTerm : Term context (Ty.piTy domainType codomainType))
    (argumentTerm : Term context domainType)
    (functionParStep : Step.par functionTerm (Term.cd functionTerm))
    (argumentParStep : Step.par argumentTerm (Term.cd argumentTerm)) :
    Step.par (Term.appPi (argumentRaw := argumentRaw) rfl functionTerm argumentTerm)
      (Term.cd (Term.appPi (argumentRaw := argumentRaw) rfl functionTerm argumentTerm)) := by
  -- cd's appPi arm rebuilds appPi structurally; the result is exactly
  -- `Term.appPi (argumentRaw := argumentRaw) rfl (cd f) (cd a)`.  This
  -- matches `Step.par.appPi`'s output type, so the proof is a single ctor
  -- application with the recursive ParSteps.
  exact Step.par.appPi functionParStep argumentParStep

/-- Σ first-projection: cong by default, deep β when developed pair
reduces to a `pair`. -/
theorem Step.par.cd_dominates_fst
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType))
    (pairParStep : Step.par pairTerm (Term.cd pairTerm)) :
    Step.par (Term.fst pairTerm) (Term.cd (Term.fst pairTerm)) := by
  simp only [Term.cd, Term.cd_fst_redex]
  split
  case _ rawFirst rawSecond heq =>
      have cdEq : Term.cd pairTerm =
          Term.pair
            (Term.firstVal_of_pair_general (Term.cd pairTerm) rfl heq)
            (Term.secondVal_of_pair_general (Term.cd pairTerm) rfl heq) :=
        Term.eq_pair_of_toRaw_pair (Term.cd pairTerm) heq
      exact Step.par.betaFstPairDeep (cdEq ▸ pairParStep)
  all_goals exact Step.par.fst pairParStep

/-- Σ second-projection: cong by default, deep β when developed pair
reduces to a `pair`.  W9.B1.2: `Term.snd` requires `rfl` for resultEq;
`Term.cd` snd arm preserves `rfl`. -/
theorem Step.par.cd_dominates_snd
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    (pairTerm : Term context (Ty.sigmaTy firstType secondType))
    (pairParStep : Step.par pairTerm (Term.cd pairTerm)) :
    Step.par (Term.snd pairTerm rfl) (Term.cd (Term.snd pairTerm rfl)) := by
  simp only [Term.cd, Term.cd_snd_redex]
  split
  case _ rawFirst rawSecond heq =>
      have cdEq : Term.cd pairTerm =
          Term.pair
            (Term.firstVal_of_pair_general (Term.cd pairTerm) rfl heq)
            (Term.secondVal_of_pair_general (Term.cd pairTerm) rfl heq) :=
        Term.eq_pair_of_toRaw_pair (Term.cd pairTerm) heq
      exact Step.par.betaSndPairDeep (cdEq ▸ pairParStep)
  all_goals exact Step.par.snd pairParStep

/-- `boolElim`: cong by default, deep ι when developed scrutinee
reduces to `boolTrue` or `boolFalse`. -/
theorem Step.par.cd_dominates_boolElim
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term context Ty.bool)
    (thenBranch : Term context resultType)
    (elseBranch : Term context resultType)
    (scrutineeParStep : Step.par scrutinee (Term.cd scrutinee))
    (thenParStep : Step.par thenBranch (Term.cd thenBranch))
    (elseParStep : Step.par elseBranch (Term.cd elseBranch)) :
    Step.par (Term.boolElim scrutinee thenBranch elseBranch)
      (Term.cd (Term.boolElim scrutinee thenBranch elseBranch)) := by
  simp only [Term.cd, Term.cd_boolElim_redex]
  split
  case _ heq =>
      have cdEq : Term.cd scrutinee = Term.boolTrue :=
        Term.eq_boolTrue_of_toRaw_boolTrue (Term.cd scrutinee) heq
      exact Step.par.iotaBoolElimTrueDeep elseBranch
        (cdEq ▸ scrutineeParStep) thenParStep
  case _ heq =>
      have cdEq : Term.cd scrutinee = Term.boolFalse :=
        Term.eq_boolFalse_of_toRaw_boolFalse (Term.cd scrutinee) heq
      exact Step.par.iotaBoolElimFalseDeep thenBranch
        (cdEq ▸ scrutineeParStep) elseParStep
  all_goals exact Step.par.boolElim scrutineeParStep thenParStep elseParStep

/-- `natElim`: cong by default, deep ι when developed scrutinee
reduces to `natZero` or `natSucc`. -/
theorem Step.par.cd_dominates_natElim
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term context Ty.nat)
    (zeroBranch : Term context resultType)
    (succBranch : Term context (Ty.arrow Ty.nat resultType))
    (scrutineeParStep : Step.par scrutinee (Term.cd scrutinee))
    (zeroParStep : Step.par zeroBranch (Term.cd zeroBranch))
    (succParStep : Step.par succBranch (Term.cd succBranch)) :
    Step.par (Term.natElim scrutinee zeroBranch succBranch)
      (Term.cd (Term.natElim scrutinee zeroBranch succBranch)) := by
  simp only [Term.cd, Term.cd_natElim_redex]
  split
  case _ heq =>
      have cdEq : Term.cd scrutinee = Term.natZero :=
        Term.eq_natZero_of_toRaw_natZero (Term.cd scrutinee) heq
      exact Step.par.iotaNatElimZeroDeep succBranch
        (cdEq ▸ scrutineeParStep) zeroParStep
  case _ rawPred heq =>
      have cdEq : Term.cd scrutinee =
          Term.natSucc (Term.predecessor_of_natSucc_general
            (Term.cd scrutinee) rfl heq) :=
        Term.eq_natSucc_of_toRaw_natSucc (Term.cd scrutinee) heq
      exact Step.par.iotaNatElimSuccDeep zeroBranch
        (cdEq ▸ scrutineeParStep) succParStep
  all_goals exact Step.par.natElim scrutineeParStep zeroParStep succParStep

/-- `natRec`: cong by default, deep ι when developed scrutinee
reduces to `natZero` or `natSucc`. -/
theorem Step.par.cd_dominates_natRec
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {resultType : Ty level scope}
    (scrutinee : Term context Ty.nat)
    (zeroBranch : Term context resultType)
    (succBranch : Term context
        (Ty.arrow Ty.nat (Ty.arrow resultType resultType)))
    (scrutineeParStep : Step.par scrutinee (Term.cd scrutinee))
    (zeroParStep : Step.par zeroBranch (Term.cd zeroBranch))
    (succParStep : Step.par succBranch (Term.cd succBranch)) :
    Step.par (Term.natRec scrutinee zeroBranch succBranch)
      (Term.cd (Term.natRec scrutinee zeroBranch succBranch)) := by
  simp only [Term.cd, Term.cd_natRec_redex]
  split
  case _ heq =>
      have cdEq : Term.cd scrutinee = Term.natZero :=
        Term.eq_natZero_of_toRaw_natZero (Term.cd scrutinee) heq
      exact Step.par.iotaNatRecZeroDeep succBranch
        (cdEq ▸ scrutineeParStep) zeroParStep
  case _ rawPred heq =>
      have cdEq : Term.cd scrutinee =
          Term.natSucc (Term.predecessor_of_natSucc_general
            (Term.cd scrutinee) rfl heq) :=
        Term.eq_natSucc_of_toRaw_natSucc (Term.cd scrutinee) heq
      exact Step.par.iotaNatRecSuccDeep
        (cdEq ▸ scrutineeParStep) zeroParStep succParStep
  all_goals exact Step.par.natRec scrutineeParStep zeroParStep succParStep

/-- `listElim`: cong by default, deep ι when developed scrutinee
reduces to `listNil` or `listCons`. -/
theorem Step.par.cd_dominates_listElim
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term context (Ty.list elementType))
    (nilBranch : Term context resultType)
    (consBranch : Term context
        (Ty.arrow elementType (Ty.arrow (Ty.list elementType) resultType)))
    (scrutineeParStep : Step.par scrutinee (Term.cd scrutinee))
    (nilParStep : Step.par nilBranch (Term.cd nilBranch))
    (consParStep : Step.par consBranch (Term.cd consBranch)) :
    Step.par (Term.listElim scrutinee nilBranch consBranch)
      (Term.cd (Term.listElim scrutinee nilBranch consBranch)) := by
  simp only [Term.cd, Term.cd_listElim_redex]
  split
  case _ heq =>
      have cdEq : Term.cd scrutinee = Term.listNil :=
        Term.eq_listNil_of_toRaw_listNil (Term.cd scrutinee) heq
      exact Step.par.iotaListElimNilDeep consBranch
        (cdEq ▸ scrutineeParStep) nilParStep
  case _ rawHead rawTail heq =>
      have cdEq : Term.cd scrutinee =
          Term.listCons
            (Term.head_of_listCons_general (Term.cd scrutinee) rfl heq)
            (Term.tail_of_listCons_general (Term.cd scrutinee) rfl heq) :=
        Term.eq_listCons_of_toRaw_listCons (Term.cd scrutinee) heq
      exact Step.par.iotaListElimConsDeep nilBranch
        (cdEq ▸ scrutineeParStep) consParStep
  all_goals exact Step.par.listElim scrutineeParStep nilParStep consParStep

/-- `optionMatch`: cong by default, deep ι when developed scrutinee
reduces to `optionNone` or `optionSome`. -/
theorem Step.par.cd_dominates_optionMatch
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType resultType : Ty level scope}
    (scrutinee : Term context (Ty.option elementType))
    (noneBranch : Term context resultType)
    (someBranch : Term context (Ty.arrow elementType resultType))
    (scrutineeParStep : Step.par scrutinee (Term.cd scrutinee))
    (noneParStep : Step.par noneBranch (Term.cd noneBranch))
    (someParStep : Step.par someBranch (Term.cd someBranch)) :
    Step.par (Term.optionMatch scrutinee noneBranch someBranch)
      (Term.cd (Term.optionMatch scrutinee noneBranch someBranch)) := by
  simp only [Term.cd, Term.cd_optionMatch_redex]
  split
  case _ heq =>
      have cdEq : Term.cd scrutinee = Term.optionNone :=
        Term.eq_optionNone_of_toRaw_optionNone (Term.cd scrutinee) heq
      exact Step.par.iotaOptionMatchNoneDeep someBranch
        (cdEq ▸ scrutineeParStep) noneParStep
  case _ rawValue heq =>
      have cdEq : Term.cd scrutinee =
          Term.optionSome
            (Term.value_of_optionSome_general (Term.cd scrutinee) rfl heq) :=
        Term.eq_optionSome_of_toRaw_optionSome (Term.cd scrutinee) heq
      exact Step.par.iotaOptionMatchSomeDeep noneBranch
        (cdEq ▸ scrutineeParStep) someParStep
  all_goals exact Step.par.optionMatch scrutineeParStep noneParStep someParStep

/-- `eitherMatch`: cong by default, deep ι when developed scrutinee
reduces to `eitherInl` or `eitherInr`. -/
theorem Step.par.cd_dominates_eitherMatch
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType resultType : Ty level scope}
    (scrutinee : Term context (Ty.either leftType rightType))
    (leftBranch : Term context (Ty.arrow leftType resultType))
    (rightBranch : Term context (Ty.arrow rightType resultType))
    (scrutineeParStep : Step.par scrutinee (Term.cd scrutinee))
    (leftParStep : Step.par leftBranch (Term.cd leftBranch))
    (rightParStep : Step.par rightBranch (Term.cd rightBranch)) :
    Step.par (Term.eitherMatch scrutinee leftBranch rightBranch)
      (Term.cd (Term.eitherMatch scrutinee leftBranch rightBranch)) := by
  simp only [Term.cd, Term.cd_eitherMatch_redex]
  split
  case _ rawValue heq =>
      have cdEq : Term.cd scrutinee =
          Term.eitherInl
            (Term.value_of_eitherInl_general (Term.cd scrutinee) rfl heq) :=
        Term.eq_eitherInl_of_toRaw_eitherInl (Term.cd scrutinee) heq
      exact Step.par.iotaEitherMatchInlDeep rightBranch
        (cdEq ▸ scrutineeParStep) leftParStep
  case _ rawValue heq =>
      have cdEq : Term.cd scrutinee =
          Term.eitherInr
            (Term.value_of_eitherInr_general (Term.cd scrutinee) rfl heq) :=
        Term.eq_eitherInr_of_toRaw_eitherInr (Term.cd scrutinee) heq
      exact Step.par.iotaEitherMatchInrDeep leftBranch
        (cdEq ▸ scrutineeParStep) rightParStep
  all_goals exact Step.par.eitherMatch scrutineeParStep leftParStep rightParStep

/-- Complete-development domination.

Each leaf and cong arm uses `Term.cd`'s auto-generated equation
lemma to reduce the target propositionally; eliminator arms
delegate to a non-recursive helper above.  The recursive structure
itself is pure term-mode dispatch — each arm is a single
expression, no `by` blocks — so Lean keeps `cd_dominates` in
structural recursion and emits equation lemmas. -/
def Step.par.cd_dominates {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    {termType : Ty level scope} → (term : Term context termType) →
      Step.par term (Term.cd term)
  | _, .var _ => by
      unfold Term.cd
      exact Step.par.refl _
  | _, .unit => by
      unfold Term.cd
      exact Step.par.refl _
  | _, .lam body => by
      simp only [Term.cd]
      exact Step.par.lam (Step.par.cd_dominates body)
  | _, .app functionTerm argumentTerm =>
      Step.par.cd_dominates_app functionTerm argumentTerm
        (Step.par.cd_dominates functionTerm)
        (Step.par.cd_dominates argumentTerm)
  | _, .lamPi body => by
      simp only [Term.cd]
      exact Step.par.lamPi (Step.par.cd_dominates body)
  | _, .appPi resultEq functionTerm argumentTerm => by
      -- W9.B1.1 — equation-bearing appPi.  Cases on resultEq normalises shape.
      cases resultEq
      exact Step.par.cd_dominates_appPi functionTerm argumentTerm
        (Step.par.cd_dominates functionTerm)
        (Step.par.cd_dominates argumentTerm)
  | _, .pair firstVal secondVal => by
      simp only [Term.cd]
      exact Step.par.pair (Step.par.cd_dominates firstVal)
        (Step.par.cd_dominates secondVal)
  | _, .fst pairTerm =>
      Step.par.cd_dominates_fst pairTerm
        (Step.par.cd_dominates pairTerm)
  | _, .snd pairTerm resultEq => by
      -- W9.B1.2 — equation-bearing snd.  Cases on resultEq normalises shape.
      cases resultEq
      exact Step.par.cd_dominates_snd pairTerm
        (Step.par.cd_dominates pairTerm)
  | _, .boolTrue => by
      unfold Term.cd
      exact Step.par.refl _
  | _, .boolFalse => by
      unfold Term.cd
      exact Step.par.refl _
  | _, .boolElim scrutinee thenBranch elseBranch =>
      Step.par.cd_dominates_boolElim scrutinee thenBranch elseBranch
        (Step.par.cd_dominates scrutinee)
        (Step.par.cd_dominates thenBranch)
        (Step.par.cd_dominates elseBranch)
  | _, .natZero => by
      unfold Term.cd
      exact Step.par.refl _
  | _, .natSucc predecessor => by
      simp only [Term.cd]
      exact Step.par.natSucc (Step.par.cd_dominates predecessor)
  | _, .natElim scrutinee zeroBranch succBranch =>
      Step.par.cd_dominates_natElim scrutinee zeroBranch succBranch
        (Step.par.cd_dominates scrutinee)
        (Step.par.cd_dominates zeroBranch)
        (Step.par.cd_dominates succBranch)
  | _, .natRec scrutinee zeroBranch succBranch =>
      Step.par.cd_dominates_natRec scrutinee zeroBranch succBranch
        (Step.par.cd_dominates scrutinee)
        (Step.par.cd_dominates zeroBranch)
        (Step.par.cd_dominates succBranch)
  | _, .listNil => by
      unfold Term.cd
      exact Step.par.refl _
  | _, .listCons head tail => by
      simp only [Term.cd]
      exact Step.par.listCons (Step.par.cd_dominates head)
        (Step.par.cd_dominates tail)
  | _, .listElim scrutinee nilBranch consBranch =>
      Step.par.cd_dominates_listElim scrutinee nilBranch consBranch
        (Step.par.cd_dominates scrutinee)
        (Step.par.cd_dominates nilBranch)
        (Step.par.cd_dominates consBranch)
  | _, .optionNone => by
      unfold Term.cd
      exact Step.par.refl _
  | _, .optionSome value => by
      simp only [Term.cd]
      exact Step.par.optionSome (Step.par.cd_dominates value)
  | _, .optionMatch scrutinee noneBranch someBranch =>
      Step.par.cd_dominates_optionMatch scrutinee noneBranch someBranch
        (Step.par.cd_dominates scrutinee)
        (Step.par.cd_dominates noneBranch)
        (Step.par.cd_dominates someBranch)
  | _, .eitherInl value => by
      simp only [Term.cd]
      exact Step.par.eitherInl (Step.par.cd_dominates value)
  | _, .eitherInr value => by
      simp only [Term.cd]
      exact Step.par.eitherInr (Step.par.cd_dominates value)
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      Step.par.cd_dominates_eitherMatch scrutinee leftBranch rightBranch
        (Step.par.cd_dominates scrutinee)
        (Step.par.cd_dominates leftBranch)
        (Step.par.cd_dominates rightBranch)
  | _, .refl _ => by
      unfold Term.cd
      exact Step.par.refl _
  | _, .idJ baseCase witness =>
      Step.par.cd_dominates_idJ baseCase witness
        (Step.par.cd_dominates baseCase)
        (Step.par.cd_dominates witness)

end LeanFX.Syntax

import LeanFX.Syntax.ToRaw
import LeanFX.Syntax.TermSubst

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Term.toRaw` commute lemmas.

These bridge typed `Term` operations (subst, rename, cast) to their
raw `RawTerm` analogues.  Used by:
  * `Step.par.toRawBridge` — translates typed parallel-step into raw.
  * `Term.toRaw_cd` — translates typed `Term.cd` into raw `RawTerm.cd`.

The key principle: `Term.toRaw` erases all Ty-level annotations, so
any cast `▸` between Ty equations vanishes under `Term.toRaw`.  This
is captured by `Term.toRaw_cast`. -/

/-- Casting a typed term through a Ty equation does not affect its
raw form.  `Term.toRaw` only inspects the term's structure (var,
lam, app, ...), not the Ty index, so the cast is invisible. -/
theorem Term.toRaw_cast {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} {T T' : Ty level scope}
    (h : T = T') (t : Term context T) :
    Term.toRaw (h ▸ t) = Term.toRaw t := by
  subst h
  rfl

/-- Renaming commutes with `toRaw`: typed renaming a term and then
projecting to raw equals projecting first and then raw-renaming.

The TermRenaming `ρt` is a typing-level constraint; only the
underlying raw renaming `ρ` matters for the raw projection. -/
theorem Term.toRaw_rename {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : Renaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming) :
    {T : Ty level sourceScope} → (t : Term sourceCtx T) →
      Term.toRaw (Term.rename termRenaming t) =
        RawTerm.rename (Term.toRaw t) rawRenaming
  | _, .var i => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      exact Term.toRaw_cast _ _
  | _, .unit => rfl
  | _, .lam body => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      rw [Term.toRaw_cast]
      congr 1
      exact Term.toRaw_rename (TermRenaming.lift termRenaming _) body
  | _, .app function argument => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      exact congrArgTwo (function := RawTerm.app)
        (Term.toRaw_rename termRenaming function)
        (Term.toRaw_rename termRenaming argument)
  | _, .lamPi body => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      exact congrArg RawTerm.lam
        (Term.toRaw_rename (TermRenaming.lift termRenaming _) body)
  | _, .appPi function argument => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      rw [Term.toRaw_cast]
      exact congrArgTwo (function := RawTerm.app)
        (Term.toRaw_rename termRenaming function)
        (Term.toRaw_rename termRenaming argument)
  | _, .pair firstVal secondVal => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      rw [Term.toRaw_cast]
      exact congrArgTwo (function := RawTerm.pair)
        (Term.toRaw_rename termRenaming firstVal)
        (Term.toRaw_rename termRenaming secondVal)
  | _, .fst pairTerm => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      exact congrArg RawTerm.fst
        (Term.toRaw_rename termRenaming pairTerm)
  | _, .snd pairTerm => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      rw [Term.toRaw_cast]
      exact congrArg RawTerm.snd
        (Term.toRaw_rename termRenaming pairTerm)
  | _, .boolTrue => rfl
  | _, .boolFalse => rfl
  | _, .boolElim scrutinee thenBranch elseBranch => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      exact congrArgThree (function := RawTerm.boolElim)
        (Term.toRaw_rename termRenaming scrutinee)
        (Term.toRaw_rename termRenaming thenBranch)
        (Term.toRaw_rename termRenaming elseBranch)
  | _, .natZero => rfl
  | _, .natSucc predecessor => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      exact congrArg RawTerm.natSucc
        (Term.toRaw_rename termRenaming predecessor)
  | _, .natElim scrutinee zeroBranch succBranch => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      exact congrArgThree (function := RawTerm.natElim)
        (Term.toRaw_rename termRenaming scrutinee)
        (Term.toRaw_rename termRenaming zeroBranch)
        (Term.toRaw_rename termRenaming succBranch)
  | _, .natRec scrutinee zeroBranch succBranch => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      exact congrArgThree (function := RawTerm.natRec)
        (Term.toRaw_rename termRenaming scrutinee)
        (Term.toRaw_rename termRenaming zeroBranch)
        (Term.toRaw_rename termRenaming succBranch)
  | _, .listNil => rfl
  | _, .listCons head tail => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      exact congrArgTwo (function := RawTerm.listCons)
        (Term.toRaw_rename termRenaming head)
        (Term.toRaw_rename termRenaming tail)
  | _, .listElim scrutinee nilBranch consBranch => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      exact congrArgThree (function := RawTerm.listElim)
        (Term.toRaw_rename termRenaming scrutinee)
        (Term.toRaw_rename termRenaming nilBranch)
        (Term.toRaw_rename termRenaming consBranch)
  | _, .optionNone => rfl
  | _, .optionSome value => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      exact congrArg RawTerm.optionSome
        (Term.toRaw_rename termRenaming value)
  | _, .optionMatch scrutinee noneBranch someBranch => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      exact congrArgThree (function := RawTerm.optionMatch)
        (Term.toRaw_rename termRenaming scrutinee)
        (Term.toRaw_rename termRenaming noneBranch)
        (Term.toRaw_rename termRenaming someBranch)
  | _, .eitherInl value => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      exact congrArg RawTerm.eitherInl
        (Term.toRaw_rename termRenaming value)
  | _, .eitherInr value => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      exact congrArg RawTerm.eitherInr
        (Term.toRaw_rename termRenaming value)
  | _, .eitherMatch scrutinee leftBranch rightBranch => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      exact congrArgThree (function := RawTerm.eitherMatch)
        (Term.toRaw_rename termRenaming scrutinee)
        (Term.toRaw_rename termRenaming leftBranch)
        (Term.toRaw_rename termRenaming rightBranch)
  | _, .refl _ => rfl
  | _, .idJ baseCase witness => by
      simp only [Term.rename, Term.toRaw, RawTerm.rename]
      exact congrArgTwo (function := RawTerm.idJ)
        (Term.toRaw_rename termRenaming baseCase)
        (Term.toRaw_rename termRenaming witness)

end LeanFX.Syntax

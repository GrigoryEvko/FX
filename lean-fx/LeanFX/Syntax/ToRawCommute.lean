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

/-! ### Substitution-bridge consistency.

A `TermSubst σt` carries term-level data that must be related to
the raw substitution `σ.forRaw` for the bridge to commute
cleanly.  The relation is: at every position `i`, the raw
projection of the term-level data equals `σ.forRaw i`.

This is automatically true for substitutions that come from
type-respecting constructions (e.g., `TermSubst.singleton` when
the Ty-level component is properly aligned with the term-level
data).  When the refl-rule's rawTerm uses the raw component, the
bridge requires this consistency.

We package the consistency as a proposition `TermSubst.RawConsistent`
and add it as a hypothesis to `Term.toRaw_subst`. -/

/-- Consistency of a `TermSubst` with its raw substitution view:
the raw projection of each term-level substituent equals the
raw substitution `σ.forRaw` at the same position. -/
def TermSubst.RawConsistent {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubst : Subst level sourceScope targetScope}
    (termSubst : TermSubst sourceCtx targetCtx typeSubst) : Prop :=
  ∀ position, Term.toRaw (termSubst position) = typeSubst.forRaw position

/-- `TermSubst.lift` preserves raw-consistency: if `σt` is consistent
with `σ.forRaw`, then the lifted `σt.lift T` is consistent with
`σ.lift.forRaw`. -/
theorem TermSubst.lift_RawConsistent {mode : Mode}
    {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubst : Subst level sourceScope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx typeSubst}
    (consistency : TermSubst.RawConsistent termSubst) (newType : Ty level sourceScope) :
    TermSubst.RawConsistent (TermSubst.lift termSubst newType) := by
  intro position
  match position with
  | ⟨0, _⟩ =>
      simp only [TermSubst.lift]
      rw [Term.toRaw_cast]
      rfl
  | ⟨k + 1, h⟩ =>
      simp only [TermSubst.lift]
      rw [Term.toRaw_cast]
      show Term.toRaw (Term.rename _ (termSubst ⟨k, _⟩)) = _
      rw [Term.toRaw_rename]
      exact congrArg (fun rt => RawTerm.rename rt Renaming.weaken)
        (consistency ⟨k, _⟩)

/-- Substitution commutes with `toRaw` when the term substitution is
raw-consistent.  Structural induction on the term; uses
`lift_RawConsistent` for the binder cases and `toRaw_cast` to peel
off Ty-level alignment casts in the eliminator cases. -/
theorem Term.toRaw_subst {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {typeSubst : Subst level sourceScope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx typeSubst}
    (consistency : TermSubst.RawConsistent termSubst) :
    {T : Ty level sourceScope} → (t : Term sourceCtx T) →
      Term.toRaw (Term.subst termSubst t) =
        (Term.toRaw t).subst typeSubst.forRaw
  | _, .var i => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact consistency i
  | _, .unit => rfl
  | _, .lam body => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      rw [Term.toRaw_cast]
      exact congrArg RawTerm.lam
        (Term.toRaw_subst (TermSubst.lift_RawConsistent consistency _) body)
  | _, .app function argument => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgTwo (function := RawTerm.app)
        (Term.toRaw_subst consistency function)
        (Term.toRaw_subst consistency argument)
  | _, .lamPi body => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArg RawTerm.lam
        (Term.toRaw_subst (TermSubst.lift_RawConsistent consistency _) body)
  | _, .appPi function argument => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      rw [Term.toRaw_cast]
      exact congrArgTwo (function := RawTerm.app)
        (Term.toRaw_subst consistency function)
        (Term.toRaw_subst consistency argument)
  | _, .pair firstVal secondVal => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      have secondEq : Term.toRaw (Term.subst termSubst secondVal) =
          (Term.toRaw secondVal).subst typeSubst.forRaw :=
        Term.toRaw_subst consistency secondVal
      exact congrArgTwo (function := RawTerm.pair)
        (Term.toRaw_subst consistency firstVal)
        (by rw [Term.toRaw_cast]; exact secondEq)
  | _, .fst pairTerm => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArg RawTerm.fst
        (Term.toRaw_subst consistency pairTerm)
  | _, .snd pairTerm => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      rw [Term.toRaw_cast]
      exact congrArg RawTerm.snd
        (Term.toRaw_subst consistency pairTerm)
  | _, .boolTrue => rfl
  | _, .boolFalse => rfl
  | _, .boolElim scrutinee thenBranch elseBranch => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgThree (function := RawTerm.boolElim)
        (Term.toRaw_subst consistency scrutinee)
        (Term.toRaw_subst consistency thenBranch)
        (Term.toRaw_subst consistency elseBranch)
  | _, .natZero => rfl
  | _, .natSucc predecessor => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArg RawTerm.natSucc
        (Term.toRaw_subst consistency predecessor)
  | _, .natElim scrutinee zeroBranch succBranch => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgThree (function := RawTerm.natElim)
        (Term.toRaw_subst consistency scrutinee)
        (Term.toRaw_subst consistency zeroBranch)
        (Term.toRaw_subst consistency succBranch)
  | _, .natRec scrutinee zeroBranch succBranch => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgThree (function := RawTerm.natRec)
        (Term.toRaw_subst consistency scrutinee)
        (Term.toRaw_subst consistency zeroBranch)
        (Term.toRaw_subst consistency succBranch)
  | _, .listNil => rfl
  | _, .listCons head tail => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgTwo (function := RawTerm.listCons)
        (Term.toRaw_subst consistency head)
        (Term.toRaw_subst consistency tail)
  | _, .listElim scrutinee nilBranch consBranch => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgThree (function := RawTerm.listElim)
        (Term.toRaw_subst consistency scrutinee)
        (Term.toRaw_subst consistency nilBranch)
        (Term.toRaw_subst consistency consBranch)
  | _, .optionNone => rfl
  | _, .optionSome value => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArg RawTerm.optionSome
        (Term.toRaw_subst consistency value)
  | _, .optionMatch scrutinee noneBranch someBranch => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgThree (function := RawTerm.optionMatch)
        (Term.toRaw_subst consistency scrutinee)
        (Term.toRaw_subst consistency noneBranch)
        (Term.toRaw_subst consistency someBranch)
  | _, .eitherInl value => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArg RawTerm.eitherInl
        (Term.toRaw_subst consistency value)
  | _, .eitherInr value => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArg RawTerm.eitherInr
        (Term.toRaw_subst consistency value)
  | _, .eitherMatch scrutinee leftBranch rightBranch => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgThree (function := RawTerm.eitherMatch)
        (Term.toRaw_subst consistency scrutinee)
        (Term.toRaw_subst consistency leftBranch)
        (Term.toRaw_subst consistency rightBranch)
  | _, .refl _ => rfl
  | _, .idJ baseCase witness => by
      simp only [Term.subst, Term.toRaw, RawTerm.subst]
      exact congrArgTwo (function := RawTerm.idJ)
        (Term.toRaw_subst consistency baseCase)
        (Term.toRaw_subst consistency witness)

/-! ### Specialization: `subst0` commute under raw-consistent singleton.

For `Term.subst0`, the typed substitution is `TermSubst.singleton arg`
and the raw side wants `RawTermSubst.singleton (toRaw arg)`.  These
agree pointwise iff arg's raw projection matches the singleton's
position-0 substituent — captured by `RawConsistent`. -/

/-- Subst0 commutes with toRaw when the typed singleton substitution
is raw-consistent (i.e., its raw side equals `RawTermSubst.singleton
(toRaw arg)`).  This holds whenever the typed kernel uses the
canonical alignment between TermSubst.singleton and Subst.singleton
on the raw component. -/
theorem Term.toRaw_subst0_of_consistent {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {T_arg : Ty level scope} {T_body : Ty level (scope + 1)}
    (body : Term (context.cons T_arg) T_body) (argument : Term context T_arg)
    (consistency :
      TermSubst.RawConsistent (TermSubst.singleton argument)) :
    Term.toRaw (Term.subst0 body argument) =
      RawTerm.subst (Term.toRaw body) (Subst.singleton T_arg).forRaw := by
  unfold Term.subst0
  exact Term.toRaw_subst consistency body

end LeanFX.Syntax

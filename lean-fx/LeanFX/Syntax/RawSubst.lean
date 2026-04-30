import LeanFX.Syntax.Ty

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## RawTerm substitution.

`RawTermSubst source target` is the raw-syntax companion to `Subst`.
It maps source-scope variables to raw target-scope terms.  This does
not affect the current closed-endpoint `Ty.id` encoding directly, but
it is the next piece of infrastructure needed for open identity
endpoints (`RawTerm scope`) in v2.3. -/

/-- Raw substitution for well-scoped raw terms. -/
abbrev RawTermSubst (source target : Nat) : Type :=
  Fin source → RawTerm target

/-- Lift a raw substitution under one raw binder.  The freshly-bound
variable maps to itself; older variables are substituted and then
weakened into the extended target scope. -/
def RawTermSubst.lift {source target : Nat}
    (rawSubstitution : RawTermSubst source target) :
    RawTermSubst (source + 1) (target + 1)
  | ⟨0, _⟩ =>
      RawTerm.var ⟨0, Nat.succ_pos target⟩
  | ⟨position + 1, isWithinSource⟩ =>
      (rawSubstitution
        ⟨position, Nat.lt_of_succ_lt_succ isWithinSource⟩).weaken

/-- Lifted raw substitution maps the freshly-bound variable to itself. -/
theorem RawTermSubst.lift_zero {source target : Nat}
    (rawSubstitution : RawTermSubst source target) :
    rawSubstitution.lift ⟨0, Nat.zero_lt_succ source⟩ =
      RawTerm.var ⟨0, Nat.zero_lt_succ target⟩ :=
  rfl

/-- Lifted raw substitution maps older variables by substituting and weakening. -/
theorem RawTermSubst.lift_succ {source target : Nat}
    (rawSubstitution : RawTermSubst source target)
    (position : Nat) (isWithinSource : position < source) :
    rawSubstitution.lift ⟨position + 1, Nat.succ_lt_succ isWithinSource⟩ =
      (rawSubstitution ⟨position, isWithinSource⟩).weaken :=
  rfl

/-- Apply a raw substitution to a raw term.  This is structurally
parallel to `RawTerm.rename`, with `RawTermSubst.lift` under lambdas. -/
def RawTerm.subst {source target : Nat} :
    RawTerm source → RawTermSubst source target → RawTerm target
  | .var position, rawSubstitution => rawSubstitution position
  | .unit, _ => .unit
  | .boolTrue, _ => .boolTrue
  | .boolFalse, _ => .boolFalse
  | .natZero, _ => .natZero
  | .natSucc predecessor, rawSubstitution =>
      .natSucc (RawTerm.subst predecessor rawSubstitution)
  | .lam body, rawSubstitution =>
      .lam (RawTerm.subst body rawSubstitution.lift)
  | .app function argument, rawSubstitution =>
      .app (RawTerm.subst function rawSubstitution)
           (RawTerm.subst argument rawSubstitution)
  | .pair first second, rawSubstitution =>
      .pair (RawTerm.subst first rawSubstitution)
            (RawTerm.subst second rawSubstitution)
  | .fst pairTerm, rawSubstitution =>
      .fst (RawTerm.subst pairTerm rawSubstitution)
  | .snd pairTerm, rawSubstitution =>
      .snd (RawTerm.subst pairTerm rawSubstitution)
  | .boolElim scrutinee thenBranch elseBranch, rawSubstitution =>
      .boolElim
        (RawTerm.subst scrutinee rawSubstitution)
        (RawTerm.subst thenBranch rawSubstitution)
        (RawTerm.subst elseBranch rawSubstitution)
  | .natElim scrutinee zeroBranch succBranch, rawSubstitution =>
      .natElim
        (RawTerm.subst scrutinee rawSubstitution)
        (RawTerm.subst zeroBranch rawSubstitution)
        (RawTerm.subst succBranch rawSubstitution)
  | .natRec scrutinee zeroBranch succBranch, rawSubstitution =>
      .natRec
        (RawTerm.subst scrutinee rawSubstitution)
        (RawTerm.subst zeroBranch rawSubstitution)
        (RawTerm.subst succBranch rawSubstitution)
  | .listNil, _ => .listNil
  | .listCons head tail, rawSubstitution =>
      .listCons (RawTerm.subst head rawSubstitution)
                (RawTerm.subst tail rawSubstitution)
  | .listElim scrutinee nilBranch consBranch, rawSubstitution =>
      .listElim
        (RawTerm.subst scrutinee rawSubstitution)
        (RawTerm.subst nilBranch rawSubstitution)
        (RawTerm.subst consBranch rawSubstitution)
  | .optionNone, _ => .optionNone
  | .optionSome value, rawSubstitution =>
      .optionSome (RawTerm.subst value rawSubstitution)
  | .optionMatch scrutinee noneBranch someBranch, rawSubstitution =>
      .optionMatch
        (RawTerm.subst scrutinee rawSubstitution)
        (RawTerm.subst noneBranch rawSubstitution)
        (RawTerm.subst someBranch rawSubstitution)
  | .eitherInl value, rawSubstitution =>
      .eitherInl (RawTerm.subst value rawSubstitution)
  | .eitherInr value, rawSubstitution =>
      .eitherInr (RawTerm.subst value rawSubstitution)
  | .eitherMatch scrutinee leftBranch rightBranch, rawSubstitution =>
      .eitherMatch
        (RawTerm.subst scrutinee rawSubstitution)
        (RawTerm.subst leftBranch rawSubstitution)
        (RawTerm.subst rightBranch rawSubstitution)
  | .refl term, rawSubstitution =>
      .refl (RawTerm.subst term rawSubstitution)
  | .idJ baseCase witness, rawSubstitution =>
      .idJ (RawTerm.subst baseCase rawSubstitution)
           (RawTerm.subst witness rawSubstitution)

/-- Identity raw substitution. -/
def RawTermSubst.identity {scope : Nat} : RawTermSubst scope scope :=
  RawTerm.var

/-- Identity raw substitution returns the same variable. -/
theorem RawTermSubst.identity_apply {scope : Nat} (position : Fin scope) :
    RawTermSubst.identity position = RawTerm.var position :=
  rfl

/-- Drop the newest raw binder.  This is the raw component of
`Subst.singleton`: variable 0 is the removed binder, and variables
`k + 1` shift down to `k`. -/
def RawTermSubst.dropNewest {scope : Nat} : RawTermSubst (scope + 1) scope
  | ⟨0, _⟩ => RawTerm.unit
  | ⟨position + 1, isWithinScope⟩ =>
      RawTerm.var ⟨position, Nat.lt_of_succ_lt_succ isWithinScope⟩

/-- Dropping the newest raw variable maps position 0 to a placeholder unit. -/
theorem RawTermSubst.dropNewest_zero {scope : Nat} :
    (@RawTermSubst.dropNewest scope) ⟨0, Nat.zero_lt_succ scope⟩ = RawTerm.unit :=
  rfl

/-- Dropping the newest raw variable shifts older variables down. -/
theorem RawTermSubst.dropNewest_succ {scope : Nat}
    (position : Nat) (isWithinScope : position < scope) :
    (@RawTermSubst.dropNewest scope)
      ⟨position + 1, Nat.succ_lt_succ isWithinScope⟩ =
        RawTerm.var ⟨position, isWithinScope⟩ :=
  rfl

/-- Pointwise equivalence for raw substitutions. -/
def RawTermSubst.equiv {source target : Nat}
    (firstSubstitution secondSubstitution : RawTermSubst source target) : Prop :=
  ∀ position, firstSubstitution position = secondSubstitution position

/-- Reflexivity for raw-substitution equivalence. -/
theorem RawTermSubst.equiv_refl {source target : Nat}
    (rawSubstitution : RawTermSubst source target) :
    RawTermSubst.equiv rawSubstitution rawSubstitution :=
  fun _ => rfl

/-- Symmetry for raw-substitution equivalence. -/
theorem RawTermSubst.equiv_symm {source target : Nat}
    {firstSubstitution secondSubstitution : RawTermSubst source target}
    (areEquivalent : RawTermSubst.equiv firstSubstitution secondSubstitution) :
    RawTermSubst.equiv secondSubstitution firstSubstitution :=
  fun position => (areEquivalent position).symm

/-- Transitivity for raw-substitution equivalence. -/
theorem RawTermSubst.equiv_trans {source target : Nat}
    {firstSubstitution secondSubstitution thirdSubstitution : RawTermSubst source target}
    (firstEquivalence : RawTermSubst.equiv firstSubstitution secondSubstitution)
    (secondEquivalence : RawTermSubst.equiv secondSubstitution thirdSubstitution) :
    RawTermSubst.equiv firstSubstitution thirdSubstitution :=
  fun position => (firstEquivalence position).trans (secondEquivalence position)

/-- Binary function congruence helper for raw-substitution proofs. -/
theorem congrArgTwo {firstType secondType resultType : Sort _}
    {function : firstType → secondType → resultType}
    {firstValue firstValue' : firstType}
    {secondValue secondValue' : secondType}
    (firstEquality : firstValue = firstValue')
    (secondEquality : secondValue = secondValue') :
    function firstValue secondValue = function firstValue' secondValue' := by
  cases firstEquality
  cases secondEquality
  rfl

/-- Ternary function congruence helper for raw-substitution proofs. -/
theorem congrArgThree {firstType secondType thirdType resultType : Sort _}
    {function : firstType → secondType → thirdType → resultType}
    {firstValue firstValue' : firstType}
    {secondValue secondValue' : secondType}
    {thirdValue thirdValue' : thirdType}
    (firstEquality : firstValue = firstValue')
    (secondEquality : secondValue = secondValue')
    (thirdEquality : thirdValue = thirdValue') :
    function firstValue secondValue thirdValue =
      function firstValue' secondValue' thirdValue' := by
  cases firstEquality
  cases secondEquality
  cases thirdEquality
  rfl

/-- Equivalent raw substitutions remain equivalent under binder lifting. -/
theorem RawTermSubst.lift_equiv {source target : Nat}
    {firstSubstitution secondSubstitution : RawTermSubst source target}
    (areEquivalent : RawTermSubst.equiv firstSubstitution secondSubstitution) :
    RawTermSubst.equiv firstSubstitution.lift secondSubstitution.lift
  | ⟨0, _⟩ => rfl
  | ⟨position + 1, isWithinSource⟩ =>
      congrArg RawTerm.weaken
        (areEquivalent ⟨position, Nat.lt_of_succ_lt_succ isWithinSource⟩)

/-- Pointwise-equivalent raw substitutions produce equal substituted raw terms. -/
theorem RawTerm.subst_congr {source target : Nat}
    {firstSubstitution secondSubstitution : RawTermSubst source target}
    (areEquivalent : RawTermSubst.equiv firstSubstitution secondSubstitution) :
    ∀ rawTerm : RawTerm source,
      rawTerm.subst firstSubstitution = rawTerm.subst secondSubstitution
  | .var position => areEquivalent position
  | .unit => rfl
  | .boolTrue => rfl
  | .boolFalse => rfl
  | .natZero => rfl
  | .natSucc predecessor => by
      exact congrArg RawTerm.natSucc (RawTerm.subst_congr areEquivalent predecessor)
  | .lam body => by
      exact congrArg RawTerm.lam
        (RawTerm.subst_congr (RawTermSubst.lift_equiv areEquivalent) body)
  | .app function argument => by
      exact congrArgTwo (function := RawTerm.app)
        (RawTerm.subst_congr areEquivalent function)
        (RawTerm.subst_congr areEquivalent argument)
  | .pair first second => by
      exact congrArgTwo (function := RawTerm.pair)
        (RawTerm.subst_congr areEquivalent first)
        (RawTerm.subst_congr areEquivalent second)
  | .fst pairTerm => by
      exact congrArg RawTerm.fst (RawTerm.subst_congr areEquivalent pairTerm)
  | .snd pairTerm => by
      exact congrArg RawTerm.snd (RawTerm.subst_congr areEquivalent pairTerm)
  | .boolElim scrutinee thenBranch elseBranch => by
      exact congrArgThree (function := RawTerm.boolElim)
        (RawTerm.subst_congr areEquivalent scrutinee)
        (RawTerm.subst_congr areEquivalent thenBranch)
        (RawTerm.subst_congr areEquivalent elseBranch)
  | .natElim scrutinee zeroBranch succBranch => by
      exact congrArgThree (function := RawTerm.natElim)
        (RawTerm.subst_congr areEquivalent scrutinee)
        (RawTerm.subst_congr areEquivalent zeroBranch)
        (RawTerm.subst_congr areEquivalent succBranch)
  | .natRec scrutinee zeroBranch succBranch => by
      exact congrArgThree (function := RawTerm.natRec)
        (RawTerm.subst_congr areEquivalent scrutinee)
        (RawTerm.subst_congr areEquivalent zeroBranch)
        (RawTerm.subst_congr areEquivalent succBranch)
  | .listNil => rfl
  | .listCons head tail => by
      exact congrArgTwo (function := RawTerm.listCons)
        (RawTerm.subst_congr areEquivalent head)
        (RawTerm.subst_congr areEquivalent tail)
  | .listElim scrutinee nilBranch consBranch => by
      exact congrArgThree (function := RawTerm.listElim)
        (RawTerm.subst_congr areEquivalent scrutinee)
        (RawTerm.subst_congr areEquivalent nilBranch)
        (RawTerm.subst_congr areEquivalent consBranch)
  | .optionNone => rfl
  | .optionSome value => by
      exact congrArg RawTerm.optionSome (RawTerm.subst_congr areEquivalent value)
  | .optionMatch scrutinee noneBranch someBranch => by
      exact congrArgThree (function := RawTerm.optionMatch)
        (RawTerm.subst_congr areEquivalent scrutinee)
        (RawTerm.subst_congr areEquivalent noneBranch)
        (RawTerm.subst_congr areEquivalent someBranch)
  | .eitherInl value => by
      exact congrArg RawTerm.eitherInl (RawTerm.subst_congr areEquivalent value)
  | .eitherInr value => by
      exact congrArg RawTerm.eitherInr (RawTerm.subst_congr areEquivalent value)
  | .eitherMatch scrutinee leftBranch rightBranch => by
      exact congrArgThree (function := RawTerm.eitherMatch)
        (RawTerm.subst_congr areEquivalent scrutinee)
        (RawTerm.subst_congr areEquivalent leftBranch)
        (RawTerm.subst_congr areEquivalent rightBranch)
  | .refl term => by
      exact congrArg RawTerm.refl (RawTerm.subst_congr areEquivalent term)
  | .idJ baseCase witness => by
      exact congrArgTwo (function := RawTerm.idJ)
        (RawTerm.subst_congr areEquivalent baseCase)
        (RawTerm.subst_congr areEquivalent witness)

/-- Lifting the identity raw substitution is pointwise equivalent to identity. -/
theorem RawTermSubst.lift_identity_equiv {scope : Nat} :
    RawTermSubst.equiv
      (RawTermSubst.lift (RawTermSubst.identity (scope := scope)))
      (RawTermSubst.identity (scope := scope + 1))
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => rfl

/-- Raw substitution identity law. -/
theorem RawTerm.subst_id {scope : Nat} :
    ∀ rawTerm : RawTerm scope,
      rawTerm.subst RawTermSubst.identity = rawTerm
  | .var _ => rfl
  | .unit => rfl
  | .boolTrue => rfl
  | .boolFalse => rfl
  | .natZero => rfl
  | .natSucc predecessor => by
      exact congrArg RawTerm.natSucc (RawTerm.subst_id predecessor)
  | .lam body => by
      have liftedToIdentity :
          RawTerm.subst body (RawTermSubst.lift RawTermSubst.identity)
            = RawTerm.subst body RawTermSubst.identity :=
        RawTerm.subst_congr RawTermSubst.lift_identity_equiv body
      exact congrArg RawTerm.lam (liftedToIdentity.trans (RawTerm.subst_id body))
  | .app function argument => by
      exact congrArgTwo (function := RawTerm.app)
        (RawTerm.subst_id function)
        (RawTerm.subst_id argument)
  | .pair first second => by
      exact congrArgTwo (function := RawTerm.pair)
        (RawTerm.subst_id first)
        (RawTerm.subst_id second)
  | .fst pairTerm => by
      exact congrArg RawTerm.fst (RawTerm.subst_id pairTerm)
  | .snd pairTerm => by
      exact congrArg RawTerm.snd (RawTerm.subst_id pairTerm)
  | .boolElim scrutinee thenBranch elseBranch => by
      exact congrArgThree (function := RawTerm.boolElim)
        (RawTerm.subst_id scrutinee)
        (RawTerm.subst_id thenBranch)
        (RawTerm.subst_id elseBranch)
  | .natElim scrutinee zeroBranch succBranch => by
      exact congrArgThree (function := RawTerm.natElim)
        (RawTerm.subst_id scrutinee)
        (RawTerm.subst_id zeroBranch)
        (RawTerm.subst_id succBranch)
  | .natRec scrutinee zeroBranch succBranch => by
      exact congrArgThree (function := RawTerm.natRec)
        (RawTerm.subst_id scrutinee)
        (RawTerm.subst_id zeroBranch)
        (RawTerm.subst_id succBranch)
  | .listNil => rfl
  | .listCons head tail => by
      exact congrArgTwo (function := RawTerm.listCons)
        (RawTerm.subst_id head)
        (RawTerm.subst_id tail)
  | .listElim scrutinee nilBranch consBranch => by
      exact congrArgThree (function := RawTerm.listElim)
        (RawTerm.subst_id scrutinee)
        (RawTerm.subst_id nilBranch)
        (RawTerm.subst_id consBranch)
  | .optionNone => rfl
  | .optionSome value => by
      exact congrArg RawTerm.optionSome (RawTerm.subst_id value)
  | .optionMatch scrutinee noneBranch someBranch => by
      exact congrArgThree (function := RawTerm.optionMatch)
        (RawTerm.subst_id scrutinee)
        (RawTerm.subst_id noneBranch)
        (RawTerm.subst_id someBranch)
  | .eitherInl value => by
      exact congrArg RawTerm.eitherInl (RawTerm.subst_id value)
  | .eitherInr value => by
      exact congrArg RawTerm.eitherInr (RawTerm.subst_id value)
  | .eitherMatch scrutinee leftBranch rightBranch => by
      exact congrArgThree (function := RawTerm.eitherMatch)
        (RawTerm.subst_id scrutinee)
        (RawTerm.subst_id leftBranch)
        (RawTerm.subst_id rightBranch)
  | .refl term => by
      exact congrArg RawTerm.refl (RawTerm.subst_id term)
  | .idJ baseCase witness => by
      exact congrArgTwo (function := RawTerm.idJ)
        (RawTerm.subst_id baseCase)
        (RawTerm.subst_id witness)

/-- Compose a raw rawRenaming with a raw substitution. -/
def RawTermSubst.afterRenaming {source middle target : Nat}
    (rawRenaming : Renaming source middle)
    (rawSubstitution : RawTermSubst middle target) :
    RawTermSubst source target :=
  fun position => rawSubstitution (rawRenaming position)

/-- Weakening followed by dropping the newest raw variable is the raw
identity substitution. -/
theorem RawTermSubst.afterRenaming_weaken_dropNewest_equiv_identity {scope : Nat} :
    RawTermSubst.equiv
      (RawTermSubst.afterRenaming
        (@Renaming.weaken scope)
        (@RawTermSubst.dropNewest scope))
      (@RawTermSubst.identity scope) :=
  fun _ => rfl

/-- Lifting agrees with composing a raw rawRenaming before a raw substitution. -/
theorem RawTermSubst.lift_afterRenaming_equiv {source middle target : Nat}
    (rawRenaming : Renaming source middle)
    (rawSubstitution : RawTermSubst middle target) :
    RawTermSubst.equiv
      (RawTermSubst.lift
        (RawTermSubst.afterRenaming rawRenaming rawSubstitution))
      (RawTermSubst.afterRenaming rawRenaming.lift rawSubstitution.lift)
  | ⟨0, _⟩ => rfl
  | ⟨position + 1, isWithinSource⟩ => by
      rfl

/-- Substitution after rawRenaming composes the rawRenaming into the substitution. -/
theorem RawTerm.subst_rename_commute {source middle target : Nat} :
    ∀ (rawTerm : RawTerm source)
      (rawRenaming : Renaming source middle)
      (rawSubstitution : RawTermSubst middle target),
      (rawTerm.rename rawRenaming).subst rawSubstitution =
        rawTerm.subst (RawTermSubst.afterRenaming rawRenaming rawSubstitution)
  | .var _, _, _ => rfl
  | .unit, _, _ => rfl
  | .boolTrue, _, _ => rfl
  | .boolFalse, _, _ => rfl
  | .natZero, _, _ => rfl
  | .natSucc predecessor, rawRenaming, rawSubstitution => by
      exact congrArg RawTerm.natSucc
        (RawTerm.subst_rename_commute predecessor rawRenaming rawSubstitution)
  | .lam body, rawRenaming, rawSubstitution => by
      have bodyComposition :=
        RawTerm.subst_rename_commute body rawRenaming.lift rawSubstitution.lift
      have liftComposition :=
        RawTerm.subst_congr
          (RawTermSubst.lift_afterRenaming_equiv rawRenaming rawSubstitution)
          body
      exact congrArg RawTerm.lam (bodyComposition.trans liftComposition.symm)
  | .app function argument, rawRenaming, rawSubstitution => by
      exact congrArgTwo (function := RawTerm.app)
        (RawTerm.subst_rename_commute function rawRenaming rawSubstitution)
        (RawTerm.subst_rename_commute argument rawRenaming rawSubstitution)
  | .pair first second, rawRenaming, rawSubstitution => by
      exact congrArgTwo (function := RawTerm.pair)
        (RawTerm.subst_rename_commute first rawRenaming rawSubstitution)
        (RawTerm.subst_rename_commute second rawRenaming rawSubstitution)
  | .fst pairTerm, rawRenaming, rawSubstitution => by
      exact congrArg RawTerm.fst
        (RawTerm.subst_rename_commute pairTerm rawRenaming rawSubstitution)
  | .snd pairTerm, rawRenaming, rawSubstitution => by
      exact congrArg RawTerm.snd
        (RawTerm.subst_rename_commute pairTerm rawRenaming rawSubstitution)
  | .boolElim scrutinee thenBranch elseBranch, rawRenaming, rawSubstitution => by
      exact congrArgThree (function := RawTerm.boolElim)
        (RawTerm.subst_rename_commute scrutinee rawRenaming rawSubstitution)
        (RawTerm.subst_rename_commute thenBranch rawRenaming rawSubstitution)
        (RawTerm.subst_rename_commute elseBranch rawRenaming rawSubstitution)
  | .natElim scrutinee zeroBranch succBranch, rawRenaming, rawSubstitution => by
      exact congrArgThree (function := RawTerm.natElim)
        (RawTerm.subst_rename_commute scrutinee rawRenaming rawSubstitution)
        (RawTerm.subst_rename_commute zeroBranch rawRenaming rawSubstitution)
        (RawTerm.subst_rename_commute succBranch rawRenaming rawSubstitution)
  | .natRec scrutinee zeroBranch succBranch, rawRenaming, rawSubstitution => by
      exact congrArgThree (function := RawTerm.natRec)
        (RawTerm.subst_rename_commute scrutinee rawRenaming rawSubstitution)
        (RawTerm.subst_rename_commute zeroBranch rawRenaming rawSubstitution)
        (RawTerm.subst_rename_commute succBranch rawRenaming rawSubstitution)
  | .listNil, _, _ => rfl
  | .listCons head tail, rawRenaming, rawSubstitution => by
      exact congrArgTwo (function := RawTerm.listCons)
        (RawTerm.subst_rename_commute head rawRenaming rawSubstitution)
        (RawTerm.subst_rename_commute tail rawRenaming rawSubstitution)
  | .listElim scrutinee nilBranch consBranch, rawRenaming, rawSubstitution => by
      exact congrArgThree (function := RawTerm.listElim)
        (RawTerm.subst_rename_commute scrutinee rawRenaming rawSubstitution)
        (RawTerm.subst_rename_commute nilBranch rawRenaming rawSubstitution)
        (RawTerm.subst_rename_commute consBranch rawRenaming rawSubstitution)
  | .optionNone, _, _ => rfl
  | .optionSome value, rawRenaming, rawSubstitution => by
      exact congrArg RawTerm.optionSome
        (RawTerm.subst_rename_commute value rawRenaming rawSubstitution)
  | .optionMatch scrutinee noneBranch someBranch, rawRenaming, rawSubstitution => by
      exact congrArgThree (function := RawTerm.optionMatch)
        (RawTerm.subst_rename_commute scrutinee rawRenaming rawSubstitution)
        (RawTerm.subst_rename_commute noneBranch rawRenaming rawSubstitution)
        (RawTerm.subst_rename_commute someBranch rawRenaming rawSubstitution)
  | .eitherInl value, rawRenaming, rawSubstitution => by
      exact congrArg RawTerm.eitherInl
        (RawTerm.subst_rename_commute value rawRenaming rawSubstitution)
  | .eitherInr value, rawRenaming, rawSubstitution => by
      exact congrArg RawTerm.eitherInr
        (RawTerm.subst_rename_commute value rawRenaming rawSubstitution)
  | .eitherMatch scrutinee leftBranch rightBranch, rawRenaming, rawSubstitution => by
      exact congrArgThree (function := RawTerm.eitherMatch)
        (RawTerm.subst_rename_commute scrutinee rawRenaming rawSubstitution)
        (RawTerm.subst_rename_commute leftBranch rawRenaming rawSubstitution)
        (RawTerm.subst_rename_commute rightBranch rawRenaming rawSubstitution)
  | .refl term, rawRenaming, rawSubstitution => by
      exact congrArg RawTerm.refl
        (RawTerm.subst_rename_commute term rawRenaming rawSubstitution)
  | .idJ baseCase witness, rawRenaming, rawSubstitution => by
      exact congrArgTwo (function := RawTerm.idJ)
        (RawTerm.subst_rename_commute baseCase rawRenaming rawSubstitution)
        (RawTerm.subst_rename_commute witness rawRenaming rawSubstitution)

/-- Compose a raw substitution with a raw rawRenaming. -/
def RawTermSubst.beforeRenaming {source middle target : Nat}
    (rawSubstitution : RawTermSubst source middle)
    (rawRenaming : Renaming middle target) :
    RawTermSubst source target :=
  fun position => (rawSubstitution position).rename rawRenaming

/-- Lifting agrees with composing a raw substitution before a raw rawRenaming. -/
theorem RawTermSubst.lift_beforeRenaming_equiv {source middle target : Nat}
    (rawSubstitution : RawTermSubst source middle)
    (rawRenaming : Renaming middle target) :
    RawTermSubst.equiv
      (RawTermSubst.lift
        (RawTermSubst.beforeRenaming rawSubstitution rawRenaming))
      (RawTermSubst.beforeRenaming rawSubstitution.lift rawRenaming.lift)
  | ⟨0, _⟩ => rfl
  | ⟨position + 1, isWithinSource⟩ =>
      (RawTerm.rename_weaken_commute
        (rawSubstitution
          ⟨position, Nat.lt_of_succ_lt_succ isWithinSource⟩)
        rawRenaming).symm

/-- Renaming after substitution composes the rawRenaming into the substitution. -/
theorem RawTerm.rename_subst_commute {source middle target : Nat} :
    ∀ (rawTerm : RawTerm source)
      (rawSubstitution : RawTermSubst source middle)
      (rawRenaming : Renaming middle target),
      (rawTerm.subst rawSubstitution).rename rawRenaming =
        rawTerm.subst (RawTermSubst.beforeRenaming rawSubstitution rawRenaming)
  | .var _, _, _ => rfl
  | .unit, _, _ => rfl
  | .boolTrue, _, _ => rfl
  | .boolFalse, _, _ => rfl
  | .natZero, _, _ => rfl
  | .natSucc predecessor, rawSubstitution, rawRenaming => by
      exact congrArg RawTerm.natSucc
        (RawTerm.rename_subst_commute predecessor rawSubstitution rawRenaming)
  | .lam body, rawSubstitution, rawRenaming => by
      have bodyComposition :=
        RawTerm.rename_subst_commute body rawSubstitution.lift rawRenaming.lift
      have liftComposition :=
        RawTerm.subst_congr
          (RawTermSubst.lift_beforeRenaming_equiv rawSubstitution rawRenaming)
          body
      exact congrArg RawTerm.lam (bodyComposition.trans liftComposition.symm)
  | .app function argument, rawSubstitution, rawRenaming => by
      exact congrArgTwo (function := RawTerm.app)
        (RawTerm.rename_subst_commute function rawSubstitution rawRenaming)
        (RawTerm.rename_subst_commute argument rawSubstitution rawRenaming)
  | .pair first second, rawSubstitution, rawRenaming => by
      exact congrArgTwo (function := RawTerm.pair)
        (RawTerm.rename_subst_commute first rawSubstitution rawRenaming)
        (RawTerm.rename_subst_commute second rawSubstitution rawRenaming)
  | .fst pairTerm, rawSubstitution, rawRenaming => by
      exact congrArg RawTerm.fst
        (RawTerm.rename_subst_commute pairTerm rawSubstitution rawRenaming)
  | .snd pairTerm, rawSubstitution, rawRenaming => by
      exact congrArg RawTerm.snd
        (RawTerm.rename_subst_commute pairTerm rawSubstitution rawRenaming)
  | .boolElim scrutinee thenBranch elseBranch, rawSubstitution, rawRenaming => by
      exact congrArgThree (function := RawTerm.boolElim)
        (RawTerm.rename_subst_commute scrutinee rawSubstitution rawRenaming)
        (RawTerm.rename_subst_commute thenBranch rawSubstitution rawRenaming)
        (RawTerm.rename_subst_commute elseBranch rawSubstitution rawRenaming)
  | .natElim scrutinee zeroBranch succBranch, rawSubstitution, rawRenaming => by
      exact congrArgThree (function := RawTerm.natElim)
        (RawTerm.rename_subst_commute scrutinee rawSubstitution rawRenaming)
        (RawTerm.rename_subst_commute zeroBranch rawSubstitution rawRenaming)
        (RawTerm.rename_subst_commute succBranch rawSubstitution rawRenaming)
  | .natRec scrutinee zeroBranch succBranch, rawSubstitution, rawRenaming => by
      exact congrArgThree (function := RawTerm.natRec)
        (RawTerm.rename_subst_commute scrutinee rawSubstitution rawRenaming)
        (RawTerm.rename_subst_commute zeroBranch rawSubstitution rawRenaming)
        (RawTerm.rename_subst_commute succBranch rawSubstitution rawRenaming)
  | .listNil, _, _ => rfl
  | .listCons head tail, rawSubstitution, rawRenaming => by
      exact congrArgTwo (function := RawTerm.listCons)
        (RawTerm.rename_subst_commute head rawSubstitution rawRenaming)
        (RawTerm.rename_subst_commute tail rawSubstitution rawRenaming)
  | .listElim scrutinee nilBranch consBranch, rawSubstitution, rawRenaming => by
      exact congrArgThree (function := RawTerm.listElim)
        (RawTerm.rename_subst_commute scrutinee rawSubstitution rawRenaming)
        (RawTerm.rename_subst_commute nilBranch rawSubstitution rawRenaming)
        (RawTerm.rename_subst_commute consBranch rawSubstitution rawRenaming)
  | .optionNone, _, _ => rfl
  | .optionSome value, rawSubstitution, rawRenaming => by
      exact congrArg RawTerm.optionSome
        (RawTerm.rename_subst_commute value rawSubstitution rawRenaming)
  | .optionMatch scrutinee noneBranch someBranch, rawSubstitution, rawRenaming => by
      exact congrArgThree (function := RawTerm.optionMatch)
        (RawTerm.rename_subst_commute scrutinee rawSubstitution rawRenaming)
        (RawTerm.rename_subst_commute noneBranch rawSubstitution rawRenaming)
        (RawTerm.rename_subst_commute someBranch rawSubstitution rawRenaming)
  | .eitherInl value, rawSubstitution, rawRenaming => by
      exact congrArg RawTerm.eitherInl
        (RawTerm.rename_subst_commute value rawSubstitution rawRenaming)
  | .eitherInr value, rawSubstitution, rawRenaming => by
      exact congrArg RawTerm.eitherInr
        (RawTerm.rename_subst_commute value rawSubstitution rawRenaming)
  | .eitherMatch scrutinee leftBranch rightBranch, rawSubstitution, rawRenaming => by
      exact congrArgThree (function := RawTerm.eitherMatch)
        (RawTerm.rename_subst_commute scrutinee rawSubstitution rawRenaming)
        (RawTerm.rename_subst_commute leftBranch rawSubstitution rawRenaming)
        (RawTerm.rename_subst_commute rightBranch rawSubstitution rawRenaming)
  | .refl term, rawSubstitution, rawRenaming => by
      exact congrArg RawTerm.refl
        (RawTerm.rename_subst_commute term rawSubstitution rawRenaming)
  | .idJ baseCase witness, rawSubstitution, rawRenaming => by
      exact congrArgTwo (function := RawTerm.idJ)
        (RawTerm.rename_subst_commute baseCase rawSubstitution rawRenaming)
        (RawTerm.rename_subst_commute witness rawSubstitution rawRenaming)

/-- Substitution commutes with weakening for raw terms. -/
theorem RawTerm.subst_weaken_commute {source target : Nat} :
    ∀ (rawTerm : RawTerm source) (rawSubstitution : RawTermSubst source target),
      rawTerm.weaken.subst rawSubstitution.lift =
        (rawTerm.subst rawSubstitution).weaken
  | rawTerm, rawSubstitution => by
      have renamedThenSubstituted :=
        RawTerm.subst_rename_commute rawTerm Renaming.weaken rawSubstitution.lift
      have weakenedSubstitution :
          RawTerm.subst
              rawTerm
              (RawTermSubst.afterRenaming Renaming.weaken rawSubstitution.lift)
            =
            RawTerm.subst
              rawTerm
              (RawTermSubst.beforeRenaming rawSubstitution Renaming.weaken) :=
        RawTerm.subst_congr (fun _ => rfl) rawTerm
      have substitutedThenWeakened :
          RawTerm.subst
              rawTerm
              (RawTermSubst.beforeRenaming rawSubstitution Renaming.weaken)
            =
            (rawTerm.subst rawSubstitution).weaken :=
        (RawTerm.rename_subst_commute rawTerm rawSubstitution Renaming.weaken).symm
      exact renamedThenSubstituted.trans
        (weakenedSubstitution.trans substitutedThenWeakened)

/-- Compose raw substitutions. -/
def RawTermSubst.compose {source middle target : Nat}
    (firstSubstitution : RawTermSubst source middle)
    (secondSubstitution : RawTermSubst middle target) :
    RawTermSubst source target :=
  fun position => (firstSubstitution position).subst secondSubstitution

/-- Lifting raw-substitution composition agrees pointwise with composing lifts. -/
theorem RawTermSubst.lift_compose_equiv {source middle target : Nat}
    (firstSubstitution : RawTermSubst source middle)
    (secondSubstitution : RawTermSubst middle target) :
    RawTermSubst.equiv
      (RawTermSubst.lift
        (RawTermSubst.compose firstSubstitution secondSubstitution))
      (RawTermSubst.compose firstSubstitution.lift secondSubstitution.lift)
  | ⟨0, _⟩ => rfl
  | ⟨position + 1, isWithinSource⟩ =>
      (RawTerm.subst_weaken_commute
        (firstSubstitution
          ⟨position, Nat.lt_of_succ_lt_succ isWithinSource⟩)
        secondSubstitution).symm

/-- Raw substitution composition law. -/
theorem RawTerm.subst_compose {source middle target : Nat} :
    ∀ (rawTerm : RawTerm source)
      (firstSubstitution : RawTermSubst source middle)
      (secondSubstitution : RawTermSubst middle target),
      (rawTerm.subst firstSubstitution).subst secondSubstitution =
        rawTerm.subst (RawTermSubst.compose firstSubstitution secondSubstitution)
  | .var _, _, _ => rfl
  | .unit, _, _ => rfl
  | .boolTrue, _, _ => rfl
  | .boolFalse, _, _ => rfl
  | .natZero, _, _ => rfl
  | .natSucc predecessor, firstSubstitution, secondSubstitution => by
      exact congrArg RawTerm.natSucc
        (RawTerm.subst_compose predecessor firstSubstitution secondSubstitution)
  | .lam body, firstSubstitution, secondSubstitution => by
      have bodyComposition :=
        RawTerm.subst_compose body firstSubstitution.lift secondSubstitution.lift
      have liftComposition :=
        RawTerm.subst_congr
          (RawTermSubst.lift_compose_equiv firstSubstitution secondSubstitution)
          body
      exact congrArg RawTerm.lam (bodyComposition.trans liftComposition.symm)
  | .app function argument, firstSubstitution, secondSubstitution => by
      exact congrArgTwo (function := RawTerm.app)
        (RawTerm.subst_compose function firstSubstitution secondSubstitution)
        (RawTerm.subst_compose argument firstSubstitution secondSubstitution)
  | .pair first second, firstSubstitution, secondSubstitution => by
      exact congrArgTwo (function := RawTerm.pair)
        (RawTerm.subst_compose first firstSubstitution secondSubstitution)
        (RawTerm.subst_compose second firstSubstitution secondSubstitution)
  | .fst pairTerm, firstSubstitution, secondSubstitution => by
      exact congrArg RawTerm.fst
        (RawTerm.subst_compose pairTerm firstSubstitution secondSubstitution)
  | .snd pairTerm, firstSubstitution, secondSubstitution => by
      exact congrArg RawTerm.snd
        (RawTerm.subst_compose pairTerm firstSubstitution secondSubstitution)
  | .boolElim scrutinee thenBranch elseBranch, firstSubstitution, secondSubstitution => by
      exact congrArgThree (function := RawTerm.boolElim)
        (RawTerm.subst_compose scrutinee firstSubstitution secondSubstitution)
        (RawTerm.subst_compose thenBranch firstSubstitution secondSubstitution)
        (RawTerm.subst_compose elseBranch firstSubstitution secondSubstitution)
  | .natElim scrutinee zeroBranch succBranch, firstSubstitution, secondSubstitution => by
      exact congrArgThree (function := RawTerm.natElim)
        (RawTerm.subst_compose scrutinee firstSubstitution secondSubstitution)
        (RawTerm.subst_compose zeroBranch firstSubstitution secondSubstitution)
        (RawTerm.subst_compose succBranch firstSubstitution secondSubstitution)
  | .natRec scrutinee zeroBranch succBranch, firstSubstitution, secondSubstitution => by
      exact congrArgThree (function := RawTerm.natRec)
        (RawTerm.subst_compose scrutinee firstSubstitution secondSubstitution)
        (RawTerm.subst_compose zeroBranch firstSubstitution secondSubstitution)
        (RawTerm.subst_compose succBranch firstSubstitution secondSubstitution)
  | .listNil, _, _ => rfl
  | .listCons head tail, firstSubstitution, secondSubstitution => by
      exact congrArgTwo (function := RawTerm.listCons)
        (RawTerm.subst_compose head firstSubstitution secondSubstitution)
        (RawTerm.subst_compose tail firstSubstitution secondSubstitution)
  | .listElim scrutinee nilBranch consBranch, firstSubstitution, secondSubstitution => by
      exact congrArgThree (function := RawTerm.listElim)
        (RawTerm.subst_compose scrutinee firstSubstitution secondSubstitution)
        (RawTerm.subst_compose nilBranch firstSubstitution secondSubstitution)
        (RawTerm.subst_compose consBranch firstSubstitution secondSubstitution)
  | .optionNone, _, _ => rfl
  | .optionSome value, firstSubstitution, secondSubstitution => by
      exact congrArg RawTerm.optionSome
        (RawTerm.subst_compose value firstSubstitution secondSubstitution)
  | .optionMatch scrutinee noneBranch someBranch, firstSubstitution, secondSubstitution => by
      exact congrArgThree (function := RawTerm.optionMatch)
        (RawTerm.subst_compose scrutinee firstSubstitution secondSubstitution)
        (RawTerm.subst_compose noneBranch firstSubstitution secondSubstitution)
        (RawTerm.subst_compose someBranch firstSubstitution secondSubstitution)
  | .eitherInl value, firstSubstitution, secondSubstitution => by
      exact congrArg RawTerm.eitherInl
        (RawTerm.subst_compose value firstSubstitution secondSubstitution)
  | .eitherInr value, firstSubstitution, secondSubstitution => by
      exact congrArg RawTerm.eitherInr
        (RawTerm.subst_compose value firstSubstitution secondSubstitution)
  | .eitherMatch scrutinee leftBranch rightBranch, firstSubstitution, secondSubstitution => by
      exact congrArgThree (function := RawTerm.eitherMatch)
        (RawTerm.subst_compose scrutinee firstSubstitution secondSubstitution)
        (RawTerm.subst_compose leftBranch firstSubstitution secondSubstitution)
        (RawTerm.subst_compose rightBranch firstSubstitution secondSubstitution)
  | .refl term, firstSubstitution, secondSubstitution => by
      exact congrArg RawTerm.refl
        (RawTerm.subst_compose term firstSubstitution secondSubstitution)
  | .idJ baseCase witness, firstSubstitution, secondSubstitution => by
      exact congrArgTwo (function := RawTerm.idJ)
        (RawTerm.subst_compose baseCase firstSubstitution secondSubstitution)
        (RawTerm.subst_compose witness firstSubstitution secondSubstitution)

/-- Weakening followed by the raw drop-newest substitution is identity.
This is the raw counterpart of `Ty.weaken_subst_singleton`. -/
theorem RawTerm.weaken_subst_dropNewest {scope : Nat} (rawTerm : RawTerm scope) :
    rawTerm.weaken.subst RawTermSubst.dropNewest = rawTerm := by
  have renamedThenSubstituted :=
    RawTerm.subst_rename_commute rawTerm
      (@Renaming.weaken scope)
      (@RawTermSubst.dropNewest scope)
  have afterRenamingIsIdentity :
      RawTermSubst.equiv
        (RawTermSubst.afterRenaming
          (@Renaming.weaken scope)
          (@RawTermSubst.dropNewest scope))
        (@RawTermSubst.identity scope) :=
    RawTermSubst.afterRenaming_weaken_dropNewest_equiv_identity
  have congruentSubstitution :=
    RawTerm.subst_congr afterRenamingIsIdentity rawTerm
  exact renamedThenSubstituted.trans
    (congruentSubstitution.trans (RawTerm.subst_id rawTerm))

/-- Singleton raw substitution: replace position 0 with `substituent`,
shift all higher positions down by one.  Used by raw β-reduction
(`RawTerm.subst0`).  Mirrors the typed `Subst.singleton` whose raw
component is `dropNewest`; the two coincide when `substituent` is
unit, which is exactly the typed-singleton-on-Ty case (Ty has no raw
substituent dependency, so the raw side just discards position 0). -/
def RawTermSubst.singleton {scope : Nat} (substituent : RawTerm scope) :
    RawTermSubst (scope + 1) scope
  | ⟨0, _⟩ => substituent
  | ⟨position + 1, isWithinScope⟩ =>
      RawTerm.var ⟨position, Nat.lt_of_succ_lt_succ isWithinScope⟩

/-- The raw counterpart of typed `Term.subst0`: substitute `argument`
for de Bruijn 0 in `body`. -/
def RawTerm.subst0 {scope : Nat}
    (body : RawTerm (scope + 1)) (argument : RawTerm scope) :
    RawTerm scope :=
  body.subst (RawTermSubst.singleton argument)

namespace SmokeTestRaw

/-- Substituting the only variable in a one-variable raw term. -/
def substUnitForSingleVariable : RawTermSubst 1 0 :=
  fun _ => RawTerm.unit

example :
    RawTerm.subst (RawTerm.var ⟨0, Nat.succ_pos 0⟩)
      substUnitForSingleVariable = RawTerm.unit := rfl

/-- Substitution under a raw lambda preserves the freshly-bound variable. -/
example :
    RawTerm.subst (RawTerm.lam (RawTerm.var ⟨0, Nat.succ_pos 1⟩))
      substUnitForSingleVariable
      = RawTerm.lam (RawTerm.var ⟨0, Nat.succ_pos 0⟩) := rfl

/-- Substitution reaches through identity raw syntax. -/
example :
    RawTerm.subst (RawTerm.refl (RawTerm.var ⟨0, Nat.succ_pos 0⟩))
      substUnitForSingleVariable
      = RawTerm.refl RawTerm.unit := rfl

end SmokeTestRaw

end LeanFX.Syntax

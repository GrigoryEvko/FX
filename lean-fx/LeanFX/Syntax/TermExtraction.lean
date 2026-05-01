import LeanFX.Syntax.TypedTerm
import LeanFX.Syntax.ToRaw

/-! ## Typed-extraction helpers.

For each Term constructor C with payload P at restricted type
indices, `Term.<payload>_of_<C>_general` is a propext-free
**computational** def that extracts P from any Term whose toRaw
form is `RawTerm.<C> ...`.

These helpers are the bridge between Term.cd's outer `Term`
match (clean — Rule 3 of the zero-axiom match recipe) and its
inner redex contractions, which dispatch on the developed
child's shape.  Direct typed match `| Term.lam body =>` on a
restricted-index scrutinee leaks propext (Rule 4); toRaw-shape
match alone gives only the raw form (no typed payload).  These
extractors solve the gap: given a witness whose toRaw is a
specific RawTerm constructor, extract the typed payload by
running `cases witness` at universal type (Rule 3) and
discharging non-target constructors via `simp [Term.toRaw] at
rawEq; cases rawEq` (toRaw constructor mismatch) or
`cases typeEq` (Ty constructor mismatch).

Each extractor is sanity-checked: extraction from a literal
constructor reduces to its payload via `rfl`. -/

namespace LeanFX.Syntax
open LeanFX.Mode

/-! ### β-app: extract `Term.lam`'s body. -/

/-- Extract the body from a Term proven to be `Term.lam` via its
type (`Ty.arrow ...`) and toRaw shape (`RawTerm.lam ...`).
Computational: `body_of_lam_general (Term.lam body) rfl rfl = body`
by `rfl`. -/
def Term.body_of_lam_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {domainType codomainType : Ty level scope}
    (typeEq : ty = Ty.arrow domainType codomainType)
    {rawBody : RawTerm (scope+1)}
    (rawEq : Term.toRaw witness = RawTerm.lam rawBody) :
    Term (ctx.cons domainType) codomainType.weaken := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => simp only [Term.toRaw] at rawEq; cases rawEq
  | lam body => cases typeEq; exact body
  | app function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | lamPi body => cases typeEq
  | appPi function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | pair firstVal secondVal => cases typeEq
  | fst pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | snd pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | boolTrue => cases typeEq
  | boolFalse => cases typeEq
  | boolElim scrutinee thenBranch elseBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natZero => cases typeEq
  | natSucc predecessor => cases typeEq
  | natElim scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natRec scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | listNil => cases typeEq
  | listCons head tail => cases typeEq
  | listElim scrutinee nilBranch consBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | optionNone => cases typeEq
  | optionSome value => cases typeEq
  | optionMatch scrutinee noneBranch someBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherInl value => cases typeEq
  | eitherInr value => cases typeEq
  | eitherMatch scrutinee leftBranch rightBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | refl rawTerm => cases typeEq
  | idJ baseCase witness =>
      simp only [Term.toRaw] at rawEq; cases rawEq

/-! ### β-appPi: extract `Term.lamPi`'s body.

The Π-flavoured body lives at scope+1 with its own codomainType
(no weaken — `lamPi`'s codomain is already at the extended
scope). -/

/-- Extract the body from a Term proven to be `Term.lamPi` via
type `Ty.piTy ...` and toRaw `RawTerm.lam ...`. -/
def Term.body_of_lamPi_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {domainType : Ty level scope}
    {codomainType : Ty level (scope+1)}
    (typeEq : ty = Ty.piTy domainType codomainType)
    {rawBody : RawTerm (scope+1)}
    (rawEq : Term.toRaw witness = RawTerm.lam rawBody) :
    Term (ctx.cons domainType) codomainType := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => simp only [Term.toRaw] at rawEq; cases rawEq
  | lam body => cases typeEq
  | app function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | lamPi body => cases typeEq; exact body
  | appPi function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | pair firstVal secondVal => cases typeEq
  | fst pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | snd pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | boolTrue => cases typeEq
  | boolFalse => cases typeEq
  | boolElim scrutinee thenBranch elseBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natZero => cases typeEq
  | natSucc predecessor => cases typeEq
  | natElim scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natRec scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | listNil => cases typeEq
  | listCons head tail => cases typeEq
  | listElim scrutinee nilBranch consBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | optionNone => cases typeEq
  | optionSome value => cases typeEq
  | optionMatch scrutinee noneBranch someBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherInl value => cases typeEq
  | eitherInr value => cases typeEq
  | eitherMatch scrutinee leftBranch rightBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | refl rawTerm => cases typeEq
  | idJ baseCase witness =>
      simp only [Term.toRaw] at rawEq; cases rawEq

/-! ### β-fst / β-snd: extract `Term.pair`'s components. -/

/-- Extract the first component from a Term proven to be
`Term.pair` via type `Ty.sigmaTy ...` and toRaw `RawTerm.pair ...`. -/
def Term.firstVal_of_pair_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {firstType : Ty level scope}
    {secondType : Ty level (scope+1)}
    (typeEq : ty = Ty.sigmaTy firstType secondType)
    {rawFirst rawSecond : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.pair rawFirst rawSecond) :
    Term ctx firstType := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => simp only [Term.toRaw] at rawEq; cases rawEq
  | lam body => cases typeEq
  | app function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | lamPi body => cases typeEq
  | appPi function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | pair firstVal secondVal => cases typeEq; exact firstVal
  | fst pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | snd pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | boolTrue => cases typeEq
  | boolFalse => cases typeEq
  | boolElim scrutinee thenBranch elseBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natZero => cases typeEq
  | natSucc predecessor => cases typeEq
  | natElim scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natRec scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | listNil => cases typeEq
  | listCons head tail => cases typeEq
  | listElim scrutinee nilBranch consBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | optionNone => cases typeEq
  | optionSome value => cases typeEq
  | optionMatch scrutinee noneBranch someBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherInl value => cases typeEq
  | eitherInr value => cases typeEq
  | eitherMatch scrutinee leftBranch rightBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | refl rawTerm => cases typeEq
  | idJ baseCase witness =>
      simp only [Term.toRaw] at rawEq; cases rawEq

/-- Extract the second component from a Term proven to be
`Term.pair` via type and toRaw. -/
def Term.secondVal_of_pair_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {firstType : Ty level scope}
    {secondType : Ty level (scope+1)}
    (typeEq : ty = Ty.sigmaTy firstType secondType)
    {rawFirst rawSecond : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.pair rawFirst rawSecond) :
    Term ctx (secondType.subst0 firstType) := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => simp only [Term.toRaw] at rawEq; cases rawEq
  | lam body => cases typeEq
  | app function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | lamPi body => cases typeEq
  | appPi function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | pair firstVal secondVal => cases typeEq; exact secondVal
  | fst pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | snd pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | boolTrue => cases typeEq
  | boolFalse => cases typeEq
  | boolElim scrutinee thenBranch elseBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natZero => cases typeEq
  | natSucc predecessor => cases typeEq
  | natElim scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natRec scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | listNil => cases typeEq
  | listCons head tail => cases typeEq
  | listElim scrutinee nilBranch consBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | optionNone => cases typeEq
  | optionSome value => cases typeEq
  | optionMatch scrutinee noneBranch someBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherInl value => cases typeEq
  | eitherInr value => cases typeEq
  | eitherMatch scrutinee leftBranch rightBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | refl rawTerm => cases typeEq
  | idJ baseCase witness =>
      simp only [Term.toRaw] at rawEq; cases rawEq

/-! ### ι-natSucc: extract predecessor. -/

/-- Extract the predecessor from a Term proven to be
`Term.natSucc` via type `Ty.nat` and toRaw `RawTerm.natSucc ...`. -/
def Term.predecessor_of_natSucc_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    (typeEq : ty = Ty.nat)
    {rawPred : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.natSucc rawPred) :
    Term ctx Ty.nat := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => simp only [Term.toRaw] at rawEq; cases rawEq
  | lam body => cases typeEq
  | app function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | lamPi body => cases typeEq
  | appPi function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | pair firstVal secondVal => cases typeEq
  | fst pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | snd pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | boolTrue => cases typeEq
  | boolFalse => cases typeEq
  | boolElim scrutinee thenBranch elseBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natZero => simp only [Term.toRaw] at rawEq; cases rawEq
  | natSucc predecessor => cases typeEq; exact predecessor
  | natElim scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natRec scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | listNil => cases typeEq
  | listCons head tail => cases typeEq
  | listElim scrutinee nilBranch consBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | optionNone => cases typeEq
  | optionSome value => cases typeEq
  | optionMatch scrutinee noneBranch someBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherInl value => cases typeEq
  | eitherInr value => cases typeEq
  | eitherMatch scrutinee leftBranch rightBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | refl rawTerm => cases typeEq
  | idJ baseCase witness =>
      simp only [Term.toRaw] at rawEq; cases rawEq

/-! ### ι-listCons: extract head + tail. -/

/-- Extract the head from a Term proven to be `Term.listCons`. -/
def Term.head_of_listCons_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {elementType : Ty level scope}
    (typeEq : ty = Ty.list elementType)
    {rawHead rawTail : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.listCons rawHead rawTail) :
    Term ctx elementType := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => simp only [Term.toRaw] at rawEq; cases rawEq
  | lam body => cases typeEq
  | app function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | lamPi body => cases typeEq
  | appPi function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | pair firstVal secondVal => cases typeEq
  | fst pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | snd pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | boolTrue => cases typeEq
  | boolFalse => cases typeEq
  | boolElim scrutinee thenBranch elseBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natZero => cases typeEq
  | natSucc predecessor => cases typeEq
  | natElim scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natRec scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | listNil => simp only [Term.toRaw] at rawEq; cases rawEq
  | listCons head tail => cases typeEq; exact head
  | listElim scrutinee nilBranch consBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | optionNone => cases typeEq
  | optionSome value => cases typeEq
  | optionMatch scrutinee noneBranch someBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherInl value => cases typeEq
  | eitherInr value => cases typeEq
  | eitherMatch scrutinee leftBranch rightBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | refl rawTerm => cases typeEq
  | idJ baseCase witness =>
      simp only [Term.toRaw] at rawEq; cases rawEq

/-- Extract the tail from a Term proven to be `Term.listCons`. -/
def Term.tail_of_listCons_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {elementType : Ty level scope}
    (typeEq : ty = Ty.list elementType)
    {rawHead rawTail : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.listCons rawHead rawTail) :
    Term ctx (Ty.list elementType) := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => simp only [Term.toRaw] at rawEq; cases rawEq
  | lam body => cases typeEq
  | app function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | lamPi body => cases typeEq
  | appPi function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | pair firstVal secondVal => cases typeEq
  | fst pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | snd pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | boolTrue => cases typeEq
  | boolFalse => cases typeEq
  | boolElim scrutinee thenBranch elseBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natZero => cases typeEq
  | natSucc predecessor => cases typeEq
  | natElim scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natRec scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | listNil => simp only [Term.toRaw] at rawEq; cases rawEq
  | listCons head tail => cases typeEq; exact tail
  | listElim scrutinee nilBranch consBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | optionNone => cases typeEq
  | optionSome value => cases typeEq
  | optionMatch scrutinee noneBranch someBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherInl value => cases typeEq
  | eitherInr value => cases typeEq
  | eitherMatch scrutinee leftBranch rightBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | refl rawTerm => cases typeEq
  | idJ baseCase witness =>
      simp only [Term.toRaw] at rawEq; cases rawEq

/-! ### ι-optionSome: extract value. -/

/-- Extract the value from a Term proven to be `Term.optionSome`. -/
def Term.value_of_optionSome_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {elementType : Ty level scope}
    (typeEq : ty = Ty.option elementType)
    {rawValue : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.optionSome rawValue) :
    Term ctx elementType := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => simp only [Term.toRaw] at rawEq; cases rawEq
  | lam body => cases typeEq
  | app function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | lamPi body => cases typeEq
  | appPi function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | pair firstVal secondVal => cases typeEq
  | fst pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | snd pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | boolTrue => cases typeEq
  | boolFalse => cases typeEq
  | boolElim scrutinee thenBranch elseBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natZero => cases typeEq
  | natSucc predecessor => cases typeEq
  | natElim scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natRec scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | listNil => cases typeEq
  | listCons head tail => cases typeEq
  | listElim scrutinee nilBranch consBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | optionNone => simp only [Term.toRaw] at rawEq; cases rawEq
  | optionSome value => cases typeEq; exact value
  | optionMatch scrutinee noneBranch someBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherInl value => cases typeEq
  | eitherInr value => cases typeEq
  | eitherMatch scrutinee leftBranch rightBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | refl rawTerm => cases typeEq
  | idJ baseCase witness =>
      simp only [Term.toRaw] at rawEq; cases rawEq

/-! ### ι-eitherInl / ι-eitherInr: extract value. -/

/-- Extract the value from a Term proven to be `Term.eitherInl`. -/
def Term.value_of_eitherInl_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {leftType rightType : Ty level scope}
    (typeEq : ty = Ty.either leftType rightType)
    {rawValue : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.eitherInl rawValue) :
    Term ctx leftType := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => simp only [Term.toRaw] at rawEq; cases rawEq
  | lam body => cases typeEq
  | app function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | lamPi body => cases typeEq
  | appPi function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | pair firstVal secondVal => cases typeEq
  | fst pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | snd pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | boolTrue => cases typeEq
  | boolFalse => cases typeEq
  | boolElim scrutinee thenBranch elseBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natZero => cases typeEq
  | natSucc predecessor => cases typeEq
  | natElim scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natRec scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | listNil => cases typeEq
  | listCons head tail => cases typeEq
  | listElim scrutinee nilBranch consBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | optionNone => cases typeEq
  | optionSome value => cases typeEq
  | optionMatch scrutinee noneBranch someBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherInl value => cases typeEq; exact value
  | eitherInr value => simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherMatch scrutinee leftBranch rightBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | refl rawTerm => cases typeEq
  | idJ baseCase witness =>
      simp only [Term.toRaw] at rawEq; cases rawEq

/-- Extract the value from a Term proven to be `Term.eitherInr`. -/
def Term.value_of_eitherInr_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {leftType rightType : Ty level scope}
    (typeEq : ty = Ty.either leftType rightType)
    {rawValue : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.eitherInr rawValue) :
    Term ctx rightType := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => simp only [Term.toRaw] at rawEq; cases rawEq
  | lam body => cases typeEq
  | app function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | lamPi body => cases typeEq
  | appPi function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | pair firstVal secondVal => cases typeEq
  | fst pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | snd pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | boolTrue => cases typeEq
  | boolFalse => cases typeEq
  | boolElim scrutinee thenBranch elseBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natZero => cases typeEq
  | natSucc predecessor => cases typeEq
  | natElim scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | natRec scrutinee zeroBranch succBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | listNil => cases typeEq
  | listCons head tail => cases typeEq
  | listElim scrutinee nilBranch consBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | optionNone => cases typeEq
  | optionSome value => cases typeEq
  | optionMatch scrutinee noneBranch someBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherInl value => simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherInr value => cases typeEq; exact value
  | eitherMatch scrutinee leftBranch rightBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | refl rawTerm => cases typeEq
  | idJ baseCase witness =>
      simp only [Term.toRaw] at rawEq; cases rawEq

end LeanFX.Syntax

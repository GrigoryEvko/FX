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

/-! ## Bridging inversion equations.

Each of the following lemmas establishes
  `witness = <head> (extracted payload)`
when the witness is at the right type and has the right toRaw
shape.  Proof structure mirrors the typed extractors above:
generalize to free `ty`, run `cases witness` at universal index
(Rule 3), discharge non-target ctors via constructor mismatch,
and close the target ctor branch by `rfl` (since the extractor
in that branch returns the literal payload). -/

/-- Generalized: `witness = Term.lam ...` modulo HEq. -/
theorem Term.eq_lam_of_toRaw_lam_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {domainType codomainType : Ty level scope}
    (typeEq : ty = Ty.arrow domainType codomainType)
    {rawBody : RawTerm (scope+1)}
    (rawEq : Term.toRaw witness = RawTerm.lam rawBody) :
    HEq witness
      (@Term.lam mode level scope ctx domainType codomainType
        (Term.body_of_lam_general witness typeEq rawEq)) := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => cases typeEq
  | lam body => cases typeEq; rfl
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

theorem Term.eq_lam_of_toRaw_lam
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    (witness : Term ctx (Ty.arrow domainType codomainType))
    {rawBody : RawTerm (scope+1)}
    (rawEq : Term.toRaw witness = RawTerm.lam rawBody) :
    witness =
      Term.lam (Term.body_of_lam_general witness rfl rawEq) :=
  eq_of_heq (Term.eq_lam_of_toRaw_lam_general witness rfl rawEq)

/-- Generalized: `witness = Term.lamPi ...` modulo HEq. -/
theorem Term.eq_lamPi_of_toRaw_lam_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {domainType : Ty level scope}
    {codomainType : Ty level (scope+1)}
    (typeEq : ty = Ty.piTy domainType codomainType)
    {rawBody : RawTerm (scope+1)}
    (rawEq : Term.toRaw witness = RawTerm.lam rawBody) :
    HEq witness
      (@Term.lamPi mode level scope ctx domainType codomainType
        (Term.body_of_lamPi_general witness typeEq rawEq)) := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => cases typeEq
  | lam body => cases typeEq
  | app function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | lamPi body => cases typeEq; rfl
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

theorem Term.eq_lamPi_of_toRaw_lam
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope+1)}
    (witness : Term ctx (Ty.piTy domainType codomainType))
    {rawBody : RawTerm (scope+1)}
    (rawEq : Term.toRaw witness = RawTerm.lam rawBody) :
    witness =
      Term.lamPi (Term.body_of_lamPi_general witness rfl rawEq) :=
  eq_of_heq (Term.eq_lamPi_of_toRaw_lam_general witness rfl rawEq)

/-- Generalized: `witness = Term.pair ...` modulo HEq. -/
theorem Term.eq_pair_of_toRaw_pair_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {firstType : Ty level scope}
    {secondType : Ty level (scope+1)}
    (typeEq : ty = Ty.sigmaTy firstType secondType)
    {rawFirst rawSecond : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.pair rawFirst rawSecond) :
    HEq witness
      (@Term.pair mode level scope ctx firstType secondType
        (Term.firstVal_of_pair_general witness typeEq rawEq)
        (Term.secondVal_of_pair_general witness typeEq rawEq)) := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => cases typeEq
  | lam body => cases typeEq
  | app function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | lamPi body => cases typeEq
  | appPi function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | pair firstVal secondVal => cases typeEq; rfl
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

theorem Term.eq_pair_of_toRaw_pair
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope+1)}
    (witness : Term ctx (Ty.sigmaTy firstType secondType))
    {rawFirst rawSecond : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.pair rawFirst rawSecond) :
    witness =
      Term.pair
        (Term.firstVal_of_pair_general witness rfl rawEq)
        (Term.secondVal_of_pair_general witness rfl rawEq) :=
  eq_of_heq (Term.eq_pair_of_toRaw_pair_general witness rfl rawEq)

/-- Generalized: `witness = Term.boolTrue` modulo HEq. -/
theorem Term.eq_boolTrue_of_toRaw_boolTrue_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    (typeEq : ty = Ty.bool)
    (rawEq : Term.toRaw witness = RawTerm.boolTrue) :
    HEq witness (@Term.boolTrue mode level scope ctx) := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => cases typeEq
  | lam body => cases typeEq
  | app function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | lamPi body => cases typeEq
  | appPi function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | pair firstVal secondVal => cases typeEq
  | fst pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | snd pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | boolTrue => rfl
  | boolFalse => simp only [Term.toRaw] at rawEq; cases rawEq
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

theorem Term.eq_boolTrue_of_toRaw_boolTrue
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    (witness : Term ctx Ty.bool)
    (rawEq : Term.toRaw witness = RawTerm.boolTrue) :
    witness = Term.boolTrue :=
  eq_of_heq
    (Term.eq_boolTrue_of_toRaw_boolTrue_general witness rfl rawEq)

/-- Generalized: `witness = Term.boolFalse` modulo HEq. -/
theorem Term.eq_boolFalse_of_toRaw_boolFalse_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    (typeEq : ty = Ty.bool)
    (rawEq : Term.toRaw witness = RawTerm.boolFalse) :
    HEq witness (@Term.boolFalse mode level scope ctx) := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => cases typeEq
  | lam body => cases typeEq
  | app function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | lamPi body => cases typeEq
  | appPi function argument =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | pair firstVal secondVal => cases typeEq
  | fst pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | snd pairTerm => simp only [Term.toRaw] at rawEq; cases rawEq
  | boolTrue => simp only [Term.toRaw] at rawEq; cases rawEq
  | boolFalse => rfl
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

theorem Term.eq_boolFalse_of_toRaw_boolFalse
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    (witness : Term ctx Ty.bool)
    (rawEq : Term.toRaw witness = RawTerm.boolFalse) :
    witness = Term.boolFalse :=
  eq_of_heq
    (Term.eq_boolFalse_of_toRaw_boolFalse_general witness rfl rawEq)

/-- Generalized: `witness = Term.natZero` modulo HEq. -/
theorem Term.eq_natZero_of_toRaw_natZero_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    (typeEq : ty = Ty.nat)
    (rawEq : Term.toRaw witness = RawTerm.natZero) :
    HEq witness (@Term.natZero mode level scope ctx) := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => cases typeEq
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
  | natZero => rfl
  | natSucc predecessor =>
      simp only [Term.toRaw] at rawEq; cases rawEq
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

theorem Term.eq_natZero_of_toRaw_natZero
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    (witness : Term ctx Ty.nat)
    (rawEq : Term.toRaw witness = RawTerm.natZero) :
    witness = Term.natZero :=
  eq_of_heq
    (Term.eq_natZero_of_toRaw_natZero_general witness rfl rawEq)

/-- Generalized: `witness = Term.natSucc ...` modulo HEq. -/
theorem Term.eq_natSucc_of_toRaw_natSucc_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    (typeEq : ty = Ty.nat)
    {rawPred : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.natSucc rawPred) :
    HEq witness
      (@Term.natSucc mode level scope ctx
        (Term.predecessor_of_natSucc_general witness typeEq rawEq)) := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => cases typeEq
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
  | natSucc predecessor => cases typeEq; rfl
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

theorem Term.eq_natSucc_of_toRaw_natSucc
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    (witness : Term ctx Ty.nat)
    {rawPred : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.natSucc rawPred) :
    witness = Term.natSucc
        (Term.predecessor_of_natSucc_general witness rfl rawEq) :=
  eq_of_heq
    (Term.eq_natSucc_of_toRaw_natSucc_general witness rfl rawEq)

/-- Generalized: `witness = Term.listNil` modulo HEq. -/
theorem Term.eq_listNil_of_toRaw_listNil_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {elementType : Ty level scope}
    (typeEq : ty = Ty.list elementType)
    (rawEq : Term.toRaw witness = RawTerm.listNil) :
    HEq witness (@Term.listNil mode level scope ctx elementType) := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => cases typeEq
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
  | listNil => cases typeEq; rfl
  | listCons head tail =>
      simp only [Term.toRaw] at rawEq; cases rawEq
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

theorem Term.eq_listNil_of_toRaw_listNil
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    (witness : Term ctx (Ty.list elementType))
    (rawEq : Term.toRaw witness = RawTerm.listNil) :
    witness = Term.listNil :=
  eq_of_heq
    (Term.eq_listNil_of_toRaw_listNil_general witness rfl rawEq)

/-- Generalized eq_listCons. -/
theorem Term.eq_listCons_of_toRaw_listCons_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {elementType : Ty level scope}
    (typeEq : ty = Ty.list elementType)
    {rawHead rawTail : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.listCons rawHead rawTail) :
    HEq witness
      (@Term.listCons mode level scope ctx elementType
        (Term.head_of_listCons_general witness typeEq rawEq)
        (Term.tail_of_listCons_general witness typeEq rawEq)) := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => cases typeEq
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
  | listCons head tail => cases typeEq; rfl
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

theorem Term.eq_listCons_of_toRaw_listCons
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    (witness : Term ctx (Ty.list elementType))
    {rawHead rawTail : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.listCons rawHead rawTail) :
    witness =
      Term.listCons
        (Term.head_of_listCons_general witness rfl rawEq)
        (Term.tail_of_listCons_general witness rfl rawEq) :=
  eq_of_heq
    (Term.eq_listCons_of_toRaw_listCons_general witness rfl rawEq)

/-- Generalized: `witness = Term.optionNone` modulo HEq. -/
theorem Term.eq_optionNone_of_toRaw_optionNone_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {elementType : Ty level scope}
    (typeEq : ty = Ty.option elementType)
    (rawEq : Term.toRaw witness = RawTerm.optionNone) :
    HEq witness
      (@Term.optionNone mode level scope ctx elementType) := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => cases typeEq
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
  | optionNone => cases typeEq; rfl
  | optionSome value =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | optionMatch scrutinee noneBranch someBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherInl value => cases typeEq
  | eitherInr value => cases typeEq
  | eitherMatch scrutinee leftBranch rightBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | refl rawTerm => cases typeEq
  | idJ baseCase witness =>
      simp only [Term.toRaw] at rawEq; cases rawEq

/-- Specialization at the right type. -/
theorem Term.eq_optionNone_of_toRaw_optionNone
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    (witness : Term ctx (Ty.option elementType))
    (rawEq : Term.toRaw witness = RawTerm.optionNone) :
    witness = Term.optionNone :=
  eq_of_heq
    (Term.eq_optionNone_of_toRaw_optionNone_general witness rfl rawEq)

/-- Generalized eq_optionSome. -/
theorem Term.eq_optionSome_of_toRaw_optionSome_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {elementType : Ty level scope}
    (typeEq : ty = Ty.option elementType)
    {rawValue : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.optionSome rawValue) :
    HEq witness
      (@Term.optionSome mode level scope ctx elementType
        (Term.value_of_optionSome_general witness typeEq rawEq)) := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => cases typeEq
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
  | optionSome value => cases typeEq; rfl
  | optionMatch scrutinee noneBranch someBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherInl value => cases typeEq
  | eitherInr value => cases typeEq
  | eitherMatch scrutinee leftBranch rightBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | refl rawTerm => cases typeEq
  | idJ baseCase witness =>
      simp only [Term.toRaw] at rawEq; cases rawEq

theorem Term.eq_optionSome_of_toRaw_optionSome
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {elementType : Ty level scope}
    (witness : Term ctx (Ty.option elementType))
    {rawValue : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.optionSome rawValue) :
    witness = Term.optionSome
        (Term.value_of_optionSome_general witness rfl rawEq) :=
  eq_of_heq
    (Term.eq_optionSome_of_toRaw_optionSome_general witness rfl rawEq)

/-- Generalized eq_eitherInl. -/
theorem Term.eq_eitherInl_of_toRaw_eitherInl_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {leftType rightType : Ty level scope}
    (typeEq : ty = Ty.either leftType rightType)
    {rawValue : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.eitherInl rawValue) :
    HEq witness
      (@Term.eitherInl mode level scope ctx leftType rightType
        (Term.value_of_eitherInl_general witness typeEq rawEq)) := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => cases typeEq
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
  | eitherInl value => cases typeEq; rfl
  | eitherInr value =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherMatch scrutinee leftBranch rightBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | refl rawTerm => cases typeEq
  | idJ baseCase witness =>
      simp only [Term.toRaw] at rawEq; cases rawEq

theorem Term.eq_eitherInl_of_toRaw_eitherInl
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    (witness : Term ctx (Ty.either leftType rightType))
    {rawValue : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.eitherInl rawValue) :
    witness = Term.eitherInl
        (Term.value_of_eitherInl_general witness rfl rawEq) :=
  eq_of_heq
    (Term.eq_eitherInl_of_toRaw_eitherInl_general witness rfl rawEq)

/-- Generalized eq_eitherInr. -/
theorem Term.eq_eitherInr_of_toRaw_eitherInr_general
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {ty : Ty level scope}
    (witness : Term ctx ty)
    {leftType rightType : Ty level scope}
    (typeEq : ty = Ty.either leftType rightType)
    {rawValue : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.eitherInr rawValue) :
    HEq witness
      (@Term.eitherInr mode level scope ctx leftType rightType
        (Term.value_of_eitherInr_general witness typeEq rawEq)) := by
  cases witness with
  | var pos => simp only [Term.toRaw] at rawEq; cases rawEq
  | unit => cases typeEq
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
  | eitherInl value =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | eitherInr value => cases typeEq; rfl
  | eitherMatch scrutinee leftBranch rightBranch =>
      simp only [Term.toRaw] at rawEq; cases rawEq
  | refl rawTerm => cases typeEq
  | idJ baseCase witness =>
      simp only [Term.toRaw] at rawEq; cases rawEq

theorem Term.eq_eitherInr_of_toRaw_eitherInr
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    (witness : Term ctx (Ty.either leftType rightType))
    {rawValue : RawTerm scope}
    (rawEq : Term.toRaw witness = RawTerm.eitherInr rawValue) :
    witness = Term.eitherInr
        (Term.value_of_eitherInr_general witness rfl rawEq) :=
  eq_of_heq
    (Term.eq_eitherInr_of_toRaw_eitherInr_general witness rfl rawEq)

end LeanFX.Syntax

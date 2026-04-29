import LeanFX.Syntax.TermSubst

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Term.toRaw` — the intrinsic-to-raw bridge.

Every well-typed intrinsic `Term context T` has a corresponding raw
`RawTerm scope` obtained by erasing all Ty-level annotations.  This
bridge witnesses that the intrinsic kernel embeds into the raw
syntax — half of the v2.2 architectural commitment that intrinsic
discipline and Term-mentioning identity types coexist in one kernel.

## Erasure correspondence

Each intrinsic constructor maps to the corresponding raw constructor:

  * `var`/`unit`/`bool*`/`nat*`/`list*`/`option*`/`either*` —
    structural, no annotations to erase.
  * `lam`/`lamPi` both collapse to `RawTerm.lam` (Curry-style; no
    domain annotation in the raw syntax).
  * `app`/`appPi` both collapse to `RawTerm.app`.
  * `pair`/`fst`/`snd` — direct.
  * `boolElim`/`natElim`/`natRec`/`listElim`/`optionMatch`/
    `eitherMatch` — direct (the result-type annotation is erased).
  * `refl rawTerm` — the rawTerm endpoint is closed (`RawTerm 0`),
    embedded into the context's scope via `RawTerm.weakenToScope`.

Subterms recurse with the appropriate scope: lam-bodies recurse at
`scope + 1`, all others at the same `scope`. -/
def Term.toRaw {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
    {T : Ty level scope} → Term context T → RawTerm scope
  | _, .var position    => RawTerm.var position
  | _, .unit            => RawTerm.unit
  | _, .lam body        => RawTerm.lam body.toRaw
  | _, .app function argument =>
      RawTerm.app function.toRaw argument.toRaw
  | _, .lamPi body      => RawTerm.lam body.toRaw
  | _, .appPi function argument =>
      RawTerm.app function.toRaw argument.toRaw
  | _, .pair firstVal secondVal =>
      RawTerm.pair firstVal.toRaw secondVal.toRaw
  | _, .fst pairTerm    => RawTerm.fst pairTerm.toRaw
  | _, .snd pairTerm    => RawTerm.snd pairTerm.toRaw
  | _, .boolTrue        => RawTerm.boolTrue
  | _, .boolFalse       => RawTerm.boolFalse
  | _, .boolElim scrutinee thenBranch elseBranch =>
      RawTerm.boolElim scrutinee.toRaw thenBranch.toRaw elseBranch.toRaw
  | _, .natZero         => RawTerm.natZero
  | _, .natSucc predecessor => RawTerm.natSucc predecessor.toRaw
  | _, .natElim scrutinee zeroBranch succBranch =>
      RawTerm.natElim scrutinee.toRaw zeroBranch.toRaw succBranch.toRaw
  | _, .natRec scrutinee zeroBranch succBranch =>
      RawTerm.natRec scrutinee.toRaw zeroBranch.toRaw succBranch.toRaw
  | _, .listNil         => RawTerm.listNil
  | _, .listCons head tail =>
      RawTerm.listCons head.toRaw tail.toRaw
  | _, .listElim scrutinee nilBranch consBranch =>
      RawTerm.listElim scrutinee.toRaw nilBranch.toRaw consBranch.toRaw
  | _, .optionNone      => RawTerm.optionNone
  | _, .optionSome value => RawTerm.optionSome value.toRaw
  | _, .optionMatch scrutinee noneBranch someBranch =>
      RawTerm.optionMatch scrutinee.toRaw noneBranch.toRaw someBranch.toRaw
  | _, .eitherInl value  => RawTerm.eitherInl value.toRaw
  | _, .eitherInr value  => RawTerm.eitherInr value.toRaw
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      RawTerm.eitherMatch scrutinee.toRaw leftBranch.toRaw rightBranch.toRaw
  | _, .refl rawTerm     =>
      RawTerm.refl (RawTerm.weakenToScope scope rawTerm)
  | _, .idJ baseCase witness =>
      RawTerm.idJ baseCase.toRaw witness.toRaw

end LeanFX.Syntax

import LeanFX.Syntax.RawSubst

namespace LeanFX.Syntax

/-! ## Raw-level complete development.

`RawTerm.cd` mirrors typed `Term.cd` (β/ι contraction on developed
shape) but at the type-erased raw level.  Because raw terms have no
type indices, this version is significantly simpler:

  * No Ty casts in the β-application case (raw substitution returns
    the same scope without type-level adjustment).
  * No `cd_idJ_redex` helper — the iotaIdJ contraction can be
    expressed as a plain `match` on the developed witness's raw
    shape, since at the raw level both endpoints of an Id type
    erase to the same `RawTerm.refl rt` shape regardless of
    intrinsic typing constraints.
  * No collapsing of lam/lamPi (already collapsed in raw syntax).

The bridge `Term.toRaw (Term.cd t) = RawTerm.cd (Term.toRaw t)`
follows by structural induction on `Term`. -/

def RawTerm.cd : {scope : Nat} → RawTerm scope → RawTerm scope
  | _, .var position => RawTerm.var position
  | _, .unit => RawTerm.unit
  | _, .lam body => RawTerm.lam (RawTerm.cd body)
  | _, .app function argument =>
      let developedFunction := RawTerm.cd function
      let developedArgument := RawTerm.cd argument
      match developedFunction with
      | RawTerm.lam body => body.subst0 developedArgument
      | _ => RawTerm.app developedFunction developedArgument
  | _, .pair firstVal secondVal =>
      RawTerm.pair (RawTerm.cd firstVal) (RawTerm.cd secondVal)
  | _, .fst pairTerm =>
      let developedPair := RawTerm.cd pairTerm
      match developedPair with
      | RawTerm.pair firstVal _ => firstVal
      | _ => RawTerm.fst developedPair
  | _, .snd pairTerm =>
      let developedPair := RawTerm.cd pairTerm
      match developedPair with
      | RawTerm.pair _ secondVal => secondVal
      | _ => RawTerm.snd developedPair
  | _, .boolTrue => RawTerm.boolTrue
  | _, .boolFalse => RawTerm.boolFalse
  | _, .boolElim scrutinee thenBranch elseBranch =>
      let developedScrutinee := RawTerm.cd scrutinee
      let developedThen := RawTerm.cd thenBranch
      let developedElse := RawTerm.cd elseBranch
      match developedScrutinee with
      | RawTerm.boolTrue => developedThen
      | RawTerm.boolFalse => developedElse
      | _ =>
          RawTerm.boolElim developedScrutinee developedThen developedElse
  | _, .natZero => RawTerm.natZero
  | _, .natSucc predecessor => RawTerm.natSucc (RawTerm.cd predecessor)
  | _, .natElim scrutinee zeroBranch succBranch =>
      let developedScrutinee := RawTerm.cd scrutinee
      let developedZero := RawTerm.cd zeroBranch
      let developedSucc := RawTerm.cd succBranch
      match developedScrutinee with
      | RawTerm.natZero => developedZero
      | RawTerm.natSucc predecessor =>
          RawTerm.app developedSucc predecessor
      | _ =>
          RawTerm.natElim developedScrutinee developedZero developedSucc
  | _, .natRec scrutinee zeroBranch succBranch =>
      let developedScrutinee := RawTerm.cd scrutinee
      let developedZero := RawTerm.cd zeroBranch
      let developedSucc := RawTerm.cd succBranch
      match developedScrutinee with
      | RawTerm.natZero => developedZero
      | RawTerm.natSucc predecessor =>
          RawTerm.app (RawTerm.app developedSucc predecessor)
            (RawTerm.natRec predecessor developedZero developedSucc)
      | _ =>
          RawTerm.natRec developedScrutinee developedZero developedSucc
  | _, .listNil => RawTerm.listNil
  | _, .listCons head tail =>
      RawTerm.listCons (RawTerm.cd head) (RawTerm.cd tail)
  | _, .listElim scrutinee nilBranch consBranch =>
      let developedScrutinee := RawTerm.cd scrutinee
      let developedNil := RawTerm.cd nilBranch
      let developedCons := RawTerm.cd consBranch
      match developedScrutinee with
      | RawTerm.listNil => developedNil
      | RawTerm.listCons head tail =>
          RawTerm.app (RawTerm.app developedCons head) tail
      | _ =>
          RawTerm.listElim developedScrutinee developedNil developedCons
  | _, .optionNone => RawTerm.optionNone
  | _, .optionSome value => RawTerm.optionSome (RawTerm.cd value)
  | _, .optionMatch scrutinee noneBranch someBranch =>
      let developedScrutinee := RawTerm.cd scrutinee
      let developedNone := RawTerm.cd noneBranch
      let developedSome := RawTerm.cd someBranch
      match developedScrutinee with
      | RawTerm.optionNone => developedNone
      | RawTerm.optionSome value =>
          RawTerm.app developedSome value
      | _ =>
          RawTerm.optionMatch developedScrutinee developedNone developedSome
  | _, .eitherInl value => RawTerm.eitherInl (RawTerm.cd value)
  | _, .eitherInr value => RawTerm.eitherInr (RawTerm.cd value)
  | _, .eitherMatch scrutinee leftBranch rightBranch =>
      let developedScrutinee := RawTerm.cd scrutinee
      let developedLeft := RawTerm.cd leftBranch
      let developedRight := RawTerm.cd rightBranch
      match developedScrutinee with
      | RawTerm.eitherInl value => RawTerm.app developedLeft value
      | RawTerm.eitherInr value => RawTerm.app developedRight value
      | _ =>
          RawTerm.eitherMatch developedScrutinee developedLeft developedRight
  | _, .refl rawTerm => RawTerm.refl (RawTerm.cd rawTerm)
  | _, .idJ baseCase witness =>
      let developedBase := RawTerm.cd baseCase
      let developedWitness := RawTerm.cd witness
      match developedWitness with
      | RawTerm.refl _ => developedBase
      | _ => RawTerm.idJ developedBase developedWitness

end LeanFX.Syntax

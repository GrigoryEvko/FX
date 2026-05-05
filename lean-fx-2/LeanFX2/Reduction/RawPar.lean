import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.RawSubst

/-! # Reduction/RawPar — raw-side parallel reduction.

The untyped counterpart of `Step.par`.  Operates on `RawTerm`
directly with single-Nat-indexed signature — pattern matching and
inversion are mechanical because there are no dep-typed
constructors.

Used by:
* `Bridge.lean` — `Step.par.toRawBridge : Step.par sourceTerm targetTerm
  → RawStep.par sourceRaw targetRaw` (forward direction)
* Future raw-side confluence as a sanity check against typed
* Decidability of conversion (Layer 9) when running on raw side

## Why a separate raw layer

Typed `Step.par`'s β/ι constructors carry conclusion types involving
Term values of dep-typed shape (`Term.subst0 body argument`,
`Term.pair`, etc.).  At the raw level there's no such typing so the
inversion principle for `RawStep.par (RawTerm.lam body) target`
gives a clean case split.  This makes raw the cleaner setting for
prototyping confluence proofs and bridging back to typed.

## Constructors

Mirrors `Step.par` at the raw layer: core MLTT congruence, shallow
β/ι, deep β/ι, D1.6 cubical/HOTT/modal congruence, and incremental
D2.5 cubical β for path application and Glue elimination.  η
deliberately omitted.

## modIntro / modElim / subsume

Lean-fx-2's RawTerm includes the three modal ctors from day 1
(per architectural commitment).  RawStep.par adds cong rules for
each.
-/

namespace LeanFX2

/-- Untyped parallel reduction.  Single-Nat-indexed scope; no
typing.  Pattern matching is mechanical. -/
inductive RawStep.par : ∀ {scope : Nat}, RawTerm scope → RawTerm scope → Prop
  /-- Reflexivity: zero parallel reductions. -/
  | refl {scope : Nat} (rawTerm : RawTerm scope) :
      RawStep.par rawTerm rawTerm
  /-- Cong: lam reduces in body. -/
  | lam {scope : Nat} {bodyRawSource bodyRawTarget : RawTerm (scope + 1)} :
      RawStep.par bodyRawSource bodyRawTarget →
      RawStep.par (RawTerm.lam bodyRawSource) (RawTerm.lam bodyRawTarget)
  /-- Cong: app reduces in both positions. -/
  | app {scope : Nat}
      {functionRawSource functionRawTarget
       argumentRawSource argumentRawTarget : RawTerm scope} :
      RawStep.par functionRawSource functionRawTarget →
      RawStep.par argumentRawSource argumentRawTarget →
      RawStep.par (RawTerm.app functionRawSource argumentRawSource)
                  (RawTerm.app functionRawTarget argumentRawTarget)
  /-- Cong: pair reduces in both components. -/
  | pair {scope : Nat}
      {firstRawSource firstRawTarget
       secondRawSource secondRawTarget : RawTerm scope} :
      RawStep.par firstRawSource firstRawTarget →
      RawStep.par secondRawSource secondRawTarget →
      RawStep.par (RawTerm.pair firstRawSource secondRawSource)
                  (RawTerm.pair firstRawTarget secondRawTarget)
  /-- Cong: fst reduces in argument. -/
  | fst {scope : Nat} {pairRawSource pairRawTarget : RawTerm scope} :
      RawStep.par pairRawSource pairRawTarget →
      RawStep.par (RawTerm.fst pairRawSource) (RawTerm.fst pairRawTarget)
  /-- Cong: snd reduces in argument. -/
  | snd {scope : Nat} {pairRawSource pairRawTarget : RawTerm scope} :
      RawStep.par pairRawSource pairRawTarget →
      RawStep.par (RawTerm.snd pairRawSource) (RawTerm.snd pairRawTarget)
  /-- Cong: boolElim reduces in all three positions. -/
  | boolElim {scope : Nat}
      {scrutineeRawSource scrutineeRawTarget
       thenRawSource thenRawTarget
       elseRawSource elseRawTarget : RawTerm scope} :
      RawStep.par scrutineeRawSource scrutineeRawTarget →
      RawStep.par thenRawSource thenRawTarget →
      RawStep.par elseRawSource elseRawTarget →
      RawStep.par (RawTerm.boolElim scrutineeRawSource thenRawSource elseRawSource)
                  (RawTerm.boolElim scrutineeRawTarget thenRawTarget elseRawTarget)
  /-- Cong: natSucc reduces in predecessor. -/
  | natSucc {scope : Nat}
      {predecessorRawSource predecessorRawTarget : RawTerm scope} :
      RawStep.par predecessorRawSource predecessorRawTarget →
      RawStep.par (RawTerm.natSucc predecessorRawSource)
                  (RawTerm.natSucc predecessorRawTarget)
  /-- Cong: natElim reduces in all three positions. -/
  | natElim {scope : Nat}
      {scrutineeRawSource scrutineeRawTarget
       zeroRawSource zeroRawTarget
       succRawSource succRawTarget : RawTerm scope} :
      RawStep.par scrutineeRawSource scrutineeRawTarget →
      RawStep.par zeroRawSource zeroRawTarget →
      RawStep.par succRawSource succRawTarget →
      RawStep.par (RawTerm.natElim scrutineeRawSource zeroRawSource succRawSource)
                  (RawTerm.natElim scrutineeRawTarget zeroRawTarget succRawTarget)
  /-- Cong: natRec reduces in all three positions. -/
  | natRec {scope : Nat}
      {scrutineeRawSource scrutineeRawTarget
       zeroRawSource zeroRawTarget
       succRawSource succRawTarget : RawTerm scope} :
      RawStep.par scrutineeRawSource scrutineeRawTarget →
      RawStep.par zeroRawSource zeroRawTarget →
      RawStep.par succRawSource succRawTarget →
      RawStep.par (RawTerm.natRec scrutineeRawSource zeroRawSource succRawSource)
                  (RawTerm.natRec scrutineeRawTarget zeroRawTarget succRawTarget)
  /-- Cong: listCons reduces in head and tail. -/
  | listCons {scope : Nat}
      {headRawSource headRawTarget
       tailRawSource tailRawTarget : RawTerm scope} :
      RawStep.par headRawSource headRawTarget →
      RawStep.par tailRawSource tailRawTarget →
      RawStep.par (RawTerm.listCons headRawSource tailRawSource)
                  (RawTerm.listCons headRawTarget tailRawTarget)
  /-- Cong: listElim reduces in all three positions. -/
  | listElim {scope : Nat}
      {scrutineeRawSource scrutineeRawTarget
       nilRawSource nilRawTarget
       consRawSource consRawTarget : RawTerm scope} :
      RawStep.par scrutineeRawSource scrutineeRawTarget →
      RawStep.par nilRawSource nilRawTarget →
      RawStep.par consRawSource consRawTarget →
      RawStep.par (RawTerm.listElim scrutineeRawSource nilRawSource consRawSource)
                  (RawTerm.listElim scrutineeRawTarget nilRawTarget consRawTarget)
  /-- Cong: optionSome reduces in value. -/
  | optionSome {scope : Nat}
      {valueRawSource valueRawTarget : RawTerm scope} :
      RawStep.par valueRawSource valueRawTarget →
      RawStep.par (RawTerm.optionSome valueRawSource)
                  (RawTerm.optionSome valueRawTarget)
  /-- Cong: optionMatch reduces in all three positions. -/
  | optionMatch {scope : Nat}
      {scrutineeRawSource scrutineeRawTarget
       noneRawSource noneRawTarget
       someRawSource someRawTarget : RawTerm scope} :
      RawStep.par scrutineeRawSource scrutineeRawTarget →
      RawStep.par noneRawSource noneRawTarget →
      RawStep.par someRawSource someRawTarget →
      RawStep.par
        (RawTerm.optionMatch scrutineeRawSource noneRawSource someRawSource)
        (RawTerm.optionMatch scrutineeRawTarget noneRawTarget someRawTarget)
  /-- Cong: eitherInl reduces in value. -/
  | eitherInl {scope : Nat}
      {valueRawSource valueRawTarget : RawTerm scope} :
      RawStep.par valueRawSource valueRawTarget →
      RawStep.par (RawTerm.eitherInl valueRawSource)
                  (RawTerm.eitherInl valueRawTarget)
  /-- Cong: eitherInr reduces in value. -/
  | eitherInr {scope : Nat}
      {valueRawSource valueRawTarget : RawTerm scope} :
      RawStep.par valueRawSource valueRawTarget →
      RawStep.par (RawTerm.eitherInr valueRawSource)
                  (RawTerm.eitherInr valueRawTarget)
  /-- Cong: eitherMatch reduces in all three positions. -/
  | eitherMatch {scope : Nat}
      {scrutineeRawSource scrutineeRawTarget
       leftRawSource leftRawTarget
       rightRawSource rightRawTarget : RawTerm scope} :
      RawStep.par scrutineeRawSource scrutineeRawTarget →
      RawStep.par leftRawSource leftRawTarget →
      RawStep.par rightRawSource rightRawTarget →
      RawStep.par
        (RawTerm.eitherMatch scrutineeRawSource leftRawSource rightRawSource)
        (RawTerm.eitherMatch scrutineeRawTarget leftRawTarget rightRawTarget)
  /-- Cong: refl reduces in its rawWitness argument.  Unlike typed
  Term.refl (frozen open-endpoint data), RawTerm.refl carries a
  RawTerm payload that substitution propagates into; this cong
  handles that. -/
  | reflCong {scope : Nat}
      {witnessRawSource witnessRawTarget : RawTerm scope} :
      RawStep.par witnessRawSource witnessRawTarget →
      RawStep.par (RawTerm.refl witnessRawSource)
                  (RawTerm.refl witnessRawTarget)
  /-- Cong: idJ reduces in baseCase and witness. -/
  | idJ {scope : Nat}
      {baseRawSource baseRawTarget
       witnessRawSource witnessRawTarget : RawTerm scope} :
      RawStep.par baseRawSource baseRawTarget →
      RawStep.par witnessRawSource witnessRawTarget →
      RawStep.par (RawTerm.idJ baseRawSource witnessRawSource)
                  (RawTerm.idJ baseRawTarget witnessRawTarget)
  /-- Cong: modIntro reduces in inner. -/
  | modIntro {scope : Nat}
      {innerRawSource innerRawTarget : RawTerm scope} :
      RawStep.par innerRawSource innerRawTarget →
      RawStep.par (RawTerm.modIntro innerRawSource)
                  (RawTerm.modIntro innerRawTarget)
  /-- Cong: modElim reduces in inner. -/
  | modElim {scope : Nat}
      {innerRawSource innerRawTarget : RawTerm scope} :
      RawStep.par innerRawSource innerRawTarget →
      RawStep.par (RawTerm.modElim innerRawSource)
                  (RawTerm.modElim innerRawTarget)
  /-- Cong: subsume reduces in inner. -/
  | subsume {scope : Nat}
      {innerRawSource innerRawTarget : RawTerm scope} :
      RawStep.par innerRawSource innerRawTarget →
      RawStep.par (RawTerm.subsume innerRawSource)
                  (RawTerm.subsume innerRawTarget)
  /-- Shallow β: `(λ. body) arg ⟶ body[arg/x]` with parallel in body+arg. -/
  | betaApp {scope : Nat}
      {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
      {argumentRawSource argumentRawTarget : RawTerm scope} :
      RawStep.par bodyRawSource bodyRawTarget →
      RawStep.par argumentRawSource argumentRawTarget →
      RawStep.par (RawTerm.app (RawTerm.lam bodyRawSource) argumentRawSource)
                  (bodyRawTarget.subst0 argumentRawTarget)
  /-- Shallow β-fst: `fst (pair a b) ⟶ a'`. -/
  | betaFstPair {scope : Nat}
      {firstRawSource firstRawTarget : RawTerm scope}
      (secondRaw : RawTerm scope) :
      RawStep.par firstRawSource firstRawTarget →
      RawStep.par (RawTerm.fst (RawTerm.pair firstRawSource secondRaw))
                  firstRawTarget
  /-- Shallow β-snd: `snd (pair a b) ⟶ b'`. -/
  | betaSndPair {scope : Nat}
      (firstRaw : RawTerm scope)
      {secondRawSource secondRawTarget : RawTerm scope} :
      RawStep.par secondRawSource secondRawTarget →
      RawStep.par (RawTerm.snd (RawTerm.pair firstRaw secondRawSource))
                  secondRawTarget
  /-- Shallow ι: `boolElim true t e ⟶ t'`. -/
  | iotaBoolElimTrue {scope : Nat}
      {thenRawSource thenRawTarget : RawTerm scope}
      (elseRaw : RawTerm scope) :
      RawStep.par thenRawSource thenRawTarget →
      RawStep.par
        (RawTerm.boolElim RawTerm.boolTrue thenRawSource elseRaw)
        thenRawTarget
  /-- Shallow ι: `boolElim false t e ⟶ e'`. -/
  | iotaBoolElimFalse {scope : Nat}
      (thenRaw : RawTerm scope)
      {elseRawSource elseRawTarget : RawTerm scope} :
      RawStep.par elseRawSource elseRawTarget →
      RawStep.par
        (RawTerm.boolElim RawTerm.boolFalse thenRaw elseRawSource)
        elseRawTarget
  /-- Shallow ι: `natElim 0 z s ⟶ z'`. -/
  | iotaNatElimZero {scope : Nat}
      {zeroRawSource zeroRawTarget : RawTerm scope}
      (succRaw : RawTerm scope) :
      RawStep.par zeroRawSource zeroRawTarget →
      RawStep.par
        (RawTerm.natElim RawTerm.natZero zeroRawSource succRaw)
        zeroRawTarget
  /-- Shallow ι: `natElim (succ n) z s ⟶ s' n'`. -/
  | iotaNatElimSucc {scope : Nat}
      (zeroRaw : RawTerm scope)
      {predecessorRawSource predecessorRawTarget : RawTerm scope}
      {succRawSource succRawTarget : RawTerm scope} :
      RawStep.par predecessorRawSource predecessorRawTarget →
      RawStep.par succRawSource succRawTarget →
      RawStep.par
        (RawTerm.natElim (RawTerm.natSucc predecessorRawSource)
                          zeroRaw succRawSource)
        (RawTerm.app succRawTarget predecessorRawTarget)
  /-- Shallow ι: `natRec 0 z s ⟶ z'`. -/
  | iotaNatRecZero {scope : Nat}
      {zeroRawSource zeroRawTarget : RawTerm scope}
      (succRaw : RawTerm scope) :
      RawStep.par zeroRawSource zeroRawTarget →
      RawStep.par
        (RawTerm.natRec RawTerm.natZero zeroRawSource succRaw)
        zeroRawTarget
  /-- Shallow ι: `natRec (succ n) z s ⟶ s' n' (natRec n' z' s')`. -/
  | iotaNatRecSucc {scope : Nat}
      {predecessorRawSource predecessorRawTarget
       zeroRawSource zeroRawTarget
       succRawSource succRawTarget : RawTerm scope} :
      RawStep.par predecessorRawSource predecessorRawTarget →
      RawStep.par zeroRawSource zeroRawTarget →
      RawStep.par succRawSource succRawTarget →
      RawStep.par
        (RawTerm.natRec (RawTerm.natSucc predecessorRawSource)
                         zeroRawSource succRawSource)
        (RawTerm.app (RawTerm.app succRawTarget predecessorRawTarget)
                     (RawTerm.natRec predecessorRawTarget
                                      zeroRawTarget succRawTarget))
  /-- Shallow ι: `listElim [] n c ⟶ n'`. -/
  | iotaListElimNil {scope : Nat}
      {nilRawSource nilRawTarget : RawTerm scope}
      (consRaw : RawTerm scope) :
      RawStep.par nilRawSource nilRawTarget →
      RawStep.par
        (RawTerm.listElim RawTerm.listNil nilRawSource consRaw)
        nilRawTarget
  /-- Shallow ι: `listElim (cons h t) n c ⟶ c' h' t'`. -/
  | iotaListElimCons {scope : Nat}
      (nilRaw : RawTerm scope)
      {headRawSource headRawTarget
       tailRawSource tailRawTarget
       consRawSource consRawTarget : RawTerm scope} :
      RawStep.par headRawSource headRawTarget →
      RawStep.par tailRawSource tailRawTarget →
      RawStep.par consRawSource consRawTarget →
      RawStep.par
        (RawTerm.listElim (RawTerm.listCons headRawSource tailRawSource)
                           nilRaw consRawSource)
        (RawTerm.app (RawTerm.app consRawTarget headRawTarget) tailRawTarget)
  /-- Shallow ι: `optionMatch none n s ⟶ n'`. -/
  | iotaOptionMatchNone {scope : Nat}
      {noneRawSource noneRawTarget : RawTerm scope}
      (someRaw : RawTerm scope) :
      RawStep.par noneRawSource noneRawTarget →
      RawStep.par
        (RawTerm.optionMatch RawTerm.optionNone noneRawSource someRaw)
        noneRawTarget
  /-- Shallow ι: `optionMatch (some v) n s ⟶ s' v'`. -/
  | iotaOptionMatchSome {scope : Nat}
      (noneRaw : RawTerm scope)
      {valueRawSource valueRawTarget
       someRawSource someRawTarget : RawTerm scope} :
      RawStep.par valueRawSource valueRawTarget →
      RawStep.par someRawSource someRawTarget →
      RawStep.par
        (RawTerm.optionMatch (RawTerm.optionSome valueRawSource)
                              noneRaw someRawSource)
        (RawTerm.app someRawTarget valueRawTarget)
  /-- Shallow ι: `eitherMatch (inl v) lb rb ⟶ lb' v'`. -/
  | iotaEitherMatchInl {scope : Nat}
      {valueRawSource valueRawTarget
       leftRawSource leftRawTarget : RawTerm scope}
      (rightRaw : RawTerm scope) :
      RawStep.par valueRawSource valueRawTarget →
      RawStep.par leftRawSource leftRawTarget →
      RawStep.par
        (RawTerm.eitherMatch (RawTerm.eitherInl valueRawSource)
                              leftRawSource rightRaw)
        (RawTerm.app leftRawTarget valueRawTarget)
  /-- Shallow ι: `eitherMatch (inr v) lb rb ⟶ rb' v'`. -/
  | iotaEitherMatchInr {scope : Nat}
      (leftRaw : RawTerm scope)
      {valueRawSource valueRawTarget
       rightRawSource rightRawTarget : RawTerm scope} :
      RawStep.par valueRawSource valueRawTarget →
      RawStep.par rightRawSource rightRawTarget →
      RawStep.par
        (RawTerm.eitherMatch (RawTerm.eitherInr valueRawSource)
                              leftRaw rightRawSource)
        (RawTerm.app rightRawTarget valueRawTarget)
  /-- Shallow ι: `idJ base (refl rt) ⟶ base'`. -/
  | iotaIdJRefl {scope : Nat}
      {baseRawSource baseRawTarget : RawTerm scope}
      (witnessRaw : RawTerm scope) :
      RawStep.par baseRawSource baseRawTarget →
      RawStep.par
        (RawTerm.idJ baseRawSource (RawTerm.refl witnessRaw))
        baseRawTarget
  /-- Deep β: `function ⟶ λ. body` then app fires. -/
  | betaAppDeep {scope : Nat}
      {functionRawSource : RawTerm scope}
      {bodyRawTarget : RawTerm (scope + 1)}
      {argumentRawSource argumentRawTarget : RawTerm scope} :
      RawStep.par functionRawSource (RawTerm.lam bodyRawTarget) →
      RawStep.par argumentRawSource argumentRawTarget →
      RawStep.par (RawTerm.app functionRawSource argumentRawSource)
                  (bodyRawTarget.subst0 argumentRawTarget)
  /-- Deep β: `pairTerm ⟶ pair fr sr` then fst fires. -/
  | betaFstPairDeep {scope : Nat}
      {pairRawSource firstRawTarget secondRawTarget : RawTerm scope} :
      RawStep.par pairRawSource (RawTerm.pair firstRawTarget secondRawTarget) →
      RawStep.par (RawTerm.fst pairRawSource) firstRawTarget
  /-- Deep β: `pairTerm ⟶ pair fr sr` then snd fires. -/
  | betaSndPairDeep {scope : Nat}
      {pairRawSource firstRawTarget secondRawTarget : RawTerm scope} :
      RawStep.par pairRawSource (RawTerm.pair firstRawTarget secondRawTarget) →
      RawStep.par (RawTerm.snd pairRawSource) secondRawTarget
  /-- Deep ι: `scrutinee ⟶ true` then boolElim fires. -/
  | iotaBoolElimTrueDeep {scope : Nat}
      {scrutineeRaw : RawTerm scope}
      {thenRawSource thenRawTarget : RawTerm scope}
      (elseRaw : RawTerm scope) :
      RawStep.par scrutineeRaw RawTerm.boolTrue →
      RawStep.par thenRawSource thenRawTarget →
      RawStep.par (RawTerm.boolElim scrutineeRaw thenRawSource elseRaw)
                  thenRawTarget
  /-- Deep ι: `scrutinee ⟶ false` then boolElim fires. -/
  | iotaBoolElimFalseDeep {scope : Nat}
      {scrutineeRaw : RawTerm scope}
      (thenRaw : RawTerm scope)
      {elseRawSource elseRawTarget : RawTerm scope} :
      RawStep.par scrutineeRaw RawTerm.boolFalse →
      RawStep.par elseRawSource elseRawTarget →
      RawStep.par (RawTerm.boolElim scrutineeRaw thenRaw elseRawSource)
                  elseRawTarget
  /-- Deep ι: `scrutinee ⟶ 0` then natElim fires. -/
  | iotaNatElimZeroDeep {scope : Nat}
      {scrutineeRaw : RawTerm scope}
      {zeroRawSource zeroRawTarget : RawTerm scope}
      (succRaw : RawTerm scope) :
      RawStep.par scrutineeRaw RawTerm.natZero →
      RawStep.par zeroRawSource zeroRawTarget →
      RawStep.par (RawTerm.natElim scrutineeRaw zeroRawSource succRaw)
                  zeroRawTarget
  /-- Deep ι: `scrutinee ⟶ succ n` then natElim fires. -/
  | iotaNatElimSuccDeep {scope : Nat}
      {scrutineeRaw : RawTerm scope}
      (zeroRaw : RawTerm scope)
      {predecessorRaw : RawTerm scope}
      {succRawSource succRawTarget : RawTerm scope} :
      RawStep.par scrutineeRaw (RawTerm.natSucc predecessorRaw) →
      RawStep.par succRawSource succRawTarget →
      RawStep.par (RawTerm.natElim scrutineeRaw zeroRaw succRawSource)
                  (RawTerm.app succRawTarget predecessorRaw)
  /-- Deep ι: `scrutinee ⟶ 0` then natRec fires. -/
  | iotaNatRecZeroDeep {scope : Nat}
      {scrutineeRaw : RawTerm scope}
      {zeroRawSource zeroRawTarget : RawTerm scope}
      (succRaw : RawTerm scope) :
      RawStep.par scrutineeRaw RawTerm.natZero →
      RawStep.par zeroRawSource zeroRawTarget →
      RawStep.par (RawTerm.natRec scrutineeRaw zeroRawSource succRaw)
                  zeroRawTarget
  /-- Deep ι: `scrutinee ⟶ succ n` then natRec fires. -/
  | iotaNatRecSuccDeep {scope : Nat}
      {scrutineeRaw : RawTerm scope}
      {predecessorRaw : RawTerm scope}
      {zeroRawSource zeroRawTarget : RawTerm scope}
      {succRawSource succRawTarget : RawTerm scope} :
      RawStep.par scrutineeRaw (RawTerm.natSucc predecessorRaw) →
      RawStep.par zeroRawSource zeroRawTarget →
      RawStep.par succRawSource succRawTarget →
      RawStep.par (RawTerm.natRec scrutineeRaw zeroRawSource succRawSource)
                  (RawTerm.app (RawTerm.app succRawTarget predecessorRaw)
                                (RawTerm.natRec predecessorRaw
                                                 zeroRawTarget succRawTarget))
  /-- Deep ι: `scrutinee ⟶ []` then listElim fires. -/
  | iotaListElimNilDeep {scope : Nat}
      {scrutineeRaw : RawTerm scope}
      {nilRawSource nilRawTarget : RawTerm scope}
      (consRaw : RawTerm scope) :
      RawStep.par scrutineeRaw RawTerm.listNil →
      RawStep.par nilRawSource nilRawTarget →
      RawStep.par (RawTerm.listElim scrutineeRaw nilRawSource consRaw)
                  nilRawTarget
  /-- Deep ι: `scrutinee ⟶ cons h t` then listElim fires. -/
  | iotaListElimConsDeep {scope : Nat}
      {scrutineeRaw : RawTerm scope}
      (nilRaw : RawTerm scope)
      {headRaw tailRaw : RawTerm scope}
      {consRawSource consRawTarget : RawTerm scope} :
      RawStep.par scrutineeRaw (RawTerm.listCons headRaw tailRaw) →
      RawStep.par consRawSource consRawTarget →
      RawStep.par (RawTerm.listElim scrutineeRaw nilRaw consRawSource)
                  (RawTerm.app (RawTerm.app consRawTarget headRaw) tailRaw)
  /-- Deep ι: `scrutinee ⟶ none` then optionMatch fires. -/
  | iotaOptionMatchNoneDeep {scope : Nat}
      {scrutineeRaw : RawTerm scope}
      {noneRawSource noneRawTarget : RawTerm scope}
      (someRaw : RawTerm scope) :
      RawStep.par scrutineeRaw RawTerm.optionNone →
      RawStep.par noneRawSource noneRawTarget →
      RawStep.par (RawTerm.optionMatch scrutineeRaw noneRawSource someRaw)
                  noneRawTarget
  /-- Deep ι: `scrutinee ⟶ some v` then optionMatch fires. -/
  | iotaOptionMatchSomeDeep {scope : Nat}
      {scrutineeRaw : RawTerm scope}
      (noneRaw : RawTerm scope)
      {valueRaw : RawTerm scope}
      {someRawSource someRawTarget : RawTerm scope} :
      RawStep.par scrutineeRaw (RawTerm.optionSome valueRaw) →
      RawStep.par someRawSource someRawTarget →
      RawStep.par (RawTerm.optionMatch scrutineeRaw noneRaw someRawSource)
                  (RawTerm.app someRawTarget valueRaw)
  /-- Deep ι: `scrutinee ⟶ inl v` then eitherMatch fires. -/
  | iotaEitherMatchInlDeep {scope : Nat}
      {scrutineeRaw : RawTerm scope}
      {valueRaw : RawTerm scope}
      {leftRawSource leftRawTarget : RawTerm scope}
      (rightRaw : RawTerm scope) :
      RawStep.par scrutineeRaw (RawTerm.eitherInl valueRaw) →
      RawStep.par leftRawSource leftRawTarget →
      RawStep.par (RawTerm.eitherMatch scrutineeRaw leftRawSource rightRaw)
                  (RawTerm.app leftRawTarget valueRaw)
  /-- Deep ι: `scrutinee ⟶ inr v` then eitherMatch fires. -/
  | iotaEitherMatchInrDeep {scope : Nat}
      {scrutineeRaw : RawTerm scope}
      (leftRaw : RawTerm scope)
      {valueRaw : RawTerm scope}
      {rightRawSource rightRawTarget : RawTerm scope} :
      RawStep.par scrutineeRaw (RawTerm.eitherInr valueRaw) →
      RawStep.par rightRawSource rightRawTarget →
      RawStep.par (RawTerm.eitherMatch scrutineeRaw leftRaw rightRawSource)
                  (RawTerm.app rightRawTarget valueRaw)
  /-- Deep ι: `witness ⟶ refl rt` then idJ fires. -/
  | iotaIdJReflDeep {scope : Nat}
      {witnessRawSource : RawTerm scope}
      {reflRawArgument : RawTerm scope}
      {baseRawSource baseRawTarget : RawTerm scope} :
      RawStep.par witnessRawSource (RawTerm.refl reflRawArgument) →
      RawStep.par baseRawSource baseRawTarget →
      RawStep.par (RawTerm.idJ baseRawSource witnessRawSource)
                  baseRawTarget
  -- D1.6 / D2.5–D2.7 extension layer: structural cong rules for
  -- the new RawTerm ctors, plus the D2.5 cubical β rule for
  -- pathApp/pathLam.  The remaining cubical / HOTT / refine /
  -- record / codata / session / effect / strict β/ι rules land
  -- incrementally with their cd/confluence cases.
  /-- Cong: intervalOpp reduces in argument. -/
  | intervalOppCong {scope : Nat}
      {intervalRawSource intervalRawTarget : RawTerm scope} :
      RawStep.par intervalRawSource intervalRawTarget →
      RawStep.par (RawTerm.intervalOpp intervalRawSource)
                  (RawTerm.intervalOpp intervalRawTarget)
  /-- Cong: intervalMeet reduces in both arguments. -/
  | intervalMeetCong {scope : Nat}
      {leftRawSource leftRawTarget rightRawSource rightRawTarget : RawTerm scope} :
      RawStep.par leftRawSource leftRawTarget →
      RawStep.par rightRawSource rightRawTarget →
      RawStep.par (RawTerm.intervalMeet leftRawSource rightRawSource)
                  (RawTerm.intervalMeet leftRawTarget rightRawTarget)
  /-- Cong: intervalJoin reduces in both arguments. -/
  | intervalJoinCong {scope : Nat}
      {leftRawSource leftRawTarget rightRawSource rightRawTarget : RawTerm scope} :
      RawStep.par leftRawSource leftRawTarget →
      RawStep.par rightRawSource rightRawTarget →
      RawStep.par (RawTerm.intervalJoin leftRawSource rightRawSource)
                  (RawTerm.intervalJoin leftRawTarget rightRawTarget)
  /-- Cong: pathLam reduces in body (under binder). -/
  | pathLamCong {scope : Nat}
      {bodyRawSource bodyRawTarget : RawTerm (scope + 1)} :
      RawStep.par bodyRawSource bodyRawTarget →
      RawStep.par (RawTerm.pathLam bodyRawSource)
                  (RawTerm.pathLam bodyRawTarget)
  /-- Cong: pathApp reduces in path and interval-arg. -/
  | pathAppCong {scope : Nat}
      {pathRawSource pathRawTarget intervalRawSource intervalRawTarget : RawTerm scope} :
      RawStep.par pathRawSource pathRawTarget →
      RawStep.par intervalRawSource intervalRawTarget →
      RawStep.par (RawTerm.pathApp pathRawSource intervalRawSource)
                  (RawTerm.pathApp pathRawTarget intervalRawTarget)
  /-- Cubical β: `(pathLam body) @ point ⟶ body[point/i]`. -/
  | betaPathApp {scope : Nat}
      {bodyRawSource bodyRawTarget : RawTerm (scope + 1)}
      {intervalRawSource intervalRawTarget : RawTerm scope} :
      RawStep.par bodyRawSource bodyRawTarget →
      RawStep.par intervalRawSource intervalRawTarget →
      RawStep.par
        (RawTerm.pathApp (RawTerm.pathLam bodyRawSource) intervalRawSource)
        (bodyRawTarget.subst0 intervalRawTarget)
  /-- Deep cubical β: `pathTerm ⟶ pathLam body` then pathApp fires. -/
  | betaPathAppDeep {scope : Nat}
      {pathRawSource : RawTerm scope}
      {bodyRawTarget : RawTerm (scope + 1)}
      {intervalRawSource intervalRawTarget : RawTerm scope} :
      RawStep.par pathRawSource (RawTerm.pathLam bodyRawTarget) →
      RawStep.par intervalRawSource intervalRawTarget →
      RawStep.par (RawTerm.pathApp pathRawSource intervalRawSource)
                  (bodyRawTarget.subst0 intervalRawTarget)
  /-- Cong: glueIntro reduces in base and partial values. -/
  | glueIntroCong {scope : Nat}
      {baseRawSource baseRawTarget partialRawSource partialRawTarget : RawTerm scope} :
      RawStep.par baseRawSource baseRawTarget →
      RawStep.par partialRawSource partialRawTarget →
      RawStep.par (RawTerm.glueIntro baseRawSource partialRawSource)
                  (RawTerm.glueIntro baseRawTarget partialRawTarget)
  /-- Cubical Glue β: `unglue (glue base partial) ⟶ base`. -/
  | betaGlueElimIntro {scope : Nat}
      {baseRawSource baseRawTarget partialRawSource partialRawTarget : RawTerm scope} :
      RawStep.par baseRawSource baseRawTarget →
      RawStep.par partialRawSource partialRawTarget →
      RawStep.par (RawTerm.glueElim
                    (RawTerm.glueIntro baseRawSource partialRawSource))
                  baseRawTarget
  /-- Deep cubical Glue β: glued value develops to a `glueIntro`. -/
  | betaGlueElimIntroDeep {scope : Nat}
      {gluedRawSource : RawTerm scope}
      {baseRawTarget partialRawTarget : RawTerm scope} :
      RawStep.par gluedRawSource
        (RawTerm.glueIntro baseRawTarget partialRawTarget) →
      RawStep.par (RawTerm.glueElim gluedRawSource) baseRawTarget
  /-- Cong: glueElim reduces in glued value. -/
  | glueElimCong {scope : Nat}
      {gluedRawSource gluedRawTarget : RawTerm scope} :
      RawStep.par gluedRawSource gluedRawTarget →
      RawStep.par (RawTerm.glueElim gluedRawSource)
                  (RawTerm.glueElim gluedRawTarget)
  /-- Cong: transp reduces in path and source. -/
  | transpCong {scope : Nat}
      {pathRawSource pathRawTarget sourceRawSource sourceRawTarget : RawTerm scope} :
      RawStep.par pathRawSource pathRawTarget →
      RawStep.par sourceRawSource sourceRawTarget →
      RawStep.par (RawTerm.transp pathRawSource sourceRawSource)
                  (RawTerm.transp pathRawTarget sourceRawTarget)
  /-- Cong: hcomp reduces in sides and cap. -/
  | hcompCong {scope : Nat}
      {sidesRawSource sidesRawTarget capRawSource capRawTarget : RawTerm scope} :
      RawStep.par sidesRawSource sidesRawTarget →
      RawStep.par capRawSource capRawTarget →
      RawStep.par (RawTerm.hcomp sidesRawSource capRawSource)
                  (RawTerm.hcomp sidesRawTarget capRawTarget)
  /-- Cong: oeqRefl reduces in witness. -/
  | oeqReflCong {scope : Nat}
      {witnessRawSource witnessRawTarget : RawTerm scope} :
      RawStep.par witnessRawSource witnessRawTarget →
      RawStep.par (RawTerm.oeqRefl witnessRawSource)
                  (RawTerm.oeqRefl witnessRawTarget)
  /-- Cong: oeqJ reduces in baseCase and witness. -/
  | oeqJCong {scope : Nat}
      {baseRawSource baseRawTarget witnessRawSource witnessRawTarget : RawTerm scope} :
      RawStep.par baseRawSource baseRawTarget →
      RawStep.par witnessRawSource witnessRawTarget →
      RawStep.par (RawTerm.oeqJ baseRawSource witnessRawSource)
                  (RawTerm.oeqJ baseRawTarget witnessRawTarget)
  /-- Cong: oeqFunext reduces in pointwiseEquality. -/
  | oeqFunextCong {scope : Nat}
      {pointwiseRawSource pointwiseRawTarget : RawTerm scope} :
      RawStep.par pointwiseRawSource pointwiseRawTarget →
      RawStep.par (RawTerm.oeqFunext pointwiseRawSource)
                  (RawTerm.oeqFunext pointwiseRawTarget)
  /-- Cong: idStrictRefl reduces in witness. -/
  | idStrictReflCong {scope : Nat}
      {witnessRawSource witnessRawTarget : RawTerm scope} :
      RawStep.par witnessRawSource witnessRawTarget →
      RawStep.par (RawTerm.idStrictRefl witnessRawSource)
                  (RawTerm.idStrictRefl witnessRawTarget)
  /-- Cong: idStrictRec reduces in baseCase and witness. -/
  | idStrictRecCong {scope : Nat}
      {baseRawSource baseRawTarget witnessRawSource witnessRawTarget : RawTerm scope} :
      RawStep.par baseRawSource baseRawTarget →
      RawStep.par witnessRawSource witnessRawTarget →
      RawStep.par (RawTerm.idStrictRec baseRawSource witnessRawSource)
                  (RawTerm.idStrictRec baseRawTarget witnessRawTarget)
  /-- Cong: equivIntro reduces in forward and backward functions. -/
  | equivIntroCong {scope : Nat}
      {forwardRawSource forwardRawTarget backwardRawSource backwardRawTarget : RawTerm scope} :
      RawStep.par forwardRawSource forwardRawTarget →
      RawStep.par backwardRawSource backwardRawTarget →
      RawStep.par (RawTerm.equivIntro forwardRawSource backwardRawSource)
                  (RawTerm.equivIntro forwardRawTarget backwardRawTarget)
  /-- Cong: equivApp reduces in equiv and argument. -/
  | equivAppCong {scope : Nat}
      {equivRawSource equivRawTarget argumentRawSource argumentRawTarget : RawTerm scope} :
      RawStep.par equivRawSource equivRawTarget →
      RawStep.par argumentRawSource argumentRawTarget →
      RawStep.par (RawTerm.equivApp equivRawSource argumentRawSource)
                  (RawTerm.equivApp equivRawTarget argumentRawTarget)
  /-- Cong: refineIntro reduces in value and predicate proof. -/
  | refineIntroCong {scope : Nat}
      {valueRawSource valueRawTarget proofRawSource proofRawTarget : RawTerm scope} :
      RawStep.par valueRawSource valueRawTarget →
      RawStep.par proofRawSource proofRawTarget →
      RawStep.par (RawTerm.refineIntro valueRawSource proofRawSource)
                  (RawTerm.refineIntro valueRawTarget proofRawTarget)
  /-- Cong: refineElim reduces in refined value. -/
  | refineElimCong {scope : Nat}
      {refinedRawSource refinedRawTarget : RawTerm scope} :
      RawStep.par refinedRawSource refinedRawTarget →
      RawStep.par (RawTerm.refineElim refinedRawSource)
                  (RawTerm.refineElim refinedRawTarget)
  /-- Cong: recordIntro reduces in first field. -/
  | recordIntroCong {scope : Nat}
      {firstRawSource firstRawTarget : RawTerm scope} :
      RawStep.par firstRawSource firstRawTarget →
      RawStep.par (RawTerm.recordIntro firstRawSource)
                  (RawTerm.recordIntro firstRawTarget)
  /-- Cong: recordProj reduces in record value. -/
  | recordProjCong {scope : Nat}
      {recordRawSource recordRawTarget : RawTerm scope} :
      RawStep.par recordRawSource recordRawTarget →
      RawStep.par (RawTerm.recordProj recordRawSource)
                  (RawTerm.recordProj recordRawTarget)
  /-- Cong: codataUnfold reduces in initial state and transition. -/
  | codataUnfoldCong {scope : Nat}
      {stateRawSource stateRawTarget transitionRawSource transitionRawTarget : RawTerm scope} :
      RawStep.par stateRawSource stateRawTarget →
      RawStep.par transitionRawSource transitionRawTarget →
      RawStep.par (RawTerm.codataUnfold stateRawSource transitionRawSource)
                  (RawTerm.codataUnfold stateRawTarget transitionRawTarget)
  /-- Cong: codataDest reduces in codata value. -/
  | codataDestCong {scope : Nat}
      {codataRawSource codataRawTarget : RawTerm scope} :
      RawStep.par codataRawSource codataRawTarget →
      RawStep.par (RawTerm.codataDest codataRawSource)
                  (RawTerm.codataDest codataRawTarget)
  /-- Cong: sessionSend reduces in channel and payload. -/
  | sessionSendCong {scope : Nat}
      {channelRawSource channelRawTarget payloadRawSource payloadRawTarget : RawTerm scope} :
      RawStep.par channelRawSource channelRawTarget →
      RawStep.par payloadRawSource payloadRawTarget →
      RawStep.par (RawTerm.sessionSend channelRawSource payloadRawSource)
                  (RawTerm.sessionSend channelRawTarget payloadRawTarget)
  /-- Cong: sessionRecv reduces in channel. -/
  | sessionRecvCong {scope : Nat}
      {channelRawSource channelRawTarget : RawTerm scope} :
      RawStep.par channelRawSource channelRawTarget →
      RawStep.par (RawTerm.sessionRecv channelRawSource)
                  (RawTerm.sessionRecv channelRawTarget)
  /-- Cong: effectPerform reduces in operation tag and arguments. -/
  | effectPerformCong {scope : Nat}
      {operationRawSource operationRawTarget argumentsRawSource argumentsRawTarget : RawTerm scope} :
      RawStep.par operationRawSource operationRawTarget →
      RawStep.par argumentsRawSource argumentsRawTarget →
      RawStep.par (RawTerm.effectPerform operationRawSource argumentsRawSource)
                  (RawTerm.effectPerform operationRawTarget argumentsRawTarget)
  -- CUMUL-2.1: Cong rules for per-shape type-code constructors.
  --
  -- Each new code ctor has a structural cong rule that says: if all
  -- subterms parallel-reduce, so does the wrapper.  Binder-shape codes
  -- (`piTyCode`, `sigmaTyCode`) take a parallel reduction at scope+1
  -- for the codomain — mirroring `lam`'s cong rule.
  --
  -- No β/ι rules exist for these codes — they are canonical type
  -- values that don't reduce at the head.  Reduction only happens
  -- inside their subterms via these cong rules.
  /-- Cong: arrowCode reduces in domain and codomain. -/
  | arrowCodeCong {scope : Nat}
      {domainSource domainTarget codomainSource codomainTarget : RawTerm scope} :
      RawStep.par domainSource domainTarget →
      RawStep.par codomainSource codomainTarget →
      RawStep.par (RawTerm.arrowCode domainSource codomainSource)
                  (RawTerm.arrowCode domainTarget codomainTarget)
  /-- Cong: piTyCode reduces in domain (scope) and codomain (scope+1). -/
  | piTyCodeCong {scope : Nat}
      {domainSource domainTarget : RawTerm scope}
      {codomainSource codomainTarget : RawTerm (scope + 1)} :
      RawStep.par domainSource domainTarget →
      RawStep.par codomainSource codomainTarget →
      RawStep.par (RawTerm.piTyCode domainSource codomainSource)
                  (RawTerm.piTyCode domainTarget codomainTarget)
  /-- Cong: sigmaTyCode reduces in domain (scope) and codomain (scope+1). -/
  | sigmaTyCodeCong {scope : Nat}
      {domainSource domainTarget : RawTerm scope}
      {codomainSource codomainTarget : RawTerm (scope + 1)} :
      RawStep.par domainSource domainTarget →
      RawStep.par codomainSource codomainTarget →
      RawStep.par (RawTerm.sigmaTyCode domainSource codomainSource)
                  (RawTerm.sigmaTyCode domainTarget codomainTarget)
  /-- Cong: productCode reduces in both subterms. -/
  | productCodeCong {scope : Nat}
      {firstSource firstTarget secondSource secondTarget : RawTerm scope} :
      RawStep.par firstSource firstTarget →
      RawStep.par secondSource secondTarget →
      RawStep.par (RawTerm.productCode firstSource secondSource)
                  (RawTerm.productCode firstTarget secondTarget)
  /-- Cong: sumCode reduces in both subterms. -/
  | sumCodeCong {scope : Nat}
      {leftSource leftTarget rightSource rightTarget : RawTerm scope} :
      RawStep.par leftSource leftTarget →
      RawStep.par rightSource rightTarget →
      RawStep.par (RawTerm.sumCode leftSource rightSource)
                  (RawTerm.sumCode leftTarget rightTarget)
  /-- Cong: listCode reduces in element. -/
  | listCodeCong {scope : Nat}
      {elementSource elementTarget : RawTerm scope} :
      RawStep.par elementSource elementTarget →
      RawStep.par (RawTerm.listCode elementSource) (RawTerm.listCode elementTarget)
  /-- Cong: optionCode reduces in element. -/
  | optionCodeCong {scope : Nat}
      {elementSource elementTarget : RawTerm scope} :
      RawStep.par elementSource elementTarget →
      RawStep.par (RawTerm.optionCode elementSource) (RawTerm.optionCode elementTarget)
  /-- Cong: eitherCode reduces in both subterms. -/
  | eitherCodeCong {scope : Nat}
      {leftSource leftTarget rightSource rightTarget : RawTerm scope} :
      RawStep.par leftSource leftTarget →
      RawStep.par rightSource rightTarget →
      RawStep.par (RawTerm.eitherCode leftSource rightSource)
                  (RawTerm.eitherCode leftTarget rightTarget)
  /-- Cong: idCode reduces in carrier and both endpoints. -/
  | idCodeCong {scope : Nat}
      {typeSource typeTarget leftSource leftTarget rightSource rightTarget : RawTerm scope} :
      RawStep.par typeSource typeTarget →
      RawStep.par leftSource leftTarget →
      RawStep.par rightSource rightTarget →
      RawStep.par (RawTerm.idCode typeSource leftSource rightSource)
                  (RawTerm.idCode typeTarget leftTarget rightTarget)
  /-- Cong: equivCode reduces in both type subterms. -/
  | equivCodeCong {scope : Nat}
      {leftSource leftTarget rightSource rightTarget : RawTerm scope} :
      RawStep.par leftSource leftTarget →
      RawStep.par rightSource rightTarget →
      RawStep.par (RawTerm.equivCode leftSource rightSource)
                  (RawTerm.equivCode leftTarget rightTarget)
  /-- CUMUL-2.6 Cong: cumulUpMarker reduces in its inner code raw. -/
  | cumulUpMarkerCong {scope : Nat}
      {sourceRaw targetRaw : RawTerm scope} :
      RawStep.par sourceRaw targetRaw →
      RawStep.par (RawTerm.cumulUpMarker sourceRaw)
                  (RawTerm.cumulUpMarker targetRaw)

end LeanFX2

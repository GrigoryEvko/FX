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
  /-- Modal β: eliminating a freshly introduced modal value returns the payload. -/
  | betaModElimIntro {scope : Nat}
      {innerRawSource innerRawTarget : RawTerm scope} :
      RawStep.par innerRawSource innerRawTarget →
      RawStep.par (RawTerm.modElim (RawTerm.modIntro innerRawSource))
                  innerRawTarget
  /-- Deep modal β: the eliminated value develops to a modal introduction. -/
  | betaModElimIntroDeep {scope : Nat}
      {innerRawSource innerRawTarget : RawTerm scope} :
      RawStep.par innerRawSource (RawTerm.modIntro innerRawTarget) →
      RawStep.par (RawTerm.modElim innerRawSource) innerRawTarget
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
  /-- Shallow ι: `idStrictRec base (idStrictRefl rt) ⟶ base'`. -/
  | iotaIdStrictRecRefl {scope : Nat}
      {baseRawSource baseRawTarget : RawTerm scope}
      (witnessRaw : RawTerm scope) :
      RawStep.par baseRawSource baseRawTarget →
      RawStep.par
        (RawTerm.idStrictRec baseRawSource (RawTerm.idStrictRefl witnessRaw))
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
  /-- Deep ι: `witness ⟶ idStrictRefl rt` then strict rec fires. -/
  | iotaIdStrictRecReflDeep {scope : Nat}
      {witnessRawSource : RawTerm scope}
      {reflRawArgument : RawTerm scope}
      {baseRawSource baseRawTarget : RawTerm scope} :
      RawStep.par witnessRawSource (RawTerm.idStrictRefl reflRawArgument) →
      RawStep.par baseRawSource baseRawTarget →
      RawStep.par (RawTerm.idStrictRec baseRawSource witnessRawSource)
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
  /-- Cubical path β at a syntactically constant path body:
  `pathApp (pathLam value.weaken) interval ⟶ value`.

  This is the raw analog of `Step.betaPathReflApp` and the parallel-step
  ctor `Step.par.betaPathReflApp`.  When the pathLam body is
  `value.weaken` (i.e. mentions no interval binder), application across
  the path gives back the original value irrespective of the interval
  argument — the cubical analog of "(λ i ⇒ value) @ i ⟶ value" when
  `value` is independent of `i`.

  ## Shallow shape (single-redex β)

  This is the shallow variant: the `pathApp` head plus the constant
  `pathLam` body must be exactly that pair on the LHS.  Inner
  reductions on `valueRawSource` and `intervalRawSource` proceed via
  the two `RawStep.par` premises.  The deep variant is intentionally
  deferred — the existing `betaPathApp` / `betaPathAppDeep` pair
  already handles the case where the path develops to `pathLam body`
  for arbitrary body, including `body = value.weaken`; the cd cascade
  arm for `betaPathReflApp` collapses against the existing path-app
  cascade through `RawTerm.weaken_subst_singleton`. -/
  | betaPathReflApp {scope : Nat}
      {valueRawSource valueRawTarget intervalRawSource intervalRawTarget :
        RawTerm scope} :
      RawStep.par valueRawSource valueRawTarget →
      RawStep.par intervalRawSource intervalRawTarget →
      RawStep.par
        (RawTerm.pathApp (RawTerm.pathLam valueRawSource.weaken) intervalRawSource)
        valueRawTarget
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
  /-- Cubical transport β at a syntactically constant type path:
  `transp (pathLam typeRaw.weaken) value ⟶ value`.

  This is the raw analog of `Step.transpReflBeta` and the Step.par
  ctor `Step.par.transpReflBeta` (`Reduction/ParRed.lean`).  When
  the type path body is `typeRaw.weaken` (i.e. mentions no interval
  binder), transport across it is the identity.  This is the
  cubical analog of "transp refl A x ⟶ x" — `pathLam typeRaw.weaken`
  is the constant path `λ i ⇒ typeRaw`, which plays the role of
  `refl typeRaw` in the cubical fragment.

  ## Shallow shape (single-redex β)

  This is the shallow variant: the `transp` head plus the constant
  `pathLam` body must be exactly that pair on the LHS.  Inner
  reductions on `typeRaw` and `sourceRaw` proceed via the two
  `RawStep.par` premises.  The deep variant (when the path is not
  literally `pathLam typeRaw.weaken` on the LHS but reduces to it)
  is intentionally deferred to D2.5-CASCADE; the diamond cd lemma
  for this rule will need it once typed confluence cascades fire. -/
  | transpReflBeta {scope : Nat}
      {typeRawSource typeRawTarget sourceRawSource sourceRawTarget :
        RawTerm scope} :
      RawStep.par typeRawSource typeRawTarget →
      RawStep.par sourceRawSource sourceRawTarget →
      RawStep.par
        (RawTerm.transp (RawTerm.pathLam typeRawSource.weaken) sourceRawSource)
        sourceRawTarget
  /-- Deep cubical transport β: when the path develops via parallel
  reduction to a constant `pathLam typeRawTarget.weaken` and the
  source steps to a target value, the whole transp reduces to that
  target.  Required for `cd_dominates` to discharge `cdTranspCase`'s
  β-firing branch when the path was NOT literally `pathLam X.weaken`
  on the LHS but reaches that shape under cd development.

  Discharge requires `RawStep.par.weaken_inv` (Phase G.0, shipped via
  `RawParWeakenInv.lean`) to invert the path reduction in cd_lemma's
  arm. -/
  | transpReflBetaDeep {scope : Nat}
      {pathRawSource typeRawTarget sourceRawSource sourceRawTarget :
        RawTerm scope} :
      RawStep.par pathRawSource (RawTerm.pathLam typeRawTarget.weaken) →
      RawStep.par sourceRawSource sourceRawTarget →
      RawStep.par (RawTerm.transp pathRawSource sourceRawSource)
                  sourceRawTarget
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
  /-- Refinement β: extracting from an introduced refinement yields the value. -/
  | betaRefineElimIntro {scope : Nat}
      {valueRawSource valueRawTarget proofRawSource proofRawTarget : RawTerm scope} :
      RawStep.par valueRawSource valueRawTarget →
      RawStep.par proofRawSource proofRawTarget →
      RawStep.par (RawTerm.refineElim
                    (RawTerm.refineIntro valueRawSource proofRawSource))
                  valueRawTarget
  /-- Deep refinement β: refined value develops to a `refineIntro`. -/
  | betaRefineElimIntroDeep {scope : Nat}
      {refinedRawSource : RawTerm scope}
      {valueRawTarget proofRawTarget : RawTerm scope} :
      RawStep.par refinedRawSource
        (RawTerm.refineIntro valueRawTarget proofRawTarget) →
      RawStep.par (RawTerm.refineElim refinedRawSource) valueRawTarget
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
  /-- Record β: projecting from a single-field record intro yields the field. -/
  | betaRecordProjIntro {scope : Nat}
      {firstRawSource firstRawTarget : RawTerm scope} :
      RawStep.par firstRawSource firstRawTarget →
      RawStep.par (RawTerm.recordProj (RawTerm.recordIntro firstRawSource))
                  firstRawTarget
  /-- Deep record β: record value develops to a `recordIntro`. -/
  | betaRecordProjIntroDeep {scope : Nat}
      {recordRawSource : RawTerm scope}
      {firstRawTarget : RawTerm scope} :
      RawStep.par recordRawSource (RawTerm.recordIntro firstRawTarget) →
      RawStep.par (RawTerm.recordProj recordRawSource) firstRawTarget
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
  /-- Codata β: observing an unfold applies the transition to the state. -/
  | betaCodataDestUnfold {scope : Nat}
      {stateRawSource stateRawTarget transitionRawSource transitionRawTarget :
        RawTerm scope} :
      RawStep.par stateRawSource stateRawTarget →
      RawStep.par transitionRawSource transitionRawTarget →
      RawStep.par
        (RawTerm.codataDest
          (RawTerm.codataUnfold stateRawSource transitionRawSource))
        (RawTerm.app transitionRawTarget stateRawTarget)
  /-- Deep codata β: codata value develops to an unfold, then observation fires. -/
  | betaCodataDestUnfoldDeep {scope : Nat}
      {codataRawSource stateRawTarget transitionRawTarget : RawTerm scope} :
      RawStep.par codataRawSource
        (RawTerm.codataUnfold stateRawTarget transitionRawTarget) →
      RawStep.par (RawTerm.codataDest codataRawSource)
        (RawTerm.app transitionRawTarget stateRawTarget)
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
  /-- D3.6-P1 Cong: uaToEquiv reduces in its inner proof raw.  The
  actual univalence-β rule (`uaToEquiv` applied at `transp` reducing
  to `equivApply`) ships in a later phase; the cong rule is the
  vocabulary-level reduction baseline. -/
  | uaToEquivCong {scope : Nat}
      {sourceRaw targetRaw : RawTerm scope} :
      RawStep.par sourceRaw targetRaw →
      RawStep.par (RawTerm.uaToEquiv sourceRaw)
                  (RawTerm.uaToEquiv targetRaw)
  /-- D3.6-P2 Cong: equivApply reduces pointwise in its equiv and
  arg raw payloads.  Binary mirror of `uaToEquivCong`. -/
  | equivApplyCong {scope : Nat}
      {equivSource equivTarget argSource argTarget : RawTerm scope} :
      RawStep.par equivSource equivTarget →
      RawStep.par argSource argTarget →
      RawStep.par (RawTerm.equivApply equivSource argSource)
                  (RawTerm.equivApply equivTarget argTarget)
  /-- D3.6-S1 univalence-β raw rule:
  `transp (uaToEquiv proof) source ⟶ equivApply (uaToEquiv proof) source`.

  The headline kernel-internal univalence-β reduction.  When the path
  argument of `transp` is a `uaToEquiv proofRaw` head (the term-level
  marker of "interpret this `Id (Universe lvl) leftTy rightTy` proof
  as the corresponding type equivalence"), the entire `transp`
  expression reduces to applying the packaged equivalence directly to
  the source value via `equivApply (uaToEquiv proof) source`.

  ## Why no typed mirror

  At the typed level, `Term.transp` requires its path argument to be a
  `Term context (Ty.path ...) pathRaw`, but `Term.uaToEquiv` produces
  type `Ty.equiv leftTy rightTy` (NOT `Ty.path`).  Therefore no typed
  `Term.transp` can have a path-raw of `RawTerm.uaToEquiv proofRaw`,
  making this β rule structurally a raw-only confluence-closure
  mechanism — listed in `isDocumentedRawOnlyParity` alongside the
  raw-only `transpReflBetaDeep`.

  ## Why both proof and source step

  Inner reductions on `proofRaw` and `sourceRaw` proceed via the two
  `RawStep.par` premises.  The β fires on the outer `transp` head
  with the path's `uaToEquiv` ctor matching syntactically.  This is
  the shallow form; a deep variant (path develops to `uaToEquiv` via
  parallel reduction) is `uaBetaDeep` below. -/
  | uaBeta {scope : Nat}
      {proofRawSource proofRawTarget sourceRawSource sourceRawTarget :
        RawTerm scope} :
      RawStep.par proofRawSource proofRawTarget →
      RawStep.par sourceRawSource sourceRawTarget →
      RawStep.par
        (RawTerm.transp (RawTerm.uaToEquiv proofRawSource) sourceRawSource)
        (RawTerm.equivApply (RawTerm.uaToEquiv proofRawTarget) sourceRawTarget)
  /-- D3.6-S1 deep univalence-β raw rule: when the path develops via
  parallel reduction to a `uaToEquiv proofRawTarget` and the source
  steps to a target value, the entire `transp` reduces to the
  univalence-β contractum.  Required for `cd_dominates` to discharge
  `cdTranspCase`'s `uaToEquiv`-firing branch when the path was NOT
  literally `uaToEquiv X` on the LHS but reaches that shape under cd
  development.

  Discharge in `cd_lemma` requires the typical path-shape inversion
  on `pathStep` (pathLam_inv / uaToEquiv_inv via the `transp_inv`
  cascade) — analogous to `transpReflBetaDeep` for the constant-path
  case.  Like `transpReflBetaDeep`, this is documented `raw-only`
  (`isDocumentedRawOnlyParity`) — a confluence-only mechanism with no
  typed mirror because `uaBeta` itself has no typed mirror. -/
  | uaBetaDeep {scope : Nat}
      {pathRawSource proofRawTarget sourceRawSource sourceRawTarget :
        RawTerm scope} :
      RawStep.par pathRawSource (RawTerm.uaToEquiv proofRawTarget) →
      RawStep.par sourceRawSource sourceRawTarget →
      RawStep.par
        (RawTerm.transp pathRawSource sourceRawSource)
        (RawTerm.equivApply (RawTerm.uaToEquiv proofRawTarget) sourceRawTarget)
  /-- D3.6-S3 Cong: pathCompose reduces pointwise in its left and right
  path raw payloads.  Binary mirror of `uaToEquivCong`. -/
  | pathComposeCong {scope : Nat}
      {leftSource leftTarget rightSource rightTarget : RawTerm scope} :
      RawStep.par leftSource leftTarget →
      RawStep.par rightSource rightTarget →
      RawStep.par (RawTerm.pathCompose leftSource rightSource)
                  (RawTerm.pathCompose leftTarget rightTarget)
  /-- D3.6-S3 raw cubical-β rule: transport distributes over path composition.

  ```
  transp (pathCompose leftPath rightPath) source
    ⟶ transp rightPath (transp leftPath source)
  ```

  This is the kernel-internal cubical-β rule encoding the spec's
  rule "transp (compose path1 path2) source ⟶ transp path2 (transp
  path1 source)" (per `fx_design.md` §27 / Appendix H).  The headline
  rule fires when `transp`'s path argument is syntactically a
  `pathCompose leftRaw rightRaw` head — both paths develop in parallel
  to their target shapes, the source value develops to its target,
  and the resulting expression nests two `transp` applications,
  applying `leftPath`'s transport first (innermost) and `rightPath`'s
  outermost.

  ## Why both paths and source step

  Inner reductions on each path raw and the source proceed via three
  `RawStep.par` premises.  The β fires on the outer `transp` head
  with the path's `pathCompose` ctor matching syntactically.  This is
  the shallow form; the deep variant (path develops to `pathCompose`
  via parallel reduction) is `transpComposeDeep` below.

  ## Raw-only cascade (matches uaBeta architecture)

  At the typed level, `Term.pathCompose` requires both paths to be
  `Term context (Ty.path ...) ...` and produces a fresh path of the
  composed endpoints — but the kernel's typed `Term` inductive does
  NOT yet have a `pathCompose` ctor (D3.10 follow-up, deferred to
  v1.1).  Therefore no typed `Term.transp` can have a path-raw of
  `RawTerm.pathCompose ...`, making this β rule structurally a raw-
  only confluence-closure mechanism — listed in
  `isDocumentedRawOnlyParity` alongside `uaBeta`/`uaBetaDeep` and
  `transpReflBetaDeep`.

  ## Connection to meta-level rule

  At the meta-level, `Path.transport_compose` in
  `HoTT/TranspCompose.lean` proves the SAME rule for set-level paths
  (Lean Eq).  The kernel-syntactic raw rule shipped here is the
  cubical analog that fires through the cd cascade. -/
  | transpCompose {scope : Nat}
      {leftRawSource leftRawTarget rightRawSource rightRawTarget
       sourceRawSource sourceRawTarget : RawTerm scope} :
      RawStep.par leftRawSource leftRawTarget →
      RawStep.par rightRawSource rightRawTarget →
      RawStep.par sourceRawSource sourceRawTarget →
      RawStep.par
        (RawTerm.transp (RawTerm.pathCompose leftRawSource rightRawSource)
          sourceRawSource)
        (RawTerm.transp rightRawTarget
          (RawTerm.transp leftRawTarget sourceRawTarget))
  /-- D3.6-S3 deep raw cubical-β rule: when the path develops via
  parallel reduction to a `pathCompose leftRawTarget rightRawTarget`
  and the source steps to a target value, the entire `transp` reduces
  to the compose-β contractum.  Required for `cd_dominates` to
  discharge `cdTranspCase`'s `pathCompose`-firing branch when the
  path was NOT literally `pathCompose left right` on the LHS but
  reaches that shape under cd development.

  Discharge in `cd_lemma` requires the typical path-shape inversion
  on `pathStep` — analogous to `uaBetaDeep` for the univalence-β case.
  Documented `raw-only` (`isDocumentedRawOnlyParity`) — a
  confluence-only mechanism with no typed mirror because
  `transpCompose` itself has no typed mirror until D3.10 v1.1. -/
  | transpComposeDeep {scope : Nat}
      {pathRawSource leftRawTarget rightRawTarget
       sourceRawSource sourceRawTarget : RawTerm scope} :
      RawStep.par pathRawSource
        (RawTerm.pathCompose leftRawTarget rightRawTarget) →
      RawStep.par sourceRawSource sourceRawTarget →
      RawStep.par (RawTerm.transp pathRawSource sourceRawSource)
                  (RawTerm.transp rightRawTarget
                    (RawTerm.transp leftRawTarget sourceRawTarget))
  /-- D3.6-S4 Cong: idToEquiv reduces pointwise in its proof raw payload.
  Unary mirror of `uaToEquivCong`. -/
  | idToEquivCong {scope : Nat}
      {proofSource proofTarget : RawTerm scope} :
      RawStep.par proofSource proofTarget →
      RawStep.par (RawTerm.idToEquiv proofSource)
                  (RawTerm.idToEquiv proofTarget)
  /-- D3.6-S4 raw univalence-refl-β rule: identity-to-equivalence at refl
  reduces to the identity equivalence.

  ```
  idToEquiv (refl witness) ⟶ equivIntro (lam (var 0)) (lam (var 0))
  ```

  This is the kernel-internal univalence-refl-β rule, encoding the
  meta-level rule `Univalence.idToEquivMeta_refl : idToEquivMeta rfl
  = Equiv.refl` (per `HoTT/Univalence.lean`) at the syntactic level.
  The β fires when `idToEquiv`'s proof argument is syntactically a
  `refl witness` head — both the proof and witness develop in
  parallel, the proof becomes a refl on the developed witness, and
  the resulting expression is the identity-equivalence shape
  `equivIntro (lam (var 0)) (lam (var 0))` (forward and backward both
  the identity function on the bound variable).

  ## Why both witness steps and outer fires

  Inner reduction on the witness raw proceeds via the witnessStep
  premise.  The β fires on the outer `idToEquiv` head with the
  proof's `refl` ctor matching syntactically.  This is the shallow
  form; the deep variant (proof develops to `refl ...` via parallel
  reduction) is `idToEquivReflDeep` below.

  ## Raw-only cascade (matches uaBeta architecture)

  At the typed level, `Term.idToEquiv` would require the proof to be
  `Term context (Ty.id ...) ...` and produce a typed `Term context
  (Ty.equiv ...)` — but the kernel's typed `Term` inductive does NOT
  yet have an `idToEquiv` ctor (v1.1 follow-up, deferred).  Therefore
  no typed `Term.idToEquiv` can have a proof-raw of `RawTerm.refl ...`,
  making this β rule structurally a raw-only confluence-closure
  mechanism — listed in `isDocumentedRawOnlyParity` alongside
  `uaBeta`/`uaBetaDeep` and `transpCompose`/`transpComposeDeep`.

  ## Connection to meta-level rule

  At the meta-level, `Univalence.idToEquivMeta_refl` proves that the
  set-level analog `(idToEquivMeta rfl) = Equiv.refl _`.  The kernel-
  syntactic raw rule shipped here is the cubical analog firing
  through the cd cascade. -/
  | idToEquivRefl {scope : Nat}
      {witnessSource witnessTarget : RawTerm scope} :
      RawStep.par witnessSource witnessTarget →
      RawStep.par
        (RawTerm.idToEquiv (RawTerm.refl witnessSource))
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var (Fin.mk 0 (Nat.zero_lt_succ _))))
          (RawTerm.lam (RawTerm.var (Fin.mk 0 (Nat.zero_lt_succ _)))))
  /-- D3.6-S4 deep raw univalence-refl-β rule: when the proof develops
  via parallel reduction to a `refl witnessTarget`, the entire
  `idToEquiv` reduces to the identity-equivalence contractum.
  Required for `cd_dominates` to discharge `cdIdToEquivCase`'s
  `refl`-firing branch when the proof was NOT literally `refl ...`
  on the LHS but reaches that shape under cd development.

  Discharge in `cd_lemma` requires the typical proof-shape inversion
  on the developed proofStep — analogous to `uaBetaDeep` for the
  univalence-β case.  Documented `raw-only`
  (`isDocumentedRawOnlyParity`) — a confluence-only mechanism with
  no typed mirror because `idToEquivRefl` itself has no typed mirror
  until v1.1. -/
  | idToEquivReflDeep {scope : Nat}
      {proofRawSource witnessTarget : RawTerm scope} :
      RawStep.par proofRawSource (RawTerm.refl witnessTarget) →
      RawStep.par
        (RawTerm.idToEquiv proofRawSource)
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var (Fin.mk 0 (Nat.zero_lt_succ _))))
          (RawTerm.lam (RawTerm.var (Fin.mk 0 (Nat.zero_lt_succ _)))))
  /-- D3.6-S5 Cong: oeqTrans reduces pointwise in both proof raw payloads.
  Binary cong rule for the new transitive-composition ctor. -/
  | oeqTransCong {scope : Nat}
      {firstSource firstTarget secondSource secondTarget : RawTerm scope} :
      RawStep.par firstSource firstTarget →
      RawStep.par secondSource secondTarget →
      RawStep.par (RawTerm.oeqTrans firstSource secondSource)
                  (RawTerm.oeqTrans firstTarget secondTarget)
  /-- D3.6-S5 Cong: equivCompose reduces pointwise in both equivalence
  raw payloads.  Binary cong rule for the new equivalence-composition
  ctor. -/
  | equivComposeCong {scope : Nat}
      {firstSource firstTarget secondSource secondTarget : RawTerm scope} :
      RawStep.par firstSource firstTarget →
      RawStep.par secondSource secondTarget →
      RawStep.par (RawTerm.equivCompose firstSource secondSource)
                  (RawTerm.equivCompose firstTarget secondTarget)
  /-- D3.6-S5 raw univalence-compose-β rule: identity-to-equivalence
  distributes over composition of observational-equality proofs.

  ```
  idToEquiv (oeqTrans first second)
    ⟶ equivCompose (idToEquiv first) (idToEquiv second)
  ```

  This is the kernel-internal univalence-compose-β rule, encoding the
  meta-level rule "idToEquiv distributes over oeqTrans" at the
  syntactic level.  The β fires when `idToEquiv`'s proof argument is
  syntactically an `oeqTrans first second` head.

  ## Why both inner steps and outer fires

  Inner reduction on `first` and `second` proceeds via the firstStep
  and secondStep premises.  The β fires on the outer `idToEquiv` head
  with the proof's `oeqTrans` ctor matching syntactically.  This is
  the shallow form; the deep variant (proof develops to `oeqTrans ...`
  via parallel reduction) is `idToEquivComposeDeep` below.

  ## Raw-only cascade (matches idToEquivRefl architecture)

  At the typed level, `Term.idToEquiv` would require the proof to be
  `Term context (Ty.id ...) ...` and produce a typed `Term context
  (Ty.equiv ...)` — but the kernel's typed `Term` inductive does NOT
  yet have `idToEquiv`/`oeqTrans`/`equivCompose` ctors (v1.1
  follow-up).  Therefore this β rule is a raw-only confluence-closure
  mechanism, listed in `isDocumentedRawOnlyParity` Section G. -/
  | idToEquivCompose {scope : Nat}
      {firstSource firstTarget secondSource secondTarget : RawTerm scope} :
      RawStep.par firstSource firstTarget →
      RawStep.par secondSource secondTarget →
      RawStep.par
        (RawTerm.idToEquiv (RawTerm.oeqTrans firstSource secondSource))
        (RawTerm.equivCompose
          (RawTerm.idToEquiv firstTarget)
          (RawTerm.idToEquiv secondTarget))
  /-- D3.6-S5 deep raw univalence-compose-β rule: when the proof
  develops via parallel reduction to an `oeqTrans firstTarget
  secondTarget`, the entire `idToEquiv` reduces to the equivCompose
  contractum.  Required for `cd_dominates` to discharge
  `cdIdToEquivCase`'s `oeqTrans`-firing branch when the proof was NOT
  literally `oeqTrans ...` on the LHS but reaches that shape under cd
  development. -/
  | idToEquivComposeDeep {scope : Nat}
      {proofRawSource firstTarget secondTarget : RawTerm scope} :
      RawStep.par proofRawSource (RawTerm.oeqTrans firstTarget secondTarget) →
      RawStep.par
        (RawTerm.idToEquiv proofRawSource)
        (RawTerm.equivCompose
          (RawTerm.idToEquiv firstTarget)
          (RawTerm.idToEquiv secondTarget))
  /-- D3.6-S6 raw univalence-refl-roundtrip-β rule: applying the
  identity equivalence (encoded as `uaToEquiv (oeqRefl _)`) yields the
  argument unchanged.

  ```
  equivApply (uaToEquiv (oeqRefl witness)) source ⟶ source
  ```

  This is the kernel-internal univalence-refl-roundtrip-β rule: when
  the `equivApply`'s equiv argument is syntactically `uaToEquiv
  (oeqRefl witness)` (the identity-equivalence-via-univalence shape),
  applying that equivalence to a value `source` reduces directly to
  `source`.  Conceptually closes the round-trip:
  `idToEquiv ∘ oeqRefl = identityEquiv` from the S4 angle, paired with
  `uaToEquiv ∘ oeqRefl ∘ apply = identity` from the S6 angle.

  ## Why both witness and source step

  Inner reduction on `witness` proceeds via the witnessStep premise
  (the inner refl's witness can develop independently); inner
  reduction on `source` proceeds via sourceStep.  The β fires on the
  outer `equivApply` head with the equiv argument's nested
  `uaToEquiv (oeqRefl _)` ctor matching syntactically.  This is the
  shallow form; the deep variant (equiv develops to
  `uaToEquiv (oeqRefl _)` via parallel reduction) is
  `uaReflEquivApplyDeep` below.

  ## Connection to S4 / S5 / uaBeta

  S4 ships `idToEquiv (refl _) ⟶ equivIntro (lam id) (lam id)` —
  identity-as-built-from-id-type.  S6 ships the dual round-trip:
  applying the univalence-of-refl equivalence reduces to identity
  directly.  Together these close the univalence round-trip cycle at
  the kernel-syntactic level.  The cd cascade integrates via the new
  helper `cdEquivApplyCase` that dispatches on the developed
  `equivRaw`'s shape.

  ## Raw-only cascade (matches uaBeta architecture)

  At the typed level, `Term.equivApply` requires its equiv argument at
  type `Ty.equiv ...` and `Term.uaToEquiv` produces type `Ty.equiv
  ...`, but `Term.oeqRefl` produces type `Ty.oeq ...` (NOT the
  `Ty.id ...` that `uaToEquiv` would consume).  Therefore no typed
  `Term.equivApply` can have an equiv-raw of `RawTerm.uaToEquiv
  (RawTerm.oeqRefl ...)` — the typed parity gate would block it
  structurally.  Listed in `isDocumentedRawOnlyParity` Section H
  alongside `uaBeta`/`idToEquivRefl`.  Once typed mirrors land
  (v1.1's D3.10 univalence-composition-closure), this rule will move
  out of the raw-only whitelist.

  ## Connection to meta-level rule

  At the meta-level, `Univalence.idToEquivMeta_refl` proves that
  `idToEquivMeta rfl = Equiv.refl _` and `Equiv.refl.apply x = x` is
  a direct unfold.  The kernel-syntactic raw rule shipped here is the
  cubical analog firing through the cd cascade. -/
  | uaReflEquivApply {scope : Nat}
      {witnessSource witnessTarget sourceRawSource sourceRawTarget :
        RawTerm scope} :
      RawStep.par witnessSource witnessTarget →
      RawStep.par sourceRawSource sourceRawTarget →
      RawStep.par
        (RawTerm.equivApply
          (RawTerm.uaToEquiv (RawTerm.oeqRefl witnessSource))
          sourceRawSource)
        sourceRawTarget
  /-- D3.6-S6 deep raw univalence-refl-roundtrip-β rule: when the
  equiv develops via parallel reduction to a `uaToEquiv (oeqRefl
  witnessTarget)`, the entire `equivApply` reduces directly to the
  developed source.  Required for `cd_dominates` to discharge
  `cdEquivApplyCase`'s `uaToEquiv (oeqRefl _)`-firing branch when the
  equiv was NOT literally `uaToEquiv (oeqRefl _)` on the LHS but
  reaches that shape under cd development.

  Discharge in `cd_lemma` requires the typical equiv-shape inversion
  on `equivStep` (uaToEquiv_inv composed with oeqRefl_inv) —
  analogous to `idToEquivReflDeep` for the S4 refl-β case.
  Documented `raw-only` (`isDocumentedRawOnlyParity`) — a
  confluence-only mechanism with no typed mirror because the rule's
  own typed structure is blocked by the `oeq` vs `id` typed-Ty
  mismatch at the equiv argument. -/
  | uaReflEquivApplyDeep {scope : Nat}
      {equivRawSource witnessTarget sourceRawSource sourceRawTarget :
        RawTerm scope} :
      RawStep.par equivRawSource
        (RawTerm.uaToEquiv (RawTerm.oeqRefl witnessTarget)) →
      RawStep.par sourceRawSource sourceRawTarget →
      RawStep.par
        (RawTerm.equivApply equivRawSource sourceRawSource)
        sourceRawTarget
  /-- Schematic-payload value cong (typed `Term.funextRefl`'s mirror at raw):
      `RawTerm.lam (RawTerm.refl applyRaw)` reduces in applyRaw.  Aliased
      via `lam ∘ reflCong`; typed parity gate sees a same-suffix mirror. -/
  | funextReflCong {scope : Nat}
      {applyRawSource applyRawTarget : RawTerm (scope + 1)} :
      RawStep.par applyRawSource applyRawTarget →
      RawStep.par (RawTerm.lam (RawTerm.refl applyRawSource))
                  (RawTerm.lam (RawTerm.refl applyRawTarget))
  /-- Schematic-payload value cong (typed `Term.funextReflAtId`'s mirror at raw). -/
  | funextReflAtIdCong {scope : Nat}
      {applyRawSource applyRawTarget : RawTerm (scope + 1)} :
      RawStep.par applyRawSource applyRawTarget →
      RawStep.par (RawTerm.lam (RawTerm.refl applyRawSource))
                  (RawTerm.lam (RawTerm.refl applyRawTarget))
  /-- Schematic-payload value cong (typed `Term.funextIntroHet`'s mirror at raw).
      The applyB raw isn't carried in the projected raw form; only applyA's
      reduction shows up at the raw level via `lam(reflCong)`. -/
  | funextIntroHetCong {scope : Nat}
      {applyARawSource applyARawTarget : RawTerm (scope + 1)} :
      RawStep.par applyARawSource applyARawTarget →
      RawStep.par (RawTerm.lam (RawTerm.refl applyARawSource))
                  (RawTerm.lam (RawTerm.refl applyARawTarget))

end LeanFX2

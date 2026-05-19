import LeanFX2.Algo.RawWHNF.ProjectionInversions

namespace LeanFX2

/-- Fuel-bounded weak head normal form reduction on raw terms.
Fires β/ι at the head until reaching a canonical/neutral form
or running out of fuel.

Inner dispatches use the `?`-projection helpers to avoid
wildcard match patterns inside the recursive body, keeping the
function propext-free.

Reductions performed:
* `app (lam body) arg`           → `body.subst0 arg`
* `fst (pair fv sv)`             → `fv`
* `snd (pair fv sv)`             → `sv`
* `boolElim true t e`            → `t`
* `boolElim false t e`           → `e`
* `natElim 0 z s`                → `z`
* `natElim (succ n) z s`         → `app s n`
* `natRec 0 z s`                 → `z`
* `natRec (succ n) z s`          → `app (app s n) (natRec n z s)`
* `listElim nil n c`             → `n`
* `listElim (cons h t) n c`      → `app (app c h) t`
* `optionMatch none n s`         → `n`
* `optionMatch (some v) n s`     → `app s v`
* `eitherMatch (inl v) l r`      → `app l v`
* `eitherMatch (inr v) l r`      → `app r v`
* `idJ b (refl _)`               → `b`

Modal `modElim (modIntro _)` reduces are deferred to Layer 6;
this WHNF treats modal forms as canonical for now. -/
def RawTerm.whnf (fuel : Nat) {scope : Nat} (term : RawTerm scope) :
    RawTerm scope :=
  match fuel with
  | 0 => term
  | fuel + 1 =>
    match term with
    | .var position => .var position
    | .unit => .unit
    | .lam body => .lam body
    | .app functionTerm argumentTerm =>
        let functionWhnf := RawTerm.whnf fuel functionTerm
        match RawTerm.lamBody? functionWhnf with
        | some body => RawTerm.whnf fuel (body.subst0 argumentTerm)
        | none      => .app functionWhnf argumentTerm
    | .pair firstValue secondValue => .pair firstValue secondValue
    | .fst pairTerm =>
        let pairWhnf := RawTerm.whnf fuel pairTerm
        match RawTerm.pairComponents? pairWhnf with
        | some (firstValue, _) => RawTerm.whnf fuel firstValue
        | none                 => .fst pairWhnf
    | .snd pairTerm =>
        let pairWhnf := RawTerm.whnf fuel pairTerm
        match RawTerm.pairComponents? pairWhnf with
        | some (_, secondValue) => RawTerm.whnf fuel secondValue
        | none                  => .snd pairWhnf
    | .boolTrue => .boolTrue
    | .boolFalse => .boolFalse
    | .boolElim scrutinee thenBranch elseBranch =>
        let scrutineeWhnf := RawTerm.whnf fuel scrutinee
        match scrutineeWhnf.headCtor with
        | .boolTrue  => RawTerm.whnf fuel thenBranch
        | .boolFalse => RawTerm.whnf fuel elseBranch
        | .var | .unit | .lam | .app | .pair | .fst | .snd
        | .boolElim | .natZero | .natSucc | .natElim | .natRec
        | .listNil | .listCons | .listElim
        | .optionNone | .optionSome | .optionMatch
        | .eitherInl | .eitherInr | .eitherMatch
        | .refl | .idJ | .modIntro | .modElim | .subsume
        | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
        | .pathLam | .pathApp | .glueIntro | .glueElim | .transp | .transpFill | .hcomp
        | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec
        | .equivIntro | .equivApp | .refineIntro | .refineElim
        | .recordIntro | .recordProj | .codataUnfold | .codataDest
        | .sessionSend | .sessionRecv | .effectPerform
        | .universeCode
        | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
        | .listCode | .optionCode | .eitherCode | .idCode | .equivCode
        | .cumulUpMarker | .uaToEquiv | .equivApply | .pathCompose
        | .idToEquiv | .oeqTrans | .equivCompose =>
            .boolElim scrutineeWhnf thenBranch elseBranch
    | .natZero => .natZero
    | .natSucc predecessor => .natSucc predecessor
    | .natElim scrutinee zeroBranch succBranch =>
        let scrutineeWhnf := RawTerm.whnf fuel scrutinee
        match scrutineeWhnf.headCtor with
        | .natZero =>
            RawTerm.whnf fuel zeroBranch
        | .natSucc =>
            match RawTerm.natSuccPred? scrutineeWhnf with
            | some predecessor =>
                RawTerm.whnf fuel (.app succBranch predecessor)
            | none =>
                .natElim scrutineeWhnf zeroBranch succBranch
        | .var | .unit | .lam | .app | .pair | .fst | .snd
        | .boolTrue | .boolFalse | .boolElim
        | .natElim | .natRec
        | .listNil | .listCons | .listElim
        | .optionNone | .optionSome | .optionMatch
        | .eitherInl | .eitherInr | .eitherMatch
        | .refl | .idJ | .modIntro | .modElim | .subsume
        | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
        | .pathLam | .pathApp | .glueIntro | .glueElim | .transp | .transpFill | .hcomp
        | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec
        | .equivIntro | .equivApp | .refineIntro | .refineElim
        | .recordIntro | .recordProj | .codataUnfold | .codataDest
        | .sessionSend | .sessionRecv | .effectPerform
        | .universeCode
        | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
        | .listCode | .optionCode | .eitherCode | .idCode | .equivCode
        | .cumulUpMarker | .uaToEquiv | .equivApply | .pathCompose
        | .idToEquiv | .oeqTrans | .equivCompose =>
            .natElim scrutineeWhnf zeroBranch succBranch
    | .natRec scrutinee zeroBranch succBranch =>
        let scrutineeWhnf := RawTerm.whnf fuel scrutinee
        match scrutineeWhnf.headCtor with
        | .natZero =>
            RawTerm.whnf fuel zeroBranch
        | .natSucc =>
            match RawTerm.natSuccPred? scrutineeWhnf with
            | some predecessor =>
                RawTerm.whnf fuel
                  (.app (.app succBranch predecessor)
                        (.natRec predecessor zeroBranch succBranch))
            | none =>
                .natRec scrutineeWhnf zeroBranch succBranch
        | .var | .unit | .lam | .app | .pair | .fst | .snd
        | .boolTrue | .boolFalse | .boolElim
        | .natElim | .natRec
        | .listNil | .listCons | .listElim
        | .optionNone | .optionSome | .optionMatch
        | .eitherInl | .eitherInr | .eitherMatch
        | .refl | .idJ | .modIntro | .modElim | .subsume
        | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
        | .pathLam | .pathApp | .glueIntro | .glueElim | .transp | .transpFill | .hcomp
        | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec
        | .equivIntro | .equivApp | .refineIntro | .refineElim
        | .recordIntro | .recordProj | .codataUnfold | .codataDest
        | .sessionSend | .sessionRecv | .effectPerform
        | .universeCode
        | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
        | .listCode | .optionCode | .eitherCode | .idCode | .equivCode
        | .cumulUpMarker | .uaToEquiv | .equivApply | .pathCompose
        | .idToEquiv | .oeqTrans | .equivCompose =>
            .natRec scrutineeWhnf zeroBranch succBranch
    | .listNil => .listNil
    | .listCons headTerm tailTerm => .listCons headTerm tailTerm
    | .listElim scrutinee nilBranch consBranch =>
        let scrutineeWhnf := RawTerm.whnf fuel scrutinee
        match scrutineeWhnf.headCtor with
        | .listNil =>
            RawTerm.whnf fuel nilBranch
        | .listCons =>
            match RawTerm.listConsParts? scrutineeWhnf with
            | some (headTerm, tailTerm) =>
                RawTerm.whnf fuel (.app (.app consBranch headTerm) tailTerm)
            | none =>
                .listElim scrutineeWhnf nilBranch consBranch
        | .var | .unit | .lam | .app | .pair | .fst | .snd
        | .boolTrue | .boolFalse | .boolElim
        | .natZero | .natSucc | .natElim | .natRec
        | .listElim
        | .optionNone | .optionSome | .optionMatch
        | .eitherInl | .eitherInr | .eitherMatch
        | .refl | .idJ | .modIntro | .modElim | .subsume
        | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
        | .pathLam | .pathApp | .glueIntro | .glueElim | .transp | .transpFill | .hcomp
        | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec
        | .equivIntro | .equivApp | .refineIntro | .refineElim
        | .recordIntro | .recordProj | .codataUnfold | .codataDest
        | .sessionSend | .sessionRecv | .effectPerform
        | .universeCode
        | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
        | .listCode | .optionCode | .eitherCode | .idCode | .equivCode
        | .cumulUpMarker | .uaToEquiv | .equivApply | .pathCompose
        | .idToEquiv | .oeqTrans | .equivCompose =>
            .listElim scrutineeWhnf nilBranch consBranch
    | .optionNone => .optionNone
    | .optionSome valueTerm => .optionSome valueTerm
    | .optionMatch scrutinee noneBranch someBranch =>
        let scrutineeWhnf := RawTerm.whnf fuel scrutinee
        match scrutineeWhnf.headCtor with
        | .optionNone =>
            RawTerm.whnf fuel noneBranch
        | .optionSome =>
            match RawTerm.optionSomeValue? scrutineeWhnf with
            | some valueTerm =>
                RawTerm.whnf fuel (.app someBranch valueTerm)
            | none =>
                .optionMatch scrutineeWhnf noneBranch someBranch
        | .var | .unit | .lam | .app | .pair | .fst | .snd
        | .boolTrue | .boolFalse | .boolElim
        | .natZero | .natSucc | .natElim | .natRec
        | .listNil | .listCons | .listElim
        | .optionMatch
        | .eitherInl | .eitherInr | .eitherMatch
        | .refl | .idJ | .modIntro | .modElim | .subsume
        | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
        | .pathLam | .pathApp | .glueIntro | .glueElim | .transp | .transpFill | .hcomp
        | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec
        | .equivIntro | .equivApp | .refineIntro | .refineElim
        | .recordIntro | .recordProj | .codataUnfold | .codataDest
        | .sessionSend | .sessionRecv | .effectPerform
        | .universeCode
        | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
        | .listCode | .optionCode | .eitherCode | .idCode | .equivCode
        | .cumulUpMarker | .uaToEquiv | .equivApply | .pathCompose
        | .idToEquiv | .oeqTrans | .equivCompose =>
            .optionMatch scrutineeWhnf noneBranch someBranch
    | .eitherInl valueTerm => .eitherInl valueTerm
    | .eitherInr valueTerm => .eitherInr valueTerm
    | .eitherMatch scrutinee leftBranch rightBranch =>
        let scrutineeWhnf := RawTerm.whnf fuel scrutinee
        match scrutineeWhnf.headCtor with
        | .eitherInl =>
            match RawTerm.eitherInlValue? scrutineeWhnf with
            | some valueTerm =>
                RawTerm.whnf fuel (.app leftBranch valueTerm)
            | none =>
                .eitherMatch scrutineeWhnf leftBranch rightBranch
        | .eitherInr =>
            match RawTerm.eitherInrValue? scrutineeWhnf with
            | some valueTerm =>
                RawTerm.whnf fuel (.app rightBranch valueTerm)
            | none =>
                .eitherMatch scrutineeWhnf leftBranch rightBranch
        | .var | .unit | .lam | .app | .pair | .fst | .snd
        | .boolTrue | .boolFalse | .boolElim
        | .natZero | .natSucc | .natElim | .natRec
        | .listNil | .listCons | .listElim
        | .optionNone | .optionSome | .optionMatch
        | .eitherMatch
        | .refl | .idJ | .modIntro | .modElim | .subsume
        | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
        | .pathLam | .pathApp | .glueIntro | .glueElim | .transp | .transpFill | .hcomp
        | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec
        | .equivIntro | .equivApp | .refineIntro | .refineElim
        | .recordIntro | .recordProj | .codataUnfold | .codataDest
        | .sessionSend | .sessionRecv | .effectPerform
        | .universeCode
        | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
        | .listCode | .optionCode | .eitherCode | .idCode | .equivCode
        | .cumulUpMarker | .uaToEquiv | .equivApply | .pathCompose
        | .idToEquiv | .oeqTrans | .equivCompose =>
            .eitherMatch scrutineeWhnf leftBranch rightBranch
    | .refl rawWitness => .refl rawWitness
    | .idJ baseCase witness =>
        let witnessWhnf := RawTerm.whnf fuel witness
        match witnessWhnf.headCtor with
        | .refl =>
            RawTerm.whnf fuel baseCase
        | .var | .unit | .lam | .app | .pair | .fst | .snd
        | .boolTrue | .boolFalse | .boolElim
        | .natZero | .natSucc | .natElim | .natRec
        | .listNil | .listCons | .listElim
        | .optionNone | .optionSome | .optionMatch
        | .eitherInl | .eitherInr | .eitherMatch
        | .idJ | .modIntro | .modElim | .subsume
        | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
        | .pathLam | .pathApp | .glueIntro | .glueElim | .transp | .transpFill | .hcomp
        | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec
        | .equivIntro | .equivApp | .refineIntro | .refineElim
        | .recordIntro | .recordProj | .codataUnfold | .codataDest
        | .sessionSend | .sessionRecv | .effectPerform
        | .universeCode
        | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
        | .listCode | .optionCode | .eitherCode | .idCode | .equivCode
        | .cumulUpMarker | .uaToEquiv | .equivApply | .pathCompose
        | .idToEquiv | .oeqTrans | .equivCompose =>
            .idJ baseCase witnessWhnf
    -- Modal: no reduction rules yet (Layer 6 will add iotaModal).
    | .modIntro innerTerm => .modIntro innerTerm
    | .modElim innerTerm => .modElim innerTerm
    | .subsume innerTerm => .subsume innerTerm
    -- D1.6: 27 new ctors are terminal at WHNF (no β/ι rules at raw
    -- level yet; cubical/HOTT/refine/record/codata/session/effect
    -- reductions land in D2.5–D2.7).
    | .interval0 => .interval0
    | .interval1 => .interval1
    | .intervalOpp intervalTerm => .intervalOpp intervalTerm
    | .intervalMeet leftInterval rightInterval => .intervalMeet leftInterval rightInterval
    | .intervalJoin leftInterval rightInterval => .intervalJoin leftInterval rightInterval
    | .pathLam body => .pathLam body
    | .pathApp pathTerm intervalArg => .pathApp pathTerm intervalArg
    | .glueIntro baseValue partialValue => .glueIntro baseValue partialValue
    | .glueElim gluedValue => .glueElim gluedValue
    | .transp pathTerm sourceTerm => .transp pathTerm sourceTerm
    | .transpFill pathTy currentInterval sourceTerm =>
        .transpFill pathTy currentInterval sourceTerm
    | .hcomp sidesTerm capTerm => .hcomp sidesTerm capTerm
    | .oeqRefl witnessTerm => .oeqRefl witnessTerm
    | .oeqJ baseCase witness => .oeqJ baseCase witness
    | .oeqFunext pointwiseEquality => .oeqFunext pointwiseEquality
    | .idStrictRefl witnessTerm => .idStrictRefl witnessTerm
    | .idStrictRec baseCase witness => .idStrictRec baseCase witness
    | .equivIntro forwardFn backwardFn => .equivIntro forwardFn backwardFn
    | .equivApp equivTerm argument => .equivApp equivTerm argument
    | .refineIntro rawValue predicateProof => .refineIntro rawValue predicateProof
    | .refineElim refinedValue => .refineElim refinedValue
    | .recordIntro firstField => .recordIntro firstField
    | .recordProj recordValue => .recordProj recordValue
    | .codataUnfold initialState transition => .codataUnfold initialState transition
    | .codataDest codataValue => .codataDest codataValue
    | .sessionSend channel payload => .sessionSend channel payload
    | .sessionRecv channel => .sessionRecv channel
    | .effectPerform operationTag arguments => .effectPerform operationTag arguments
    | .universeCode innerLevel => .universeCode innerLevel
    -- CUMUL-2.1 per-shape type codes (canonical: no β/ι rule fires).
    | .arrowCode domainCode codomainCode => .arrowCode domainCode codomainCode
    | .piTyCode domainCode codomainCode => .piTyCode domainCode codomainCode
    | .sigmaTyCode domainCode codomainCode => .sigmaTyCode domainCode codomainCode
    | .productCode firstCode secondCode => .productCode firstCode secondCode
    | .sumCode leftCode rightCode => .sumCode leftCode rightCode
    | .listCode elementCode => .listCode elementCode
    | .optionCode elementCode => .optionCode elementCode
    | .eitherCode leftCode rightCode => .eitherCode leftCode rightCode
    | .idCode typeCode leftRaw rightRaw => .idCode typeCode leftRaw rightRaw
    | .equivCode leftTypeCode rightTypeCode => .equivCode leftTypeCode rightTypeCode
    -- CUMUL-2.6: cumulUpMarker — value form, no β/ι.
    | .cumulUpMarker innerCodeRaw => .cumulUpMarker innerCodeRaw
    -- D3.6-P1: uaToEquiv — value form, no β/ι (S1+ adds the actual rule).
    | .uaToEquiv proofRaw => .uaToEquiv proofRaw
    -- D3.6-P2: equivApply — value form, no β/ι (S1+ adds the actual rule).
    | .equivApply equivRaw argRaw => .equivApply equivRaw argRaw
    -- D3.6-S3: pathCompose — value form at WHNF; the actual β rule
    -- `transp (pathCompose left right) source ⟶ ...` fires through the
    -- transp arm of `whnf` (raw-only confluence-closure mechanism).
    | .pathCompose leftPathRaw rightPathRaw =>
        .pathCompose leftPathRaw rightPathRaw
    -- D3.6-S4: idToEquiv — value form at WHNF; the actual β rule
    -- `idToEquiv (refl _) ⟶ equivIntro id id` fires through later
    -- whnf engine integration (raw-only confluence-closure mechanism).
    | .idToEquiv proofRaw => .idToEquiv proofRaw
    -- D3.6-S5: oeqTrans — value form at WHNF; the actual β rule
    -- `idToEquiv (oeqTrans first second) ⟶ equivCompose ...` fires
    -- through cdIdToEquivCase, not inside oeqTrans itself.
    | .oeqTrans firstProof secondProof => .oeqTrans firstProof secondProof
    -- D3.6-S5: equivCompose — value form at WHNF; the contractum
    -- target of the headline `idToEquivCompose` β rule.
    | .equivCompose firstEquiv secondEquiv => .equivCompose firstEquiv secondEquiv

end LeanFX2

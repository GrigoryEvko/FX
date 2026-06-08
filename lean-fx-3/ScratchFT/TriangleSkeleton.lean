import FX1Poly.Core.CompleteDevelopment
import FX1Poly.Core.ParallelReduction
import FX1Poly.Core.ParStepSubstPointwise
import FX1Poly.Core.RawTermSubst0Commute

namespace FX1Poly.Core

open Foundation

-- Skeleton: validate the triangle's OUTER beta arm + cong (none + some-beta). Other arms sorry.
theorem triangle_probe {scope0 : Nat} {a0 b0 : RawTerm scope0} (step0 : ParStep a0 b0) :
    ParStep b0 (RawTerm.completeDevelopment a0) :=
  ParStep.rec
    (motive_1 := fun {scope} a b _ => ParStep b (RawTerm.completeDevelopment a))
    (motive_2 := fun {binderShifts} {scope} cs cs' _ =>
      ParStepChildren cs' (RawTerm.completeDevelopmentChildren cs))
    -- beta OUTER
    (fun {scope} {body body' arg arg'} _bodyStep _argStep ihBody ihArg =>
        ParStep.subst0_diagonal ihBody ihArg)
    -- cong
    (fun {scope} gen payload {children children'} childrenStep ih => by
        show ParStep (.mkGen gen payload children')
          (RawTerm.fireRootRedexOrSelfGated gen payload children
            (RawTerm.completeDevelopmentChildren children))
        unfold RawTerm.fireRootRedexOrSelfGated
        cases hfire : RawTerm.fireRootRedex gen payload children with
        | none => exact ParStep.cong gen payload ih
        | some reduct =>
            by_cases hApp : gen = .gen_app
            · subst hApp
              cases childrenStep with
              | cons headStep tailStep => cases tailStep with
                | cons argStep tailNil => cases tailNil with
                  | nil =>
                      cases ih with
                      | cons ihHead ihTail => cases ihTail with
                        | cons ihArg ihNil => cases ihNil with
                          | nil =>
                              -- headStep : ParStep func func', argStep : ParStep arg arg'
                              -- ihHead : ParStep func' (cd func), ihArg : ParStep arg' (cd arg)
                              -- learn func = lam body
                              rename_i func _func' _arg _arg'
                              cases func with
                              | mkGen ig ip ic =>
                                  by_cases hLam : ig = .gen_lam
                                  · subst hLam
                                    cases ic with | childCons body icNil => cases icNil with
                                      | childNil =>
                                          -- headStep : ParStep (lam body) func'; cases to learn func' = lam bodyTgt'
                                          cases headStep with
                                          | cong _ _ csH => cases csH with
                                            | cons _bodyToTgt rH => cases rH with
                                              | nil =>
                                                  -- now func' = lam bodyTgt'; ihHead : ParStep (lam bodyTgt') (lam (cd body))
                                                  cases ihHead with
                                                  | cong _ _ csI => cases csI with
                                                    | cons bodyTgtToDev rI => cases rI with
                                                      | nil => exact ParStep.beta bodyTgtToDev ihArg
                                  · have key : RawTerm.fireRootRedex .gen_app payload
                                        (.childCons (.mkGen ig ip ic) (.childCons _arg .childNil)) = none :=
                                      dif_neg hLam
                                    rw [key] at hfire; nomatch hfire
            · sorry)
    -- all other iota OUTER arms: sorry
    (fun {scope} {thenBranch thenBranch' elseBranch} _step ih => by exact ih)
    (fun {scope} {thenBranch elseBranch elseBranch'} _step ih => by exact ih)
    (fun {scope} {firstValue firstValue' secondValue} _step ih => by exact ih)
    (fun {scope} {firstValue secondValue secondValue'} _step ih => by exact ih)
    (fun {scope} {zeroBranch zeroBranch' succBranch} _step ih => by exact ih)
    (fun {scope} {zeroBranch zeroBranch' succBranch} _step ih => by exact ih)
    (fun {scope} {nilBranch nilBranch' consBranch} _step ih => by exact ih)
    (fun {scope} {noneBranch noneBranch' someBranch} _step ih => by exact ih)
    (fun {scope} {value value' noneBranch someBranch someBranch'} _s _v ihSome ihVal => by sorry)
    (fun {scope} {value value' leftBranch leftBranch' rightBranch} _s _v ihL ihVal => by sorry)
    (fun {scope} {value value' leftBranch rightBranch rightBranch'} _s _v ihR ihVal => by sorry)
    (fun {scope} {predecessor predecessor' zeroBranch zeroBranch' succBranch succBranch'} _ _ _ ihP ihZ ihS => by sorry)
    (fun {scope} {predecessor predecessor' zeroBranch zeroBranch' succBranch succBranch'} _ _ _ ihP ihZ ihS => by sorry)
    (fun {scope} {headVal headVal' tailVal tailVal' nilBranch nilBranch' consBranch consBranch'} _ _ _ _ ihH ihT ihN ihC => by sorry)
    (fun {scope} {baseCase baseCase' rawWitness} _step ih => by exact ih)
    (fun {scope} {baseCase baseCase' rawWitness} _step ih => by exact ih)
    -- ParStepChildren arms
    (fun {scope} => ParStepChildren.nil)
    (fun {scope shift restShifts} {childHead childHead' childTail childTail'} _hs _ts ihHead ihTail =>
        ParStepChildren.cons ihHead ihTail)
    step0

end FX1Poly.Core

import LeanFX2.Confluence.RawDiamond

/-! # Confluence/RawParStarCong — parStar congruence rules

`RawStep.parStar` (the reflexive-transitive closure of `RawStep.par`)
is closed under the same congruence rules as `RawStep.par`: applying
parallel reduction sub-term-by-sub-term and chaining yields a chain
on the whole term.

This file derives those congruence rules.  Each `parStar.<ctor>`
rule is proved by induction on its parStar argument(s), using
`RawStep.par.<ctor>` as the per-step lifter and parStar.refl /
trans / append for chaining.

## Use

`RawTerm.whnf_reaches` (in `Algo/RawWHNFCorrect`) inducts on the
input term, reducing each sub-term first via the IH (giving a
parStar chain), then assembling the whole-term chain via these
cong rules.
-/

namespace LeanFX2

variable {scope : Nat}

/-- parStar respects `lam` body. -/
theorem RawStep.parStar.lam
    {sourceBody targetBody : RawTerm (scope + 1)}
    (chain : RawStep.parStar sourceBody targetBody) :
    RawStep.parStar (.lam sourceBody) (.lam targetBody) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.lam firstStep) restIH

/-- parStar respects `app` on the function side. -/
theorem RawStep.parStar.appLeft
    {sourceFunction targetFunction : RawTerm scope}
    (argument : RawTerm scope)
    (chain : RawStep.parStar sourceFunction targetFunction) :
    RawStep.parStar (.app sourceFunction argument)
                    (.app targetFunction argument) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.app firstStep (.refl _)) restIH

/-- parStar respects `app` on the argument side. -/
theorem RawStep.parStar.appRight
    (functionTerm : RawTerm scope)
    {sourceArgument targetArgument : RawTerm scope}
    (chain : RawStep.parStar sourceArgument targetArgument) :
    RawStep.parStar (.app functionTerm sourceArgument)
                    (.app functionTerm targetArgument) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.app (.refl _) firstStep) restIH

/-- parStar respects `app` on both sides. -/
theorem RawStep.parStar.app
    {sourceFunction targetFunction : RawTerm scope}
    {sourceArgument targetArgument : RawTerm scope}
    (functionChain : RawStep.parStar sourceFunction targetFunction)
    (argumentChain : RawStep.parStar sourceArgument targetArgument) :
    RawStep.parStar (.app sourceFunction sourceArgument)
                    (.app targetFunction targetArgument) :=
  RawStep.parStar.append
    (RawStep.parStar.appLeft sourceArgument functionChain)
    (RawStep.parStar.appRight targetFunction argumentChain)

/-- parStar respects `pair` on the first component. -/
theorem RawStep.parStar.pairLeft
    {sourceFirst targetFirst : RawTerm scope}
    (secondValue : RawTerm scope)
    (chain : RawStep.parStar sourceFirst targetFirst) :
    RawStep.parStar (.pair sourceFirst secondValue)
                    (.pair targetFirst secondValue) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.pair firstStep (.refl _)) restIH

/-- parStar respects `pair` on the second component. -/
theorem RawStep.parStar.pairRight
    (firstValue : RawTerm scope)
    {sourceSecond targetSecond : RawTerm scope}
    (chain : RawStep.parStar sourceSecond targetSecond) :
    RawStep.parStar (.pair firstValue sourceSecond)
                    (.pair firstValue targetSecond) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.pair (.refl _) firstStep) restIH

/-- parStar respects `pair` on both components. -/
theorem RawStep.parStar.pair
    {sourceFirst targetFirst sourceSecond targetSecond : RawTerm scope}
    (firstChain : RawStep.parStar sourceFirst targetFirst)
    (secondChain : RawStep.parStar sourceSecond targetSecond) :
    RawStep.parStar (.pair sourceFirst sourceSecond)
                    (.pair targetFirst targetSecond) :=
  RawStep.parStar.append
    (RawStep.parStar.pairLeft sourceSecond firstChain)
    (RawStep.parStar.pairRight targetFirst secondChain)

/-- parStar respects `fst`. -/
theorem RawStep.parStar.fst
    {sourcePair targetPair : RawTerm scope}
    (chain : RawStep.parStar sourcePair targetPair) :
    RawStep.parStar (.fst sourcePair) (.fst targetPair) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.fst firstStep) restIH

/-- parStar respects `snd`. -/
theorem RawStep.parStar.snd
    {sourcePair targetPair : RawTerm scope}
    (chain : RawStep.parStar sourcePair targetPair) :
    RawStep.parStar (.snd sourcePair) (.snd targetPair) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.snd firstStep) restIH

/-- parStar respects `boolElim` on the scrutinee. -/
theorem RawStep.parStar.boolElimScrutinee
    {sourceScrutinee targetScrutinee : RawTerm scope}
    (thenBranch elseBranch : RawTerm scope)
    (chain : RawStep.parStar sourceScrutinee targetScrutinee) :
    RawStep.parStar (.boolElim sourceScrutinee thenBranch elseBranch)
                    (.boolElim targetScrutinee thenBranch elseBranch) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans
        (RawStep.par.boolElim firstStep (.refl _) (.refl _)) restIH

/-- parStar respects `natSucc`. -/
theorem RawStep.parStar.natSucc
    {sourcePred targetPred : RawTerm scope}
    (chain : RawStep.parStar sourcePred targetPred) :
    RawStep.parStar (.natSucc sourcePred) (.natSucc targetPred) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.natSucc firstStep) restIH

/-- parStar respects `natElim` on the scrutinee. -/
theorem RawStep.parStar.natElimScrutinee
    {sourceScrutinee targetScrutinee : RawTerm scope}
    (zeroBranch succBranch : RawTerm scope)
    (chain : RawStep.parStar sourceScrutinee targetScrutinee) :
    RawStep.parStar (.natElim sourceScrutinee zeroBranch succBranch)
                    (.natElim targetScrutinee zeroBranch succBranch) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans
        (RawStep.par.natElim firstStep (.refl _) (.refl _)) restIH

/-- parStar respects `natRec` on the scrutinee. -/
theorem RawStep.parStar.natRecScrutinee
    {sourceScrutinee targetScrutinee : RawTerm scope}
    (zeroBranch succBranch : RawTerm scope)
    (chain : RawStep.parStar sourceScrutinee targetScrutinee) :
    RawStep.parStar (.natRec sourceScrutinee zeroBranch succBranch)
                    (.natRec targetScrutinee zeroBranch succBranch) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans
        (RawStep.par.natRec firstStep (.refl _) (.refl _)) restIH

/-- parStar respects `listCons` on the head. -/
theorem RawStep.parStar.listConsHead
    {sourceHead targetHead : RawTerm scope}
    (tailTerm : RawTerm scope)
    (chain : RawStep.parStar sourceHead targetHead) :
    RawStep.parStar (.listCons sourceHead tailTerm)
                    (.listCons targetHead tailTerm) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.listCons firstStep (.refl _)) restIH

/-- parStar respects `listCons` on the tail. -/
theorem RawStep.parStar.listConsTail
    (headTerm : RawTerm scope)
    {sourceTail targetTail : RawTerm scope}
    (chain : RawStep.parStar sourceTail targetTail) :
    RawStep.parStar (.listCons headTerm sourceTail)
                    (.listCons headTerm targetTail) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.listCons (.refl _) firstStep) restIH

/-- parStar respects `listElim` on the scrutinee. -/
theorem RawStep.parStar.listElimScrutinee
    {sourceScrutinee targetScrutinee : RawTerm scope}
    (nilBranch consBranch : RawTerm scope)
    (chain : RawStep.parStar sourceScrutinee targetScrutinee) :
    RawStep.parStar (.listElim sourceScrutinee nilBranch consBranch)
                    (.listElim targetScrutinee nilBranch consBranch) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans
        (RawStep.par.listElim firstStep (.refl _) (.refl _)) restIH

/-- parStar respects `optionSome`. -/
theorem RawStep.parStar.optionSome
    {sourceValue targetValue : RawTerm scope}
    (chain : RawStep.parStar sourceValue targetValue) :
    RawStep.parStar (.optionSome sourceValue) (.optionSome targetValue) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.optionSome firstStep) restIH

/-- parStar respects `optionMatch` on the scrutinee. -/
theorem RawStep.parStar.optionMatchScrutinee
    {sourceScrutinee targetScrutinee : RawTerm scope}
    (noneBranch someBranch : RawTerm scope)
    (chain : RawStep.parStar sourceScrutinee targetScrutinee) :
    RawStep.parStar (.optionMatch sourceScrutinee noneBranch someBranch)
                    (.optionMatch targetScrutinee noneBranch someBranch) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans
        (RawStep.par.optionMatch firstStep (.refl _) (.refl _)) restIH

/-- parStar respects `eitherInl`. -/
theorem RawStep.parStar.eitherInl
    {sourceValue targetValue : RawTerm scope}
    (chain : RawStep.parStar sourceValue targetValue) :
    RawStep.parStar (.eitherInl sourceValue) (.eitherInl targetValue) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.eitherInl firstStep) restIH

/-- parStar respects `eitherInr`. -/
theorem RawStep.parStar.eitherInr
    {sourceValue targetValue : RawTerm scope}
    (chain : RawStep.parStar sourceValue targetValue) :
    RawStep.parStar (.eitherInr sourceValue) (.eitherInr targetValue) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.eitherInr firstStep) restIH

/-- parStar respects `eitherMatch` on the scrutinee. -/
theorem RawStep.parStar.eitherMatchScrutinee
    {sourceScrutinee targetScrutinee : RawTerm scope}
    (leftBranch rightBranch : RawTerm scope)
    (chain : RawStep.parStar sourceScrutinee targetScrutinee) :
    RawStep.parStar (.eitherMatch sourceScrutinee leftBranch rightBranch)
                    (.eitherMatch targetScrutinee leftBranch rightBranch) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans
        (RawStep.par.eitherMatch firstStep (.refl _) (.refl _)) restIH

/-- parStar respects `refl` (via reflCong on the witness). -/
theorem RawStep.parStar.reflWitness
    {sourceWitness targetWitness : RawTerm scope}
    (chain : RawStep.parStar sourceWitness targetWitness) :
    RawStep.parStar (.refl sourceWitness) (.refl targetWitness) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.reflCong firstStep) restIH

/-- parStar respects `idJ` on the witness. -/
theorem RawStep.parStar.idJWitness
    (baseCase : RawTerm scope)
    {sourceWitness targetWitness : RawTerm scope}
    (chain : RawStep.parStar sourceWitness targetWitness) :
    RawStep.parStar (.idJ baseCase sourceWitness)
                    (.idJ baseCase targetWitness) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.idJ (.refl _) firstStep) restIH

/-- parStar respects `modIntro`. -/
theorem RawStep.parStar.modIntro
    {sourceInner targetInner : RawTerm scope}
    (chain : RawStep.parStar sourceInner targetInner) :
    RawStep.parStar (.modIntro sourceInner) (.modIntro targetInner) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.modIntro firstStep) restIH

/-- parStar respects `modElim`. -/
theorem RawStep.parStar.modElim
    {sourceInner targetInner : RawTerm scope}
    (chain : RawStep.parStar sourceInner targetInner) :
    RawStep.parStar (.modElim sourceInner) (.modElim targetInner) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.modElim firstStep) restIH

/-- parStar respects `subsume`. -/
theorem RawStep.parStar.subsume
    {sourceInner targetInner : RawTerm scope}
    (chain : RawStep.parStar sourceInner targetInner) :
    RawStep.parStar (.subsume sourceInner) (.subsume targetInner) := by
  induction chain with
  | refl _ => exact .refl _
  | trans firstStep _ restIH =>
      exact .trans (RawStep.par.subsume firstStep) restIH

end LeanFX2

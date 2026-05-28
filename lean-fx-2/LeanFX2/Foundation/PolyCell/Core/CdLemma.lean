import LeanFX2.Foundation.PolyCell.Core.CriticalPairs

/-! # Foundation/PolyCell/Core/CdLemma
    — M7 confluence join API

This file starts M7 (`cd_lemma`) by pinning the exact existential join
shape that the generic proof must produce for two one-step reductions from
the same source.

M6 supplies proof-relevant `LocalDiamond` fillers for the finite substantive
critical-pair families.  The first M7 bridge is intentionally small: every
`LocalDiamond` erases to the `StepPairJoin` existential that the eventual
generic `cd_lemma` returns.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- The local Church-Rosser join shape for two one-step reductions from the
same source.

The step witnesses are parameters because the eventual dispatcher case-splits
on them, but the resulting proposition is exactly the shared reduct plus the
two `StepStar` joining chains. -/
def StepPairJoin {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (_leftStep : Step sourceTerm leftReduct)
    (_rightStep : Step sourceTerm rightReduct) : Prop :=
  ∃ commonReduct : RawTerm scope,
    StepStar leftReduct commonReduct ∧
      StepStar rightReduct commonReduct

/-- The target statement of M7, as a reusable Prop alias.

The theorem named `cd_lemma` will inhabit this statement once the proof
dispatch over `Step`/`StepChildren` is built. -/
def CdLemmaStatement : Prop :=
  ∀ {scope : Nat} {sourceTerm leftReduct rightReduct : RawTerm scope},
    (leftStep : Step sourceTerm leftReduct) →
    (rightStep : Step sourceTerm rightReduct) →
    StepPairJoin leftStep rightStep

namespace StepPairJoin

/-- Same-reduct closure for the M7 join target.

When the two one-step reducts are equal, the local join is the shared reduct
itself and both joining chains are reflexive.  This is the direct
`StepPairJoin` version of `LocalDiamond.sameReductOfEq`, used by the eventual
`cd_lemma` dispatcher for same-redex cases. -/
theorem ofReductsEqual {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    {leftStep : Step sourceTerm leftReduct}
    {rightStep : Step sourceTerm rightReduct}
    (reductsEqual : leftReduct = rightReduct) :
    StepPairJoin leftStep rightStep := by
  cases reductsEqual
  exact ⟨leftReduct, StepStar.refl _, StepStar.refl _⟩

/-- A step trivially joins with itself. -/
theorem sameStep {scope : Nat} {sourceTerm targetTerm : RawTerm scope}
    (sameStepWitness : Step sourceTerm targetTerm) :
    StepPairJoin sameStepWitness sameStepWitness :=
  ofReductsEqual rfl

/-- Reverse the two branches of a local join.

This is the `StepPairJoin`-level orientation bridge used when M6 exposes a
diamond in the opposite root/congruence order from the arbitrary branching that
`cd_lemma` receives. -/
theorem swap {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    {leftStep : Step sourceTerm leftReduct}
    {rightStep : Step sourceTerm rightReduct} :
    StepPairJoin leftStep rightStep →
      StepPairJoin rightStep leftStep :=
  fun join =>
    Exists.elim join
      (fun commonReduct chains =>
        ⟨commonReduct, chains.2, chains.1⟩)

end StepPairJoin

namespace LocalStepBranching

/-- Package the arbitrary one-step pair received by `cd_lemma` as a concrete
local branching.

The M7 dispatcher works on `LocalStepBranching`; this constructor is the
lossless ingress from the theorem's raw `Step` arguments into that packaged
shape. -/
def fromSteps {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step sourceTerm leftReduct)
    (rightStep : Step sourceTerm rightReduct) :
    LocalStepBranching (scope := scope) where
  source := sourceTerm
  leftReduct := leftReduct
  rightReduct := rightReduct
  leftStep := leftStep
  rightStep := rightStep

/-- Packaging commutes with swapping the two one-step sides. -/
theorem fromSteps_swap {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    (leftStep : Step sourceTerm leftReduct)
    (rightStep : Step sourceTerm rightReduct) :
    (fromSteps leftStep rightStep).swap =
      fromSteps rightStep leftStep := rfl

/-- The `StepPairJoin` proposition packaged over an M6 local branching. -/
def HasJoin {scope : Nat}
    (branching : LocalStepBranching (scope := scope)) : Prop :=
  StepPairJoin branching.leftStep branching.rightStep

/-- Two local branchings whose source terms cannot be definitionally the same.

This is the M7-facing form of the M6 mutually-exclusive root/root facts:
same-generator root rules such as `boolTrue` versus `boolFalse` do not produce
a join obligation, because the shared-source branching itself is impossible. -/
def SourcesDisjoint {scope : Nat}
    (leftBranching rightBranching : LocalStepBranching (scope := scope)) :
    Prop :=
  Not (leftBranching.source = rightBranching.source)

/-- A source-disjoint pair of local branchings cannot be viewed as sharing the
same source. -/
theorem sourcesDisjoint_noSharedSource {scope : Nat}
    {leftBranching rightBranching : LocalStepBranching (scope := scope)}
    (branchingsHaveDisjointSources :
      SourcesDisjoint leftBranching rightBranching)
    (sourcesEqual : leftBranching.source = rightBranching.source) :
    False :=
  branchingsHaveDisjointSources sourcesEqual

/-- `fromSteps` preserves the `StepPairJoin` goal definitionally. -/
theorem fromSteps_hasJoin {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    {leftStep : Step sourceTerm leftReduct}
    {rightStep : Step sourceTerm rightReduct} :
    (fromSteps leftStep rightStep).HasJoin →
      StepPairJoin leftStep rightStep :=
  fun join => join

/-- A join for arbitrary theorem inputs can be viewed as a join for their
packaged local branching. -/
theorem hasJoin_fromSteps {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    {leftStep : Step sourceTerm leftReduct}
    {rightStep : Step sourceTerm rightReduct} :
    StepPairJoin leftStep rightStep →
      (fromSteps leftStep rightStep).HasJoin :=
  fun join => join

/-- Same-reduct closure packaged over a concrete local branching. -/
theorem hasJoin_ofReductsEqual {scope : Nat}
    (branching : LocalStepBranching (scope := scope))
    (reductsEqual : branching.leftReduct = branching.rightReduct) :
    branching.HasJoin :=
  StepPairJoin.ofReductsEqual reductsEqual

/-- Reverse a packaged branching join along `LocalStepBranching.swap`. -/
theorem hasJoin_swap {scope : Nat}
    {branching : LocalStepBranching (scope := scope)} :
    branching.HasJoin → branching.swap.HasJoin :=
  StepPairJoin.swap

end LocalStepBranching

namespace StepPairJoin

/-- Consume an M6 diamond for the local branching induced by arbitrary
`cd_lemma` inputs.

This is the direct bridge from the eventual theorem's raw `Step` arguments to
the proof-relevant M6 filler templates. -/
theorem ofLocalDiamondFromSteps {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    {leftStep : Step sourceTerm leftReduct}
    {rightStep : Step sourceTerm rightReduct}
    (diamond :
      LocalDiamond (LocalStepBranching.fromSteps leftStep rightStep)) :
    StepPairJoin leftStep rightStep :=
  ⟨diamond.commonReduct, diamond.leftChain, diamond.rightChain⟩

/-- Consume an M6 diamond in the opposite orientation from arbitrary
`cd_lemma` inputs. -/
theorem ofLocalDiamondFromSteps_swap {scope : Nat}
    {sourceTerm leftReduct rightReduct : RawTerm scope}
    {leftStep : Step sourceTerm leftReduct}
    {rightStep : Step sourceTerm rightReduct}
    (diamond :
      LocalDiamond (LocalStepBranching.fromSteps rightStep leftStep)) :
    StepPairJoin leftStep rightStep :=
  StepPairJoin.swap
    ⟨diamond.commonReduct, diamond.leftChain, diamond.rightChain⟩

end StepPairJoin

namespace LocalDiamond

/-- Every M6 local diamond supplies the existential join shape M7 needs. -/
theorem hasJoin {scope : Nat}
    {branching : LocalStepBranching (scope := scope)}
    (diamond : LocalDiamond branching) :
    branching.HasJoin :=
  ⟨diamond.commonReduct, diamond.leftChain, diamond.rightChain⟩

/-- Same bridge stated directly against the `StepPairJoin` alias. -/
theorem toStepPairJoin {scope : Nat}
    {branching : LocalStepBranching (scope := scope)}
    (diamond : LocalDiamond branching) :
    StepPairJoin branching.leftStep branching.rightStep :=
  diamond.hasJoin

/-- A local diamond also supplies the join for the swapped branching. -/
theorem toStepPairJoin_swap {scope : Nat}
    {branching : LocalStepBranching (scope := scope)}
    (diamond : LocalDiamond branching) :
    StepPairJoin branching.swap.leftStep branching.swap.rightStep :=
  StepPairJoin.swap diamond.toStepPairJoin

end LocalDiamond

namespace LocalStepBranching

/-- Resolver arm for the beta/beta root-root branching. -/
theorem betaBeta_hasJoin {scope : Nat}
    (body : RawTerm (scope + 1)) (arg : RawTerm scope) :
    (betaBeta body arg).HasJoin :=
  (LocalDiamond.betaBeta body arg).hasJoin

/-- Resolver arm for beta competing with congruence in the function child. -/
theorem betaFunctionCong_hasJoin {scope : Nat}
    {body updatedBody : RawTerm (scope + 1)}
    (argument : RawTerm scope) (bodyStep : Step body updatedBody) :
    (betaFunctionCong argument bodyStep).HasJoin :=
  (LocalDiamond.betaFunctionCong argument bodyStep).hasJoin

/-- Resolver arm for the reverse orientation of beta/function congruence. -/
theorem betaFunctionCongReverse_hasJoin {scope : Nat}
    {body updatedBody : RawTerm (scope + 1)}
    (argument : RawTerm scope) (bodyStep : Step body updatedBody) :
    (betaFunctionCong argument bodyStep).swap.HasJoin :=
  (LocalDiamond.betaFunctionCongReverse argument bodyStep).hasJoin

/-- Resolver arm for beta competing with congruence in the argument child. -/
theorem betaArgumentCong_hasJoin {scope : Nat}
    (body : RawTerm (scope + 1))
    {argument updatedArgument : RawTerm scope}
    (argumentStep : Step argument updatedArgument) :
    (betaArgumentCong body argumentStep).HasJoin :=
  (LocalDiamond.betaArgumentCong body argumentStep).hasJoin

/-- Resolver arm for the reverse orientation of beta/argument congruence. -/
theorem betaArgumentCongReverse_hasJoin {scope : Nat}
    (body : RawTerm (scope + 1))
    {argument updatedArgument : RawTerm scope}
    (argumentStep : Step argument updatedArgument) :
    (betaArgumentCong body argumentStep).swap.HasJoin :=
  (LocalDiamond.betaArgumentCongReverse body argumentStep).hasJoin

/-- Resolver arm for same-root `boolTrue` iota branchings. -/
theorem iotaBoolTrueSameRoot_hasJoin {scope : Nat}
    (thenBranch elseBranch : RawTerm scope) :
    (iotaBoolTrueSameRoot thenBranch elseBranch).HasJoin :=
  (LocalDiamond.iotaBoolTrueSameRoot thenBranch elseBranch).hasJoin

/-- Resolver arm for same-root `boolFalse` iota branchings. -/
theorem iotaBoolFalseSameRoot_hasJoin {scope : Nat}
    (thenBranch elseBranch : RawTerm scope) :
    (iotaBoolFalseSameRoot thenBranch elseBranch).HasJoin :=
  (LocalDiamond.iotaBoolFalseSameRoot thenBranch elseBranch).hasJoin

/-- Resolver arm for same-root first-projection iota branchings. -/
theorem iotaFstPairSameRoot_hasJoin {scope : Nat}
    (firstValue secondValue : RawTerm scope) :
    (iotaFstPairSameRoot firstValue secondValue).HasJoin :=
  (LocalDiamond.iotaFstPairSameRoot firstValue secondValue).hasJoin

/-- Resolver arm for same-root second-projection iota branchings. -/
theorem iotaSndPairSameRoot_hasJoin {scope : Nat}
    (firstValue secondValue : RawTerm scope) :
    (iotaSndPairSameRoot firstValue secondValue).HasJoin :=
  (LocalDiamond.iotaSndPairSameRoot firstValue secondValue).hasJoin

/-- Resolver arm for same-root `natElim` zero-case branchings. -/
theorem iotaNatElimZeroSameRoot_hasJoin {scope : Nat}
    (zeroBranch succBranch : RawTerm scope) :
    (iotaNatElimZeroSameRoot zeroBranch succBranch).HasJoin :=
  (LocalDiamond.iotaNatElimZeroSameRoot zeroBranch succBranch).hasJoin

/-- Resolver arm for same-root `natRec` zero-case branchings. -/
theorem iotaNatRecZeroSameRoot_hasJoin {scope : Nat}
    (zeroBranch succBranch : RawTerm scope) :
    (iotaNatRecZeroSameRoot zeroBranch succBranch).HasJoin :=
  (LocalDiamond.iotaNatRecZeroSameRoot zeroBranch succBranch).hasJoin

/-- Resolver arm for same-root `listElim` nil-case branchings. -/
theorem iotaListElimNilSameRoot_hasJoin {scope : Nat}
    (nilBranch consBranch : RawTerm scope) :
    (iotaListElimNilSameRoot nilBranch consBranch).HasJoin :=
  (LocalDiamond.iotaListElimNilSameRoot nilBranch consBranch).hasJoin

/-- Resolver arm for same-root `optionMatch` none-case branchings. -/
theorem iotaOptionMatchNoneSameRoot_hasJoin {scope : Nat}
    (noneBranch someBranch : RawTerm scope) :
    (iotaOptionMatchNoneSameRoot noneBranch someBranch).HasJoin :=
  (LocalDiamond.iotaOptionMatchNoneSameRoot noneBranch someBranch).hasJoin

/-- Resolver arm for same-root `idJ` refl-case branchings. -/
theorem iotaIdJReflSameRoot_hasJoin {scope : Nat}
    (baseCase rawWitness : RawTerm scope) :
    (iotaIdJReflSameRoot baseCase rawWitness).HasJoin :=
  (LocalDiamond.iotaIdJReflSameRoot baseCase rawWitness).hasJoin

/-- Resolver arm for same-root `idStrictRec` refl-case branchings. -/
theorem iotaIdStrictRecReflSameRoot_hasJoin {scope : Nat}
    (baseCase rawWitness : RawTerm scope) :
    (iotaIdStrictRecReflSameRoot baseCase rawWitness).HasJoin :=
  (LocalDiamond.iotaIdStrictRecReflSameRoot baseCase rawWitness).hasJoin

/-- Resolver arm for same-root `optionMatch` some-case branchings. -/
theorem iotaOptionMatchSomeSameRoot_hasJoin {scope : Nat}
    (value noneBranch someBranch : RawTerm scope) :
    (iotaOptionMatchSomeSameRoot value noneBranch someBranch).HasJoin :=
  (LocalDiamond.iotaOptionMatchSomeSameRoot
    value noneBranch someBranch).hasJoin

/-- Resolver arm for same-root `eitherMatch` inl-case branchings. -/
theorem iotaEitherMatchInlSameRoot_hasJoin {scope : Nat}
    (value leftBranch rightBranch : RawTerm scope) :
    (iotaEitherMatchInlSameRoot value leftBranch rightBranch).HasJoin :=
  (LocalDiamond.iotaEitherMatchInlSameRoot
    value leftBranch rightBranch).hasJoin

/-- Resolver arm for same-root `eitherMatch` inr-case branchings. -/
theorem iotaEitherMatchInrSameRoot_hasJoin {scope : Nat}
    (value leftBranch rightBranch : RawTerm scope) :
    (iotaEitherMatchInrSameRoot value leftBranch rightBranch).HasJoin :=
  (LocalDiamond.iotaEitherMatchInrSameRoot
    value leftBranch rightBranch).hasJoin

/-- Resolver arm for same-root `natElim` succ-case branchings. -/
theorem iotaNatElimSuccSameRoot_hasJoin {scope : Nat}
    (predecessor zeroBranch succBranch : RawTerm scope) :
    (iotaNatElimSuccSameRoot predecessor zeroBranch succBranch).HasJoin :=
  (LocalDiamond.iotaNatElimSuccSameRoot
    predecessor zeroBranch succBranch).hasJoin

/-- Resolver arm for same-root `natRec` succ-case branchings. -/
theorem iotaNatRecSuccSameRoot_hasJoin {scope : Nat}
    (predecessor zeroBranch succBranch : RawTerm scope) :
    (iotaNatRecSuccSameRoot predecessor zeroBranch succBranch).HasJoin :=
  (LocalDiamond.iotaNatRecSuccSameRoot
    predecessor zeroBranch succBranch).hasJoin

/-- Resolver arm for same-root `listElim` cons-case branchings. -/
theorem iotaListElimConsSameRoot_hasJoin {scope : Nat}
    (headValue tailValue nilBranch consBranch : RawTerm scope) :
    (iotaListElimConsSameRoot
      headValue tailValue nilBranch consBranch).HasJoin :=
  (LocalDiamond.iotaListElimConsSameRoot
    headValue tailValue nilBranch consBranch).hasJoin

/-- Resolver arm for `boolTrue` iota competing with selected then-branch congruence. -/
theorem iotaBoolTrueThenCong_hasJoin {scope : Nat}
    {thenBranch steppedThenBranch elseBranch : RawTerm scope}
    (thenStep : Step thenBranch steppedThenBranch) :
    (iotaBoolTrueThenCong (elseBranch := elseBranch) thenStep).HasJoin :=
  (LocalDiamond.iotaBoolTrueThenCong
    (elseBranch := elseBranch) thenStep).hasJoin

/-- Resolver arm for `boolTrue` iota competing with discarded else-branch congruence. -/
theorem iotaBoolTrueElseCong_hasJoin {scope : Nat}
    {thenBranch elseBranch steppedElseBranch : RawTerm scope}
    (elseStep : Step elseBranch steppedElseBranch) :
    (iotaBoolTrueElseCong (thenBranch := thenBranch) elseStep).HasJoin :=
  (LocalDiamond.iotaBoolTrueElseCong
    (thenBranch := thenBranch) elseStep).hasJoin

/-- Resolver arm for `boolFalse` iota competing with discarded then-branch congruence. -/
theorem iotaBoolFalseThenCong_hasJoin {scope : Nat}
    {thenBranch steppedThenBranch elseBranch : RawTerm scope}
    (thenStep : Step thenBranch steppedThenBranch) :
    (iotaBoolFalseThenCong (elseBranch := elseBranch) thenStep).HasJoin :=
  (LocalDiamond.iotaBoolFalseThenCong
    (elseBranch := elseBranch) thenStep).hasJoin

/-- Resolver arm for `boolFalse` iota competing with selected else-branch congruence. -/
theorem iotaBoolFalseElseCong_hasJoin {scope : Nat}
    {thenBranch elseBranch steppedElseBranch : RawTerm scope}
    (elseStep : Step elseBranch steppedElseBranch) :
    (iotaBoolFalseElseCong (thenBranch := thenBranch) elseStep).HasJoin :=
  (LocalDiamond.iotaBoolFalseElseCong
    (thenBranch := thenBranch) elseStep).hasJoin

/-- Resolver arm for first projection competing with selected first-component congruence. -/
theorem iotaFstPairFirstCong_hasJoin {scope : Nat}
    {firstValue steppedFirstValue secondValue : RawTerm scope}
    (firstStep : Step firstValue steppedFirstValue) :
    (iotaFstPairFirstCong
      (secondValue := secondValue) firstStep).HasJoin :=
  (LocalDiamond.iotaFstPairFirstCong
    (secondValue := secondValue) firstStep).hasJoin

/-- Resolver arm for first projection competing with discarded second-component congruence. -/
theorem iotaFstPairSecondCong_hasJoin {scope : Nat}
    {firstValue secondValue steppedSecondValue : RawTerm scope}
    (secondStep : Step secondValue steppedSecondValue) :
    (iotaFstPairSecondCong
      (firstValue := firstValue) secondStep).HasJoin :=
  (LocalDiamond.iotaFstPairSecondCong
    (firstValue := firstValue) secondStep).hasJoin

/-- Resolver arm for second projection competing with discarded first-component congruence. -/
theorem iotaSndPairFirstCong_hasJoin {scope : Nat}
    {firstValue steppedFirstValue secondValue : RawTerm scope}
    (firstStep : Step firstValue steppedFirstValue) :
    (iotaSndPairFirstCong
      (secondValue := secondValue) firstStep).HasJoin :=
  (LocalDiamond.iotaSndPairFirstCong
    (secondValue := secondValue) firstStep).hasJoin

/-- Resolver arm for second projection competing with selected second-component congruence. -/
theorem iotaSndPairSecondCong_hasJoin {scope : Nat}
    {firstValue secondValue steppedSecondValue : RawTerm scope}
    (secondStep : Step secondValue steppedSecondValue) :
    (iotaSndPairSecondCong
      (firstValue := firstValue) secondStep).HasJoin :=
  (LocalDiamond.iotaSndPairSecondCong
    (firstValue := firstValue) secondStep).hasJoin

/-- M7 contradiction arm for the mutually-exclusive bool true/false root pair. -/
theorem iotaBoolTrue_iotaBoolFalse_hasSourcesDisjoint {scope : Nat}
    (thenTrue elseTrue thenFalse elseFalse : RawTerm scope) :
    SourcesDisjoint
      (iotaBoolTrueSameRoot thenTrue elseTrue)
      (iotaBoolFalseSameRoot thenFalse elseFalse) :=
  iotaBoolTrue_iotaBoolFalse_sourcesDisjoint
    thenTrue elseTrue thenFalse elseFalse

/-- Reverse M7 contradiction arm for the mutually-exclusive bool false/true root pair. -/
theorem iotaBoolFalse_iotaBoolTrue_hasSourcesDisjoint {scope : Nat}
    (thenFalse elseFalse thenTrue elseTrue : RawTerm scope) :
    SourcesDisjoint
      (iotaBoolFalseSameRoot thenFalse elseFalse)
      (iotaBoolTrueSameRoot thenTrue elseTrue) :=
  iotaBoolFalse_iotaBoolTrue_sourcesDisjoint
    thenFalse elseFalse thenTrue elseTrue

/-- M7 contradiction arm for the mutually-exclusive nat-elim zero/succ root pair. -/
theorem iotaNatElimZero_iotaNatElimSucc_hasSourcesDisjoint {scope : Nat}
    (zeroBranch succBranch predecessor
      zeroBranchSucc succBranchSucc : RawTerm scope) :
    SourcesDisjoint
      (iotaNatElimZeroSameRoot zeroBranch succBranch)
      (iotaNatElimSuccSameRoot
        predecessor zeroBranchSucc succBranchSucc) :=
  iotaNatElimZero_iotaNatElimSucc_sourcesDisjoint
    zeroBranch succBranch predecessor zeroBranchSucc succBranchSucc

/-- Reverse M7 contradiction arm for the mutually-exclusive nat-elim succ/zero root pair. -/
theorem iotaNatElimSucc_iotaNatElimZero_hasSourcesDisjoint {scope : Nat}
    (predecessor zeroBranchSucc succBranchSucc
      zeroBranch succBranch : RawTerm scope) :
    SourcesDisjoint
      (iotaNatElimSuccSameRoot
        predecessor zeroBranchSucc succBranchSucc)
      (iotaNatElimZeroSameRoot zeroBranch succBranch) :=
  iotaNatElimSucc_iotaNatElimZero_sourcesDisjoint
    predecessor zeroBranchSucc succBranchSucc zeroBranch succBranch

/-- M7 contradiction arm for the mutually-exclusive nat-rec zero/succ root pair. -/
theorem iotaNatRecZero_iotaNatRecSucc_hasSourcesDisjoint {scope : Nat}
    (zeroBranch succBranch predecessor
      zeroBranchSucc succBranchSucc : RawTerm scope) :
    SourcesDisjoint
      (iotaNatRecZeroSameRoot zeroBranch succBranch)
      (iotaNatRecSuccSameRoot
        predecessor zeroBranchSucc succBranchSucc) :=
  iotaNatRecZero_iotaNatRecSucc_sourcesDisjoint
    zeroBranch succBranch predecessor zeroBranchSucc succBranchSucc

/-- Reverse M7 contradiction arm for the mutually-exclusive nat-rec succ/zero root pair. -/
theorem iotaNatRecSucc_iotaNatRecZero_hasSourcesDisjoint {scope : Nat}
    (predecessor zeroBranchSucc succBranchSucc
      zeroBranch succBranch : RawTerm scope) :
    SourcesDisjoint
      (iotaNatRecSuccSameRoot
        predecessor zeroBranchSucc succBranchSucc)
      (iotaNatRecZeroSameRoot zeroBranch succBranch) :=
  iotaNatRecSucc_iotaNatRecZero_sourcesDisjoint
    predecessor zeroBranchSucc succBranchSucc zeroBranch succBranch

/-- M7 contradiction arm for the mutually-exclusive list-elim nil/cons root pair. -/
theorem iotaListElimNil_iotaListElimCons_hasSourcesDisjoint {scope : Nat}
    (nilBranch consBranch headValue tailValue
      nilBranchCons consBranchCons : RawTerm scope) :
    SourcesDisjoint
      (iotaListElimNilSameRoot nilBranch consBranch)
      (iotaListElimConsSameRoot
        headValue tailValue nilBranchCons consBranchCons) :=
  iotaListElimNil_iotaListElimCons_sourcesDisjoint
    nilBranch consBranch headValue tailValue nilBranchCons consBranchCons

/-- Reverse M7 contradiction arm for the mutually-exclusive list-elim cons/nil root pair. -/
theorem iotaListElimCons_iotaListElimNil_hasSourcesDisjoint {scope : Nat}
    (headValue tailValue nilBranchCons consBranchCons
      nilBranch consBranch : RawTerm scope) :
    SourcesDisjoint
      (iotaListElimConsSameRoot
        headValue tailValue nilBranchCons consBranchCons)
      (iotaListElimNilSameRoot nilBranch consBranch) :=
  iotaListElimCons_iotaListElimNil_sourcesDisjoint
    headValue tailValue nilBranchCons consBranchCons nilBranch consBranch

/-- M7 contradiction arm for the mutually-exclusive option-match none/some root pair. -/
theorem iotaOptionMatchNone_iotaOptionMatchSome_hasSourcesDisjoint
    {scope : Nat}
    (noneBranch someBranch value
      noneBranchSome someBranchSome : RawTerm scope) :
    SourcesDisjoint
      (iotaOptionMatchNoneSameRoot noneBranch someBranch)
      (iotaOptionMatchSomeSameRoot
        value noneBranchSome someBranchSome) :=
  iotaOptionMatchNone_iotaOptionMatchSome_sourcesDisjoint
    noneBranch someBranch value noneBranchSome someBranchSome

/-- Reverse M7 contradiction arm for the mutually-exclusive option-match some/none root pair. -/
theorem iotaOptionMatchSome_iotaOptionMatchNone_hasSourcesDisjoint
    {scope : Nat}
    (value noneBranchSome someBranchSome
      noneBranch someBranch : RawTerm scope) :
    SourcesDisjoint
      (iotaOptionMatchSomeSameRoot
        value noneBranchSome someBranchSome)
      (iotaOptionMatchNoneSameRoot noneBranch someBranch) :=
  iotaOptionMatchSome_iotaOptionMatchNone_sourcesDisjoint
    value noneBranchSome someBranchSome noneBranch someBranch

/-- M7 contradiction arm for the mutually-exclusive either-match inl/inr root pair. -/
theorem iotaEitherMatchInl_iotaEitherMatchInr_hasSourcesDisjoint
    {scope : Nat}
    (leftValue leftBranch rightBranch rightValue
      leftBranchRight rightBranchRight : RawTerm scope) :
    SourcesDisjoint
      (iotaEitherMatchInlSameRoot
        leftValue leftBranch rightBranch)
      (iotaEitherMatchInrSameRoot
        rightValue leftBranchRight rightBranchRight) :=
  iotaEitherMatchInl_iotaEitherMatchInr_sourcesDisjoint
    leftValue leftBranch rightBranch rightValue
    leftBranchRight rightBranchRight

/-- Reverse M7 contradiction arm for the mutually-exclusive either-match inr/inl root pair. -/
theorem iotaEitherMatchInr_iotaEitherMatchInl_hasSourcesDisjoint
    {scope : Nat}
    (rightValue leftBranchRight rightBranchRight leftValue
      leftBranch rightBranch : RawTerm scope) :
    SourcesDisjoint
      (iotaEitherMatchInrSameRoot
        rightValue leftBranchRight rightBranchRight)
      (iotaEitherMatchInlSameRoot
        leftValue leftBranch rightBranch) :=
  iotaEitherMatchInr_iotaEitherMatchInl_sourcesDisjoint
    rightValue leftBranchRight rightBranchRight leftValue
    leftBranch rightBranch

end LocalStepBranching

namespace CdLemmaStatement

/-- Reduce the full M7 target to a resolver over packaged local branchings.

The future `cd_lemma` proof should supply `resolveBranching` by case analysis
over the M6 critical-pair dispatcher plus structural congruence recursion; this
theorem fixes the final theorem shape without claiming that dispatcher exists
yet. -/
theorem ofLocalBranchingResolver
    (resolveBranching :
      ∀ {scope : Nat} (branching : LocalStepBranching (scope := scope)),
        branching.HasJoin) :
    CdLemmaStatement :=
  fun {scope} {sourceTerm} {leftReduct} {rightReduct}
      leftStep rightStep =>
    LocalStepBranching.fromSteps_hasJoin
      (resolveBranching
        (LocalStepBranching.fromSteps
          (scope := scope)
          (sourceTerm := sourceTerm)
          (leftReduct := leftReduct)
          (rightReduct := rightReduct)
          leftStep rightStep))

end CdLemmaStatement

end LeanFX2.Foundation.PolyCell.Core

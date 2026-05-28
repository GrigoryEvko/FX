import LeanFX2.Foundation.PolyCell.Core.CriticalPairs
import LeanFX2.Foundation.PolyCell.Core.RawSize

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

/-- The child-spine version of `StepPairJoin`.

Congruence/congruence branchings reduce to this shape: both parent steps are
`Step.cong`, so the real join obligation lives between the two child-spine
reductions. -/
def StepChildrenPairJoin {scope : Nat} {binderShifts : List Nat}
    {sourceChildren leftChildren rightChildren :
      RawTermChildren binderShifts scope}
    (_leftStep : StepChildren sourceChildren leftChildren)
    (_rightStep : StepChildren sourceChildren rightChildren) : Prop :=
  ∃ commonChildren : RawTermChildren binderShifts scope,
    StepChildrenStar leftChildren commonChildren ∧
      StepChildrenStar rightChildren commonChildren

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

/-- Lift a child-spine join through a uniform generator congruence context.

This is the reusable congruence/congruence bridge: once structural recursion
over `StepChildren` supplies a child join, the parent `Step.cong` pair joins
by replaying both child-spine chains under the same generator and payload. -/
theorem ofCongChildrenJoin {scope : Nat}
    {generator : Generator} {payload : generator.payload scope}
    {sourceChildren leftChildren rightChildren :
      RawTermChildren generator.binderShifts scope}
    {leftChildrenStep : StepChildren sourceChildren leftChildren}
    {rightChildrenStep : StepChildren sourceChildren rightChildren}
    (childrenJoin :
      StepChildrenPairJoin leftChildrenStep rightChildrenStep) :
    StepPairJoin
      (Step.cong generator payload leftChildrenStep)
      (Step.cong generator payload rightChildrenStep) :=
  Exists.elim childrenJoin
    (fun commonChildren chains =>
      ⟨ .mkGen generator payload commonChildren
      , StepStar.ofChildrenStar chains.1
      , StepStar.ofChildrenStar chains.2 ⟩)

end StepPairJoin

namespace StepChildrenPairJoin

/-- Lift a term-level join through the head child of a spine. -/
theorem ofHeadJoin {scope shift : Nat} {restShifts : List Nat}
    {sourceHead leftHead rightHead : RawTerm (scope + shift)}
    (restChildren : RawTermChildren restShifts scope)
    {leftHeadStep : Step sourceHead leftHead}
    {rightHeadStep : Step sourceHead rightHead}
    (headJoin : StepPairJoin leftHeadStep rightHeadStep) :
    StepChildrenPairJoin
      (StepChildren.here restChildren leftHeadStep)
      (StepChildren.here restChildren rightHeadStep) :=
  Exists.elim headJoin
    (fun commonHead chains =>
      ⟨ RawTermChildren.childCons commonHead restChildren
      , StepChildrenStar.here restChildren chains.1
      , StepChildrenStar.here restChildren chains.2 ⟩)

/-- Join independent reductions in the head child and tail spine. -/
theorem ofIndependentHeadTail {scope shift : Nat} {restShifts : List Nat}
    {sourceHead targetHead : RawTerm (scope + shift)}
    {sourceTail targetTail : RawTermChildren restShifts scope}
    (headStep : Step sourceHead targetHead)
    (tailStep : StepChildren sourceTail targetTail) :
    StepChildrenPairJoin
      (StepChildren.here sourceTail headStep)
      (StepChildren.there sourceHead tailStep) :=
  ⟨ RawTermChildren.childCons targetHead targetTail
  , StepChildrenStar.trans
      (StepChildren.there targetHead tailStep)
      (StepChildrenStar.refl _)
  , StepChildrenStar.trans
      (StepChildren.here targetTail headStep)
      (StepChildrenStar.refl _) ⟩

/-- Join independent reductions in the tail spine and head child. -/
theorem ofIndependentTailHead {scope shift : Nat} {restShifts : List Nat}
    {sourceHead targetHead : RawTerm (scope + shift)}
    {sourceTail targetTail : RawTermChildren restShifts scope}
    (tailStep : StepChildren sourceTail targetTail)
    (headStep : Step sourceHead targetHead) :
    StepChildrenPairJoin
      (StepChildren.there sourceHead tailStep)
      (StepChildren.here sourceTail headStep) :=
  ⟨ RawTermChildren.childCons targetHead targetTail
  , StepChildrenStar.trans
      (StepChildren.here targetTail headStep)
      (StepChildrenStar.refl _)
  , StepChildrenStar.trans
      (StepChildren.there targetHead tailStep)
      (StepChildrenStar.refl _) ⟩

/-- Lift a tail-spine join through a shared head child. -/
theorem ofTailJoin {scope shift : Nat} {restShifts : List Nat}
    (head : RawTerm (scope + shift))
    {sourceTail leftTail rightTail : RawTermChildren restShifts scope}
    {leftTailStep : StepChildren sourceTail leftTail}
    {rightTailStep : StepChildren sourceTail rightTail}
    (tailJoin : StepChildrenPairJoin leftTailStep rightTailStep) :
    StepChildrenPairJoin
      (StepChildren.there head leftTailStep)
      (StepChildren.there head rightTailStep) :=
  Exists.elim tailJoin
    (fun commonTail chains =>
      ⟨ RawTermChildren.childCons head commonTail
      , StepChildrenStar.there head chains.1
      , StepChildrenStar.there head chains.2 ⟩)

/-- Same-child-reduct closure for child-spine joins. -/
theorem ofReductsEqual {scope : Nat} {binderShifts : List Nat}
    {sourceChildren leftChildren rightChildren :
      RawTermChildren binderShifts scope}
    {leftStep : StepChildren sourceChildren leftChildren}
    {rightStep : StepChildren sourceChildren rightChildren}
    (reductsEqual : leftChildren = rightChildren) :
    StepChildrenPairJoin leftStep rightStep := by
  cases reductsEqual
  exact ⟨leftChildren, StepChildrenStar.refl _, StepChildrenStar.refl _⟩

/-- A child-spine step trivially joins with itself. -/
theorem sameStep {scope : Nat} {binderShifts : List Nat}
    {sourceChildren targetChildren :
      RawTermChildren binderShifts scope}
    (sameStepWitness : StepChildren sourceChildren targetChildren) :
    StepChildrenPairJoin sameStepWitness sameStepWitness :=
  ofReductsEqual rfl

/-- Reverse the two branches of a child-spine join. -/
theorem swap {scope : Nat} {binderShifts : List Nat}
    {sourceChildren leftChildren rightChildren :
      RawTermChildren binderShifts scope}
    {leftStep : StepChildren sourceChildren leftChildren}
    {rightStep : StepChildren sourceChildren rightChildren} :
    StepChildrenPairJoin leftStep rightStep →
      StepChildrenPairJoin rightStep leftStep :=
  fun join =>
    Exists.elim join
      (fun commonChildren chains =>
        ⟨commonChildren, chains.2, chains.1⟩)

/-- Resolve child-spine branchings structurally, assuming a term-level
one-step resolver for head/head conflicts.

This is the child half of the eventual mutual M7 resolver.  The
head/head case delegates to the term-level resolver; head/tail and
tail/head are independent-position diamonds; tail/tail recurses on the
tail spine. -/
theorem ofStepPairResolver
    (resolveStepPair :
      ∀ {scope : Nat} {sourceTerm leftReduct rightReduct : RawTerm scope},
        (leftStep : Step sourceTerm leftReduct) →
        (rightStep : Step sourceTerm rightReduct) →
        StepPairJoin leftStep rightStep) :
    ∀ {scope : Nat} {binderShifts : List Nat}
      {sourceChildren leftChildren rightChildren :
        RawTermChildren binderShifts scope},
      (leftStep : StepChildren sourceChildren leftChildren) →
      (rightStep : StepChildren sourceChildren rightChildren) →
      StepChildrenPairJoin leftStep rightStep
  | _, _, _, _, _, .here restChildren leftHeadStep,
      .here _ rightHeadStep =>
      ofHeadJoin restChildren
        (resolveStepPair leftHeadStep rightHeadStep)
  | _, _, _, _, _, .here _ leftHeadStep,
      .there _ rightTailStep =>
      ofIndependentHeadTail leftHeadStep rightTailStep
  | _, _, _, _, _, .there _ leftTailStep,
      .here _ rightHeadStep =>
      ofIndependentTailHead leftTailStep rightHeadStep
  | _, _, _, _, _, .there sourceHead leftTailStep,
      .there _ rightTailStep =>
      ofTailJoin sourceHead
        (ofStepPairResolver resolveStepPair leftTailStep rightTailStep)
termination_by _scope _binderShifts sourceChildren _leftChildren
    _rightChildren _leftStep _rightStep => sourceChildren.size
decreasing_by
  exact RawTermChildren.size_lt_childCons_tail _ _

/-- Resolve child-spine branchings using only term-level recursive calls whose
source term is below a supplied parent size.

This is the well-founded variant needed by the final M7 resolver.  The
head/head case proves the head source is smaller than the whole child spine,
then composes that fact with the caller-provided child-spine bound.  The
tail/tail case recurses on the smaller tail spine.

The proof uses the explicit mutual `StepChildren.rec` recursor instead of
equation-compiler recursion because the extra `< parentSize` proof argument is
proof-valued; the recursor form keeps the theorem audit-clean. -/
theorem ofSmallerStepPairResolver
    {parentSize : Nat}
    (resolveSmallerStepPair :
      ∀ {scope : Nat} {sourceTerm leftReduct rightReduct : RawTerm scope},
        sourceTerm.size < parentSize →
        (leftStep : Step sourceTerm leftReduct) →
        (rightStep : Step sourceTerm rightReduct) →
        StepPairJoin leftStep rightStep) :
    ∀ {scope : Nat} {binderShifts : List Nat}
      {sourceChildren leftChildren rightChildren :
        RawTermChildren binderShifts scope},
      sourceChildren.size < parentSize →
      (leftStep : StepChildren sourceChildren leftChildren) →
      (rightStep : StepChildren sourceChildren rightChildren) →
      StepChildrenPairJoin leftStep rightStep := by
  intro scope binderShifts sourceChildren leftChildren rightChildren
    sourceChildren_lt_parent leftStep rightStep
  exact
    StepChildren.rec
      (motive_1 := fun {_} _ _ _ => True)
      (motive_2 := fun {_} {_} sourceChildren _leftChildren leftStep =>
        ∀ {rightChildren}, sourceChildren.size < parentSize →
          (rightStep : StepChildren sourceChildren rightChildren) →
          StepChildrenPairJoin leftStep rightStep)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by intros; trivial)
      (by
        intro _parentScope _headShift _restShifts sourceHead targetHead
          restChildren childStep _trivialTermMotive
        intro _rightChildren childCons_lt_parent rightStep
        cases rightStep with
        | here _ rightHeadStep =>
            exact ofHeadJoin restChildren
              (resolveSmallerStepPair
                (Nat.lt_trans
                  (RawTermChildren.size_lt_childCons_head
                    sourceHead restChildren)
                  childCons_lt_parent)
                childStep rightHeadStep)
        | there _ rightTailStep =>
            exact ofIndependentHeadTail childStep rightTailStep)
      (by
        intro _parentScope _headShift _restShifts sourceHead sourceTail
          _leftTail restStep tailResolver
        intro _rightChildren childCons_lt_parent rightStep
        cases rightStep with
        | here _ rightHeadStep =>
            exact ofIndependentTailHead restStep rightHeadStep
        | there _ rightTailStep =>
            exact ofTailJoin sourceHead
              (tailResolver
                (Nat.lt_trans
                  (RawTermChildren.size_lt_childCons_tail
                    sourceHead sourceTail)
                  childCons_lt_parent)
                rightTailStep))
      leftStep sourceChildren_lt_parent rightStep

end StepChildrenPairJoin

namespace StepPairJoin

/-- Resolve a `Step.cong`/`Step.cong` branching from the reusable
child-spine resolver.

This is the term-level congruence/congruence arm of the future M7
resolver, parameterized by the still-future term-level resolver used by
the head/head child-spine case. -/
theorem ofCongCongStepPairResolver
    (resolveStepPair :
      ∀ {scope : Nat} {sourceTerm leftReduct rightReduct : RawTerm scope},
        (leftStep : Step sourceTerm leftReduct) →
        (rightStep : Step sourceTerm rightReduct) →
        StepPairJoin leftStep rightStep)
    {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {sourceChildren leftChildren rightChildren :
      RawTermChildren generator.binderShifts scope}
    (leftChildrenStep : StepChildren sourceChildren leftChildren)
    (rightChildrenStep : StepChildren sourceChildren rightChildren) :
    StepPairJoin
      (Step.cong generator payload leftChildrenStep)
      (Step.cong generator payload rightChildrenStep) :=
  ofCongChildrenJoin
    (StepChildrenPairJoin.ofStepPairResolver
      resolveStepPair leftChildrenStep rightChildrenStep)

/-- Resolve a `Step.cong`/`Step.cong` branching using only recursive calls on
source terms smaller than the parent congruence source.

This is the term-level bridge that the final well-founded `resolveBranching`
spine can use directly in the congruence/congruence case. -/
theorem ofCongCongSmallerStepPairResolver
    {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {sourceChildren leftChildren rightChildren :
      RawTermChildren generator.binderShifts scope}
    (resolveSmallerStepPair :
      ∀ {childScope : Nat}
        {sourceTerm leftReduct rightReduct : RawTerm childScope},
        sourceTerm.size <
          (RawTerm.mkGen generator payload sourceChildren).size →
        (leftStep : Step sourceTerm leftReduct) →
        (rightStep : Step sourceTerm rightReduct) →
        StepPairJoin leftStep rightStep)
    (leftChildrenStep : StepChildren sourceChildren leftChildren)
    (rightChildrenStep : StepChildren sourceChildren rightChildren) :
    StepPairJoin
      (Step.cong generator payload leftChildrenStep)
      (Step.cong generator payload rightChildrenStep) :=
  ofCongChildrenJoin
    (StepChildrenPairJoin.ofSmallerStepPairResolver
      (parentSize := (RawTerm.mkGen generator payload sourceChildren).size)
      resolveSmallerStepPair
      (by
        change sourceChildren.size < sourceChildren.size + 1
        exact Nat.lt_succ_self sourceChildren.size)
      leftChildrenStep rightChildrenStep)

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

/-- Packaged `Step.cong`/`Step.cong` resolver arm over arbitrary theorem
inputs.

This keeps the future `resolveBranching` proof from duplicating the
child-spine recursion at the `LocalStepBranching.fromSteps` boundary. -/
theorem congCong_hasJoin_ofStepPairResolver
    (resolveStepPair :
      ∀ {scope : Nat} {sourceTerm leftReduct rightReduct : RawTerm scope},
        (leftStep : Step sourceTerm leftReduct) →
        (rightStep : Step sourceTerm rightReduct) →
        StepPairJoin leftStep rightStep)
    {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {sourceChildren leftChildren rightChildren :
      RawTermChildren generator.binderShifts scope}
    (leftChildrenStep : StepChildren sourceChildren leftChildren)
    (rightChildrenStep : StepChildren sourceChildren rightChildren) :
    (fromSteps
      (Step.cong generator payload leftChildrenStep)
      (Step.cong generator payload rightChildrenStep)).HasJoin :=
  hasJoin_fromSteps
    (StepPairJoin.ofCongCongStepPairResolver
      resolveStepPair leftChildrenStep rightChildrenStep)

/-- Packaged `Step.cong`/`Step.cong` resolver arm for the final
well-founded M7 resolver.

Unlike `congCong_hasJoin_ofStepPairResolver`, this variant only asks for a
resolver on source terms smaller than the parent congruence source. -/
theorem congCong_hasJoin_ofSmallerStepPairResolver
    {scope : Nat} {generator : Generator}
    {payload : generator.payload scope}
    {sourceChildren leftChildren rightChildren :
      RawTermChildren generator.binderShifts scope}
    (resolveSmallerStepPair :
      ∀ {childScope : Nat}
        {sourceTerm leftReduct rightReduct : RawTerm childScope},
        sourceTerm.size <
          (RawTerm.mkGen generator payload sourceChildren).size →
        (leftStep : Step sourceTerm leftReduct) →
        (rightStep : Step sourceTerm rightReduct) →
        StepPairJoin leftStep rightStep)
    (leftChildrenStep : StepChildren sourceChildren leftChildren)
    (rightChildrenStep : StepChildren sourceChildren rightChildren) :
    (fromSteps
      (Step.cong generator payload leftChildrenStep)
      (Step.cong generator payload rightChildrenStep)).HasJoin :=
  hasJoin_fromSteps
    (StepPairJoin.ofCongCongSmallerStepPairResolver
      resolveSmallerStepPair leftChildrenStep rightChildrenStep)

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

/-- `fromSteps`-facing beta/beta resolver arm. -/
theorem fromSteps_betaBeta_hasJoin {scope : Nat}
    (body : RawTerm (scope + 1)) (argument : RawTerm scope) :
    (fromSteps
      (Step.beta (body := body) (arg := argument))
      (Step.beta (body := body) (arg := argument))).HasJoin :=
  betaBeta_hasJoin body argument

/-- Resolver arm for beta competing with congruence in the function child. -/
theorem betaFunctionCong_hasJoin {scope : Nat}
    {body updatedBody : RawTerm (scope + 1)}
    (argument : RawTerm scope) (bodyStep : Step body updatedBody) :
    (betaFunctionCong argument bodyStep).HasJoin :=
  (LocalDiamond.betaFunctionCong argument bodyStep).hasJoin

/-- `fromSteps`-facing beta/function-congruence resolver arm. -/
theorem fromSteps_betaFunctionCong_hasJoin {scope : Nat}
    {body updatedBody : RawTerm (scope + 1)}
    (argument : RawTerm scope) (bodyStep : Step body updatedBody) :
    (fromSteps
      (Step.beta (body := body) (arg := argument))
      (betaFunctionCong argument bodyStep).rightStep).HasJoin :=
  betaFunctionCong_hasJoin argument bodyStep

/-- Resolver arm for the reverse orientation of beta/function congruence. -/
theorem betaFunctionCongReverse_hasJoin {scope : Nat}
    {body updatedBody : RawTerm (scope + 1)}
    (argument : RawTerm scope) (bodyStep : Step body updatedBody) :
    (betaFunctionCong argument bodyStep).swap.HasJoin :=
  (LocalDiamond.betaFunctionCongReverse argument bodyStep).hasJoin

/-- `fromSteps`-facing reverse beta/function-congruence resolver arm. -/
theorem fromSteps_betaFunctionCongReverse_hasJoin {scope : Nat}
    {body updatedBody : RawTerm (scope + 1)}
    (argument : RawTerm scope) (bodyStep : Step body updatedBody) :
    (fromSteps
      (betaFunctionCong argument bodyStep).rightStep
      (Step.beta (body := body) (arg := argument))).HasJoin :=
  betaFunctionCongReverse_hasJoin argument bodyStep

/-- Resolver arm for beta competing with congruence in the argument child. -/
theorem betaArgumentCong_hasJoin {scope : Nat}
    (body : RawTerm (scope + 1))
    {argument updatedArgument : RawTerm scope}
    (argumentStep : Step argument updatedArgument) :
    (betaArgumentCong body argumentStep).HasJoin :=
  (LocalDiamond.betaArgumentCong body argumentStep).hasJoin

/-- `fromSteps`-facing beta/argument-congruence resolver arm. -/
theorem fromSteps_betaArgumentCong_hasJoin {scope : Nat}
    (body : RawTerm (scope + 1))
    {argument updatedArgument : RawTerm scope}
    (argumentStep : Step argument updatedArgument) :
    (fromSteps
      (Step.beta (body := body) (arg := argument))
      (betaArgumentCong body argumentStep).rightStep).HasJoin :=
  betaArgumentCong_hasJoin body argumentStep

/-- Resolver arm for the reverse orientation of beta/argument congruence. -/
theorem betaArgumentCongReverse_hasJoin {scope : Nat}
    (body : RawTerm (scope + 1))
    {argument updatedArgument : RawTerm scope}
    (argumentStep : Step argument updatedArgument) :
    (betaArgumentCong body argumentStep).swap.HasJoin :=
  (LocalDiamond.betaArgumentCongReverse body argumentStep).hasJoin

/-- `fromSteps`-facing reverse beta/argument-congruence resolver arm. -/
theorem fromSteps_betaArgumentCongReverse_hasJoin {scope : Nat}
    (body : RawTerm (scope + 1))
    {argument updatedArgument : RawTerm scope}
    (argumentStep : Step argument updatedArgument) :
    (fromSteps
      (betaArgumentCong body argumentStep).rightStep
      (Step.beta (body := body) (arg := argument))).HasJoin :=
  betaArgumentCongReverse_hasJoin body argumentStep

/-- Resolve every local branching whose left step is beta.

The dependent case split on the right step leaves only the real beta
branchings from the shared beta-redex source: beta/beta, congruence in the
application function child, or congruence in the application argument child.
Empty-spine tails are impossible by direct `cases`. -/
theorem fromSteps_betaLeft_hasJoin {scope : Nat}
    {body : RawTerm (scope + 1)}
    {argument rightReduct : RawTerm scope}
    (rightStep : Step
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam () (.childCons body .childNil))
          (.childCons argument .childNil)))
      rightReduct) :
    (fromSteps
      (Step.beta (body := body) (arg := argument))
      rightStep).HasJoin := by
  cases rightStep with
  | beta =>
      exact fromSteps_betaBeta_hasJoin body argument
  | cong generator payload childStep =>
      cases childStep with
      | here restChildren functionStep =>
          cases functionStep with
          | cong functionGenerator functionPayload functionChildStep =>
              cases functionChildStep with
              | here functionRest bodyStep =>
                  exact fromSteps_betaFunctionCong_hasJoin argument bodyStep
              | there functionHead functionRestStep =>
                  cases functionRestStep
      | there functionChild argumentChildrenStep =>
          cases argumentChildrenStep with
          | here argumentRest argumentStep =>
              exact fromSteps_betaArgumentCong_hasJoin body argumentStep
          | there argumentHead argumentRestStep =>
              cases argumentRestStep

/-- Resolve every local branching whose right step is beta.

This is the orientation bridge for the beta-left resolver arm, preserving the
future resolver spine's ability to consume either arbitrary step order. -/
theorem fromSteps_betaRight_hasJoin {scope : Nat}
    {body : RawTerm (scope + 1)}
    {argument leftReduct : RawTerm scope}
    (leftStep : Step
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam () (.childCons body .childNil))
          (.childCons argument .childNil)))
      leftReduct) :
    (fromSteps
      leftStep
      (Step.beta (body := body) (arg := argument))).HasJoin :=
  hasJoin_swap (fromSteps_betaLeft_hasJoin leftStep)

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

/-- `fromSteps`-facing same-root `boolTrue` iota resolver arm. -/
theorem fromSteps_iotaBoolTrueSameRoot_hasJoin {scope : Nat}
    (thenBranch elseBranch : RawTerm scope) :
    (fromSteps
      (Step.iotaBoolTrue
        (thenBranch := thenBranch) (elseBranch := elseBranch))
      (Step.iotaBoolTrue
        (thenBranch := thenBranch) (elseBranch := elseBranch))).HasJoin :=
  iotaBoolTrueSameRoot_hasJoin thenBranch elseBranch

/-- `fromSteps`-facing same-root `boolFalse` iota resolver arm. -/
theorem fromSteps_iotaBoolFalseSameRoot_hasJoin {scope : Nat}
    (thenBranch elseBranch : RawTerm scope) :
    (fromSteps
      (Step.iotaBoolFalse
        (thenBranch := thenBranch) (elseBranch := elseBranch))
      (Step.iotaBoolFalse
        (thenBranch := thenBranch) (elseBranch := elseBranch))).HasJoin :=
  iotaBoolFalseSameRoot_hasJoin thenBranch elseBranch

/-- `fromSteps`-facing same-root first-projection iota resolver arm. -/
theorem fromSteps_iotaFstPairSameRoot_hasJoin {scope : Nat}
    (firstValue secondValue : RawTerm scope) :
    (fromSteps
      (Step.iotaFstPair
        (firstValue := firstValue) (secondValue := secondValue))
      (Step.iotaFstPair
        (firstValue := firstValue) (secondValue := secondValue))).HasJoin :=
  iotaFstPairSameRoot_hasJoin firstValue secondValue

/-- `fromSteps`-facing same-root second-projection iota resolver arm. -/
theorem fromSteps_iotaSndPairSameRoot_hasJoin {scope : Nat}
    (firstValue secondValue : RawTerm scope) :
    (fromSteps
      (Step.iotaSndPair
        (firstValue := firstValue) (secondValue := secondValue))
      (Step.iotaSndPair
        (firstValue := firstValue) (secondValue := secondValue))).HasJoin :=
  iotaSndPairSameRoot_hasJoin firstValue secondValue

/-- `fromSteps`-facing same-root `natElim` zero-case iota resolver arm. -/
theorem fromSteps_iotaNatElimZeroSameRoot_hasJoin {scope : Nat}
    (zeroBranch succBranch : RawTerm scope) :
    (fromSteps
      (Step.iotaNatElimZero
        (zeroBranch := zeroBranch) (succBranch := succBranch))
      (Step.iotaNatElimZero
        (zeroBranch := zeroBranch) (succBranch := succBranch))).HasJoin :=
  iotaNatElimZeroSameRoot_hasJoin zeroBranch succBranch

/-- `fromSteps`-facing same-root `natRec` zero-case iota resolver arm. -/
theorem fromSteps_iotaNatRecZeroSameRoot_hasJoin {scope : Nat}
    (zeroBranch succBranch : RawTerm scope) :
    (fromSteps
      (Step.iotaNatRecZero
        (zeroBranch := zeroBranch) (succBranch := succBranch))
      (Step.iotaNatRecZero
        (zeroBranch := zeroBranch) (succBranch := succBranch))).HasJoin :=
  iotaNatRecZeroSameRoot_hasJoin zeroBranch succBranch

/-- `fromSteps`-facing same-root `listElim` nil-case iota resolver arm. -/
theorem fromSteps_iotaListElimNilSameRoot_hasJoin {scope : Nat}
    (nilBranch consBranch : RawTerm scope) :
    (fromSteps
      (Step.iotaListElimNil
        (nilBranch := nilBranch) (consBranch := consBranch))
      (Step.iotaListElimNil
        (nilBranch := nilBranch) (consBranch := consBranch))).HasJoin :=
  iotaListElimNilSameRoot_hasJoin nilBranch consBranch

/-- `fromSteps`-facing same-root `optionMatch` none-case iota resolver arm. -/
theorem fromSteps_iotaOptionMatchNoneSameRoot_hasJoin {scope : Nat}
    (noneBranch someBranch : RawTerm scope) :
    (fromSteps
      (Step.iotaOptionMatchNone
        (noneBranch := noneBranch) (someBranch := someBranch))
      (Step.iotaOptionMatchNone
        (noneBranch := noneBranch) (someBranch := someBranch))).HasJoin :=
  iotaOptionMatchNoneSameRoot_hasJoin noneBranch someBranch

/-- `fromSteps`-facing same-root `idJ` refl-case iota resolver arm. -/
theorem fromSteps_iotaIdJReflSameRoot_hasJoin {scope : Nat}
    (baseCase rawWitness : RawTerm scope) :
    (fromSteps
      (Step.iotaIdJRefl
        (baseCase := baseCase) (rawWitness := rawWitness))
      (Step.iotaIdJRefl
        (baseCase := baseCase) (rawWitness := rawWitness))).HasJoin :=
  iotaIdJReflSameRoot_hasJoin baseCase rawWitness

/-- `fromSteps`-facing same-root `idStrictRec` refl-case iota resolver arm. -/
theorem fromSteps_iotaIdStrictRecReflSameRoot_hasJoin {scope : Nat}
    (baseCase rawWitness : RawTerm scope) :
    (fromSteps
      (Step.iotaIdStrictRecRefl
        (baseCase := baseCase) (rawWitness := rawWitness))
      (Step.iotaIdStrictRecRefl
        (baseCase := baseCase) (rawWitness := rawWitness))).HasJoin :=
  iotaIdStrictRecReflSameRoot_hasJoin baseCase rawWitness

/-- `fromSteps`-facing same-root `optionMatch` some-case iota resolver arm. -/
theorem fromSteps_iotaOptionMatchSomeSameRoot_hasJoin {scope : Nat}
    (value noneBranch someBranch : RawTerm scope) :
    (fromSteps
      (Step.iotaOptionMatchSome
        (value := value) (noneBranch := noneBranch)
        (someBranch := someBranch))
      (Step.iotaOptionMatchSome
        (value := value) (noneBranch := noneBranch)
        (someBranch := someBranch))).HasJoin :=
  iotaOptionMatchSomeSameRoot_hasJoin value noneBranch someBranch

/-- `fromSteps`-facing same-root `eitherMatch` inl-case iota resolver arm. -/
theorem fromSteps_iotaEitherMatchInlSameRoot_hasJoin {scope : Nat}
    (value leftBranch rightBranch : RawTerm scope) :
    (fromSteps
      (Step.iotaEitherMatchInl
        (value := value) (leftBranch := leftBranch)
        (rightBranch := rightBranch))
      (Step.iotaEitherMatchInl
        (value := value) (leftBranch := leftBranch)
        (rightBranch := rightBranch))).HasJoin :=
  iotaEitherMatchInlSameRoot_hasJoin value leftBranch rightBranch

/-- `fromSteps`-facing same-root `eitherMatch` inr-case iota resolver arm. -/
theorem fromSteps_iotaEitherMatchInrSameRoot_hasJoin {scope : Nat}
    (value leftBranch rightBranch : RawTerm scope) :
    (fromSteps
      (Step.iotaEitherMatchInr
        (value := value) (leftBranch := leftBranch)
        (rightBranch := rightBranch))
      (Step.iotaEitherMatchInr
        (value := value) (leftBranch := leftBranch)
        (rightBranch := rightBranch))).HasJoin :=
  iotaEitherMatchInrSameRoot_hasJoin value leftBranch rightBranch

/-- `fromSteps`-facing same-root `natElim` succ-case iota resolver arm. -/
theorem fromSteps_iotaNatElimSuccSameRoot_hasJoin {scope : Nat}
    (predecessor zeroBranch succBranch : RawTerm scope) :
    (fromSteps
      (Step.iotaNatElimSucc
        (predecessor := predecessor) (zeroBranch := zeroBranch)
        (succBranch := succBranch))
      (Step.iotaNatElimSucc
        (predecessor := predecessor) (zeroBranch := zeroBranch)
        (succBranch := succBranch))).HasJoin :=
  iotaNatElimSuccSameRoot_hasJoin predecessor zeroBranch succBranch

/-- `fromSteps`-facing same-root `natRec` succ-case iota resolver arm. -/
theorem fromSteps_iotaNatRecSuccSameRoot_hasJoin {scope : Nat}
    (predecessor zeroBranch succBranch : RawTerm scope) :
    (fromSteps
      (Step.iotaNatRecSucc
        (predecessor := predecessor) (zeroBranch := zeroBranch)
        (succBranch := succBranch))
      (Step.iotaNatRecSucc
        (predecessor := predecessor) (zeroBranch := zeroBranch)
        (succBranch := succBranch))).HasJoin :=
  iotaNatRecSuccSameRoot_hasJoin predecessor zeroBranch succBranch

/-- `fromSteps`-facing same-root `listElim` cons-case iota resolver arm. -/
theorem fromSteps_iotaListElimConsSameRoot_hasJoin {scope : Nat}
    (headValue tailValue nilBranch consBranch : RawTerm scope) :
    (fromSteps
      (Step.iotaListElimCons
        (headVal := headValue) (tailVal := tailValue)
        (nilBranch := nilBranch) (consBranch := consBranch))
      (Step.iotaListElimCons
        (headVal := headValue) (tailVal := tailValue)
        (nilBranch := nilBranch) (consBranch := consBranch))).HasJoin :=
  iotaListElimConsSameRoot_hasJoin
    headValue tailValue nilBranch consBranch

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

/-- `fromSteps`-facing `boolTrue` iota / selected then-branch congruence arm. -/
theorem fromSteps_iotaBoolTrueThenCong_hasJoin {scope : Nat}
    {thenBranch steppedThenBranch elseBranch : RawTerm scope}
    (thenStep : Step thenBranch steppedThenBranch) :
    (fromSteps
      (Step.iotaBoolTrue
        (thenBranch := thenBranch) (elseBranch := elseBranch))
      (iotaBoolTrueThenCong
        (elseBranch := elseBranch) thenStep).rightStep).HasJoin :=
  iotaBoolTrueThenCong_hasJoin thenStep

/-- `fromSteps`-facing `boolTrue` iota / discarded else-branch congruence arm. -/
theorem fromSteps_iotaBoolTrueElseCong_hasJoin {scope : Nat}
    {thenBranch elseBranch steppedElseBranch : RawTerm scope}
    (elseStep : Step elseBranch steppedElseBranch) :
    (fromSteps
      (Step.iotaBoolTrue
        (thenBranch := thenBranch) (elseBranch := elseBranch))
      (iotaBoolTrueElseCong
        (thenBranch := thenBranch) elseStep).rightStep).HasJoin :=
  iotaBoolTrueElseCong_hasJoin elseStep

/-- `fromSteps`-facing `boolFalse` iota / discarded then-branch congruence arm. -/
theorem fromSteps_iotaBoolFalseThenCong_hasJoin {scope : Nat}
    {thenBranch steppedThenBranch elseBranch : RawTerm scope}
    (thenStep : Step thenBranch steppedThenBranch) :
    (fromSteps
      (Step.iotaBoolFalse
        (thenBranch := thenBranch) (elseBranch := elseBranch))
      (iotaBoolFalseThenCong
        (elseBranch := elseBranch) thenStep).rightStep).HasJoin :=
  iotaBoolFalseThenCong_hasJoin thenStep

/-- `fromSteps`-facing `boolFalse` iota / selected else-branch congruence arm. -/
theorem fromSteps_iotaBoolFalseElseCong_hasJoin {scope : Nat}
    {thenBranch elseBranch steppedElseBranch : RawTerm scope}
    (elseStep : Step elseBranch steppedElseBranch) :
    (fromSteps
      (Step.iotaBoolFalse
        (thenBranch := thenBranch) (elseBranch := elseBranch))
      (iotaBoolFalseElseCong
        (thenBranch := thenBranch) elseStep).rightStep).HasJoin :=
  iotaBoolFalseElseCong_hasJoin elseStep

/-- `fromSteps`-facing first-projection / selected first-component congruence arm. -/
theorem fromSteps_iotaFstPairFirstCong_hasJoin {scope : Nat}
    {firstValue steppedFirstValue secondValue : RawTerm scope}
    (firstStep : Step firstValue steppedFirstValue) :
    (fromSteps
      (Step.iotaFstPair
        (firstValue := firstValue) (secondValue := secondValue))
      (iotaFstPairFirstCong
        (secondValue := secondValue) firstStep).rightStep).HasJoin :=
  iotaFstPairFirstCong_hasJoin firstStep

/-- `fromSteps`-facing first-projection / discarded second-component congruence arm. -/
theorem fromSteps_iotaFstPairSecondCong_hasJoin {scope : Nat}
    {firstValue secondValue steppedSecondValue : RawTerm scope}
    (secondStep : Step secondValue steppedSecondValue) :
    (fromSteps
      (Step.iotaFstPair
        (firstValue := firstValue) (secondValue := secondValue))
      (iotaFstPairSecondCong
        (firstValue := firstValue) secondStep).rightStep).HasJoin :=
  iotaFstPairSecondCong_hasJoin secondStep

/-- `fromSteps`-facing second-projection / discarded first-component congruence arm. -/
theorem fromSteps_iotaSndPairFirstCong_hasJoin {scope : Nat}
    {firstValue steppedFirstValue secondValue : RawTerm scope}
    (firstStep : Step firstValue steppedFirstValue) :
    (fromSteps
      (Step.iotaSndPair
        (firstValue := firstValue) (secondValue := secondValue))
      (iotaSndPairFirstCong
        (secondValue := secondValue) firstStep).rightStep).HasJoin :=
  iotaSndPairFirstCong_hasJoin firstStep

/-- `fromSteps`-facing second-projection / selected second-component congruence arm. -/
theorem fromSteps_iotaSndPairSecondCong_hasJoin {scope : Nat}
    {firstValue secondValue steppedSecondValue : RawTerm scope}
    (secondStep : Step secondValue steppedSecondValue) :
    (fromSteps
      (Step.iotaSndPair
        (firstValue := firstValue) (secondValue := secondValue))
      (iotaSndPairSecondCong
        (firstValue := firstValue) secondStep).rightStep).HasJoin :=
  iotaSndPairSecondCong_hasJoin secondStep

/-- Resolver arm for `natElim natZero` iota competing with selected
zero-branch congruence. -/
theorem iotaNatElimZeroBranchCong_hasJoin {scope : Nat}
    {zeroBranch steppedZeroBranch succBranch : RawTerm scope}
    (zeroStep : Step zeroBranch steppedZeroBranch) :
    (iotaNatElimZeroBranchCong
      (succBranch := succBranch) zeroStep).HasJoin :=
  (LocalDiamond.iotaNatElimZeroBranchCong
    (succBranch := succBranch) zeroStep).hasJoin

/-- Resolver arm for `natElim natZero` iota competing with discarded
successor-branch congruence. -/
theorem iotaNatElimSuccBranchCong_hasJoin {scope : Nat}
    {zeroBranch succBranch steppedSuccBranch : RawTerm scope}
    (succStep : Step succBranch steppedSuccBranch) :
    (iotaNatElimSuccBranchCong
      (zeroBranch := zeroBranch) succStep).HasJoin :=
  (LocalDiamond.iotaNatElimSuccBranchCong
    (zeroBranch := zeroBranch) succStep).hasJoin

/-- Resolver arm for `natRec natZero` iota competing with selected
zero-branch congruence. -/
theorem iotaNatRecZeroBranchCong_hasJoin {scope : Nat}
    {zeroBranch steppedZeroBranch succBranch : RawTerm scope}
    (zeroStep : Step zeroBranch steppedZeroBranch) :
    (iotaNatRecZeroBranchCong
      (succBranch := succBranch) zeroStep).HasJoin :=
  (LocalDiamond.iotaNatRecZeroBranchCong
    (succBranch := succBranch) zeroStep).hasJoin

/-- Resolver arm for `natRec natZero` iota competing with discarded
successor-branch congruence. -/
theorem iotaNatRecSuccBranchCong_hasJoin {scope : Nat}
    {zeroBranch succBranch steppedSuccBranch : RawTerm scope}
    (succStep : Step succBranch steppedSuccBranch) :
    (iotaNatRecSuccBranchCong
      (zeroBranch := zeroBranch) succStep).HasJoin :=
  (LocalDiamond.iotaNatRecSuccBranchCong
    (zeroBranch := zeroBranch) succStep).hasJoin

/-- Resolver arm for `natElim (natSucc predecessor)` iota competing with
zero-branch congruence. -/
theorem iotaNatElimSuccZeroBranchCong_hasJoin {scope : Nat}
    {predecessor zeroBranch steppedZeroBranch succBranch : RawTerm scope}
    (zeroStep : Step zeroBranch steppedZeroBranch) :
    (iotaNatElimSuccZeroBranchCong
      (predecessor := predecessor) (succBranch := succBranch)
      zeroStep).HasJoin :=
  (LocalDiamond.iotaNatElimSuccZeroBranchCong
    (predecessor := predecessor) (succBranch := succBranch)
    zeroStep).hasJoin

/-- Resolver arm for `natElim (natSucc predecessor)` iota competing with
successor-branch congruence. -/
theorem iotaNatElimSuccSuccBranchCong_hasJoin {scope : Nat}
    {predecessor zeroBranch succBranch steppedSuccBranch : RawTerm scope}
    (succStep : Step succBranch steppedSuccBranch) :
    (iotaNatElimSuccSuccBranchCong
      (predecessor := predecessor) (zeroBranch := zeroBranch)
      succStep).HasJoin :=
  (LocalDiamond.iotaNatElimSuccSuccBranchCong
    (predecessor := predecessor) (zeroBranch := zeroBranch)
    succStep).hasJoin

/-- Resolver arm for `natRec (natSucc predecessor)` iota competing with
zero-branch congruence. -/
theorem iotaNatRecSuccZeroBranchCong_hasJoin {scope : Nat}
    {predecessor zeroBranch steppedZeroBranch succBranch : RawTerm scope}
    (zeroStep : Step zeroBranch steppedZeroBranch) :
    (iotaNatRecSuccZeroBranchCong
      (predecessor := predecessor) (succBranch := succBranch)
      zeroStep).HasJoin :=
  (LocalDiamond.iotaNatRecSuccZeroBranchCong
    (predecessor := predecessor) (succBranch := succBranch)
    zeroStep).hasJoin

/-- Resolver arm for `natRec (natSucc predecessor)` iota competing with
successor-branch congruence. -/
theorem iotaNatRecSuccSuccBranchCong_hasJoin {scope : Nat}
    {predecessor zeroBranch succBranch steppedSuccBranch : RawTerm scope}
    (succStep : Step succBranch steppedSuccBranch) :
    (iotaNatRecSuccSuccBranchCong
      (predecessor := predecessor) (zeroBranch := zeroBranch)
      succStep).HasJoin :=
  (LocalDiamond.iotaNatRecSuccSuccBranchCong
    (predecessor := predecessor) (zeroBranch := zeroBranch)
    succStep).hasJoin

/-- Resolver arm for `natElim (natSucc predecessor)` iota competing with
congruence inside the predecessor child. -/
theorem iotaNatElimSuccPredecessorCong_hasJoin {scope : Nat}
    {predecessor steppedPredecessor zeroBranch succBranch : RawTerm scope}
    (predecessorStep : Step predecessor steppedPredecessor) :
    (iotaNatElimSuccPredecessorCong
      (zeroBranch := zeroBranch) (succBranch := succBranch)
      predecessorStep).HasJoin :=
  (LocalDiamond.iotaNatElimSuccPredecessorCong
    (zeroBranch := zeroBranch) (succBranch := succBranch)
    predecessorStep).hasJoin

/-- Resolver arm for `natRec (natSucc predecessor)` iota competing with
congruence inside the predecessor child. -/
theorem iotaNatRecSuccPredecessorCong_hasJoin {scope : Nat}
    {predecessor steppedPredecessor zeroBranch succBranch : RawTerm scope}
    (predecessorStep : Step predecessor steppedPredecessor) :
    (iotaNatRecSuccPredecessorCong
      (zeroBranch := zeroBranch) (succBranch := succBranch)
      predecessorStep).HasJoin :=
  (LocalDiamond.iotaNatRecSuccPredecessorCong
    (zeroBranch := zeroBranch) (succBranch := succBranch)
    predecessorStep).hasJoin

/-- `fromSteps`-facing `natElim natZero` iota / zero-branch congruence arm. -/
theorem fromSteps_iotaNatElimZeroBranchCong_hasJoin {scope : Nat}
    {zeroBranch steppedZeroBranch succBranch : RawTerm scope}
    (zeroStep : Step zeroBranch steppedZeroBranch) :
    (fromSteps
      (Step.iotaNatElimZero
        (zeroBranch := zeroBranch) (succBranch := succBranch))
      (iotaNatElimZeroBranchCong
        (succBranch := succBranch) zeroStep).rightStep).HasJoin :=
  iotaNatElimZeroBranchCong_hasJoin zeroStep

/-- `fromSteps`-facing `natElim natZero` iota / successor-branch congruence arm. -/
theorem fromSteps_iotaNatElimSuccBranchCong_hasJoin {scope : Nat}
    {zeroBranch succBranch steppedSuccBranch : RawTerm scope}
    (succStep : Step succBranch steppedSuccBranch) :
    (fromSteps
      (Step.iotaNatElimZero
        (zeroBranch := zeroBranch) (succBranch := succBranch))
      (iotaNatElimSuccBranchCong
        (zeroBranch := zeroBranch) succStep).rightStep).HasJoin :=
  iotaNatElimSuccBranchCong_hasJoin succStep

/-- `fromSteps`-facing `natRec natZero` iota / zero-branch congruence arm. -/
theorem fromSteps_iotaNatRecZeroBranchCong_hasJoin {scope : Nat}
    {zeroBranch steppedZeroBranch succBranch : RawTerm scope}
    (zeroStep : Step zeroBranch steppedZeroBranch) :
    (fromSteps
      (Step.iotaNatRecZero
        (zeroBranch := zeroBranch) (succBranch := succBranch))
      (iotaNatRecZeroBranchCong
        (succBranch := succBranch) zeroStep).rightStep).HasJoin :=
  iotaNatRecZeroBranchCong_hasJoin zeroStep

/-- `fromSteps`-facing `natRec natZero` iota / successor-branch congruence arm. -/
theorem fromSteps_iotaNatRecSuccBranchCong_hasJoin {scope : Nat}
    {zeroBranch succBranch steppedSuccBranch : RawTerm scope}
    (succStep : Step succBranch steppedSuccBranch) :
    (fromSteps
      (Step.iotaNatRecZero
        (zeroBranch := zeroBranch) (succBranch := succBranch))
      (iotaNatRecSuccBranchCong
        (zeroBranch := zeroBranch) succStep).rightStep).HasJoin :=
  iotaNatRecSuccBranchCong_hasJoin succStep

/-- `fromSteps`-facing `natElim natSucc` iota / zero-branch congruence arm. -/
theorem fromSteps_iotaNatElimSuccZeroBranchCong_hasJoin {scope : Nat}
    {predecessor zeroBranch steppedZeroBranch succBranch : RawTerm scope}
    (zeroStep : Step zeroBranch steppedZeroBranch) :
    (fromSteps
      (Step.iotaNatElimSucc
        (predecessor := predecessor) (zeroBranch := zeroBranch)
        (succBranch := succBranch))
      (iotaNatElimSuccZeroBranchCong
        (predecessor := predecessor) (succBranch := succBranch)
        zeroStep).rightStep).HasJoin :=
  iotaNatElimSuccZeroBranchCong_hasJoin zeroStep

/-- `fromSteps`-facing `natElim natSucc` iota / successor-branch congruence arm. -/
theorem fromSteps_iotaNatElimSuccSuccBranchCong_hasJoin {scope : Nat}
    {predecessor zeroBranch succBranch steppedSuccBranch : RawTerm scope}
    (succStep : Step succBranch steppedSuccBranch) :
    (fromSteps
      (Step.iotaNatElimSucc
        (predecessor := predecessor) (zeroBranch := zeroBranch)
        (succBranch := succBranch))
      (iotaNatElimSuccSuccBranchCong
        (predecessor := predecessor) (zeroBranch := zeroBranch)
        succStep).rightStep).HasJoin :=
  iotaNatElimSuccSuccBranchCong_hasJoin succStep

/-- `fromSteps`-facing `natRec natSucc` iota / zero-branch congruence arm. -/
theorem fromSteps_iotaNatRecSuccZeroBranchCong_hasJoin {scope : Nat}
    {predecessor zeroBranch steppedZeroBranch succBranch : RawTerm scope}
    (zeroStep : Step zeroBranch steppedZeroBranch) :
    (fromSteps
      (Step.iotaNatRecSucc
        (predecessor := predecessor) (zeroBranch := zeroBranch)
        (succBranch := succBranch))
      (iotaNatRecSuccZeroBranchCong
        (predecessor := predecessor) (succBranch := succBranch)
        zeroStep).rightStep).HasJoin :=
  iotaNatRecSuccZeroBranchCong_hasJoin zeroStep

/-- `fromSteps`-facing `natRec natSucc` iota / successor-branch congruence arm. -/
theorem fromSteps_iotaNatRecSuccSuccBranchCong_hasJoin {scope : Nat}
    {predecessor zeroBranch succBranch steppedSuccBranch : RawTerm scope}
    (succStep : Step succBranch steppedSuccBranch) :
    (fromSteps
      (Step.iotaNatRecSucc
        (predecessor := predecessor) (zeroBranch := zeroBranch)
        (succBranch := succBranch))
      (iotaNatRecSuccSuccBranchCong
        (predecessor := predecessor) (zeroBranch := zeroBranch)
        succStep).rightStep).HasJoin :=
  iotaNatRecSuccSuccBranchCong_hasJoin succStep

/-- `fromSteps`-facing `natElim natSucc` iota / predecessor congruence arm. -/
theorem fromSteps_iotaNatElimSuccPredecessorCong_hasJoin {scope : Nat}
    {predecessor steppedPredecessor zeroBranch succBranch : RawTerm scope}
    (predecessorStep : Step predecessor steppedPredecessor) :
    (fromSteps
      (Step.iotaNatElimSucc
        (predecessor := predecessor) (zeroBranch := zeroBranch)
        (succBranch := succBranch))
      (iotaNatElimSuccPredecessorCong
        (zeroBranch := zeroBranch) (succBranch := succBranch)
        predecessorStep).rightStep).HasJoin :=
  iotaNatElimSuccPredecessorCong_hasJoin predecessorStep

/-- `fromSteps`-facing `natRec natSucc` iota / predecessor congruence arm. -/
theorem fromSteps_iotaNatRecSuccPredecessorCong_hasJoin {scope : Nat}
    {predecessor steppedPredecessor zeroBranch succBranch : RawTerm scope}
    (predecessorStep : Step predecessor steppedPredecessor) :
    (fromSteps
      (Step.iotaNatRecSucc
        (predecessor := predecessor) (zeroBranch := zeroBranch)
        (succBranch := succBranch))
      (iotaNatRecSuccPredecessorCong
        (zeroBranch := zeroBranch) (succBranch := succBranch)
        predecessorStep).rightStep).HasJoin :=
  iotaNatRecSuccPredecessorCong_hasJoin predecessorStep

/-- Resolver arm for `listElim (listCons head tail)` iota competing with
congruence inside the head child. -/
theorem iotaListElimConsHeadCong_hasJoin {scope : Nat}
    {headValue steppedHeadValue tailValue nilBranch consBranch :
      RawTerm scope}
    (headStep : Step headValue steppedHeadValue) :
    (iotaListElimConsHeadCong
      (tailValue := tailValue) (nilBranch := nilBranch)
      (consBranch := consBranch) headStep).HasJoin :=
  (LocalDiamond.iotaListElimConsHeadCong
    (tailValue := tailValue) (nilBranch := nilBranch)
    (consBranch := consBranch) headStep).hasJoin

/-- Resolver arm for `listElim (listCons head tail)` iota competing with
congruence inside the tail child. -/
theorem iotaListElimConsTailCong_hasJoin {scope : Nat}
    {headValue tailValue steppedTailValue nilBranch consBranch :
      RawTerm scope}
    (tailStep : Step tailValue steppedTailValue) :
    (iotaListElimConsTailCong
      (headValue := headValue) (nilBranch := nilBranch)
      (consBranch := consBranch) tailStep).HasJoin :=
  (LocalDiamond.iotaListElimConsTailCong
    (headValue := headValue) (nilBranch := nilBranch)
    (consBranch := consBranch) tailStep).hasJoin

/-- Resolver arm for `listElim (listCons head tail)` iota competing with
nil-branch congruence. -/
theorem iotaListElimConsNilBranchCong_hasJoin {scope : Nat}
    {headValue tailValue nilBranch steppedNilBranch consBranch :
      RawTerm scope}
    (nilStep : Step nilBranch steppedNilBranch) :
    (iotaListElimConsNilBranchCong
      (headValue := headValue) (tailValue := tailValue)
      (consBranch := consBranch) nilStep).HasJoin :=
  (LocalDiamond.iotaListElimConsNilBranchCong
    (headValue := headValue) (tailValue := tailValue)
    (consBranch := consBranch) nilStep).hasJoin

/-- Resolver arm for `listElim (listCons head tail)` iota competing with
cons-branch congruence. -/
theorem iotaListElimConsConsBranchCong_hasJoin {scope : Nat}
    {headValue tailValue nilBranch consBranch steppedConsBranch :
      RawTerm scope}
    (consStep : Step consBranch steppedConsBranch) :
    (iotaListElimConsConsBranchCong
      (headValue := headValue) (tailValue := tailValue)
      (nilBranch := nilBranch) consStep).HasJoin :=
  (LocalDiamond.iotaListElimConsConsBranchCong
    (headValue := headValue) (tailValue := tailValue)
    (nilBranch := nilBranch) consStep).hasJoin

/-- Resolver arm for `listElim listNil` iota competing with selected
nil-branch congruence. -/
theorem iotaListElimNilBranchCong_hasJoin {scope : Nat}
    {nilBranch steppedNilBranch consBranch : RawTerm scope}
    (nilStep : Step nilBranch steppedNilBranch) :
    (iotaListElimNilBranchCong
      (consBranch := consBranch) nilStep).HasJoin :=
  (LocalDiamond.iotaListElimNilBranchCong
    (consBranch := consBranch) nilStep).hasJoin

/-- Resolver arm for `listElim listNil` iota competing with discarded
cons-branch congruence. -/
theorem iotaListElimConsBranchCong_hasJoin {scope : Nat}
    {nilBranch consBranch steppedConsBranch : RawTerm scope}
    (consStep : Step consBranch steppedConsBranch) :
    (iotaListElimConsBranchCong
      (nilBranch := nilBranch) consStep).HasJoin :=
  (LocalDiamond.iotaListElimConsBranchCong
    (nilBranch := nilBranch) consStep).hasJoin

/-- Resolver arm for `optionMatch optionNone` iota competing with selected
none-branch congruence. -/
theorem iotaOptionMatchNoneBranchCong_hasJoin {scope : Nat}
    {noneBranch steppedNoneBranch someBranch : RawTerm scope}
    (noneStep : Step noneBranch steppedNoneBranch) :
    (iotaOptionMatchNoneBranchCong
      (someBranch := someBranch) noneStep).HasJoin :=
  (LocalDiamond.iotaOptionMatchNoneBranchCong
    (someBranch := someBranch) noneStep).hasJoin

/-- Resolver arm for `optionMatch optionNone` iota competing with discarded
some-branch congruence. -/
theorem iotaOptionMatchSomeBranchCong_hasJoin {scope : Nat}
    {noneBranch someBranch steppedSomeBranch : RawTerm scope}
    (someStep : Step someBranch steppedSomeBranch) :
    (iotaOptionMatchSomeBranchCong
      (noneBranch := noneBranch) someStep).HasJoin :=
  (LocalDiamond.iotaOptionMatchSomeBranchCong
    (noneBranch := noneBranch) someStep).hasJoin

/-- Resolver arm for `optionMatch (optionSome value)` iota competing with
congruence inside the payload value. -/
theorem iotaOptionMatchSomeValueCong_hasJoin {scope : Nat}
    {value steppedValue noneBranch someBranch : RawTerm scope}
    (valueStep : Step value steppedValue) :
    (iotaOptionMatchSomeValueCong
      (noneBranch := noneBranch) (someBranch := someBranch)
      valueStep).HasJoin :=
  (LocalDiamond.iotaOptionMatchSomeValueCong
    (noneBranch := noneBranch) (someBranch := someBranch)
    valueStep).hasJoin

/-- Resolver arm for `optionMatch (optionSome value)` iota competing with
discarded none-branch congruence. -/
theorem iotaOptionMatchSomeNoneBranchCong_hasJoin {scope : Nat}
    {value noneBranch steppedNoneBranch someBranch : RawTerm scope}
    (noneStep : Step noneBranch steppedNoneBranch) :
    (iotaOptionMatchSomeNoneBranchCong
      (value := value) (someBranch := someBranch) noneStep).HasJoin :=
  (LocalDiamond.iotaOptionMatchSomeNoneBranchCong
    (value := value) (someBranch := someBranch) noneStep).hasJoin

/-- Resolver arm for `optionMatch (optionSome value)` iota competing with
selected some-branch congruence. -/
theorem iotaOptionMatchSomeSomeBranchCong_hasJoin {scope : Nat}
    {value noneBranch someBranch steppedSomeBranch : RawTerm scope}
    (someStep : Step someBranch steppedSomeBranch) :
    (iotaOptionMatchSomeSomeBranchCong
      (value := value) (noneBranch := noneBranch) someStep).HasJoin :=
  (LocalDiamond.iotaOptionMatchSomeSomeBranchCong
    (value := value) (noneBranch := noneBranch) someStep).hasJoin

/-- Resolver arm for `eitherMatch (eitherInl value)` iota competing with
congruence inside the left payload value. -/
theorem iotaEitherMatchInlValueCong_hasJoin {scope : Nat}
    {value steppedValue leftBranch rightBranch : RawTerm scope}
    (valueStep : Step value steppedValue) :
    (iotaEitherMatchInlValueCong
      (leftBranch := leftBranch) (rightBranch := rightBranch)
      valueStep).HasJoin :=
  (LocalDiamond.iotaEitherMatchInlValueCong
    (leftBranch := leftBranch) (rightBranch := rightBranch)
    valueStep).hasJoin

/-- Resolver arm for `eitherMatch (eitherInl value)` iota competing with
selected left-branch congruence. -/
theorem iotaEitherMatchInlLeftBranchCong_hasJoin {scope : Nat}
    {value leftBranch steppedLeftBranch rightBranch : RawTerm scope}
    (leftStep : Step leftBranch steppedLeftBranch) :
    (iotaEitherMatchInlLeftBranchCong
      (value := value) (rightBranch := rightBranch) leftStep).HasJoin :=
  (LocalDiamond.iotaEitherMatchInlLeftBranchCong
    (value := value) (rightBranch := rightBranch) leftStep).hasJoin

/-- Resolver arm for `eitherMatch (eitherInl value)` iota competing with
discarded right-branch congruence. -/
theorem iotaEitherMatchInlRightBranchCong_hasJoin {scope : Nat}
    {value leftBranch rightBranch steppedRightBranch : RawTerm scope}
    (rightStep : Step rightBranch steppedRightBranch) :
    (iotaEitherMatchInlRightBranchCong
      (value := value) (leftBranch := leftBranch) rightStep).HasJoin :=
  (LocalDiamond.iotaEitherMatchInlRightBranchCong
    (value := value) (leftBranch := leftBranch) rightStep).hasJoin

/-- Resolver arm for `eitherMatch (eitherInr value)` iota competing with
congruence inside the right payload value. -/
theorem iotaEitherMatchInrValueCong_hasJoin {scope : Nat}
    {value steppedValue leftBranch rightBranch : RawTerm scope}
    (valueStep : Step value steppedValue) :
    (iotaEitherMatchInrValueCong
      (leftBranch := leftBranch) (rightBranch := rightBranch)
      valueStep).HasJoin :=
  (LocalDiamond.iotaEitherMatchInrValueCong
    (leftBranch := leftBranch) (rightBranch := rightBranch)
    valueStep).hasJoin

/-- Resolver arm for `eitherMatch (eitherInr value)` iota competing with
discarded left-branch congruence. -/
theorem iotaEitherMatchInrLeftBranchCong_hasJoin {scope : Nat}
    {value leftBranch steppedLeftBranch rightBranch : RawTerm scope}
    (leftStep : Step leftBranch steppedLeftBranch) :
    (iotaEitherMatchInrLeftBranchCong
      (value := value) (rightBranch := rightBranch) leftStep).HasJoin :=
  (LocalDiamond.iotaEitherMatchInrLeftBranchCong
    (value := value) (rightBranch := rightBranch) leftStep).hasJoin

/-- Resolver arm for `eitherMatch (eitherInr value)` iota competing with
selected right-branch congruence. -/
theorem iotaEitherMatchInrRightBranchCong_hasJoin {scope : Nat}
    {value leftBranch rightBranch steppedRightBranch : RawTerm scope}
    (rightStep : Step rightBranch steppedRightBranch) :
    (iotaEitherMatchInrRightBranchCong
      (value := value) (leftBranch := leftBranch) rightStep).HasJoin :=
  (LocalDiamond.iotaEitherMatchInrRightBranchCong
    (value := value) (leftBranch := leftBranch) rightStep).hasJoin

/-- Resolver arm for `idJ refl` iota competing with selected base-case
congruence. -/
theorem iotaIdJBaseCaseCong_hasJoin {scope : Nat}
    {baseCase steppedBaseCase rawWitness : RawTerm scope}
    (baseStep : Step baseCase steppedBaseCase) :
    (iotaIdJBaseCaseCong
      (rawWitness := rawWitness) baseStep).HasJoin :=
  (LocalDiamond.iotaIdJBaseCaseCong
    (rawWitness := rawWitness) baseStep).hasJoin

/-- Resolver arm for `idJ refl` iota competing with discarded witness
congruence. -/
theorem iotaIdJWitnessCong_hasJoin {scope : Nat}
    {baseCase rawWitness steppedRawWitness : RawTerm scope}
    (witnessStep : Step rawWitness steppedRawWitness) :
    (iotaIdJWitnessCong
      (baseCase := baseCase) witnessStep).HasJoin :=
  (LocalDiamond.iotaIdJWitnessCong
    (baseCase := baseCase) witnessStep).hasJoin

/-- Resolver arm for `idStrictRec refl` iota competing with selected
base-case congruence. -/
theorem iotaIdStrictRecBaseCaseCong_hasJoin {scope : Nat}
    {baseCase steppedBaseCase rawWitness : RawTerm scope}
    (baseStep : Step baseCase steppedBaseCase) :
    (iotaIdStrictRecBaseCaseCong
      (rawWitness := rawWitness) baseStep).HasJoin :=
  (LocalDiamond.iotaIdStrictRecBaseCaseCong
    (rawWitness := rawWitness) baseStep).hasJoin

/-- Resolver arm for `idStrictRec refl` iota competing with discarded
witness congruence. -/
theorem iotaIdStrictRecWitnessCong_hasJoin {scope : Nat}
    {baseCase rawWitness steppedRawWitness : RawTerm scope}
    (witnessStep : Step rawWitness steppedRawWitness) :
    (iotaIdStrictRecWitnessCong
      (baseCase := baseCase) witnessStep).HasJoin :=
  (LocalDiamond.iotaIdStrictRecWitnessCong
    (baseCase := baseCase) witnessStep).hasJoin

/-- `fromSteps`-facing `listElim listCons` iota / head congruence arm. -/
theorem fromSteps_iotaListElimConsHeadCong_hasJoin {scope : Nat}
    {headValue steppedHeadValue tailValue nilBranch consBranch :
      RawTerm scope}
    (headStep : Step headValue steppedHeadValue) :
    (fromSteps
      (Step.iotaListElimCons
        (headVal := headValue) (tailVal := tailValue)
        (nilBranch := nilBranch) (consBranch := consBranch))
      (iotaListElimConsHeadCong
        (tailValue := tailValue) (nilBranch := nilBranch)
        (consBranch := consBranch) headStep).rightStep).HasJoin :=
  iotaListElimConsHeadCong_hasJoin headStep

/-- `fromSteps`-facing `listElim listCons` iota / tail congruence arm. -/
theorem fromSteps_iotaListElimConsTailCong_hasJoin {scope : Nat}
    {headValue tailValue steppedTailValue nilBranch consBranch :
      RawTerm scope}
    (tailStep : Step tailValue steppedTailValue) :
    (fromSteps
      (Step.iotaListElimCons
        (headVal := headValue) (tailVal := tailValue)
        (nilBranch := nilBranch) (consBranch := consBranch))
      (iotaListElimConsTailCong
        (headValue := headValue) (nilBranch := nilBranch)
        (consBranch := consBranch) tailStep).rightStep).HasJoin :=
  iotaListElimConsTailCong_hasJoin tailStep

/-- `fromSteps`-facing `listElim listCons` iota / nil-branch congruence arm. -/
theorem fromSteps_iotaListElimConsNilBranchCong_hasJoin {scope : Nat}
    {headValue tailValue nilBranch steppedNilBranch consBranch :
      RawTerm scope}
    (nilStep : Step nilBranch steppedNilBranch) :
    (fromSteps
      (Step.iotaListElimCons
        (headVal := headValue) (tailVal := tailValue)
        (nilBranch := nilBranch) (consBranch := consBranch))
      (iotaListElimConsNilBranchCong
        (headValue := headValue) (tailValue := tailValue)
        (consBranch := consBranch) nilStep).rightStep).HasJoin :=
  iotaListElimConsNilBranchCong_hasJoin nilStep

/-- `fromSteps`-facing `listElim listCons` iota / cons-branch congruence arm. -/
theorem fromSteps_iotaListElimConsConsBranchCong_hasJoin {scope : Nat}
    {headValue tailValue nilBranch consBranch steppedConsBranch :
      RawTerm scope}
    (consStep : Step consBranch steppedConsBranch) :
    (fromSteps
      (Step.iotaListElimCons
        (headVal := headValue) (tailVal := tailValue)
        (nilBranch := nilBranch) (consBranch := consBranch))
      (iotaListElimConsConsBranchCong
        (headValue := headValue) (tailValue := tailValue)
        (nilBranch := nilBranch) consStep).rightStep).HasJoin :=
  iotaListElimConsConsBranchCong_hasJoin consStep

/-- `fromSteps`-facing `listElim listNil` iota / nil-branch congruence arm. -/
theorem fromSteps_iotaListElimNilBranchCong_hasJoin {scope : Nat}
    {nilBranch steppedNilBranch consBranch : RawTerm scope}
    (nilStep : Step nilBranch steppedNilBranch) :
    (fromSteps
      (Step.iotaListElimNil
        (nilBranch := nilBranch) (consBranch := consBranch))
      (iotaListElimNilBranchCong
        (consBranch := consBranch) nilStep).rightStep).HasJoin :=
  iotaListElimNilBranchCong_hasJoin nilStep

/-- `fromSteps`-facing `listElim listNil` iota / cons-branch congruence arm. -/
theorem fromSteps_iotaListElimConsBranchCong_hasJoin {scope : Nat}
    {nilBranch consBranch steppedConsBranch : RawTerm scope}
    (consStep : Step consBranch steppedConsBranch) :
    (fromSteps
      (Step.iotaListElimNil
        (nilBranch := nilBranch) (consBranch := consBranch))
      (iotaListElimConsBranchCong
        (nilBranch := nilBranch) consStep).rightStep).HasJoin :=
  iotaListElimConsBranchCong_hasJoin consStep

/-- `fromSteps`-facing `optionMatch optionNone` iota / none-branch congruence arm. -/
theorem fromSteps_iotaOptionMatchNoneBranchCong_hasJoin {scope : Nat}
    {noneBranch steppedNoneBranch someBranch : RawTerm scope}
    (noneStep : Step noneBranch steppedNoneBranch) :
    (fromSteps
      (Step.iotaOptionMatchNone
        (noneBranch := noneBranch) (someBranch := someBranch))
      (iotaOptionMatchNoneBranchCong
        (someBranch := someBranch) noneStep).rightStep).HasJoin :=
  iotaOptionMatchNoneBranchCong_hasJoin noneStep

/-- `fromSteps`-facing `optionMatch optionNone` iota / some-branch congruence arm. -/
theorem fromSteps_iotaOptionMatchSomeBranchCong_hasJoin {scope : Nat}
    {noneBranch someBranch steppedSomeBranch : RawTerm scope}
    (someStep : Step someBranch steppedSomeBranch) :
    (fromSteps
      (Step.iotaOptionMatchNone
        (noneBranch := noneBranch) (someBranch := someBranch))
      (iotaOptionMatchSomeBranchCong
        (noneBranch := noneBranch) someStep).rightStep).HasJoin :=
  iotaOptionMatchSomeBranchCong_hasJoin someStep

/-- `fromSteps`-facing `optionMatch optionSome` iota / value congruence arm. -/
theorem fromSteps_iotaOptionMatchSomeValueCong_hasJoin {scope : Nat}
    {value steppedValue noneBranch someBranch : RawTerm scope}
    (valueStep : Step value steppedValue) :
    (fromSteps
      (Step.iotaOptionMatchSome
        (value := value) (noneBranch := noneBranch)
        (someBranch := someBranch))
      (iotaOptionMatchSomeValueCong
        (noneBranch := noneBranch) (someBranch := someBranch)
        valueStep).rightStep).HasJoin :=
  iotaOptionMatchSomeValueCong_hasJoin valueStep

/-- `fromSteps`-facing `optionMatch optionSome` iota / none-branch congruence arm. -/
theorem fromSteps_iotaOptionMatchSomeNoneBranchCong_hasJoin {scope : Nat}
    {value noneBranch steppedNoneBranch someBranch : RawTerm scope}
    (noneStep : Step noneBranch steppedNoneBranch) :
    (fromSteps
      (Step.iotaOptionMatchSome
        (value := value) (noneBranch := noneBranch)
        (someBranch := someBranch))
      (iotaOptionMatchSomeNoneBranchCong
        (value := value) (someBranch := someBranch)
        noneStep).rightStep).HasJoin :=
  iotaOptionMatchSomeNoneBranchCong_hasJoin noneStep

/-- `fromSteps`-facing `optionMatch optionSome` iota / some-branch congruence arm. -/
theorem fromSteps_iotaOptionMatchSomeSomeBranchCong_hasJoin {scope : Nat}
    {value noneBranch someBranch steppedSomeBranch : RawTerm scope}
    (someStep : Step someBranch steppedSomeBranch) :
    (fromSteps
      (Step.iotaOptionMatchSome
        (value := value) (noneBranch := noneBranch)
        (someBranch := someBranch))
      (iotaOptionMatchSomeSomeBranchCong
        (value := value) (noneBranch := noneBranch)
        someStep).rightStep).HasJoin :=
  iotaOptionMatchSomeSomeBranchCong_hasJoin someStep

/-- `fromSteps`-facing `eitherMatch eitherInl` iota / value congruence arm. -/
theorem fromSteps_iotaEitherMatchInlValueCong_hasJoin {scope : Nat}
    {value steppedValue leftBranch rightBranch : RawTerm scope}
    (valueStep : Step value steppedValue) :
    (fromSteps
      (Step.iotaEitherMatchInl
        (value := value) (leftBranch := leftBranch)
        (rightBranch := rightBranch))
      (iotaEitherMatchInlValueCong
        (leftBranch := leftBranch) (rightBranch := rightBranch)
        valueStep).rightStep).HasJoin :=
  iotaEitherMatchInlValueCong_hasJoin valueStep

/-- `fromSteps`-facing `eitherMatch eitherInl` iota / left-branch congruence arm. -/
theorem fromSteps_iotaEitherMatchInlLeftBranchCong_hasJoin {scope : Nat}
    {value leftBranch steppedLeftBranch rightBranch : RawTerm scope}
    (leftStep : Step leftBranch steppedLeftBranch) :
    (fromSteps
      (Step.iotaEitherMatchInl
        (value := value) (leftBranch := leftBranch)
        (rightBranch := rightBranch))
      (iotaEitherMatchInlLeftBranchCong
        (value := value) (rightBranch := rightBranch)
        leftStep).rightStep).HasJoin :=
  iotaEitherMatchInlLeftBranchCong_hasJoin leftStep

/-- `fromSteps`-facing `eitherMatch eitherInl` iota / right-branch congruence arm. -/
theorem fromSteps_iotaEitherMatchInlRightBranchCong_hasJoin {scope : Nat}
    {value leftBranch rightBranch steppedRightBranch : RawTerm scope}
    (rightStep : Step rightBranch steppedRightBranch) :
    (fromSteps
      (Step.iotaEitherMatchInl
        (value := value) (leftBranch := leftBranch)
        (rightBranch := rightBranch))
      (iotaEitherMatchInlRightBranchCong
        (value := value) (leftBranch := leftBranch)
        rightStep).rightStep).HasJoin :=
  iotaEitherMatchInlRightBranchCong_hasJoin rightStep

/-- `fromSteps`-facing `eitherMatch eitherInr` iota / value congruence arm. -/
theorem fromSteps_iotaEitherMatchInrValueCong_hasJoin {scope : Nat}
    {value steppedValue leftBranch rightBranch : RawTerm scope}
    (valueStep : Step value steppedValue) :
    (fromSteps
      (Step.iotaEitherMatchInr
        (value := value) (leftBranch := leftBranch)
        (rightBranch := rightBranch))
      (iotaEitherMatchInrValueCong
        (leftBranch := leftBranch) (rightBranch := rightBranch)
        valueStep).rightStep).HasJoin :=
  iotaEitherMatchInrValueCong_hasJoin valueStep

/-- `fromSteps`-facing `eitherMatch eitherInr` iota / left-branch congruence arm. -/
theorem fromSteps_iotaEitherMatchInrLeftBranchCong_hasJoin {scope : Nat}
    {value leftBranch steppedLeftBranch rightBranch : RawTerm scope}
    (leftStep : Step leftBranch steppedLeftBranch) :
    (fromSteps
      (Step.iotaEitherMatchInr
        (value := value) (leftBranch := leftBranch)
        (rightBranch := rightBranch))
      (iotaEitherMatchInrLeftBranchCong
        (value := value) (rightBranch := rightBranch)
        leftStep).rightStep).HasJoin :=
  iotaEitherMatchInrLeftBranchCong_hasJoin leftStep

/-- `fromSteps`-facing `eitherMatch eitherInr` iota / right-branch congruence arm. -/
theorem fromSteps_iotaEitherMatchInrRightBranchCong_hasJoin {scope : Nat}
    {value leftBranch rightBranch steppedRightBranch : RawTerm scope}
    (rightStep : Step rightBranch steppedRightBranch) :
    (fromSteps
      (Step.iotaEitherMatchInr
        (value := value) (leftBranch := leftBranch)
        (rightBranch := rightBranch))
      (iotaEitherMatchInrRightBranchCong
        (value := value) (leftBranch := leftBranch)
        rightStep).rightStep).HasJoin :=
  iotaEitherMatchInrRightBranchCong_hasJoin rightStep

/-- `fromSteps`-facing `idJ refl` iota / base-case congruence arm. -/
theorem fromSteps_iotaIdJBaseCaseCong_hasJoin {scope : Nat}
    {baseCase steppedBaseCase rawWitness : RawTerm scope}
    (baseStep : Step baseCase steppedBaseCase) :
    (fromSteps
      (Step.iotaIdJRefl
        (baseCase := baseCase) (rawWitness := rawWitness))
      (iotaIdJBaseCaseCong
        (rawWitness := rawWitness) baseStep).rightStep).HasJoin :=
  iotaIdJBaseCaseCong_hasJoin baseStep

/-- `fromSteps`-facing `idJ refl` iota / witness congruence arm. -/
theorem fromSteps_iotaIdJWitnessCong_hasJoin {scope : Nat}
    {baseCase rawWitness steppedRawWitness : RawTerm scope}
    (witnessStep : Step rawWitness steppedRawWitness) :
    (fromSteps
      (Step.iotaIdJRefl
        (baseCase := baseCase) (rawWitness := rawWitness))
      (iotaIdJWitnessCong
        (baseCase := baseCase) witnessStep).rightStep).HasJoin :=
  iotaIdJWitnessCong_hasJoin witnessStep

/-- `fromSteps`-facing `idStrictRec refl` iota / base-case congruence arm. -/
theorem fromSteps_iotaIdStrictRecBaseCaseCong_hasJoin {scope : Nat}
    {baseCase steppedBaseCase rawWitness : RawTerm scope}
    (baseStep : Step baseCase steppedBaseCase) :
    (fromSteps
      (Step.iotaIdStrictRecRefl
        (baseCase := baseCase) (rawWitness := rawWitness))
      (iotaIdStrictRecBaseCaseCong
        (rawWitness := rawWitness) baseStep).rightStep).HasJoin :=
  iotaIdStrictRecBaseCaseCong_hasJoin baseStep

/-- `fromSteps`-facing `idStrictRec refl` iota / witness congruence arm. -/
theorem fromSteps_iotaIdStrictRecWitnessCong_hasJoin {scope : Nat}
    {baseCase rawWitness steppedRawWitness : RawTerm scope}
    (witnessStep : Step rawWitness steppedRawWitness) :
    (fromSteps
      (Step.iotaIdStrictRecRefl
        (baseCase := baseCase) (rawWitness := rawWitness))
      (iotaIdStrictRecWitnessCong
        (baseCase := baseCase) witnessStep).rightStep).HasJoin :=
  iotaIdStrictRecWitnessCong_hasJoin witnessStep

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

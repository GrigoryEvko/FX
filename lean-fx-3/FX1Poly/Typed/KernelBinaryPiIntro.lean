import FX1Poly.Typed.KernelBinaryPiElim
import FX1Poly.Core.HeadExpansionClosure
import FX1Poly.Core.RawTermSubstConsCommute
import FX1Poly.Core.StrongNormalizationConstructors

/-! # FX1Poly/Typed/KernelBinaryPiIntro
    — the binary Π-INTRODUCTION (λ-pair) arm: two-sided head-expansion closure + env cons (OP1-K2 brick 2)

The binder crux of the binary fundamental theorem, mirroring the unary
`DenoteKeyedBoundedPiIntroArm` chain.  As with determinism (brick 1), the unary's forget-bridge
economy is unavailable — the unary head-expansion closure transferred to the denote engine; the
binary closure is a DIRECT induction, ONE PER SIDE:

  * `BinaryHeadExpansionClosedLeft` / `Right` — spine-general β-head-expansion closure of a
    binary candidate on one side, the other member held fixed (the one-sided formulation is
    what lets the Π arm absorb the extra application argument into the spine on its own side).
  * `binaryDenoteBelowFamilyBounded_eq_empty_of_ge` + the one-sided
    `binaryDenoteBelowFamilyBounded_backwardWeakHeadStepLeft/Right` legs (by-cases ports).
  * ★ `BinaryReducibleTypeStepBounded.headExpansionClosedLeft/Right` — every candidate the
    binary relation assigns is head-expansion-closed on each side (8-arm inductions; the
    `dataFlat` arm additionally prepends the β step to the Conv conjunct — the same-value
    refinement is expansion-stable).
  * `BinaryReducibleTypeAtBounded.reducibleMemberPairCandidate` — the canonical member-PAIR
    candidate (the choice-free engine, via brick 1's determinism).
  * `BinaryReducibleEnvAtBounded.cons` — extend a related substitution pair under a binder.
  * ★ `binaryAbstractionMemberPairAtBounded` (+ the closing-substitution form) — the λ-PAIR is
    a related member pair of the Π pair: expand the body-instance pair back through β on the
    right, then on the left.
  * ★ `binaryFundamentalPiIntroArm` — the piIntro FT arm over the binary motive, pinning both
    candidates to the canonical member-pair predicate and threading the env cons.

Honest scope: the conv arm (binary Conv-invariance) and the former/telescope arms remain for
the next K2 bricks; with var + piElim (brick 1) + piIntro (this brick), the λΠ-fragment arms
of the binary FT are complete.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-! ## One-sided spine-general head-expansion closure -/

/-- A binary candidate is **head-expansion-closed on the LEFT**: the spined β-redex inherits
membership from its spined contractum in the left component, the right member held fixed
(annotation and argument SN, as in the unary `HeadExpansionClosed`). -/
def BinaryHeadExpansionClosedLeft {scope : Nat} (relation : BinaryCandidate scope) : Prop :=
  ∀ {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)} {argument : RawTerm scope}
    {spine : List (RawTerm scope)} {rightTerm : RawTerm scope},
    IsStronglyNormalizing domainAnn →
    IsStronglyNormalizing argument →
    relation (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine) rightTerm →
    relation
      (RawTerm.applySpineApp
        (.mkGen .gen_app ()
          (.childCons (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
            (.childCons argument .childNil)))
        spine)
      rightTerm

/-- A binary candidate is **head-expansion-closed on the RIGHT** (mirror). -/
def BinaryHeadExpansionClosedRight {scope : Nat} (relation : BinaryCandidate scope) : Prop :=
  ∀ {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)} {argument : RawTerm scope}
    {spine : List (RawTerm scope)} {leftTerm : RawTerm scope},
    IsStronglyNormalizing domainAnn →
    IsStronglyNormalizing argument →
    relation leftTerm (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine) →
    relation leftTerm
      (RawTerm.applySpineApp
        (.mkGen .gen_app ()
          (.childCons (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
            (.childCons argument .childNil)))
        spine)

/-! ## The below-family backward legs -/

/-- At or above the bound, the binary below-family is the empty relation (mirror of
`denoteBelowFamilyBounded_eq_empty_of_ge`). -/
theorem binaryDenoteBelowFamilyBounded_eq_empty_of_ge {scope : Nat} (env : Nat → Nat) :
    ∀ (bound lvl : Nat), bound ≤ lvl →
      binaryDenoteBelowFamilyBounded (scope := scope) env bound lvl
        = (fun _ _ _ => False) := by
  intro bound
  induction bound with
  | zero => intro lvl _; rfl
  | succ predBound _ih =>
      intro lvl hle
      have predLessThan : predBound < lvl :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self predBound) hle
      show (if lvl < predBound then binaryDenoteBelowFamilyBounded env predBound lvl
            else if lvl = predBound then
              BinaryReducibleTypeStepBounded env
                (binaryDenoteBelowFamilyBounded env predBound) predBound
            else fun _ _ _ => False) = fun _ _ _ => False
      rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt predLessThan)),
        if_neg (Ne.symm (Nat.ne_of_lt predLessThan))]

/-- Backward weak-head step for the binary below-family on the LEFT index (by-cases port:
coherence + `whnfExpandLeft` below the bound; vacuous at/above). -/
theorem binaryDenoteBelowFamilyBounded_backwardWeakHeadStepLeft {scope : Nat} (env : Nat → Nat)
    (bound : Nat) (lvl : Nat) {leftCode leftReduct rightCode : RawTerm scope}
    {relation : BinaryCandidate scope}
    (member : binaryDenoteBelowFamilyBounded env bound lvl leftReduct rightCode relation)
    (weakHeadStep : WeakHeadStep leftCode leftReduct) :
    binaryDenoteBelowFamilyBounded env bound lvl leftCode rightCode relation := by
  by_cases hlt : lvl < bound
  · rw [binaryDenoteBelowFamilyBounded_eq_reducible env bound lvl hlt] at member ⊢
    exact BinaryReducibleTypeStepBounded.whnfExpandLeft weakHeadStep member
  · rw [binaryDenoteBelowFamilyBounded_eq_empty_of_ge env bound lvl (Nat.not_lt.mp hlt)]
      at member
    exact member.elim

/-- Backward weak-head step for the binary below-family on the RIGHT index (mirror). -/
theorem binaryDenoteBelowFamilyBounded_backwardWeakHeadStepRight {scope : Nat} (env : Nat → Nat)
    (bound : Nat) (lvl : Nat) {leftCode rightCode rightReduct : RawTerm scope}
    {relation : BinaryCandidate scope}
    (member : binaryDenoteBelowFamilyBounded env bound lvl leftCode rightReduct relation)
    (weakHeadStep : WeakHeadStep rightCode rightReduct) :
    binaryDenoteBelowFamilyBounded env bound lvl leftCode rightCode relation := by
  by_cases hlt : lvl < bound
  · rw [binaryDenoteBelowFamilyBounded_eq_reducible env bound lvl hlt] at member ⊢
    exact BinaryReducibleTypeStepBounded.whnfExpandRight weakHeadStep member
  · rw [binaryDenoteBelowFamilyBounded_eq_empty_of_ge env bound lvl (Nat.not_lt.mp hlt)]
      at member
    exact member.elim

/-! ## ★ Every assigned binary candidate is head-expansion-closed (one direct induction per side) -/

/-- ★ **LEFT head-expansion closure of every assigned binary candidate** (parametric in
`lowerAt`, with the left leg).  Direct 8-arm induction — the unary's forget-bridge transfer is
unavailable.  The `dataFlat` arm shows the same-value candidate is expansion-stable: the Conv
conjunct absorbs the β step by prepending it to the left chain. -/
theorem BinaryReducibleTypeStepBounded.headExpansionClosedLeft {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    (lowerHeadExpandLeft : ∀ (lvl : Nat) {domainAnn : RawTerm scope}
      {body : RawTerm (scope + 1)} {argument : RawTerm scope}
      {spine : List (RawTerm scope)} {rightCode : RawTerm scope}
      {lowerRelation : BinaryCandidate scope},
      lowerAt lvl (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine) rightCode
        lowerRelation →
      lowerAt lvl (RawTerm.applySpineApp
        (.mkGen .gen_app ()
          (.childCons (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
            (.childCons argument .childNil)))
        spine) rightCode lowerRelation)
    {leftCode rightCode : RawTerm scope} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation) :
    BinaryHeadExpansionClosedLeft relation := by
  induction related with
  | whnfExpandLeft _weakHeadStep _reductRelated reductIH =>
      exact reductIH
  | whnfExpandRight _weakHeadStep _reductRelated reductIH =>
      exact reductIH
  | neutral _ _ _ _ _ _ _ _ _ _ =>
      intro _domainAnn _body _argument _spine _rightTerm domainAnnSN argumentSN membership
      exact ⟨betaSpineHeadExpansion domainAnnSN argumentSN membership.1, membership.2⟩
  | piType codomainRelation _leftDomainUnary _rightDomainUnary _domainsRelated
      _codomainsRelated _domainIH codomainIH =>
      intro domainAnn body argument spine rightTerm domainAnnSN argumentSN contractumRelated
      refine ⟨betaSpineHeadExpansion domainAnnSN argumentSN contractumRelated.1,
        contractumRelated.2.1, ?_⟩
      intro extraLeft extraRight leftGuard rightGuard extraRelated
      have contractumAtExtendedSpine :
          codomainRelation extraLeft extraRight
            (RawTerm.applySpineApp (RawTerm.subst0 body argument) (spine ++ [extraLeft]))
            (.mkGen .gen_app () (.childCons rightTerm (.childCons extraRight .childNil))) := by
        rw [applySpineApp_append]
        exact contractumRelated.2.2 extraLeft extraRight leftGuard rightGuard extraRelated
      have redexAtExtendedSpine :
          codomainRelation extraLeft extraRight
            (RawTerm.applySpineApp
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
                  (.childCons argument .childNil)))
              (spine ++ [extraLeft]))
            (.mkGen .gen_app () (.childCons rightTerm (.childCons extraRight .childNil))) :=
        (codomainIH extraLeft extraRight leftGuard rightGuard extraRelated)
          domainAnnSN argumentSN contractumAtExtendedSpine
      rw [applySpineApp_append] at redexAtExtendedSpine
      exact redexAtExtendedSpine
  | universeCode levelExpr _flag _belowBound =>
      intro _domainAnn _body _argument _spine _rightTerm domainAnnSN argumentSN membership
      obtain ⟨leftSN, rightSN, lowerRelation, lowerRelated⟩ := membership
      exact ⟨betaSpineHeadExpansion domainAnnSN argumentSN leftSN, rightSN,
        lowerRelation, lowerHeadExpandLeft (LevelExpr.denote levelExpr env) lowerRelated⟩
  | dataEmpty =>
      intro _domainAnn _body _argument _spine _rightTerm domainAnnSN argumentSN membership
      exact ⟨emptyTaitCandidate_headExpansionClosed domainAnnSN argumentSN membership.1,
        membership.2⟩
  | dataFlat _flatPinned _headsAgree =>
      intro _domainAnn _body _argument _spine _rightTerm domainAnnSN argumentSN membership
      obtain ⟨leftMember, rightMember, ⟨commonTerm, leftChain, rightChain⟩⟩ := membership
      exact ⟨dataTaitCandidate_headExpansionClosed domainAnnSN argumentSN leftMember,
        rightMember,
        ⟨commonTerm, StepStar.trans (WeakHeadStep.betaSpine).toStep leftChain, rightChain⟩⟩
  | ofPointwiseIff _innerRelated pointwiseIff innerIH =>
      intro _domainAnn _body _argument _spine _rightTerm domainAnnSN argumentSN membership
      exact (pointwiseIff _ _).mp
        (innerIH domainAnnSN argumentSN ((pointwiseIff _ _).mpr membership))

/-- ★ **RIGHT head-expansion closure** — the mirror induction with the right leg. -/
theorem BinaryReducibleTypeStepBounded.headExpansionClosedRight {scope : Nat} {env : Nat → Nat}
    {lowerAt : Nat → RawTerm scope → RawTerm scope → BinaryCandidate scope → Prop} {bound : Nat}
    (lowerHeadExpandRight : ∀ (lvl : Nat) {domainAnn : RawTerm scope}
      {body : RawTerm (scope + 1)} {argument : RawTerm scope}
      {spine : List (RawTerm scope)} {leftCode : RawTerm scope}
      {lowerRelation : BinaryCandidate scope},
      lowerAt lvl leftCode (RawTerm.applySpineApp (RawTerm.subst0 body argument) spine)
        lowerRelation →
      lowerAt lvl leftCode (RawTerm.applySpineApp
        (.mkGen .gen_app ()
          (.childCons (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
            (.childCons argument .childNil)))
        spine) lowerRelation)
    {leftCode rightCode : RawTerm scope} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeStepBounded env lowerAt bound leftCode rightCode relation) :
    BinaryHeadExpansionClosedRight relation := by
  induction related with
  | whnfExpandLeft _weakHeadStep _reductRelated reductIH =>
      exact reductIH
  | whnfExpandRight _weakHeadStep _reductRelated reductIH =>
      exact reductIH
  | neutral _ _ _ _ _ _ _ _ _ _ =>
      intro _domainAnn _body _argument _spine _leftTerm domainAnnSN argumentSN membership
      exact ⟨membership.1, betaSpineHeadExpansion domainAnnSN argumentSN membership.2⟩
  | piType codomainRelation _leftDomainUnary _rightDomainUnary _domainsRelated
      _codomainsRelated _domainIH codomainIH =>
      intro domainAnn body argument spine leftTerm domainAnnSN argumentSN contractumRelated
      refine ⟨contractumRelated.1,
        betaSpineHeadExpansion domainAnnSN argumentSN contractumRelated.2.1, ?_⟩
      intro extraLeft extraRight leftGuard rightGuard extraRelated
      have contractumAtExtendedSpine :
          codomainRelation extraLeft extraRight
            (.mkGen .gen_app () (.childCons leftTerm (.childCons extraLeft .childNil)))
            (RawTerm.applySpineApp (RawTerm.subst0 body argument) (spine ++ [extraRight])) := by
        rw [applySpineApp_append]
        exact contractumRelated.2.2 extraLeft extraRight leftGuard rightGuard extraRelated
      have redexAtExtendedSpine :
          codomainRelation extraLeft extraRight
            (.mkGen .gen_app () (.childCons leftTerm (.childCons extraLeft .childNil)))
            (RawTerm.applySpineApp
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
                  (.childCons argument .childNil)))
              (spine ++ [extraRight])) :=
        (codomainIH extraLeft extraRight leftGuard rightGuard extraRelated)
          domainAnnSN argumentSN contractumAtExtendedSpine
      rw [applySpineApp_append] at redexAtExtendedSpine
      exact redexAtExtendedSpine
  | universeCode levelExpr _flag _belowBound =>
      intro _domainAnn _body _argument _spine _leftTerm domainAnnSN argumentSN membership
      obtain ⟨leftSN, rightSN, lowerRelation, lowerRelated⟩ := membership
      exact ⟨leftSN, betaSpineHeadExpansion domainAnnSN argumentSN rightSN,
        lowerRelation, lowerHeadExpandRight (LevelExpr.denote levelExpr env) lowerRelated⟩
  | dataEmpty =>
      intro _domainAnn _body _argument _spine _leftTerm domainAnnSN argumentSN membership
      exact ⟨membership.1,
        emptyTaitCandidate_headExpansionClosed domainAnnSN argumentSN membership.2⟩
  | dataFlat _flatPinned _headsAgree =>
      intro _domainAnn _body _argument _spine _leftTerm domainAnnSN argumentSN membership
      obtain ⟨leftMember, rightMember, ⟨commonTerm, leftChain, rightChain⟩⟩ := membership
      exact ⟨leftMember,
        dataTaitCandidate_headExpansionClosed domainAnnSN argumentSN rightMember,
        ⟨commonTerm, leftChain, StepStar.trans (WeakHeadStep.betaSpine).toStep rightChain⟩⟩
  | ofPointwiseIff _innerRelated pointwiseIff innerIH =>
      intro _domainAnn _body _argument _spine _leftTerm domainAnnSN argumentSN membership
      exact (pointwiseIff _ _).mp
        (innerIH domainAnnSN argumentSN ((pointwiseIff _ _).mpr membership))

/-- Family-level LEFT closure (discharges the leg via the below-family backward step). -/
theorem BinaryReducibleTypeAtBounded.headExpansionClosedLeft {scope : Nat} {env : Nat → Nat}
    {bound : Nat} {leftCode rightCode : RawTerm scope} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeAtBounded env bound leftCode rightCode relation) :
    BinaryHeadExpansionClosedLeft relation := by
  refine BinaryReducibleTypeStepBounded.headExpansionClosedLeft ?leg related
  intro lvl _domainAnn _body _argument _spine _rightCode _lowerRelation lowerMember
  exact binaryDenoteBelowFamilyBounded_backwardWeakHeadStepLeft env bound lvl lowerMember
    WeakHeadStep.betaSpine

/-- Family-level RIGHT closure (mirror). -/
theorem BinaryReducibleTypeAtBounded.headExpansionClosedRight {scope : Nat} {env : Nat → Nat}
    {bound : Nat} {leftCode rightCode : RawTerm scope} {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeAtBounded env bound leftCode rightCode relation) :
    BinaryHeadExpansionClosedRight relation := by
  refine BinaryReducibleTypeStepBounded.headExpansionClosedRight ?leg related
  intro lvl _domainAnn _body _argument _spine _leftCode _lowerRelation lowerMember
  exact binaryDenoteBelowFamilyBounded_backwardWeakHeadStepRight env bound lvl lowerMember
    WeakHeadStep.betaSpine

/-! ## The canonical member-pair candidate + the binary env cons -/

/-- **The canonical member-PAIR predicate is the pair's own candidate** — the choice-free
engine (via brick 1's determinism), the binary twin of `reducibleMemberCandidate`. -/
theorem BinaryReducibleTypeAtBounded.reducibleMemberPairCandidate {scope : Nat}
    {env : Nat → Nat} {bound : Nat} {leftCode rightCode : RawTerm scope}
    {relation : BinaryCandidate scope}
    (related : BinaryReducibleTypeAtBounded env bound leftCode rightCode relation) :
    BinaryReducibleTypeAtBounded env bound leftCode rightCode
      (fun leftTerm rightTerm =>
        IsBinaryReducibleMemberPairAtBounded env bound leftCode rightCode
          leftTerm rightTerm) := by
  refine BinaryReducibleTypeStepBounded.ofPointwiseIff related
    (fun leftTerm rightTerm => ?_)
  constructor
  · intro inRelation
    exact ⟨relation, related, inRelation⟩
  · intro memberPair
    obtain ⟨otherRelation, otherRelated, otherMembership⟩ := memberPair
    exact (BinaryReducibleTypeAtBounded.deterministic otherRelated related
      leftTerm rightTerm).mp otherMembership

/-- Existence of a binary candidate suffices for the canonical member-pair candidate. -/
theorem IsBinaryReducibleTypePairAtBounded.reducibleMemberPairCandidate {scope : Nat}
    {env : Nat → Nat} {bound : Nat} {leftCode rightCode : RawTerm scope}
    (relatedPair : IsBinaryReducibleTypePairAtBounded env bound leftCode rightCode) :
    BinaryReducibleTypeAtBounded env bound leftCode rightCode
      (fun leftTerm rightTerm =>
        IsBinaryReducibleMemberPairAtBounded env bound leftCode rightCode
          leftTerm rightTerm) :=
  let ⟨_relation, related⟩ := relatedPair
  related.reducibleMemberPairCandidate

/-- **Extend a binary-related environment at a binder** — the binary env cons: variable 0
lands on the related head pair (the weakened lookup cancels on each side); variable `k+1`
routes to the tail. -/
theorem BinaryReducibleEnvAtBounded.cons {profile : PolyProfile} {scope targetScope : Nat}
    {env : Nat → Nat} {bound : Nat}
    {context : TypingContext profile scope} {bindingType : RawTerm scope}
    {leftTail rightTail : RawTermSubst scope targetScope}
    {leftHead rightHead : RawTerm targetScope}
    (tailRelated : BinaryReducibleEnvAtBounded env bound context leftTail rightTail)
    (headRelated : IsBinaryReducibleMemberPairAtBounded env bound
      (RawTerm.subst leftTail bindingType) (RawTerm.subst rightTail bindingType)
      leftHead rightHead) :
    BinaryReducibleEnvAtBounded env bound (context.cons bindingType)
      (RawTermSubst.cons leftHead leftTail) (RawTermSubst.cons rightHead rightTail) := by
  intro index
  match index with
  | ⟨0, isLt⟩ =>
      rw [TypingContext.lookup_cons_zero context bindingType isLt,
        RawTerm.weaken_subst_cons bindingType leftHead leftTail,
        RawTerm.weaken_subst_cons bindingType rightHead rightTail]
      exact headRelated
  | ⟨position + 1, isLtSucc⟩ =>
      rw [TypingContext.lookup_cons_succ context bindingType position isLtSucc,
        RawTerm.weaken_subst_cons
          (context.lookup ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩) leftHead leftTail,
        RawTerm.weaken_subst_cons
          (context.lookup ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩) rightHead rightTail]
      exact tailRelated ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩

/-! ## ★ The λ-pair abstraction member arm -/

/-- ★ **The binary Π-introduction member arm — the binder crux, doubled.**  The λ-PAIR is a
related member pair of the Π pair: starting from the related body-instance pair, expand back
through β on the RIGHT (the codomain candidate's right closure), then on the LEFT — each at
the empty spine. -/
theorem binaryAbstractionMemberPairAtBounded {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {leftDomainAnn rightDomainAnn leftDomain rightDomain : RawTerm scope}
    {leftCodomain rightCodomain : RawTerm (scope + 1)}
    {leftDomainCandidate rightDomainCandidate : RawTerm scope → Prop}
    {domainRelation : BinaryCandidate scope}
    {codomainRelation : RawTerm scope → RawTerm scope → BinaryCandidate scope}
    {leftBody rightBody : RawTerm (scope + 1)}
    (leftDomainUnary : ReducibleTypeAtBounded env bound leftDomain leftDomainCandidate)
    (rightDomainUnary : ReducibleTypeAtBounded env bound rightDomain rightDomainCandidate)
    (domainsRelated : BinaryReducibleTypeAtBounded env bound leftDomain rightDomain
      domainRelation)
    (leftDomainAnnSN : IsStronglyNormalizing leftDomainAnn)
    (rightDomainAnnSN : IsStronglyNormalizing rightDomainAnn)
    (codomainsRelated : ∀ leftArgument rightArgument : RawTerm scope,
      leftDomainCandidate leftArgument → rightDomainCandidate rightArgument →
      domainRelation leftArgument rightArgument →
      BinaryReducibleTypeAtBounded env bound
        (RawTerm.subst0 leftCodomain leftArgument)
        (RawTerm.subst0 rightCodomain rightArgument)
        (codomainRelation leftArgument rightArgument))
    (domainArgumentsSN : ∀ leftArgument rightArgument : RawTerm scope,
      leftDomainCandidate leftArgument → rightDomainCandidate rightArgument →
      domainRelation leftArgument rightArgument →
      IsStronglyNormalizing leftArgument ∧ IsStronglyNormalizing rightArgument)
    (leftBodySN : IsStronglyNormalizing leftBody)
    (rightBodySN : IsStronglyNormalizing rightBody)
    (bodiesRelated : ∀ leftArgument rightArgument : RawTerm scope,
      leftDomainCandidate leftArgument → rightDomainCandidate rightArgument →
      domainRelation leftArgument rightArgument →
      codomainRelation leftArgument rightArgument
        (RawTerm.subst0 leftBody leftArgument) (RawTerm.subst0 rightBody rightArgument)) :
    IsBinaryReducibleMemberPairAtBounded env bound
      (.mkGen .gen_piTyCode () (.childCons leftDomain (.childCons leftCodomain .childNil)))
      (.mkGen .gen_piTyCode () (.childCons rightDomain (.childCons rightCodomain .childNil)))
      (.mkGen .gen_lam () (.childCons leftDomainAnn (.childCons leftBody .childNil)))
      (.mkGen .gen_lam () (.childCons rightDomainAnn (.childCons rightBody .childNil))) :=
  ⟨fun leftFunction rightFunction =>
      IsStronglyNormalizing leftFunction ∧ IsStronglyNormalizing rightFunction ∧
        ∀ leftArgument rightArgument : RawTerm scope,
          leftDomainCandidate leftArgument → rightDomainCandidate rightArgument →
          domainRelation leftArgument rightArgument →
          codomainRelation leftArgument rightArgument
            (.mkGen .gen_app () (.childCons leftFunction (.childCons leftArgument .childNil)))
            (.mkGen .gen_app () (.childCons rightFunction (.childCons rightArgument .childNil))),
   BinaryReducibleTypeStepBounded.piType codomainRelation leftDomainUnary rightDomainUnary
     domainsRelated codomainsRelated,
   lam_isStronglyNormalizing_of_body leftDomainAnnSN leftBodySN,
   lam_isStronglyNormalizing_of_body rightDomainAnnSN rightBodySN,
   fun leftArgument rightArgument leftGuard rightGuard argumentsRelated =>
     (codomainsRelated leftArgument rightArgument leftGuard rightGuard
         argumentsRelated).headExpansionClosedLeft
       (spine := [])
       leftDomainAnnSN
       (domainArgumentsSN leftArgument rightArgument leftGuard rightGuard argumentsRelated).1
       ((codomainsRelated leftArgument rightArgument leftGuard rightGuard
           argumentsRelated).headExpansionClosedRight
         (spine := [])
         rightDomainAnnSN
         (domainArgumentsSN leftArgument rightArgument leftGuard rightGuard
           argumentsRelated).2
         (bodiesRelated leftArgument rightArgument leftGuard rightGuard argumentsRelated))⟩

/-- The λ-pair member arm under a closing-substitution pair: `subst` distributes over Π/λ
definitionally on each side; the IH-shaped premises bridge via `subst_cons_eq_subst0_lift`. -/
theorem binaryAbstractionMemberPairUnderClosingSubstitutionBounded {scope targetScope : Nat}
    (env : Nat → Nat) (bound : Nat)
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    {leftSubstitution rightSubstitution : RawTermSubst scope targetScope}
    {leftDomainCandidate rightDomainCandidate : RawTerm targetScope → Prop}
    {domainRelation : BinaryCandidate targetScope}
    {codomainRelation : RawTerm targetScope → RawTerm targetScope →
      BinaryCandidate targetScope}
    (leftDomainUnary : ReducibleTypeAtBounded env bound
      (RawTerm.subst leftSubstitution domainCode) leftDomainCandidate)
    (rightDomainUnary : ReducibleTypeAtBounded env bound
      (RawTerm.subst rightSubstitution domainCode) rightDomainCandidate)
    (domainsRelated : BinaryReducibleTypeAtBounded env bound
      (RawTerm.subst leftSubstitution domainCode) (RawTerm.subst rightSubstitution domainCode)
      domainRelation)
    (leftDomainAnnSN : IsStronglyNormalizing (RawTerm.subst leftSubstitution domainCode))
    (rightDomainAnnSN : IsStronglyNormalizing (RawTerm.subst rightSubstitution domainCode))
    (codomainsRelated : ∀ leftArgument rightArgument : RawTerm targetScope,
      leftDomainCandidate leftArgument → rightDomainCandidate rightArgument →
      domainRelation leftArgument rightArgument →
      BinaryReducibleTypeAtBounded env bound
        (RawTerm.subst (RawTermSubst.cons leftArgument leftSubstitution) codomainCode)
        (RawTerm.subst (RawTermSubst.cons rightArgument rightSubstitution) codomainCode)
        (codomainRelation leftArgument rightArgument))
    (domainArgumentsSN : ∀ leftArgument rightArgument : RawTerm targetScope,
      leftDomainCandidate leftArgument → rightDomainCandidate rightArgument →
      domainRelation leftArgument rightArgument →
      IsStronglyNormalizing leftArgument ∧ IsStronglyNormalizing rightArgument)
    (leftBodySN : IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift leftSubstitution) body))
    (rightBodySN :
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift rightSubstitution) body))
    (bodiesRelated : ∀ leftArgument rightArgument : RawTerm targetScope,
      leftDomainCandidate leftArgument → rightDomainCandidate rightArgument →
      domainRelation leftArgument rightArgument →
      codomainRelation leftArgument rightArgument
        (RawTerm.subst (RawTermSubst.cons leftArgument leftSubstitution) body)
        (RawTerm.subst (RawTermSubst.cons rightArgument rightSubstitution) body)) :
    IsBinaryReducibleMemberPairAtBounded env bound
      (RawTerm.subst leftSubstitution
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
      (RawTerm.subst rightSubstitution
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
      (RawTerm.subst leftSubstitution
        (.mkGen .gen_lam () (.childCons domainCode (.childCons body .childNil))))
      (RawTerm.subst rightSubstitution
        (.mkGen .gen_lam () (.childCons domainCode (.childCons body .childNil)))) := by
  show IsBinaryReducibleMemberPairAtBounded env bound
    (.mkGen .gen_piTyCode ()
      (.childCons (RawTerm.subst leftSubstitution domainCode)
        (.childCons (RawTerm.subst (RawTermSubst.lift leftSubstitution) codomainCode)
          .childNil)))
    (.mkGen .gen_piTyCode ()
      (.childCons (RawTerm.subst rightSubstitution domainCode)
        (.childCons (RawTerm.subst (RawTermSubst.lift rightSubstitution) codomainCode)
          .childNil)))
    (.mkGen .gen_lam ()
      (.childCons (RawTerm.subst leftSubstitution domainCode)
        (.childCons (RawTerm.subst (RawTermSubst.lift leftSubstitution) body) .childNil)))
    (.mkGen .gen_lam ()
      (.childCons (RawTerm.subst rightSubstitution domainCode)
        (.childCons (RawTerm.subst (RawTermSubst.lift rightSubstitution) body) .childNil)))
  refine binaryAbstractionMemberPairAtBounded (codomainRelation := codomainRelation) env bound
    leftDomainUnary rightDomainUnary
    domainsRelated leftDomainAnnSN rightDomainAnnSN
    (fun leftArgument rightArgument leftGuard rightGuard argumentsRelated => ?_)
    domainArgumentsSN
    leftBodySN rightBodySN
    (fun leftArgument rightArgument leftGuard rightGuard argumentsRelated => ?_)
  · rw [← RawTerm.subst_cons_eq_subst0_lift codomainCode leftArgument leftSubstitution,
      ← RawTerm.subst_cons_eq_subst0_lift codomainCode rightArgument rightSubstitution]
    exact codomainsRelated leftArgument rightArgument leftGuard rightGuard argumentsRelated
  · rw [← RawTerm.subst_cons_eq_subst0_lift body leftArgument leftSubstitution,
      ← RawTerm.subst_cons_eq_subst0_lift body rightArgument rightSubstitution]
    exact bodiesRelated leftArgument rightArgument leftGuard rightGuard argumentsRelated

/-! ## ★ The binary piIntro FT arm -/

/-- ★ **The binary `piIntro` (λ) fundamental-theorem arm** — pins both candidates to the
canonical member-PAIR predicate and threads the binder environment via the binary env cons.
Premise-isolating exactly like the unary: the domain/codomain pair reducibilities and the SN
side conditions are caller premises (the FT assembly supplies them); the body conclusion is
the body IH under the cons-extended related environment pair. -/
theorem binaryFundamentalPiIntroArm {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (bound : Nat) (context : TypingContext profile scope)
    {domainCode : RawTerm scope} {codomainCode body : RawTerm (scope + 1)}
    (domainUnaryReduciblePair : ∀ {targetScope : Nat}
      (leftSubstitution rightSubstitution : RawTermSubst scope targetScope),
      BinaryReducibleEnvAtBounded env bound context leftSubstitution rightSubstitution →
      IsReducibleTypeAtBounded env bound (RawTerm.subst leftSubstitution domainCode) ∧
        IsReducibleTypeAtBounded env bound (RawTerm.subst rightSubstitution domainCode))
    (domainsRelatedAtBound : ∀ {targetScope : Nat}
      (leftSubstitution rightSubstitution : RawTermSubst scope targetScope),
      BinaryReducibleEnvAtBounded env bound context leftSubstitution rightSubstitution →
      IsBinaryReducibleTypePairAtBounded env bound
        (RawTerm.subst leftSubstitution domainCode)
        (RawTerm.subst rightSubstitution domainCode))
    (domainCodeStronglyNormalizing : ∀ {targetScope : Nat}
      (leftSubstitution rightSubstitution : RawTermSubst scope targetScope),
      BinaryReducibleEnvAtBounded env bound context leftSubstitution rightSubstitution →
      IsStronglyNormalizing (RawTerm.subst leftSubstitution domainCode)
        ∧ IsStronglyNormalizing (RawTerm.subst rightSubstitution domainCode))
    (domainArgumentsSN : ∀ {targetScope : Nat}
      (leftSubstitution rightSubstitution : RawTermSubst scope targetScope),
      BinaryReducibleEnvAtBounded env bound context leftSubstitution rightSubstitution →
      ∀ leftArgument rightArgument : RawTerm targetScope,
        IsBinaryReducibleMemberPairAtBounded env bound
          (RawTerm.subst leftSubstitution domainCode)
          (RawTerm.subst rightSubstitution domainCode) leftArgument rightArgument →
        IsStronglyNormalizing leftArgument ∧ IsStronglyNormalizing rightArgument)
    (codomainsRelatedAtBound : ∀ {targetScope : Nat}
      (leftSubstitution rightSubstitution : RawTermSubst scope targetScope),
      BinaryReducibleEnvAtBounded env bound context leftSubstitution rightSubstitution →
      ∀ leftArgument rightArgument : RawTerm targetScope,
        IsBinaryReducibleMemberPairAtBounded env bound
          (RawTerm.subst leftSubstitution domainCode)
          (RawTerm.subst rightSubstitution domainCode) leftArgument rightArgument →
        IsBinaryReducibleTypePairAtBounded env bound
          (RawTerm.subst (RawTermSubst.cons leftArgument leftSubstitution) codomainCode)
          (RawTerm.subst (RawTermSubst.cons rightArgument rightSubstitution) codomainCode))
    (bodyCodeStronglyNormalizing : ∀ {targetScope : Nat}
      (leftSubstitution rightSubstitution : RawTermSubst scope targetScope),
      BinaryReducibleEnvAtBounded env bound context leftSubstitution rightSubstitution →
      IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift leftSubstitution) body) ∧
        IsStronglyNormalizing (RawTerm.subst (RawTermSubst.lift rightSubstitution) body))
    (bodyConclusion : BinaryFundamentalConclusionAtBounded env bound
      (context.cons domainCode) body codomainCode) :
    BinaryFundamentalConclusionAtBounded env bound context (lamCell domainCode body)
      (piTyCodeCell domainCode codomainCode) := by
  intro _targetScope leftSubstitution rightSubstitution envRelated
  obtain ⟨⟨leftDomainCandidate, leftDomainUnary⟩, ⟨rightDomainCandidate, rightDomainUnary⟩⟩ :=
    domainUnaryReduciblePair leftSubstitution rightSubstitution envRelated
  exact binaryAbstractionMemberPairUnderClosingSubstitutionBounded
    (domainRelation := fun leftTerm rightTerm =>
      IsBinaryReducibleMemberPairAtBounded env bound
        (RawTerm.subst leftSubstitution domainCode)
        (RawTerm.subst rightSubstitution domainCode) leftTerm rightTerm)
    (codomainRelation := fun leftArgument rightArgument leftTerm rightTerm =>
      IsBinaryReducibleMemberPairAtBounded env bound
        (RawTerm.subst (RawTermSubst.cons leftArgument leftSubstitution) codomainCode)
        (RawTerm.subst (RawTermSubst.cons rightArgument rightSubstitution) codomainCode)
        leftTerm rightTerm)
    env bound
    leftDomainUnary rightDomainUnary
    (domainsRelatedAtBound leftSubstitution rightSubstitution
      envRelated).reducibleMemberPairCandidate
    (domainCodeStronglyNormalizing leftSubstitution rightSubstitution envRelated).1
    (domainCodeStronglyNormalizing leftSubstitution rightSubstitution envRelated).2
    (fun leftArgument rightArgument _leftGuard _rightGuard argumentsMember =>
      (codomainsRelatedAtBound leftSubstitution rightSubstitution envRelated
        leftArgument rightArgument argumentsMember).reducibleMemberPairCandidate)
    (fun leftArgument rightArgument _leftGuard _rightGuard argumentsMember =>
      domainArgumentsSN leftSubstitution rightSubstitution envRelated
        leftArgument rightArgument argumentsMember)
    (bodyCodeStronglyNormalizing leftSubstitution rightSubstitution envRelated).1
    (bodyCodeStronglyNormalizing leftSubstitution rightSubstitution envRelated).2
    (fun leftArgument rightArgument _leftGuard _rightGuard argumentsMember =>
      bodyConclusion (RawTermSubst.cons leftArgument leftSubstitution)
        (RawTermSubst.cons rightArgument rightSubstitution)
        (BinaryReducibleEnvAtBounded.cons envRelated argumentsMember))

end FX1Poly.Typed

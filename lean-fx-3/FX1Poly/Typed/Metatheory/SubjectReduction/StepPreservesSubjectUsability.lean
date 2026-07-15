import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionRootStepToTypedOrCongruence
import FX1Poly.Typed.Engine.Union.HasTypeUnionSubstitution

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/StepPreservesSubjectUsability
    — usability preservation under reduction (the residual the SR cascade defers as `reductUsable`)

The SR congruence/gate cascade (`elimGateRowReassemble`'s `usabilityAfter`, the per-row
`reductUsable` premises in `NatElimCongruenceSubjectReduction`, `MatchCongruenceSubjectReduction`,
`ProjectionCongruenceSubjectReduction`, `AppCongruenceSubjectReduction`, …) all defer ONE residual: a
single `Step` of a union-typed subject keeps the subject FIBRANTLY USABLE (the A1-CONJUNCT-WIRE FitchTT
use-site predicate `isSubjectUsableAtModality … .fibrant`).  This file discharges it unconditionally.

## Why the residual is real but cheap

`isSubjectUsableAtModality reduct .fibrant` is automatically `true` UNLESS the reduct is a bare variable
`var k` that the affine lock makes fibrantly inaccessible (a `lockCons`-bound dimension).  A reduction can
expose such a variable two ways — by SELECTING a branch (`boolElim … boolTrue ↝ thenBranch`) or by
SUBSTITUTING into a binder (`β`) — and in both the well-typedness of the redex certifies the exposed term
usable (the branch is a fibrant elim obligation; the substituent carries the FitchTT condition).  So the
theorem needs NO `WfContextUnion`: usability rides entirely on the obligation-usability conjunct the rule
arms already carry (`invertAtElimHeadGeneric`'s `usableHold`) plus the use-site substitution transport
(`subjectUsabilityPreservedUnderSubst`).

## Structure

`Step` has two arms.  The `cong` arm is trivial: `isSubjectUsableAtModality` inspects only the
generator/payload of the `mkGen` cell and IGNORES the children, so a child-step leaves usability
definitionally unchanged.  The `tableRedex` arm dispatches the 21-row reduction table; every iota/beta
firing's contractum falls into one of three shapes —

  1. **A spine branch verbatim** (`boolElim`→then/else, `natElim`/`natRec`→zero, `listElim`→nil,
     `optionMatch`→none, `idJ`→base, `fst`/`snd`→component): it IS a fibrant elim/intro obligation subject,
     usable directly off the redex's `usableHold`;
  2. **A non-variable `app` cell** (`optionMatch`-some, `eitherMatch`, `listElim`-cons): a `gen_app` head is
     usable at any modality (`isSubjectUsableAtModality_ofNonVarHead`);
  3. **A single/double `subst0`** (`β`, endpoint-`β`, `natElim`/`natRec`-succ): usable via
     `subjectUsabilityPreservedUnderSubst` fed the singleton/pair accessibility-preservation glue, the
     binder body's usability coming from the intro inversion.

The reserved heads (`idStrictRec`, quot/trunc) are untypable (`reservedHeadUntyped`).

## Zero-axiom verification

`cases` on `Step` + the shipped per-row firing inversions + the obligation-usability extractors + the
substitution use-site transport.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax

/-! ## The `cong`-arm invariance helper

`isSubjectUsableAtModality` matches the single `mkGen` cell and ignores its children, so replacing the
children spine leaves the predicate definitionally fixed. -/

/-- Usability is invariant under a children-spine change: it depends only on the cell's generator and
payload (the `mkGen` match binds the children variable but never uses it).  Closes the `cong` arm — a
child-step keeps the generator/payload, hence the usability. -/
theorem isSubjectUsableAtModality_invariantUnderChildrenChange {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator) (payload : generator.payload scope)
    (children1 children2 : RawTermChildren generator.binderShifts scope)
    (modality : ObligationModality) :
    context.isSubjectUsableAtModality (.mkGen generator payload children1) modality
      = context.isSubjectUsableAtModality (.mkGen generator payload children2) modality :=
  rfl

/-! ## Branch / component / body usability extractors

The fibrant elim/intro obligations the existing `…Usable` extractors do not already surface: the
two `boolElim` branches, the `optionMatch` none branch, the `idJ` base case, the `lam`/`pathLam` binder
body, and the `fst`/`snd` projected component (a TWO-level inversion: the eliminator's pair obligation,
then the pair introducer's component obligation).  Each reads `usableHold` at the obligation's index,
exactly as `optionMatchSomeBranchUsable` / `listElimBranchesUsable` do. -/

/-- The `boolElim` then/else branches are fibrantly usable (off the redex's `usabilityHolds`). -/
theorem HasTypeUnion.boolElimThenElseBranchesUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {scrutinee thenBranch elseBranch : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = boolElimCell motive scrutinee thenBranch elseBranch) :
    context.isSubjectUsableAtModality thenBranch .fibrant = true ∧
    context.isSubjectUsableAtModality elseBranch .fibrant = true := by
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, _obligationsHold, usableHold,
      _outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := boolElimRule)
      (show elimRuleOf Generator.gen_boolElim = some boolElimRule from rfl) (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, usableHold with
  | .childCons _argMotive (.childCons _argScrut (.childCons _argThen (.childCons _argElse .childNil))),
    .childNil, subjectIsMember, usableHold =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact ⟨usableHold _ (List.Mem.tail _ (List.Mem.head _)),
      usableHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))⟩

/-- The `optionMatch` none branch is fibrantly usable (off the redex's `usabilityHolds`). -/
theorem HasTypeUnion.optionMatchNoneBranchUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 1)} {noneBranch someBranch scrutinee : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = optionMatchCell motive noneBranch someBranch scrutinee) :
    context.isSubjectUsableAtModality noneBranch .fibrant = true := by
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, _obligationsHold, usableHold,
      _outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := optionMatchElimRule)
      (show elimRuleOf Generator.gen_optionMatch = some optionMatchElimRule from rfl)
      (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, usableHold with
  | .childCons _argMotive (.childCons _argNone (.childCons _argSome (.childCons _argScrut .childNil))),
    .childCons _typeParamA (.childCons _typeParamB .childNil),
    subjectIsMember, usableHold =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact usableHold _ (List.Mem.tail _ (List.Mem.head _))

/-- The `idJ` base case is fibrantly usable (off the redex's `usabilityHolds`). -/
theorem HasTypeUnion.idJBaseCaseUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {motive : RawTerm (scope + 2)} {baseCase witness : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = idJCell motive baseCase witness) :
    context.isSubjectUsableAtModality baseCase .fibrant = true := by
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, _obligationsHold, usableHold,
      _outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := idJElimRule) elimRuleOf_idJ (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, usableHold with
  | .childCons _argMotive (.childCons _argBase (.childCons _argWitness .childNil)),
    .childCons _typeCode (.childCons _leftEndpoint (.childCons _rightEndpoint .childNil)),
    subjectIsMember, usableHold =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact usableHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-- The `lam` binder body is fibrantly usable under the domain binder (off the lam introducer's
`usabilityHolds`).  The body obligation is the lam intro rule's index-2 obligation (context
`context.cons domain`, modality fibrant). -/
theorem HasTypeUnion.lamBodyFibrantlyUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {domain : RawTerm scope} {body : RawTerm (scope + 1)}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = lamCell domain body) :
    (context.cons domain).isSubjectUsableAtModality body .fibrant = true := by
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, usableHold⟩ :=
    derivation.invertAtIntroHeadGenericUsable (rule := lamIntroRule) introRuleOf_lam
      (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, usableHold with
  | .childCons _domainCode (.childCons _bodyChild .childNil), .childCons _codomainCode .childNil,
    subjectIsMember, usableHold =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact usableHold _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-- The `pathLam` binder body is fibrantly usable under the affine dimension lock (off the pathLam
introducer's `usabilityHolds`).  The body obligation is the pathLam intro rule's index-0 obligation
(context `context.lockCons intervalTypeCell`, modality fibrant). -/
theorem HasTypeUnion.pathLamBodyFibrantlyUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {body : RawTerm (scope + 1)}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = pathLamCell body) :
    (context.lockCons intervalTypeCell).isSubjectUsableAtModality body .fibrant = true := by
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, usableHold⟩ :=
    derivation.invertAtIntroHeadGenericUsable (rule := pathLamIntroRule) introRuleOf_pathLam
      (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, usableHold with
  | .childCons _bodyChild .childNil, .childCons _carrierCode .childNil, subjectIsMember, usableHold =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    exact usableHold _ (List.Mem.head _)

/-- The first component projected by `fst (pair firstValue secondValue)` is fibrantly usable: a TWO-level
inversion — the `fst` eliminator surfaces the pair scrutinee TYPED (index-0 obligation), and the pair
introducer surfaces its first component USABLE (index-0 `usabilityHolds`). -/
theorem HasTypeUnion.fstPairFirstComponentUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = fstCell (pairCell firstValue secondValue)) :
    context.isSubjectUsableAtModality firstValue .fibrant = true := by
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, obligationsHold, _usableHold,
      _outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := fstElimRule) elimRuleOf_fst (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold with
  | .childCons _pairChild .childNil, .childCons _firstType (.childCons _secondType .childNil),
    subjectIsMember, obligationsHold =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    obtain ⟨pairArgs, pairParams, _l0, _l1, _flag2, pairIsMember, pairUsableHold⟩ :=
      (obligationsHold _ (List.Mem.head _)).invertAtIntroHeadGenericUsable (rule := pairIntroRule)
        introRuleOf_pair rfl
    match pairArgs, pairParams, pairIsMember, pairUsableHold with
    | .childCons _child0 (.childCons _child1 .childNil),
      .childCons _typeParam0 (.childCons _typeParam1 .childNil), pairIsMember, pairUsableHold =>
      rcases pairIsMember with ⟨⟩
      exact pairUsableHold _ (List.Mem.head _)

/-- The second component projected by `snd (pair firstValue secondValue)` is fibrantly usable: the `snd`
twin of `fstPairFirstComponentUsable` (the pair introducer's index-1 `usabilityHolds`). -/
theorem HasTypeUnion.sndPairSecondComponentUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = sndCell (pairCell firstValue secondValue)) :
    context.isSubjectUsableAtModality secondValue .fibrant = true := by
  obtain ⟨args, params, _level0, _level1, _flag, subjectIsMember, obligationsHold, _usableHold,
      _outputConv⟩ :=
    derivation.invertAtElimHeadGeneric (rule := sndElimRule) elimRuleOf_snd (by rw [subjectShape]; rfl)
  match args, params, subjectIsMember, obligationsHold with
  | .childCons _pairChild .childNil, .childCons _firstType (.childCons _secondType .childNil),
    subjectIsMember, obligationsHold =>
    rw [subjectShape] at subjectIsMember
    rcases subjectIsMember with ⟨⟩
    obtain ⟨pairArgs, pairParams, _l0, _l1, _flag2, pairIsMember, pairUsableHold⟩ :=
      (obligationsHold _ (List.Mem.head _)).invertAtIntroHeadGenericUsable (rule := pairIntroRule)
        introRuleOf_pair rfl
    match pairArgs, pairParams, pairIsMember, pairUsableHold with
    | .childCons _child0 (.childCons _child1 .childNil),
      .childCons _typeParam0 (.childCons _typeParam1 .childNil), pairIsMember, pairUsableHold =>
      rcases pairIsMember with ⟨⟩
      exact pairUsableHold _ (List.Mem.tail _ (List.Mem.head _))

/-! ## The substitution-shaped contracta (β / endpoint-β / recursor-succ)

The reduct is a single (`β`, endpoint-`β`) or double (`natElim`/`natRec`-succ) `subst0`.  Usability rides
on `subjectUsabilityPreservedUnderSubst`, fed the singleton/pair accessibility-preservation glue keyed on
the substituent's own usability and the binder body's usability (surfaced from the intro/elim inversions). -/

/-- `β`'s reduct `subst0 body argument` is fibrantly usable: the argument is fibrantly usable (the `app`
argument obligation), the body fibrantly usable under the domain binder (the `lam` body obligation), and
`substSingletonAccessibilityPreserved` transports usability across the single substitution. -/
theorem betaReductFibrantlyUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {domain : RawTerm scope} {body : RawTerm (scope + 1)} {argument classifier : RawTerm scope}
    (typed : HasTypeUnion profile context (appCell (lamCell domain body) argument) classifier) :
    context.isSubjectUsableAtModality (RawTerm.subst0 body argument) .fibrant = true := by
  have argumentUsable := typed.appArgumentUsable rfl
  obtain ⟨_dom, _cod, lamTyped, _argumentTyped, _classifierConv⟩ := typed.invertAtAppHead rfl
  have bodyUsable := lamTyped.lamBodyFibrantlyUsable rfl
  exact subjectUsabilityPreservedUnderSubst (RawTermSubst.singleton argument) .fibrant
    (substSingletonAccessibilityPreserved context domain argument argumentUsable .fibrant)
    body bodyUsable

/-- endpoint-`β`'s reduct `subst0 body endpoint` is fibrantly usable: the endpoint is DIMENSIONALLY usable
(the `pathApp` interval argument obligation), the body fibrantly usable under the dimension lock (the
`pathLam` body obligation), and `substLockSingletonAccessibilityPreserved` transports usability across the
locked single substitution. -/
theorem pathBetaReductFibrantlyUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {body : RawTerm (scope + 1)} {endpoint classifier : RawTerm scope}
    (typed : HasTypeUnion profile context (pathAppCell (pathLamCell body) endpoint) classifier) :
    context.isSubjectUsableAtModality (RawTerm.subst0 body endpoint) .fibrant = true := by
  have endpointUsable := typed.pathAppArgumentUsable rfl
  obtain ⟨_appCarrier, _appLeft, _appRight, pathLamTyped, _endpointTyped, _classifierConv⟩ :=
    typed.invertAtPathAppHead rfl
  have bodyUsable := pathLamTyped.pathLamBodyFibrantlyUsable rfl
  exact subjectUsabilityPreservedUnderSubst (RawTermSubst.singleton endpoint) .fibrant
    (substLockSingletonAccessibilityPreserved context intervalTypeCell endpoint endpointUsable .fibrant)
    body bodyUsable

/-- `natElim`-succ's reduct `natElimSuccContractum` is fibrantly usable: the step branch is fibrantly
usable under the two recursor binders, the recursive `natElim` call is a non-variable head (usable), the
predecessor is fibrantly usable (the `natSucc` payload obligation), and `substPairAccessibilityPreserved`
transports usability across the double substitution. -/
theorem natElimSuccContractumFibrantlyUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    {predecessor classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (natElimCell motive zeroBranch succBranch (natSuccCell predecessor)) classifier) :
    context.isSubjectUsableAtModality
        (natElimSuccContractum motive zeroBranch succBranch predecessor) .fibrant = true := by
  obtain ⟨_zeroBranchUsable, succBranchUsable, _motiveUsable⟩ := typed.natElimBranchesMotiveUsable rfl
  obtain ⟨_resultLevel, _resultFlag, scrutineeTyped, _zT, _sT, _mF, _cC⟩ :=
    typed.invertAtNatElimHeadAllPremises rfl
  have predecessorUsable := scrutineeTyped.natSuccPredecessorUsable rfl
  have recursiveCallUsable : context.isSubjectUsableAtModality
      (natElimCell motive zeroBranch succBranch predecessor) .fibrant = true :=
    isSubjectUsableAtModality_ofNonVarHead context Generator.gen_natElim _ _ .fibrant (by decide)
  exact subjectUsabilityPreservedUnderSubst
    (RawTermSubst.cons (natElimCell motive zeroBranch succBranch predecessor)
      (RawTermSubst.singleton predecessor)) .fibrant
    (substPairAccessibilityPreserved context natTypeCell motive
      (natElimCell motive zeroBranch succBranch predecessor) predecessor
      recursiveCallUsable predecessorUsable .fibrant)
    succBranch succBranchUsable

/-- `natRec`-succ's reduct `natRecSuccContractum` is fibrantly usable: the dependent-recursor twin of
`natElimSuccContractumFibrantlyUsable`. -/
theorem natRecSuccContractumFibrantlyUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope} {succBranch : RawTerm (scope + 2)}
    {predecessor classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (natRecCell motive zeroBranch succBranch (natSuccCell predecessor)) classifier) :
    context.isSubjectUsableAtModality
        (natRecSuccContractum motive zeroBranch succBranch predecessor) .fibrant = true := by
  obtain ⟨_zeroBranchUsable, succBranchUsable, _motiveUsable⟩ := typed.natRecBranchesMotiveUsable rfl
  obtain ⟨_resultLevel, _resultFlag, scrutineeTyped, _zT, _sT, _mF, _cC⟩ :=
    typed.invertAtNatRecHeadAllPremises rfl
  have predecessorUsable := scrutineeTyped.natSuccPredecessorUsable rfl
  have recursiveCallUsable : context.isSubjectUsableAtModality
      (natRecCell motive zeroBranch succBranch predecessor) .fibrant = true :=
    isSubjectUsableAtModality_ofNonVarHead context Generator.gen_natRec _ _ .fibrant (by decide)
  exact subjectUsabilityPreservedUnderSubst
    (RawTermSubst.cons (natRecCell motive zeroBranch succBranch predecessor)
      (RawTermSubst.singleton predecessor)) .fibrant
    (substPairAccessibilityPreserved context natTypeCell motive
      (natRecCell motive zeroBranch succBranch predecessor) predecessor
      recursiveCallUsable predecessorUsable .fibrant)
    succBranch succBranchUsable

/-! ## The iota-head contractum dispatcher

A single induction over `IotaHeadStep` discharges every root-iota firing's reduct usability — the 14 live
families plus the reserved `idStrictRec` (untypable).  The 21-row `Step.tableRedex` enumeration then routes
each firing through the shipped per-row inversion converters to this one lemma. -/

/-- **The iota-head reduct is fibrantly usable.**  For a union-typed redex `IotaHeadStep`-reducing to
`reduct`, the reduct is fibrantly usable: branch selectors read the redex's fibrant obligation usability,
the `app`-chain contracta are non-variable-headed, the recursor-succ contracta ride the double-substitution
transport, and the reserved `idStrictRec` redex is untypable. -/
theorem HasTypeUnion.iotaHeadReductFibrantlyUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {redex reduct classifier : RawTerm scope}
    (typed : HasTypeUnion profile context redex classifier)
    (headStep : IotaHeadStep redex reduct) :
    context.isSubjectUsableAtModality reduct .fibrant = true := by
  cases headStep with
  | iotaBoolTrue => exact (typed.boolElimThenElseBranchesUsable rfl).1
  | iotaBoolFalse => exact (typed.boolElimThenElseBranchesUsable rfl).2
  | iotaFstPair => exact typed.fstPairFirstComponentUsable rfl
  | iotaSndPair => exact typed.sndPairSecondComponentUsable rfl
  | iotaNatElimZero => exact (typed.natElimBranchesMotiveUsable rfl).1
  | iotaNatRecZero => exact (typed.natRecBranchesMotiveUsable rfl).1
  | iotaListElimNil => exact (typed.listElimBranchesUsable rfl).1
  | iotaOptionMatchNone => exact typed.optionMatchNoneBranchUsable rfl
  | iotaIdJRefl => exact typed.idJBaseCaseUsable rfl
  | iotaOptionMatchSome =>
      exact isSubjectUsableAtModality_ofNonVarHead context Generator.gen_app _ _ .fibrant (by decide)
  | iotaEitherMatchInl =>
      exact isSubjectUsableAtModality_ofNonVarHead context Generator.gen_app _ _ .fibrant (by decide)
  | iotaEitherMatchInr =>
      exact isSubjectUsableAtModality_ofNonVarHead context Generator.gen_app _ _ .fibrant (by decide)
  | iotaListElimCons =>
      exact isSubjectUsableAtModality_ofNonVarHead context Generator.gen_app _ _ .fibrant (by decide)
  | iotaNatElimSucc => exact natElimSuccContractumFibrantlyUsable typed
  | iotaNatRecSucc => exact natRecSuccContractumFibrantlyUsable typed
  | iotaIdStrictRecRefl => exact (typed.reservedHeadUntyped rfl).elim

/-! ## The metatheorem -/

/-- **★ Usability is preserved under reduction.**  A single `Step` of a union-typed, fibrantly-usable
subject keeps the reduct fibrantly usable.  The residual the SR congruence/gate cascade defers as
`reductUsable` / `usabilityAfter`; discharging it lets every one of those obligations close.  No
`WfContextUnion` is needed — usability rides on the rule arms' obligation-usability conjunct plus the
use-site substitution transport, not on context well-formedness.

The `cong` arm is invariance under a children-spine change (`isSubjectUsableAtModality` ignores children);
the `tableRedex` arm routes the 21-row firing through the shipped per-row converters to
`iotaHeadReductFibrantlyUsable` (the 14 iota families + reserved `idStrictRec`), with `β` / endpoint-`β`
pinned by `betaRowFiringPinsRedex` / `pathBetaRowFiringPinsRedex` and the four remaining reserved heads
refuted by `reservedHeadUntyped`. -/
theorem HasTypeUnion.stepPreservesFibrantSubjectUsability {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reduct subjectType : RawTerm scope}
    (typed : HasTypeUnion profile context subject subjectType)
    (step : Step subject reduct)
    (usable : context.isSubjectUsableAtModality subject .fibrant = true) :
    context.isSubjectUsableAtModality reduct .fibrant = true := by
  cases step with
  | cong _generator _payload _childStep =>
      -- The reduct shares the subject's generator + payload (only children differ), and
      -- `isSubjectUsableAtModality` ignores children, so usability is definitionally unchanged.
      exact usable
  | tableRedex isRow elimPayload fires =>
    cases isRow with
    | head =>
        obtain ⟨_domain, _body, _argument, subjectEq, reductEq⟩ :=
          betaRowFiringPinsRedex elimPayload fires
        rw [reductEq]
        rw [subjectEq] at typed
        exact betaReductFibrantlyUsable typed
    | tail _ isRow => cases isRow with
      | head =>
          exact typed.iotaHeadReductFibrantlyUsable (boolTrueRowFiringToIotaHead elimPayload fires)
      | tail _ isRow => cases isRow with
        | head =>
            exact typed.iotaHeadReductFibrantlyUsable (boolFalseRowFiringToIotaHead elimPayload fires)
        | tail _ isRow => cases isRow with
          | head =>
              exact typed.iotaHeadReductFibrantlyUsable (fstPairRowFiringToIotaHead elimPayload fires)
          | tail _ isRow => cases isRow with
            | head =>
                exact typed.iotaHeadReductFibrantlyUsable (sndPairRowFiringToIotaHead elimPayload fires)
            | tail _ isRow => cases isRow with
              | head =>
                  exact typed.iotaHeadReductFibrantlyUsable
                    (natElimZeroRowFiringToIotaHead elimPayload fires)
              | tail _ isRow => cases isRow with
                | head =>
                    exact typed.iotaHeadReductFibrantlyUsable
                      (natRecZeroRowFiringToIotaHead elimPayload fires)
                | tail _ isRow => cases isRow with
                  | head =>
                      exact typed.iotaHeadReductFibrantlyUsable
                        (natElimSuccRowFiringToIotaHead elimPayload fires)
                  | tail _ isRow => cases isRow with
                    | head =>
                        exact typed.iotaHeadReductFibrantlyUsable
                          (natRecSuccRowFiringToIotaHead elimPayload fires)
                    | tail _ isRow => cases isRow with
                      | head =>
                          exact typed.iotaHeadReductFibrantlyUsable
                            (listElimNilRowFiringToIotaHead elimPayload fires)
                      | tail _ isRow => cases isRow with
                        | head =>
                            exact typed.iotaHeadReductFibrantlyUsable
                              (listElimConsRowFiringToIotaHead elimPayload fires)
                        | tail _ isRow => cases isRow with
                          | head =>
                              exact typed.iotaHeadReductFibrantlyUsable
                                (optionMatchNoneRowFiringToIotaHead elimPayload fires)
                          | tail _ isRow => cases isRow with
                            | head =>
                                exact typed.iotaHeadReductFibrantlyUsable
                                  (optionMatchSomeRowFiringToIotaHead elimPayload fires)
                            | tail _ isRow => cases isRow with
                              | head =>
                                  exact typed.iotaHeadReductFibrantlyUsable
                                    (eitherMatchInlRowFiringToIotaHead elimPayload fires)
                              | tail _ isRow => cases isRow with
                                | head =>
                                    exact typed.iotaHeadReductFibrantlyUsable
                                      (eitherMatchInrRowFiringToIotaHead elimPayload fires)
                                | tail _ isRow => cases isRow with
                                  | head =>
                                      exact typed.iotaHeadReductFibrantlyUsable
                                        (idJReflRowFiringToIotaHead elimPayload fires)
                                  | tail _ isRow => cases isRow with
                                    | head =>
                                        exact typed.iotaHeadReductFibrantlyUsable
                                          (idStrictRecReflRowFiringToIotaHead elimPayload fires)
                                    | tail _ isRow => cases isRow with
                                      | head =>
                                          obtain ⟨_body, _endpoint, subjectEq, reductEq⟩ :=
                                            pathBetaRowFiringPinsRedex elimPayload fires
                                          rw [reductEq]
                                          rw [subjectEq] at typed
                                          exact pathBetaReductFibrantlyUsable typed
                                      | tail _ isRow => cases isRow with
                                        | head => exact (typed.reservedHeadUntyped rfl).elim
                                        | tail _ isRow => cases isRow with
                                          | head => exact (typed.reservedHeadUntyped rfl).elim
                                          | tail _ isRow => cases isRow with
                                            | head => exact (typed.reservedHeadUntyped rfl).elim
                                            | tail _ isRow => cases isRow with
                                              | head => exact (typed.reservedHeadUntyped rfl).elim
                                              | tail _ isRow => cases isRow

end FX1Poly.Typed

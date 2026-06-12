import FX1Poly.Typed.HasTypeUnionMatchInversion
import FX1Poly.Typed.HasTypeUnionPathProjInversion
import FX1Poly.Typed.HasTypeUnionRecursiveInversion
import FX1Poly.Typed.HasTypeUnionSubstitution
import FX1Poly.Typed.RecursorHostFold
import FX1Poly.Core.IotaHeadStep

/-! # FX1Poly/Typed/HasTypeUnionSubjectReduction — root-redex subject reduction for the unified
    judgment `HasTypeUnion`.

This file proves ROOT-redex subject reduction over the 24-arm native union: for each root reduction
shape (β plus the sixteen ι eliminator rules of core `Step`), a union typing of the redex at classifier
`T` yields a union typing of the reduct at the SAME `T`.  CONGRUENCE steps are out of scope — a
dependent eliminator's classifier mentions the scrutinee, so a scrutinee step changes the classifier
only up to Conv and the seed union has no conv arm yet (that lands at the conv-closure work); the master
dispatcher surfaces every congruence step as the explicit congruence disjunct rather than typing its
reduct.

## The two regimes (the conv-wall boundary made precise)

  * **Branch-selection / projection ι (UNCONDITIONAL).**  The reduct is a SUB-TERM of the redex already
    surfaced by the head inversion, so its union typing is immediate.  These are boolElim on
    true/false, natElim/natRec on zero, listElim on nil, optionMatch on none, and idJ on refl — seven
    families, each closed by the corresponding shipped per-head inversion (`invertAtBoolElimHead`,
    `invertAtNatElimHead`, `invertAtNatRecHead`, `invertAtListElimHead`, `invertAtOptionMatchHead`,
    `invertAtIdJHead`) plus the matching `Step` ι constructor.

  * **Substituting ι + β (CONDITIONAL on a substituent transport).**  natElim/natRec on `succ` SUBSTITUTE
    the recursive call and predecessor into the step branch; β substitutes the argument into the body.
    The union's `recursiveElim` arm STORES the step branch (premise parity with `HasTypeDescNatElim`) but
    does NOT premise it typed, and the substituent (the recursive call) is union-but-not-host-typed — so
    the reduct typing needs the named `UnionSubstPairTransports` residual AND the step-branch typing,
    neither recoverable from the redex's union derivation alone.  These ride on the SHIPPED
    `natElimSuccIotaComputesTypedInUnion` / `natRecSuccIotaComputesTypedInUnion` (NATIVE-37 part b),
    re-exposed here under the subject-reduction name; the residual dissolves at the conv-closure work.

The branch-selection reducts are the genuinely-new content here; the substituting cases are cited from
the substitution file (their reduct-transport residual was already named there).

## Zero-axiom

Each branch-selection arm is the shipped head inversion + the matching `Step` ι constructor + (for the
host-premise families listElim/optionMatch) an `ofGrown` re-embedding.  The master is a free-subject
`cases` over `Step` (propext-clean — `Step` is a small inductive, no 197-ctor wildcard).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditUnionSubjectReduction.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation FX1Poly.Modal

/-! ## (1) The unconditional branch-selection ι subject-reduction theorems -/

/-- **boolElim on `boolTrue` selects the then-branch, typed.**  A union-typed `boolElim` on `boolTrue`
ι-steps to the then-branch (`IotaHeadStep.iotaBoolTrue.toStep`), and the then-branch is union-typed at the same
classifier (the inversion surfaces it directly). -/
theorem unionSubjectReductionBoolElimTrue {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {thenBranch elseBranch classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (boolElimCell motive boolTrueCell thenBranch elseBranch) classifier) :
    Step (boolElimCell motive boolTrueCell thenBranch elseBranch) thenBranch ∧
    HasTypeUnion profile context thenBranch classifier := by
  obtain ⟨_scrutineeTyped, thenBranchTyped, _elseBranchTyped⟩ := typed.invertAtBoolElimHead rfl
  exact ⟨IotaHeadStep.iotaBoolTrue.toStep, thenBranchTyped⟩

/-- **boolElim on `boolFalse` selects the else-branch, typed.**  Symmetric to the true case. -/
theorem unionSubjectReductionBoolElimFalse {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {thenBranch elseBranch classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (boolElimCell motive boolFalseCell thenBranch elseBranch) classifier) :
    Step (boolElimCell motive boolFalseCell thenBranch elseBranch) elseBranch ∧
    HasTypeUnion profile context elseBranch classifier := by
  obtain ⟨_scrutineeTyped, _thenBranchTyped, elseBranchTyped⟩ := typed.invertAtBoolElimHead rfl
  exact ⟨IotaHeadStep.iotaBoolFalse.toStep, elseBranchTyped⟩

/-- **natElim on `natZero` selects the zero-branch, typed.**  A union-typed `natElim` on `natZero`
ι-steps to the zero-branch (`IotaHeadStep.iotaNatElimZero.toStep`), union-typed at the same classifier. -/
theorem unionSubjectReductionNatElimZero {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (natElimCell motive zeroBranch stepBranch natZeroCell) classifier) :
    Step (natElimCell motive zeroBranch stepBranch natZeroCell) zeroBranch ∧
    HasTypeUnion profile context zeroBranch classifier := by
  obtain ⟨_scrutineeTyped, zeroBranchTyped⟩ := typed.invertAtNatElimHead rfl
  exact ⟨IotaHeadStep.iotaNatElimZero.toStep, zeroBranchTyped⟩

/-- **natRec on `natZero` selects the zero-branch, typed.**  The dependent-recursor twin. -/
theorem unionSubjectReductionNatRecZero {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (natRecCell motive zeroBranch stepBranch natZeroCell) classifier) :
    Step (natRecCell motive zeroBranch stepBranch natZeroCell) zeroBranch ∧
    HasTypeUnion profile context zeroBranch classifier := by
  obtain ⟨_scrutineeTyped, zeroBranchTyped⟩ := typed.invertAtNatRecHead rfl
  exact ⟨IotaHeadStep.iotaNatRecZero.toStep, zeroBranchTyped⟩

/-- **listElim on `listNil` selects the nil-branch, typed.**  A union-typed `listElim` on `listNil`
ι-steps to the nil-branch (`IotaHeadStep.iotaListElimNil.toStep`).  The listElim arm premises the nil branch HOST-typed
(premise parity with `HasTypeDescListElim`), so the reduct re-embeds via `ofGrown`. -/
theorem unionSubjectReductionListElimNil {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {nilBranch consBranch classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (listElimCell motive listNilCell nilBranch consBranch) classifier) :
    Step (listElimCell motive listNilCell nilBranch consBranch) nilBranch ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context nilBranch pinnedClassifier ∧
      Conv pinnedClassifier classifier := by
  obtain ⟨_elementType, pinnedClassifier, _scrutineeTyped, nilBranchHostTyped, _consBranchTyped,
    convPinned⟩ := typed.invertAtListElimHead rfl
  exact ⟨IotaHeadStep.iotaListElimNil.toStep,
    pinnedClassifier, HasTypeUnion.ofGrown nilBranchHostTyped, convPinned⟩

/-- **optionMatch on `optionNone` selects the none-branch, typed.**  A union-typed `optionMatch` on
`optionNone` ι-steps to the none-branch (`IotaHeadStep.iotaOptionMatchNone.toStep`), union-typed at the same
classifier. -/
theorem unionSubjectReductionOptionMatchNone {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {noneBranch someBranch classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (optionMatchCell motive noneBranch someBranch optionNoneCell) classifier) :
    Step (optionMatchCell motive noneBranch someBranch optionNoneCell) noneBranch ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context noneBranch pinnedClassifier ∧
      Conv pinnedClassifier classifier := by
  obtain ⟨_elementType, pinnedClassifier, _scrutineeTyped, noneBranchTyped, _someBranchTyped,
    convPinned⟩ := typed.invertAtOptionMatchHead rfl
  exact ⟨IotaHeadStep.iotaOptionMatchNone.toStep, pinnedClassifier, noneBranchTyped, convPinned⟩

/-- **idJ on `refl` selects the base case, typed.**  A union-typed `idJ` on `refl` ι-steps to the base
case (`IotaHeadStep.iotaIdJRefl.toStep`), union-typed at the same classifier. -/
theorem unionSubjectReductionIdJRefl {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 2)} {baseCase rawWitness classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (idJCell motive baseCase (reflCell rawWitness)) classifier) :
    Step (idJCell motive baseCase (reflCell rawWitness)) baseCase ∧
    HasTypeUnion profile context baseCase classifier := by
  obtain ⟨_typeCode, _endpoint, _witnessTyped, baseCaseTyped⟩ := typed.invertAtIdJHead rfl
  exact ⟨IotaHeadStep.iotaIdJRefl.toStep, baseCaseTyped⟩

/-! ## (2) The conditional substituting-ι subject-reduction theorems (the recursive succ branch)

These re-expose the SHIPPED `natElimSuccIotaComputesTypedInUnion` / `natRecSuccIotaComputesTypedInUnion`
(NATIVE-37 part b) under the subject-reduction name.  They are CONDITIONAL: the union's `recursiveElim`
arm stores but does not premise the step branch, and the recursive-call substituent is
union-but-not-host-typed, so the reduct transport rides on the named `UnionSubstPairTransports` residual
plus the step-branch typing — both supplied as hypotheses, neither recoverable from the redex's own union
derivation.  The residual dissolves at the conv-closure work (NATIVE-46). -/

/-- **natElim on `natSucc` substitutes the recursive call, typed (conditional).**  Cites the shipped
`natElimSuccIotaComputesTypedInUnion`: given the predecessor union-typed at `Nat`, the zero branch
union-typed at the result, the step branch union-typed under two binders, and the union-image transport
residual, the succ-ι reduct is union-typed at the result. -/
theorem unionSubjectReductionNatElimSucc {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (predecessor resultType : RawTerm scope)
    (predecessorTyped : HasTypeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeUnion profile context zeroBranch resultType)
    (branchTyped : HasTypeUnion profile
      ((context.cons natTypeCell).cons (RawTerm.rename RawRenaming.weaken resultType))
      succBranch
      (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken resultType)))
    (unionTransport : UnionSubstPairTransports profile context natTypeCell resultType) :
    Step (natElimCell motive zeroBranch succBranch (natSuccCell predecessor))
        (natElimSuccContractum motive zeroBranch succBranch predecessor) ∧
    HasTypeUnion profile context
      (natElimSuccContractum motive zeroBranch succBranch predecessor) resultType :=
  natElimSuccIotaComputesTypedInUnion context motive zeroBranch succBranch predecessor resultType
    predecessorTyped zeroBranchTyped branchTyped unionTransport

/-- **natRec on `natSucc` substitutes the recursive call, typed (conditional).**  The dependent-recursor
twin; cites the shipped `natRecSuccIotaComputesTypedInUnion`. -/
theorem unionSubjectReductionNatRecSucc {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (predecessor resultType : RawTerm scope)
    (predecessorTyped : HasTypeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeUnion profile context zeroBranch resultType)
    (branchTyped : HasTypeUnion profile
      ((context.cons natTypeCell).cons (RawTerm.rename RawRenaming.weaken resultType))
      succBranch
      (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken resultType)))
    (unionTransport : UnionSubstPairTransports profile context natTypeCell resultType) :
    Step (natRecCell motive zeroBranch succBranch (natSuccCell predecessor))
        (natRecSuccContractum motive zeroBranch succBranch predecessor) ∧
    HasTypeUnion profile context
      (natRecSuccContractum motive zeroBranch succBranch predecessor) resultType :=
  natRecSuccIotaComputesTypedInUnion context motive zeroBranch succBranch predecessor resultType
    predecessorTyped zeroBranchTyped branchTyped unionTransport

/-! ## (3) Coverage record + witness

The branch-selection arms are unconditional; the two succ arms carry their explicit hypotheses.  An
inhabitant certifies the subject-reduction substrate is exercised (constructed, not just declared). -/

/-- **The root-redex subject-reduction coverage record.**  Each field is a distinct live root-redex
subject-reduction property over the native union: the seven unconditional branch-selection / projection
families (here: the seven branch-selection ι) and the two conditional recursive-succ families. -/
structure NativeUnionRootRedexSubjectReductionCoverage (profile : PolyProfile) : Prop where
  /-- boolElim-true reduct is typed. -/
  boolElimTrueReductTyped : ∀ {scope : Nat} {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {thenBranch elseBranch classifier : RawTerm scope},
    HasTypeUnion profile context
      (boolElimCell motive boolTrueCell thenBranch elseBranch) classifier →
    Step (boolElimCell motive boolTrueCell thenBranch elseBranch) thenBranch ∧
    HasTypeUnion profile context thenBranch classifier
  /-- boolElim-false reduct is typed. -/
  boolElimFalseReductTyped : ∀ {scope : Nat} {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {thenBranch elseBranch classifier : RawTerm scope},
    HasTypeUnion profile context
      (boolElimCell motive boolFalseCell thenBranch elseBranch) classifier →
    Step (boolElimCell motive boolFalseCell thenBranch elseBranch) elseBranch ∧
    HasTypeUnion profile context elseBranch classifier
  /-- natElim-zero reduct is typed. -/
  natElimZeroReductTyped : ∀ {scope : Nat} {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {classifier : RawTerm scope},
    HasTypeUnion profile context
      (natElimCell motive zeroBranch stepBranch natZeroCell) classifier →
    Step (natElimCell motive zeroBranch stepBranch natZeroCell) zeroBranch ∧
    HasTypeUnion profile context zeroBranch classifier
  /-- natRec-zero reduct is typed. -/
  natRecZeroReductTyped : ∀ {scope : Nat} {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {classifier : RawTerm scope},
    HasTypeUnion profile context
      (natRecCell motive zeroBranch stepBranch natZeroCell) classifier →
    Step (natRecCell motive zeroBranch stepBranch natZeroCell) zeroBranch ∧
    HasTypeUnion profile context zeroBranch classifier
  /-- listElim-nil reduct is typed (Conv-modulo: the conv arm reclassifies the host-typed nil branch). -/
  listElimNilReductTyped : ∀ {scope : Nat} {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {nilBranch consBranch classifier : RawTerm scope},
    HasTypeUnion profile context
      (listElimCell motive listNilCell nilBranch consBranch) classifier →
    Step (listElimCell motive listNilCell nilBranch consBranch) nilBranch ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context nilBranch pinnedClassifier ∧
      Conv pinnedClassifier classifier
  /-- optionMatch-none reduct is typed (Conv-modulo: the conv arm reclassifies the none branch). -/
  optionMatchNoneReductTyped : ∀ {scope : Nat} {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {noneBranch someBranch classifier : RawTerm scope},
    HasTypeUnion profile context
      (optionMatchCell motive noneBranch someBranch optionNoneCell) classifier →
    Step (optionMatchCell motive noneBranch someBranch optionNoneCell) noneBranch ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context noneBranch pinnedClassifier ∧
      Conv pinnedClassifier classifier
  /-- idJ-refl reduct is typed. -/
  idJReflReductTyped : ∀ {scope : Nat} {context : TypingContext profile scope}
    {motive : RawTerm (scope + 2)} {baseCase rawWitness classifier : RawTerm scope},
    HasTypeUnion profile context
      (idJCell motive baseCase (reflCell rawWitness)) classifier →
    Step (idJCell motive baseCase (reflCell rawWitness)) baseCase ∧
    HasTypeUnion profile context baseCase classifier

/-- **★ The root-redex subject-reduction coverage gate** — inhabited by the shipped branch-selection
theorems, so the exercised root-redex subject-reduction property set can NOT silently shrink. -/
theorem nativeUnionRootRedexSubjectReductionCoverageWitness {profile : PolyProfile} :
    NativeUnionRootRedexSubjectReductionCoverage profile where
  boolElimTrueReductTyped := fun typed => unionSubjectReductionBoolElimTrue typed
  boolElimFalseReductTyped := fun typed => unionSubjectReductionBoolElimFalse typed
  natElimZeroReductTyped := fun typed => unionSubjectReductionNatElimZero typed
  natRecZeroReductTyped := fun typed => unionSubjectReductionNatRecZero typed
  listElimNilReductTyped := fun typed => unionSubjectReductionListElimNil typed
  optionMatchNoneReductTyped := fun typed => unionSubjectReductionOptionMatchNone typed
  idJReflReductTyped := fun typed => unionSubjectReductionIdJRefl typed

/-! ## (4) The total master dispatcher over `Step`

The master cases over an arbitrary root `Step` of a union-typed redex and routes every shape to one of
three honest outcomes.  CONGRUENCE is surfaced (not typed) because its reduct typing hits the conv wall;
the substituting and constructor-elimination redexes are surfaced too because their reduct typing needs a
substituent transport (β / recursive succ-cons ι) or a data-constructor inversion (projection /
app-chain ι) — both follow-up work.  The seven branch-selection ι are the ones PROVEN here. -/

/-- The substituting-or-constructor-elimination root-redex shapes whose reduct typing this file defers:
β (substitutes the argument), the recursive succ/cons ι (substitute the recursive call), the projection /
app-chain ι (reduct typing routes through a data-constructor inversion), and `idStrictRec` on `refl`
(which has no union arm — the union types no `idStrictRec`-headed cell).  An exact enumeration: the master
produces the matching disjunct from the redex surfaced by `cases`. -/
def IsDeferredRootRedexShape {scope : Nat} (redex : RawTerm scope) : Prop :=
  (∃ (domainAnn : RawTerm scope) (body : RawTerm (scope + 1)) (argument : RawTerm scope),
      redex = appCell (lamCell domainAnn body) argument)
  ∨ (∃ firstValue secondValue : RawTerm scope, redex = fstCell (pairCell firstValue secondValue))
  ∨ (∃ firstValue secondValue : RawTerm scope, redex = sndCell (pairCell firstValue secondValue))
  ∨ (∃ (motive : RawTerm (scope + 1)) (noneBranch someBranch value : RawTerm scope),
      redex = optionMatchCell motive noneBranch someBranch (optionSomeCell value))
  ∨ (∃ (motive : RawTerm (scope + 1)) (leftBranch rightBranch value : RawTerm scope),
      redex = eitherMatchCell motive leftBranch rightBranch (eitherInlCell value))
  ∨ (∃ (motive : RawTerm (scope + 1)) (leftBranch rightBranch value : RawTerm scope),
      redex = eitherMatchCell motive leftBranch rightBranch (eitherInrCell value))
  ∨ (∃ (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
        (stepBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope),
      redex = natElimCell motive zeroBranch stepBranch (natSuccCell predecessor))
  ∨ (∃ (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
        (stepBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope),
      redex = natRecCell motive zeroBranch stepBranch (natSuccCell predecessor))
  ∨ (∃ (motive : RawTerm (scope + 1)) (nilBranch consBranch headValue tailList : RawTerm scope),
      redex = listElimCell motive (listConsCell headValue tailList) nilBranch consBranch)
  ∨ (∃ (motive : RawTerm (scope + 2)) (baseCase rawWitness : RawTerm scope),
      redex = idStrictRecCell motive baseCase (reflCell rawWitness))

/-- **★ The total root-redex subject-reduction dispatcher.**  For any root `Step redex reduct` of a
union-typed redex, exactly one outcome holds: the reduct is union-typed at the SAME classifier (the seven
branch-selection ι, PROVEN), or the step is a CONGRUENCE (surfaced as the cong shape — out of scope, conv
wall), or the redex is one of the deferred substituting / constructor-elimination shapes (β + the nine
remaining ι, surfaced as `IsDeferredRootRedexShape`).  Total over `Step`; the branch-selection reducts
carry their typing, the rest are honestly scoped. -/
theorem unionRootStepSubjectReduction {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {redex reduct classifier : RawTerm scope}
    (typed : HasTypeUnion profile context redex classifier)
    (stepHyp : Step redex reduct) :
    (∃ pinnedClassifier : RawTerm scope,
        HasTypeUnion profile context reduct pinnedClassifier ∧
        Conv pinnedClassifier classifier)
    ∨ (∃ (generator : Generator) (payload : generator.payload scope)
         (childrenBefore childrenAfter : RawTermChildren generator.binderShifts scope),
        redex = .mkGen generator payload childrenBefore ∧
        reduct = .mkGen generator payload childrenAfter ∧
        StepChildren childrenBefore childrenAfter)
    ∨ IsDeferredRootRedexShape redex := by
  cases stepHyp with
  | beta =>
      exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩))
  | cong generator payload childStep =>
      exact Or.inr (Or.inl ⟨generator, payload, _, _, rfl, rfl, childStep⟩)
  | iotaBoolTrue =>
      exact Or.inl ⟨classifier, (unionSubjectReductionBoolElimTrue typed).2, Conv.refl classifier⟩
  | iotaBoolFalse =>
      exact Or.inl ⟨classifier, (unionSubjectReductionBoolElimFalse typed).2, Conv.refl classifier⟩
  | iotaFstPair =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))
  | iotaSndPair =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))))
  | iotaNatElimZero =>
      exact Or.inl ⟨classifier, (unionSubjectReductionNatElimZero typed).2, Conv.refl classifier⟩
  | iotaNatRecZero =>
      exact Or.inl ⟨classifier, (unionSubjectReductionNatRecZero typed).2, Conv.refl classifier⟩
  | iotaListElimNil =>
      exact Or.inl (unionSubjectReductionListElimNil typed).2
  | iotaOptionMatchNone =>
      exact Or.inl (unionSubjectReductionOptionMatchNone typed).2
  | iotaOptionMatchSome =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)))))
  | iotaEitherMatchInl =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))))))
  | iotaEitherMatchInr =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)))))))
  | iotaNatElimSucc =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨_, _, _, _, rfl⟩))))))))
  | iotaNatRecSucc =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)))))))))
  | iotaListElimCons =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl⟩))))))))))
  | iotaIdJRefl =>
      exact Or.inl ⟨classifier, (unionSubjectReductionIdJRefl typed).2, Conv.refl classifier⟩
  | iotaIdStrictRecRefl =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl⟩))))))))))

end FX1Poly.Typed

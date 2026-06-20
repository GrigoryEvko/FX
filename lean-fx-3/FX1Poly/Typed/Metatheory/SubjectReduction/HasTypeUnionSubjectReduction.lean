import FX1Poly.Typed.Engine.Union.HasTypeUnionMatchInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionPathProjInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionRecursiveInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionSubstitution
import FX1Poly.Typed.Corpus.Faithfulness.RecursorHostFold
import FX1Poly.Typed.Engine.Classifier.UnionStaticTypingSoundness
import FX1Poly.Typed.Engine.Formation.ConvFlatCodeInjectivity
import FX1Poly.Typed.Ledger.Bridge.BridgeEndpointStep
import FX1Poly.Core.Rewriting.Reduction.Head.IotaHeadStep
import FX1Poly.Core.Rewriting.RuleTables.StepOver.StepTable
import FX1Poly.Core.Equality.Eta.EtaRowFiringSubstrate

/-! # FX1Poly/Typed/HasTypeUnionSubjectReduction — root-redex subject reduction for the unified
    judgment `HasTypeUnion`.

This file proves ROOT-redex subject reduction over the 5-arm native union: for each root reduction
shape (β plus the sixteen ι eliminator rules of core `Step`), a union typing of the redex at classifier
`T` yields a union typing of the reduct at the SAME `T`.  CONGRUENCE steps are out of scope here — a
dependent eliminator's classifier mentions the scrutinee, so a scrutinee step changes the classifier
only up to Conv; absorbing that drift through the union's `conv` arm is the conv-closure work, so the
master dispatcher surfaces every congruence step as the explicit congruence disjunct rather than typing
its reduct.

## The three regimes (the conv-wall boundary made precise)

  * **Branch-selection ι (UNCONDITIONAL).**  The reduct is a SUB-TERM of the redex already surfaced by the
    head inversion, so its union typing is immediate.  These are boolElim on true/false, natElim/natRec on
    zero, listElim on nil, optionMatch on none, and idJ on refl — seven families, each closed by the
    corresponding shipped per-head inversion (`invertAtBoolElimHead`, `invertAtNatElimHead`,
    `invertAtNatRecHead`, `invertAtListElimHead`, `invertAtOptionMatchHead`, `invertAtIdJHead`) plus the
    matching `Step` ι constructor.

  * **Projection ι (UNCONDITIONAL, Conv-modulo — TYTAB-2).**  `fst(pair(a, b))` / `snd(pair(a, b))` ι-step
    to the component, typed at the component type read off the pair's product code (`invertAtFstHead` /
    `invertAtSndHead` surface the pair as a whole; the new `invertAtPairHead` surfaces the component; the
    product code's `Conv`-injectivity pins the component type to the classifier up to Conv).  No extra
    hypotheses.

  * **Substituting ι + β + app-chain ι (CONDITIONAL — the succ arms + the six TYTAB-2 deferred rows).**
    natElim/natRec on `succ` and β / endpoint-β SUBSTITUTE into a binder (`UnionSubstPairTransports` /
    `UnionSubst0Transports` residual, the union-image binder descent the no-conv-arm seed defers); the
    option-some / either-inl/inr / list-cons ι APPLY the selected handler to the constructor payload
    (built from `unionAppCellTyped`, NO binder descent, the non-dependent codomain collapsing by
    `subst0_weaken`).  Each is CONDITIONAL exactly as the succ arms are: the handler/body and payload
    typings — and, for the genuine substitutions, the transport residual — are supplied as hypotheses,
    not recoverable from the redex's own union derivation (the union's `elim` arm stores but does not
    premise the branch; the data-constructor payload's introducer-head inversion is not yet union-shipped;
    binder descent with a union-typed substituent is the no-conv-arm gap).  The list-cons step both
    selects AND recurses, threading the recursive `listElim` call (built through the union's own `elim`
    arm) into the curried app-chain.

The branch-selection + projection reducts are unconditional; the substituting / app-chain cases carry
their explicit hypotheses.  The two succ arms ride the SHIPPED
`natElimSuccIotaComputesTypedInUnion` / `natRecSuccIotaComputesTypedInUnion` (NATIVE-37 part b).

## Zero-axiom

Each unconditional arm is the shipped head inversion + the matching `Step` ι constructor (+ for the
projections the new `invertAtPairHead` + `productCode_inj`); each conditional arm is `unionAppCellTyped`
or the transport residual + the matching `Step` / `IotaHeadStep` constructor.  The master is a free-subject
`cases` over `Step` (propext-clean — `Step` is a small inductive, no 205-ctor wildcard).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditUnionSubjectReduction.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax FX1Poly.Modal

/-! ## (0) Local building blocks the projection / app-chain rows consume

Two helpers the eight new rows need that the inversion files did not yet ship:

  * `HasTypeUnion.invertAtPairHead` — the introducer-head inversion at the `gen_pair` row (the
    `invertAtNatSuccHead` twin: pin the `gen_pair` intro row, surface BOTH component premises, read the
    output `product` code off the row params).  The projection rows `fst`/`snd` consume it after the
    shipped `invertAtFstHead`/`invertAtSndHead` surface the pair-as-a-whole.
  * `unionAppCellTyped` — the app-row builder: `f : Pi(domain, codomain)` and `a : domain` give
    `app(f, a) : subst0 codomain a` through the unified `elim` arm at the `gen_app` row.  The app-chain
    iota reducts (option-some / either-inl/inr / list-cons select-then-apply) are built from it. -/

/-- **★ Inversion at the pair head.**  A union typing of a `pairCell`-headed subject IS a non-dependent
data-pair introduction at the `gen_pair` row: for some component types `A`, `B`, the first component is
union-typed at `A`, the second at `B`, and the classifier is convertible to `product(A, B)`.  No grown
disjunct: `pairCell` is untypable in the grown engine (`pairCellHasNoTyping`).  The `invertAtNatSuccHead`
twin for the binary product constructor. -/
theorem HasTypeUnion.invertAtPairHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = pairCell firstValue secondValue) :
    ∃ firstType secondType : RawTerm scope,
      HasTypeUnion profile context firstValue firstType ∧
      HasTypeUnion profile context secondValue secondType ∧
      Conv (productTypeCell firstType secondType) classifier := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨firstType, secondType, firstTyped, secondTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨firstType, secondType, firstTyped, secondTyped, convInner.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.pairCellHasNoTyping (fun contra => contra)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      -- The unified introducer arm: only the `gen_pair` row produces a `pair`-headed cell; the other
      -- sixteen introducer heads clash with the `pair` subject head.
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- boolTrue
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- boolFalse
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- unit
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- interval0
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- interval1
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natZero
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- lam
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- pathLam
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- natSucc
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listCons
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- optionSome
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- optionNone
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- listNil
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- eitherInl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- eitherInr
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- ★ pair — the SURVIVOR.  Destructure args (`[0, 0]`) + params (`[0, 0]`), recover the components
      -- from `subjectShape`, surface both component premises; the output type IS `product(A, B)`, so the
      -- Conv is `refl`.
      · match args, params with
        | .childCons _armFirst (.childCons _armSecond .childNil),
          .childCons _firstType (.childCons _secondType .childNil) =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, _, premisesHold _ (List.Mem.head _),
            premisesHold _ (List.Mem.tail _ (List.Mem.head _)), Conv.refl _⟩
      -- refl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params isElim premisesHold =>
      -- The unified eliminator arm: no eliminator row produces a `pair`-headed cell (pair is a data
      -- constructor), so the row's generator clashes with `gen_pair` (`elimRuleOf gen_pair = none`).
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_pair :=
        (elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      rw [headEq] at isElim
      exact absurd isElim (by intro tableHit; cases tableHit)

/-- **The app-row union builder.**  A function union-typed at the Π code `Pi(domain, codomain)` applied to
an argument union-typed at `domain` gives the application cell union-typed at the dependent output
`subst0 codomain argument` — the unified `elim` arm at the `gen_app` row, with the two `appElimRule`
obligations discharged by the two premises.  The select-then-apply ι reducts (option-some / either-inl/inr
/ the list-cons step) build their `app(branch, value)` contracta through it. -/
theorem unionAppCellTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (functionTerm argument domain : RawTerm scope) (codomain : RawTerm (scope + 1))
    (functionTyped : HasTypeUnion profile context functionTerm (piTyCodeCell domain codomain))
    (argumentTyped : HasTypeUnion profile context argument domain) :
    HasTypeUnion profile context (appCell functionTerm argument)
      (RawTerm.subst0 codomain argument) := by
  refine HasTypeUnion.elim context .gen_app appElimRule
    (.childCons functionTerm (.childCons argument .childNil))
    (.childCons domain (.childCons codomain .childNil)) rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact functionTyped
  | tail _ hmem => cases hmem with
    | head => exact argumentTyped
    | tail _ hmem => cases hmem

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
ι-steps to the nil-branch (`IotaHeadStep.iotaListElimNil.toStep`).  After the TYTAB-1 elim collapse the
listElim row's obligations homogenize the former grown nil/cons branches to UNION obligations, so the
inversion already yields a union-typed nil branch — the reduct's typing is that premise DIRECTLY, no
`ofGrown` re-embedding (exactly as the always-union `optionMatch`/`eitherMatch` siblings below). -/
theorem unionSubjectReductionListElimNil {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {nilBranch consBranch classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (listElimCell motive listNilCell nilBranch consBranch) classifier) :
    Step (listElimCell motive listNilCell nilBranch consBranch) nilBranch ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context nilBranch pinnedClassifier ∧
      Conv pinnedClassifier classifier := by
  obtain ⟨_elementType, pinnedClassifier, _scrutineeTyped, nilBranchTyped, _consBranchTyped,
    convPinned⟩ := typed.invertAtListElimHead rfl
  exact ⟨IotaHeadStep.iotaListElimNil.toStep,
    pinnedClassifier, nilBranchTyped, convPinned⟩

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

/-- **fst on `pair` projects the first component, typed (Conv-modulo).**  A union-typed `fst(pair(a, b))`
ι-steps to `a` (`IotaHeadStep.iotaFstPair.toStep`).  The projection-head inversion (`invertAtFstHead`) surfaces the
pair union-typed at `product(C, B)` with `Conv C classifier`; the pair-head inversion
(`invertAtPairHead`) then surfaces `a` union-typed at `A` with `Conv (product(A, B')) (product(C, B))`,
whose first leg (`productCode_inj`) pins `Conv A C`.  So `a` is union-typed at `A` with `Conv A classifier`
— the projected component carries its OWN classifier, Conv-equal to the ambient one (the conv wall: the
projected type is read off the pair's product code, convertible to but not syntactically the classifier). -/
theorem unionSubjectReductionFstPair {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {firstValue secondValue classifier : RawTerm scope}
    (typed : HasTypeUnion profile context (fstCell (pairCell firstValue secondValue)) classifier) :
    Step (fstCell (pairCell firstValue secondValue)) firstValue ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context firstValue pinnedClassifier ∧
      Conv pinnedClassifier classifier := by
  obtain ⟨_secondType, pinnedProductFirst, pairTyped, convOuter⟩ := typed.invertAtFstHead rfl
  obtain ⟨firstType, _secondType', firstTyped, _secondTyped, convProduct⟩ :=
    pairTyped.invertAtPairHead rfl
  obtain ⟨convFirst, _convSecond⟩ := Conv.productCode_inj convProduct
  exact ⟨IotaHeadStep.iotaFstPair.toStep,
    firstType, firstTyped, convFirst.trans convOuter⟩

/-- **snd on `pair` projects the second component, typed (Conv-modulo).**  Symmetric to the fst case:
a union-typed `snd(pair(a, b))` ι-steps to `b` (`IotaHeadStep.iotaSndPair.toStep`), union-typed at the second
component type, Conv-equal to the classifier (via the SECOND leg of `productCode_inj`). -/
theorem unionSubjectReductionSndPair {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {firstValue secondValue classifier : RawTerm scope}
    (typed : HasTypeUnion profile context (sndCell (pairCell firstValue secondValue)) classifier) :
    Step (sndCell (pairCell firstValue secondValue)) secondValue ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context secondValue pinnedClassifier ∧
      Conv pinnedClassifier classifier := by
  obtain ⟨_firstType, pinnedProductSecond, pairTyped, convOuter⟩ := typed.invertAtSndHead rfl
  obtain ⟨_firstType', secondType, _firstTyped, secondTyped, convProduct⟩ :=
    pairTyped.invertAtPairHead rfl
  obtain ⟨_convFirst, convSecond⟩ := Conv.productCode_inj convProduct
  exact ⟨IotaHeadStep.iotaSndPair.toStep,
    secondType, secondTyped, convSecond.trans convOuter⟩

/-! ## (2) The conditional substituting-ι subject-reduction theorems (the recursive succ branch)

These re-expose the SHIPPED `natElimSuccIotaComputesTypedInUnion` / `natRecSuccIotaComputesTypedInUnion`
(NATIVE-37 part b) under the subject-reduction name.  They are CONDITIONAL: the union's `elim` arm at the
natElim / natRec row stores but does not premise the step branch, and the recursive-call substituent is
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

/-! ## (2b) The conditional substituting-ι + β + app-chain subject-reduction theorems (the six TYTAB-2
deferred rows)

Six more substituting / constructor-elimination root-redex shapes, all CONDITIONAL exactly as the two
succ arms are.  Two regimes:

  * **App-chain value-selectors (option-some / either-inl / either-inr / list-cons).**  The ι reduct
    APPLIES the selected handler to the constructor payload — `optionMatch(.., some v) ↝ app(someBranch, v)`
    etc. — building an `app` cell (no binder descent), so the reduct typing is the `unionAppCellTyped`
    builder fed the handler typing and the payload typing.  These carry NO substituent-transport residual:
    the application output collapses by `subst0_weaken` (the non-dependent handler codomain is weakened).
    The handler + payload typings are supplied as hypotheses (the eliminator-head inversion surfaces the
    handler at the Π handler type; the payload at the element type is the introducer-head inversion the
    union does not yet ship for the data constructors — supplied here so the statement stays self-contained
    and matches the conditional succ-arm style).

  * **β + endpoint-β (the genuine 1-binder substitutions).**  `app(lam(_, body), arg) ↝ subst0 body arg`
    and the path twin `pathApp(pathLam(body), endpoint) ↝ subst0 body endpoint` substitute the argument
    INTO the body binder.  As with the succ arms, the union's binder descent with a union-typed substituent
    is the no-conv-arm residual (`UnionSubst0Transports`), supplied as a hypothesis alongside the body
    typing; the residual dissolves at the conv-closure work (NATIVE-46).

The list-cons step both selects AND recurses: its reduct `app(app(app(consBranch, head), tail), recCall)`
threads the recursive `listElim` call (built through the union's own `elim` arm, exactly as
`natElimRecursiveCallUnionTyped` closes the nat-recursion loop) into the curried handler app-chain. -/

/-- The union-substituent 1-binder transport for a β / endpoint-β redex: a body typed in the UNION at a
codomain under one binder, substituted at `var 0 := argument` with a UNION-typed substituent, is
union-typed at the substituted codomain.  This is `substRespectingContext` at `singleton argument` with a
UNION inner substituent — the ingredient the host `subst0` cannot supply (its substituent must be
host-typed).  Building it needs union-image binder descent (general union weakening), the seed union's
no-conv-arm gap; so it is the residual the β / endpoint-β discharge consumes, the 1-binder twin of
`UnionSubstPairTransports`. -/
abbrev UnionSubst0Transports (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (domain : RawTerm scope) : Prop :=
  ∀ (body codomain : RawTerm (scope + 1)) (argument : RawTerm scope),
    HasTypeUnion profile (context.cons domain) body codomain →
      HasTypeUnion profile context argument domain →
      HasTypeUnion profile context
        (RawTerm.subst0 body argument) (RawTerm.subst0 codomain argument)

/-- **optionMatch on `optionSome` applies the Some handler, typed (conditional, Conv-modulo).**
`optionMatch(motive, noneBranch, someBranch, some(v))` ι-steps to `app(someBranch, v)`
(`IotaHeadStep.iotaOptionMatchSome.toStep`).  Given the Some handler union-typed at `A → C` (the
`invertAtOptionMatchHead` premise) and the payload `v` union-typed at the element type `A`, the reduct is
union-typed at `C` (the `unionAppCellTyped` output `subst0 (weaken C) v` collapses to `C` by
`subst0_weaken`), Conv-equal to the ambient classifier (the conv wall: the result is read off the option
type, convertible to but not syntactically the classifier).  Conditional exactly as the succ arms are: the
handler + payload typings are supplied (the eliminator-head inversion surfaces the handler; the data
constructor's introducer-head inversion is not yet union-shipped), not premised by a redex typing. -/
theorem unionSubjectReductionOptionMatchSome {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {noneBranch someBranch value classifier : RawTerm scope}
    (elementType resultType : RawTerm scope)
    (someBranchTyped : HasTypeUnion profile context someBranch
      (piTyCodeCell elementType (RawTerm.weaken resultType)))
    (valueTyped : HasTypeUnion profile context value elementType)
    (resultConverts : Conv resultType classifier) :
    Step (optionMatchCell motive noneBranch someBranch (optionSomeCell value))
        (appCell someBranch value) ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context (appCell someBranch value) pinnedClassifier ∧
      Conv pinnedClassifier classifier := by
  refine ⟨IotaHeadStep.iotaOptionMatchSome.toStep, resultType, ?_, resultConverts⟩
  have applied := unionAppCellTyped someBranch value elementType (RawTerm.weaken resultType)
    someBranchTyped valueTyped
  rwa [RawTerm.subst0_weaken] at applied

/-- **eitherMatch on `eitherInl` applies the left handler, typed (conditional, Conv-modulo).**
`eitherMatch(motive, leftBranch, rightBranch, inl(v))` ι-steps to `app(leftBranch, v)`
(`IotaHeadStep.iotaEitherMatchInl.toStep`); given the left handler union-typed at `A → C` and the payload at the
left type `A`, the reduct is union-typed at `C` (collapse by `subst0_weaken`), Conv-equal to the
classifier. -/
theorem unionSubjectReductionEitherMatchInl {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {leftBranch rightBranch value classifier : RawTerm scope}
    (leftType resultType : RawTerm scope)
    (leftBranchTyped : HasTypeUnion profile context leftBranch
      (piTyCodeCell leftType (RawTerm.weaken resultType)))
    (valueTyped : HasTypeUnion profile context value leftType)
    (resultConverts : Conv resultType classifier) :
    Step (eitherMatchCell motive leftBranch rightBranch (eitherInlCell value))
        (appCell leftBranch value) ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context (appCell leftBranch value) pinnedClassifier ∧
      Conv pinnedClassifier classifier := by
  refine ⟨IotaHeadStep.iotaEitherMatchInl.toStep, resultType, ?_, resultConverts⟩
  have applied := unionAppCellTyped leftBranch value leftType (RawTerm.weaken resultType)
    leftBranchTyped valueTyped
  rwa [RawTerm.subst0_weaken] at applied

/-- **eitherMatch on `eitherInr` applies the right handler, typed (conditional, Conv-modulo).**  The
right-injection twin: `eitherMatch(.., inr(v)) ↝ app(rightBranch, v)`
(`IotaHeadStep.iotaEitherMatchInr.toStep`), the reduct union-typed at `C` via the right handler at `B → C` and
the payload at the right type `B`, Conv-equal to the classifier. -/
theorem unionSubjectReductionEitherMatchInr {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {leftBranch rightBranch value classifier : RawTerm scope}
    (rightType resultType : RawTerm scope)
    (rightBranchTyped : HasTypeUnion profile context rightBranch
      (piTyCodeCell rightType (RawTerm.weaken resultType)))
    (valueTyped : HasTypeUnion profile context value rightType)
    (resultConverts : Conv resultType classifier) :
    Step (eitherMatchCell motive leftBranch rightBranch (eitherInrCell value))
        (appCell rightBranch value) ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context (appCell rightBranch value) pinnedClassifier ∧
      Conv pinnedClassifier classifier := by
  refine ⟨IotaHeadStep.iotaEitherMatchInr.toStep, resultType, ?_, resultConverts⟩
  have applied := unionAppCellTyped rightBranch value rightType (RawTerm.weaken resultType)
    rightBranchTyped valueTyped
  rwa [RawTerm.subst0_weaken] at applied

/-- **β substitutes the argument into the body, typed (conditional).**  A union-typed
`app(lam(domain, body), arg)` ι-steps to `subst0 body arg` (`HeadStep.beta` lifted through `Step.beta`);
given the body union-typed at the codomain under the domain binder and the argument union-typed at the
domain, the union-image 1-binder transport (`UnionSubst0Transports`) types the reduct at
`subst0 codomain arg`.  The β twin of the succ arms: the substituent is union-typed (the body's λ-bound
variable image is the argument), so the reduct rides the no-conv-arm transport residual. -/
theorem unionSubjectReductionBeta {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (domain : RawTerm scope) (body codomain : RawTerm (scope + 1)) (argument : RawTerm scope)
    (bodyTyped : HasTypeUnion profile (context.cons domain) body codomain)
    (argumentTyped : HasTypeUnion profile context argument domain)
    (unionTransport : UnionSubst0Transports profile context domain) :
    Step (appCell (lamCell domain body) argument) (RawTerm.subst0 body argument) ∧
    HasTypeUnion profile context
      (RawTerm.subst0 body argument) (RawTerm.subst0 codomain argument) :=
  ⟨Step.beta, unionTransport body codomain argument bodyTyped argumentTyped⟩

/-- **endpoint-β substitutes the interval endpoint into the path body, typed (conditional).**  A
union-typed `pathApp(pathLam(body), endpoint)` ι-steps to `subst0 body endpoint`
(`Step.pathBeta`); given the body union-typed at the carrier under the interval binder and the endpoint
union-typed at the interval type, the union-image 1-binder transport types the reduct at
`subst0 carrier endpoint`.  The path twin of β. -/
theorem unionSubjectReductionEndpointBeta {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (body carrier : RawTerm (scope + 1)) (endpoint : RawTerm scope)
    (bodyTyped : HasTypeUnion profile (context.cons intervalTypeCell) body carrier)
    (endpointTyped : HasTypeUnion profile context endpoint intervalTypeCell)
    (unionTransport : UnionSubst0Transports profile context intervalTypeCell) :
    Step (pathAppCell (pathLamCell body) endpoint) (RawTerm.subst0 body endpoint) ∧
    HasTypeUnion profile context
      (RawTerm.subst0 body endpoint) (RawTerm.subst0 carrier endpoint) :=
  ⟨stepOverTable_iff_step.mp (StepTable.pathBetaFires body endpoint),
    unionTransport body carrier endpoint bodyTyped endpointTyped⟩

/-- The recursive call `listElim(motive, tail, nilBranch, consBranch)` is union-typed at `resultType` — by
the union's own `elim` arm at the `gen_listElim` row, given the tail union-typed at `List(elementType)`,
the nil branch at `resultType`, and the cons branch at the curried step type.  The list twin of
`natElimRecursiveCallUnionTyped`: the recursion loop closes through the union's listElim elim arm. -/
theorem listElimRecursiveCallUnionTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (tail nilBranch consBranch elementType resultType : RawTerm scope)
    (tailTyped : HasTypeUnion profile context tail (listTypeCell elementType))
    (nilBranchTyped : HasTypeUnion profile context nilBranch resultType)
    (consBranchTyped : HasTypeUnion profile context consBranch
      (listStepFunctionType elementType resultType)) :
    HasTypeUnion profile context
      (listElimCell motive tail nilBranch consBranch) resultType := by
  refine HasTypeUnion.elim context .gen_listElim listElimRule
    (.childCons motive (.childCons tail (.childCons nilBranch (.childCons consBranch .childNil))))
    (.childCons elementType (.childCons resultType .childNil)) rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact tailTyped
  | tail _ hmem => cases hmem with
    | head => exact nilBranchTyped
    | tail _ hmem => cases hmem with
      | head => exact consBranchTyped
      | tail _ hmem => cases hmem

/-- **listElim on `listCons` applies the cons handler and recurses, typed (conditional, Conv-modulo).**
`listElim(motive, cons(head, tail), nilBranch, consBranch)` ι-steps to
`app(app(app(consBranch, head), tail), listElim(motive, tail, nilBranch, consBranch))`
(`IotaHeadStep.iotaListElimCons.toStep`) — the curried cons handler is applied to the head, the tail, and the
recursive call on the tail.  Given the head at `elementType`, the tail at `List(elementType)`, the nil
branch at `resultType`, and the cons branch at the curried step type
`elementType → List(elementType) → resultType → resultType`, the reduct is union-typed at `resultType`:
each of the three applications collapses its non-dependent codomain by `subst0_weaken`, and the recursive
call is built through the union's own listElim elim arm (`listElimRecursiveCallUnionTyped`, the list twin
of the nat recursion-loop close).  The recursive twin of the natElim-succ arm.  Carries NO substituent
transport residual: the contractum is a pure app-chain (no binder descent). -/
theorem unionSubjectReductionListElimCons {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {headValue tailList nilBranch consBranch classifier : RawTerm scope}
    (elementType resultType : RawTerm scope)
    (headTyped : HasTypeUnion profile context headValue elementType)
    (tailTyped : HasTypeUnion profile context tailList (listTypeCell elementType))
    (nilBranchTyped : HasTypeUnion profile context nilBranch resultType)
    (consBranchTyped : HasTypeUnion profile context consBranch
      (listStepFunctionType elementType resultType))
    (resultConverts : Conv resultType classifier) :
    Step (listElimCell motive (listConsCell headValue tailList) nilBranch consBranch)
        (appCell
          (appCell (appCell consBranch headValue) tailList)
          (listElimCell motive tailList nilBranch consBranch)) ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context
        (appCell
          (appCell (appCell consBranch headValue) tailList)
          (listElimCell motive tailList nilBranch consBranch)) pinnedClassifier ∧
      Conv pinnedClassifier classifier := by
  refine ⟨IotaHeadStep.iotaListElimCons.toStep, resultType, ?_, resultConverts⟩
  -- The cons branch is `A → (List A → (C → C))` (every codomain weakened past its binder).  Apply to the
  -- head (collapse `subst0_weaken` to `List A → (C → C)`), to the tail (collapse to `C → C`), then to the
  -- recursive call (collapse to `C`).
  have appliedHead := unionAppCellTyped consBranch headValue elementType
    (RawTerm.weaken (piTyCodeCell (listTypeCell elementType)
      (RawTerm.weaken (piTyCodeCell resultType (RawTerm.weaken resultType)))))
    consBranchTyped headTyped
  rw [RawTerm.subst0_weaken] at appliedHead
  have appliedTail := unionAppCellTyped (appCell consBranch headValue) tailList
    (listTypeCell elementType)
    (RawTerm.weaken (piTyCodeCell resultType (RawTerm.weaken resultType)))
    appliedHead tailTyped
  rw [RawTerm.subst0_weaken] at appliedTail
  have recursiveCall := listElimRecursiveCallUnionTyped context motive tailList nilBranch consBranch
    elementType resultType tailTyped nilBranchTyped consBranchTyped
  have appliedRec := unionAppCellTyped (appCell (appCell consBranch headValue) tailList)
    (listElimCell motive tailList nilBranch consBranch) resultType (RawTerm.weaken resultType)
    appliedTail recursiveCall
  rwa [RawTerm.subst0_weaken] at appliedRec

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
  /-- fst-pair reduct is typed (Conv-modulo: the projected first component carries its own type, read off
  the pair's product code, convertible to the classifier). -/
  fstPairReductTyped : ∀ {scope : Nat} {context : TypingContext profile scope}
    {firstValue secondValue classifier : RawTerm scope},
    HasTypeUnion profile context (fstCell (pairCell firstValue secondValue)) classifier →
    Step (fstCell (pairCell firstValue secondValue)) firstValue ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context firstValue pinnedClassifier ∧
      Conv pinnedClassifier classifier
  /-- snd-pair reduct is typed (Conv-modulo: the projected second component carries its own type). -/
  sndPairReductTyped : ∀ {scope : Nat} {context : TypingContext profile scope}
    {firstValue secondValue classifier : RawTerm scope},
    HasTypeUnion profile context (sndCell (pairCell firstValue secondValue)) classifier →
    Step (sndCell (pairCell firstValue secondValue)) secondValue ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context secondValue pinnedClassifier ∧
      Conv pinnedClassifier classifier

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
  fstPairReductTyped := fun typed => unionSubjectReductionFstPair typed
  sndPairReductTyped := fun typed => unionSubjectReductionSndPair typed

/-! ## (4) The total master dispatcher over `Step`

The master cases over an arbitrary root `Step` of a union-typed redex and routes every shape to one of
three honest outcomes.  CONGRUENCE is surfaced (not typed) because its reduct typing hits the conv wall;
the substituting and constructor-elimination redexes are surfaced too because their reduct typing needs a
substituent transport (β / recursive succ-cons ι) or a data-constructor inversion (projection /
app-chain ι) — both follow-up work.  The seven branch-selection ι are the ones PROVEN here. -/

/-- The substituting-or-constructor-elimination root-redex shapes whose reduct typing this file defers:
β (substitutes the argument), the recursive succ/cons ι (substitute the recursive call), the projection /
app-chain ι (reduct typing routes through a data-constructor inversion), `idStrictRec` on `refl`
(which has no union arm — the union types no `idStrictRec`-headed cell), and endpoint-β (`pathApp` on
`pathLam`, the path-twin of β — substitutes the path argument).  An exact enumeration: the master
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
  ∨ (∃ (pathBody : RawTerm (scope + 1)) (argument : RawTerm scope),
      redex = pathAppCell (pathLamCell pathBody) argument)

/-- The endpoint-β (`pathBeta`) row's firing surfaces the redex as the deferred `pathApp(pathLam(_), _)`
shape.  The path-twin of `betaRowFiringToHeadStep`: takes the abstract spine implicitly, splits it into
the two `pathApp` children, and reads the path-lambda head off `pathBetaRowFiringDecompose`. -/
theorem pathBetaRowFiringIsDeferredShape {scope : Nat}
    (elimPayload : pathBetaIotaRow.elimGenerator.payload scope)
    {spine : RawTermChildren pathBetaIotaRow.elimGenerator.binderShifts scope}
    {reduct : RawTerm scope}
    (fires : pathBetaIotaRow.firesOn? elimPayload spine = some reduct) :
    ∃ (pathBody : RawTerm (scope + 1)) (argument : RawTerm scope),
      RawTerm.mkGen pathBetaIotaRow.elimGenerator elimPayload spine
        = pathAppCell (pathLamCell pathBody) argument := by
  revert fires
  cases spine with
  | childCons functionChild restSpine =>
    cases restSpine with
    | childCons argumentChild restNil =>
      cases restNil
      intro fires
      obtain ⟨pathBody, functionEq, _reductEq⟩ := pathBetaRowFiringDecompose fires
      subst functionEq
      exact ⟨pathBody, argumentChild, rfl⟩

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
  cases stepOverTable_iff_step.mpr stepHyp with
  | cong generator payload childStep =>
      exact Or.inr (Or.inl ⟨generator, payload, _, _, rfl, rfl,
        StepOverTableChildren.toStepChildren childStep⟩)
  | tableRedex isRow elimPayload fires =>
    cases isRow with
    | head =>
        -- beta row: the firing pins the function child to a λ, so the
        -- head-step inversion can only be the β contraction
        cases betaRowFiringToHeadStep elimPayload fires with
        | beta => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩))
        | appCongruence functionStep =>
            rename_i functionValue _functionReduct _argumentValue
            cases functionValue with
            | mkGen functionGen functionPayload functionChildren =>
              have isLamHead : functionGen = .gen_lam :=
                IotaRuleDesc.firesOn?_some_primaryHead fires rfl rfl
              subst isLamHead
              cases functionChildren with
              | childCons domainAnn lamRest =>
                cases lamRest with
                | childCons lamBody lamNil =>
                  cases lamNil
                  exact absurd functionStep HeadStep.not_from_lam
    | tail _ isRow => cases isRow with
      | head =>
          cases boolTrueRowFiringToIotaHead elimPayload fires with
          | iotaBoolTrue =>
              exact Or.inl ⟨classifier,
                (unionSubjectReductionBoolElimTrue typed).2,
                Conv.refl classifier⟩
          | iotaBoolFalse =>
              exact Or.inl ⟨classifier,
                (unionSubjectReductionBoolElimFalse typed).2,
                Conv.refl classifier⟩
      | tail _ isRow => cases isRow with
        | head =>
            cases boolFalseRowFiringToIotaHead elimPayload fires with
            | iotaBoolTrue =>
                exact Or.inl ⟨classifier,
                  (unionSubjectReductionBoolElimTrue typed).2,
                  Conv.refl classifier⟩
            | iotaBoolFalse =>
                exact Or.inl ⟨classifier,
                  (unionSubjectReductionBoolElimFalse typed).2,
                  Conv.refl classifier⟩
        | tail _ isRow => cases isRow with
          | head =>
              cases fstPairRowFiringToIotaHead elimPayload fires with
              | iotaFstPair =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))
          | tail _ isRow => cases isRow with
            | head =>
                cases sndPairRowFiringToIotaHead elimPayload fires with
                | iotaSndPair =>
                    exact Or.inr (Or.inr (Or.inr (Or.inr
                      (Or.inl ⟨_, _, rfl⟩))))
            | tail _ isRow => cases isRow with
              | head =>
                  cases natElimZeroRowFiringToIotaHead elimPayload fires with
                  | iotaNatElimZero =>
                      exact Or.inl ⟨classifier,
                        (unionSubjectReductionNatElimZero typed).2,
                        Conv.refl classifier⟩
                  | iotaNatElimSucc =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))))))))
              | tail _ isRow => cases isRow with
                | head =>
                    cases natRecZeroRowFiringToIotaHead elimPayload fires with
                    | iotaNatRecZero =>
                        exact Or.inl ⟨classifier,
                          (unionSubjectReductionNatRecZero typed).2,
                          Conv.refl classifier⟩
                    | iotaNatRecSucc =>
                        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                          (Or.inr (Or.inr (Or.inr
                            (Or.inl ⟨_, _, _, _, rfl⟩)))))))))
                | tail _ isRow => cases isRow with
                  | head =>
                      cases natElimSuccRowFiringToIotaHead elimPayload
                          fires with
                      | iotaNatElimZero =>
                          exact Or.inl ⟨classifier,
                            (unionSubjectReductionNatElimZero typed).2,
                            Conv.refl classifier⟩
                      | iotaNatElimSucc =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                            (Or.inr (Or.inr (Or.inr
                              (Or.inl ⟨_, _, _, _, rfl⟩))))))))
                  | tail _ isRow => cases isRow with
                    | head =>
                        cases natRecSuccRowFiringToIotaHead elimPayload
                            fires with
                        | iotaNatRecZero =>
                            exact Or.inl ⟨classifier,
                              (unionSubjectReductionNatRecZero typed).2,
                              Conv.refl classifier⟩
                        | iotaNatRecSucc =>
                            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                              (Or.inr (Or.inr (Or.inr (Or.inr
                                (Or.inl ⟨_, _, _, _, rfl⟩)))))))))
                    | tail _ isRow => cases isRow with
                      | head =>
                          cases listElimNilRowFiringToIotaHead elimPayload
                              fires with
                          | iotaListElimNil =>
                              exact Or.inl
                                (unionSubjectReductionListElimNil typed).2
                          | iotaListElimCons =>
                              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                  (Or.inl ⟨_, _, _, _, _, rfl⟩))))))))))
                      | tail _ isRow => cases isRow with
                        | head =>
                            cases listElimConsRowFiringToIotaHead
                                elimPayload fires with
                            | iotaListElimNil =>
                                exact Or.inl
                                  (unionSubjectReductionListElimNil typed).2
                            | iotaListElimCons =>
                                exact Or.inr (Or.inr (Or.inr (Or.inr
                                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                    (Or.inr (Or.inl
                                      ⟨_, _, _, _, _, rfl⟩))))))))))
                        | tail _ isRow => cases isRow with
                          | head =>
                              cases optionMatchNoneRowFiringToIotaHead
                                  elimPayload fires with
                              | iotaOptionMatchNone =>
                                  exact Or.inl
                                    (unionSubjectReductionOptionMatchNone
                                      typed).2
                              | iotaOptionMatchSome =>
                                  exact Or.inr (Or.inr (Or.inr (Or.inr
                                    (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)))))
                          | tail _ isRow => cases isRow with
                            | head =>
                                cases optionMatchSomeRowFiringToIotaHead
                                    elimPayload fires with
                                | iotaOptionMatchNone =>
                                    exact Or.inl
                                      (unionSubjectReductionOptionMatchNone
                                        typed).2
                                | iotaOptionMatchSome =>
                                    exact Or.inr (Or.inr (Or.inr (Or.inr
                                      (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)))))
                            | tail _ isRow => cases isRow with
                              | head =>
                                  cases eitherMatchInlRowFiringToIotaHead
                                      elimPayload fires with
                                  | iotaEitherMatchInl =>
                                      exact Or.inr (Or.inr (Or.inr (Or.inr
                                        (Or.inr (Or.inr (Or.inl
                                          ⟨_, _, _, _, rfl⟩))))))
                                  | iotaEitherMatchInr =>
                                      exact Or.inr (Or.inr (Or.inr (Or.inr
                                        (Or.inr (Or.inr (Or.inr (Or.inl
                                          ⟨_, _, _, _, rfl⟩)))))))
                              | tail _ isRow => cases isRow with
                                | head =>
                                    cases eitherMatchInrRowFiringToIotaHead
                                        elimPayload fires with
                                    | iotaEitherMatchInl =>
                                        exact Or.inr (Or.inr (Or.inr
                                          (Or.inr (Or.inr (Or.inr (Or.inl
                                            ⟨_, _, _, _, rfl⟩))))))
                                    | iotaEitherMatchInr =>
                                        exact Or.inr (Or.inr (Or.inr
                                          (Or.inr (Or.inr (Or.inr (Or.inr
                                            (Or.inl
                                              ⟨_, _, _, _, rfl⟩)))))))
                                | tail _ isRow => cases isRow with
                                  | head =>
                                      cases idJReflRowFiringToIotaHead
                                          elimPayload fires with
                                      | iotaIdJRefl =>
                                          exact Or.inl ⟨classifier,
                                            (unionSubjectReductionIdJRefl
                                              typed).2,
                                            Conv.refl classifier⟩
                                  | tail _ isRow => cases isRow with
                                    | head =>
                                        cases
                                          idStrictRecReflRowFiringToIotaHead
                                            elimPayload fires with
                                        | iotaIdStrictRecRefl =>
                                            exact Or.inr (Or.inr (Or.inr
                                              (Or.inr (Or.inr (Or.inr
                                                (Or.inr (Or.inr (Or.inr
                                                  (Or.inr (Or.inr (Or.inl
                                                    ⟨_, _, _,
                                                      rfl⟩)))))))))))
                                    | tail _ isRow => cases isRow with
                                      | head =>
                                          -- pathBeta (endpoint-β) row: the redex is the deferred
                                          -- `pathApp(pathLam(_), _)` substituting shape (path-twin of β)
                                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                              (pathBetaRowFiringIsDeferredShape
                                                elimPayload fires))))))))))))
                                      | tail _ isRow => cases isRow with
                                        | head =>
                                            -- quotRecMk row: `gen_quotRec` carries no union typing rule
                                            exact (typed.reservedHeadUntyped rfl).elim
                                        | tail _ isRow => cases isRow with
                                          | head =>
                                              -- quotElimMk row: `gen_quotElim` carries no union typing rule
                                              exact (typed.reservedHeadUntyped rfl).elim
                                          | tail _ isRow => cases isRow with
                                            | head =>
                                                -- truncRecIntro row: `gen_truncRec` carries no union rule
                                                exact (typed.reservedHeadUntyped rfl).elim
                                            | tail _ isRow => cases isRow with
                                              | head =>
                                                  -- gel-β row: `gen_ungel` carries no union typing rule
                                                  exact (typed.reservedHeadUntyped rfl).elim
                                              | tail _ isRow => cases isRow

end FX1Poly.Typed

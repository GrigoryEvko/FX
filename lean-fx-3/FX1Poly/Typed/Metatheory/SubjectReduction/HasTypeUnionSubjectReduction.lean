import FX1Poly.Typed.Engine.Union.HasTypeUnionMatchInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionPathProjInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionRecursiveInversion
import FX1Poly.Typed.Engine.Union.HasTypeUnionSubstitution
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionUnionSubstituent
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionValidity
import FX1Poly.Typed.Corpus.Faithfulness.RecursorHostFold
import FX1Poly.Typed.Engine.Classifier.UnionStaticTypingSoundness
import FX1Poly.Typed.Engine.Formation.ConvFlatCodeInjectivity
import FX1Poly.Typed.Ledger.Misc.ConvDataCodeInjectivity
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

  * **App-chain ι (GENUINE-EXCEPT-RECLASSIFICATION — option-some / either-inl/inr / list-cons).**  The ι
    reduct APPLIES the selected handler to the constructor payload — `optionMatch(.., some v) ↝ app(someBranch, v)`
    etc., the list-cons step ALSO recursing.  These four rows now take the REDEX TYPING as their SOLE typing
    input: the eliminator-head inversion (`invertAtOptionMatchHead` / `invertAtEitherMatchHead` /
    `invertAtListElimHead`) DERIVES the handler at its Π handler type AND the scrutinee at the constructor's
    data type; the NEW data-constructor introducer-head inversions (`invertAtOptionSomeHead` /
    `invertAtEitherInlHead` / `invertAtEitherInrHead` / `invertAtListConsHead`) DERIVE the payload at its own
    type with the element-type `Conv` (via `optionCode_inj` / `eitherCode_inj` / `listCode_inj`).  The reduct
    is `unionAppCellTyped` (NO binder descent, the non-dependent codomain collapsing by `subst0_weaken`) fed
    the DERIVED handler + the payload RECLASSIFIED across the element `Conv`.  The lone surviving hypothesis is
    that reclassification — the `UnionElementReclassifies` residual (the no-validity / type-Conv-closure gap:
    the union `conv` arm reclassifies only WITH a universe witness for the element type, which no inversion
    surfaces — the same wall the host `piElimUpToClassifierConv` factors out).  The list-cons step both selects
    AND recurses, threading the recursive `listElim` call (built through the union's own `elim` arm
    via `listElimRecursiveCallUnionTyped`, fed the DERIVED nil/cons branches) into the curried app-chain.

  * **Substituting ι + β (UNCONDITIONAL — the binder descent and the cumulative former are both SHIPPED).**
    natElim/natRec on `succ` and β / endpoint-β SUBSTITUTE a UNION-typed argument into a binder.  The binder
    descent is shipped (`HasTypeUnion.subst0WithUnionImage` / `substPairNonDependentUnionImages`, the
    union-substituent substitution lemmas — substitute a union-but-not-host argument into a union body), and
    its sole formation arm closes through `unionCumulativeFormerCloses` (wave U3 — the five cumulative codes
    `gen_piTyCode`/`gen_sigmaTyCode`/`gen_listCode`/`gen_optionCode`/`gen_unitCode` are now `formationRuleOf`
    rows), so these rows are UNCONDITIONAL.

The branch-selection + projection reducts are unconditional; the app-chain rows carry only the single
`UnionElementReclassifies` residual; the β-family rows are unconditional.  The two succ arms ride the
SHIPPED `natElimSuccIotaComputesTypedInUnion` / `natRecSuccIotaComputesTypedInUnion` (NATIVE-37 part b),
fed the unconditional transport `unionSubstPairTransports`.

## Zero-axiom

Each unconditional arm is the shipped head inversion + the matching `Step` ι constructor (+ for the
projections the new `invertAtPairHead` + `productCode_inj`); each app-chain arm is the eliminator-head +
data-constructor introducer-head inversions + the data-code `Conv`-injectivity + `unionAppCellTyped` + the
`UnionElementReclassifies` residual; each substituting arm is the unconditional union-substituent
transport + the matching `Step` / `IotaHeadStep` constructor.  The new introducer-head inversions are free-subject `induction` + the shipped
`introRuleOf_cases` seventeen-row inverter + head no-confusion + the matching `*CellHasNoTyping` refutation
(listCons via the table-generic `cellHasNoTypingWhenRootGenericallyExcluded`).  The master is a free-subject
`cases` over `Step` (propext-clean — `Step` is a small inductive, no 205-ctor wildcard).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditUnionSubjectReduction.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax FX1Poly.Modal

/-! ## (0) Local building blocks the projection / app-chain rows consume

The data-constructor introducer-head inversions + the app-row builder the projection / app-chain rows need:

  * `HasTypeUnion.invertAtPairHead` — the introducer-head inversion at the `gen_pair` row (the
    `invertAtNatSuccHead` twin: pin the `gen_pair` intro row, surface BOTH component premises, read the
    output `product` code off the row params).  The projection rows `fst`/`snd` consume it after the
    shipped `invertAtFstHead`/`invertAtSndHead` surface the pair-as-a-whole.
  * `HasTypeUnion.invertAtOptionSomeHead` / `invertAtEitherInlHead` / `invertAtEitherInrHead` /
    `invertAtListConsHead` — the introducer-head inversions for the four data constructors the select-then-apply
    ι rows eliminate: each pins its `gen_*` intro row, surfaces the payload premise(s), and reads the output
    `option`/`either`/`List` code off the row params (so the classifier `Conv`s to it).  The app-chain rows
    consume them (after the eliminator-head inversion surfaces the scrutinee at the data type) to DERIVE the
    payload typing, leaving only the element reclassification.  `eitherInr`'s output puts the free LEFT type
    first; `listCons`'s grown disjunct is killed by the table-generic
    `cellHasNoTypingWhenRootGenericallyExcluded` (no named `listConsCellHasNoTyping` ships).
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
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
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
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      -- The unified eliminator arm: no eliminator row produces a `pair`-headed cell (pair is a data
      -- constructor), so the row's generator clashes with `gen_pair` (`elimRuleOf gen_pair = none`).
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_pair :=
        (elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      rw [headEq] at isElim
      exact absurd isElim (by intro tableHit; cases tableHit)

/-- **★ Inversion at the optionSome head.**  A union typing of an `optionSomeCell`-headed subject IS a
unary data introduction at the `gen_optionSome` row: for some payload type `A`, the payload value is
union-typed at `A` and the classifier is convertible to `option(A)`.  No grown disjunct: `optionSomeCell`
is untypable in the grown engine (`optionSomeCellHasNoTyping`).  The `invertAtPairHead` twin for the unary
Option constructor; the scrutinee-introducer inversion the option-some ι reduct's reduct typing consumes. -/
theorem HasTypeUnion.invertAtOptionSomeHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {payloadValue : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = optionSomeCell payloadValue) :
    ∃ payloadType : RawTerm scope,
      HasTypeUnion profile context payloadValue payloadType ∧
      Conv (optionTypeCell payloadType) classifier := by
  induction derivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨payloadType, payloadTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨payloadType, payloadTyped, convInner.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.optionSomeCellHasNoTyping (fun contra => contra)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      -- The unified introducer arm: only the `gen_optionSome` row produces an `optionSome`-headed cell.
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
      -- ★ optionSome — the SURVIVOR.  Destructure args (`[0]`) + params (`[0]`), recover the payload from
      -- `subjectShape`, surface its premise; the output type IS `option(A)`, so the Conv is `refl`.
      · match args, params with
        | .childCons _armValue .childNil, .childCons _payloadType .childNil =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, premisesHold _ (List.Mem.head _), Conv.refl _⟩
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
      -- pair
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- refl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      -- The unified eliminator arm: no eliminator row produces an `optionSome`-headed cell.
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_optionSome :=
        (elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      rw [headEq] at isElim
      exact absurd isElim (by intro tableHit; cases tableHit)

/-- **★ Inversion at the eitherInl head.**  A union typing of an `eitherInlCell`-headed subject IS a left
coproduct introduction at the `gen_eitherInl` row: for some left/right types `A`, `B`, the payload value is
union-typed at the LEFT type `A` and the classifier is convertible to `either(A, B)`.  No grown disjunct:
`eitherInlCell` is untypable in the grown engine (`eitherInlCellHasNoTyping`).  The `invertAtOptionSomeHead`
twin for the left injection. -/
theorem HasTypeUnion.invertAtEitherInlHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {payloadValue : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = eitherInlCell payloadValue) :
    ∃ leftType rightType : RawTerm scope,
      HasTypeUnion profile context payloadValue leftType ∧
      Conv (eitherTypeCell leftType rightType) classifier := by
  induction derivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨leftType, rightType, payloadTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨leftType, rightType, payloadTyped, convInner.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.eitherInlCellHasNoTyping (fun contra => contra)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      -- The unified introducer arm: only the `gen_eitherInl` row produces an `eitherInl`-headed cell.
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
      -- ★ eitherInl — the SURVIVOR.  Destructure args (`[0]`) + params (`[0, 0]`), recover the payload from
      -- `subjectShape`, surface its premise at the LEFT type; the output type IS `either(A, B)` (left first),
      -- so the Conv is `refl`.
      · match args, params with
        | .childCons _armValue .childNil,
          .childCons _leftType (.childCons _rightType .childNil) =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, _, premisesHold _ (List.Mem.head _), Conv.refl _⟩
      -- eitherInr
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- pair
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- refl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      -- The unified eliminator arm: no eliminator row produces an `eitherInl`-headed cell.
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_eitherInl :=
        (elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      rw [headEq] at isElim
      exact absurd isElim (by intro tableHit; cases tableHit)

/-- **★ Inversion at the eitherInr head.**  A union typing of an `eitherInrCell`-headed subject IS a right
coproduct introduction at the `gen_eitherInr` row: for some left/right types `A`, `B`, the payload value is
union-typed at the RIGHT type `B` and the classifier is convertible to `either(A, B)`.  No grown disjunct:
`eitherInrCell` is untypable in the grown engine (`eitherInrCellHasNoTyping`).  The right-injection twin of
`invertAtEitherInlHead` (the row's output puts the free LEFT type first, the value's RIGHT type second). -/
theorem HasTypeUnion.invertAtEitherInrHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {payloadValue : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = eitherInrCell payloadValue) :
    ∃ leftType rightType : RawTerm scope,
      HasTypeUnion profile context payloadValue rightType ∧
      Conv (eitherTypeCell leftType rightType) classifier := by
  induction derivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨leftType, rightType, payloadTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨leftType, rightType, payloadTyped, convInner.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      exact absurd hostTyped.eitherInrCellHasNoTyping (fun contra => contra)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      -- The unified introducer arm: only the `gen_eitherInr` row produces an `eitherInr`-headed cell.
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
      -- ★ eitherInr — the SURVIVOR.  Destructure args (`[0]`) + params (`[0, 0]`), recover the payload from
      -- `subjectShape`, surface its premise at the value's pinned type `typeParam0`; the output type IS
      -- `either(typeParam1, typeParam0)` (free LEFT first, value's RIGHT second), so the Conv is `refl`.
      · match args, params with
        | .childCons _armValue .childNil,
          .childCons _rightType (.childCons _leftType .childNil) =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, _, premisesHold _ (List.Mem.head _), Conv.refl _⟩
      -- pair
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- refl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      -- The unified eliminator arm: no eliminator row produces an `eitherInr`-headed cell.
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_eitherInr :=
        (elimMemberCellRootGenerator isElimUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)
      rw [headEq] at isElim
      exact absurd isElim (by intro tableHit; cases tableHit)

/-- **★ Inversion at the listCons head.**  A union typing of a `listConsCell`-headed subject IS a binary
recursive list introduction at the `gen_listCons` row: for some element type `A`, the head is union-typed at
`A`, the tail at `List(A)`, and the classifier is convertible to `List(A)`.  No grown disjunct: `listConsCell`
is untypable in the grown engine (refuted inline by the table-generic `cellHasNoTypingWhenRootGenericallyExcluded`,
as the `*CellHasNoTyping` lemmas are; the union ships no named `listConsCellHasNoTyping`).  The recursive twin
of `invertAtOptionSomeHead` — the scrutinee-introducer inversion the list-cons ι reduct consumes for its
head + tail premises. -/
theorem HasTypeUnion.invertAtListConsHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {headValue tailList : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (subjectShape : subject = listConsCell headValue tailList) :
    ∃ elementType : RawTerm scope,
      HasTypeUnion profile context headValue elementType ∧
      HasTypeUnion profile context tailList (listTypeCell elementType) ∧
      Conv (listTypeCell elementType) classifier := by
  induction derivation with
  | var _context _index =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | universeFormation _context _levelExpr _flag =>
      exact absurd (congrArg RawTerm.rootGenerator subjectShape) (by intro headEq; cases headEq)
  | conv levelExpr flag typed converts reclassifierTyped innerInversion _reclassifierIH =>
      obtain ⟨elementType, headTyped, tailTyped, convInner⟩ := innerInversion subjectShape
      exact ⟨elementType, headTyped, tailTyped, convInner.trans converts⟩
  | ofGrown hostTyped =>
      rw [subjectShape] at hostTyped
      refine absurd ?_ (fun contra => contra)
      apply hostTyped.cellHasNoTypingWhenRootGenericallyExcluded <;>
        (first | (intro contra; cases contra) | rfl)
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premise =>
      have headEq : generator = _ := congrArg RawTerm.rootGenerator subjectShape
      subst headEq
      exact absurd isFormationRule (by intro tableHit; cases tableHit)
  | intro ctx generator rule args params level0 level1 flag isIntro sideHolds premisesHold =>
      -- The unified introducer arm: only the `gen_listCons` row produces a `listCons`-headed cell.
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
      -- ★ listCons — the SURVIVOR.  Destructure args (`[0, 0]`) + params (`[0]`), recover head + tail from
      -- `subjectShape`, surface both premises; the output type IS `List(A)`, so the Conv is `refl`.
      · match args, params with
        | .childCons _armHead (.childCons _armTail .childNil), .childCons _elementType .childNil =>
          rcases subjectShape with ⟨⟩
          exact ⟨_, premisesHold _ (List.Mem.head _),
            premisesHold _ (List.Mem.tail _ (List.Mem.head _)), Conv.refl _⟩
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
      -- pair
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
      -- refl
      · exact absurd ((introMemberCellRootGenerator isIntroUnwrapped args).symm.trans
          (congrArg RawTerm.rootGenerator subjectShape)) (by intro headEq; cases headEq)
  | elim ctx generator rule args params level0 level1 flag isElim premisesHold =>
      -- The unified eliminator arm: no eliminator row produces a `listCons`-headed cell.
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      have headEq : generator = Generator.gen_listCons :=
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
  -- `app` is the ONE non-self-certifying elim row (see `appElimRule`), so the builder needs only the
  -- function + argument premises — the output formedness is NOT a table obligation (it is discharged in
  -- `classifierIsType` where `WfContextUnion` lives).  The level/flag args are immaterial (the row's
  -- 2-entry obligation list ignores them).
  refine HasTypeUnion.elim context .gen_app appElimRule
    (.childCons functionTerm (.childCons argument .childNil))
    (.childCons domain (.childCons codomain .childNil))
    LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact functionTyped
  | tail _ hmem => cases hmem with
    | head => exact argumentTyped
    | tail _ hmem => cases hmem

/-! ## (1) The unconditional branch-selection ι subject-reduction theorems -/

/-- **boolElim on `boolTrue` selects the then-branch, typed (DEPENDENT).**  A union-typed `boolElim` on
`boolTrue` ι-steps to the then-branch (`IotaHeadStep.iotaBoolTrue.toStep`).  The then-branch is union-typed at
its DEPENDENT natural type `subst0 motive boolTrueCell` (= the eliminator's output when the scrutinee is
`boolTrue`), which the inversion's conversion leg relates to the ambient classifier.  The reduct-at-canonical
+ conversion shape feeds the `∃ C', reduct : C' ∧ Conv C' classifier` SR-certificate directly (the
dependent twin of the `app`-β `subst0 codomain arg` discipline). -/
theorem unionSubjectReductionBoolElimTrue {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {thenBranch elseBranch classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (boolElimCell motive boolTrueCell thenBranch elseBranch) classifier) :
    Step (boolElimCell motive boolTrueCell thenBranch elseBranch) thenBranch ∧
    HasTypeUnion profile context thenBranch (RawTerm.subst0 motive boolTrueCell) ∧
    Conv (RawTerm.subst0 motive boolTrueCell) classifier := by
  obtain ⟨_scrutineeTyped, thenBranchTyped, _elseBranchTyped, outputConv⟩ := typed.invertAtBoolElimHead rfl
  exact ⟨IotaHeadStep.iotaBoolTrue.toStep, thenBranchTyped, outputConv⟩

/-- **boolElim on `boolFalse` selects the else-branch, typed (DEPENDENT).**  Symmetric to the true case:
the else-branch is at `subst0 motive boolFalseCell`, with the conversion leg to the ambient classifier. -/
theorem unionSubjectReductionBoolElimFalse {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {thenBranch elseBranch classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (boolElimCell motive boolFalseCell thenBranch elseBranch) classifier) :
    Step (boolElimCell motive boolFalseCell thenBranch elseBranch) elseBranch ∧
    HasTypeUnion profile context elseBranch (RawTerm.subst0 motive boolFalseCell) ∧
    Conv (RawTerm.subst0 motive boolFalseCell) classifier := by
  obtain ⟨_scrutineeTyped, _thenBranchTyped, elseBranchTyped, outputConv⟩ := typed.invertAtBoolElimHead rfl
  exact ⟨IotaHeadStep.iotaBoolFalse.toStep, elseBranchTyped, outputConv⟩

/-- **natElim on `natZero` selects the zero-branch, typed (DEPENDENT).**  Like `boolElim` on `boolTrue`:
the zero-branch is at `subst0 motive natZeroCell` (the dependent base classifier), with the conversion leg to
the ambient classifier (`subst0 motive natZeroCell` IS the dependent output at the `natZero` head, so the
inversion supplies `Conv (subst0 motive natZeroCell) classifier`). -/
theorem unionSubjectReductionNatElimZero {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (natElimCell motive zeroBranch stepBranch natZeroCell) classifier) :
    Step (natElimCell motive zeroBranch stepBranch natZeroCell) zeroBranch ∧
    HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell) ∧
    Conv (RawTerm.subst0 motive natZeroCell) classifier := by
  obtain ⟨_scrutineeTyped, zeroBranchTyped, outputConv⟩ := typed.invertAtNatElimHead rfl
  exact ⟨IotaHeadStep.iotaNatElimZero.toStep, zeroBranchTyped, outputConv⟩

/-- **natRec on `natZero` selects the zero-branch, typed (DEPENDENT).**  The dependent-recursor twin. -/
theorem unionSubjectReductionNatRecZero {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (natRecCell motive zeroBranch stepBranch natZeroCell) classifier) :
    Step (natRecCell motive zeroBranch stepBranch natZeroCell) zeroBranch ∧
    HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell) ∧
    Conv (RawTerm.subst0 motive natZeroCell) classifier := by
  obtain ⟨_scrutineeTyped, zeroBranchTyped, outputConv⟩ := typed.invertAtNatRecHead rfl
  exact ⟨IotaHeadStep.iotaNatRecZero.toStep, zeroBranchTyped, outputConv⟩

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
    convPinned, _resultLevel, _resultFlag, _pinnedFormed⟩ := typed.invertAtListElimHead rfl
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
  -- DEPENDENT: the none branch is the nullary reduct, typed DIRECTLY at the eliminator's none output
  -- `subst0 motive optionNoneCell` (the bool-true template — no `app`, no codomain reshape), which the
  -- inversion's output-conversion leg `convPinned` relates to the ambient classifier.
  obtain ⟨_elementType, _scrutineeTyped, noneBranchTyped, _someBranchTyped,
    convPinned, _resultLevel, _resultFlag, _motiveFormed⟩ := typed.invertAtOptionMatchHead rfl
  exact ⟨IotaHeadStep.iotaOptionMatchNone.toStep, _, noneBranchTyped, convPinned⟩

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

/-! ## (2) The substituting-ι subject-reduction theorems (the recursive succ branch — W4 transport shipped)

These re-expose the SHIPPED `natElimSuccIotaComputesTypedInUnion` / `natRecSuccIotaComputesTypedInUnion`
(NATIVE-37 part b) under the subject-reduction name.  The recursive-call substituent is
union-but-not-host-typed, so the reduct transport needs the union-substituent two-binder substitution —
now SHIPPED as `HasTypeUnion.substPairNonDependentUnionImages`.  These rows feed it the UNCONDITIONAL
transport `unionSubstPairTransports` (the cumulative former closes through `unionCumulativeFormerCloses`,
wave U3), so the natElim·natRec succ subject-reduction rows are unconditional. -/

/-- **natElim on `natSucc` substitutes the recursive call, typed (UNCONDITIONAL, DEPENDENT).**  Cites the
shipped dependent `natElimSuccIotaComputesTypedInUnion`: given the motive union-typed at a universe under
`Nat`, the predecessor at `Nat`, the zero branch at `subst0 motive natZeroCell`, and the step branch at the
dependent succ-branch type under the two binders, the two-binder transport (fed via the unconditional
`unionSubstPairTransports`) types the succ-ι reduct at the dependent output `subst0 motive (natSucc pred)`. -/
theorem unionSubjectReductionNatElimSucc {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope)
    (resultLevel : LevelExpr) (resultFlag : UniverseFlag)
    (motiveFormed : HasTypeUnion profile (context.cons natTypeCell) motive
      (universeCodeCell resultLevel resultFlag))
    (predecessorTyped : HasTypeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell))
    (branchTyped : HasTypeUnion profile
      ((context.cons natTypeCell).cons motive)
      succBranch (natElimDependentSuccBranchType motive)) :
    Step (natElimCell motive zeroBranch succBranch (natSuccCell predecessor))
        (natElimSuccContractum motive zeroBranch succBranch predecessor) ∧
    HasTypeUnion profile context
      (natElimSuccContractum motive zeroBranch succBranch predecessor)
      (RawTerm.subst0 motive (natSuccCell predecessor)) :=
  natElimSuccIotaComputesTypedInUnion context motive zeroBranch succBranch predecessor
    resultLevel resultFlag motiveFormed predecessorTyped zeroBranchTyped branchTyped
    (unionSubstPairTransports context motive)

/-- **natRec on `natSucc` substitutes the recursive call, typed (UNCONDITIONAL, DEPENDENT).**  The
dependent-recursor twin; cites the shipped dependent `natRecSuccIotaComputesTypedInUnion`, with the two-binder
transport fed via the unconditional `unionSubstPairTransports`. -/
theorem unionSubjectReductionNatRecSucc {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (zeroBranch : RawTerm scope)
    (succBranch : RawTerm (scope + 2)) (predecessor : RawTerm scope)
    (resultLevel : LevelExpr) (resultFlag : UniverseFlag)
    (motiveFormed : HasTypeUnion profile (context.cons natTypeCell) motive
      (universeCodeCell resultLevel resultFlag))
    (predecessorTyped : HasTypeUnion profile context predecessor natTypeCell)
    (zeroBranchTyped : HasTypeUnion profile context zeroBranch (RawTerm.subst0 motive natZeroCell))
    (branchTyped : HasTypeUnion profile
      ((context.cons natTypeCell).cons motive)
      succBranch (natElimDependentSuccBranchType motive)) :
    Step (natRecCell motive zeroBranch succBranch (natSuccCell predecessor))
        (natRecSuccContractum motive zeroBranch succBranch predecessor) ∧
    HasTypeUnion profile context
      (natRecSuccContractum motive zeroBranch succBranch predecessor)
      (RawTerm.subst0 motive (natSuccCell predecessor)) :=
  natRecSuccIotaComputesTypedInUnion context motive zeroBranch succBranch predecessor
    resultLevel resultFlag motiveFormed predecessorTyped zeroBranchTyped branchTyped
    (unionSubstPairTransports context motive)

/-! ## (2b) The app-chain ι + β subject-reduction theorems (the six TYTAB-2 rows)

Two regimes:

  * **App-chain value-selectors (option-some / either-inl / either-inr / list-cons) — GENUINE EXCEPT THE
    RECLASSIFICATION RESIDUAL.**  The ι reduct APPLIES the selected handler to the constructor payload —
    `optionMatch(.., some v) ↝ app(someBranch, v)` etc. — building an `app` cell (no binder descent).  These
    four rows now take the REDEX TYPING as their SOLE typing input: the eliminator-head inversion DERIVES the
    handler at its Π handler type and the scrutinee at the constructor's data type, the data-constructor
    introducer-head inversion (`invertAtOptionSomeHead` / `invertAtEitherInlHead` / `invertAtEitherInrHead` /
    `invertAtListConsHead`, shipped above) DERIVES the payload at its own type with the element `Conv` (via
    `optionCode_inj` / `eitherCode_inj` / `listCode_inj`).  The reduct is `unionAppCellTyped` (output collapsed
    by `subst0_weaken`) fed the DERIVED handler + the payload RECLASSIFIED across the element `Conv` by the
    `UnionElementReclassifies` residual — the LONE surviving hypothesis (the no-validity / type-Conv-closure
    gap, the same wall the host `piElimUpToClassifierConv` factors out).  The list-cons step both selects AND
    recurses, threading the recursive `listElim` call (built through the union's own `elim` arm via
    `listElimRecursiveCallUnionTyped`, fed the DERIVED nil/cons branches) into the curried handler app-chain.

  * **β + endpoint-β (the genuine 1-binder substitutions) — UNCONDITIONAL.**  `app(lam(_, body),
    arg) ↝ subst0 body arg` and the path twin `pathApp(pathLam(body), endpoint) ↝ subst0 body endpoint`
    substitute the argument INTO the body binder.  As with the succ arms, the substituent is union-but-not-host
    typed; the union-substituent single-substitution is SHIPPED as `HasTypeUnion.subst0WithUnionImage`, and
    its cumulative-former arm closes through the theorem `unionCumulativeFormerCloses` (wave U3 — the five
    cumulative type-codes are now `formationRuleOf` rows), so these rows hold with NO extra hypothesis. -/

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

/-- **The `UnionSubst0Transports` shape, UNCONDITIONAL.**  The 1-binder transport is an instance of the
shipped `HasTypeUnion.subst0WithUnionImage` (the union-substituent single-substitution lemma):
substituting a UNION-typed argument into a union body under one binder preserves union typing.  The β /
endpoint-β rows therefore hold unconditionally — the cumulative former closes through
`unionCumulativeFormerCloses` (wave U3). -/
theorem unionSubst0Transports {profile : PolyProfile}
    {scope : Nat} (context : TypingContext profile scope) (domain : RawTerm scope) :
    UnionSubst0Transports profile context domain :=
  fun body codomain argument bodyTyped argumentTyped =>
    HasTypeUnion.subst0WithUnionImage argument bodyTyped argumentTyped

/-- **The union element-reclassification residual for an app-chain ι redex.**  Given a value union-typed at
its OWN payload type and that payload type `Conv`-equal to the eliminator-surfaced element type, the value
reclassifies to the element type.  This is the SOLE genuinely-missing ingredient of the select-then-apply ι
rows AFTER the two now-shipped inversions (the eliminator-head inversion surfaces the handler at the Π
handler type, the introducer-head inversion surfaces the payload at its own type with the element `Conv`):
the union `conv` arm reclassifies only WITH a universe witness for the element type, which neither inversion
surfaces (the union ships no unconditional classifier validity / `type-Conv-closure`, the same wall the host
`piElimUpToClassifierConv` factors out).  So it is the residual the option-some / either-inl/inr discharge
consumes — the app-chain twin of `UnionSubst0Transports`; it dissolves at the conv-closure work
(NATIVE-46 / VAL-2). -/
abbrev UnionElementReclassifies (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) : Prop :=
  ∀ (value payloadType elementType : RawTerm scope),
    HasTypeUnion profile context value payloadType →
      Conv payloadType elementType →
      HasTypeUnion profile context value elementType

/-- **★ Reclassify a value along a Conv whose TARGET is a known union type (TYTAB-2 W5).**  The union
`conv` arm reclassifies a value only WITH a universe witness for the target classifier; supplied that
witness (`UnionClassifierIsType` of the target type), a value union-typed at `sourceType` reclassifies to a
`Conv`-equal `targetType`.  This packages the `conv` arm as a forward reclassification — the ingredient that
discharges the former `UnionElementReclassifies` oracle on the four select-then-apply ι rows: each row gets
the target (element) type's universe witness by inverting the scrutinee's data-code validity via the
now-unconditional `HasTypeUnion.classifierIsType` (over `WfContextUnion`) plus the element-leg head
inversions (`invertAtOptionCodeHeadElement` / `invertAtListCodeHeadElement` /
`eitherComponents_ofValidity`). -/
theorem HasTypeUnion.reclassifyToType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {value sourceType targetType : RawTerm scope}
    (valueTyped : HasTypeUnion profile context value sourceType)
    (converts : Conv sourceType targetType)
    (targetIsType : UnionClassifierIsType profile context targetType) :
    HasTypeUnion profile context value targetType := by
  obtain ⟨levelExpr, flag, targetTyped⟩ := targetIsType
  exact HasTypeUnion.conv levelExpr flag valueTyped converts targetTyped

/-- **optionMatch on `optionSome` applies the Some handler, typed (UNCONDITIONAL over `WfContextUnion`).**
`optionMatch(motive, noneBranch, someBranch, some(v))` ι-steps to `app(someBranch, v)`
(`IotaHeadStep.iotaOptionMatchSome.toStep`).  GENUINE except the lone reclassification residual: the redex
typing is the SOLE typing input.  The eliminator-head inversion (`invertAtOptionMatchHead`) DERIVES the Some
handler at `A → C` and the scrutinee `some(v) : option(A)`; the introducer-head inversion
(`invertAtOptionSomeHead`) DERIVES `v : A'` with `Conv (option A') (option A)`, whence `Conv A' A`
(`optionCode_inj`).  The reduct `app(someBranch, v)` is then `unionAppCellTyped` fed the handler and the
value reclassified `A' → A` by the `UnionElementReclassifies` residual (the output `subst0 (weaken C) v`
collapses to `C` by `subst0_weaken`), Conv-equal to the ambient classifier.  Conditional ONLY in the
reclassification residual — the handler + payload typings are now DERIVED from the redex, not premised. -/
theorem unionSubjectReductionOptionMatchSome {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {noneBranch someBranch value classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (optionMatchCell motive noneBranch someBranch (optionSomeCell value)) classifier)
    (wellFormed : WfContextUnion context) :
    Step (optionMatchCell motive noneBranch someBranch (optionSomeCell value))
        (appCell someBranch value) ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context (appCell someBranch value) pinnedClassifier ∧
      Conv pinnedClassifier classifier := by
  obtain ⟨elementType, scrutineeTyped, _noneTyped, someBranchTyped, convPinned,
    _resultLevel, _resultFlag, _motiveFormed⟩ := typed.invertAtOptionMatchHead rfl
  obtain ⟨payloadType, valueTyped, convOption⟩ := scrutineeTyped.invertAtOptionSomeHead rfl
  -- The element type's universe witness: invert the scrutinee's `option(elementType)` validity (the
  -- now-unconditional classifier validity over `WfContextUnion`) at the option-code element leg.
  obtain ⟨_optionLevel, _optionFlag, optionTyped⟩ := scrutineeTyped.classifierIsType wellFormed
  have elementIsType : UnionClassifierIsType profile context elementType :=
    HasTypeUnion.invertAtOptionCodeHeadElement optionTyped rfl
  have valueAtElement : HasTypeUnion profile context value elementType :=
    HasTypeUnion.reclassifyToType valueTyped (Conv.optionCode_inj convOption) elementIsType
  -- DEPENDENT: the reduct `app someBranch value` is typed at the some-branch codomain at `value`, which the
  -- some-ι type-preservation pin carries to `subst0 motive (some value)` — exactly the eliminator's output
  -- type, which `convPinned` relates to the ambient classifier.
  refine ⟨IotaHeadStep.iotaOptionMatchSome.toStep, _, ?_, convPinned⟩
  have applied := unionAppCellTyped someBranch value elementType
    (optionMatchDependentSomeBranchCodomain motive) someBranchTyped valueAtElement
  rwa [subst0_optionMatchDependentSomeBranchCodomain_someIota] at applied

/-- **eitherMatch on `eitherInl` applies the left handler, typed (conditional, Conv-modulo).**
`eitherMatch(motive, leftBranch, rightBranch, inl(v))` ι-steps to `app(leftBranch, v)`
(`IotaHeadStep.iotaEitherMatchInl.toStep`).  GENUINE except the lone reclassification residual: the redex
typing is the SOLE typing input.  `invertAtEitherMatchHead` DERIVES the left handler at `A → C` and the
scrutinee `inl(v) : either(A, B)`; `invertAtEitherInlHead` DERIVES `v : A'` with `Conv (either A' B')
(either A B)`, whence `Conv A' A` (`eitherCode_inj`, first leg).  The reduct is `unionAppCellTyped` fed the
handler and the value reclassified `A' → A`, Conv-equal to the classifier. -/
theorem unionSubjectReductionEitherMatchInl {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {leftBranch rightBranch value classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (eitherMatchCell motive leftBranch rightBranch (eitherInlCell value)) classifier)
    (wellFormed : WfContextUnion context) :
    Step (eitherMatchCell motive leftBranch rightBranch (eitherInlCell value))
        (appCell leftBranch value) ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context (appCell leftBranch value) pinnedClassifier ∧
      Conv pinnedClassifier classifier := by
  obtain ⟨leftType, rightType, scrutineeTyped, leftBranchTyped, _rightTyped,
    convPinned, _resultLevel, _resultFlag, _motiveFormed⟩ := typed.invertAtEitherMatchHead rfl
  obtain ⟨payloadLeftType, _payloadRightType, valueTyped, convEither⟩ :=
    scrutineeTyped.invertAtEitherInlHead rfl
  have convPayloadLeft : Conv payloadLeftType leftType := (Conv.eitherCode_inj convEither).1
  -- The left type's universe witness: invert the scrutinee's `either(leftType, rightType)` validity.
  have leftIsType : UnionClassifierIsType profile context leftType :=
    (UnionClassifierIsType.eitherComponents_ofValidity context leftType rightType
      (scrutineeTyped.classifierIsType wellFormed)).1
  have valueAtLeft : HasTypeUnion profile context value leftType :=
    HasTypeUnion.reclassifyToType valueTyped convPayloadLeft leftIsType
  -- DEPENDENT: the reduct `app leftBranch value` is typed at the inl-branch codomain at `value`, which the
  -- inl-ι type-preservation pin carries to `subst0 motive (inl value)` — exactly the eliminator's output
  -- type, which `convPinned` relates to the ambient classifier.
  refine ⟨IotaHeadStep.iotaEitherMatchInl.toStep, _, ?_, convPinned⟩
  have applied := unionAppCellTyped leftBranch value leftType
    (eitherMatchDependentInlBranchCodomain motive) leftBranchTyped valueAtLeft
  rwa [subst0_eitherMatchDependentInlBranchCodomain_inlIota] at applied

/-- **eitherMatch on `eitherInr` applies the right handler, typed (conditional, Conv-modulo).**  The
right-injection twin: `eitherMatch(.., inr(v)) ↝ app(rightBranch, v)`
(`IotaHeadStep.iotaEitherMatchInr.toStep`).  GENUINE except the lone reclassification residual: the redex
typing is the SOLE typing input.  `invertAtEitherMatchHead` DERIVES the right handler at `B → C` and the
scrutinee `inr(v) : either(A, B)`; `invertAtEitherInrHead` DERIVES `v : B'` with `Conv (either A' B')
(either A B)`, whence `Conv B' B` (`eitherCode_inj`, second leg).  The reduct is `unionAppCellTyped` fed the
right handler and the value reclassified `B' → B`, Conv-equal to the classifier. -/
theorem unionSubjectReductionEitherMatchInr {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {leftBranch rightBranch value classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (eitherMatchCell motive leftBranch rightBranch (eitherInrCell value)) classifier)
    (wellFormed : WfContextUnion context) :
    Step (eitherMatchCell motive leftBranch rightBranch (eitherInrCell value))
        (appCell rightBranch value) ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context (appCell rightBranch value) pinnedClassifier ∧
      Conv pinnedClassifier classifier := by
  obtain ⟨leftType, rightType, scrutineeTyped, _leftTyped, rightBranchTyped,
    convPinned, _resultLevel, _resultFlag, _motiveFormed⟩ := typed.invertAtEitherMatchHead rfl
  obtain ⟨_payloadLeftType, payloadRightType, valueTyped, convEither⟩ :=
    scrutineeTyped.invertAtEitherInrHead rfl
  have convPayloadRight : Conv payloadRightType rightType := (Conv.eitherCode_inj convEither).2
  -- The right type's universe witness: invert the scrutinee's `either(leftType, rightType)` validity.
  have rightIsType : UnionClassifierIsType profile context rightType :=
    (UnionClassifierIsType.eitherComponents_ofValidity context leftType rightType
      (scrutineeTyped.classifierIsType wellFormed)).2
  have valueAtRight : HasTypeUnion profile context value rightType :=
    HasTypeUnion.reclassifyToType valueTyped convPayloadRight rightIsType
  -- DEPENDENT: the reduct `app rightBranch value` is typed at the inr-branch codomain at `value`, carried by
  -- the inr-ι type-preservation pin to `subst0 motive (inr value)` (the output), `convPinned`-equal to the
  -- ambient classifier.
  refine ⟨IotaHeadStep.iotaEitherMatchInr.toStep, _, ?_, convPinned⟩
  have applied := unionAppCellTyped rightBranch value rightType
    (eitherMatchDependentInrBranchCodomain motive) rightBranchTyped valueAtRight
  rwa [subst0_eitherMatchDependentInrBranchCodomain_inrIota] at applied

/-- **★ β substitutes the argument into the body, typed (UNCONDITIONAL).**  A union-typed
`app(lam(domain, body), arg)` ι-steps to `subst0 body arg` (`HeadStep.beta` lifted through `Step.beta`);
given the body union-typed at the codomain under the domain binder and the argument union-typed at the
domain, the union-substituent single-substitution `HasTypeUnion.subst0WithUnionImage` types the reduct at
`subst0 codomain arg`.  No hypotheses beyond the body / argument typings — the cumulative former closes
through `unionCumulativeFormerCloses` (wave U3), so β-subject-reduction is unconditional. -/
theorem unionSubjectReductionBeta {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (domain : RawTerm scope) (body codomain : RawTerm (scope + 1)) (argument : RawTerm scope)
    (bodyTyped : HasTypeUnion profile (context.cons domain) body codomain)
    (argumentTyped : HasTypeUnion profile context argument domain) :
    Step (appCell (lamCell domain body) argument) (RawTerm.subst0 body argument) ∧
    HasTypeUnion profile context
      (RawTerm.subst0 body argument) (RawTerm.subst0 codomain argument) :=
  ⟨Step.beta,
    HasTypeUnion.subst0WithUnionImage argument bodyTyped argumentTyped⟩

/-- **★ endpoint-β substitutes the interval endpoint into the path body, typed (UNCONDITIONAL).**  A
union-typed `pathApp(pathLam(body), endpoint)` ι-steps to `subst0 body endpoint` (`Step.pathBeta`); given
the body union-typed at the carrier under the interval binder and the endpoint union-typed at the interval
type, the union-substituent single-substitution `HasTypeUnion.subst0WithUnionImage` types the reduct at
`subst0 carrier endpoint`.  The path twin of β — unconditional (wave U3). -/
theorem unionSubjectReductionEndpointBeta {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (body carrier : RawTerm (scope + 1)) (endpoint : RawTerm scope)
    (bodyTyped : HasTypeUnion profile (context.cons intervalTypeCell) body carrier)
    (endpointTyped : HasTypeUnion profile context endpoint intervalTypeCell) :
    Step (pathAppCell (pathLamCell body) endpoint) (RawTerm.subst0 body endpoint) ∧
    HasTypeUnion profile context
      (RawTerm.subst0 body endpoint) (RawTerm.subst0 carrier endpoint) :=
  ⟨stepOverTable_iff_step.mp (StepTable.pathBetaFires body endpoint),
    HasTypeUnion.subst0WithUnionImage endpoint bodyTyped endpointTyped⟩

/-- The recursive call `listElim(motive, tail, nilBranch, consBranch)` is union-typed at `resultType` — by
the union's own `elim` arm at the `gen_listElim` row, given the tail union-typed at `List(elementType)`,
the nil branch at `resultType`, and the cons branch at the curried step type.  The list twin of
`natElimRecursiveCallUnionTyped`: the recursion loop closes through the union's listElim elim arm. -/
theorem listElimRecursiveCallUnionTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (tail nilBranch consBranch elementType resultType : RawTerm scope)
    {resultLevel : LevelExpr} {resultFlag : UniverseFlag}
    (tailTyped : HasTypeUnion profile context tail (listTypeCell elementType))
    (nilBranchTyped : HasTypeUnion profile context nilBranch resultType)
    (consBranchTyped : HasTypeUnion profile context consBranch
      (listStepFunctionType elementType resultType))
    (resultTypeFormed : HasTypeUnion profile context resultType
      (universeCodeCell resultLevel resultFlag)) :
    HasTypeUnion profile context
      (listElimCell motive tail nilBranch consBranch) resultType := by
  refine HasTypeUnion.elim context .gen_listElim listElimRule
    (.childCons motive (.childCons tail (.childCons nilBranch (.childCons consBranch .childNil))))
    (.childCons elementType (.childCons resultType .childNil)) resultLevel resultLevel resultFlag rfl ?_
  intro obligation hmem
  cases hmem with
  | head => exact tailTyped
  | tail _ hmem => cases hmem with
    | head => exact nilBranchTyped
    | tail _ hmem => cases hmem with
      | head => exact consBranchTyped
      | tail _ hmem => cases hmem with
        | head => exact resultTypeFormed
        | tail _ hmem => cases hmem

/-- **listElim on `listCons` applies the cons handler and recurses, typed (conditional, Conv-modulo).**
`listElim(motive, cons(head, tail), nilBranch, consBranch)` ι-steps to
`app(app(app(consBranch, head), tail), listElim(motive, tail, nilBranch, consBranch))`
(`IotaHeadStep.iotaListElimCons.toStep`) — the curried cons handler is applied to the head, the tail, and the
recursive call on the tail.  GENUINE except the lone reclassification residual: the redex typing is the SOLE
typing input.  `invertAtListElimHead` DERIVES the cons branch at the curried step type
`A → List(A) → C → C`, the nil branch at `C`, and the scrutinee `cons(head, tail) : List(A)`;
`invertAtListConsHead` DERIVES `head : A'` and `tail : List(A')` with `Conv (List A') (List A)`, whence
`Conv A' A` (`listCode_inj`).  Head + tail are reclassified `A' → A` / `List A' → List A` by the
`UnionElementReclassifies` residual (the SAME residual the match rows consume); then each of the three
applications collapses its non-dependent codomain by `subst0_weaken`, and the recursive `listElim` call is
built through the union's own listElim elim arm (`listElimRecursiveCallUnionTyped`, the list twin of the nat
recursion-loop close) fed the DERIVED nil/cons branches.  Carries NO substituent transport residual (pure
app-chain, no binder descent); conditional ONLY in the reclassification residual — every branch typing is
now DERIVED from the redex.  The recursive twin of the natElim-succ arm. -/
theorem unionSubjectReductionListElimCons {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {headValue tailList nilBranch consBranch classifier : RawTerm scope}
    (typed : HasTypeUnion profile context
      (listElimCell motive (listConsCell headValue tailList) nilBranch consBranch) classifier)
    (wellFormed : WfContextUnion context) :
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
  obtain ⟨elementType, pinnedClassifier, scrutineeTyped, nilBranchTyped, consBranchTyped,
    convPinned, resultLevel, resultFlag, pinnedFormed⟩ := typed.invertAtListElimHead rfl
  obtain ⟨payloadElement, headTyped, tailAtPayload, convListElement⟩ :=
    scrutineeTyped.invertAtListConsHead rfl
  have convPayloadElement : Conv payloadElement elementType := Conv.listCode_inj convListElement
  -- The element type's universe witness: invert the scrutinee's `List(elementType)` validity (the
  -- now-unconditional classifier validity over `WfContextUnion`).  The whole `List(elementType)` validity
  -- ALSO serves as the tail's target witness directly (the tail is reclassified at `List(elementType)`).
  have listElementIsType : UnionClassifierIsType profile context (listTypeCell elementType) :=
    scrutineeTyped.classifierIsType wellFormed
  have elementIsType : UnionClassifierIsType profile context elementType := by
    obtain ⟨_listLevel, _listFlag, listTyped⟩ := listElementIsType
    exact HasTypeUnion.invertAtListCodeHeadElement listTyped rfl
  have headAtElement : HasTypeUnion profile context headValue elementType :=
    HasTypeUnion.reclassifyToType headTyped convPayloadElement elementIsType
  have tailAtElement : HasTypeUnion profile context tailList (listTypeCell elementType) :=
    HasTypeUnion.reclassifyToType tailAtPayload convListElement listElementIsType
  refine ⟨IotaHeadStep.iotaListElimCons.toStep, pinnedClassifier, ?_, convPinned⟩
  -- The cons branch is `A → (List A → (C → C))` (every codomain weakened past its binder).  Apply to the
  -- head (collapse `subst0_weaken` to `List A → (C → C)`), to the tail (collapse to `C → C`), then to the
  -- recursive call (collapse to `C`).  `app` is non-self-certifying, so each application needs only its
  -- function + argument; only the recursive `listElim` call needs the result-type formedness `pinnedFormed`.
  have appliedHead := unionAppCellTyped consBranch headValue elementType
    (RawTerm.weaken (piTyCodeCell (listTypeCell elementType)
      (RawTerm.weaken (piTyCodeCell pinnedClassifier (RawTerm.weaken pinnedClassifier)))))
    consBranchTyped headAtElement
  rw [RawTerm.subst0_weaken] at appliedHead
  have appliedTail := unionAppCellTyped (appCell consBranch headValue) tailList
    (listTypeCell elementType)
    (RawTerm.weaken (piTyCodeCell pinnedClassifier (RawTerm.weaken pinnedClassifier)))
    appliedHead tailAtElement
  rw [RawTerm.subst0_weaken] at appliedTail
  have recursiveCall := listElimRecursiveCallUnionTyped context motive tailList nilBranch consBranch
    elementType pinnedClassifier tailAtElement nilBranchTyped consBranchTyped pinnedFormed
  have appliedRec := unionAppCellTyped (appCell (appCell consBranch headValue) tailList)
    (listElimCell motive tailList nilBranch consBranch) pinnedClassifier (RawTerm.weaken pinnedClassifier)
    appliedTail recursiveCall
  rwa [RawTerm.subst0_weaken] at appliedRec

/-! ## (3) Coverage record + witness

The branch-selection arms are unconditional; the two succ arms carry their explicit hypotheses.  An
inhabitant certifies the subject-reduction substrate is exercised (constructed, not just declared). -/

/-- **The root-redex subject-reduction coverage record.**  Each field is a distinct live root-redex
subject-reduction property over the native union: the seven unconditional branch-selection / projection
families (here: the seven branch-selection ι) and the two conditional recursive-succ families. -/
structure NativeUnionRootRedexSubjectReductionCoverage (profile : PolyProfile) : Prop where
  /-- boolElim-true reduct is typed (Conv-modulo, DEPENDENT: the then-branch carries the motive over
  `boolTrue` — `subst0 motive boolTrueCell` — convertible to the ascribed classifier). -/
  boolElimTrueReductTyped : ∀ {scope : Nat} {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {thenBranch elseBranch classifier : RawTerm scope},
    HasTypeUnion profile context
      (boolElimCell motive boolTrueCell thenBranch elseBranch) classifier →
    Step (boolElimCell motive boolTrueCell thenBranch elseBranch) thenBranch ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context thenBranch pinnedClassifier ∧
      Conv pinnedClassifier classifier
  /-- boolElim-false reduct is typed (Conv-modulo, DEPENDENT: the else-branch carries the motive over
  `boolFalse` — `subst0 motive boolFalseCell` — convertible to the ascribed classifier). -/
  boolElimFalseReductTyped : ∀ {scope : Nat} {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {thenBranch elseBranch classifier : RawTerm scope},
    HasTypeUnion profile context
      (boolElimCell motive boolFalseCell thenBranch elseBranch) classifier →
    Step (boolElimCell motive boolFalseCell thenBranch elseBranch) elseBranch ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context elseBranch pinnedClassifier ∧
      Conv pinnedClassifier classifier
  /-- natElim-zero reduct is typed (Conv-modulo: the zero branch carries its own dependent base classifier
  `subst0 motive natZeroCell`, convertible to the ambient classifier — exactly the `boolElim`-true shape). -/
  natElimZeroReductTyped : ∀ {scope : Nat} {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {classifier : RawTerm scope},
    HasTypeUnion profile context
      (natElimCell motive zeroBranch stepBranch natZeroCell) classifier →
    Step (natElimCell motive zeroBranch stepBranch natZeroCell) zeroBranch ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context zeroBranch pinnedClassifier ∧
      Conv pinnedClassifier classifier
  /-- natRec-zero reduct is typed (Conv-modulo: the dependent-recursor twin). -/
  natRecZeroReductTyped : ∀ {scope : Nat} {context : TypingContext profile scope}
    {motive : RawTerm (scope + 1)} {zeroBranch : RawTerm scope}
    {stepBranch : RawTerm (scope + 2)} {classifier : RawTerm scope},
    HasTypeUnion profile context
      (natRecCell motive zeroBranch stepBranch natZeroCell) classifier →
    Step (natRecCell motive zeroBranch stepBranch natZeroCell) zeroBranch ∧
    ∃ pinnedClassifier : RawTerm scope,
      HasTypeUnion profile context zeroBranch pinnedClassifier ∧
      Conv pinnedClassifier classifier
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
  boolElimTrueReductTyped := fun typed =>
    let reduct := unionSubjectReductionBoolElimTrue typed
    ⟨reduct.1, _, reduct.2.1, reduct.2.2⟩
  boolElimFalseReductTyped := fun typed =>
    let reduct := unionSubjectReductionBoolElimFalse typed
    ⟨reduct.1, _, reduct.2.1, reduct.2.2⟩
  natElimZeroReductTyped := fun typed =>
    let reduct := unionSubjectReductionNatElimZero typed
    ⟨reduct.1, _, reduct.2.1, reduct.2.2⟩
  natRecZeroReductTyped := fun typed =>
    let reduct := unionSubjectReductionNatRecZero typed
    ⟨reduct.1, _, reduct.2.1, reduct.2.2⟩
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
              exact Or.inl ⟨_, (unionSubjectReductionBoolElimTrue typed).2.1,
                (unionSubjectReductionBoolElimTrue typed).2.2⟩
          | iotaBoolFalse =>
              exact Or.inl ⟨_, (unionSubjectReductionBoolElimFalse typed).2.1,
                (unionSubjectReductionBoolElimFalse typed).2.2⟩
      | tail _ isRow => cases isRow with
        | head =>
            cases boolFalseRowFiringToIotaHead elimPayload fires with
            | iotaBoolTrue =>
                exact Or.inl ⟨_, (unionSubjectReductionBoolElimTrue typed).2.1,
                  (unionSubjectReductionBoolElimTrue typed).2.2⟩
            | iotaBoolFalse =>
                exact Or.inl ⟨_, (unionSubjectReductionBoolElimFalse typed).2.1,
                  (unionSubjectReductionBoolElimFalse typed).2.2⟩
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
                      exact Or.inl ⟨_, (unionSubjectReductionNatElimZero typed).2.1,
                        (unionSubjectReductionNatElimZero typed).2.2⟩
                  | iotaNatElimSucc =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩))))))))
              | tail _ isRow => cases isRow with
                | head =>
                    cases natRecZeroRowFiringToIotaHead elimPayload fires with
                    | iotaNatRecZero =>
                        exact Or.inl ⟨_, (unionSubjectReductionNatRecZero typed).2.1,
                          (unionSubjectReductionNatRecZero typed).2.2⟩
                    | iotaNatRecSucc =>
                        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                          (Or.inr (Or.inr (Or.inr
                            (Or.inl ⟨_, _, _, _, rfl⟩)))))))))
                | tail _ isRow => cases isRow with
                  | head =>
                      cases natElimSuccRowFiringToIotaHead elimPayload
                          fires with
                      | iotaNatElimZero =>
                          exact Or.inl ⟨_, (unionSubjectReductionNatElimZero typed).2.1,
                            (unionSubjectReductionNatElimZero typed).2.2⟩
                      | iotaNatElimSucc =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                            (Or.inr (Or.inr (Or.inr
                              (Or.inl ⟨_, _, _, _, rfl⟩))))))))
                  | tail _ isRow => cases isRow with
                    | head =>
                        cases natRecSuccRowFiringToIotaHead elimPayload
                            fires with
                        | iotaNatRecZero =>
                            exact Or.inl ⟨_, (unionSubjectReductionNatRecZero typed).2.1,
                              (unionSubjectReductionNatRecZero typed).2.2⟩
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

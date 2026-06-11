import FX1Poly.Typed.HasTypeDescGeneralElim
import FX1Poly.Typed.HasTypeDescBaseType
import FX1Poly.Typed.HasTypeDescDataIntro
import FX1Poly.Typed.HasTypeDescTermIndexedFormer
import FX1Poly.Typed.HasTypeDescNatElim
import FX1Poly.Typed.NativeUnionRuleTables

/-! # FX1Poly/Typed/HasTypeNativeUnion — NATIVE-25: the seed unified judgment + Bridge full adequacy

THE SEQUENCING PIVOT (the ultrathink resequencing, user-approved direction): the judgment-boundary
wall is SYSTEMIC, not a pathElim quirk — recursive data constructors need data-typed arguments, data
eliminators need data-typed scrutinees, pathElim needs Bridge-typed paths, and closed
endpoints/numerals are NOT host-typable (the NATIVE-08 wall).  Every adequacy task in the wave
(NATIVE-29..35) hits the same wall.  So instead of building a throwaway bridge-fragment union here and
the real union at NATIVE-46, this file SEEDS the NATIVE-46 unified judgment now and proves the Bridge
adequacy INTO it.

## The seed design: engine embeddings + recursive native arms

  * Four EMBEDDING arms (`ofGrown` / `ofBaseType` / `ofDataIntro` / `ofTermIndexedFormer`) — premises
    are completed prior inductives, so positivity is trivial (no mutual telescope blocks, the banked
    positivity trap avoided).  They provide the base typing mass; the wave later converts each
    embedding into table-driven native arms (NATIVE-36) without disturbing this seed.
  * Two RECURSIVE native arms (`gradedBinderIntro` / `generalElim`) — the NATIVE-23/24 keystone arms
    with premises in the union ITSELF.  These provide the compositional closure that was the walls.

## What becomes typable for the FIRST TIME (the wall-falls smokes)

  * `endpointRedexNativelyTypedWhole` — the WHOLE endpoint redex `pathApp(pathLam(Type@0), 0)` typed
    in ONE derivation (intro arm + data arm composing inside one judgment; previously the path lived
    in the graded engine and the argument in the data engine with no judgment containing both).
  * `constantIntervalLambdaNativelyTyped` — `λ(x:Bool).0 : Π(x:Bool).Interval`: a λ whose BODY lives
    in the data engine.  Untypable in every prior engine (the host demands a host-typed body; `0` is
    not host-typable).

## ★ Bridge full adequacy (all 6 arms → the union)

`HasTypeDescBridge.toNativeUnion`: every Bridge derivation translates to a union typing at the SAME
subject and classifier — intervalFormation→baseType row, endpoints→data rows,
bridgeFormation→termIndexed row, pathIntro→graded intro row, pathElim→general elim row with the
RECURSIVE premises discharged by the induction hypotheses (the judgment boundary dissolves exactly as
the NATIVE-04 verdict predicted).  ONE honest exception, carried as an explicit disjunct:
`Bridge.intervalFormation` is ANY-flag while the native base-type row pins `standard` (the deliberate
DI-1b-flagpin determinism discipline) — a bare non-standard-flag interval formation has no native
image at its own flag; the disjunct records the dropped liberality AND supplies the standard-flag
native typing.  The bespoke any-flag formation was flag-AMBIGUOUS (no uniqueness); the native
strictness is the better semantics, recorded rather than papered over.

## Honest scope

  * The `conv` arm IS present (NATIVE-46, additive — the 25th arm): a union typing at `classifier`
    plus `Conv classifier reclassifier` plus a universe-code derivation for `reclassifier` reclassifies
    the subject, exactly as `HasTypeDescPi.conv` does on the grown engine.  `Conv` is a raw StepStar
    relation never mentioning typing, so the arm is strictly positive and free-subject `cases` over all
    25 arms stays propext-clean.
  * The union-wide affine-rejection statement (`pathLam(pair(var 0, var 0))` untypable in the UNION)
    needs a host-engine pathLam-head-untyped lemma not yet in `HasTypeDescPiDataHeadUntyped`; the
    graded-arm rejection is shipped (NATIVE-23); the union-wide form is pinned as wave work.
  * The reverse direction (union restricted to bridge heads → Bridge) is the per-family wave adequacy.

## NATIVE-36 scope note (appended): the new families are table-resident; the embeddings STAY

NATIVE-36 makes the NON-recursive data-eliminator families (boolElim / optionMatch / eitherMatch via
`twoBranchMatchElim`, idJ via `pathInductionElim`, fst / snd via `projectionElim`), the n-ary /
recursive data-INTRO families (natSucc / listCons / optionSome / optionNone / eitherInl / eitherInr /
pair / refl via the seven intro arms), and the listElim family (via `listElim`, discharging the batch-1
pin "listElim union residency lands with NATIVE-33") RESIDENT in `HasTypeNativeUnion` as table-driven
arms, with their native twin tables hoisted into the pre-union `NativeUnionRuleTables` (the import-cycle
hazard avoided exactly as NATIVE-32 avoided it).  The scrutinee-embedding arms the data eliminators need
(`ofOptionIntro` / `ofEitherIntro` / `ofIdIntro` / `ofPairIntro` / `ofListIntro`) are added here,
mirroring `ofNatIntro`.  The OTHER embeddings (`ofGrown` / `ofBaseType` / `ofDataIntro` /
`ofTermIndexedFormer`) STAY embeddings for now — converting them to table arms is entangled with
NATIVE-46's conv-closure restatement and is out of scope here.  The spike→union transfers
(`DataElimUnionSpike.toNativeUnion`, `DataIntroNaryUnionSpike.toNativeUnion`,
`ListElimUnionSpike.toNativeUnion`) live in separate post-union files (they import both the spike and
this union).

## Zero-axiom

Embeddings are constructor applications; the recursive arms mirror the keystone arms; the adequacy is
`induction` over the 6 Bridge arms with head-generator no-confusion refutations of the flag disjunct in
the recursive case.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! ## The native recursive-eliminator row schema (NATIVE-32 union residency of the spike's rows)

The seed union (NATIVE-25) carried the non-recursive eliminator compositions through `generalElim`.
The RECURSIVE eliminators (`natElim` / `natRec`) need a dedicated row whose scrutinee and base-branch
premises are RECURSIVE in the union itself — the exact construction the NATIVE-27 spike
(`RecursiveElimUnionSpike.recursiveElimRow`) locked as GO.  This schema mirrors the spike's
`RecursiveElimRule` field-for-field; it is defined HERE (below the union, above the inductive) so the
union arm can reference it without the spike→union import cycle.  The two Nat rows reuse the shipped
`natElimCell` / `natRecCell` cells and their succ-ι contracta. -/

/-- A native recursive-eliminator row: the inductive type code its scrutinee inhabits, the eliminator
member cell (motive, base branch, two-binder step branch, scrutinee), and the succ-ι contractum (the
step branch with the recursive call at var 0 and the predecessor at var 1).  Field-identical to the
spike's `RecursiveElimRule` — the union residency of the locked schema. -/
structure NativeRecursiveElimRule where
  /-- The inductive type code the scrutinee must inhabit (`natTypeCell` for both Nat rows). -/
  scrutineeType : (scope : Nat) → RawTerm scope
  /-- The eliminator cell: motive (one binder), base branch, step branch (two binders), scrutinee. -/
  memberCell : (scope : Nat) → RawTerm (scope + 1) → RawTerm scope → RawTerm (scope + 2) →
    RawTerm scope → RawTerm scope
  /-- The succ-ι contractum at a predecessor: the step branch with the recursive call at var 0 and
  the predecessor at var 1. -/
  succContractum : (scope : Nat) → RawTerm (scope + 1) → RawTerm scope → RawTerm (scope + 2) →
    RawTerm scope → RawTerm scope

/-- The native `gen_natElim` row. -/
def natElimNativeRecursiveRule : NativeRecursiveElimRule where
  scrutineeType := fun _ => natTypeCell
  memberCell := fun _ => natElimCell
  succContractum := fun _ => natElimSuccContractum

/-- The native `gen_natRec` row (the dependent-recursor twin — identical substrate metadata). -/
def natRecNativeRecursiveRule : NativeRecursiveElimRule where
  scrutineeType := fun _ => natTypeCell
  memberCell := fun _ => natRecCell
  succContractum := fun _ => natRecSuccContractum

/-- The native recursive-eliminator table.  `gen_listElim` does NOT join here: its cons-ι is an
app-chain (not a substitution) so it has a different row shape (NATIVE-33). -/
def nativeRecursiveElimRuleOf (generator : Generator) : Option NativeRecursiveElimRule :=
  if generator = .gen_natElim then some natElimNativeRecursiveRule
  else if generator = .gen_natRec then some natRecNativeRecursiveRule
  else none

/-- Table metadata: the native natElim row is hit (rfl on the diagonal). -/
theorem nativeRecursiveElimRuleOf_natElim :
    nativeRecursiveElimRuleOf .gen_natElim = some natElimNativeRecursiveRule := rfl

/-- Table metadata: the native natRec row is hit. -/
theorem nativeRecursiveElimRuleOf_natRec :
    nativeRecursiveElimRuleOf .gen_natRec = some natRecNativeRecursiveRule := rfl

/-- **The seed unified native judgment (the NATIVE-46 miniature).**  Four engine embeddings (the base
typing mass) + the two table-driven keystone arms with RECURSIVE premises (the compositional closure).
A subject typed here is typed BY THE NATIVE SYSTEM — table rows and their compositions — with no
judgment boundary between the families. -/
inductive HasTypeNativeUnion (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  /-- Embed the host (grown) engine: var / universe / formation / piIntro / piElim / conv. -/
  | ofGrown {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (hostTyped : HasTypeDescPi profile context subject classifier) :
      HasTypeNativeUnion profile context subject classifier
  /-- Embed the nullary base-type formation rows (bool/empty/nat/unit/interval codes). -/
  | ofBaseType {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (baseTyped : HasTypeDescBaseType profile context subject classifier) :
      HasTypeNativeUnion profile context subject classifier
  /-- Embed the nullary data-constructor rows (boolTrue/boolFalse/unit/interval endpoints). -/
  | ofDataIntro {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (dataTyped : HasTypeDescDataIntro profile context subject classifier) :
      HasTypeNativeUnion profile context subject classifier
  /-- Embed the term-indexed former rows (Id / Bridge formation). -/
  | ofTermIndexedFormer {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (formerTyped : HasTypeDescTermIndexedFormer profile context subject classifier) :
      HasTypeNativeUnion profile context subject classifier
  /-- The graded binder-introduction arm (the NATIVE-23 keystone arm with RECURSIVE premises): the
  table's usage grade is enforced, and the domain/classifier/body premises live in the UNION — so a
  body typed by ANY native family is admissible (the λ-over-data wall falls). -/
  | gradedBinderIntro {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : GradedIntroRule)
      (typeParamA : RawTerm scope) (typeParamB : RawTerm (scope + 1))
      (body : RawTerm (scope + 1))
      (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
      (isIntro : gradedIntroRuleOf generator = some rule)
      (binderGraded : gradedBinderChecks rule.binderUsage body)
      (domainFormed : rule.demandsDomainFormation = true →
        HasTypeNativeUnion profile context (rule.domainCell scope typeParamA)
          (universeCodeCell domainLevel flag))
      (classifierFormed : rule.demandsClassifierFormation = true →
        HasTypeNativeUnion profile (context.cons (rule.domainCell scope typeParamA))
          (rule.bodyClassifier scope typeParamA typeParamB)
          (universeCodeCell codomainLevel flag))
      (bodyTyped : HasTypeNativeUnion profile (context.cons (rule.domainCell scope typeParamA))
        body (rule.bodyClassifier scope typeParamA typeParamB)) :
      HasTypeNativeUnion profile context
        (rule.memberCell scope typeParamA body)
        (rule.outputType scope typeParamA typeParamB body)
  /-- The general elimination arm (the NATIVE-24 keystone arm with RECURSIVE premises): an eliminated
  child typed by ANY native family is admissible (the cross-engine elimination wall falls — the
  pathElim translation's crux discharges through THIS arm's recursion). -/
  | generalElim {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : GeneralElimRule)
      (typeParamA : RawTerm scope) (typeParamB : RawTerm (scope + 1))
      (typeParamC typeParamD : RawTerm scope)
      (eliminated argument : RawTerm scope)
      (isElim : generalElimRuleOf generator = some rule)
      (eliminatedTyped : HasTypeNativeUnion profile context eliminated
        (rule.eliminatedType scope typeParamA typeParamB typeParamC typeParamD))
      (argumentTyped : HasTypeNativeUnion profile context argument
        (rule.argumentType scope typeParamA)) :
      HasTypeNativeUnion profile context
        (rule.memberCell scope eliminated argument)
        (rule.outputType scope typeParamA typeParamB argument)
  /-- Embed the Nat value constructors (numeral scrutinees).  The sanctioned interim embedding form
  (the NATIVE-36 native-row conversion replaces it later): a numeral typed by `HasTypeDescNatIntro` is
  an admissible union subject, so a recursive eliminator's scrutinee premise has a union witness.
  Mirrors the NATIVE-27 spike's `ofNatIntro` embedding. -/
  | ofNatIntro {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (natTyped : HasTypeDescNatIntro profile context subject classifier) :
      HasTypeNativeUnion profile context subject classifier
  /-- The table-driven recursive-eliminator arm (the NATIVE-32 union residency of the spike's
  `recursiveElimRow`): the scrutinee and base-branch premises are RECURSIVE in the UNION itself — so a
  recursive call (`natElimCell` at the predecessor) is an admissible scrutinee-typed subject, closing
  the recursion loop the bespoke engine could not.  The motive stays STORED; the step branch is
  PREMISED at the two-binder context (outer binder the scrutinee's element type, inner binder the
  once-weakened recursive result) — the conv-closure churn closing the premise-shape gap, so the
  substituting succ-iota reduct typing is recoverable from the redex's own derivation. -/
  | recursiveElim {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : NativeRecursiveElimRule)
      (motive : RawTerm (scope + 1)) (baseBranch : RawTerm scope)
      (stepBranch : RawTerm (scope + 2)) (scrutinee : RawTerm scope)
      (resultType : RawTerm scope)
      (isRecursiveElim : nativeRecursiveElimRuleOf generator = some rule)
      (scrutineeTyped : HasTypeNativeUnion profile context scrutinee
        (rule.scrutineeType scope))
      (baseBranchTyped : HasTypeNativeUnion profile context baseBranch resultType)
      (stepBranchTyped : HasTypeNativeUnion profile
        ((context.cons (rule.scrutineeType scope)).cons
          (RawTerm.rename FX1Poly.Foundation.RawRenaming.weaken resultType))
        stepBranch
        (RawTerm.rename FX1Poly.Foundation.RawRenaming.weaken
          (RawTerm.rename FX1Poly.Foundation.RawRenaming.weaken resultType))) :
      HasTypeNativeUnion profile context
        (rule.memberCell scope motive baseBranch stepBranch scrutinee) resultType
  /-- Embed the Option value constructors (`optionNone` / `optionSome` scrutinees) — the data-elim
  scrutinee embedding for `optionMatch` (NATIVE-36; mirrors `ofNatIntro`). -/
  | ofOptionIntro {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (optionTyped : HasTypeDescOptionIntro profile context subject classifier) :
      HasTypeNativeUnion profile context subject classifier
  /-- Embed the Either value constructors (`eitherInl` / `eitherInr` scrutinees) — the data-elim
  scrutinee embedding for `eitherMatch`. -/
  | ofEitherIntro {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (eitherTyped : HasTypeDescEitherIntro profile context subject classifier) :
      HasTypeNativeUnion profile context subject classifier
  /-- Embed the identity reflexivity constructor (`refl` witnesses) — the data-elim scrutinee embedding
  for `idJ`. -/
  | ofIdIntro {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (idTyped : HasTypeDescIdIntro profile context subject classifier) :
      HasTypeNativeUnion profile context subject classifier
  /-- Embed the pair constructor (`pair` scrutinees) — the data-elim scrutinee embedding for fst / snd. -/
  | ofPairIntro {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (pairTyped : HasTypeDescPairIntro profile context subject classifier) :
      HasTypeNativeUnion profile context subject classifier
  /-- Embed the List value constructors (`listNil` / `listCons` scrutinees) — supplies the listElim
  scrutinee and the recursive-binary intro base. -/
  | ofListIntro {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (listTyped : HasTypeDescListIntro profile context subject classifier) :
      HasTypeNativeUnion profile context subject classifier
  /-- The table-driven NON-recursive two-branch match arm (the NATIVE-36 union residency of the
  `DataElimUnionSpike.twoBranchMatchRow`): scrutinee and both branches are RECURSIVE in the UNION, with
  the branch classifiers rule-parametric.  Premise parity with the spike (the one-binder motive is
  stored). -/
  | twoBranchMatchElim {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : NativeTwoBranchMatchElimRule)
      (motive : RawTerm (scope + 1))
      (firstBranch secondBranch scrutinee : RawTerm scope)
      (typeParamA typeParamB resultType : RawTerm scope)
      (isTwoBranchMatch : nativeTwoBranchMatchRuleOf generator = some rule)
      (scrutineeTyped : HasTypeNativeUnion profile context scrutinee
        (rule.scrutineeType scope typeParamA typeParamB))
      (firstBranchTyped : HasTypeNativeUnion profile context firstBranch
        (rule.firstBranchType scope typeParamA typeParamB resultType))
      (secondBranchTyped : HasTypeNativeUnion profile context secondBranch
        (rule.secondBranchType scope typeParamA typeParamB resultType)) :
      HasTypeNativeUnion profile context
        (rule.memberCell scope motive firstBranch secondBranch scrutinee) resultType
  /-- The table-driven path-induction arm (idJ; the NATIVE-36 union residency of
  `DataElimUnionSpike.pathInductionRow`): witness at a reflexive identity code and base case RECURSIVE
  in the UNION, the two-binder motive stored. -/
  | pathInductionElim {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : NativePathInductionElimRule)
      (motive : RawTerm (scope + 2))
      (baseCase witness : RawTerm scope)
      (typeCode endpoint resultType : RawTerm scope)
      (isPathInduction : nativePathInductionRuleOf generator = some rule)
      (witnessTyped : HasTypeNativeUnion profile context witness
        (rule.witnessType scope typeCode endpoint))
      (baseCaseTyped : HasTypeNativeUnion profile context baseCase resultType) :
      HasTypeNativeUnion profile context
        (rule.memberCell scope motive baseCase witness) resultType
  /-- The table-driven projection arm (fst / snd; the NATIVE-36 union residency of
  `DataElimUnionSpike.projectionRow`): scrutinee at a product code RECURSIVE in the UNION, output the
  selected component type. -/
  | projectionElim {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : NativeProjectionElimRule)
      (pairTerm firstType secondType : RawTerm scope)
      (isProjection : nativeProjectionRuleOf generator = some rule)
      (pairTyped : HasTypeNativeUnion profile context pairTerm
        (productTypeCell firstType secondType)) :
      HasTypeNativeUnion profile context
        (rule.memberCell scope pairTerm) (rule.projectedType scope firstType secondType)
  /-- The RECURSIVE-UNARY data-intro arm (`natSucc`; the NATIVE-36 union residency of
  `DataIntroNaryUnionSpike.recursiveUnaryRow`): the child premise is RECURSIVE in the UNION — a numeral
  tower composes through this arm. -/
  | recursiveUnaryIntro {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : NativeRecursiveUnaryDataIntroRule) (child : RawTerm scope)
      (isRecursiveUnary : nativeRecursiveUnaryDataIntroRuleOf generator = some rule)
      (childTyped : HasTypeNativeUnion profile context child (rule.childType scope)) :
      HasTypeNativeUnion profile context
        (rule.memberCell scope child) (rule.outputType scope)
  /-- The RECURSIVE-BINARY data-intro arm (`listCons`; the NATIVE-36 union residency of
  `DataIntroNaryUnionSpike.recursiveBinaryRow`): a GROWN head plus a UNION-recursive tail — `cons`
  chains compose through this arm. -/
  | recursiveBinaryIntro {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : NativeRecursiveBinaryDataIntroRule)
      (head tail elementType : RawTerm scope)
      (isRecursiveBinary : nativeRecursiveBinaryDataIntroRuleOf generator = some rule)
      (headTyped : HasTypeDescPi profile context head elementType)
      (tailTyped : HasTypeNativeUnion profile context tail
        (rule.containerType scope elementType)) :
      HasTypeNativeUnion profile context
        (rule.memberCell scope head tail) (rule.containerType scope elementType)
  /-- The PINNED-UNARY data-intro arm (`optionSome`): a single GROWN child whose classifier pins the
  element type param, the output computed from that param. -/
  | pinnedUnaryIntro {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : NativePinnedUnaryDataIntroRule) (child elementType : RawTerm scope)
      (isPinnedUnary : nativePinnedUnaryDataIntroRuleOf generator = some rule)
      (childTyped : HasTypeDescPi profile context child elementType) :
      HasTypeNativeUnion profile context
        (rule.memberCell scope child) (rule.outputType scope elementType)
  /-- The NULLARY-FREE-TYPE data-intro arm (`optionNone`): a CHILDLESS value whose element type is
  FREE, carrying a grown type-formedness premise, the container-code output. -/
  | nullaryFreeTypeIntro {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : NativeNullaryFreeTypeDataIntroRule)
      (elementType : RawTerm scope) (elementLevel : LevelExpr) (flag : UniverseFlag)
      (isNullaryFreeType : nativeNullaryFreeTypeDataIntroRuleOf generator = some rule)
      (elementTypeFormed :
        HasTypeDescPi profile context elementType (universeCodeCell elementLevel flag)) :
      HasTypeNativeUnion profile context
        (rule.memberCell scope) (rule.outputType scope elementType)
  /-- The COPRODUCT data-intro arm (`eitherInl` / `eitherInr`): a GROWN value premise plus a free-type
  formedness premise for the un-injected side, the either-code output. -/
  | coproductIntro {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : NativeCoproductDataIntroRule)
      (value pinnedType freeType : RawTerm scope) (freeLevel : LevelExpr) (flag : UniverseFlag)
      (isCoproduct : nativeCoproductDataIntroRuleOf generator = some rule)
      (valueTyped : HasTypeDescPi profile context value pinnedType)
      (freeTypeFormed :
        HasTypeDescPi profile context freeType (universeCodeCell freeLevel flag)) :
      HasTypeNativeUnion profile context
        (rule.injectionCell scope value) (rule.outputType scope pinnedType freeType)
  /-- The NON-DEPENDENT-BINARY data-intro arm (`pair`): two GROWN children at two independent type
  params, the product-code output. -/
  | nonDependentBinaryIntro {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : NativeNonDependentBinaryDataIntroRule)
      (firstChild secondChild firstType secondType : RawTerm scope)
      (isNonDependentBinary : nativeNonDependentBinaryDataIntroRuleOf generator = some rule)
      (firstTyped : HasTypeDescPi profile context firstChild firstType)
      (secondTyped : HasTypeDescPi profile context secondChild secondType) :
      HasTypeNativeUnion profile context
        (rule.memberCell scope firstChild secondChild)
        (rule.outputType scope firstType secondType)
  /-- The REFLEXIVE data-intro arm (`refl`): a GROWN witness, a TERM-INDEXED output `Id(A, x, x)`. -/
  | reflexiveIntro {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : NativeReflexiveDataIntroRule) (witness witnessType : RawTerm scope)
      (isReflexive : nativeReflexiveDataIntroRuleOf generator = some rule)
      (witnessTyped : HasTypeDescPi profile context witness witnessType) :
      HasTypeNativeUnion profile context
        (rule.memberCell scope witness) (rule.outputType scope witnessType witness)
  /-- The table-driven listElim arm (the NATIVE-33 union residency of
  `ListElimUnionSpike.listElimRecursiveRow`, discharging the batch-1 pin): scrutinee LIST-INTRO-typed,
  nil/cons branches host-typed at the non-dependent result / 3-arg curried step type.  Premise parity
  with the bespoke `HasTypeDescListElim.listElimIntro`; the cons branch stays STORED. -/
  | listElim {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : NativeListElimRule)
      (motive : RawTerm (scope + 1))
      (scrutinee nilBranch consBranch elementType resultType : RawTerm scope)
      (isListElim : listElimNativeRuleOf generator = some rule)
      (scrutineeTyped : HasTypeDescListIntro profile context scrutinee (listTypeCell elementType))
      (nilBranchTyped : HasTypeDescPi profile context nilBranch resultType)
      (consBranchTyped : HasTypeDescPi profile context consBranch
        (listStepFunctionType elementType resultType)) :
      HasTypeNativeUnion profile context
        (rule.memberCell scope motive scrutinee nilBranch consBranch) resultType
  /-- The CONVERSION arm (the conv-closure): a union-typed subject reclassifies along a raw
  definitional equality, with the target classifier itself union-typed at a universe code.
  Field-identical to `HasTypeDescPi.conv` — shape parity is what the embedding adequacies need.
  This arm dissolves the no-conv-arm wall: union substitution no longer needs host-typed
  substituent images, and congruence-step subject reduction can absorb the dependent-scrutinee
  classifier drift. -/
  | conv {scope : Nat} {context : TypingContext profile scope}
      {subject classifier reclassifier : RawTerm scope}
      (levelExpr : LevelExpr) (flag : UniverseFlag)
      (typed : HasTypeNativeUnion profile context subject classifier)
      (converts : Conv classifier reclassifier)
      (reclassifierTyped :
        HasTypeNativeUnion profile context reclassifier
          (universeCodeCell levelExpr flag)) :
      HasTypeNativeUnion profile context subject reclassifier

/-! ## ★ The wall-falls smokes — typable for the FIRST time -/

/-- **★ The WHOLE endpoint redex in ONE derivation.**  `pathApp(pathLam(Type@0), 0) : Type@1` — the
path through the graded intro arm, the endpoint argument through the data embedding, composed by the
recursive elim arm.  No prior judgment contained both premises. -/
theorem endpointRedexNativelyTypedWhole {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeNativeUnion profile (TypingContext.empty : TypingContext profile 0)
      (pathAppCell (pathLamCell (universeCodeCell LevelExpr.lzero flag)) intervalZeroCell)
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) :=
  HasTypeNativeUnion.generalElim TypingContext.empty .gen_pathApp pathAppGeneralElimRule
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (RawTerm.weaken (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag))
    (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)
    (pathLamCell (universeCodeCell LevelExpr.lzero flag)) intervalZeroCell rfl
    (HasTypeNativeUnion.gradedBinderIntro TypingContext.empty .gen_pathLam pathLamGradedIntroRule
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
      (RawTerm.weaken (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag))
      (universeCodeCell LevelExpr.lzero flag)
      LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl (Nat.zero_le 1)
      (fun gateHolds => Bool.noConfusion gateHolds)
      (fun gateHolds => Bool.noConfusion gateHolds)
      (HasTypeNativeUnion.ofGrown
        (HasTypeDescPi.ofFormation
          (HasTypeDesc.universeFormation
            (TypingContext.empty.cons intervalTypeCell) LevelExpr.lzero flag))))
    (HasTypeNativeUnion.ofDataIntro
      (HasTypeDescDataIntro.nullaryIntro TypingContext.empty .gen_interval0 () .childNil
        { outputTypeCode := fun _ => intervalTypeCell } rfl))

/-- **★ The λ-over-data wall falls.**  `λ(x:Bool).0 : Π(x:Bool).Interval` — a λ whose BODY (`0`) is
typed by the DATA embedding, with the domain/classifier formation premises through the base-type
embedding.  Untypable in every prior engine: the host `piIntro` demands a host-typed body and the
interval endpoint is not host-typable (`intervalZeroGrownUntypable`, the NATIVE-08 wall). -/
theorem constantIntervalLambdaNativelyTyped {profile : PolyProfile} :
    HasTypeNativeUnion profile (TypingContext.empty : TypingContext profile 0)
      (lamCell boolTypeCell intervalZeroCell)
      (piTyCodeCell boolTypeCell intervalTypeCell) :=
  HasTypeNativeUnion.gradedBinderIntro TypingContext.empty .gen_lam lamGradedIntroRule
    boolTypeCell intervalTypeCell intervalZeroCell
    LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl trivial
    (fun _ => HasTypeNativeUnion.ofBaseType
      (HasTypeDescBaseType.baseFormation TypingContext.empty .gen_boolCode () .childNil
        { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } rfl))
    (fun _ => HasTypeNativeUnion.ofBaseType
      (HasTypeDescBaseType.baseFormation (TypingContext.empty.cons boolTypeCell)
        .gen_intervalCode () .childNil
        { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } rfl))
    (HasTypeNativeUnion.ofDataIntro
      (HasTypeDescDataIntro.nullaryIntro (TypingContext.empty.cons boolTypeCell)
        .gen_interval0 () .childNil { outputTypeCode := fun _ => intervalTypeCell } rfl))

/-! ## ★ Bridge full adequacy: all 6 arms translate into the union -/

/-- **★ Every Bridge typing translates to a native-union typing at the same subject and classifier —
with the interval-formation FLAG LIBERALITY honestly surfaced.**  The left disjunct is the exact
translation (5 of 6 arms + every recursive composition).  The right disjunct fires ONLY for a bare
`intervalFormation` instance at a (possibly non-standard) flag: the native base-type row pins
`standard` (flag-determinism), so the bespoke any-flag formation is reproduced at the PINNED flag with
the dropped liberality recorded in the equations.  In the recursive `pathElim` case the disjunct is
REFUTED for both premises by classifier-head no-confusion (a path's classifier is bridge-headed and an
argument's is interval-headed — never universe-headed), so the recursion always proceeds on exact
translations: the judgment boundary dissolves through the union's recursive elim arm. -/
theorem HasTypeDescBridge.toNativeUnion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescBridge profile context subject classifier) :
    HasTypeNativeUnion profile context subject classifier
    ∨ (∃ liberalFlag : UniverseFlag,
        subject = intervalTypeCell ∧
        classifier = universeCodeCell LevelExpr.lzero liberalFlag ∧
        HasTypeNativeUnion profile context intervalTypeCell
          (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) := by
  induction derivation with
  | intervalFormation flag =>
      exact Or.inr ⟨flag, rfl, rfl,
        HasTypeNativeUnion.ofBaseType
          (HasTypeDescBaseType.baseFormation _ .gen_intervalCode () .childNil
            { outputUniverse := fun _ =>
                universeCodeCell LevelExpr.lzero UniverseFlag.standard } rfl)⟩
  | intervalZero =>
      exact Or.inl (HasTypeNativeUnion.ofDataIntro
        (HasTypeDescDataIntro.nullaryIntro _ .gen_interval0 () .childNil
          { outputTypeCode := fun _ => intervalTypeCell } rfl))
  | intervalOne =>
      exact Or.inl (HasTypeNativeUnion.ofDataIntro
        (HasTypeDescDataIntro.nullaryIntro _ .gen_interval1 () .childNil
          { outputTypeCode := fun _ => intervalTypeCell } rfl))
  | bridgeFormation typeCode leftEndpoint rightEndpoint level flag
      typeCodeTyped leftTyped rightTyped =>
      exact Or.inl (HasTypeNativeUnion.ofTermIndexedFormer
        (termIndexedFormerGenFormation_reconstructsBridge typeCode leftEndpoint rightEndpoint
          level flag typeCodeTyped leftTyped rightTyped))
  | pathIntro body typeCode bodyTyped dimensionAffine =>
      exact Or.inl (HasTypeNativeUnion.gradedBinderIntro _ .gen_pathLam pathLamGradedIntroRule
        typeCode (RawTerm.weaken typeCode) body
        LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl dimensionAffine
        (fun gateHolds => Bool.noConfusion gateHolds)
        (fun gateHolds => Bool.noConfusion gateHolds)
        (HasTypeNativeUnion.ofGrown bodyTyped))
  | pathElim path argument typeCode leftEndpoint rightEndpoint
      pathTyped argumentTyped pathTranslated argumentTranslated =>
      rcases pathTranslated with pathNative | ⟨_, _, pathClassifierClash, _⟩
      · rcases argumentTranslated with argumentNative |
          ⟨_, _, argumentClassifierClash, _⟩
        · exact Or.inl (HasTypeNativeUnion.generalElim _ .gen_pathApp pathAppGeneralElimRule
            typeCode (RawTerm.weaken typeCode) leftEndpoint rightEndpoint
            path argument rfl pathNative argumentNative)
        · -- The argument premise's classifier is `intervalTypeCell`, never universe-headed.
          exact absurd (congrArg RawTerm.rootGenerator argumentClassifierClash)
            (by intro headEq; cases headEq)
      · -- The path premise's classifier is bridge-headed, never universe-headed.
        exact absurd (congrArg RawTerm.rootGenerator pathClassifierClash)
          (by intro headEq; cases headEq)

/-- **The standard-flag corollary: on the flag-disciplined fragment the translation is EXACT.**  A
Bridge typing whose classifier is not a bare universe code (every endpoint, every bridge formation,
every path intro/elim — all but the bare `intervalFormation` instances) translates to the union at
the SAME subject and classifier with no disjunct. -/
theorem HasTypeDescBridge.toNativeUnionExact {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescBridge profile context subject classifier)
    (isNotBareIntervalFormation : subject ≠ intervalTypeCell) :
    HasTypeNativeUnion profile context subject classifier := by
  rcases derivation.toNativeUnion with nativeTyped | ⟨_, subjectEq, _, _⟩
  · exact nativeTyped
  · exact absurd subjectEq isNotBareIntervalFormation

/-! ## The coverage gate -/

/-- **The NATIVE-25 coverage record.**  Each field is a distinct live property of the seed union; an
inhabitant certifies the union is exercised (both wall-falls compositions + both adequacy forms). -/
structure NativeUnionCoverage (profile : PolyProfile) (flag : UniverseFlag) : Prop where
  /-- The whole endpoint redex types in one derivation. -/
  wholeRedexTyped : HasTypeNativeUnion profile (TypingContext.empty : TypingContext profile 0)
    (pathAppCell (pathLamCell (universeCodeCell LevelExpr.lzero flag)) intervalZeroCell)
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
  /-- The λ-over-data composition types. -/
  lambdaOverDataTyped : HasTypeNativeUnion profile (TypingContext.empty : TypingContext profile 0)
    (lamCell boolTypeCell intervalZeroCell)
    (piTyCodeCell boolTypeCell intervalTypeCell)
  /-- Every Bridge typing translates (with the flag disjunct). -/
  bridgeTranslates : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    HasTypeDescBridge profile context subject classifier →
    HasTypeNativeUnion profile context subject classifier
    ∨ (∃ liberalFlag : UniverseFlag,
        subject = intervalTypeCell ∧
        classifier = universeCodeCell LevelExpr.lzero liberalFlag ∧
        HasTypeNativeUnion profile context intervalTypeCell
          (universeCodeCell LevelExpr.lzero UniverseFlag.standard))
  /-- On non-interval-formation subjects the translation is exact. -/
  bridgeTranslatesExact : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    HasTypeDescBridge profile context subject classifier →
    subject ≠ intervalTypeCell →
    HasTypeNativeUnion profile context subject classifier

/-- **★ The NATIVE-25 coverage gate** — inhabited by the shipped witnesses. -/
theorem nativeUnionCoverageWitness {profile : PolyProfile} (flag : UniverseFlag) :
    NativeUnionCoverage profile flag where
  wholeRedexTyped := endpointRedexNativelyTypedWhole flag
  lambdaOverDataTyped := constantIntervalLambdaNativelyTyped
  bridgeTranslates := fun derivation => derivation.toNativeUnion
  bridgeTranslatesExact := fun derivation isNotBare =>
    derivation.toNativeUnionExact isNotBare

/-! ## ★ NATIVE-36 headline smokes — the new families exercised IN THE UNION

Cheap restatements through the new arms: the recursive `natSucc` row applied twice (the numeral tower
the host engine could not state), one boolElim ι reduct typed through the two-branch match arm, and the
listElim nil-ι typed through the listElim arm. -/

/-- **★ The numeral `2` types IN THE UNION through the recursive `natSucc` arm applied twice.**
`2 = natSucc(natSucc(natZero)) : Nat` through `recursiveUnaryIntro` twice, the `natZero` base reached
via the `ofNatIntro` embedding.  Exactly the statement a host-premise schema could not make — the
numeral tower closes purely through the union's own recursive intro arm. -/
theorem numeralTwoTypedThroughUnionRecursiveIntroTwice {profile : PolyProfile} :
    HasTypeNativeUnion profile (TypingContext.empty : TypingContext profile 0)
      (natSuccCell (natSuccCell natZeroCell)) natTypeCell :=
  HasTypeNativeUnion.recursiveUnaryIntro TypingContext.empty .gen_natSucc
    natSuccNativeRecursiveUnaryRule (natSuccCell natZeroCell) rfl
    (HasTypeNativeUnion.recursiveUnaryIntro TypingContext.empty .gen_natSucc
      natSuccNativeRecursiveUnaryRule natZeroCell rfl
      (HasTypeNativeUnion.ofNatIntro (HasTypeDescNatIntro.natZeroIntro TypingContext.empty)))

/-- **★ One boolElim ι reduct types IN THE UNION through the two-branch match arm.**  A union-typed
`boolElim` on `boolTrue` (both branches union-typed at the result `C`) ι-reduces to the THEN branch
(`Step.iotaBoolTrue`), union-typed at `C`.  The redex and the reduct both type in the union. -/
theorem boolElimTrueIotaUnionTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (thenBranch elseBranch resultType : RawTerm scope)
    (thenBranchTyped : HasTypeNativeUnion profile context thenBranch resultType)
    (elseBranchTyped : HasTypeNativeUnion profile context elseBranch resultType) :
    HasTypeNativeUnion profile context
      (boolElimCell motive boolTrueCell thenBranch elseBranch) resultType ∧
    Step (boolElimCell motive boolTrueCell thenBranch elseBranch) thenBranch ∧
    HasTypeNativeUnion profile context thenBranch resultType :=
  ⟨HasTypeNativeUnion.twoBranchMatchElim context .gen_boolElim boolElimNativeMatchRule
      motive thenBranch elseBranch boolTrueCell boolTrueCell boolTrueCell resultType rfl
      (HasTypeNativeUnion.ofDataIntro (HasTypeDescDataIntro.boolTrueTyped context))
      thenBranchTyped elseBranchTyped,
    Step.iotaBoolTrue,
    thenBranchTyped⟩

/-- **★ The listElim nil-ι selects the nil branch, typed IN THE UNION.**  A union-typed `listElim` on
`nil` ι-steps to the nil branch (`Step.iotaListElimNil`), the eliminator typed by the union's own
`listElim` arm (scrutinee `nil` list-intro-typed via `listNilIntro`), and the nil branch host-typed. -/
theorem listElimNilIotaUnionTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (nilBranch consBranch elementType resultType : RawTerm scope)
    (elementLevel : LevelExpr) (flag : UniverseFlag)
    (elementTypeFormed :
      HasTypeDescPi profile context elementType (universeCodeCell elementLevel flag))
    (nilBranchTyped : HasTypeDescPi profile context nilBranch resultType)
    (consBranchTyped : HasTypeDescPi profile context consBranch
      (listStepFunctionType elementType resultType)) :
    HasTypeNativeUnion profile context
      (listElimCell motive listNilCell nilBranch consBranch) resultType ∧
    Step (listElimCell motive listNilCell nilBranch consBranch) nilBranch ∧
    HasTypeDescPi profile context nilBranch resultType :=
  ⟨HasTypeNativeUnion.listElim context .gen_listElim listElimNativeRule
      motive listNilCell nilBranch consBranch elementType resultType rfl
      (HasTypeDescListIntro.listNilIntro context elementType elementLevel flag elementTypeFormed)
      nilBranchTyped consBranchTyped,
    Step.iotaListElimNil, nilBranchTyped⟩

/-! ## ★ The NATIVE-36 union-residency coverage gate -/

/-- **The NATIVE-36 union-residency coverage record.**  Each field is a distinct live property of the
new families landed IN the real union: the recursive data-intro tower composes, a non-recursive
eliminator ι reduct types through the match arm, and the listElim nil-ι types through the listElim arm.
An inhabitant certifies the new arms are live (constructed, not just declared). -/
structure NativeFamiliesUnionResidencyCoverage (profile : PolyProfile) (flag : UniverseFlag) : Prop where
  /-- The numeral `2` types through the recursive `natSucc` intro arm applied twice. -/
  numeralTowerComposesInUnion : HasTypeNativeUnion profile
    (TypingContext.empty : TypingContext profile 0)
    (natSuccCell (natSuccCell natZeroCell)) natTypeCell
  /-- A boolElim ι reduct types through the two-branch match arm. -/
  boolElimIotaInUnion : ∀ {scope : Nat} (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (thenBranch elseBranch resultType : RawTerm scope),
    HasTypeNativeUnion profile context thenBranch resultType →
    HasTypeNativeUnion profile context elseBranch resultType →
    HasTypeNativeUnion profile context
      (boolElimCell motive boolTrueCell thenBranch elseBranch) resultType ∧
    Step (boolElimCell motive boolTrueCell thenBranch elseBranch) thenBranch ∧
    HasTypeNativeUnion profile context thenBranch resultType
  /-- The listElim nil-ι types through the listElim arm. -/
  listElimNilIotaInUnion : ∀ {scope : Nat} (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (nilBranch consBranch elementType resultType : RawTerm scope)
    (elementLevel : LevelExpr) (flag : UniverseFlag),
    HasTypeDescPi profile context elementType (universeCodeCell elementLevel flag) →
    HasTypeDescPi profile context nilBranch resultType →
    HasTypeDescPi profile context consBranch
      (listStepFunctionType elementType resultType) →
    HasTypeNativeUnion profile context
      (listElimCell motive listNilCell nilBranch consBranch) resultType ∧
    Step (listElimCell motive listNilCell nilBranch consBranch) nilBranch ∧
    HasTypeDescPi profile context nilBranch resultType

/-- **★ The NATIVE-36 union-residency gate** — inhabited by the shipped witnesses. -/
theorem nativeFamiliesUnionResidencyWitness {profile : PolyProfile} (flag : UniverseFlag) :
    NativeFamiliesUnionResidencyCoverage profile flag where
  numeralTowerComposesInUnion := numeralTwoTypedThroughUnionRecursiveIntroTwice
  boolElimIotaInUnion := fun context motive thenBranch elseBranch resultType
    thenBranchTyped elseBranchTyped =>
    boolElimTrueIotaUnionTyped context motive thenBranch elseBranch resultType
      thenBranchTyped elseBranchTyped
  listElimNilIotaInUnion := fun context motive nilBranch consBranch elementType resultType
    elementLevel flag elementTypeFormed nilBranchTyped consBranchTyped =>
    listElimNilIotaUnionTyped context motive nilBranch consBranch elementType resultType
      elementLevel flag elementTypeFormed nilBranchTyped consBranchTyped

end FX1Poly.Typed

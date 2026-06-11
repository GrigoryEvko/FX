import FX1Poly.Typed.HasTypeNativeUnion
import FX1Poly.Typed.HasTypeDescBoolElim
import FX1Poly.Typed.HasTypeDescOptionMatch
import FX1Poly.Typed.HasTypeDescEitherMatch
import FX1Poly.Typed.HasTypeDescIdElim
import FX1Poly.Typed.HasTypeDescSigmaProjection

/-! # FX1Poly/Typed/DataElimUnionSpike — NATIVE-28: NON-recursive data-eliminator rows on the seed union

This file is the NON-recursive sibling of `RecursiveElimUnionSpike` (NATIVE-27, the recursive natElim /
natRec spike).  Where that file handled the eliminators whose succ-ι reduct re-invokes the eliminator
itself (the recursion-closure obstruction), the NON-recursive eliminators here have NO inductive
hypothesis: their ι reduct is a branch (boolElim / optionMatch None / eitherMatch / idJ), a handler
APPLIED to the payload (optionMatch Some / eitherMatch), or a CHILD of the scrutinee (fst / snd).  Their
premise telescopes split into three genuinely-distinct shapes — so, per the NATIVE-27 verdict (dedicated
per-premise-shape tables, NOT a single `GeneralElimRule` overload), this file ships THREE rule structures,
grouped by premise-telescope shape, plus ONE spike inductive that table-drives all three.

## The three premise-telescope shapes (three rule structures)

  * **`TwoBranchMatchElimRule`** — `boolElim` / `optionMatch` / `eitherMatch`.  Motive under one binder
    (`scope + 1`, stored), a scrutinee at a type-parameter-indexed inductive code, and TWO branches whose
    classifiers are RULE-PARAMETRIC (boolElim: both at the result type; optionMatch: a value None branch
    at the result and a function Some branch `A → C`; eitherMatch: two function branches `A → C`, `B → C`).
    Rows: `boolElimMatchRule` / `optionMatchMatchRule` / `eitherMatchMatchRule`; table `twoBranchMatchRuleOf`.
  * **`PathInductionElimRule`** — `idJ`.  Motive under TWO binders (`scope + 2`, stored), a base case at the
    result type, and a witness at a REFLEXIVE identity code `Id(A, x, x)`.  Row `idJPathInductionRule`;
    table `pathInductionRuleOf`.
  * **`ProjectionElimRule`** — `fst` / `snd`.  No motive, no branches: a single scrutinee at a product code
    `product(A, B)` and an output that is one of the two component types.  Rows `fstProjectionRule` /
    `sndProjectionRule`; table `projectionRuleOf`.

## The spike judgment (`DataElimUnionSpike`)

The seed union (`HasTypeNativeUnion`, embedded by `ofUnion` — bool scrutinees route through its
`ofDataIntro` arm) extended by intro-engine embeddings for the non-union scrutinees (`ofOptionIntro` /
`ofEitherIntro` / `ofIdIntro` / `ofPairIntro`) and ONE table-driven arm per shape (`twoBranchMatchRow` /
`pathInductionRow` / `projectionRow`) whose scrutinee and branch premises are RECURSIVE IN THE SPIKE.  The
motives (one- and two-binder) stay STORED exactly as the bespoke engines store them — premise parity is the
delete-safety requirement for the NATIVE-29/30/31 folds.  Refactor-by-addition sibling: nothing in the
shipped union or any bespoke engine is touched.

## Adequacy (premise parity) + typed ι smokes

  * `HasTypeDescBoolElim.toDataElimUnionSpike` / `…OptionMatch…` / `…EitherMatch…` / `…IdElim…` /
    `…SigmaProjection…` — every bespoke derivation maps into the spike (cases + constructor application; the
    NATIVE-29/30/31 fold's delete-safety direction).
  * `boolElimTrueIotaSpikeTyped` / `optionMatchNoneIotaSpikeTyped` / `optionMatchSomeIotaSpikeTyped` /
    `fstProjectionIotaSpikeTyped` — typed ι smokes: the eliminator fires (`Step.iota…`) and the reduct types
    IN THE SPIKE.  More families' ι smokes are shipped; the honestly-pinned residual is recorded in the
    docstrings (the eitherMatch / idJ ι reducts type identically through the same `piElim` / branch routes —
    shipped — while a fully-general arbitrary-branch reduct typing inherits the same standard-machinery
    deferral the bespoke engines carry).

## Zero-axiom

The three tables are if-then-else over `DecidableEq Generator` (rfl on the diagonal); the spike is a
strictly-positive inductive (four intro-embedding arms + three table-driven arms); the adequacy theorems are
single-`cases` + constructor application; the ι smokes are direct constructions composing `Step.iota…` with
the spike's own arms and `piElim` for the app-chain reducts.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditNativeWaveDataElim.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## Shape 1: the two-branch match rule schema + the three match rows -/

/-- A two-branch match-eliminator row (`boolElim` / `optionMatch` / `eitherMatch`).  The motive lives under
ONE binder (`scope + 1`, stored).  The scrutinee inhabits a type-parameter-indexed inductive code, and the
two branches carry RULE-PARAMETRIC classifiers (built from the two type parameters and the result type) —
this is what lets one structure cover the value-branch boolElim, the value/function-branch optionMatch, and
the two-function-branch eitherMatch without a `GeneralElimRule` overload. -/
structure TwoBranchMatchElimRule where
  /-- The inductive code the scrutinee inhabits, built from the (up to two) type parameters.  boolElim:
  the constant `boolTypeCell` (parameters ignored).  optionMatch: `optionTypeCell typeParamA`.  eitherMatch:
  `eitherTypeCell typeParamA typeParamB`. -/
  scrutineeType : (scope : Nat) → RawTerm scope → RawTerm scope → RawTerm scope
  /-- The eliminator cell: motive (one binder), first branch, second branch, scrutinee. -/
  memberCell : (scope : Nat) → RawTerm (scope + 1) → RawTerm scope → RawTerm scope →
    RawTerm scope → RawTerm scope
  /-- The first branch's classifier, built from the type parameters and the result type.  boolElim: the
  result type (the then branch is a value).  optionMatch: the result type (the None branch is a value).
  eitherMatch: `piTyCodeCell typeParamA (weaken resultType)` (the left handler `A → C`). -/
  firstBranchType : (scope : Nat) → RawTerm scope → RawTerm scope → RawTerm scope → RawTerm scope
  /-- The second branch's classifier.  boolElim: the result type (the else branch is a value).
  optionMatch: `piTyCodeCell typeParamA (weaken resultType)` (the Some handler `A → C`).  eitherMatch:
  `piTyCodeCell typeParamB (weaken resultType)` (the right handler `B → C`). -/
  secondBranchType : (scope : Nat) → RawTerm scope → RawTerm scope → RawTerm scope → RawTerm scope

/-- The `gen_boolElim` row: scrutinee at the constant `boolTypeCell`, both branches at the result type. -/
def boolElimMatchRule : TwoBranchMatchElimRule where
  scrutineeType := fun _ _ _ => boolTypeCell
  memberCell := fun _ motive thenBranch elseBranch scrutinee =>
    boolElimCell motive scrutinee thenBranch elseBranch
  firstBranchType := fun _ _ _ resultType => resultType
  secondBranchType := fun _ _ _ resultType => resultType

/-- The `gen_optionMatch` row: scrutinee at `option(A)`, None branch at the result type, Some branch the
non-dependent handler `A → C`. -/
def optionMatchMatchRule : TwoBranchMatchElimRule where
  scrutineeType := fun _ typeParamA _ => optionTypeCell typeParamA
  memberCell := fun _ motive noneBranch someBranch scrutinee =>
    optionMatchCell motive noneBranch someBranch scrutinee
  firstBranchType := fun _ _ _ resultType => resultType
  secondBranchType := fun _ typeParamA _ resultType =>
    piTyCodeCell typeParamA (RawTerm.weaken resultType)

/-- The `gen_eitherMatch` row: scrutinee at `either(A, B)`, both branches the non-dependent handlers
`A → C` / `B → C`. -/
def eitherMatchMatchRule : TwoBranchMatchElimRule where
  scrutineeType := fun _ typeParamA typeParamB => eitherTypeCell typeParamA typeParamB
  memberCell := fun _ motive leftBranch rightBranch scrutinee =>
    eitherMatchCell motive leftBranch rightBranch scrutinee
  firstBranchType := fun _ typeParamA _ resultType =>
    piTyCodeCell typeParamA (RawTerm.weaken resultType)
  secondBranchType := fun _ _ typeParamB resultType =>
    piTyCodeCell typeParamB (RawTerm.weaken resultType)

/-- The two-branch match table. -/
def twoBranchMatchRuleOf (generator : Generator) : Option TwoBranchMatchElimRule :=
  if generator = .gen_boolElim then some boolElimMatchRule
  else if generator = .gen_optionMatch then some optionMatchMatchRule
  else if generator = .gen_eitherMatch then some eitherMatchMatchRule
  else none

/-- Table metadata: the boolElim row is hit (rfl on the diagonal). -/
theorem twoBranchMatchRuleOf_boolElim :
    twoBranchMatchRuleOf .gen_boolElim = some boolElimMatchRule := rfl

/-- Table metadata: the optionMatch row is hit. -/
theorem twoBranchMatchRuleOf_optionMatch :
    twoBranchMatchRuleOf .gen_optionMatch = some optionMatchMatchRule := rfl

/-- Table metadata: the eitherMatch row is hit. -/
theorem twoBranchMatchRuleOf_eitherMatch :
    twoBranchMatchRuleOf .gen_eitherMatch = some eitherMatchMatchRule := rfl

/-! ## Shape 2: the path-induction rule schema + the idJ row -/

/-- A path-induction eliminator row (`idJ`).  The motive lives under TWO binders (`scope + 2`, stored).
The witness inhabits a REFLEXIVE identity code `Id(typeCode, endpoint, endpoint)`, and the base case carries
the result type (non-dependent J, following the bespoke `HasTypeDescIdElim`). -/
structure PathInductionElimRule where
  /-- The reflexive identity code the witness inhabits, built from the type code and the (shared) endpoint:
  `Id(typeCode, endpoint, endpoint)`. -/
  witnessType : (scope : Nat) → RawTerm scope → RawTerm scope → RawTerm scope
  /-- The eliminator cell: motive (two binders), base case, witness. -/
  memberCell : (scope : Nat) → RawTerm (scope + 2) → RawTerm scope → RawTerm scope → RawTerm scope

/-- The `gen_idJ` row. -/
def idJPathInductionRule : PathInductionElimRule where
  witnessType := fun _ typeCode endpoint => idTypeCell typeCode endpoint endpoint
  memberCell := fun _ motive baseCase witness => idJCell motive baseCase witness

/-- The path-induction table. -/
def pathInductionRuleOf (generator : Generator) : Option PathInductionElimRule :=
  if generator = .gen_idJ then some idJPathInductionRule
  else none

/-- Table metadata: the idJ row is hit. -/
theorem pathInductionRuleOf_idJ :
    pathInductionRuleOf .gen_idJ = some idJPathInductionRule := rfl

/-! ## Shape 3: the projection rule schema + the fst / snd rows -/

/-- A projection eliminator row (`fst` / `snd`).  No motive, no branches: a single scrutinee inhabiting a
product code `product(firstType, secondType)`, and the output is one of the two component types selected by
the row. -/
structure ProjectionElimRule where
  /-- The projection cell, built from the scrutinee pair term. -/
  memberCell : (scope : Nat) → RawTerm scope → RawTerm scope
  /-- The projected component type, selected from the two product components.  fst: the first component.
  snd: the second component. -/
  projectedType : (scope : Nat) → RawTerm scope → RawTerm scope → RawTerm scope

/-- The `gen_fst` row: project the first component. -/
def fstProjectionRule : ProjectionElimRule where
  memberCell := fun _ pairTerm => fstCell pairTerm
  projectedType := fun _ firstType _ => firstType

/-- The `gen_snd` row: project the second component. -/
def sndProjectionRule : ProjectionElimRule where
  memberCell := fun _ pairTerm => sndCell pairTerm
  projectedType := fun _ _ secondType => secondType

/-- The projection table. -/
def projectionRuleOf (generator : Generator) : Option ProjectionElimRule :=
  if generator = .gen_fst then some fstProjectionRule
  else if generator = .gen_snd then some sndProjectionRule
  else none

/-- Table metadata: the fst row is hit. -/
theorem projectionRuleOf_fst :
    projectionRuleOf .gen_fst = some fstProjectionRule := rfl

/-- Table metadata: the snd row is hit. -/
theorem projectionRuleOf_snd :
    projectionRuleOf .gen_snd = some sndProjectionRule := rfl

/-! ## The spike judgment: the seed union + the three table-driven non-recursive-eliminator arms -/

/-- **The NATIVE-28 spike judgment** — the seed union extended by intro-engine embeddings (for the
non-union scrutinees) and three table-driven non-recursive-eliminator arms with premises RECURSIVE in the
spike.  A refactor-by-addition sibling of `HasTypeNativeUnion`.  The one- and two-binder motives are STORED
(premise parity with the bespoke engines — the NATIVE-29/30/31 folds' delete-safety requirement). -/
inductive DataElimUnionSpike (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  /-- Embed the seed union (host / base-type / data / term-indexed / graded intro / general elim).  Bool
  scrutinees route through this arm's `ofDataIntro` family. -/
  | ofUnion {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (unionTyped : HasTypeNativeUnion profile context subject classifier) :
      DataElimUnionSpike profile context subject classifier
  /-- Embed the Option value constructors (`optionNone` / `optionSome` scrutinees). -/
  | ofOptionIntro {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (optionTyped : HasTypeDescOptionIntro profile context subject classifier) :
      DataElimUnionSpike profile context subject classifier
  /-- Embed the Either value constructors (`eitherInl` / `eitherInr` scrutinees). -/
  | ofEitherIntro {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (eitherTyped : HasTypeDescEitherIntro profile context subject classifier) :
      DataElimUnionSpike profile context subject classifier
  /-- Embed the identity reflexivity constructor (`refl` witnesses for idJ). -/
  | ofIdIntro {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (idTyped : HasTypeDescIdIntro profile context subject classifier) :
      DataElimUnionSpike profile context subject classifier
  /-- Embed the pair constructor (`pair` scrutinees for fst / snd). -/
  | ofPairIntro {scope : Nat} {context : TypingContext profile scope}
      {subject classifier : RawTerm scope}
      (pairTyped : HasTypeDescPairIntro profile context subject classifier) :
      DataElimUnionSpike profile context subject classifier
  /-- The two-branch match arm (boolElim / optionMatch / eitherMatch): scrutinee and both branches typed by
  THIS judgment, the branch classifiers rule-parametric. -/
  | twoBranchMatchRow {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : TwoBranchMatchElimRule)
      (motive : RawTerm (scope + 1))
      (firstBranch secondBranch scrutinee : RawTerm scope)
      (typeParamA typeParamB resultType : RawTerm scope)
      (isTwoBranchMatch : twoBranchMatchRuleOf generator = some rule)
      (scrutineeTyped : DataElimUnionSpike profile context scrutinee
        (rule.scrutineeType scope typeParamA typeParamB))
      (firstBranchTyped : DataElimUnionSpike profile context firstBranch
        (rule.firstBranchType scope typeParamA typeParamB resultType))
      (secondBranchTyped : DataElimUnionSpike profile context secondBranch
        (rule.secondBranchType scope typeParamA typeParamB resultType)) :
      DataElimUnionSpike profile context
        (rule.memberCell scope motive firstBranch secondBranch scrutinee) resultType
  /-- The path-induction arm (idJ): witness at a reflexive identity code and base case typed by THIS
  judgment, the two-binder motive stored. -/
  | pathInductionRow {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : PathInductionElimRule)
      (motive : RawTerm (scope + 2))
      (baseCase witness : RawTerm scope)
      (typeCode endpoint resultType : RawTerm scope)
      (isPathInduction : pathInductionRuleOf generator = some rule)
      (witnessTyped : DataElimUnionSpike profile context witness
        (rule.witnessType scope typeCode endpoint))
      (baseCaseTyped : DataElimUnionSpike profile context baseCase resultType) :
      DataElimUnionSpike profile context
        (rule.memberCell scope motive baseCase witness) resultType
  /-- The projection arm (fst / snd): scrutinee at a product code typed by THIS judgment, output the
  selected component type. -/
  | projectionRow {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : ProjectionElimRule)
      (pairTerm firstType secondType : RawTerm scope)
      (isProjection : projectionRuleOf generator = some rule)
      (pairTyped : DataElimUnionSpike profile context pairTerm
        (productTypeCell firstType secondType)) :
      DataElimUnionSpike profile context
        (rule.memberCell scope pairTerm) (rule.projectedType scope firstType secondType)

/-! ## Adequacy: every bespoke derivation maps into the spike (premise parity) -/

/-- **Bespoke boolElim adequacy.**  Every `HasTypeDescBoolElim` derivation translates to a spike typing at
the same subject and classifier — the scrutinee through the union's data-intro embedding, both branches
through the union's host embedding.  Premise parity (the NATIVE-29 fold's delete-safety direction). -/
theorem HasTypeDescBoolElim.toDataElimUnionSpike {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescBoolElim profile context subject classifier) :
    DataElimUnionSpike profile context subject classifier := by
  cases derivation with
  | boolElimIntro motive scrutinee thenBranch elseBranch _resultType
      scrutineeTyped thenTyped elseTyped =>
      exact DataElimUnionSpike.twoBranchMatchRow context .gen_boolElim boolElimMatchRule
        motive thenBranch elseBranch scrutinee scrutinee scrutinee classifier rfl
        (DataElimUnionSpike.ofUnion (HasTypeNativeUnion.ofDataIntro scrutineeTyped))
        (DataElimUnionSpike.ofUnion (HasTypeNativeUnion.ofGrown thenTyped))
        (DataElimUnionSpike.ofUnion (HasTypeNativeUnion.ofGrown elseTyped))

/-- **Bespoke optionMatch adequacy.**  The scrutinee through the option-intro embedding (type parameter
`A := elementType`), the None branch (value) and Some branch (`A → C`) through the host embedding. -/
theorem HasTypeDescOptionMatch.toDataElimUnionSpike {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescOptionMatch profile context subject classifier) :
    DataElimUnionSpike profile context subject classifier := by
  cases derivation with
  | optionMatchIntro motive scrutinee noneBranch someBranch elementType _resultType
      scrutineeTyped noneBranchTyped someBranchTyped =>
      exact DataElimUnionSpike.twoBranchMatchRow context .gen_optionMatch optionMatchMatchRule
        motive noneBranch someBranch scrutinee elementType elementType classifier rfl
        (DataElimUnionSpike.ofOptionIntro scrutineeTyped)
        (DataElimUnionSpike.ofUnion (HasTypeNativeUnion.ofGrown noneBranchTyped))
        (DataElimUnionSpike.ofUnion (HasTypeNativeUnion.ofGrown someBranchTyped))

/-- **Bespoke eitherMatch adequacy.**  The scrutinee through the either-intro embedding (type parameters
`A := leftType`, `B := rightType`), both function branches (`A → C`, `B → C`) through the host embedding. -/
theorem HasTypeDescEitherMatch.toDataElimUnionSpike {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescEitherMatch profile context subject classifier) :
    DataElimUnionSpike profile context subject classifier := by
  cases derivation with
  | eitherMatchIntro motive scrutinee leftBranch rightBranch leftType rightType _resultType
      scrutineeTyped leftBranchTyped rightBranchTyped =>
      exact DataElimUnionSpike.twoBranchMatchRow context .gen_eitherMatch eitherMatchMatchRule
        motive leftBranch rightBranch scrutinee leftType rightType classifier rfl
        (DataElimUnionSpike.ofEitherIntro scrutineeTyped)
        (DataElimUnionSpike.ofUnion (HasTypeNativeUnion.ofGrown leftBranchTyped))
        (DataElimUnionSpike.ofUnion (HasTypeNativeUnion.ofGrown rightBranchTyped))

/-- **Bespoke idJ adequacy.**  The witness through the id-intro embedding (type code and shared endpoint),
the base case through the host embedding; the two-binder motive stays stored. -/
theorem HasTypeDescIdElim.toDataElimUnionSpike {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescIdElim profile context subject classifier) :
    DataElimUnionSpike profile context subject classifier := by
  cases derivation with
  | idJIntro motive baseCase witness typeCode endpoint _resultType
      witnessTyped baseCaseTyped =>
      exact DataElimUnionSpike.pathInductionRow context .gen_idJ idJPathInductionRule
        motive baseCase witness typeCode endpoint classifier rfl
        (DataElimUnionSpike.ofIdIntro witnessTyped)
        (DataElimUnionSpike.ofUnion (HasTypeNativeUnion.ofGrown baseCaseTyped))

/-- **Bespoke Σ-projection adequacy.**  Both `fst` and `snd` derivations translate — the scrutinee pair
through the pair-intro embedding, the output the selected component type.  Two-arm `cases`. -/
theorem HasTypeDescSigmaProjection.toDataElimUnionSpike {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescSigmaProjection profile context subject classifier) :
    DataElimUnionSpike profile context subject classifier := by
  cases derivation with
  | fstIntro pairTerm _firstType secondType pairTyped =>
      exact DataElimUnionSpike.projectionRow context .gen_fst fstProjectionRule
        pairTerm classifier secondType rfl
        (DataElimUnionSpike.ofPairIntro pairTyped)
  | sndIntro pairTerm firstType _secondType pairTyped =>
      exact DataElimUnionSpike.projectionRow context .gen_snd sndProjectionRule
        pairTerm firstType classifier rfl
        (DataElimUnionSpike.ofPairIntro pairTyped)

/-! ## ★ Typed ι smokes: the eliminator fires and the reduct types IN THE SPIKE

Each smoke takes the branch / value typings as spike (or host) premises and exhibits the typed reduct
directly — constructor-side, so it is SR-free and propext-free (no derivation casing at a literal cell
subject, no branch-congruence).  The genuinely-new content over the bespoke ι theorems is that the redex
AND the reduct both type IN THE SPIKE (the union-spanning judgment), not in a per-family bespoke engine. -/

/-- Helper: a host (grown) typing embeds into the spike through the union's host arm. -/
theorem DataElimUnionSpike.ofGrownTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (hostTyped : HasTypeDescPi profile context subject classifier) :
    DataElimUnionSpike profile context subject classifier :=
  DataElimUnionSpike.ofUnion (HasTypeNativeUnion.ofGrown hostTyped)

/-- **★ Typed branch-selection ι (boolElim, true case).**  A spike-typed `boolElim` on `boolTrue` (both
branches spike-typed at the result `C`) ι-reduces to the THEN branch (`Step.iotaBoolTrue`), and that branch
is spike-typed at `C`.  The redex and the reduct both type in the spike. -/
theorem boolElimTrueIotaSpikeTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (thenBranch elseBranch resultType : RawTerm scope)
    (thenBranchTyped : DataElimUnionSpike profile context thenBranch resultType)
    (elseBranchTyped : DataElimUnionSpike profile context elseBranch resultType) :
    DataElimUnionSpike profile context
      (boolElimCell motive boolTrueCell thenBranch elseBranch) resultType ∧
    Step (boolElimCell motive boolTrueCell thenBranch elseBranch) thenBranch ∧
    DataElimUnionSpike profile context thenBranch resultType :=
  ⟨DataElimUnionSpike.twoBranchMatchRow context .gen_boolElim boolElimMatchRule
      motive thenBranch elseBranch boolTrueCell boolTrueCell boolTrueCell resultType rfl
      (DataElimUnionSpike.ofUnion (HasTypeNativeUnion.ofDataIntro
        (HasTypeDescDataIntro.boolTrueTyped context)))
      thenBranchTyped elseBranchTyped,
    Step.iotaBoolTrue,
    thenBranchTyped⟩

/-- **★ Typed branch-selection ι (boolElim, false case).**  The `boolFalse` mirror: ι-reduces to the ELSE
branch (`Step.iotaBoolFalse`), spike-typed at `C`. -/
theorem boolElimFalseIotaSpikeTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (thenBranch elseBranch resultType : RawTerm scope)
    (thenBranchTyped : DataElimUnionSpike profile context thenBranch resultType)
    (elseBranchTyped : DataElimUnionSpike profile context elseBranch resultType) :
    DataElimUnionSpike profile context
      (boolElimCell motive boolFalseCell thenBranch elseBranch) resultType ∧
    Step (boolElimCell motive boolFalseCell thenBranch elseBranch) elseBranch ∧
    DataElimUnionSpike profile context elseBranch resultType :=
  ⟨DataElimUnionSpike.twoBranchMatchRow context .gen_boolElim boolElimMatchRule
      motive thenBranch elseBranch boolFalseCell boolFalseCell boolFalseCell resultType rfl
      (DataElimUnionSpike.ofUnion (HasTypeNativeUnion.ofDataIntro
        (HasTypeDescDataIntro.boolFalseTyped context)))
      thenBranchTyped elseBranchTyped,
    Step.iotaBoolFalse,
    elseBranchTyped⟩

/-- **★ Typed branch-selection ι (optionMatch, None case).**  A spike-typed `optionMatch` on `optionNone`
ι-reduces to the None branch (`Step.iotaOptionMatchNone`), spike-typed at `C`.  The `optionNone` scrutinee
typing needs the element-type-formedness witness (the `None` asymmetry), carried as a host premise. -/
theorem optionMatchNoneIotaSpikeTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (noneBranch someBranch elementType resultType : RawTerm scope)
    (elementLevel : LevelExpr) (flag : UniverseFlag)
    (elementTypeFormed :
      HasTypeDescPi profile context elementType (universeCodeCell elementLevel flag))
    (noneBranchTyped : DataElimUnionSpike profile context noneBranch resultType)
    (someBranchTyped : DataElimUnionSpike profile context someBranch
      (piTyCodeCell elementType (RawTerm.weaken resultType))) :
    DataElimUnionSpike profile context
      (optionMatchCell motive noneBranch someBranch optionNoneCell) resultType ∧
    Step (optionMatchCell motive noneBranch someBranch optionNoneCell) noneBranch ∧
    DataElimUnionSpike profile context noneBranch resultType :=
  ⟨DataElimUnionSpike.twoBranchMatchRow context .gen_optionMatch optionMatchMatchRule
      motive noneBranch someBranch optionNoneCell elementType elementType resultType rfl
      (DataElimUnionSpike.ofOptionIntro
        (HasTypeDescOptionIntro.optionNoneIntro context elementType elementLevel flag elementTypeFormed))
      noneBranchTyped someBranchTyped,
    Step.iotaOptionMatchNone,
    noneBranchTyped⟩

/-- **★ Typed app-chain ι (optionMatch, Some case).**  A spike-typed `optionMatch` on `optionSome(value)`
ι-reduces to `app(someBranch, value)` (`Step.iotaOptionMatchSome`), and that application is spike-typed at
`C` (built by host `piElim` with the non-dependent codomain collapsing via `weaken_subst_singleton`, then
embedded into the spike).  Branch and value are host premises (premise parity with the bespoke ι). -/
theorem optionMatchSomeIotaSpikeTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (value noneBranch someBranch elementType resultType : RawTerm scope)
    (valueTyped : HasTypeDescPi profile context value elementType)
    (noneBranchTyped : HasTypeDescPi profile context noneBranch resultType)
    (someBranchTyped :
      HasTypeDescPi profile context someBranch (piTyCodeCell elementType (RawTerm.weaken resultType))) :
    DataElimUnionSpike profile context
      (optionMatchCell motive noneBranch someBranch (optionSomeCell value)) resultType ∧
    Step (optionMatchCell motive noneBranch someBranch (optionSomeCell value))
      (appCell someBranch value) ∧
    DataElimUnionSpike profile context (appCell someBranch value) resultType := by
  refine ⟨?_, Step.iotaOptionMatchSome, ?_⟩
  · exact DataElimUnionSpike.twoBranchMatchRow context .gen_optionMatch optionMatchMatchRule
      motive noneBranch someBranch (optionSomeCell value) elementType elementType resultType rfl
      (DataElimUnionSpike.ofOptionIntro
        (HasTypeDescOptionIntro.optionSomeIntro context value elementType valueTyped))
      (DataElimUnionSpike.ofGrownTyping noneBranchTyped)
      (DataElimUnionSpike.ofGrownTyping someBranchTyped)
  · have appTyped := HasTypeDescPi.piElim someBranchTyped valueTyped
    have codomainCollapses : (RawTerm.weaken resultType).subst0 value = resultType :=
      RawTerm.weaken_subst_singleton resultType value
    rw [codomainCollapses] at appTyped
    exact DataElimUnionSpike.ofGrownTyping appTyped

/-- **★ Typed app-chain ι (eitherMatch, inl case).**  A spike-typed `eitherMatch` on `eitherInl(value)`
ι-reduces to `app(leftBranch, value)` (`Step.iotaEitherMatchInl`), spike-typed at `C` (host `piElim` + the
codomain collapse, embedded into the spike).  The un-injected component `B` carries a formedness witness. -/
theorem eitherMatchInlIotaSpikeTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (value leftBranch rightBranch leftType rightType resultType : RawTerm scope)
    (rightLevel : LevelExpr) (flag : UniverseFlag)
    (valueTyped : HasTypeDescPi profile context value leftType)
    (rightTypeFormed : HasTypeDescPi profile context rightType (universeCodeCell rightLevel flag))
    (leftBranchTyped :
      HasTypeDescPi profile context leftBranch (piTyCodeCell leftType (RawTerm.weaken resultType)))
    (rightBranchTyped :
      HasTypeDescPi profile context rightBranch (piTyCodeCell rightType (RawTerm.weaken resultType))) :
    DataElimUnionSpike profile context
      (eitherMatchCell motive leftBranch rightBranch (eitherInlCell value)) resultType ∧
    Step (eitherMatchCell motive leftBranch rightBranch (eitherInlCell value))
      (appCell leftBranch value) ∧
    DataElimUnionSpike profile context (appCell leftBranch value) resultType := by
  refine ⟨?_, Step.iotaEitherMatchInl, ?_⟩
  · exact DataElimUnionSpike.twoBranchMatchRow context .gen_eitherMatch eitherMatchMatchRule
      motive leftBranch rightBranch (eitherInlCell value) leftType rightType resultType rfl
      (DataElimUnionSpike.ofEitherIntro
        (HasTypeDescEitherIntro.eitherInlIntro context value leftType rightType rightLevel flag
          valueTyped rightTypeFormed))
      (DataElimUnionSpike.ofGrownTyping leftBranchTyped)
      (DataElimUnionSpike.ofGrownTyping rightBranchTyped)
  · have appTyped := HasTypeDescPi.piElim leftBranchTyped valueTyped
    have codomainCollapses : (RawTerm.weaken resultType).subst0 value = resultType :=
      RawTerm.weaken_subst_singleton resultType value
    rw [codomainCollapses] at appTyped
    exact DataElimUnionSpike.ofGrownTyping appTyped

/-- **★ Typed app-chain ι (eitherMatch, inr case).**  The `eitherInr` mirror: ι-reduces to
`app(rightBranch, value)` (`Step.iotaEitherMatchInr`), spike-typed at `C`. -/
theorem eitherMatchInrIotaSpikeTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (value leftBranch rightBranch leftType rightType resultType : RawTerm scope)
    (leftLevel : LevelExpr) (flag : UniverseFlag)
    (valueTyped : HasTypeDescPi profile context value rightType)
    (leftTypeFormed : HasTypeDescPi profile context leftType (universeCodeCell leftLevel flag))
    (leftBranchTyped :
      HasTypeDescPi profile context leftBranch (piTyCodeCell leftType (RawTerm.weaken resultType)))
    (rightBranchTyped :
      HasTypeDescPi profile context rightBranch (piTyCodeCell rightType (RawTerm.weaken resultType))) :
    DataElimUnionSpike profile context
      (eitherMatchCell motive leftBranch rightBranch (eitherInrCell value)) resultType ∧
    Step (eitherMatchCell motive leftBranch rightBranch (eitherInrCell value))
      (appCell rightBranch value) ∧
    DataElimUnionSpike profile context (appCell rightBranch value) resultType := by
  refine ⟨?_, Step.iotaEitherMatchInr, ?_⟩
  · exact DataElimUnionSpike.twoBranchMatchRow context .gen_eitherMatch eitherMatchMatchRule
      motive leftBranch rightBranch (eitherInrCell value) leftType rightType resultType rfl
      (DataElimUnionSpike.ofEitherIntro
        (HasTypeDescEitherIntro.eitherInrIntro context value leftType rightType leftLevel flag
          valueTyped leftTypeFormed))
      (DataElimUnionSpike.ofGrownTyping leftBranchTyped)
      (DataElimUnionSpike.ofGrownTyping rightBranchTyped)
  · have appTyped := HasTypeDescPi.piElim rightBranchTyped valueTyped
    have codomainCollapses : (RawTerm.weaken resultType).subst0 value = resultType :=
      RawTerm.weaken_subst_singleton resultType value
    rw [codomainCollapses] at appTyped
    exact DataElimUnionSpike.ofGrownTyping appTyped

/-- **★ Typed branch-selection ι (idJ on refl).**  A spike-typed `idJ` on `refl(witness)` ι-reduces to the
base case (`Step.iotaIdJRefl`), spike-typed at `C`.  The witness typing (`witness : A`, host premise) feeds
the reflexive `Id(A, x, x)` scrutinee through the id-intro embedding; the two-binder motive stays stored. -/
theorem idJReflIotaSpikeTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (motive : RawTerm (scope + 2))
    (witness baseCase typeCode resultType : RawTerm scope)
    (witnessTyped : HasTypeDescPi profile context witness typeCode)
    (baseCaseTyped : DataElimUnionSpike profile context baseCase resultType) :
    DataElimUnionSpike profile context (idJCell motive baseCase (reflCell witness)) resultType ∧
    Step (idJCell motive baseCase (reflCell witness)) baseCase ∧
    DataElimUnionSpike profile context baseCase resultType :=
  ⟨DataElimUnionSpike.pathInductionRow context .gen_idJ idJPathInductionRule
      motive baseCase (reflCell witness) typeCode witness resultType rfl
      (DataElimUnionSpike.ofIdIntro
        (HasTypeDescIdIntro.reflIntro context witness typeCode witnessTyped))
      baseCaseTyped,
    Step.iotaIdJRefl,
    baseCaseTyped⟩

/-- **★ Typed content-projection ι (fst).**  A spike-typed `fst` of a `pair` ι-reduces to the FIRST
component (`Step.iotaFstPair`), spike-typed at the first component type `A` (the component hypothesis
verbatim).  The pair scrutinee is built from its two component host typings through the pair-intro
embedding. -/
theorem fstProjectionIotaSpikeTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (firstValue secondValue firstType secondType : RawTerm scope)
    (firstTyped : HasTypeDescPi profile context firstValue firstType)
    (secondTyped : HasTypeDescPi profile context secondValue secondType) :
    DataElimUnionSpike profile context (fstCell (pairCell firstValue secondValue)) firstType ∧
    Step (fstCell (pairCell firstValue secondValue)) firstValue ∧
    DataElimUnionSpike profile context firstValue firstType :=
  ⟨DataElimUnionSpike.projectionRow context .gen_fst fstProjectionRule
      (pairCell firstValue secondValue) firstType secondType rfl
      (DataElimUnionSpike.ofPairIntro
        (HasTypeDescPairIntro.pairIntro context firstValue secondValue firstType secondType
          firstTyped secondTyped)),
    Step.iotaFstPair,
    DataElimUnionSpike.ofGrownTyping firstTyped⟩

/-- **★ Typed content-projection ι (snd).**  The `snd` mirror: ι-reduces to the SECOND component
(`Step.iotaSndPair`), spike-typed at the second component type `B`. -/
theorem sndProjectionIotaSpikeTyped {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (firstValue secondValue firstType secondType : RawTerm scope)
    (firstTyped : HasTypeDescPi profile context firstValue firstType)
    (secondTyped : HasTypeDescPi profile context secondValue secondType) :
    DataElimUnionSpike profile context (sndCell (pairCell firstValue secondValue)) secondType ∧
    Step (sndCell (pairCell firstValue secondValue)) secondValue ∧
    DataElimUnionSpike profile context secondValue secondType :=
  ⟨DataElimUnionSpike.projectionRow context .gen_snd sndProjectionRule
      (pairCell firstValue secondValue) firstType secondType rfl
      (DataElimUnionSpike.ofPairIntro
        (HasTypeDescPairIntro.pairIntro context firstValue secondValue firstType secondType
          firstTyped secondTyped)),
    Step.iotaSndPair,
    DataElimUnionSpike.ofGrownTyping secondTyped⟩

/-! ## The coverage / verdict gate -/

/-- **The NATIVE-28 coverage record.**  Each field is a distinct live property of the non-recursive
data-eliminator row design; an inhabitant certifies the rows are expressible, the five bespoke engines map
in (premise parity — the NATIVE-29/30/31 folds' delete-safety direction), and the ι reducts type IN THE
SPIKE across all three premise-telescope shapes (branch-selection, app-chain, content-projection). -/
structure DataElimRowCoverage (profile : PolyProfile) : Prop where
  /-- Every bespoke boolElim derivation maps into the spike. -/
  boolElimAdequate : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    HasTypeDescBoolElim profile context subject classifier →
    DataElimUnionSpike profile context subject classifier
  /-- Every bespoke optionMatch derivation maps into the spike. -/
  optionMatchAdequate : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    HasTypeDescOptionMatch profile context subject classifier →
    DataElimUnionSpike profile context subject classifier
  /-- Every bespoke eitherMatch derivation maps into the spike. -/
  eitherMatchAdequate : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    HasTypeDescEitherMatch profile context subject classifier →
    DataElimUnionSpike profile context subject classifier
  /-- Every bespoke idJ derivation maps into the spike. -/
  idElimAdequate : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    HasTypeDescIdElim profile context subject classifier →
    DataElimUnionSpike profile context subject classifier
  /-- Every bespoke fst / snd derivation maps into the spike. -/
  projectionAdequate : ∀ {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope},
    HasTypeDescSigmaProjection profile context subject classifier →
    DataElimUnionSpike profile context subject classifier
  /-- The branch-selection ι reduct types in the spike (boolElim true). -/
  branchSelectionIotaInternal : ∀ {scope : Nat} (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1)) (thenBranch elseBranch resultType : RawTerm scope),
    DataElimUnionSpike profile context thenBranch resultType →
    DataElimUnionSpike profile context elseBranch resultType →
    DataElimUnionSpike profile context
      (boolElimCell motive boolTrueCell thenBranch elseBranch) resultType ∧
    Step (boolElimCell motive boolTrueCell thenBranch elseBranch) thenBranch ∧
    DataElimUnionSpike profile context thenBranch resultType
  /-- The app-chain ι reduct types in the spike (optionMatch Some). -/
  appChainIotaInternal : ∀ {scope : Nat} (context : TypingContext profile scope)
    (motive : RawTerm (scope + 1))
    (value noneBranch someBranch elementType resultType : RawTerm scope),
    HasTypeDescPi profile context value elementType →
    HasTypeDescPi profile context noneBranch resultType →
    HasTypeDescPi profile context someBranch (piTyCodeCell elementType (RawTerm.weaken resultType)) →
    DataElimUnionSpike profile context
      (optionMatchCell motive noneBranch someBranch (optionSomeCell value)) resultType ∧
    Step (optionMatchCell motive noneBranch someBranch (optionSomeCell value))
      (appCell someBranch value) ∧
    DataElimUnionSpike profile context (appCell someBranch value) resultType
  /-- The content-projection ι reduct types in the spike (fst). -/
  contentProjectionIotaInternal : ∀ {scope : Nat} (context : TypingContext profile scope)
    (firstValue secondValue firstType secondType : RawTerm scope),
    HasTypeDescPi profile context firstValue firstType →
    HasTypeDescPi profile context secondValue secondType →
    DataElimUnionSpike profile context (fstCell (pairCell firstValue secondValue)) firstType ∧
    Step (fstCell (pairCell firstValue secondValue)) firstValue ∧
    DataElimUnionSpike profile context firstValue firstType

/-- **★ The NATIVE-28 coverage gate** — inhabited by the shipped witnesses (five adequacy maps + one ι
smoke per premise-telescope shape). -/
theorem dataElimRowCoverageWitness {profile : PolyProfile} :
    DataElimRowCoverage profile where
  boolElimAdequate := fun derivation => derivation.toDataElimUnionSpike
  optionMatchAdequate := fun derivation => derivation.toDataElimUnionSpike
  eitherMatchAdequate := fun derivation => derivation.toDataElimUnionSpike
  idElimAdequate := fun derivation => derivation.toDataElimUnionSpike
  projectionAdequate := fun derivation => derivation.toDataElimUnionSpike
  branchSelectionIotaInternal := fun context motive thenBranch elseBranch resultType
    thenBranchTyped elseBranchTyped =>
    boolElimTrueIotaSpikeTyped context motive thenBranch elseBranch resultType
      thenBranchTyped elseBranchTyped
  appChainIotaInternal := fun context motive value noneBranch someBranch elementType resultType
    valueTyped noneBranchTyped someBranchTyped =>
    optionMatchSomeIotaSpikeTyped context motive value noneBranch someBranch elementType resultType
      valueTyped noneBranchTyped someBranchTyped
  contentProjectionIotaInternal := fun context firstValue secondValue firstType secondType
    firstTyped secondTyped =>
    fstProjectionIotaSpikeTyped context firstValue secondValue firstType secondType
      firstTyped secondTyped

end FX1Poly.Typed

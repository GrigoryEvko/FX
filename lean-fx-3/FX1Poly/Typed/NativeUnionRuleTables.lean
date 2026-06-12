import FX1Poly.Typed.CellConstructors
import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/NativeUnionRuleTables — NATIVE-36: the native twin rule tables for the
    data-eliminator, n-ary/recursive data-intro, and listElim families (PRE-UNION, imported by the
    union)

The non-recursive data-eliminator rows, the n-ary/recursive data-constructor rows, and the listElim
row currently live in spike-sibling judgments (`DataElimUnionSpike` / `DataIntroNaryUnionSpike` /
`ListElimUnionSpike`) whose rule tables are defined in files that IMPORT `HasTypeNativeUnion` — so the
union cannot import those tables back without a cycle.  The NATIVE-32 precedent resolved exactly this
hazard by defining NATIVE TWINS of the recursive-elim table inside the union file
(`NativeRecursiveElimRule` etc.).  This file follows that pattern but, because these three families
together carry ELEVEN row schemas, hoists the native twins into a dedicated PRE-UNION module that
imports ONLY the bespoke cell/elim engines (none of which imports `HasTypeNativeUnion` — verified:
the only importers of the union are the spike files and the audit shards; the direct zoo INTRO imports
were dropped with the NATIVE-42 embedding-arm retirement — the cell vocabulary arrives through the
elim engines until NATIVE-43 retires those too), and `HasTypeNativeUnion`
imports THIS file.  The arms that reference these tables live on `HasTypeNativeUnion` itself
(additive); the transfers from the spike judgments live in separate post-union files.

## What this ships (the native twins of the spike tables, field-for-field)

  * **Three data-eliminator row schemas** (`NativeTwoBranchMatchElimRule` / `NativePathInductionElimRule`
    / `NativeProjectionElimRule`) with the six rows (boolElim / optionMatch / eitherMatch / idJ / fst /
    snd), their `if`-then-`else` tables, the rfl-diagonal metadata, and the table-inversion `…_cases`
    lemmas (decidable case analysis over the option table — never an elimination over a derivation).
  * **Seven data-intro row schemas** (`NativeRecursiveUnaryDataIntroRule` /
    `NativeRecursiveBinaryDataIntroRule` / `NativePinnedUnaryDataIntroRule` /
    `NativeNullaryFreeTypeDataIntroRule` / `NativeCoproductDataIntroRule` /
    `NativeNonDependentBinaryDataIntroRule` / `NativeReflexiveDataIntroRule`) with their rows, tables,
    metadata, and table-inversion lemmas.
  * **One listElim row schema** (`NativeListElimRule`) with the `gen_listElim` row, table, metadata, the
    cons-ι contractum match, and the table-inversion lemma.

Each native rule's fields are DEFINITIONALLY EQUAL to the corresponding spike rule's fields (same cell
builders), so the spike→union transfers can hand the spike's row cells to the union arms unchanged.

## Zero-axiom

Every table is an `if`-then-`else` over `DecidableEq Generator` (rfl on the diagonal); every
table-inversion lemma is decidable case analysis (`by_cases generator = .gen_X`, `if_pos` / `if_neg`,
`Option.some.inj`, `Option.noConfusion` on the `none` tail) — no `propext`, no derivation elimination.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditNativeWaveUnionResidency.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## Data-eliminator family — shape 1: two-branch match rows (boolElim / optionMatch / eitherMatch) -/

/-- A native two-branch match-eliminator row.  Field-identical to the spike's `TwoBranchMatchElimRule`:
the motive lives under ONE binder (stored), the scrutinee inhabits a type-parameter-indexed inductive
code, and the two branches carry rule-parametric classifiers built from the type parameters and the
result type. -/
structure NativeTwoBranchMatchElimRule where
  /-- The inductive code the scrutinee inhabits, built from the (up to two) type parameters. -/
  scrutineeType : (scope : Nat) → RawTerm scope → RawTerm scope → RawTerm scope
  /-- The eliminator cell: motive (one binder), first branch, second branch, scrutinee. -/
  memberCell : (scope : Nat) → RawTerm (scope + 1) → RawTerm scope → RawTerm scope →
    RawTerm scope → RawTerm scope
  /-- The first branch's classifier, built from the type parameters and the result type. -/
  firstBranchType : (scope : Nat) → RawTerm scope → RawTerm scope → RawTerm scope → RawTerm scope
  /-- The second branch's classifier. -/
  secondBranchType : (scope : Nat) → RawTerm scope → RawTerm scope → RawTerm scope → RawTerm scope

/-- The native `gen_boolElim` row: scrutinee at `boolTypeCell`, both branches at the result type. -/
def boolElimNativeMatchRule : NativeTwoBranchMatchElimRule where
  scrutineeType := fun _ _ _ => boolTypeCell
  memberCell := fun _ motive thenBranch elseBranch scrutinee =>
    boolElimCell motive scrutinee thenBranch elseBranch
  firstBranchType := fun _ _ _ resultType => resultType
  secondBranchType := fun _ _ _ resultType => resultType

/-- The native `gen_optionMatch` row: scrutinee at `option(A)`, None branch at the result type, Some
branch the non-dependent handler `A → C`. -/
def optionMatchNativeMatchRule : NativeTwoBranchMatchElimRule where
  scrutineeType := fun _ typeParamA _ => optionTypeCell typeParamA
  memberCell := fun _ motive noneBranch someBranch scrutinee =>
    optionMatchCell motive noneBranch someBranch scrutinee
  firstBranchType := fun _ _ _ resultType => resultType
  secondBranchType := fun _ typeParamA _ resultType =>
    piTyCodeCell typeParamA (RawTerm.weaken resultType)

/-- The native `gen_eitherMatch` row: scrutinee at `either(A, B)`, both branches the non-dependent
handlers `A → C` / `B → C`. -/
def eitherMatchNativeMatchRule : NativeTwoBranchMatchElimRule where
  scrutineeType := fun _ typeParamA typeParamB => eitherTypeCell typeParamA typeParamB
  memberCell := fun _ motive leftBranch rightBranch scrutinee =>
    eitherMatchCell motive leftBranch rightBranch scrutinee
  firstBranchType := fun _ typeParamA _ resultType =>
    piTyCodeCell typeParamA (RawTerm.weaken resultType)
  secondBranchType := fun _ _ typeParamB resultType =>
    piTyCodeCell typeParamB (RawTerm.weaken resultType)

/-- The native two-branch match table. -/
def nativeTwoBranchMatchRuleOf (generator : Generator) : Option NativeTwoBranchMatchElimRule :=
  if generator = .gen_boolElim then some boolElimNativeMatchRule
  else if generator = .gen_optionMatch then some optionMatchNativeMatchRule
  else if generator = .gen_eitherMatch then some eitherMatchNativeMatchRule
  else none

/-- Table metadata: the native boolElim row is hit (rfl on the diagonal). -/
theorem nativeTwoBranchMatchRuleOf_boolElim :
    nativeTwoBranchMatchRuleOf .gen_boolElim = some boolElimNativeMatchRule := rfl

/-- Table metadata: the native optionMatch row is hit. -/
theorem nativeTwoBranchMatchRuleOf_optionMatch :
    nativeTwoBranchMatchRuleOf .gen_optionMatch = some optionMatchNativeMatchRule := rfl

/-- Table metadata: the native eitherMatch row is hit. -/
theorem nativeTwoBranchMatchRuleOf_eitherMatch :
    nativeTwoBranchMatchRuleOf .gen_eitherMatch = some eitherMatchNativeMatchRule := rfl

/-- **A two-branch match table hit pins one of the three rows.**  Decidable case analysis over the
`if`-then-`else` table on the three diagonal generators (the `none` tail refutes any other generator's
`some` by `Option.noConfusion`).  Zero-axiom: `by_cases` over `DecidableEq Generator`, no `propext`. -/
theorem nativeTwoBranchMatchRuleOf_cases {generator : Generator}
    {rule : NativeTwoBranchMatchElimRule}
    (tableHit : nativeTwoBranchMatchRuleOf generator = some rule) :
    (generator = .gen_boolElim ∧ rule = boolElimNativeMatchRule) ∨
    (generator = .gen_optionMatch ∧ rule = optionMatchNativeMatchRule) ∨
    (generator = .gen_eitherMatch ∧ rule = eitherMatchNativeMatchRule) := by
  unfold nativeTwoBranchMatchRuleOf at tableHit
  by_cases isBoolElim : generator = .gen_boolElim
  · rw [if_pos isBoolElim] at tableHit
    exact Or.inl ⟨isBoolElim, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isBoolElim] at tableHit
    by_cases isOptionMatch : generator = .gen_optionMatch
    · rw [if_pos isOptionMatch] at tableHit
      exact Or.inr (Or.inl ⟨isOptionMatch, (Option.some.inj tableHit).symm⟩)
    · rw [if_neg isOptionMatch] at tableHit
      by_cases isEitherMatch : generator = .gen_eitherMatch
      · rw [if_pos isEitherMatch] at tableHit
        exact Or.inr (Or.inr ⟨isEitherMatch, (Option.some.inj tableHit).symm⟩)
      · rw [if_neg isEitherMatch] at tableHit
        exact absurd tableHit (by intro hit; cases hit)

/-! ## Data-eliminator family — shape 2: path-induction rows (idJ) -/

/-- A native path-induction eliminator row.  Field-identical to the spike's `PathInductionElimRule`:
the motive lives under TWO binders (stored), the witness inhabits a reflexive identity code
`Id(typeCode, endpoint, endpoint)`, and the base case carries the result type (non-dependent J). -/
structure NativePathInductionElimRule where
  /-- The reflexive identity code the witness inhabits, from the type code and shared endpoint. -/
  witnessType : (scope : Nat) → RawTerm scope → RawTerm scope → RawTerm scope
  /-- The eliminator cell: motive (two binders), base case, witness. -/
  memberCell : (scope : Nat) → RawTerm (scope + 2) → RawTerm scope → RawTerm scope → RawTerm scope

/-- The native `gen_idJ` row. -/
def idJNativePathInductionRule : NativePathInductionElimRule where
  witnessType := fun _ typeCode endpoint => idTypeCell typeCode endpoint endpoint
  memberCell := fun _ motive baseCase witness => idJCell motive baseCase witness

/-- The native path-induction table. -/
def nativePathInductionRuleOf (generator : Generator) : Option NativePathInductionElimRule :=
  if generator = .gen_idJ then some idJNativePathInductionRule
  else none

/-- Table metadata: the native idJ row is hit. -/
theorem nativePathInductionRuleOf_idJ :
    nativePathInductionRuleOf .gen_idJ = some idJNativePathInductionRule := rfl

/-- **A path-induction table hit pins the idJ row.**  Decidable case analysis over the single-row
table; the `none` tail refutes any other generator. -/
theorem nativePathInductionRuleOf_cases {generator : Generator}
    {rule : NativePathInductionElimRule}
    (tableHit : nativePathInductionRuleOf generator = some rule) :
    generator = .gen_idJ ∧ rule = idJNativePathInductionRule := by
  unfold nativePathInductionRuleOf at tableHit
  by_cases isIdJ : generator = .gen_idJ
  · rw [if_pos isIdJ] at tableHit
    exact ⟨isIdJ, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isIdJ] at tableHit
    exact absurd tableHit (by intro hit; cases hit)

/-! ## Data-eliminator family — shape 3: projection rows (fst / snd) -/

/-- A native projection eliminator row.  Field-identical to the spike's `ProjectionElimRule`: no
motive, no branches — a single scrutinee inhabiting a product code, the output one component type. -/
structure NativeProjectionElimRule where
  /-- The projection cell, built from the scrutinee pair term. -/
  memberCell : (scope : Nat) → RawTerm scope → RawTerm scope
  /-- The projected component type, selected from the two product components. -/
  projectedType : (scope : Nat) → RawTerm scope → RawTerm scope → RawTerm scope

/-- The native `gen_fst` row: project the first component. -/
def fstNativeProjectionRule : NativeProjectionElimRule where
  memberCell := fun _ pairTerm => fstCell pairTerm
  projectedType := fun _ firstType _ => firstType

/-- The native `gen_snd` row: project the second component. -/
def sndNativeProjectionRule : NativeProjectionElimRule where
  memberCell := fun _ pairTerm => sndCell pairTerm
  projectedType := fun _ _ secondType => secondType

/-- The native projection table. -/
def nativeProjectionRuleOf (generator : Generator) : Option NativeProjectionElimRule :=
  if generator = .gen_fst then some fstNativeProjectionRule
  else if generator = .gen_snd then some sndNativeProjectionRule
  else none

/-- Table metadata: the native fst row is hit. -/
theorem nativeProjectionRuleOf_fst :
    nativeProjectionRuleOf .gen_fst = some fstNativeProjectionRule := rfl

/-- Table metadata: the native snd row is hit. -/
theorem nativeProjectionRuleOf_snd :
    nativeProjectionRuleOf .gen_snd = some sndNativeProjectionRule := rfl

/-- **A projection table hit pins one of the two rows.**  Decidable case analysis over the two
diagonal generators; the `none` tail refutes any other. -/
theorem nativeProjectionRuleOf_cases {generator : Generator} {rule : NativeProjectionElimRule}
    (tableHit : nativeProjectionRuleOf generator = some rule) :
    (generator = .gen_fst ∧ rule = fstNativeProjectionRule) ∨
    (generator = .gen_snd ∧ rule = sndNativeProjectionRule) := by
  unfold nativeProjectionRuleOf at tableHit
  by_cases isFst : generator = .gen_fst
  · rw [if_pos isFst] at tableHit
    exact Or.inl ⟨isFst, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isFst] at tableHit
    by_cases isSnd : generator = .gen_snd
    · rw [if_pos isSnd] at tableHit
      exact Or.inr ⟨isSnd, (Option.some.inj tableHit).symm⟩
    · rw [if_neg isSnd] at tableHit
      exact absurd tableHit (by intro hit; cases hit)

/-! ## Data-intro family — the seven n-ary / recursive row schemas (native twins) -/

/-- A native RECURSIVE-UNARY data-constructor row (`natSucc`): a single SPIKE/UNION-recursive child at
a fixed type code, fixed output code.  Field-identical to `RecursiveUnaryDataIntroRule`. -/
structure NativeRecursiveUnaryDataIntroRule where
  /-- The fixed type code the recursive child must inhabit. -/
  childType : (scope : Nat) → RawTerm scope
  /-- The member cell built from the recursive child. -/
  memberCell : (scope : Nat) → RawTerm scope → RawTerm scope
  /-- The fixed output type code. -/
  outputType : (scope : Nat) → RawTerm scope

/-- The native `gen_natSucc` recursive-unary row. -/
def natSuccNativeRecursiveUnaryRule : NativeRecursiveUnaryDataIntroRule where
  childType := fun _ => natTypeCell
  memberCell := fun _ => natSuccCell
  outputType := fun _ => natTypeCell

/-- The native recursive-unary data-constructor table. -/
def nativeRecursiveUnaryDataIntroRuleOf (generator : Generator) :
    Option NativeRecursiveUnaryDataIntroRule :=
  if generator = .gen_natSucc then some natSuccNativeRecursiveUnaryRule
  else none

/-- Table metadata: the native `natSucc` row is hit (rfl on the diagonal). -/
theorem nativeRecursiveUnaryDataIntroRuleOf_natSucc :
    nativeRecursiveUnaryDataIntroRuleOf .gen_natSucc = some natSuccNativeRecursiveUnaryRule := rfl

/-- **A recursive-unary table hit pins the natSucc row.** -/
theorem nativeRecursiveUnaryDataIntroRuleOf_cases {generator : Generator}
    {rule : NativeRecursiveUnaryDataIntroRule}
    (tableHit : nativeRecursiveUnaryDataIntroRuleOf generator = some rule) :
    generator = .gen_natSucc ∧ rule = natSuccNativeRecursiveUnaryRule := by
  unfold nativeRecursiveUnaryDataIntroRuleOf at tableHit
  by_cases isNatSucc : generator = .gen_natSucc
  · rw [if_pos isNatSucc] at tableHit
    exact ⟨isNatSucc, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isNatSucc] at tableHit
    exact absurd tableHit (by intro hit; cases hit)

/-- A native RECURSIVE-BINARY data-constructor row (`listCons`): a GROWN head at a free element type
plus a UNION-recursive tail at the container code, container-code output.  Field-identical to
`RecursiveBinaryDataIntroRule`. -/
structure NativeRecursiveBinaryDataIntroRule where
  /-- The container type code over the element type, classifying both the tail premise and the output. -/
  containerType : (scope : Nat) → RawTerm scope → RawTerm scope
  /-- The member cell built from the grown head and the recursive tail. -/
  memberCell : (scope : Nat) → RawTerm scope → RawTerm scope → RawTerm scope

/-- The native `gen_listCons` recursive-binary row. -/
def listConsNativeRecursiveBinaryRule : NativeRecursiveBinaryDataIntroRule where
  containerType := fun _ => listTypeCell
  memberCell := fun _ => listConsCell

/-- The native recursive-binary data-constructor table. -/
def nativeRecursiveBinaryDataIntroRuleOf (generator : Generator) :
    Option NativeRecursiveBinaryDataIntroRule :=
  if generator = .gen_listCons then some listConsNativeRecursiveBinaryRule
  else none

/-- Table metadata: the native `listCons` row is hit. -/
theorem nativeRecursiveBinaryDataIntroRuleOf_listCons :
    nativeRecursiveBinaryDataIntroRuleOf .gen_listCons = some listConsNativeRecursiveBinaryRule := rfl

/-- **A recursive-binary table hit pins the listCons row.** -/
theorem nativeRecursiveBinaryDataIntroRuleOf_cases {generator : Generator}
    {rule : NativeRecursiveBinaryDataIntroRule}
    (tableHit : nativeRecursiveBinaryDataIntroRuleOf generator = some rule) :
    generator = .gen_listCons ∧ rule = listConsNativeRecursiveBinaryRule := by
  unfold nativeRecursiveBinaryDataIntroRuleOf at tableHit
  by_cases isListCons : generator = .gen_listCons
  · rw [if_pos isListCons] at tableHit
    exact ⟨isListCons, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isListCons] at tableHit
    exact absurd tableHit (by intro hit; cases hit)

/-- A native PINNED-UNARY data-constructor row (`optionSome`): one GROWN child whose classifier IS the
element type param, the output computed from that param.  Field-identical to
`PinnedUnaryDataIntroRule`. -/
structure NativePinnedUnaryDataIntroRule where
  /-- The member cell built from the grown child. -/
  memberCell : (scope : Nat) → RawTerm scope → RawTerm scope
  /-- The output type code computed from the element type param. -/
  outputType : (scope : Nat) → RawTerm scope → RawTerm scope

/-- The native `gen_optionSome` pinned-unary row. -/
def optionSomeNativePinnedUnaryRule : NativePinnedUnaryDataIntroRule where
  memberCell := fun _ => optionSomeCell
  outputType := fun _ => optionTypeCell

/-- The native pinned-unary data-constructor table. -/
def nativePinnedUnaryDataIntroRuleOf (generator : Generator) :
    Option NativePinnedUnaryDataIntroRule :=
  if generator = .gen_optionSome then some optionSomeNativePinnedUnaryRule
  else none

/-- Table metadata: the native `optionSome` row is hit. -/
theorem nativePinnedUnaryDataIntroRuleOf_optionSome :
    nativePinnedUnaryDataIntroRuleOf .gen_optionSome = some optionSomeNativePinnedUnaryRule := rfl

/-- **A pinned-unary table hit pins the optionSome row.** -/
theorem nativePinnedUnaryDataIntroRuleOf_cases {generator : Generator}
    {rule : NativePinnedUnaryDataIntroRule}
    (tableHit : nativePinnedUnaryDataIntroRuleOf generator = some rule) :
    generator = .gen_optionSome ∧ rule = optionSomeNativePinnedUnaryRule := by
  unfold nativePinnedUnaryDataIntroRuleOf at tableHit
  by_cases isOptionSome : generator = .gen_optionSome
  · rw [if_pos isOptionSome] at tableHit
    exact ⟨isOptionSome, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isOptionSome] at tableHit
    exact absurd tableHit (by intro hit; cases hit)

/-- A native NULLARY-FREE-TYPE data-constructor row (`optionNone`): a CHILDLESS value whose element
type is FREE, a grown type-formedness premise, the container-code output.  Field-identical to
`NullaryFreeTypeDataIntroRule`. -/
structure NativeNullaryFreeTypeDataIntroRule where
  /-- The childless member cell. -/
  memberCell : (scope : Nat) → RawTerm scope
  /-- The container type code over the free element type. -/
  outputType : (scope : Nat) → RawTerm scope → RawTerm scope

/-- The native `gen_optionNone` nullary-free-type row. -/
def optionNoneNativeNullaryFreeTypeRule : NativeNullaryFreeTypeDataIntroRule where
  memberCell := fun _ => optionNoneCell
  outputType := fun _ => optionTypeCell

/-- The native `gen_listNil` nullary-free-type row — the empty list at a FREE
element type, the exact shape twin of `optionNone` with the list container
code (the row that retires the `ofListIntro` embedding's nil half). -/
def listNilNativeNullaryFreeTypeRule : NativeNullaryFreeTypeDataIntroRule where
  memberCell := fun _ => listNilCell
  outputType := fun _ => listTypeCell

/-- The native nullary-free-type data-constructor table. -/
def nativeNullaryFreeTypeDataIntroRuleOf (generator : Generator) :
    Option NativeNullaryFreeTypeDataIntroRule :=
  if generator = .gen_optionNone then some optionNoneNativeNullaryFreeTypeRule
  else if generator = .gen_listNil then some listNilNativeNullaryFreeTypeRule
  else none

/-- Table metadata: the native `optionNone` row is hit. -/
theorem nativeNullaryFreeTypeDataIntroRuleOf_optionNone :
    nativeNullaryFreeTypeDataIntroRuleOf .gen_optionNone = some optionNoneNativeNullaryFreeTypeRule :=
  rfl

/-- Table metadata: the native `listNil` row is hit. -/
theorem nativeNullaryFreeTypeDataIntroRuleOf_listNil :
    nativeNullaryFreeTypeDataIntroRuleOf .gen_listNil = some listNilNativeNullaryFreeTypeRule :=
  rfl

/-- **A nullary-free-type table hit pins the optionNone or the listNil row.** -/
theorem nativeNullaryFreeTypeDataIntroRuleOf_cases {generator : Generator}
    {rule : NativeNullaryFreeTypeDataIntroRule}
    (tableHit : nativeNullaryFreeTypeDataIntroRuleOf generator = some rule) :
    (generator = .gen_optionNone ∧ rule = optionNoneNativeNullaryFreeTypeRule) ∨
    (generator = .gen_listNil ∧ rule = listNilNativeNullaryFreeTypeRule) := by
  unfold nativeNullaryFreeTypeDataIntroRuleOf at tableHit
  by_cases isOptionNone : generator = .gen_optionNone
  · rw [if_pos isOptionNone] at tableHit
    exact Or.inl ⟨isOptionNone, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isOptionNone] at tableHit
    by_cases isListNil : generator = .gen_listNil
    · rw [if_pos isListNil] at tableHit
      exact Or.inr ⟨isListNil, (Option.some.inj tableHit).symm⟩
    · rw [if_neg isListNil] at tableHit
      exact absurd tableHit (by intro hit; cases hit)

/-- A native COPRODUCT data-constructor row (`eitherInl` / `eitherInr`): a GROWN value premise plus a
free-type formedness premise for the un-injected side, the either-code output.  Field-identical to
`CoproductDataIntroRule`. -/
structure NativeCoproductDataIntroRule where
  /-- The injection cell built from the grown value. -/
  injectionCell : (scope : Nat) → RawTerm scope → RawTerm scope
  /-- The output either code, from the pinned value's type and the free other side's type. -/
  outputType : (scope : Nat) → (pinnedType freeType : RawTerm scope) → RawTerm scope

/-- The native `gen_eitherInl` coproduct row: the value pins the LEFT type, the right is free. -/
def eitherInlNativeCoproductRule : NativeCoproductDataIntroRule where
  injectionCell := fun _ => eitherInlCell
  outputType := fun _ pinnedType freeType => eitherTypeCell pinnedType freeType

/-- The native `gen_eitherInr` coproduct row: the value pins the RIGHT type, the left is free. -/
def eitherInrNativeCoproductRule : NativeCoproductDataIntroRule where
  injectionCell := fun _ => eitherInrCell
  outputType := fun _ pinnedType freeType => eitherTypeCell freeType pinnedType

/-- The native coproduct data-constructor table. -/
def nativeCoproductDataIntroRuleOf (generator : Generator) : Option NativeCoproductDataIntroRule :=
  if generator = .gen_eitherInl then some eitherInlNativeCoproductRule
  else if generator = .gen_eitherInr then some eitherInrNativeCoproductRule
  else none

/-- Table metadata: the native `eitherInl` row is hit. -/
theorem nativeCoproductDataIntroRuleOf_eitherInl :
    nativeCoproductDataIntroRuleOf .gen_eitherInl = some eitherInlNativeCoproductRule := rfl

/-- Table metadata: the native `eitherInr` row is hit. -/
theorem nativeCoproductDataIntroRuleOf_eitherInr :
    nativeCoproductDataIntroRuleOf .gen_eitherInr = some eitherInrNativeCoproductRule := rfl

/-- **A coproduct table hit pins one of the two rows.** -/
theorem nativeCoproductDataIntroRuleOf_cases {generator : Generator}
    {rule : NativeCoproductDataIntroRule}
    (tableHit : nativeCoproductDataIntroRuleOf generator = some rule) :
    (generator = .gen_eitherInl ∧ rule = eitherInlNativeCoproductRule) ∨
    (generator = .gen_eitherInr ∧ rule = eitherInrNativeCoproductRule) := by
  unfold nativeCoproductDataIntroRuleOf at tableHit
  by_cases isInl : generator = .gen_eitherInl
  · rw [if_pos isInl] at tableHit
    exact Or.inl ⟨isInl, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isInl] at tableHit
    by_cases isInr : generator = .gen_eitherInr
    · rw [if_pos isInr] at tableHit
      exact Or.inr ⟨isInr, (Option.some.inj tableHit).symm⟩
    · rw [if_neg isInr] at tableHit
      exact absurd tableHit (by intro hit; cases hit)

/-- A native NON-DEPENDENT-BINARY data-constructor row (`pair`): two GROWN children at two independent
type params, the product-code output.  Field-identical to `NonDependentBinaryDataIntroRule`. -/
structure NativeNonDependentBinaryDataIntroRule where
  /-- The member cell built from the two grown children. -/
  memberCell : (scope : Nat) → RawTerm scope → RawTerm scope → RawTerm scope
  /-- The output type code from the two independent type params. -/
  outputType : (scope : Nat) → (firstType secondType : RawTerm scope) → RawTerm scope

/-- The native `gen_pair` non-dependent-binary row. -/
def pairNativeNonDependentBinaryRule : NativeNonDependentBinaryDataIntroRule where
  memberCell := fun _ => pairCell
  outputType := fun _ => productTypeCell

/-- The native non-dependent-binary data-constructor table. -/
def nativeNonDependentBinaryDataIntroRuleOf (generator : Generator) :
    Option NativeNonDependentBinaryDataIntroRule :=
  if generator = .gen_pair then some pairNativeNonDependentBinaryRule
  else none

/-- Table metadata: the native `pair` row is hit. -/
theorem nativeNonDependentBinaryDataIntroRuleOf_pair :
    nativeNonDependentBinaryDataIntroRuleOf .gen_pair = some pairNativeNonDependentBinaryRule := rfl

/-- **A non-dependent-binary table hit pins the pair row.** -/
theorem nativeNonDependentBinaryDataIntroRuleOf_cases {generator : Generator}
    {rule : NativeNonDependentBinaryDataIntroRule}
    (tableHit : nativeNonDependentBinaryDataIntroRuleOf generator = some rule) :
    generator = .gen_pair ∧ rule = pairNativeNonDependentBinaryRule := by
  unfold nativeNonDependentBinaryDataIntroRuleOf at tableHit
  by_cases isPair : generator = .gen_pair
  · rw [if_pos isPair] at tableHit
    exact ⟨isPair, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isPair] at tableHit
    exact absurd tableHit (by intro hit; cases hit)

/-- A native REFLEXIVE data-constructor row (`refl`): a GROWN witness, a TERM-INDEXED output
`Id(A, x, x)` (the witness value appears in the classifier).  Field-identical to
`ReflexiveDataIntroRule`. -/
structure NativeReflexiveDataIntroRule where
  /-- The member cell built from the grown witness. -/
  memberCell : (scope : Nat) → RawTerm scope → RawTerm scope
  /-- The output type code from the witness's type and the witness VALUE. -/
  outputType : (scope : Nat) → (witnessType witnessValue : RawTerm scope) → RawTerm scope

/-- The native `gen_refl` reflexive row. -/
def reflNativeReflexiveRule : NativeReflexiveDataIntroRule where
  memberCell := fun _ => reflCell
  outputType := fun _ witnessType witnessValue => idTypeCell witnessType witnessValue witnessValue

/-- The native reflexive data-constructor table. -/
def nativeReflexiveDataIntroRuleOf (generator : Generator) : Option NativeReflexiveDataIntroRule :=
  if generator = .gen_refl then some reflNativeReflexiveRule
  else none

/-- Table metadata: the native `refl` row is hit. -/
theorem nativeReflexiveDataIntroRuleOf_refl :
    nativeReflexiveDataIntroRuleOf .gen_refl = some reflNativeReflexiveRule := rfl

/-- **A reflexive table hit pins the refl row.** -/
theorem nativeReflexiveDataIntroRuleOf_cases {generator : Generator}
    {rule : NativeReflexiveDataIntroRule}
    (tableHit : nativeReflexiveDataIntroRuleOf generator = some rule) :
    generator = .gen_refl ∧ rule = reflNativeReflexiveRule := by
  unfold nativeReflexiveDataIntroRuleOf at tableHit
  by_cases isRefl : generator = .gen_refl
  · rw [if_pos isRefl] at tableHit
    exact ⟨isRefl, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isRefl] at tableHit
    exact absurd tableHit (by intro hit; cases hit)

/-! ## ListElim family — the app-chain row schema (native twin) -/

/-- A native list-eliminator row.  Field-identical to the spike's `ListElimRule`: the cons branch sits
at SHIFT 0 and the cons-ι contractum is the app-chain `app (app (app cons head) tail)
(listElim motive tail nil cons)` (matching `gen_listElim`'s `binderShifts [1, 0, 0, 0]`). -/
structure NativeListElimRule where
  /-- The list type code the scrutinee must inhabit (`listTypeCell elementType`). -/
  scrutineeType : (scope : Nat) → RawTerm scope → RawTerm scope
  /-- The eliminator cell: motive (one binder), scrutinee, nil branch, cons branch. -/
  memberCell : (scope : Nat) → RawTerm (scope + 1) → RawTerm scope → RawTerm scope →
    RawTerm scope → RawTerm scope
  /-- The cons-ι contractum at a head and a tail: the triple app-chain. -/
  consContractum : (scope : Nat) → RawTerm (scope + 1) → RawTerm scope → RawTerm scope →
    RawTerm scope → RawTerm scope → RawTerm scope

/-- The native `gen_listElim` row. -/
def listElimNativeRule : NativeListElimRule where
  scrutineeType := fun _ elementType => listTypeCell elementType
  memberCell := fun _ motive scrutinee nilBranch consBranch =>
    listElimCell motive scrutinee nilBranch consBranch
  consContractum := fun _ motive nilBranch consBranch headValue tailList =>
    appCell (appCell (appCell consBranch headValue) tailList)
      (listElimCell motive tailList nilBranch consBranch)

/-- The native list-eliminator table. -/
def listElimNativeRuleOf (generator : Generator) : Option NativeListElimRule :=
  if generator = .gen_listElim then some listElimNativeRule
  else none

/-- Table metadata: the native listElim row is hit (rfl on the diagonal). -/
theorem listElimNativeRuleOf_listElim :
    listElimNativeRuleOf .gen_listElim = some listElimNativeRule := rfl

/-- The native cons-ι contractum IS the triple app-chain the Step arm produces (`rfl`). -/
theorem listElimNativeRule_consContractum_eq {scope : Nat} (motive : RawTerm (scope + 1))
    (nilBranch consBranch headValue tailList : RawTerm scope) :
    listElimNativeRule.consContractum scope motive nilBranch consBranch headValue tailList
      = appCell (appCell (appCell consBranch headValue) tailList)
          (listElimCell motive tailList nilBranch consBranch) := rfl

/-- **A listElim table hit pins the listElim row.** -/
theorem listElimNativeRuleOf_cases {generator : Generator} {rule : NativeListElimRule}
    (tableHit : listElimNativeRuleOf generator = some rule) :
    generator = .gen_listElim ∧ rule = listElimNativeRule := by
  unfold listElimNativeRuleOf at tableHit
  by_cases isListElim : generator = .gen_listElim
  · rw [if_pos isListElim] at tableHit
    exact ⟨isListElim, (Option.some.inj tableHit).symm⟩
  · rw [if_neg isListElim] at tableHit
    exact absurd tableHit (by intro hit; cases hit)

end FX1Poly.Typed

import FX1Poly.Typed.CellConstructors
import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.FlatDescTelescope
import FX1Poly.Typed.HasTypeDescWeakening
import FX1Poly.Typed.HasTypeDescSubstitution

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

/-! ## Nullary base-type formation family — the flag-pinned `Type@0(standard)` output table

The non-dependent `[]`-binderShifts base type codes (`boolCode` / `emptyCode` / `natCode` / `unitCode` /
`intervalCode`) form a member of `Type@0(standard)`; the universe flag is FIXED in the table (never a free
parameter), so the formation is flag-deterministic by construction.  A new nullary base type code is ONE
more row.  The `HasTypeNativeUnion.baseTypeFormation` arm reads this table; the cell-stability lemmas below
let the union's rename/substitution metatheory re-fire the arm without an engine round-trip. -/

/-- A formation-rule description for a NULLARY base type-former: the FIXED output universe code (a
function of the scope), the universe flag pinned INSIDE the description.  Pure syntax, strictly
positive. -/
structure BaseTypeRuleDesc where
  outputUniverse : (scope : Nat) → RawTerm scope

/-- The per-generator NULLARY base-type formation table.  Its rows are exactly the childless type-code
formers; `boolCode` / `emptyCode` / `natCode` / `unitCode` / `intervalCode` all form a member of
`Type@0(standard)`. -/
def baseTypeRuleDescOf (generator : Generator) : Option BaseTypeRuleDesc :=
  if generator = .gen_boolCode then
    some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard }
  else if generator = .gen_emptyCode then
    some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard }
  else if generator = .gen_natCode then
    some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard }
  else if generator = .gen_unitCode then
    some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard }
  else if generator = .gen_intervalCode then
    some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard }
  else none

/-- `gen_boolCode` forms a member of `Type@0(standard)` (metadata check, `rfl` on the diagonal). -/
theorem baseTypeRuleDescOf_boolCode :
    baseTypeRuleDescOf .gen_boolCode
      = some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } :=
  rfl

/-- `gen_emptyCode` forms a member of `Type@0(standard)` (metadata check). -/
theorem baseTypeRuleDescOf_emptyCode :
    baseTypeRuleDescOf .gen_emptyCode
      = some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } :=
  rfl

/-- `gen_natCode` forms a member of `Type@0(standard)` (metadata check). -/
theorem baseTypeRuleDescOf_natCode :
    baseTypeRuleDescOf .gen_natCode
      = some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } :=
  rfl

/-- `gen_unitCode` forms a member of `Type@0(standard)` (metadata check). -/
theorem baseTypeRuleDescOf_unitCode :
    baseTypeRuleDescOf .gen_unitCode
      = some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } :=
  rfl

/-- `gen_intervalCode` forms a member of `Type@0(standard)` (metadata check). -/
theorem baseTypeRuleDescOf_intervalCode :
    baseTypeRuleDescOf .gen_intervalCode
      = some { outputUniverse := fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard } :=
  rfl

/-- **A base-type table hit pins one of the five nullary base codes.**  Decidable case analysis over the
`if`-then-`else` table. -/
theorem baseTypeRuleTableHitIsNullaryBaseCode {generator : Generator} {rule : BaseTypeRuleDesc}
    (isBaseType : baseTypeRuleDescOf generator = some rule) :
    generator = .gen_boolCode ∨ generator = .gen_emptyCode ∨ generator = .gen_natCode ∨
      generator = .gen_unitCode ∨ generator = .gen_intervalCode := by
  by_cases isBool : generator = .gen_boolCode
  · exact Or.inl isBool
  · by_cases isEmpty : generator = .gen_emptyCode
    · exact Or.inr (Or.inl isEmpty)
    · by_cases isNat : generator = .gen_natCode
      · exact Or.inr (Or.inr (Or.inl isNat))
      · by_cases isUnit : generator = .gen_unitCode
        · exact Or.inr (Or.inr (Or.inr (Or.inl isUnit)))
        · by_cases isInterval : generator = .gen_intervalCode
          · exact Or.inr (Or.inr (Or.inr (Or.inr isInterval)))
          · exfalso
            dsimp only [baseTypeRuleDescOf] at isBaseType
            rw [if_neg isBool, if_neg isEmpty, if_neg isNat, if_neg isUnit, if_neg isInterval]
              at isBaseType
            contradiction

/-- **A base-type rule's generator is not `gen_var`.**  Needed to reconstruct the abstract nullary
`mkGen` cell under renaming / substitution (`rename_mkGen_of_ne_var` / `subst_mkGen_of_ne_var`). -/
theorem baseTypeRuleImpliesNotVariable {generator : Generator} {rule : BaseTypeRuleDesc}
    (isBaseType : baseTypeRuleDescOf generator = some rule) :
    generator ≠ Generator.gen_var := by
  intro isVar
  subst isVar
  exact absurd isBaseType (by intro hit; cases hit)

/-- **A base-type rule outputs the flag-pinned `Type@0(standard)` universe code.**  Every tabled base
row fixes the flag, so its output is the closed universe cell — the load-bearing fact behind classifier
determinism AND behind the rename / substitution stability below. -/
theorem baseTypeRuleTableOutputIsType0 {generator : Generator} {rule : BaseTypeRuleDesc}
    (isBaseType : baseTypeRuleDescOf generator = some rule) :
    rule.outputUniverse = fun _ => universeCodeCell LevelExpr.lzero UniverseFlag.standard := by
  rcases baseTypeRuleTableHitIsNullaryBaseCode isBaseType with
    isBool | isEmpty | isNat | isUnit | isInterval
  · subst isBool
    rw [← Option.some.inj isBaseType]
  · subst isEmpty
    rw [← Option.some.inj isBaseType]
  · subst isNat
    rw [← Option.some.inj isBaseType]
  · subst isUnit
    rw [← Option.some.inj isBaseType]
  · subst isInterval
    rw [← Option.some.inj isBaseType]

/-- A nullary base rule's output universe is a closed cell, hence renaming-invariant across scopes. -/
theorem baseTypeRuleDescOf_outputRenameStable {generator : Generator} {rule : BaseTypeRuleDesc}
    (isBaseType : baseTypeRuleDescOf generator = some rule)
    {sourceScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope targetScope) :
    RawTerm.rename rawRenaming (rule.outputUniverse sourceScope)
      = rule.outputUniverse targetScope := by
  rw [baseTypeRuleTableOutputIsType0 isBaseType]
  rfl

/-- A nullary base rule's output universe is a closed cell, hence substitution-invariant across scopes. -/
theorem baseTypeRuleDescOf_outputSubstStable {generator : Generator} {rule : BaseTypeRuleDesc}
    (isBaseType : baseTypeRuleDescOf generator = some rule)
    {sourceScope targetScope : Nat}
    (substitution : FX1Poly.Core.RawTermSubst sourceScope targetScope) :
    RawTerm.subst substitution (rule.outputUniverse sourceScope)
      = rule.outputUniverse targetScope := by
  rw [baseTypeRuleTableOutputIsType0 isBaseType]
  rfl

/-! ## Nullary data-constructor introduction family — the closed data type-code output table

The childless data constructors (`boolTrue` / `boolFalse` / `unit` / `interval0` / `interval1` /
`natZero`) introduce a member of a closed data type code (`boolCode` / `unitCode` / `intervalCode` /
`natCode`).  The `HasTypeNativeUnion.dataIntroNullary` arm reads this table. -/

/-- An introduction-rule description for a NULLARY data constructor: the fixed output type-code (a
function of the scope).  Pure syntax, strictly positive. -/
structure DataIntroNullaryRuleDesc where
  outputTypeCode : (scope : Nat) → RawTerm scope

/-- The per-generator NULLARY data-constructor intro table.  Its rows are exactly the childless data
constructors. -/
def dataIntroNullaryRuleDescOf (generator : Generator) : Option DataIntroNullaryRuleDesc :=
  if generator = .gen_boolTrue then some { outputTypeCode := fun _ => boolTypeCell }
  else if generator = .gen_boolFalse then some { outputTypeCode := fun _ => boolTypeCell }
  else if generator = .gen_unit then some { outputTypeCode := fun _ => unitTypeCell }
  else if generator = .gen_interval0 then some { outputTypeCode := fun _ => intervalTypeCell }
  else if generator = .gen_interval1 then some { outputTypeCode := fun _ => intervalTypeCell }
  else if generator = .gen_natZero then some { outputTypeCode := fun _ => natTypeCell }
  else none

/-- `gen_unit` introduces a member of `unitCode` (metadata check, `rfl` on the diagonal). -/
theorem dataIntroNullaryRuleDescOf_unit :
    dataIntroNullaryRuleDescOf .gen_unit
      = some { outputTypeCode := fun _ => unitTypeCell } :=
  rfl

/-- `gen_boolTrue` introduces a member of `boolCode` (metadata check). -/
theorem dataIntroNullaryRuleDescOf_boolTrue :
    dataIntroNullaryRuleDescOf .gen_boolTrue
      = some { outputTypeCode := fun _ => boolTypeCell } := rfl

/-- `gen_natZero` introduces a member of `natCode` (metadata check). -/
theorem dataIntroNullaryRuleDescOf_natZero :
    dataIntroNullaryRuleDescOf .gen_natZero
      = some { outputTypeCode := fun _ => natTypeCell } := rfl

/-- `gen_boolFalse` introduces a member of `boolCode` (metadata check). -/
theorem dataIntroNullaryRuleDescOf_boolFalse :
    dataIntroNullaryRuleDescOf .gen_boolFalse
      = some { outputTypeCode := fun _ => boolTypeCell } := rfl

/-- `gen_interval0` introduces a member of `intervalCode` (metadata check). -/
theorem dataIntroNullaryRuleDescOf_interval0 :
    dataIntroNullaryRuleDescOf .gen_interval0
      = some { outputTypeCode := fun _ => intervalTypeCell } := rfl

/-- `gen_interval1` introduces a member of `intervalCode` (metadata check). -/
theorem dataIntroNullaryRuleDescOf_interval1 :
    dataIntroNullaryRuleDescOf .gen_interval1
      = some { outputTypeCode := fun _ => intervalTypeCell } := rfl

/-- **A nullary data-intro table hit pins one of the six nullary value constructors.**  Decidable case
analysis over the `if`-then-`else` table. -/
theorem dataIntroNullaryRuleTableHitIsValueConstructor {generator : Generator}
    {rule : DataIntroNullaryRuleDesc}
    (isDataIntro : dataIntroNullaryRuleDescOf generator = some rule) :
    generator = .gen_boolTrue ∨ generator = .gen_boolFalse ∨ generator = .gen_unit ∨
      generator = .gen_interval0 ∨ generator = .gen_interval1 ∨ generator = .gen_natZero := by
  by_cases isTrue : generator = .gen_boolTrue
  · exact Or.inl isTrue
  · by_cases isFalse : generator = .gen_boolFalse
    · exact Or.inr (Or.inl isFalse)
    · by_cases isUnit : generator = .gen_unit
      · exact Or.inr (Or.inr (Or.inl isUnit))
      · by_cases isZero : generator = .gen_interval0
        · exact Or.inr (Or.inr (Or.inr (Or.inl isZero)))
        · by_cases isOne : generator = .gen_interval1
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl isOne))))
          · by_cases isNatZero : generator = .gen_natZero
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr isNatZero))))
            · exfalso
              dsimp only [dataIntroNullaryRuleDescOf] at isDataIntro
              rw [if_neg isTrue, if_neg isFalse, if_neg isUnit, if_neg isZero, if_neg isOne,
                if_neg isNatZero] at isDataIntro
              contradiction

/-- **A nullary data-intro rule's generator is not `gen_var`.**  Needed to reconstruct the abstract
nullary `mkGen` cell under renaming / substitution. -/
theorem dataIntroNullaryRuleImpliesNotVariable {generator : Generator}
    {rule : DataIntroNullaryRuleDesc}
    (isDataIntro : dataIntroNullaryRuleDescOf generator = some rule) :
    generator ≠ Generator.gen_var := by
  intro isVar
  subst isVar
  exact absurd isDataIntro (by intro hit; cases hit)

/-- A nullary data-intro rule's output type code is a closed nullary cell, hence renaming-invariant. -/
theorem dataIntroNullaryRuleDescOf_outputRenameStable {generator : Generator}
    {rule : DataIntroNullaryRuleDesc}
    (isDataIntro : dataIntroNullaryRuleDescOf generator = some rule)
    {sourceScope targetScope : Nat}
    (rawRenaming : FX1Poly.Foundation.RawRenaming sourceScope targetScope) :
    RawTerm.rename rawRenaming (rule.outputTypeCode sourceScope)
      = rule.outputTypeCode targetScope := by
  rcases dataIntroNullaryRuleTableHitIsValueConstructor isDataIntro with
    isTrue | isFalse | isUnit | isZero | isOne | isNatZero
  · subst isTrue
    rw [show rule = { outputTypeCode := fun _ => boolTypeCell } from
      (Option.some.inj isDataIntro).symm]
    rfl
  · subst isFalse
    rw [show rule = { outputTypeCode := fun _ => boolTypeCell } from
      (Option.some.inj isDataIntro).symm]
    rfl
  · subst isUnit
    rw [show rule = { outputTypeCode := fun _ => unitTypeCell } from
      (Option.some.inj isDataIntro).symm]
    rfl
  · subst isZero
    rw [show rule = { outputTypeCode := fun _ => intervalTypeCell } from
      (Option.some.inj isDataIntro).symm]
    rfl
  · subst isOne
    rw [show rule = { outputTypeCode := fun _ => intervalTypeCell } from
      (Option.some.inj isDataIntro).symm]
    rfl
  · subst isNatZero
    rw [show rule = { outputTypeCode := fun _ => natTypeCell } from
      (Option.some.inj isDataIntro).symm]
    rfl

/-- A nullary data-intro rule's output type code is a closed nullary cell, hence subst-invariant. -/
theorem dataIntroNullaryRuleDescOf_outputSubstStable {generator : Generator}
    {rule : DataIntroNullaryRuleDesc}
    (isDataIntro : dataIntroNullaryRuleDescOf generator = some rule)
    {sourceScope targetScope : Nat}
    (substitution : FX1Poly.Core.RawTermSubst sourceScope targetScope) :
    RawTerm.subst substitution (rule.outputTypeCode sourceScope)
      = rule.outputTypeCode targetScope := by
  rcases dataIntroNullaryRuleTableHitIsValueConstructor isDataIntro with
    isTrue | isFalse | isUnit | isZero | isOne | isNatZero
  · subst isTrue
    rw [show rule = { outputTypeCode := fun _ => boolTypeCell } from
      (Option.some.inj isDataIntro).symm]
    rfl
  · subst isFalse
    rw [show rule = { outputTypeCode := fun _ => boolTypeCell } from
      (Option.some.inj isDataIntro).symm]
    rfl
  · subst isUnit
    rw [show rule = { outputTypeCode := fun _ => unitTypeCell } from
      (Option.some.inj isDataIntro).symm]
    rfl
  · subst isZero
    rw [show rule = { outputTypeCode := fun _ => intervalTypeCell } from
      (Option.some.inj isDataIntro).symm]
    rfl
  · subst isOne
    rw [show rule = { outputTypeCode := fun _ => intervalTypeCell } from
      (Option.some.inj isDataIntro).symm]
    rfl
  · subst isNatZero
    rw [show rule = { outputTypeCode := fun _ => natTypeCell } from
      (Option.some.inj isDataIntro).symm]
    rfl

/-! ## Flat (non-dependent `[0,0]`) type-former family — the `universeFormerOutput` table

The non-dependent two-child formers `product` / `sum` / `either` / `arrow` / `equiv` all share
`universeFormerOutput` (the former lives at the `lmax` of its children's levels).  The
`HasTypeNativeUnion.flatFormation` arm reads this table; the telescope rename / substitution lemmas below
re-type the flat premise spine so the union metatheory can re-fire the arm engine-free. -/

/-- The per-generator description table for the FLAT (non-dependent) type-code formers. -/
def flatTypingRuleDescOf (generator : Generator) : Option TypingRuleDesc :=
  if generator = .gen_productCode then some { outputType := universeFormerOutput }
  else if generator = .gen_sumCode then some { outputType := universeFormerOutput }
  else if generator = .gen_eitherCode then some { outputType := universeFormerOutput }
  else if generator = .gen_arrowCode then some { outputType := universeFormerOutput }
  else if generator = .gen_equivCode then some { outputType := universeFormerOutput }
  else none

/-- `gen_productCode` is a flat former (metadata check). -/
theorem flatTypingRuleDescOf_productCode :
    flatTypingRuleDescOf .gen_productCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_sumCode` is a flat former (metadata check). -/
theorem flatTypingRuleDescOf_sumCode :
    flatTypingRuleDescOf .gen_sumCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_eitherCode` is a flat former (metadata check). -/
theorem flatTypingRuleDescOf_eitherCode :
    flatTypingRuleDescOf .gen_eitherCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_arrowCode` is a flat former (metadata check). -/
theorem flatTypingRuleDescOf_arrowCode :
    flatTypingRuleDescOf .gen_arrowCode = some { outputType := universeFormerOutput } := rfl

/-- `gen_equivCode` is a flat former (metadata check). -/
theorem flatTypingRuleDescOf_equivCode :
    flatTypingRuleDescOf .gen_equivCode = some { outputType := universeFormerOutput } := rfl

/-- **The flat/cumulative partition.**  `gen_productCode` is NOT a cumulative former. -/
theorem typingRuleDescOf_productCode_none :
    typingRuleDescOf .gen_productCode = none := rfl

/-- **The value/former partition.**  `gen_boolTrue` is a data VALUE — only the
`dataIntroNullaryRuleDescOf` table types it, never the cumulative formation table. -/
theorem typingRuleDescOf_boolTrue_none :
    typingRuleDescOf .gen_boolTrue = none := rfl

/-- **The base-type/cumulative partition.**  `gen_boolCode` is typed by the flag-pinning
`baseTypeRuleDescOf` table; the cumulative formation table deliberately excludes it. -/
theorem typingRuleDescOf_boolCode_none :
    typingRuleDescOf .gen_boolCode = none := rfl

/-- **The base-type/cumulative partition.**  `gen_emptyCode`'s exclusion from the cumulative
table KEEPS consistency (`emptyTypeCellHasNoTyping` / SN-050 stays true at the grown engine). -/
theorem typingRuleDescOf_emptyCode_none :
    typingRuleDescOf .gen_emptyCode = none := rfl

/-- **The base-type/cumulative partition.**  `gen_natCode` is a `baseTypeRuleDescOf` row only. -/
theorem typingRuleDescOf_natCode_none :
    typingRuleDescOf .gen_natCode = none := rfl

/-- **Every flat formation rule outputs a universe code.** -/
theorem flatTypingRuleDescOf_outputIsUniverseFormer {generator : Generator} {rule : TypingRuleDesc}
    (isFlatFormation : flatTypingRuleDescOf generator = some rule) :
    rule.outputType = universeFormerOutput := by
  by_cases isProduct : generator = .gen_productCode
  · subst isProduct
    have hRule : rule = { outputType := universeFormerOutput } := Option.some.inj isFlatFormation.symm
    rw [hRule]
  · by_cases isSum : generator = .gen_sumCode
    · subst isSum
      have hRule : rule = { outputType := universeFormerOutput } := Option.some.inj isFlatFormation.symm
      rw [hRule]
    · by_cases isEither : generator = .gen_eitherCode
      · subst isEither
        have hRule : rule = { outputType := universeFormerOutput } := Option.some.inj isFlatFormation.symm
        rw [hRule]
      · by_cases isArrow : generator = .gen_arrowCode
        · subst isArrow
          have hRule : rule = { outputType := universeFormerOutput } := Option.some.inj isFlatFormation.symm
          rw [hRule]
        · by_cases isEquiv : generator = .gen_equivCode
          · subst isEquiv
            have hRule : rule = { outputType := universeFormerOutput } := Option.some.inj isFlatFormation.symm
            rw [hRule]
          · exfalso
            dsimp only [flatTypingRuleDescOf] at isFlatFormation
            rw [if_neg isProduct, if_neg isSum, if_neg isEither, if_neg isArrow, if_neg isEquiv]
              at isFlatFormation
            contradiction

/-- **A flat formation rule's generator is not `gen_var`.** -/
theorem flatFormationRuleImpliesNotVariable {generator : Generator} {rule : TypingRuleDesc}
    (isFlatFormation : flatTypingRuleDescOf generator = some rule) :
    generator ≠ Generator.gen_var := by
  intro isVariable
  subst isVariable
  dsimp only [flatTypingRuleDescOf] at isFlatFormation
  rw [if_neg (fun isProduct => Generator.noConfusion isProduct),
    if_neg (fun isSum => Generator.noConfusion isSum),
    if_neg (fun isEither => Generator.noConfusion isEither),
    if_neg (fun isArrow => Generator.noConfusion isArrow),
    if_neg (fun isEquiv => Generator.noConfusion isEquiv)] at isFlatFormation
  cases isFlatFormation

/-- **A flat formation rule IS the universe-former rule (full structure).** -/
theorem flatFormationRuleIsUniverseFormer {generator : Generator} {rule : TypingRuleDesc}
    (isFlatFormation : flatTypingRuleDescOf generator = some rule) :
    rule = { outputType := universeFormerOutput } := by
  have outputIsFormer : rule.outputType = universeFormerOutput :=
    flatTypingRuleDescOf_outputIsUniverseFormer isFlatFormation
  cases rule
  rw [← outputIsFormer]

/-- **Flat telescope renaming.**  Re-types the flat premise spine along a context-respecting renaming.
Structural `match`-recursion reusing `HasTypeDesc.renameRespectingContext` on each head child; the flat
`cons` keeps every sibling at the SAME base context, so the renaming stays at the base `rawRenaming`. -/
theorem FlatDescTelescope.renameRespectingTelescope {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag} {binderShifts : List Nat}
    {levels : List LevelExpr} {children : RawTermChildren binderShifts scope}
    (telescope : FlatDescTelescope profile context flag levels children) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (rawRenaming : FX1Poly.Foundation.RawRenaming scope targetScope),
      (∀ index : Fin scope,
        RawTerm.rename rawRenaming (context.lookup index)
          = targetContext.lookup (rawRenaming index)) →
      FlatDescTelescope profile targetContext flag levels
        (RawTermChildren.rename rawRenaming children) :=
  match telescope with
  | .nil => fun targetContext _rawRenaming _contextCondition => FlatDescTelescope.nil
  | .cons head headLevel restLevels rest headTyped restTyped =>
      fun targetContext rawRenaming contextCondition => by
        have renamedHeadTyped :
            HasTypeDesc profile targetContext
              (RawTerm.rename rawRenaming head)
              (universeCodeCell headLevel flag) := by
          have headRenamed :=
            HasTypeDesc.renameRespectingContext headTyped targetContext rawRenaming contextCondition
          rwa [rename_universeCodeCell] at headRenamed
        exact FlatDescTelescope.cons (RawTerm.rename rawRenaming head) headLevel restLevels
          (RawTermChildren.rename rawRenaming rest) renamedHeadTyped
          (FlatDescTelescope.renameRespectingTelescope restTyped targetContext rawRenaming
            contextCondition)

/-- **Flat telescope substitution.**  Re-types the flat premise spine along a substitution whose
substituents are target-typed.  Structural `match`-recursion reusing `HasTypeDesc.substRespectingContext`
on each head child; the flat `cons` keeps every sibling at the SAME base context. -/
theorem FlatDescTelescope.substRespectingTelescope {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag} {binderShifts : List Nat}
    {levels : List LevelExpr} {children : RawTermChildren binderShifts scope}
    (telescope : FlatDescTelescope profile context flag levels children) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : FX1Poly.Core.RawTermSubst scope targetScope),
      (∀ index : Fin scope,
        HasTypeDesc profile targetContext (substitution index)
          (RawTerm.subst substitution (context.lookup index))) →
      FlatDescTelescope profile targetContext flag levels
        (RawTermChildren.subst substitution children) :=
  match telescope with
  | .nil => fun targetContext _substitution _substitutionTyped => FlatDescTelescope.nil
  | .cons head headLevel restLevels rest headTyped restTyped =>
      fun targetContext substitution substitutionTyped => by
        have substHeadTyped :
            HasTypeDesc profile targetContext
              (RawTerm.subst substitution head)
              (universeCodeCell headLevel flag) := by
          have headSubst :=
            HasTypeDesc.substRespectingContext headTyped targetContext substitution substitutionTyped
          rwa [subst_universeCodeCell] at headSubst
        exact FlatDescTelescope.cons (RawTerm.subst substitution head) headLevel restLevels
          (RawTermChildren.subst substitution rest) substHeadTyped
          (FlatDescTelescope.substRespectingTelescope restTyped targetContext substitution
            substitutionTyped)

end FX1Poly.Typed

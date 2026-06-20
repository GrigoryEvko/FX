import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDesc
import FX1Poly.Typed.Engine.RuleTables.UnionRuleTables
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescTermIndexedFormer
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescGradedIntro
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescGeneralElim
import FX1Poly.Typed.Engine.RuleTables.DataIntroSpec

/-! # FX1Poly/Typed/TypingTableBundle — TYTAB-1 brick 1: the static-side bundle

The operational axis already collapsed to data: `Step = StepOver fxBundle`, where one
`RuleTableBundle` (RW-5) carries the ι/η/δ row-lists and one two-constructor relation fires
them.  Adding a reduction rule is adding a table row.

The TYPING axis was unified at the JUDGMENT level (`HasTypeUnion`) but NOT at the TABLE level:
its arms each consult their own per-generator descriptor dispatcher — `typingRuleDescOf`,
`flatTypingRuleDescOf`, `baseTypeRuleDescOf`, `termIndexedFormerDescOf`, `gradedIntroRuleOf`,
`generalElimRuleOf`, `dataIntroNullaryRuleDescOf`, and eleven `native*RuleOf` data-eliminator /
data-introduction lookups.  Nineteen scattered tables, no single value to quantify a generic
metatheorem over.

This module is the static-side mirror of the RW-5 `RuleTableBundle`: ONE `TypingTableBundle`
record carrying all nineteen tables as role-grouped fields, and the canonical instance
`fxTypingBundle` populated from the shipped dispatchers.  Unlike the redex side, the arms do NOT
collapse to one constructor — formation outputs a universe FROM LEVELS, introduction a type-code
FROM TYPE-PARAMETERS, elimination FROM A CHILD; those output arities are the irreducible
formation/introduction/elimination trichotomy of type theory, not accidental duplication.  So the
bundle unifies the TABLES (and the lookup), leaving a fixed role-many arm shapes.

**Brick scope (faithful repackaging, zero behaviour change).**  The record + instance + the
faithfulness certificate that every field is DEFINITIONALLY the shipped dispatcher
(`fxTypingBundle_faithful`).  `HasTypeUnion` is untouched, so there is no cascade and no proof
re-run.  The unified `typingRowsOf` collector and the decidable role-orthogonality certificate
(the static-side `WfIotaTable`) are the next bricks; rebasing the arms to READ the bundle is the
brick after that.

Zero-axiom: a record, a `def` of constants, and `rfl` field projections.  Audit-gated in
`FX1PolyAudit/AuditTypingTableBundle.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core (Generator)

/-- ★ **The typing-table bundle** — the static-side `RuleTableBundle`.  Every per-generator
typing dispatcher the native union consults, gathered into ONE value so a generic metatheorem can
quantify over `bundle : TypingTableBundle` once and instantiate at `fxTypingBundle` with no
regression.  Fields are grouped by typing ROLE (formation / binder / elimination / data
introduction); each is the same `Generator → Option _` shape the shipped table already has. -/
structure TypingTableBundle where
  -- Formation role: output a classifier from the children's universe levels.
  /-- Dependent type-former formation (Π / Σ / list / option / unit codes). -/
  formation : Generator → Option TypingRuleDesc
  /-- Flat (non-cumulative) data-former formation (arrow / product / sum / either / equiv). -/
  flatFormation : Generator → Option TypingRuleDesc
  /-- Nullary base-type formation (bool / empty / nat / unit / interval codes). -/
  baseType : Generator → Option BaseTypeRuleDesc
  /-- Term-indexed former formation (Id / Bridge). -/
  termIndexedFormer : Generator → Option TermIndexedFormerDesc
  -- Binder role: output a type from the binder's type-parameters / eliminated child.
  /-- Graded binder introduction (λ / pathLam) with its usage grade. -/
  gradedIntro : Generator → Option GradedIntroRule
  /-- General elimination (application / pathApp). -/
  generalElim : Generator → Option GeneralElimRule
  -- Elimination role: data eliminators with role-specific premise shapes.
  /-- Recursive eliminator (natElim / natRec). -/
  recursiveElim : Generator → Option NativeRecursiveElimRule
  /-- Two-branch match (boolElim / optionMatch / eitherMatch). -/
  twoBranchMatch : Generator → Option NativeTwoBranchMatchElimRule
  /-- Path induction (idJ). -/
  pathInduction : Generator → Option NativePathInductionElimRule
  /-- Σ-projection (fst / snd). -/
  projection : Generator → Option NativeProjectionElimRule
  /-- List eliminator (listElim). -/
  listElim : Generator → Option NativeListElimRule
  -- Data-introduction role: constructors with role-specific premise shapes.
  /-- Nullary data constructor (boolTrue / boolFalse / unit / interval endpoints). -/
  dataIntroNullary : Generator → Option DataIntroNullaryRuleDesc
  /-- Recursive data constructor (natSucc / listCons) — the unified descriptor that collapsed the two
  per-family recursive-intro arms into one (TYTAB-1 arm collapse). -/
  recursiveDataIntro : Generator → Option RecursiveDataIntroSpec
  /-- Pinned-unary data constructor (optionSome). -/
  pinnedUnaryIntro : Generator → Option NativePinnedUnaryDataIntroRule
  /-- Nullary free-type data constructor (optionNone / listNil). -/
  nullaryFreeTypeIntro : Generator → Option NativeNullaryFreeTypeDataIntroRule
  /-- Coproduct data constructor (eitherInl / eitherInr). -/
  coproductIntro : Generator → Option NativeCoproductDataIntroRule
  /-- Non-dependent binary data constructor (pair). -/
  nonDependentBinaryIntro : Generator → Option NativeNonDependentBinaryDataIntroRule
  /-- Reflexive data constructor (refl). -/
  reflexiveIntro : Generator → Option NativeReflexiveDataIntroRule

/-- ★ **The canonical FX typing-table bundle** — every field is the shipped per-generator
dispatcher.  This is the static-side `fxBundle`: the one value the typing metatheory will be
re-expressed over.  Defining the fields to BE the dispatchers makes faithfulness definitional. -/
def fxTypingBundle : TypingTableBundle where
  formation := typingRuleDescOf
  flatFormation := flatTypingRuleDescOf
  baseType := baseTypeRuleDescOf
  termIndexedFormer := termIndexedFormerDescOf
  gradedIntro := gradedIntroRuleOf
  generalElim := generalElimRuleOf
  recursiveElim := nativeRecursiveElimRuleOf
  twoBranchMatch := nativeTwoBranchMatchRuleOf
  pathInduction := nativePathInductionRuleOf
  projection := nativeProjectionRuleOf
  listElim := listElimNativeRuleOf
  dataIntroNullary := dataIntroNullaryRuleDescOf
  recursiveDataIntro := recursiveDataIntroSpecOf
  pinnedUnaryIntro := nativePinnedUnaryDataIntroRuleOf
  nullaryFreeTypeIntro := nativeNullaryFreeTypeDataIntroRuleOf
  coproductIntro := nativeCoproductDataIntroRuleOf
  nonDependentBinaryIntro := nativeNonDependentBinaryDataIntroRuleOf
  reflexiveIntro := nativeReflexiveDataIntroRuleOf

/-- **The faithfulness certificate.**  Each field of `fxTypingBundle` equals the shipped
dispatcher it bundles.  Inhabiting this is what licenses the next brick to rebase a `HasTypeUnion`
arm from `nativeFooRuleOf gen` to `bundle.foo gen` (instantiated at `fxTypingBundle`) with ZERO
behaviour change — the rewrite is by these equalities, definitional throughout. -/
structure TypingTableBundleFaithful (bundle : TypingTableBundle) : Prop where
  formation_eq : bundle.formation = typingRuleDescOf
  flatFormation_eq : bundle.flatFormation = flatTypingRuleDescOf
  baseType_eq : bundle.baseType = baseTypeRuleDescOf
  termIndexedFormer_eq : bundle.termIndexedFormer = termIndexedFormerDescOf
  gradedIntro_eq : bundle.gradedIntro = gradedIntroRuleOf
  generalElim_eq : bundle.generalElim = generalElimRuleOf
  recursiveElim_eq : bundle.recursiveElim = nativeRecursiveElimRuleOf
  twoBranchMatch_eq : bundle.twoBranchMatch = nativeTwoBranchMatchRuleOf
  pathInduction_eq : bundle.pathInduction = nativePathInductionRuleOf
  projection_eq : bundle.projection = nativeProjectionRuleOf
  listElim_eq : bundle.listElim = listElimNativeRuleOf
  dataIntroNullary_eq : bundle.dataIntroNullary = dataIntroNullaryRuleDescOf
  recursiveDataIntro_eq : bundle.recursiveDataIntro = recursiveDataIntroSpecOf
  pinnedUnaryIntro_eq : bundle.pinnedUnaryIntro = nativePinnedUnaryDataIntroRuleOf
  nullaryFreeTypeIntro_eq : bundle.nullaryFreeTypeIntro = nativeNullaryFreeTypeDataIntroRuleOf
  coproductIntro_eq : bundle.coproductIntro = nativeCoproductDataIntroRuleOf
  nonDependentBinaryIntro_eq : bundle.nonDependentBinaryIntro = nativeNonDependentBinaryDataIntroRuleOf
  reflexiveIntro_eq : bundle.reflexiveIntro = nativeReflexiveDataIntroRuleOf

/-- ★ **`fxTypingBundle` faithfully bundles every shipped typing table.**  All nineteen field
projections are `rfl`, certifying the bundle is a pure repackaging of the existing dispatchers. -/
theorem fxTypingBundle_faithful : TypingTableBundleFaithful fxTypingBundle where
  formation_eq := rfl
  flatFormation_eq := rfl
  baseType_eq := rfl
  termIndexedFormer_eq := rfl
  gradedIntro_eq := rfl
  generalElim_eq := rfl
  recursiveElim_eq := rfl
  twoBranchMatch_eq := rfl
  pathInduction_eq := rfl
  projection_eq := rfl
  listElim_eq := rfl
  dataIntroNullary_eq := rfl
  recursiveDataIntro_eq := rfl
  pinnedUnaryIntro_eq := rfl
  nullaryFreeTypeIntro_eq := rfl
  coproductIntro_eq := rfl
  nonDependentBinaryIntro_eq := rfl
  reflexiveIntro_eq := rfl

end FX1Poly.Typed

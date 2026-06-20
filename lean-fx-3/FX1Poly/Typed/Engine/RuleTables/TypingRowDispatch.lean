import FX1Poly.Typed.Engine.RuleTables.TypingTableBundle

/-! # FX1Poly/Typed/TypingRowDispatch — TYTAB-1 brick 2: the type concept as ONE lookup

Brick 1 gathered the nineteen typing dispatchers into a `TypingTableBundle`.  This brick collapses
the nineteen separate `Generator → Option _` lookups into ONE: a single tagged union `TypingRow`
carrying whichever rule a generator's typing role supplies, and `typingRowsOf bundle generator` —
the list of all rows that fire.  This is the static-side analogue of "reduction is one `StepOver`
relation over one bundle": the TYPE of a generator-headed cell pipes through ONE function of the
generator, and a new type former is a new row in the bundle, surfacing through the same lookup with
no new dispatcher.

`typingRowsOf` is generic over `bundle : TypingTableBundle`, so a `ProfileExtension`'s bundle gets
the unified lookup for free — whatever types one adds flow through the same `.type` pipe.

**Why a list, not an `Option`.**  Soundness of "exactly one row fires" (role-orthogonality) is the
decidable certificate of the NEXT brick (the static-side `WfIotaTable`).  Returning the list of
firing rows keeps THIS brick free of that assumption: faithfulness is stated structurally (a field
firing puts its row in the list, and the canonical generators compute to a singleton), with no
orthogonality precondition.  The unique-row `Option` view is the orthogonality corollary.

Zero-axiom: a tagged union, a structural `consMapped` fold, and `List.Mem` constructor reasoning
(NOT `mem_append`/`mem_map` iff lemmas, which would leak `propext`).  Audit-gated in
`FX1PolyAudit/AuditTypingRowDispatch.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core (Generator)

/-- ★ **The unified typing row** — the type-level semantics of ONE generator, whichever role it
plays.  Nineteen constructors, one per bundle field; a generator's row (when it has one) IS its
complete table-driven typing rule, read through a single lookup.  A new type former adds a
constructor here only if it needs a genuinely new premise shape; the existing roles absorb most
additions as new bundle rows under the same constructor. -/
inductive TypingRow where
  /-- Dependent type-former formation row (Π / Σ / list / option / unit). -/
  | formation (rule : TypingRuleDesc)
  /-- Flat data-former formation row (arrow / product / sum / either / equiv). -/
  | flatFormation (rule : TypingRuleDesc)
  /-- Nullary base-type formation row (bool / empty / nat / unit / interval). -/
  | baseType (rule : BaseTypeRuleDesc)
  /-- Term-indexed former formation row (Id / Bridge). -/
  | termIndexedFormer (rule : TermIndexedFormerDesc)
  /-- Graded binder-introduction row (λ / pathLam). -/
  | gradedIntro (rule : GradedIntroRule)
  /-- General elimination row (application / pathApp). -/
  | generalElim (rule : GeneralElimRule)
  /-- Recursive eliminator row (natElim / natRec). -/
  | recursiveElim (rule : NativeRecursiveElimRule)
  /-- Two-branch match row (boolElim / optionMatch / eitherMatch). -/
  | twoBranchMatch (rule : NativeTwoBranchMatchElimRule)
  /-- Path-induction row (idJ). -/
  | pathInduction (rule : NativePathInductionElimRule)
  /-- Σ-projection row (fst / snd). -/
  | projection (rule : NativeProjectionElimRule)
  /-- List eliminator row (listElim). -/
  | listElim (rule : NativeListElimRule)
  /-- Nullary data-constructor row (boolTrue / boolFalse / unit / interval endpoints). -/
  | dataIntroNullary (rule : DataIntroNullaryRuleDesc)
  /-- Recursive data-constructor row (natSucc / listCons) — unified (TYTAB-1 arm collapse). -/
  | recursiveDataIntro (spec : RecursiveDataIntroSpec)
  /-- Grown data-constructor row (optionSome / optionNone / listNil / either / pair / refl) — the
  unified fixed-slot grown intro (TYTAB-1 arm collapse). -/
  | grownDataIntro (spec : GrownDataIntroSpec)

/-- Prepend the row a single field contributes: `some rule` tagged into `TypingRow`, or nothing.
The structural cons (no `Option.toList`/`map`/`++`) keeps membership reasoning on `List.Mem`
constructors, away from the `propext`-leaking iff lemmas. -/
def consMapped {payload : Type} (tag : payload → TypingRow)
    (slot : Option payload) (rest : List TypingRow) : List TypingRow :=
  match slot with
  | some value => tag value :: rest
  | none => rest

/-- A firing field contributes its row at the head of its segment. -/
theorem consMapped_mem_head {payload : Type} {tag : payload → TypingRow}
    {slot : Option payload} {value : payload} {rest : List TypingRow}
    (fires : slot = some value) :
    tag value ∈ consMapped tag slot rest := by
  subst fires
  exact List.Mem.head rest

/-- Membership in the tail survives the segment, whether or not the segment's field fires. -/
theorem consMapped_mem_tail {payload : Type} {tag : payload → TypingRow}
    {slot : Option payload} {rest : List TypingRow} {row : TypingRow}
    (inRest : row ∈ rest) :
    row ∈ consMapped tag slot rest := by
  cases slot with
  | none => exact inRest
  | some value => exact List.Mem.tail _ inRest

/-- ★ **The single typing lookup** — every row a generator fires across all nineteen tables, in
role order.  With role-orthogonality (the next brick) this list has length ≤ 1, giving the unique
`TypingRow` of the generator; here it is the honest collection, assumption-free. -/
def typingRowsOf (bundle : TypingTableBundle) (generator : Generator) : List TypingRow :=
  consMapped TypingRow.formation (bundle.formation generator) <|
  consMapped TypingRow.flatFormation (bundle.flatFormation generator) <|
  consMapped TypingRow.baseType (bundle.baseType generator) <|
  consMapped TypingRow.termIndexedFormer (bundle.termIndexedFormer generator) <|
  consMapped TypingRow.gradedIntro (bundle.gradedIntro generator) <|
  consMapped TypingRow.generalElim (bundle.generalElim generator) <|
  consMapped TypingRow.recursiveElim (bundle.recursiveElim generator) <|
  consMapped TypingRow.twoBranchMatch (bundle.twoBranchMatch generator) <|
  consMapped TypingRow.pathInduction (bundle.pathInduction generator) <|
  consMapped TypingRow.projection (bundle.projection generator) <|
  consMapped TypingRow.listElim (bundle.listElim generator) <|
  consMapped TypingRow.dataIntroNullary (bundle.dataIntroNullary generator) <|
  consMapped TypingRow.recursiveDataIntro (bundle.recursiveDataIntro generator) <|
  consMapped TypingRow.grownDataIntro (bundle.grownDataIntro generator) []

/-! ## Faithfulness — every firing field surfaces its row through the single lookup

One forward theorem per role: a field firing puts its tagged row in `typingRowsOf`.  Each proof
navigates the segment chain count-free — try firing this segment's head, else peel a tail, repeat —
so the depth is found automatically and no row's position is hand-counted.  No orthogonality
assumption, generic over the bundle. -/

/-- The count-free navigator: peel tails until the firing segment, then fire its head.  Only the two
`consMapped` membership lemmas are used, so the search is `propext`-clean. -/
macro "navigateToRow " fires:term : tactic =>
  `(tactic| (dsimp only [typingRowsOf];
             repeat first | exact consMapped_mem_head $fires | apply consMapped_mem_tail))

theorem typingRowsOf_mem_formation {bundle : TypingTableBundle} {generator : Generator}
    {rule : TypingRuleDesc} (fires : bundle.formation generator = some rule) :
    TypingRow.formation rule ∈ typingRowsOf bundle generator := by
  navigateToRow fires

theorem typingRowsOf_mem_flatFormation {bundle : TypingTableBundle} {generator : Generator}
    {rule : TypingRuleDesc} (fires : bundle.flatFormation generator = some rule) :
    TypingRow.flatFormation rule ∈ typingRowsOf bundle generator := by
  navigateToRow fires

theorem typingRowsOf_mem_baseType {bundle : TypingTableBundle} {generator : Generator}
    {rule : BaseTypeRuleDesc} (fires : bundle.baseType generator = some rule) :
    TypingRow.baseType rule ∈ typingRowsOf bundle generator := by
  navigateToRow fires

theorem typingRowsOf_mem_termIndexedFormer {bundle : TypingTableBundle} {generator : Generator}
    {rule : TermIndexedFormerDesc} (fires : bundle.termIndexedFormer generator = some rule) :
    TypingRow.termIndexedFormer rule ∈ typingRowsOf bundle generator := by
  navigateToRow fires

theorem typingRowsOf_mem_gradedIntro {bundle : TypingTableBundle} {generator : Generator}
    {rule : GradedIntroRule} (fires : bundle.gradedIntro generator = some rule) :
    TypingRow.gradedIntro rule ∈ typingRowsOf bundle generator := by
  navigateToRow fires

theorem typingRowsOf_mem_generalElim {bundle : TypingTableBundle} {generator : Generator}
    {rule : GeneralElimRule} (fires : bundle.generalElim generator = some rule) :
    TypingRow.generalElim rule ∈ typingRowsOf bundle generator := by
  navigateToRow fires

theorem typingRowsOf_mem_recursiveElim {bundle : TypingTableBundle} {generator : Generator}
    {rule : NativeRecursiveElimRule} (fires : bundle.recursiveElim generator = some rule) :
    TypingRow.recursiveElim rule ∈ typingRowsOf bundle generator := by
  navigateToRow fires

theorem typingRowsOf_mem_twoBranchMatch {bundle : TypingTableBundle} {generator : Generator}
    {rule : NativeTwoBranchMatchElimRule} (fires : bundle.twoBranchMatch generator = some rule) :
    TypingRow.twoBranchMatch rule ∈ typingRowsOf bundle generator := by
  navigateToRow fires

theorem typingRowsOf_mem_pathInduction {bundle : TypingTableBundle} {generator : Generator}
    {rule : NativePathInductionElimRule} (fires : bundle.pathInduction generator = some rule) :
    TypingRow.pathInduction rule ∈ typingRowsOf bundle generator := by
  navigateToRow fires

theorem typingRowsOf_mem_projection {bundle : TypingTableBundle} {generator : Generator}
    {rule : NativeProjectionElimRule} (fires : bundle.projection generator = some rule) :
    TypingRow.projection rule ∈ typingRowsOf bundle generator := by
  navigateToRow fires

theorem typingRowsOf_mem_listElim {bundle : TypingTableBundle} {generator : Generator}
    {rule : NativeListElimRule} (fires : bundle.listElim generator = some rule) :
    TypingRow.listElim rule ∈ typingRowsOf bundle generator := by
  navigateToRow fires

theorem typingRowsOf_mem_dataIntroNullary {bundle : TypingTableBundle} {generator : Generator}
    {rule : DataIntroNullaryRuleDesc} (fires : bundle.dataIntroNullary generator = some rule) :
    TypingRow.dataIntroNullary rule ∈ typingRowsOf bundle generator := by
  navigateToRow fires

theorem typingRowsOf_mem_recursiveDataIntro {bundle : TypingTableBundle} {generator : Generator}
    {spec : RecursiveDataIntroSpec}
    (fires : bundle.recursiveDataIntro generator = some spec) :
    TypingRow.recursiveDataIntro spec ∈ typingRowsOf bundle generator := by
  navigateToRow fires

theorem typingRowsOf_mem_grownDataIntro {bundle : TypingTableBundle} {generator : Generator}
    {spec : GrownDataIntroSpec} (fires : bundle.grownDataIntro generator = some spec) :
    TypingRow.grownDataIntro spec ∈ typingRowsOf bundle generator := by
  navigateToRow fires

/-! ## The lookup computes — canonical generators pipe their type row through one call

`rfl`-level demonstrations that `typingRowsOf fxTypingBundle` returns exactly the singleton row of a
canonical former / constructor / eliminator, and the empty list for a generator with no typing rule.
These give both directions of faithfulness computationally for the canonical heads. -/

/-- The λ generator's single row is its graded-introduction rule. -/
theorem typingRowsOf_lam_singleton :
    typingRowsOf fxTypingBundle .gen_lam = [TypingRow.gradedIntro lamGradedIntroRule] := rfl

/-- The application generator's single row is its general-elimination rule. -/
theorem typingRowsOf_app_singleton :
    typingRowsOf fxTypingBundle .gen_app = [TypingRow.generalElim appGeneralElimRule] := rfl

/-- The Π-former generator's single row is its formation rule. -/
theorem typingRowsOf_piTyCode_singleton :
    typingRowsOf fxTypingBundle .gen_piTyCode
      = [TypingRow.formation { outputType := universeFormerOutput }] := rfl

/-- A generator with no typing rule yields the empty list — nothing pipes through. -/
theorem typingRowsOf_var_empty : typingRowsOf fxTypingBundle .gen_var = [] := rfl

end FX1Poly.Typed

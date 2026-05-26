import LeanFX2.Foundation.PolyCell.Core.GeneratorCore
import LeanFX2.Foundation.PolyCell.Core.CellSort

/-! # Foundation/PolyCell/Core/GeneratorMetadataV2 — sort + child metadata for v2

This file ships the v2 generator metadata layer on top of `GeneratorCore`'s
74-summand `Generator` enum.  Three deliverables (tasks V2-L1.1 / V2-L1.2 /
V2-L1.3):

* `Generator.cellSort : Generator → CellSort` — the 74-arm output-sort table.
  Each generator's result inhabits exactly one sort from the `CellSort` enum;
  this is FX's structural typing discipline at the generator level.  Adding a
  feature is one new arm here (plus the matching `SupportedGeneratorV2` arm in
  the admission layer), never a new `PolyCellV2` constructor.

* `Generator.childSpecs : Generator → List ChildSpecV2` — the 74-arm
  child-spec table.  Each generator declares the expected `(cellSort,
  cellDimension, scopeShift)` of every child position.  Length equals
  `Generator.arity`; `scopeShift` entries equal `Generator.binderShifts`.

* `Generator.childSpecs_scopeShifts_eq_binderShifts` — the coherence lemma
  tying the two metadata views.  Mechanically `cases g <;> rfl` since both
  tables are defined by structural enumeration over the same enum.

The structure `ChildSpecV2` is a v2-pure parallel to v1's
`GeneratorSpec.ChildSpec`: same fields, but living in this file so the v2
layer has no transitive dependency on `PolyTerm.lean` (the v1 dim-indexed
inductive).  At Stage 6 (v1 deletion + V2 suffix drop) the structure will be
renamed to `ChildSpec`.

Imports: `GeneratorCore` (for `Generator` + `arity` + `binderShifts`) and
`CellSort` (for the sort vocabulary).  No `PolyTerm`, no v1 metadata. -/

namespace LeanFX2.Foundation.PolyCell.Core

/-- One expected child position of a v2 generator.

Parallel to v1 `ChildSpec` but carrying no dependency on the v1 dim-indexed
`PolyTerm` inductive.  Three fields:

* `cellSort` — which sort the child must inhabit (term / type / context /
  mode / effect / grade / protocol).
* `cellDimension` — the child's dimension (current v2 generators all produce
  dim-0 children; positive-dim children appear only at the `RuleSpec` /
  `generatingCell` layer).
* `scopeShift` — the de Bruijn scope offset relative to the parent.  A
  lambda body's child has `scopeShift = 1` (one fresh binder); a pi-type
  codomain's child has `scopeShift = 1` (one fresh type binder); all other
  current v2 generators have `scopeShift = 0` per the `Generator.binderShifts`
  table.

Carrier-free by construction: this struct doesn't store a cell, it only
describes what the certifier should expect at this child position. -/
structure ChildSpecV2 where
  cellSort : CellSort
  cellDimension : Nat
  scopeShift : Nat
  deriving DecidableEq

namespace ChildSpecV2

/-- A child at the parent scope with dimension zero, any sort. -/
@[reducible] def sameScopeDimZero (sort : CellSort) : ChildSpecV2 where
  cellSort := sort
  cellDimension := 0
  scopeShift := 0

/-- A child under exactly one new binder, dimension zero. -/
@[reducible] def underOneBinderDimZero (sort : CellSort) : ChildSpecV2 where
  cellSort := sort
  cellDimension := 0
  scopeShift := 1

/-- Same-scope term child (dim 0, scope shift 0). -/
@[reducible] def termSameScope : ChildSpecV2 := sameScopeDimZero .term

/-- Term child under one fresh binder (dim 0, scope shift 1). -/
@[reducible] def termUnderBinder : ChildSpecV2 := underOneBinderDimZero .term

/-- Same-scope type child (dim 0, scope shift 0). -/
@[reducible] def typeSameScope : ChildSpecV2 := sameScopeDimZero .type

/-- Type child under one fresh binder (dim 0, scope shift 1). -/
@[reducible] def typeUnderBinder : ChildSpecV2 := underOneBinderDimZero .type

end ChildSpecV2

/-- Output sort of each v2 generator.  74 arms, one per `Generator` ctor.

Classification rationale:

* Most generators are TERM constructors: they build runtime values.  This
  covers `var`, `lam`, `app`, all data-type intro/elim families (bool, nat,
  list, option, either), identity-type witnesses, modal operations, cubical
  values + operations, observational equality witnesses, strict identity,
  refinement intro/elim, record intro/projection, codata, sessions, effects,
  and the composition vocabulary (`uaToEquiv`, `equivApply`, `pathCompose`,
  etc.).

* TYPE-CODE generators produce reified type values whose cellSort is `.type`:
  `universeCode`, `arrowCode`, `piTyCode`, `sigmaTyCode`, `productCode`,
  `sumCode`, `listCode`, `optionCode`, `eitherCode`, `idCode`, `equivCode`,
  and the cumulativity marker `cumulUpMarker` which lifts a type code to a
  higher universe.

No generator currently produces a `.context`, `.mode`, `.effect`, `.grade`,
or `.protocol` cell directly — those sorts will populate when the
corresponding RawTerm fragments are folded into v2 (Stage 1 extensions
beyond term/type). -/
def Generator.cellSort : Generator → CellSort
  -- Variable + unit
  | .gen_var          => .term
  | .gen_unit         => .term
  -- Function intro/elim
  | .gen_lam          => .term
  | .gen_app          => .term
  -- Pair intro/elim
  | .gen_pair         => .term
  | .gen_fst          => .term
  | .gen_snd          => .term
  -- Booleans
  | .gen_boolTrue     => .term
  | .gen_boolFalse    => .term
  | .gen_boolElim     => .term
  -- Naturals
  | .gen_natZero      => .term
  | .gen_natSucc      => .term
  | .gen_natElim      => .term
  | .gen_natRec       => .term
  -- Lists
  | .gen_listNil      => .term
  | .gen_listCons     => .term
  | .gen_listElim     => .term
  -- Options
  | .gen_optionNone   => .term
  | .gen_optionSome   => .term
  | .gen_optionMatch  => .term
  -- Eithers
  | .gen_eitherInl    => .term
  | .gen_eitherInr    => .term
  | .gen_eitherMatch  => .term
  -- Identity-type witnesses + eliminator
  | .gen_refl         => .term
  | .gen_idJ          => .term
  -- Modal intro/elim/subsume — all term-level
  | .gen_modIntro     => .term
  | .gen_modElim      => .term
  | .gen_subsume      => .term
  -- Cubical interval endpoints + lattice ops
  | .gen_interval0    => .term
  | .gen_interval1    => .term
  | .gen_intervalOpp  => .term
  | .gen_intervalMeet => .term
  | .gen_intervalJoin => .term
  -- Cubical path
  | .gen_pathLam      => .term
  | .gen_pathApp      => .term
  -- Cubical glue + transport + composition
  | .gen_glueIntro    => .term
  | .gen_glueElim     => .term
  | .gen_transp       => .term
  | .gen_hcomp        => .term
  -- Observational equality witnesses
  | .gen_oeqRefl      => .term
  | .gen_oeqJ         => .term
  | .gen_oeqFunext    => .term
  -- Strict identity
  | .gen_idStrictRefl => .term
  | .gen_idStrictRec  => .term
  -- Type equivalence
  | .gen_equivIntro   => .term
  | .gen_equivApp     => .term
  -- Refinement intro/elim
  | .gen_refineIntro  => .term
  | .gen_refineElim   => .term
  -- Record intro/projection
  | .gen_recordIntro  => .term
  | .gen_recordProj   => .term
  -- Codata
  | .gen_codataUnfold => .term
  | .gen_codataDest   => .term
  -- Sessions
  | .gen_sessionSend  => .term
  | .gen_sessionRecv  => .term
  -- Effects
  | .gen_effectPerform => .term
  -- Universe code — a type code (output sort .type)
  | .gen_universeCode => .type
  -- Per-shape type codes (atom-shape)
  | .gen_arrowCode    => .type
  -- Per-shape type codes (binder-shape)
  | .gen_piTyCode     => .type
  | .gen_sigmaTyCode  => .type
  -- More atom-shape codes
  | .gen_productCode  => .type
  | .gen_sumCode      => .type
  | .gen_listCode     => .type
  | .gen_optionCode   => .type
  | .gen_eitherCode   => .type
  | .gen_idCode       => .type
  | .gen_equivCode    => .type
  -- Cumulativity marker on a type code
  | .gen_cumulUpMarker => .type
  -- Univalence-to-equiv vocabulary — term-level operations
  | .gen_uaToEquiv    => .term
  | .gen_equivApply   => .term
  -- Composition vocabulary — term-level
  | .gen_pathCompose  => .term
  | .gen_idToEquiv    => .term
  | .gen_oeqTrans     => .term
  | .gen_equivCompose => .term
  -- Cubical fill — term-level
  | .gen_transpFill   => .term

/-- Expected child positions for each v2 generator.  74 arms, one per
`Generator` ctor.

Two invariants tie this table to `GeneratorCore.lean`:

1. `(childSpecs g).length = arity g` — proved by `cases g <;> rfl`.
2. `(childSpecs g).map (·.scopeShift) = binderShifts g` — proved as
   `Generator.childSpecs_scopeShifts_eq_binderShifts` below, the load-bearing
   coherence lemma.

Sort classification of children:

* Term-producing generators with structural children: every child is a term
  (function/argument, predecessor, scrutinee + branches, head + tail,
  optional value, etc.).  Lambda's body is a term under one binder; path
  lambda's body is a term under one interval binder.

* Type-code generators with structural children: every child is a type code
  (domain + codomain for arrow/pi/sigma; element type for list/option;
  left/right for product/sum/either/equiv).  Two exceptions:

  - `gen_idCode` (arity 3) has children `[type, term, term]` — a type code
    for the carrier type plus two terms of that type whose equality is
    asserted.

  - `gen_transpFill` (arity 3) has children `[type, term, term]` — a type
    code (the path-type to transport along) plus the current interval point
    and the source term.

The scope-shift entries match `binderShifts` arm-for-arm: `gen_lam` and
`gen_pathLam` have a `1`-shifted body; `gen_piTyCode` and `gen_sigmaTyCode`
have a `1`-shifted codomain; everything else uses `0`. -/
def Generator.childSpecs : Generator → List ChildSpecV2
  -- Variable + unit
  | .gen_var          => []
  | .gen_unit         => []
  -- Function
  | .gen_lam          => [ChildSpecV2.termUnderBinder]
  | .gen_app          => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Pair
  | .gen_pair         => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_fst          => [ChildSpecV2.termSameScope]
  | .gen_snd          => [ChildSpecV2.termSameScope]
  -- Booleans
  | .gen_boolTrue     => []
  | .gen_boolFalse    => []
  | .gen_boolElim     =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- Naturals
  | .gen_natZero      => []
  | .gen_natSucc      => [ChildSpecV2.termSameScope]
  | .gen_natElim      =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  | .gen_natRec       =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- Lists
  | .gen_listNil      => []
  | .gen_listCons     => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_listElim     =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- Options
  | .gen_optionNone   => []
  | .gen_optionSome   => [ChildSpecV2.termSameScope]
  | .gen_optionMatch  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- Eithers
  | .gen_eitherInl    => [ChildSpecV2.termSameScope]
  | .gen_eitherInr    => [ChildSpecV2.termSameScope]
  | .gen_eitherMatch  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- Identity-type witnesses + eliminator
  | .gen_refl         => [ChildSpecV2.termSameScope]
  | .gen_idJ          => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Modal
  | .gen_modIntro     => [ChildSpecV2.termSameScope]
  | .gen_modElim      => [ChildSpecV2.termSameScope]
  | .gen_subsume      => [ChildSpecV2.termSameScope]
  -- Cubical interval
  | .gen_interval0    => []
  | .gen_interval1    => []
  | .gen_intervalOpp  => [ChildSpecV2.termSameScope]
  | .gen_intervalMeet =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_intervalJoin =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Cubical path
  | .gen_pathLam      => [ChildSpecV2.termUnderBinder]
  | .gen_pathApp      => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Cubical glue / transport / composition
  | .gen_glueIntro    => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_glueElim     => [ChildSpecV2.termSameScope]
  | .gen_transp       => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_hcomp        => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Observational equality witnesses
  | .gen_oeqRefl      => [ChildSpecV2.termSameScope]
  | .gen_oeqJ         => [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_oeqFunext    => [ChildSpecV2.termSameScope]
  -- Strict identity
  | .gen_idStrictRefl => [ChildSpecV2.termSameScope]
  | .gen_idStrictRec  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Type equivalence
  | .gen_equivIntro   =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_equivApp     =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Refinement intro/elim
  | .gen_refineIntro  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_refineElim   => [ChildSpecV2.termSameScope]
  -- Record intro/projection
  | .gen_recordIntro  => [ChildSpecV2.termSameScope]
  | .gen_recordProj   => [ChildSpecV2.termSameScope]
  -- Codata
  | .gen_codataUnfold =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_codataDest   => [ChildSpecV2.termSameScope]
  -- Sessions
  | .gen_sessionSend  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_sessionRecv  => [ChildSpecV2.termSameScope]
  -- Effects
  | .gen_effectPerform =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Universe code (Nat payload, no children)
  | .gen_universeCode => []
  -- Per-shape type codes (atom-shape)
  | .gen_arrowCode    =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeSameScope]
  -- Per-shape type codes (binder-shape: codomain at scope + 1)
  | .gen_piTyCode     =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeUnderBinder]
  | .gen_sigmaTyCode  =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeUnderBinder]
  -- More atom-shape codes
  | .gen_productCode  =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeSameScope]
  | .gen_sumCode      =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeSameScope]
  | .gen_listCode     => [ChildSpecV2.typeSameScope]
  | .gen_optionCode   => [ChildSpecV2.typeSameScope]
  | .gen_eitherCode   =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeSameScope]
  -- Identity type code: carrier-type, leftRaw, rightRaw
  | .gen_idCode       =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]
  -- Equivalence type code: two carrier types
  | .gen_equivCode    =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.typeSameScope]
  -- Cumulativity marker: one inner type code
  | .gen_cumulUpMarker => [ChildSpecV2.typeSameScope]
  -- Univalence-to-equiv vocabulary
  | .gen_uaToEquiv    => [ChildSpecV2.termSameScope]
  | .gen_equivApply   =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Composition vocabulary
  | .gen_pathCompose  =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_idToEquiv    => [ChildSpecV2.termSameScope]
  | .gen_oeqTrans     =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  | .gen_equivCompose =>
    [ChildSpecV2.termSameScope, ChildSpecV2.termSameScope]
  -- Cubical fill: pathTy + currentInterval + source
  | .gen_transpFill   =>
    [ChildSpecV2.typeSameScope, ChildSpecV2.termSameScope,
     ChildSpecV2.termSameScope]

/-- The `childSpecs` table has length exactly `arity g`.  Proof by
case-analysis: each of the 74 arms closes via `rfl` on
`[].length = 0`, `[_].length = 1`, `[_,_].length = 2`, `[_,_,_].length = 3`. -/
theorem Generator.childSpecs_length_eq_arity (generator : Generator) :
    generator.childSpecs.length = generator.arity := by
  cases generator <;> rfl

/-- The coherence lemma between `childSpecs` and `binderShifts`: extracting
the per-child scope shift from the child-spec list yields exactly the
non-dependent `binderShifts` list.  Together with
`binderShifts_length_eq_arity` (in `GeneratorCore`) and
`childSpecs_length_eq_arity` (above) this pins the discipline:

  arity g = (childSpecs g).length = (binderShifts g).length

and the per-position scope-shift agrees between both views.

Mechanically a `cases g <;> rfl` since both tables enumerate the same enum
in the same order with literal-list bodies; per arm the `List.map` reduces
on `[]` / `[x]` / `[x, y]` / `[x, y, z]` and each `ChildSpecV2`'s
`scopeShift` projection is also a literal. -/
theorem Generator.childSpecs_scopeShifts_eq_binderShifts
    (generator : Generator) :
    (generator.childSpecs.map ChildSpecV2.scopeShift) =
      generator.binderShifts := by
  cases generator <;> rfl

end LeanFX2.Foundation.PolyCell.Core

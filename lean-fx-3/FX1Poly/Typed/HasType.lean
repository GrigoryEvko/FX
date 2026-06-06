import FX1Poly.Core.CellSort
import FX1Poly.Typed.TypingContext
import FX1Poly.Core.StepStarConfluence

/-! # FX1Poly/Typed/HasType — native fibrant-cell typing judgment

The native typed layer over the fibrant cell substrate.  The judgment
classifies `.term`-sorted SUBJECT cells by `.type`-sorted CLASSIFIER
cells — both `RawTerm` cells over the one fibrant polygraph (§5: "every
structural rule is a morphism at its sort").  No legacy MLTT `Ty` tower:
the classifier is a `.type`-cell and the universe level lives inside that
cell's `gen_universeCode` payload, never as an extrinsic kernel index.

## The native design — cells classifying cells (polycell.md §11.8.5, §5)

The typing judgment classifies a `.term`-sorted SUBJECT cell by a
`.type`-sorted CLASSIFIER cell — BOTH are `RawTerm` cells over the one
fibrant polygraph substrate (§5: "every structural rule is a morphism at
its sort").  Shape:

    HasType : (profile : PolyProfile) → {scope : Nat} →
      TypingContext profile scope →   -- bindings are .type-sorted cells
      RawTerm scope →                 -- subject:    a .term-sorted cell
      RawTerm scope →                 -- classifier: a .type-sorted cell
      Prop

A `TypingContext profile scope` is a de Bruijn sequence of `.type`-cells
(each binding's type is itself a cell, well-formed by an `IsType` side
condition `∃ levelCode, HasType ctx bindingType (universeCell levelCode)`),
NOT a list of `Ty` values.  The universe LEVEL lives INSIDE the
classifier cell — the `gen_universeCode` payload `LevelExpr × UniverseFlag`
(§3.16.3, §11.8.2) — never as an extrinsic kernel index, per §11.8.2's
no-Type-in-Type universe policy (the seven-gap audit's gap #1).

## Zero-axiom verification

`CellSort` markers + one `rfl`-closed conjunction.  No `axiom`, no
`sorry`, no `propext` / `Quot.sound` / `Classical`.  Audit-gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The SUBJECT of the native typing judgment is a `.term`-sorted cell. -/
def hasTypeSubjectSort : CellSort := .term

/-- The CLASSIFIER is a `.type`-sorted cell — NOT a legacy `Foundation.Ty`.
The universe level lives inside this cell's `gen_universeU` code, not as
an extrinsic kernel index (§11.8.2 no-Type-in-Type). -/
def hasTypeClassifierSort : CellSort := .type

/-- Context bindings are `.type`-sorted cells (each binding's type is a
cell), NOT `Ty` values. -/
def hasTypeContextBindingSort : CellSort := .type

/-- The native typing discipline, pinned as a checked fact: a `.term`
SUBJECT is classified by a `.type` CLASSIFIER — cells classifying cells.
This guards against reintroducing an MLTT `Ty` classifier in place of the
`.type`-cell. -/
theorem hasType_classifies_term_by_type :
    hasTypeSubjectSort = .term ∧ hasTypeClassifierSort = .type :=
  ⟨rfl, rfl⟩

/-! ## The typing core

The native `HasType` inductive over the cell substrate.  Five arms: `var`
(consuming `TypingContext.lookup`); `conv` (the SOLE door through which
`Conv` enters); `universeFormation` — `Type@(e, flag) : Type@(lsucc e,
flag)`, the predicative successor that GROUNDS `IsType` (without it no
cell inhabits a universe, so the `conv` well-formedness premise is
unsatisfiable and `IsType` / `WfContext` are empty); and `piFormation` /
`sigmaFormation`, the dependent function- and pair-type formers landing a
`gen_piTyCode` / `gen_sigmaTyCode` cell in `Type@(lmax dom cod, flag)`.

* `HasType : Prop` — typing is a property of the already-data `RawTerm`;
  buys decidable "is-it-typed" and §1.5 erasure.  Reconciled with the
  proof-relevant `(∞,ω)` reading by uniqueness-of-typing (#469).
* `conv` carries the classifier's well-formedness as a DIRECT premise
  `HasType … reclassifier (universeCodeCell levelExpr flag)`, with the
  universe witness `(levelExpr, flag)` exposed as explicit `conv`
  arguments.  This keeps `HasType` a SINGLE inductive: the tidier
  `∃ levelExpr flag, HasType …` form nests `HasType` under `Exists` with
  the constructor's local variables in the nested parameter, which the
  Lean kernel rejects ("nested inductive datatypes parameters cannot
  contain local variables").  `IsType` (the existential) is therefore a
  post-hoc `def` for downstream use, not a `conv` premise.  A single
  inductive also keeps later induction (SR, inversion) on one recursor —
  friendlier to the zero-axiom discipline than a `HasType`/`IsType`
  mutual block.

Sound by construction (0 false positives: ill-formed cells like
`app(unit, unit)` have no derivation in this fragment). -/

/-- The universe-code classifier cell `Type@(levelExpr, flag)` — the
`.type`-sorted cell that classifies types at universe level `levelExpr`
under hierarchy flag `flag` (§11.8.2). -/
def universeCodeCell {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) : RawTerm scope :=
  .mkGen .gen_universeCode (levelExpr, flag) .childNil

/-- The empty-type code cell `Empty` — the `.type`-sorted nullary `gen_emptyCode`
cell (the bottom type, fx_design §3.9 `never`).  No payload data (`Unit`), no
children (`binderShifts = []`, hence `childNil`): a closed nullary type-former
leaf, structurally like `universeCodeCell` but at a distinct generator.  The
formation subject of CON-A2's dedicated `emptyFormation` arm (`Empty : Type@0`)
and the type whose reducibility candidate is the empty candidate (CON-A3), the
substrate of typed consistency (SN-050). -/
def emptyTypeCell {scope : Nat} : RawTerm scope :=
  .mkGen .gen_emptyCode () .childNil

/-- The bool-type code cell `Bool` — the `.type`-sorted nullary `gen_boolCode`
cell.  No payload data (`Unit`), no children (`binderShifts = []`, hence
`childNil`): a closed nullary type-former leaf, structurally identical to
`emptyTypeCell` but at a distinct generator (the `gen_boolCode` substrate, SN-047).
The future formation subject of `Bool : Type@0` (via the nullary-former formation
`hasTypeDescPi_nullaryFormation_viaGenArm` once the `typingRuleDescOf` row lands —
GTL-11-gated) and the type whose reducibility candidate is the bool data candidate
(`boolCanonicalFormsCandidate`, #676) — the substrate of bool canonicity (SN-047).
Distinct from the VALUE cells `gen_boolTrue` / `gen_boolFalse`: this is the TYPE
code, which the kernel previously lacked (only the values were generators). -/
def boolTypeCell {scope : Nat} : RawTerm scope :=
  .mkGen .gen_boolCode () .childNil

/-- The variable cell at de Bruijn position `index`. -/
def variableCell {scope : Nat} (index : Fin scope) : RawTerm scope :=
  .mkGen .gen_var index .childNil

/-- The dependent function-type code cell `Π domainCode. codomainCode` — the
`.type`-sorted `gen_piTyCode` cell (binder shifts `[0, 1]`: the codomain lives
under one fresh value binder, hence at `scope + 1`).  Payload is `Unit`; the two
children are the domain and codomain codes.  The subject cell of the
`piFormation` arm. -/
def piTyCodeCell {scope : Nat} (domainCode : RawTerm scope)
    (codomainCode : RawTerm (scope + 1)) : RawTerm scope :=
  .mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))

/-- The dependent pair-type code cell `Σ domainCode. codomainCode` — the
`.type`-sorted `gen_sigmaTyCode` cell.  Structurally identical to
`piTyCodeCell` (binder shifts `[0, 1]`: the codomain lives under one fresh
value binder, hence at `scope + 1`; payload is `Unit`; the two children are the
domain and codomain codes); only the head generator differs (`gen_sigmaTyCode`
vs `gen_piTyCode`).  The subject cell of the `sigmaFormation` arm, the dual of
the Π-formation cell. -/
def sigmaTyCodeCell {scope : Nat} (domainCode : RawTerm scope)
    (codomainCode : RawTerm (scope + 1)) : RawTerm scope :=
  .mkGen .gen_sigmaTyCode () (.childCons domainCode (.childCons codomainCode .childNil))

/-- The native typing judgment over the cell substrate: a `.term`-sorted
SUBJECT cell classified by a `.type`-sorted CLASSIFIER cell in a
`TypingContext`.  Arms: `var`, `conv`, `universeFormation`, `piFormation`,
`sigmaFormation`. -/
inductive HasType (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope →
      RawTerm scope → RawTerm scope → Prop
  | var {scope : Nat} (context : TypingContext profile scope)
      (index : Fin scope) :
      HasType profile context (variableCell index) (context.lookup index)
  | conv {scope : Nat} {context : TypingContext profile scope}
      {subject classifier reclassifier : RawTerm scope}
      (levelExpr : LevelExpr) (flag : UniverseFlag)
      (typed : HasType profile context subject classifier)
      (converts : Conv classifier reclassifier)
      (reclassifierTyped :
        HasType profile context reclassifier
          (universeCodeCell levelExpr flag)) :
      HasType profile context subject reclassifier
  | universeFormation {scope : Nat} (context : TypingContext profile scope)
      (levelExpr : LevelExpr) (flag : UniverseFlag) :
      HasType profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr.lsucc flag)
  | piFormation {scope : Nat} (context : TypingContext profile scope)
      (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
      (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
      (domainTyped :
        HasType profile context domainCode
          (universeCodeCell domainLevel flag))
      (codomainTyped :
        HasType profile (context.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag)) :
      HasType profile context (piTyCodeCell domainCode codomainCode)
        (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag)
  | sigmaFormation {scope : Nat} (context : TypingContext profile scope)
      (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
      (domainLevel codomainLevel : LevelExpr) (flag : UniverseFlag)
      (domainTyped :
        HasType profile context domainCode
          (universeCodeCell domainLevel flag))
      (codomainTyped :
        HasType profile (context.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag)) :
      HasType profile context (sigmaTyCodeCell domainCode codomainCode)
        (universeCodeCell (LevelExpr.lmax domainLevel codomainLevel) flag)

/-- `IsType profile context classifier` — the classifier cell inhabits
some universe.  A `def` (not part of the inductive): the existential here
nests `HasType` under `Exists` and so cannot appear in a `HasType`
constructor (kernel-rejected) — `conv` exposes its universe witness
`(levelExpr, flag)` explicitly instead, and this abbreviation is for
downstream use (WfContext, IsType-stability) only. -/
def IsType (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (classifier : RawTerm scope) :
    Prop :=
  ∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
    HasType profile context classifier (universeCodeCell levelExpr flag)

end FX1Poly.Typed

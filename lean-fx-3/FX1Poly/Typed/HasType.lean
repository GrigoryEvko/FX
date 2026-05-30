import FX1Poly.Core.CellSort
import FX1Poly.Typed.TypingContext
import FX1Poly.Core.StepStarConfluence

/-! # FX1Poly/Typed/HasType — native fibrant-cell typing judgment (design scaffold)

ROOT STATUS: Scaffold / Deferred (polycell.md §12.6.8).  This file ships
NO typing theorems yet.  It is the clean-cut landing pad for the native
typed layer: it records the design and SEVERS the MLTT-flavored shape
that lean-fx-2's `Foundation/PolyCell/Typed/` still carries, so the
future port cannot silently re-confuse the cell substrate with the
legacy `Ty` tower.  The real `HasType` inductive lands once `RawTerm` /
`Generator` are ported into `FX1Poly.Core` (the next migration bricks);
this file pins the target.

## The native design — cells classifying cells (polycell.md §11.8.5, §5)

The typing judgment classifies a `.term`-sorted SUBJECT cell by a
`.type`-sorted CLASSIFIER cell — BOTH are `RawTerm` cells over the one
fibrant polygraph substrate (§5: "every structural rule is a morphism at
its sort").  Design-intent shape:

    HasType : (profile : PolyProfile) → {scope : Nat} →
      TypingContext profile scope →   -- bindings are .type-sorted cells
      RawTerm scope →                 -- subject:    a .term-sorted cell
      RawTerm scope →                 -- classifier: a .type-sorted cell
      Prop

A `TypingContext profile scope` is a de Bruijn sequence of `.type`-cells
(each binding's type is itself a cell, well-formed by an `IsType` side
condition `∃ levelCode, HasType ctx bindingType (universeCell levelCode)`),
NOT a list of legacy `Ty` values.  The universe LEVEL lives INSIDE the
classifier cell — the `gen_universeU` payload `LevelExpr × UniverseFlag`
(§3.16.3, §11.8.2) — never as an extrinsic kernel index.

## MLTT vestiges DELETED (deliberately NOT carried from lean-fx-2)

lean-fx-2's `Foundation/PolyCell/Typed/{TypingContext,HasType}.lean` is
HYBRID-MLTT: the subject is a `RawTerm` (native), but the classifier is a
legacy `Foundation.Ty` (MLTT).  The clean cut severs exactly:

* SEVERED `import LeanFX2.Foundation.Ty` — the legacy MLTT `Ty` inductive
  is NOT a dependency of FX1Poly.  Types are `.type`-sorted cells.
* SEVERED the `Ty level scope` CLASSIFIER index of `HasType` — replaced
  by a `.type`-sorted `RawTerm scope` classifier cell (§11.8.5).
* SEVERED the extrinsic `level : Nat` index on `TypingContext` / `HasType`
  — the universe level is carried by the universe CODE inside the type
  cell (`gen_universeU : LevelExpr × UniverseFlag`), per §11.8.2's
  no-Type-in-Type universe policy (the seven-gap audit's gap #1).
* SEVERED `TypingContext` storing `Ty` bindings — native bindings are
  `.type`-cells with an `IsType` well-formedness witness.

Cells classify cells.  The new kernel does not reach for `Foundation.Ty`.

## TODO — the native rework, with diabolical power (polycell.md §11.8)

Ordered by dependency; each cites its polycell.md section + M-task slot:

* TODO[blocker]: port `RawTerm` + `Generator` / `GeneratorCore` into
  `FX1Poly.Core` (the un-indexed term/cell layer, §4).  `HasType` cannot
  be STATED natively until the subject/classifier cell type lives here.
* TODO[Z₁ M31/M32]: `TypingContext profile scope` over `.type`-cells +
  `lookup` / weakening (NO `level` index; NO `Ty`).
* TODO[Z₁ M35/M42]: universe-formation with NO Type-in-Type —
  `universeCell e : universeCell (lsucc e)` via the `gen_universeU`
  `LevelExpr × UniverseFlag` payload (§11.8.2 gap #1, §3.16.3); ship the
  `probe_universe_Type_in_Type_rejected` honesty probe.
* TODO[Z₁ M36–M41]: Π/λ/app, Σ/pair/fst/snd, Unit, bool, Nat, List,
  Option, Either, Id — every eliminator MOTIVE-CARRYING (dependent
  motive child at the right binder shift, §3.16.6, §11.8.3).  No
  non-dependent-only eliminators.
* TODO[Z₁ M33/M43]: `conv` rule = type-up-to-Conv where Conv is the
  saturation MARKING on `.type` cells (§3.3–§3.4); cumulativity is a
  Conv rule (NOT a Ty ctor).
* TODO[Z₁ M46]: typed Subject Reduction over the cell substrate
  (§11.8.5) — `HasType.subject_reduction`.
* TODO[Z₂ M48–M50]: canonicity + consistency (`HasType .empty t Empty
  → False`) from typed SR + SN.
* TODO[Z₃ ★ MILESTONE A, M53/M55]: decidable typed checking + decidable
  typed Conv via cubical NbE on cells (§11.8.4, §11.8.7) — the
  STRICT-COMPLEXITY-gated deciders, no external SMT.
* TODO[Z₈ M96]: the other 20 graded dimensions as judgments composed
  with `HasType` (HasUsage/Effect/Security/.../Version, §11.8.6), each
  with univalence on its own type-universe (§11.8.13).
* TODO[§5 endgame]: ultimately `HasType` is the dim-0 face of the
  `.term`-over-`.type` DISPLAYED structure of the polygraph (a CwF
  presented cellularly) — the judgment becomes a marking on cells, not
  a bespoke inductive — and `.context` / `.grade` / `.mode` / `.effect` /
  `.protocol` get their classifying judgments uniformly.
* TODO[FX0]: every native `HasType` rule must round-trip through the
  FX0-PolyCell certificate verifier (§12.6) via `encodeCellSound`.

Until the blocker clears, this file only PINS the sort discipline below.

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
This guards the clean cut, so the future `RawTerm`-based `HasType` port
cannot reintroduce the MLTT `Ty` classifier without changing this fact. -/
theorem hasType_classifies_term_by_type :
    hasTypeSubjectSort = .term ∧ hasTypeClassifierSort = .type :=
  ⟨rfl, rfl⟩

/-! ## The typing core (var + conv) — TY-ENGINE #282, first slice

The native `HasType` lands now that `RawTerm` / `Generator` live in
`FX1Poly.Core`.  This slice ships three foundational arms: `var`
(consuming `TypingContext.lookup`, #467); `conv` (the SOLE door through
which `Conv` enters); and `universeFormation` — `Type@(e, flag) :
Type@(lsucc e, flag)`, the predicative successor that GROUNDS `IsType`
(without it no cell inhabits a universe, so the `conv` well-formedness
premise is unsatisfiable and `IsType` / `WfContext` are empty).  The
metadata-driven `gen` arm (#483) follows as its own brick.

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

Sound by construction (0 false positives: with no `gen` arm, ill-formed
cells like `app(unit, unit)` have no derivation); the false-negative rate
is high now and falls to 0 as the `gen` rules + decidable `Conv` land. -/

/-- The universe-code classifier cell `Type@(levelExpr, flag)` — the
`.type`-sorted cell that classifies types at universe level `levelExpr`
under hierarchy flag `flag` (§11.8.2). -/
def universeCodeCell {scope : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) : RawTerm scope :=
  .mkGen .gen_universeCode (levelExpr, flag) .childNil

/-- The variable cell at de Bruijn position `index`. -/
def variableCell {scope : Nat} (index : Fin scope) : RawTerm scope :=
  .mkGen .gen_var index .childNil

/-- The dependent function-type code cell `Π domainCode. codomainCode` — the
`.type`-sorted `gen_piTyCode` cell (binder shifts `[0, 1]`: the codomain lives
under one fresh value binder, hence at `scope + 1`).  Payload is `Unit`; the two
children are the domain and codomain codes.  Shape brick for #443 Π-formation. -/
def piTyCodeCell {scope : Nat} (domainCode : RawTerm scope)
    (codomainCode : RawTerm (scope + 1)) : RawTerm scope :=
  .mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))

/-- The dependent pair-type code cell `Σ domainCode. codomainCode` — the
`.type`-sorted `gen_sigmaTyCode` cell.  Structurally identical to
`piTyCodeCell` (binder shifts `[0, 1]`: the codomain lives under one fresh
value binder, hence at `scope + 1`; payload is `Unit`; the two children are the
domain and codomain codes); only the head generator differs (`gen_sigmaTyCode`
vs `gen_piTyCode`).  Shape brick for the Σ-formation arm, the dual of #443's
Π-formation. -/
def sigmaTyCodeCell {scope : Nat} (domainCode : RawTerm scope)
    (codomainCode : RawTerm (scope + 1)) : RawTerm scope :=
  .mkGen .gen_sigmaTyCode () (.childCons domainCode (.childCons codomainCode .childNil))

/-- The native typing judgment over the cell substrate: a `.term`-sorted
SUBJECT cell classified by a `.type`-sorted CLASSIFIER cell in a
`TypingContext`.  First slice — `var`, `conv`, and `universeFormation`. -/
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

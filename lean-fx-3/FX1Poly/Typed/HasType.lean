import FX1Poly.Core.CellSort

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

open FX1Poly.Core

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

end FX1Poly.Typed

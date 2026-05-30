import FX1Poly.Typed.HasType

/-! # FX1Poly/Typed/HasTypeHonesty — the 0-false-positive probe corpus

The type wrapper's defining guarantee is 0 false positives: an ill-typed
cell has NO `HasType` derivation (the fiber over an unsound cell is empty).
Raw cells are nonsense-constructable ON PURPOSE — `app(unit, unit)` is a
perfectly good `RawTerm` (a non-function applied to an argument); the typed
layer is what rejects it.  This file makes that rejection a CHECKED fact
(the typed-layer 0-FP gate, #470) — the type-level counterpart of the
structural-vs-semantic gap probes, now at the .term-over-.type layer.

## Scope of this slice (var + conv core)

`HasType` currently has two arms — `var` and `conv`.  `var` types a
variable cell; `conv` preserves the subject.  So the var+conv core types
ONLY variable cells (`HasType.typedSubjectIsVariableCell`).  Every
non-variable cell — in particular the genuinely ill-typed `app(unit, unit)`
— therefore has no derivation (`appUnitUnit_hasNoTyping`).

This is the FIRST entry of the 0-FP corpus.  As the `gen` arm lands (driven
by the `TypingRule` metadata, #483), the corpus grows and this probe is
re-established by real inversion — but the ill-typed witnesses (app of a
non-function, ...) must stay underivable forever: 0 false positives is the
invariant, the false-negative rate is what shrinks.

## Zero-axiom verification

Induction over `HasType` + a constructor-distinctness refutation via a
head-generator projection.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- The unit cell. -/
def unitCell {scope : Nat} : RawTerm scope :=
  .mkGen .gen_unit () .childNil

/-- The ill-typed witness `app(unit, unit)` — a non-function applied to an
argument.  A perfectly good RAW cell (`gen_app` has two same-scope term
children); only the TYPING rejects it. -/
def appUnitUnit {scope : Nat} : RawTerm scope :=
  .mkGen .gen_app () (.childCons unitCell (.childCons unitCell .childNil))

/-- The head generator of a cell (the first field of `mkGen`).  Used to
refute equalities between cells with distinct head generators without
dependent-`injection` pain on the payload. -/
def RawTerm.headGenerator {scope : Nat} : RawTerm scope → Generator
  | .mkGen generator _ _ => generator

/-- In the var+conv core, every typed subject is a variable cell.  Proof:
`var` produces a `variableCell`; `conv` preserves the subject (its IH gives
the same subject).  FRAGMENT-SPECIFIC — retired (re-proved by real
inversion) once the `gen` arm lands; kept here as the current proof
technique for the 0-FP probe. -/
theorem HasType.typedSubjectIsVariableCell {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasType profile context subject classifier) :
    ∃ index : Fin scope, subject = variableCell index := by
  induction typed with
  | var index => exact ⟨index, rfl⟩
  | conv levelExpr flag typedPremise converts reclassifierTyped
      ihTypedPremise ihReclassifier =>
      exact ihTypedPremise

/-- 0-FP probe: the ill-typed cell `app(unit, unit)` has NO typing
derivation in the var+conv core, for any classifier.  The typed layer
rejects what the raw layer admits. -/
theorem appUnitUnit_hasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope} :
    HasType profile context appUnitUnit classifier → False := by
  intro typed
  obtain ⟨index, subjectEq⟩ := typed.typedSubjectIsVariableCell
  have headGeneratorsAgree :
      Generator.gen_app = Generator.gen_var :=
    congrArg RawTerm.headGenerator subjectEq
  exact Generator.noConfusion headGeneratorsAgree

end FX1Poly.Typed

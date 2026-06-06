import FX1Poly.Typed.HasType
import FX1Poly.Typed.RawTermHeadGenerator

/-! # FX1Poly/Typed/HasTypeHonesty — the 0-false-positive probe corpus

The type wrapper's defining guarantee is 0 false positives: an ill-typed
cell has NO `HasType` derivation (the fiber over an unsound cell is empty).
Raw cells are nonsense-constructable ON PURPOSE — `app(unit, unit)` is a
perfectly good `RawTerm` (a non-function applied to an argument); the typed
layer is what rejects it.  This file makes that rejection a CHECKED fact
— the type-level counterpart of the structural-vs-semantic gap probes, at
the .term-over-.type layer.

## Scope: native pi/sigma-formation HasType core

`HasType` types only variable, universe-code, Π-type code, and Σ-type code
cells on the native pi/sigma-formation HasType core (`HasType.subjectIsVariableOrTypeFormerCode`).
Every other cell — in particular the genuinely ill-typed `app(unit, unit)`
— therefore has no derivation (`appUnitUnit_hasNoTyping`).

An entry of the 0-FP corpus.  As typing arms grow, the corpus grows and this
probe is re-established by real inversion — but the ill-typed witnesses (app of
a non-function, ...) stay underivable: 0 false positives is the invariant, the
false-negative rate is what shrinks.

## Zero-axiom verification

Induction over `HasType` + a constructor-distinctness refutation via a
head-generator projection.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The ill-typed witness `app(unit, unit)` — a non-function applied to an
argument.  A perfectly good RAW cell (`gen_app` has two same-scope term
children); only the TYPING rejects it. -/
def appUnitUnit {scope : Nat} : RawTerm scope :=
  .mkGen .gen_app () (.childCons unitCell (.childCons unitCell .childNil))

/-- In the var/conv/universe/Π-formation/Σ-formation core, every typed subject
is a variable cell, a universe-code cell, a Π-type code cell, or a Σ-type code
cell.  Proof: `var` produces a `variableCell`; `universeFormation` produces a
`universeCodeCell`; `piFormation` produces a `piTyCodeCell`; `sigmaFormation`
produces a `sigmaTyCodeCell`; `conv` preserves the subject (its IH gives the
same subject).  Native-core-specific: it grows by one disjunct per non-`conv` arm;
the proof technique for the 0-FP probe.  This proof is `Conv.trans`-free (the
`conv` case just forwards its IH).

The name covers four shapes (variable, universe code, Π-type code, Σ-type
code). -/
theorem HasType.subjectIsVariableOrTypeFormerCode {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (typed : HasType profile context subject classifier) :
    (∃ index : Fin scope, subject = variableCell index) ∨
      (∃ (levelExpr : LevelExpr) (flag : UniverseFlag),
        subject = universeCodeCell levelExpr flag) ∨
      (∃ (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)),
        subject = piTyCodeCell domainCode codomainCode) ∨
      (∃ (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)),
        subject = sigmaTyCodeCell domainCode codomainCode) := by
  induction typed with
  | var context index => exact Or.inl ⟨index, rfl⟩
  | conv levelExpr flag typedPremise converts reclassifierTyped
      ihTypedPremise ihReclassifier =>
      exact ihTypedPremise
  | universeFormation context levelExpr flag =>
      exact Or.inr (Or.inl ⟨levelExpr, flag, rfl⟩)
  | piFormation context domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped ihDomain ihCodomain =>
      exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
  | sigmaFormation context domainCode codomainCode domainLevel codomainLevel flag
      domainTyped codomainTyped ihDomain ihCodomain =>
      exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩))

/-- 0-FP probe: the ill-typed cell `app(unit, unit)` has NO typing
derivation in the native pi/sigma-formation HasType core, for any classifier.  The typed layer
rejects what the raw layer admits. -/
theorem appUnitUnit_hasNoTyping {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier : RawTerm scope} :
    HasType profile context appUnitUnit classifier → False := by
  intro typed
  rcases typed.subjectIsVariableOrTypeFormerCode with
    ⟨index, subjectEq⟩ | ⟨levelExpr, flag, subjectEq⟩ |
      ⟨domainCode, codomainCode, subjectEq⟩ | ⟨domainCode, codomainCode, subjectEq⟩
  · have headGeneratorsAgree : Generator.gen_app = Generator.gen_var :=
      congrArg RawTerm.headGenerator subjectEq
    exact Generator.noConfusion headGeneratorsAgree
  · have headGeneratorsAgree :
        Generator.gen_app = Generator.gen_universeCode :=
      congrArg RawTerm.headGenerator subjectEq
    exact Generator.noConfusion headGeneratorsAgree
  · have headGeneratorsAgree :
        Generator.gen_app = Generator.gen_piTyCode :=
      congrArg RawTerm.headGenerator subjectEq
    exact Generator.noConfusion headGeneratorsAgree
  · have headGeneratorsAgree :
        Generator.gen_app = Generator.gen_sigmaTyCode :=
      congrArg RawTerm.headGenerator subjectEq
    exact Generator.noConfusion headGeneratorsAgree

end FX1Poly.Typed

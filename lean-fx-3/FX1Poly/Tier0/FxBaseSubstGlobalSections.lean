import FX1Poly.Tier0.FxBaseRenamingVecGlobalSections
import FX1Poly.Tier0.FxBaseSubstComprehension

/-! # FX1Poly/Tier0/FxBaseSubstGlobalSections
    — the closed-terms `GlobalSections` over the term base (brick 6 of the term-carrying CwR base)

`FxBaseRenamingVecGlobalSections.lean` (SN-089) built the FIRST `GlobalSections` for FX — but over the pure
RENAMING base, where the canonical global-sections functor is `Hom(-, T)` at the TERMINAL object (scope `1`, since
`Hom(X, 1)` is a singleton — exactly one renaming into a one-variable scope).  Its own docstring flags the
limitation: the renaming category carries no term content, so its global sections are a SUBSINGLETON — NOT a
"closed terms at a type" functor; that needs a term-carrying base.

This file is that functor over the term-carrying base `fxBaseSubstCategory` (SUBSTVEC-2..5).  The crucial
structural difference, established last firing: the substitution category has NO terminal object (`Hom(X, T) =
SubstVec T X` is never a singleton for `X ≥ 1`, since `RawTerm T` is infinite).  It has an INITIAL object, scope
`0`.  So the canonical global-sections functor here is the representable `Hom(-, 0)` at the INITIAL object:
`sections X = Morphism X 0 = SubstVec 0 X` = the X-tuple of `RawTerm 0` = the CLOSED TERMS / closing substitutions
for an X-variable context.  Unlike the renaming base's subsingleton-at-terminal, this carries REAL content — the
first NON-VACUOUS, canonicity-relevant global-sections functor for FX.

## What lands here (all zero-axiom)

  * `fxBaseSubstGlobalSections : GlobalSections fxBaseSubstCategory` — the representable presheaf `Hom(-, 0)`
    (`GlobalSections.representable` at the initial object scope `0`); the closed-terms / closing-substitutions
    functor.
  * `fxBaseSubstGlobalSections_sections_eq` — its sections at scope `X` ARE the closing substitutions
    `SubstVec 0 X` (`X` closed terms); `rfl`.
  * `closedTermAsSection` / `sectionAsClosedTerm` — the iso `sections 1 ≅ RawTerm 0`: a global element of the
    single-variable context IS a closed term (`cons closedTerm ()` ↔ `lookup 0`).
  * `sectionAsClosedTerm_closedTermAsSection` / `closedTermAsSection_sectionAsClosedTerm` — both round-trips
    (`rfl`, via `cons_lookup_zero` + product eta + `PUnit` eta).
  * **`closedTermAsSection_injective`** — the closed-terms presheaf FAITHFULLY EMBEDS `RawTerm 0`: distinct
    closed terms are distinct global elements.  The concrete NON-VACUITY witness contrasting the renaming base's
    `..._terminal_subsingleton` — the term base's global sections genuinely SEE the closed terms.

## Honest scope boundary

This is the global-sections FUNCTOR (the contravariant `Hom(-, 0)` presheaf with its functoriality laws) over the
term base, plus the "global elements = closed terms" iso that makes it non-vacuous.  It is the structural
prerequisite the BKS sconing ladder consumes (`SconingObject.realizationMap : semanticDomain →
globalSections.sections syntacticObject` glues semantic domains onto exactly these closed-term sections).  It does
NOT itself construct the realization presheaves whose sections are "canonical forms at a TYPE" — that needs the
type-classifier structure (SN-086 display map as a representable map / SN-088 Uemura bijection) and a sconing
witness gluing reducibility onto these sections; those are the later bricks, now hostable for the first time over
a base whose global sections are real closed terms.

## Zero-axiom verification

`fxBaseSubstGlobalSections` reuses the generic `GlobalSections.representable` (structure population over the
category laws) at scope `0`.  `sections_eq` is `rfl` (`Hom(X, 0) = SubstVec 0 X` defeq).  The iso functions are
`SubstVec.cons` / `lookup`; both round-trips are `rfl` (the section is `(closedTerm, ())` and `SubstVec 0 0 =
PUnit`, so product eta + `PUnit` eta collapse it).  Injectivity is `congrArg sectionAsClosedTerm` + the
round-trip.  The section index `1` is written on the concrete `SubstVec 0 1` (a `Nat` argument) to avoid the
`OfNat ... Object 1` numeral-synthesis failure on the opaque `Object` projection (the same trap the renaming base
sidesteps with its `(1 : Nat)` ascription).  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core FX1Poly.Foundation

/-- **The closed-terms / closing-substitutions `GlobalSections` over the term base.**  The representable presheaf
`Hom(-, 0)` at the INITIAL object scope `0`: `sections X = Morphism X 0 = SubstVec 0 X` = the `X` closed terms
closing an `X`-variable context.  The first NON-VACUOUS, canonicity-relevant global-sections functor for FX (the
renaming base's was a subsingleton-at-terminal). -/
def fxBaseSubstGlobalSections : GlobalSections.{0, 0, 0} fxBaseSubstCategory :=
  GlobalSections.representable (category := fxBaseSubstCategory) (0 : Nat)

/-- The sections at scope `X` ARE the closing substitutions `SubstVec 0 X` (`X` closed terms). -/
theorem fxBaseSubstGlobalSections_sections_eq (scope : Nat) :
    fxBaseSubstGlobalSections.sections scope = SubstVec 0 scope := rfl

/-- A closed term is a global element of the single-variable context: `sections 1 = SubstVec 0 1`, and a closed
term `closedTerm : RawTerm 0` extends the empty closing substitution. -/
def closedTermAsSection (closedTerm : RawTerm 0) : SubstVec 0 1 :=
  SubstVec.cons closedTerm (PUnit.unit : SubstVec 0 0)

/-- Extract the closed term from a global element of the single-variable context (its zeroth lookup). -/
def sectionAsClosedTerm (someSection : SubstVec 0 1) : RawTerm 0 :=
  someSection.lookup ⟨0, Nat.one_pos⟩

/-- Round-trip: extracting the closed term from `closedTermAsSection` recovers it (`cons_lookup_zero`). -/
theorem sectionAsClosedTerm_closedTermAsSection (closedTerm : RawTerm 0) :
    sectionAsClosedTerm (closedTermAsSection closedTerm) = closedTerm := rfl

/-- Round-trip: rebuilding a single-variable section from its closed term recovers it (product eta + `PUnit`
eta — a `SubstVec 0 1` is exactly `(closedTerm, ())`). -/
theorem closedTermAsSection_sectionAsClosedTerm (someSection : SubstVec 0 1) :
    closedTermAsSection (sectionAsClosedTerm someSection) = someSection := rfl

/-- **The closed-terms presheaf faithfully embeds `RawTerm 0`:** distinct closed terms are distinct global
elements of the single-variable context.  The concrete NON-VACUITY witness — the term base's global sections
genuinely SEE the closed terms, unlike the renaming base's subsingleton-at-terminal. -/
theorem closedTermAsSection_injective {firstClosedTerm secondClosedTerm : RawTerm 0}
    (sectionsEqual : closedTermAsSection firstClosedTerm = closedTermAsSection secondClosedTerm) :
    firstClosedTerm = secondClosedTerm :=
  (sectionAsClosedTerm_closedTermAsSection firstClosedTerm).symm.trans
    ((congrArg sectionAsClosedTerm sectionsEqual).trans
      (sectionAsClosedTerm_closedTermAsSection secondClosedTerm))

end FX1Poly.Tier0

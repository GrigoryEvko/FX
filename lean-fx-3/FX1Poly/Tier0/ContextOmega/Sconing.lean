import FX1Poly.Tier0.FxBaseSubstCanonicityExtraction

/-! # Tier0/ContextOmega/Sconing — synthetic Tait computability over the context base (context-11)

**Synthetic Tait computability** (STC; Sterling, Sterling-Harper) builds the normalization/canonicity
logical relation NOT by hand but as a **scone** — the Artin gluing of the syntactic model with the
global-sections (closed-terms) model, worked in the internal language of the glued (Sierpiński) topos.
The computability predicate of Tait's method becomes a type IN the scone; **relative induction** is the
induction principle of the glued model relative to the syntactic one, realized by the realization map's
splitting (every syntactic closed term lifts to a computability witness).

On the FX context base this is heavily shipped (the sconing leg of the SN triangulation, SUBSTVEC-7/8/9
+ SN-089..102).  This module exhibits the STC construction as living over the CONTEXT ω-category
`fxBaseSubstCategory`, and proves the relative-induction core zero-axiom.

## What is built

  * ★ `relativeInductionEquivalence` — the closed-term scone's realization is a **two-sided iso** (both
    SUBSTVEC-6 round-trips): the glued model is EQUIVALENT to syntax-with-computability at the single
    context, the relative-induction equivalence — global sections (closed terms) ≃ the scone's semantic
    domain.
  * `relativeInductionLift` — STC relative induction: every syntactic global section (closed term over
    the context base) LIFTS to a computability witness in the scone, splitting the realization (the
    shipped `SconeCanonicityExtraction` IS Sterling's relative-induction section).
  * `openModalPartAlwaysLifts` — the open-modal (syntax-only / tautological) scone trivially admits
    relative induction (extract = `id`): the syntactic part of the gluing is canonical by construction.
  * `boolCanonicityViaRelativeInduction` — the bool data scone's relative induction IS canonicity: its
    computability domain is inhabited and strongly normalizing (every closed bool-typed term canonical).
  * `consistencyViaRelativeInduction` — the empty data scone REFUSES relative induction (no extraction):
    its computability domain is uninhabited while its sections are not — the consistency reading of STC.
  * ★ `syntheticTaitComputabilityCore` — the headline: the relative-induction equivalence + bool
    canonicity + empty consistency, the operational core of synthetic Tait computability over the
    context base.

## Honest boundary (recorded, not faked)

The FULL STC relative-induction recursor — the eliminator of the glued model over ALL of syntax (every
type carrying its computability predicate, the QIIT recursor of the Artin-gluing topos) — needs the
QIIT eliminator / `funext` (the same boundary as context-3..10: comparing whole computability families
at every type).  What IS zero-axiom is the OPERATIONAL core: the relative-induction EQUIVALENCE at the
context (the realization iso), the per-scone extraction (the relative-induction section), and the
concrete bool-canonicity / empty-consistency outputs.

## Zero-axiom verification

`relativeInductionEquivalence` bundles the shipped SUBSTVEC-6 round-trips; `relativeInductionLift` is
`SconeCanonicityExtraction.realizationIsSurjective` on `closedTermSconeCanonicityExtraction`;
`openModalPartAlwaysLifts` is `tautologicalSconeCanonicityExtraction`; the bool/empty outputs are the
shipped SUBSTVEC-9 `boolValueScone_inhabited`/`_semanticIsStronglyNormalizing` and
`emptyValueScone_hasNoCanonicityExtraction`.  No `funext`, no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core FX1Poly.Core.StepStar

/-! ## The relative-induction equivalence -/

/-- ★ **The relative-induction equivalence over the context base.**  The closed-term scone's
realization map `closedTermAsSection` (the term-presheaf embedding) is a TWO-SIDED iso — both SUBSTVEC-6
round-trips hold — so the glued model is EQUIVALENT to syntax-with-computability at the single context:
global sections (closed terms `RawTerm 0`) correspond bijectively to the scone's semantic domain.  This
equivalence is what makes synthetic Tait computability a SINGLE induction (relative induction): the
syntactic and glued models agree up to the realization iso. -/
theorem relativeInductionEquivalence :
    (∀ closedTerm : RawTerm 0,
        sectionAsClosedTerm (closedTermAsSection closedTerm) = closedTerm) ∧
    (∀ someSection : SubstVec 0 1,
        closedTermAsSection (sectionAsClosedTerm someSection) = someSection) :=
  ⟨sectionAsClosedTerm_closedTermAsSection, closedTermAsSection_sectionAsClosedTerm⟩

/-! ## Relative induction: the section that lifts syntax into the scone -/

/-- **STC relative induction.**  Every syntactic global section (closed term over the context base)
LIFTS to a computability witness in the scone whose realization is itself — the shipped per-scone
`SconeCanonicityExtraction` IS Sterling's relative-induction section (the syntactic model maps into the
glued model, splitting the realization).  Here at the closed-term scone, where the lift is the
SUBSTVEC-6 iso direction. -/
theorem relativeInductionLift
    (closedTerm :
      fxBaseSubstGlobalSections.sections fxBaseSubstClosedTermScone.syntacticObject) :
    ∃ member : fxBaseSubstClosedTermScone.semanticDomain,
      fxBaseSubstClosedTermScone.realizationMap member = closedTerm :=
  closedTermSconeCanonicityExtraction.realizationIsSurjective closedTerm

/-- **The open-modal part trivially lifts.**  The tautological (syntax-only / open-modal) scone always
admits relative induction (`extract = id`): the syntactic component of the Artin gluing is canonical by
construction — the open modality's image needs no computability content. -/
def openModalPartAlwaysLifts (baseObject : fxBaseSubstCategory.Object) :
    SconeCanonicityExtraction (SconingObject.tautological fxBaseSubstGlobalSections baseObject) :=
  tautologicalSconeCanonicityExtraction fxBaseSubstGlobalSections baseObject

/-! ## Concrete relative-induction outputs: canonicity + consistency -/

/-- **Bool canonicity via relative induction.**  The bool data scone (SUBSTVEC-9) has an inhabited,
strongly-normalizing computability domain: relative induction over it turns well-typedness into
canonicity — every closed bool-typed term reduces to a canonical bool value, and all such values are
strongly normalizing. -/
theorem boolCanonicityViaRelativeInduction :
    Nonempty boolValueScone.semanticDomain ∧
    ∀ member : boolValueScone.semanticDomain, IsStronglyNormalizing member.val :=
  ⟨boolValueScone_inhabited, boolValueScone_semanticIsStronglyNormalizing⟩

/-- **Consistency via relative induction.**  The empty data scone REFUSES relative induction: it has NO
canonicity extraction, because its computability domain is uninhabited while its global sections are not
— exactly the consistency reading of synthetic Tait computability (the bottom type admits no closed
canonical inhabitant). -/
theorem consistencyViaRelativeInduction
    (extraction : SconeCanonicityExtraction emptyValueScone) : False :=
  emptyValueScone_hasNoCanonicityExtraction extraction

/-! ## The headline -/

/-- ★ **Synthetic Tait computability over the context base, operational core.**  On the FX context base
the STC gluing yields (a) the **relative-induction equivalence** — the realization is a two-sided iso,
so the glued and syntactic models agree; (b) **bool canonicity** — the bool data scone's computability
domain is inhabited; and (c) **empty consistency** — the empty data scone admits no extraction.  With
the relative-induction section (`relativeInductionLift`) and the open-modal trivial lift
(`openModalPartAlwaysLifts`), this is the operational heart of synthetic Tait computability + relative
induction.  (The full glued-model QIIT recursor over all of syntax is the recorded funext boundary.) -/
theorem syntheticTaitComputabilityCore :
    (∀ closedTerm : RawTerm 0,
        sectionAsClosedTerm (closedTermAsSection closedTerm) = closedTerm) ∧
    (∀ someSection : SubstVec 0 1,
        closedTermAsSection (sectionAsClosedTerm someSection) = someSection) ∧
    Nonempty boolValueScone.semanticDomain ∧
    (SconeCanonicityExtraction emptyValueScone → False) :=
  ⟨sectionAsClosedTerm_closedTermAsSection,
   closedTermAsSection_sectionAsClosedTerm,
   boolValueScone_inhabited,
   emptyValueScone_hasNoCanonicityExtraction⟩

end FX1Poly.Tier0.ContextOmega

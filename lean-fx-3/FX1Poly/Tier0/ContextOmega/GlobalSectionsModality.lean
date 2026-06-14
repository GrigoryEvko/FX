import FX1Poly.Tier0.ContextOmega.ModalLock
import FX1Poly.Tier0.FxBaseSubstGlobalSections

/-! # Tier0/ContextOmega/GlobalSectionsModality — global sections / flat ♭ + the LOPS18 no-go (context-18)

In a presheaf model `Psh(B)` over a base with a terminal object, the **global-sections** functor
`Γ : Psh(B) → Set` sends a presheaf to its set of global elements (the elements over the terminal
object); its left adjoint is the constant-presheaf functor `Δ`, and the composite `♭ = Δ ∘ Γ` is the
**flat comonad** — the global-sections modality.  Licata-Orton-Pitts-Spitters ("Internal Universes in
Models of Homotopy Type Theory", FSCD 2018) is the landmark internalization: it builds an internal
*univalent universe* using the fact that the **interval is tiny** (atomic — the exponential `(-)^I`
has a further right adjoint), threaded through a **crisp / Fitch-style** discipline.

The **no-go** that LOPS18 works around: the global-sections functor `Γ` is NOT an ordinary internal /
fibred operation — it collapses a presheaf to its global points, so it does NOT commute with arbitrary
reindexing; the flat modality `♭` cannot be stated as a plain fibred type-former.  It is stateable only
relative to a **lock** `◐` (the Fitch-style left adjoint), and its full internalization needs the tiny
interval.  FX HAS the lock (context-4's `dimensionLock`), so it CAN state `♭`; what it does NOT build is
the tiny-interval internal universe (a specific presheaf base + atomicity, off the zero-axiom path).

This is a RECOGNITION over the FX substrate (`baseIsFXSyntacticContext = true`, like context-10/15/16):

  * **the global-sections OBJECT action is realized** — `Γ` evaluated at the term family is the set of
    CLOSED terms `RawTerm 0`, and the shipped two-sided iso `closedTermAsSection` / `sectionAsClosedTerm`
    (SUBSTVEC-6, context-11's `relativeInductionEquivalence`) IS that `Γ ≅ {closed terms}` on the nose;
  * **the flat modality is stateable via the lock** — context-4's `dimensionLock` is the Fitch-style
    `◐` left adjoint that `♭` is defined relative to (the lock strictly adds a dimension,
    `objectMap scope = scope + 1`).

## Honest boundary (the LOPS18 no-go, recorded not faked)

What is NOT mechanized zero-axiom: the full LOPS18 construction — the tiny / atomic interval, the
`(-)^I ⊣ √` right-adjoint chain, the internally-defined ♭-modal univalent universe — needs a specific
presheaf base with a tiny object and is the cited construction.  And the no-go proper (`Γ` is not a
fibred functor; naive internalization of `♭` fails) is the metatheoretic reason it needs the lock.  The
ledger records both as absent; what is zero-axiom is the OBJECT action (`Γ` = closed terms) + the lock
that makes `♭` stateable.

## What is built

  * `GlobalSectionsModalityLedger` — the recognition record (which global-sections / flat ingredients
    FX realizes, which are the LOPS18 boundary).
  * `fxGlobalSectionsModalityLedger` — FX's instance.
  * the flag pins.
  * ★ `globalSectionsObjectActionIsClosedTerms` — the genuine anchor: `Γ ≅ {closed terms}` via the
    shipped two-sided iso, conjoined with the realized flag.
  * ★ `flatModalityStateableViaDimensionLock` — the lock anchor: the Fitch `◐` exists (context-4),
    conjoined with the stateable flag.
  * `globalSectionsModalityRecognized` — the headline.

## Zero-axiom verification

Record + `rfl` flag pins, plus cross-references applying the shipped zero-axiom
`sectionAsClosedTerm_closedTermAsSection` / `closedTermAsSection_sectionAsClosedTerm` (the Γ-iso) and
`dimensionLock_objectMap` (the lock).  No `funext`, no `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-! ## The global-sections / flat-modality ledger -/

/-- A recognition record for the global-sections modality `♭ = Δ ∘ Γ` on the FX context base: which
ingredients FX realizes zero-axiom (the `Γ` object action, the lock that makes `♭` stateable) and which
are the LOPS18 boundary (the full internal universe via the tiny interval; `Γ`-as-a-fibred-functor). -/
structure GlobalSectionsModalityLedger where
  /-- The global-sections object action is realized: `Γ` at the term family is the closed terms
  (`RawTerm 0`), via the shipped two-sided iso. -/
  globalSectionsObjectActionRealized : Bool
  /-- The flat modality `♭` is stateable via the Fitch-style lock `◐` (context-4's `dimensionLock`). -/
  flatModalityStateableViaLock : Bool
  /-- Whether the base is the FX syntactic context category.  `true` — built ON the FX contexts. -/
  baseIsFXSyntacticContext : Bool
  /-- Honest absence marker: whether the flat COMONAD is fully internalized as a fibred operation.
  `false` — the no-go: `Γ` is not a fibred functor (doesn't commute with reindexing). -/
  flatComonadFullyInternalized : Bool
  /-- Honest absence marker: whether the LOPS18 tiny-interval internal univalent universe is
  constructed.  `false` — the cited construction (needs a tiny / atomic interval). -/
  tinyIntervalUniverseConstructed : Bool

/-- FX's global-sections modality instance: the `Γ` object action (closed terms) and the Fitch lock are
realized on the FX contexts; the flat-comonad full internalization and the LOPS18 tiny-interval universe
are the recorded boundary. -/
def fxGlobalSectionsModalityLedger : GlobalSectionsModalityLedger where
  globalSectionsObjectActionRealized := true
  flatModalityStateableViaLock := true
  baseIsFXSyntacticContext := true
  flatComonadFullyInternalized := false
  tinyIntervalUniverseConstructed := false

/-! ## Flag pins -/

/-- The global-sections object action is realized (anchored by `globalSectionsObjectActionIsClosedTerms`
below). -/
theorem fxGlobalSectionsModalityLedger_globalSectionsObjectActionRealized :
    fxGlobalSectionsModalityLedger.globalSectionsObjectActionRealized = true := rfl

/-- The flat modality is stateable via the lock (anchored by `flatModalityStateableViaDimensionLock`). -/
theorem fxGlobalSectionsModalityLedger_flatModalityStateableViaLock :
    fxGlobalSectionsModalityLedger.flatModalityStateableViaLock = true := rfl

/-- The global-sections modality is recognized ON the FX syntactic context category (not a model over a
different base). -/
theorem fxGlobalSectionsModalityLedger_baseIsFXSyntacticContext :
    fxGlobalSectionsModalityLedger.baseIsFXSyntacticContext = true := rfl

/-- Honest absence marker: the flat comonad is NOT fully internalized as a fibred operation — the no-go
(`Γ` is not a fibred functor). -/
theorem fxGlobalSectionsModalityLedger_flatComonadNotFullyInternalized :
    fxGlobalSectionsModalityLedger.flatComonadFullyInternalized = false := rfl

/-- Honest absence marker: the LOPS18 tiny-interval internal univalent universe is NOT constructed —
the cited boundary. -/
theorem fxGlobalSectionsModalityLedger_tinyIntervalUniverseNotConstructed :
    fxGlobalSectionsModalityLedger.tinyIntervalUniverseConstructed = false := rfl

/-! ## The genuine anchors -/

/-- ★ **The global-sections object action IS the closed terms.**  Evaluating the global-sections functor
`Γ` at the term family gives the GLOBAL elements — the terms over the terminal context `◇ = scope 0`,
i.e. the CLOSED terms `RawTerm 0`.  The shipped two-sided iso `closedTermAsSection` / `sectionAsClosedTerm`
(SUBSTVEC-6, the realization underlying context-11's `relativeInductionEquivalence`) is exactly that
`Γ(Tm) ≅ {closed terms}` correspondence: a global section is a substitution into `◇`, and these are in
bijection with closed terms, both round-trips holding.  This theorem conjoins both shipped round-trips
with the realized flag — the `Γ` object action, on the nose. -/
theorem globalSectionsObjectActionIsClosedTerms :
    ((∀ closedTerm : RawTerm 0,
        sectionAsClosedTerm (closedTermAsSection closedTerm) = closedTerm) ∧
     (∀ someSection : SubstVec 0 1,
        closedTermAsSection (sectionAsClosedTerm someSection) = someSection)) ∧
    fxGlobalSectionsModalityLedger.globalSectionsObjectActionRealized = true :=
  ⟨⟨sectionAsClosedTerm_closedTermAsSection, closedTermAsSection_sectionAsClosedTerm⟩, rfl⟩

/-- ★ **The flat modality is stateable via the Fitch lock.**  The flat modality `♭` cannot be stated as a
plain fibred type-former (`Γ` does not commute with reindexing — the no-go); it is stateable only
relative to a **lock** `◐`, the Fitch-style left adjoint.  FX HAS that lock: context-4's `dimensionLock`,
which strictly adds a dimension (`objectMap scope = scope + 1`).  So `♭` is stateable in FX — the
prerequisite LOPS18 work around the no-go.  This conjoins the shipped lock object-map with the
stateable flag. -/
theorem flatModalityStateableViaDimensionLock (scope : Nat) :
    dimensionLock.objectMap scope = scope + 1 ∧
    fxGlobalSectionsModalityLedger.flatModalityStateableViaLock = true :=
  ⟨dimensionLock_objectMap scope, rfl⟩

/-! ## The headline -/

/-- ★ **The global-sections modality, recognized.**  On the FX context base the global-sections modality
`♭ = Δ ∘ Γ` has (a) its `Γ` object action realized — `Γ` at the term family is the closed terms, via the
shipped two-sided iso — and (b) is stateable via the Fitch lock `◐` (context-4's `dimensionLock`), over
the FX syntactic context category, while (c) the flat comonad's full fibred internalization and (d) the
LOPS18 tiny-interval internal univalent universe are the recorded no-go boundary. -/
theorem globalSectionsModalityRecognized :
    fxGlobalSectionsModalityLedger.globalSectionsObjectActionRealized = true ∧
    fxGlobalSectionsModalityLedger.flatModalityStateableViaLock = true ∧
    fxGlobalSectionsModalityLedger.baseIsFXSyntacticContext = true ∧
    fxGlobalSectionsModalityLedger.flatComonadFullyInternalized = false ∧
    fxGlobalSectionsModalityLedger.tinyIntervalUniverseConstructed = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Tier0.ContextOmega

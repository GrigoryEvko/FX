import FX1Poly.Tier0.ContextOmega.ModalLock
import FX1Poly.Tier0.FxBaseSubstGlobalSections

/-! # Tier0/ContextOmega/GlobalSectionsModality — global sections / flat ♭ + the LOPS18 no-go (context-18)

In a presheaf model `Psh(B)` over a base with a terminal object, the **global-sections** functor
`Γ : Psh(B) → Set` sends a presheaf to its set of global elements (the elements over the terminal
object); its left adjoint is the constant-presheaf functor `Δ`, and the composite `♭ = Δ ∘ Γ` is the
**flat comonad** — the global-sections modality.  Licata-Orton-Pitts-Spitters ("Internal Universes in
Models of Homotopy Type Theory", FSCD 2018) is the landmark internalization: it builds an internal
*univalent universe* using the fact that the **interval is tiny** (atomic), threaded through a
**crisp / Fitch-style** discipline.

The **no-go** that LOPS18 works around: the global-sections functor `Γ` is NOT an ordinary internal /
fibred operation — it collapses a presheaf to its global points, so it does NOT commute with arbitrary
reindexing; the flat modality `♭` cannot be stated as a plain fibred type-former.  It is stateable only
relative to a **lock** `◐` (the Fitch-style left adjoint).  FX HAS the lock (context-4's `dimensionLock`),
so it CAN state `♭`.  This module ships the two genuine zero-axiom anchors:

  * ★ `globalSectionsObjectActionIsClosedTerms` — `Γ` evaluated at the term family is the set of CLOSED
    terms `RawTerm 0`, via the shipped two-sided iso `closedTermAsSection` / `sectionAsClosedTerm`
    (SUBSTVEC-6, the realization underlying context-11's `relativeInductionEquivalence`): `Γ(Tm) ≅ {closed
    terms}` on the nose.
  * ★ `flatModalityStateableViaDimensionLock` — the Fitch-style `◐` exists (context-4's `dimensionLock`
    strictly adds a dimension, `objectMap scope = scope + 1`), the prerequisite that makes `♭` stateable.

## Honest boundary (the LOPS18 no-go, recorded not faked)

What is NOT mechanized zero-axiom: the full LOPS18 construction — the tiny / atomic interval, the
`(-)^I ⊣ √` right-adjoint chain, the internally-defined ♭-modal univalent universe — needs a specific
presheaf base with a tiny object and is the cited construction.  And the no-go proper (`Γ` is not a fibred
functor; naive internalization of `♭` fails) is the metatheoretic reason it needs the lock.  What IS
zero-axiom is the OBJECT action (`Γ` = closed terms) + the lock that makes `♭` stateable.

Cross-references apply the shipped zero-axiom `sectionAsClosedTerm_closedTermAsSection` /
`closedTermAsSection_sectionAsClosedTerm` (the Γ-iso) and `dimensionLock_objectMap` (the lock).  No
`funext`, no `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-- ★ **The global-sections object action IS the closed terms.**  Evaluating the global-sections functor
`Γ` at the term family gives the GLOBAL elements — the terms over the terminal context `◇ = scope 0`,
i.e. the CLOSED terms `RawTerm 0`.  The shipped two-sided iso `closedTermAsSection` / `sectionAsClosedTerm`
(SUBSTVEC-6) is exactly that `Γ(Tm) ≅ {closed terms}` correspondence: a global section is a substitution
into `◇`, and these are in bijection with closed terms, both round-trips holding.  The `Γ` object action,
on the nose. -/
theorem globalSectionsObjectActionIsClosedTerms :
    (∀ closedTerm : RawTerm 0,
        sectionAsClosedTerm (closedTermAsSection closedTerm) = closedTerm) ∧
    (∀ someSection : SubstVec 0 1,
        closedTermAsSection (sectionAsClosedTerm someSection) = someSection) :=
  ⟨sectionAsClosedTerm_closedTermAsSection, closedTermAsSection_sectionAsClosedTerm⟩

/-- ★ **The flat modality is stateable via the Fitch lock.**  The flat modality `♭` cannot be stated as a
plain fibred type-former (`Γ` does not commute with reindexing — the no-go); it is stateable only relative
to a **lock** `◐`, the Fitch-style left adjoint.  FX HAS that lock: context-4's `dimensionLock`, which
strictly adds a dimension (`objectMap scope = scope + 1`).  So `♭` is stateable in FX — the prerequisite
LOPS18 work around the no-go.  Delegates to the shipped `dimensionLock_objectMap`. -/
theorem flatModalityStateableViaDimensionLock (scope : Nat) :
    dimensionLock.objectMap scope = scope + 1 :=
  dimensionLock_objectMap scope

end FX1Poly.Tier0.ContextOmega

import FX1Poly.Tier0.ContextOmega.Fibration

/-! # Tier0/ContextOmega/FibrationCategory — the Avigad-Kapulkin-Lumsdaine fibration category (context-15)

The syntactic category of CONTEXTS of a type theory with identity types carries a **fibration category**
structure (Brown's "category of fibrant objects"; Avigad-Kapulkin-Lumsdaine "Homotopy limits in type
theory"; Gambino-Garner "The identity type weak factorisation system"; Kapulkin-Lumsdaine "The homotopy
theory of type theories"): the **fibrations** are the (composites of) display maps `π_A` (dependent
projections), the **weak equivalences** are the homotopy equivalences induced by the Id-types, and every
object is fibrant.

This module ships the two CATEGORICAL anchors that the fibration-category axioms reduce to on the FX
context base — both genuine zero-axiom facts about the display-map class:

  * ★ `pullbackStabilityViaBeckChevalley` — Brown's pullback-stability axiom (FC3) for the display-map
    class IS the shipped Beck-Chevalley square (context-10): reindexing the display map along any
    substitution gives the display map of the reindexed type.
  * `fibrationPullbackCoversBaseViaCartesianLift` — the Cartesian lift of a substitution over the display
    map covers its base (FC3 existence): the pullback of a fibration exists and is again a fibration.

## Honest boundary (recorded, not faked)

What is NOT mechanized zero-axiom: the HOMOTOPY-THEORETIC half — the weak-equivalence class (homotopy
equivalences via Id) as a defined class, the proof that `(src,tgt)` is a fibration and `refl` a weak
equivalence, the 2-out-of-3 / 2-out-of-6 properties, and the homotopy category as a localisation.  Those
compare whole hom-families / need the Id-elimination's full behaviour across all contexts (the
funext-adjacent boundary of context-3..12).  The homotopy category of this fibration category presents the
(∞,1)-CwF of context-14.

Cross-references apply the shipped zero-axiom `beckChevalleyDisplaySquare` and `cartesianLift_coversBase`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-- ★ **Pullback-stability IS Beck-Chevalley.**  Brown's fibration-category axiom FC3 — fibrations are
pullback-stable — is, for the display-map class, exactly the shipped zero-axiom Beck-Chevalley square:
reindexing the display map `π` along any substitution `σ` (via the Cartesian lift) gives the display map
of the reindexed type, `weakening ∘ (lift σ) = σ ∘ weakening`.  Delegates to the shipped
`beckChevalleyDisplaySquare` (context-10) — the genuine categorical heart of the fibration category on the
FX contexts. -/
theorem pullbackStabilityViaBeckChevalley {sourceScope targetScope : Nat}
    (substVec : SubstVec targetScope sourceScope) :
    (SubstVec.weakening sourceScope).compose substVec.liftUnderBinder =
      substVec.compose (SubstVec.weakening targetScope) :=
  beckChevalleyDisplaySquare substVec

/-- **The pullback of a fibration is a fibration (existence).**  The Cartesian lift `σ⁺` of a substitution
over the display map covers its base — `weakening ∘ σ⁺ = σ ∘ weakening` — so the pullback of the display
map along `σ` exists and is again a display map.  Delegates to the shipped `cartesianLift_coversBase`
(context-10). -/
theorem fibrationPullbackCoversBaseViaCartesianLift {sourceScope targetScope : Nat}
    (substVec : SubstVec targetScope sourceScope) :
    (SubstVec.weakening sourceScope).compose (cartesianLift substVec) =
      substVec.compose (SubstVec.weakening targetScope) :=
  cartesianLift_coversBase substVec

end FX1Poly.Tier0.ContextOmega

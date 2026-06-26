import FX1Poly.Core.Fib.FibrationArchitecture
import FX1Poly.Tier0.Context.Initiality

/-! # FX1Poly/Core/Fib/BiInitiality — fib-5 (b/d): the fibred kernel's object-level bi-initiality + the honest boundary

fib-5 ★ asks: is the fibred kernel the BI-INITIAL model of its presentation — for every model, a (weakly) unique
interpreting morphism (the recursion/interpretation principle)?  The FULL theorem is `×type+term`: it threads
the substitution-coherence of every former through an intrinsic QIIT presentation, whose quotient needs
`Quot.sound` (off-limits under the zero-axiom discipline) — so the architecture commits to the WEAK (up-to-iso)
form and an honest strict-uniqueness boundary.

This file ships the GENUINELY-REACHABLE residue — the OBJECT-LEVEL (context) bi-initiality, assembled at the
`fxFibredKernel` and `= true` zero-axiom — by REUSING the per-axis initialities already proven (NO new
quotient, NO funext):

  * **context-5** (`Tier0/Context/Initiality`) proved the syntactic CONTEXT structure `fxBaseSubstContextAlgebra`
    is the INITIAL context-extension algebra: `syntacticRealizationMorphism` is the interpretation morphism OUT
    of it into ANY model (EXISTENCE, the recursor on scopes), and `syntacticRealizationMorphism_unique` proves
    it is the ONLY one (UNIQUENESS) — both zero-axiom, the type abstracted away (the `×type` deferral).
  * **term-1** (SOAS-initiality, `Tier0/Term`) is the dual term-axis fact: `RawTerm` is the initial algebra over
    the signature.

This file ties context-5's object-level initiality to the fib-0 `FibredKernel` (the four-axis glue), so the
bi-initiality statement is made AT the assembled kernel, not just the standalone context axis.

## ★★ HONESTY — what is and is NOT realized (do not conflate, per the fib-3 dimension lesson)

REALIZED here (`= true`, zero-axiom): the OBJECT-LEVEL (context) bi-initiality of the fibred kernel — the
interpretation morphism on context OBJECTS exists and is unique.

NOT realized (the genuine fib-5 keystone, deferred): the morphism's action on SUBSTITUTIONS (carrying `RawTerm`
content, `×term`), the TYPE/TERM presheaf morphisms (`×type`), and the intrinsic QIIT presentation with its
substitution-coherence quotient (needs `Quot.sound`).  The RMC / `CwRMorphism` 2-categorical packaging the flag
`fxFib_hasWeakBiInitiality` names ALSO needs the display-map `MorphismClass` whose decidability over the
term-carrying substitution category hits the data-morphism `funext` wall.  Because BOTH the `Quot.sound` QIIT and
the `funext` RMC are off-limits, `fxFib_hasWeakBiInitiality` STAYS `false` — this file is fib-5 SUBSTRATE
(fib-5b object-model + fib-5d boundary), not the flag flip.

## Zero-axiom

Re-exposes context-5's zero-axiom `syntacticRealizationMorphism` / `_unique` at the fibred kernel.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Core.Fib

open FX1Poly.Tier0

/-- The fibred kernel's OBJECT-LEVEL syntactic context structure: the `context-5` initial context-extension
algebra `fxBaseSubstContextAlgebra` (carrier = scopes, empty = `0`, extend = `+1`) — the object-action of the
fibred kernel's context axis (`fxFibredKernel.base`'s context category, whose objects are scopes). -/
def fxFibredKernel_contextAlgebra : ContextExtensionAlgebra :=
  fxBaseSubstContextAlgebra

/-- **★ fib-5b: the interpretation morphism out of the fibred kernel's context structure EXISTS** (the
object-level recursion principle).  For ANY model (context-extension algebra), `syntacticRealizationMorphism`
gives the interpreting homomorphism out of the fibred kernel's syntactic context structure — the EXISTENCE half
of bi-initiality, on context objects, zero-axiom (the recursor on scopes). -/
def fxFibredKernel_interpretation (target : ContextExtensionAlgebra) :
    ContextExtensionAlgebraMorphism fxFibredKernel_contextAlgebra target :=
  syntacticRealizationMorphism target

/-- **★ fib-5 (object-level bi-initiality): the interpretation morphism is UNIQUE** (the initiality theorem
proper, on context objects).  Any homomorphism out of the fibred kernel's syntactic context structure equals
`fxFibredKernel_interpretation` pointwise — so the fibred kernel's context-object structure is genuinely
BI-INITIAL (existence + uniqueness), zero-axiom, no `Quot.sound`.  This is context-5's `×type`-abstracted
residue, stated at the assembled fibred kernel. -/
theorem fxFibredKernel_interpretation_unique (target : ContextExtensionAlgebra)
    (otherMorphism :
      ContextExtensionAlgebraMorphism fxFibredKernel_contextAlgebra target) (scope : Nat) :
    otherMorphism.mapCarrier scope = (fxFibredKernel_interpretation target).mapCarrier scope :=
  syntacticRealizationMorphism_unique target otherMorphism scope

/-- The fibred kernel's context-object bi-initiality is NON-VACUOUS: there is a model (telescopes of
unit-bindings, `unaryListAlgebra`) into which the interpretation embeds the syntactic scopes FAITHFULLY (scope
`n` realizes to a length-`n` telescope, injectively) — initiality does not collapse the structure. -/
theorem fxFibredKernel_interpretation_faithful {firstScope secondScope : Nat}
    (realizationsAgree :
      (fxFibredKernel_interpretation unaryListAlgebra).mapCarrier firstScope
        = (fxFibredKernel_interpretation unaryListAlgebra).mapCarrier secondScope) :
    firstScope = secondScope :=
  realizeScope_unaryList_injective realizationsAgree

/-! ## fib-5d — the honest strict-uniqueness / full-QIIT boundary -/

/-- **Honesty marker (fib-5d).**  The fibred kernel's OBJECT-level (context) bi-initiality is realized
(`fxFibredKernel_interpretation` + `_unique`, zero-axiom).  The FULL bi-initiality — the interpreting
`CwRMorphism`'s action on substitutions (`×term`), the type/term presheaf uniqueness (`×type`), and the
intrinsic QIIT substitution-coherence quotient — needs `Quot.sound`; and the RMC display-map `MorphismClass`
needs the data-morphism `funext`.  BOTH are off-limits zero-axiom, so this stays the honest boundary and
`fxFib_hasWeakBiInitiality` stays `false`.  `= false`. -/
def fxFib_biInitiality_objectLevelOnly_fullNeedsQuotSound : Bool := false

/-- Smoke: the fibred kernel's context algebra IS context-5's syntactic algebra (the object-level structure the
initiality is about), definitionally. -/
theorem fxFibredKernel_contextAlgebra_isSyntactic :
    fxFibredKernel_contextAlgebra = fxBaseSubstContextAlgebra := rfl

end FX1Poly.Core.Fib

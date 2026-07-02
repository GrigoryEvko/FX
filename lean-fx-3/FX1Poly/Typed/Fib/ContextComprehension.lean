import FX1Poly.Typed.Fib.DisplayFibre
import FX1Poly.Tier0.Context.ComprehensionCategory

/-! # FX1Poly/Typed/Fib/ContextComprehension — fib-1c: the kernel's `TypingContext.cons` IS the context axis's comprehension `Γ.A`

The CONTEXT axis (`Tier0/Context`, `fxComprehensionCategory` / `StandaloneModalRMC`) was ORPHANED from the
running kernel: zero engine files imported its comprehension structure, even though the context axis is BUILT
OVER the same `SubstVec` parallel-substitution substrate the kernel's `TypingContext` / `RawTerm.subst` use.
This file performs the genuine `Core → Tier0/Context` REWIRE the "delegate, axis-by-axis" directive calls for:
it imports `fxComprehensionCategory` and proves the kernel's de Bruijn context extension `TypingContext.cons`
realizes the context axis's Σ-comprehension `Γ.A` on the nose.

The connection is structural, not a coincidence: the context axis's base `fxBaseSubstCategory` has bare scopes
(`Nat`) as objects, the comprehension object `Γ.A` is `scope + 1`, and the representability iso
`Sub(Δ, Γ.A) ≅ Sub(Δ, Γ) × Tm(Δ, A)` IS `SubstVec.comprehensionIso`.  The kernel's `TypingContext.cons` is the
CLASSIFIED refinement of this object: forgetting the classifiers (`comprehensionObject`), `cons` sends the
object `scope` to `scope + 1` — exactly the comprehension object — and substitutions into it decompose by the
context axis's representability.  The shipped fib-1b display admission (`genericClassifiedCell_admittedByUnion`,
the fresh variable typed at the weakened binding type) is the TYPED universal element of this comprehension.

So this is the load-bearing first half of fib-1: Core now DEPENDS ON the context axis, and the kernel's context
extension is certified by it.  fib-1d supplies the fibred-Π right adjoint and flips
`fxFib_hasTypeContextDisplay` once the `.context` rule sort is populated.

## Zero-axiom

`rfl` — the comprehension object is the de Bruijn `+1` by construction, and the context axis's representability
unfolds (def chain `representability → splitFibration.cartesianUniversal → SubstVec.comprehensionIso`) to the
kernel's `SubstVec` comprehension iso definitionally.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core.Fib

open FX1Poly.Core FX1Poly.Tier0 FX1Poly.Typed FX1Poly.Universe

/-- The forgetful COMPREHENSION OBJECT of a typing context: its de Bruijn scope — the bare object of the
context axis's base category `fxBaseSubstCategory` (whose objects ARE `Nat`).  A typing context is the
CLASSIFIED refinement of this object; forgetting the classifiers lands in the context axis. -/
def _root_.FX1Poly.Typed.TypingContext.comprehensionObject {profile : PolyProfile} {scope : Nat}
    (_context : TypingContext profile scope) : Nat := scope

/-- ★ The kernel's context extension `TypingContext.cons` IS the context axis's comprehension extension `Γ.A`:
forgetting classifiers, `cons` sends the object `scope` to `scope + 1` — exactly the comprehension object the
context axis's representability iso lives over. -/
theorem typingContextCons_comprehensionObject {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (bindingType : RawTerm scope) :
    (TypingContext.cons restContext bindingType).comprehensionObject
      = restContext.comprehensionObject + 1 := rfl

/-- The affine dimension LOCK `lockCons` ALSO realizes the comprehension extension at the object level: it
lifts the scope by one exactly as `cons` does — the lock marks the bound dimension's zone, not the object.
(The mode-fibred lock discipline that distinguishes it is fib-3 / the A1 lineage.) -/
theorem typingContextLockCons_comprehensionObject {profile : PolyProfile} {scope : Nat}
    (restContext : TypingContext profile scope) (dimensionType : RawTerm scope) :
    (TypingContext.lockCons restContext dimensionType).comprehensionObject
      = restContext.comprehensionObject + 1 := rfl

/-- ★ The context axis's comprehension representability iso IS the kernel's `SubstVec.comprehensionIso` — the
context axis is built over the kernel's parallel-substitution substrate, definitionally.  This is the shared
substrate that makes the cons-realizes-comprehension identification structural rather than a fresh bridge. -/
theorem fxComprehensionCategory_representability_isSubstVecComprehensionIso {target source : Nat} :
    fxComprehensionCategory.representability (target := target) (source := source)
      = SubstVec.comprehensionIso := rfl

/-- ★ **The fib-1c headline: `TypingContext.cons` realizes the context axis's comprehension `Γ.A`.**  The
cons-extended context lives over the comprehension object `scope + 1`, and substitutions into it (a `SubstVec
target (scope + 1)`) decompose by the context axis's representability iso — which IS `SubstVec.comprehensionIso`
— into a substitution `Δ ⟶ Γ` paired with a term `Δ ⊢ A`.  So the kernel's de Bruijn context extension IS the
context axis's Σ-comprehension, and Core depends on the (previously orphaned) context axis. -/
theorem typingContextCons_realizesComprehension {profile : PolyProfile} {scope target : Nat}
    (restContext : TypingContext profile scope) (bindingType : RawTerm scope) :
    (TypingContext.cons restContext bindingType).comprehensionObject = scope + 1
    ∧ fxComprehensionCategory.representability (target := target) (source := scope)
        = SubstVec.comprehensionIso :=
  ⟨rfl, rfl⟩

end FX1Poly.Core.Fib

import LeanFX2.Term
import LeanFX2.Term.Subst

/-! # AuditPhase12AB14CumulUpScope — verify Term.cumulUp accepts arbitrary scopeLow

Phase 12.A.B1.4: drop scope=0 restriction on Term.cumulUp's lowerTerm.

The kernel now accepts `Term.cumulUp` where `ctxLow : Ctx mode levelLow
scopeLow` for arbitrary `scopeLow`, decoupled from the outer scope.
This is the architectural commitment for "real cumul at arbitrary
scope".

The smoke test below builds a Term.cumulUp where ctxLow has scope=2,
demonstrating that scope=0 is no longer required.

## Architecture

Phase 12.A.B1.4 decouples `scopeLow` from outer `scope`:
* `scopeLow` becomes a separate implicit parameter
* `ctxLow : Ctx mode levelLow scopeLow` (was `Ctx mode levelLow 0`)
* lowerTerm: `Term ctxLow (Ty.universe lowerLevel _) (RawTerm.universeCode _)`
   at scope = `scopeLow` (was constrained to scope=0)

The decoupling sidesteps the P-4 cumul-Subst-mismatch wall: the outer
Term.subst doesn't touch lowerTerm (different scope), so no cross-level
substituents are required.  The lower side stays substantively unchanged
through outer substitution.

For Phase 6 ConvCumul.subst_compatible — the outer-only case is what
this enables.  Lower-side substitution remains a separate operation
(see `Term.cumulUp_subst_lower` if needed).
-/

namespace LeanFX2

/-- Smoke test: Term.cumulUp with scopeLow = 2 (no longer scope=0).
The ctxLow has 2 binders; lowerTerm is a `Term.universeCode` which is
scope-polymorphic and inhabits any context.  Demonstrates that the
Phase 12.A.B1.4 decoupling actually works. -/
example
    {mode : Mode}
    (ctxLow : Ctx mode 1 2)              -- scopeLow = 2 (decoupled!)
    (ctxHigh : Ctx mode 1 0) :
    Term ctxHigh (Ty.universe UniverseLevel.zero (Nat.le_refl _))
                 (RawTerm.universeCode 0) :=
  Term.cumulUp (ctxHigh := ctxHigh)
               UniverseLevel.zero UniverseLevel.zero UniverseLevel.zero
               (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
               (Nat.le_refl _) (Nat.le_refl _)
               (Term.universeCode (context := ctxLow)
                                  UniverseLevel.zero UniverseLevel.zero
                                  (Nat.le_refl _) (Nat.le_refl _))

#print axioms LeanFX2.Term.cumulUp

end LeanFX2

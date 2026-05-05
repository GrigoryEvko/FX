import LeanFX2.Term
import LeanFX2.Term.Subst

/-! # AuditPhase12AB14CumulUpScope — verify Term.cumulUp at scope > 0

Phase CUMUL-2.6 Design D revises this audit: cumulUp now uses a
SINGLE context (no decoupled scopeLow), and ANY scope ≥ 0 is
permitted for the typeCode.  The propext-leak floor is sidestepped
via `RawTerm.cumulUpMarker` instead of via scope decoupling.

## Architecture

Phase CUMUL-2.6 Design D unifies the lower and outer contexts:
* SINGLE `context : Ctx mode level scope`
* `codeRaw : RawTerm scope` is SCHEMATIC — any code-shaped raw
* Output type: `Ty.universe higherLevel _`
* Output raw: `RawTerm.cumulUpMarker codeRaw` — structurally distinct
   from every other RawTerm ctor, so inversion lemmas keep working.

The smoke test below builds `Term.cumulUp` at scope = 2,
demonstrating that any scope is admissible.
-/

namespace LeanFX2

/-- Smoke test: Term.cumulUp at scope = 2.  The typeCode is
`Term.universeCode 0` inhabiting `Ty.universe 0` at scope 2.
Phase CUMUL-2.6 Design D — single context, schematic codeRaw,
output wrapped in `RawTerm.cumulUpMarker`. -/
example
    {mode : Mode}
    (context : Ctx mode 2 2) :
    Term context
      (Ty.universe (UniverseLevel.succ UniverseLevel.zero)
        (show (UniverseLevel.succ UniverseLevel.zero).toNat + 1 ≤ 2 by decide))
      (RawTerm.cumulUpMarker (RawTerm.universeCode 0)) :=
  Term.cumulUp (context := context)
               UniverseLevel.zero (UniverseLevel.succ UniverseLevel.zero)
               (by decide) (by decide) (by decide)
               (Term.universeCode (context := context)
                                  UniverseLevel.zero UniverseLevel.zero
                                  (Nat.le_refl _) (by decide))

#print axioms LeanFX2.Term.cumulUp

end LeanFX2

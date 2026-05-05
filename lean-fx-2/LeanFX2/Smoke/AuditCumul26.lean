import LeanFX2.Term
import LeanFX2.Term.Subst

/-! # Smoke/AuditCumul26 — CUMUL-2.6 Design D + cumulUpMarker audit.

Phase CUMUL-2.6 ships `RawTerm.cumulUpMarker` and `Term.cumulUp` under
Design D (single context, schematic codeRaw, output wrapped in
`cumulUpMarker codeRaw`).  This is the architectural answer to 15
prior CUMUL-2.6 retreats: with the marker present, Lean 4 v4.29.1's
match compiler discharges cumulUp branches in `Term.cases` via
raw-ctor mismatch (cumulUpMarker vs .unit/.universeCode/etc.) — no
propositional index equation, no propext leak.

## Demonstration: lifting universeCode

The smoke below verifies that `Term.cumulUp` accepts a
`Term.universeCode` typed source.  The KEY observation is that the
output raw is now `RawTerm.cumulUpMarker (RawTerm.universeCode ...)` —
structurally distinct from `.universeCode` itself, sidestepping the
propext-leak floor.

## What this audit proves

* `Term.cumulUp` zero-axiom under Design D.
* `RawTerm.cumulUpMarker` zero-axiom (new ctor).
* The 6-field signature accepts a typed `Term.universeCode` source
  and produces a Term at the higher universe level wrapped in the
  marker.
* The 27 inversion lemmas in `Term/Inversion.lean` are unmodified
  and continue to build (verified separately by `lake build
  LeanFX2.Term.Inversion`).
-/

namespace LeanFX2

/-- Universe constants for the smokes. -/
private abbrev levelLow : UniverseLevel := UniverseLevel.zero
private abbrev levelHigh : UniverseLevel := UniverseLevel.succ UniverseLevel.zero

private theorem cumulMonotone : levelLow.toNat ≤ levelHigh.toNat := by decide
private theorem levelLeLow : levelLow.toNat + 1 ≤ 2 := by decide
private theorem levelLeHigh : levelHigh.toNat + 1 ≤ 2 := by decide

/-- Lift a `Term.universeCode` typed source via `Term.cumulUp`.
The source has type `Term ctx (Ty.universe levelLow _) (universeCode 0)`;
the output has type `Term ctx (Ty.universe levelHigh _) (cumulUpMarker
(universeCode 0))`. -/
example
    {mode : Mode}
    (context : Ctx mode 2 0) :
    Term context (Ty.universe levelHigh levelLeHigh)
                 (RawTerm.cumulUpMarker (RawTerm.universeCode 0)) :=
  Term.cumulUp (context := context)
               levelLow levelHigh cumulMonotone
               levelLeLow levelLeHigh
               (Term.universeCode (context := context)
                                  UniverseLevel.zero levelLow
                                  (Nat.le_refl _) levelLeLow)

/-! ## Audit declarations - all zero-axiom under Design D -/

#print axioms LeanFX2.Term.cumulUp
#print axioms LeanFX2.RawTerm.cumulUpMarker
#print axioms LeanFX2.Term.universeCode

end LeanFX2

import FX1Poly.Typed.Engine.RuleTables.FlatDescTelescope
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiWeakening
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiSubstitution

/-! # FX1Poly/Typed/FlatDescTelescopePi — the GROWN flat formation premise telescope

`FlatDescTelescope` types every flat-former child with the FORMATION engine (`HasTypeDesc`).  That premise
is correct for the retired standalone flat engine, but it is NOT substitution-stable at the union: the
union's substitution lemma carries GROWN (`HasTypeDescPi`) substituent images, and a formation-typed flat
child whose head is a variable can be substituted by a term (e.g. a beta-redex at a universe code) that has
grown typing but NO formation typing — so the substituted children cannot rebuild a `FlatDescTelescope`,
and a union flat arm stated over the formation telescope makes the union's grown-image substitution lemma
FALSE.  The one-judgment repair is to state the union's flat-formation premise at the strongest prior
judgment: this file builds `FlatDescTelescopePi`, the same flat spine with every child typed by the GROWN
engine at its universe code.

  * `FlatDescTelescopePi` — the inductive: same `[0, 0, ...]` flat shape, `cons` premise
    `HasTypeDescPi profile context head (universeCodeCell headLevel flag)`.

## Zero-axiom

Structural inductive over the standalone (non-mutual) shape, `cons` premise reusing the shipped
grown engine (`HasTypeDescPi`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTypedTypingEngines.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The GROWN flat formation premise telescope: every child is typed at its own universe code by the
grown engine (`HasTypeDescPi`) under the SAME base `context` — the substitution-stable twin of
`FlatDescTelescope` and the premise of the union's `formationRule` arm (flat family). -/
inductive FlatDescTelescopePi (profile : PolyProfile) {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag) :
    {binderShifts : List Nat} → List LevelExpr → RawTermChildren binderShifts scope → Prop where
  | nil : FlatDescTelescopePi profile context flag [] .childNil
  | cons {restShifts : List Nat} (head : RawTerm (scope + 0)) (headLevel : LevelExpr)
      (restLevels : List LevelExpr) (rest : RawTermChildren restShifts scope)
      (headTyped : HasTypeDescPi profile context head (universeCodeCell headLevel flag))
      (restTyped : FlatDescTelescopePi profile context flag restLevels rest) :
      FlatDescTelescopePi profile context flag (headLevel :: restLevels) (.childCons head rest)

end FX1Poly.Typed

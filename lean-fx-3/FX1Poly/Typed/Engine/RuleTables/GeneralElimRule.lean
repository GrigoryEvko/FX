import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPi

/-! # FX1Poly/Typed/Engine/RuleTables/GeneralElimRule — the v2 elimination-rule table (live rule-data)

The pure-syntax elimination-rule descriptor `GeneralElimRule` and its two-row table
`generalElimRuleOf`, extracted out of the (deprecated) formation-engine module `HasTypeDescGeneralElim`
so the native union `HasTypeUnion` and the RuleTables bundle read the rule DATA without importing a dead
typing engine.  The description-driven elimination JUDGMENT that once consumed this table lives (dead)
in the old engine module; the live substrate reads only the table below.

  * `GeneralElimRule` — the v2 schema: the eliminated FORMER (`eliminatedType`), the argument type,
    the member shape, and the argument-dependent output, all as rule data over four type-parameters.
  * `appGeneralElimRule` — the dependent application row (`subst0` output, member `appCell`).
  * `pathAppGeneralElimRule` — the non-dependent bridge-elimination row (constant carrier output,
    member `pathAppCell`).
  * `generalElimRuleOf` — the two-row dispatch table (`gen_app` / `gen_pathApp`).
  * `generalElimRuleOf_app` / `generalElimRuleOf_pathApp` / `generalElimRuleOf_isAppOrPathApp` — the
    table-metadata lemmas every dispatch consumer routes through.

## Zero-axiom

The table is pure syntax; the metadata collapses by `rfl` / `by_cases`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/Typed/Engine/RuleTables/GeneralElimRule.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **The v2 elimination-rule description.**  Everything the generic elimination arm needs, as rule
DATA: the eliminated child's FORMER (`eliminatedType` — Π code for app, bridge code for pathApp), the
argument's type, the member shape, and the argument-dependent output.  Four type-parameters cover the
current former arities: `typeParamA : RawTerm scope` (app: the domain; pathApp: the carrier),
`typeParamB : RawTerm (scope+1)` (app: the codomain; pathApp: unused), `typeParamC typeParamD :
RawTerm scope` (pathApp: the bridge endpoints; app: unused).  Pure syntax — strictly positive. -/
structure GeneralElimRule where
  /-- The eliminated child's type (the FORMER being eliminated).  app: `piTyCodeCell paramA paramB`.
  pathApp: `bridgeTypeCell paramA paramC paramD`. -/
  eliminatedType : (scope : Nat) → RawTerm scope → RawTerm (scope + 1) →
    RawTerm scope → RawTerm scope → RawTerm scope
  /-- The argument's type.  app: the domain parameter.  pathApp: PINNED `intervalTypeCell`. -/
  argumentType : (scope : Nat) → RawTerm scope → RawTerm scope
  /-- The elimination member's shape — rule data.  app: `appCell`.  pathApp: `pathAppCell`. -/
  memberCell : (scope : Nat) → RawTerm scope → RawTerm scope → RawTerm scope
  /-- The output — ARGUMENT-dependent (the §11.8.5 children-dependent seam).  app: `subst0 paramB
  argument` (the dependent application type).  pathApp: `paramA` (the carrier — the constant family,
  the non-dependent degenerate case). -/
  outputType : (scope : Nat) → RawTerm scope → RawTerm (scope + 1) → RawTerm scope → RawTerm scope

/-- The app row: eliminated at the Π code, argument at the domain, member `appCell`, dependent
`subst0` output — exactly `HasTypeDescPi.piElim`. -/
def appGeneralElimRule : GeneralElimRule where
  eliminatedType := fun _ domainCode codomainCode _ _ => piTyCodeCell domainCode codomainCode
  argumentType := fun _ domainCode => domainCode
  memberCell := fun _ functionTerm argument => appCell functionTerm argument
  outputType := fun _ _ codomainCode argument => RawTerm.subst0 codomainCode argument

/-- The pathApp row: eliminated at the bridge code `bridgeTypeCell carrier left right`, argument
PINNED to the interval, member `pathAppCell`, CONSTANT output (the carrier) — the NON-DEPENDENT bridge
elimination shape (a path applied to an interval endpoint lands in the bridge's carrier, the constant
family).  This is exactly the conclusion the union's `generalElim` arm produces at this row. -/
def pathAppGeneralElimRule : GeneralElimRule where
  eliminatedType := fun _ carrierCode _ leftEndpoint rightEndpoint =>
    bridgeTypeCell carrierCode leftEndpoint rightEndpoint
  argumentType := fun _ _ => intervalTypeCell
  memberCell := fun _ path argument => pathAppCell path argument
  outputType := fun _ carrierCode _ _ => carrierCode

/-- **The v2 elimination table.**  Two rows: the dependent app and the non-dependent pathApp.  A new
eliminator (the data-eliminator family, NATIVE-28/32) is one more row here — never a new arm. -/
def generalElimRuleOf (generator : Generator) : Option GeneralElimRule :=
  if generator = .gen_app then some appGeneralElimRule
  else if generator = .gen_pathApp then some pathAppGeneralElimRule
  else none

/-! ## Table metadata (cascade-death lemmas) -/

/-- `gen_app`'s v2 row is the dependent application rule. -/
theorem generalElimRuleOf_app :
    generalElimRuleOf .gen_app = some appGeneralElimRule := rfl

/-- `gen_pathApp`'s v2 row is the non-dependent bridge elimination rule. -/
theorem generalElimRuleOf_pathApp :
    generalElimRuleOf .gen_pathApp = some pathAppGeneralElimRule := rfl

/-- **The current v2 elimination table is exactly `{gen_app, gen_pathApp}`.**  The enumeration lemma
every dispatch consumer routes through. -/
theorem generalElimRuleOf_isAppOrPathApp {generator : Generator} {rule : GeneralElimRule}
    (isElim : generalElimRuleOf generator = some rule) :
    generator = Generator.gen_app ∨ generator = Generator.gen_pathApp := by
  by_cases hApp : generator = .gen_app
  · exact Or.inl hApp
  · by_cases hPath : generator = .gen_pathApp
    · exact Or.inr hPath
    · exfalso
      dsimp only [generalElimRuleOf] at isElim
      rw [if_neg hApp, if_neg hPath] at isElim
      contradiction

end FX1Poly.Typed

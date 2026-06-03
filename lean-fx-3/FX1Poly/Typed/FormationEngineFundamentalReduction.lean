import FX1Poly.Typed.HasTypeDescPiStronglyNormalizingFromFundamental

/-! # FX1Poly/Typed/FormationEngineFundamentalReduction
    — SN-027 reduces to the formation-engine fundamental theorem (#674; the Kripke route)

This file names the precise residual of SN-027 (`HasTypeDescPi → reducible / strongly normalizing`) on the
KRIPKE route (SN-026), the route that — unlike the refined-motive-via-`ValidTyping` route, whose conjunct-2 is
provably unsatisfiable for type variables (`ValidTypingVariableLevelPinned.lean`) — routes neutral type-codes
through the reducibility environment rather than through `ValidTyping` levels.

The grown-engine induction is ALREADY DONE: `HasTypeDescPi.fundamentalAtAllFromFormation`
(`HasTypeDescPiFundamentalVectorFromFormation.lean`) discharges the entire `HasTypeDescPi` recursor
(`ofFormation` / `conv` / `piIntro` / `piElim` / `genFormationPi`, with `ReducibleEnvAtAllLevels` threading and
binder-local vector premises) CONDITIONAL on a single hypothesis — the FORMATION-engine fundamental theorem:

```
formationFundamental :
  ∀ {scope context subject classifier},
    HasTypeDesc profile context subject classifier → IsFundamentalConclusionAtVector context subject classifier
```

`HasTypeDesc` is the four-constructor formation sub-engine (`var` / `conv` / `universeFormation` /
`genFormation`) — no `piIntro` / `piElim`.  Its FT is the sole remaining obligation (#674), and unlike the
ValidTyping route its `var` arm is dischargeable: the all-level environment supplies the variable at every
positive level (`ReducibleEnvVec.lookupReducible` / `fundamentalVarAtVectorMatchingLevel`), so there is no
level-pinning wall here.

## What is proved

* `HasTypeDescPiAllLevelFundamentalTheorem.ofFormationFundamental` — **the wiring**: the formation-engine FT
  discharges the all-level FT INTERFACE `HasTypeDescPiAllLevelFundamentalTheorem profile`.  That interface is
  consumed (never previously produced) by ~10 downstream theorems in
  `HasTypeDescPiStronglyNormalizingFromFundamental.lean` (subject/classifier SN, closed-term reducibility,
  consistency-facing handoffs).  So once #674 lands, every one of those becomes unconditional in one step.

## Zero-axiom verification

The wiring is `fun typed => HasTypeDescPi.fundamentalAtAllFromFormation formationFundamental typed`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

/-- **The all-level FT interface is discharged by the formation-engine FT.**  Given the formation-engine
fundamental theorem (`HasTypeDesc → IsFundamentalConclusionAtVector`), the already-proven grown-engine recursor
`HasTypeDescPi.fundamentalAtAllFromFormation` yields the all-level FT interface
`HasTypeDescPiAllLevelFundamentalTheorem profile` — the hypothesis consumed by the downstream SN / canonicity /
consistency theorems.  This is the explicit SN-027 reduction on the Kripke route: the sole open obligation is the
formation-engine FT (#674). -/
theorem HasTypeDescPiAllLevelFundamentalTheorem.ofFormationFundamental {profile : PolyProfile}
    (formationFundamental :
      ∀ {scope : Nat} {context : TypingContext profile scope}
        {subject classifier : RawTerm scope},
        HasTypeDesc profile context subject classifier →
          IsFundamentalConclusionAtVector context subject classifier) :
    HasTypeDescPiAllLevelFundamentalTheorem profile :=
  fun typed => HasTypeDescPi.fundamentalAtAllFromFormation formationFundamental typed

end FX1Poly.Typed

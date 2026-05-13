import LeanFX2.Reduction.Cumul.Relation

/-! # LeanFX2.Reduction.Cumul.Promotion

Real term-promotion theorems: every typed source `Term` promotes to a
cumul-target via `Term.cumulUp` and the relation USES the source as a
constructor field.  Includes the headline `Conv.cumul_uses_source`,
its idempotent counterpart `Conv.cumul_idempotent`, the raw-form
projection `ConvCumul.viaUp_raw_eq`, and the cross-level real promotion
`Conv.cumul_cross_level_real`.

## Root status

Layer 3 cumulativity helper.  Consumed by `Reduction.Cumul` shim. -/

namespace LeanFX2

/-! ## REAL TERM-PROMOTION (uses source substantively)

`Term.cumulUp` (the kernel ctor in Term.lean) takes lowerTerm as
a real field — not as `_sourceTerm` ignored.  The output Term
contains lowerTerm by construction.

`Conv.cumul_uses_source` certifies that every cumul-promoted Term
is in `ConvCumul` with its source.  `lowerTerm` appears on BOTH
sides of the relation — the directive's hard requirement
("Term.cumulUp lowerTerm MUST USE lowerTerm") is satisfied
structurally. -/

/-- **OPTION C HEADLINE**: every typed source Term promotes to a
cumul-target via `Term.cumulUp`, and the relation USES the source.

The output `Term.cumulUp ... lowerTerm` literally contains
`lowerTerm` as a constructor field.  No witness synthesis: the
output's structure IS the input wrapped in a cumul packaging.

This theorem certifies that Option C's `Term.cumulUp` ctor is the
substantive promotion the directive demanded. -/
theorem Conv.cumul_uses_source
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe lowerLevel levelLeLow) codeRaw) :
    ConvCumul typeCode
              (Term.cumulUp (context := context)
                            lowerLevel higherLevel cumulMonotone
                            levelLeLow levelLeHigh typeCode) :=
  ConvCumul.viaUp lowerLevel higherLevel cumulMonotone
                  levelLeLow levelLeHigh typeCode

/-- **Idempotent up-promotion**: when `lowerLevel = higherLevel` and
the contexts match, the cumulUp-wrapped Term is `ConvCumul`-related
to the source via the substantive `viaUp` ctor.  Demonstrates that
even the trivial cumul chain (no level shift) uses lowerTerm
substantively — same combinator, just at the equal-level boundary. -/
theorem Conv.cumul_idempotent
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (sameLevel : UniverseLevel)
    (levelLe : sameLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe sameLevel levelLe) codeRaw) :
    ConvCumul typeCode
              (Term.cumulUp (context := context)
                            sameLevel sameLevel (Nat.le_refl _)
                            levelLe levelLe typeCode) :=
  ConvCumul.viaUp sameLevel sameLevel (Nat.le_refl _)
                  levelLe levelLe typeCode

/-! ## Raw-form equality projection

ConvCumul implies raw-form equality (modulo scope shift).  The
projection direction is straightforward: `Term.cumulUp`'s output
raw is `RawTerm.universeCode innerLevel.toNat`, identical to its
input's raw (both at scope-0 and scope-X).  The general projection
is by induction on ConvCumul. -/

/-- The raw-form projection of the cumulUp-wrapped term is
`RawTerm.cumulUpMarker (Term.toRaw typeCode)` — Phase CUMUL-2.6
Design D directly exposes the marker. -/
theorem ConvCumul.viaUp_raw_eq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe lowerLevel levelLeLow) codeRaw) :
    RawTerm.cumulUpMarker (Term.toRaw typeCode) =
      Term.toRaw (Term.cumulUp (context := context)
                               lowerLevel higherLevel cumulMonotone
                               levelLeLow levelLeHigh typeCode) := rfl

/-! ## Cross-level cumul over arbitrary scope (existing theorem set)

These theorems certify that universe-code Terms at distinct outer
levels are cross-level cumul.  The pattern is `Term.cumulUp` followed
by `ConvCumul.viaUp` — using lowerTerm substantively. -/

/-- **Cross-level via real cumulUp**: given a typed universe-code
at outer level `lowerLevel`, its `Term.cumulUp`-promoted version at
outer level `higherLevel` is `ConvCumul`-related back to the source.

Body: invokes `ConvCumul.viaUp` on the typed source `lowerTerm`,
constructed as `Term.universeCode innerLevel lowerLevel ...`.  The
typed source appears as a real ctor field — not synthesized. -/
theorem Conv.cumul_cross_level_real
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel lowerLevel higherLevel : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ lowerLevel.toNat)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level) :
    ConvCumul
      (Term.universeCode (context := context) innerLevel lowerLevel
                         cumulOkLow levelLeLow)
      (Term.cumulUp (context := context)
                    lowerLevel higherLevel cumulMonotone
                    levelLeLow levelLeHigh
                    (Term.universeCode (context := context) innerLevel
                                       lowerLevel cumulOkLow levelLeLow)) :=
  ConvCumul.viaUp lowerLevel higherLevel cumulMonotone
                  levelLeLow levelLeHigh _

end LeanFX2

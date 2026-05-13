import LeanFX2.Reduction.Cumul.Relation

/-! # LeanFX2.Reduction.Cumul.SubstOuter

Closed-source subst-compatibility theorems for `ConvCumul`.
Covers `Conv.cumul_subst_outer`, `Conv.cumul_subst_raw_invariant`,
the Phase 6 headline `ConvCumul.subst_compatible_outer`, and the
auxiliary `Conv.cumul_outer_eq` discharging same-context cumul
across distinct outer-level inhabitants.

## Root status

Layer 3 cumulativity helper.  Consumed by `Reduction.Cumul` shim. -/

namespace LeanFX2

/-! ## Phase 12.A.B1.6 — ConvCumul subst-compatibility (closed-source case)

The Phase 6 commitment: ConvCumul commutes with Subst.  At the
current architecture (Term.cumulUp's lowerTerm at scope=0), we get
the closed-source case for free: substituting the OUTER side of a
viaUp leaves cumulUp's structure intact, so ConvCumul is preserved.

A fully general "ConvCumul commutes with Subst" theorem requires
either dropping scope=0 on Term.cumulUp OR introducing a Term-level
heterogeneous substitution (Term.substHet).  Both are deferred —
this section ships the closed-source case zero-axiom. -/

/-- **Substitution preserves cumulUp's ConvCumul**: applying a Subst
to a `Term.cumulUp ... lowerTerm` produces a Term that's still
ConvCumul-related to the (unchanged) lowerTerm.

Body: `(Term.cumulUp ... lowerTerm).subst sigma` reduces to
`Term.cumulUp ... lowerTerm` (same lowerTerm, new outer scope) per
Term/Subst.lean's cumulUp arm.  ConvCumul.viaUp witnesses the result. -/
theorem Conv.cumul_subst_outer
    {mode : Mode} {level scope targetScope : Nat}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {context : Ctx mode level scope}
    {targetContext : Ctx mode level targetScope}
    {codeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (sigma : Subst level scope targetScope)
    (termSubst : TermSubst context targetContext sigma) :
    ConvCumul (Term.subst termSubst typeCode)
              (Term.subst termSubst
                (Term.cumulUp (context := context)
                              lowerLevel higherLevel cumulMonotone
                              levelLeLow levelLeHigh typeCode)) :=
  -- Term.subst's cumulUp arm recurses on typeCode.  The result is
  -- `Term.cumulUp ... (Term.subst typeCode)`, so ConvCumul.viaUp
  -- between the substituted typeCode and that wrapped term holds
  -- directly.
  ConvCumul.viaUp lowerLevel higherLevel cumulMonotone
                  levelLeLow levelLeHigh (Term.subst termSubst typeCode)

/-- **Substitution preserves cumulUp's raw shape**: substituting a
Term.cumulUp gives a Term whose raw form is
`RawTerm.cumulUpMarker ((Term.toRaw typeCode).subst sigma.forRaw)`.
Phase CUMUL-2.6 Design D directly exposes the marker. -/
theorem Conv.cumul_subst_raw_invariant
    {mode : Mode} {level scope targetScope : Nat}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {context : Ctx mode level scope}
    {targetContext : Ctx mode level targetScope}
    {codeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (sigma : Subst level scope targetScope)
    (termSubst : TermSubst context targetContext sigma) :
    Term.toRaw (Term.subst termSubst
                (Term.cumulUp (context := context)
                              lowerLevel higherLevel cumulMonotone
                              levelLeLow levelLeHigh typeCode)) =
      RawTerm.cumulUpMarker (codeRaw.subst sigma.forRaw) := rfl

/-! ## Headline Phase 6 theorem (closed-source case)

`ConvCumul.subst_compatible` asserts that ConvCumul is closed under
substitution of the OUTER side, given the Subst commutes with the
Term-side substitution machinery.  At the current architecture, this
is provable for the `viaUp` ctor directly via
`Conv.cumul_subst_outer`. -/

/-- **Phase 6 headline**: ConvCumul is preserved by subst on its
target.  The closed-source restriction (lowerTerm at scope=0) is
inherited from Term.cumulUp — the source side is invariant, the
target side gets substituted via Term.subst's cumulUp arm. -/
theorem ConvCumul.subst_compatible_outer
    {mode : Mode} {level scope targetScope : Nat}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {context : Ctx mode level scope}
    {targetContext : Ctx mode level targetScope}
    {codeRaw : RawTerm scope}
    (typeCode :
      Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (sigma : Subst level scope targetScope)
    (termSubst : TermSubst context targetContext sigma)
    (_cumulRel :
      ConvCumul typeCode
                (Term.cumulUp (context := context)
                              lowerLevel higherLevel cumulMonotone
                              levelLeLow levelLeHigh typeCode)) :
    ConvCumul (Term.subst termSubst typeCode)
              (Term.subst termSubst
                (Term.cumulUp (context := context)
                              lowerLevel higherLevel cumulMonotone
                              levelLeLow levelLeHigh typeCode)) :=
  -- Term.subst's cumulUp arm recurses on typeCode.  The result is
  -- `Term.cumulUp ... (Term.subst typeCode)`, so ConvCumul.viaUp on
  -- the substituted typeCode witnesses the result.
  Conv.cumul_subst_outer lowerLevel higherLevel cumulMonotone
                         levelLeLow levelLeHigh typeCode sigma termSubst

/-- **Same-context cumul across distinct outer levels**: when both
universe-codes happen to live in the same context (same `level`), the
outer-level alignment forces `outerLow.toNat + 1 = outerHigh.toNat +
1`, hence `outerLow.toNat = outerHigh.toNat` (`Nat.succ.inj`).  When
additionally the outer `UniverseLevel` constructors are equal, the two
universe-codes coincide as Term values and `Conv.refl` discharges. -/
theorem Conv.cumul_outer_eq
    {mode : Mode} {scope level : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevelA outerLevelB : UniverseLevel)
    (outerEq : outerLevelA = outerLevelB)
    (cumulOkA : innerLevel.toNat ≤ outerLevelA.toNat)
    (cumulOkB : innerLevel.toNat ≤ outerLevelB.toNat)
    (levelLeA : outerLevelA.toNat + 1 ≤ level)
    (levelLeB : outerLevelB.toNat + 1 ≤ level) :
    Conv (Term.universeCode (context := context) innerLevel outerLevelA
                            cumulOkA levelLeA)
         (Term.universeCode (context := context) innerLevel outerLevelB
                            cumulOkB levelLeB) := by
  cases outerEq
  have proofIrrelCumul : cumulOkA = cumulOkB :=
    Subsingleton.elim cumulOkA cumulOkB
  cases proofIrrelCumul
  have proofIrrelLevel : levelLeA = levelLeB :=
    Subsingleton.elim levelLeA levelLeB
  cases proofIrrelLevel
  exact Conv.refl _

end LeanFX2

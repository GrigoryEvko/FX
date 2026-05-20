import LeanFX2.Reduction.Cumul.Relation.Inductive

/-! # LeanFX2.Reduction.Cumul.SubstCompatTerm

CUMUL-1.7 per-Term-shape `subst_compatible_*` building-block helpers
that feed the unified `ConvCumul.subst_compatible` Pattern 3 wire-in
in `Reduction/CumulSubstCompat.lean`.  Each helper handles the
variable, unit, or cumulUp source-Term shapes against a pair of
heterogeneous substitutions whose substituents satisfy a pointwise
ConvCumul compatibility predicate.

## Root status

Layer 3 cumulativity helper.  Consumed by `Reduction.Cumul` shim. -/

namespace LeanFX2

/-! ### Per-Term-shape `subst_compatible_*` helpers

Per-Term-ctor lemmas building blocks below (`subst_compatible_var`,
`subst_compatible_unit`, `subst_compatible_cumulUp_term`) feed the
unified `ConvCumul.subst_compatible` in
`Reduction/CumulSubstCompat.lean` (Pattern 3 wire-in). -/

/-- **CUMUL-1.7 substantive unified theorem (variable-only)**: when
the source Term is a variable, the result is the pointwise compat. -/
theorem ConvCumul.subst_compatible_var
    {mode : Mode} {sourceLevel targetLevel : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigmaA sigmaB :
      SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA : TermSubstHet sourceCtx targetCtx sigmaA)
    (termSubstB : TermSubstHet sourceCtx targetCtx sigmaB)
    (pointwiseCompat : ∀ position,
        ConvCumul (termSubstA position) (termSubstB position))
    (position : Fin sourceScope) :
    ConvCumul ((Term.var (context := sourceCtx) position).substHet termSubstA)
              ((Term.var (context := sourceCtx) position).substHet termSubstB) :=
  -- Term.substHet on .var is termSubst position directly.
  pointwiseCompat position

/-- **CUMUL-1.7 substantive unified theorem (unit-only)**: the unit
ctor is closed (no positions), so substituted endpoints coincide. -/
theorem ConvCumul.subst_compatible_unit
    {mode : Mode} {sourceLevel targetLevel : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigmaA sigmaB :
      SubstHet sourceLevel targetLevel sourceScope targetScope}
    (_termSubstA : TermSubstHet sourceCtx targetCtx sigmaA)
    (_termSubstB : TermSubstHet sourceCtx targetCtx sigmaB) :
    ConvCumul ((Term.unit (context := sourceCtx)).substHet _termSubstA)
              ((Term.unit (context := sourceCtx)).substHet _termSubstB) :=
  -- Term.substHet on .unit returns Term.unit unchanged on both sides.
  ConvCumul.refl _

/-- **CUMUL-1.7 substantive unified theorem (cumulUp-only)**: the
cumulUp ctor preserves `lowerTerm` unchanged under Term.substHet,
so substituted endpoints coincide. -/
theorem ConvCumul.subst_compatible_cumulUp_term
    {mode : Mode} {sourceLevel targetLevel : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode sourceLevel sourceScope}
    {targetCtx : Ctx mode targetLevel targetScope}
    {sigmaA sigmaB :
      SubstHet sourceLevel targetLevel sourceScope targetScope}
    (termSubstA : TermSubstHet sourceCtx targetCtx sigmaA)
    (termSubstB : TermSubstHet sourceCtx targetCtx sigmaB)
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ sourceLevel)
    (levelLeHigh : higherLevel.toNat + 1 ≤ sourceLevel)
    {codeRaw : RawTerm sourceScope}
    (typeCode :
      Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw)
    (innerCompat :
      ConvCumul (typeCode.substHet termSubstA) (typeCode.substHet termSubstB)) :
    ConvCumul
      ((Term.cumulUp (context := sourceCtx)
                     lowerLevel higherLevel cumulMonotone
                     levelLeLow levelLeHigh typeCode).substHet termSubstA)
      ((Term.cumulUp (context := sourceCtx)
                     lowerLevel higherLevel cumulMonotone
                     levelLeLow levelLeHigh typeCode).substHet termSubstB) :=
  -- Term.substHet's cumulUp arm recurses on typeCode.  The result on
  -- each side is `Term.cumulUp ... (typeCode.substHet ...)`.  Wrap
  -- the inner ConvCumul via cumulUpCong.
  ConvCumul.cumulUpCong lowerLevel higherLevel cumulMonotone
                        (Nat.le_trans levelLeLow sigmaA.cumulOk)
                        (Nat.le_trans levelLeHigh sigmaA.cumulOk)
                        innerCompat

end LeanFX2

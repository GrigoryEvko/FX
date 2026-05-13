import LeanFX2.Reduction.Cumul.Relation

/-! # LeanFX2.Reduction.Cumul.BackwardCompat

Old Option A theorems preserved for downstream callers.  These
continue to project to raw-form equality and don't depend on the new
`Term.cumulUp` ctor — pure raw-side reasoning.  Includes
`Conv.cumul_refl`, `Conv.cumul_proof_irrel`, and
`Conv.cumul_raw_shared`.

## Root status

Layer 3 cumulativity helper.  Consumed by `Reduction.Cumul` shim. -/

namespace LeanFX2

/-! ## Backward-compat layer (old Option A theorems preserved)

The original Option A theorems are retained for downstream callers.
They continue to project to raw-form equality and don't depend on
the new `Term.cumulUp` ctor — pure raw-side reasoning. -/

/-- **Same-level cumul (the trivial case)**: two universe-codes at the
same outer level with the same inner level, same cumul witness, same
level-equation are Conv-equal.  Body is `Conv.refl`. -/
theorem Conv.cumul_refl
    {mode : Mode} {scope level : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Conv (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk levelLe)
         (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk levelLe) :=
  Conv.refl _

/-- **Cumulativity-witness equivalence**: two universe-codes at the
same outer level with the same inner level but POSSIBLY DIFFERENT
cumul witnesses are Conv-equal.  Body uses Subsingleton-on-`Nat.le`
(decidable Prop with proof irrelevance) to collapse the two proofs to
the same Term value, then discharges with `Conv.refl`. -/
theorem Conv.cumul_proof_irrel
    {mode : Mode} {scope level : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk1 cumulOk2 : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Conv (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk1 levelLe)
         (Term.universeCode (context := context) innerLevel outerLevel
                            cumulOk2 levelLe) := by
  have proofIrrel : cumulOk1 = cumulOk2 := Subsingleton.elim cumulOk1 cumulOk2
  cases proofIrrel
  exact Conv.refl _

/-- **Raw-form sharing** (cross-level cumul bridge at the raw level):
two universe-codes at different outer levels with the same inner level
project to the same `RawTerm.universeCode innerLevel.toNat`. -/
theorem Conv.cumul_raw_shared
    {mode : Mode} {scope levelLow levelHigh : Nat}
    {contextLow : Ctx mode levelLow scope}
    {contextHigh : Ctx mode levelHigh scope}
    (innerLevel outerLow outerHigh : UniverseLevel)
    (cumulOkLow : innerLevel.toNat ≤ outerLow.toNat)
    (cumulOkHigh : innerLevel.toNat ≤ outerHigh.toNat)
    (levelLeLow : outerLow.toNat + 1 ≤ levelLow)
    (levelLeHigh : outerHigh.toNat + 1 ≤ levelHigh) :
    Term.toRaw (Term.universeCode (context := contextLow) innerLevel
                                  outerLow cumulOkLow levelLeLow)
      = Term.toRaw (Term.universeCode (context := contextHigh) innerLevel
                                      outerHigh cumulOkHigh levelLeHigh) :=
  rfl

end LeanFX2

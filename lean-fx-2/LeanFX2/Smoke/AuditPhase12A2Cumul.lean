import LeanFX2.Reduction.Cumul

/-! # Smoke/AuditPhase12A2Cumul — kernel-sprint A2 + cross-level audit

This file gates every cumulativity declaration in `Reduction/Cumul.lean`
and the supporting typed `Term.universeCode` ctor.  Every entry MUST
report "does not depend on any axioms" under strict policy
(no propext, no Quot.sound, no Classical.choice).

If any entry reports a non-trivial axiom, the deliverable is NOT
shipped — either rewrite cleanly or delete.

## What gets audited

### Layer 0: foundational ctors
* `Term.universeCode` — typed Term ctor for universe-codes
* `RawTerm.universeCode` — raw-level universe-code

### Layer 1: cross-level relation + transformer
* `ConvCumul` — cross-level Prop relation (level-polymorphic)
* `ConvCumul.refl` — reflexivity
* `ConvCumul.sym` — symmetry
* `ConvCumul.trans` — transitivity
* `Term.cumulPromote` — REAL Term-level promotion across outer levels
* `Term.cumulPromote_toRaw_eq` — raw-form preservation under promote

### Layer 2: headline cross-level cumul theorems
* `Conv.cumul_cross_level` — REAL cross-level cumulativity for two
  universe-codes at distinct outer levels
* `Conv.cumul_cross_level_promoted` — every source promotes
* `Conv.cumul_cross_level_exists` — existential form
* `Conv.cumul_cross_level_chain` — three-level transitivity

### Layer 3: same-level legacy theorems (kept for completeness)
* `Conv.cumul_refl`
* `Conv.cumul_proof_irrel`
* `Conv.cumul_raw_shared`
* `Conv.cumul_outer_eq`
-/

namespace LeanFX2

-- Foundation: the typed Term.universeCode ctor itself
#print axioms Term.universeCode

-- Raw layer: RawTerm.universeCode
#print axioms RawTerm.universeCode

-- Cross-level relation + equivalence laws
#print axioms ConvCumul
#print axioms ConvCumul.refl
#print axioms ConvCumul.sym
#print axioms ConvCumul.trans

-- REAL Term-level promotion
#print axioms Term.cumulPromote
#print axioms Term.cumulPromote_toRaw_eq

-- HEADLINE: cross-level cumulativity theorems
#print axioms Conv.cumul_cross_level
#print axioms Conv.cumul_cross_level_promoted
#print axioms Conv.cumul_cross_level_exists
#print axioms Conv.cumul_cross_level_chain

-- Same-level legacy theorems (retained)
#print axioms Conv.cumul_refl
#print axioms Conv.cumul_proof_irrel
#print axioms Conv.cumul_raw_shared
#print axioms Conv.cumul_outer_eq

end LeanFX2

import LeanFX2.Reduction.Cumul

/-! # Smoke/AuditPhase12A2Cumul — Option C real-promotion audit

This file gates every cumulativity declaration in `Reduction/Cumul.lean`
and the supporting typed kernel ctors `Term.universeCode` and
`Term.cumulUp`.  Every entry MUST report
"does not depend on any axioms" under strict policy
(no propext, no Quot.sound, no Classical.choice, no user axioms).

If any entry reports a non-trivial axiom, the deliverable is NOT
shipped — either rewrite cleanly or delete.

## What gets audited

### Layer 0: foundational ctors
* `Term.universeCode` — typed Term ctor for universe-codes
* `Term.cumulUp` — REAL cross-level promotion ctor (Option C)
* `RawTerm.universeCode` — raw-level universe-code

### Layer 1: substantive ConvCumul relation + ctors
* `ConvCumul` — substantive inductive relation
* `ConvCumul.refl` — reflexivity ctor
* `ConvCumul.viaUp` — REAL UP-PROMOTION ctor (uses lowerTerm
  substantively as a constructor field on BOTH sides of the
  relation)
* `ConvCumul.sym` — symmetry ctor
* `ConvCumul.trans` — transitivity ctor

### Layer 2: headline real-promotion theorems
* `Conv.cumul_uses_source` — every typed source produces a
  `Term.cumulUp`-wrapped target that ConvCumul-relates back to
  the source.  This is the headline that proves the directive's
  hard requirement: "Term.cumulUp lowerTerm MUST USE lowerTerm"
  is satisfied structurally.
* `Conv.cumul_idempotent` — same-level real cumul (lowerLevel
  = higherLevel) still uses the typed source substantively
* `ConvCumul.viaUp_raw_eq` — raw-form preservation under real
  promotion
* `Conv.cumul_cross_level_real` — universe-code at distinct
  outer levels via the real ctor

### Layer 3: backward-compat (preserved Option A theorems)
* `Conv.cumul_refl`
* `Conv.cumul_proof_irrel`
* `Conv.cumul_raw_shared`
* `Conv.cumul_outer_eq`
-/

namespace LeanFX2

-- Foundation: the typed kernel ctors
#print axioms Term.universeCode
#print axioms Term.cumulUp
#print axioms RawTerm.universeCode

-- Substantive ConvCumul relation + ctors
#print axioms ConvCumul
#print axioms ConvCumul.refl
#print axioms ConvCumul.viaUp
#print axioms ConvCumul.sym
#print axioms ConvCumul.trans

-- HEADLINE: REAL up-promotion theorems
#print axioms Conv.cumul_uses_source
#print axioms Conv.cumul_idempotent
#print axioms ConvCumul.viaUp_raw_eq
#print axioms Conv.cumul_cross_level_real

-- Backward-compat: preserved Option A theorems
#print axioms Conv.cumul_refl
#print axioms Conv.cumul_proof_irrel
#print axioms Conv.cumul_raw_shared
#print axioms Conv.cumul_outer_eq

-- Phase 12.A.B1.6: ConvCumul subst-compatibility (closed-source case)
#print axioms Conv.cumul_subst_outer
#print axioms Conv.cumul_subst_raw_invariant
#print axioms ConvCumul.subst_compatible_outer

-- Phase 12.A.B1.5 cong ctors: structural cong rules for Term shapes
#print axioms ConvCumul.lamCong
#print axioms ConvCumul.lamPiCong
#print axioms ConvCumul.appCong
#print axioms ConvCumul.appPiCong
#print axioms ConvCumul.pairCong
#print axioms ConvCumul.fstCong
#print axioms ConvCumul.sndCong
#print axioms ConvCumul.boolElimCong
#print axioms ConvCumul.natSuccCong
#print axioms ConvCumul.listConsCong
#print axioms ConvCumul.optionSomeCong
#print axioms ConvCumul.eitherInlCong
#print axioms ConvCumul.eitherInrCong
#print axioms ConvCumul.idJCong
#print axioms ConvCumul.modIntroCong
#print axioms ConvCumul.modElimCong
#print axioms ConvCumul.subsumeCong
#print axioms ConvCumul.cumulUpCong

-- Phase 12.A.B1.6-finish: subst-compat theorems (decomposed approach)
#print axioms ConvCumul.subst_compatible_refl
#print axioms ConvCumul.subst_compatible_sym
#print axioms ConvCumul.subst_compatible_trans
#print axioms ConvCumul.appCong_subst_compatible
#print axioms ConvCumul.pairCong_subst_compatible
#print axioms ConvCumul.fstCong_subst_compatible
#print axioms ConvCumul.sndCong_subst_compatible
#print axioms ConvCumul.cumulUpCong_subst_compatible

end LeanFX2

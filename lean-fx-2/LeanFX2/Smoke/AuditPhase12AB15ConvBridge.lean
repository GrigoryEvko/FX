import LeanFX2.Reduction.ConvBridge

/-! # Smoke/AuditPhase12AB15ConvBridge — Conv ↔ ConvCumul bridge audit.

Audits the refl-restricted bridge fragment of `Conv` ↔ `ConvCumul`.

## Architectural blockers (acknowledged, not papered over)

The full unrestricted bridge is NOT shipped because:

* `ConvCumul` lacks β/ι ctors → cannot lift arbitrary `Step`
  reductions to `ConvCumul` cong rules.
* `Conv.trans` requires Church-Rosser (Layer 3, deferred).
* `Step.cumulUpInner` not yet shipped (CUMUL-3.1 pending).

The refl-restricted ship is a real, honest milestone.  Each
audited theorem has a real body, no `sorry`, no `axiom`, no
hypothesis-as-postulate.

## Audited declarations

* `Conv.refl_toConvCumul` — Conv → ConvCumul on identical Terms.
* `ConvCumul.refl_toConv` — ConvCumul → Conv on identical Terms.
* `Conv.toConvCumul_toConv_refl` — round-trip via ConvCumul.
* `ConvCumul.toConv_toConvCumul_refl` — round-trip via Conv.
* `Conv.sym_via_ConvCumul_refl` — sym dispatch on refl.
* `ConvCumul.sym_via_refl` — ConvCumul.sym on refl trivializes.
-/

namespace LeanFX2

#print axioms Conv.refl_toConvCumul
#print axioms ConvCumul.refl_toConv
#print axioms Conv.toConvCumul_toConv_refl
#print axioms ConvCumul.toConv_toConvCumul_refl
#print axioms Conv.sym_via_ConvCumul_refl
#print axioms ConvCumul.sym_via_refl

end LeanFX2

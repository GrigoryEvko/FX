import LeanFX2.Modal.TwoCell
import LeanFX2.Tools.DependencyAudit

/-! # AuditPhase12A4TwoCell — TwoCell zero-axiom audit (#1699 D4.0a).

Phase 12.A.4 atom D4.0a shipped the 2-cell inductive
`LeanFX2.TwoCell` along with three core ctors:

* `TwoCell.refl`  — identity 2-cell
* `TwoCell.vert`  — vertical composition
* `TwoCell.horiz` — horizontal composition (whiskering)

This atom is the LOAD-BEARING Day 4 unblock for the modal-
adjunction layer.  Without it, η : id ⇒ □ ∘ ◇ collapses to
1-cell label equality `Modality.identity m = Modality.boxK m`,
which is provably false; the structural lie would propagate
through D4.2 (Adjunction), D4.3 (BoxPath), D4.5 (full ♭ ⊣ ◇ ⊣
□ ⊣ ♯ chain), D4.6 (Bridge), and D4.8 (2LTT).

This file enforces the project's zero-axiom commitment for
each shipped declaration via two complementary gates:

1. `#assert_no_axioms NAME` — fails the build if `NAME`'s
   transitive dependency closure contains any axiom.  Comes
   from `LeanFX2.Tools.DependencyAudit`.
2. `#print axioms NAME` — reviewer-facing log; expected output
   is "does not depend on any axioms".

Both gates fire at compile time during `lake build`.  Per
`CLAUDE.md`, the namespace sweep `#audit_namespace LeanFX2` in
`Tools/AuditAll/GatesNsSweepAxiom.lean` ALREADY covers every
declaration under `LeanFX2.*` — these per-decl gates are
defense-in-depth for the load-bearing TwoCell ctors so any
future regression on the 2-cell inductive surfaces in this
file's compile-time output rather than being buried in the
namespace-wide sweep banner.

## Coherence laws (deferred)

Coherence laws (associativity of `vert`, left/right identity
for `vert`, middle-four exchange between `vert` and `horiz`,
unit-vs-vertical coherence) ship in `Modal/TwoCellLaws.lean`
under tracker #1700 (D4.0b).  This audit grows when those
theorems land.

## Cross-mode horizontal composition (deferred)

`TwoCell.horiz` here is restricted to same-mode because
`Modality.compose` is itself same-mode only.  Cross-mode
generalisation ships under tracker #1701 (D4.0c) along with
the `Modality.composeOpen` extension; the same-mode `horiz`
ctor's signature generalises straightforwardly.
-/

namespace LeanFX2.Smoke

/-! ## D4.0a — TwoCell inductive + 3 core ctors -/

#assert_no_axioms LeanFX2.TwoCell
#assert_no_axioms LeanFX2.TwoCell.refl
#assert_no_axioms LeanFX2.TwoCell.vert
#assert_no_axioms LeanFX2.TwoCell.horiz

/-! ## Reviewer-facing log -/

#print axioms LeanFX2.TwoCell
#print axioms LeanFX2.TwoCell.refl
#print axioms LeanFX2.TwoCell.vert
#print axioms LeanFX2.TwoCell.horiz

end LeanFX2.Smoke

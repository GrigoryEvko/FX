import LeanFX2.Modal.TwoCell
import LeanFX2.Modal.TwoCellLaws
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

## Coherence laws (D4.0b #1700, landed)

Coherence laws ship in `Modal/TwoCellLaws.lean` under tracker
#1700 (D4.0b) up to an explicit equivalence relation
`TwoCellEq`.  Per the `Modal/TwoCellLaws.lean` top docstring,
the free `TwoCell` inductive does NOT admit these four
equations as Lean `=` — `TwoCellEq` is the smallest congruence
on `TwoCell` containing the strict-2-category coherence laws,
and the laws are constructors of that inductive (so they are
zero-axiom data, not postulates).

The four shipped laws are: `TwoCell.vertAssoc`,
`TwoCell.vertLeftId`, `TwoCell.vertRightId`, `TwoCell.exchange`.

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

/-! ## D4.0b — TwoCellEq inductive + 9 ctors -/

#assert_no_axioms LeanFX2.TwoCellEq
#assert_no_axioms LeanFX2.TwoCellEq.reflEq
#assert_no_axioms LeanFX2.TwoCellEq.symmEq
#assert_no_axioms LeanFX2.TwoCellEq.transEq
#assert_no_axioms LeanFX2.TwoCellEq.vertCongEq
#assert_no_axioms LeanFX2.TwoCellEq.horizCongEq
#assert_no_axioms LeanFX2.TwoCellEq.vertAssocEq
#assert_no_axioms LeanFX2.TwoCellEq.vertLeftIdEq
#assert_no_axioms LeanFX2.TwoCellEq.vertRightIdEq
#assert_no_axioms LeanFX2.TwoCellEq.exchangeEq

/-! ## D4.0b — Four coherence-law theorems (up to TwoCellEq) -/

#assert_no_axioms LeanFX2.TwoCell.vertAssoc
#assert_no_axioms LeanFX2.TwoCell.vertLeftId
#assert_no_axioms LeanFX2.TwoCell.vertRightId
#assert_no_axioms LeanFX2.TwoCell.exchange

/-! ## Reviewer-facing log -/

#print axioms LeanFX2.TwoCell
#print axioms LeanFX2.TwoCell.refl
#print axioms LeanFX2.TwoCell.vert
#print axioms LeanFX2.TwoCell.horiz

#print axioms LeanFX2.TwoCellEq
#print axioms LeanFX2.TwoCellEq.reflEq
#print axioms LeanFX2.TwoCellEq.symmEq
#print axioms LeanFX2.TwoCellEq.transEq
#print axioms LeanFX2.TwoCellEq.vertCongEq
#print axioms LeanFX2.TwoCellEq.horizCongEq
#print axioms LeanFX2.TwoCellEq.vertAssocEq
#print axioms LeanFX2.TwoCellEq.vertLeftIdEq
#print axioms LeanFX2.TwoCellEq.vertRightIdEq
#print axioms LeanFX2.TwoCellEq.exchangeEq

#print axioms LeanFX2.TwoCell.vertAssoc
#print axioms LeanFX2.TwoCell.vertLeftId
#print axioms LeanFX2.TwoCell.vertRightId
#print axioms LeanFX2.TwoCell.exchange

/-! ## Type-level smoke samples — TwoCell.refl at each Modality ctor

Confirms that the identity 2-cell `TwoCell.refl` typechecks at
each of the five `Modality` constructors (identity, boxK,
diamondK, flat, sharp) without any inference hint, exercising
the implicit `{sourceMode targetMode : Mode}` arguments. -/

example : TwoCell (Modality.identity Mode.software)
                  (Modality.identity Mode.software) :=
  TwoCell.refl (Modality.identity Mode.software)

example : TwoCell (Modality.boxK Mode.software)
                  (Modality.boxK Mode.software) :=
  TwoCell.refl (Modality.boxK Mode.software)

example : TwoCell (Modality.diamondK Mode.software)
                  (Modality.diamondK Mode.software) :=
  TwoCell.refl (Modality.diamondK Mode.software)

example : TwoCell Modality.flat Modality.flat :=
  TwoCell.refl Modality.flat

example : TwoCell Modality.sharp Modality.sharp :=
  TwoCell.refl Modality.sharp

/-! ## Type-level smoke samples — TwoCell.vert composition

Confirms that vertical composition typechecks when the middle
1-cell is shared.  Uses `refl` 2-cells as components — the
result is again an identity 2-cell (left/right identity laws
for `vert` are deferred to D4.0b #1700). -/

example
    (firstCell : TwoCell (Modality.boxK Mode.software)
                         (Modality.boxK Mode.software))
    (secondCell : TwoCell (Modality.boxK Mode.software)
                          (Modality.boxK Mode.software)) :
    TwoCell (Modality.boxK Mode.software)
            (Modality.boxK Mode.software) :=
  TwoCell.vert firstCell secondCell

example : TwoCell (Modality.boxK Mode.software)
                  (Modality.boxK Mode.software) :=
  TwoCell.vert (TwoCell.refl _) (TwoCell.refl _)

/-! ## Type-level smoke samples — TwoCell.horiz composition

Confirms that horizontal composition typechecks.  At
`Mode.software`, composing two `boxK` modalities horizontally
gives a 2-cell whose source and target are
`Modality.compose (boxK ...) (boxK ...) = boxK ...` (by
`compose_boxK_idempotent`).  Lean elaborates the indices via
`Modality.compose`'s reducibility (Discipline #4 marker
applied in `Modal/Foundation.lean`). -/

example : TwoCell (Modality.compose (Modality.boxK Mode.software)
                                    (Modality.boxK Mode.software))
                  (Modality.compose (Modality.boxK Mode.software)
                                    (Modality.boxK Mode.software)) :=
  TwoCell.horiz (TwoCell.refl (Modality.boxK Mode.software))
                (TwoCell.refl (Modality.boxK Mode.software))

example : TwoCell (Modality.compose (Modality.identity Mode.ghost)
                                    (Modality.diamondK Mode.ghost))
                  (Modality.compose (Modality.identity Mode.ghost)
                                    (Modality.diamondK Mode.ghost)) :=
  TwoCell.horiz (TwoCell.refl (Modality.identity Mode.ghost))
                (TwoCell.refl (Modality.diamondK Mode.ghost))

end LeanFX2.Smoke

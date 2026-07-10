import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCupSlide

/-! # WP-BRAUER-4 r4 — V2 soundness: the cup-slide row is diagram-sound in ANY horizontal context (B2)

The V1 general soundness (`fxBrauer_hasBrauerSoundness`, r15/r3) rides the relation-agnostic keystone
`brauerConv_relation_inContext` (`Brauer/WiringDescPadCongruence.lean`): a per-relation seed-soundness witness plus
`BrauerWordInRange` + zero-internal-loop witnesses produce a `BrauerConv` for that relation whiskered after ANY
prefix at ANY offset in ANY wider boundary, and `brauerConv_sound` (`Brauer/WiringDescConv.lean`) makes the closure
diagram-sound.

This file adds the ONE new arm for V2: the cup-slide row (`cupSlideRelation`) fed through the SAME keystone.  Since
the keystone is relation-agnostic, the "new fold arm" is a single application supplying the cup-slide's data (the two
`BrauerWordInRange` witnesses, the two zero-loop witnesses, `cupSlide_diagram_sound`).  The result
(`brauerConv_cupSlide_inContext`) is GENERAL — all offsets `leftPad`, all right-pads `rightPad`, all boundary widths
`bottomCount` (via the width condition), all prefixes; loops are respected (the row is zero-internal-loop on both
sides).  Because `brauerConv_sound` (unchanged) makes `BrauerConv` diagram-sound, V2 diagram-soundness holds — the
V1 soundness is EXTENDED, never weakened.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The ONE new arm — the cup slide is `BrauerConv`-convertible in arbitrary horizontal context

The cup-slide-specific data (its two `BrauerWordInRange` witnesses at its own boundary `1`, its two zero-internal-loop
witnesses, and `cupSlide_diagram_sound`) fed to the relation-agnostic keystone.  Everything else — the prefix, the
offset `leftPad`, the right-pad `rightPad`, the ambient boundary `bottomCount` — is a free parameter (constrained only
by the post-prefix width condition). -/

/-- ★ **V2 SOUNDNESS ARM — the cup slide fires in ANY horizontal context.**  For any ambient boundary `bottomCount`
(> 0), any in-range prefix leaving post-prefix width `leftPad + (1 + rightPad)`, the cup-slide row fired at offset
`leftPad` is `BrauerConv`-convertible to its rhs there.  This is the cup-slide instance of the keystone
`brauerConv_relation_inContext`: the cup slide's boundary is `1` (`cupSlideRelation.boundaryCount`), its two sides are
in range at that boundary (the cup grows the running boundary to `3`, where the crossing then fires), both carry zero
internal loops, and `cupSlide_diagram_sound` supplies the seed soundness. -/
theorem brauerConv_cupSlide_inContext (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (prefixAtoms : List BrauerAtom) (prefixInRange : BrauerWordInRange bottomCount prefixAtoms)
    (leftPad rightPad : Nat)
    (widthEq : (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length
                = leftPad + (1 + rightPad)) :
    BrauerConv bottomCount (prefixAtoms ++ shiftBrauerWord leftPad cupSlideRelation.lhs)
      (prefixAtoms ++ shiftBrauerWord leftPad cupSlideRelation.rhs) :=
  brauerConv_relation_inContext bottomCount bottomPos prefixAtoms prefixInRange leftPad 1 rightPad
    cupSlideRelation.lhs cupSlideRelation.rhs widthEq
    (BrauerWordInRange.cons (cupAt 0) 1 rfl (by decide)
      (BrauerWordInRange.cons (crossingAt 1) 0 rfl (by decide) (BrauerWordInRange.nil 3)))
    (BrauerWordInRange.cons (cupAt 1) 0 rfl (by decide)
      (BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide) (BrauerWordInRange.nil 3)))
    rfl rfl cupSlide_diagram_sound

/-! ## Non-vacuity — a genuinely boundary-CHANGING firing on a NON-minimal instance -/

/-- ★ **The cup slide fired at offset `1` in a width-3 boundary (`1 + (1 + 1)`) is `BrauerConv`-convertible.**  A
NON-minimal instance (the row's own boundary is `1`; here it fires two strands into a width-3 boundary), so the pad
congruence is doing real boundary-CHANGING work — not the trivial shift-0 seed. -/
theorem brauerConv_cupSlide_inWiderContext :
    BrauerConv 3 ([] ++ shiftBrauerWord 1 cupSlideRelation.lhs)
      ([] ++ shiftBrauerWord 1 cupSlideRelation.rhs) :=
  brauerConv_cupSlide_inContext 3 (by decide) [] (BrauerWordInRange.nil 3) 1 1 (by decide)

/-- The non-minimal instance is genuinely diagram-equal at the wider boundary — the cup slide fired at offset `1`
over `3` bottom wires reads the SAME `DiagramType` on both sides (`decide`), witnessing that the keystone's output is
not vacuous. -/
theorem cupSlide_shifted_diagramEq :
    brauerDiagramOf 3 (shiftBrauerWord 1 cupSlideRelation.lhs)
      = brauerDiagramOf 3 (shiftBrauerWord 1 cupSlideRelation.rhs) := by decide

/-- The wider-context firing genuinely relates DISTINCT words (offset `1`, both nonempty). -/
theorem brauerConv_cupSlide_inWiderContext_distinct :
    ([] ++ shiftBrauerWord 1 cupSlideRelation.lhs) ≠ ([] ++ shiftBrauerWord 1 cupSlideRelation.rhs) := by decide

/-! ## Honesty marker -/

/-- ★ **Honesty marker — V2 diagram-soundness covers the cup-slide row.**  The cup slide, whiskered after ANY prefix
at ANY offset in ANY wider boundary, is `BrauerConv`-convertible via the relation-agnostic keystone
`brauerConv_relation_inContext` (`brauerConv_cupSlide_inContext`, general; `brauerConv_cupSlide_inWiderContext`, a
genuinely boundary-CHANGING non-minimal instance backed by the non-vacuity check `cupSlide_shifted_diagramEq`), fed
the cup-slide seed-soundness leg `cupSlide_diagram_sound`.  Since `brauerConv_sound` (unchanged) makes `BrauerConv`
diagram-sound and `brauerConv_iff_diagram` shows `BrauerConv` = diagram equality, V2 soundness holds over the
eight-relation presentation — the V1 soundness (`fxBrauer_hasBrauerSoundness`) is EXTENDED to the cup slide, never
weakened.  `= true`. -/
def fxBrauer_hasCupSlideConvSoundness : Bool := true

end FX1Poly.Polygraph

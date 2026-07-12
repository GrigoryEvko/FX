import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingFaithfulStep
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision

/-! # MODE-COMMUTE r14 (I3) — faithful-engine invariant threading twins (`nextFresh` monotone + fold freshness)

The shipped freshness machinery (`ArcFreshDecision`) threads the fold invariants through the SHIPPED engine:
`stepArcAtom_nextFresh_le` (one shipped step never lowers `nextFresh`), `arcStateFresh_stepArcAtom` /
`arcStateFresh_processArcSpine` (freshness preservation).  The FAITHFUL engine (`stepArcAtomFaithful` /
`processArcSpineFaithful`, the r7 additive sibling with the corrected `2⇒2` crossing arm) had no such twins.  This
file lands the two the general-signature FAITHFUL peel would thread (mirroring the shipped consumers):

  ★ `stepArcAtomFaithful_nextFresh_le` — one faithful step never lowers `nextFresh` (cup `+3`, cap `+1`, cross
    `+0` — a crossing is an in-place transposition, the r7 `stepCrossArc_nextFresh`, so `Nat.le_refl` — box
    `+numProduced`).  By `split` on the four-arm faithful arity match.
  ★ `processArcSpineFaithful_nextFresh_le` — the whole faithful fold never lowers `nextFresh`, structural on the
    spine threading the per-step law.
  ★ `arcStateFresh_processArcSpineFaithful_of_allCupOrCap` — the faithful fold preserves `ArcStateFresh` on the
    REACHABLE cup/cap regime, via the shipped agreement `processArcSpineFaithful_eq_processArcSpine_of_allCupOrCap`
    + `arcStateFresh_processArcSpine` (every walking-adjunction spine is all-cup/cap, so the faithful fold's
    freshness there is exactly the shipped one's — the honest fold-freshness statement; a general-signature
    faithful fold-freshness needs the per-atom boundary-tracking already shipped as the r11
    `arcStateFresh_stepCrossArc` / `arcFaithfulConsCongrStep_cross` for the crossing atom).

These are the `nextFresh`-monotone and fresh legs a faithful general-signature `stepArcAtom` peel threads (the
shipped peel `arcTraceInvariantFresh` threads exactly `arcStateFresh_stepArcAtom` + `stepArcAtom_nextFresh_le`
through its `consCongr` arm).  They feed the walled Mazurkiewicz renaming route (#2043 / WP-AMALG); this file
supplies the bricks, not the keystone.

## What this file does NOT do (the pins stay false PERMANENTLY)

It does NOT build a faithful general-signature peel and does NOT flip the general keystone.
`fxMode_hasArcPeelGeneralSignature` (the arity ceiling) and the #2043 / WP-AMALG residual
`fxMode_hasArcGodementSamePartitionFreshProof` stay `false`; the shipped `stepArcAtom` / `stepArcAtomFaithful` /
`stepCrossArc` are never edited.  This certificate is strictly ADDITIVE.

Raw Lean 4 + Init; structural recursion + `split` on the arity match, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` AND independent `#print axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## `nextFresh` monotonicity of the faithful engine -/

/-- ★ **One faithful step never lowers `nextFresh`.**  The four-arm faithful arity match: a cup adds `+3`, a cap
`+1`, a crossing `+0` (it only permutes `openWires`, the r7 `stepCrossArc_nextFresh` — `Nat.le_refl`), the generic
box `+numProduced`.  The faithful twin of the shipped `stepArcAtom_nextFresh_le` (whose three-arm match has no
crossing arm).  By `split` on the arity match. -/
theorem stepArcAtomFaithful_nextFresh_le {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode) :
    state.nextFresh ≤ (stepArcAtomFaithful state atom).nextFresh := by
  unfold stepArcAtomFaithful
  split
  · exact Nat.le_add_right state.nextFresh 3
  · exact Nat.le_add_right state.nextFresh 1
  · exact Nat.le_refl state.nextFresh
  · exact Nat.le_add_right state.nextFresh _

/-- ★ **The whole faithful fold never lowers `nextFresh`.**  Structural recursion on the spine, the head via
`stepArcAtomFaithful_nextFresh_le` and the tail transitively.  The faithful twin of the shipped fold's
`nextFresh` monotonicity that the peel's `consCongr` arm threads. -/
theorem processArcSpineFaithful_nextFresh_le {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (atoms : List (SpineAtom signature sourceMode targetMode)) → (state : ArcWireState) →
    state.nextFresh ≤ (processArcSpineFaithful state atoms).nextFresh
  | [], state => Nat.le_refl state.nextFresh
  | atom :: rest, state => by
      show state.nextFresh ≤ (processArcSpineFaithful (stepArcAtomFaithful state atom) rest).nextFresh
      exact Nat.le_trans (stepArcAtomFaithful_nextFresh_le state atom)
        (processArcSpineFaithful_nextFresh_le rest (stepArcAtomFaithful state atom))

/-! ## Fold freshness on the reachable cup/cap regime -/

/-- ★ **The faithful fold preserves `ArcStateFresh` on the all-cup/cap regime.**  When every spine atom is a cup or
a cap (`AtomHasCupOrCapArity`) — the reachable walking-adjunction regime — the faithful fold equals the shipped one
(`processArcSpineFaithful_eq_processArcSpine_of_allCupOrCap`), so its freshness preservation is exactly the
shipped `arcStateFresh_processArcSpine`.  The honest faithful fold-freshness twin: on the crossing atoms the
per-step freshness is the r11 `arcStateFresh_stepCrossArc` (window-gated), assembled into the crossing `consCongr`
step `arcFaithfulConsCongrStep_cross`; a general-signature faithful fold threads those, this covers the
cup/cap-only fold outright. -/
theorem arcStateFresh_processArcSpineFaithful_of_allCupOrCap {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (cupOrCap : ∀ (atom : SpineAtom signature sourceMode targetMode), AtomHasCupOrCapArity atom)
    (atoms : List (SpineAtom signature sourceMode targetMode)) (state : ArcWireState)
    (fresh : ArcStateFresh state) :
    ArcStateFresh (processArcSpineFaithful state atoms) := by
  rw [processArcSpineFaithful_eq_processArcSpine_of_allCupOrCap cupOrCap atoms state]
  exact arcStateFresh_processArcSpine atoms state fresh

/-! ## Non-vacuity — the monotonicity fires at the fresh initial seed -/

/-- ★ **Non-vacuous: the faithful fold's `nextFresh` monotonicity holds at the fresh initial seed on the concrete
`crossAtom`.**  From `mk (range 2) [] 2 0 [] []`, firing the toy `crossModeSignature`'s single-crossing spine keeps
`nextFresh` at least `2` (the crossing allocates nothing).  A real instance of `processArcSpineFaithful_nextFresh_le`. -/
theorem arcFaithfulNextFresh_crossSeed_confirms :
    (2 : Nat) ≤ (processArcSpineFaithful (ArcWireState.mk (List.range 2) [] 2 0 [] []) [crossAtom]).nextFresh :=
  processArcSpineFaithful_nextFresh_le [crossAtom] (ArcWireState.mk (List.range 2) [] 2 0 [] [])

/-! ## Honesty markers + pins -/

/-- **Honesty marker — the faithful engine's invariant threading twins are shipped.**  The faithful step never
lowers `nextFresh` (`stepArcAtomFaithful_nextFresh_le`), nor does the whole faithful fold
(`processArcSpineFaithful_nextFresh_le`), and the faithful fold preserves freshness on the reachable all-cup/cap
regime (`arcStateFresh_processArcSpineFaithful_of_allCupOrCap`).  These are the `nextFresh`-monotone + fresh legs a
faithful general-signature peel threads, mirroring the shipped `arcTraceInvariantFresh` consumers.  The shipped
`stepArcAtom` / `stepArcAtomFaithful` are never edited.  `= true`. -/
def fxMode_hasArcFaithfulSpineInvariantThreading : Bool := true

/-- **Honesty pin — the faithful crossing engine is untouched.**  This file only reads `stepArcAtomFaithful` /
`processArcSpineFaithful`; `fxMode_hasArcCrossingFaithfulStep` stays `true`.  `rfl`. -/
theorem arcFaithfulSpineInvariantThreading_faithfulStep_stays_true :
    fxMode_hasArcCrossingFaithfulStep = true := rfl

/-- **Honesty pin — the general-signature peel stays the open keystone.**  These invariant twins supply the
`nextFresh`/fresh legs a faithful peel threads, but they do NOT build the peel;
`fxMode_hasArcPeelGeneralSignature` stays `false`.  `rfl`. -/
theorem arcFaithfulSpineInvariantThreading_generalSignature_stays_false :
    fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — the #2043 / WP-AMALG fresh-partition keystone is untouched** (the Mazurkiewicz renaming
witness).  `fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.  `rfl`. -/
theorem arcFaithfulSpineInvariantThreading_samePartitionFreshProof_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph

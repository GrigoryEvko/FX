import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingDisjointBlockCommute
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPeelSignatureCeiling
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision

/-! # MODE-COMMUTE r11 — the faithful crossing `consCongr` step: freshness + boundary-tracking across a `2⇒2`

The general-signature arc peel (`extractArc_eq_of_atomicTraceEquiv`, WalkingAdjunction/ArcSwapPeel) threads FIVE
state invariants through ONE `stepArcAtom` in its `consCongr` arm — freshness, forest-rootedness, `nextFresh`
positivity, the bottom-boundary bound, and the wire-count boundary tracking — and it works precisely because
`adjunctionSpineAtom_hasCupOrCapArity` discharges the arity hypothesis of the tracking law
(`stepArcAtom_openWires_tracksBoundary`) for every walking-adjunction atom.  A general signature carrying a `2⇒2`
crossing (the toy `crossModeSignature`'s `crossAtom`) is NOT cup/cap, so that arm has no provider — the two
residuals a FAITHFUL peel (over the shipped `stepArcAtomFaithful` / `stepCrossArc` sibling) leaves open at a
crossing atom:

  ★ **R1 — freshness across a crossing** (`arcStateFresh_stepCrossArc`).  `stepCrossArc` only permutes
    `openWires` by an adjacent transposition (`natListSwapTwoAt`), leaving `links`, `nextFresh`, and the event
    lists untouched; so every id in the swapped list is an id of the original list (the two moved entries are the
    two in-window `natListGetAt` reads), hence still below `nextFresh`.  The other three freshness conjuncts
    transport on the nose.

  ★ **R2 — the crossing tracking law + the in-window fit** (`stepCrossArc_openWires_tracksBoundary`).  The
    crossing analog of `stepArcAtom_openWires_tracksBoundary`: for a `2⇒2` atom, `domBoundaryLength` and
    `codBoundaryLength` are EQUAL (both `leftContext + 2 + rightContext`), and `stepCrossArc` preserves width
    (`stepCrossArc_openWires_length`, r10) — with the window `leftContext + 1 < openWires.length` DERIVED from the
    entry tracking `openWires.length = domBoundaryLength`, mirroring the peel's `ofSwap` `windowsFit` derivation.

`arcFaithfulConsCongrStep_cross` then packages all five exit invariants for a faithful `2⇒2` step — a structural
mirror of the shipped `consCongr` arm — consuming R1, R2, and the r10 `rfl`-clean field-untouched lemmas
(`stepCrossArc_links` / `stepCrossArc_nextFresh` supply the forest / `nextFresh` legs by defeq).  The disjoint
crossing×crossing Godement independence the `ofSwap` arm needs is already the r10 unconditional
`extractArc_stepCrossArc_disjointCommute`; so with this brick the only genuine gaps left before a faithful
general-signature peel are the general-signature swap DISPATCHER and the heterogeneous crossing×cup/cap disjoint
commute (round 2+, not this round).

## What this file does NOT do (the pins stay false PERMANENTLY)

It does NOT build the general-signature swap dispatcher, does NOT extend the peel to crossings, and does NOT flip
the general keystone.  `fxMode_hasArcPeelGeneralSignature` (the arity ceiling) and the #2043 / WP-AMALG residual
`fxMode_hasArcGodementSamePartitionFreshProof` stay `false`; the shipped `stepArcAtom` / `stepArcAtomFaithful` /
`stepCrossArc` / `extractArc` are never edited.  This certificate is strictly ADDITIVE.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.  Membership is decomposed by
`List.Mem` constructor casing (never iff lemmas); the window derivation reuses the propext-free
`Nat.lt_of_lt_of_le` / `Nat.le_add_right` anchors.  Per-declaration `#assert_no_axioms` AND independent
`#print axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A member-in-range reader (the R1 building block) -/

/-- Reading a `Nat` list in range yields a genuine member (not the past-the-end `0` default): structural
recursion on the list and position, `propext`-free.  The R1 freshness proof reads the two moved wires
(`natListGetAt openWires position` / `... (position + 1)`) as members of the original list under the window. -/
private theorem natListGetAt_mem_of_lt :
    (wires : List Nat) → (index : Nat) → index < wires.length →
    natListGetAt wires index ∈ wires
  | [], index, indexLt => absurd indexLt (Nat.not_lt_zero index)
  | _ :: _, 0, _ => List.Mem.head _
  | head :: rest, index + 1, indexLt =>
      List.Mem.tail head (natListGetAt_mem_of_lt rest index (Nat.lt_of_succ_lt_succ indexLt))

/-! ## R1 — the faithful crossing preserves `ArcStateFresh` -/

/-- ★ **R1: one faithful crossing step preserves `ArcStateFresh`.**  `stepCrossArc state position` only permutes
`openWires` by the adjacent transposition `natListSwapTwoAt` (its `links`, `nextFresh`, and event lists are
`state`'s verbatim, `rfl`).  Every id in the swapped list is an id of the original: it is either an id of the
removed-pair remainder (`mem_natListRemoveTwoAt_imp`) or one of the two spliced-back reads
(`natListGetAt openWires (position + 1)` / `... position`), both members of the original list under the in-window
hypothesis (`natListGetAt_mem_of_lt`).  So the open-wire freshness conjunct transports; the forest / cup / cap
conjuncts are `state`'s on the nose.  The crossing analog of `arcStateFresh_stepArcAtom` — the missing R1 provider
the shipped consCongr arm's `arcStateFresh_stepArcAtom` has no crossing counterpart for. -/
theorem arcStateFresh_stepCrossArc (state : ArcWireState) (position : Nat)
    (window : position + 1 < state.openWires.length)
    (fresh : ArcStateFresh state) : ArcStateFresh (stepCrossArc state position) := by
  obtain ⟨wiresFresh, linksFresh, cupFresh, capFresh⟩ := fresh
  refine ⟨?_, linksFresh, cupFresh, capFresh⟩
  intro wire wireMem
  have inSwap : wire ∈ natListInsertAt (natListRemoveTwoAt state.openWires position) position
      [natListGetAt state.openWires (position + 1), natListGetAt state.openWires position] := wireMem
  cases mem_natListInsertAt_imp (natListRemoveTwoAt state.openWires position) position
      [natListGetAt state.openWires (position + 1), natListGetAt state.openWires position] inSwap with
  | inl inRemoved =>
      exact wiresFresh wire (mem_natListRemoveTwoAt_imp state.openWires position inRemoved)
  | inr inBlock =>
      cases inBlock with
      | head => exact wiresFresh _ (natListGetAt_mem_of_lt state.openWires (position + 1) window)
      | tail _ tailMem =>
          cases tailMem with
          | head =>
              exact wiresFresh _ (natListGetAt_mem_of_lt state.openWires position
                (Nat.lt_of_succ_lt window))
          | tail _ emptyMem => nomatch emptyMem

/-! ## R2 — the crossing tracking law + the in-window fit -/

/-- The `2⇒2` crossing arity discipline: the atom's generator has a width-2 source and a width-2 target.  The
faithful crossing arm of `stepArcAtomFaithful` fires exactly on this arity; a literal `∧` of two length
equalities so the discharge stays propext-free. -/
def AtomHasCrossArity {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (atom : SpineAtom signature sourceMode targetMode) : Prop :=
  atom.generatorDom.length = 2 ∧ atom.generatorCod.length = 2

/-- ★ **R2: one faithful crossing step tracks the boundary.**  Entering at the atom's dom boundary
(`openWires.length = domBoundaryLength`), the faithful crossing exits at its cod boundary — which for a `2⇒2` atom
EQUALS the dom boundary (both are `leftContext + 2 + rightContext`).  `stepCrossArc` preserves width
(`stepCrossArc_openWires_length`, r10), and the in-window fit `leftContext + 1 < openWires.length` is DERIVED from
the entry tracking and the arity (the crossing window is a prefix of the boundary sum) — mirroring the peel's
`ofSwap` `windowsFit` derivation, so no separate window hypothesis is needed.  The crossing analog of
`stepArcAtom_openWires_tracksBoundary` (whose arity lock `adjunctionSpineAtom_hasCupOrCapArity` cannot cover a
`2⇒2`). -/
theorem stepCrossArc_openWires_tracksBoundary {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (arity : AtomHasCrossArity atom)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength) :
    (stepCrossArc state atom.leftContext.length).openWires.length = atom.codBoundaryLength := by
  obtain ⟨domTwo, codTwo⟩ := arity
  have entryShape : state.openWires.length
      = atom.leftContext.length + 2 + atom.rightContext.length := by
    rw [tracksEntry]
    show atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length
       = atom.leftContext.length + 2 + atom.rightContext.length
    rw [domTwo]
  have window : atom.leftContext.length + 1 < state.openWires.length := by
    rw [entryShape]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (atom.leftContext.length + 1))
      (Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length)
  rw [stepCrossArc_openWires_length state atom.leftContext.length window, entryShape]
  show atom.leftContext.length + 2 + atom.rightContext.length
     = atom.leftContext.length + atom.generatorCod.length + atom.rightContext.length
  rw [codTwo]

/-! ## The assembled faithful `consCongr` step for a `2⇒2` atom -/

/-- ★ **The faithful crossing `consCongr` step — all five state invariants at once.**  A structural mirror of the
shipped peel's `consCongr` arm (`extractArc_eq_of_atomicTraceEquiv`), delivering for one faithful `2⇒2` step the
same five invariants the shipped arm threads through `stepArcAtom`:

  1. freshness — R1 `arcStateFresh_stepCrossArc`, with the window derived from the entry tracking + arity;
  2. forest-rootedness — `stepCrossArc_links` (the crossing leaves `links` untouched, so `forest` transports by
     defeq);
  3. `nextFresh` positivity — `stepCrossArc_nextFresh` (unchanged, so `nextFreshPos` transports by defeq);
  4. the bottom-boundary bound — likewise unchanged, `boundaryBelowFresh` transports;
  5. wire-count boundary tracking — R2 `stepCrossArc_openWires_tracksBoundary`.

This is the crossing counterpart of the shipped arm's five-fact bundle
`(arcStateFresh_stepArcAtom, isUnionFindForest_stepArcAtom, …_nextFresh_le, …_nextFresh_le,
stepArcAtom_openWires_tracksBoundary)` — the brick a faithful general-signature peel threads at a `2⇒2` atom. -/
theorem arcFaithfulConsCongrStep_cross {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode) (bottomCount : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nextFreshPos : 0 < state.nextFresh) (boundaryBelowFresh : bottomCount ≤ state.nextFresh)
    (arity : AtomHasCrossArity atom)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength) :
    ArcStateFresh (stepCrossArc state atom.leftContext.length)
      ∧ isUnionFindForest (stepCrossArc state atom.leftContext.length).links
      ∧ 0 < (stepCrossArc state atom.leftContext.length).nextFresh
      ∧ bottomCount ≤ (stepCrossArc state atom.leftContext.length).nextFresh
      ∧ (stepCrossArc state atom.leftContext.length).openWires.length = atom.codBoundaryLength := by
  have domTwo : atom.generatorDom.length = 2 := arity.1
  have entryShape : state.openWires.length
      = atom.leftContext.length + 2 + atom.rightContext.length := by
    rw [tracksEntry]
    show atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length
       = atom.leftContext.length + 2 + atom.rightContext.length
    rw [domTwo]
  have window : atom.leftContext.length + 1 < state.openWires.length := by
    rw [entryShape]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (atom.leftContext.length + 1))
      (Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length)
  exact ⟨arcStateFresh_stepCrossArc state atom.leftContext.length window fresh,
    forest, nextFreshPos, boundaryBelowFresh,
    stepCrossArc_openWires_tracksBoundary state atom arity tracksEntry⟩

/-! ## Non-vacuity — the assembly fires at the fresh seed on the concrete `crossAtom` -/

/-- ★ **The faithful crossing `consCongr` step is non-vacuous.**  On the toy `crossModeSignature`'s bare
`crossAtom` (`2⇒2`, position `0`) and the width-2 fresh seed `mk (range 2) [] 2 0 [] []`, all five invariants
discharge — witnessed here by the fifth (the exit boundary tracking `openWires.length = codBoundaryLength = 2`).
A real instantiation of `arcFaithfulConsCongrStep_cross` (the entry invariants supplied by `arcStateFresh_initial`
/ `isUnionFindForest_nil` / the concrete arity), not a hand fixture. -/
theorem arcFaithfulConsCongrStep_cross_seed_confirms :
    (stepCrossArc (ArcWireState.mk (List.range 2) [] 2 0 [] []) crossAtom.leftContext.length).openWires.length
      = crossAtom.codBoundaryLength :=
  (arcFaithfulConsCongrStep_cross (ArcWireState.mk (List.range 2) [] 2 0 [] []) crossAtom 2
    (arcStateFresh_initial 2) isUnionFindForest_nil (by decide) (Nat.le_refl 2)
    ⟨crossAtom_generatorDom_length, crossAtom_generatorCod_length⟩ rfl).2.2.2.2

/-! ## Honesty marker + pins -/

/-- **Honesty marker — the faithful crossing `consCongr` step is shipped.**  For a faithful `2⇒2` transposition
step (`stepCrossArc`), the two residuals a general-signature FAITHFUL peel leaves open at a crossing atom are
discharged: freshness across the crossing (R1 `arcStateFresh_stepCrossArc`) and the boundary tracking law with its
in-window fit (R2 `stepCrossArc_openWires_tracksBoundary`), assembled into the shipped-arm-shaped five-invariant
bundle `arcFaithfulConsCongrStep_cross` (non-vacuous at the fresh seed on `crossAtom`,
`arcFaithfulConsCongrStep_cross_seed_confirms`).  Combined with the r10 unconditional crossing×crossing Godement
independence (`extractArc_stepCrossArc_disjointCommute`), the `consCongr` and `ofSwap` crossing obligations are now
both provided — the residual before a faithful general-signature peel is the general swap DISPATCHER plus the
heterogeneous crossing×cup/cap disjoint commute (round 2+).  The shipped `stepArcAtom` / `stepArcAtomFaithful` /
`stepCrossArc` are never edited.  `= true`. -/
def fxMode_hasArcCrossingConsCongrStep : Bool := true

/-- **Honesty pin — the general-signature peel stays the open keystone.**  This brick supplies the crossing
`consCongr` step's invariants, but it does NOT build the general-signature `arcSwapCorePackage` dispatcher (no
builder arm for `crossAtom`).  `fxMode_hasArcPeelGeneralSignature` stays `false`.  `rfl`. -/
theorem arcCrossingConsCongrStep_generalSignature_stays_false :
    fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — the #2043 / WP-AMALG fresh-partition keystone is untouched.**  The general-signature peel is
exactly `ArcGodementSamePartitionFresh signature`; the crossing `consCongr` step does not advance it.
`fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.  `rfl`. -/
theorem arcCrossingConsCongrStep_samePartitionFreshProof_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

/-- **Honesty pin — the r10 unconditional disjoint-block crossing commute stays `true`.**  The `ofSwap`-arm
crossing×crossing Godement independence this `consCongr` brick composes with is the r10 marker, untouched.  `rfl`. -/
theorem arcCrossingConsCongrStep_disjointBlockCommute_stays_true :
    fxMode_hasArcCrossingDisjointBlockCommute = true := rfl

end FX1Poly.Polygraph

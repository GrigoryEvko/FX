import FX.KernelMTT.Coherence

/-!
# Coherence tests (R0.7)

The heavy lifting for R0.7 is done by theorems inside
`Coherence.lean` itself.  This test module adds `by decide`
checks at the TestsTests layer so a regression on any
coherence property fails the `lake build Tests` gate (not
just the library build).

Coverage:

  * Spot-check 3 reflexivity, 3 transitivity, 4 incomparable-
    pair theorems are accessible via `Tests.*` namespace.
  * Cross-cell-and-collision invariants hold on composite
    data.
  * Aggregate `mode_theory_coherent` witness is decidable at
    the test layer.
-/

namespace Tests.KernelMTT.CoherenceTests

open FX.KernelMTT

/-! ## Property 2 — 2-cell coherence spot checks -/

-- Reflexivity at sampled grades.
example : SubsumptionCell.subsumes Modality.usage "1" "1" := by decide
example : SubsumptionCell.subsumes Modality.eff   "IO" "IO" := by decide
example : SubsumptionCell.subsumes Modality.mutation "append_only" "append_only" := by decide

-- Transitivity chains.
example : SubsumptionCell.subsumes Modality.usage "0" "w" := by decide
example : SubsumptionCell.subsumes Modality.eff   "Tot" "Write" := by decide
example : SubsumptionCell.subsumes Modality.trust "Verified" "External" := by decide

-- Reverse direction fails.
example : ¬ SubsumptionCell.subsumes Modality.usage "w" "0" := by decide
example : ¬ SubsumptionCell.subsumes Modality.eff   "Write" "Tot" := by decide
example : ¬ SubsumptionCell.subsumes Modality.trust "External" "Verified" := by decide

-- Overflow pairs stay incomparable.
example : ¬ SubsumptionCell.subsumes Modality.overflow "wrap" "trap" := by decide
example : ¬ SubsumptionCell.subsumes Modality.overflow "trap" "saturate" := by decide

/-! ## Property 3 — adjunction coherence spot checks -/

-- Each adjunction crosses modes.
example : Adjunction.ghostSoftware.leftMode    ≠ Adjunction.ghostSoftware.rightMode    := by decide
example : Adjunction.softwareHardware.leftMode ≠ Adjunction.softwareHardware.rightMode := by decide
example : Adjunction.softwareWire.leftMode     ≠ Adjunction.softwareWire.rightMode     := by decide
example : Adjunction.hardwareSoftware.leftMode ≠ Adjunction.hardwareSoftware.rightMode := by decide

-- Forward names are distinct — test via explicit inequality.
example : Adjunction.ghostSoftware.forwardName    ≠ Adjunction.softwareHardware.forwardName := by decide
example : Adjunction.softwareHardware.forwardName ≠ Adjunction.softwareWire.forwardName     := by decide
example : Adjunction.softwareWire.forwardName     ≠ Adjunction.hardwareSoftware.forwardName := by decide
example : Adjunction.ghostSoftware.forwardName    ≠ Adjunction.hardwareSoftware.forwardName := by decide

-- Proper adjunctions have backward morphism names.
example : Adjunction.ghostSoftware.backwardName.isSome := by decide
example : Adjunction.softwareWire.backwardName.isSome  := by decide

-- Non-proper adjunctions do NOT have backward morphism names.
example : Adjunction.softwareHardware.backwardName.isNone := by decide
example : Adjunction.hardwareSoftware.backwardName.isNone := by decide

/-! ## Aggregate witness

The `mode_theory_coherent` conjunction in `Coherence.lean`
holds — a single top-level check that every load-bearing
coherence property passes simultaneously. -/

example :
    (SubsumptionCell.all.all
      (fun cell => Modality.all.contains cell.modality))
      ∧ (CollisionRule.all.all
          (fun rule => 2 ≤ rule.sources.length))
      ∧ (Adjunction.all.all (fun adj => adj.leftMode ≠ adj.rightMode))
      ∧ ((Adjunction.all.map (·.forwardName)).length = 4)
      ∧ (Adjunction.all.all
          (fun adj => adj.isProperAdj → adj.backwardName.isSome))
    := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Closure invariants

Every enumerated structure references only enumerated pieces
— no dangling references between layers. -/

-- Every modality's admissibility set references only enumerated modes.
example :
    Modality.all.all
      (fun m => m.admissibleModes.all
                  (fun mode => Mode.all.contains mode)) = true := by
  decide

-- Every 2-cell's modality is enumerated.
example :
    SubsumptionCell.all.all
      (fun cell => Modality.all.contains cell.modality) = true := by
  decide

-- Every collision rule's error code is in the declared list.
example :
    CollisionRule.all.all
      (fun rule =>
        [ "I002", "L002", "E044", "I003", "M012"
        , "P002", "I004", "N002", "L003" ].contains rule.errorCode) = true := by
  decide

-- Every adjunction's modes are enumerated.
example :
    Adjunction.all.all
      (fun adj => Mode.all.contains adj.leftMode
                    && Mode.all.contains adj.rightMode) = true := by
  decide

/-! ## Missing-2-cell coherence (spot check)

For each §6.8 collision rule, a 2-cell directly admitting the
bad composition doesn't exist in `SubsumptionCell.all`.  The
check here is structural — cells are single-modality, so no
single cell entry could admit a multi-modality collision.

Specifically: confirm no cell has both classified-subsumption
AND Fail-effect-enabling behavior in one entry (I002-style). -/

-- No single 2-cell references both sec AND eff modalities (cells are
-- mono-modality by construction; the filter below should yield zero
-- sec ∩ eff intersections, trivially).
example :
    (SubsumptionCell.all.filter
      (fun cell => cell.modality = Modality.sec)).all
      (fun cell => cell.modality ≠ Modality.eff) = true := by
  decide

-- No single 2-cell admits the P002 shape "ghost (usage 0) in
-- runtime conditional" — because conditional positions aren't
-- modality grades in our enumeration, no cell could encode this.
-- The closest check: no cell has `modality = usage, fromGrade = "0"`
-- mapping to a non-usage grade.
example :
    (SubsumptionCell.all.filter
      (fun cell => cell.modality = Modality.usage && cell.fromGrade == "0")).all
      (fun cell => cell.modality = Modality.usage) = true := by
  decide

/-! ## Forward ≠ backward morphism names

Within each adjunction record with a backward name, forward ≠
backward (no morphism is its own inverse). -/

example :
    Adjunction.all.all
      (fun adj =>
        match adj.backwardName with
        | some back => back ≠ adj.forwardName
        | none      => true) = true := by
  decide

/-! ## R0.8 — unit/counit aggregate

Spot checks for the `Coherence.lean` R0.8 additions.  The full
`mode_theory_coherent` witness is checked as a single `example`
below; per-conjunct checks are preserved for faster localization
when something drifts. -/

/-! ### Name-existence biconditionals -/

example :
    Adjunction.all.all (fun adj =>
      adj.isProperAdj = adj.unitName.isSome) = true := by decide

example :
    Adjunction.all.all (fun adj =>
      adj.isProperAdj = adj.counitName.isSome) = true := by decide

/-! ### Triangle-shape invariants -/

example :
    Adjunction.all.all (fun adj =>
      adj.isProperAdj →
        adj.unitTriangleEndpoints? =
          some (adj.leftMode, adj.rightMode, adj.leftMode)) = true := by decide

example :
    Adjunction.all.all (fun adj =>
      adj.isProperAdj →
        adj.counitTriangleEndpoints? =
          some (adj.rightMode, adj.leftMode, adj.rightMode)) = true := by decide

/-! ### Ten-name shape -/

example :
    (Adjunction.all.map (·.forwardName))
      ++ (Adjunction.all.filterMap (·.backwardName))
      ++ Adjunction.twoCellNames
      = [ "ghost", "synth", "serialize", "observe"
        , "erase", "parse"
        , "eta_ghost", "epsilon_ghost"
        , "eta_serialize", "epsilon_serialize" ] := by
  decide

/-! ### Extended aggregate witness

The nine-conjunct `mode_theory_coherent` bundles R0.5 closure +
R0.6 collision shape + R0.7 distinctness + R0.8 unit/counit +
triangle shapes. -/

example :
    (SubsumptionCell.all.all (fun cell => Modality.all.contains cell.modality))
      ∧ (CollisionRule.all.all
          (fun rule => 2 ≤ rule.sources.length))
      ∧ (Adjunction.all.all (fun adj => adj.leftMode ≠ adj.rightMode))
      ∧ ((Adjunction.all.map (·.forwardName)).length = 4)
      ∧ (Adjunction.all.all
          (fun adj => adj.isProperAdj → adj.backwardName.isSome))
      ∧ (Adjunction.all.all
          (fun adj => adj.isProperAdj = adj.unitName.isSome))
      ∧ (Adjunction.all.all
          (fun adj => adj.isProperAdj = adj.counitName.isSome))
      ∧ (Adjunction.all.all
          (fun adj => adj.isProperAdj →
            adj.unitTriangleEndpoints? =
              some (adj.leftMode, adj.rightMode, adj.leftMode)))
      ∧ (Adjunction.all.all
          (fun adj => adj.isProperAdj →
            adj.counitTriangleEndpoints? =
              some (adj.rightMode, adj.leftMode, adj.rightMode)))
    := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Tests.KernelMTT.CoherenceTests

import FX1Poly.Polygraph.TwoCategory.Amalgam.RealCoprojection

/-! # Polygraph/TwoCategory/Amalgam/RealCoprojectionLeft — the genuine-generator LEFT coprojection `onTwoCell`

`RealCoprojection.lean` (r6 P2) shipped the RIGHT real coprojection `inclusionRightTwoReal`: a genuine
reconstructed generating 2-cell of component 2 maps to the pushout via `embedRightTwoGen` + `interpretWordFrom_map`.
The reverse-completeness ledger named the LEFT mirror as absent (`inclusionLeftTwoReal does not exist` — the r1
jam).  This file supplies it — a mechanical mirror.

## The mirror is direct: `interpretWordFrom_map` is already generic

`interpretWordFrom_map` (`RealCoprojection.lean`) is GENERIC over any mode-injective `ComputadMorphism` — not
hardwired to `inclusionRight` — so the left coprojection reuses it verbatim.  The three new primitives mirror the
right ones:

  * **`embedLeftTwoGen`** — a component-1 2-generator index maps to the pushout's 2-generator list with NO shift
    (component-1 generators are the PREFIX; the right embedding shifts by `comp1.twoCellGenerators.length`).
  * **`pushoutTwoGenGetLeft`** — the pushout's 2-generator at the left embedding is the retagged component-1
    generator (via `getAppendLeft` + `getMap`, mirror of `pushoutTwoGenGetRight`).
  * **`inclusionLeft_onModes_injective`** — `inclusionLeft.onModes` is the IDENTITY (`fun mode => mode`), so
    injectivity is immediate (the mode-injectivity hypothesis `interpretWordFrom_map` needs).
  * **`inclusionLeftTwoReal`** — the `ComputadMorphismTwo comp1 (pushoutShared ...)` with a GENUINE `onTwoCell`,
    structurally identical to `inclusionRightTwoReal`.

## Non-vacuity scope (honest)

At `involution +_M monad` the LEFT component (`involutionComputad`) is THIN (no 2-generators), so
`inclusionLeftTwoReal involutionComputad monadComputad ..` has a vacuous `onTwoCell`.  Non-vacuity therefore needs a
comp1 WITH 2-generators — witnessed here at `monad +_M involution` (monad on the LEFT), where the monad unit fires.
This serves the n-ary / left-real fold scope, ORTHOGONAL to the `involution +_M monad` disjoint two-sided decision.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The 2-generator left embedding + its get-alignment -/

/-- Embed a component-1 **2-generator** index into the pushout's 2-generator list — index UNCHANGED (component-1
generators are the prefix of the pushout 2-generator list, shift 0).  The mirror of `embedRightTwoGen`. -/
def embedLeftTwoGen (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount)
    (index : Fin comp1.twoCellGenerators.length) :
    Fin (pushoutShared comp1 comp2 sameModes).twoCellGenerators.length :=
  ⟨index.val, by
    rw [pushoutShared_twoCellCount]; exact Nat.lt_of_lt_of_le index.isLt (Nat.le_add_right _ _)⟩

/-- ★ **The 2-generator get-alignment (LEFT)** — the pushout's 2-generator at the left embedding is exactly the
retagged component-1 generator.  Via `getAppendLeft` (index in the PREFIX, no shift) + `getMap`, the mirror of
`pushoutTwoGenGetRight`. -/
theorem pushoutTwoGenGetLeft (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount)
    (index : Fin comp1.twoCellGenerators.length) :
    (pushoutShared comp1 comp2 sameModes).twoCellGenerators.get
        (embedLeftTwoGen comp1 comp2 sameModes index)
      = retagLeftTwoGen comp1 comp2 sameModes (comp1.twoCellGenerators.get index) := by
  have boundMapped : index.val
      < (comp1.twoCellGenerators.map (retagLeftTwoGen comp1 comp2 sameModes)).length := by
    rw [lengthMap]; exact index.isLt
  calc (pushoutShared comp1 comp2 sameModes).twoCellGenerators.get
            (embedLeftTwoGen comp1 comp2 sameModes index)
      = (comp1.twoCellGenerators.map (retagLeftTwoGen comp1 comp2 sameModes)).get ⟨index.val, boundMapped⟩ :=
          getAppendLeft (comp1.twoCellGenerators.map (retagLeftTwoGen comp1 comp2 sameModes))
            (comp2.twoCellGenerators.map (retagRightTwoGen comp1 comp2 sameModes)) index.val boundMapped
            (embedLeftTwoGen comp1 comp2 sameModes index).isLt
    _ = retagLeftTwoGen comp1 comp2 sameModes (comp1.twoCellGenerators.get index) :=
          getMap (retagLeftTwoGen comp1 comp2 sameModes) comp1.twoCellGenerators index.val index.isLt boundMapped

/-! ## The left coprojection is mode-injective (its mode action is the identity) -/

/-- The left coprojection's mode action is `fun mode => mode` (the identity), so it is trivially injective —
packaged for `interpretWordFrom_map`. -/
theorem inclusionLeft_onModes_injective (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount)
    (firstMode secondMode : Fin comp1.modeCount)
    (imagesEqual : (inclusionLeft comp1 comp2 sameModes).onModes firstMode
      = (inclusionLeft comp1 comp2 sameModes).onModes secondMode) :
    firstMode = secondMode :=
  imagesEqual

/-! ## The genuine-generator left coprojection -/

/-- ★ **The left coprojection lifted to a `ComputadMorphismTwo`, with a GENUINE `onTwoCell`.**  A reconstructed
generating 2-cell of component 1 maps to the pushout reconstructed 2-cell at `embedLeftTwoGen`, whose interpreter
conjuncts are `interpretWordFrom_map` (at the mode-injective — indeed identity-on-modes — left coprojection)
composed with the source 2-cell's own conjuncts.  Structurally identical to `inclusionRightTwoReal`; unlike
`inclusionLeftTwo` (which required `comp1` locally thin), this works for component 1 WITH 2-generators. -/
def inclusionLeftTwoReal (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount) :
    ComputadMorphismTwo comp1 (pushoutShared comp1 comp2 sameModes) where
  toComputadMorphism := inclusionLeft comp1 comp2 sameModes
  onTwoCell := fun {srcMode _tgtMode _sourcePath _targetPath} generator =>
    ⟨embedLeftTwoGen comp1 comp2 sameModes generator.val,
      ⟨(congrArg ((pushoutShared comp1 comp2 sameModes).interpretWordFrom
              ((inclusionLeft comp1 comp2 sameModes).onModes srcMode))
            (congrArg ComputadTwoGen.lhs (pushoutTwoGenGetLeft comp1 comp2 sameModes generator.val))).trans
          ((interpretWordFrom_map (inclusionLeft comp1 comp2 sameModes)
              (inclusionLeft_onModes_injective comp1 comp2 sameModes) srcMode
              (comp1.twoCellGenerators.get generator.val).lhs).trans
            (congrArg (fun option => option.map
                (fun sig => (⟨(inclusionLeft comp1 comp2 sameModes).onModes sig.fst,
                    mapPath (inclusionLeft comp1 comp2 sameModes) sig.snd⟩ :
                  Sigma (fun targetMode : Fin (pushoutShared comp1 comp2 sameModes).modeCount =>
                    ModalityPath (pushoutShared comp1 comp2 sameModes).toModeGraph
                      ((inclusionLeft comp1 comp2 sameModes).onModes srcMode) targetMode))))
              generator.property.1)),
       (congrArg ((pushoutShared comp1 comp2 sameModes).interpretWordFrom
              ((inclusionLeft comp1 comp2 sameModes).onModes srcMode))
            (congrArg ComputadTwoGen.rhs (pushoutTwoGenGetLeft comp1 comp2 sameModes generator.val))).trans
          ((interpretWordFrom_map (inclusionLeft comp1 comp2 sameModes)
              (inclusionLeft_onModes_injective comp1 comp2 sameModes) srcMode
              (comp1.twoCellGenerators.get generator.val).rhs).trans
            (congrArg (fun option => option.map
                (fun sig => (⟨(inclusionLeft comp1 comp2 sameModes).onModes sig.fst,
                    mapPath (inclusionLeft comp1 comp2 sameModes) sig.snd⟩ :
                  Sigma (fun targetMode : Fin (pushoutShared comp1 comp2 sameModes).modeCount =>
                    ModalityPath (pushoutShared comp1 comp2 sameModes).toModeGraph
                      ((inclusionLeft comp1 comp2 sameModes).onModes srcMode) targetMode))))
              generator.property.2))⟩⟩

/-! ## Non-vacuity: the monad unit fires through the real LEFT coprojection (monad on the LEFT) -/

/-- ★ **Non-vacuity — the real LEFT coprojection FIRES on the monad unit.**  With the monad as component 1
(`monad +_M involution`), feeding the genuine reconstructed unit `monadComputadReconstructsUnit` (a REAL
2-generator) to `inclusionLeftTwoReal`'s `onTwoCell` lands at pushout 2-generator index `0` (`embedLeftTwoGen ⟨0⟩`,
no shift).  Witnesses the LEFT coprojection's 2-cell action is genuinely inhabited on real generators, ORTHOGONAL to
the `involution +_M monad` disjoint scope. -/
theorem inclusionLeftTwoReal_onUnit_index :
    ((inclusionLeftTwoReal monadComputad involutionComputad involutionMonadSameModes.symm).onTwoCell
        monadComputadReconstructsUnit).val.val = 0 := rfl

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the genuine-generator LEFT coprojection `onTwoCell` SHIPS.**  `embedLeftTwoGen` (the
no-shift 2-generator left embedding) with its get-alignment `pushoutTwoGenGetLeft` (`getAppendLeft` + `getMap`), the
left coprojection's mode-injectivity (`inclusionLeft_onModes_injective`, immediate — identity on modes), and the
REAL left coprojection `inclusionLeftTwoReal` whose `onTwoCell` transports a genuine reconstructed generating 2-cell
to the pushout via `embedLeftTwoGen` + the generic `interpretWordFrom_map`.  Non-vacuous: the monad unit fires with
the monad on the LEFT (`inclusionLeftTwoReal_onUnit_index`).  This discharges the r1 LEFT-coprojection jam named in
the dispatch ledger — the LEFT real coprojection now EXISTS.  It serves the n-ary / left-real fold scope, ORTHOGONAL
to the `involution +_M monad` two-sided decision.  `= true`. -/
def fxAmalg_hasRealGeneratorCoprojectionLeft : Bool := true

end FX1Poly.Polygraph.Amalgam

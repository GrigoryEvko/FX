import FX1Poly.Polygraph.TwoCategory.Amalgam.MapCell
import FX1Poly.Polygraph.TwoCategory.Amalgam.Witness

/-! # Polygraph/TwoCategory/Amalgam/RealCoprojection — the genuine-generator coprojection `onTwoCell`
(WP-AMALG r6, P2)

`MapCell.lean` (r4) lifted the two pushout coprojections to `ComputadMorphismTwo` only for NO-2-generator
(locally-thin) components (`inclusionLeftTwo` / `inclusionRightTwo`, whose `onTwoCell` is vacuous `Fin.elim0`).
The residual it named (`fxAmalg_hasRealGeneratorCoprojection = false`) is the action of a coprojection on a
GENUINE generating 2-cell: `monadComputad`'s `eta` / `mu` under the right embedding.  This file closes it.

## The load-bearing lemma: `interpretWordFrom_map`

A coprojection `morphism : ComputadMorphism source target` acts on 1-generators by `onModalityGenerators` and on
modes by `onModes`, preserving the recorded endpoints (`endpointsPreserved`).  The word-to-`ModalityPath`
interpreter `interpretWordFrom` therefore COMMUTES with the morphism: interpreting a `morphism`-mapped word from a
`morphism`-mapped seed is the `mapPath`-image of interpreting the original word.  Formally

  `target.interpretWordFrom (onModes src) (word.map onModalityGenerators)
     = (source.interpretWordFrom src word).map (fun sig => ⟨onModes sig.fst, mapPath morphism sig.snd⟩)`

by STRUCTURAL induction on `word`; the `cons` step bridges the two interpreter `dite`s through the abstract
`endpointsPreserved` field (a genuine propositional endpoint rewrite, handled by the cons-form helper
`interpretWordFrom_cons_of_get` whose recorded endpoint is a free variable).  The `Modality` witnesses are
proof-irrelevant subtypes, so the two reconstructed paths coincide by `Subtype.ext rfl`.

## From the lemma to `onTwoCell`

A source `ReconstructedTwoCell sourcePath targetPath = ⟨j, ⟨hlhs, hrhs⟩⟩` maps to the pushout reconstructed 2-cell
at index `embedRightTwoGen j` (the 2-generator analogue of `embedRightLetter`), whose `lhs` / `rhs` words are the
`embedRightLetter`-retags of `(comp2.twoCellGenerators.get j)`'s words (the get-alignment
`pushoutTwoGenGetRight`).  Each interpreter conjunct is then `interpretWordFrom_map` composed with `hlhs` / `hrhs`.
This populates the RIGHT coprojection's `onTwoCell` on ALL its generators, giving `inclusionRightTwoReal`, and
flips `fxAmalg_hasRealGeneratorCoprojection`.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## Propext-free `Option.map` plumbing -/

/-- `(some x).map f = some (f x)` — definitional. -/
theorem optionMapSome {Source Target : Type} (mapper : Source → Target) (value : Source) :
    (some value).map mapper = some (mapper value) := rfl

/-- `none.map f = none` — definitional. -/
theorem optionMapNone {Source Target : Type} (mapper : Source → Target) :
    (none : Option Source).map mapper = none := rfl

/-- `(o.map f).map g = o.map (g ∘ f)`, propext-free (`cases` on the option). -/
theorem optionMapMap {A B C : Type} (first : A → B) (second : B → C) (option : Option A) :
    (option.map first).map second = option.map (fun value => second (first value)) := by
  cases option with
  | none => rfl
  | some _ => rfl

/-- Two `Option.map`s of the same option agree when their mappers agree pointwise, propext-free. -/
theorem optionMapCongr {Source Target : Type} {first second : Source → Target}
    (option : Option Source) (mappersEqual : ∀ value, first value = second value) :
    option.map first = option.map second := by
  cases option with
  | none => rfl
  | some value => exact congrArg some (mappersEqual value)

/-! ## The interpreter cons-form with an abstract recorded endpoint

`interpretWordFrom` recurses by looking up `computad.modalityGenerators.get index` inside its `dite`, blocking a
propositional rewrite of that lookup.  This lemma restates the `cons` step with the recorded endpoint pair `gv` a
FREE VARIABLE plus a proof `hget : get index = gv`, so `cases hget` substitutes it and the body reduces by `rfl`.
The morphism-image lookup (`endpointsPreserved`) is then a legal `gv`. -/

/-- The `cons` unfolding of `interpretWordFrom` with the recorded endpoint abstracted as `gv`.  `cases hget` fixes
`gv := get index`; unfolding the interpreter exposes its `match … | none | some`, which agrees with `Option.map`
after casing the recursive result. -/
theorem interpretWordFrom_cons_of_get (computad : ModeComputad) (src : Fin computad.modeCount)
    (index : Fin computad.modalityGenerators.length) (rest : List (Fin computad.modalityGenerators.length))
    (gv : Fin computad.modeCount × Fin computad.modeCount)
    (hget : computad.modalityGenerators.get index = gv) :
    computad.interpretWordFrom src (index :: rest)
      = if headMatch : gv.1 = src then
          (computad.interpretWordFrom gv.2 rest).map
            (fun restInterpreted =>
              ⟨restInterpreted.fst,
                ModalityPath.cons
                  (⟨index, hget.trans (congrArg (fun endpointSource => (endpointSource, gv.2)) headMatch)⟩ :
                    computad.Modality src gv.2)
                  restInterpreted.snd⟩)
        else none := by
  cases hget
  simp only [ModeComputad.interpretWordFrom]
  split
  · cases computad.interpretWordFrom (computad.modalityGenerators.get index).2 rest <;> rfl
  · rfl

/-! ## The interpreter commutes with a mode-injective computad morphism -/

/-- ★ **`interpretWordFrom` commutes with a mode-injective `ComputadMorphism`** — interpreting the morphism-mapped
word from the morphism-mapped seed is the `mapPath`-image of interpreting the original word.  STRUCTURAL on `word`;
the `cons` step bridges the two interpreter `dite`s through the abstract `endpointsPreserved` field, and the
reconstructed `Modality` witnesses coincide by definitional proof-irrelevance.  Mode injectivity is REQUIRED: a
non-injective `onModes` could let the target interpreter chain a step the source rejected (an endpoint collision),
returning `some` where the source returns `none`.  The pushout coprojections have `onModes = castFinAcrossCount`,
which is `.val`-preserving hence injective. -/
theorem interpretWordFrom_map {source target : ModeComputad} (morphism : ComputadMorphism source target)
    (onModesInjective : ∀ (firstMode secondMode : Fin source.modeCount),
      morphism.onModes firstMode = morphism.onModes secondMode → firstMode = secondMode) :
    (srcMode : Fin source.modeCount) →
    (word : List (Fin source.modalityGenerators.length)) →
    target.interpretWordFrom (morphism.onModes srcMode) (word.map morphism.onModalityGenerators)
      = (source.interpretWordFrom srcMode word).map
          (fun sig => (⟨morphism.onModes sig.fst, mapPath morphism sig.snd⟩ :
            Sigma (fun targetMode : Fin target.modeCount =>
              ModalityPath target.toModeGraph (morphism.onModes srcMode) targetMode)))
  | srcMode, [] => rfl
  | srcMode, index :: rest => by
      -- name the recorded source endpoints, carried through the morphism
      have hendpoints := morphism.endpointsPreserved index
      -- expose the SOURCE interpreter's cons step (recorded endpoint = get index, by rfl)
      rw [interpretWordFrom_cons_of_get source srcMode index rest
            (source.modalityGenerators.get index) rfl]
      -- expose the TARGET interpreter's cons step (recorded endpoint = the morphism image, via endpointsPreserved)
      show target.interpretWordFrom (morphism.onModes srcMode)
            (morphism.onModalityGenerators index :: rest.map morphism.onModalityGenerators) = _
      rw [interpretWordFrom_cons_of_get target (morphism.onModes srcMode)
            (morphism.onModalityGenerators index) (rest.map morphism.onModalityGenerators)
            (morphism.onModes (source.modalityGenerators.get index).1,
             morphism.onModes (source.modalityGenerators.get index).2) hendpoints]
      by_cases headMatch : (source.modalityGenerators.get index).1 = srcMode
      · -- both dites fire; recurse via IH, then repackage the cons head (proof-irrelevant)
        rw [dif_pos headMatch, dif_pos (congrArg morphism.onModes headMatch),
            interpretWordFrom_map morphism onModesInjective (source.modalityGenerators.get index).2 rest,
            optionMapMap, optionMapMap]
        exact optionMapCongr (source.interpretWordFrom (source.modalityGenerators.get index).2 rest)
          (fun _ => rfl)
      · -- neither dite fires: source fails to chain, and injectivity forbids the target chaining
        rw [dif_neg headMatch,
            dif_neg (fun collision => headMatch (onModesInjective _ _ collision))]
        rfl

/-! ## The right coprojection is mode-injective -/

/-- `castFinAcrossCount` is injective — it preserves `.val`, so equal images have equal `.val`, hence equal `Fin`
values by `Fin.ext`.  This is the mode-injectivity hypothesis `interpretWordFrom_map` needs at the right
coprojection. -/
theorem castFinAcrossCount_injective {source target : Nat} (sameCount : source = target)
    (firstIndex secondIndex : Fin target)
    (imagesEqual : castFinAcrossCount sameCount firstIndex = castFinAcrossCount sameCount secondIndex) :
    firstIndex = secondIndex :=
  Fin.ext (by
    have valsEqual : (castFinAcrossCount sameCount firstIndex).val
        = (castFinAcrossCount sameCount secondIndex).val := congrArg Fin.val imagesEqual
    rw [castFinAcrossCount_val, castFinAcrossCount_val] at valsEqual
    exact valsEqual)

/-- The right coprojection's mode action (`castFinAcrossCount sameModes`) is injective — packaged for
`interpretWordFrom_map`. -/
theorem inclusionRight_onModes_injective (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount)
    (firstMode secondMode : Fin comp2.modeCount)
    (imagesEqual : (inclusionRight comp1 comp2 sameModes).onModes firstMode
      = (inclusionRight comp1 comp2 sameModes).onModes secondMode) :
    firstMode = secondMode :=
  castFinAcrossCount_injective sameModes firstMode secondMode imagesEqual

/-! ## The 2-generator right embedding + its get-alignment -/

/-- Embed a component-2 **2-generator** index into the pushout's 2-generator list — index shifted by
`comp1.twoCellGenerators.length` (the 2-generator analogue of `embedRightLetter`). -/
def embedRightTwoGen (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount)
    (index : Fin comp2.twoCellGenerators.length) :
    Fin (pushoutShared comp1 comp2 sameModes).twoCellGenerators.length :=
  ⟨comp1.twoCellGenerators.length + index.val, by
    rw [pushoutShared_twoCellCount]; exact Nat.add_lt_add_left index.isLt _⟩

/-- ★ **The 2-generator get-alignment** — the pushout's 2-generator at the right embedding is exactly the retagged
component-2 generator.  A `getValCongr` (bridging `comp1.twoCellGenerators.length` and the retag-mapped first
part's length) + `getAppendRight` + `getMap`, the 2-generator mirror of `inclusionRight.endpointsPreserved`. -/
theorem pushoutTwoGenGetRight (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount)
    (index : Fin comp2.twoCellGenerators.length) :
    (pushoutShared comp1 comp2 sameModes).twoCellGenerators.get
        (embedRightTwoGen comp1 comp2 sameModes index)
      = retagRightTwoGen comp1 comp2 sameModes (comp2.twoCellGenerators.get index) := by
  have boundMapped : index.val
      < (comp2.twoCellGenerators.map (retagRightTwoGen comp1 comp2 sameModes)).length := by
    rw [lengthMap]; exact index.isLt
  have valsEqual : (embedRightTwoGen comp1 comp2 sameModes index).val
      = (comp1.twoCellGenerators.map (retagLeftTwoGen comp1 comp2 sameModes)).length + index.val :=
    congrArg (· + index.val) (lengthMap (retagLeftTwoGen comp1 comp2 sameModes) comp1.twoCellGenerators).symm
  calc (pushoutShared comp1 comp2 sameModes).twoCellGenerators.get
            (embedRightTwoGen comp1 comp2 sameModes index)
      = (comp1.twoCellGenerators.map (retagLeftTwoGen comp1 comp2 sameModes)
          ++ comp2.twoCellGenerators.map (retagRightTwoGen comp1 comp2 sameModes)).get
          ⟨(comp1.twoCellGenerators.map (retagLeftTwoGen comp1 comp2 sameModes)).length + index.val, by
            rw [← valsEqual]; exact (embedRightTwoGen comp1 comp2 sameModes index).isLt⟩ :=
          getValCongr (pushoutShared comp1 comp2 sameModes).twoCellGenerators valsEqual
    _ = (comp2.twoCellGenerators.map (retagRightTwoGen comp1 comp2 sameModes)).get ⟨index.val, boundMapped⟩ :=
          getAppendRight _ index.val boundMapped
            (comp1.twoCellGenerators.map (retagLeftTwoGen comp1 comp2 sameModes)) _
    _ = retagRightTwoGen comp1 comp2 sameModes (comp2.twoCellGenerators.get index) :=
          getMap (retagRightTwoGen comp1 comp2 sameModes) comp2.twoCellGenerators index.val index.isLt boundMapped

/-! ## The genuine-generator right coprojection -/

/-- ★ **The right coprojection lifted to a `ComputadMorphismTwo`, with a GENUINE `onTwoCell`.**  A reconstructed
generating 2-cell of component 2 (`monadComputad`'s `eta` / `mu`) maps to the pushout reconstructed 2-cell at
`embedRightTwoGen`, whose interpreter conjuncts are `interpretWordFrom_map` (at the mode-injective right
coprojection) composed with the source 2-cell's own conjuncts.  This is the `interpretWordFrom`-transport the r4
residual named — no longer vacuous.  Unlike `inclusionRightTwo` (which required `comp2` locally thin), this works
for component 2 WITH 2-generators. -/
def inclusionRightTwoReal (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount) :
    ComputadMorphismTwo comp2 (pushoutShared comp1 comp2 sameModes) where
  toComputadMorphism := inclusionRight comp1 comp2 sameModes
  onTwoCell := fun {srcMode _tgtMode _sourcePath _targetPath} generator =>
    ⟨embedRightTwoGen comp1 comp2 sameModes generator.val,
      ⟨(congrArg ((pushoutShared comp1 comp2 sameModes).interpretWordFrom
              ((inclusionRight comp1 comp2 sameModes).onModes srcMode))
            (congrArg ComputadTwoGen.lhs (pushoutTwoGenGetRight comp1 comp2 sameModes generator.val))).trans
          ((interpretWordFrom_map (inclusionRight comp1 comp2 sameModes)
              (inclusionRight_onModes_injective comp1 comp2 sameModes) srcMode
              (comp2.twoCellGenerators.get generator.val).lhs).trans
            (congrArg (fun option => option.map
                (fun sig => (⟨(inclusionRight comp1 comp2 sameModes).onModes sig.fst,
                    mapPath (inclusionRight comp1 comp2 sameModes) sig.snd⟩ :
                  Sigma (fun targetMode : Fin (pushoutShared comp1 comp2 sameModes).modeCount =>
                    ModalityPath (pushoutShared comp1 comp2 sameModes).toModeGraph
                      ((inclusionRight comp1 comp2 sameModes).onModes srcMode) targetMode))))
              generator.property.1)),
       (congrArg ((pushoutShared comp1 comp2 sameModes).interpretWordFrom
              ((inclusionRight comp1 comp2 sameModes).onModes srcMode))
            (congrArg ComputadTwoGen.rhs (pushoutTwoGenGetRight comp1 comp2 sameModes generator.val))).trans
          ((interpretWordFrom_map (inclusionRight comp1 comp2 sameModes)
              (inclusionRight_onModes_injective comp1 comp2 sameModes) srcMode
              (comp2.twoCellGenerators.get generator.val).rhs).trans
            (congrArg (fun option => option.map
                (fun sig => (⟨(inclusionRight comp1 comp2 sameModes).onModes sig.fst,
                    mapPath (inclusionRight comp1 comp2 sameModes) sig.snd⟩ :
                  Sigma (fun targetMode : Fin (pushoutShared comp1 comp2 sameModes).modeCount =>
                    ModalityPath (pushoutShared comp1 comp2 sameModes).toModeGraph
                      ((inclusionRight comp1 comp2 sameModes).onModes srcMode) targetMode))))
              generator.property.2))⟩⟩

/-! ## Non-vacuity: the monad unit fires through the real right coprojection -/

/-- The reconstructed `t`-path of `monadComputad` — the interpreter's image of the endo-1-generator word `[t]`. -/
def monadComputadReconstructedT :
    ModalityPath monadComputad.toModeGraph (⟨0, by decide⟩ : Fin 1) (⟨0, by decide⟩ : Fin 1) :=
  ModalityPath.cons
    (⟨⟨0, by decide⟩, rfl⟩ : monadComputad.Modality ⟨0, by decide⟩ ⟨0, by decide⟩)
    (ModalityPath.nil (graph := monadComputad.toModeGraph) ⟨0, by decide⟩)

/-- The **reconstructed monad unit** — 2-generator index `0` of `monadComputad` inhabits `ReconstructedTwoCell` at
the boundary `(id_point, t)`: the interpreter sends `lhs = []` to `id_point` and `rhs = [t]` to
`monadComputadReconstructedT`, both by `rfl`.  A GENUINE generating 2-cell to feed the real coprojection. -/
def monadComputadReconstructsUnit :
    monadComputad.ReconstructedTwoCell
      (ModalityPath.nil (graph := monadComputad.toModeGraph) (⟨0, by decide⟩ : Fin 1))
      monadComputadReconstructedT :=
  ⟨⟨0, by decide⟩, ⟨rfl, rfl⟩⟩

/-- ★ **Non-vacuity — the real right coprojection FIRES on the monad unit.**  Feeding the genuine reconstructed
unit `monadComputadReconstructsUnit` (a REAL 2-generator, not a vacuous `Fin.elim0`) to
`inclusionRightTwoReal`'s `onTwoCell` lands at pushout 2-generator index `0` (`embedRightTwoGen ⟨0⟩` with
`involutionComputad`'s empty 2-generator list, so the shift is `0 + 0`).  Witnesses the coprojection's 2-cell
action is genuinely inhabited on real generators — the r4 residual, discharged concretely. -/
theorem inclusionRightTwoReal_onUnit_index :
    ((inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes).onTwoCell
        monadComputadReconstructsUnit).val.val = 0 := rfl

/-! ## Honesty marker -/

/-- ★ **Honesty marker — the genuine-generator coprojection `onTwoCell` SHIPS (r6 P2).**  The load-bearing
interpreter-commutation `interpretWordFrom_map` (over any mode-injective `ComputadMorphism`, via the abstract
`endpointsPreserved` field and the cons-form helper `interpretWordFrom_cons_of_get`), the right coprojection's
mode-injectivity (`inclusionRight_onModes_injective` from `castFinAcrossCount_injective`), the 2-generator right
embedding `embedRightTwoGen` with its get-alignment `pushoutTwoGenGetRight`, and the REAL coprojection
`inclusionRightTwoReal` whose `onTwoCell` transports a genuine reconstructed generating 2-cell to the pushout via
`embedRightTwoGen` + `interpretWordFrom_map`.  Non-vacuous: the monad unit fires
(`inclusionRightTwoReal_onUnit_index`).  This flips `fxAmalg_hasRealGeneratorCoprojection` (`MapCell.lean`) to
`true`.  `= true`. -/
def fxAmalg_hasRealGeneratorCoprojectionShipped : Bool := true

end FX1Poly.Polygraph.Amalgam

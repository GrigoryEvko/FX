import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadMonotoneEngine

/-! # WalkingMonad — the map-factorization engine: the fold stays in Δ₊, and the incoming map post-composes

`WalkingMonad/MonadMonotoneEngine` shipped the fold engine (`monadRunMonoCell`), the length-width invariant
(`monadRunMonoCell_width`), and the three monad laws sound at an arbitrary left-whisker context.  Toward the FULL
soundness leg `mapEqOfConv` (invariance of the fold under EVERY `MonadSaturatedTwoCellConv` derivation), the
honesty marker named a first ingredient: the **whisker-shift FACTORIZATION** threading the running map through the
vcomp / whisker CONGRUENCE cases (the incoming map post-composes, so the map of a run from state `(w, m)` is `m`
post-composed onto the map of the run from the identity state `(w, idMap w)`).  This file ships that ingredient,
plus the invariant it rests on.

## What this file ships (each piece zero-axiom)

  * ★ **`monadRunMonoCell_mapsInto`** — the fold lands every free 2-cell in a GENUINE Δ₊ morphism: the running map
    always maps INTO the running width (no junk / out-of-range value).  The crux is that in the monad EVERY `mu`
    fires as an **INTERNAL** degeneracy (position `p = leftAcc.length < w - 1`, since the source carries the two
    `t`'s), so `internalCapPreservesMapsInto` applies — exactly the well-behaved fragment the walking adjunction's
    BOUNDARY cap escaped (`boundaryCapBreaksMapsInto`, `counitMonotoneMap_notMapsInto`).  This is the monad-side
    confirmation that the covariant fold is sound-VALUED, not merely sound on the seed laws.
  * ★ **`monadRunMonoCell_mapFactor`** — the factorization: `(monadRunMonoCell (w, m) …).2 = composeMap m
    (monadRunMonoCell (w, idMap w) …).2`.  The width thread is independent of the map, so the sequence of
    face / degeneracy factors is identical whether the run starts from `m` or from `idMap w`; the incoming map
    therefore post-composes onto the "local map" of the cell, by `composeMap_assoc` (whose in-range side condition
    is exactly the `mapsInto` invariant above) and `composeMap_idMap_eq`.

Both carry the length-width precondition `w = leftAcc.length + localDom.length + rightAcc.length` (the same the
width invariant carries), because the internal-degeneracy fact `p < w - 1` needs it.  Raw Lean 4 + Init;
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The fold lands in a genuine Δ₊ morphism -/

/-- The `mapsInto` invariant at a GENERATOR — split out with FREE boundary paths so casing on the generator is
propext-free.  The `eta` case is `cupPreservesMapsInto` (a face never escapes the grown ordinal); the `mu` case is
`internalCapPreservesMapsInto`, which needs the degeneracy to be INTERNAL (`p < w - 1`) — furnished by the
length-width precondition (`w = leftAcc.length + 2 + rightAcc.length`, so `leftAcc.length < w - 1`). -/
theorem monadRunMonoCell_mapsInto_gen {overallSource overallTarget sourceMode targetMode : MonadMode}
    {generatorDom generatorCod : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (generator : MonadTwoCell generatorDom generatorCod)
    (width : Nat) (map : List Nat)
    (leftAcc : ModalityPath monadModeSignature.graph overallSource sourceMode)
    (rightAcc : ModalityPath monadModeSignature.graph targetMode overallTarget)
    (hwidth : width = leftAcc.length + generatorDom.length + rightAcc.length)
    (hmap : mapsInto map width) :
    mapsInto (monadRunMonoCell (width, map) leftAcc rightAcc (RawTwoCellExpr.gen generator)).2
      (monadRunMonoCell (width, map) leftAcc rightAcc (RawTwoCellExpr.gen generator)).1 := by
  cases generator with
  | eta =>
      show mapsInto (composeMap map (faceMap leftAcc.length width)) (width + 1)
      exact cupPreservesMapsInto leftAcc.length width map hmap
  | mu =>
      show mapsInto (composeMap map (degenMap leftAcc.length (width - 1))) (width - 1)
      -- Rewrite `width - 1` to its `+`-normal form up front (avoids truncated-subtraction lemmas).
      have hwidthPred : width - 1 = leftAcc.length + 1 + rightAcc.length := by
        rw [hwidth]; exact monadMuWidthShift leftAcc.length rightAcc.length
      rw [hwidthPred]
      have hinternal : leftAcc.length < leftAcc.length + 1 + rightAcc.length :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self leftAcc.length)
          (Nat.le_add_right (leftAcc.length + 1) rightAcc.length)
      have hmapSucc : mapsInto map (leftAcc.length + 1 + rightAcc.length + 1) := by
        have hsucc : leftAcc.length + 1 + rightAcc.length + 1 = width := by
          rw [hwidth]
          show leftAcc.length + 1 + rightAcc.length + 1 = leftAcc.length + 2 + rightAcc.length
          rw [Nat.add_right_comm leftAcc.length 2 rightAcc.length,
              Nat.add_right_comm leftAcc.length 1 rightAcc.length]
        rw [hsucc]; exact hmap
      exact internalCapPreservesMapsInto leftAcc.length (leftAcc.length + 1 + rightAcc.length)
        map hmapSucc hinternal

/-- ★ **The monad's covariant fold lands every free 2-cell in a genuine Δ₊ morphism.**  Given the running width
tracks the current 1-cell length, the running map maps INTO the running width — no out-of-range junk.  Structural
recursion: a generator via `monadRunMonoCell_mapsInto_gen`, a vertical composite threads through both factors (the
intermediate width supplied by `monadRunMonoCell_width`), the whiskerings recurse under shifted accumulators.
Contrast the adjunction, whose boundary cap breaks this very invariant (`counitMonotoneMap_notMapsInto`); the
monad has no boundary cap, so the covariant fold is junk-free everywhere. -/
theorem monadRunMonoCell_mapsInto {overallSource overallTarget : MonadMode} :
    {localSource localTarget : MonadMode} →
    {localDom localCod : ModalityPath monadModeSignature.graph localSource localTarget} →
    (cell : RawTwoCellExpr monadModeSignature localDom localCod) →
    (width : Nat) → (map : List Nat) →
    (leftAcc : ModalityPath monadModeSignature.graph overallSource localSource) →
    (rightAcc : ModalityPath monadModeSignature.graph localTarget overallTarget) →
    width = leftAcc.length + localDom.length + rightAcc.length →
    mapsInto map width →
    mapsInto (monadRunMonoCell (width, map) leftAcc rightAcc cell).2
      (monadRunMonoCell (width, map) leftAcc rightAcc cell).1
  | _, _, _, _, .gen generator, width, map, leftAcc, rightAcc, hwidth, hmap =>
      monadRunMonoCell_mapsInto_gen generator width map leftAcc rightAcc hwidth hmap
  | _, _, _, _, .id _, _, _, _, _, _, hmap => hmap
  | _, _, _, _, .vcomp cellLeft cellRight, width, map, leftAcc, rightAcc, hwidth, hmap => by
      rw [monadRunMonoCell_vcomp]
      exact monadRunMonoCell_mapsInto cellRight _ _ leftAcc rightAcc
        (monadRunMonoCell_width cellLeft width map leftAcc rightAcc hwidth)
        (monadRunMonoCell_mapsInto cellLeft width map leftAcc rightAcc hwidth hmap)
  | _, _, _, _, .whiskerLeft oneCell body, width, map, leftAcc, rightAcc, hwidth, hmap => by
      rename_i bodyDom _
      rw [monadRunMonoCell_whiskerLeft]
      exact monadRunMonoCell_mapsInto body width map (composePath leftAcc oneCell) rightAcc (by
        rw [hwidth, ModalityPath.length_composePath oneCell bodyDom,
            ModalityPath.length_composePath leftAcc oneCell,
            Nat.add_assoc leftAcc.length oneCell.length bodyDom.length]) hmap
  | _, _, _, _, .whiskerRight oneCell body, width, map, leftAcc, rightAcc, hwidth, hmap => by
      rename_i bodyDom _
      rw [monadRunMonoCell_whiskerRight]
      exact monadRunMonoCell_mapsInto body width map leftAcc (composePath oneCell rightAcc) (by
        rw [hwidth, ModalityPath.length_composePath bodyDom oneCell,
            ModalityPath.length_composePath oneCell rightAcc,
            ← Nat.add_assoc leftAcc.length bodyDom.length oneCell.length,
            Nat.add_assoc (leftAcc.length + bodyDom.length) oneCell.length rightAcc.length]) hmap

/-! ## The running map's length is the starting map's length (the map thread preserves length) -/

/-- The fold never changes the map's LENGTH: each step post-composes a same-length factor
(`faceMap`/`degenMap` both have length matching the incoming width), so the running map keeps the starting map's
length.  The domain-width bookkeeping the factorization's associativity side condition needs. -/
theorem monadRunMonoCell_map_length {overallSource overallTarget : MonadMode} :
    {localSource localTarget : MonadMode} →
    {localDom localCod : ModalityPath monadModeSignature.graph localSource localTarget} →
    (cell : RawTwoCellExpr monadModeSignature localDom localCod) →
    (state : Nat × List Nat) →
    (leftAcc : ModalityPath monadModeSignature.graph overallSource localSource) →
    (rightAcc : ModalityPath monadModeSignature.graph localTarget overallTarget) →
    (monadRunMonoCell state leftAcc rightAcc cell).2.length = state.2.length
  | _, _, _, _, .gen generator, state, _, _ => by cases generator <;> exact composeMap_length _ _
  | _, _, _, _, .id _, _, _, _ => rfl
  | _, _, _, _, .vcomp cellLeft cellRight, state, leftAcc, rightAcc => by
      rw [monadRunMonoCell_vcomp, monadRunMonoCell_map_length cellRight _ leftAcc rightAcc,
          monadRunMonoCell_map_length cellLeft state leftAcc rightAcc]
  | _, _, _, _, .whiskerLeft oneCell body, state, leftAcc, rightAcc => by
      rw [monadRunMonoCell_whiskerLeft]
      exact monadRunMonoCell_map_length body state (composePath leftAcc oneCell) rightAcc
  | _, _, _, _, .whiskerRight oneCell body, state, leftAcc, rightAcc => by
      rw [monadRunMonoCell_whiskerRight]
      exact monadRunMonoCell_map_length body state leftAcc (composePath oneCell rightAcc)

/-! ## The incoming map post-composes: the factorization -/

/-- The factorization at a GENERATOR — split out with FREE boundary paths so casing on the generator is
propext-free.  From the identity state the first fold step is exactly the face / degeneracy factor
(`composeMap (idMap width) factor = factor` by `composeMap_idMap_eq`), so the general-state result post-composes
the incoming map onto it. -/
theorem monadRunMonoCell_mapFactor_gen {overallSource overallTarget sourceMode targetMode : MonadMode}
    {generatorDom generatorCod : ModalityPath monadModeSignature.graph sourceMode targetMode}
    (generator : MonadTwoCell generatorDom generatorCod)
    (state : Nat × List Nat)
    (leftAcc : ModalityPath monadModeSignature.graph overallSource sourceMode)
    (rightAcc : ModalityPath monadModeSignature.graph targetMode overallTarget)
    (hwidth : state.1 = leftAcc.length + generatorDom.length + rightAcc.length) :
    (monadRunMonoCell state leftAcc rightAcc (RawTwoCellExpr.gen generator)).2
      = composeMap state.2
          (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc (RawTwoCellExpr.gen generator)).2 := by
  cases generator with
  | eta =>
      show composeMap state.2 (faceMap leftAcc.length state.1)
        = composeMap state.2 (composeMap (idMap state.1) (faceMap leftAcc.length state.1))
      have hcollapse : composeMap (idMap state.1) (faceMap leftAcc.length state.1)
          = faceMap leftAcc.length state.1 := by
        have hc := composeMap_idMap_eq (faceMap leftAcc.length state.1)
        rw [faceMap_length leftAcc.length state.1] at hc
        exact hc
      rw [hcollapse]
  | mu =>
      show composeMap state.2 (degenMap leftAcc.length (state.1 - 1))
        = composeMap state.2 (composeMap (idMap state.1) (degenMap leftAcc.length (state.1 - 1)))
      have hsucc : state.1 - 1 + 1 = state.1 := by
        have hwidthPred : state.1 - 1 = leftAcc.length + 1 + rightAcc.length := by
          rw [hwidth]; exact monadMuWidthShift leftAcc.length rightAcc.length
        rw [hwidthPred, hwidth]
        show leftAcc.length + 1 + rightAcc.length + 1 = leftAcc.length + 2 + rightAcc.length
        rw [Nat.add_right_comm leftAcc.length 2 rightAcc.length,
            Nat.add_right_comm leftAcc.length 1 rightAcc.length]
      have hcollapse : composeMap (idMap state.1) (degenMap leftAcc.length (state.1 - 1))
          = degenMap leftAcc.length (state.1 - 1) := by
        have hc := composeMap_idMap_eq (degenMap leftAcc.length (state.1 - 1))
        rw [degenMap_length leftAcc.length (state.1 - 1), hsucc] at hc
        exact hc
      rw [hcollapse]

/-- ★ **The factorization: the incoming map post-composes onto the cell's local map.**  Running the fold from state
`(w, m)` gives the SAME map as running from the identity state `(w, idMap w)`, left-composed with `m`.  The width
thread is independent of the map, so both runs meet the SAME sequence of face / degeneracy factors; the incoming
map accumulates by `composeMap`, associating out by `composeMap_assoc` (its in-range side condition supplied by
`monadRunMonoCell_mapsInto`).  Carries the length-width precondition (needed at each `mu`).  This is the vcomp /
whisker CONGRUENCE-case engine the honesty marker named as `mapEqOfConv`'s first ingredient. -/
theorem monadRunMonoCell_mapFactor {overallSource overallTarget : MonadMode} :
    {localSource localTarget : MonadMode} →
    {localDom localCod : ModalityPath monadModeSignature.graph localSource localTarget} →
    (cell : RawTwoCellExpr monadModeSignature localDom localCod) →
    (state : Nat × List Nat) →
    (leftAcc : ModalityPath monadModeSignature.graph overallSource localSource) →
    (rightAcc : ModalityPath monadModeSignature.graph localTarget overallTarget) →
    state.1 = leftAcc.length + localDom.length + rightAcc.length →
    mapsInto state.2 state.1 →
    (monadRunMonoCell state leftAcc rightAcc cell).2
      = composeMap state.2 (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cell).2
  | _, _, _, _, .gen generator, state, leftAcc, rightAcc, hwidth, _ =>
      monadRunMonoCell_mapFactor_gen generator state leftAcc rightAcc hwidth
  | _, _, _, _, .id _, state, _, _, _, hmap => (composeMap_idMap_right state.2 state.1 hmap).symm
  | _, _, _, _, .vcomp cellLeft cellRight, state, leftAcc, rightAcc, hwidth, hmap => by
      have hS1w : (monadRunMonoCell state leftAcc rightAcc cellLeft).1
          = leftAcc.length + _ + rightAcc.length :=
        monadRunMonoCell_width cellLeft state.1 state.2 leftAcc rightAcc hwidth
      have hT1w : (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).1
          = leftAcc.length + _ + rightAcc.length :=
        monadRunMonoCell_width cellLeft state.1 (idMap state.1) leftAcc rightAcc hwidth
      have hS1into : mapsInto (monadRunMonoCell state leftAcc rightAcc cellLeft).2
          (monadRunMonoCell state leftAcc rightAcc cellLeft).1 :=
        monadRunMonoCell_mapsInto cellLeft state.1 state.2 leftAcc rightAcc hwidth hmap
      have hT1into : mapsInto (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).2
          (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).1 :=
        monadRunMonoCell_mapsInto cellLeft state.1 (idMap state.1) leftAcc rightAcc hwidth
          (idMap_mapsInto state.1)
      have hS1map : (monadRunMonoCell state leftAcc rightAcc cellLeft).2
          = composeMap state.2 (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).2 :=
        monadRunMonoCell_mapFactor cellLeft state leftAcc rightAcc hwidth hmap
      have hwidthEq : (monadRunMonoCell state leftAcc rightAcc cellLeft).1
          = (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).1 := hS1w.trans hT1w.symm
      have hT1len : (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).2.length
          = (idMap state.1).length :=
        monadRunMonoCell_map_length cellLeft (state.1, idMap state.1) leftAcc rightAcc
      rw [monadRunMonoCell_vcomp, monadRunMonoCell_vcomp,
          monadRunMonoCell_mapFactor cellRight (monadRunMonoCell state leftAcc rightAcc cellLeft)
            leftAcc rightAcc hS1w hS1into,
          monadRunMonoCell_mapFactor cellRight
            (monadRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft)
            leftAcc rightAcc hT1w hT1into,
          hS1map, hwidthEq]
      exact composeMap_assoc state.2 _ _ (by rw [hT1len, idMap_length]; exact hmap)
  | _, _, _, _, .whiskerLeft oneCell body, state, leftAcc, rightAcc, hwidth, hmap => by
      rename_i bodyDom _
      rw [monadRunMonoCell_whiskerLeft, monadRunMonoCell_whiskerLeft]
      exact monadRunMonoCell_mapFactor body state (composePath leftAcc oneCell) rightAcc (by
        rw [hwidth, ModalityPath.length_composePath oneCell bodyDom,
            ModalityPath.length_composePath leftAcc oneCell,
            Nat.add_assoc leftAcc.length oneCell.length bodyDom.length]) hmap
  | _, _, _, _, .whiskerRight oneCell body, state, leftAcc, rightAcc, hwidth, hmap => by
      rename_i bodyDom _
      rw [monadRunMonoCell_whiskerRight, monadRunMonoCell_whiskerRight]
      exact monadRunMonoCell_mapFactor body state leftAcc (composePath oneCell rightAcc) (by
        rw [hwidth, ModalityPath.length_composePath bodyDom oneCell,
            ModalityPath.length_composePath oneCell rightAcc,
            ← Nat.add_assoc leftAcc.length bodyDom.length oneCell.length,
            Nat.add_assoc (leftAcc.length + bodyDom.length) oneCell.length rightAcc.length]) hmap

/-! ## Consequence: the vertical-composition HOMOMORPHISM + the two vcomp-congruence cases of `mapEqOfConv`

The factorization says the running map post-composes; specialized to the whole-cell fold from the identity state,
it gives the clean statement that `monadMonotoneMapOf` is a FUNCTOR on vertical composition — the map of a vertical
composite is the `composeMap` of the two maps.  The two vcomp-congruence cases of `mapEqOfConv`
(`vcompCongrLeft` / `vcompCongrRight`) are then immediate `congrArg`s. -/

/-- The run-level vcomp homomorphism at an ARBITRARY well-formed state: running `α ⊟ β` post-composes the run of
`α` onto the run of `β` started from `α`'s output width's identity.  Proved by `monadRunMonoCell_vcomp` (peel `α`)
then `monadRunMonoCell_mapFactor` (β's incoming map post-composes), with the intermediate width / in-range facts
from `monadRunMonoCell_width` / `monadRunMonoCell_mapsInto`.  Stated with the state / accumulators GENERAL so the
whole-cell corollary instantiates it at the identity state without any `identityPath`-graph unification friction. -/
theorem monadRunMonoCell_vcomp_map {overallSource overallTarget localSource localTarget : MonadMode}
    {oneCellF oneCellG oneCellH : ModalityPath monadGraph localSource localTarget}
    (cellAlpha : RawTwoCellExpr monadModeSignature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr monadModeSignature oneCellG oneCellH)
    (state : Nat × List Nat)
    (leftAcc : ModalityPath monadGraph overallSource localSource)
    (rightAcc : ModalityPath monadGraph localTarget overallTarget)
    (hwidth : state.1 = leftAcc.length + oneCellF.length + rightAcc.length)
    (hmap : mapsInto state.2 state.1) :
    (monadRunMonoCell state leftAcc rightAcc (RawTwoCellExpr.vcomp cellAlpha cellBeta)).2
      = composeMap (monadRunMonoCell state leftAcc rightAcc cellAlpha).2
          (monadRunMonoCell ((monadRunMonoCell state leftAcc rightAcc cellAlpha).1,
              idMap (monadRunMonoCell state leftAcc rightAcc cellAlpha).1)
            leftAcc rightAcc cellBeta).2 := by
  rw [monadRunMonoCell_vcomp]
  exact monadRunMonoCell_mapFactor cellBeta (monadRunMonoCell state leftAcc rightAcc cellAlpha)
    leftAcc rightAcc (monadRunMonoCell_width cellAlpha state.1 state.2 leftAcc rightAcc hwidth)
    (monadRunMonoCell_mapsInto cellAlpha state.1 state.2 leftAcc rightAcc hwidth hmap)

/-- ★ **The vertical-composition homomorphism.**  `monadMonotoneMapOf (α ⊟ β) = composeMap (map α) (map β)` — the
fold is a FUNCTOR on vertical composition, the whole-cell instance of `monadRunMonoCell_vcomp_map` at the identity
state (width `oneCellF.length`), with `α`'s output width pinned to the middle 1-cell length so `β`'s identity-state
run IS `monadMonotoneMapOf β`. -/
theorem monadMonotoneMapOf_vcomp {sourceMode targetMode : MonadMode}
    {oneCellF oneCellG oneCellH : ModalityPath monadGraph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr monadModeSignature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr monadModeSignature oneCellG oneCellH) :
    monadMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = composeMap (monadMonotoneMapOf cellAlpha) (monadMonotoneMapOf cellBeta) := by
  have hpre : oneCellF.length = 0 + oneCellF.length + 0 := by rw [Nat.add_zero, Nat.zero_add]
  have key := monadRunMonoCell_vcomp_map cellAlpha cellBeta (oneCellF.length, idMap oneCellF.length)
      (identityPath (graph := monadModeSignature.graph) sourceMode)
      (identityPath (graph := monadModeSignature.graph) targetMode)
      hpre (idMap_mapsInto oneCellF.length)
  have hSw : (monadRunMonoCell (oneCellF.length, idMap oneCellF.length)
        (identityPath (graph := monadModeSignature.graph) sourceMode)
        (identityPath (graph := monadModeSignature.graph) targetMode) cellAlpha).1 = oneCellG.length := by
    rw [monadRunMonoCell_width cellAlpha oneCellF.length (idMap oneCellF.length)
          (identityPath (graph := monadModeSignature.graph) sourceMode)
          (identityPath (graph := monadModeSignature.graph) targetMode) hpre]
    show 0 + oneCellG.length + 0 = oneCellG.length
    rw [Nat.add_zero, Nat.zero_add]
  refine (monadMonotoneMapOf_eq_runMonoCell (RawTwoCellExpr.vcomp cellAlpha cellBeta)).trans
    (key.trans ?_)
  rw [hSw]
  rfl

/-- ★ **`mapEqOfConv`, LEFT-vcomp-congruence case.**  Maps agreeing on the left factor give equal composite maps —
immediate from the vcomp homomorphism. -/
theorem monadMonotoneMapOf_vcompCongrLeft {sourceMode targetMode : MonadMode}
    {oneCellF oneCellG oneCellH : ModalityPath monadGraph sourceMode targetMode}
    {cellAlpha cellAlpha' : RawTwoCellExpr monadModeSignature oneCellF oneCellG}
    (cellBeta : RawTwoCellExpr monadModeSignature oneCellG oneCellH)
    (hmap : monadMonotoneMapOf cellAlpha = monadMonotoneMapOf cellAlpha') :
    monadMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = monadMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha' cellBeta) := by
  rw [monadMonotoneMapOf_vcomp, monadMonotoneMapOf_vcomp, hmap]

/-- ★ **`mapEqOfConv`, RIGHT-vcomp-congruence case.**  Maps agreeing on the right factor give equal composite maps
— immediate from the vcomp homomorphism.  This is the case the factorization was named for: the incoming map
post-composes, so replacing the right factor by a map-equal one leaves the composite unchanged. -/
theorem monadMonotoneMapOf_vcompCongrRight {sourceMode targetMode : MonadMode}
    {oneCellF oneCellG oneCellH : ModalityPath monadGraph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr monadModeSignature oneCellF oneCellG)
    {cellBeta cellBeta' : RawTwoCellExpr monadModeSignature oneCellG oneCellH}
    (hmap : monadMonotoneMapOf cellBeta = monadMonotoneMapOf cellBeta') :
    monadMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = monadMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta') := by
  rw [monadMonotoneMapOf_vcomp, monadMonotoneMapOf_vcomp, hmap]

/-! ## Honesty marker -/

/-- **ESTABLISHED.**  The map-factorization ENGINE is shipped: the fold lands every free 2-cell in a genuine Δ₊
morphism (`monadRunMonoCell_mapsInto` — every `mu` an INTERNAL degeneracy, the fragment the adjunction's boundary
cap escaped), the map length is fold-invariant (`monadRunMonoCell_map_length`), the incoming map post-composes
(`monadRunMonoCell_mapFactor`), and — the consequence — `monadMonotoneMapOf` is a FUNCTOR on vertical composition
(`monadMonotoneMapOf_vcomp`), discharging the TWO vcomp-congruence cases of `mapEqOfConv`
(`monadMonotoneMapOf_vcompCongrLeft` / `…Right`).  This is the "whisker-shift FACTORIZATION" the
`fxMonad_hasFullMapEqOfConvAndCompleteness` honesty marker named as `mapEqOfConv`'s first ingredient, now
delivered zero-axiom.  `= true`. -/
def fxMonad_hasMapFactorizationAndVcompCongruence : Bool := true

end FX1Poly.Polygraph

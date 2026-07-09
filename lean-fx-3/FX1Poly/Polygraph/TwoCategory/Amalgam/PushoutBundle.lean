import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutMonotoneReflection

/-! # Polygraph/TwoCategory/Amalgam/PushoutBundle — the signature-generic arity-fold ENGINE, the
convertibility-soundness bundle re-homed generic-over-a-face/degen-arity discipline, and the pushout instance
that flips the LIVE combined pushout isFalse hypothesis-free (WP-AMALG r8)

`PushoutMonotoneReflection.lean` (r7) reduced the LIVE pushout non-convertibility to ONE bundle
`ArityFoldConvSound involutionMonadPushout.toModeSignature`, inhabited over the BESPOKE `monadModeSignature` by the
shipped walking-monad Δ-fold soundness but OPEN over the pushout signature — the residual it named "the
reconstruction arity discipline".  This file discharges exactly that.

## The re-homing verdict (recon)

The walking-monad Δ-fold soundness chain has THREE layers.  Layer A (pure `List Nat` ordinal-sum algebra —
`embedLocalMap` and its `composeMap` / disjoint-window / nesting identities) is ALREADY signature-independent and is
reused verbatim.  Layer B (the fold ENGINE `monadRunMonoCell` + the width / mapsInto / map-length / factorization /
localEmbed laws + the vcomp/whisker homomorphisms) is signature-generic in its RECURSION; here it is re-homed to an
arbitrary `ModeSignature` as `arityRunMonoCell` etc.  Layer C is the ONLY genuine content: the FIVE `_gen` base
cases where the fold reads a 2-generator's arity `(generatorDom.length, generatorCod.length)`.  Over the monad they
reduce by `cases generator` (eta ↦ `(0,1)`, mu ↦ `(2,1)`, each `rfl`); over an arbitrary signature they need a
DISCIPLINE — every generator has arity `(0,1)` or `(2,1)` — which the pushout's two reconstructed 2-generators (the
retagged `eta` / `mu`) satisfy via the interpreter's length invariant `interpretWordFrom_length`.

## What this file ships (each piece zero-axiom)

  * **`arityRunMonoCell` / `arityMonoProcessSpine`** — the generic fold engine, the payload-blind twins of
    `monadRunMonoCell` / `monadMonoProcessSpine`.
  * **`HasFaceDegenArity`** — the face/degen arity discipline: every 2-generator has arity `(0,1)` or `(2,1)`.
  * ★ **`arityRunMonoCell_width` / `_mapsInto` / `_mapFactor` / `_localEmbed`** — Layer B re-homed generic over the
    discipline, the five `_gen` base cases discharged from the discipline's disjunction.
  * ★ **`arityMonotoneMapOf_vcomp` / `_whiskerLeft` / `_whiskerRight` / `_hcomp` / `_interchange`** — the fold
    homomorphisms + the Godement invariance, generic over the discipline, reusing Layer A verbatim.
  * ★★ **`arityFoldConvSound_ofDiscipline`** — the bundle `ArityFoldConvSound signature` from any discipline; the
    monad instance re-derives `monadArityFoldConvSound`.
  * **`interpretWordFrom_length`** — the interpreter's length invariant (the single genuinely-new brick).
  * ★★ **`pushoutHasFaceDegenArity` / `pushoutArityFoldConvSound`** — the pushout discipline (casing the two
    reconstructed `Fin 2` generators) and the pushout bundle instance.
  * ★★★ **`crossPairPushoutNonConvUnconditional`** — the LIVE combined pushout isFalse, HYPOTHESIS-FREE: with r6's
    isTrue `crossPairConvertibleCounterpart` the complete discriminating pair.  THE #2043 MILESTONE.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free (structural recursion,
cons-only lists, hand arithmetic, `Fin`-subtype casing).  Per-declaration `#assert_no_axioms` gated in the audit
twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The generic fold engine (payload-blind twins of the walking-monad engine) -/

/-- Fold the generic arity step `arityFoldStepAtom` over a spine-atom list — the spine-list-level engine
underlying `arityMonotoneMapOf`, generic over any `ModeSignature`. -/
def arityMonoProcessSpine {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : Nat × List Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode)) : Nat × List Nat :=
  atoms.foldl arityFoldStepAtom state

/-- Run the generic arity fold over ONE cell's spine from a given state (its contribution alone, empty tail) — the
per-block fold unit the context decomposition peels. -/
def arityRunMonoCell {signature : ModeSignature}
    {overallSource overallTarget localSource localTarget : signature.graph.Mode}
    (state : Nat × List Nat)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {localDom localCod : ModalityPath signature.graph localSource localTarget}
    (cell : RawTwoCellExpr signature localDom localCod) : Nat × List Nat :=
  arityMonoProcessSpine state (cell.spineDiff leftAcc rightAcc [])

/-! ## The face/degen arity discipline + the step-shape helpers (the arity discipline made computational) -/

/-- ★ **The face/degen arity discipline.**  Every generating 2-cell of the signature has arity `(0,1)` (a
face-shaped unit) or `(2,1)` (a degeneracy-shaped multiplication).  This is exactly the arity fact the fold's
`_gen` base cases read; the walking monad satisfies it by `cases generator` (eta ↦ `(0,1)`, mu ↦ `(2,1)`), the
pushout by its two reconstructed generators (`pushoutHasFaceDegenArity`). -/
def HasFaceDegenArity (signature : ModeSignature) : Prop :=
  ∀ {sourceMode targetMode : signature.graph.Mode}
    {generatorDom generatorCod : ModalityPath signature.graph sourceMode targetMode},
    signature.twoCell generatorDom generatorCod →
    (generatorDom.length = 0 ∧ generatorCod.length = 1)
      ∨ (generatorDom.length = 2 ∧ generatorCod.length = 1)

/-- Running a generator of FACE arity `(0,1)` grows the width and post-composes the face `δ_p` at position
`leftAcc.length` — the run-level step reduction bundling the spine-atom defeq and the match collapse. -/
theorem arityRunMonoCell_gen_face {signature : ModeSignature}
    {overallSource overallTarget sourceMode targetMode : signature.graph.Mode}
    {generatorDom generatorCod : ModalityPath signature.graph sourceMode targetMode}
    (generator : signature.twoCell generatorDom generatorCod)
    (state : Nat × List Nat)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (hdom : generatorDom.length = 0) (hcod : generatorCod.length = 1) :
    arityRunMonoCell state leftAcc rightAcc (RawTwoCellExpr.gen generator)
      = (state.1 + 1, composeMap state.2 (faceMap leftAcc.length state.1)) := by
  show (match generatorDom.length, generatorCod.length with
      | 0, 1 => (state.1 + 1, composeMap state.2 (faceMap leftAcc.length state.1))
      | 2, 1 => (state.1 - 1, composeMap state.2 (degenMap leftAcc.length (state.1 - 1)))
      | _, _ => state) = _
  rw [hdom, hcod]

/-- Running a generator of DEGENERACY arity `(2,1)` shrinks the width and post-composes the degeneracy `σ_p`. -/
theorem arityRunMonoCell_gen_degen {signature : ModeSignature}
    {overallSource overallTarget sourceMode targetMode : signature.graph.Mode}
    {generatorDom generatorCod : ModalityPath signature.graph sourceMode targetMode}
    (generator : signature.twoCell generatorDom generatorCod)
    (state : Nat × List Nat)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (hdom : generatorDom.length = 2) (hcod : generatorCod.length = 1) :
    arityRunMonoCell state leftAcc rightAcc (RawTwoCellExpr.gen generator)
      = (state.1 - 1, composeMap state.2 (degenMap leftAcc.length (state.1 - 1))) := by
  show (match generatorDom.length, generatorCod.length with
      | 0, 1 => (state.1 + 1, composeMap state.2 (faceMap leftAcc.length state.1))
      | 2, 1 => (state.1 - 1, composeMap state.2 (degenMap leftAcc.length (state.1 - 1)))
      | _, _ => state) = _
  rw [hdom, hcod]

/-! ## The fold-decomposition over a `spineDiff` difference-list (generic; no discipline) -/

/-- ★ **The fold-decomposition.**  Folding `arityFoldStepAtom` over `cell.spineDiff leftAcc rightAcc rest` equals
running the cell alone (`arityRunMonoCell`) then over `rest`.  Structural recursion on the cell — the payload-blind
twin of `monadMonoProcessSpine_spineDiff`. -/
theorem arityMonoProcessSpine_spineDiff {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc : ModalityPath signature.graph localTarget overallTarget) →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (state : Nat × List Nat) →
    (rest : List (SpineAtom signature overallSource overallTarget)) →
    arityMonoProcessSpine state (cell.spineDiff leftAcc rightAcc rest)
      = arityMonoProcessSpine (arityRunMonoCell state leftAcc rightAcc cell) rest
  | _, _, _, _, _, _, .gen _, _, _ => rfl
  | _, _, _, _, _, _, .id _, _, _ => rfl
  | _, _, leftAcc, rightAcc, _, _, .vcomp cellLeft cellRight, state, rest => by
      show arityMonoProcessSpine state
          (cellLeft.spineDiff leftAcc rightAcc (cellRight.spineDiff leftAcc rightAcc rest))
        = arityMonoProcessSpine (arityRunMonoCell state leftAcc rightAcc (RawTwoCellExpr.vcomp cellLeft cellRight)) rest
      rw [arityMonoProcessSpine_spineDiff leftAcc rightAcc cellLeft state (cellRight.spineDiff leftAcc rightAcc rest),
        arityMonoProcessSpine_spineDiff leftAcc rightAcc cellRight (arityRunMonoCell state leftAcc rightAcc cellLeft) rest]
      congr 1
      show arityRunMonoCell (arityRunMonoCell state leftAcc rightAcc cellLeft) leftAcc rightAcc cellRight
        = arityMonoProcessSpine state (cellLeft.spineDiff leftAcc rightAcc (cellRight.spineDiff leftAcc rightAcc []))
      rw [arityMonoProcessSpine_spineDiff leftAcc rightAcc cellLeft state (cellRight.spineDiff leftAcc rightAcc [])]
      rfl
  | _, _, leftAcc, rightAcc, _, _, .whiskerLeft oneCell body, state, rest =>
      arityMonoProcessSpine_spineDiff (composePath leftAcc oneCell) rightAcc body state rest
  | _, _, leftAcc, rightAcc, _, _, .whiskerRight oneCell body, state, rest =>
      arityMonoProcessSpine_spineDiff leftAcc (composePath oneCell rightAcc) body state rest

/-- Running a vertical composite is running the first factor then the second. -/
theorem arityRunMonoCell_vcomp {signature : ModeSignature}
    {overallSource overallTarget localSource localTarget : signature.graph.Mode}
    (state : Nat × List Nat)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph localSource localTarget}
    (cellLeft : RawTwoCellExpr signature oneCellF oneCellG)
    (cellRight : RawTwoCellExpr signature oneCellG oneCellH) :
    arityRunMonoCell state leftAcc rightAcc (RawTwoCellExpr.vcomp cellLeft cellRight)
      = arityRunMonoCell (arityRunMonoCell state leftAcc rightAcc cellLeft) leftAcc rightAcc cellRight :=
  arityMonoProcessSpine_spineDiff leftAcc rightAcc cellLeft state (cellRight.spineDiff leftAcc rightAcc [])

/-- Running a left-whiskered cell shifts the left accumulator by the whisker (definitional). -/
theorem arityRunMonoCell_whiskerLeft {signature : ModeSignature}
    {overallSource overallTarget localSource localMiddle localTarget : signature.graph.Mode}
    (state : Nat × List Nat)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    (oneCell : ModalityPath signature.graph localSource localMiddle)
    {oneCellG oneCellH : ModalityPath signature.graph localMiddle localTarget}
    (body : RawTwoCellExpr signature oneCellG oneCellH) :
    arityRunMonoCell state leftAcc rightAcc (RawTwoCellExpr.whiskerLeft oneCell body)
      = arityRunMonoCell state (composePath leftAcc oneCell) rightAcc body := rfl

/-- Running a right-whiskered cell shifts the right accumulator by the whisker (definitional). -/
theorem arityRunMonoCell_whiskerRight {signature : ModeSignature}
    {overallSource overallTarget localSource localMiddle localTarget : signature.graph.Mode}
    (state : Nat × List Nat)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    (oneCell : ModalityPath signature.graph localMiddle localTarget)
    {oneCellF oneCellG : ModalityPath signature.graph localSource localMiddle}
    (body : RawTwoCellExpr signature oneCellF oneCellG) :
    arityRunMonoCell state leftAcc rightAcc (RawTwoCellExpr.whiskerRight oneCell body)
      = arityRunMonoCell state leftAcc (composePath oneCell rightAcc) body := rfl

/-- `arityMonotoneMapOf` IS the `.2` of `arityRunMonoCell` from the source-length identity state at empty
accumulators (definitional bridge). -/
theorem arityMonotoneMapOf_eq_runMonoCell {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    arityMonotoneMapOf cell
      = (arityRunMonoCell (sourcePath.length, idMap sourcePath.length)
          (identityPath sourceMode) (identityPath targetMode) cell).2 := rfl

/-! ## The length-width invariant (Layer B, discipline threaded through the `_gen` case) -/

/-- The length-width invariant at a GENERATOR — the discipline disjunction furnishes the eta / mu `±1` length
change. -/
theorem arityRunMonoCell_width_gen {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {overallSource overallTarget sourceMode targetMode : signature.graph.Mode}
    {generatorDom generatorCod : ModalityPath signature.graph sourceMode targetMode}
    (generator : signature.twoCell generatorDom generatorCod)
    (width : Nat) (map : List Nat)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (hwidth : width = leftAcc.length + generatorDom.length + rightAcc.length) :
    (arityRunMonoCell (width, map) leftAcc rightAcc (RawTwoCellExpr.gen generator)).1
      = leftAcc.length + generatorCod.length + rightAcc.length := by
  rcases disc generator with ⟨hdom, hcod⟩ | ⟨hdom, hcod⟩
  · rw [arityRunMonoCell_gen_face generator (width, map) leftAcc rightAcc hdom hcod]
    show width + 1 = leftAcc.length + generatorCod.length + rightAcc.length
    rw [hwidth, hcod, hdom]
    exact monadEtaWidthShift leftAcc.length rightAcc.length
  · rw [arityRunMonoCell_gen_degen generator (width, map) leftAcc rightAcc hdom hcod]
    show width - 1 = leftAcc.length + generatorCod.length + rightAcc.length
    rw [hwidth, hcod, hdom]
    exact monadMuWidthShift leftAcc.length rightAcc.length

/-- ★ **The length-width invariant.**  Given the running width equals the current 1-cell length, running the cell
lands the width at the codomain 1-cell length.  Structural recursion; the generator step via the discipline. -/
theorem arityRunMonoCell_width {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (width : Nat) → (map : List Nat) →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc : ModalityPath signature.graph localTarget overallTarget) →
    width = leftAcc.length + localDom.length + rightAcc.length →
    (arityRunMonoCell (width, map) leftAcc rightAcc cell).1
      = leftAcc.length + localCod.length + rightAcc.length
  | _, _, _, _, .gen generator, width, map, leftAcc, rightAcc, hwidth =>
      arityRunMonoCell_width_gen disc generator width map leftAcc rightAcc hwidth
  | _, _, _, _, .id _, _, _, _, _, hwidth => hwidth
  | _, _, _, _, .vcomp cellLeft cellRight, width, map, leftAcc, rightAcc, hwidth => by
      rw [arityRunMonoCell_vcomp]
      exact arityRunMonoCell_width disc cellRight _ _ leftAcc rightAcc
        (arityRunMonoCell_width disc cellLeft width map leftAcc rightAcc hwidth)
  | _, _, _, _, .whiskerLeft oneCell body, width, map, leftAcc, rightAcc, hwidth => by
      rename_i bodyDom bodyCod
      rw [arityRunMonoCell_whiskerLeft,
          arityRunMonoCell_width disc body width map (composePath leftAcc oneCell) rightAcc (by
            rw [hwidth, ModalityPath.length_composePath oneCell bodyDom,
                ModalityPath.length_composePath leftAcc oneCell,
                Nat.add_assoc leftAcc.length oneCell.length bodyDom.length]),
          ModalityPath.length_composePath leftAcc oneCell,
          ModalityPath.length_composePath oneCell bodyCod,
          Nat.add_assoc leftAcc.length oneCell.length bodyCod.length]
  | _, _, _, _, .whiskerRight oneCell body, width, map, leftAcc, rightAcc, hwidth => by
      rename_i bodyDom bodyCod
      rw [arityRunMonoCell_whiskerRight,
          arityRunMonoCell_width disc body width map leftAcc (composePath oneCell rightAcc) (by
            rw [hwidth, ModalityPath.length_composePath bodyDom oneCell,
                ModalityPath.length_composePath oneCell rightAcc,
                ← Nat.add_assoc leftAcc.length bodyDom.length oneCell.length,
                Nat.add_assoc (leftAcc.length + bodyDom.length) oneCell.length rightAcc.length]),
          ModalityPath.length_composePath oneCell rightAcc,
          ModalityPath.length_composePath bodyCod oneCell,
          ← Nat.add_assoc leftAcc.length bodyCod.length oneCell.length,
          Nat.add_assoc (leftAcc.length + bodyCod.length) oneCell.length rightAcc.length]

/-! ## The fold lands in a genuine Δ₊ morphism (mapsInto), discipline threaded -/

/-- The `mapsInto` invariant at a GENERATOR — the eta case is `cupPreservesMapsInto`; the mu case is
`internalCapPreservesMapsInto` (the degeneracy is INTERNAL by the length-width precondition). -/
theorem arityRunMonoCell_mapsInto_gen {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {overallSource overallTarget sourceMode targetMode : signature.graph.Mode}
    {generatorDom generatorCod : ModalityPath signature.graph sourceMode targetMode}
    (generator : signature.twoCell generatorDom generatorCod)
    (width : Nat) (map : List Nat)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (hwidth : width = leftAcc.length + generatorDom.length + rightAcc.length)
    (hmap : mapsInto map width) :
    mapsInto (arityRunMonoCell (width, map) leftAcc rightAcc (RawTwoCellExpr.gen generator)).2
      (arityRunMonoCell (width, map) leftAcc rightAcc (RawTwoCellExpr.gen generator)).1 := by
  rcases disc generator with ⟨hdom, hcod⟩ | ⟨hdom, hcod⟩
  · rw [arityRunMonoCell_gen_face generator (width, map) leftAcc rightAcc hdom hcod]
    exact cupPreservesMapsInto leftAcc.length width map hmap
  · rw [arityRunMonoCell_gen_degen generator (width, map) leftAcc rightAcc hdom hcod]
    show mapsInto (composeMap map (degenMap leftAcc.length (width - 1))) (width - 1)
    have hwidthPred : width - 1 = leftAcc.length + 1 + rightAcc.length := by
      rw [hwidth, hdom]; exact monadMuWidthShift leftAcc.length rightAcc.length
    rw [hwidthPred]
    have hinternal : leftAcc.length < leftAcc.length + 1 + rightAcc.length :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self leftAcc.length)
        (Nat.le_add_right (leftAcc.length + 1) rightAcc.length)
    have hmapSucc : mapsInto map (leftAcc.length + 1 + rightAcc.length + 1) := by
      have hsucc : leftAcc.length + 1 + rightAcc.length + 1 = width := by
        rw [hwidth, hdom]
        show leftAcc.length + 1 + rightAcc.length + 1 = leftAcc.length + 2 + rightAcc.length
        rw [Nat.add_right_comm leftAcc.length 2 rightAcc.length,
            Nat.add_right_comm leftAcc.length 1 rightAcc.length]
      rw [hsucc]; exact hmap
    exact internalCapPreservesMapsInto leftAcc.length (leftAcc.length + 1 + rightAcc.length)
      map hmapSucc hinternal

/-- ★ **The fold lands every free 2-cell in a genuine Δ₊ morphism** — the running map maps INTO the running width.
Structural recursion; the generator step via `arityRunMonoCell_mapsInto_gen`. -/
theorem arityRunMonoCell_mapsInto {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (width : Nat) → (map : List Nat) →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc : ModalityPath signature.graph localTarget overallTarget) →
    width = leftAcc.length + localDom.length + rightAcc.length →
    mapsInto map width →
    mapsInto (arityRunMonoCell (width, map) leftAcc rightAcc cell).2
      (arityRunMonoCell (width, map) leftAcc rightAcc cell).1
  | _, _, _, _, .gen generator, width, map, leftAcc, rightAcc, hwidth, hmap =>
      arityRunMonoCell_mapsInto_gen disc generator width map leftAcc rightAcc hwidth hmap
  | _, _, _, _, .id _, _, _, _, _, _, hmap => hmap
  | _, _, _, _, .vcomp cellLeft cellRight, width, map, leftAcc, rightAcc, hwidth, hmap => by
      rw [arityRunMonoCell_vcomp]
      exact arityRunMonoCell_mapsInto disc cellRight _ _ leftAcc rightAcc
        (arityRunMonoCell_width disc cellLeft width map leftAcc rightAcc hwidth)
        (arityRunMonoCell_mapsInto disc cellLeft width map leftAcc rightAcc hwidth hmap)
  | _, _, _, _, .whiskerLeft oneCell body, width, map, leftAcc, rightAcc, hwidth, hmap => by
      rename_i bodyDom _
      rw [arityRunMonoCell_whiskerLeft]
      exact arityRunMonoCell_mapsInto disc body width map (composePath leftAcc oneCell) rightAcc (by
        rw [hwidth, ModalityPath.length_composePath oneCell bodyDom,
            ModalityPath.length_composePath leftAcc oneCell,
            Nat.add_assoc leftAcc.length oneCell.length bodyDom.length]) hmap
  | _, _, _, _, .whiskerRight oneCell body, width, map, leftAcc, rightAcc, hwidth, hmap => by
      rename_i bodyDom _
      rw [arityRunMonoCell_whiskerRight]
      exact arityRunMonoCell_mapsInto disc body width map leftAcc (composePath oneCell rightAcc) (by
        rw [hwidth, ModalityPath.length_composePath bodyDom oneCell,
            ModalityPath.length_composePath oneCell rightAcc,
            ← Nat.add_assoc leftAcc.length bodyDom.length oneCell.length,
            Nat.add_assoc (leftAcc.length + bodyDom.length) oneCell.length rightAcc.length]) hmap

/-! ## The running map's length is fold-invariant (discipline threaded through the `_gen` case) -/

/-- The fold never changes the map's LENGTH: each generator step post-composes a same-length face / degeneracy
factor.  The discipline furnishes the two arity arms; both are `composeMap_length`. -/
theorem arityRunMonoCell_map_length {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (state : Nat × List Nat) →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc : ModalityPath signature.graph localTarget overallTarget) →
    (arityRunMonoCell state leftAcc rightAcc cell).2.length = state.2.length
  | _, _, _, _, .gen generator, state, leftAcc, rightAcc => by
      rcases disc generator with ⟨hdom, hcod⟩ | ⟨hdom, hcod⟩
      · rw [arityRunMonoCell_gen_face generator state leftAcc rightAcc hdom hcod]; exact composeMap_length _ _
      · rw [arityRunMonoCell_gen_degen generator state leftAcc rightAcc hdom hcod]; exact composeMap_length _ _
  | _, _, _, _, .id _, _, _, _ => rfl
  | _, _, _, _, .vcomp cellLeft cellRight, state, leftAcc, rightAcc => by
      rw [arityRunMonoCell_vcomp, arityRunMonoCell_map_length disc cellRight _ leftAcc rightAcc,
          arityRunMonoCell_map_length disc cellLeft state leftAcc rightAcc]
  | _, _, _, _, .whiskerLeft oneCell body, state, leftAcc, rightAcc => by
      rw [arityRunMonoCell_whiskerLeft]
      exact arityRunMonoCell_map_length disc body state (composePath leftAcc oneCell) rightAcc
  | _, _, _, _, .whiskerRight oneCell body, state, leftAcc, rightAcc => by
      rw [arityRunMonoCell_whiskerRight]
      exact arityRunMonoCell_map_length disc body state leftAcc (composePath oneCell rightAcc)

/-! ## The incoming map post-composes: the factorization (discipline threaded) -/

/-- The factorization at a GENERATOR — from the identity state the first fold step is exactly the face / degeneracy
factor, so the general-state result post-composes the incoming map onto it.  The discipline furnishes both arms. -/
theorem arityRunMonoCell_mapFactor_gen {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {overallSource overallTarget sourceMode targetMode : signature.graph.Mode}
    {generatorDom generatorCod : ModalityPath signature.graph sourceMode targetMode}
    (generator : signature.twoCell generatorDom generatorCod)
    (state : Nat × List Nat)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (hwidth : state.1 = leftAcc.length + generatorDom.length + rightAcc.length) :
    (arityRunMonoCell state leftAcc rightAcc (RawTwoCellExpr.gen generator)).2
      = composeMap state.2
          (arityRunMonoCell (state.1, idMap state.1) leftAcc rightAcc (RawTwoCellExpr.gen generator)).2 := by
  rcases disc generator with ⟨hdom, hcod⟩ | ⟨hdom, hcod⟩
  · rw [arityRunMonoCell_gen_face generator state leftAcc rightAcc hdom hcod,
        arityRunMonoCell_gen_face generator (state.1, idMap state.1) leftAcc rightAcc hdom hcod]
    show composeMap state.2 (faceMap leftAcc.length state.1)
      = composeMap state.2 (composeMap (idMap state.1) (faceMap leftAcc.length state.1))
    have hcollapse : composeMap (idMap state.1) (faceMap leftAcc.length state.1)
        = faceMap leftAcc.length state.1 := by
      have hc := composeMap_idMap_eq (faceMap leftAcc.length state.1)
      rw [faceMap_length leftAcc.length state.1] at hc
      exact hc
    rw [hcollapse]
  · rw [arityRunMonoCell_gen_degen generator state leftAcc rightAcc hdom hcod,
        arityRunMonoCell_gen_degen generator (state.1, idMap state.1) leftAcc rightAcc hdom hcod]
    show composeMap state.2 (degenMap leftAcc.length (state.1 - 1))
      = composeMap state.2 (composeMap (idMap state.1) (degenMap leftAcc.length (state.1 - 1)))
    have hsucc : state.1 - 1 + 1 = state.1 := by
      have hwidthPred : state.1 - 1 = leftAcc.length + 1 + rightAcc.length := by
        rw [hwidth, hdom]; exact monadMuWidthShift leftAcc.length rightAcc.length
      rw [hwidthPred, hwidth, hdom]
      show leftAcc.length + 1 + rightAcc.length + 1 = leftAcc.length + 2 + rightAcc.length
      rw [Nat.add_right_comm leftAcc.length 2 rightAcc.length,
          Nat.add_right_comm leftAcc.length 1 rightAcc.length]
    have hcollapse : composeMap (idMap state.1) (degenMap leftAcc.length (state.1 - 1))
        = degenMap leftAcc.length (state.1 - 1) := by
      have hc := composeMap_idMap_eq (degenMap leftAcc.length (state.1 - 1))
      rw [degenMap_length leftAcc.length (state.1 - 1), hsucc] at hc
      exact hc
    rw [hcollapse]

/-- ★ **The factorization: the incoming map post-composes onto the cell's local map.**  Running from state `(w, m)`
gives the same map as running from `(w, idMap w)`, left-composed with `m`.  Structural recursion; the generator
step via `arityRunMonoCell_mapFactor_gen`, the vcomp side conditions from `_width` / `_mapsInto` / `_map_length`. -/
theorem arityRunMonoCell_mapFactor {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (state : Nat × List Nat) →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc : ModalityPath signature.graph localTarget overallTarget) →
    state.1 = leftAcc.length + localDom.length + rightAcc.length →
    mapsInto state.2 state.1 →
    (arityRunMonoCell state leftAcc rightAcc cell).2
      = composeMap state.2 (arityRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cell).2
  | _, _, _, _, .gen generator, state, leftAcc, rightAcc, hwidth, _ =>
      arityRunMonoCell_mapFactor_gen disc generator state leftAcc rightAcc hwidth
  | _, _, _, _, .id _, state, _, _, _, hmap => (composeMap_idMap_right state.2 state.1 hmap).symm
  | _, _, _, _, .vcomp cellLeft cellRight, state, leftAcc, rightAcc, hwidth, hmap => by
      have hS1w : (arityRunMonoCell state leftAcc rightAcc cellLeft).1
          = leftAcc.length + _ + rightAcc.length :=
        arityRunMonoCell_width disc cellLeft state.1 state.2 leftAcc rightAcc hwidth
      have hT1w : (arityRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).1
          = leftAcc.length + _ + rightAcc.length :=
        arityRunMonoCell_width disc cellLeft state.1 (idMap state.1) leftAcc rightAcc hwidth
      have hS1into : mapsInto (arityRunMonoCell state leftAcc rightAcc cellLeft).2
          (arityRunMonoCell state leftAcc rightAcc cellLeft).1 :=
        arityRunMonoCell_mapsInto disc cellLeft state.1 state.2 leftAcc rightAcc hwidth hmap
      have hT1into : mapsInto (arityRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).2
          (arityRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).1 :=
        arityRunMonoCell_mapsInto disc cellLeft state.1 (idMap state.1) leftAcc rightAcc hwidth
          (idMap_mapsInto state.1)
      have hS1map : (arityRunMonoCell state leftAcc rightAcc cellLeft).2
          = composeMap state.2 (arityRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).2 :=
        arityRunMonoCell_mapFactor disc cellLeft state leftAcc rightAcc hwidth hmap
      have hwidthEq : (arityRunMonoCell state leftAcc rightAcc cellLeft).1
          = (arityRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).1 := hS1w.trans hT1w.symm
      have hT1len : (arityRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft).2.length
          = (idMap state.1).length :=
        arityRunMonoCell_map_length disc cellLeft (state.1, idMap state.1) leftAcc rightAcc
      rw [arityRunMonoCell_vcomp, arityRunMonoCell_vcomp,
          arityRunMonoCell_mapFactor disc cellRight (arityRunMonoCell state leftAcc rightAcc cellLeft)
            leftAcc rightAcc hS1w hS1into,
          arityRunMonoCell_mapFactor disc cellRight
            (arityRunMonoCell (state.1, idMap state.1) leftAcc rightAcc cellLeft)
            leftAcc rightAcc hT1w hT1into,
          hS1map, hwidthEq]
      exact composeMap_assoc state.2 _ _ (by rw [hT1len, idMap_length]; exact hmap)
  | _, _, _, _, .whiskerLeft oneCell body, state, leftAcc, rightAcc, hwidth, hmap => by
      rename_i bodyDom _
      rw [arityRunMonoCell_whiskerLeft, arityRunMonoCell_whiskerLeft]
      exact arityRunMonoCell_mapFactor disc body state (composePath leftAcc oneCell) rightAcc (by
        rw [hwidth, ModalityPath.length_composePath oneCell bodyDom,
            ModalityPath.length_composePath leftAcc oneCell,
            Nat.add_assoc leftAcc.length oneCell.length bodyDom.length]) hmap
  | _, _, _, _, .whiskerRight oneCell body, state, leftAcc, rightAcc, hwidth, hmap => by
      rename_i bodyDom _
      rw [arityRunMonoCell_whiskerRight, arityRunMonoCell_whiskerRight]
      exact arityRunMonoCell_mapFactor disc body state leftAcc (composePath oneCell rightAcc) (by
        rw [hwidth, ModalityPath.length_composePath bodyDom oneCell,
            ModalityPath.length_composePath oneCell rightAcc,
            ← Nat.add_assoc leftAcc.length bodyDom.length oneCell.length,
            Nat.add_assoc (leftAcc.length + bodyDom.length) oneCell.length rightAcc.length]) hmap

/-! ## The vertical-composition homomorphism + the two vcomp-congruence cases -/

/-- The run-level vcomp homomorphism at an ARBITRARY well-formed state. -/
theorem arityRunMonoCell_vcomp_map {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {overallSource overallTarget localSource localTarget : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph localSource localTarget}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH)
    (state : Nat × List Nat)
    (leftAcc : ModalityPath signature.graph overallSource localSource)
    (rightAcc : ModalityPath signature.graph localTarget overallTarget)
    (hwidth : state.1 = leftAcc.length + oneCellF.length + rightAcc.length)
    (hmap : mapsInto state.2 state.1) :
    (arityRunMonoCell state leftAcc rightAcc (RawTwoCellExpr.vcomp cellAlpha cellBeta)).2
      = composeMap (arityRunMonoCell state leftAcc rightAcc cellAlpha).2
          (arityRunMonoCell ((arityRunMonoCell state leftAcc rightAcc cellAlpha).1,
              idMap (arityRunMonoCell state leftAcc rightAcc cellAlpha).1)
            leftAcc rightAcc cellBeta).2 := by
  rw [arityRunMonoCell_vcomp]
  exact arityRunMonoCell_mapFactor disc cellBeta (arityRunMonoCell state leftAcc rightAcc cellAlpha)
    leftAcc rightAcc (arityRunMonoCell_width disc cellAlpha state.1 state.2 leftAcc rightAcc hwidth)
    (arityRunMonoCell_mapsInto disc cellAlpha state.1 state.2 leftAcc rightAcc hwidth hmap)

/-- ★ **The vertical-composition homomorphism.**  `arityMonotoneMapOf (α ⊟ β) = composeMap (map α) (map β)` — the
fold is a FUNCTOR on vertical composition. -/
theorem arityMonotoneMapOf_vcomp {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH) :
    arityMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = composeMap (arityMonotoneMapOf cellAlpha) (arityMonotoneMapOf cellBeta) := by
  have hpre : oneCellF.length = 0 + oneCellF.length + 0 := by rw [Nat.add_zero, Nat.zero_add]
  have key := arityRunMonoCell_vcomp_map disc cellAlpha cellBeta (oneCellF.length, idMap oneCellF.length)
      (identityPath (graph := signature.graph) sourceMode)
      (identityPath (graph := signature.graph) targetMode)
      hpre (idMap_mapsInto oneCellF.length)
  have hSw : (arityRunMonoCell (oneCellF.length, idMap oneCellF.length)
        (identityPath (graph := signature.graph) sourceMode)
        (identityPath (graph := signature.graph) targetMode) cellAlpha).1 = oneCellG.length := by
    rw [arityRunMonoCell_width disc cellAlpha oneCellF.length (idMap oneCellF.length)
          (identityPath (graph := signature.graph) sourceMode)
          (identityPath (graph := signature.graph) targetMode) hpre]
    show 0 + oneCellG.length + 0 = oneCellG.length
    rw [Nat.add_zero, Nat.zero_add]
  refine (arityMonotoneMapOf_eq_runMonoCell (RawTwoCellExpr.vcomp cellAlpha cellBeta)).trans
    (key.trans ?_)
  rw [hSw]
  rfl

/-- ★ **The LEFT-vcomp-congruence case.** -/
theorem arityMonotoneMapOf_vcompCongrLeft {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellAlpha' : RawTwoCellExpr signature oneCellF oneCellG}
    (cellBeta : RawTwoCellExpr signature oneCellG oneCellH)
    (hmap : arityMonotoneMapOf cellAlpha = arityMonotoneMapOf cellAlpha') :
    arityMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = arityMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha' cellBeta) := by
  rw [arityMonotoneMapOf_vcomp disc, arityMonotoneMapOf_vcomp disc, hmap]

/-- ★ **The RIGHT-vcomp-congruence case.** -/
theorem arityMonotoneMapOf_vcompCongrRight {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    {cellBeta cellBeta' : RawTwoCellExpr signature oneCellG oneCellH}
    (hmap : arityMonotoneMapOf cellBeta = arityMonotoneMapOf cellBeta') :
    arityMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta)
      = arityMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta') := by
  rw [arityMonotoneMapOf_vcomp disc, arityMonotoneMapOf_vcomp disc, hmap]

/-! ## The generator local-map values (the FACE / DEGENERACY normal forms of a disciplined generator) -/

/-- A FACE-arity generator's whole-cell local map is the empty map `[]` (the bare `eta`). -/
theorem arityMonotoneMapOf_gen_face {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {generatorDom generatorCod : ModalityPath signature.graph sourceMode targetMode}
    (generator : signature.twoCell generatorDom generatorCod)
    (hdom : generatorDom.length = 0) (hcod : generatorCod.length = 1) :
    arityMonotoneMapOf (RawTwoCellExpr.gen generator) = [] := by
  rw [arityMonotoneMapOf_eq_runMonoCell (RawTwoCellExpr.gen generator),
      arityRunMonoCell_gen_face generator (generatorDom.length, idMap generatorDom.length)
        (identityPath sourceMode) (identityPath targetMode) hdom hcod]
  show composeMap (idMap generatorDom.length) (faceMap (identityPath sourceMode).length generatorDom.length) = []
  rw [hdom]
  rfl

/-- A DEGENERACY-arity generator's whole-cell local map is the merge `[0, 0]` (the bare `mu`). -/
theorem arityMonotoneMapOf_gen_degen {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    {generatorDom generatorCod : ModalityPath signature.graph sourceMode targetMode}
    (generator : signature.twoCell generatorDom generatorCod)
    (hdom : generatorDom.length = 2) (hcod : generatorCod.length = 1) :
    arityMonotoneMapOf (RawTwoCellExpr.gen generator) = [0, 0] := by
  rw [arityMonotoneMapOf_eq_runMonoCell (RawTwoCellExpr.gen generator),
      arityRunMonoCell_gen_degen generator (generatorDom.length, idMap generatorDom.length)
        (identityPath sourceMode) (identityPath targetMode) hdom hcod]
  show composeMap (idMap generatorDom.length)
      (degenMap (identityPath sourceMode).length (generatorDom.length - 1)) = [0, 0]
  rw [hdom]
  have hc := composeMap_idMap_eq (degenMap (0 : Nat) (2 - 1))
  rw [degenMap_length (0 : Nat) (2 - 1)] at hc
  exact hc

/-! ## The whole-cell map length + codomain (the vcomp side conditions) -/

/-- The whole-cell monotone map has the source 1-cell's length as its domain. -/
theorem arityMonotoneMapOf_length {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    (arityMonotoneMapOf cell).length = sourcePath.length := by
  rw [arityMonotoneMapOf_eq_runMonoCell,
      arityRunMonoCell_map_length disc cell (sourcePath.length, idMap sourcePath.length)
        (identityPath (graph := signature.graph) sourceMode)
        (identityPath (graph := signature.graph) targetMode)]
  exact idMap_length sourcePath.length

/-- The whole-cell monotone map lands in the target 1-cell's length (a genuine Δ₊ codomain). -/
theorem arityMonotoneMapOf_mapsInto {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    mapsInto (arityMonotoneMapOf cell) targetPath.length := by
  have hwidth : sourcePath.length
      = (identityPath (graph := signature.graph) sourceMode).length + sourcePath.length
        + (identityPath (graph := signature.graph) targetMode).length := by
    show sourcePath.length = 0 + sourcePath.length + 0
    rw [Nat.add_zero, Nat.zero_add]
  have hmaps := arityRunMonoCell_mapsInto disc cell sourcePath.length (idMap sourcePath.length)
    (identityPath (graph := signature.graph) sourceMode)
    (identityPath (graph := signature.graph) targetMode) hwidth (idMap_mapsInto sourcePath.length)
  have hw1 : (arityRunMonoCell (sourcePath.length, idMap sourcePath.length)
      (identityPath (graph := signature.graph) sourceMode)
      (identityPath (graph := signature.graph) targetMode) cell).1 = targetPath.length := by
    rw [arityRunMonoCell_width disc cell sourcePath.length (idMap sourcePath.length)
          (identityPath (graph := signature.graph) sourceMode)
          (identityPath (graph := signature.graph) targetMode) hwidth]
    show 0 + targetPath.length + 0 = targetPath.length
    rw [Nat.add_zero, Nat.zero_add]
  rw [hw1] at hmaps
  rw [arityMonotoneMapOf_eq_runMonoCell]
  exact hmaps

/-! ## The whisker-embedding crux: the fold run at any context is the ordinal-sum embedding of the local map -/

/-- The generator case of the embedding lemma — face folds to the FACE decomposition of `[]`, degen to the
DEGENERACY decomposition of `[0, 0]`.  The discipline furnishes the two arity arms. -/
theorem arityRunMonoCell_localEmbed_gen {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {overallSource overallTarget sourceMode targetMode : signature.graph.Mode}
    {generatorDom generatorCod : ModalityPath signature.graph sourceMode targetMode}
    (generator : signature.twoCell generatorDom generatorCod)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget) :
    (arityRunMonoCell (leftAcc.length + generatorDom.length + rightAcc.length,
        idMap (leftAcc.length + generatorDom.length + rightAcc.length)) leftAcc rightAcc
        (RawTwoCellExpr.gen generator)).2
      = embedLocalMap leftAcc.length generatorCod.length rightAcc.length
          (arityMonotoneMapOf (RawTwoCellExpr.gen generator)) := by
  rcases disc generator with ⟨hdom, hcod⟩ | ⟨hdom, hcod⟩
  · rw [arityRunMonoCell_gen_face generator _ leftAcc rightAcc hdom hcod, hcod,
        arityMonotoneMapOf_gen_face generator hdom hcod, hdom]
    show composeMap (idMap (leftAcc.length + 0 + rightAcc.length))
        (faceMap leftAcc.length (leftAcc.length + 0 + rightAcc.length))
      = embedLocalMap leftAcc.length 1 rightAcc.length []
    have hstep : composeMap (idMap (leftAcc.length + 0 + rightAcc.length))
        (faceMap leftAcc.length (leftAcc.length + 0 + rightAcc.length))
        = faceMap leftAcc.length (leftAcc.length + 0 + rightAcc.length) := by
      have hc := composeMap_idMap_eq (faceMap leftAcc.length (leftAcc.length + 0 + rightAcc.length))
      rw [faceMap_length leftAcc.length (leftAcc.length + 0 + rightAcc.length)] at hc
      exact hc
    rw [hstep]
    exact faceMap_eq_embedLocalMap leftAcc.length rightAcc.length
  · rw [arityRunMonoCell_gen_degen generator _ leftAcc rightAcc hdom hcod, hcod,
        arityMonotoneMapOf_gen_degen generator hdom hcod, hdom]
    show composeMap (idMap (leftAcc.length + 2 + rightAcc.length))
        (degenMap leftAcc.length (leftAcc.length + 2 + rightAcc.length - 1))
      = embedLocalMap leftAcc.length 1 rightAcc.length [0, 0]
    rw [monadMuWidthShift leftAcc.length rightAcc.length]
    have hstep : composeMap (idMap (leftAcc.length + 2 + rightAcc.length))
        (degenMap leftAcc.length (leftAcc.length + 1 + rightAcc.length))
        = degenMap leftAcc.length (leftAcc.length + 1 + rightAcc.length) := by
      have hc := composeMap_idMap_eq (degenMap leftAcc.length (leftAcc.length + 1 + rightAcc.length))
      rw [degenMap_length leftAcc.length (leftAcc.length + 1 + rightAcc.length),
          show leftAcc.length + 1 + rightAcc.length + 1 = leftAcc.length + 2 + rightAcc.length from by
            rw [Nat.add_right_comm (leftAcc.length + 1) rightAcc.length 1]] at hc
      exact hc
    rw [hstep]
    exact degenMap_eq_embedLocalMap leftAcc.length rightAcc.length

/-- ★ **The whisker-embedding crux.**  Running the fold over a free 2-cell from the identity state at accumulators
`leftAcc / rightAcc` yields the ORDINAL-SUM embedding of the cell's LOCAL map into the `leftAcc.length`-prefixed,
`rightAcc.length`-suffixed context.  Structural recursion; generators via `arityRunMonoCell_localEmbed_gen`, vcomp
via `embedLocalMap_composeMap`, the whiskerings via `embedLocalMap_nest`. -/
theorem arityRunMonoCell_localEmbed {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {overallSource overallTarget : signature.graph.Mode} :
    {localSource localTarget : signature.graph.Mode} →
    {localDom localCod : ModalityPath signature.graph localSource localTarget} →
    (cell : RawTwoCellExpr signature localDom localCod) →
    (width : Nat) →
    (leftAcc : ModalityPath signature.graph overallSource localSource) →
    (rightAcc : ModalityPath signature.graph localTarget overallTarget) →
    width = leftAcc.length + localDom.length + rightAcc.length →
    (arityRunMonoCell (width, idMap width) leftAcc rightAcc cell).2
      = embedLocalMap leftAcc.length localCod.length rightAcc.length (arityMonotoneMapOf cell)
  | _, _, _, _, .gen generator, width, leftAcc, rightAcc, hw => by
      subst hw
      exact arityRunMonoCell_localEmbed_gen disc generator leftAcc rightAcc
  | _, _, _, _, .id path, width, leftAcc, rightAcc, hw => by
      subst hw
      show idMap (leftAcc.length + path.length + rightAcc.length)
        = embedLocalMap leftAcc.length path.length rightAcc.length (arityMonotoneMapOf (RawTwoCellExpr.id path))
      rw [show arityMonotoneMapOf (RawTwoCellExpr.id path) = idMap path.length from rfl, embedLocalMap_idMap]
  | _, _, _, oneCellH, .vcomp cellLeft cellRight, width, leftAcc, rightAcc, hw => by
      have hrange : mapsInto (arityMonotoneMapOf cellLeft) (arityMonotoneMapOf cellRight).length := by
        rw [arityMonotoneMapOf_length disc cellRight]; exact arityMonotoneMapOf_mapsInto disc cellLeft
      rw [arityRunMonoCell_vcomp_map disc cellLeft cellRight (width, idMap width) leftAcc rightAcc hw
            (idMap_mapsInto width),
          arityRunMonoCell_localEmbed disc cellLeft width leftAcc rightAcc hw,
          arityRunMonoCell_localEmbed disc cellRight
            (arityRunMonoCell (width, idMap width) leftAcc rightAcc cellLeft).1 leftAcc rightAcc
            (arityRunMonoCell_width disc cellLeft width (idMap width) leftAcc rightAcc hw),
          arityMonotoneMapOf_vcomp disc cellLeft cellRight,
          embedLocalMap_composeMap leftAcc.length rightAcc.length oneCellH.length
            (arityMonotoneMapOf cellLeft) (arityMonotoneMapOf cellRight) hrange,
          arityMonotoneMapOf_length disc cellRight]
  | _, _, _, _, .whiskerLeft oneCell body, width, leftAcc, rightAcc, hw => by
      rename_i sourceMode targetMode middleMode oneCellG oneCellH
      have hwBody : width = (composePath leftAcc oneCell).length + oneCellG.length + rightAcc.length := by
        rw [hw, ModalityPath.length_composePath oneCell oneCellG, ModalityPath.length_composePath leftAcc oneCell,
            Nat.add_assoc leftAcc.length oneCell.length oneCellG.length]
      have hMap : arityMonotoneMapOf (RawTwoCellExpr.whiskerLeft oneCell body)
          = embedLocalMap oneCell.length oneCellH.length 0 (arityMonotoneMapOf body) := by
        have hwMap : (composePath oneCell oneCellG).length = oneCell.length + oneCellG.length
            + (identityPath (graph := signature.graph) targetMode).length := by
          show (composePath oneCell oneCellG).length = oneCell.length + oneCellG.length + 0
          rw [ModalityPath.length_composePath oneCell oneCellG, Nat.add_zero]
        rw [arityMonotoneMapOf_eq_runMonoCell (RawTwoCellExpr.whiskerLeft oneCell body),
            arityRunMonoCell_whiskerLeft, composePath_identityPath_left]
        exact arityRunMonoCell_localEmbed disc body (composePath oneCell oneCellG).length oneCell
          (identityPath (graph := signature.graph) targetMode) hwMap
      rw [arityRunMonoCell_whiskerLeft,
          arityRunMonoCell_localEmbed disc body width (composePath leftAcc oneCell) rightAcc hwBody,
          ModalityPath.length_composePath leftAcc oneCell, hMap,
          ModalityPath.length_composePath oneCell oneCellH]
      have hnest := embedLocalMap_nest leftAcc.length oneCell.length oneCellH.length 0 rightAcc.length
        (arityMonotoneMapOf body)
      rw [Nat.add_zero, Nat.zero_add] at hnest
      exact hnest.symm
  | _, _, _, _, .whiskerRight oneCell body, width, leftAcc, rightAcc, hw => by
      rename_i sourceMode targetMode middleMode oneCellF oneCellG
      have hwBody : width = leftAcc.length + oneCellF.length + (composePath oneCell rightAcc).length := by
        rw [hw, ModalityPath.length_composePath oneCellF oneCell, ModalityPath.length_composePath oneCell rightAcc,
            ← Nat.add_assoc leftAcc.length oneCellF.length oneCell.length,
            Nat.add_assoc (leftAcc.length + oneCellF.length) oneCell.length rightAcc.length]
      have hMap : arityMonotoneMapOf (RawTwoCellExpr.whiskerRight oneCell body)
          = embedLocalMap 0 oneCellG.length oneCell.length (arityMonotoneMapOf body) := by
        have hwMap : (composePath oneCellF oneCell).length
            = (identityPath (graph := signature.graph) sourceMode).length + oneCellF.length
              + (composePath oneCell (identityPath (graph := signature.graph) targetMode)).length := by
          rw [ModalityPath.length_composePath oneCellF oneCell,
              ModalityPath.length_composePath oneCell (identityPath (graph := signature.graph) targetMode)]
          show oneCellF.length + oneCell.length = 0 + oneCellF.length + (oneCell.length + 0)
          rw [Nat.zero_add, Nat.add_zero]
        rw [arityMonotoneMapOf_eq_runMonoCell (RawTwoCellExpr.whiskerRight oneCell body),
            arityRunMonoCell_whiskerRight]
        have hkey := arityRunMonoCell_localEmbed disc body (composePath oneCellF oneCell).length
          (identityPath (graph := signature.graph) sourceMode)
          (composePath oneCell (identityPath (graph := signature.graph) targetMode)) hwMap
        rw [ModalityPath.length_composePath oneCell
              (identityPath (graph := signature.graph) targetMode)] at hkey
        exact hkey
      rw [arityRunMonoCell_whiskerRight,
          arityRunMonoCell_localEmbed disc body width leftAcc (composePath oneCell rightAcc) hwBody,
          ModalityPath.length_composePath oneCell rightAcc, hMap,
          ModalityPath.length_composePath oneCellG oneCell]
      have hnest := embedLocalMap_nest leftAcc.length 0 oneCellG.length oneCell.length rightAcc.length
        (arityMonotoneMapOf body)
      rw [Nat.add_zero, Nat.zero_add] at hnest
      exact hnest.symm

/-! ## The top-level whisker embeddings + the two WHISKER-congruence cases -/

/-- ★ **The LEFT-whisker embedding.** -/
theorem arityMonotoneMapOf_whiskerLeft {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode}
    (body : RawTwoCellExpr signature oneCellG oneCellH) :
    arityMonotoneMapOf (RawTwoCellExpr.whiskerLeft oneCell body)
      = embedLocalMap oneCell.length oneCellH.length 0 (arityMonotoneMapOf body) := by
  have hwMap : (composePath oneCell oneCellG).length = oneCell.length + oneCellG.length
      + (identityPath (graph := signature.graph) targetMode).length := by
    show (composePath oneCell oneCellG).length = oneCell.length + oneCellG.length + 0
    rw [ModalityPath.length_composePath oneCell oneCellG, Nat.add_zero]
  rw [arityMonotoneMapOf_eq_runMonoCell (RawTwoCellExpr.whiskerLeft oneCell body),
      arityRunMonoCell_whiskerLeft, composePath_identityPath_left]
  exact arityRunMonoCell_localEmbed disc body (composePath oneCell oneCellG).length oneCell
    (identityPath (graph := signature.graph) targetMode) hwMap

/-- ★ **The RIGHT-whisker embedding.** -/
theorem arityMonotoneMapOf_whiskerRight {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
    (oneCell : ModalityPath signature.graph middleMode targetMode)
    (body : RawTwoCellExpr signature oneCellF oneCellG) :
    arityMonotoneMapOf (RawTwoCellExpr.whiskerRight oneCell body)
      = embedLocalMap 0 oneCellG.length oneCell.length (arityMonotoneMapOf body) := by
  have hwMap : (composePath oneCellF oneCell).length
      = (identityPath (graph := signature.graph) sourceMode).length + oneCellF.length
        + (composePath oneCell (identityPath (graph := signature.graph) targetMode)).length := by
    rw [ModalityPath.length_composePath oneCellF oneCell,
        ModalityPath.length_composePath oneCell (identityPath (graph := signature.graph) targetMode)]
    show oneCellF.length + oneCell.length = 0 + oneCellF.length + (oneCell.length + 0)
    rw [Nat.zero_add, Nat.add_zero]
  rw [arityMonotoneMapOf_eq_runMonoCell (RawTwoCellExpr.whiskerRight oneCell body),
      arityRunMonoCell_whiskerRight]
  have hkey := arityRunMonoCell_localEmbed disc body (composePath oneCellF oneCell).length
    (identityPath (graph := signature.graph) sourceMode)
    (composePath oneCell (identityPath (graph := signature.graph) targetMode)) hwMap
  rw [ModalityPath.length_composePath oneCell
        (identityPath (graph := signature.graph) targetMode)] at hkey
  exact hkey

/-- ★ **The LEFT-whisker-congruence case.** -/
theorem arityMonotoneMapOf_whiskerLeftCongr {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode}
    {body body' : RawTwoCellExpr signature oneCellG oneCellH}
    (hmap : arityMonotoneMapOf body = arityMonotoneMapOf body') :
    arityMonotoneMapOf (RawTwoCellExpr.whiskerLeft oneCell body)
      = arityMonotoneMapOf (RawTwoCellExpr.whiskerLeft oneCell body') := by
  rw [arityMonotoneMapOf_whiskerLeft disc, arityMonotoneMapOf_whiskerLeft disc, hmap]

/-- ★ **The RIGHT-whisker-congruence case.** -/
theorem arityMonotoneMapOf_whiskerRightCongr {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
    (oneCell : ModalityPath signature.graph middleMode targetMode)
    {body body' : RawTwoCellExpr signature oneCellF oneCellG}
    (hmap : arityMonotoneMapOf body = arityMonotoneMapOf body') :
    arityMonotoneMapOf (RawTwoCellExpr.whiskerRight oneCell body)
      = arityMonotoneMapOf (RawTwoCellExpr.whiskerRight oneCell body') := by
  rw [arityMonotoneMapOf_whiskerRight disc, arityMonotoneMapOf_whiskerRight disc, hmap]

/-! ## The horizontal composite + the Godement / interchange invariance (Layer A reused verbatim) -/

/-- ★ **The map of a horizontal composite** — the two-whisker `composeMap` of the ordinal-sum embeddings.
`hcomp α β = vcomp (whiskerRight _ α) (whiskerLeft _ β)`; immediate from the vcomp homomorphism + the two whisker
embeddings. -/
theorem arityMonotoneMapOf_hcomp {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellFDom oneCellFCod : ModalityPath signature.graph sourceMode middleMode}
    {oneCellGDom oneCellGCod : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellFDom oneCellFCod)
    (cellBeta : RawTwoCellExpr signature oneCellGDom oneCellGCod) :
    arityMonotoneMapOf (RawTwoCellExpr.hcomp cellAlpha cellBeta)
      = composeMap (embedLocalMap 0 oneCellFCod.length oneCellGDom.length (arityMonotoneMapOf cellAlpha))
          (embedLocalMap oneCellFCod.length oneCellGCod.length 0 (arityMonotoneMapOf cellBeta)) := by
  have hstep := arityMonotoneMapOf_vcomp disc (RawTwoCellExpr.whiskerRight oneCellGDom cellAlpha)
    (RawTwoCellExpr.whiskerLeft oneCellFCod cellBeta)
  rw [arityMonotoneMapOf_whiskerRight disc, arityMonotoneMapOf_whiskerLeft disc] at hstep
  exact hstep

/-- ★★ **The Godement / interchange invariance of the fold.**  The two orders of the Godement product fold to the
SAME monotone map, via `arityMonotoneMapOf_hcomp` (both sides become two-whisker composites),
`embedLocalMap_composeMap` (split the inner vcomps), `composeMap_middleSwap` (reassociate), and
`embedLocalMap_disjointCommute` (the middle blocks commute, cap-free on Δ — Layer A reused verbatim). -/
theorem arityMonotoneMapOf_interchange {signature : ModeSignature} (disc : HasFaceDegenArity signature)
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fLow fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid gHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature fLow fMid)
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (cellBetaUpper : RawTwoCellExpr signature gMid gHigh) :
    arityMonotoneMapOf (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cellAlpha cellAlphaUpper)
        (RawTwoCellExpr.vcomp cellBeta cellBetaUpper))
      = arityMonotoneMapOf (RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp cellAlpha cellBeta)
          (RawTwoCellExpr.hcomp cellAlphaUpper cellBetaUpper)) := by
  have hrange1 : mapsInto (arityMonotoneMapOf cellAlpha) (arityMonotoneMapOf cellAlphaUpper).length := by
    rw [arityMonotoneMapOf_length disc cellAlphaUpper]; exact arityMonotoneMapOf_mapsInto disc cellAlpha
  have hrange2 : mapsInto (arityMonotoneMapOf cellBeta) (arityMonotoneMapOf cellBetaUpper).length := by
    rw [arityMonotoneMapOf_length disc cellBetaUpper]; exact arityMonotoneMapOf_mapsInto disc cellBeta
  have hAB : mapsInto (embedLocalMap 0 fMid.length gLow.length (arityMonotoneMapOf cellAlpha))
      (embedLocalMap 0 fHigh.length gLow.length (arityMonotoneMapOf cellAlphaUpper)).length := by
    rw [embedLocalMap_length, arityMonotoneMapOf_length disc cellAlphaUpper]
    exact embedLocalMap_mapsInto 0 fMid.length gLow.length _ (arityMonotoneMapOf_mapsInto disc cellAlpha)
  have hBinto : mapsInto (embedLocalMap 0 fHigh.length gLow.length (arityMonotoneMapOf cellAlphaUpper))
      (fHigh.length + gLow.length) := by
    have hb := embedLocalMap_mapsInto 0 fHigh.length gLow.length _ (arityMonotoneMapOf_mapsInto disc cellAlphaUpper)
    rw [Nat.zero_add] at hb; exact hb
  have hClen : (embedLocalMap fHigh.length gMid.length 0 (arityMonotoneMapOf cellBeta)).length
      = fHigh.length + gLow.length := by
    rw [embedLocalMap_length, arityMonotoneMapOf_length disc cellBeta]; exact Nat.add_zero _
  have hBC : mapsInto (embedLocalMap 0 fHigh.length gLow.length (arityMonotoneMapOf cellAlphaUpper))
      (embedLocalMap fHigh.length gMid.length 0 (arityMonotoneMapOf cellBeta)).length := by
    rw [hClen]; exact hBinto
  have hAinto : mapsInto (embedLocalMap 0 fMid.length gLow.length (arityMonotoneMapOf cellAlpha))
      (fMid.length + gLow.length) := by
    have ha := embedLocalMap_mapsInto 0 fMid.length gLow.length _ (arityMonotoneMapOf_mapsInto disc cellAlpha)
    rw [Nat.zero_add] at ha; exact ha
  have hC'len : (embedLocalMap fMid.length gMid.length 0 (arityMonotoneMapOf cellBeta)).length
      = fMid.length + gLow.length := by
    rw [embedLocalMap_length, arityMonotoneMapOf_length disc cellBeta]; exact Nat.add_zero _
  have hAC' : mapsInto (embedLocalMap 0 fMid.length gLow.length (arityMonotoneMapOf cellAlpha))
      (embedLocalMap fMid.length gMid.length 0 (arityMonotoneMapOf cellBeta)).length := by
    rw [hC'len]; exact hAinto
  have hC'into : mapsInto (embedLocalMap fMid.length gMid.length 0 (arityMonotoneMapOf cellBeta))
      (fMid.length + gMid.length) := by
    have hc := embedLocalMap_mapsInto fMid.length gMid.length 0 _ (arityMonotoneMapOf_mapsInto disc cellBeta)
    rw [Nat.add_zero] at hc; exact hc
  have hB'len : (embedLocalMap 0 fHigh.length gMid.length (arityMonotoneMapOf cellAlphaUpper)).length
      = fMid.length + gMid.length := by
    rw [embedLocalMap_length, arityMonotoneMapOf_length disc cellAlphaUpper]
    exact congrArg (· + gMid.length) (Nat.zero_add fMid.length)
  have hC'B' : mapsInto (embedLocalMap fMid.length gMid.length 0 (arityMonotoneMapOf cellBeta))
      (embedLocalMap 0 fHigh.length gMid.length (arityMonotoneMapOf cellAlphaUpper)).length := by
    rw [hB'len]; exact hC'into
  have hswap : composeMap (embedLocalMap 0 fHigh.length gLow.length (arityMonotoneMapOf cellAlphaUpper))
        (embedLocalMap fHigh.length gMid.length 0 (arityMonotoneMapOf cellBeta))
      = composeMap (embedLocalMap fMid.length gMid.length 0 (arityMonotoneMapOf cellBeta))
        (embedLocalMap 0 fHigh.length gMid.length (arityMonotoneMapOf cellAlphaUpper)) :=
    embedLocalMap_disjointCommute fMid.length fHigh.length gMid.length gLow.length
      (arityMonotoneMapOf cellAlphaUpper) (arityMonotoneMapOf cellBeta)
      (arityMonotoneMapOf_length disc cellAlphaUpper) (arityMonotoneMapOf_mapsInto disc cellAlphaUpper)
      (arityMonotoneMapOf_length disc cellBeta) (arityMonotoneMapOf_mapsInto disc cellBeta)
  rw [arityMonotoneMapOf_hcomp disc (RawTwoCellExpr.vcomp cellAlpha cellAlphaUpper)
        (RawTwoCellExpr.vcomp cellBeta cellBetaUpper),
      arityMonotoneMapOf_vcomp disc cellAlpha cellAlphaUpper, arityMonotoneMapOf_vcomp disc cellBeta cellBetaUpper,
      embedLocalMap_composeMap 0 gLow.length fHigh.length (arityMonotoneMapOf cellAlpha)
        (arityMonotoneMapOf cellAlphaUpper) hrange1,
      embedLocalMap_composeMap fHigh.length 0 gHigh.length (arityMonotoneMapOf cellBeta)
        (arityMonotoneMapOf cellBetaUpper) hrange2,
      arityMonotoneMapOf_length disc cellAlphaUpper, arityMonotoneMapOf_length disc cellBetaUpper,
      arityMonotoneMapOf_vcomp disc (RawTwoCellExpr.hcomp cellAlpha cellBeta)
        (RawTwoCellExpr.hcomp cellAlphaUpper cellBetaUpper),
      arityMonotoneMapOf_hcomp disc cellAlpha cellBeta, arityMonotoneMapOf_hcomp disc cellAlphaUpper cellBetaUpper]
  exact composeMap_middleSwap
    (embedLocalMap 0 fMid.length gLow.length (arityMonotoneMapOf cellAlpha))
    (embedLocalMap 0 fHigh.length gLow.length (arityMonotoneMapOf cellAlphaUpper))
    (embedLocalMap fHigh.length gMid.length 0 (arityMonotoneMapOf cellBeta))
    (embedLocalMap fHigh.length gHigh.length 0 (arityMonotoneMapOf cellBetaUpper))
    (embedLocalMap fMid.length gMid.length 0 (arityMonotoneMapOf cellBeta))
    (embedLocalMap 0 fHigh.length gMid.length (arityMonotoneMapOf cellAlphaUpper))
    hAB hBC hAC' hC'B' hswap

/-! ## The bundle assembled from any discipline -/

/-- ★★ **The convertibility-soundness bundle from any face/degen arity discipline.**  The five fields are the
Godement interchange invariance + the four fold-congruence homomorphisms, generic over the discipline.  This is the
signature-generic inhabitant of `ArityFoldConvSound`; the monad and the pushout are its two instances. -/
def arityFoldConvSound_ofDiscipline {signature : ModeSignature} (disc : HasFaceDegenArity signature) :
    ArityFoldConvSound signature where
  interchange := arityMonotoneMapOf_interchange disc
  vcompCongrLeft := arityMonotoneMapOf_vcompCongrLeft disc
  vcompCongrRight := arityMonotoneMapOf_vcompCongrRight disc
  whiskerLeftCongr := arityMonotoneMapOf_whiskerLeftCongr disc
  whiskerRightCongr := arityMonotoneMapOf_whiskerRightCongr disc

/-! ## The walking-monad instance: the discipline holds by `cases generator` (re-derives `monadArityFoldConvSound`) -/

/-- ★ **The walking monad satisfies the face/degen arity discipline** — eta has arity `(0,1)`, mu has arity
`(2,1)`, each by `rfl` on the bespoke `MonadTwoCell` boundaries. -/
theorem monadHasFaceDegenArity : HasFaceDegenArity monadModeSignature := by
  intro _ _ generatorDom generatorCod generator
  cases generator with
  | eta => exact Or.inl ⟨rfl, rfl⟩
  | mu => exact Or.inr ⟨rfl, rfl⟩

/-- The generic bundle at the monad discipline inhabits `ArityFoldConvSound monadModeSignature` — an alternate,
discipline-routed construction of `monadArityFoldConvSound`. -/
def monadArityFoldConvSound_ofDiscipline : ArityFoldConvSound monadModeSignature :=
  arityFoldConvSound_ofDiscipline monadHasFaceDegenArity

/-! ## The interpreter's length invariant (the single genuinely-new brick for the pushout discipline)

`ModeComputad.interpretWordFrom` folds a generator-word head-first into a typed `ModalityPath`.  Whenever it
succeeds, the built path has length EXACTLY the word length: each `cons` step adds one letter for one word head.
This is the bridge from a reconstructed 2-generator's boundary-PATH lengths to its stored boundary-WORD lengths,
which the pushout discipline reads off by casing the two reconstructed generators. -/

/-- ★ **The interpreter's length invariant.**  If `interpretWordFrom src word` succeeds with path `path`, then
`path.length = word.length`.  Structural on the word; the `cons` step peels one letter and one path node, the
path-length equality extracted from the `Sigma`-valued result by the non-dependent `.snd.length` projection
(propext-free, no `HEq` juggling). -/
theorem interpretWordFrom_length (computad : ModeComputad) :
    (word : List (Fin computad.modalityGenerators.length)) →
    (src targetMode : Fin computad.modeCount) →
    (path : ModalityPath computad.toModeGraph src targetMode) →
    computad.interpretWordFrom src word = some ⟨targetMode, path⟩ →
    path.length = word.length
  | [], src, targetMode, path, hyp => by
      have hsig : (⟨src, ModalityPath.nil (graph := computad.toModeGraph) src⟩ :
          Sigma (fun tm => ModalityPath computad.toModeGraph src tm)) = ⟨targetMode, path⟩ :=
        Option.some.inj hyp
      exact (congrArg (fun entry => entry.snd.length) hsig).symm
  | index :: rest, src, targetMode, path, hyp => by
      dsimp only [ModeComputad.interpretWordFrom] at hyp
      by_cases hcond : (computad.modalityGenerators.get index).1 = src
      · rw [dif_pos hcond] at hyp
        cases hInner : computad.interpretWordFrom (computad.modalityGenerators.get index).2 rest with
        | none => rw [hInner] at hyp; nomatch hyp
        | some restInterpreted =>
            rw [hInner] at hyp
            have hsig := Option.some.inj hyp
            have hrest : restInterpreted.snd.length = rest.length :=
              interpretWordFrom_length computad rest (computad.modalityGenerators.get index).2
                restInterpreted.fst restInterpreted.snd hInner
            have hlen : restInterpreted.snd.length + 1 = path.length :=
              congrArg (fun entry => entry.snd.length) hsig
            show path.length = rest.length + 1
            rw [← hlen, hrest]
      · rw [dif_neg hcond] at hyp
        nomatch hyp

/-! ## The pushout discipline + the pushout bundle instance -/

/-- The two reconstructed generators of the pushout have face/degen word-arities: index `0` (retagged `eta`) has
words `([], [t])` — lengths `(0, 1)`; index `1` (retagged `mu`) has words `([t, t], [t])` — lengths `(2, 1)`.
Read straight off the concrete `twoCellGenerators` list (each `rfl`), the `Fin 2` index cased propext-free. -/
theorem pushoutTwoGenWordArity (index : Fin involutionMonadPushout.twoCellGenerators.length) :
    ((involutionMonadPushout.twoCellGenerators.get index).lhs.length = 0
        ∧ (involutionMonadPushout.twoCellGenerators.get index).rhs.length = 1)
      ∨ ((involutionMonadPushout.twoCellGenerators.get index).lhs.length = 2
        ∧ (involutionMonadPushout.twoCellGenerators.get index).rhs.length = 1) :=
  match index with
  | ⟨0, _⟩ => Or.inl ⟨rfl, rfl⟩
  | ⟨1, _⟩ => Or.inr ⟨rfl, rfl⟩
  | ⟨count + 2, isLt⟩ =>
      (Nat.not_lt_zero count (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ isLt))).elim

/-- ★★ **The pushout satisfies the face/degen arity discipline.**  Every reconstructed 2-generator has arity
`(0,1)` or `(2,1)`: its boundary PATH lengths equal its stored boundary WORD lengths (`interpretWordFrom_length`),
which for the two `Fin 2` generators are `(0,1)` / `(2,1)` (`pushoutTwoGenWordArity`).  This is the "reconstruction
arity discipline" the r7 residual named — the PROPOSITIONAL (not definitional) arity fact. -/
theorem pushoutHasFaceDegenArity : HasFaceDegenArity involutionMonadPushout.toModeSignature := by
  intro sourceMode targetMode generatorDom generatorCod generator
  obtain ⟨index, hlhs, hrhs⟩ := generator
  have hdomLen : generatorDom.length = (involutionMonadPushout.twoCellGenerators.get index).lhs.length :=
    interpretWordFrom_length involutionMonadPushout
      (involutionMonadPushout.twoCellGenerators.get index).lhs sourceMode targetMode generatorDom hlhs
  have hcodLen : generatorCod.length = (involutionMonadPushout.twoCellGenerators.get index).rhs.length :=
    interpretWordFrom_length involutionMonadPushout
      (involutionMonadPushout.twoCellGenerators.get index).rhs sourceMode targetMode generatorCod hrhs
  rcases pushoutTwoGenWordArity index with ⟨hlenDom, hlenCod⟩ | ⟨hlenDom, hlenCod⟩
  · exact Or.inl ⟨hdomLen.trans hlenDom, hcodLen.trans hlenCod⟩
  · exact Or.inr ⟨hdomLen.trans hlenDom, hcodLen.trans hlenCod⟩

/-- ★★★ **The convertibility-soundness bundle for the pushout signature — INHABITED, hypothesis-free.**  The
generic bundle `arityFoldConvSound_ofDiscipline` at the pushout's face/degen arity discipline.  This is EXACTLY the
r7 residual `ArityFoldConvSound involutionMonadPushout.toModeSignature`, now discharged: the Godement interchange
soundness (`embedLocalMap_disjointCommute`, cap-free on Δ, reused verbatim) plus the four fold-congruence
homomorphisms (the fold engine re-homed generic-over-the-discipline). -/
def pushoutArityFoldConvSound : ArityFoldConvSound involutionMonadPushout.toModeSignature :=
  arityFoldConvSound_ofDiscipline pushoutHasFaceDegenArity

/-! ## ★★★ THE MILESTONE: the LIVE combined pushout isFalse, HYPOTHESIS-FREE -/

/-- ★★★ **THE #2043 MILESTONE — the LIVE combined non-convertibility, UNCONDITIONAL.**  `crossPairAlpha` is NOT
saturated-pushout-convertible to `crossPairBeta` — a hypothesis-FREE verdict: the arity fold, invariant under the
completed pushout convertibility via the now-INHABITED bundle `pushoutArityFoldConvSound`, forces their maps equal
(`[0, 2] = [0, 1]`), contradicting `crossPair_arityMapsDiffer`.  Pairs with r6's UNCONDITIONAL isTrue
`crossPairConvertibleCounterpart` (disjoint-component whiskers commute) as the COMPLETE discriminating pair over a
real-relation pushout: same-component monad faces are non-convertible, disjoint-component whiskers are convertible.
The r7 conditional `crossPairPushoutNonConv` is now applied to the shipped bundle — the reflection is
hypothesis-free. -/
theorem crossPairPushoutNonConvUnconditional :
    ¬ SaturatedConvOver involutionMonadPushout.toModeSignature crossPairPushoutRel
        crossPairAlpha crossPairBeta :=
  crossPairPushoutNonConv pushoutArityFoldConvSound

/-! ## Non-vacuity: the completed discriminating pair, traced end-to-end -/

-- The δ₁ face whiskered by s folds to `[0, 2]`, the δ₀ face to `[0, 1]`; they differ. Expect `true`.
#eval decide (arityMonotoneMapOf crossPairAlpha = [0, 2] ∧ arityMonotoneMapOf crossPairBeta = [0, 1]
  ∧ arityMonotoneMapOf crossPairAlpha ≠ arityMonotoneMapOf crossPairBeta)

/-! ## Honesty markers -/

/-- ★★★ **THE #2043 MILESTONE marker — the LIVE combined pushout isFalse ships HYPOTHESIS-FREE (r8).**  The bundle
residual `ArityFoldConvSound involutionMonadPushout.toModeSignature` is DISCHARGED (`pushoutArityFoldConvSound`) by
re-homing the walking-monad Δ-fold soundness generic-over-a-face/degen-arity-discipline
(`arityFoldConvSound_ofDiscipline`) and proving the pushout satisfies that discipline
(`pushoutHasFaceDegenArity`, via the new interpreter length invariant `interpretWordFrom_length` casing the two
`Fin 2` reconstructed generators).  Layer A (the `embedLocalMap` ordinal-sum algebra, incl. the cap-free
disjoint-window commute) is reused VERBATIM; Layer B (the fold engine `arityRunMonoCell` + width / mapsInto /
factorization / localEmbed + the vcomp/whisker/hcomp homomorphisms + interchange) is the generic port; Layer C (the
five `_gen` base cases) is the sole genuine content, discharged from the discipline's `(0,1)`/`(2,1)` disjunction.
Hence `crossPairPushoutNonConvUnconditional` is hypothesis-free, and with r6's isTrue
`crossPairConvertibleCounterpart` it is the COMPLETE discriminating pair.  Literature: free-product / Δ₊ word
problem (Nyberg-Brodda; Street; Mac Lane §VII.5); the transport-along-a-discipline is the institution satisfaction
condition made computational.  `= true`. -/
def fxAmalg_hasLiveMonadPushoutBundle : Bool := true

/-- **Honesty marker — the r9+ residual: the GENERAL saturated dispatch decision.**  This milestone ships the LIVE
non-convertibility of the SPECIFIC discriminating pair (`crossPairAlpha` / `crossPairBeta`) via the arity-fold
reflection — a SEMANTIC invariant (`arityMonotoneMapOf`) that reflects blockwise monad inequality directly, WITHOUT
routing through the Nelson-Oppen / Baader-Tinelli block-projection DISPATCH (`DispatchSaturated.lean`).  What stays
open for r9+ is the GENERAL decision procedure: a `Decidable (SaturatedConvOver involutionMonadPushout.toModeSignature
… )` for ARBITRARY pushout pairs.  That needs either (i) the reconstruction decider reseat
(`fxAmalg_hasReconstructionDecoderReseat`, fib-3-coupled) or (ii) the purification-reflection completeness for the
wire-creating unit/mult regime (`fxAmalg_hasSaturatedDispatchTheorem`, the Ghilardi-Nicolini-Zucchelli
Noetherian-interface residual).  The arity-fold gives an unconditional isFalse on any pair whose monotone maps
differ, and an isTrue on any free/whisker-exchange pair — a partial-but-sound decision, not the full dispatch.
`= false`. -/
def fxAmalg_hasGeneralPushoutDispatch : Bool := false

end FX1Poly.Polygraph.Amalgam

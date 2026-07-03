/-! # Polygraph/Computad/Signature — the generic 2-computad carrier: quiver, free 1-cells, 2-polygraph signature

The SIGNATURE-FREE data model of a 2-polygraph (a 2-computad, after Burroni / Street / Batanin): a quiver of
0- and 1-cell GENERATORS, the FREE 1-cells (composable paths) it generates with their category laws, decidable
1-cell equality, and the 2-polygraph signature layering generating 2-cells over parallel pairs of free 1-cells.

This is pure (∞,ω)-category presentation machinery with NO dependence on any mode theory (MTT / modalities): it
is parameterised over an arbitrary `ModeGraph`.  The MODE axis instantiates it (its `ModeSignature` IS a
2-computad), and the free-2-cell rewriting tower is built over it; but the carrier itself is generic, so it
lives in the signature-free `Polygraph/` library.

## What is shipped here (each piece zero-axiom)

  * **`ModeGraph`** — the 0- and 1-cell generators: a quiver of 0-cells and typed 1-cell generators.
  * **`ModalityPath`** — the free 1-cells: finite composable sequences of generators.  `identityPath` (the
    empty path) and `composePath` (concatenation) with the three CATEGORY LAWS (`composePath_identityPath_left`
    definitional, `composePath_assoc` and `composePath_identityPath_right` by structural induction); `length`
    is the free-monoid word length.
  * **`singletonModalityPath`** — the generator embedding as the length-1 1-cell, with its length smoke and
    injectivity (the free construction's faithfulness).
  * **`ModalityPath.firstStepTarget` / `modalityPathDecEq`** — decidable equality of free 1-cells given
    decidable generators (the §3.13 `oneCellEqDecidable`), propext-free.
  * **`ModeSignature`** — the 2-polygraph: a `ModeGraph` plus a family of generating 2-cells between PARALLEL
    free 1-cells (their boundary).

The RawCategory / RawTwoCategory PACKAGING of the free category (`freeModeCategory`, the §3.13 `ModeTheory`
structure) is the mode-axis specialisation and stays in `FX1Poly.Tier0.Mode.TwoCategoryCore`.

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Polygraph

/-! ## The 0- and 1-cell generators: the mode quiver -/

/-- A **mode quiver** — the 0- and 1-cell generators of a mode theory: `Mode`s (the 0-cells) and typed
`Modality` generators (the 1-cells, `Modality sourceMode targetMode`).  This is the underlying directed graph
(1-computad) the free 1-category is built on. -/
structure ModeGraph where
  /-- The modes (0-cells). -/
  Mode : Type
  /-- The generating modalities (1-cell generators), typed by source and target mode. -/
  Modality : Mode → Mode → Type

/-! ## The free 1-cells: paths of modalities -/

/-- A **modality path** — a free 1-cell: a finite composable sequence of modality generators from
`sourceMode` to `targetMode`.  `nil` is the identity 1-cell; `cons` prepends a generator.  These are the
1-cells of the free category on the quiver. -/
inductive ModalityPath (graph : ModeGraph) : graph.Mode → graph.Mode → Type where
  /-- The empty path — the identity 1-cell at a mode. -/
  | nil : (mode : graph.Mode) → ModalityPath graph mode mode
  /-- Prepend a modality generator to a path. -/
  | cons : {sourceMode middleMode targetMode : graph.Mode} →
      graph.Modality sourceMode middleMode →
      ModalityPath graph middleMode targetMode →
      ModalityPath graph sourceMode targetMode

/-- The length of a modality path (the number of generators composed) — the 1-cell's word length. -/
def ModalityPath.length {graph : ModeGraph} {sourceMode targetMode : graph.Mode}
    (path : ModalityPath graph sourceMode targetMode) : Nat :=
  match path with
  | .nil _ => 0
  | .cons _ rest => rest.length + 1

/-- The identity 1-cell at a mode (the empty path). -/
def identityPath {graph : ModeGraph} (mode : graph.Mode) : ModalityPath graph mode mode :=
  ModalityPath.nil mode

/-- 1-cell composition — concatenation of modality paths (recursion on the first path).  Its associativity
and right identity (making this a category) are proved below. -/
def composePath {graph : ModeGraph} {sourceMode middleMode targetMode : graph.Mode}
    (first : ModalityPath graph sourceMode middleMode)
    (second : ModalityPath graph middleMode targetMode) : ModalityPath graph sourceMode targetMode :=
  match first with
  | .nil _ => second
  | .cons modality rest => .cons modality (composePath rest second)

/-- Smoke: the left identity law holds DEFINITIONALLY (`composePath` recurses on the first path, so the empty
path on the left is erased on the nose). -/
theorem composePath_identityPath_left {graph : ModeGraph} {sourceMode targetMode : graph.Mode}
    (path : ModalityPath graph sourceMode targetMode) : composePath (identityPath sourceMode) path = path :=
  rfl

/-- Path composition is associative — by structural induction on the first path (the recursive call threads
the `∀`-quantified tail paths, kept in the conclusion so the motive stays general). -/
theorem composePath_assoc {graph : ModeGraph} {sourceMode middleMode : graph.Mode}
    (first : ModalityPath graph sourceMode middleMode) :
    ∀ {nextMode lastMode : graph.Mode}
      (second : ModalityPath graph middleMode nextMode) (third : ModalityPath graph nextMode lastMode),
      composePath (composePath first second) third = composePath first (composePath second third) := by
  induction first with
  | nil _ => intro _ _ second third; rfl
  | cons modality rest ih => intro _ _ second third; exact congrArg (ModalityPath.cons modality) (ih second third)

/-- The empty path is a right identity for composition (the left identity is definitional). -/
theorem composePath_identityPath_right {graph : ModeGraph} {sourceMode targetMode : graph.Mode}
    (path : ModalityPath graph sourceMode targetMode) :
    composePath path (identityPath targetMode) = path := by
  induction path with
  | nil _ => rfl
  | cons modality rest ih => exact congrArg (ModalityPath.cons modality) ih

/-! ## The generator embedding + its faithfulness -/

/-- A generating modality embeds as the length-1 1-cell (the single-step path). -/
def singletonModalityPath {graph : ModeGraph} {sourceMode targetMode : graph.Mode}
    (modality : graph.Modality sourceMode targetMode) : ModalityPath graph sourceMode targetMode :=
  ModalityPath.cons modality (ModalityPath.nil targetMode)

/-- The generator embedding has length 1 (a freeness smoke: generators are exactly the atomic 1-cells). -/
theorem singletonModalityPath_length {graph : ModeGraph} {sourceMode targetMode : graph.Mode}
    (modality : graph.Modality sourceMode targetMode) : (singletonModalityPath modality).length = 1 :=
  rfl

/-- The Yoneda-style faithfulness of the free construction: distinct modality generators give distinct 1-cells
(the generator embedding is injective).  The round-trip's "back" direction: a generator is recovered from its
singleton path. -/
theorem singletonModalityPath_injective {graph : ModeGraph} {sourceMode targetMode : graph.Mode}
    {modalityOne modalityTwo : graph.Modality sourceMode targetMode}
    (singletonsEqual : singletonModalityPath modalityOne = singletonModalityPath modalityTwo) :
    modalityOne = modalityTwo := by
  have consEqual : ModalityPath.cons modalityOne (ModalityPath.nil targetMode)
      = ModalityPath.cons modalityTwo (ModalityPath.nil targetMode) := singletonsEqual
  injection consEqual

/-! ## Decidable equality of 1-cells — the §3.13 `oneCellEqDecidable` -/

/-- The target mode of a path's first step (`none` for the identity), a propext-free discriminator used to
separate `cons`es whose middle modes differ. -/
def ModalityPath.firstStepTarget {graph : ModeGraph} {sourceMode targetMode : graph.Mode}
    (path : ModalityPath graph sourceMode targetMode) : Option graph.Mode :=
  match path with
  | .nil _ => none
  | @ModalityPath.cons _ _ middleMode _ _ _ => some middleMode

/-- ★ **Decidable equality of 1-cells** (modality paths), given decidable equality on the generating modes and
modalities — the §3.13 `oneCellEqDecidable`.  Propext-free (the `RawTermDecEq` technique: same-index `cases`
for the constructor injectivity, the `length` / `firstStepTarget` discriminators for the impossible /
distinct-middle-mode cases). -/
def modalityPathDecEq {graph : ModeGraph}
    (modeDecEq : DecidableEq graph.Mode)
    (modalityDecEq : (sourceMode targetMode : graph.Mode) → DecidableEq (graph.Modality sourceMode targetMode)) :
    {sourceMode targetMode : graph.Mode} →
      (firstPath secondPath : ModalityPath graph sourceMode targetMode) → Decidable (firstPath = secondPath)
  | _, _, .nil _, .nil _ => .isTrue rfl
  | _, _, .nil _, .cons _ _ =>
      .isFalse (fun pathsEqual => Nat.noConfusion (congrArg ModalityPath.length pathsEqual))
  | _, _, .cons _ _, .nil _ =>
      .isFalse (fun pathsEqual => Nat.noConfusion (congrArg ModalityPath.length pathsEqual))
  | _, _, @ModalityPath.cons _ _ middleOne _ modalityOne restOne,
          @ModalityPath.cons _ _ middleTwo _ modalityTwo restTwo =>
    match modeDecEq middleOne middleTwo with
    | .isFalse middlesDiffer =>
        .isFalse (fun pathsEqual =>
          middlesDiffer (Option.some.inj (congrArg ModalityPath.firstStepTarget pathsEqual)))
    | .isTrue middlesEqual => by
        subst middlesEqual
        exact match modalityDecEq _ _ modalityOne modalityTwo,
                    modalityPathDecEq modeDecEq modalityDecEq restOne restTwo with
          | .isTrue modalityEqual, .isTrue restEqual => .isTrue (by subst modalityEqual; subst restEqual; rfl)
          | .isFalse modalitiesDiffer, _ =>
              .isFalse (by intro pathsEqual; cases pathsEqual; exact modalitiesDiffer rfl)
          | _, .isFalse restsDiffer =>
              .isFalse (by intro pathsEqual; cases pathsEqual; exact restsDiffer rfl)

/-! ## The 2-polygraph signature -/

/-- A **mode signature** — the 2-polygraph presenting a mode theory: a `ModeGraph` (0- and 1-cell generators)
plus a family `twoCell` of generating 2-cells between PARALLEL 1-cells (modality paths sharing source and
target).  The freely-generated strict 2-category (with the laws) is `mode-1`. -/
structure ModeSignature where
  /-- The underlying quiver of modes and modality generators. -/
  graph : ModeGraph
  /-- The generating 2-cells, indexed by a parallel pair of modality paths (their boundary). -/
  twoCell : {sourceMode targetMode : graph.Mode} →
    ModalityPath graph sourceMode targetMode → ModalityPath graph sourceMode targetMode → Type

end FX1Poly.Polygraph

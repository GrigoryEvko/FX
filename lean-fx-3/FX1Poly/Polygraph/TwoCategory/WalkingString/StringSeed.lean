import FX1Poly.Polygraph.Computad.Signature

/-! # Polygraph/TwoCategory/WalkingString/StringSeed — the walking ADJOINT-TRIPLE seed (`F ⊣ G ⊣ H`)

The presentation of the WALKING ADJOINT TRIPLE as a 2-computad (`ModeSignature`).  Where the walking ADJUNCTION
seed (`AdjunctionSeed`) has TWO modes, a 1-generator each way, and TWO 2-cell generators (unit / counit), and the
walking MONAD seed (`MonadSeed`) has ONE mode and one endo-generator, the walking ADJOINT TRIPLE is TWO adjacent
adjunctions `F ⊣ G ⊣ H` SHARING the central 1-cell `G`:

  * TWO modes `base` (mode `A`) and `tip` (mode `B`),
  * THREE modality generators — `left = F : base ⟶ tip`, `right = G : tip ⟶ base` (the SHARED middle), and
    `coLeft = H : base ⟶ tip` (parallel to `F`, a DISTINCT generator),
  * FOUR generating 2-cells — two units and two counits, one adjunction each:
      - the LOWER adjunction `F ⊣ G` contributes `unitLower : id_base ⇒ F·G` (a CUP) and
        `counitLower : G·F ⇒ id_tip` (a CAP),
      - the UPPER adjunction `G ⊣ H` contributes `unitUpper : id_tip ⇒ G·H` (a CUP) and
        `counitUpper : H·G ⇒ id_base` (a CAP).

The FOUR triangle identities (each adjunction contributes two) are posited as saturation relations in
`WalkingString/StringSaturatedConv`; here we ship the seed (the free generators only).  The boundary convention
mirrors `FreeAdjunctionData` (`AdjointStrings`): a unit is `id ⇒ leftCell·rightCell`, a counit is
`rightCell·leftCell ⇒ id`, so for `F ⊣ G` (`leftCell = F`, `rightCell = G`) and `G ⊣ H` (`leftCell = G`,
`rightCell = H`) the four boundaries are as above.

By Schanuel–Street ("The free adjunction") the SINGLE walking adjunction's homs are the augmented simplex
category Δ₊; by the adjoint-string literature (nLab `adjoint string` / `adjoint triple`) an adjoint triple is
"an adjoint pair in the 2-category of adjoint pairs" (Licata–Shulman), i.e. two adjacent Δ-levels coupled through
the shared `G`.  This seed is the free 2-category on that data — the walking adjoint triple.

Generic presentation data (no mode-theory dependence).  Zero external dependencies beyond the computad signature.
Raw Lean 4 + Init. -/

namespace FX1Poly.Polygraph

/-! ## The walking-adjoint-triple quiver: two modes, three modality generators -/

/-- The two modes (0-cells) of the walking adjoint triple: `base` (the source object `A`) and `tip` (the target
object `B`). -/
inductive AdjointTripleMode where
  /-- The source mode `A`. -/
  | base
  /-- The target mode `B`. -/
  | tip

/-- The three generating modalities (1-cells) of the walking adjoint triple: the left adjoint `F = left`, the
central shared 1-cell `G = right`, and the right adjoint `H = coLeft`.  `F` and `H` are PARALLEL (both
`base ⟶ tip`) but DISTINCT generators; `G : tip ⟶ base` is right adjoint to `F` and left adjoint to `H`. -/
inductive AdjointTripleModality : AdjointTripleMode → AdjointTripleMode → Type where
  /-- The left adjoint `F : base ⟶ tip`. -/
  | left : AdjointTripleModality AdjointTripleMode.base AdjointTripleMode.tip
  /-- The central shared 1-cell `G : tip ⟶ base`. -/
  | right : AdjointTripleModality AdjointTripleMode.tip AdjointTripleMode.base
  /-- The right adjoint `H : base ⟶ tip` (parallel to `F`, distinct generator). -/
  | coLeft : AdjointTripleModality AdjointTripleMode.base AdjointTripleMode.tip

/-- The walking-adjoint-triple quiver: two modes, three modality generators. -/
def adjointTripleGraph : ModeGraph where
  Mode := AdjointTripleMode
  Modality := AdjointTripleModality

/-! ## The four endo-paths the generating 2-cells live between -/

/-- The composite 1-cell `F·G : base ⟶ tip ⟶ base` — the codomain of the lower unit `η` (a `base` endo-path). -/
def stringFG : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.base :=
  ModalityPath.cons AdjointTripleModality.left
    (ModalityPath.cons AdjointTripleModality.right
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))

/-- The composite 1-cell `G·F : tip ⟶ base ⟶ tip` — the domain of the lower counit `ε` (a `tip` endo-path). -/
def stringGF : ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.tip :=
  ModalityPath.cons AdjointTripleModality.right
    (ModalityPath.cons AdjointTripleModality.left
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip))

/-- The composite 1-cell `G·H : tip ⟶ base ⟶ tip` — the codomain of the upper unit `η'` (a `tip` endo-path). -/
def stringGH : ModalityPath adjointTripleGraph AdjointTripleMode.tip AdjointTripleMode.tip :=
  ModalityPath.cons AdjointTripleModality.right
    (ModalityPath.cons AdjointTripleModality.coLeft
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip))

/-- The composite 1-cell `H·G : base ⟶ tip ⟶ base` — the domain of the upper counit `ε'` (a `base` endo-path). -/
def stringHG : ModalityPath adjointTripleGraph AdjointTripleMode.base AdjointTripleMode.base :=
  ModalityPath.cons AdjointTripleModality.coLeft
    (ModalityPath.cons AdjointTripleModality.right
      (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base))

/-! ## The four generating 2-cells: two units and two counits -/

/-- The generating 2-cells of the walking adjoint triple — two units (`unitLower`, `unitUpper`) and two counits
(`counitLower`, `counitUpper`), between parallel endo-paths.  These are the GENERATORS only; the FOUR triangle
identities relating them are the saturation relations (`WalkingString/StringSaturatedConv`).  Each is a cup
(arity `(0, 2)`) or a cap (arity `(2, 0)`), exactly like the walking-adjunction seed but at THREE generators. -/
inductive StringTwoCell :
    {sourceMode targetMode : AdjointTripleMode} →
    ModalityPath adjointTripleGraph sourceMode targetMode →
    ModalityPath adjointTripleGraph sourceMode targetMode → Type where
  /-- The **lower unit** `η : id_base ⇒ F·G` (arity `(0, 2)`, the lower CUP). -/
  | unitLower : StringTwoCell (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base) stringFG
  /-- The **lower counit** `ε : G·F ⇒ id_tip` (arity `(2, 0)`, the lower CAP). -/
  | counitLower : StringTwoCell stringGF (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip)
  /-- The **upper unit** `η' : id_tip ⇒ G·H` (arity `(0, 2)`, the upper CUP). -/
  | unitUpper : StringTwoCell (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.tip) stringGH
  /-- The **upper counit** `ε' : H·G ⇒ id_base` (arity `(2, 0)`, the upper CAP). -/
  | counitUpper : StringTwoCell stringHG (ModalityPath.nil (graph := adjointTripleGraph) AdjointTripleMode.base)

/-- ★ The **walking-adjoint-triple mode signature** — the free 2-category on `F ⊣ G ⊣ H`: two modes, three
modality generators (`F`/`G`/`H` with `G` shared), and the four unit / counit 2-cell generators.  This is the
seed the two-level (two-colour) matching tower is instantiated at. -/
def adjointTripleModeSignature : ModeSignature where
  graph := adjointTripleGraph
  twoCell := fun firstPath secondPath => StringTwoCell firstPath secondPath

/-! ## Freeness smokes -/

/-- Smoke: `F·G` is the length-2 endo-path at `base`. -/
theorem stringFG_length : stringFG.length = 2 := rfl

/-- Smoke: `G·F` is the length-2 endo-path at `tip`. -/
theorem stringGF_length : stringGF.length = 2 := rfl

/-- Smoke: `G·H` is the length-2 endo-path at `tip`. -/
theorem stringGH_length : stringGH.length = 2 := rfl

/-- Smoke: `H·G` is the length-2 endo-path at `base`. -/
theorem stringHG_length : stringHG.length = 2 := rfl

/-- Smoke: `F` and `H` are PARALLEL (both `base ⟶ tip`) but DISTINCT generators — the injectivity of the free
construction separates them, so the adjoint triple is not a degenerate collapse of `F` onto `H`. -/
theorem string_left_ne_coLeft :
    singletonModalityPath (graph := adjointTripleGraph) AdjointTripleModality.left
      ≠ singletonModalityPath (graph := adjointTripleGraph) AdjointTripleModality.coLeft := by
  intro pathsEqual
  have generatorsEqual : AdjointTripleModality.left = AdjointTripleModality.coLeft :=
    singletonModalityPath_injective pathsEqual
  nomatch generatorsEqual

end FX1Poly.Polygraph

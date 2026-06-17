import FX1Poly.Tier0.Mode.MultiplierEndofunctor

/-! # mode-16 — MTT□: unifying cubical + modal via the orthogonality exchange rules

Cubical type theory adds an INTERVAL `𝕀` (with endpoints / FACES) and the PATH functor `□A = 𝕀 → A`; multimodal
type theory adds MODALITIES `M`.  Combining them (Gratzer–Cavallo et al.; the transpension reading,
Nuyts–Devriese) hinges on the **orthogonality EXCHANGE rule**: a modality and the interval are ORTHOGONAL, so
the modality COMMUTES with the path functor — `M(𝕀 → A) ≅ (𝕀 → M A)`.  Equivalently, applying a modality to a
path is a path of modalized values, and the FACES exchange (the modal path's endpoints are the modality applied
to the path's endpoints).

The exchange is a genuine CONSTRAINT (a product modality `A × C` does NOT satisfy it), and the modalities that DO
are the READER / Π modalities `M A = D → A` — for which the exchange is the argument-SWAP (both round trips by
`rfl`).  The cube / path functor `□A = 𝕀 → A` is ITSELF such a reader modality, so the orthogonality of two cube
dimensions is the dimension-swap.  This ties `mode-11`'s reader (`weaken ⊣ Π`) and `mode-12`'s `cubeInterval`
together.

## What this file ships (each piece zero-axiom)

  * **`ModalOperator`** — a modality as an endofunctor (`Apply` + `map` + the two functor laws), with
    `identityModalOperator`, `readerModalOperator` (`D → -`), and `cubeModality` (`□ = 𝕀 → -`, a reader).
  * **`OrthogonalExchange modality 𝕀`** — the exchange iso `M(𝕀 → A) ≅ (𝕀 → M A)` (`push` / `pull` mutually
    inverse) plus the FACE coherence `push` commutes with endpoint evaluation.  Derived: `push_injective`.
  * **`identityExchange`** + **`readerExchange`** — the witnesses (the reader is the genuine NON-degenerate one,
    by argument swap), and `cubeCubeExchange` (two cube dimensions are orthogonal — the dimension swap).
  * **`readerExchange_cube_faces`** — the FACE coherence at the concrete cube endpoints `0` / `1`.

## What is DEFERRED (markers)

  * the modal KAN operations (`hcomp` / `transp` / `coe`) commuting with modalities (`hasModalKanOperations`);
  * the full de Morgan FACE LATTICE / cube-category orthogonality, beyond the single interval functor
    (`hasFaceLatticeOrthogonality`);
  * the modal LOCK `◐_μ` exchanging with the dimension context extension at the CwF / context level (cross-axis,
    `fib`) (`hasModalLockDimensionExchange`);
  * the kernel `gen_path` / `gen_modality` orthogonality rows (cross-axis, `fib`)
    (`hasKernelCubicalModalConnection`).

Zero external dependencies beyond the mode core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## The path / interval functor -/

/-- A **path space** over an interval `Interval` — the cube functor `A^Interval = Interval → A` (a path is a
function out of the interval; the dimension variable ranges over the interval). -/
abbrev PathSpace (Interval A : Type) : Type := Interval → A

/-- The **face map** at an interval point — evaluate a path at the point (a genuine FACE when the point is an
endpoint).  `faceAt point : PathSpace 𝕀 A → A`. -/
def faceAt {Interval A : Type} (point : Interval) (path : PathSpace Interval A) : A := path point

/-! ## Modal operators -/

/-- A **modal operator** as an endofunctor on `Type` (`Apply` + `map` + the two functor laws, pointwise). -/
structure ModalOperator where
  /-- The underlying endofunctor. -/
  Apply : Type → Type
  /-- Functorial action on maps. -/
  map : {A B : Type} → (A → B) → Apply A → Apply B
  /-- Functor law `map id = id` (pointwise). -/
  map_id : {A : Type} → (value : Apply A) → map (fun element => element) value = value
  /-- Functor law `map (g ∘ f) = map g ∘ map f` (pointwise). -/
  map_comp : {A B C : Type} → (firstMap : A → B) → (secondMap : B → C) → (value : Apply A) →
    map (fun element => secondMap (firstMap element)) value = map secondMap (map firstMap value)

/-- The **identity** modality `Id`. -/
def identityModalOperator : ModalOperator where
  Apply := fun carrier => carrier
  map := fun mapFunction value => mapFunction value
  map_id := fun _value => rfl
  map_comp := fun _firstMap _secondMap _value => rfl

/-- The **reader** modality `D → -` over a shape `Shape` (the Π / dependent-product modality over a fixed
dimension — the kind that is orthogonal to the interval). -/
def readerModalOperator (Shape : Type) : ModalOperator where
  Apply := fun carrier => Shape → carrier
  map := fun mapFunction value => fun shapePoint => mapFunction (value shapePoint)
  map_id := fun _value => rfl
  map_comp := fun _firstMap _secondMap _value => rfl

/-- The **cube / path modality** `□ = 𝕀 → -` — itself a reader modality (over the interval `𝕀`). -/
def cubeModality (Interval : Type) : ModalOperator := readerModalOperator Interval

/-! ## The orthogonality exchange -/

/-- An **orthogonality exchange** between a modality `M` and an interval `𝕀` — the natural iso
`M(𝕀 → A) ≅ (𝕀 → M A)` (`push` / `pull` mutually inverse) PLUS the FACE coherence (`push` commutes with
evaluation at an interval point).  This is the orthogonality of the cubical and modal structure: the modality
commutes with the path functor. -/
structure OrthogonalExchange (modality : ModalOperator) (Interval : Type) where
  /-- `push : M(𝕀 → A) → (𝕀 → M A)` — the modalized path is a path of modalized values. -/
  push : {A : Type} → modality.Apply (PathSpace Interval A) → PathSpace Interval (modality.Apply A)
  /-- `pull : (𝕀 → M A) → M(𝕀 → A)` — the backward direction. -/
  pull : {A : Type} → PathSpace Interval (modality.Apply A) → modality.Apply (PathSpace Interval A)
  /-- The iso, one direction. -/
  push_pull : {A : Type} → (modalizedPath : PathSpace Interval (modality.Apply A)) →
    push (pull modalizedPath) = modalizedPath
  /-- The iso, the other direction. -/
  pull_push : {A : Type} → (pathOfModal : modality.Apply (PathSpace Interval A)) →
    pull (push pathOfModal) = pathOfModal
  /-- The **FACE coherence**: the face of a pushed modal path is the modality applied to the path's face. -/
  push_faceAt : {A : Type} → (pathOfModal : modality.Apply (PathSpace Interval A)) → (point : Interval) →
    faceAt point (push pathOfModal) = modality.map (faceAt point) pathOfModal

/-- ★ The exchange is FAITHFUL — `push` is injective (from `pull_push`), a derived consequence of the
orthogonality iso (no funext). -/
theorem OrthogonalExchange.push_injective {modality : ModalOperator} {Interval : Type}
    (exchange : OrthogonalExchange modality Interval) {A : Type}
    {firstPath secondPath : modality.Apply (PathSpace Interval A)}
    (pushesEqual : exchange.push firstPath = exchange.push secondPath) : firstPath = secondPath := by
  rw [← exchange.pull_push firstPath, ← exchange.pull_push secondPath, pushesEqual]

/-! ## Witnesses -/

/-- The **identity** modality's exchange — `M = Id`, so `M(𝕀 → A) = (𝕀 → A) = (𝕀 → M A)`, the exchange the
identity (everything by `rfl`). -/
def identityExchange (Interval : Type) : OrthogonalExchange identityModalOperator Interval where
  push := fun pathOfModal => pathOfModal
  pull := fun modalizedPath => modalizedPath
  push_pull := fun _modalizedPath => rfl
  pull_push := fun _pathOfModal => rfl
  push_faceAt := fun _pathOfModal _point => rfl

/-- ★ The **reader** modality's exchange — `M A = Shape → A` commutes with the path functor by the argument
SWAP: `push (f : Shape → 𝕀 → A) = fun i s => f s i`.  The genuine NON-degenerate witness (works for any
`Shape`), both round trips and the face coherence by `rfl` (function eta).  This is the orthogonality of a Π /
reader modality and the interval. -/
def readerExchange (Shape Interval : Type) : OrthogonalExchange (readerModalOperator Shape) Interval where
  push := fun pathOfModal => fun intervalPoint shapePoint => pathOfModal shapePoint intervalPoint
  pull := fun modalizedPath => fun shapePoint intervalPoint => modalizedPath intervalPoint shapePoint
  push_pull := fun _modalizedPath => rfl
  pull_push := fun _pathOfModal => rfl
  push_faceAt := fun _pathOfModal _point => rfl

/-- ★ Two cube DIMENSIONS are orthogonal — the exchange of the cube modality `□_FirstDim = FirstDim → -` with a
`SecondDim`-path is the dimension SWAP (`cubeModality` is a reader).  The cubical-cubical orthogonality. -/
def cubeCubeExchange (FirstDim SecondDim : Type) :
    OrthogonalExchange (cubeModality FirstDim) SecondDim :=
  readerExchange FirstDim SecondDim

/-- ★ **Face coherence at the cube endpoints** — for the reader (`□`) modality over the cube interval
`𝕀 = Bool` ({0, 1}), the 0-face and the 1-face of a pushed modal path are the modality applied to the path's
faces.  The "exchange respects faces" rule, instantiated at the concrete cube endpoints. -/
theorem readerExchange_cube_faces (Shape : Type) {A : Type}
    (pathOfModal : (readerModalOperator Shape).Apply (PathSpace cubeInterval A)) :
    faceAt false ((readerExchange Shape cubeInterval).push pathOfModal)
        = (readerModalOperator Shape).map (faceAt false) pathOfModal
      ∧ faceAt true ((readerExchange Shape cubeInterval).push pathOfModal)
        = (readerModalOperator Shape).map (faceAt true) pathOfModal :=
  ⟨(readerExchange Shape cubeInterval).push_faceAt pathOfModal false,
   (readerExchange Shape cubeInterval).push_faceAt pathOfModal true⟩

/-- The cube modality's underlying endofunctor IS the path functor — `□ A = 𝕀 → A` (the tie to `PathSpace`). -/
theorem cubeModality_Apply (Interval A : Type) :
    (cubeModality Interval).Apply A = PathSpace Interval A := rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  The modal KAN operations — `hcomp` / `transp` / `coe` commuting with the modalities (the
modal Kan structure that makes the combined theory have the cubical composition) — are deferred.  `= false`. -/
def fxMode_hasModalKanOperations : Bool := false

/-- **Honesty marker.**  The full de Morgan FACE LATTICE / cube-category orthogonality (faces, degeneracies,
connections of the genuine cube category exchanging with the modalities), beyond the single interval-functor
exchange here, is deferred.  `= false`. -/
def fxMode_hasFaceLatticeOrthogonality : Bool := false

/-- **Honesty marker.**  The modal LOCK `◐_μ` exchanging with the DIMENSION context extension `(Γ, i : 𝕀)` at the
CwF / context level (the genuine `MTT□` structural exchange rule) is cross-axis (`fib`), deferred.  `= false`. -/
def fxMode_hasModalLockDimensionExchange : Bool := false

/-- **Honesty marker.**  The connection to the kernel's `gen_path` / `gen_modality` orthogonality rows is
cross-axis (`fib`), deferred.  `= false`. -/
def fxMode_hasKernelCubicalModalConnection : Bool := false

end FX1Poly.Tier0

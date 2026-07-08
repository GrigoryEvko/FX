import FX1Poly.Polygraph.Computad.Signature

/-! # Polygraph/Computad/MonadSeed — the walking-monad seed: the terminal monad presentation on one endo-1-cell

The presentation of the WALKING MONAD as a 2-computad (`ModeSignature`).  Where the walking ADJUNCTION seed
(`AdjunctionSeed`) has TWO modes and a 1-generator each way (so a `base ⟶ tip` hom carries per-atom variance
flips), the walking MONAD has ONE mode `point`, ONE endo-1-generator `t : point ⟶ point`, and TWO generating
2-cells between parallel `t`-power paths:

  * the **unit** `eta : id ⇒ t`  (arity `(0, 1)` — grows the ordinal by one),
  * the **multiplication** `mu : t·t ⇒ t`  (arity `(2, 1)` — merges two into one).

By Street ("The formal theory of monads") and Mac Lane (§VII.5), a monad in any 2-category `K` is exactly a
strict monoidal functor out of the augmented simplex category Δ₊ — the free monoidal category on a monoid object
`[1]` — so the walking monad's delooping `BΔ₊` is the terminal such presentation.  This seed is that `[1]`: one
generating object `t`, the unit/multiplication maps, with the three monad LAWS (left-unit, right-unit,
associativity) posited as saturation relations in `WalkingMonad/MonadSaturatedConv`.

Because there is ONE object and ONE variance, the covariant monotone-map fold that is REFUTED for the walking
adjunction (`covariantMonotoneMapOf_notSound`) is SOUND here — `WalkingMonad/MonadDeltaModel` re-aims exactly the
retired-for-adjunction machinery at this seed.

Generic presentation data (no mode-theory dependence), so it lives in the signature-free `Polygraph/` library.
Zero external dependencies beyond the computad signature.  Raw Lean 4 + Init. -/

namespace FX1Poly.Polygraph

/-! ## The walking-monad quiver: one object, one endo-generator -/

/-- The single mode (0-cell) of the walking monad. -/
inductive MonadMode where
  /-- The unique object. -/
  | point

/-- The single generating modality (1-cell) of the walking monad: the endo-generator `t : point ⟶ point`. -/
inductive MonadModality : MonadMode → MonadMode → Type where
  /-- The generating endo-1-cell `t`. -/
  | t : MonadModality MonadMode.point MonadMode.point

/-- The walking-monad quiver: one mode, one endo-modality. -/
def monadGraph : ModeGraph where
  Mode := MonadMode
  Modality := MonadModality

/-- The generating endo-1-cell `t` as the length-1 path. -/
def monadT : ModalityPath monadGraph MonadMode.point MonadMode.point :=
  singletonModalityPath MonadModality.t

/-- The composite 1-cell `t·t` (length 2), the source of the multiplication `mu`.  Defined as `composePath monadT
monadT` so it is DEFINITIONALLY the codomain of `t`-whiskered `t` (keeps the seed relation boundaries clean). -/
def monadTThenT : ModalityPath monadGraph MonadMode.point MonadMode.point :=
  composePath monadT monadT

/-- The composite 1-cell `t·t·t` (length 3), the common source of the two associativity composites. -/
def monadTThenTThenT : ModalityPath monadGraph MonadMode.point MonadMode.point :=
  composePath monadTThenT monadT

/-! ## The generating 2-cells: the unit and the multiplication -/

/-- The generating 2-cells of the walking monad — the unit and the multiplication, between parallel `t`-power
paths.  These are the GENERATORS only; the three monad LAWS relating them are the saturation relations
(`WalkingMonad/MonadSaturatedConv`). -/
inductive MonadTwoCell :
    {sourceMode targetMode : MonadMode} →
    ModalityPath monadGraph sourceMode targetMode →
    ModalityPath monadGraph sourceMode targetMode → Type where
  /-- The **unit** `eta : id_point ⇒ t` (arity `(0, 1)`). -/
  | eta : MonadTwoCell (ModalityPath.nil MonadMode.point) monadT
  /-- The **multiplication** `mu : t·t ⇒ t` (arity `(2, 1)`). -/
  | mu : MonadTwoCell monadTThenT monadT

/-- ★ The **walking-monad mode signature** — the terminal monad presentation: one mode `point`, one endo-1-cell
`t`, and the unit / multiplication 2-cell generators between parallel `t`-power paths.  This is the seed the
walking-monad free-2-cell tower and the Δ₊ monotone-map model are instantiated at. -/
def monadModeSignature : ModeSignature where
  graph := monadGraph
  twoCell := fun firstPath secondPath => MonadTwoCell firstPath secondPath

/-! ## Freeness smokes -/

/-- Smoke: `t` is the length-1 1-cell. -/
theorem monadT_length : monadT.length = 1 := rfl

/-- Smoke: `t·t` is the length-2 1-cell. -/
theorem monadTThenT_length : monadTThenT.length = 2 := rfl

/-- Smoke: `t·t·t` is the length-3 1-cell. -/
theorem monadTThenTThenT_length : monadTThenTThenT.length = 3 := rfl

end FX1Poly.Polygraph

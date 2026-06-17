import FX1Poly.Tier0.Mode.Mode

/-! # mode-11 — the transpension universal modality (the rightmost adjoint)

For a "multiplier" (a fresh dimension / nominal atom — `mode-2`'s structure-class datum), the substitution
functor sits in an ADJOINT CHAIN, and its RIGHTMOST adjoint is the **transpension** `Ξ` (Nuyts–Devriese,
"Transpension: the right adjoint to the Π-type", arXiv:2008.08533).  This single universal modality is the
common home of a whole zoo of type formers: the parametricity **Gel**, the cubical **Glue** / **Weld** /
**mill**, the amazing right adjoint **√**, the nominal **Φ** / **Ψ**, and the nominal fresh-name binder.
`mode-11` ships the defining adjunction `Π ⊣ Ξ` and names that zoo; the per-operator recoveries (deep) are
deferred.

## What this file ships (each piece zero-axiom)

  * **`TranspensionAdjunction`** — the adjunction `Π ⊣ Ξ` as a natural hom-set bijection: `transpose`
    (`(Π A → B) → (A → Ξ B)`) and `untranspose`, mutually inverse (`transpose_untranspose` /
    `untranspose_transpose`).  This IS "transpension is the right adjoint to the Π-type".
  * **`identityTranspension`** — the concrete witness (the trivial multiplier: `Π = Ξ = Id`, the bijection the
    identity, the laws by `rfl`).
  * **`transpose_injective`** / **`untranspose_injective`** — derived from the adjunction iso (a genuine use of
    the round-trip laws, no funext): the transposition is faithful both ways.
  * **`TranspensionRecoverable`** — the enumerated zoo the transpension is the universal home of (Gel / Glue /
    Weld / mill / √ / Φ / Ψ / nominal), with `all` + the count.

## What is DEFERRED (markers)

  * the actual per-operator RECOVERIES (each of the zoo as a concrete transpension instance)
    (`hasTranspensionZooRecovery`);
  * the FULL multiplier adjoint chain `∫ ⊣ fresh-weaken ⊣ Π ⊣ Ξ`, beyond the single `Π ⊣ Ξ` here
    (`hasFullMultiplierAdjointString`);
  * the DEPENDENT transpension (a type-family former), beyond the simple-type modeling here
    (`hasDependentTranspension`);
  * the connection to the kernel's `gen_transpension` former (`hasKernelTranspensionConnection`, cross-axis;
    the syntactic instance + gel-β is `TRANSP-1`).

This is the rightmost adjoint extending `mode-4`'s adjoint strings (`AdjointTriple`) by one more step.
Zero external dependencies beyond the mode core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## The transpension adjunction `Π ⊣ Ξ` -/

/-- A **transpension adjunction** — the dimension Π-type (`DimProduct`, the left adjoint) together with its
RIGHT adjoint the transpension (`Transpension`, `Ξ`), presented by the natural hom-set bijection
`transpose : (Π A → B) ≃ (A → Ξ B)`.  This is the defining datum of the transpension as "the right adjoint to
the Π-type" (modeled on simple types; the dependent former is deferred). -/
structure TranspensionAdjunction where
  /-- The Π-type over the dimension (the left adjoint). -/
  DimProduct : Type → Type
  /-- The transpension `Ξ` (the right adjoint). -/
  Transpension : Type → Type
  /-- The forward transposition `(Π A → B) → (A → Ξ B)`. -/
  transpose : {A B : Type} → (DimProduct A → B) → (A → Transpension B)
  /-- The backward transposition `(A → Ξ B) → (Π A → B)`. -/
  untranspose : {A B : Type} → (A → Transpension B) → (DimProduct A → B)
  /-- The bijection, one direction. -/
  transpose_untranspose : {A B : Type} → (rightMorphism : A → Transpension B) →
    transpose (untranspose rightMorphism) = rightMorphism
  /-- The bijection, the other direction. -/
  untranspose_transpose : {A B : Type} → (leftMorphism : DimProduct A → B) →
    untranspose (transpose leftMorphism) = leftMorphism

/-- The **trivial multiplier**'s transpension — `Π = Ξ = Id`, the transposition the identity, the bijection laws
by `rfl`.  The concrete witness that the transpension adjunction is satisfiable.

RIGOR NOTE (why this is the ONLY non-presheaf witness, not laziness): the genuine transpension `Ξ` is the right
adjoint of the reader `Π = (D → -)`, and for a dimension `D` with ≥ 2 points the reader does NOT preserve
colimits (`D → (A ⊕ B) ≇ (D → A) ⊕ (D → B)`), so it has NO right adjoint among `Type`-endofunctors — `Ξ` exists
only in the PRESHEAF setting (`fxMode_hasPresheafMultiplierModel`-adjacent, deferred).  The identity here is the
DEGENERATE `D = point` transpension; the non-degenerate `(- × D) ⊣ (D → -)` adjunction is the `weakening ⊣ Π`
step (the LEFT neighbour in the chain, `fxMode_hasFullMultiplierAdjointString`), NOT a transpension. -/
def identityTranspension : TranspensionAdjunction where
  DimProduct := fun carrier => carrier
  Transpension := fun carrier => carrier
  transpose := fun morphism => morphism
  untranspose := fun morphism => morphism
  transpose_untranspose := fun _rightMorphism => rfl
  untranspose_transpose := fun _leftMorphism => rfl

/-- ★ The forward transposition is FAITHFUL — derived from the adjunction iso (`untranspose_transpose`), no
function extensionality. -/
theorem TranspensionAdjunction.transpose_injective (adjunction : TranspensionAdjunction) {A B : Type}
    {firstMorphism secondMorphism : adjunction.DimProduct A → B}
    (transposesEqual : adjunction.transpose firstMorphism = adjunction.transpose secondMorphism) :
    firstMorphism = secondMorphism := by
  rw [← adjunction.untranspose_transpose firstMorphism,
      ← adjunction.untranspose_transpose secondMorphism, transposesEqual]

/-- ★ The backward transposition is FAITHFUL — derived from the adjunction iso (`transpose_untranspose`). -/
theorem TranspensionAdjunction.untranspose_injective (adjunction : TranspensionAdjunction) {A B : Type}
    {firstMorphism secondMorphism : A → adjunction.Transpension B}
    (untransposesEqual : adjunction.untranspose firstMorphism = adjunction.untranspose secondMorphism) :
    firstMorphism = secondMorphism := by
  rw [← adjunction.transpose_untranspose firstMorphism,
      ← adjunction.transpose_untranspose secondMorphism, untransposesEqual]

/-- ★ The forward transposition is SURJECTIVE — every `A → Ξ B` is `transpose` of its untranspose.  With
`transpose_injective`, `transpose` is a BIJECTION: the full adjunction hom-iso, not just a faithful map. -/
theorem TranspensionAdjunction.transpose_surjective (adjunction : TranspensionAdjunction) {A B : Type}
    (rightMorphism : A → adjunction.Transpension B) :
    ∃ leftMorphism : adjunction.DimProduct A → B, adjunction.transpose leftMorphism = rightMorphism :=
  ⟨adjunction.untranspose rightMorphism, adjunction.transpose_untranspose rightMorphism⟩

/-- ★ The backward transposition is SURJECTIVE — dually `untranspose` is a bijection too. -/
theorem TranspensionAdjunction.untranspose_surjective (adjunction : TranspensionAdjunction) {A B : Type}
    (leftMorphism : adjunction.DimProduct A → B) :
    ∃ rightMorphism : A → adjunction.Transpension B, adjunction.untranspose rightMorphism = leftMorphism :=
  ⟨adjunction.transpose leftMorphism, adjunction.untranspose_transpose leftMorphism⟩

/-! ## The zoo the transpension is the universal home of -/

/-- The type formers RECOVERED as instances of the transpension (each from a particular multiplier /
configuration): the parametricity **Gel**, the cubical **Glue** / **Weld** / **mill**, the amazing right
adjoint **√**, the nominal **Φ** / **Ψ**, and the nominal fresh-name binder.  This file names the targets; the
per-operator recoveries are deferred (`fxMode_hasTranspensionZooRecovery`). -/
inductive TranspensionRecoverable
  /-- The parametricity Gel type. -/
  | gel
  /-- The cubical Glue type. -/
  | glue
  /-- The cubical Weld type. -/
  | weld
  /-- The mill type. -/
  | mill
  /-- The amazing right adjoint √. -/
  | amazingRightAdjoint
  /-- The nominal Φ operator. -/
  | phi
  /-- The nominal Ψ operator. -/
  | psi
  /-- The nominal fresh-name binder. -/
  | nominal
  deriving DecidableEq

/-- The full enumeration of the transpension-recovered zoo. -/
def TranspensionRecoverable.all : List TranspensionRecoverable :=
  [.gel, .glue, .weld, .mill, .amazingRightAdjoint, .phi, .psi, .nominal]

/-- The transpension is the universal home of EIGHT named operators. -/
theorem TranspensionRecoverable.all_length : TranspensionRecoverable.all.length = 8 := rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  The actual per-operator RECOVERIES — each of `TranspensionRecoverable` (Gel / Glue /
Weld / mill / √ / Φ / Ψ / nominal) constructed as a concrete transpension instance — are deferred; this file
ships the adjunction + the named targets.  `= false`. -/
def fxMode_hasTranspensionZooRecovery : Bool := false

/-- **Honesty marker.**  The FULL multiplier adjoint chain `∫ ⊣ fresh-weaken ⊣ Π ⊣ Ξ` (Nuyts–Devriese), beyond
the single `Π ⊣ Ξ` adjunction shipped here, is deferred.  `= false`. -/
def fxMode_hasFullMultiplierAdjointString : Bool := false

/-- **Honesty marker.**  The DEPENDENT transpension (a type-FAMILY former with the dependent gel-β), beyond the
simple-type modeling here, is deferred.  `= false`. -/
def fxMode_hasDependentTranspension : Bool := false

/-- **Honesty marker.**  The connection to the kernel's `gen_transpension` former (the syntactic instance +
gel-β iota row — `TRANSP-1`) is cross-axis (`fib`), deferred.  `= false`. -/
def fxMode_hasKernelTranspensionConnection : Bool := false

end FX1Poly.Tier0

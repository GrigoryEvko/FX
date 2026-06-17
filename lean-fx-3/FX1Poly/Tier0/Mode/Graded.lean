import FX1Poly.Tier0.Mode.GradeAlgebra.ResourceGraded
import FX1Poly.Tier0.Mode.Linear

/-! # mode-26 — graded / coeffect modalities: the graded exponential `!_r` + the alongside-vs-beneath boundary

The GRADED exponential `!_r` (the coeffect modality) as a mode-polygraph instance, built DIRECTLY over the shipped
DIM-2 usage grade semiring (`FX1Poly.Modal.UsageGrade` `{0, 1, ω}`, §6.1 — the verified
`IsLawfulOrderedGradeSemiring fxUsageSemiring`).  This is the mode axis cohering with the resource dimension: the
modality is indexed by a grade, and the grade arithmetic IS the coeffect bookkeeping.

This file adds NO new grade algebra — it reuses `UsageGrade` / `UsageGrade.add` / `UsageGrade.mul` / `UsageGrade.le`
and CITES the shipped distributivity (`UsageGrade.left_distrib`) for the soundness crux.  The new content is the
graded `!_r` comonad and the alongside/beneath operations on top of it.

## The alongside-vs-beneath boundary (the soundness crux)

A graded modality has TWO ways grades compose, and getting their interaction right is the soundness crux:

  * **beneath** (the `*`, nesting / sequential use): `comult : !_{r*s} A → !_r (!_s A)` — when a graded value is used
    UNDER another graded modality, the grades MULTIPLY.  This is the graded comonad comultiplication; the
    co-Kleisli composition `gradedCompose` accumulates the coeffect by `*`.
  * **alongside** (the `+`, splitting / parallel use): `split : !_{r+s} A → !_r A ⊗ !_s A` — when a graded value is
    used ALONGSIDE itself, the grades ADD (the graded contraction).  The output is a linear `Tensor` (mode-22's
    multiplicative conjunction — the axes compose).

The two are linked by **distributivity**: `r * (s + t) = (r * s) + (r * t)` — scaling (beneath) distributes over
splitting (alongside).  This is exactly `UsageGrade.left_distrib`, a PROVEN law of the shipped lawful semiring; it
is the equation that makes nested graded coeffects sound, and `beneathDistributesOverAlongside` re-exposes it under
the modality reading.

## What this file ships (each piece zero-axiom)

  * **`GradedExponential`** — the graded `!_r` comonad over `UsageGrade`: a grade-indexed functor with dereliction
    `counit` (ONLY at grade `1`), digging `comult` (grades multiply), the alongside `split` (grades add → `Tensor`),
    `discard` (grade `0` carries no usage), and bounded `subsume` (`r ≤ s ⟹ !_s A → !_r A`, GATED by the order
    proof — the genuine bounded-coeffect weakening).  Witnesses: ★ `storeGradedExponential` (`!_r A = Resource × A`,
    the store comonad with the grade as a tracked coeffect index — every law by `rfl`) and `identityGradedExponential`.
  * **`gradedCompose`** — the beneath co-Kleisli composition whose result grade is the PRODUCT `r * s` (the coeffect
    accumulation) + `gradedCompose_eval` (the resource threads through).
  * **`beneathDistributesOverAlongside`** — ★ the alongside-vs-beneath crux, citing the shipped `UsageGrade.left_distrib`.
  * the witness laws (all `rfl`): `counit_comult` (graded dereliction-after-digging), `split_leftFactor` /
    `split_rightFactor` (alongside duplicates faithfully), `discard_unit` (grade-0 weakening), `subsume_refl`
    (subsuming along reflexivity is the identity).

## What is DEFERRED (markers)

  * the grade-SENSITIVE action `!_n A = n copies` (a `Fin n → A` / vector model where the carrier genuinely depends
    on the grade VALUE, so `!_0` is empty and `!_2` is a pair) — here the action is uniform (`hasGradeSensitiveAction`);
  * the modality-level alongside/beneath interchange — `split`/`comult` transported through the `left_distrib` TYPE
    cast `Bang (r*(s+t)) ≅ Bang ((r*s)+(r*t))` (`hasGradedDistributiveCoherence`);
  * the full graded comonad as a lax monoidal functor + the graded Seely coherence (`hasGradedLaxMonoidal`);
  * subsumption as a genuine 2-cell (the functoriality `subsume (le_trans p q) = subsume p ∘ subsume q` + naturality)
    (`hasSubsumptionTwoCell`);
  * the kernel `gen_gradedModality` / `HasGradeOver` formers fibred into the mode doctrine (cross-axis, `fib`)
    (`hasKernelGradedFibration`).

Reuses the shipped DIM-2 grade algebra + mode-22's `Tensor`.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

open FX1Poly.Modal

/-! ## The graded `!_r` exponential comonad -/

/-- The **graded exponential** `!_r` (the coeffect modality) over the usage grade semiring `{0, 1, ω}`: a
grade-indexed functor `Bang` with dereliction `counit` at grade `1`, digging `comult` (grades MULTIPLY — the
beneath/sequential composition), the alongside `split` (grades ADD — the parallel/contraction split, into mode-22's
`Tensor`), `discard` at grade `0` (the unused value carries no obligation), and bounded `subsume` (`r ≤ s ⟹ !_s A →
!_r A`, gated by the order — the genuine bounded-coeffect weakening).  All laws are pointwise, so the structure is
`funext`-free. -/
structure GradedExponential where
  /-- The grade-indexed `!_r` functor. -/
  Bang : UsageGrade → Type → Type
  /-- The functorial action (uniform in the grade). -/
  map : {grade : UsageGrade} → {A B : Type} → (A → B) → Bang grade A → Bang grade B
  /-- Dereliction `ε : !_1 A → A` — extraction is licensed ONLY at grade `1`. -/
  counit : {A : Type} → Bang UsageGrade.one A → A
  /-- Digging `δ : !_{r*s} A → !_r (!_s A)` — nesting multiplies grades (BENEATH). -/
  comult : {leftGrade rightGrade : UsageGrade} → {A : Type} →
    Bang (UsageGrade.mul leftGrade rightGrade) A → Bang leftGrade (Bang rightGrade A)
  /-- Splitting `!_{r+s} A → !_r A ⊗ !_s A` — parallel use adds grades (ALONGSIDE). -/
  split : {leftGrade rightGrade : UsageGrade} → {A : Type} →
    Bang (UsageGrade.add leftGrade rightGrade) A → Tensor (Bang leftGrade A) (Bang rightGrade A)
  /-- Discard `!_0 A → ⊤` — a grade-`0` value carries no usage obligation (weakening). -/
  discard : {A : Type} → Bang UsageGrade.zero A → Unit
  /-- Bounded subsumption `r ≤ s ⟹ !_s A → !_r A` — the order licenses weakening the grade. -/
  subsume : {smallGrade largeGrade : UsageGrade} → {A : Type} →
    UsageGrade.le smallGrade largeGrade = true → Bang largeGrade A → Bang smallGrade A
  /-- `map` preserves identities. -/
  map_id : {grade : UsageGrade} → {A : Type} → (boxed : Bang grade A) →
    map (fun element => element) boxed = boxed
  /-- `ε` is natural (at grade `1`). -/
  counit_natural : {A B : Type} → (morphism : A → B) → (boxed : Bang UsageGrade.one A) →
    counit (map morphism boxed) = morphism (counit boxed)

/-- ★ The **store graded exponential** `!_r A = Resource × A` — the store comonad with the grade carried as a
tracked COEFFECT INDEX (the action is uniform in the grade; the grade does the bookkeeping in the type).  Digging
duplicates the resource, splitting duplicates the value, discard forgets, subsumption is the identity carrier-side.
Every law holds by `rfl`. -/
def storeGradedExponential (Resource : Type) : GradedExponential where
  Bang := fun _grade carrier => Resource × carrier
  map := fun morphism boxed => (boxed.1, morphism boxed.2)
  counit := fun boxed => boxed.2
  comult := fun boxed => (boxed.1, boxed)
  split := fun boxed => ⟨boxed, boxed⟩
  discard := fun _ => ()
  subsume := fun _belowProof boxed => boxed
  map_id := fun _ => rfl
  counit_natural := fun _ _ => rfl

/-- The trivial graded exponential `!_r A = A` (the cartesian collapse — every grade acts as the identity). -/
def identityGradedExponential : GradedExponential where
  Bang := fun _grade carrier => carrier
  map := fun morphism => morphism
  counit := fun boxed => boxed
  comult := fun boxed => boxed
  split := fun boxed => ⟨boxed, boxed⟩
  discard := fun _ => ()
  subsume := fun _belowProof boxed => boxed
  map_id := fun _ => rfl
  counit_natural := fun _ _ => rfl

/-! ## The beneath co-Kleisli composition (coeffect accumulation by `*`) -/

/-- The **graded co-Kleisli composition** (beneath) — compose `!_s A → B` then `!_r B → C`; the composite consumes
`!_{r*s} A`, so the coeffect ACCUMULATES by multiplication (the grade of the whole is the product of the parts). -/
def GradedExponential.gradedCompose (exponential : GradedExponential)
    {outerGrade innerGrade : UsageGrade} {A B C : Type}
    (secondMap : exponential.Bang outerGrade B → C) (firstMap : exponential.Bang innerGrade A → B) :
    exponential.Bang (UsageGrade.mul outerGrade innerGrade) A → C :=
  fun boxed => secondMap (exponential.map firstMap (exponential.comult boxed))

/-! ## The alongside-vs-beneath soundness crux -/

/-- ★ The **alongside-vs-beneath crux**: scaling (beneath, `*`) DISTRIBUTES over splitting (alongside, `+`) —
`r * (s + t) = (r * s) + (r * t)`.  This is the equation that makes nested graded coeffects sound (a grade-`r`-scaled
value used alongside at `s + t` agrees with the split of its scalings).  Re-exposed from the SHIPPED lawful-semiring
law `UsageGrade.left_distrib` — no new proof, the mode modality grounding in the verified DIM-2 distributivity. -/
theorem beneathDistributesOverAlongside (scaleGrade firstGrade secondGrade : UsageGrade) :
    UsageGrade.mul scaleGrade (UsageGrade.add firstGrade secondGrade)
      = UsageGrade.add (UsageGrade.mul scaleGrade firstGrade) (UsageGrade.mul scaleGrade secondGrade) :=
  UsageGrade.left_distrib scaleGrade firstGrade secondGrade

/-! ## Witness laws (store graded exponential) -/

/-- Graded dereliction-after-digging `ε ∘ δ = id` at outer grade `1` (`δ : !_{1*s} → !_1 !_s`, then `ε`). -/
theorem storeGradedExponential_counit_comult (Resource : Type) {rightGrade : UsageGrade} {A : Type}
    (boxed : (storeGradedExponential Resource).Bang (UsageGrade.mul UsageGrade.one rightGrade) A) :
    (storeGradedExponential Resource).counit ((storeGradedExponential Resource).comult boxed) = boxed := rfl

/-- The alongside split duplicates the value into the left factor faithfully. -/
theorem storeGradedExponential_split_leftFactor (Resource : Type) {leftGrade rightGrade : UsageGrade} {A : Type}
    (boxed : (storeGradedExponential Resource).Bang (UsageGrade.add leftGrade rightGrade) A) :
    ((storeGradedExponential Resource).split boxed).leftFactor = boxed := rfl

/-- The alongside split duplicates the value into the right factor faithfully. -/
theorem storeGradedExponential_split_rightFactor (Resource : Type) {leftGrade rightGrade : UsageGrade} {A : Type}
    (boxed : (storeGradedExponential Resource).Bang (UsageGrade.add leftGrade rightGrade) A) :
    ((storeGradedExponential Resource).split boxed).rightFactor = boxed := rfl

/-- A grade-`0` value discards to the unit (weakening). -/
theorem storeGradedExponential_discard_unit (Resource : Type) {A : Type}
    (boxed : (storeGradedExponential Resource).Bang UsageGrade.zero A) :
    (storeGradedExponential Resource).discard boxed = () := rfl

/-- Subsuming along reflexivity (`r ≤ r`) is the identity. -/
theorem storeGradedExponential_subsume_refl (Resource : Type) {someGrade : UsageGrade} {A : Type}
    (boxed : (storeGradedExponential Resource).Bang someGrade A) :
    (storeGradedExponential Resource).subsume (UsageGrade.le_refl someGrade) boxed = boxed := rfl

/-- The beneath composition threads the resource and applies the maps in order — the coeffect-`*` evaluation. -/
theorem storeGradedExponential_gradedCompose_eval (Resource : Type) {outerGrade innerGrade : UsageGrade}
    {A B C : Type} (secondMap : (storeGradedExponential Resource).Bang outerGrade B → C)
    (firstMap : (storeGradedExponential Resource).Bang innerGrade A → B)
    (boxed : (storeGradedExponential Resource).Bang (UsageGrade.mul outerGrade innerGrade) A) :
    (storeGradedExponential Resource).gradedCompose secondMap firstMap boxed
      = secondMap (boxed.1, firstMap boxed) := rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  The grade-SENSITIVE action `!_n A = n copies` (a `Fin n → A` / vector model where the
carrier genuinely depends on the grade VALUE — `!_0` empty, `!_2` a pair) is deferred; here the action is uniform.
`= false`. -/
def fxMode_hasGradeSensitiveAction : Bool := false

/-- **Honesty marker.**  The modality-level alongside/beneath interchange — `split` / `comult` transported through
the `left_distrib` TYPE cast `Bang (r*(s+t)) ≅ Bang ((r*s)+(r*t))` — is deferred (the grade-level crux
`beneathDistributesOverAlongside` IS shipped).  `= false`. -/
def fxMode_hasGradedDistributiveCoherence : Bool := false

/-- **Honesty marker.**  The full graded comonad as a LAX MONOIDAL functor + the graded Seely coherence is deferred.
`= false`. -/
def fxMode_hasGradedLaxMonoidal : Bool := false

/-- **Honesty marker.**  Subsumption as a genuine 2-cell — the functoriality `subsume (le_trans p q) = subsume p ∘
subsume q` + naturality — is deferred (the operation + reflexivity law ARE shipped).  `= false`. -/
def fxMode_hasSubsumptionTwoCell : Bool := false

/-- **Honesty marker.**  The kernel `gen_gradedModality` / `HasGradeOver` formers fibred into the mode doctrine
(cross-axis, `fib`) is deferred.  `= false`. -/
def fxMode_hasKernelGradedFibration : Bool := false

end FX1Poly.Tier0

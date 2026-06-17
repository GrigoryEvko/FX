import FX1Poly.Tier0.Mode.Mode

/-! # mode-22 ★ — linear / BI exponential modalities: the `!` and the bunched structure

The linear-logic modalities as a mode-polygraph instance.  The headline is the EXPONENTIAL `!` (of-course) as a
COMONAD — the modality mediating the linear ⊣ intuitionistic adjunction (`! = R ∘ L`), the modal home of FX's
linear / separation dimensions (fx_design §6.4).  The dual `?` (why-not), the full Seely coherence, and the
bunched / separation-PCM structure are scoped to markers.

## What this file ships (each piece zero-axiom)

  * **`LinearExponential`** — the `!` comonad: a functor `Bang` with dereliction `counit : !A → A`, digging
    `comult : !A → !!A`, and the six comonad laws, all POINTWISE (funext-free).  Witnesses: ★ `storeExponential`
    (`!A = Resource × A`, the genuine NON-degenerate store/contraction comonad — every law by `rfl`) and
    `identityExponential` (the base).
  * **`coKleisliExtend`** + `coKleisliExtend_extract` + `extract_coKleisliExtend` — the co-Kleisli (linear →
    intuitionistic) extension structure with its two unit laws (the of-course promotion / dereliction).
  * the linear connectives — **`Tensor`** (⊗, multiplicative), **`With`** (&, additive), **`LinearArrow`** (⊸):
    `Tensor.swap` / `swap_swap` (⊗ symmetric), ★ `tensorCurry` / `tensorUncurry` + the round trips (the closed
    ⊗⊸ tensor-hom adjunction `(A⊗B) ⊸ C ≅ A ⊸ (B ⊸ C)`, by `rfl`), and `With.diagonal` + the projection laws
    (& is CARTESIAN: it has the diagonal / contraction — the additive vs multiplicative split).
  * **`seelyIsoIdentity`** — the Seely iso `!(A & B) ≅ !A ⊗ !B` for the identity exponential (where it holds by
    `rfl`; the store comonad provably fails it, so the general Seely is a marker).

## What is DEFERRED (markers)

  * the general Seely monoidal-natural iso `!(A & B) ≅ !A ⊗ !B` for a NON-trivial comonad (here only the identity
    witness) (`hasSeelyCoherence`);
  * the `?` why-not modality (the de Morgan dual `? = ¬!¬`, a monad) + the full linear-logic involution
    (`hasWhyNotDuality`);
  * the O'Hearn-Pym BUNCHED context management (additive `,` / multiplicative `;` bunch trees) + the
    separation-logic permission PCM (fx_design §6.4) (`hasBunchedContextManagement`);
  * linearity ENFORCEMENT — Lean is cartesian, so "no weakening / contraction except on `!`" is not kernel-checked
    here (⊗ and & are both pairs at the type level) (`hasLinearityEnforcement`);
  * the kernel's `gen_tensorProduct` / `linearArrow` / `bangModality` / `whyNotModality` formers fibred into the
    mode doctrine (cross-axis, `fib`) (`hasKernelLinearConnection`).

Zero external dependencies beyond the mode core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## Type isomorphisms -/

/-- A **type isomorphism** — forward and backward maps with both round trips (used for the Seely iso). -/
structure LinearIso (First Second : Type) where
  /-- The forward map. -/
  forward : First → Second
  /-- The backward map. -/
  backward : Second → First
  /-- `forward ∘ backward = id`. -/
  forward_backward : (point : Second) → forward (backward point) = point
  /-- `backward ∘ forward = id`. -/
  backward_forward : (point : First) → backward (forward point) = point

/-! ## The `!` exponential as a comonad -/

/-- The **`!` exponential** (of-course) as a COMONAD: a functor `Bang` with dereliction `counit` (`!A → A`),
digging `comult` (`!A → !!A`), and the six comonad laws.  All laws are pointwise, so the structure is
`funext`-free.  This is the modality that re-admits the structural rules (weakening / contraction) in linear
logic. -/
structure LinearExponential where
  /-- The `!` functor. -/
  Bang : Type → Type
  /-- The functorial action. -/
  map : {A B : Type} → (A → B) → Bang A → Bang B
  /-- Dereliction `ε : !A → A`. -/
  counit : {A : Type} → Bang A → A
  /-- Digging `δ : !A → !!A`. -/
  comult : {A : Type} → Bang A → Bang (Bang A)
  /-- `map` preserves identities. -/
  map_id : {A : Type} → (boxed : Bang A) → map (fun element => element) boxed = boxed
  /-- `ε` is natural. -/
  counit_natural : {A B : Type} → (morphism : A → B) → (boxed : Bang A) →
    counit (map morphism boxed) = morphism (counit boxed)
  /-- `δ` is natural. -/
  comult_natural : {A B : Type} → (morphism : A → B) → (boxed : Bang A) →
    comult (map morphism boxed) = map (map morphism) (comult boxed)
  /-- Left counit law `ε ∘ δ = id`. -/
  counit_comult : {A : Type} → (boxed : Bang A) → counit (comult boxed) = boxed
  /-- Right counit law `!ε ∘ δ = id`. -/
  map_counit_comult : {A : Type} → (boxed : Bang A) → map counit (comult boxed) = boxed
  /-- Coassociativity `δ ∘ δ = !δ ∘ δ`. -/
  comult_comult : {A : Type} → (boxed : Bang A) → comult (comult boxed) = map comult (comult boxed)

/-- ★ The **store exponential** `!A = Resource × A` — the genuine non-degenerate `!` comonad: digging DUPLICATES
the resource (`δ ⟨r, a⟩ = ⟨r, ⟨r, a⟩⟩`), the structure behind contraction.  Every comonad law holds by `rfl`
(Prod structure eta). -/
def storeExponential (Resource : Type) : LinearExponential where
  Bang := fun carrier => Resource × carrier
  map := fun morphism boxed => (boxed.1, morphism boxed.2)
  counit := fun boxed => boxed.2
  comult := fun boxed => (boxed.1, boxed)
  map_id := fun _ => rfl
  counit_natural := fun _ _ => rfl
  comult_natural := fun _ _ => rfl
  counit_comult := fun _ => rfl
  map_counit_comult := fun _ => rfl
  comult_comult := fun _ => rfl

/-- The trivial exponential `!A = A` — the base (the cartesian collapse). -/
def identityExponential : LinearExponential where
  Bang := fun carrier => carrier
  map := fun morphism => morphism
  counit := fun boxed => boxed
  comult := fun boxed => boxed
  map_id := fun _ => rfl
  counit_natural := fun _ _ => rfl
  comult_natural := fun _ _ => rfl
  counit_comult := fun _ => rfl
  map_counit_comult := fun _ => rfl
  comult_comult := fun _ => rfl

/-! ## The co-Kleisli (linear → intuitionistic) structure -/

/-- The **co-Kleisli extension** — promote a co-Kleisli map `!A → B` to `!A → !B` (`δ` then `!f`).  The co-Kleisli
category of `!` is the intuitionistic category sitting over the linear base. -/
def LinearExponential.coKleisliExtend (exponential : LinearExponential) {A B : Type}
    (coKleisliMap : exponential.Bang A → B) (boxed : exponential.Bang A) : exponential.Bang B :=
  exponential.map coKleisliMap (exponential.comult boxed)

/-- Extending dereliction is the identity (the co-Kleisli right unit). -/
theorem LinearExponential.coKleisliExtend_extract (exponential : LinearExponential) {A : Type}
    (boxed : exponential.Bang A) : exponential.coKleisliExtend exponential.counit boxed = boxed :=
  exponential.map_counit_comult boxed

/-- ★ Dereliction after extension recovers the map (the co-Kleisli left unit) — `ε ∘ extend f = f` pointwise. -/
theorem LinearExponential.extract_coKleisliExtend (exponential : LinearExponential) {A B : Type}
    (coKleisliMap : exponential.Bang A → B) (boxed : exponential.Bang A) :
    exponential.counit (exponential.coKleisliExtend coKleisliMap boxed) = coKleisliMap boxed := by
  show exponential.counit (exponential.map coKleisliMap (exponential.comult boxed)) = coKleisliMap boxed
  rw [exponential.counit_natural, exponential.counit_comult]

/-! ## The linear connectives ⊗ / ⊸ / & -/

/-- **Multiplicative conjunction** `⊗` (tensor) — the linear product (no projections in the linear discipline). -/
structure Tensor (Left Right : Type) where
  /-- The left factor. -/
  leftFactor : Left
  /-- The right factor. -/
  rightFactor : Right

/-- `⊗` is symmetric — the monoidal swap. -/
def Tensor.swap {Left Right : Type} (tensor : Tensor Left Right) : Tensor Right Left :=
  ⟨tensor.rightFactor, tensor.leftFactor⟩

/-- The swap is involutive (`⊗` is a SYMMETRIC monoidal product). -/
theorem Tensor.swap_swap {Left Right : Type} (tensor : Tensor Left Right) : tensor.swap.swap = tensor := rfl

/-- **Linear implication** `⊸` (lollipop) — a function consuming its argument exactly once. -/
def LinearArrow (Source Target : Type) : Type := Source → Target

/-- Curry a tensor-consuming map to a curried linear map (`(A ⊗ B) ⊸ C → A ⊸ (B ⊸ C)`). -/
def tensorCurry {A B C : Type} (uncurried : Tensor A B → C) : A → B → C :=
  fun left right => uncurried ⟨left, right⟩

/-- Uncurry a curried linear map to a tensor-consuming map. -/
def tensorUncurry {A B C : Type} (curried : A → B → C) : Tensor A B → C :=
  fun tensor => curried tensor.leftFactor tensor.rightFactor

/-- ★ The closed **⊗⊸ adjunction** `(A ⊗ B) ⊸ C ≅ A ⊸ (B ⊸ C)` — the tensor-hom adjunction, one round trip by
`rfl`. -/
theorem tensorCurry_uncurry {A B C : Type} (curried : A → B → C) :
    tensorCurry (tensorUncurry curried) = curried := rfl

/-- The other round trip of the ⊗⊸ adjunction. -/
theorem tensorUncurry_curry {A B C : Type} (uncurried : Tensor A B → C) :
    tensorUncurry (tensorCurry uncurried) = uncurried := rfl

/-- **Additive conjunction** `&` (with) — the CARTESIAN product: it has projections AND a diagonal (so it admits
weakening and contraction), unlike `⊗`. -/
structure With (Left Right : Type) where
  /-- The left component. -/
  leftComponent : Left
  /-- The right component. -/
  rightComponent : Right

/-- The diagonal `A → A & A` — the CONTRACTION available to the additive `&` (but not to `⊗`). -/
def With.diagonal {A : Type} (value : A) : With A A := ⟨value, value⟩

/-- Contraction then left projection is the identity (`&` is cartesian). -/
theorem With.diagonal_leftComponent {A : Type} (value : A) : (With.diagonal value).leftComponent = value := rfl

/-- Contraction then right projection is the identity. -/
theorem With.diagonal_rightComponent {A : Type} (value : A) : (With.diagonal value).rightComponent = value := rfl

/-! ## The Seely isomorphism (for the identity exponential) -/

/-- ★ The **Seely isomorphism** `!(A & B) ≅ !A ⊗ !B` for the identity exponential — `!` sends the additive `&` to
the multiplicative `⊗`.  Holds by `rfl` at the cartesian collapse; the general Seely (for a non-trivial `!`) is a
marker. -/
def seelyIsoIdentity (A B : Type) :
    LinearIso (identityExponential.Bang (With A B))
      (Tensor (identityExponential.Bang A) (identityExponential.Bang B)) where
  forward := fun boxed => ⟨boxed.leftComponent, boxed.rightComponent⟩
  backward := fun tensor => ⟨tensor.leftFactor, tensor.rightFactor⟩
  forward_backward := fun _ => rfl
  backward_forward := fun _ => rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  The general Seely monoidal-natural iso `!(A & B) ≅ !A ⊗ !B` for a NON-trivial comonad
(beyond the identity-exponential witness — the store comonad provably fails it) is deferred.  `= false`. -/
def fxMode_hasSeelyCoherence : Bool := false

/-- **Honesty marker.**  The `?` why-not modality (the de Morgan dual `? = ¬!¬`, a monad) + the full linear-logic
involution is deferred.  `= false`. -/
def fxMode_hasWhyNotDuality : Bool := false

/-- **Honesty marker.**  The O'Hearn-Pym BUNCHED context management (additive `,` / multiplicative `;` bunch trees)
+ the separation-logic permission PCM (fx_design §6.4) is deferred.  `= false`. -/
def fxMode_hasBunchedContextManagement : Bool := false

/-- **Honesty marker.**  Linearity ENFORCEMENT — Lean is cartesian, so "no weakening / contraction except on `!`"
is not kernel-checked here (`⊗` and `&` are both pairs at the type level).  `= false`. -/
def fxMode_hasLinearityEnforcement : Bool := false

/-- **Honesty marker.**  The kernel's `gen_tensorProduct` / `linearArrow` / `bangModality` / `whyNotModality`
formers (LL 5.5) fibred into the mode doctrine (cross-axis, `fib`) is deferred.  `= false`. -/
def fxMode_hasKernelLinearConnection : Bool := false

end FX1Poly.Tier0

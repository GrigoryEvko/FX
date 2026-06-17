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

/-! ## The `?` why-not modality as a monad (discharges hasWhyNotDuality) -/

/-- The **`?` why-not modality** as a MONAD — the categorical DUAL of the `!` comonad: a functor `WhyNot` with
return `unit : A → ?A` (dual to dereliction), join `mult : ??A → ?A` (dual to digging), and the six monad laws
(the same shapes as the comonad laws, with the arrows reversed). -/
structure WhyNotModality where
  /-- The `?` functor. -/
  WhyNot : Type → Type
  /-- The functorial action. -/
  map : {A B : Type} → (A → B) → WhyNot A → WhyNot B
  /-- Return `η : A → ?A`. -/
  unit : {A : Type} → A → WhyNot A
  /-- Join `μ : ??A → ?A`. -/
  mult : {A : Type} → WhyNot (WhyNot A) → WhyNot A
  /-- `map` preserves identities. -/
  map_id : {A : Type} → (boxed : WhyNot A) → map (fun element => element) boxed = boxed
  /-- `η` is natural. -/
  unit_natural : {A B : Type} → (morphism : A → B) → (value : A) →
    map morphism (unit value) = unit (morphism value)
  /-- `μ` is natural. -/
  mult_natural : {A B : Type} → (morphism : A → B) → (nested : WhyNot (WhyNot A)) →
    map morphism (mult nested) = mult (map (map morphism) nested)
  /-- Left unit law `μ ∘ η = id`. -/
  unit_mult : {A : Type} → (boxed : WhyNot A) → mult (unit boxed) = boxed
  /-- Right unit law `μ ∘ ?η = id`. -/
  map_unit_mult : {A : Type} → (boxed : WhyNot A) → mult (map unit boxed) = boxed
  /-- Associativity `μ ∘ μ = μ ∘ ?μ`. -/
  mult_mult : {A : Type} → (nested : WhyNot (WhyNot (WhyNot A))) →
    mult (mult nested) = mult (map mult nested)

/-- ★ The **reader why-not** `?A = Resource → A` — the canonical `?` MONAD dual to the store `!` comonad: join
DIAGONALIZES the resource (`μ f = fun r => f r r`).  Every monad law holds by `rfl` (function eta). -/
def readerWhyNot (Resource : Type) : WhyNotModality where
  WhyNot := fun carrier => Resource → carrier
  map := fun morphism reader => fun resource => morphism (reader resource)
  unit := fun value => fun _ => value
  mult := fun nested => fun resource => nested resource resource
  map_id := fun _ => rfl
  unit_natural := fun _ _ => rfl
  mult_natural := fun _ _ => rfl
  unit_mult := fun _ => rfl
  map_unit_mult := fun _ => rfl
  mult_mult := fun _ => rfl

/-- The trivial why-not `?A = A` — the base. -/
def identityWhyNot : WhyNotModality where
  WhyNot := fun carrier => carrier
  map := fun morphism => morphism
  unit := fun value => value
  mult := fun nested => nested
  map_id := fun _ => rfl
  unit_natural := fun _ _ => rfl
  mult_natural := fun _ _ => rfl
  unit_mult := fun _ => rfl
  map_unit_mult := fun _ => rfl
  mult_mult := fun _ => rfl

/-- The **Kleisli extension** (dual to `coKleisliExtend`) — promote a Kleisli map `A → ?B` to `?A → ?B` (`?f` then
`μ`).  The Kleisli category of `?` is the intuitionistic category under the why-not monad. -/
def WhyNotModality.kleisliExtend (whyNot : WhyNotModality) {A B : Type}
    (kleisliMap : A → whyNot.WhyNot B) (boxed : whyNot.WhyNot A) : whyNot.WhyNot B :=
  whyNot.mult (whyNot.map kleisliMap boxed)

/-- Extending after `unit` recovers the map (the Kleisli left unit) — `extend f ∘ η = f`. -/
theorem WhyNotModality.kleisliExtend_unit (whyNot : WhyNotModality) {A B : Type}
    (kleisliMap : A → whyNot.WhyNot B) (value : A) :
    whyNot.kleisliExtend kleisliMap (whyNot.unit value) = kleisliMap value := by
  show whyNot.mult (whyNot.map kleisliMap (whyNot.unit value)) = kleisliMap value
  rw [whyNot.unit_natural, whyNot.unit_mult]

/-- Extending `unit` is the identity (the Kleisli right unit). -/
theorem WhyNotModality.unit_kleisliExtend (whyNot : WhyNotModality) {A : Type}
    (boxed : whyNot.WhyNot A) : whyNot.kleisliExtend whyNot.unit boxed = boxed :=
  whyNot.map_unit_mult boxed

/-- ★ The `! ⊣ ?` adjunction: the store `!` (a `Resource ×`-comonad) is LEFT adjoint to the reader `?` (a
`Resource →`-monad) — the hom-set iso `(!A → B) ≅ (A → ?B)`, i.e. currying `(Resource × A → B) ≅ (A → Resource →
B)`.  This is the genuine dual relationship between the two exponential modalities, both round trips by `rfl`. -/
def storeReaderAdjunction (Resource A B : Type) :
    LinearIso ((storeExponential Resource).Bang A → B) (A → (readerWhyNot Resource).WhyNot B) where
  forward := fun linearMap value resource => linearMap (resource, value)
  backward := fun intuitMap boxed => intuitMap boxed.2 boxed.1
  forward_backward := fun _ => rfl
  backward_forward := fun _ => rfl

/-! ## Honesty markers -/

/-- **Honesty marker.**  The general Seely monoidal-natural iso `!(A & B) ≅ !A ⊗ !B` for a NON-trivial comonad
(beyond the identity-exponential witness — the store comonad provably fails it) is deferred.  `= false`. -/
def fxMode_hasSeelyCoherence : Bool := false

/-- The `?` why-not MODALITY is SHIPPED as a monad: `WhyNotModality` (the categorical dual of `LinearExponential`),
the canonical `readerWhyNot` witness (`?A = Resource → A`, laws by `rfl`), the Kleisli extension + unit laws, and
the ★ `! ⊣ ?` adjunction `storeReaderAdjunction` (store ⊣ reader = `(×) ⊣ (→)`).  Still deferred (so the marker
stays scoped): the CLASSICAL de Morgan INVOLUTION `?A ≅ ¬!¬A` / `!A ≅ ¬?¬A`, which needs an involutive linear
negation (`Classical.choice`).  `= true` (the `?`-monad + the `!⊣?` duality). -/
def fxMode_hasWhyNotDuality : Bool := true

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

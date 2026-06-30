import FX1Poly.Polygraph.Category.RawCategory

/-! # context-24 — realizability / the effective topos, context-side residue

`context-24` is the REALIZABILITY MODEL rung: the Hyland effective topos and, more elementarily, the category
of ASSEMBLIES over a partial combinatory algebra — the model where a type is a set EQUIPPED WITH REALIZERS
(elements of a combinatory algebra / "programs"), a term is realized by a program, and a function is a map
TRACKED by a program.  Its computational content is the extraction story (FX0 / `fib-16`): the realizer IS
the extracted program.

## What is context-side here, and what is deferred

The category of CONTEXTS of a realizability model is `Asm(A)` — assemblies over a combinatory algebra `A`.
That base, together with the combinatory substrate it is built on, is pure category-of-contexts data; that is
the CONTEXT-SIDE residue shipped here, in full and zero-axiom, GENERIC over the algebra:

  * **`CombinatoryAlgebra`** — the substrate: a carrier with a (total) application and the `k`/`s`
    combinators satisfying the two combinator laws.  (We ship the TOTAL presentation — a combinatory
    algebra; total CAs already give realizability categories.  The PARTIAL PCA, e.g. Kleene's `K₁`, is the
    canonical example and is the deferred concrete instance below.)
  * derived COMBINATORICS, PROVED generically (true in EVERY combinatory algebra): the identity combinator
    `I = S K K` with **`apply_identityCombinator`** (`I · a = a`) and the composition combinator
    `B = S (K S) K` with **`apply_composeCombinator`** (`B · f · g · x = f · (g · x)`).  These are the
    trackers the category needs.
  * **`Assembly`** — a set with a realizability relation in which every element has a realizer; and
    **`AssemblyMorphism`** — a function TRACKED by an algebra element.  Because "tracked" is an EXISTENTIAL
    `Prop`, a morphism is equal to another exactly when their underlying functions are.
  * **`assemblyCategory`** — `Asm(A)` as a genuine `RawCategory`: identity tracked by `I`, composition
    tracked by `B`, and (as in `□`/`Δ`/`Grpd`) the three category laws hold DEFINITIONALLY — β/η on the
    underlying functions + proof irrelevance of the tracking `Prop` — so each is `rfl`, no `funext`.
  * **`Assembly.isModest`** — the MODEST (single-valued realizability) refinement, the assemblies that form
    the internal sets of the effective topos; the **`terminalAssembly`** is a concrete modest object.

DEFERRED (honestly NOT here):
  * the canonical NON-TRIVIAL PCA — Kleene's `K₁` (partial recursive application) — which is what makes the
    realizability relation have genuine CONTENT (not every function tracked); it needs a model of
    computation (Turing machines / μ-recursion), a heavy CONCRETE-substrate increment.  `trivialCombinatoryAlgebra`
    is shipped ONLY to witness the structure is inhabited (so the generic theorems are not vacuous); over it
    `Asm` collapses to `Set` (degenerate).  The GENERIC `assemblyCategory` over an abstract algebra is the
    faithful, non-degenerate deliverable — `hasNumberRealizability = false`.
  * the REALIZABILITY TYPE STRUCTURE — the interpretation of `Id`/`Π`/`Σ` by realizability, the CwF type
    structure over `Asm`, and soundness (well-typed ⟹ realizable) — `×type`, `hasRealizabilityTypeStructure
    = false`.
  * the MODEST-SET UNIVERSE / the effective topos proper (the tripos-to-topos exact completion) —
    `×type`/beyond context-side, `hasModestSetUniverse = false`.

Reference: Hyland, "The effective topos" (1982); van Oosten, "Realizability: An Introduction to its
Categorical Side" (2008).

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

/-! ## The combinatory-algebra substrate -/

/-- A **combinatory algebra** — a carrier with a (total) application and the `k`/`s` combinators satisfying
the two combinator laws.  This is the realizability substrate (`A` in `Asm(A)`).  The partial PCA (Kleene's
`K₁`) is the canonical example; we ship the total presentation, which already yields a realizability category. -/
structure CombinatoryAlgebra where
  /-- The carrier (the "programs" / realizers). -/
  Carrier : Type
  /-- (Total) application of one element to another. -/
  apply : Carrier → Carrier → Carrier
  /-- The `k` combinator. -/
  k : Carrier
  /-- The `s` combinator. -/
  s : Carrier
  /-- `k · a · b = a`. -/
  kLaw : ∀ (elementA elementB : Carrier), apply (apply k elementA) elementB = elementA
  /-- `s · a · b · c = (a · c) · (b · c)`. -/
  sLaw : ∀ (elementA elementB elementC : Carrier),
    apply (apply (apply s elementA) elementB) elementC
      = apply (apply elementA elementC) (apply elementB elementC)

/-- The identity combinator `I = S K K`. -/
def CombinatoryAlgebra.identityCombinator (algebra : CombinatoryAlgebra) : algebra.Carrier :=
  algebra.apply (algebra.apply algebra.s algebra.k) algebra.k

/-- ★ `I · a = a` — derived from `k`/`s` in ANY combinatory algebra (the classic `SKK = I`). -/
theorem CombinatoryAlgebra.apply_identityCombinator (algebra : CombinatoryAlgebra)
    (element : algebra.Carrier) :
    algebra.apply algebra.identityCombinator element = element :=
  (algebra.sLaw algebra.k algebra.k element).trans
    (algebra.kLaw element (algebra.apply algebra.k element))

/-- The composition combinator `B = S (K S) K`. -/
def CombinatoryAlgebra.composeCombinator (algebra : CombinatoryAlgebra) : algebra.Carrier :=
  algebra.apply (algebra.apply algebra.s (algebra.apply algebra.k algebra.s)) algebra.k

/-- ★ `B · f · g · x = f · (g · x)` — the composition combinator, derived generically.  This is the tracker
for composition of assembly morphisms. -/
theorem CombinatoryAlgebra.apply_composeCombinator (algebra : CombinatoryAlgebra)
    (functionOuter functionInner argument : algebra.Carrier) :
    algebra.apply (algebra.apply (algebra.apply algebra.composeCombinator functionOuter) functionInner)
        argument
      = algebra.apply functionOuter (algebra.apply functionInner argument) := by
  show algebra.apply (algebra.apply (algebra.apply (algebra.apply (algebra.apply algebra.s
      (algebra.apply algebra.k algebra.s)) algebra.k) functionOuter) functionInner) argument
    = algebra.apply functionOuter (algebra.apply functionInner argument)
  rw [algebra.sLaw, algebra.kLaw, algebra.sLaw, algebra.kLaw]

/-! ## Assemblies + the category Asm(A) -/

/-- An **assembly** over `algebra` — a set with a realizability relation in which every element has at least
one realizer (a "program" that witnesses it). -/
structure Assembly (algebra : CombinatoryAlgebra) where
  /-- The underlying set. -/
  Carrier : Type
  /-- The realizability relation: which programs realize which elements. -/
  realizes : algebra.Carrier → Carrier → Prop
  /-- Every element is realized by some program. -/
  isRealized : ∀ (element : Carrier), ∃ (realizer : algebra.Carrier), realizes realizer element

/-- A **morphism of assemblies** — a function that is TRACKED by an algebra element: some program sends every
realizer of `element` to a realizer of `onElements element`.  The tracking condition is an existential
`Prop`, so a morphism is determined (for equality) by its underlying function. -/
structure AssemblyMorphism {algebra : CombinatoryAlgebra} (source target : Assembly algebra) where
  /-- The underlying function on elements. -/
  onElements : source.Carrier → target.Carrier
  /-- The function is tracked by a program. -/
  isTracked : ∃ (tracker : algebra.Carrier),
    ∀ (element : source.Carrier) (realizer : algebra.Carrier),
      source.realizes realizer element →
      target.realizes (algebra.apply tracker realizer) (onElements element)

/-- The identity morphism of assemblies — tracked by the identity combinator `I`. -/
def AssemblyMorphism.identityMorphism {algebra : CombinatoryAlgebra} (assembly : Assembly algebra) :
    AssemblyMorphism assembly assembly where
  onElements := fun element => element
  isTracked := ⟨algebra.identityCombinator, by
    intro element realizer hrealizes
    rw [algebra.apply_identityCombinator]
    exact hrealizes⟩

/-- Composition of assembly morphisms (apply `first`, then `second`) — tracked by `B trackerSecond
trackerFirst`. -/
def AssemblyMorphism.composeMorphism {algebra : CombinatoryAlgebra}
    {sourceAssembly midAssembly targetAssembly : Assembly algebra}
    (first : AssemblyMorphism sourceAssembly midAssembly)
    (second : AssemblyMorphism midAssembly targetAssembly) :
    AssemblyMorphism sourceAssembly targetAssembly where
  onElements := fun element => second.onElements (first.onElements element)
  isTracked := by
    obtain ⟨trackerFirst, trackFirst⟩ := first.isTracked
    obtain ⟨trackerSecond, trackSecond⟩ := second.isTracked
    refine ⟨algebra.apply (algebra.apply algebra.composeCombinator trackerSecond) trackerFirst, ?_⟩
    intro element realizer hrealizes
    rw [algebra.apply_composeCombinator]
    exact trackSecond (first.onElements element) (algebra.apply trackerFirst realizer)
      (trackFirst element realizer hrealizes)

/-- ★ **The category of assemblies `Asm(A)`** as a genuine `RawCategory` — the category of CONTEXTS of the
realizability model over `algebra`.  Identity is tracked by `I`, composition by `B`; all three category laws
hold DEFINITIONALLY (β/η on the underlying functions + proof irrelevance of the tracking `Prop`) — each
`rfl`, no `funext`. -/
def assemblyCategory (algebra : CombinatoryAlgebra) : RawCategory where
  Object := Assembly algebra
  Morphism := fun source target => AssemblyMorphism source target
  identity := fun assembly => AssemblyMorphism.identityMorphism assembly
  compose := fun first second => AssemblyMorphism.composeMorphism first second
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl

/-! ## Modest sets + a concrete object -/

/-- An assembly is **modest** when realizers are SINGLE-VALUED: no program realizes two distinct elements.
Modest sets are the internal sets of the effective topos (`≃` partial equivalence relations). -/
def Assembly.isModest {algebra : CombinatoryAlgebra} (assembly : Assembly algebra) : Prop :=
  ∀ (realizer : algebra.Carrier) (elementOne elementTwo : assembly.Carrier),
    assembly.realizes realizer elementOne → assembly.realizes realizer elementTwo → elementOne = elementTwo

/-- The terminal assembly (the unit object): one element, realized by every program. -/
def terminalAssembly (algebra : CombinatoryAlgebra) : Assembly algebra where
  Carrier := Unit
  realizes := fun _ _ => True
  isRealized := fun _ => ⟨algebra.k, trivial⟩

/-- The terminal assembly is modest (its carrier is a subsingleton). -/
theorem terminalAssembly_isModest (algebra : CombinatoryAlgebra) :
    (terminalAssembly algebra).isModest :=
  fun _ _ _ _ _ => rfl

/-- The INDISCRETE assembly on `Bool` — two distinct elements, both realized by every program. -/
def indiscreteBoolAssembly (algebra : CombinatoryAlgebra) : Assembly algebra where
  Carrier := Bool
  realizes := fun _ _ => True
  isRealized := fun _ => ⟨algebra.k, trivial⟩

/-- ★ The indiscrete `Bool` assembly is NOT modest — so modesty is a GENUINE restriction (not every assembly
is modest): the single program `k` realizes both `true` and `false`, which are distinct.  Together with
`terminalAssembly_isModest` this shows `isModest` is a real two-sided distinction (modest sets are a proper
subcategory). -/
theorem indiscreteBoolAssembly_not_isModest (algebra : CombinatoryAlgebra) :
    ¬ (indiscreteBoolAssembly algebra).isModest :=
  fun isModest => Bool.noConfusion (isModest algebra.k true false trivial trivial)

/-! ## A non-vacuity witness for the substrate -/

/-- The TRIVIAL (one-point) combinatory algebra — shipped ONLY to witness that `CombinatoryAlgebra` is
inhabited, so the generic theorems above are not vacuous.  It is DEGENERATE: over it `Asm` collapses to
`Set`.  The canonical non-trivial PCA (`K₁`) is the deferred concrete instance. -/
def trivialCombinatoryAlgebra : CombinatoryAlgebra where
  Carrier := Unit
  apply := fun _ _ => ()
  k := ()
  s := ()
  kLaw := fun _ _ => rfl
  sLaw := fun _ _ _ => rfl

/-! ## The model datum + honesty markers -/

/-- The context-side datum of the realizability model over a combinatory algebra: the algebra + its category
of assemblies (the base of contexts).  Realizability is PCA-INDEXED — one model per algebra. -/
structure RealizabilityModelData where
  /-- The combinatory algebra (the realizers). -/
  algebra : CombinatoryAlgebra
  /-- The base — the category of assemblies `Asm(A)` (the contexts).  Objects are assemblies (`Type 1`). -/
  base : RawCategory.{1, 0}

/-- ★ The FX realizability-model datum over a combinatory algebra: `Asm(A)` as the base.  Parameterized by
the algebra (realizability is PCA-indexed); the faithful, non-degenerate deliverable. -/
def fxRealizabilityModel (algebra : CombinatoryAlgebra) : RealizabilityModelData where
  algebra := algebra
  base := assemblyCategory algebra

/-- **Honesty marker.**  The REALIZABILITY TYPE STRUCTURE — the interpretation of `Id`/`Π`/`Σ` by
realizability, the CwF type structure over `Asm`, and soundness (well-typed ⟹ realizable) — is `×type`,
deferred.  `= false`. -/
def fxRealizabilityModel_hasRealizabilityTypeStructure : Bool := false

/-- **Honesty marker.**  The MODEST-SET UNIVERSE / the effective topos proper (the tripos-to-topos exact
completion) is `×type` / beyond context-side, deferred.  `= false`. -/
def fxRealizabilityModel_hasModestSetUniverse : Bool := false

/-- **Honesty marker.**  NUMBER REALIZABILITY over the canonical non-trivial PCA `K₁` (partial recursive
application) — what makes the realizability relation have genuine content, plus the existence/disjunction
properties — needs a model of computation, a deferred CONCRETE-substrate increment.  The generic
`assemblyCategory` over an abstract algebra is the faithful deliverable.  `= false`. -/
def fxRealizabilityModel_hasNumberRealizability : Bool := false

/-! ## Smoke -/

/-- Smoke: the left identity law of the assembly category holds (exercises `Asm(A)`'s `RawCategory`
structure — identity tracked by `I`, composition by `B`). -/
theorem assemblyCategory_identityLeft_smoke (algebra : CombinatoryAlgebra)
    {source target : Assembly algebra} (morphism : AssemblyMorphism source target) :
    (assemblyCategory algebra).compose ((assemblyCategory algebra).identity source) morphism = morphism :=
  (assemblyCategory algebra).identityLeft morphism

end FX1Poly.Tier0

import FX1Poly.Tier0.Context.FibrationCategory
import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstColimits

/-! # context-16 — democracy + local cartesian closure, context-side residue (`⊟SPLIT`)

`context-16` is the DEMOCRACY + LCC rung, marked `⊟SPLIT · core=democracy×type→fib-1`: a CwF is DEMOCRATIC
(Clairambault–Dybjer) when every context is isomorphic to the comprehension of a single CLOSED TYPE — and a
category of contexts is LOCALLY CARTESIAN CLOSED when pullback along each display map has a right adjoint
(the Π-type).  BOTH notions are fundamentally `×type`: democracy needs the closed-type packing of a context
(a Σ-type), and local closure needs Π.  This rung therefore ships the context-side INTERFACES + a witness,
and DEFERS the genuine cores to the type axis / `fib-1`.

## What is context-side here, and what is deferred

  * **`DemocraticStructure`** — the democracy interface: each context Γ comes with a "democratic"
    object `democraticType Γ` and an ISOMORPHISM Γ ≅ `democraticType Γ` (in a real democratic CwF the
    democratic object is the comprehension `⊤.Σ_Γ` of the closed Σ-type packing Γ; here it is abstract,
    since the type layer is `×type`).
  * **`LocallyCartesianClosedStructure`** — the LCC interface restricted to its CONTEXT-SIDE part: a
    terminal object and BINARY PRODUCTS with their universal property (the "cartesian" half — the products
    are the context-concatenation already shipped as `context-3`'s coproduct in `fxBaseSubstCategory`).
    The "locally CLOSED" half (Π / slice exponentials) is the deferred `×type` core.
  * **`LocallyCartesianClosedStructure.ofOppositeFiniteCoproducts`** — the GENERIC dualization: finite
    coproducts in any `𝒟` ARE finite products in `𝒟ᵒᵖ`, with every product law `rfl`-inherited from the
    coproduct's universal property (the opposite reverses composition definitionally).
  * **`fxContextCartesianClosed`** — ★ the NON-degenerate context-side witness: the genuine category of
    contexts `𝒞 = fxBaseSubstCategory.opposite` is cartesian, its terminal object the empty context `◇` and
    its product real context CONCATENATION (`leftLen + rightLen`).  Built by dualizing `context-3`'s
    `fxBaseSubstBinaryCoproduct`; products compute (`product 2 3 = 5`), not a point.
  * **`terminalDemocratic` / `terminalLCC`** — the point as a (trivially) democratic, cartesian-closed
    category: genuine witnesses inhabiting the interfaces (all laws by `rfl`, via `PUnit` eta).

DEFERRED (honestly NOT here, the `×type → fib-1` core, recorded by the `= false` markers):
  * the CLOSED-TYPE PACKING of a context (the Σ-type whose comprehension recovers the context) —
    `hasClosedTypePacking = false` (`×type`, the democracy core);
  * LOCAL EXPONENTIALS / the Π right adjoint to pullback along display maps —
    `hasLocalExponentials = false` (`×type`, the LCC core);
  * the genuine FX democracy/LCC WITNESS over `fxBaseSubstCategory` (with its real contexts and the
    Σ/Π type formers) — `hasFxWitness = false` (`fib-1`).

Reference: Clairambault & Dybjer, "The biequivalence of locally cartesian closed categories and Martin-Löf
type theories", TLCA 2011 / MSCS 24 (2014).

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0
open FX1Poly.Polygraph

/-! ## Democracy (the interface) -/

/-- A **democratic structure** on a category of contexts: every context Γ is isomorphic to a distinguished
"democratic" object `democraticType Γ`.  In a democratic CwF the democratic object is the comprehension of
the closed Σ-type packing Γ — that packing is `×type` (the deferred core); here the interface records the
required isomorphism. -/
structure DemocraticStructure where
  /-- The base category of contexts. -/
  base : RawCategory
  /-- The democratic object for each context (its closed-type comprehension, abstractly). -/
  democraticType : base.Object → base.Object
  /-- The comparison map exhibiting the context as its democratic object. -/
  comparison : (object : base.Object) → base.Morphism object (democraticType object)
  /-- The comparison is an isomorphism: every context IS (up to iso) the comprehension of a closed type. -/
  comparisonIso : (object : base.Object) → IsIsomorphism base (comparison object)

/-- ★ The point is trivially democratic: the one context is (identically) isomorphic to itself. -/
def terminalDemocratic : DemocraticStructure where
  base := terminalCategory
  democraticType := fun object => object
  comparison := fun object => terminalCategory.identity object
  comparisonIso := fun object => IsIsomorphism.identityWitness terminalCategory object

/-! ## Local cartesian closure — the cartesian (context-side) part -/

/-- The **cartesian part of local cartesian closure**: a terminal object and binary PRODUCTS with their
universal property.  The products are the context-side structure (the context concatenation — `context-3`'s
coproduct in `fxBaseSubstCategory`).  The "locally CLOSED" part (Π / slice exponentials) is the `×type`
core, deferred (see the markers). -/
structure LocallyCartesianClosedStructure where
  /-- The base category of contexts. -/
  base : RawCategory
  /-- The terminal object (the empty context). -/
  terminalObject : base.Object
  /-- The unique map to the terminal object. -/
  toTerminal : (object : base.Object) → base.Morphism object terminalObject
  /-- Terminality. -/
  toTerminalUnique : ∀ {object : base.Object} (morphism : base.Morphism object terminalObject),
    morphism = toTerminal object
  /-- Binary products (context concatenation). -/
  product : base.Object → base.Object → base.Object
  /-- Left projection. -/
  projectionLeft : (left right : base.Object) → base.Morphism (product left right) left
  /-- Right projection. -/
  projectionRight : (left right : base.Object) → base.Morphism (product left right) right
  /-- Pairing of two maps with common domain. -/
  pair : {domain left right : base.Object} →
    base.Morphism domain left → base.Morphism domain right → base.Morphism domain (product left right)
  /-- The pairing's left β-law. -/
  pairProjectionLeft : ∀ {domain left right : base.Object}
    (toLeft : base.Morphism domain left) (toRight : base.Morphism domain right),
    base.compose (pair toLeft toRight) (projectionLeft left right) = toLeft
  /-- The pairing's right β-law. -/
  pairProjectionRight : ∀ {domain left right : base.Object}
    (toLeft : base.Morphism domain left) (toRight : base.Morphism domain right),
    base.compose (pair toLeft toRight) (projectionRight left right) = toRight
  /-- The pairing's η/uniqueness law. -/
  pairUnique : ∀ {domain left right : base.Object} (morphism : base.Morphism domain (product left right)),
    morphism = pair (base.compose morphism (projectionLeft left right))
      (base.compose morphism (projectionRight left right))

/-- ★ The point is trivially (locally) cartesian closed at the cartesian level: terminal and products are
the unique object, every law by `rfl` (via `PUnit` eta). -/
def terminalLCC : LocallyCartesianClosedStructure where
  base := terminalCategory
  terminalObject := PUnit.unit
  toTerminal := fun _ => PUnit.unit
  toTerminalUnique := fun _ => rfl
  product := fun _ _ => PUnit.unit
  projectionLeft := fun _ _ => PUnit.unit
  projectionRight := fun _ _ => PUnit.unit
  pair := fun _ _ => PUnit.unit
  pairProjectionLeft := fun _ _ => rfl
  pairProjectionRight := fun _ _ => rfl
  pairUnique := fun _ => rfl

/-! ## The GENUINE cartesian witness over `𝒞` — finite coproducts in `𝒞ᵒᵖ` are finite products in `𝒞` -/

/-- ★ **The dualization.**  Finite COPRODUCTS in a category `𝒟` ARE finite PRODUCTS in its opposite
`𝒟ᵒᵖ`: an initial object and binary coproducts in `𝒟` give the cartesian part of local cartesian closure
over `RawCategory.opposite 𝒟`.  Every product law is the matching coproduct law transported across the
opposite — and because `opposite.compose f g` is DEFINITIONALLY `𝒟.compose g f`, each law holds by the
coproduct's own universal-property field (the β-laws are the `copair`-after-injection laws; uniqueness is
`copairUnique` with both compatibility hypotheses `rfl`).  No extensionality. -/
def LocallyCartesianClosedStructure.ofOppositeFiniteCoproducts
    (category : RawCategory)
    {initialObject : category.Object}
    (initial : IsInitialObject category initialObject)
    (coproductObject : category.Object → category.Object → category.Object)
    (coproduct : (left right : category.Object) →
      IsBinaryCoproduct category left right (coproductObject left right)) :
    LocallyCartesianClosedStructure where
  base := RawCategory.opposite category
  terminalObject := initialObject
  toTerminal := fun object => initial.fromInitial object
  toTerminalUnique := fun morphism => initial.fromInitialUnique morphism
  product := coproductObject
  projectionLeft := fun left right => (coproduct left right).injectLeft
  projectionRight := fun left right => (coproduct left right).injectRight
  pair := fun toLeft toRight => (coproduct _ _).copair toLeft toRight
  pairProjectionLeft := fun toLeft toRight => (coproduct _ _).copairInjectLeft toLeft toRight
  pairProjectionRight := fun toLeft toRight => (coproduct _ _).copairInjectRight toLeft toRight
  pairUnique := fun morphism => (coproduct _ _).copairUnique morphism _ _ rfl rfl

/-- ★ The GENUINE category of contexts `𝒞` (`= fxBaseSubstCategory.opposite`) is CARTESIAN: its terminal
object is the empty context `◇` (scope `0`, initial in `𝒞ᵒᵖ`) and its binary product is context
CONCATENATION (`leftLen + rightLen`, the coproduct in `𝒞ᵒᵖ`).  This is the non-degenerate context-side
cartesian skeleton of LCC — products are real scope addition, not a point.  Built by dualizing
`context-3`'s `fxBaseSubstBinaryCoproduct` + `fxBaseSubstInitial`; all laws inherited zero-axiom. -/
def fxContextCartesianClosed : LocallyCartesianClosedStructure :=
  LocallyCartesianClosedStructure.ofOppositeFiniteCoproducts
    fxBaseSubstCategory fxBaseSubstInitial
    (fun leftLen rightLen => Nat.add leftLen rightLen)
    fxBaseSubstBinaryCoproduct

/-! ## Honesty markers (the `×type → fib-1` core) -/

/-- **Honesty marker.**  The CLOSED-TYPE PACKING of a context — the Σ-type whose comprehension recovers the
context (the democracy core) — is `×type`, deferred to `fib-1`.  `= false`. -/
def democracyLCC_hasClosedTypePacking : Bool := false

/-- **Honesty marker.**  LOCAL EXPONENTIALS — the Π right adjoint to pullback along display maps (the
locally-CLOSED part of LCC) — is `×type`, deferred to `fib-1`.  `= false`. -/
def democracyLCC_hasLocalExponentials : Bool := false

/-- **Honesty marker.**  The genuine FX democracy/LCC witness over `fxBaseSubstCategory` WITH its Σ/Π
type formers is the cross-axis assembly, deferred to `fib-1`.  `= false`.  (The cartesian SKELETON — the
finite products of the genuine `𝒞` — DOES land here as `fxContextCartesianClosed`; what is deferred is the
democracy Σ-packing and the LCC Π local-exponential, both `×type`.) -/
def democracyLCC_hasFxWitness : Bool := false

/-! ## Smoke -/

/-- Smoke: in the point, the democratic comparison composed with its inverse is the identity (the iso law),
exercising `comparisonIso`. -/
theorem terminalDemocratic_comparisonIso_smoke (object : terminalDemocratic.base.Object) :
    terminalDemocratic.base.compose (terminalDemocratic.comparison object)
        (terminalDemocratic.comparisonIso object).inverse
      = terminalDemocratic.base.identity object :=
  (terminalDemocratic.comparisonIso object).rightInverse

/-- Smoke (NON-degeneracy): the product in the genuine `𝒞` is real context concatenation — the product of
a 2-variable and a 3-variable context is the 5-variable context, by `rfl` (scope addition).  This is what
distinguishes `fxContextCartesianClosed` from the degenerate `terminalLCC` (where every product is the
point). -/
theorem fxContextCartesianClosed_product_smoke :
    fxContextCartesianClosed.product (2 : Nat) (3 : Nat) = (5 : Nat) := by
  with_unfolding_all rfl

end FX1Poly.Tier0

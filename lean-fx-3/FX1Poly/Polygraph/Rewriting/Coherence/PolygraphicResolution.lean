import FX1Poly.Polygraph.Rewriting.Coherence.SquierCoherence

/-! # Tier0/Term — the polygraphic resolution + 𝔽₂ polygraphic homology (term-5)

`term-4` shipped Squier coherence: the proof-relevant rewriting 2-category and the diamonds as a
homotopy basis.  `term-5` goes one dimension further — the (∞)-polygraphic resolution (an acyclic
ω-polygraph extending the rewriting system by higher cells) and its POLYGRAPHIC HOMOLOGY `Hₙ`.

## The zero-axiom design (the two hard constraints)

  * **Homology groups are quotients.**  `Hₙ = ker ∂ₙ / im ∂ₙ₊₁` needs `Quot.sound` (banned).  So
    homology is expressed as VANISHING — a `Prop`: `ker ∂ₙ ⊆ im ∂ₙ₊₁` (every cycle is a boundary) — never
    as a quotient group.  Acyclicity = vanishing at every degree.
  * **`Int` coefficients are unavailable.**  No `Int` arithmetic exists zero-axiom here (its core lemmas
    are in the same `propext`-leaking class as `Nat.add_comm`, which this codebase systematically avoids,
    and there is no additive inverse anywhere).  So the coefficient ring is **𝔽₂** (`Bool` with `xor`):
    self-inverse (`x + x = 0`, so no negation needed), and all chain laws are stated/closed by `Bool`
    case analysis — propext-clean.  Integral (ℤ) homology is the deferred refinement.

## What this file ships (each zero-axiom)

  * **`F2ChainComplex`** — an abstract chain complex over 𝔽₂: chain groups, the 𝔽₂ abelian-group ops, and
    the boundary with `∂² = 0`.
  * **`IsCycle` / `IsBoundary`** + **`boundary_isCycle`** — every boundary is a cycle (from `∂² = 0`).
  * **`HomologyVanishes` / `IsAcyclic`** — homology vanishing as a `Prop` (cycles ⊆ boundaries) and
    acyclicity (vanishing at every degree) — the quotient-free `Hₙ = 0`.
  * **`trivialComplex`** (acyclic) + **`zeroDifferentialComplex`** (homology does NOT vanish) — concrete
    witnesses that the machinery genuinely DISTINGUISHES acyclic from non-acyclic (non-vacuity).
  * **`rewriteResolution_dimTwoAcyclic`** — the (∞)-resolution connection: `term-4`'s `coherence` IS the
    resolution's DIM-2 ACYCLICITY (every 2-sphere — a pair of parallel reduction paths to a normal form —
    is filled by a homotopy 2-cell), the start of the polygraphic resolution.
  * **`PolygraphResolution`** — the (∞)-resolution interface: an acyclic cell tower (every n-sphere filled
    by an (n+1)-cell).
  * **`presentationComplex`** + **`monoidNComplex` / `trivialMonoidComplex`** — the ABELIANIZED CHAIN
    COMPLEX OF A PRESENTATION built as a real `F2ChainComplex` (`C₁ = 𝔽₂[generators]`, `C₂ = 𝔽₂[relations]`,
    `∂₂` = the relation differential), with `H₁` COMPUTED for two genuine monoid presentations: `⟨a,b|a=b⟩`
    (≅ `ℕ`) has `H₁ ≠ 0` (`monoidNComplex_homologyNotVanishing`) and `⟨a|a=ε⟩` (trivial) has `H₁ = 0`
    (`trivialMonoidComplex_homologyVanishes`).  The complex's `∂₂` IS `relationBoundaryF2`
    (`monoidNComplex_degreeTwoBoundary_eq_relationBoundary`), wiring the standalone abelianization into the
    framework.

HONEST SCOPE: the 𝔽₂ homology FRAMEWORK + small concrete presentation complexes (`H₁` only, 2-truncated) +
the resolution's dim-2 acyclicity from `term-4`.  Deferred (the `OHOM-1` #1261 capstone): the full
polygraphic chain complex over the 205-generator table (the abelianization of `fxKernelPolygraph`), integral
(ℤ) homology, the higher (≥3) critical-triple cells, and the homology-computes-coherence theorem.

## Zero-axiom verification

A record bundle + `Prop` definitions, `Bool` case-analysis for the 𝔽₂ laws (`add_self`/`add_zero`), `rfl`
for the trivial/`Unit`-eta witness, `Bool.noConfusion` for the non-vanishing witness, and `term-4`'s
`coherence` for the dim-2 connection.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTier0TermPolygraphicResolution.lean`.
-/

namespace FX1Poly.Core

variable {Carrier : Type}

/-- An abstract **chain complex over 𝔽₂** (`Bool` / `xor` coefficients — self-inverse, so no negation):
the chain groups `chain n`, the 𝔽₂ abelian-group operations (`zero` / `add` with `add_self` giving
`x + x = 0`), and the boundary `∂` with `∂² = 0`.  The quotient-free carrier of polygraphic homology. -/
structure F2ChainComplex where
  /-- The chain group in each dimension. -/
  chain : Nat → Type
  /-- The 𝔽₂ zero chain. -/
  zero : {dimension : Nat} → chain dimension
  /-- 𝔽₂ addition (XOR of chains). -/
  add : {dimension : Nat} → chain dimension → chain dimension → chain dimension
  /-- The boundary map `∂ : Cₙ₊₁ → Cₙ`. -/
  boundary : {dimension : Nat} → chain (dimension + 1) → chain dimension
  /-- `zero` is a right unit for `add`. -/
  add_zero : ∀ {dimension : Nat} (element : chain dimension), add element zero = element
  /-- 𝔽₂ self-inverse: `x + x = 0` (so subtraction is addition). -/
  add_self : ∀ {dimension : Nat} (element : chain dimension), add element element = zero
  /-- The boundary preserves zero. -/
  boundary_zero : ∀ {dimension : Nat},
    boundary (zero : chain (dimension + 1)) = (zero : chain dimension)
  /-- The boundary is additive. -/
  boundary_add : ∀ {dimension : Nat} (first second : chain (dimension + 1)),
    boundary (add first second) = add (boundary first) (boundary second)
  /-- The chain-complex condition `∂ ∘ ∂ = 0`. -/
  boundary_squared_zero : ∀ {dimension : Nat} (element : chain (dimension + 2)),
    boundary (boundary element) = (zero : chain dimension)

/-- A chain is a **cycle** when its boundary is zero. -/
def F2ChainComplex.IsCycle (complex : F2ChainComplex) {dimension : Nat}
    (element : complex.chain (dimension + 1)) : Prop :=
  complex.boundary element = complex.zero

/-- A chain is a **boundary** when it is in the image of `∂`. -/
def F2ChainComplex.IsBoundary (complex : F2ChainComplex) {dimension : Nat}
    (element : complex.chain (dimension + 1)) : Prop :=
  ∃ source : complex.chain (dimension + 2), complex.boundary source = element

/-- ★ **Boundaries are cycles** (from `∂² = 0`): the image of `∂` lies in the kernel of `∂`, so homology
is well-defined as the quotient kernel/image (here, expressed by vanishing). -/
theorem F2ChainComplex.boundary_isCycle (complex : F2ChainComplex) {dimension : Nat}
    {element : complex.chain (dimension + 1)} (isBoundary : complex.IsBoundary element) :
    complex.IsCycle element := by
  obtain ⟨source, hsource⟩ := isBoundary
  show complex.boundary element = complex.zero
  rw [← hsource]
  exact complex.boundary_squared_zero source

/-- ★ **Homology vanishing** `Hₙ₊₁ = 0` as a `Prop` (quotient-free): every cycle is a boundary
(`ker ∂ ⊆ im ∂`). -/
def F2ChainComplex.HomologyVanishes (complex : F2ChainComplex) (dimension : Nat) : Prop :=
  ∀ element : complex.chain (dimension + 1), complex.IsCycle element → complex.IsBoundary element

/-- The complex is **acyclic** when its homology vanishes in every (positive) degree — an exact complex /
a resolution. -/
def F2ChainComplex.IsAcyclic (complex : F2ChainComplex) : Prop :=
  ∀ dimension : Nat, complex.HomologyVanishes dimension

/-! ## Concrete witnesses — the machinery distinguishes acyclic from non-acyclic -/

/-- The **trivial complex** (every chain group is `Unit`): acyclic by construction (everything is the
unique element).  All 𝔽₂ laws hold by `Unit` eta (`rfl`). -/
def F2ChainComplex.trivialComplex : F2ChainComplex where
  chain := fun _ => Unit
  zero := ()
  add := fun _ _ => ()
  boundary := fun _ => ()
  add_zero := fun _ => rfl
  add_self := fun _ => rfl
  boundary_zero := rfl
  boundary_add := fun _ _ => rfl
  boundary_squared_zero := fun _ => rfl

/-- The trivial complex is **acyclic** — its homology vanishes in every degree. -/
theorem F2ChainComplex.trivialComplex_isAcyclic :
    F2ChainComplex.trivialComplex.IsAcyclic := by
  intro _dimension _element _isCycle
  exact ⟨(), rfl⟩

/-- The **zero-differential complex** over 𝔽₂ (every chain group is `Bool`, boundary `≡ 0`): its homology
is the chains themselves, so it does NOT vanish — the genuine witness that homology is non-trivial. -/
def F2ChainComplex.zeroDifferentialComplex : F2ChainComplex where
  chain := fun _ => Bool
  zero := false
  add := Bool.xor
  boundary := fun _ => false
  add_zero := fun element => by cases element <;> rfl
  add_self := fun element => by cases element <;> rfl
  boundary_zero := rfl
  boundary_add := fun _ _ => rfl
  boundary_squared_zero := fun _ => rfl

/-- ★ The zero-differential complex's homology does NOT vanish (the chain `true` is a cycle but not a
boundary): the machinery genuinely detects non-acyclicity. -/
theorem F2ChainComplex.zeroDifferentialComplex_homologyNotVanishing :
    ¬ F2ChainComplex.zeroDifferentialComplex.HomologyVanishes 0 := by
  intro homologyVanishes
  obtain ⟨_source, hsource⟩ := homologyVanishes true rfl
  exact Bool.noConfusion hsource

/-! ## The (∞)-polygraphic resolution and the term-4 connection -/

/-- ★ **The resolution's dim-2 acyclicity (from Squier coherence).**  `term-4`'s `coherence` IS the start
of the (∞)-polygraphic resolution: every 2-SPHERE — a pair of parallel reduction paths to a normal form —
is FILLED by a homotopy 2-cell.  So the rewriting polygraph extended with the diamond confluence cells is
acyclic in dimension 2 (no homology obstruction to coherence in that degree). -/
theorem rewriteResolution_dimTwoAcyclic {Step : Carrier → Carrier → Type} (dp : SquierDiamond Step)
    {source target : Carrier} (isNormalForm : ∀ next, Step target next → False)
    (leftPath rightPath : RewritePath Step source target) :
    RewriteHomotopy dp leftPath rightPath :=
  dp.coherence isNormalForm leftPath rightPath

/-- The **(∞)-polygraphic resolution interface**: an acyclic cell tower — a family of `cell`s at each
dimension, a notion of parallel n-cells (sharing a boundary), and a FILLER `(n+1)`-cell for every parallel
pair (`acyclic`).  The resolution is the cofibrant replacement whose homology is the polygraphic homology;
its dim-2 instance is `rewriteResolution_dimTwoAcyclic`. -/
structure PolygraphResolution where
  /-- The n-cells at each dimension. -/
  cell : Nat → Type
  /-- Two n-cells are parallel when they can be filled (share a boundary). -/
  parallel : {dimension : Nat} → cell dimension → cell dimension → Prop
  /-- An `(n+1)`-cell fills a parallel n-cell pair. -/
  fills : {dimension : Nat} → cell (dimension + 1) → cell dimension → cell dimension → Prop
  /-- ACYCLICITY: every parallel n-cell pair has a filling `(n+1)`-cell. -/
  acyclic : ∀ {dimension : Nat} (first second : cell dimension),
    parallel first second → ∃ filler : cell (dimension + 1), fills filler first second

/-! ## Cycles and boundaries are 𝔽₂-subgroups (homology is a quotient of subgroups) -/

/-- The zero chain is a cycle. -/
theorem F2ChainComplex.zero_isCycle (complex : F2ChainComplex) {dimension : Nat} :
    complex.IsCycle (complex.zero : complex.chain (dimension + 1)) :=
  complex.boundary_zero

/-- ★ **Cycles are closed under addition** — `ker ∂` is a 𝔽₂-subspace. -/
theorem F2ChainComplex.add_isCycle (complex : F2ChainComplex) {dimension : Nat}
    {first second : complex.chain (dimension + 1)}
    (firstIsCycle : complex.IsCycle first) (secondIsCycle : complex.IsCycle second) :
    complex.IsCycle (complex.add first second) := by
  show complex.boundary (complex.add first second) = complex.zero
  rw [complex.boundary_add, firstIsCycle, secondIsCycle, complex.add_zero]

/-- The zero chain is a boundary. -/
theorem F2ChainComplex.zero_isBoundary (complex : F2ChainComplex) {dimension : Nat} :
    complex.IsBoundary (complex.zero : complex.chain (dimension + 1)) :=
  ⟨complex.zero, complex.boundary_zero⟩

/-- ★ **Boundaries are closed under addition** — `im ∂` is a 𝔽₂-subspace.  With `boundary_isCycle`
(`im ∂ ⊆ ker ∂`), homology `Hₙ = ker ∂ₙ / im ∂ₙ₊₁` is a genuine quotient of subspaces (here:
the vanishing `ker ⊆ im`). -/
theorem F2ChainComplex.add_isBoundary (complex : F2ChainComplex) {dimension : Nat}
    {first second : complex.chain (dimension + 1)}
    (firstIsBoundary : complex.IsBoundary first) (secondIsBoundary : complex.IsBoundary second) :
    complex.IsBoundary (complex.add first second) := by
  obtain ⟨firstSource, firstSourceBoundary⟩ := firstIsBoundary
  obtain ⟨secondSource, secondSourceBoundary⟩ := secondIsBoundary
  exact ⟨complex.add firstSource secondSource, by
    rw [complex.boundary_add, firstSourceBoundary, secondSourceBoundary]⟩

/-! ## A concrete polygraphic computation — the 𝔽₂ abelianization of a presentation

The abelianized boundary `∂₂` of a monoid presentation: a relation `lhs = rhs` maps to the 𝔽₂ difference
of generator-multiplicities `lhs + rhs` (mod 2).  Computed here for two presentations over a 2-letter
alphabet (`false` = a, `true` = b). -/

/-- The 𝔽₂ abelianization of a word: the pair of generator-parities (count of `a` mod 2, count of `b`
mod 2) — the dim-1 chain a relation's boundary lands in. -/
def wordAbelianizationF2 : List Bool → Bool × Bool
  | [] => (false, false)
  | false :: rest => (!(wordAbelianizationF2 rest).1, (wordAbelianizationF2 rest).2)
  | true :: rest => ((wordAbelianizationF2 rest).1, !(wordAbelianizationF2 rest).2)

/-- The abelianized boundary `∂₂` of a relation `lhs = rhs` over 𝔽₂: `lhs + rhs` (= `lhs − rhs` mod 2). -/
def relationBoundaryF2 (lhs rhs : List Bool) : Bool × Bool :=
  let leftAbelian := wordAbelianizationF2 lhs
  let rightAbelian := wordAbelianizationF2 rhs
  (Bool.xor leftAbelian.1 rightAbelian.1, Bool.xor leftAbelian.2 rightAbelian.2)

/-- ★ **ℤ/2 = ⟨a | a²⟩**: the relation `a² = ε` abelianizes to ZERO over 𝔽₂ (the word `aa` has even
`a`-parity: `2·[a] = 0` mod 2), so it imposes nothing on H₁ — the 𝔽₂ polygraphic homology
`H₁(ℤ/2; 𝔽₂) = 𝔽₂ ≠ 0`, realized by the non-vanishing `zeroDifferentialComplex`.  Computed by `rfl`. -/
theorem zmod2_relationBoundary_zero :
    relationBoundaryF2 [false, false] [] = (false, false) := rfl

/-- ★ **⟨a, b | a = b⟩**: the relation `a = b` abelianizes to the NON-ZERO 𝔽₂ chain `a + b = (true, true)`
— a genuine non-trivial boundary computed from the presentation, whose image determines `H₁ = 𝔽₂` (the
homology of the presented monoid `≅ ℕ`).  Computed by `rfl`. -/
theorem aEqB_relationBoundary_nonzero :
    relationBoundaryF2 [false] [true] = (true, true) := rfl

/-! ## The abelianized chain complex of a finite presentation — in-framework homology

The free-standing `relationBoundaryF2` above is now WIRED into an actual `F2ChainComplex`: the
2-truncated abelianized resolution of a monoid presentation `⟨generators | relations⟩`.  Its chain
groups are `C₀` = the 0-cells (one object ⟹ the differential `∂₁` is zero), `C₁ = 𝔽₂[generators]`, and
`C₂ = 𝔽₂[relations]`; the degree-2 differential `∂₂` sends a relation to the 𝔽₂ difference of its two
sides (its abelianization).  `H₁ = C₁ / im ∂₂` is the abelianized monoid mod 2.  We BUILD the complex
and COMPUTE `H₁` for two genuine presentations (one vanishing, one not) — converting the disconnected
`relationBoundaryF2` computation above into actual homology inside the `F2ChainComplex` framework. -/

/-- A finite-dimensional **𝔽₂-module** as data (a carrier with the 𝔽₂ abelian-group structure): the
free 𝔽₂-module on a generating set, represented concretely (tuples of `Bool`) so equality is structural
and the laws close by `Bool` case analysis — no `funext`. -/
structure F2Module where
  /-- The underlying set of 𝔽₂-vectors. -/
  carrier : Type
  /-- The zero vector. -/
  zero : carrier
  /-- 𝔽₂ addition (componentwise XOR). -/
  add : carrier → carrier → carrier
  /-- `zero` is a right unit. -/
  add_zero : ∀ element, add element zero = element
  /-- 𝔽₂ self-inverse: `v + v = 0` (so subtraction is addition). -/
  add_self : ∀ element, add element element = zero

/-- The 1-dimensional 𝔽₂-module `𝔽₂` (one generator) — `Bool` under XOR. -/
def boolF2Module : F2Module where
  carrier := Bool
  zero := false
  add := Bool.xor
  add_zero := fun element => by cases element <;> rfl
  add_self := fun element => by cases element <;> rfl

/-- The 2-dimensional 𝔽₂-module `𝔽₂²` (two generators) — `Bool × Bool` under componentwise XOR. -/
def boolPairF2Module : F2Module where
  carrier := Bool × Bool
  zero := (false, false)
  add := fun first second => (Bool.xor first.1 second.1, Bool.xor first.2 second.2)
  add_zero := fun element => by obtain ⟨left, right⟩ := element; cases left <;> cases right <;> rfl
  add_self := fun element => by obtain ⟨left, right⟩ := element; cases left <;> cases right <;> rfl

/-- ★ **The abelianized chain complex of a 2-cell presentation** `⟨generators | relations⟩`: a genuine
`F2ChainComplex` with `C₀ = 𝔽₂[one object]` truncated to `Unit` (so `∂₁ = 0`), `C₁ = generators`,
`C₂ = relations`, higher chain groups `0`, and the degree-2 differential `∂₂ = differential` (a relation's
abelianized side-difference).  Every chain-complex law is discharged from the two module structures and
the additivity of `differential` — including `∂² = 0` (degree-1 instance is exactly `differential_zero`:
`∂₂(0) = 0`). -/
def presentationComplex (generators relations : F2Module)
    (differential : relations.carrier → generators.carrier)
    (differential_zero : differential relations.zero = generators.zero)
    (differential_add : ∀ first second,
      differential (relations.add first second)
        = generators.add (differential first) (differential second)) : F2ChainComplex where
  chain := fun dimension => match dimension with
    | 0 => Unit
    | 1 => generators.carrier
    | 2 => relations.carrier
    | _ + 3 => Unit
  zero := fun {dimension} => match dimension with
    | 0 => ()
    | 1 => generators.zero
    | 2 => relations.zero
    | _ + 3 => ()
  add := fun {dimension} => match dimension with
    | 0 => fun _ _ => ()
    | 1 => generators.add
    | 2 => relations.add
    | _ + 3 => fun _ _ => ()
  boundary := fun {dimension} => match dimension with
    | 0 => fun _ => ()
    | 1 => differential
    | 2 => fun _ => relations.zero
    | _ + 3 => fun _ => ()
  add_zero := fun {dimension} element => match dimension, element with
    | 0, _ => rfl
    | 1, element => generators.add_zero element
    | 2, element => relations.add_zero element
    | _ + 3, _ => rfl
  add_self := fun {dimension} element => match dimension, element with
    | 0, _ => rfl
    | 1, element => generators.add_self element
    | 2, element => relations.add_self element
    | _ + 3, _ => rfl
  boundary_zero := fun {dimension} => match dimension with
    | 0 => rfl
    | 1 => differential_zero
    | 2 => rfl
    | _ + 3 => rfl
  boundary_add := fun {dimension} first second => match dimension, first, second with
    | 0, _, _ => rfl
    | 1, first, second => differential_add first second
    | 2, _, _ => (relations.add_zero relations.zero).symm
    | _ + 3, _, _ => rfl
  boundary_squared_zero := fun {dimension} element => match dimension, element with
    | 0, _ => rfl
    | 1, _ => differential_zero
    | 2, _ => rfl
    | _ + 3, _ => rfl

/-- ★ **`H₁(ℕ; 𝔽₂) ≠ 0`** — the abelianized complex of `⟨a, b | a = b⟩` (presenting the free commutative
monoid `ℕ`).  `∂₂` sends the single relation to `a + b` (its abelianization), a NON-ZERO differential. -/
def monoidNComplex : F2ChainComplex :=
  presentationComplex boolPairF2Module boolF2Module
    (fun relation => (relation, relation)) rfl (fun _ _ => rfl)

/-- The degree-2 differential of `monoidNComplex` IS the abelianized relation boundary
`relationBoundaryF2 [false] [true] = a + b`: the free word-abelianization function and the actual complex
differential agree (`rfl`), wiring the standalone computation into the chain complex. -/
theorem monoidNComplex_degreeTwoBoundary_eq_relationBoundary :
    monoidNComplex.boundary (dimension := 1) true = relationBoundaryF2 [false] [true] :=
  rfl

/-- ★ **`monoidNComplex` has non-vanishing `H₁`.**  The chain `a` (`(true, false) ∈ C₁`) is a cycle
(`∂₁ = 0`) but NOT a boundary — `im ∂₂` is only the diagonal `{(false,false), (true,true)}` — so
`H₁ = C₁ / im ∂₂ ≅ 𝔽₂ ≠ 0`.  The first homology of a genuine monoid presentation, computed in-framework
with a non-zero differential. -/
theorem monoidNComplex_homologyNotVanishing :
    ¬ monoidNComplex.HomologyVanishes 0 := by
  intro homologyVanishes
  obtain ⟨source, hsource⟩ := homologyVanishes (true, false) rfl
  have hfst : source = true := congrArg Prod.fst hsource
  have hsnd : source = false := congrArg Prod.snd hsource
  exact Bool.noConfusion (hfst.symm.trans hsnd)

/-- ★ **`H₁ = 0` for the trivial monoid** — the abelianized complex of `⟨a | a = ε⟩` (presenting the
trivial monoid).  `∂₂` sends the relation to `a` (the identity differential, still NON-ZERO), so
`im ∂₂ = C₁` and `H₁ = C₁ / im ∂₂ = 0`: every cycle is a boundary.  The framework computes a VANISHING
presentation homology from a non-trivial differential — distinct from the all-`Unit` `trivialComplex`. -/
def trivialMonoidComplex : F2ChainComplex :=
  presentationComplex boolF2Module boolF2Module (fun relation => relation) rfl (fun _ _ => rfl)

/-- The trivial-monoid complex has VANISHING `H₁` — every degree-1 cycle is the boundary of itself
(`∂₂ = id`). -/
theorem trivialMonoidComplex_homologyVanishes :
    trivialMonoidComplex.HomologyVanishes 0 := by
  intro element _isCycle
  exact ⟨element, rfl⟩

end FX1Poly.Core

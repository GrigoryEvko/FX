import FX1Poly.Tier0.Term.Rewrite.SquierCoherence

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

HONEST SCOPE: the 𝔽₂ homology FRAMEWORK + the resolution's dim-2 acyclicity from `term-4`.  Deferred (the
`OHOM-1` #1261 capstone): the concrete polygraphic chain complex over the 205-generator table (the
abelianization of `fxKernelPolygraph`), integral (ℤ) homology, the higher (≥3) critical-triple cells, and
the homology-computes-coherence theorem (`Hₙ` of the term monoid).

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

end FX1Poly.Core

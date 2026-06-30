import FX1Poly.Polygraph.TwoCategory.GrayCategory

/-! # mode-6 — weak ω-categories: the Batanin–Leinster globular-operad presentation

`mode-0..5` built the mode theory dimension by dimension (modes, modalities, 2-cells, oriented 3-cells, the
Gray interchanger).  `mode-6` gives the UNIFORM all-dimensions substrate and the weak-coherence mechanism: the
Batanin–Leinster presentation of WEAK ω-CATEGORIES.

A weak ω-category (Batanin 1998, Leinster 2004) is an ALGEBRA for a CONTRACTIBLE GLOBULAR OPERAD.  The pieces:
GLOBULAR SETS (presheaves on the globe category `𝔾` — cells in every dimension with source/target maps
satisfying the globular identities); the free strict ω-category MONAD `T` on them (built from globular pasting
diagrams / Batanin trees); a globular OPERAD (an operad over `T`); and a CONTRACTION (Leinster) providing all
the coherence cells.

## What this file ships (each piece zero-axiom)

  * **`RawGlobularSet`** — THE foundational data: `cells : Nat → Type` with `source` / `target :
    cells (n+1) → cells n` satisfying the GLOBULAR IDENTITIES (`s∘s = s∘t`, `t∘s = t∘t`).  This is the underlying
    object of every GLOBULAR (Batanin–Leinster) ω-category — the all-dimensions generalisation of the MODE
    substrate's per-dimension cells (modes / modalities / 2-cells are globular).  It is NOT the kernel's general
    cell substrate, which is strictly more general — see the scope marker
    `fxMode_hasGeneralDirectedComplexCellShape`.
  * **`terminalGlobularSet`** / **`discreteGlobularSet`** — the terminal globular set (one cell per dimension)
    and the discrete one (a `Type` at dimension 0, nothing above) — genuine instances.
  * **`GlobularMap`** + `identity` / `compose` — morphisms of globular sets (commuting with source/target);
    globular sets form a category (`= PSh(𝔾)`).
  * **`RawGlobularSet.IsParallel`** + **`GlobularContraction`** — Leinster's CONTRACTION: for every PARALLEL
    pair of `n`-cells (same source, same target) a chosen `(n+1)`-cell filler between them.  This is the
    weak-coherence skeleton: any two parallel cells are linked by a higher cell.
  * **`ContractibleGlobularSet`** — a globular set together with a contraction; `terminalContractibleGlobularSet`
    realizes it.  The coherence half of a weak ω-category.

## What is DEFERRED (recorded by `= false` markers)

  * the free strict ω-category MONAD `T` on globular sets (globular pasting diagrams / Batanin trees / globular
    cardinals — the deep combinatorial core) and globular OPERADS over it
    (`hasFreeStrictOmegaMonadAndOperad = false`).
  * Leinster's INITIAL contractible globular operad `L` and its ALGEBRAS — which ARE the weak ω-categories, with
    their composition operations (`hasInitialContractibleOperadAlgebras = false`).
  * the strict ω-category instance + the strict ⟹ weak embedding (the degenerate contraction)
    (`hasStrictOmegaCategory = false`).

Zero external dependencies beyond the mode core.  Raw Lean 4 + Init.
-/

namespace FX1Poly.Tier0

/-! ## Globular sets -/

/-- A **globular set** — cells in every dimension with source/target maps satisfying the GLOBULAR IDENTITIES.
The underlying object of a GLOBULAR (Batanin–Leinster) ω-category: `cells 0` are objects, `cells 1` are
1-cells, etc.; `source`/`target`
take an `(n+1)`-cell to its boundary `n`-cells, and the globular laws say the boundary of a boundary is
well-defined (`s∘s = s∘t`, `t∘s = t∘t`).  This is `PSh(𝔾)` for the globe category `𝔾`, in presheaf-data form. -/
structure RawGlobularSet where
  /-- The cells of each dimension. -/
  cells : Nat → Type
  /-- The source boundary of an `(n+1)`-cell. -/
  source : {dim : Nat} → cells (dim + 1) → cells dim
  /-- The target boundary of an `(n+1)`-cell. -/
  target : {dim : Nat} → cells (dim + 1) → cells dim
  /-- Globular identity: the source of the source equals the source of the target. -/
  source_globular : ∀ {dim : Nat} (cell : cells (dim + 2)), source (source cell) = source (target cell)
  /-- Globular identity: the target of the source equals the target of the target. -/
  target_globular : ∀ {dim : Nat} (cell : cells (dim + 2)), target (source cell) = target (target cell)

/-- The **terminal globular set** — exactly one cell in every dimension.  The terminal object of `PSh(𝔾)`. -/
def terminalGlobularSet : RawGlobularSet where
  cells := fun _ => Unit
  source := fun _ => ()
  target := fun _ => ()
  source_globular := fun _ => rfl
  target_globular := fun _ => rfl

/-- The **discrete globular set** on a type — the type as `0`-cells, nothing in higher dimensions.  A `Type`
viewed as a `0`-truncated globular set (the modes of the mode theory form one). -/
def discreteGlobularSet (carrier : Type) : RawGlobularSet where
  cells := fun dim => match dim with | 0 => carrier | _ + 1 => Empty
  source := fun cell => Empty.elim cell
  target := fun cell => Empty.elim cell
  source_globular := fun cell => Empty.elim cell
  target_globular := fun cell => Empty.elim cell

/-! ## Morphisms of globular sets -/

/-- A **morphism of globular sets** — a map on cells in every dimension commuting with source and target.
With these globular sets form a category (`PSh(𝔾)`). -/
structure GlobularMap (domain codomain : RawGlobularSet) where
  /-- The action on cells of each dimension. -/
  onCells : {dim : Nat} → domain.cells dim → codomain.cells dim
  /-- Commutes with source. -/
  commutesSource : ∀ {dim : Nat} (cell : domain.cells (dim + 1)),
    onCells (domain.source cell) = codomain.source (onCells cell)
  /-- Commutes with target. -/
  commutesTarget : ∀ {dim : Nat} (cell : domain.cells (dim + 1)),
    onCells (domain.target cell) = codomain.target (onCells cell)

/-- The identity morphism of globular sets. -/
def GlobularMap.identity (globularSet : RawGlobularSet) : GlobularMap globularSet globularSet where
  onCells := fun cell => cell
  commutesSource := fun _ => rfl
  commutesTarget := fun _ => rfl

/-- Composition of globular-set morphisms (apply `first` then `second`); the commuting squares chain. -/
def GlobularMap.compose {globularSetA globularSetB globularSetC : RawGlobularSet}
    (first : GlobularMap globularSetA globularSetB) (second : GlobularMap globularSetB globularSetC) :
    GlobularMap globularSetA globularSetC where
  onCells := fun cell => second.onCells (first.onCells cell)
  commutesSource := fun cell => by
    rw [first.commutesSource, second.commutesSource]
  commutesTarget := fun cell => by
    rw [first.commutesTarget, second.commutesTarget]

/-! ## Contraction — the weak-coherence mechanism -/

/-- Two `n`-cells are **parallel** when they share source and target (vacuously for `0`-cells, which have no
boundary).  Parallelism is the boundary the contraction fills. -/
def RawGlobularSet.IsParallel (globularSet : RawGlobularSet) :
    {dim : Nat} → globularSet.cells dim → globularSet.cells dim → Prop
  | 0, _, _ => True
  | _ + 1, cellA, cellB =>
      globularSet.source cellA = globularSet.source cellB ∧ globularSet.target cellA = globularSet.target cellB

/-- A **contraction** (Leinster) on a globular set: for every PARALLEL pair of cells `a, b` a chosen filler
`(n+1)`-cell with source `a` and target `b`.  This is the heart of weak coherence — any two parallel cells are
connected by a higher cell, so all coherence (associators, unitors, the Gray interchanger of `mode-5`, …) is
provided rather than imposed strictly. -/
structure GlobularContraction (globularSet : RawGlobularSet) where
  /-- The filler cell for a parallel pair. -/
  filler : {dim : Nat} → (cellA cellB : globularSet.cells dim) →
    globularSet.IsParallel cellA cellB → globularSet.cells (dim + 1)
  /-- The filler's source is the first cell. -/
  fillerSource : ∀ {dim : Nat} (cellA cellB : globularSet.cells dim)
    (parallel : globularSet.IsParallel cellA cellB), globularSet.source (filler cellA cellB parallel) = cellA
  /-- The filler's target is the second cell. -/
  fillerTarget : ∀ {dim : Nat} (cellA cellB : globularSet.cells dim)
    (parallel : globularSet.IsParallel cellA cellB), globularSet.target (filler cellA cellB parallel) = cellB

/-- The terminal globular set is CONTRACTIBLE — every filler is the unique cell (`()`), source/target laws by
`Unit` eta.  The trivial contraction. -/
def terminalGlobularContraction : GlobularContraction terminalGlobularSet where
  filler := fun _ _ _ => ()
  fillerSource := fun _ _ _ => rfl
  fillerTarget := fun _ _ _ => rfl

/-- A **contractible globular set** — a globular set with a chosen contraction.  The coherence half of a weak
ω-category (the COMPOSITION half — the globular-operad algebra structure — is deferred; see the markers). -/
structure ContractibleGlobularSet where
  /-- The underlying globular set. -/
  globularSet : RawGlobularSet
  /-- The contraction providing all coherence fillers. -/
  contraction : GlobularContraction globularSet

/-- ★ The terminal globular set as a contractible globular set — the degenerate weak-coherence skeleton, and a
witness that `ContractibleGlobularSet` is inhabited. -/
def terminalContractibleGlobularSet : ContractibleGlobularSet where
  globularSet := terminalGlobularSet
  contraction := terminalGlobularContraction

/-! ## Honesty markers -/

/-- **Honesty marker.**  The free strict ω-category MONAD `T` on globular sets (globular pasting diagrams /
Batanin trees / globular cardinals — the deep combinatorial core) and globular OPERADS over it (an operad =
a `T`-collection with operad multiplication) are deferred.  `= false`. -/
def fxMode_hasFreeStrictOmegaMonadAndOperad : Bool := false

/-- **Honesty marker.**  Leinster's INITIAL contractible globular operad `L` and its ALGEBRAS — which ARE the
weak ω-categories, carrying the composition operations governed by `L` — are deferred (they need the operad
machinery above).  `= false`. -/
def fxMode_hasInitialContractibleOperadAlgebras : Bool := false

/-- **Honesty marker.**  The strict ω-category instance (the algebra for the terminal operad) and the strict ⟹
weak embedding (a strict ω-category is weak via the degenerate contraction) are deferred.  `= false`. -/
def fxMode_hasStrictOmegaCategory : Bool := false

/-- **Scope marker — globular is the MODE shape, NOT the kernel cell shape.**  `RawGlobularSet` is GLOBULAR,
which is the RIGHT foundation FOR THE MODE AXIS: a mode theory is a (strict→weak) globular `n`-category — modes
are 0-cells, modalities 1-cells, the `mode-3` 2-cells and the `mode-5` Gray interchanger are all globular-shaped
(every `k`-cell has ONE source and ONE target `(k-1)`-cell).  It is NOT the kernel's general CELL substrate.
The PolyCell kernel cells — `Generator` + `arity` / `binderShifts` / `payload` (presented by
`Generator.toPolygraphGenerator` as a boundary-carrying polygraph generator) over `RawTerm` / `RawCell` — are a
SECOND-ORDER (binding) POLYNOMIAL signature: a polynomial monad (polycell.md §3.2 — polynomial monads STRICTLY
GENERALIZE the globular T-polygraphs of ABGMMM §18.1) shaped over Hadzihasanovic REGULAR DIRECTED COMPLEXES
(polycell.md Axis 1, arXiv:2404.07273), of which the six classical shapes (globular / cubical / simplicial /
opetopic / Θ / Steiner) are all values of ONE inductive and globular is the most DEGENERATE special case.  A
kernel generator has an arbitrary `arity` (0–4 INPUTS, not one source + one target) and per-child binder shifts
(a globular set has no binding), so the kernel polygraph is non-groupoidal (polycell.md: "steps have
direction"), sort-stratified, and STRICTLY MORE GENERAL ("more powerful") than globular.  That general
directed-complex cell shape is Axis 1, deferred here; this file's globular sets are the mode-axis-specific shape
only.  `= false`. -/
def fxMode_hasGeneralDirectedComplexCellShape : Bool := false

end FX1Poly.Tier0

import LeanFX2.Foundation.PolyCell.Core.GeneratorSpec
/-!
# CellChildren — Heterogeneous Child Spines

`CellChildren` is the staged TCB.3 child layer.  It does not certify any raw
`PolyTerm` by itself.  Instead, it is parameterized by an abstract child
carrier and enforces that each child position has exactly the sort, dimension,
and shifted scope demanded by the generator metadata.

The later certified `PolyCell` layer will instantiate the child carrier with
actual certified cells.  Until then this file gives a small, non-recursive
spine with no semantic shortcuts and no invented cell inhabitants.
-/

namespace LeanFX2.Foundation.PolyCell.Core

universe u

namespace ChildSpec

/-- Scope expected for this child when the parent lives at `parentScope`. -/
def expectedScope (childSpec : ChildSpec) (parentScope : Nat) : Nat :=
  parentScope + childSpec.scopeShift

/-- Same-scope children compute back to the parent scope. -/
theorem expectedScope_sameScopeDimZero (parentScope : Nat)
    (cellSort : CellSort) :
    (ChildSpec.sameScopeDimZero cellSort).expectedScope parentScope =
      parentScope := by
  exact Nat.add_zero parentScope

/-- Bound children live at `parentScope + 1` by definition. -/
theorem expectedScope_boundDimZero (parentScope : Nat)
    (cellSort : CellSort) :
    (ChildSpec.boundDimZero cellSort).expectedScope parentScope =
      parentScope + 1 := rfl

/-- Carrier slot expected by one child spec at one parent scope. -/
def ExpectedCell
    (ChildCarrier : CellSort → CellDim → Nat → Type u)
    (childSpec : ChildSpec) (parentScope : Nat) : Type u :=
  ChildCarrier childSpec.cellSort childSpec.cellDimension
    (childSpec.expectedScope parentScope)

end ChildSpec

/-- Heterogeneous child list following a list of `ChildSpec` entries.

For each child spec, the constructor demands a child from `ChildCarrier` at
the exact `cellSort`, `cellDimension`, and `expectedScope` dictated by the
head spec.  This separates the polynomial child shape from the future
certified-cell boundary layer. -/
inductive CellChildren
    (ChildCarrier : CellSort → CellDim → Nat → Type u)
    (parentScope : Nat) : List ChildSpec → Type u where
  /-- Empty child spine for a nullary generator. -/
  | nil :
      CellChildren ChildCarrier parentScope []
  /-- Cons one child whose indices are dictated by the head spec. -/
  | cons {childSpec : ChildSpec} {remainingSpecs : List ChildSpec} :
      childSpec.ExpectedCell ChildCarrier parentScope →
      CellChildren ChildCarrier parentScope remainingSpecs →
      CellChildren ChildCarrier parentScope (childSpec :: remainingSpecs)

namespace CellChildren

/-- Child spine required by a generator's declared child metadata. -/
def ForGenerator
    (ChildCarrier : CellSort → CellDim → Nat → Type u)
    (parentScope : Nat) (generatorSpec : GeneratorSpec) : Type u :=
  CellChildren ChildCarrier parentScope generatorSpec.childSpecs

/-- Arity of a child spine, read from its metadata index. -/
def arity {ChildCarrier : CellSort → CellDim → Nat → Type u}
    {parentScope : Nat} {childSpecs : List ChildSpec}
    (_children : CellChildren ChildCarrier parentScope childSpecs) : Nat :=
  childSpecs.length

/-- Child-spine arity is exactly the length of its metadata index. -/
theorem arity_eq_length {ChildCarrier : CellSort → CellDim → Nat → Type u}
    {parentScope : Nat} {childSpecs : List ChildSpec}
    (children : CellChildren ChildCarrier parentScope childSpecs) :
    children.arity = childSpecs.length := rfl

/-- Generator child-spine arity is the generator's declared arity. -/
theorem arity_forGenerator_eq
    {ChildCarrier : CellSort → CellDim → Nat → Type u}
    {parentScope : Nat} {generatorSpec : GeneratorSpec}
    (children : ForGenerator ChildCarrier parentScope generatorSpec) :
    children.arity = generatorSpec.arity := rfl

variable {ChildCarrier : CellSort → CellDim → Nat → Type u}

/-- Build the child spine required by the lambda generator metadata. -/
def lambdaChildren {parentScope : Nat}
    (domainChild : ChildCarrier .type 0 parentScope)
    (bodyChild : ChildCarrier .term 0 (parentScope + 1)) :
    ForGenerator ChildCarrier parentScope lambdaGeneratorSpec :=
  .cons domainChild (.cons bodyChild .nil)

/-- Build the child spine required by the dependent-function type metadata. -/
def piTypeChildren {parentScope : Nat}
    (domainChild : ChildCarrier .type 0 parentScope)
    (codomainChild : ChildCarrier .type 0 (parentScope + 1)) :
    ForGenerator ChildCarrier parentScope piTypeGeneratorSpec :=
  .cons domainChild (.cons codomainChild .nil)

/-- Build the child spine required by the context-extension metadata. -/
def contextConsChildren {parentScope : Nat}
    (contextChild : ChildCarrier .context 0 parentScope)
    (typeChild : ChildCarrier .type 0 parentScope)
    (modeChild : ChildCarrier .mode 0 parentScope) :
    ForGenerator ChildCarrier parentScope contextConsGeneratorSpec :=
  .cons contextChild (.cons typeChild (.cons modeChild .nil))

/-- The lambda child builder carries the lambda generator's declared arity. -/
theorem lambdaChildren_arity_eq_generator {parentScope : Nat}
    (domainChild : ChildCarrier .type 0 parentScope)
    (bodyChild : ChildCarrier .term 0 (parentScope + 1)) :
    (lambdaChildren domainChild bodyChild).arity =
      lambdaGeneratorSpec.arity := rfl

/-- The dependent-function type child builder carries the generator's declared arity. -/
theorem piTypeChildren_arity_eq_generator {parentScope : Nat}
    (domainChild : ChildCarrier .type 0 parentScope)
    (codomainChild : ChildCarrier .type 0 (parentScope + 1)) :
    (piTypeChildren domainChild codomainChild).arity =
      piTypeGeneratorSpec.arity := rfl

/-- The context-extension child builder carries the generator's declared arity. -/
theorem contextConsChildren_arity_eq_generator {parentScope : Nat}
    (contextChild : ChildCarrier .context 0 parentScope)
    (typeChild : ChildCarrier .type 0 parentScope)
    (modeChild : ChildCarrier .mode 0 parentScope) :
    (contextConsChildren contextChild typeChild modeChild).arity =
      contextConsGeneratorSpec.arity := rfl

end CellChildren

end LeanFX2.Foundation.PolyCell.Core

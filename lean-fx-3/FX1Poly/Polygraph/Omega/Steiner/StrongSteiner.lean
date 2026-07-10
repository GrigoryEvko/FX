import FX1Poly.Polygraph.Steiner.ComputadLoopFree

/-! # Polygraph/Omega/Steiner/StrongSteiner — the admission predicate `isStrongSteiner` (OMEGA-2 r1, B1)

★ **THE INTERFACE LINE.**  `isStrongSteiner : AugmentedDirectedComplex → Bool` decides (a bounded
under-approximation of) the Ara-Guetta-Ozornova-Riehl characterization (arXiv:2204.12962) of the
strong-Steiner computads — the exact fragment where the ω-word-problem is decidable BY ARITHMETIC
(Steiner arXiv:math/0403237).  Recon JOB 3 correction: the predicate lives on the FLAT
`AugmentedDirectedComplex` (its `basisCount` / `boundaryMatrix` carry the finite decidable support
data), NOT on `OmegaComputad` (whose `genLabel` is an opaque `Type` with nothing to compute over).

## The decomposition (`isStronglyLoopFree` && `decideAtomicDirect`)

  * **`isStronglyLoopFreeUpTo` — the teeth.**  Acyclicity of the shipped same-dimension Steiner overlap
    order `sameDimensionOverlapOrder` (`Steiner/ComputadLoopFree.lean`), decided by bounded reachability
    over the boundary matrices (fuel = `basisCount`).  This is what REJECTS a support cycle: the walking
    adjunction's naive order has a `base -> tip -> base` 2-cycle (ComputadLoopFree docstring), exactly why
    Steiner's hypothesis has teeth.
  * **`decideAtomicDirect` — the direct-boundary atomicity conjunct.**  Per atom, per face, source and
    target support are disjoint at the immediate boundary (`entryIsSignPure`: a single Int entry cannot be
    both positive and negative).  This is a GENUINE AGOR conjunct but it is FREE — `entryIsSignPure_true`
    proves it always holds; the teeth are in loop-freeness.

## HONEST SCOPE (ledgered, not hidden)

The FULL AGOR predicate additionally requires the ITERATED-support atomicity (source/target of an atom
disjoint after iterating the boundary down to dimension 0) and Steiner UNITALITY (iterated source/target
stabilise into the basis).  Both need the full Steiner cell-table `⟨x⟩` construction, whose general
computation from the ADC is DEFERRED (`Steiner/CellCoordinates.lean:88` docstring) — the OMEGA-2 r3
completeness item.  So `isStrongSteiner` here is a SOUND UNDER-APPROXIMATION: it admits the
loop-free + direct-atomic complexes; the two deferred conjuncts can only shrink the admitted set, never
grow it, so an admitted complex stays admitted under refinement.  Cross-check anchors: the single-object
semiring complex (no overlap edge) is ADMITTED; a two-object support-CYCLE complex is REFUSED.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.ComputerAlgebra
open FX1Poly.Polygraph.Steiner

/-! ## Bounded Bool quantifiers over a finite index range -/

/-- `true` iff `predicate` holds at some index `< bound` — structural on `bound`, no `Fin`. -/
def anyIndexBelow : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | bound + 1, predicate => anyIndexBelow bound predicate || predicate bound

/-- `true` iff `predicate` holds at every index `< bound` — structural on `bound`. -/
def allIndexBelow : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | bound + 1, predicate => allIndexBelow bound predicate && predicate bound

/-! ## The sign test (source / target support membership) -/

/-- Is an integer entry nonzero? — structural on the `Int` constructors, no `Decidable`/`BEq`. -/
def isNonzeroInt : Int → Bool
  | Int.ofNat 0 => false
  | Int.ofNat (_ + 1) => true
  | Int.negSucc _ => true

/-! ## The same-dimension overlap edge, as a `Bool` -/

/-- **The Steiner `(odot)` overlap edge, decided.**  Two `(faceDim+1)`-atoms `aIndex (odot) bIndex` iff
some `faceDim`-face lies in `aIndex`'s TARGET (positive clamp of the boundary column) and in `bIndex`'s
SOURCE (negative clamp) — the `Bool` form of `sameDimensionOverlapOrder`. -/
def overlapEdgeBool (complex : AugmentedDirectedComplex) (faceDim aIndex bIndex : Nat) : Bool :=
  anyIndexBelow (complex.basisCount faceDim) (fun faceIndex =>
    isNonzeroInt (positiveClampEntry ((complex.boundaryMatrix faceDim).entryAt faceIndex aIndex))
    && isNonzeroInt (negativeClampEntry ((complex.boundaryMatrix faceDim).entryAt faceIndex bIndex)))

/-- **Bounded overlap reachability** — `target` reachable from `source` via `<= fuel` overlap edges,
structural on `fuel` (never `WellFounded.fix`).  A cycle through an atom is reachability from it to
itself with at least one edge (the `fuel = 0` base returns `false`, so a zero-length path is not a
cycle). -/
def overlapReachableWithin (complex : AugmentedDirectedComplex) (faceDim : Nat) :
    Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, source, target =>
      overlapEdgeBool complex faceDim source target
      || anyIndexBelow (complex.basisCount (faceDim + 1)) (fun middleIndex =>
           overlapEdgeBool complex faceDim source middleIndex
           && overlapReachableWithin complex faceDim fuel middleIndex target)

/-- **Some `(faceDim+1)`-atom lies on an overlap cycle** — reaches itself within `basisCount` steps. -/
def hasOverlapCycleAtFaceDim (complex : AugmentedDirectedComplex) (faceDim : Nat) : Bool :=
  anyIndexBelow (complex.basisCount (faceDim + 1)) (fun atomIndex =>
    overlapReachableWithin complex faceDim (complex.basisCount (faceDim + 1)) atomIndex atomIndex)

/-- ★ **The strong-loop-free conjunct** — no overlap cycle at any dimension below `dimensionBound`. -/
def isStronglyLoopFreeUpTo (complex : AugmentedDirectedComplex) (dimensionBound : Nat) : Bool :=
  allIndexBelow dimensionBound (fun faceDim => ! hasOverlapCycleAtFaceDim complex faceDim)

/-! ## The direct-boundary atomicity conjunct -/

/-- A single boundary entry is SIGN-PURE: its positive and negative clamps are not both nonzero — a
single `Int` cannot be both positive and negative.  The immediate-boundary atomicity test. -/
def entryIsSignPure (entry : Int) : Bool :=
  (! isNonzeroInt (positiveClampEntry entry)) || (! isNonzeroInt (negativeClampEntry entry))

/-- **Every integer entry is sign-pure** — the direct-atomicity conjunct is FREE (adds no rejection
power; the teeth are in loop-freeness).  Structural on the `Int` constructors. -/
theorem entryIsSignPure_true : (entry : Int) → entryIsSignPure entry = true
  | Int.ofNat 0 => rfl
  | Int.ofNat (_ + 1) => rfl
  | Int.negSucc _ => rfl

/-- ★ **The direct-boundary atomicity conjunct** — every generator's immediate source/target support is
disjoint (the genuine, direct AGOR atomicity; the iterated form is deferred, see the module ledger). -/
def decideAtomicDirect (complex : AugmentedDirectedComplex) (dimensionBound : Nat) : Bool :=
  allIndexBelow dimensionBound (fun faceDim =>
    allIndexBelow (complex.basisCount (faceDim + 1)) (fun atomIndex =>
      allIndexBelow (complex.basisCount faceDim) (fun faceIndex =>
        entryIsSignPure ((complex.boundaryMatrix faceDim).entryAt faceIndex atomIndex))))

/-! ## The admission predicate -/

/-- ★ **`isStrongSteiner` — the interface line.**  A complex is admitted iff it is strongly-loop-free
(no support cycle up to `dimensionBound`) and direct-atomic.  The decidable `Bool` split between the
arithmetic word-problem fragment (admitted) and the presented/undecidable fragment (refused). -/
def isStrongSteiner (complex : AugmentedDirectedComplex) (dimensionBound : Nat) : Bool :=
  isStronglyLoopFreeUpTo complex dimensionBound && decideAtomicDirect complex dimensionBound

/-! ## The negative cross-check — a two-object support-cycle complex (REFUSED) -/

/-- Basis of the cyclic complex: two 0-cells (objects), two 1-generators (`A : o0 -> o1`,
`B : o1 -> o0`), nothing higher. -/
def cyclicBasisCount : Nat → Nat
  | 0 => 2
  | 1 => 2
  | _ + 2 => 0

/-- Boundary matrices: `d0` is `[[-1, 1], [1, -1]]` (column 0 = `A`: source `o0`, target `o1`;
column 1 = `B`: source `o1`, target `o0`), so `A`'s target `o1` meets `B`'s source `o1` and `B`'s
target `o0` meets `A`'s source `o0` — a 2-cycle `A (odot) B (odot) A`.  `d1` is `2x0`, higher empty. -/
def cyclicBoundaryMatrix : Nat → IntMatrix
  | 0 => ⟨[[-1, 1], [1, -1]]⟩
  | 1 => ⟨[[], []]⟩
  | _ + 2 => ⟨[]⟩

/-- **The two-object support-cycle augmented directed complex.**  A genuine ADC (both chain
obligations hold — `d d = 0` is vacuous since `basisCount (dim+2) = 0`; `eps d = 0` cancels
column-wise for `eps = [1, 1]`), whose Steiner overlap order has the 2-cycle above. -/
def cyclicComplex : AugmentedDirectedComplex where
  basisCount := cyclicBasisCount
  boundaryMatrix := cyclicBoundaryMatrix
  augmentation := [1, 1]
  boundaryHasDimensions := fun dim =>
    match dim with
    | 0 => ⟨rfl, rfl, rfl, True.intro⟩
    | 1 => ⟨rfl, rfl, rfl, True.intro⟩
    | _ + 2 => ⟨rfl, True.intro⟩
  augmentationHasWidth := rfl
  boundaryComposesToZero := fun _ _ colIndex _ colBound =>
    absurd colBound (Nat.not_lt_zero colIndex)
  augmentationComposesToZero := fun colIndex colBound => by
    match colIndex with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 =>
        exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ colBound)) (Nat.not_lt_zero _)

/-! ## Non-vacuity cross-checks -/

/-- The single-object semiring complex is ADMITTED (no overlap edge, direct-atomic). -/
example : isStrongSteiner singleObjectSemiringComplex 3 = true := rfl

/-- ★ The two-object support-CYCLE complex is REFUSED (loop-freeness fails). -/
example : isStrongSteiner cyclicComplex 3 = false := rfl

/-- The refusal is specifically the loop-free conjunct (the direct-atomic conjunct passes). -/
example : isStronglyLoopFreeUpTo cyclicComplex 3 = false := rfl

/-- The direct-atomic conjunct passes on the cycle complex — the teeth are loop-freeness. -/
example : decideAtomicDirect cyclicComplex 3 = true := rfl

end FX1Poly.Polygraph.Omega

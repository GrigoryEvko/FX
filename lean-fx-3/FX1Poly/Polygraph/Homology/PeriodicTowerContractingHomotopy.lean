import FX1Poly.Polygraph.Homology.PeriodicTowerDiagonalChainMapGeneric
import FX1Poly.Polygraph.Homology.AnickTelescopeAugmentationAndMonomialFiniteness
import FX1Poly.Polygraph.Homology.HopfShadowCokerGroupIsoCertificate
import FX1Poly.ComputerAlgebra.Number.IntSubNatNat
import FX1Poly.ComputerAlgebra.Number.IntDistributivity
import FX1Poly.ComputerAlgebra.Number.IntNegation

/-! # FX1Poly/Polygraph/Homology/PeriodicTowerContractingHomotopy — the ASSEMBLED contracting homotopy
    `d s + s d = id` of the `ZZ/3` 2-periodic group-ring resolution, its all-degrees kernel-witness
    exactness (every kernel element receives an EXPLICIT boundary preimage), the augmentation
    exactness at degree 0, and the tensor tie certifying that `ZZ (X)_A -` of THIS resolution IS the
    shipped `PeriodicTowerChainComplex` boundary data (TOWER-ANICK / TOWER-PERIODIC exactness brick,
    #2144 / #2146 follow-on)

The shipped homology tower (`PeriodicTowerChainComplex`) computes `H0 = ZZ, H_odd = ZZ/3,
H_{even>0} = 0` from the TENSORED (`ZZ (X)_A -`, `A = ZZ[ZZ/3]`) boundary literals `[[0]]` / `[[-3]]`
— but nothing in-tree proved that the underlying A-MODULE complex those literals come from is a
genuine RESOLUTION (exact in positive degrees, augmentation-exact at 0).  Without that, the
all-degree read-offs are chain-complex arithmetic; with it, they are the group homology
`Tor_*^{ZZ[ZZ/3]}(ZZ, ZZ) = H_*(ZZ/3; ZZ)`.  The gap is the standing r4 named node
`anickResolutionExactnessIsNamedNode` ("it does NOT prove the complex is EXACT (that it computes
`Tor(k, k)`)") and the r5 assembly node `contractingHomotopyIngredientsPresentAssemblyNamedNode`
("A-module exactness needs a contracting homotopy `s` with `d s + s d = 1` ... the ASSEMBLY ... is
the deep wall").  THIS module supplies that assembly for the cyclic-3 periodic resolution.

## The math (compute first, state after)

`A = ZZ[ZZ/3] = ZZ[t]/(t^3 - 1)`, basis `{1, t, t^2}`.  The 2-periodic resolution of `ZZ` over `A`
(Brown, *Cohomology of Groups*, Ch. I par. 6):

  `... --N--> A --(t-1)--> A --N--> A --(t-1)--> A --eps--> ZZ --> 0`,  `N = 1 + t + t^2`.

The classical contracting homotopy is defined on the group basis and extended `ZZ`-LINEARLY
(NOT A-linearly — an A-linear homotopy would split the resolution over A and force `H_* = 0`,
contradicting the shipped `H_1 = ZZ/3`; `ZZ`-linearity is exactly what exactness of the underlying
complex needs, and the non-equivariance is machine-checked below as an honesty probe):

  `s_{-1} : ZZ -> W_0,    z ↦ z . 1`                                (the augmentation section)
  `s_even : W_even -> W_odd,   t^a ↦ 1 + t + ... + t^(a-1)`          (the partial norm; `1 ↦ 0`)
  `s_odd  : W_odd -> W_even,   t^2 ↦ 1,  t^a ↦ 0 (a < 2)`            (the top-power indicator)

The three homotopy identities, per basis element and hence per coefficient vector:

  degree 0:        `(t-1) . s_even(x) + s_{-1}(eps(x)) = x`
  odd degrees:     `N . s_odd(x) + s_even((t-1) . x) = x`
  even degrees>0:  `(t-1) . s_even(x) + s_odd(N . x) = x`   (definitionally THE SAME as degree 0,
                                                             since `s_odd(N x) = s_{-1}(eps x)` — the
                                                             2-periodicity of the homotopy itself)

Kernel-witness exactness follows: if `d x = 0` then `d(s x) = x` — an EXPLICIT preimage for every
kernel element, in every degree, constructively (no image/kernel set equality, no choice).

## What this module proves, zero-axiom

  * the dense `ZZ[ZZ/3]` carrier `CyclicThreeGroupRingElement` (three `Int` coefficients over the
    basis `{1, t, t^2}`) with the module maps `t .`, `(t-1) .`, `N .`, the augmentation, its
    section, and the two homotopy maps — all total, all structural;
  * ★★ the THREE HOMOTOPY IDENTITIES above, for EVERY coefficient vector (not only basis elements);
  * ★★ the ALL-DEGREES packaging over the tower's own `Nat` degree indexing (period-2 structural
    recursion, the shipped `degree + 2 ↦ degree` idiom): `d_{p+1} s_p + s_{p-1} d_p = id` on `W_p`
    for every `p >= 1`, plus the degree-0 identity with `s_{-1} eps`;
  * ★★ THE KERNEL-WITNESS EXACTNESS: `d_p x = 0  ==>  d_{p+1}(s_p x) = x` at EVERY positive degree,
    and `eps(x) = 0 ==> d_1(s_0 x) = x` at degree 0, plus `eps(s_{-1} z) = z` (surjectivity);
  * the complex facts on the module side: `d d = 0` at every degree and `eps d_1 = 0`;
  * ★ THE TENSOR TIE: `eps((t-1) . x) = entry(boundaryMatrix 0) * eps(x)` and
    `eps(N . x) = -(entry(boundaryMatrix 1)) * eps(x)` — the induced `ZZ (X)_A -` maps of THIS
    resolution are multiplication by `0` and by `3`, exactly the shipped tower literals (up to the
    documented seed sign `[[-3]]`), so the shipped tower IS the tensored image of a PROVEN resolution;
  * `ZZ`-linearity (additivity) certificates for the boundaries, the augmentation, and both homotopy
    maps; `t`-equivariance (A-linearity generator) for both boundary maps; and the honesty probe that
    the homotopy is NOT `t`-equivariant (as it must not be);
  * carrier bridges to the shipped Anick-telescope list carrier (`cyclicThreeGroupRingAugmentation`,
    `cyclicThreeNorm`, `cyclicThreeBoundaryElement`).

## What this DISCHARGES and what it does NOT (honest scope)

DISCHARGED (the cyclic-3 / periodic-tower INSTANCE): the contracting-homotopy ASSEMBLY the r5 node
`contractingHomotopyIngredientsPresentAssemblyNamedNode` names, and the resolution-exactness content
the r4 node `anickResolutionExactnessIsNamedNode` names — FOR THE `ZZ/3` PERIODIC RESOLUTION.  With
this brick the shipped all-degrees read-off `H0 = ZZ, H_odd = ZZ/3, H_{even>0} = 0` is the genuine
`Tor_*^{ZZ[ZZ/3]}(ZZ, ZZ)` of the presented monoid `ZZ/3`, not bare chain arithmetic; the tower's
graded-homology infinite-generation escape (`towerPeriodicHomologyLedgerIsComplete`) is now backed by
a proven resolution.  The committed marker Bools in the r4/r5 files are NOT edited (additive-only
discipline); the orchestrator reads the discharge from THIS file's markers.

NOT claimed (the walls stand): the MONOMIAL / Fibonacci Anick complex exactness (a different
combinatorial argument — `aModuleAnickDifferentialIsNamedNode` and the monomial side of the r4
exactness node stay walled); the generic-`n` periodic resolution homotopy (this brick is the
concrete `n = 3` instance; the generic partial-norm homotopy needs `List.range`-style indexed sums —
the documented propext minefield — and is a named residual); the Fox-derivative derivation of `N`
from `sss ⟹ id` (`normDifferentialFromRelationIsNamedNode` stays); Squier's `S_1` non-finiteness
(`carrierDegreeThreeChainIsAlwaysFinite` wall UNMOVED — exactness here legitimizes the tower's
homology, it does not produce infinite rank at one degree); and the chain-homotopy equivalence
between the Squier walker complex and this resolution (the shipped honest residual, unchanged).

## Zero-axiom design decisions

  * The carrier is a plain three-field `Int` record (non-indexed, no propext trap); every map is a
    record-builder, so projections reduce definitionally and most bridges close by `rfl`.
  * Every coefficient identity routes through the propext-clean kit: `intAddAssoc` / `intAddComm` /
    `intZeroAdd` / `intAddZero` (`IntArithmeticCore`), `intAddRightNeg` / `intAddLeftNeg`
    (`IntSubNatNat`), `intNegAdd` (`IntNegation`), `intRightDistrib` (`IntDistributivity`), and the
    shipped Homology-lane helpers `intSubSelf` / `intSubCancelChain` (diagonal kit),
    `intAddSubCancelLeft` / `intAddSwapMiddleLocal` (Hopf-shadow kit) — never Init `Int.*` lemmas.
  * Degree indexing is period-2 STRUCTURAL recursion (`dim + 2 ↦ dim`), the shipped tower idiom —
    no `WellFounded.fix`, no `omega`, no `decide`.
  * The non-equivariance probe refutes via a `Nat`-valued composite projection (`coeffAtUnit.toNat`)
    and `Nat.noConfusion` — no `decide`, no `Int` DecidableEq detour.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`, `decide`,
`WellFounded.fix`.  Per-declaration gated in
`FX1PolyAudit/Polygraph/Homology/PeriodicTowerContractingHomotopy.lean` with an independent
`#print axioms` cross-check in `…PeriodicTowerContractingHomotopyAxiomWitness.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## E1 — the small propext-clean `Int` cancellation kit (only what the lane does not already ship) -/

/-- `0 - value = -value` — subtraction from zero is negation. -/
theorem intZeroSub (value : Int) : 0 - value = -value :=
  (intSubEqAddNeg 0 value).trans (intZeroAdd (-value))

/-- `value - 0 = value` — subtracting zero is the identity. -/
theorem intSubZero (value : Int) : value - 0 = value :=
  (intSubEqAddNeg value 0).trans ((congrArg (value + ·) intNegZero).trans (intAddZero value))

/-- `(value + 0) + 0 = value` — the two-step right-zero collapse (the augmentation of a
`⟨value, 0, 0⟩` element). -/
theorem intAddZeroAddZero (value : Int) : (value + 0) + 0 = value :=
  (intAddZero (value + 0)).trans (intAddZero value)

/-- `(kept + dropped) - dropped = kept` — the right-addend cancellation. -/
theorem intAddSubCancel (keptValue droppedValue : Int) :
    (keptValue + droppedValue) - droppedValue = keptValue :=
  (intSubEqAddNeg (keptValue + droppedValue) droppedValue).trans
    ((intAddAssoc keptValue droppedValue (-droppedValue)).trans
      ((congrArg (keptValue + ·) (intAddRightNeg droppedValue)).trans (intAddZero keptValue)))

/-- `-cancelled + (kept + cancelled) = kept` — the wrap-around cancellation (the degree-0
identity's first component). -/
theorem intNegAddAddCancel (cancelledValue keptValue : Int) :
    -cancelledValue + (keptValue + cancelledValue) = keptValue :=
  (congrArg (-cancelledValue + ·) (intAddComm keptValue cancelledValue)).trans
    ((intAddAssoc (-cancelledValue) cancelledValue keptValue).symm.trans
      ((congrArg (· + keptValue) (intAddLeftNeg cancelledValue)).trans (intZeroAdd keptValue)))

/-- `(first + second) + third = (second + third) + first` — the three-summand rotation (the
`t`-equivariance of the norm map). -/
theorem intAddRotateLeft (firstValue secondValue thirdValue : Int) :
    (firstValue + secondValue) + thirdValue = (secondValue + thirdValue) + firstValue :=
  (intAddAssoc firstValue secondValue thirdValue).trans
    (intAddComm firstValue (secondValue + thirdValue))

/-- `(first + second) - (third + fourth) = (first - third) + (second - fourth)` — subtraction
distributes over the pairwise regrouping (the boundary-additivity component). -/
theorem intSubAddExchange (firstValue secondValue thirdValue fourthValue : Int) :
    (firstValue + secondValue) - (thirdValue + fourthValue)
      = (firstValue - thirdValue) + (secondValue - fourthValue) :=
  (intSubEqAddNeg (firstValue + secondValue) (thirdValue + fourthValue)).trans
    ((congrArg ((firstValue + secondValue) + ·) (intNegAdd thirdValue fourthValue)).trans
      ((intAddSwapMiddleLocal firstValue secondValue (-thirdValue) (-fourthValue)).trans
        ((congrArg (· + (secondValue + -fourthValue))
            (intSubEqAddNeg firstValue thirdValue).symm).trans
          (congrArg ((firstValue - thirdValue) + ·)
            (intSubEqAddNeg secondValue fourthValue).symm))))

/-- `3 * value = value + value + value` — the norm's tensored action is the triple sum (through
`intRightDistrib` on `3 = (2) + 1 = ((1) + 1) + 1`, then `intOneMul` three times). -/
theorem intThreeMulIsTripleSum (value : Int) :
    (3 : Int) * value = value + value + value :=
  (intRightDistrib 2 1 value).trans
    ((congrArg (· + 1 * value) (intRightDistrib 1 1 value)).trans
      ((congrArg (fun scaledValue => (scaledValue + 1 * value) + 1 * value)
          (intOneMul value)).trans
        ((congrArg (fun scaledValue => (value + scaledValue) + 1 * value)
            (intOneMul value)).trans
          (congrArg ((value + value) + ·) (intOneMul value)))))

/-! ## E2 — the dense `ZZ[ZZ/3]` carrier and the module maps -/

/-- **A `ZZ[ZZ/3]` group-ring element** in the dense basis `{1, t, t^2}` — three integer
coefficients.  The A-module carrier of every rank-1 free stage `W_p = A` of the 2-periodic
resolution.  Plain non-indexed record (propext-clean). -/
structure CyclicThreeGroupRingElement where
  /-- The coefficient of the group unit `1 = t^0`. -/
  coeffAtUnit : Int
  /-- The coefficient of the generator `t`. -/
  coeffAtT : Int
  /-- The coefficient of `t^2`. -/
  coeffAtTSquare : Int

/-- Record congruence from the three component equalities — the assembly step every componentwise
identity closes with. -/
theorem cyclicThreeElementCongr
    {unitLeft unitRight tLeft tRight squareLeft squareRight : Int}
    (unitAgree : unitLeft = unitRight) (tAgree : tLeft = tRight)
    (squareAgree : squareLeft = squareRight) :
    CyclicThreeGroupRingElement.mk unitLeft tLeft squareLeft
      = CyclicThreeGroupRingElement.mk unitRight tRight squareRight := by
  rw [unitAgree, tAgree, squareAgree]

/-- Componentwise addition of group-ring elements — the abelian-group structure of each stage. -/
def addCyclicThreeElements
    (leftElement rightElement : CyclicThreeGroupRingElement) : CyclicThreeGroupRingElement :=
  { coeffAtUnit := leftElement.coeffAtUnit + rightElement.coeffAtUnit
  , coeffAtT := leftElement.coeffAtT + rightElement.coeffAtT
  , coeffAtTSquare := leftElement.coeffAtTSquare + rightElement.coeffAtTSquare }

/-- The zero element. -/
def zeroCyclicThreeElement : CyclicThreeGroupRingElement :=
  { coeffAtUnit := 0, coeffAtT := 0, coeffAtTSquare := 0 }

/-- The group basis element `1 = t^0`. -/
def cyclicThreeBasisUnit : CyclicThreeGroupRingElement :=
  { coeffAtUnit := 1, coeffAtT := 0, coeffAtTSquare := 0 }

/-- **Multiplication by the generator `t`** — the cyclic coefficient rotation
`t . (c0 + c1 t + c2 t^2) = c2 + c0 t + c1 t^2`. -/
def cyclicThreeMultiplyByT (element : CyclicThreeGroupRingElement) : CyclicThreeGroupRingElement :=
  { coeffAtUnit := element.coeffAtTSquare
  , coeffAtT := element.coeffAtUnit
  , coeffAtTSquare := element.coeffAtT }

/-- **The odd-index boundary: multiplication by `t - 1`** (the map `d_{2i+1} : W_{2i+1} -> W_{2i}`
of the resolution; tensors to the shipped `[[0]]`). -/
def cyclicThreeMultiplyByTMinusOne
    (element : CyclicThreeGroupRingElement) : CyclicThreeGroupRingElement :=
  { coeffAtUnit := element.coeffAtTSquare - element.coeffAtUnit
  , coeffAtT := element.coeffAtUnit - element.coeffAtT
  , coeffAtTSquare := element.coeffAtT - element.coeffAtTSquare }

/-- **The augmentation `eps : A -> ZZ`, `t ↦ 1`** — the coefficient sum.  The `ZZ (X)_A -` reading
of an element (matches the shipped list-carrier `cyclicThreeGroupRingAugmentation`, bridged below). -/
def cyclicThreeElementAugmentation (element : CyclicThreeGroupRingElement) : Int :=
  element.coeffAtUnit + element.coeffAtT + element.coeffAtTSquare

/-- **The even-index boundary: multiplication by the norm `N = 1 + t + t^2`** (the map
`d_{2i+2} : W_{2i+2} -> W_{2i+1}`; tensors to multiplication by `3`, the shipped `[[-3]]` up to the
documented seed sign).  `N . x = eps(x) . N` since `t . N = N`. -/
def cyclicThreeMultiplyByNorm
    (element : CyclicThreeGroupRingElement) : CyclicThreeGroupRingElement :=
  { coeffAtUnit := cyclicThreeElementAugmentation element
  , coeffAtT := cyclicThreeElementAugmentation element
  , coeffAtTSquare := cyclicThreeElementAugmentation element }

/-- **The augmentation section `s_{-1} : ZZ -> W_0`, `z ↦ z . 1`** — the degree `-1` leg of the
contracting homotopy; `eps ∘ s_{-1} = id` (below). -/
def cyclicThreeAugmentationSection (value : Int) : CyclicThreeGroupRingElement :=
  { coeffAtUnit := value, coeffAtT := 0, coeffAtTSquare := 0 }

/-- **The even-degree homotopy leg `s_even : W_even -> W_odd`** — the partial norm
`t^a ↦ 1 + t + ... + t^(a-1)` (`1 ↦ 0`, `t ↦ 1`, `t^2 ↦ 1 + t`), extended `ZZ`-linearly:
`x ↦ (c1 + c2) + c2 t`.  `ZZ`-linear, deliberately NOT A-linear (the honesty probe below). -/
def cyclicThreeHomotopyEvenToOdd
    (element : CyclicThreeGroupRingElement) : CyclicThreeGroupRingElement :=
  { coeffAtUnit := element.coeffAtT + element.coeffAtTSquare
  , coeffAtT := element.coeffAtTSquare
  , coeffAtTSquare := 0 }

/-- **The odd-degree homotopy leg `s_odd : W_odd -> W_even`** — the top-power indicator
`t^2 ↦ 1`, `t^a ↦ 0 (a < 2)`, extended `ZZ`-linearly: `x ↦ c2 . 1`. -/
def cyclicThreeHomotopyOddToEven
    (element : CyclicThreeGroupRingElement) : CyclicThreeGroupRingElement :=
  { coeffAtUnit := element.coeffAtTSquare, coeffAtT := 0, coeffAtTSquare := 0 }

/-! ## E3 — the three homotopy identities `d s + s d = id` (per coefficient vector, all of `A`) -/

/-- ★★ **THE DEGREE-0 HOMOTOPY IDENTITY** — `(t-1) . s_even(x) + s_{-1}(eps(x)) = x` for EVERY
group-ring element `x`.  The augmentation-exactness engine at the resolution's bottom. -/
theorem cyclicThreeHomotopyIdentityAtDegreeZero :
    ∀ element : CyclicThreeGroupRingElement,
      addCyclicThreeElements
        (cyclicThreeMultiplyByTMinusOne (cyclicThreeHomotopyEvenToOdd element))
        (cyclicThreeAugmentationSection (cyclicThreeElementAugmentation element))
        = element
  | ⟨unitCoeff, tCoeff, squareCoeff⟩ =>
      cyclicThreeElementCongr
        ((congrArg (· + ((unitCoeff + tCoeff) + squareCoeff))
            (intZeroSub (tCoeff + squareCoeff))).trans
          ((congrArg (-(tCoeff + squareCoeff) + ·)
              (intAddAssoc unitCoeff tCoeff squareCoeff)).trans
            (intNegAddAddCancel (tCoeff + squareCoeff) unitCoeff)))
        ((intAddZero ((tCoeff + squareCoeff) - squareCoeff)).trans
          (intAddSubCancel tCoeff squareCoeff))
        ((intAddZero (squareCoeff - 0)).trans (intSubZero squareCoeff))

/-- ★★ **THE ODD-DEGREE HOMOTOPY IDENTITY** — `N . s_odd(x) + s_even((t-1) . x) = x` for EVERY
group-ring element `x`.  The identity on every `W_{2i+1}`. -/
theorem cyclicThreeHomotopyIdentityAtOddDegree :
    ∀ element : CyclicThreeGroupRingElement,
      addCyclicThreeElements
        (cyclicThreeMultiplyByNorm (cyclicThreeHomotopyOddToEven element))
        (cyclicThreeHomotopyEvenToOdd (cyclicThreeMultiplyByTMinusOne element))
        = element
  | ⟨unitCoeff, tCoeff, squareCoeff⟩ =>
      cyclicThreeElementCongr
        ((congrArg (· + ((unitCoeff - tCoeff) + (tCoeff - squareCoeff)))
            (intAddZeroAddZero squareCoeff)).trans
          ((congrArg (squareCoeff + ·)
              (intSubCancelChain unitCoeff tCoeff squareCoeff)).trans
            (intAddSubCancelLeft squareCoeff unitCoeff)))
        ((congrArg (· + (tCoeff - squareCoeff)) (intAddZeroAddZero squareCoeff)).trans
          (intAddSubCancelLeft squareCoeff tCoeff))
        ((intAddZero ((squareCoeff + 0) + 0)).trans (intAddZeroAddZero squareCoeff))

/-- **The homotopy is 2-periodic at the seam** — `s_odd(N . x) = s_{-1}(eps(x))`: the odd homotopy
leg applied to a norm boundary IS the augmentation section of the augmentation.  Definitional. -/
theorem cyclicThreeHomotopyOfNormIsAugmentationSection
    (element : CyclicThreeGroupRingElement) :
    cyclicThreeHomotopyOddToEven (cyclicThreeMultiplyByNorm element)
      = cyclicThreeAugmentationSection (cyclicThreeElementAugmentation element) := rfl

/-- ★★ **THE EVEN-POSITIVE-DEGREE HOMOTOPY IDENTITY** — `(t-1) . s_even(x) + s_odd(N . x) = x` for
EVERY group-ring element `x`.  The identity on every `W_{2i+2}`; by the seam periodicity it IS the
degree-0 identity (the homotopy's own 2-periodicity). -/
theorem cyclicThreeHomotopyIdentityAtEvenPositiveDegree
    (element : CyclicThreeGroupRingElement) :
    addCyclicThreeElements
      (cyclicThreeMultiplyByTMinusOne (cyclicThreeHomotopyEvenToOdd element))
      (cyclicThreeHomotopyOddToEven (cyclicThreeMultiplyByNorm element))
      = element :=
  cyclicThreeHomotopyIdentityAtDegreeZero element

/-! ## E4 — the all-degrees packaging over the tower's `Nat` degree indexing

The resolution boundary at ADC index `dim` is `d_{dim+1} : W_{dim+1} -> W_dim` (matching the shipped
`boundaryMatrix dim = d_{dim+1}` convention): `t - 1` at even `dim`, `N` at odd `dim`.  The homotopy
at index `dim` is `s_dim : W_dim -> W_{dim+1}`: `s_even` at even `dim`, `s_odd` at odd `dim`.
Period-2 structural recursion (`dim + 2 ↦ dim`), the shipped tower idiom. -/

/-- **The resolution boundary action at ADC index `dim`** — the module map whose `ZZ (X)_A -` image
is the shipped `boundaryMatrix dim` (tensor tie below): `t - 1` at even index, `N` at odd. -/
def cyclicThreeResolutionBoundaryAction :
    Nat → CyclicThreeGroupRingElement → CyclicThreeGroupRingElement
  | 0 => cyclicThreeMultiplyByTMinusOne
  | 1 => cyclicThreeMultiplyByNorm
  | dim + 2 => cyclicThreeResolutionBoundaryAction dim

/-- **The contracting homotopy at index `dim`** (`s_dim : W_dim -> W_{dim+1}`): the partial-norm leg
at even index, the top-power-indicator leg at odd. -/
def cyclicThreeContractingHomotopyAction :
    Nat → CyclicThreeGroupRingElement → CyclicThreeGroupRingElement
  | 0 => cyclicThreeHomotopyEvenToOdd
  | 1 => cyclicThreeHomotopyOddToEven
  | dim + 2 => cyclicThreeContractingHomotopyAction dim

/-- ★★ **`d s + s d = id` AT EVERY POSITIVE DEGREE** — on `W_{dim+1}` (all `dim`):
`d_{dim+2}(s_{dim+1} x) + s_dim(d_{dim+1} x) = x`.  Period-2 structural recursion: the base cases
are the odd-degree and even-positive-degree identities; the step is the definitional period
collapse.  THE assembled contracting homotopy, all infinitely many degrees from the two parity
identities — the same finite-check-to-infinite-conclusion shape as the shipped tower's `d d = 0`. -/
theorem cyclicThreeContractingHomotopyIdentityAtEveryPositiveDegree :
    ∀ (dim : Nat) (element : CyclicThreeGroupRingElement),
      addCyclicThreeElements
        (cyclicThreeResolutionBoundaryAction (dim + 1)
          (cyclicThreeContractingHomotopyAction (dim + 1) element))
        (cyclicThreeContractingHomotopyAction dim
          (cyclicThreeResolutionBoundaryAction dim element))
        = element
  | 0, element => cyclicThreeHomotopyIdentityAtOddDegree element
  | 1, element => cyclicThreeHomotopyIdentityAtEvenPositiveDegree element
  | dim + 2, element =>
      cyclicThreeContractingHomotopyIdentityAtEveryPositiveDegree dim element

/-! ## E5 — kernel-witness exactness (the constructive `im = ker`, every degree) -/

/-- Adding the zero element on the right is the identity. -/
theorem addCyclicThreeElementsZeroRight :
    ∀ element : CyclicThreeGroupRingElement,
      addCyclicThreeElements element zeroCyclicThreeElement = element
  | ⟨unitCoeff, tCoeff, squareCoeff⟩ =>
      cyclicThreeElementCongr (intAddZero unitCoeff) (intAddZero tCoeff) (intAddZero squareCoeff)

/-- The homotopy annihilates the zero element at every index (period-2 recursion; each base arm is
definitional). -/
theorem cyclicThreeContractingHomotopyOfZeroIsZero :
    ∀ dim : Nat,
      cyclicThreeContractingHomotopyAction dim zeroCyclicThreeElement = zeroCyclicThreeElement
  | 0 => rfl
  | 1 => rfl
  | dim + 2 => cyclicThreeContractingHomotopyOfZeroIsZero dim

/-- ★★ **THE KERNEL WITNESS AT EVERY POSITIVE DEGREE** — if `x ∈ W_{dim+1}` is a cycle
(`d_{dim+1} x = 0`) then `s_{dim+1} x` is an EXPLICIT boundary preimage: `d_{dim+2}(s_{dim+1} x) = x`.
Constructive `im d_{dim+2} ⊇ ker d_{dim+1}` with a computable witness function (the converse
inclusion is `d d = 0` below) — resolution exactness in witness form, no set equality, no choice. -/
theorem cyclicThreeResolutionKernelWitnessAtEveryPositiveDegree
    (dim : Nat) (element : CyclicThreeGroupRingElement)
    (isCycle : cyclicThreeResolutionBoundaryAction dim element = zeroCyclicThreeElement) :
    cyclicThreeResolutionBoundaryAction (dim + 1)
      (cyclicThreeContractingHomotopyAction (dim + 1) element) = element := by
  have homotopyIdentity :=
    cyclicThreeContractingHomotopyIdentityAtEveryPositiveDegree dim element
  rw [isCycle, cyclicThreeContractingHomotopyOfZeroIsZero dim] at homotopyIdentity
  exact (addCyclicThreeElementsZeroRight
    (cyclicThreeResolutionBoundaryAction (dim + 1)
      (cyclicThreeContractingHomotopyAction (dim + 1) element))).symm.trans homotopyIdentity

/-- ★★ **AUGMENTATION EXACTNESS AT DEGREE 0** — if `eps(x) = 0` then `s_0 x` is an explicit
`d_1`-preimage: `(t-1) . s_even(x) = x`.  Constructive `im d_1 ⊇ ker eps` (the converse is
`eps ∘ d_1 = 0` below). -/
theorem cyclicThreeAugmentationKernelWitness
    (element : CyclicThreeGroupRingElement)
    (augmentationVanishes : cyclicThreeElementAugmentation element = 0) :
    cyclicThreeMultiplyByTMinusOne (cyclicThreeHomotopyEvenToOdd element) = element := by
  have homotopyIdentity := cyclicThreeHomotopyIdentityAtDegreeZero element
  rw [augmentationVanishes] at homotopyIdentity
  exact (addCyclicThreeElementsZeroRight
    (cyclicThreeMultiplyByTMinusOne (cyclicThreeHomotopyEvenToOdd element))).symm.trans
    homotopyIdentity

/-- ★ **The augmentation SPLITS** — `eps(s_{-1}(z)) = z` for every integer: `eps` is surjective with
the explicit section.  Exactness of `W_0 --eps--> ZZ --> 0`. -/
theorem cyclicThreeAugmentationSectionSplits (value : Int) :
    cyclicThreeElementAugmentation (cyclicThreeAugmentationSection value) = value :=
  intAddZeroAddZero value

/-! ### E5b — non-vacuity: the kernel witness COMPUTES on concrete nonzero cycles

Two concrete NONZERO cycles, one per boundary parity, the second at a DEEP degree (`W_8`, four
period-2 recursion steps): the general kernel-witness theorem instantiates on each with an
`rfl`-discharged cycle hypothesis, and the resulting preimage equation ALSO closes by pure
definitional computation — the witness function genuinely computes, nothing is vacuous. -/

/-- **The degree-1 cycle probe `⟨1, 1, 1⟩ = N . 1 ∈ W_1`** — a nonzero `d_1`-cycle
(`(t-1) . ⟨1,1,1⟩ = 0`, the constants are exactly the `t-1` kernel). -/
def cyclicThreeNormCycleProbe : CyclicThreeGroupRingElement :=
  { coeffAtUnit := 1, coeffAtT := 1, coeffAtTSquare := 1 }

/-- The degree-1 probe is NONZERO (via the `toNat` composite projection and `Nat.noConfusion` —
no `decide`, no `Int` DecidableEq). -/
theorem cyclicThreeNormCycleProbeIsNonzero :
    cyclicThreeNormCycleProbe ≠ zeroCyclicThreeElement :=
  fun probeWereZero =>
    Nat.noConfusion
      (congrArg (fun element => element.coeffAtUnit.toNat) probeWereZero : (1 : Nat) = 0)

/-- The degree-1 probe IS a `d_1`-cycle.  Definitional. -/
theorem cyclicThreeNormCycleProbeIsCycle :
    cyclicThreeResolutionBoundaryAction 0 cyclicThreeNormCycleProbe
      = zeroCyclicThreeElement := rfl

/-- ★ **The kernel witness on the degree-1 probe, via the GENERAL theorem** — the all-degrees
kernel-witness theorem instantiated at `dim = 0` on the nonzero cycle `⟨1,1,1⟩`: the explicit
preimage is `s_1(⟨1,1,1⟩) = ⟨1,0,0⟩` and `d_2(⟨1,0,0⟩) = N . 1 = ⟨1,1,1⟩` — the cycle is recovered
exactly. -/
theorem cyclicThreeNormCycleProbeReceivesWitness :
    cyclicThreeResolutionBoundaryAction 1
      (cyclicThreeContractingHomotopyAction 1 cyclicThreeNormCycleProbe)
      = cyclicThreeNormCycleProbe :=
  cyclicThreeResolutionKernelWitnessAtEveryPositiveDegree 0 cyclicThreeNormCycleProbe rfl

/-- **The deep-degree cycle probe `⟨-1, 1, 0⟩ = (t-1) . 1 ∈ W_8`** — the shipped boundary-element
vector, a nonzero `d_8`-cycle at EVEN degree 8 (`d_8 = N` at ADC index 7; `N . ⟨-1,1,0⟩ = 0` since
the coefficients augment to zero). -/
def cyclicThreeDeepDegreeCycleProbe : CyclicThreeGroupRingElement :=
  { coeffAtUnit := -1, coeffAtT := 1, coeffAtTSquare := 0 }

/-- The deep-degree probe is NONZERO (the `coeffAtT.toNat` projection separates it from zero). -/
theorem cyclicThreeDeepDegreeCycleProbeIsNonzero :
    cyclicThreeDeepDegreeCycleProbe ≠ zeroCyclicThreeElement :=
  fun probeWereZero =>
    Nat.noConfusion
      (congrArg (fun element => element.coeffAtT.toNat) probeWereZero : (1 : Nat) = 0)

/-- The deep-degree probe IS a `d_8`-cycle — the ADC-index-7 boundary (norm, through THREE period-2
recursion steps `7 → 5 → 3 → 1`) kills it.  Definitional. -/
theorem cyclicThreeDeepDegreeCycleProbeIsCycle :
    cyclicThreeResolutionBoundaryAction 7 cyclicThreeDeepDegreeCycleProbe
      = zeroCyclicThreeElement := rfl

/-- ★ **The kernel witness at DEEP degree, via the GENERAL theorem** — instantiated at `dim = 7`
on the nonzero cycle `⟨-1,1,0⟩ ∈ W_8`: the explicit preimage is `s_8(⟨-1,1,0⟩) = ⟨1,0,0⟩` and
`d_9(⟨1,0,0⟩) = (t-1) . 1 = ⟨-1,1,0⟩` — four levels of the period-2 recursion compute through. -/
theorem cyclicThreeDeepDegreeCycleProbeReceivesWitness :
    cyclicThreeResolutionBoundaryAction 8
      (cyclicThreeContractingHomotopyAction 8 cyclicThreeDeepDegreeCycleProbe)
      = cyclicThreeDeepDegreeCycleProbe :=
  cyclicThreeResolutionKernelWitnessAtEveryPositiveDegree 7 cyclicThreeDeepDegreeCycleProbe rfl

/-- ★ **The deep-degree witness equation closes by PURE DEFINITIONAL COMPUTATION** — the same
statement as `cyclicThreeDeepDegreeCycleProbeReceivesWitness`, proven by `rfl` alone: the preimage
is not merely proven to exist, it numerically EVALUATES through the degree recursion (no `decide`,
no tactic). -/
theorem cyclicThreeDeepDegreeCycleProbeWitnessComputes :
    cyclicThreeResolutionBoundaryAction 8
      (cyclicThreeContractingHomotopyAction 8 cyclicThreeDeepDegreeCycleProbe)
      = cyclicThreeDeepDegreeCycleProbe := rfl

/-! ## E6 — the complex facts on the module side (`d d = 0`, `eps d_1 = 0`) -/

/-- **`eps ∘ (t-1) = 0`** — the augmentation kills every `d_1`-boundary (the telescope
`(s-u) + (u-t) + (t-s) = 0`).  Also the `ZZ (X)_A -` collapse of the odd boundary. -/
theorem cyclicThreeAugmentationKillsBoundary :
    ∀ element : CyclicThreeGroupRingElement,
      cyclicThreeElementAugmentation (cyclicThreeMultiplyByTMinusOne element) = 0
  | ⟨unitCoeff, tCoeff, squareCoeff⟩ =>
      (congrArg (· + (tCoeff - squareCoeff))
          (intSubCancelChain squareCoeff unitCoeff tCoeff)).trans
        ((intSubCancelChain squareCoeff tCoeff squareCoeff).trans (intSubSelf squareCoeff))

/-- ★ **`d d = 0` at every degree, on the A-MODULE side** — `(t-1) ∘ N = 0` (constant vectors die
under `t - 1`) and `N ∘ (t-1) = 0` (boundaries augment to zero), packaged over the degree indexing
by period-2 recursion.  The module-level source of the shipped tower's windowed `d d = 0`. -/
theorem cyclicThreeResolutionBoundaryComposesToZero :
    ∀ (dim : Nat) (element : CyclicThreeGroupRingElement),
      cyclicThreeResolutionBoundaryAction dim
        (cyclicThreeResolutionBoundaryAction (dim + 1) element) = zeroCyclicThreeElement
  | 0, element =>
      cyclicThreeElementCongr
        (intSubSelf (cyclicThreeElementAugmentation element))
        (intSubSelf (cyclicThreeElementAugmentation element))
        (intSubSelf (cyclicThreeElementAugmentation element))
  | 1, element =>
      cyclicThreeElementCongr
        (cyclicThreeAugmentationKillsBoundary element)
        (cyclicThreeAugmentationKillsBoundary element)
        (cyclicThreeAugmentationKillsBoundary element)
  | dim + 2, element => cyclicThreeResolutionBoundaryComposesToZero dim element

/-! ## E7 — the tensor tie: `ZZ (X)_A -` of THIS resolution IS the shipped tower

For a rank-1 free `A`-module stage, tensoring a multiplication-by-`r` map down to `ZZ` gives
multiplication by `eps(r)`.  The two theorems below compute the induced maps of the two resolution
boundaries and pin them to the SHIPPED tower literals: the even-index boundary induces `0 . -`
(the shipped `[[0]]` entry) and the odd-index boundary induces `3 . -` = `-(-3) . -` (the shipped
`[[-3]]` entry up to the documented cyclic-seed sign).  Together with E3–E6 this certifies: the
shipped `PeriodicTowerChainComplex` is the `ZZ (X)_A -` image of a PROVEN resolution of `ZZ` over
`ZZ[ZZ/3]`, hence its all-degrees homology read-off is `Tor_*^{ZZ[ZZ/3]}(ZZ, ZZ) = H_*(ZZ/3; ZZ)`. -/

/-- ★★ **The even-index boundary tensors to the shipped `[[0]]`** —
`eps((t-1) . x) = entry(boundaryMatrix 0) * eps(x)` (the entry is `0`, definitionally). -/
theorem cyclicThreeEvenBoundaryTensorsToShippedEntry (element : CyclicThreeGroupRingElement) :
    cyclicThreeElementAugmentation (cyclicThreeMultiplyByTMinusOne element)
      = (cyclicThreePeriodicTower.boundaryMatrix 0).entryAt 0 0
          * cyclicThreeElementAugmentation element :=
  (cyclicThreeAugmentationKillsBoundary element).trans
    (intZeroMul (cyclicThreeElementAugmentation element)).symm

/-- ★★ **The odd-index boundary tensors to the shipped `[[-3]]` (up to the documented seed sign)** —
`eps(N . x) = -(entry(boundaryMatrix 1)) * eps(x)` (the entry is `-3`, so the induced map is
multiplication by `3`; the sign is the shipped tower's cyclic-seed convention, recorded in its
header and in `cyclicThreeTelescopeAugmentsToTowerEntries`). -/
theorem cyclicThreeOddBoundaryTensorsToShippedEntry (element : CyclicThreeGroupRingElement) :
    cyclicThreeElementAugmentation (cyclicThreeMultiplyByNorm element)
      = -((cyclicThreePeriodicTower.boundaryMatrix 1).entryAt 0 0)
          * cyclicThreeElementAugmentation element :=
  (intThreeMulIsTripleSum (cyclicThreeElementAugmentation element)).symm

/-- **The carrier bridge to the shipped Anick-telescope list augmentation** — the record
augmentation equals `cyclicThreeGroupRingAugmentation` on the corresponding coefficient list. -/
theorem cyclicThreeElementAugmentationMatchesListAugmentation :
    ∀ element : CyclicThreeGroupRingElement,
      cyclicThreeElementAugmentation element
        = cyclicThreeGroupRingAugmentation
            [element.coeffAtUnit, element.coeffAtT, element.coeffAtTSquare]
  | ⟨unitCoeff, tCoeff, squareCoeff⟩ =>
      (intAddAssoc unitCoeff tCoeff squareCoeff).trans
        (congrArg (unitCoeff + ·)
          (congrArg (tCoeff + ·) (intAddZero squareCoeff).symm))

/-- ★ **Probe: `N . 1` IS the shipped norm vector** — the norm map on the basis unit produces
`⟨1, 1, 1⟩`, the record form of the shipped `cyclicThreeNorm = [1, 1, 1]`. `rfl`. -/
theorem cyclicThreeNormOnBasisUnitIsShippedNorm :
    [(cyclicThreeMultiplyByNorm cyclicThreeBasisUnit).coeffAtUnit,
     (cyclicThreeMultiplyByNorm cyclicThreeBasisUnit).coeffAtT,
     (cyclicThreeMultiplyByNorm cyclicThreeBasisUnit).coeffAtTSquare] = cyclicThreeNorm := rfl

/-- ★ **Probe: `(t-1) . 1` IS the shipped boundary element** — the odd-index boundary on the basis
unit produces `⟨-1, 1, 0⟩`, the record form of the shipped `cyclicThreeBoundaryElement =
[-1, 1, 0]`. `rfl`. -/
theorem cyclicThreeBoundaryOnBasisUnitIsShippedBoundaryElement :
    [(cyclicThreeMultiplyByTMinusOne cyclicThreeBasisUnit).coeffAtUnit,
     (cyclicThreeMultiplyByTMinusOne cyclicThreeBasisUnit).coeffAtT,
     (cyclicThreeMultiplyByTMinusOne cyclicThreeBasisUnit).coeffAtTSquare]
      = cyclicThreeBoundaryElement := rfl

/-! ## E8 — linearity certificates: the boundaries are A-linear, the homotopy is `ZZ`-linear ONLY

Exactness of a complex of A-modules is a property of the underlying abelian groups, so a
`ZZ`-linear contracting homotopy proves it; the boundary maps themselves are A-linear (additive +
`t`-equivariant).  The homotopy MUST NOT be A-linear — an A-linear homotopy would split the
resolution over A and force `H_*(ZZ/3) = 0`, contradicting the shipped `H_1 = ZZ/3` — and the probe
below machine-checks that our homotopy indeed fails `t`-equivariance.  This is exactly why the
ZZ-Smith certificate reader was BLIND to this object (the r5 node's "an `A`-linear object the
ℤ-Smith reader is blind to"): the homotopy lives on the module carrier, not in any tensored matrix. -/

/-- The augmentation is additive. -/
theorem cyclicThreeElementAugmentationIsAdditive
    (leftElement rightElement : CyclicThreeGroupRingElement) :
    cyclicThreeElementAugmentation (addCyclicThreeElements leftElement rightElement)
      = cyclicThreeElementAugmentation leftElement
          + cyclicThreeElementAugmentation rightElement :=
  (congrArg (· + (leftElement.coeffAtTSquare + rightElement.coeffAtTSquare))
      (intAddSwapMiddleLocal leftElement.coeffAtUnit rightElement.coeffAtUnit
        leftElement.coeffAtT rightElement.coeffAtT)).trans
    (intAddSwapMiddleLocal (leftElement.coeffAtUnit + leftElement.coeffAtT)
      (rightElement.coeffAtUnit + rightElement.coeffAtT)
      leftElement.coeffAtTSquare rightElement.coeffAtTSquare)

/-- The odd-index boundary `t - 1` is additive. -/
theorem cyclicThreeOddBoundaryIsAdditive
    (leftElement rightElement : CyclicThreeGroupRingElement) :
    cyclicThreeMultiplyByTMinusOne (addCyclicThreeElements leftElement rightElement)
      = addCyclicThreeElements (cyclicThreeMultiplyByTMinusOne leftElement)
          (cyclicThreeMultiplyByTMinusOne rightElement) :=
  cyclicThreeElementCongr
    (intSubAddExchange leftElement.coeffAtTSquare rightElement.coeffAtTSquare
      leftElement.coeffAtUnit rightElement.coeffAtUnit)
    (intSubAddExchange leftElement.coeffAtUnit rightElement.coeffAtUnit
      leftElement.coeffAtT rightElement.coeffAtT)
    (intSubAddExchange leftElement.coeffAtT rightElement.coeffAtT
      leftElement.coeffAtTSquare rightElement.coeffAtTSquare)

/-- The even-index boundary `N` is additive. -/
theorem cyclicThreeEvenBoundaryIsAdditive
    (leftElement rightElement : CyclicThreeGroupRingElement) :
    cyclicThreeMultiplyByNorm (addCyclicThreeElements leftElement rightElement)
      = addCyclicThreeElements (cyclicThreeMultiplyByNorm leftElement)
          (cyclicThreeMultiplyByNorm rightElement) :=
  cyclicThreeElementCongr
    (cyclicThreeElementAugmentationIsAdditive leftElement rightElement)
    (cyclicThreeElementAugmentationIsAdditive leftElement rightElement)
    (cyclicThreeElementAugmentationIsAdditive leftElement rightElement)

/-- The even-degree homotopy leg is additive (`ZZ`-linear). -/
theorem cyclicThreeHomotopyEvenToOddIsAdditive
    (leftElement rightElement : CyclicThreeGroupRingElement) :
    cyclicThreeHomotopyEvenToOdd (addCyclicThreeElements leftElement rightElement)
      = addCyclicThreeElements (cyclicThreeHomotopyEvenToOdd leftElement)
          (cyclicThreeHomotopyEvenToOdd rightElement) :=
  cyclicThreeElementCongr
    (intAddSwapMiddleLocal leftElement.coeffAtT rightElement.coeffAtT
      leftElement.coeffAtTSquare rightElement.coeffAtTSquare)
    rfl
    rfl

/-- The odd-degree homotopy leg is additive (`ZZ`-linear).  Definitional. -/
theorem cyclicThreeHomotopyOddToEvenIsAdditive
    (leftElement rightElement : CyclicThreeGroupRingElement) :
    cyclicThreeHomotopyOddToEven (addCyclicThreeElements leftElement rightElement)
      = addCyclicThreeElements (cyclicThreeHomotopyOddToEven leftElement)
          (cyclicThreeHomotopyOddToEven rightElement) := rfl

/-- **The odd-index boundary is `t`-equivariant** — `(t-1) ∘ (t .) = (t .) ∘ (t-1)`; with
additivity this is A-linearity of `d_odd`.  Definitional (both sides are the same coefficient
permutation of differences). -/
theorem cyclicThreeOddBoundaryCommutesWithT (element : CyclicThreeGroupRingElement) :
    cyclicThreeMultiplyByTMinusOne (cyclicThreeMultiplyByT element)
      = cyclicThreeMultiplyByT (cyclicThreeMultiplyByTMinusOne element) := rfl

/-- **The even-index boundary is `t`-equivariant** — `N ∘ (t .) = (t .) ∘ N` (the norm absorbs the
rotation: `t . N = N`); with additivity this is A-linearity of `d_even`. -/
theorem cyclicThreeEvenBoundaryCommutesWithT :
    ∀ element : CyclicThreeGroupRingElement,
      cyclicThreeMultiplyByNorm (cyclicThreeMultiplyByT element)
        = cyclicThreeMultiplyByT (cyclicThreeMultiplyByNorm element)
  | ⟨unitCoeff, tCoeff, squareCoeff⟩ =>
      cyclicThreeElementCongr
        (intAddRotateLeft squareCoeff unitCoeff tCoeff)
        (intAddRotateLeft squareCoeff unitCoeff tCoeff)
        (intAddRotateLeft squareCoeff unitCoeff tCoeff)

/-- ★ **HONESTY PROBE: the homotopy is NOT `t`-equivariant** —
`s_even(t . 1) = 1 ≠ 0 = t . s_even(1)`.  As it MUST be: an A-linear contracting homotopy would
split the resolution over `A` and force `H_*(ZZ/3) = 0`, contradicting the shipped `H_1 = ZZ/3`.
The homotopy is a `ZZ`-linear object invisible to the tensored Smith layer — exactly the blindness
the r5 node recorded. -/
theorem cyclicThreeHomotopyIsNotTEquivariant :
    cyclicThreeHomotopyEvenToOdd (cyclicThreeMultiplyByT cyclicThreeBasisUnit)
      ≠ cyclicThreeMultiplyByT (cyclicThreeHomotopyEvenToOdd cyclicThreeBasisUnit) :=
  fun equivarianceWitness =>
    Nat.noConfusion
      (congrArg (fun element => element.coeffAtUnit.toNat) equivarianceWitness : (1 : Nat) = 0)

/-! ## E9 — THE EXACTNESS PACKAGE and the honest-record markers -/

/-- ★★★ **THE `ZZ/3` PERIODIC RESOLUTION IS EXACT, WITH EXPLICIT WITNESSES.**  The three-conjunct
constructive exactness package of the augmented complex
`... --N--> A --(t-1)--> A --eps--> ZZ --> 0`:

  1. `eps` is SURJECTIVE with the explicit section `s_{-1}` (`eps ∘ s_{-1} = id`);
  2. exactness AT DEGREE 0: every `eps`-kernel element has the explicit `d_1`-preimage `s_0 x`;
  3. exactness AT EVERY POSITIVE DEGREE: every `d_{dim+1}`-cycle has the explicit
     `d_{dim+2}`-preimage `s_{dim+1} x`.

Together with `cyclicThreeResolutionBoundaryComposesToZero` / `cyclicThreeAugmentationKillsBoundary`
(the `im ⊆ ker` halves) and the tensor tie (E7), this certifies the shipped
`PeriodicTowerChainComplex` computes `Tor_*^{ZZ[ZZ/3]}(ZZ, ZZ) = H_*(ZZ/3; ZZ)` in every degree —
genuine group homology of the presented monoid, not chain-complex arithmetic. -/
theorem cyclicThreePeriodicResolutionIsExactWithExplicitWitnesses :
    (∀ value : Int,
      cyclicThreeElementAugmentation (cyclicThreeAugmentationSection value) = value) ∧
    (∀ element : CyclicThreeGroupRingElement,
      cyclicThreeElementAugmentation element = 0 →
      cyclicThreeMultiplyByTMinusOne (cyclicThreeHomotopyEvenToOdd element) = element) ∧
    (∀ (dim : Nat) (element : CyclicThreeGroupRingElement),
      cyclicThreeResolutionBoundaryAction dim element = zeroCyclicThreeElement →
      cyclicThreeResolutionBoundaryAction (dim + 1)
        (cyclicThreeContractingHomotopyAction (dim + 1) element) = element) :=
  ⟨cyclicThreeAugmentationSectionSplits,
   cyclicThreeAugmentationKernelWitness,
   cyclicThreeResolutionKernelWitnessAtEveryPositiveDegree⟩

/-- ★ **The contracting-homotopy ASSEMBLY marker (the r5 named node's periodic-tower instance,
DISCHARGED HERE).**  The r5 node `contractingHomotopyIngredientsPresentAssemblyNamedNode` named
"the ASSEMBLY into `d s + s d = 1`" as the deep wall; THIS module assembles it for the `ZZ/3`
2-periodic resolution: `cyclicThreeContractingHomotopyIdentityAtEveryPositiveDegree` +
`cyclicThreeHomotopyIdentityAtDegreeZero` are the assembled `d s + s d = id`, and
`cyclicThreePeriodicResolutionIsExactWithExplicitWitnesses` is the kernel-witness exactness it
yields.  Scope: the PERIODIC (group-ring) resolution behind the shipped tower — the r4 node
`anickResolutionExactnessIsNamedNode`'s cyclic-3 instance is thereby discharged, while its MONOMIAL
(Fibonacci) side and the generic-`n` homotopy stay open (named below).  The committed r4/r5 marker
Bools are NOT edited (additive-only); the orchestrator flips ledgers from THIS record.  Read the
meaning from THIS docstring (the honest-record convention).  `= true`. -/
def cyclicThreeResolutionContractingHomotopyIsAssembled : Bool := true

/-- ★ **The honest residual marker (what this brick does NOT claim).**  NOT claimed here: (i) the
monomial / Fibonacci Anick-complex exactness (the r4 `anickResolutionExactnessIsNamedNode`'s
monomial side — a different, branching-combinatorics argument); (ii) the generic-`n` periodic
homotopy (the partial-norm leg at generic `n` needs indexed range sums — the documented `List.range`
propext minefield; this brick is the concrete `n = 3` instance whose SHAPE ports); (iii) the
Fox-derivative derivation of `N` from `sss ⟹ id` (`normDifferentialFromRelationIsNamedNode`
stands); (iv) any movement of the `S_1` rank-finiteness wall
(`carrierDegreeThreeChainIsAlwaysFinite` — exactness legitimizes the tower's homology as `Tor`, it
does not produce infinite rank at one degree); (v) the chain-homotopy equivalence to the Squier
walker complex (the shipped honest residual).  Read the meaning from THIS docstring.  `= true`. -/
def cyclicThreeResolutionExactnessScopeStaysHonest : Bool := true

end FX1Poly.Polygraph.Homology

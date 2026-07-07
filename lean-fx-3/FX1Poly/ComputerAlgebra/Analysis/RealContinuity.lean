import FX1Poly.ComputerAlgebra.Analysis.RealLimit

/-! # Real uniform continuity — modulus of continuity (ANALYSIS-CONT-1)

The second calculus rung.  A function `RegularReal -> RegularReal` is
UNIFORMLY CONTINUOUS with an EXPLICIT modulus of continuity `omega`:
shrinking the input to `1/(omega k + 1)` forces the output within
`1/(k+1)` in the real-level distance.  Bishop's discipline — the modulus
is the constructive witness, no unbounded `∃delta`.  The two-variable
form perturbs both slots and sums the input hypotheses.

Basic continuous operations land directly from the real-level
bound-respecting lemmas of `RealLimit`:

  * `negReal` is a two-sided ISOMETRY — modulus is the identity (the
    output bound equals the input bound, unchanged);
  * `addReal` is uniformly continuous in two variables — modulus
    `2k+1`, because two `1/(2k+2)` input perturbations recombine EXACTLY
    to `1/(k+1)` (the same index doubling `addReal` already samples at).

Uniformly continuous maps form a CATEGORY: they compose (moduli compose
CONTRAVARIANTLY, `omega_compose k = omega_inner (omega_outer k)`), with
the identity map carrying the identity modulus.  Bundling the map with
its modulus certificate (`UniformlyContinuousMap`) mirrors the carrier
discipline of `RegularReal` (approximation + regularity) and
`RegularRealSequence` (values + Cauchy).

Zero axioms throughout.

HONEST SCOPE: the uniformly continuous operations landed here are the
Lipschitz-1 ones whose output bound is a fixed recombination of the
input bound.  `mulReal` (uniformly continuous only on bounded
subdomains) and `sqrtReal` (Hölder-1/2, quadratic modulus) require
reworking the shipped `mulRealRespectsDenotesSame` /
`sqrtApproxPairDifferenceBounded` from a SHRINKING setoid bound to a
FIXED continuity bound — genuine analytic content, deferred, never
faked. -/

namespace FX1Poly.ComputerAlgebra

open RationalPair

/-! ## The uniform-continuity predicates -/

/-- **Uniform continuity with an explicit modulus** — one variable.  At
output precision `outputPrecision`, an input within
`1/(modulus outputPrecision + 1)` maps to an output within
`1/(outputPrecision+1)`. -/
def IsUniformlyContinuous (function : RegularReal → RegularReal)
    (modulus : Nat → Nat) : Prop :=
  ∀ leftValue rightValue : RegularReal, ∀ outputPrecision : Nat,
    IsWithinRealBound leftValue rightValue
        (reciprocalOfSucc (modulus outputPrecision)) →
      IsWithinRealBound (function leftValue) (function rightValue)
        (reciprocalOfSucc outputPrecision)

/-- **Uniform continuity with an explicit modulus** — two variables.
Both slots perturbed within `1/(modulus outputPrecision + 1)`. -/
def IsUniformlyContinuousTwo
    (function : RegularReal → RegularReal → RegularReal)
    (modulus : Nat → Nat) : Prop :=
  ∀ leftFirst leftSecond rightFirst rightSecond : RegularReal,
    ∀ outputPrecision : Nat,
      IsWithinRealBound leftFirst rightFirst
          (reciprocalOfSucc (modulus outputPrecision)) →
        IsWithinRealBound leftSecond rightSecond
            (reciprocalOfSucc (modulus outputPrecision)) →
          IsWithinRealBound (function leftFirst leftSecond)
            (function rightFirst rightSecond)
            (reciprocalOfSucc outputPrecision)

/-! ## Basic continuous operations -/

/-- **Negation is uniformly continuous** with the identity modulus — a
two-sided isometry, the output bound equals the input bound. -/
theorem isUniformlyContinuousNegReal :
    IsUniformlyContinuous negReal (fun outputPrecision => outputPrecision) :=
  fun _ _ _ isClose => negRealRespectsIsWithinRealBound isClose

/-- **Addition is uniformly continuous** in two variables with modulus
`2k+1` — the two input perturbations at `1/(2k+2)` recombine EXACTLY to
`1/(k+1)`. -/
theorem isUniformlyContinuousTwoAddReal :
    IsUniformlyContinuousTwo addReal
      (fun outputPrecision => 2 * outputPrecision + 1) :=
  fun _ _ _ _ outputPrecision isFirstClose isSecondClose =>
    isWithinRealBoundCongrBound
      (reciprocalDoubleSumDenotesSame outputPrecision)
      (addRealRespectsIsWithinRealBound isFirstClose isSecondClose)

/-! ## The category of uniformly continuous maps -/

/-- **A uniformly continuous self-map of the reals** — the function
bundled with its modulus of continuity and the certificate.  The map's
data mirrors the carrier discipline of `RegularReal`. -/
structure UniformlyContinuousMap where
  apply : RegularReal → RegularReal
  modulus : Nat → Nat
  isUniformlyContinuous : IsUniformlyContinuous apply modulus

/-- The identity map — identity modulus, the certificate is the input
hypothesis verbatim. -/
def idUniformlyContinuousMap : UniformlyContinuousMap :=
  { apply := fun value => value
    modulus := fun outputPrecision => outputPrecision
    isUniformlyContinuous := fun _ _ _ isClose => isClose }

/-- **Composition** — moduli compose CONTRAVARIANTLY: to reach output
precision `k` through `outer` after `inner`, pre-shrink the input by
`inner.modulus (outer.modulus k)`. -/
def composeUniformlyContinuousMap (outer inner : UniformlyContinuousMap) :
    UniformlyContinuousMap :=
  { apply := fun value => outer.apply (inner.apply value)
    modulus := fun outputPrecision =>
      inner.modulus (outer.modulus outputPrecision)
    isUniformlyContinuous := fun leftValue rightValue outputPrecision isClose =>
      outer.isUniformlyContinuous (inner.apply leftValue) (inner.apply rightValue)
        outputPrecision
        (inner.isUniformlyContinuous leftValue rightValue
          (outer.modulus outputPrecision) isClose) }

/-- Negation as a uniformly continuous map — the isometry packaged. -/
def negUniformlyContinuousMap : UniformlyContinuousMap :=
  { apply := negReal
    modulus := fun outputPrecision => outputPrecision
    isUniformlyContinuous := isUniformlyContinuousNegReal }

end FX1Poly.ComputerAlgebra

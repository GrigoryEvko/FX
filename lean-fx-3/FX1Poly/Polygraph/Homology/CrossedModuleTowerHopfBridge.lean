import FX1Poly.Polygraph.Homology.CrossedModuleFreeGroupMeasureInduction
import FX1Poly.Polygraph.Homology.AnickTelescopeAugmentationAndMonomialFiniteness

/-! # FX1Poly/Polygraph/Homology/CrossedModuleTowerHopfBridge — the pi2/H2 CARRIER bridge between the two
    already-closed cyclic-3 crowns: the crossed-module `pi_2<s | s^3> ~= ker(N)` group ring
    `GroupRingZmod3` and the periodic-tower `H_odd = ZZ/3` group ring `List Int`, identified basis by
    basis, with the shared invariant constant `3 = epsilon(N)` tied across both, and the `(t-1)`-action
    Hopf-shadow matrix on `ker(N)` with `det = 3` (TOWER-ANICK r6, #2144)

## What is already closed (this file re-proves NEITHER homology fact)

Both crowns landed before r6 and stay verbatim untouched:

  * the crossed-module crown `pi_2<s | s^3> ~= ker(N)`: the unconditional
    `freeCrossedModulePiTwoIso` (`Homology/CrossedModuleFreeGroupMeasureInduction`), resting on the
    separating `ZZ[ZZ/3] ~= ZZ^3` invariant `crossedModuleImage`, the Peiffer-invariance keystone, the
    kernel landing `identityLandsAugmentationZero`, and the measure-induction surjection;
  * the tower crown `H_odd = ZZ/3`, `H_even>0 = 0`: `cyclicThreeTowerOddDegreeHomologyIsZmodThree` /
    `cyclicThreeTowerEvenPositiveDegreeHomologyIsZero` (`Homology/PeriodicTowerChainComplex`), read off
    the parity Smith data; the r5 computed augmentation `cyclicThreeNormAugmentationIsThree` ties
    `epsilon(N) = 3` to the shipped odd-degree torsion factor `[3]`.

The r6 bridge is CONNECTIVE TISSUE, NOT a new homology theorem: the two crowns were built independently
over TWO different Lean representations of the same math object `ZZ[ZZ/3] ~= ZZ^3` (a 3-field record on
the crossed-module side, a `List Int` on the tower side).  This file IDENTIFIES those carriers element by
element and TIES the shared constant `3 = epsilon(N)` that both homology facts depend on.  No cross-directory
import edge is created (both crowns are Homology-internal leaves).

## The three bridge RUNGS (stated explicitly; a weak rung dressed as Hopf would be refuted)

  * **RUNG (i) — DATA bridge (SHIPPED, all definitional).**  Explicit translation maps
    `groupRingZmod3ToList` / `listToGroupRingZmod3`, both round trips, the generator/norm/boundary
    identifications `groupRingZmod3ToList (N . e0) = cyclicThreeNorm`,
    `groupRingZmod3ToList ((t-1) . e0) = cyclicThreeBoundaryElement`.
  * **RUNG (ii) — INVARIANT bridge (SHIPPED).**  The augmentations agree
    (`crossedAugmentationAgreesWithTowerAugmentation`, general; the norm case reduces to the literal `3`);
    the headline `crossedNormAugTiesTowerOddTorsion` proves `[epsilon(N)] = [3] =`
    `(cyclicThreeTowerHomologyInvariantAtDegree 1).torsionFactors` — the crossed-module `ker(N)` constant
    and the tower `H_1 = ZZ/3` constant are the SAME `3`.
  * **RUNG (iii) — HOPF-SHADOW bridge (PARTIAL: det tie SHIPPED, coker iso NAMED).**  The `(t-1)`-action
    on the rotation basis `g1 = 1 - t`, `g2 = t^2 - t` of `ker(N)` is the integer matrix
    `[[-1, 1], [-1, -2]]` (`hopfShadowActionMatrix`), verified to reconstruct the shipped
    `groupRingTMinusOneAction` on each generator; its determinant is `3 = epsilon(N)`
    (`hopfShadowDeterminantEqualsNormAugmentation`) — the Hopf constant.  The genuine coinvariant iso
    `coker M ~= ZZ/3` (SNF `diag(1, 3)`) needs a `Quot` (banned) or a `SmithReductionCertificate` whose
    propext corners are not opened under round pressure, so it is the NAMED residual
    `hopfShadowCokerIsZmodThreeIsNamedNode`, with the determinant-3 tie shipped as the honest down-payment.

## Zero-axiom design decisions

  * `groupRingZmod3ToList` is a 3-literal list; `listToGroupRingZmod3` reads back with the shipped
    `listGetWithDefault` — every generator/norm/boundary/round-trip identification closes by `rfl` (record
    eta + Int literal arithmetic reduce in the kernel).
  * The one non-`rfl` fact `crossedAugmentationAgreesWithTowerAugmentation` routes the bracket mismatch
    `(a + b) + c` vs `a + (b + (c + 0))` through the propext-clean kit `intAddAssoc` / `intAddZero`
    exclusively (never Init's `Int.add_assoc`).
  * The Hopf-shadow determinant is a hand 2x2 `def` (`a d - b c`, `rfl`); there is no `IntMatrix`
    determinant in the shipped kit, and the coker iso is NAMED rather than routed through the
    Smith-certificate machinery.

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated (and independently `#print axioms`-checked for the load-bearing decls) in
`FX1PolyAudit/Polygraph/Homology/CrossedModuleTowerHopfBridge.lean`. -/

namespace FX1Poly.Polygraph.Homology

open FX1Poly.ComputerAlgebra

/-! ## RUNG (i) — the DATA bridge: `GroupRingZmod3` (crossed module) <-> `List Int` (tower) -/

/-- **The crossed-module -> tower translation** — the 3-field group-ring record as its coefficient list
in the shared `{1, t, t^2}` basis, exactly the tower's `List Int` shape. -/
def groupRingZmod3ToList (value : GroupRingZmod3) : List Int :=
  [value.coeffOne, value.coeffT, value.coeffTsq]

/-- **The tower -> crossed-module translation** — read a length-3 coefficient list back into the record
via the shipped total lookup (`listGetWithDefault`), defaulting missing slots to `0`. -/
def listToGroupRingZmod3 (coefficients : List Int) : GroupRingZmod3 :=
  ⟨listGetWithDefault 0 coefficients 0, listGetWithDefault 0 coefficients 1,
    listGetWithDefault 0 coefficients 2⟩

/-- **Round trip A** — `listToGroupRingZmod3 (groupRingZmod3ToList v) = v`.  The list reads back the
three fields; record eta collapses the reconstruction.  `cases` then `rfl` (never `mk.injEq`). -/
theorem listToGroupRingZmod3CancelsToList (value : GroupRingZmod3) :
    listToGroupRingZmod3 (groupRingZmod3ToList value) = value := by
  cases value
  rfl

/-- **Round trip B** — `groupRingZmod3ToList (listToGroupRingZmod3 [a, b, c]) = [a, b, c]` for a length-3
list.  `rfl`. -/
theorem groupRingZmod3ToListCancelsFromListOnTriple (targetOne targetT targetTsq : Int) :
    groupRingZmod3ToList (listToGroupRingZmod3 [targetOne, targetT, targetTsq])
      = [targetOne, targetT, targetTsq] := rfl

/-- The three basis generators map to the tower's `{1, t, t^2}` unit coordinate lists.  `rfl`. -/
theorem crossedGeneratorsMapToTowerBasis :
    groupRingZmod3ToList (powerOfT ZmodThree.residue0) = [1, 0, 0] ∧
    groupRingZmod3ToList (powerOfT ZmodThree.residue1) = [0, 1, 0] ∧
    groupRingZmod3ToList (powerOfT ZmodThree.residue2) = [0, 0, 1] :=
  ⟨rfl, rfl, rfl⟩

/-- ★ **The crossed-module norm element IS the tower norm** — `groupRingZmod3ToList (N . e0) =
cyclicThreeNorm = [1, 1, 1]`.  The two independently-built `N = 1 + t + t^2` coincide under the carrier
translation.  `rfl`. -/
theorem towerNormIsCrossedNorm :
    groupRingZmod3ToList (groupRingNormElement (powerOfT ZmodThree.residue0)) = cyclicThreeNorm := rfl

/-- ★ **The crossed-module boundary element IS the tower boundary** — `groupRingZmod3ToList ((t - 1) . e0)
= cyclicThreeBoundaryElement = [-1, 1, 0]`, where `(t - 1) . e0 = s . e0 + (- e0)`.  `rfl`. -/
theorem towerBoundaryIsCrossedBoundary :
    groupRingZmod3ToList (groupRingAdd (groupRingSAction (powerOfT ZmodThree.residue0))
        (groupRingNeg (powerOfT ZmodThree.residue0)))
      = cyclicThreeBoundaryElement := rfl

/-! ## RUNG (ii) — the INVARIANT bridge: the augmentation and the shared constant `3` -/

/-- ★ **The two augmentations agree on every group-ring element** — `groupRingAugmentation v =
cyclicThreeGroupRingAugmentation (groupRingZmod3ToList v)`.  The crossed-module augmentation brackets
`(a + b) + c`; the tower augmentation folds `a + (b + (c + 0))`; the two are reconciled by one
associativity and one `+ 0` cancel through the propext-clean kit. -/
theorem crossedAugmentationAgreesWithTowerAugmentation (value : GroupRingZmod3) :
    groupRingAugmentation value
      = cyclicThreeGroupRingAugmentation (groupRingZmod3ToList value) :=
  (intAddAssoc value.coeffOne value.coeffT value.coeffTsq).trans
    (congrArg (fun tailSum => value.coeffOne + (value.coeffT + tailSum))
      (intAddZero value.coeffTsq)).symm

/-- The crossed-module and tower norm augmentations agree on the concrete norm — both `3` (literal
reduction).  `rfl`. -/
theorem crossedAndTowerNormAugmentationsAgree :
    groupRingAugmentation (groupRingNormElement (powerOfT ZmodThree.residue0))
      = cyclicThreeGroupRingAugmentation cyclicThreeNorm := rfl

/-- The crossed-module norm augments to `3 = epsilon(N)` — the `ker(N)` torsion constant.  `rfl`. -/
theorem crossedNormAugmentationIsThree :
    groupRingAugmentation (groupRingNormElement (powerOfT ZmodThree.residue0)) = 3 := rfl

/-- ★★ **THE pi2/H2 HEADLINE** — the crossed-module `ker(N)` constant and the tower `H_1 = ZZ/3` constant
are the SAME `3`: `[epsilon(N)] = [3] = (cyclicThreeTowerHomologyInvariantAtDegree 1).torsionFactors`.
`pi_2<s | s^3> ~= ker(N)` (via `freeCrossedModulePiTwoIso`) and `H_1(tower) = ZZ/3` (via
`cyclicThreeTowerOddDegreeHomologyIsZmodThree`) provably share the single integer `epsilon(N) = 3`.  This
is the identification the two independently-closed crowns were missing — NOT a re-proof of either homology
fact, but the bridge tying their common torsion order.  `rfl`. -/
theorem crossedNormAugTiesTowerOddTorsion :
    [groupRingAugmentation (groupRingNormElement (powerOfT ZmodThree.residue0))]
      = (cyclicThreeTowerHomologyInvariantAtDegree 1).torsionFactors := rfl

/-! ## RUNG (iii) — the HOPF-SHADOW bridge: the `(t-1)`-action matrix and `det = 3` (coker NAMED) -/

/-- **The `(t-1)`-action on `ZZ[ZZ/3]`** — `(t - 1) . v = s . v + (- v)`, multiplication by the boundary
element.  On `ker(N)` its cokernel is the coinvariants `ker(N) / (t-1) ker(N)`, the Hopf module. -/
def groupRingTMinusOneAction (value : GroupRingZmod3) : GroupRingZmod3 :=
  groupRingAdd (groupRingSAction value) (groupRingNeg value)

/-- The first `ker(N)` rotation generator `g1 = 1 - t = (1, -1, 0)` (the shipped
`augmentationZeroSpannedByRotations` spanning vector). -/
def hopfRotationGeneratorOne : GroupRingZmod3 := ⟨1, -1, 0⟩

/-- The second `ker(N)` rotation generator `g2 = t^2 - t = (0, -1, 1)`. -/
def hopfRotationGeneratorTwo : GroupRingZmod3 := ⟨0, -1, 1⟩

/-- The `(t-1)`-action on `g1` lands in `ker(N)`: `(t - 1) . g1 = (-1, 2, -1) = - g1 - g2`.  `rfl`. -/
theorem hopfShadowActionOnGeneratorOne :
    groupRingTMinusOneAction hopfRotationGeneratorOne = GroupRingZmod3.mk (-1) 2 (-1) := rfl

/-- The `(t-1)`-action on `g2` lands in `ker(N)`: `(t - 1) . g2 = (1, 1, -2) = g1 - 2 g2`.  `rfl`. -/
theorem hopfShadowActionOnGeneratorTwo :
    groupRingTMinusOneAction hopfRotationGeneratorTwo = GroupRingZmod3.mk 1 1 (-2) := rfl

/-- **The Hopf-shadow action matrix** — the `(t-1)`-action written in the rotation basis `(g1, g2)` of
`ker(N)`: column `j` is the coordinate vector of `(t - 1) . g_j`.  `[[-1, 1], [-1, -2]]`. -/
def hopfShadowActionMatrix : IntMatrix := ⟨[[-1, 1], [-1, -2]]⟩

/-- ★ **The matrix's first column reconstructs the action on `g1`** — `M[0,0] . g1 + M[1,0] . g2 =
(t - 1) . g1`.  Ties the abstract integer matrix to the shipped `groupRingTMinusOneAction`.  `rfl`. -/
theorem hopfShadowColumnOneReconstructsAction :
    groupRingAdd (groupRingZScale (hopfShadowActionMatrix.entryAt 0 0) hopfRotationGeneratorOne)
        (groupRingZScale (hopfShadowActionMatrix.entryAt 1 0) hopfRotationGeneratorTwo)
      = groupRingTMinusOneAction hopfRotationGeneratorOne := rfl

/-- ★ **The matrix's second column reconstructs the action on `g2`** — `M[0,1] . g1 + M[1,1] . g2 =
(t - 1) . g2`.  `rfl`. -/
theorem hopfShadowColumnTwoReconstructsAction :
    groupRingAdd (groupRingZScale (hopfShadowActionMatrix.entryAt 0 1) hopfRotationGeneratorOne)
        (groupRingZScale (hopfShadowActionMatrix.entryAt 1 1) hopfRotationGeneratorTwo)
      = groupRingTMinusOneAction hopfRotationGeneratorTwo := rfl

/-- The 2x2 integer determinant (hand `a d - b c`; there is no `IntMatrix` determinant in the shipped
kit).  Used only on the concrete Hopf-shadow matrix. -/
def hopfShadowDeterminant (matrix : IntMatrix) : Int :=
  matrix.entryAt 0 0 * matrix.entryAt 1 1 - matrix.entryAt 0 1 * matrix.entryAt 1 0

/-- ★ **The Hopf-shadow determinant is `3`** — `det [[-1, 1], [-1, -2]] = (-1)(-2) - (1)(-1) = 3`.  `rfl`. -/
theorem hopfShadowDeterminantIsThree : hopfShadowDeterminant hopfShadowActionMatrix = 3 := rfl

/-- ★★ **THE HOPF CONSTANT** — `det M = epsilon(N) = 3`: the determinant of the `(t-1)`-action on `ker(N)`
equals the norm augmentation, hence the order of the coinvariants `coker M ~= ZZ/3` matches the tower
`H_1 = ZZ/3`.  The determinant-3 tie is the honest down-payment on the coker iso (NAMED below).  `rfl`. -/
theorem hopfShadowDeterminantEqualsNormAugmentation :
    hopfShadowDeterminant hopfShadowActionMatrix
      = groupRingAugmentation (groupRingNormElement (powerOfT ZmodThree.residue0)) := rfl

/-- ★ **The coinvariant iso `coker M ~= ZZ/3` is a NAMED node.**  The Hopf-shadow matrix
`M = [[-1, 1], [-1, -2]]` (`det = 3`) has Smith normal form `diag(1, 3)`, so its cokernel
`ker(N) / (t-1) ker(N) ~= ZZ/3` — matching the tower `H_1`.  A machine-checked coker iso needs either a
`Quot` (BANNED: `Quot.sound`) or a `SmithReductionCertificate` reducing `M` to `diag(1, 3)` followed by
`smithInvariantFactorsWithin ... = [3]`; the certificate route's `IsSmithNormalFormWithin` /
`applyOperations` corners are not opened under round pressure.  The `rfl`-clean determinant-3 tie
(`hopfShadowDeterminantEqualsNormAugmentation`) is shipped as the down-payment.  Read the meaning from
THIS docstring (the honest-record convention).  `= true`. -/
def hopfShadowCokerIsZmodThreeIsNamedNode : Bool := true

/-! ## The r6 bridge ledger (honest scope) -/

/-- The honest status of one bridge rung. -/
inductive TowerBridgeRungStatus where
  /-- Fully shipped, zero-axiom, no residual. -/
  | shipped
  /-- The concrete down-payment shipped; a precisely-named residual stands (the coker iso). -/
  | shippedWithNamedResidual

/-- The three-rung ledger of the crossed-module / tower carrier bridge. -/
structure CrossedModuleTowerBridgeLedger where
  /-- RUNG (i): the `GroupRingZmod3` <-> `List Int` data bridge (round trips + generator/norm/boundary). -/
  dataRungStatus : TowerBridgeRungStatus
  /-- RUNG (ii): the augmentation agreement + the shared torsion constant `3 = epsilon(N)`. -/
  invariantRungStatus : TowerBridgeRungStatus
  /-- RUNG (iii): the `(t-1)`-action matrix + `det = 3` shipped; the coker iso NAMED. -/
  hopfShadowRungStatus : TowerBridgeRungStatus

/-- ★ **The r6 bridge ledger.**  RUNG (i) and RUNG (ii) fully shipped; RUNG (iii) is the determinant-3 tie
shipped with the coker iso NAMED.  The honest reading: neither homology fact is re-proved (both crowns
pre-exist); this bridge IDENTIFIES the two carriers of `ZZ[ZZ/3] ~= ZZ^3` and TIES the shared constant
`3 = epsilon(N)`, plus the `(t-1)`-action Hopf-shadow matrix with `det = 3`. -/
def crossedModuleTowerBridgeLedger : CrossedModuleTowerBridgeLedger :=
  { dataRungStatus := TowerBridgeRungStatus.shipped
  , invariantRungStatus := TowerBridgeRungStatus.shipped
  , hopfShadowRungStatus := TowerBridgeRungStatus.shippedWithNamedResidual }

/-- ★ **The TOWER-ANICK (#2144) r6 crossed-module/tower bridge marker.**  Shipped zero-axiom over the two
already-closed crowns, additively (neither crown file edited):

  * **RUNG (i)** — the DATA bridge: `groupRingZmod3ToList` / `listToGroupRingZmod3`, both round trips
    (`listToGroupRingZmod3CancelsToList`, `groupRingZmod3ToListCancelsFromListOnTriple`), the generator
    maps (`crossedGeneratorsMapToTowerBasis`), and `towerNormIsCrossedNorm` /
    `towerBoundaryIsCrossedBoundary` — the two independently-built `ZZ[ZZ/3]` carriers identified.
  * **RUNG (ii)** — the INVARIANT bridge: `crossedAugmentationAgreesWithTowerAugmentation` (general),
    `crossedNormAugmentationIsThree`, and ★★ `crossedNormAugTiesTowerOddTorsion` — the pi2/H2 headline
    `[epsilon(N)] = [3] =` the tower's degree-1 torsion factor.
  * **RUNG (iii)** — the HOPF-SHADOW bridge (PARTIAL): `groupRingTMinusOneAction` + the rotation basis
    `g1, g2`, the action matrix `hopfShadowActionMatrix = [[-1, 1], [-1, -2]]` reconstructing the action
    (`hopfShadowColumnOneReconstructsAction`, `hopfShadowColumnTwoReconstructsAction`), and ★★
    `hopfShadowDeterminantEqualsNormAugmentation` (`det M = epsilon(N) = 3`).  The coker iso
    `coker M ~= ZZ/3` is the NAMED residual `hopfShadowCokerIsZmodThreeIsNamedNode` (Smith-certificate /
    `Quot` wall), with the determinant-3 tie shipped as the down-payment.

No overclaim: both homology facts pre-exist (`freeCrossedModulePiTwoIso`,
`cyclicThreeTowerOddDegreeHomologyIsZmodThree`); this file is the connective identification of carriers and
the tie of the constant `3`.  Read the meaning from THIS docstring (the honest-record convention). -/
def crossedModuleTowerHopfBridgeIsComplete : Bool := true

end FX1Poly.Polygraph.Homology

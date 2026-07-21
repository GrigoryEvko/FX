import FX1Poly.ComputerAlgebra.Decision.CombinationDispatch
import FX1Poly.ComputerAlgebra.Decision.FourierMotzkinExtension

/-! # FX1Poly/ComputerAlgebra/Decision/CombinationCompleteness — Nelson–Oppen
    completeness for the ground-congruence + Farkas combination

The completeness-side companion to `CombinationDispatch` (the `noc` core, whose
soundness chain `nocCombinationSound` / `nocFinderSound` /
`nocFinderRefutesJointModels` is proven zero-axiom).  This file supplies the reverse
direction — an unsatisfiable combined system yields an accepted refutation
certificate — up to one honest semantic wall.  The A-side Farkas leg is discharged
against the proven `lreFarkasCompletenessHolds` (in `FourierMotzkinExtension`), so
only the E-side equality-interpolation leg remains premised.

## Proven here (zero-axiom, no premise)

  * `nccAugmentedInfeasibleIffFarkasCertificate` — the propagation-augmented A-side
    is rationally infeasible (in the denominator encoding of
    `lfkFarkasCompletenessStatement`'s antecedent) iff a Farkas certificate refutes
    it.  Forward is `lreFarkasCompletenessHolds`, backward is
    `lreScaledInfeasibilityOfAcceptedCertificate`.
  * `nccAcceptedCertificateOfAugmentedInfeasible` — the completeness reduction:
    rational infeasibility of the augmented A-side yields an accepted combination
    certificate carrying the propagated equalities (Farkas multipliers from the
    discharged leg; equality half `nocPropagatedAllCheck`).
  * `nccJointModelSatisfiesAugmented` — every joint model satisfies the augmented
    A-side, so a Farkas refutation of that side refutes every joint model.
  * `nccPropagatedCountBoundedByTriangle` — one-round propagation emits at most a
    triangular number (in the interface length) of shared equalities: the
    constructive-pigeonhole bound on the finite pair census that would cap the fuel
    of a multi-round saturation loop.

## The single honest wall (owner-false)

`nccEqualityInterpolationStatement` — joint unsatisfiability of the committed integer
`nocIsJointModel` semantics upgrades to rational infeasibility of the augmented
A-side.  FALSE over ℤ as literally stated: the empty-E, A-part `{2x = 1}` problem is
integer-joint-unsat yet rationally feasible (`x = 1/2`), so no Farkas certificate
exists.  The reachable rational target additionally needs equality-interpolation
completeness of the E-engine (single shared equalities suffice only for convex
theories; ℤ-LIA is non-convex — `1 ≤ x ≤ 2` entails `x = 1 ∨ x = 2` with neither
disjunct entailed) and model amalgamation across the shared arrangement (stable
infiniteness / cardinality agreement, a semantic condition no certificate checker
inspects).  Owner `fxNccCombine_hasEqualityInterpolation := false`.

Given that wall as a hypothesis, `nccCombinationCompleteGivenInterpolation` and the
end-to-end decision iff `nccCombinationDecidesGivenInterpolation` follow: soundness
is unconditional, completeness rests on the one named leg.

## Zero-axiom discipline

Init only; imports the `noc` dispatch and the Fourier–Motzkin completeness cascade.
Structural recursion; no `WellFounded.fix`, `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `funext`, `omega`, no `decide` on
`Prop`, no wildcard arms.  The census length bound uses only the probed-clean
`Nat.le` kit; all list helpers are bespoke, monomorphic, cons-only.  Per-declaration
gate in the audit twin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.ComputerAlgebra

/-! ## Stage A — the propagation-augmented A-side and its rational infeasibility -/

/-- The A-side of a problem AUGMENTED with the one-round propagated shared equalities —
the exact system the committed finder feeds to Fourier–Motzkin. -/
def nccAugmentedArithmetic (problem : NocProblem) : List LfkConstraint :=
  nocAugmentSystem (nocPropagateEqualities problem) problem.arithmeticPart

/-- RATIONAL infeasibility of the augmented A-side, stated in the denominator encoding of
`lfkFarkasCompletenessStatement`'s antecedent VERBATIM: no positive denominator admits an
integer environment for the scaled-bounds system (the environment then denotes the
rational point `env / denominator`). -/
def nccAugmentedRationallyInfeasible (problem : NocProblem) : Prop :=
  ∀ (denominatorPred : Nat) (env : List LfkInt),
    lfkSatisfiesSystem env
      (lfkScaleBoundsForDenominator (denominatorPred + 1)
        (nccAugmentedArithmetic problem)) = true → False

/-! ## Stage B — the Farkas leg

Both directions of the rational-Farkas iff, specialised to the augmented A-side; this
turns the combination's A-side completeness from a premise into a theorem. -/

/-- The A-side iff: the augmented A-side is rationally infeasible iff a Farkas
certificate refutes it.  Forward is the completeness inhabitant
`lreFarkasCompletenessHolds`; backward is `lreScaledInfeasibilityOfAcceptedCertificate`. -/
theorem nccAugmentedInfeasibleIffFarkasCertificate (problem : NocProblem) :
    Iff (nccAugmentedRationallyInfeasible problem)
      (∃ (farkasCertificate : List Nat),
        lfkCheckRefutation farkasCertificate (nccAugmentedArithmetic problem) = true) :=
  Iff.intro
    (fun infeasibilityWitness =>
      lreFarkasCompletenessHolds (nccAugmentedArithmetic problem) infeasibilityWitness)
    (fun certificateWitness =>
      Exists.elim certificateWitness
        (fun farkasCertificate acceptedWitness =>
          lreScaledInfeasibilityOfAcceptedCertificate farkasCertificate
            (nccAugmentedArithmetic problem) acceptedWitness))

/-- THE COMPLETENESS REDUCTION (fully proven, zero-axiom, no premise): if the
propagation-augmented A-side is rationally infeasible, the combination checker accepts a
certificate whose derived-equality list is exactly the propagated equalities.  The Farkas
multipliers come from the discharged completeness leg; the equality half is
`nocPropagatedAllCheck`. -/
theorem nccAcceptedCertificateOfAugmentedInfeasible (problem : NocProblem)
    (infeasibilityWitness : nccAugmentedRationallyInfeasible problem) :
    ∃ (certificate : NocCertificate), nocCheckCombination problem certificate = true :=
  Exists.elim
    (lreFarkasCompletenessHolds (nccAugmentedArithmetic problem) infeasibilityWitness)
    (fun farkasCertificate farkasAccepted =>
      Exists.intro (NocCertificate.mk (nocPropagateEqualities problem) farkasCertificate)
        (lfkBoolAndIntro
          (nocCheckAllDerivedEqualities problem.equationalPart problem.sharedInterface
            (nocPropagateEqualities problem))
          (lfkCheckRefutation farkasCertificate
            (nocAugmentSystem (nocPropagateEqualities problem) problem.arithmeticPart))
          (nocPropagatedAllCheck problem)
          farkasAccepted))

/-! ## Stage C — the joint-model companion, the interpolation wall, and the conditionals -/

/-- Every joint model satisfies the propagation-augmented A-side: the bridge
(`nocFunctionalConsistencyHolds`) fires each propagated equality row through
`nocAugmentedSystemSatisfied`, and the A-part is a sublist.  Completeness-side companion
of soundness — a Farkas refutation of the augmented A-side refutes every joint model. -/
theorem nccJointModelSatisfiesAugmented (problem : NocProblem) (env : List LfkInt)
    (jointModelWitness : nocIsJointModel problem env) :
    lfkSatisfiesSystem env (nccAugmentedArithmetic problem) = true :=
  nocAugmentedSystemSatisfied problem env jointModelWitness.right jointModelWitness.left
    (nocPropagateEqualities problem) (nocPropagatedAllCheck problem)

/-- The equality-interpolation wall (owner-false): joint unsatisfiability of the
committed integer `nocIsJointModel` semantics upgrades to rational infeasibility of the
augmented A-side.  FALSE over ℤ as stated (the empty-E, A-part `{2x = 1}` problem is
integer-joint-unsat yet rationally feasible); the reachable rational target further
needs E-engine equality-interpolation completeness and model amalgamation (see the
header).  Owner: `fxNccCombine_hasEqualityInterpolation := false`. -/
def nccEqualityInterpolationStatement : Prop :=
  ∀ (problem : NocProblem),
    (∀ (env : List LfkInt), nocIsJointModel problem env → False) →
      nccAugmentedRationallyInfeasible problem

/-- Conditional completeness: given the equality-interpolation leg, every
jointly-unsatisfiable problem has an accepted combination certificate.  The Farkas half
is unconditional (Stage B); only the E-side interpolation is premised. -/
theorem nccCombinationCompleteGivenInterpolation
    (interpolationWitness : nccEqualityInterpolationStatement) (problem : NocProblem)
    (jointUnsatWitness : ∀ (env : List LfkInt), nocIsJointModel problem env → False) :
    ∃ (certificate : NocCertificate), nocCheckCombination problem certificate = true :=
  nccAcceptedCertificateOfAugmentedInfeasible problem
    (interpolationWitness problem jointUnsatWitness)

/-- The end-to-end decision iff: given the equality-interpolation leg, the combination
checker decides joint unsatisfiability — an accepted certificate exists iff no joint
model exists.  Soundness (`nocCombinationSound`) supplies the backward half with no
premise; completeness supplies the forward half through the one named leg. -/
theorem nccCombinationDecidesGivenInterpolation
    (interpolationWitness : nccEqualityInterpolationStatement) (problem : NocProblem) :
    Iff (∀ (env : List LfkInt), nocIsJointModel problem env → False)
      (∃ (certificate : NocCertificate), nocCheckCombination problem certificate = true) :=
  Iff.intro
    (fun jointUnsatWitness =>
      nccCombinationCompleteGivenInterpolation interpolationWitness problem
        jointUnsatWitness)
    (fun certificateWitness =>
      Exists.elim certificateWitness
        (fun certificate acceptedWitness =>
          nocCombinationSound problem certificate acceptedWitness))

/-! ## Stage D — the finite pair census (the pigeonhole fuel bound) -/

/-- Bespoke cons-only length of an index-pair list. -/
def nccPairListLength : List (Nat × Nat) → Nat
  | List.nil => 0
  | _headPair :: remainingPairs => Nat.succ (nccPairListLength remainingPairs)

/-- Bespoke cons-only length of a shared interface. -/
def nccInterfaceLength : List (Nat × GccTerm) → Nat
  | List.nil => 0
  | _headEntry :: remainingEntries => Nat.succ (nccInterfaceLength remainingEntries)

/-- The triangular number `0 + 1 + ... + count` — the count of unordered pairs bound of a
census of size `count`. -/
def nccTriangular : Nat → Nat
  | 0 => 0
  | Nat.succ previousCount => previousCount + Nat.succ (nccTriangular previousCount)

/-- The bespoke append is length-additive. -/
theorem nccPairListAppendLength : ∀ (leftPairs rightPairs : List (Nat × Nat)),
    nccPairListLength (nocIndexPairListAppend leftPairs rightPairs)
      = nccPairListLength leftPairs + nccPairListLength rightPairs
  | List.nil, rightPairs => (Nat.zero_add (nccPairListLength rightPairs)).symm
  | _headPair :: remainingPairs, rightPairs =>
      (congrArg Nat.succ (nccPairListAppendLength remainingPairs rightPairs)).trans
        (Nat.succ_add (nccPairListLength remainingPairs)
          (nccPairListLength rightPairs)).symm

/-- Every anchor collects at most one pair per later interface entry: the collected list
is no longer than the entry list it scans. -/
theorem nccCollectCountBounded (equations : List (GccTerm × GccTerm))
    (sharedInterface : List (Nat × GccTerm)) (anchorIndex : Nat) :
    ∀ (interfaceEntries : List (Nat × GccTerm)),
      Nat.le
        (nccPairListLength
          (nocCollectProvablePairs equations sharedInterface anchorIndex interfaceEntries))
        (nccInterfaceLength interfaceEntries)
  | List.nil => Nat.le_refl 0
  | laterEntry :: remainingEntries => by
      cases hCheck : nocCheckDerivedEquality equations sharedInterface
          (anchorIndex, laterEntry.fst) with
      | true =>
          have hUnfold : nocCollectProvablePairs equations sharedInterface anchorIndex
              (laterEntry :: remainingEntries)
              = (anchorIndex, laterEntry.fst)
                :: nocCollectProvablePairs equations sharedInterface anchorIndex
                  remainingEntries := by
            simp only [nocCollectProvablePairs]
            rw [hCheck]
            rfl
          rw [hUnfold]
          exact Nat.succ_le_succ
            (nccCollectCountBounded equations sharedInterface anchorIndex remainingEntries)
      | false =>
          have hUnfold : nocCollectProvablePairs equations sharedInterface anchorIndex
              (laterEntry :: remainingEntries)
              = nocCollectProvablePairs equations sharedInterface anchorIndex
                remainingEntries := by
            simp only [nocCollectProvablePairs]
            rw [hCheck]
            rfl
          rw [hUnfold]
          exact Nat.le_trans
            (nccCollectCountBounded equations sharedInterface anchorIndex remainingEntries)
            (Nat.le_add_right (nccInterfaceLength remainingEntries) 1)

/-- The one-round suffix propagation emits at most a triangular-number (in the interface
length) of shared equalities: each anchor contributes at most its suffix length, and the
suffix lengths sum to the triangular number.  This is the finite pair census whose size
would bound the fuel of a multi-round saturation loop. -/
theorem nccPropagateOverSuffixCountBounded (equations : List (GccTerm × GccTerm))
    (sharedInterface : List (Nat × GccTerm)) :
    ∀ (suffixEntries : List (Nat × GccTerm)),
      Nat.le
        (nccPairListLength
          (nocPropagateOverSuffix equations sharedInterface suffixEntries))
        (nccTriangular (nccInterfaceLength suffixEntries))
  | List.nil => Nat.le_refl 0
  | anchorEntry :: remainingEntries => by
      show Nat.le
        (nccPairListLength
          (nocIndexPairListAppend
            (nocCollectProvablePairs equations sharedInterface anchorEntry.fst
              remainingEntries)
            (nocPropagateOverSuffix equations sharedInterface remainingEntries)))
        (nccInterfaceLength remainingEntries
          + Nat.succ (nccTriangular (nccInterfaceLength remainingEntries)))
      rw [nccPairListAppendLength]
      exact Nat.add_le_add
        (nccCollectCountBounded equations sharedInterface anchorEntry.fst remainingEntries)
        (Nat.le_succ_of_le
          (nccPropagateOverSuffixCountBounded equations sharedInterface remainingEntries))

/-- THE CENSUS BOUND: a problem's one-round propagation emits at most
`nccTriangular (interface length)` shared equalities — the constructive pigeonhole cap on
the finite pair census. -/
theorem nccPropagatedCountBoundedByTriangle (problem : NocProblem) :
    Nat.le (nccPairListLength (nocPropagateEqualities problem))
      (nccTriangular (nccInterfaceLength problem.sharedInterface)) :=
  nccPropagateOverSuffixCountBounded problem.equationalPart problem.sharedInterface
    problem.sharedInterface

/-! ## Stage E — markers -/

/-- The completeness reduction is decided, resting only on the single named
equality-interpolation leg.  Three zero-axiom deliverables:
(1) the A-side Farkas leg is discharged, not premised
    (`nccAugmentedInfeasibleIffFarkasCertificate`,
    `nccAcceptedCertificateOfAugmentedInfeasible` route through the proven
    `lreFarkasCompletenessHolds`);
(2) the conditional completeness reduction and end-to-end decision iff
    (`nccCombinationCompleteGivenInterpolation`,
    `nccCombinationDecidesGivenInterpolation`);
(3) the finite pair census bound `nccPropagatedCountBoundedByTriangle` caps the
    one-round propagation output by a triangular number of the interface length. -/
def fxNccCombine_hasCompletenessReduction : Bool := true

/-- Owner flag for `nccEqualityInterpolationStatement` — FALSE over ℤ as stated (see the
header for the rational-side interpolation and amalgamation legs). -/
def fxNccCombine_hasEqualityInterpolation : Bool := false

/-! ## Stage F — fires (concrete kernel pins routing through the completeness machinery)

Symbols: `0 = a`, `1 = b`, `3 = f`.  The congruence fire needs a genuine congruence-
closure call: from `a = b` the E-engine derives `f(a) = f(b)` (a fresh path beyond the
sibling smoke's symmetry/transitivity), which the A-side then refutes. -/

/-- Smoke term `f(a)`. -/
def nccCongruenceTermFofA : GccTerm := GccTerm.apply (GccTerm.symbol 3) (GccTerm.symbol 0)

/-- Smoke term `f(b)`. -/
def nccCongruenceTermFofB : GccTerm := GccTerm.apply (GccTerm.symbol 3) (GccTerm.symbol 1)

/-- E-part `{a = b}` — the equality that the congruence engine must LIFT through `f`. -/
def nccCongruenceEquations : List (GccTerm × GccTerm) :=
  [(GccTerm.symbol 0, GccTerm.symbol 1)]

/-- Shared interface `x0 ↦ f(a)`, `x1 ↦ f(b)` — the shared variables denote the LIFTED
terms, so the derived equality `x0 = x1` needs the congruence step. -/
def nccCongruenceInterface : List (Nat × GccTerm) :=
  [(0, nccCongruenceTermFofA), (1, nccCongruenceTermFofB)]

/-- A-part `x0 - x1 >= 1` — alone satisfiable, jointly contradictory with `x0 = x1`. -/
def nccCongruenceArithmetic : List LfkConstraint :=
  [LfkConstraint.mk [LfkInt.mk 1 0, LfkInt.mk 0 1] (LfkInt.mk 1 0)
    LfkRelation.isGreaterOrEqual]

/-- The jointly-unsatisfiable congruence problem: gcc lifts `a = b` to `f(a) = f(b) = x0 =
x1`, contradicting the arithmetic gap. -/
def nccCongruenceProblem : NocProblem :=
  NocProblem.mk nccCongruenceEquations nccCongruenceArithmetic nccCongruenceInterface

/-- The jointly-satisfiable control: A-part `x0 - x1 >= 0` is consistent with `x0 = x1`. -/
def nccCongruenceSatArithmetic : List LfkConstraint :=
  [LfkConstraint.mk [LfkInt.mk 1 0, LfkInt.mk 0 1] lfkIntZero LfkRelation.isGreaterOrEqual]

/-- The jointly-satisfiable congruence problem. -/
def nccCongruenceSatProblem : NocProblem :=
  NocProblem.mk nccCongruenceEquations nccCongruenceSatArithmetic nccCongruenceInterface

/-- Kernel pin: the congruence-lifted equality `x0 = x1` is what the propagation derives —
a genuine congruence-closure call, not a literal equation. -/
theorem nccCongruencePropagatesLiftedEquality :
    nocPropagateEqualities nccCongruenceProblem = [(0, 1)] := rfl

/-- Kernel pin: the end-to-end finder CLOSES the congruence problem — congruence
propagation feeds the arithmetic refutation. -/
theorem nccCongruenceFinderHitPin :
    (nocFindRefutation nccCongruenceProblem).isSome = true := rfl

/-- Kernel pin (SAT control): on the jointly-satisfiable variant the finder returns
nothing. -/
theorem nccCongruenceFinderMissPin :
    (nocFindRefutation nccCongruenceSatProblem).isSome = false := rfl

/-- Kernel pin: the hand certificate (derive `x0 = x1`; weight the flipped equality row
and the A-row once each) is ACCEPTED on the congruence problem. -/
theorem nccCongruenceAcceptedPin :
    nocCheckCombination nccCongruenceProblem (NocCertificate.mk [(0, 1)] [0, 1, 1])
      = true := rfl

/-- CONTENT FIRE: the congruence problem's augmented A-side is rationally infeasible,
witnessed through the DISCHARGED Farkas leg (`nccAugmentedInfeasibleIffFarkasCertificate`)
by the concrete multipliers `[0, 1, 1]`. -/
theorem nccCongruenceAugmentedInfeasible :
    nccAugmentedRationallyInfeasible nccCongruenceProblem :=
  (nccAugmentedInfeasibleIffFarkasCertificate nccCongruenceProblem).mpr
    (Exists.intro [0, 1, 1] rfl)

/-- CONTENT FIRE (end-to-end through the completeness machinery): the completeness
reduction produces an accepted combination certificate for the congruence problem — Farkas
leg discharged, no premise consumed. -/
theorem nccCongruenceHasAcceptedCertificate :
    ∃ (certificate : NocCertificate),
      nocCheckCombination nccCongruenceProblem certificate = true :=
  nccAcceptedCertificateOfAugmentedInfeasible nccCongruenceProblem
    nccCongruenceAugmentedInfeasible

/-- CONTENT FIRE: the propagation census bound on the two-entry congruence interface — the
one-round propagation emits at most `nccTriangular 2 = 3` shared equalities. -/
theorem nccCongruenceCensusBoundPin :
    Nat.le (nccPairListLength (nocPropagateEqualities nccCongruenceProblem))
      (nccTriangular (nccInterfaceLength nccCongruenceProblem.sharedInterface)) :=
  nccPropagatedCountBoundedByTriangle nccCongruenceProblem

-- Congruence propagation derives x0 = x1 (a=b lifted through f). Expect: [(0, 1)]
#eval nocPropagateEqualities nccCongruenceProblem
-- The finder closes the joint congruence contradiction. Expect: true
#eval (nocFindRefutation nccCongruenceProblem).isSome
-- SAT control: the finder finds nothing on the satisfiable variant. Expect: false
#eval (nocFindRefutation nccCongruenceSatProblem).isSome
-- The hand certificate is accepted. Expect: true
#eval nocCheckCombination nccCongruenceProblem (NocCertificate.mk [(0, 1)] [0, 1, 1])
-- The found certificate is checker-accepted (finder soundness made executable). Expect: true
#eval match nocFindRefutation nccCongruenceProblem with
  | Option.some foundCertificate =>
      nocCheckCombination nccCongruenceProblem foundCertificate
  | Option.none => false
-- Census bound: triangular number of a 2-entry interface. Expect: 3
#eval nccTriangular (nccInterfaceLength nccCongruenceProblem.sharedInterface)

end FX1Poly.ComputerAlgebra

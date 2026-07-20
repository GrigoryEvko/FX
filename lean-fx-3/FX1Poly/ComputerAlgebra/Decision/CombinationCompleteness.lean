import FX1Poly.ComputerAlgebra.Decision.CombinationDispatch
import FX1Poly.ComputerAlgebra.Decision.FourierMotzkinExtension

/-! # FX1Poly/ComputerAlgebra/Decision/CombinationCompleteness — the DISSAT-COMBINE
    completeness legs (Nelson–Oppen completeness for the gcc + Farkas dispatch)

The completeness-side companion to `CombinationDispatch` (the `noc` core, whose SOUNDNESS
chain `nocCombinationSound` / `nocFinderSound` / `nocFinderRefutesJointModels` is already
proven zero-axiom).  This file supplies the reverse direction — an unsatisfiable combined
system yields an accepted refutation certificate — up to exactly ONE honest semantic wall.

## The drift this file corrects

`CombinationDispatch`'s combination-completeness wall docstring lists, among its three
missing legs, "(ii) Farkas completeness over the rationals (the sibling's owner-false
Fourier–Motzkin backward brick)".  That description is STALE: the Fourier–Motzkin
completeness brick has since been PROVEN — `lreFarkasCompletenessHolds` (in
`FourierMotzkinExtension`) inhabits `lfkFarkasCompletenessStatement` verbatim.  This file
DISCHARGES that leg for the combination: the A-side of the dispatch is no longer premised
but proven.  What remains is the E-side equality-interpolation / model-amalgamation leg,
named here as the single owner-false wall.

## What is PROVEN here (zero-axiom, no premise)

  * `nccAugmentedInfeasibleIffFarkasCertificate` — the propagation-augmented A-side is
    RATIONALLY infeasible (in the exact denominator-encoded shape of
    `lfkFarkasCompletenessStatement`'s antecedent) IFF a Farkas certificate refutes it.
    Forward = `lreFarkasCompletenessHolds`; backward = the sibling's
    `lreScaledInfeasibilityOfAcceptedCertificate`.
  * `nccAcceptedCertificateOfAugmentedInfeasible` — THE COMPLETENESS REDUCTION: if the
    propagation-augmented A-side is rationally infeasible, the combination checker accepts
    a certificate carrying exactly the propagated equalities.  The Farkas half is
    discharged (multipliers from `lreFarkasCompletenessHolds`); the equality half is
    `nocPropagatedAllCheck`.
  * `nccJointModelSatisfiesAugmented` — every joint model satisfies the augmented A-side
    (the bridge fires each propagated equality row; the A-part is a sublist).  This is the
    completeness-side companion of soundness: a Farkas refutation of the augmented A-side
    therefore refutes every joint model.
  * The finite pair census (T1 flavour): `nccPropagatedCountBoundedByTriangle` — the
    one-round propagation emits at most a triangular-number of shared equalities in the
    interface length.  This is the constructive-pigeonhole bound that would cap the fuel
    of a multi-round saturation loop (the loop itself is not built here — the committed
    finder is one-round).

## The single honest wall (owner-false, NOT proven)

  * `nccEqualityInterpolationStatement` — joint unsatisfiability of the committed
    (integer) `nocIsJointModel` semantics upgrades to RATIONAL infeasibility of the
    propagation-augmented A-side.  FALSE as literally stated over ℤ: the empty-E,
    A-part `{2x = 1}` problem is integer-joint-unsat yet rationally feasible (`x = 1/2`),
    so no Farkas certificate exists.  The reachable target is the RATIONAL relaxation, and
    even there the leg needs (a) equality-interpolation completeness of the E-engine
    (single shared equalities suffice only for CONVEX theories; ℤ-LIA is non-convex:
    `1 <= x <= 2` entails `x = 1 ∨ x = 2` with neither disjunct entailed, so non-convex
    completeness needs equality-disjunction case-split trees / arrangement enumeration),
    and (b) model amalgamation across the shared arrangement (stable infiniteness /
    cardinality agreement — a semantic condition no certificate checker inspects).  Owner
    `fxNccCombine_hasEqualityInterpolation := false`.

Given that wall as a hypothesis, `nccCombinationCompleteGivenInterpolation` (completeness)
and `nccCombinationDecidesGivenInterpolation` (the end-to-end iff: the checker DECIDES
joint unsatisfiability) both follow — soundness is unconditional, completeness rests on
the one named leg.  These conditional reductions are the first-class deliverable.

## Zero-axiom discipline

Init only; imports the `noc` dispatch and the Fourier–Motzkin completeness cascade.
Structural recursion; no `WellFounded.fix`, `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `funext`, `omega`, no `decide` on `Prop`, no wildcard arms.
The census length bound uses only the probed-clean `Nat.le` kit (`Nat.le_refl`,
`Nat.le_trans`, `Nat.succ_le_succ`, `Nat.le_add_right`, `Nat.add_le_add`).  All list
helpers are bespoke, monomorphic, cons-only.  Per-declaration gate in
`FX1PolyAudit/ComputerAlgebra/Decision/CombinationCompleteness.lean`. -/

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

/-! ## Stage B — the Farkas leg, DISCHARGED (the drift fix)

The sibling proves both directions of the rational-Farkas iff.  Specialising them to the
augmented A-side turns the combination's A-side completeness from a premise into a
theorem. -/

/-- THE A-SIDE IFF: the augmented A-side is rationally infeasible IFF a Farkas certificate
refutes it.  Forward is the proven completeness inhabitant `lreFarkasCompletenessHolds`;
backward is the proven `lreScaledInfeasibilityOfAcceptedCertificate`.  This is the leg
`CombinationDispatch`'s wall docstring still calls owner-false. -/
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

/-- THE EQUALITY-INTERPOLATION WALL (owner-false, NOT proven — FALSE over ℤ as literally
stated): joint unsatisfiability of the committed integer `nocIsJointModel` semantics
upgrades to rational infeasibility of the propagation-augmented A-side.  The integer
counterexample: empty E-part, A-part `{2x = 1}` is integer-joint-unsat yet rationally
feasible (`x = 1/2`), certificate-free.  The reachable rational target still needs
equality-interpolation completeness of the E-engine (single equalities suffice only for
convex theories; ℤ-LIA is non-convex) and model amalgamation over the shared arrangement
(stable infiniteness / cardinality agreement — a semantic side condition, never
certificate-checkable).  Owner: `fxNccCombine_hasEqualityInterpolation := false`. -/
def nccEqualityInterpolationStatement : Prop :=
  ∀ (problem : NocProblem),
    (∀ (env : List LfkInt), nocIsJointModel problem env → False) →
      nccAugmentedRationallyInfeasible problem

/-- CONDITIONAL COMPLETENESS (first-class honest reduction): GIVEN the equality-
interpolation leg, every jointly-unsatisfiable problem has an accepted combination
certificate.  The Farkas half is unconditional (discharged in Stage B); only the E-side
interpolation is premised. -/
theorem nccCombinationCompleteGivenInterpolation
    (interpolationWitness : nccEqualityInterpolationStatement) (problem : NocProblem)
    (jointUnsatWitness : ∀ (env : List LfkInt), nocIsJointModel problem env → False) :
    ∃ (certificate : NocCertificate), nocCheckCombination problem certificate = true :=
  nccAcceptedCertificateOfAugmentedInfeasible problem
    (interpolationWitness problem jointUnsatWitness)

/-- THE END-TO-END IFF (T3, conditional): GIVEN the equality-interpolation leg, the
combination checker DECIDES joint unsatisfiability — there is an accepted certificate iff
no joint model exists.  Soundness (`nocCombinationSound`) supplies the backward half with
NO premise; completeness supplies the forward half through the one named leg. -/
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

/-! ## Stage D — the finite pair census (T1: the pigeonhole fuel bound) -/

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

/-- DECIDED marker: the A-side (Farkas / rational) completeness leg of the combination is
DISCHARGED, not premised — `nccAugmentedInfeasibleIffFarkasCertificate` and
`nccAcceptedCertificateOfAugmentedInfeasible` route through the proven sibling inhabitant
`lreFarkasCompletenessHolds`.  Supersedes the stale "owner-false Farkas" leg in
`CombinationDispatch`'s completeness-wall docstring. -/
def fxNccCombine_hasFarkasLegDischarged : Bool := true

/-- DECIDED marker: the conditional completeness reduction and the end-to-end
decision iff (`nccCombinationCompleteGivenInterpolation`,
`nccCombinationDecidesGivenInterpolation`) are proven zero-axiom, resting only on the
single named equality-interpolation leg. -/
def fxNccCombine_hasConditionalCompleteness : Bool := true

/-- DECIDED marker: the finite pair census bound `nccPropagatedCountBoundedByTriangle`
caps the one-round propagation output by a triangular number of the interface length. -/
def fxNccCombine_hasPropagationCensusBound : Bool := true

/-- Owner flag for `nccEqualityInterpolationStatement` — NOT proven; FALSE over ℤ as
stated (see the wall docstring for the rational-side interpolation and amalgamation
legs). -/
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

/-- CONTENT FIRE (end-to-end through the new completeness machinery): the completeness
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

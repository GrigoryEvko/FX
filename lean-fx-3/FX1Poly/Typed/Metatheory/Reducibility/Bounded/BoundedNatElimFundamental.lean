import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedDataMemberExtraction
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedMemberWeakHeadExpansion
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.GenericDependentDataElimBridge
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedConvArm
import FX1Poly.Core.Eliminators.Nat.NatElimDependentMemberFamily
import FX1Poly.Core.Rewriting.Reduction.Step.StepSubst0ArgumentStar
import FX1Poly.Typed.Cell.UnionCellSubstitution

/-! # FX1Poly/Typed/BoundedNatElimFundamental
    — the bounded DEPENDENT recursive `natElim` / `natRec` member engine (DEP-NAT-WIRE, table-independent)

The recursive-eliminator analogue of `boolElimMemberAtBounded`.  Where `boolElim` lands in a SINGLE result
candidate (the motive at the scrutinee — its two branches supply the value-conversion directly), the genuinely
DEPENDENT recursive `natElim` cannot: the succ-ι reduct recurses at the PREDECESSOR, whose cell has type
`subst0 motive predecessor`, NOT convertible to `subst0 motive scrutinee`.  So this engine instantiates the
VALUE-INDEXED candidate family `natElimDependentReducibleMemberFamily` at

  `resultCandidateAt value term := IsReducibleMemberAtBounded env bound (subst0 motive value) term`,

the bounded member predicate of the result type at each scrutinee VALUE.  The family's four per-value premises
fall out of the bounded model:

  * `candidateMembersSN` — a bounded member is strongly normalizing (CR1 of its own candidate);
  * `headExpand` — the contractum member's candidate absorbs the redex (`ReducibleTypeAtBounded.\
    memberWeakHeadExpansion`);
  * `memberOfStronglyNormalizingNeutral` — the result type at the value is bound-reducible
    (`resultTypeReducibleAtValue`, the value-general motive recovery), so its candidate takes the stuck neutral
    by CR3;
  * `candidateStable` — the result type's reduction lockstep `subst0 motive value ↠ subst0 motive valueReduct`
    (`StepStar.subst0Argument`) gives a `Conv` the member rides both ways (`memberConvAtBounded`), the type
    reducibility at each end supplied by `resultTypeReducibleAtValue` (the value's `dataTaitCandidate` carries to
    its reducts by step-closure).

The motive / branch strong normalization, the zero-branch member, the recursive succ-branch substitution closure,
and the succ-contractum termination are threaded as hypotheses — exactly the recursive-eliminator obligations the
elim-FT row discharges (the contractum-SN hypothesis is the standing recursive-eliminator residue every `natElim`
member carries, per FTGEN-HONESTY).

## Zero-axiom verification

Direct instantiation of the Core `natElimDependentReducibleMemberFamily` / `natRecDependentReducibleMemberFamily`
with the bounded member predicate, the four per-value premises discharged by the shipped bounded lemmas
(`natMemberAtBounded_dataTaitCandidate`, `ReducibleTypeAtBounded.memberWeakHeadExpansion` / `.isReducibilityCandidate`,
`dependentMotiveResultTypeReducibleAtBoundedValue`, `memberConvAtBounded`, `StepStar.subst0Argument`).  No `funext`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax
open StepStar

/-- `dataTaitCandidate IsNatStructured` is closed under a whole reduction chain (CR2 iterated) — the bounded
bridge needs the reducts of a structured value to stay structured (so their result types are reducible). -/
private theorem natStructuredClosedUnderStepStar {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) (member : dataTaitCandidate IsNatStructured source) :
    dataTaitCandidate IsNatStructured target := by
  induction chain with
  | refl _ => exact member
  | trans firstStep _restChain restInductiveHypothesis =>
      exact restInductiveHypothesis (member.closedUnderStep firstStep)

/-- **The bounded dependent recursive `natElim` member engine.**  Instantiates the value-indexed candidate family
at the bounded member predicate.  Given the result type at every nat-structured value is bound-reducible
(`resultTypeReducibleAtValue`), the scrutinee is a bound-reducible `Nat` member, the motive / branches are
strongly normalizing, the zero branch is a result member at `natZero`, the succ branch's substitution closure
takes a predecessor-cell member to the succ-reduct member, and the succ-contractum terminates, the `natElim` cell
is a bound-reducible member of the dependent result type `subst0 motive scrutinee`. -/
theorem natElimMemberAtBounded {closingScope : Nat} (env : Nat → Nat) (bound : Nat)
    {motive : RawTerm (closingScope + 1 + 1)} {scrutinee zeroBranch : RawTerm (closingScope + 1)}
    {succBranch : RawTerm (closingScope + 1 + 2)}
    (resultTypeReducibleAtValue : ∀ {value : RawTerm (closingScope + 1)},
      dataTaitCandidate IsNatStructured value →
      IsReducibleTypeAtBounded env bound (RawTerm.subst0 motive value))
    (scrutineeNatMember :
      IsReducibleMemberAtBounded env bound (natTypeCell (scope := closingScope + 1)) scrutinee)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (succBranchStronglyNormalizing : IsStronglyNormalizing succBranch)
    (zeroBranchMember :
      IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive natZeroCell) zeroBranch)
    (succBranchSubstClosed : ∀ {predecessor : RawTerm (closingScope + 1)},
        dataTaitCandidate IsNatStructured predecessor →
        IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive predecessor)
          (natElimCellSpine motive predecessor zeroBranch succBranch) →
        IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive (natSuccCell predecessor))
          (RawTerm.subst
            (RawTermSubst.cons (natElimCellSpine motive predecessor zeroBranch succBranch)
              (RawTermSubst.singleton predecessor))
            succBranch)) :
    IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive scrutinee)
      (natElimCell motive zeroBranch succBranch scrutinee) :=
  natElimDependentReducibleMemberFamilySelfContained
    (resultCandidateAt := fun value term =>
      IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive value) term)
    (candidateMembersSN := fun _structured member => by
      obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
      exact (ReducibleTypeAtBounded.isReducibilityCandidate candidateReducible).stronglyNormalizing
        termInCandidate)
    (headExpand := fun _structured weakHeadStep contractumMember redexStronglyNormalizing => by
      obtain ⟨candidate, candidateReducible, contractumInCandidate⟩ := contractumMember
      exact ⟨candidate, candidateReducible,
        ReducibleTypeAtBounded.memberWeakHeadExpansion candidateReducible weakHeadStep
          redexStronglyNormalizing contractumInCandidate⟩)
    (memberOfStronglyNormalizingNeutral := fun structured neutralStronglyNormalizing neutral => by
      obtain ⟨candidate, candidateReducible⟩ := resultTypeReducibleAtValue structured
      exact ⟨candidate, candidateReducible,
        (ReducibleTypeAtBounded.isReducibilityCandidate candidateReducible).memberOfStronglyNormalizingNeutral
          neutralStronglyNormalizing neutral⟩)
    (candidateStable := fun structured reaches =>
      ⟨fun member =>
        memberConvAtBounded env bound member
          (resultTypeReducibleAtValue (natStructuredClosedUnderStepStar reaches structured))
          (Conv.fromStepStar (StepStar.subst0Argument motive reaches)),
       fun member =>
        memberConvAtBounded env bound member (resultTypeReducibleAtValue structured)
          (Conv.sym (Conv.fromStepStar (StepStar.subst0Argument motive reaches)))⟩)
    motiveStronglyNormalizing zeroBranchMember succBranchStronglyNormalizing
    (fun predecessorStructured predecessorCellMember =>
      succBranchSubstClosed predecessorStructured predecessorCellMember)
    (natMemberAtBounded_dataTaitCandidate scrutineeNatMember)

/-- **The bounded dependent recursive `natRec` member engine** — the `gen_natRec` twin of
`natElimMemberAtBounded`.  Identical instantiation of the value-indexed candidate family at the bounded member
predicate, with the `natRecCellSpine` / `natRecCell` formers. -/
theorem natRecMemberAtBounded {closingScope : Nat} (env : Nat → Nat) (bound : Nat)
    {motive : RawTerm (closingScope + 1 + 1)} {scrutinee zeroBranch : RawTerm (closingScope + 1)}
    {succBranch : RawTerm (closingScope + 1 + 2)}
    (resultTypeReducibleAtValue : ∀ {value : RawTerm (closingScope + 1)},
      dataTaitCandidate IsNatStructured value →
      IsReducibleTypeAtBounded env bound (RawTerm.subst0 motive value))
    (scrutineeNatMember :
      IsReducibleMemberAtBounded env bound (natTypeCell (scope := closingScope + 1)) scrutinee)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (succBranchStronglyNormalizing : IsStronglyNormalizing succBranch)
    (zeroBranchMember :
      IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive natZeroCell) zeroBranch)
    (succBranchSubstClosed : ∀ {predecessor : RawTerm (closingScope + 1)},
        dataTaitCandidate IsNatStructured predecessor →
        IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive predecessor)
          (natRecCellSpine motive predecessor zeroBranch succBranch) →
        IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive (natSuccCell predecessor))
          (RawTerm.subst
            (RawTermSubst.cons (natRecCellSpine motive predecessor zeroBranch succBranch)
              (RawTermSubst.singleton predecessor))
            succBranch)) :
    IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive scrutinee)
      (natRecCell motive zeroBranch succBranch scrutinee) :=
  natRecDependentReducibleMemberFamilySelfContained
    (resultCandidateAt := fun value term =>
      IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive value) term)
    (candidateMembersSN := fun _structured member => by
      obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
      exact (ReducibleTypeAtBounded.isReducibilityCandidate candidateReducible).stronglyNormalizing
        termInCandidate)
    (headExpand := fun _structured weakHeadStep contractumMember redexStronglyNormalizing => by
      obtain ⟨candidate, candidateReducible, contractumInCandidate⟩ := contractumMember
      exact ⟨candidate, candidateReducible,
        ReducibleTypeAtBounded.memberWeakHeadExpansion candidateReducible weakHeadStep
          redexStronglyNormalizing contractumInCandidate⟩)
    (memberOfStronglyNormalizingNeutral := fun structured neutralStronglyNormalizing neutral => by
      obtain ⟨candidate, candidateReducible⟩ := resultTypeReducibleAtValue structured
      exact ⟨candidate, candidateReducible,
        (ReducibleTypeAtBounded.isReducibilityCandidate candidateReducible).memberOfStronglyNormalizingNeutral
          neutralStronglyNormalizing neutral⟩)
    (candidateStable := fun structured reaches =>
      ⟨fun member =>
        memberConvAtBounded env bound member
          (resultTypeReducibleAtValue (natStructuredClosedUnderStepStar reaches structured))
          (Conv.fromStepStar (StepStar.subst0Argument motive reaches)),
       fun member =>
        memberConvAtBounded env bound member (resultTypeReducibleAtValue structured)
          (Conv.sym (Conv.fromStepStar (StepStar.subst0Argument motive reaches)))⟩)
    motiveStronglyNormalizing zeroBranchMember succBranchStronglyNormalizing
    (fun predecessorStructured predecessorCellMember =>
      succBranchSubstClosed predecessorStructured predecessorCellMember)
    (natMemberAtBounded_dataTaitCandidate scrutineeNatMember)

end FX1Poly.Typed

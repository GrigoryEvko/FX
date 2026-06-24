import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedDataMemberExtraction
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedMemberWeakHeadExpansion
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.GenericDependentDataElimBridge
import FX1Poly.Typed.Metatheory.Denote.Bounded.DenoteKeyedBoundedConvArm
import FX1Poly.Core.Eliminators.List.ListElimDependentMemberFamily
import FX1Poly.Core.Rewriting.Reduction.Step.StepSubst0ArgumentStar
import FX1Poly.Typed.Cell.UnionCellSubstitution

/-! # FX1Poly/Typed/BoundedListElimFundamental
    — the bounded DEPENDENT recursive `listElim` member engine (DEP-LIST sub-bridge, table-independent)

The BINARY recursive-eliminator analogue of `natElimMemberAtBounded`.  Where `boolElim` lands in a SINGLE result
candidate, the genuinely DEPENDENT recursive `listElim` cannot: the cons-ι reduct recurses at the TAIL, whose cell
has type `subst0 motive tail`, NOT convertible to `subst0 motive scrutinee`.  So this engine instantiates the
VALUE-INDEXED candidate family `listElimDependentReducibleMemberFamily` at

  `resultCandidateAt value term := IsReducibleMemberAtBounded env bound (subst0 motive value) term`,

the bounded member predicate of the result type at each scrutinee VALUE.  The family's four per-value premises fall
out of the bounded model EXACTLY as for nat — they are recursion-shape-agnostic:

  * `candidateMembersSN` — a bounded member is strongly normalizing (CR1 of its own candidate);
  * `headExpand` — the contractum member's candidate absorbs the redex (`ReducibleTypeAtBounded.\
    memberWeakHeadExpansion`);
  * `memberOfStronglyNormalizingNeutral` — the result type at the value is bound-reducible
    (`resultTypeReducibleAtValue`), so its candidate takes the stuck neutral by CR3;
  * `candidateStable` — the result type's reduction lockstep `subst0 motive value ↠ subst0 motive valueReduct`
    (`StepStar.subst0Argument`) gives a `Conv` the member rides both ways (`memberConvAtBounded`).

The ONLY differences from nat are the recursor-specific premises: the `nilBranch` member sits at
`subst0 motive listNilCell`; the `cons`-ι reduct is the NESTED app spine `listElimConsContractum` (not a subst), so
nat's `succBranchSubstClosed` becomes `consBranchApplicationClosed` (head SN + tail candidate member + recursive
tail-cell member → the app-spine member at `subst0 motive (listCons head tail)`); and the scrutinee, a bound-reducible
member of `listTypeCell elementType`, is read as `dataTaitCandidate IsListStructured` via
`listMemberAtBounded_dataTaitCandidate` (DEP-LIST-MODEL).

## Zero-axiom verification

Direct instantiation of the Core `listElimDependentReducibleMemberFamily` with the bounded member predicate, the
four per-value premises discharged by the shipped bounded lemmas (`listMemberAtBounded_dataTaitCandidate`,
`ReducibleTypeAtBounded.memberWeakHeadExpansion` / `.isReducibilityCandidate` / `.memberOfStronglyNormalizingNeutral`,
`memberConvAtBounded`, `StepStar.subst0Argument`).  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax
open StepStar

/-- The `listElim` cons-ι contractum — mirrors Core's own private `listElimConsContractum` byte-for-byte (defeq to
the family file's copy, so the recursor premises align positionally). -/
private abbrev listElimConsContractum {scope : Nat} (motive : RawTerm (scope + 1))
    (consBranch head tail nilBranch : RawTerm scope) : RawTerm scope :=
  .mkGen .gen_app ()
    (.childCons
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_app () (.childCons consBranch (.childCons head .childNil)))
          (.childCons tail .childNil)))
      (.childCons
        (.mkGen .gen_listElim ()
          (.childCons motive
            (.childCons nilBranch
              (.childCons consBranch (.childCons tail .childNil)))))
        .childNil))

/-- `dataTaitCandidate IsListStructured` is closed under a whole reduction chain (CR2 iterated) — the bounded
bridge needs the reducts of a structured value to stay structured (so their result types are reducible). -/
private theorem listStructuredClosedUnderStepStar {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) (member : dataTaitCandidate IsListStructured source) :
    dataTaitCandidate IsListStructured target := by
  induction chain with
  | refl _ => exact member
  | trans firstStep _restChain restInductiveHypothesis =>
      exact restInductiveHypothesis (member.closedUnderStep firstStep)

/-- **The bounded dependent recursive `listElim` member engine.**  Instantiates the value-indexed candidate family
at the bounded member predicate.  Given the result type at every list-structured value is bound-reducible
(`resultTypeReducibleAtValue`), the scrutinee is a bound-reducible `list` member, the motive / branches are strongly
normalizing, the nil branch is a result member at `listNil`, and the cons branch's application closure takes a
tail-cell member to the cons-reduct member, the `listElim` cell is a bound-reducible member of the dependent result
type `subst0 motive scrutinee` — whole-cell SN is self-contained (the value-indexed family derives it from the
in-recursion cons-contractum membership), so no SN-of-branches premise is needed. -/
theorem listElimMemberAtBounded {closingScope : Nat} (env : Nat → Nat) (bound : Nat)
    {motive : RawTerm (closingScope + 1 + 1)}
    {scrutinee nilBranch consBranch elementType : RawTerm (closingScope + 1)}
    (resultTypeReducibleAtValue : ∀ {value : RawTerm (closingScope + 1)},
      dataTaitCandidate IsListStructured value →
      IsReducibleTypeAtBounded env bound (RawTerm.subst0 motive value))
    (scrutineeListMember :
      IsReducibleMemberAtBounded env bound (listTypeCell elementType) scrutinee)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (consBranchStronglyNormalizing : IsStronglyNormalizing consBranch)
    (nilBranchMember :
      IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive listNilCell) nilBranch)
    (consBranchApplicationClosed : ∀ {head tail : RawTerm (closingScope + 1)},
        IsStronglyNormalizing head →
        dataTaitCandidate IsListStructured tail →
        IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive tail)
          (listElimCellSpine motive tail nilBranch consBranch) →
        IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive (listConsCell head tail))
          (listElimConsContractum motive consBranch head tail nilBranch)) :
    IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive scrutinee)
      (listElimCell motive scrutinee nilBranch consBranch) :=
  listElimDependentReducibleMemberFamilySelfContained
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
          (resultTypeReducibleAtValue (listStructuredClosedUnderStepStar reaches structured))
          (Conv.fromStepStar (StepStar.subst0Argument motive reaches)),
       fun member =>
        memberConvAtBounded env bound member (resultTypeReducibleAtValue structured)
          (Conv.sym (Conv.fromStepStar (StepStar.subst0Argument motive reaches)))⟩)
    motiveStronglyNormalizing nilBranchMember consBranchStronglyNormalizing
    (fun headStronglyNormalizing tailStructured tailCellMember =>
      consBranchApplicationClosed headStronglyNormalizing tailStructured tailCellMember)
    (listMemberAtBounded_dataTaitCandidate scrutineeListMember)

/-- **The `+1`-closing dependent recursive `listElim` fundamental-theorem arm (table-independent engine).**  The
recursive twin of `fundamentalEitherMatchAtBoundedSucc` (non-recursive, scrutinee-fixed result candidate) crossed
with `fundamentalNatElimAtBoundedSucc` (recursive, value-indexed result candidate): like `natElim`, `listElim`'s
cons-ι recurses at the TAIL, whose cell has type `subst0 motive tail` not convertible to `subst0 motive scrutinee`,
so the result candidate must be VALUE-INDEXED — the engine `listElimMemberAtBounded` instantiates the value-indexed
candidate family; this bridge threads the closing substitution and discharges its hypotheses from the four
obligation fundamental conclusions, the motive/cons-branch strong-normalization (read off the obligations), and the
recursion-closing application residue (consBranchApplicationClosed — threaded, the eitherMatch-style
branch-application member that needs the closed-term substitution-SN content, discharged at the consistency leg).
Whole-cell SN is self-contained in the engine (no SN-of-branches premise) — the former universally-false
cons-contractum SN residue is gone (FTGEN-13.1).

The keystone discharges are the `resultTypeReducibleAtValue` family and the `nilBranchMember` reshape.  Because
`listTypeCell A` pins to the CONTENT-FREE `dataFlat` candidate (DEP-LIST-MODEL — the `nat` route), a list-structured
recursion value is a `listTypeCell` member for any element type (`listMemberAtBounded_ofDataTaitCandidate`); feeding
the motive's universe membership at the value-extended environment (`dependentMotiveResultTypeReducibleAtBoundedValue`)
then yields the result type's reducibility at that value.  The nil branch's obligation conclusion lands at
`subst σ (subst0 motive listNil)`; `subst0_subst_commute` + `subst_listNilCell` carry it to the engine's
`subst0 (subst (lift σ) motive) listNil` (the `natElim` zero-branch reshape).  The `listElim` twin of the nat / either
bridges; the elim-FT row wires it from `listElimRule`'s obligation IHs. -/
theorem fundamentalListElimAtBoundedSucc {profile : PolyProfile} {scope : Nat} (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile scope)
    {motive : RawTerm (scope + 1)} {scrutinee nilBranch consBranch elementType : RawTerm scope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (motiveConclusion : FundamentalConclusionAtBoundedSucc env bound
      (context.cons (listTypeCell elementType)) motive (universeCodeCell levelExpr flag))
    (scrutineeConclusion : FundamentalConclusionAtBoundedSucc env bound context scrutinee
      (listTypeCell elementType))
    (nilBranchConclusion : FundamentalConclusionAtBoundedSucc env bound context nilBranch
      (RawTerm.subst0 motive listNilCell))
    (consBranchConclusion : FundamentalConclusionAtBoundedSucc env bound context consBranch
      (listElimDependentConsBranchType motive elementType))
    (consBranchApplicationClosed : ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ {head tail : RawTerm (targetScope + 1)},
          IsStronglyNormalizing head →
          dataTaitCandidate IsListStructured tail →
          IsReducibleMemberAtBounded env bound
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) motive) tail)
            (listElimCellSpine (RawTerm.subst (RawTermSubst.lift substitution) motive) tail
              (RawTerm.subst substitution nilBranch) (RawTerm.subst substitution consBranch)) →
          IsReducibleMemberAtBounded env bound
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) motive) (listConsCell head tail))
            (listElimConsContractum (RawTerm.subst (RawTermSubst.lift substitution) motive)
              (RawTerm.subst substitution consBranch) head tail (RawTerm.subst substitution nilBranch))) :
    FundamentalConclusionAtBoundedSucc env bound context
      (listElimCell motive scrutinee nilBranch consBranch) (RawTerm.subst0 motive scrutinee) := by
  intro _targetScope substitution envReducible
  rw [RawTerm.subst0_subst_commute motive scrutinee substitution]
  refine listElimMemberAtBounded env bound
    (motive := RawTerm.subst (RawTermSubst.lift substitution) motive)
    (scrutinee := RawTerm.subst substitution scrutinee)
    (nilBranch := RawTerm.subst substitution nilBranch)
    (consBranch := RawTerm.subst substitution consBranch)
    (elementType := RawTerm.subst substitution elementType)
    (fun {value} structured =>
      dependentMotiveResultTypeReducibleAtBoundedValue env bound context motiveConclusion substitution
        envReducible (listMemberAtBounded_ofDataTaitCandidate structured))
    (scrutineeConclusion substitution envReducible)
    (dependentMotiveUnderBinderStronglyNormalizing env bound context motiveConclusion scrutineeConclusion
      substitution envReducible)
    (stronglyNormalizing_of_memberAtBoundedSucc (consBranchConclusion substitution envReducible))
    ?nilBranchMember
    (consBranchApplicationClosed substitution envReducible)
  case nilBranchMember =>
    have nilMem := nilBranchConclusion substitution envReducible
    rw [RawTerm.subst0_subst_commute motive listNilCell substitution, subst_listNilCell] at nilMem
    exact nilMem

end FX1Poly.Typed

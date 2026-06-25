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

/-- **The bounded dependent recursive `listElim` member engine — REACH-AWARE re-key.**  Instantiates the
value-indexed candidate family at the bounded member predicate, the value index carrying its REACH-AWARE list
membership (over the scrutinee's recovered element candidate `elementCandidate`) rather than the content-free
structural predicate.  Given the result type at every reach-aware list value is bound-reducible
(`resultTypeReducibleAtValue`), the scrutinee is a reach-aware `list` member, the motive / branches are strongly
normalizing, the nil branch is a result member at `listNil`, and the cons branch's application closure takes a
tail-cell member to the cons-reduct member, the `listElim` cell is a bound-reducible member of the dependent result
type `subst0 motive scrutinee` — whole-cell SN is self-contained (the value-indexed family derives it from the
in-recursion cons-contractum membership), so no SN-of-branches premise is needed.  The reach-aware value index is
what lets `resultTypeReducibleAtValue` rebuild a `listTypeCell` member at each reached value (via
`listMemberAtBounded_ofReachAware`) post gate-1 swap 4, where a bare structured value no longer carries the element
membership the carrier-aware model demands. -/
theorem listElimMemberAtBounded {closingScope : Nat} (env : Nat → Nat) (bound : Nat)
    {motive : RawTerm (closingScope + 1 + 1)}
    {scrutinee nilBranch consBranch elementType : RawTerm (closingScope + 1)}
    {elementCandidate : RawTerm (closingScope + 1) → Prop}
    (elementReducible : ReducibleTypeAtBounded env bound elementType elementCandidate)
    (resultTypeReducibleAtValue : ∀ {value : RawTerm (closingScope + 1)},
      reachAwareListCandidate elementCandidate value →
      IsReducibleTypeAtBounded env bound (RawTerm.subst0 motive value))
    (scrutineeReachAware : reachAwareListCandidate elementCandidate scrutinee)
    (motiveStronglyNormalizing : IsStronglyNormalizing motive)
    (consBranchStronglyNormalizing : IsStronglyNormalizing consBranch)
    (nilBranchMember :
      IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive listNilCell) nilBranch)
    (consBranchApplicationClosed : ∀ {head tail : RawTerm (closingScope + 1)},
        elementCandidate head →
        reachAwareListCandidate elementCandidate tail →
        IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive tail)
          (listElimCellSpine motive tail nilBranch consBranch) →
        IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive (listConsCell head tail))
          (listElimConsContractum motive consBranch head tail nilBranch)) :
    IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive scrutinee)
      (listElimCell motive scrutinee nilBranch consBranch) :=
  listElimDependentReducibleMemberFamilySelfContained
    (carrierCandidate := elementCandidate)
    (resultCandidateAt := fun value term =>
      IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive value) term)
    (candidateMembersSN := fun _reachAware member => by
      obtain ⟨candidate, candidateReducible, termInCandidate⟩ := member
      exact (ReducibleTypeAtBounded.isReducibilityCandidate candidateReducible).stronglyNormalizing
        termInCandidate)
    (headExpand := fun _reachAware weakHeadStep contractumMember redexStronglyNormalizing => by
      obtain ⟨candidate, candidateReducible, contractumInCandidate⟩ := contractumMember
      exact ⟨candidate, candidateReducible,
        ReducibleTypeAtBounded.memberWeakHeadExpansion candidateReducible weakHeadStep
          redexStronglyNormalizing contractumInCandidate⟩)
    (memberOfStronglyNormalizingNeutral := fun reachAware neutralStronglyNormalizing neutral => by
      obtain ⟨candidate, candidateReducible⟩ := resultTypeReducibleAtValue reachAware
      exact ⟨candidate, candidateReducible,
        (ReducibleTypeAtBounded.isReducibilityCandidate candidateReducible).memberOfStronglyNormalizingNeutral
          neutralStronglyNormalizing neutral⟩)
    (candidateStable := fun reachAware reaches =>
      ⟨fun member =>
        memberConvAtBounded env bound member
          (resultTypeReducibleAtValue (reachAwareListCandidate_closedUnderStepStar reachAware reaches))
          (Conv.fromStepStar (StepStar.subst0Argument motive reaches)),
       fun member =>
        memberConvAtBounded env bound member (resultTypeReducibleAtValue reachAware)
          (Conv.sym (Conv.fromStepStar (StepStar.subst0Argument motive reaches)))⟩)
    motiveStronglyNormalizing nilBranchMember consBranchStronglyNormalizing
    (fun headMember tailReachAware tailCellMember =>
      consBranchApplicationClosed headMember tailReachAware tailCellMember)
    scrutineeReachAware

/-- **★ The cons-branch application residue, DISCHARGED from the reach-aware list candidate.**  The RECURSIVE
analogue of `eitherMatchLeftBranchMemberFromReachAware`: given the substituted cons branch is a member of the
three-fold dependent cons-branch type `(head : A) → (tail : List A) → (rec : motive tail) → motive (cons head
tail)`, the reached cons cell's head lies in the element candidate, the tail is a reach-aware list member, and the
recursive `listElim … tail` cell is a member at `subst0 motive tail`, the app-spine contractum
`app (app (app consBranch head) tail) (listElim … tail)` is a member of the cons-ι output type
`subst0 motive (cons head tail)`.  Three `applicationMemberAtBounded` steps, each reshaping the consumed Π's
codomain by the shipped App-1/2/3 pins (`subst0_listElimConsBranchOuterCodomain_afterHead`,
`subst0_listElimConsTypeAfterHead_afterHeadTail`, `subst0_listElimConsTypeAfterHeadTailCodomain_consIota`); the
head's element membership and the tail's `listTypeCell` membership (`listMemberAtBounded_ofReachAware`) come off the
reach-aware substrate, the recursive argument off the engine's in-recursion cell member.  This is the content the
threaded `consBranchApplicationClosed` residue used to carry — now dissolved (FTGEN-13.1, the recursive twin of the
eitherMatch branch discharge): the entire union elim dispatcher `fundamentalElimRowAtBoundedSucc` becomes
residue-free, the DEP-GLUE `elimFundamental` premise body. -/
theorem listElimConsBranchMemberFromReachAware {scope : Nat} (env : Nat → Nat) (bound : Nat)
    {elementType : RawTerm scope} {motive : RawTerm (scope + 1)}
    {nilBranch consBranch : RawTerm scope} {elementCandidate : RawTerm scope → Prop}
    (elementReducible : ReducibleTypeAtBounded env bound elementType elementCandidate)
    (consBranchMember : IsReducibleMemberAtBounded env bound
      (listElimDependentConsBranchType motive elementType) consBranch)
    {head tail : RawTerm scope}
    (headMember : elementCandidate head)
    (tailReachAware : reachAwareListCandidate elementCandidate tail)
    (tailCellMember : IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive tail)
      (listElimCellSpine motive tail nilBranch consBranch)) :
    IsReducibleMemberAtBounded env bound (RawTerm.subst0 motive (listConsCell head tail))
      (listElimConsContractum motive consBranch head tail nilBranch) := by
  have headMem : IsReducibleMemberAtBounded env bound elementType head :=
    ⟨elementCandidate, elementReducible, headMember⟩
  have tailMem : IsReducibleMemberAtBounded env bound (listTypeCell elementType) tail :=
    listMemberAtBounded_ofReachAware elementReducible tailReachAware
  have app1 := applicationMemberAtBounded env bound consBranchMember headMem
  rw [subst0_listElimConsBranchOuterCodomain_afterHead] at app1
  have app2 := applicationMemberAtBounded env bound app1 tailMem
  rw [subst0_listElimConsTypeAfterHead_afterHeadTail] at app2
  have app3 := applicationMemberAtBounded env bound app2 tailCellMember
  rw [subst0_listElimConsTypeAfterHeadTailCodomain_consIota] at app3
  exact app3

/-- **The `+1`-closing dependent recursive `listElim` fundamental-theorem arm (table-independent engine).**  The
recursive twin of `fundamentalEitherMatchAtBoundedSucc` (non-recursive, scrutinee-fixed result candidate) crossed
with `fundamentalNatElimAtBoundedSucc` (recursive, value-indexed result candidate): like `natElim`, `listElim`'s
cons-ι recurses at the TAIL, whose cell has type `subst0 motive tail` not convertible to `subst0 motive scrutinee`,
so the result candidate must be VALUE-INDEXED — the engine `listElimMemberAtBounded` instantiates the value-indexed
candidate family; this bridge threads the closing substitution and discharges its hypotheses from the four
obligation fundamental conclusions and the motive/cons-branch strong-normalization (read off the obligations).
The recursion-closing cons-branch application is now discharged INTERNALLY (FTGEN-13.1): the engine's
`consBranchApplicationClosed` is supplied by `listElimConsBranchMemberFromReachAware` over the substituted
cons-branch obligation member, so NO residue is threaded — the recursive twin of the eitherMatch branch discharge.
Whole-cell SN is self-contained in the engine (no SN-of-branches premise) too.

The keystone discharges are the `resultTypeReducibleAtValue` family and the `nilBranchMember` reshape.  Post
gate-1 swap 4 `listTypeCell A` rides the carrier-aware `dataUnaryCarrierAware @ listLike` candidate
`reachAwareListCandidate elementCandidate` (element candidate recovered from the scrutinee via
`listMemberAtBounded_carrierAware`), so each reached value's reach-aware membership rebuilds a `listTypeCell` member
(`listMemberAtBounded_ofReachAware`); feeding the motive's universe membership at the value-extended environment
(`dependentMotiveResultTypeReducibleAtBoundedValue`) then yields the result type's reducibility at that value.  The
nil branch's obligation conclusion lands at
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
      (listElimDependentConsBranchType motive elementType)) :
    FundamentalConclusionAtBoundedSucc env bound context
      (listElimCell motive scrutinee nilBranch consBranch) (RawTerm.subst0 motive scrutinee) := by
  intro _targetScope substitution envReducible
  rw [RawTerm.subst0_subst_commute motive scrutinee substitution]
  obtain ⟨elementCandidate, elementReducible, scrutineeReachAware⟩ :=
    listMemberAtBounded_carrierAware (scrutineeConclusion substitution envReducible)
  have consBranchSubstMember :
      IsReducibleMemberAtBounded env bound
        (listElimDependentConsBranchType (RawTerm.subst (RawTermSubst.lift substitution) motive)
          (RawTerm.subst substitution elementType))
        (RawTerm.subst substitution consBranch) := by
    have member := consBranchConclusion substitution envReducible
    rwa [subst_listElimDependentConsBranchType_iterateLift] at member
  refine listElimMemberAtBounded env bound
    (motive := RawTerm.subst (RawTermSubst.lift substitution) motive)
    (scrutinee := RawTerm.subst substitution scrutinee)
    (nilBranch := RawTerm.subst substitution nilBranch)
    (consBranch := RawTerm.subst substitution consBranch)
    (elementType := RawTerm.subst substitution elementType)
    (elementCandidate := elementCandidate)
    elementReducible
    (fun {value} reachAware =>
      dependentMotiveResultTypeReducibleAtBoundedValue env bound context motiveConclusion substitution
        envReducible (listMemberAtBounded_ofReachAware elementReducible reachAware))
    scrutineeReachAware
    (dependentMotiveUnderBinderStronglyNormalizing env bound context motiveConclusion scrutineeConclusion
      substitution envReducible)
    (stronglyNormalizing_of_memberAtBoundedSucc (consBranchConclusion substitution envReducible))
    ?nilBranchMember
    (fun headMember tailReachAware tailCellMember =>
      listElimConsBranchMemberFromReachAware env bound elementReducible consBranchSubstMember
        headMember tailReachAware tailCellMember)
  case nilBranchMember =>
    have nilMem := nilBranchConclusion substitution envReducible
    rw [RawTerm.subst0_subst_commute motive listNilCell substitution, subst_listNilCell] at nilMem
    exact nilMem

end FX1Poly.Typed

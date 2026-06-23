import FX1Poly.Typed.Engine.RuleTables.ElimRuleTable
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.GenericDependentDataElimBridge
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedBoolElimFundamental
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedCodomainOpenSN
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedNatElimFundamentalBridge
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedEitherMatchFundamental
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedOptionMatchFundamental
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedPairProjectionFundamental
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedListElimFundamental
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedIdJFundamental

/-! # FX1Poly/Typed/DependentDataElimRows
    — the DEPENDENT data-eliminator FT rows (TYTAB-4 step 4, the elim side's data-eliminator cases)

The data eliminators whose dependent member witness is a SHIPPED bounded-member engine.  Each row is a
pure wiring of its `fundamental…AtBoundedSucc` bridge: extract the rule's obligation IHs by their `List.Mem`
position, discharge the under-binder motive strong-normalization premise the bridge cannot read off a
sub-conclusion, feed the bridge, and close (its conclusion is definitionally the row's goal, the rule's
`memberCell` / `outputType` reducing to the cell / `subst0 motive scrutinee`).

This is the data-eliminator twin of `GeneralElimRows` (the `app` / `pathApp` rows): there the codomain
reducibility is bundled inside the Π candidate, here the dependent result type rides a SEPARATE motive
obligation, so the row additionally feeds the motive premise and discharges its under-binder SN.

`boolElim` is the first row (DEP-BOOL-ROW).  Its bridge `fundamentalBoolElimAtBoundedSucc`
(`BoundedBoolElimFundamental`) is table-independent; this row connects it to `boolElimRule`'s four
obligations.  The motive's under-binder SN is reflected from the motive obligation IH by the
pathLam/genFormationPi recipe: fill the `Bool` binder with the scrutinee's reducible member (via
`ReducibleEnvAtBounded.cons`), reshape the filled membership with `subst_cons_eq_subst0_lift`, and reflect
open-body SN with `codomainOpenStronglyNormalizing_ofBoundedFilledMember`.  The `nat` / `option` / `either`
/ `proj` / `list` / `id` rows land here as their bridges ship.

## Zero-axiom verification

`fundamentalBoolElimAtBoundedSucc` (the dependent member engine) + the under-binder SN reflection
(`ReducibleEnvAtBounded.cons` + `subst_cons_eq_subst0_lift` + `codomainOpenStronglyNormalizing_ofBoundedFilledMember`)
+ the propext-clean `List.Mem` obligation witnesses.  No induction, no `funext`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- The `listElim` cons-ι contractum — byte-for-byte identical to the bridge file's own private copy (defeq to the
Core family file's copy), so the `fundamentalListElimRowAtBoundedSucc` premise types align positionally with what
`fundamentalListElimAtBoundedSucc` expects.  Replicated locally because that copy is `private` to its file. -/
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

/-- The dependent `gen_boolElim` elim FT member: `boolElim motive scrutinee thenBranch elseBranch` is a
bound-reducible member of the DEPENDENT result type `subst0 motive scrutinee`, given the scrutinee is a `Bool`
member, the two branches are members of the motive over `true` / `false` (`subst0 motive boolTrue/False`), and
the motive is a type under `Bool`.  Output type `subst0 motive scrutinee` is the row's `outputType`; the member
witness is the shipped `fundamentalBoolElimAtBoundedSucc` engine, fed the four obligation IHs.  The motive's
under-binder strong normalization — the one premise not on a sub-conclusion — is reflected from the motive
obligation IH by filling the `Bool` binder with the scrutinee's reducible member. -/
theorem fundamentalBoolElimRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren boolElimRule.argShifts scope}
    {params : RawTermChildren boolElimRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ boolElimRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context (boolElimRule.memberCell scope args)
      (boolElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons scrutinee (.childCons thenBranch (.childCons elseBranch .childNil))),
    .childNil =>
    -- The four obligation IHs, dispatched by `List.Mem` position over `boolElimRule.obligations`.
    have scrutineeConclusion :
        FundamentalConclusionAtBoundedSucc env bound context scrutinee boolTypeCell :=
      premisesFundamental _ (List.Mem.head _)
    have thenBranchConclusion :
        FundamentalConclusionAtBoundedSucc env bound context thenBranch
          (RawTerm.subst0 motive (RawTerm.mkGen .gen_boolTrue () .childNil)) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.head _))
    have elseBranchConclusion :
        FundamentalConclusionAtBoundedSucc env bound context elseBranch
          (RawTerm.subst0 motive (RawTerm.mkGen .gen_boolFalse () .childNil)) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have motiveConclusion :
        FundamentalConclusionAtBoundedSucc env bound (context.cons boolTypeCell) motive
          (universeCodeCell level0 flag) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    -- The dependent `boolElim` member engine, with the under-binder motive SN reflected from the motive IH:
    -- fill the `Bool` binder with the scrutinee's reducible member, reshape, then reflect open-body SN.
    -- Ascribe the engine's (folded) conclusion, then close into the closing-substitution form so the goal's
    -- `memberCell` / `outputType` reduce to `boolElimCell` / `subst0 motive scrutinee` (match-iota) — the `app`
    -- row's discipline.
    have boolElimMember :
        FundamentalConclusionAtBoundedSucc env bound context
          (boolElimCell motive scrutinee thenBranch elseBranch) (RawTerm.subst0 motive scrutinee) :=
      fundamentalBoolElimAtBoundedSucc env bound context motiveConclusion scrutineeConclusion
        thenBranchConclusion elseBranchConclusion
        (fun substitution envReducible =>
          dependentMotiveUnderBinderStronglyNormalizing env bound context motiveConclusion
            scrutineeConclusion substitution envReducible)
    intro _targetScope substitution envReducible
    exact boolElimMember substitution envReducible

/-- The dependent recursive `gen_natElim` elim FT member: `natElim motive baseBranch stepBranch scrutinee` is a
bound-reducible member of the DEPENDENT result type `subst0 motive scrutinee`, given the four obligation IHs
(scrutinee a `Nat` member; base branch at `subst0 motive natZero`; step branch at the two-binder dependent succ
type `natElimDependentSuccBranchType motive` over `(context.cons Nat).cons motive`; motive a type under `Nat`).
The member witness is the shipped recursive engine bridge `fundamentalNatElimAtBoundedSucc`, fed the four IHs plus
two strong-normalization facts: the succ branch's under-TWO-binders SN — discharged INLINE from the obligation IHs
by `dependentSuccBranchUnderTwoBindersStronglyNormalizing` (concrete-fill + substitution reflection, NO
renaming-stability) — and `succContractumTerminates`, the recursive-eliminator contractum-termination residue.
That residue is NOT discharged here and is NOT dischargeable at the open level: the succ-ι contractum embeds a raw
`natElimCellSpine` whose strong normalization fails for arbitrary open terms (raw `natElim` is not globally SN);
it is threaded as a row premise, to be discharged at the closed-term consistency leg where the spine reduces to a
value (the standing residue the recursive engine has always carried). -/
theorem fundamentalNatElimRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren natElimRule.argShifts scope}
    {params : RawTermChildren natElimRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ natElimRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier)
    (succContractumTerminates : ∀ {targetScope : Nat}
        (currentMotive : RawTerm (targetScope + 1 + 1)) (currentSucc : RawTerm (targetScope + 1 + 2))
        (predecessor currentZero : RawTerm (targetScope + 1)), IsStronglyNormalizing predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons (natElimCellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc)) :
    FundamentalConclusionAtBoundedSucc env bound context (natElimRule.memberCell scope args)
      (natElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))),
    .childNil =>
    have scrutineeConclusion :
        FundamentalConclusionAtBoundedSucc env bound context scrutinee natTypeCell :=
      premisesFundamental _ (List.Mem.head _)
    have zeroBranchConclusion :
        FundamentalConclusionAtBoundedSucc env bound context baseBranch
          (RawTerm.subst0 motive natZeroCell) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.head _))
    have succBranchConclusion :
        FundamentalConclusionAtBoundedSucc env bound
          ((context.cons natTypeCell).cons motive) stepBranch
          (natElimDependentSuccBranchType motive) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have motiveConclusion :
        FundamentalConclusionAtBoundedSucc env bound (context.cons natTypeCell) motive
          (universeCodeCell level0 flag) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have natElimMember :
        FundamentalConclusionAtBoundedSucc env bound context
          (natElimCell motive baseBranch stepBranch scrutinee) (RawTerm.subst0 motive scrutinee) :=
      fundamentalNatElimAtBoundedSucc env bound context motiveConclusion scrutineeConclusion
        zeroBranchConclusion succBranchConclusion
        (fun substitution envReducible =>
          dependentSuccBranchUnderTwoBindersStronglyNormalizing env bound context motiveConclusion
            scrutineeConclusion succBranchConclusion substitution envReducible)
        succContractumTerminates
    intro _targetScope substitution envReducible
    exact natElimMember substitution envReducible

/-- The dependent recursive `gen_natRec` elim FT member — the `natRec` twin of `fundamentalNatElimRowAtBoundedSucc`.
Identical four-obligation wiring and inline succ-branch SN discharge; the recursive engine bridge
`fundamentalNatRecAtBoundedSucc` and the `natRecCellSpine` contractum residue are the only differences (the branch
TYPES, the two-binder succ obligation, and the dependent output are shared with `natElim`). -/
theorem fundamentalNatRecRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren natRecElimRule.argShifts scope}
    {params : RawTermChildren natRecElimRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ natRecElimRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier)
    (succContractumTerminates : ∀ {targetScope : Nat}
        (currentMotive : RawTerm (targetScope + 1 + 1)) (currentSucc : RawTerm (targetScope + 1 + 2))
        (predecessor currentZero : RawTerm (targetScope + 1)), IsStronglyNormalizing predecessor →
        IsStronglyNormalizing
          (RawTerm.subst
            (RawTermSubst.cons (natRecCellSpine currentMotive predecessor currentZero currentSucc)
              (RawTermSubst.singleton predecessor))
            currentSucc)) :
    FundamentalConclusionAtBoundedSucc env bound context (natRecElimRule.memberCell scope args)
      (natRecElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))),
    .childNil =>
    have scrutineeConclusion :
        FundamentalConclusionAtBoundedSucc env bound context scrutinee natTypeCell :=
      premisesFundamental _ (List.Mem.head _)
    have zeroBranchConclusion :
        FundamentalConclusionAtBoundedSucc env bound context baseBranch
          (RawTerm.subst0 motive natZeroCell) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.head _))
    have succBranchConclusion :
        FundamentalConclusionAtBoundedSucc env bound
          ((context.cons natTypeCell).cons motive) stepBranch
          (natElimDependentSuccBranchType motive) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have motiveConclusion :
        FundamentalConclusionAtBoundedSucc env bound (context.cons natTypeCell) motive
          (universeCodeCell level0 flag) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have natRecMember :
        FundamentalConclusionAtBoundedSucc env bound context
          (natRecCell motive baseBranch stepBranch scrutinee) (RawTerm.subst0 motive scrutinee) :=
      fundamentalNatRecAtBoundedSucc env bound context motiveConclusion scrutineeConclusion
        zeroBranchConclusion succBranchConclusion
        (fun substitution envReducible =>
          dependentSuccBranchUnderTwoBindersStronglyNormalizing env bound context motiveConclusion
            scrutineeConclusion succBranchConclusion substitution envReducible)
        succContractumTerminates
    intro _targetScope substitution envReducible
    exact natRecMember substitution envReducible

/-- The dependent non-recursive `gen_eitherMatch` elim FT member: `eitherMatch motive leftBranch rightBranch
scrutinee` is a bound-reducible member of the DEPENDENT result type `subst0 motive scrutinee`, given the four
obligation IHs (scrutinee an `eitherTypeCell A B` member; leftBranch at the one-binder dependent inl branch type
`eitherMatchDependentInlBranchType motive A`; rightBranch at the inr branch type; motive a type under
`eitherTypeCell A B`).  The member witness is the shipped engine bridge `fundamentalEitherMatchAtBoundedSucc`, fed
the four IHs plus the under-binder motive SN — discharged INLINE by `dependentMotiveUnderBinderStronglyNormalizing`
(generic over the scrutinee's type cell, here `eitherTypeCell A B`), exactly as in the `boolElim` row.

Unlike `boolElim` (whose branches land DIRECTLY in the result candidate), `eitherMatch`'s branches are Π over the
carrier and the ι APPLIES them to the injected payload, so — like the recursive `natElim` row — this row THREADS
the bridge's standing residues as row premises: the branch-application strong normalization
(`branchApplicationStronglyNormalizing`, ONE generic premise instantiated at both branches) and the two
reach-conditioned branch-application member residues (`leftBranchMemberIfReachesInl` / `…Inr`).  Those residues are
NOT dischargeable at the open level (extracting `payload ∈ ⟦A⟧` for a non-normal reachable payload needs the
substitution-SN content the fundamental theorem itself supplies); they are threaded to the closed-term consistency
leg where the closed scrutinee reduces to a canonical value.  Each is quantified over the args it references
(branch / motive / scrutinee), since those are matched only inside the body; instantiating at the matched terms
recovers the bridge's specialized residue — the same generalization the `natElim` row uses for its spine residue. -/
theorem fundamentalEitherMatchRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren eitherMatchElimRule.argShifts scope}
    {params : RawTermChildren eitherMatchElimRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ eitherMatchElimRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier)
    (branchApplicationStronglyNormalizing : ∀ (branch : RawTerm scope) {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ value : RawTerm (targetScope + 1), IsStronglyNormalizing value →
          IsStronglyNormalizing (applicationCell (RawTerm.subst substitution branch) value))
    (leftBranchMemberIfReachesInl : ∀ (currentMotive : RawTerm (scope + 1))
        (currentScrutinee currentLeftBranch : RawTerm scope) {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ payload : RawTerm (targetScope + 1),
          StepStar (RawTerm.subst substitution currentScrutinee) (eitherInlCell payload) →
          IsReducibleMemberAtBounded env bound
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) currentMotive)
              (RawTerm.subst substitution currentScrutinee))
            (applicationCell (RawTerm.subst substitution currentLeftBranch) payload))
    (rightBranchMemberIfReachesInr : ∀ (currentMotive : RawTerm (scope + 1))
        (currentScrutinee currentRightBranch : RawTerm scope) {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ payload : RawTerm (targetScope + 1),
          StepStar (RawTerm.subst substitution currentScrutinee) (eitherInrCell payload) →
          IsReducibleMemberAtBounded env bound
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) currentMotive)
              (RawTerm.subst substitution currentScrutinee))
            (applicationCell (RawTerm.subst substitution currentRightBranch) payload)) :
    FundamentalConclusionAtBoundedSucc env bound context (eitherMatchElimRule.memberCell scope args)
      (eitherMatchElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))),
    .childCons typeParamA (.childCons typeParamB .childNil) =>
    have scrutineeConclusion :
        FundamentalConclusionAtBoundedSucc env bound context scrutinee
          (eitherTypeCell typeParamA typeParamB) :=
      premisesFundamental _ (List.Mem.head _)
    have leftBranchConclusion :
        FundamentalConclusionAtBoundedSucc env bound context leftBranch
          (eitherMatchDependentInlBranchType motive typeParamA) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.head _))
    have rightBranchConclusion :
        FundamentalConclusionAtBoundedSucc env bound context rightBranch
          (eitherMatchDependentInrBranchType motive typeParamB) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have motiveConclusion :
        FundamentalConclusionAtBoundedSucc env bound
          (context.cons (eitherTypeCell typeParamA typeParamB)) motive
          (universeCodeCell level0 flag) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have eitherMatchMember :
        FundamentalConclusionAtBoundedSucc env bound context
          (eitherMatchCell motive leftBranch rightBranch scrutinee) (RawTerm.subst0 motive scrutinee) :=
      fundamentalEitherMatchAtBoundedSucc env bound context motiveConclusion scrutineeConclusion
        leftBranchConclusion rightBranchConclusion
        (fun substitution envReducible =>
          dependentMotiveUnderBinderStronglyNormalizing env bound context motiveConclusion
            scrutineeConclusion substitution envReducible)
        (branchApplicationStronglyNormalizing leftBranch)
        (branchApplicationStronglyNormalizing rightBranch)
        (leftBranchMemberIfReachesInl motive scrutinee leftBranch)
        (rightBranchMemberIfReachesInr motive scrutinee rightBranch)
    intro _targetScope substitution envReducible
    exact eitherMatchMember substitution envReducible

/-- The dependent non-recursive `gen_optionMatch` elim FT member: `optionMatch motive noneBranch someBranch
scrutinee` is a bound-reducible member of the DEPENDENT result type `subst0 motive scrutinee`, given the four
obligation IHs (scrutinee an `optionTypeCell A` member; noneBranch at the nullary dependent classifier
`subst0 motive optionNoneCell`; someBranch at the one-binder dependent some branch type
`optionMatchDependentSomeBranchType motive A`; motive a type under `optionTypeCell A`).  The member witness is the
shipped engine bridge `fundamentalOptionMatchAtBoundedSucc`, fed the four IHs plus the under-binder motive SN —
discharged INLINE by `dependentMotiveUnderBinderStronglyNormalizing` — exactly as in the `boolElim` / `eitherMatch`
rows.

Option is the `bool` / `either` HYBRID: the `none` branch lands DIRECTLY in the result candidate (its
reach-conditioned member is discharged INSIDE the bridge by `branchMemberTransferAlongScrutineeReduction`, carrying
NO residue, the `boolElim`-style direct branch), and only the `some` branch is Π over the carrier with the ι
APPLYING it to the injected payload — so this row THREADS only the `some`-side standing residues (the
`eitherMatch`-style applied branch): the branch-application strong normalization
(`someBranchApplicationStronglyNormalizing`) and the reach-conditioned branch-application member residue
(`someBranchMemberIfReachesSome`).  Those residues are NOT dischargeable at the open level; they are threaded to
the closed-term consistency leg where the closed scrutinee reduces to a canonical value.  Each is quantified over
the args it references (branch / motive / scrutinee), since those are matched only inside the body; instantiating
at the matched terms recovers the bridge's specialized residue — the same generalization the `eitherMatch` row
uses for its applied-branch residues. -/
theorem fundamentalOptionMatchRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren optionMatchElimRule.argShifts scope}
    {params : RawTermChildren optionMatchElimRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ optionMatchElimRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier)
    (someBranchApplicationStronglyNormalizing : ∀ (branch : RawTerm scope) {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ value : RawTerm (targetScope + 1), IsStronglyNormalizing value →
          IsStronglyNormalizing (applicationCell (RawTerm.subst substitution branch) value))
    (someBranchMemberIfReachesSome : ∀ (currentMotive : RawTerm (scope + 1))
        (currentScrutinee currentSomeBranch : RawTerm scope) {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ payload : RawTerm (targetScope + 1),
          StepStar (RawTerm.subst substitution currentScrutinee) (optionSomeCell payload) →
          IsReducibleMemberAtBounded env bound
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) currentMotive)
              (RawTerm.subst substitution currentScrutinee))
            (applicationCell (RawTerm.subst substitution currentSomeBranch) payload)) :
    FundamentalConclusionAtBoundedSucc env bound context (optionMatchElimRule.memberCell scope args)
      (optionMatchElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))),
    .childCons typeParamA (.childCons typeParamB .childNil) =>
    have scrutineeConclusion :
        FundamentalConclusionAtBoundedSucc env bound context scrutinee (optionTypeCell typeParamA) :=
      premisesFundamental _ (List.Mem.head _)
    have noneBranchConclusion :
        FundamentalConclusionAtBoundedSucc env bound context noneBranch
          (RawTerm.subst0 motive optionNoneCell) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.head _))
    have someBranchConclusion :
        FundamentalConclusionAtBoundedSucc env bound context someBranch
          (optionMatchDependentSomeBranchType motive typeParamA) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have motiveConclusion :
        FundamentalConclusionAtBoundedSucc env bound
          (context.cons (optionTypeCell typeParamA)) motive (universeCodeCell level0 flag) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have optionMatchMember :
        FundamentalConclusionAtBoundedSucc env bound context
          (optionMatchCell motive noneBranch someBranch scrutinee) (RawTerm.subst0 motive scrutinee) :=
      fundamentalOptionMatchAtBoundedSucc env bound context motiveConclusion scrutineeConclusion
        noneBranchConclusion someBranchConclusion
        (fun substitution envReducible =>
          dependentMotiveUnderBinderStronglyNormalizing env bound context motiveConclusion
            scrutineeConclusion substitution envReducible)
        (someBranchApplicationStronglyNormalizing someBranch)
        (someBranchMemberIfReachesSome motive scrutinee someBranch)
    intro _targetScope substitution envReducible
    exact optionMatchMember substitution envReducible

/-- The `gen_fst` elim FT member: `fst pairTerm` is a bound-reducible member of the NON-DEPENDENT result type
`firstType` (the first component type), given the two obligation IHs (scrutinee an `productTypeCell firstType
secondType` member; firstType a type at a universe).  The member witness is the shipped engine bridge
`fundamentalFstAtBoundedSucc`, fed the two IHs.  Projection has no motive and no under-binder SN to discharge —
the result type is the component-type obligation directly — so this row only THREADS the one conditioned
component-member residue (`firstMemberIfReachesPair`, open-level-irreducible since the scrutinee arrives as the
weak `dataTaitCandidate isPairValue`; discharged at the closed-term consistency leg).  Quantified over the args it
references (pairTerm / firstType), matched only inside the body. -/
theorem fundamentalFstRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren fstElimRule.argShifts scope}
    {params : RawTermChildren fstElimRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ fstElimRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier)
    (firstMemberIfReachesPair : ∀ (currentPairTerm currentFirstType : RawTerm scope) {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ first second : RawTerm (targetScope + 1),
          StepStar (RawTerm.subst substitution currentPairTerm) (pairCell first second) →
          IsReducibleMemberAtBounded env bound (RawTerm.subst substitution currentFirstType) first) :
    FundamentalConclusionAtBoundedSucc env bound context (fstElimRule.memberCell scope args)
      (fstElimRule.outputType scope args params) := by
  match args, params with
  | .childCons pairTerm .childNil, .childCons firstType (.childCons secondType .childNil) =>
    have pairTermConclusion :
        FundamentalConclusionAtBoundedSucc env bound context pairTerm
          (productTypeCell firstType secondType) :=
      premisesFundamental _ (List.Mem.head _)
    have firstTypeConclusion :
        FundamentalConclusionAtBoundedSucc env bound context firstType (universeCodeCell level0 flag) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.head _))
    have fstMember :
        FundamentalConclusionAtBoundedSucc env bound context (fstCell pairTerm) firstType :=
      fundamentalFstAtBoundedSucc env bound context pairTermConclusion firstTypeConclusion
        (firstMemberIfReachesPair pairTerm firstType)
    intro _targetScope substitution envReducible
    exact fstMember substitution envReducible

/-- The `gen_snd` elim FT member — the second-projection twin of `fundamentalFstRowAtBoundedSucc`, at the
NON-DEPENDENT result type `secondType`, threading the one conditioned second-component-member residue. -/
theorem fundamentalSndRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren sndElimRule.argShifts scope}
    {params : RawTermChildren sndElimRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ sndElimRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier)
    (secondMemberIfReachesPair : ∀ (currentPairTerm currentSecondType : RawTerm scope) {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ first second : RawTerm (targetScope + 1),
          StepStar (RawTerm.subst substitution currentPairTerm) (pairCell first second) →
          IsReducibleMemberAtBounded env bound (RawTerm.subst substitution currentSecondType) second) :
    FundamentalConclusionAtBoundedSucc env bound context (sndElimRule.memberCell scope args)
      (sndElimRule.outputType scope args params) := by
  match args, params with
  | .childCons pairTerm .childNil, .childCons firstType (.childCons secondType .childNil) =>
    have pairTermConclusion :
        FundamentalConclusionAtBoundedSucc env bound context pairTerm
          (productTypeCell firstType secondType) :=
      premisesFundamental _ (List.Mem.head _)
    have secondTypeConclusion :
        FundamentalConclusionAtBoundedSucc env bound context secondType (universeCodeCell level0 flag) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.head _))
    have sndMember :
        FundamentalConclusionAtBoundedSucc env bound context (sndCell pairTerm) secondType :=
      fundamentalSndAtBoundedSucc env bound context pairTermConclusion secondTypeConclusion
        (secondMemberIfReachesPair pairTerm secondType)
    intro _targetScope substitution envReducible
    exact sndMember substitution envReducible

/-- The dependent recursive `gen_listElim` elim FT member — the `nat` × `either` HYBRID: `listElim` recurses at the
TAIL (`nat`-style, value-indexed result candidate; the row threads `consContractumTerminates` straight through to
the engine, exactly as the `natElim` / `natRec` rows thread their spine residue) AND its cons-ι APPLIES the branch
to the injected head/tail/recursive-call (`either`-style applied branch; the row threads the reach-conditioned
recursive branch-application member `consBranchApplicationClosed`, the recursive generalization of `eitherMatch`'s
`leftBranchMemberIfReachesInl`).  The nil branch lands DIRECTLY in the result candidate (`bool` / `nat`-zero style)
so it carries NO residue — its member is read off the obligation IH and reshaped inside the bridge.

Wiring is uniform with the other dependent recursive rows: the four obligation IHs come out of `premisesFundamental`
in `listElimRule.obligations` order (scrutinee `.head`; nilBranch `.tail.head`; consBranch `.tail.tail.head`; motive
`.tail.tail.tail.head`), then the engine bridge `fundamentalListElimAtBoundedSucc` assembles the member at the
dependent output `subst0 motive scrutinee`.  The `consBranchApplicationClosed` residue is quantified over the args
it references (the motive + the two branches), since they are matched only inside the body; instantiating at the
matched terms recovers the bridge's specialized residue — the `eitherMatch` / `natElim` generalization pattern. -/
theorem fundamentalListElimRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren listElimRule.argShifts scope}
    {params : RawTermChildren listElimRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ listElimRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier)
    (consContractumTerminates : ∀ {targetScope : Nat}
        (currentMotive : RawTerm (targetScope + 1 + 1)) (currentCons currentNil : RawTerm (targetScope + 1))
        (head tail : RawTerm (targetScope + 1)), IsStronglyNormalizing head → IsStronglyNormalizing tail →
        IsStronglyNormalizing (listElimConsContractum currentMotive currentCons head tail currentNil))
    (consBranchApplicationClosed : ∀ (currentMotive : RawTerm (scope + 1)) (currentNil currentCons : RawTerm scope)
        {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        ∀ {head tail : RawTerm (targetScope + 1)},
          IsStronglyNormalizing head →
          dataTaitCandidate IsListStructured tail →
          IsReducibleMemberAtBounded env bound
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) currentMotive) tail)
            (listElimCellSpine (RawTerm.subst (RawTermSubst.lift substitution) currentMotive) tail
              (RawTerm.subst substitution currentNil) (RawTerm.subst substitution currentCons)) →
          IsReducibleMemberAtBounded env bound
            (RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift substitution) currentMotive)
              (listConsCell head tail))
            (listElimConsContractum (RawTerm.subst (RawTermSubst.lift substitution) currentMotive)
              (RawTerm.subst substitution currentCons) head tail (RawTerm.subst substitution currentNil))) :
    FundamentalConclusionAtBoundedSucc env bound context (listElimRule.memberCell scope args)
      (listElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))),
    .childCons elementType (.childCons _resultType .childNil) =>
    have scrutineeConclusion :
        FundamentalConclusionAtBoundedSucc env bound context scrutinee (listTypeCell elementType) :=
      premisesFundamental _ (List.Mem.head _)
    have nilBranchConclusion :
        FundamentalConclusionAtBoundedSucc env bound context nilBranch
          (RawTerm.subst0 motive listNilCell) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.head _))
    have consBranchConclusion :
        FundamentalConclusionAtBoundedSucc env bound context consBranch
          (listElimDependentConsBranchType motive elementType) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have motiveConclusion :
        FundamentalConclusionAtBoundedSucc env bound (context.cons (listTypeCell elementType)) motive
          (universeCodeCell level0 flag) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have listElimMember :
        FundamentalConclusionAtBoundedSucc env bound context
          (listElimCell motive scrutinee nilBranch consBranch) (RawTerm.subst0 motive scrutinee) :=
      fundamentalListElimAtBoundedSucc env bound context motiveConclusion scrutineeConclusion
        nilBranchConclusion consBranchConclusion consContractumTerminates
        (consBranchApplicationClosed motive nilBranch consBranch)
    intro _targetScope substitution envReducible
    exact listElimMember substitution envReducible

/-- The dependent `gen_idJ` elim FT member (DEP-ID row, GENUINE Paulin-Mohring): `idJ motive baseCase witness` is
a bound-reducible member of the DEPENDENT output `idJMotiveAt motive right witness = C[b := right, p := witness]`,
given the four obligation IHs (witness a GENERAL `idTypeCell typeCode left right` member; right endpoint an `A`
member; base case a `C[left, refl left]` member; motive a type at a universe in the 2-extended context).  The
member witness is the genuine engine bridge `fundamentalIdJGenuineAtBoundedSucc`, fed the four IHs (in the rule's
obligation order: witness, right, base, motive).  Path induction contracts to the base case on `refl`, and the
based scrutinee `dataTaitCandidate (isReflValueBetween left right)` (DEP-ID model flip) supplies the endpoint
conversions the genuine motive-reclassification consumes (`isReflValueBetween_endpointConvOfReaches`, JMAX-3) so
the base case transfers to the output along `convSubstPairArgs` (JMAX-2).  The one vestigial-motive SN residue (the
motive carries NO obligation as a SUB-conclusion — it is the arity-3 cell's binderShift-2 child) threads to the
closed-term consistency leg. -/
theorem fundamentalIdJRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {args : RawTermChildren idJElimRule.argShifts scope}
    {params : RawTermChildren idJElimRule.paramShifts scope}
    {level0 level1 : LevelExpr} {flag : UniverseFlag}
    (premisesFundamental : ∀ obligation,
        obligation ∈ idJElimRule.obligations scope context args params level0 level1 flag →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier)
    (motiveStronglyNormalizing : ∀ (currentMotive : RawTerm (scope + 2)) {targetScope : Nat}
        (substitution : RawTermSubst scope (targetScope + 1)),
        ReducibleEnvAtBounded env bound context substitution →
        IsStronglyNormalizing (RawTerm.subst (iterateLiftRaw substitution 2) currentMotive)) :
    FundamentalConclusionAtBoundedSucc env bound context (idJElimRule.memberCell scope args)
      (idJElimRule.outputType scope args params) := by
  match args, params with
  | .childCons motive (.childCons baseCase (.childCons witness .childNil)),
    .childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
    have witnessConclusion :
        FundamentalConclusionAtBoundedSucc env bound context witness
          (idTypeCell typeCode leftEndpoint rightEndpoint) :=
      premisesFundamental _ (List.Mem.head _)
    have rightEndpointConclusion :
        FundamentalConclusionAtBoundedSucc env bound context rightEndpoint typeCode :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.head _))
    have baseCaseConclusion :
        FundamentalConclusionAtBoundedSucc env bound context baseCase
          (idJMotiveAt motive leftEndpoint (reflCell leftEndpoint)) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have motiveConclusion :
        FundamentalConclusionAtBoundedSucc env bound
          ((context.cons typeCode).cons (idJMotiveSecondBinderType typeCode leftEndpoint)) motive
          (universeCodeCell level0 flag) :=
      premisesFundamental _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have idJMember :
        FundamentalConclusionAtBoundedSucc env bound context (idJCell motive baseCase witness)
          (idJMotiveAt motive rightEndpoint witness) :=
      fundamentalIdJGenuineAtBoundedSucc env bound context witnessConclusion rightEndpointConclusion
        baseCaseConclusion motiveConclusion (motiveStronglyNormalizing motive)
    intro _targetScope substitution envReducible
    exact idJMember substitution envReducible

end FX1Poly.Typed

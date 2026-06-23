import FX1Poly.Typed.Engine.RuleTables.ElimRuleTable
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.GenericDependentDataElimBridge
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedBoolElimFundamental
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedCodomainOpenSN
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.BoundedNatElimFundamentalBridge

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

end FX1Poly.Typed

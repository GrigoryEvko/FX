import LeanFX.Syntax.Strengthen
import LeanFX.Syntax.Subst

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## Optional renaming across substitution.

These lemmas state that substitution and optional renaming commute when
their variable-level data form a pointwise square.  They are the
syntax-level prerequisite for typed term strengthening under dependent
constructors, where `subst0` appears in result types. -/

/-- A raw substitution square for optional renaming.

Substituting a source variable and then optional-renaming in the middle
scope agrees with optional-renaming the variable position first and then
substituting in the final scope. -/
def RawTermSubst.OptionalRenamingSquare {source middle target final : Nat}
    (sourceSubstitution : RawTermSubst source middle)
    (optionalSourceRenaming : OptionalRenaming source target)
    (optionalTargetRenaming : OptionalRenaming middle final)
    (targetSubstitution : RawTermSubst target final) : Prop :=
  ∀ sourcePosition,
    (sourceSubstitution sourcePosition).optRename optionalTargetRenaming =
      Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
        (Option.map RawTerm.var (optionalSourceRenaming sourcePosition))

/-- Raw optional-renaming substitution squares are stable under binders. -/
theorem RawTermSubst.lift_optionalRenamingSquare {source middle target final : Nat}
    {sourceSubstitution : RawTermSubst source middle}
    {optionalSourceRenaming : OptionalRenaming source target}
    {optionalTargetRenaming : OptionalRenaming middle final}
    {targetSubstitution : RawTermSubst target final}
    (isOptionalRenamingSquare : RawTermSubst.OptionalRenamingSquare
      sourceSubstitution optionalSourceRenaming optionalTargetRenaming targetSubstitution) :
    RawTermSubst.OptionalRenamingSquare sourceSubstitution.lift
      optionalSourceRenaming.lift optionalTargetRenaming.lift targetSubstitution.lift
  | ⟨0, _⟩ => rfl
  | ⟨sourcePosition + 1, isWithinSource⟩ => by
      let sourcePredecessor : Fin source :=
        ⟨sourcePosition, Nat.lt_of_succ_lt_succ isWithinSource⟩
      change (sourceSubstitution sourcePredecessor).weaken.optRename
          optionalTargetRenaming.lift =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution.lift)
          (Option.map RawTerm.var
            (Option.map Fin.succ (optionalSourceRenaming sourcePredecessor)))
      rw [RawTerm.weaken_optRename_lift optionalTargetRenaming
        (sourceSubstitution sourcePredecessor)]
      rw [isOptionalRenamingSquare sourcePredecessor]
      cases optionalSourceRenaming sourcePredecessor <;> rfl

/-- The raw component of one-hole substitution forms an optional-renaming
square with lifted optional renaming. -/
theorem RawTermSubst.dropNewest_optionalRenamingSquare {source target : Nat}
    (optionalRenaming : OptionalRenaming source target) :
    RawTermSubst.OptionalRenamingSquare RawTermSubst.dropNewest
      optionalRenaming.lift optionalRenaming RawTermSubst.dropNewest
  | ⟨0, _⟩ => rfl
  | ⟨sourcePosition + 1, isWithinSource⟩ => by
      let sourcePredecessor : Fin source :=
        ⟨sourcePosition, Nat.lt_of_succ_lt_succ isWithinSource⟩
      change Option.map RawTerm.var (optionalRenaming sourcePredecessor) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst RawTermSubst.dropNewest)
          (Option.map RawTerm.var
            (Option.map Fin.succ (optionalRenaming sourcePredecessor)))
      cases optionalRenaming sourcePredecessor <;> rfl

/-- Raw substitution commutes with optional renaming when the variable
mappings form a raw optional-renaming square. -/
theorem RawTerm.subst_optRename_commute {source middle target final : Nat}
    (sourceSubstitution : RawTermSubst source middle)
    (optionalSourceRenaming : OptionalRenaming source target)
    (optionalTargetRenaming : OptionalRenaming middle final)
    (targetSubstitution : RawTermSubst target final)
    (isOptionalRenamingSquare : RawTermSubst.OptionalRenamingSquare
      sourceSubstitution optionalSourceRenaming optionalTargetRenaming targetSubstitution) :
    ∀ rawTerm : RawTerm source,
      (rawTerm.subst sourceSubstitution).optRename optionalTargetRenaming =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (rawTerm.optRename optionalSourceRenaming)
  | .var position => isOptionalRenamingSquare position
  | .unit => rfl
  | .boolTrue => rfl
  | .boolFalse => rfl
  | .natZero => rfl
  | .natSucc predecessor => by
      have predecessorEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare predecessor
      change Option.map RawTerm.natSucc
          ((predecessor.subst sourceSubstitution).optRename optionalTargetRenaming) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.map RawTerm.natSucc
            (predecessor.optRename optionalSourceRenaming))
      rw [predecessorEquality]
      cases predecessor.optRename optionalSourceRenaming <;> rfl
  | .lam body => by
      have bodyEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution.lift
          optionalSourceRenaming.lift optionalTargetRenaming.lift
          targetSubstitution.lift
          (RawTermSubst.lift_optionalRenamingSquare isOptionalRenamingSquare) body
      change Option.map RawTerm.lam
          ((body.subst sourceSubstitution.lift).optRename optionalTargetRenaming.lift) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.map RawTerm.lam (body.optRename optionalSourceRenaming.lift))
      rw [bodyEquality]
      cases body.optRename optionalSourceRenaming.lift <;> rfl
  | .app function argument => by
      have functionEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare function
      have argumentEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare argument
      change Option.bind
          ((function.subst sourceSubstitution).optRename optionalTargetRenaming)
          (fun renamedFunction =>
            Option.bind
              ((argument.subst sourceSubstitution).optRename optionalTargetRenaming)
              (fun renamedArgument =>
                some (RawTerm.app renamedFunction renamedArgument))) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.bind (function.optRename optionalSourceRenaming)
            (fun renamedFunction =>
              Option.bind (argument.optRename optionalSourceRenaming)
                (fun renamedArgument =>
                  some (RawTerm.app renamedFunction renamedArgument))))
      rw [functionEquality, argumentEquality]
      cases function.optRename optionalSourceRenaming <;>
        cases argument.optRename optionalSourceRenaming <;> rfl
  | .pair first second => by
      have firstEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare first
      have secondEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare second
      change Option.bind
          ((first.subst sourceSubstitution).optRename optionalTargetRenaming)
          (fun renamedFirst =>
            Option.bind
              ((second.subst sourceSubstitution).optRename optionalTargetRenaming)
              (fun renamedSecond => some (RawTerm.pair renamedFirst renamedSecond))) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.bind (first.optRename optionalSourceRenaming)
            (fun renamedFirst =>
              Option.bind (second.optRename optionalSourceRenaming)
                (fun renamedSecond => some (RawTerm.pair renamedFirst renamedSecond))))
      rw [firstEquality, secondEquality]
      cases first.optRename optionalSourceRenaming <;>
        cases second.optRename optionalSourceRenaming <;> rfl
  | .fst pairTerm => by
      have pairEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare pairTerm
      change Option.map RawTerm.fst
          ((pairTerm.subst sourceSubstitution).optRename optionalTargetRenaming) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.map RawTerm.fst (pairTerm.optRename optionalSourceRenaming))
      rw [pairEquality]
      cases pairTerm.optRename optionalSourceRenaming <;> rfl
  | .snd pairTerm => by
      have pairEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare pairTerm
      change Option.map RawTerm.snd
          ((pairTerm.subst sourceSubstitution).optRename optionalTargetRenaming) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.map RawTerm.snd (pairTerm.optRename optionalSourceRenaming))
      rw [pairEquality]
      cases pairTerm.optRename optionalSourceRenaming <;> rfl
  | .boolElim scrutinee thenBranch elseBranch => by
      have scrutineeEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare scrutinee
      have thenEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare thenBranch
      have elseEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare elseBranch
      change Option.bind
          ((scrutinee.subst sourceSubstitution).optRename optionalTargetRenaming)
          (fun renamedScrutinee =>
            Option.bind
              ((thenBranch.subst sourceSubstitution).optRename optionalTargetRenaming)
              (fun renamedThen =>
                Option.bind
                  ((elseBranch.subst sourceSubstitution).optRename
                    optionalTargetRenaming)
                  (fun renamedElse =>
                    some (RawTerm.boolElim renamedScrutinee renamedThen renamedElse)))) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.bind (scrutinee.optRename optionalSourceRenaming)
            (fun renamedScrutinee =>
              Option.bind (thenBranch.optRename optionalSourceRenaming)
                (fun renamedThen =>
                  Option.bind (elseBranch.optRename optionalSourceRenaming)
                    (fun renamedElse =>
                      some (RawTerm.boolElim renamedScrutinee
                        renamedThen renamedElse)))))
      rw [scrutineeEquality, thenEquality, elseEquality]
      cases scrutinee.optRename optionalSourceRenaming <;>
        cases thenBranch.optRename optionalSourceRenaming <;>
        cases elseBranch.optRename optionalSourceRenaming <;> rfl
  | .natElim scrutinee zeroBranch succBranch => by
      have scrutineeEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare scrutinee
      have zeroEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare zeroBranch
      have succEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare succBranch
      change Option.bind
          ((scrutinee.subst sourceSubstitution).optRename optionalTargetRenaming)
          (fun renamedScrutinee =>
            Option.bind
              ((zeroBranch.subst sourceSubstitution).optRename optionalTargetRenaming)
              (fun renamedZero =>
                Option.bind
                  ((succBranch.subst sourceSubstitution).optRename
                    optionalTargetRenaming)
                  (fun renamedSucc =>
                    some (RawTerm.natElim renamedScrutinee renamedZero renamedSucc)))) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.bind (scrutinee.optRename optionalSourceRenaming)
            (fun renamedScrutinee =>
              Option.bind (zeroBranch.optRename optionalSourceRenaming)
                (fun renamedZero =>
                  Option.bind (succBranch.optRename optionalSourceRenaming)
                    (fun renamedSucc =>
                      some (RawTerm.natElim renamedScrutinee
                        renamedZero renamedSucc)))))
      rw [scrutineeEquality, zeroEquality, succEquality]
      cases scrutinee.optRename optionalSourceRenaming <;>
        cases zeroBranch.optRename optionalSourceRenaming <;>
        cases succBranch.optRename optionalSourceRenaming <;> rfl
  | .natRec scrutinee zeroBranch succBranch => by
      have scrutineeEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare scrutinee
      have zeroEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare zeroBranch
      have succEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare succBranch
      change Option.bind
          ((scrutinee.subst sourceSubstitution).optRename optionalTargetRenaming)
          (fun renamedScrutinee =>
            Option.bind
              ((zeroBranch.subst sourceSubstitution).optRename optionalTargetRenaming)
              (fun renamedZero =>
                Option.bind
                  ((succBranch.subst sourceSubstitution).optRename
                    optionalTargetRenaming)
                  (fun renamedSucc =>
                    some (RawTerm.natRec renamedScrutinee renamedZero renamedSucc)))) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.bind (scrutinee.optRename optionalSourceRenaming)
            (fun renamedScrutinee =>
              Option.bind (zeroBranch.optRename optionalSourceRenaming)
                (fun renamedZero =>
                  Option.bind (succBranch.optRename optionalSourceRenaming)
                    (fun renamedSucc =>
                      some (RawTerm.natRec renamedScrutinee
                        renamedZero renamedSucc)))))
      rw [scrutineeEquality, zeroEquality, succEquality]
      cases scrutinee.optRename optionalSourceRenaming <;>
        cases zeroBranch.optRename optionalSourceRenaming <;>
        cases succBranch.optRename optionalSourceRenaming <;> rfl
  | .listNil => rfl
  | .listCons head tail => by
      have headEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare head
      have tailEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare tail
      change Option.bind
          ((head.subst sourceSubstitution).optRename optionalTargetRenaming)
          (fun renamedHead =>
            Option.bind ((tail.subst sourceSubstitution).optRename optionalTargetRenaming)
              (fun renamedTail => some (RawTerm.listCons renamedHead renamedTail))) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.bind (head.optRename optionalSourceRenaming)
            (fun renamedHead =>
              Option.bind (tail.optRename optionalSourceRenaming)
                (fun renamedTail => some (RawTerm.listCons renamedHead renamedTail))))
      rw [headEquality, tailEquality]
      cases head.optRename optionalSourceRenaming <;>
        cases tail.optRename optionalSourceRenaming <;> rfl
  | .listElim scrutinee nilBranch consBranch => by
      have scrutineeEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare scrutinee
      have nilEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare nilBranch
      have consEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare consBranch
      change Option.bind
          ((scrutinee.subst sourceSubstitution).optRename optionalTargetRenaming)
          (fun renamedScrutinee =>
            Option.bind
              ((nilBranch.subst sourceSubstitution).optRename optionalTargetRenaming)
              (fun renamedNil =>
                Option.bind
                  ((consBranch.subst sourceSubstitution).optRename
                    optionalTargetRenaming)
                  (fun renamedCons =>
                    some (RawTerm.listElim renamedScrutinee renamedNil renamedCons)))) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.bind (scrutinee.optRename optionalSourceRenaming)
            (fun renamedScrutinee =>
              Option.bind (nilBranch.optRename optionalSourceRenaming)
                (fun renamedNil =>
                  Option.bind (consBranch.optRename optionalSourceRenaming)
                    (fun renamedCons =>
                      some (RawTerm.listElim renamedScrutinee
                        renamedNil renamedCons)))))
      rw [scrutineeEquality, nilEquality, consEquality]
      cases scrutinee.optRename optionalSourceRenaming <;>
        cases nilBranch.optRename optionalSourceRenaming <;>
        cases consBranch.optRename optionalSourceRenaming <;> rfl
  | .optionNone => rfl
  | .optionSome value => by
      have valueEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare value
      change Option.map RawTerm.optionSome
          ((value.subst sourceSubstitution).optRename optionalTargetRenaming) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.map RawTerm.optionSome (value.optRename optionalSourceRenaming))
      rw [valueEquality]
      cases value.optRename optionalSourceRenaming <;> rfl
  | .optionMatch scrutinee noneBranch someBranch => by
      have scrutineeEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare scrutinee
      have noneEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare noneBranch
      have someEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare someBranch
      change Option.bind
          ((scrutinee.subst sourceSubstitution).optRename optionalTargetRenaming)
          (fun renamedScrutinee =>
            Option.bind
              ((noneBranch.subst sourceSubstitution).optRename optionalTargetRenaming)
              (fun renamedNone =>
                Option.bind
                  ((someBranch.subst sourceSubstitution).optRename
                    optionalTargetRenaming)
                  (fun renamedSome =>
                    some (RawTerm.optionMatch renamedScrutinee renamedNone renamedSome)))) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.bind (scrutinee.optRename optionalSourceRenaming)
            (fun renamedScrutinee =>
              Option.bind (noneBranch.optRename optionalSourceRenaming)
                (fun renamedNone =>
                  Option.bind (someBranch.optRename optionalSourceRenaming)
                    (fun renamedSome =>
                      some (RawTerm.optionMatch renamedScrutinee
                        renamedNone renamedSome)))))
      rw [scrutineeEquality, noneEquality, someEquality]
      cases scrutinee.optRename optionalSourceRenaming <;>
        cases noneBranch.optRename optionalSourceRenaming <;>
        cases someBranch.optRename optionalSourceRenaming <;> rfl
  | .eitherInl value => by
      have valueEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare value
      change Option.map RawTerm.eitherInl
          ((value.subst sourceSubstitution).optRename optionalTargetRenaming) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.map RawTerm.eitherInl (value.optRename optionalSourceRenaming))
      rw [valueEquality]
      cases value.optRename optionalSourceRenaming <;> rfl
  | .eitherInr value => by
      have valueEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare value
      change Option.map RawTerm.eitherInr
          ((value.subst sourceSubstitution).optRename optionalTargetRenaming) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.map RawTerm.eitherInr (value.optRename optionalSourceRenaming))
      rw [valueEquality]
      cases value.optRename optionalSourceRenaming <;> rfl
  | .eitherMatch scrutinee leftBranch rightBranch => by
      have scrutineeEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare scrutinee
      have leftEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare leftBranch
      have rightEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare rightBranch
      change Option.bind
          ((scrutinee.subst sourceSubstitution).optRename optionalTargetRenaming)
          (fun renamedScrutinee =>
            Option.bind
              ((leftBranch.subst sourceSubstitution).optRename optionalTargetRenaming)
              (fun renamedLeft =>
                Option.bind
                  ((rightBranch.subst sourceSubstitution).optRename
                    optionalTargetRenaming)
                  (fun renamedRight =>
                    some (RawTerm.eitherMatch renamedScrutinee
                      renamedLeft renamedRight)))) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.bind (scrutinee.optRename optionalSourceRenaming)
            (fun renamedScrutinee =>
              Option.bind (leftBranch.optRename optionalSourceRenaming)
                (fun renamedLeft =>
                  Option.bind (rightBranch.optRename optionalSourceRenaming)
                    (fun renamedRight =>
                      some (RawTerm.eitherMatch renamedScrutinee
                        renamedLeft renamedRight)))))
      rw [scrutineeEquality, leftEquality, rightEquality]
      cases scrutinee.optRename optionalSourceRenaming <;>
        cases leftBranch.optRename optionalSourceRenaming <;>
        cases rightBranch.optRename optionalSourceRenaming <;> rfl
  | .refl term => by
      have termEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare term
      change Option.map RawTerm.refl
          ((term.subst sourceSubstitution).optRename optionalTargetRenaming) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.map RawTerm.refl (term.optRename optionalSourceRenaming))
      rw [termEquality]
      cases term.optRename optionalSourceRenaming <;> rfl
  | .idJ baseCase witness => by
      have baseEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare baseCase
      have witnessEquality :=
        RawTerm.subst_optRename_commute sourceSubstitution optionalSourceRenaming
          optionalTargetRenaming targetSubstitution isOptionalRenamingSquare witness
      change Option.bind
          ((baseCase.subst sourceSubstitution).optRename optionalTargetRenaming)
          (fun renamedBase =>
            Option.bind
              ((witness.subst sourceSubstitution).optRename optionalTargetRenaming)
              (fun renamedWitness => some (RawTerm.idJ renamedBase renamedWitness))) =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst targetSubstitution)
          (Option.bind (baseCase.optRename optionalSourceRenaming)
            (fun renamedBase =>
              Option.bind (witness.optRename optionalSourceRenaming)
                (fun renamedWitness => some (RawTerm.idJ renamedBase renamedWitness))))
      rw [baseEquality, witnessEquality]
      cases baseCase.optRename optionalSourceRenaming <;>
        cases witness.optRename optionalSourceRenaming <;> rfl

/-- Dropping the newest raw binder commutes with optional renaming under
lifted optional renaming. -/
theorem RawTerm.dropNewest_optRename_commute {source target : Nat}
    (optionalRenaming : OptionalRenaming source target) :
    ∀ rawTerm : RawTerm (source + 1),
      (rawTerm.subst RawTermSubst.dropNewest).optRename optionalRenaming =
        Option.map (fun renamedRawTerm => renamedRawTerm.subst RawTermSubst.dropNewest)
          (rawTerm.optRename optionalRenaming.lift) :=
  RawTerm.subst_optRename_commute RawTermSubst.dropNewest optionalRenaming.lift
    optionalRenaming RawTermSubst.dropNewest
    (RawTermSubst.dropNewest_optionalRenamingSquare optionalRenaming)

end LeanFX.Syntax

import LeanFX2.Reducibility.FundamentalWrappers

/-! # LeanFX2.Reducibility.FundamentalEliminators.IotaEliminators

Fundamental-theorem cases for ι-redex eliminators on closed
inductives: `boolElim` at `Ty.bool`, `natElim` / `natRec` at
`Ty.nat`, `optionMatch` at `Ty.optionType`, `eitherMatch` at
`Ty.eitherType`, `listElim` at `Ty.listType`.  Includes the
SN-output endpoint aliases and the `Term.X_isStronglyNormalizing`
direct SN endpoints.

## Root status

Layer 3 metatheory leaf.  Second slice of `FundamentalEliminators`. -/

namespace LeanFX2


/-! ## K12.22 fundamental ι-eliminator cases -/

/-- Fundamental case: `Term.boolElim` at `Ty.bool` (K12.22.A,
SN-output).

The current bool arm is an SN-direct closed-type clause.  Since the motive
type is arbitrary rather than a structural sub-type of `Ty.bool`, this case
returns SN of the eliminator result.
-/
theorem Reducible.fundamental_boolElim_at_bool_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (scrutineeIH :
      Reducible ((Ty.bool : Ty level scope).subst sigma)
        (Term.subst termSubst scrutinee))
    (thenIH :
      Reducible ((motiveType.subst0 Ty.bool RawTerm.boolTrue).subst sigma)
        (Term.subst termSubst thenBranch))
    (elseIH :
      Reducible ((motiveType.subst0 Ty.bool RawTerm.boolFalse).subst sigma)
        (Term.subst termSubst elseBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.boolElim scrutinee thenBranch elseBranch)) :=
  RawTerm.boolElim_isStronglyNormalizing
    (Reducible.isStronglyNormalizing thenIH)
    (Reducible.isStronglyNormalizing elseIH)
    scrutineeIH

/-- Fundamental endpoint: canonical `Term.natElim` at `natZero`
(K12.22.D).

This is the zero ι-case needed by the SN-output Tait endpoint: the
eliminator result is strongly normalizing because it contracts to the
zero branch, while congruent movement under the successor branch is
covered by the branch SN premise.
-/
theorem Reducible.fundamental_natElimZero_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    (zeroIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst zeroBranch))
    (succIH :
      Reducible ((Ty.arrow Ty.nat motiveType).subst sigma)
        (Term.subst termSubst succBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.natElim Term.natZero zeroBranch succBranch)) :=
  Term.natElim_natZero_isStronglyNormalizing
    (Reducible.isStronglyNormalizing zeroIH)
    (Reducible.isStronglyNormalizing succIH)

/-- Fundamental endpoint: canonical `Term.natElim` at `natSucc`
(K12.22.E).

The successor branch is arrow-reducible, so applying it to the
reducible predecessor yields a reducible motive result; CR1 then gives
the SN premise required by the raw successor ι-expansion.
-/
theorem Reducible.fundamental_natElimSucc_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level scope}
    {predecessorRaw zeroRaw succRaw : RawTerm scope}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    (predecessorIH :
      Reducible ((Ty.nat : Ty level scope).subst sigma)
        (Term.subst termSubst predecessor))
    (zeroIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst zeroBranch))
    (succIH :
      Reducible ((Ty.arrow Ty.nat motiveType).subst sigma)
        (Term.subst termSubst succBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.natElim
          (Term.natSucc predecessor) zeroBranch succBranch)) :=
  Term.natElim_natSucc_isStronglyNormalizing
    (Reducible.isStronglyNormalizing predecessorIH)
    (Reducible.isStronglyNormalizing zeroIH)
    (Reducible.isStronglyNormalizing succIH)
    (Reducible.isStronglyNormalizing
      (succIH.2 (Term.subst termSubst predecessor) predecessorIH))

/-- Fundamental case: `Term.natElim` at `Ty.nat`
(SN-output endpoint).

The successor-application SN closure is explicit for the same reason it
is explicit in `RawTerm.natElim_isStronglyNormalizing`: a deep successor
ι step exposes an arbitrary raw predecessor developed from the
scrutinee.  This theorem packages the substitution-facing fundamental
case without claiming full Reducible-at-motive closure. -/
theorem Reducible.fundamental_natElim_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    (scrutineeIH :
      Reducible ((Ty.nat : Ty level scope).subst sigma)
        (Term.subst termSubst scrutinee))
    (zeroIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst zeroBranch))
    (succIH :
      Reducible ((Ty.arrow Ty.nat motiveType).subst sigma)
        (Term.subst termSubst succBranch))
    (succAppIsSN :
      ∀ {predecessorRaw : RawTerm targetScope},
        RawTerm.isStronglyNormalizing predecessorRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app (succRaw.subst sigma.forRaw) predecessorRaw)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.natElim scrutinee zeroBranch succBranch)) :=
  Term.natElim_isStronglyNormalizing
    scrutineeIH
    (Reducible.isStronglyNormalizing zeroIH)
    (Reducible.isStronglyNormalizing succIH)
    succAppIsSN

/-- Fundamental endpoint: canonical `Term.natRec` at `natZero`
(K12.22.F).

This zero ι-case mirrors `fundamental_natElimZero_at_nat`: the
recursor contracts to the zero branch, while successor-branch
congruence is covered by the branch SN premise.
-/
theorem Reducible.fundamental_natRecZero_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (zeroIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst zeroBranch))
    (succIH :
      Reducible ((Ty.arrow Ty.nat
                    (Ty.arrow motiveType motiveType)).subst sigma)
        (Term.subst termSubst succBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.natRec Term.natZero zeroBranch succBranch)) :=
  Term.natRec_natZero_isStronglyNormalizing
    (Reducible.isStronglyNormalizing zeroIH)
    (Reducible.isStronglyNormalizing succIH)

/-- Fundamental endpoint: canonical `Term.natRec` at `natSucc`
(K12.22.G).

The successor branch is arrow-reducible twice: first at the predecessor,
then at the recursive call.  The recursive result remains an explicit
premise because this endpoint is a local ι backward-closure, not the
general nat-recursion fundamental theorem. -/
theorem Reducible.fundamental_natRecSucc_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level scope}
    {predecessorRaw zeroRaw succRaw : RawTerm scope}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (predecessorIH :
      Reducible ((Ty.nat : Ty level scope).subst sigma)
        (Term.subst termSubst predecessor))
    (zeroIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst zeroBranch))
    (succIH :
      Reducible ((Ty.arrow Ty.nat
                    (Ty.arrow motiveType motiveType)).subst sigma)
        (Term.subst termSubst succBranch))
    (recursiveIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst
          (Term.natRec predecessor zeroBranch succBranch))) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.natRec
          (Term.natSucc predecessor) zeroBranch succBranch)) :=
  Term.natRec_natSucc_isStronglyNormalizing
    (Reducible.isStronglyNormalizing predecessorIH)
    (Reducible.isStronglyNormalizing zeroIH)
    (Reducible.isStronglyNormalizing succIH)
    (Reducible.isStronglyNormalizing recursiveIH)
    (Reducible.isStronglyNormalizing
      ((succIH.2 (Term.subst termSubst predecessor) predecessorIH).2
        (Term.subst termSubst
          (Term.natRec predecessor zeroBranch succBranch))
        recursiveIH))

/-- Fundamental case: `Term.natRec` at `Ty.nat`
(SN-output endpoint).

The successor contractum closure is explicit over raw target branches:
the current `Ty.nat` candidate stores only SN, so this theorem does not
derive full recursive Reducible-at-motive normalization by itself. -/
theorem Reducible.fundamental_natRec_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (scrutineeIH :
      Reducible ((Ty.nat : Ty level scope).subst sigma)
        (Term.subst termSubst scrutinee))
    (zeroIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst zeroBranch))
    (succIH :
      Reducible ((Ty.arrow Ty.nat
                    (Ty.arrow motiveType motiveType)).subst sigma)
        (Term.subst termSubst succBranch))
    (contractumIsSN :
      ∀ {predecessorRaw zeroTargetRaw succTargetRaw : RawTerm targetScope},
        RawTerm.isStronglyNormalizing predecessorRaw →
        RawTerm.isStronglyNormalizing zeroTargetRaw →
        RawTerm.isStronglyNormalizing succTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app (RawTerm.app succTargetRaw predecessorRaw)
            (RawTerm.natRec
              predecessorRaw zeroTargetRaw succTargetRaw))) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.natRec scrutinee zeroBranch succBranch)) :=
  Term.natRec_isStronglyNormalizing
    scrutineeIH
    (Reducible.isStronglyNormalizing zeroIH)
    (Reducible.isStronglyNormalizing succIH)
    contractumIsSN

/-- Fundamental case: `Term.optionMatch` at `Ty.optionType` (K12.22.B,
SN-output).

The `Ty.optionType` reducibility arm stores an eliminator closure:
SN of the scrutinee plus SN of the none branch plus SN of each
some-branch application at a reducible element.  The branch-application
premise is supplied by the arrow reducibility of `someBranch`, then
demoted to SN because the current closure returns SN at the arbitrary
motive type.
-/
theorem Reducible.fundamental_optionMatch_at_option_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (scrutineeIH :
      Reducible ((Ty.optionType elementType).subst sigma)
        (Term.subst termSubst scrutinee))
    (noneIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst noneBranch))
    (someIH :
      Reducible ((Ty.arrow elementType motiveType).subst sigma)
        (Term.subst termSubst someBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.optionMatch scrutinee noneBranch someBranch)) :=
  scrutineeIH.2
    (Term.subst termSubst noneBranch)
    (Term.subst termSubst someBranch)
    (Reducible.isStronglyNormalizing noneIH)
    (Reducible.isStronglyNormalizing someIH)
    (fun valueTerm valueIH =>
      Reducible.isStronglyNormalizing (someIH.2 valueTerm valueIH))

/-- Fundamental case: `Term.eitherMatch` at `Ty.eitherType` (K12.22.C,
SN-output).

Same SN-output eliminator pattern as `optionMatch`, with one arrow-typed
branch for each side.  The current candidate can prove SN of the
eliminator result.
-/
theorem Reducible.fundamental_eitherMatch_at_either_sn
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch :
      Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch :
      Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeIH :
      Reducible ((Ty.eitherType leftType rightType).subst sigma)
        (Term.subst termSubst scrutinee))
    (leftIH :
      Reducible ((Ty.arrow leftType motiveType).subst sigma)
        (Term.subst termSubst leftBranch))
    (rightIH :
      Reducible ((Ty.arrow rightType motiveType).subst sigma)
        (Term.subst termSubst rightBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.eitherMatch scrutinee leftBranch rightBranch)) :=
  scrutineeIH.2
    (Term.subst termSubst leftBranch)
    (Term.subst termSubst rightBranch)
    (Reducible.isStronglyNormalizing leftIH)
    (Reducible.isStronglyNormalizing rightIH)
    (fun valueTerm valueIH =>
      Reducible.isStronglyNormalizing (leftIH.2 valueTerm valueIH))
    (fun valueTerm valueIH =>
      Reducible.isStronglyNormalizing (rightIH.2 valueTerm valueIH))

/-! ## K12.22 SN-output endpoint aliases

These aliases drop the historical `_sn` suffix for K12.22 eliminator
fundamentals.  The theorem statements still state the exact SN-output
contract, matching the current Tait endpoint for M04 strong
normalization without claiming full Reducible-at-motive closure. -/

/-- Fundamental case: `Term.boolElim` at `Ty.bool` (SN-output endpoint). -/
theorem Reducible.fundamental_boolElim_at_bool
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (scrutineeIH :
      Reducible ((Ty.bool : Ty level scope).subst sigma)
        (Term.subst termSubst scrutinee))
    (thenIH :
      Reducible ((motiveType.subst0 Ty.bool RawTerm.boolTrue).subst sigma)
        (Term.subst termSubst thenBranch))
    (elseIH :
      Reducible ((motiveType.subst0 Ty.bool RawTerm.boolFalse).subst sigma)
        (Term.subst termSubst elseBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.boolElim scrutinee thenBranch elseBranch)) :=
  Reducible.fundamental_boolElim_at_bool_sn
    scrutineeIH thenIH elseIH

/-- Fundamental case: `Term.optionMatch` at `Ty.optionType`
(SN-output endpoint). -/
theorem Reducible.fundamental_optionMatch_at_optionType
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (scrutineeIH :
      Reducible ((Ty.optionType elementType).subst sigma)
        (Term.subst termSubst scrutinee))
    (noneIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst noneBranch))
    (someIH :
      Reducible ((Ty.arrow elementType motiveType).subst sigma)
        (Term.subst termSubst someBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.optionMatch scrutinee noneBranch someBranch)) :=
  Reducible.fundamental_optionMatch_at_option_sn
    scrutineeIH noneIH someIH

/-- Fundamental case: `Term.eitherMatch` at `Ty.eitherType`
(SN-output endpoint). -/
theorem Reducible.fundamental_eitherMatch_at_eitherType
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch :
      Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch :
      Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeIH :
      Reducible ((Ty.eitherType leftType rightType).subst sigma)
        (Term.subst termSubst scrutinee))
    (leftIH :
      Reducible ((Ty.arrow leftType motiveType).subst sigma)
        (Term.subst termSubst leftBranch))
    (rightIH :
      Reducible ((Ty.arrow rightType motiveType).subst sigma)
        (Term.subst termSubst rightBranch)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.eitherMatch scrutinee leftBranch rightBranch)) :=
  Reducible.fundamental_eitherMatch_at_either_sn
    scrutineeIH leftIH rightIH

/-- Fundamental case: `Term.listElim` at `Ty.listType`
(SN-output endpoint).

The current list candidate intentionally asks for the cons-branch
application SN closure at every reducible head and strongly-normalizing
tail.  That premise is load-bearing: the tail component is SN-only in
the K12.8 closure, so the ordinary arrow-reducibility of `consBranch`
is not enough to manufacture this closure for arbitrary tails. -/
theorem Reducible.fundamental_listElim_at_listType
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term sourceCtx motiveType nilRaw}
    {consBranch :
      Term sourceCtx
        (Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType)) consRaw}
    (scrutineeIH :
      Reducible ((Ty.listType elementType).subst sigma)
        (Term.subst termSubst scrutinee))
    (nilIH :
      Reducible (motiveType.subst sigma)
        (Term.subst termSubst nilBranch))
    (consIH :
      Reducible
        ((Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType)).subst sigma)
        (Term.subst termSubst consBranch))
    (consAppIsSN :
      ∀ {headRaw tailRaw : RawTerm targetScope}
        (headTerm : Term targetCtx (elementType.subst sigma) headRaw)
        (tailTerm : Term targetCtx ((Ty.listType elementType).subst sigma) tailRaw),
        Reducible (elementType.subst sigma) headTerm →
        Term.isStronglyNormalizing tailTerm →
        Term.isStronglyNormalizing
          (Term.app
            (Term.app (Term.subst termSubst consBranch) headTerm)
            tailTerm)) :
    Term.isStronglyNormalizing
      (Term.subst termSubst
        (Term.listElim scrutinee nilBranch consBranch)) :=
  scrutineeIH.2
    (Term.subst termSubst nilBranch)
    (Term.subst termSubst consBranch)
    (Reducible.isStronglyNormalizing nilIH)
    (Reducible.isStronglyNormalizing consIH)
    consAppIsSN

/-- Direct M04 SN endpoint for list elimination.

The list reducibility candidate carries the eliminator closure directly.
The cons branch still needs an explicit application-SN premise because
the current list closure tracks the tail only at SN, not full reducible
tail evidence. -/
theorem Term.listElim_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term sourceCtx motiveType nilRaw}
    {consBranch :
      Term sourceCtx
        (Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType)) consRaw}
    (scrutineeReducible :
      Reducible (Ty.listType elementType) scrutinee)
    (nilIsSN : Term.isStronglyNormalizing nilBranch)
    (consIsSN : Term.isStronglyNormalizing consBranch)
    (consAppIsSN :
      ∀ {headRaw tailRaw : RawTerm scope}
        (headTerm : Term sourceCtx elementType headRaw)
        (tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw),
        Reducible elementType headTerm →
        Term.isStronglyNormalizing tailTerm →
        Term.isStronglyNormalizing
          (Term.app (Term.app consBranch headTerm) tailTerm)) :
    Term.isStronglyNormalizing
      (Term.listElim scrutinee nilBranch consBranch) :=
  scrutineeReducible.2 nilBranch consBranch nilIsSN consIsSN consAppIsSN

/-- Direct M04 SN endpoint for option matching.

This exposes the SN-output eliminator closure stored in the option
reducibility candidate: reducible scrutinee, SN branches, and an
application-SN closure for the `Some` branch. -/
theorem Term.optionMatch_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (scrutineeReducible :
      Reducible (Ty.optionType elementType) scrutinee)
    (noneIsSN : Term.isStronglyNormalizing noneBranch)
    (someIsSN : Term.isStronglyNormalizing someBranch)
    (someAppIsSN :
      ∀ {valueRaw : RawTerm scope}
        (valueTerm : Term sourceCtx elementType valueRaw),
        Reducible elementType valueTerm →
        Term.isStronglyNormalizing (Term.app someBranch valueTerm)) :
    Term.isStronglyNormalizing
      (Term.optionMatch scrutinee noneBranch someBranch) :=
  scrutineeReducible.2 noneBranch someBranch
    noneIsSN someIsSN someAppIsSN

/-- Direct M04 SN endpoint for either matching.

The either candidate stores symmetric SN-output eliminator closures for the
left and right branches.  This theorem exposes that exact M04 endpoint
without claiming full reducibility at the arbitrary motive type. -/
theorem Term.eitherMatch_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch :
      Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch :
      Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeReducible :
      Reducible (Ty.eitherType leftType rightType) scrutinee)
    (leftIsSN : Term.isStronglyNormalizing leftBranch)
    (rightIsSN : Term.isStronglyNormalizing rightBranch)
    (leftAppIsSN :
      ∀ {valueRaw : RawTerm scope}
        (valueTerm : Term sourceCtx leftType valueRaw),
        Reducible leftType valueTerm →
        Term.isStronglyNormalizing (Term.app leftBranch valueTerm))
    (rightAppIsSN :
      ∀ {valueRaw : RawTerm scope}
        (valueTerm : Term sourceCtx rightType valueRaw),
        Reducible rightType valueTerm →
        Term.isStronglyNormalizing (Term.app rightBranch valueTerm)) :
    Term.isStronglyNormalizing
      (Term.eitherMatch scrutinee leftBranch rightBranch) :=
  scrutineeReducible.2 leftBranch rightBranch
    leftIsSN rightIsSN leftAppIsSN rightAppIsSN


/-! ## Renaming-stable mirrors of the SN-output ι-eliminator
fundamentals (K12.22.A / K12.22.B / K12.22.C)

Each `_sn_stable` companion below mirrors the `IsRenamingStableIsSN`
pattern from `IdentityEliminators`: rebuild SN at every injective-
renamed future world by re-deriving the underlying SN closure inputs
from `IsRenamingStableReducible` premises at the renamed world.  The
branch-application SN witnesses fall out of the arrow Reducibility's
second component evaluated at the renamed world, then `.isStronglyNormalizing`
projects SN — no external SN premises required.

Coverage of the K12.22 batch:

* `fundamental_boolElim_at_bool_sn_stable` — bool eliminator, all three
  IH Reducibles at the renamed world feed `RawTerm.boolElim_isStronglyNormalizing`.
* `fundamental_optionMatch_at_option_sn_stable` — option eliminator,
  the some-branch's arrow closure produces the value-application SN
  at every renamed world.
* `fundamental_eitherMatch_at_either_sn_stable` — either eliminator,
  same arrow-closure derivation for both left and right branches. -/

/-- Renaming-stable SN of `Term.boolElim` at `Ty.bool` —
`IsRenamingStableIsSN` mirror of `fundamental_boolElim_at_bool_sn`.
At each renamed world `Reducible Ty.bool` reduces to `Term.isStronglyNormalizing`
definitionally (Ty.bool is a closed leaf), so the three renamed-world
Reducibles feed `RawTerm.boolElim_isStronglyNormalizing` directly. -/
theorem Reducible.fundamental_boolElim_at_bool_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw}
    {elseBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw}
    (scrutineeIsStable :
      IsRenamingStableReducible ((Ty.bool : Ty level scope).subst sigma)
        (Term.subst termSubst scrutinee))
    (thenIsStable :
      IsRenamingStableReducible
        ((motiveType.subst0 Ty.bool RawTerm.boolTrue).subst sigma)
        (Term.subst termSubst thenBranch))
    (elseIsStable :
      IsRenamingStableReducible
        ((motiveType.subst0 Ty.bool RawTerm.boolFalse).subst sigma)
        (Term.subst termSubst elseBranch)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.boolElim scrutinee thenBranch elseBranch)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  have scrutineeReducibleAtRho :=
    scrutineeIsStable rhoIsInjective termRenaming
  have thenReducibleAtRho :=
    thenIsStable rhoIsInjective termRenaming
  have elseReducibleAtRho :=
    elseIsStable rhoIsInjective termRenaming
  exact RawTerm.boolElim_isStronglyNormalizing
    (Reducible.isStronglyNormalizing thenReducibleAtRho)
    (Reducible.isStronglyNormalizing elseReducibleAtRho)
    scrutineeReducibleAtRho

/-- Renaming-stable SN of `Term.optionMatch` at `Ty.optionType` —
`IsRenamingStableIsSN` mirror of `fundamental_optionMatch_at_option_sn`.
The some-branch arrow Reducibility at the renamed world is consumed
by `_at_option_sn` to derive the value-application SN closure
internally — no external lifting required. -/
theorem Reducible.fundamental_optionMatch_at_option_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term sourceCtx motiveType noneRaw}
    {someBranch :
      Term sourceCtx (Ty.arrow elementType motiveType) someRaw}
    (scrutineeIsStable :
      IsRenamingStableReducible ((Ty.optionType elementType).subst sigma)
        (Term.subst termSubst scrutinee))
    (noneIsStable :
      IsRenamingStableReducible (motiveType.subst sigma)
        (Term.subst termSubst noneBranch))
    (someIsStable :
      IsRenamingStableReducible ((Ty.arrow elementType motiveType).subst sigma)
        (Term.subst termSubst someBranch)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.optionMatch scrutinee noneBranch someBranch)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  have scrutineeReducibleAtRho :=
    scrutineeIsStable rhoIsInjective termRenaming
  have noneReducibleAtRho :=
    noneIsStable rhoIsInjective termRenaming
  have someReducibleAtRho :=
    someIsStable rhoIsInjective termRenaming
  exact scrutineeReducibleAtRho.2
    (Term.rename termRenaming (Term.subst termSubst noneBranch))
    (Term.rename termRenaming (Term.subst termSubst someBranch))
    (Reducible.isStronglyNormalizing noneReducibleAtRho)
    (Reducible.isStronglyNormalizing someReducibleAtRho)
    (fun valueTerm valueIH =>
      Reducible.isStronglyNormalizing
        (someReducibleAtRho.2 valueTerm valueIH))

/-- Renaming-stable SN of `Term.eitherMatch` at `Ty.eitherType` —
`IsRenamingStableIsSN` mirror of `fundamental_eitherMatch_at_either_sn`.
Both left and right branches' arrow Reducibilities at the renamed
world feed the corresponding application-SN closures. -/
theorem Reducible.fundamental_eitherMatch_at_either_sn_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    {scrutinee :
      Term sourceCtx (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch :
      Term sourceCtx (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch :
      Term sourceCtx (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeIsStable :
      IsRenamingStableReducible
        ((Ty.eitherType leftType rightType).subst sigma)
        (Term.subst termSubst scrutinee))
    (leftIsStable :
      IsRenamingStableReducible
        ((Ty.arrow leftType motiveType).subst sigma)
        (Term.subst termSubst leftBranch))
    (rightIsStable :
      IsRenamingStableReducible
        ((Ty.arrow rightType motiveType).subst sigma)
        (Term.subst termSubst rightBranch)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.eitherMatch scrutinee leftBranch rightBranch)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  have scrutineeReducibleAtRho :=
    scrutineeIsStable rhoIsInjective termRenaming
  have leftReducibleAtRho :=
    leftIsStable rhoIsInjective termRenaming
  have rightReducibleAtRho :=
    rightIsStable rhoIsInjective termRenaming
  exact scrutineeReducibleAtRho.2
    (Term.rename termRenaming (Term.subst termSubst leftBranch))
    (Term.rename termRenaming (Term.subst termSubst rightBranch))
    (Reducible.isStronglyNormalizing leftReducibleAtRho)
    (Reducible.isStronglyNormalizing rightReducibleAtRho)
    (fun valueTerm valueIH =>
      Reducible.isStronglyNormalizing
        (leftReducibleAtRho.2 valueTerm valueIH))
    (fun valueTerm valueIH =>
      Reducible.isStronglyNormalizing
        (rightReducibleAtRho.2 valueTerm valueIH))

/-! ## K12.21.U5 renaming-stable mirrors for natRec head-β endpoints

`fundamental_natRecZero_at_nat` and `fundamental_natRecSucc_at_nat`
ship per-canonical-introducer ι head-β endpoints at the `_sn` level
(K12.22).  The K12.21.U5 contract supplies the matching
`IsRenamingStableIsSN` mirrors: every typed Reducible IH becomes a
`IsRenamingStableReducible` premise, and the renamed-world SN
discharge runs through the raw endpoint
`RawTerm.natRec_natZero_isStronglyNormalizing` /
`RawTerm.natRec_natSucc_isStronglyNormalizing`. -/

/-- Renaming-stable variant of `fundamental_natRecZero_at_nat`. -/
theorem Reducible.fundamental_natRecZero_at_nat_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (zeroIsStable :
      IsRenamingStableReducible (motiveType.subst sigma)
        (Term.subst termSubst zeroBranch))
    (succIsStable :
      IsRenamingStableReducible
        ((Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)).subst sigma)
        (Term.subst termSubst succBranch)) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.natRec Term.natZero zeroBranch succBranch)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  have zeroReducibleAtRho :=
    zeroIsStable rhoIsInjective termRenaming
  have succReducibleAtRho :=
    succIsStable rhoIsInjective termRenaming
  exact RawTerm.natRec_natZero_isStronglyNormalizing
    (Reducible.isStronglyNormalizing zeroReducibleAtRho)
    (Reducible.isStronglyNormalizing succReducibleAtRho)

/-- Renaming-stable variant of `fundamental_natRecSucc_at_nat`. -/
theorem Reducible.fundamental_natRecSucc_at_nat_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {motiveType : Ty level scope}
    {predecessorRaw zeroRaw succRaw : RawTerm scope}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (predecessorIsStable :
      IsRenamingStableReducible
        ((Ty.nat : Ty level scope).subst sigma)
        (Term.subst termSubst predecessor))
    (zeroIsStable :
      IsRenamingStableReducible (motiveType.subst sigma)
        (Term.subst termSubst zeroBranch))
    (succIsStable :
      IsRenamingStableReducible
        ((Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)).subst sigma)
        (Term.subst termSubst succBranch))
    (recursiveIsStable :
      IsRenamingStableReducible (motiveType.subst sigma)
        (Term.subst termSubst
          (Term.natRec predecessor zeroBranch succBranch))) :
    IsRenamingStableIsSN
      (Term.subst termSubst
        (Term.natRec
          (Term.natSucc predecessor) zeroBranch succBranch)) := by
  intro _renamedScope _renamedCtx _rho rhoIsInjective termRenaming
  have predecessorReducibleAtRho :=
    predecessorIsStable rhoIsInjective termRenaming
  have zeroReducibleAtRho :=
    zeroIsStable rhoIsInjective termRenaming
  have succReducibleAtRho :=
    succIsStable rhoIsInjective termRenaming
  have recursiveReducibleAtRho :=
    recursiveIsStable rhoIsInjective termRenaming
  have predecessorIsSN :=
    Reducible.isStronglyNormalizing predecessorReducibleAtRho
  have zeroIsSN :=
    Reducible.isStronglyNormalizing zeroReducibleAtRho
  have succIsSN :=
    Reducible.isStronglyNormalizing succReducibleAtRho
  have recursiveIsSN :=
    Reducible.isStronglyNormalizing recursiveReducibleAtRho
  have contractumIsSN :=
    Reducible.isStronglyNormalizing
      ((succReducibleAtRho.2
          (Term.rename termRenaming (Term.subst termSubst predecessor))
          predecessorReducibleAtRho).2
        (Term.rename termRenaming
          (Term.subst termSubst
            (Term.natRec predecessor zeroBranch succBranch)))
        recursiveReducibleAtRho)
  exact RawTerm.natRec_natSucc_isStronglyNormalizing
    predecessorIsSN zeroIsSN succIsSN recursiveIsSN contractumIsSN

end LeanFX2

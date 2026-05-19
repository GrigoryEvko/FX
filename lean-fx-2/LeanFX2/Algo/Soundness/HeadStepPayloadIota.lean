import LeanFX2.Algo.Soundness.HeadStepBaseIota

namespace LeanFX2

/-! ## Payload-bearing β/ι soundness

The five soundness theorems for `Term.headStep?` firings on
canonical-with-payload scrutinee shapes — natElim/natRec succ,
listElim cons, optionMatch some, eitherMatch inl/inr.

Each follows the pattern:
1. From `scrutinee.headCtor = .X`, derive raw shape via
   `Term.headCtor_X_raw` (existential over payload raw).
2. Cases the raw equation to make raw concrete.
3. Apply `Term.<ctor>Destruct` to extract the typed payload + HEq.
4. Use the HEq to substitute scrutinee with the canonical form.
5. Apply the matching `Step.iota<Rule>` ctor.

Returns: the firing produces a Step witness from source to
the β/ι-reduct.  Zero-axiom under strict policy via
match-with-witness pattern (`feedback_lean_match_witness_pattern.md`).

These are the building blocks for closing the M08 contract
(extending `Term.headStep?_sound` to handle payload-firings). -/

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-- Soundness for the natElim-succ case: when scrutinee's head
is `natSucc`, the firing produces `app succBranch predTerm`,
reachable via `Step.iotaNatElimSucc`. -/
theorem Term.headStep?_sound_natElimSucc
    {motiveType : Ty level scope}
    {scrutRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.natSucc) :
    ∃ (predRaw' : RawTerm scope) (predTerm : Term context Ty.nat predRaw'),
      Step (Term.natElim scrutinee zeroBranch succBranch)
           (Term.app succBranch predTerm) := by
  obtain ⟨predRaw, rawEq⟩ := Term.headCtor_natSucc_raw scrutinee headEq
  cases rawEq
  obtain ⟨predTerm, scrutHEq⟩ := Term.natSuccDestruct scrutinee
  have scrutEq : scrutinee = Term.natSucc predTerm := eq_of_heq scrutHEq
  refine ⟨_, predTerm, ?_⟩
  rw [scrutEq]
  exact Step.iotaNatElimSucc predTerm zeroBranch succBranch

/-- Soundness for the natRec-succ case. -/
theorem Term.headStep?_sound_natRecSucc
    {motiveType : Ty level scope}
    {scrutRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context
                    (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.natSucc) :
    ∃ (predRaw' : RawTerm scope) (predTerm : Term context Ty.nat predRaw'),
      Step (Term.natRec scrutinee zeroBranch succBranch)
           (Term.app (Term.app succBranch predTerm)
                     (Term.natRec predTerm zeroBranch succBranch)) := by
  obtain ⟨predRaw, rawEq⟩ := Term.headCtor_natSucc_raw scrutinee headEq
  cases rawEq
  obtain ⟨predTerm, scrutHEq⟩ := Term.natSuccDestruct scrutinee
  have scrutEq : scrutinee = Term.natSucc predTerm := eq_of_heq scrutHEq
  refine ⟨_, predTerm, ?_⟩
  rw [scrutEq]
  exact Step.iotaNatRecSucc predTerm zeroBranch succBranch

/-- Soundness for the listElim-cons case. -/
theorem Term.headStep?_sound_listElimCons
    {elementType motiveType : Ty level scope}
    {scrutRaw nilRaw consRaw : RawTerm scope}
    (scrutinee : Term context (Ty.listType elementType) scrutRaw)
    (nilBranch : Term context motiveType nilRaw)
    (consBranch : Term context
                    (Ty.arrow elementType
                      (Ty.arrow (Ty.listType elementType) motiveType)) consRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.listCons) :
    ∃ (headRaw' tailRaw' : RawTerm scope)
      (headTerm : Term context elementType headRaw')
      (tailTerm : Term context (Ty.listType elementType) tailRaw'),
      Step (Term.listElim scrutinee nilBranch consBranch)
           (Term.app (Term.app consBranch headTerm) tailTerm) := by
  obtain ⟨headRaw, tailRaw, rawEq⟩ := Term.headCtor_listCons_raw scrutinee headEq
  cases rawEq
  obtain ⟨headTerm, tailTerm, scrutHEq⟩ := Term.listConsDestruct scrutinee
  have scrutEq : scrutinee = Term.listCons headTerm tailTerm := eq_of_heq scrutHEq
  refine ⟨_, _, headTerm, tailTerm, ?_⟩
  rw [scrutEq]
  exact Step.iotaListElimCons headTerm tailTerm nilBranch consBranch

/-- Soundness for the optionMatch-some case. -/
theorem Term.headStep?_sound_optionMatchSome
    {elementType motiveType : Ty level scope}
    {scrutRaw noneRaw someRaw : RawTerm scope}
    (scrutinee : Term context (Ty.optionType elementType) scrutRaw)
    (noneBranch : Term context motiveType noneRaw)
    (someBranch : Term context (Ty.arrow elementType motiveType) someRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.optionSome) :
    ∃ (valueRaw' : RawTerm scope) (valueTerm : Term context elementType valueRaw'),
      Step (Term.optionMatch scrutinee noneBranch someBranch)
           (Term.app someBranch valueTerm) := by
  obtain ⟨valueRaw, rawEq⟩ := Term.headCtor_optionSome_raw scrutinee headEq
  cases rawEq
  obtain ⟨valueTerm, scrutHEq⟩ := Term.optionSomeDestruct scrutinee
  have scrutEq : scrutinee = Term.optionSome valueTerm := eq_of_heq scrutHEq
  refine ⟨_, valueTerm, ?_⟩
  rw [scrutEq]
  exact Step.iotaOptionMatchSome valueTerm noneBranch someBranch

/-- Soundness for the eitherMatch-inl case. -/
theorem Term.headStep?_sound_eitherMatchInl
    {leftType rightType motiveType : Ty level scope}
    {scrutRaw leftBranchRaw rightBranchRaw : RawTerm scope}
    (scrutinee : Term context (Ty.eitherType leftType rightType) scrutRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftBranchRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightBranchRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.eitherInl) :
    ∃ (valueRaw' : RawTerm scope) (valueTerm : Term context leftType valueRaw'),
      Step (Term.eitherMatch scrutinee leftBranch rightBranch)
           (Term.app leftBranch valueTerm) := by
  obtain ⟨valueRaw, rawEq⟩ := Term.headCtor_eitherInl_raw scrutinee headEq
  cases rawEq
  obtain ⟨valueTerm, scrutHEq⟩ := Term.eitherInlDestruct scrutinee
  have scrutEq : scrutinee = Term.eitherInl (rightType := rightType) valueTerm :=
    eq_of_heq scrutHEq
  refine ⟨_, valueTerm, ?_⟩
  rw [scrutEq]
  exact Step.iotaEitherMatchInl valueTerm leftBranch rightBranch

/-- Soundness for the eitherMatch-inr case. -/
theorem Term.headStep?_sound_eitherMatchInr
    {leftType rightType motiveType : Ty level scope}
    {scrutRaw leftBranchRaw rightBranchRaw : RawTerm scope}
    (scrutinee : Term context (Ty.eitherType leftType rightType) scrutRaw)
    (leftBranch : Term context (Ty.arrow leftType motiveType) leftBranchRaw)
    (rightBranch : Term context (Ty.arrow rightType motiveType) rightBranchRaw)
    (headEq : scrutinee.headCtor = Term.HeadCtor.eitherInr) :
    ∃ (valueRaw' : RawTerm scope) (valueTerm : Term context rightType valueRaw'),
      Step (Term.eitherMatch scrutinee leftBranch rightBranch)
           (Term.app rightBranch valueTerm) := by
  obtain ⟨valueRaw, rawEq⟩ := Term.headCtor_eitherInr_raw scrutinee headEq
  cases rawEq
  obtain ⟨valueTerm, scrutHEq⟩ := Term.eitherInrDestruct scrutinee
  have scrutEq : scrutinee = Term.eitherInr (leftType := leftType) valueTerm :=
    eq_of_heq scrutHEq
  refine ⟨_, valueTerm, ?_⟩
  rw [scrutEq]
  exact Step.iotaEitherMatchInr valueTerm leftBranch rightBranch

end LeanFX2

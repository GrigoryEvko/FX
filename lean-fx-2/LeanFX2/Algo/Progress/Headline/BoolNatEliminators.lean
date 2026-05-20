import LeanFX2.Algo.Progress.Headline.Prelude

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-- Progress or step for `Term.boolElim`: when the scrutinee's head
is `boolTrue`, the term fires via `Step.iotaBoolElimTrue` producing
`thenBranch`; when `boolFalse`, via `Step.iotaBoolElimFalse` producing
`elseBranch`; for any other 74 heads, the boolElim is itself in WHNF
(template arm).

M05.D.2 conditional eliminator #13 of 17.  First TWO-firing case:
both literal Boolean introducers produce contracta.  Unlike the
previous three (pathApp/glueElim/idJ) — which required inlined
destructors to deconstruct unique-raw-shape Term ctors — boolElim
needs NO new destructor since `boolTrue` and `boolFalse` are
nullary canonical heads.  We reuse `Term.headCtor_boolTrue_raw` /
`_boolFalse_raw` (Algo/WHNF/NullaryInversions.lean) to recover the
raw projection from the head-ctor dispatch, then `Term.boolTrue_unique`
/ `_boolFalse_unique` (Term/Inversion.lean) to identify the scrutinee
with the literal at the typed level.  Same pattern as `headStep?_sound_boolElimTrue` in `Algo/Soundness.lean:70-86`. -/
theorem Term.boolElim_progress_or_step
    {context : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutineeRaw)
    (thenBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolTrue) thenRaw)
    (elseBranch :
      Term context (motiveType.subst0 Ty.bool RawTerm.boolFalse) elseRaw) :
    Term.isWHNF (Term.boolElim scrutinee thenBranch elseBranch) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.boolElim scrutinee thenBranch elseBranch) target := by
  cases h : scrutinee.headCtor with
  | boolTrue =>
      have rawEq : scrutineeRaw = RawTerm.boolTrue :=
        Term.headCtor_boolTrue_raw scrutinee h
      cases rawEq
      have scrutEq : scrutinee = Term.boolTrue :=
        eq_of_heq (Term.boolTrue_unique scrutinee Term.boolTrue)
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaBoolElimTrue thenBranch elseBranch⟩
  | boolFalse =>
      have rawEq : scrutineeRaw = RawTerm.boolFalse :=
        Term.headCtor_boolFalse_raw scrutinee h
      cases rawEq
      have scrutEq : scrutinee = Term.boolFalse :=
        eq_of_heq (Term.boolFalse_unique scrutinee Term.boolFalse)
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaBoolElimFalse thenBranch elseBranch⟩
  | var =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | unit =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | lam =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | app =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | lamPi =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | appPi =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pair =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | fst =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | snd =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natZero =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natSucc =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natRec =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listNil =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listCons =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionNone =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionSome =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionMatch =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherInl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherInr =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherMatch =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idJ =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqJ =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqFunext =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idStrictRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idStrictRec =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | modIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | modElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | subsume =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | interval0 =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | interval1 =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalOpp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalMeet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalJoin =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pathLam =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pathApp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | glueIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | glueElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | transp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | hcomp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | recordIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | recordProj =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refineIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refineElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | codataUnfold =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | codataDest =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sessionSend =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sessionRecv =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | effectPerform =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | universeCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | cumulUp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivReflId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivReflIdAtId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextReflAtId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivApp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | uaIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | uaToEquiv =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivApply =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | arrowCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | piTyCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sigmaTyCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | productCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sumCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide

/-- Progress or step for `Term.natElim`: when the scrutinee's head is
`natZero`, the term fires via `Step.iotaNatElimZero` producing
`zeroBranch`; when `natSucc`, via `Step.iotaNatElimSucc` producing
`Term.app succBranch predecessor`; for any other 74 heads, the natElim
is itself in WHNF (template arm).

M05.D.2 conditional eliminator #14 of 17.  Second two-firing case.
Unlike `boolElim_progress_or_step` (#13), the `natSucc` firing branch
needs the destructor `Term.natSuccDestruct` (Term/Inversion.lean:123)
to extract the predecessor for the `Step.iotaNatElimSucc` reduct
`Term.app succBranch predTerm`.  The `natZero` arm is identical in
shape to a nullary-canonical firing (parallel to boolTrue/boolFalse).
Same pattern as `headStep?_sound_natElimSucc` in
`Algo/Soundness.lean:251-267`. -/
theorem Term.natElim_progress_or_step
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
    Term.isWHNF (Term.natElim scrutinee zeroBranch succBranch) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.natElim scrutinee zeroBranch succBranch) target := by
  cases h : scrutinee.headCtor with
  | natZero =>
      have rawEq : scrutineeRaw = RawTerm.natZero :=
        Term.headCtor_natZero_raw scrutinee h
      cases rawEq
      have scrutEq : scrutinee = Term.natZero :=
        eq_of_heq (Term.natZero_unique scrutinee Term.natZero)
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaNatElimZero zeroBranch succBranch⟩
  | natSucc =>
      obtain ⟨predRaw, rawEq⟩ := Term.headCtor_natSucc_raw scrutinee h
      cases rawEq
      obtain ⟨predTerm, scrutHEq⟩ := Term.natSuccDestruct scrutinee
      have scrutEq : scrutinee = Term.natSucc predTerm :=
        eq_of_heq scrutHEq
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaNatElimSucc predTerm zeroBranch succBranch⟩
  | var =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | unit =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | lam =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | app =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | lamPi =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | appPi =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pair =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | fst =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | snd =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolTrue =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolFalse =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natRec =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listNil =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listCons =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionNone =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionSome =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionMatch =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherInl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherInr =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherMatch =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idJ =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqJ =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqFunext =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idStrictRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idStrictRec =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | modIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | modElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | subsume =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | interval0 =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | interval1 =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalOpp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalMeet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalJoin =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pathLam =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pathApp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | glueIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | glueElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | transp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | hcomp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | recordIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | recordProj =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refineIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refineElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | codataUnfold =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | codataDest =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sessionSend =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sessionRecv =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | effectPerform =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | universeCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | cumulUp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivReflId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivReflIdAtId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextReflAtId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivApp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | uaIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | uaToEquiv =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivApply =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | arrowCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | piTyCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sigmaTyCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | productCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sumCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide

/-- Progress or step for `Term.natRec`: when scrutinee head is `natZero`,
fires `Step.iotaNatRecZero` producing `zeroBranch`; when `natSucc`,
fires `Step.iotaNatRecSucc` producing `Term.app (Term.app succBranch
predecessor) (Term.natRec predecessor zeroBranch succBranch)`; otherwise
natRec is WHNF.

M05.D.2 conditional eliminator #15 of 17.  Mirrors
`natElim_progress_or_step` structure; only difference is `succBranch`
has binary arrow type (predecessor + prior result) and the reduct is
a nested `Term.app` chain.  Reuses the same `Term.natSuccDestruct`.
Pattern at `Algo/Soundness.lean:269-288`. -/
theorem Term.natRec_progress_or_step
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutineeRaw)
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
    Term.isWHNF (Term.natRec scrutinee zeroBranch succBranch) = true ∨
    ∃ (targetType : Ty level scope) (targetRaw : RawTerm scope)
      (target : Term context targetType targetRaw),
      Step (Term.natRec scrutinee zeroBranch succBranch) target := by
  cases h : scrutinee.headCtor with
  | natZero =>
      have rawEq : scrutineeRaw = RawTerm.natZero :=
        Term.headCtor_natZero_raw scrutinee h
      cases rawEq
      have scrutEq : scrutinee = Term.natZero :=
        eq_of_heq (Term.natZero_unique scrutinee Term.natZero)
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaNatRecZero zeroBranch succBranch⟩
  | natSucc =>
      obtain ⟨predRaw, rawEq⟩ := Term.headCtor_natSucc_raw scrutinee h
      cases rawEq
      obtain ⟨predTerm, scrutHEq⟩ := Term.natSuccDestruct scrutinee
      have scrutEq : scrutinee = Term.natSucc predTerm :=
        eq_of_heq scrutHEq
      rw [scrutEq]
      exact Or.inr
        ⟨_, _, _, Step.iotaNatRecSucc predTerm zeroBranch succBranch⟩
  | var =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | unit =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | lam =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | app =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | lamPi =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | appPi =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pair =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | fst =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | snd =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolTrue =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolFalse =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | boolElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | natRec =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listNil =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listCons =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionNone =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionSome =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionMatch =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherInl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherInr =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherMatch =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idJ =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqJ =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | oeqFunext =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idStrictRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idStrictRec =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | modIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | modElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | subsume =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | interval0 =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | interval1 =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalOpp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalMeet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | intervalJoin =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pathLam =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | pathApp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | glueIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | glueElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | transp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | hcomp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | recordIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | recordProj =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refineIntro =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | refineElim =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | codataUnfold =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | codataDest =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sessionSend =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sessionRecv =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | effectPerform =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | universeCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | cumulUp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivReflId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextRefl =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivReflIdAtId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextReflAtId =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivApp =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | uaIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | funextIntroHet =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | uaToEquiv =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivApply =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | arrowCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | piTyCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sigmaTyCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | productCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | sumCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | listCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | optionCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | eitherCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | idCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide
  | equivCode =>
      apply Or.inl; dsimp only [Term.isWHNF]; rw [h]; decide


end LeanFX2

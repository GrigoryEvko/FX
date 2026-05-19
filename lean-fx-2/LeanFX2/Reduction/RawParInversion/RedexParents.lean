import LeanFX2.Reduction.RawParRename

/-! # LeanFX2.Reduction.RawParInversion.RedexParents

Redex-parent inversion lemmas — for each ctor that may fire a β / ι
or its Deep variant, the inversion returns a disjunction over the
cong arm and each redex variant.  Consumed by `RawParWeakenInv`.

Covered families:

* `app` — refl, cong, shallow β, deep β
* `fst`, `snd` — refl, cong, shallow β, deep β
* `boolElim`, `natElim`, `natRec` — refl, cong, true/zero-ι and
  false/succ-ι plus their deep variants
* `listElim`, `optionMatch`, `eitherMatch` — refl, cong, nil/none/inl-ι
  and cons/some/inr-ι plus their deep variants
* `idJ` — refl, cong, refl-ι, deep refl-ι

## Root status

Layer 2 raw parallel-step inversion helper.  Zero axioms. -/

namespace LeanFX2

/-! ## Redex-parent inversions used by `RawParWeakenInv`.

For each ctor that may fire a redex / Deep par rule, the inversion
returns a disjunction: cong arm vs each redex / Deep variant. -/

/-- `RawStep.par (app f a) target` — refl, cong, shallow β, deep β. -/
theorem RawStep.par.app_inv {scope : Nat}
    {functionTerm argumentTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.app functionTerm argumentTerm) target) :
    (∃ functionTarget argumentTarget,
      target = RawTerm.app functionTarget argumentTarget ∧
        RawStep.par functionTerm functionTarget ∧
        RawStep.par argumentTerm argumentTarget) ∨
    (∃ bodyTarget argumentTarget,
      target = bodyTarget.subst0 argumentTarget ∧
        RawStep.par functionTerm (RawTerm.lam bodyTarget) ∧
        RawStep.par argumentTerm argumentTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨functionTerm, argumentTerm, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | app functionStep argumentStep =>
      exact Or.inl ⟨_, _, rfl, functionStep, argumentStep⟩
  | betaApp bodyStep argumentStep =>
      exact Or.inr ⟨_, _, rfl, RawStep.par.lam bodyStep, argumentStep⟩
  | betaAppDeep functionStep argumentStep =>
      exact Or.inr ⟨_, _, rfl, functionStep, argumentStep⟩

/-- `RawStep.par (fst p) target` — refl, cong, shallow β, deep β. -/
theorem RawStep.par.fst_inv {scope : Nat}
    {pairTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.fst pairTerm) target) :
    (∃ pairTarget,
      target = RawTerm.fst pairTarget ∧
        RawStep.par pairTerm pairTarget) ∨
    (∃ firstTarget secondTarget,
      target = firstTarget ∧
        RawStep.par pairTerm (RawTerm.pair firstTarget secondTarget)) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨pairTerm, rfl, RawStep.par.refl _⟩
  | fst pairStep =>
      exact Or.inl ⟨_, rfl, pairStep⟩
  | betaFstPair secondRaw firstStep =>
      exact Or.inr ⟨_, secondRaw, rfl,
        RawStep.par.pair firstStep (RawStep.par.refl _)⟩
  | betaFstPairDeep pairStep =>
      exact Or.inr ⟨_, _, rfl, pairStep⟩

/-- `RawStep.par (snd p) target` — refl, cong, shallow β, deep β. -/
theorem RawStep.par.snd_inv {scope : Nat}
    {pairTerm : RawTerm scope} {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.snd pairTerm) target) :
    (∃ pairTarget,
      target = RawTerm.snd pairTarget ∧
        RawStep.par pairTerm pairTarget) ∨
    (∃ firstTarget secondTarget,
      target = secondTarget ∧
        RawStep.par pairTerm (RawTerm.pair firstTarget secondTarget)) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨pairTerm, rfl, RawStep.par.refl _⟩
  | snd pairStep =>
      exact Or.inl ⟨_, rfl, pairStep⟩
  | betaSndPair firstRaw secondStep =>
      exact Or.inr ⟨firstRaw, _, rfl,
        RawStep.par.pair (RawStep.par.refl _) secondStep⟩
  | betaSndPairDeep pairStep =>
      exact Or.inr ⟨_, _, rfl, pairStep⟩

/-- `RawStep.par (boolElim s t e) target` — refl, cong, true-ι, false-ι,
plus their deep variants. -/
theorem RawStep.par.boolElim_inv {scope : Nat}
    {scrutinee thenBranch elseBranch : RawTerm scope}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.boolElim scrutinee thenBranch elseBranch) target) :
    (∃ scrutineeTarget thenTarget elseTarget,
      target = RawTerm.boolElim scrutineeTarget thenTarget elseTarget ∧
        RawStep.par scrutinee scrutineeTarget ∧
        RawStep.par thenBranch thenTarget ∧
        RawStep.par elseBranch elseTarget) ∨
    (∃ thenTarget,
      target = thenTarget ∧
        RawStep.par scrutinee RawTerm.boolTrue ∧
        RawStep.par thenBranch thenTarget) ∨
    (∃ elseTarget,
      target = elseTarget ∧
        RawStep.par scrutinee RawTerm.boolFalse ∧
        RawStep.par elseBranch elseTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨scrutinee, thenBranch, elseBranch, rfl,
        RawStep.par.refl _, RawStep.par.refl _, RawStep.par.refl _⟩
  | boolElim scrutineeStep thenStep elseStep =>
      exact Or.inl ⟨_, _, _, rfl, scrutineeStep, thenStep, elseStep⟩
  | iotaBoolElimTrue _elseRaw thenStep =>
      exact Or.inr (Or.inl ⟨_, rfl, RawStep.par.refl _, thenStep⟩)
  | iotaBoolElimFalse _thenRaw elseStep =>
      exact Or.inr (Or.inr ⟨_, rfl, RawStep.par.refl _, elseStep⟩)
  | iotaBoolElimTrueDeep _elseRaw scrutineeStep thenStep =>
      exact Or.inr (Or.inl ⟨_, rfl, scrutineeStep, thenStep⟩)
  | iotaBoolElimFalseDeep _thenRaw scrutineeStep elseStep =>
      exact Or.inr (Or.inr ⟨_, rfl, scrutineeStep, elseStep⟩)

/-- `RawStep.par (natElim s z c) target` — refl, cong, zero-ι, succ-ι,
plus their deep variants. -/
theorem RawStep.par.natElim_inv {scope : Nat}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.natElim scrutinee zeroBranch succBranch) target) :
    (∃ scrutineeTarget zeroTarget succTarget,
      target = RawTerm.natElim scrutineeTarget zeroTarget succTarget ∧
        RawStep.par scrutinee scrutineeTarget ∧
        RawStep.par zeroBranch zeroTarget ∧
        RawStep.par succBranch succTarget) ∨
    (∃ zeroTarget,
      target = zeroTarget ∧
        RawStep.par scrutinee RawTerm.natZero ∧
        RawStep.par zeroBranch zeroTarget) ∨
    (∃ predRaw succTarget,
      target = RawTerm.app succTarget predRaw ∧
        RawStep.par scrutinee (RawTerm.natSucc predRaw) ∧
        RawStep.par succBranch succTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨scrutinee, zeroBranch, succBranch, rfl,
        RawStep.par.refl _, RawStep.par.refl _, RawStep.par.refl _⟩
  | natElim scrutineeStep zeroStep succStep =>
      exact Or.inl ⟨_, _, _, rfl, scrutineeStep, zeroStep, succStep⟩
  | iotaNatElimZero _succRaw zeroStep =>
      exact Or.inr (Or.inl ⟨_, rfl, RawStep.par.refl _, zeroStep⟩)
  | iotaNatElimSucc _zeroRaw predStep succStep =>
      exact Or.inr (Or.inr ⟨_, _, rfl, RawStep.par.natSucc predStep, succStep⟩)
  | iotaNatElimZeroDeep _succRaw scrutineeStep zeroStep =>
      exact Or.inr (Or.inl ⟨_, rfl, scrutineeStep, zeroStep⟩)
  | iotaNatElimSuccDeep _zeroRaw scrutineeStep succStep =>
      exact Or.inr (Or.inr ⟨_, _, rfl, scrutineeStep, succStep⟩)

/-- `RawStep.par (natRec s z c) target` — refl, cong, zero-ι, succ-ι,
plus their deep variants. -/
theorem RawStep.par.natRec_inv {scope : Nat}
    {scrutinee zeroBranch succBranch : RawTerm scope}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.natRec scrutinee zeroBranch succBranch) target) :
    (∃ scrutineeTarget zeroTarget succTarget,
      target = RawTerm.natRec scrutineeTarget zeroTarget succTarget ∧
        RawStep.par scrutinee scrutineeTarget ∧
        RawStep.par zeroBranch zeroTarget ∧
        RawStep.par succBranch succTarget) ∨
    (∃ zeroTarget,
      target = zeroTarget ∧
        RawStep.par scrutinee RawTerm.natZero ∧
        RawStep.par zeroBranch zeroTarget) ∨
    (∃ predRaw zeroTarget succTarget,
      target = RawTerm.app (RawTerm.app succTarget predRaw)
                            (RawTerm.natRec predRaw zeroTarget succTarget) ∧
        RawStep.par scrutinee (RawTerm.natSucc predRaw) ∧
        RawStep.par zeroBranch zeroTarget ∧
        RawStep.par succBranch succTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨scrutinee, zeroBranch, succBranch, rfl,
        RawStep.par.refl _, RawStep.par.refl _, RawStep.par.refl _⟩
  | natRec scrutineeStep zeroStep succStep =>
      exact Or.inl ⟨_, _, _, rfl, scrutineeStep, zeroStep, succStep⟩
  | iotaNatRecZero _succRaw zeroStep =>
      exact Or.inr (Or.inl ⟨_, rfl, RawStep.par.refl _, zeroStep⟩)
  | iotaNatRecSucc predStep zeroStep succStep =>
      exact Or.inr (Or.inr ⟨_, _, _, rfl, RawStep.par.natSucc predStep,
                              zeroStep, succStep⟩)
  | iotaNatRecZeroDeep _succRaw scrutineeStep zeroStep =>
      exact Or.inr (Or.inl ⟨_, rfl, scrutineeStep, zeroStep⟩)
  | iotaNatRecSuccDeep scrutineeStep zeroStep succStep =>
      exact Or.inr (Or.inr ⟨_, _, _, rfl, scrutineeStep, zeroStep, succStep⟩)

/-- `RawStep.par (listElim s n c) target` — refl, cong, nil-ι, cons-ι,
plus their deep variants. -/
theorem RawStep.par.listElim_inv {scope : Nat}
    {scrutinee nilBranch consBranch : RawTerm scope}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par (RawTerm.listElim scrutinee nilBranch consBranch) target) :
    (∃ scrutineeTarget nilTarget consTarget,
      target = RawTerm.listElim scrutineeTarget nilTarget consTarget ∧
        RawStep.par scrutinee scrutineeTarget ∧
        RawStep.par nilBranch nilTarget ∧
        RawStep.par consBranch consTarget) ∨
    (∃ nilTarget,
      target = nilTarget ∧
        RawStep.par scrutinee RawTerm.listNil ∧
        RawStep.par nilBranch nilTarget) ∨
    (∃ headRaw tailRaw consTarget,
      target = RawTerm.app (RawTerm.app consTarget headRaw) tailRaw ∧
        RawStep.par scrutinee (RawTerm.listCons headRaw tailRaw) ∧
        RawStep.par consBranch consTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨scrutinee, nilBranch, consBranch, rfl,
        RawStep.par.refl _, RawStep.par.refl _, RawStep.par.refl _⟩
  | listElim scrutineeStep nilStep consStep =>
      exact Or.inl ⟨_, _, _, rfl, scrutineeStep, nilStep, consStep⟩
  | iotaListElimNil _consRaw nilStep =>
      exact Or.inr (Or.inl ⟨_, rfl, RawStep.par.refl _, nilStep⟩)
  | iotaListElimCons _nilRaw headStep tailStep consStep =>
      exact Or.inr (Or.inr ⟨_, _, _, rfl,
        RawStep.par.listCons headStep tailStep, consStep⟩)
  | iotaListElimNilDeep _consRaw scrutineeStep nilStep =>
      exact Or.inr (Or.inl ⟨_, rfl, scrutineeStep, nilStep⟩)
  | iotaListElimConsDeep _nilRaw scrutineeStep consStep =>
      exact Or.inr (Or.inr ⟨_, _, _, rfl, scrutineeStep, consStep⟩)

/-- `RawStep.par (optionMatch s n s') target` — refl, cong, none-ι, some-ι,
plus their deep variants. -/
theorem RawStep.par.optionMatch_inv {scope : Nat}
    {scrutinee noneBranch someBranch : RawTerm scope}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par
        (RawTerm.optionMatch scrutinee noneBranch someBranch) target) :
    (∃ scrutineeTarget noneTarget someTarget,
      target = RawTerm.optionMatch scrutineeTarget noneTarget someTarget ∧
        RawStep.par scrutinee scrutineeTarget ∧
        RawStep.par noneBranch noneTarget ∧
        RawStep.par someBranch someTarget) ∨
    (∃ noneTarget,
      target = noneTarget ∧
        RawStep.par scrutinee RawTerm.optionNone ∧
        RawStep.par noneBranch noneTarget) ∨
    (∃ valueRaw someTarget,
      target = RawTerm.app someTarget valueRaw ∧
        RawStep.par scrutinee (RawTerm.optionSome valueRaw) ∧
        RawStep.par someBranch someTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨scrutinee, noneBranch, someBranch, rfl,
        RawStep.par.refl _, RawStep.par.refl _, RawStep.par.refl _⟩
  | optionMatch scrutineeStep noneStep someStep =>
      exact Or.inl ⟨_, _, _, rfl, scrutineeStep, noneStep, someStep⟩
  | iotaOptionMatchNone _someRaw noneStep =>
      exact Or.inr (Or.inl ⟨_, rfl, RawStep.par.refl _, noneStep⟩)
  | iotaOptionMatchSome _noneRaw valueStep someStep =>
      exact Or.inr (Or.inr ⟨_, _, rfl,
        RawStep.par.optionSome valueStep, someStep⟩)
  | iotaOptionMatchNoneDeep _someRaw scrutineeStep noneStep =>
      exact Or.inr (Or.inl ⟨_, rfl, scrutineeStep, noneStep⟩)
  | iotaOptionMatchSomeDeep _noneRaw scrutineeStep someStep =>
      exact Or.inr (Or.inr ⟨_, _, rfl, scrutineeStep, someStep⟩)

/-- `RawStep.par (eitherMatch s l r) target` — refl, cong, inl-ι, inr-ι,
plus their deep variants. -/
theorem RawStep.par.eitherMatch_inv {scope : Nat}
    {scrutinee leftBranch rightBranch : RawTerm scope}
    {target : RawTerm scope}
    (parallelStep :
      RawStep.par
        (RawTerm.eitherMatch scrutinee leftBranch rightBranch) target) :
    (∃ scrutineeTarget leftTarget rightTarget,
      target = RawTerm.eitherMatch scrutineeTarget leftTarget rightTarget ∧
        RawStep.par scrutinee scrutineeTarget ∧
        RawStep.par leftBranch leftTarget ∧
        RawStep.par rightBranch rightTarget) ∨
    (∃ valueRaw leftTarget,
      target = RawTerm.app leftTarget valueRaw ∧
        RawStep.par scrutinee (RawTerm.eitherInl valueRaw) ∧
        RawStep.par leftBranch leftTarget) ∨
    (∃ valueRaw rightTarget,
      target = RawTerm.app rightTarget valueRaw ∧
        RawStep.par scrutinee (RawTerm.eitherInr valueRaw) ∧
        RawStep.par rightBranch rightTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨scrutinee, leftBranch, rightBranch, rfl,
        RawStep.par.refl _, RawStep.par.refl _, RawStep.par.refl _⟩
  | eitherMatch scrutineeStep leftStep rightStep =>
      exact Or.inl ⟨_, _, _, rfl, scrutineeStep, leftStep, rightStep⟩
  | iotaEitherMatchInl _rightRaw valueStep leftStep =>
      exact Or.inr (Or.inl ⟨_, _, rfl,
        RawStep.par.eitherInl valueStep, leftStep⟩)
  | iotaEitherMatchInr _leftRaw valueStep rightStep =>
      exact Or.inr (Or.inr ⟨_, _, rfl,
        RawStep.par.eitherInr valueStep, rightStep⟩)
  | iotaEitherMatchInlDeep _rightRaw scrutineeStep leftStep =>
      exact Or.inr (Or.inl ⟨_, _, rfl, scrutineeStep, leftStep⟩)
  | iotaEitherMatchInrDeep _leftRaw scrutineeStep rightStep =>
      exact Or.inr (Or.inr ⟨_, _, rfl, scrutineeStep, rightStep⟩)

/-- `RawStep.par (idJ b w) target` — refl, cong, refl-ι, deep refl-ι. -/
theorem RawStep.par.idJ_inv {scope : Nat}
    {baseCase witness : RawTerm scope}
    {target : RawTerm scope}
    (parallelStep : RawStep.par (RawTerm.idJ baseCase witness) target) :
    (∃ baseTarget witnessTarget,
      target = RawTerm.idJ baseTarget witnessTarget ∧
        RawStep.par baseCase baseTarget ∧
        RawStep.par witness witnessTarget) ∨
    (∃ witnessRaw baseTarget,
      target = baseTarget ∧
        RawStep.par witness (RawTerm.refl witnessRaw) ∧
        RawStep.par baseCase baseTarget) := by
  cases parallelStep with
  | refl _ =>
      exact Or.inl ⟨baseCase, witness, rfl,
        RawStep.par.refl _, RawStep.par.refl _⟩
  | idJ baseStep witnessStep =>
      exact Or.inl ⟨_, _, rfl, baseStep, witnessStep⟩
  | iotaIdJRefl witnessRaw baseStep =>
      exact Or.inr ⟨witnessRaw, _, rfl,
        RawStep.par.refl _, baseStep⟩
  | iotaIdJReflDeep witnessStep baseStep =>
      exact Or.inr ⟨_, _, rfl, witnessStep, baseStep⟩

end LeanFX2

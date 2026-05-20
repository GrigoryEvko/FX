import LeanFX2.Foundation.RawSubst.RenameDefs

/-! # Foundation/RawTermInjective — rename injectivity (D2.5.5 prerequisite)

Foundation lemmas for the cd-cascade rename helper that fires when
the dispatcher detects `piTyCode A A.weaken` shapes.  Without these,
the `decide (A = B)` test inside `cdTranspPathLamBody` is not
rename-equivariant under non-injective renamings.

Strict zero-axiom verified per declaration.  CRITICAL: proofs use
DIRECT pattern-match style (matching the propext-clean precedent of
`RawRenaming.lift_pointwise` in `RawSubst.lean`), NOT `by ... match`
tactic mode (which leaks propext through Lean 4 v4.29.1's match
compiler).

## Root status

* Layer: foundation (above `RawSubst`, below `Confluence/RawCdRename`)
* Load-bearing for: D2.5.5+ cd-cascade rename helpers
* Axiom budget: zero
-/

namespace LeanFX2

/-- A renaming is injective when distinct source positions map to
distinct target positions. -/
def RawRenamingInjective {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) : Prop :=
  ∀ (positionA positionB : Fin sourceScope),
    rawRenaming positionA = rawRenaming positionB →
    positionA = positionB

/-- `RawRenaming.weaken` (= `Fin.succ`) is injective.  Pure
val-level reasoning via `Nat.succ.inj`; no Fin pattern matching. -/
theorem RawRenamingInjective.weaken {scope : Nat} :
    RawRenamingInjective (RawRenaming.weaken (scope := scope)) := by
  intro positionA positionB succEq
  apply Fin.ext
  have valEq : (RawRenaming.weaken positionA).val =
               (RawRenaming.weaken positionB).val :=
    congrArg Fin.val succEq
  exact Nat.succ.inj valEq

/-- `RawRenaming.lift` preserves injectivity through binders.

DIRECT pattern-match style on `(positionA, positionB)` Fin pairs —
matches `RawRenaming.lift_pointwise`'s propext-clean precedent.
NOT `by ... match positionA with ...` (tactic-mode match leaks propext). -/
theorem RawRenamingInjective.lift {sourceScope targetScope : Nat}
    {rho : RawRenaming sourceScope targetScope}
    (rhoInjective : RawRenamingInjective rho) :
    RawRenamingInjective rho.lift
  | ⟨0, _⟩, ⟨0, _⟩, _ => rfl
  | ⟨0, _⟩, ⟨kB + 1, ltB⟩, liftEq => by
      exfalso
      have valLiftEq : (rho.lift ⟨0, Nat.zero_lt_succ _⟩).val =
                       (rho.lift ⟨kB + 1, ltB⟩).val :=
        congrArg Fin.val liftEq
      exact Nat.noConfusion valLiftEq
  | ⟨kA + 1, ltA⟩, ⟨0, _⟩, liftEq => by
      exfalso
      have valLiftEq : (rho.lift ⟨kA + 1, ltA⟩).val =
                       (rho.lift ⟨0, Nat.zero_lt_succ _⟩).val :=
        congrArg Fin.val liftEq
      exact Nat.noConfusion valLiftEq
  | ⟨kA + 1, ltA⟩, ⟨kB + 1, ltB⟩, liftEq => by
      have valLiftEq : (rho.lift ⟨kA + 1, ltA⟩).val =
                       (rho.lift ⟨kB + 1, ltB⟩).val :=
        congrArg Fin.val liftEq
      have rhoValEq : (rho ⟨kA, Nat.lt_of_succ_lt_succ ltA⟩).val =
                      (rho ⟨kB, Nat.lt_of_succ_lt_succ ltB⟩).val :=
        Nat.succ.inj valLiftEq
      have rhoEq : rho ⟨kA, Nat.lt_of_succ_lt_succ ltA⟩ =
                   rho ⟨kB, Nat.lt_of_succ_lt_succ ltB⟩ :=
        Fin.ext rhoValEq
      have abEq : (⟨kA, Nat.lt_of_succ_lt_succ ltA⟩ : Fin sourceScope) =
                  ⟨kB, Nat.lt_of_succ_lt_succ ltB⟩ :=
        rhoInjective _ _ rhoEq
      apply Fin.ext
      have valAB : kA = kB := congrArg Fin.val abEq
      show kA + 1 = kB + 1
      exact congrArg (· + 1) valAB

/-! ## Term-rename injectivity — full 73-ctor enumeration

When the renaming is injective, `term.rename rho` is injective in
`term`.  Structural induction on the source term; each ctor's case
splits on the second term.  `injection` is applied directly to
`renameEq` without first normalizing with `simp only [RawTerm.rename]`:
`RawTerm.rename` reduces definitionally per arm, so `injection`
sees through the `.rename` application straight to the underlying
constructor.  Non-matching ctors close because `injection` on an
equation between distinct constructors derives `False` and discharges
the goal; matching ctors extract the sub-equalities (the leading `_`
binds the scope-index equality the indexed-inductive `injection`
emits first) and apply IHs, lifting injectivity through binders via
`RawRenamingInjective.lift`.

Dropping the per-arm `simp only [RawTerm.rename]` avoids loading the
full equational unfolder of an 78-arm definition once per matching
constructor; combined over the constructor x constructor case split
this is the difference between ~125s and ~20s of elaboration.

Theorem signature: outer `(termA : RawTerm scope)` is the induction
variable; `targetScope`, `rho`, `termB`, `renameEq` are universally
quantified inside the body so the IH motive carries them. -/

theorem RawTerm.rename_injective_under_injective_renaming
    {scope : Nat} (termA : RawTerm scope) :
    ∀ {targetScope : Nat} {rho : RawRenaming scope targetScope},
      RawRenamingInjective rho →
      ∀ (termB : RawTerm scope),
        termA.rename rho = termB.rename rho → termA = termB := by
  induction termA with
  | var positionA =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | var positionB =>
          injection renameEq with _ positionEq
          exact congrArg RawTerm.var (rhoInjective positionA positionB positionEq)
      | _ =>
          injection renameEq
  | unit =>
      intro _ _ _ termB renameEq
      cases termB with
      | unit => rfl
      | _ =>
          injection renameEq
  | lam bodyA bodyIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | lam bodyB =>
          injection renameEq with _ bodyEq
          exact congrArg RawTerm.lam
            (bodyIH (RawRenamingInjective.lift rhoInjective) _ bodyEq)
      | _ =>
          injection renameEq
  | app fnA argA fnIH argIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | app fnB argB =>
          injection renameEq with _ fnEq argEq
          rw [fnIH rhoInjective _ fnEq, argIH rhoInjective _ argEq]
      | _ =>
          injection renameEq
  | pair firstA secondA firstIH secondIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | pair firstB secondB =>
          injection renameEq with _ firstEq secondEq
          rw [firstIH rhoInjective _ firstEq, secondIH rhoInjective _ secondEq]
      | _ =>
          injection renameEq
  | fst pairA pairIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | fst pairB =>
          injection renameEq with _ pairEq
          exact congrArg RawTerm.fst (pairIH rhoInjective _ pairEq)
      | _ =>
          injection renameEq
  | snd pairA pairIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | snd pairB =>
          injection renameEq with _ pairEq
          exact congrArg RawTerm.snd (pairIH rhoInjective _ pairEq)
      | _ =>
          injection renameEq
  | boolTrue =>
      intro _ _ _ termB renameEq
      cases termB with
      | boolTrue => rfl
      | _ =>
          injection renameEq
  | boolFalse =>
      intro _ _ _ termB renameEq
      cases termB with
      | boolFalse => rfl
      | _ =>
          injection renameEq
  | boolElim sA tA eA sIH tIH eIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | boolElim sB tB eB =>
          injection renameEq with _ sEq tEq eEq
          rw [sIH rhoInjective _ sEq, tIH rhoInjective _ tEq, eIH rhoInjective _ eEq]
      | _ =>
          injection renameEq
  | natZero =>
      intro _ _ _ termB renameEq
      cases termB with
      | natZero => rfl
      | _ =>
          injection renameEq
  | natSucc predA predIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | natSucc predB =>
          injection renameEq with _ predEq
          exact congrArg RawTerm.natSucc (predIH rhoInjective _ predEq)
      | _ =>
          injection renameEq
  | natElim sA zA succA sIH zIH succIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | natElim sB zB succB =>
          injection renameEq with _ sEq zEq succEq
          rw [sIH rhoInjective _ sEq, zIH rhoInjective _ zEq, succIH rhoInjective _ succEq]
      | _ =>
          injection renameEq
  | natRec sA zA succA sIH zIH succIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | natRec sB zB succB =>
          injection renameEq with _ sEq zEq succEq
          rw [sIH rhoInjective _ sEq, zIH rhoInjective _ zEq, succIH rhoInjective _ succEq]
      | _ =>
          injection renameEq
  | listNil =>
      intro _ _ _ termB renameEq
      cases termB with
      | listNil => rfl
      | _ =>
          injection renameEq
  | listCons headA tailA headIH tailIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | listCons headB tailB =>
          injection renameEq with _ headEq tailEq
          rw [headIH rhoInjective _ headEq, tailIH rhoInjective _ tailEq]
      | _ =>
          injection renameEq
  | listElim sA nA cA sIH nIH cIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | listElim sB nB cB =>
          injection renameEq with _ sEq nEq cEq
          rw [sIH rhoInjective _ sEq, nIH rhoInjective _ nEq, cIH rhoInjective _ cEq]
      | _ =>
          injection renameEq
  | optionNone =>
      intro _ _ _ termB renameEq
      cases termB with
      | optionNone => rfl
      | _ =>
          injection renameEq
  | optionSome valueA valueIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | optionSome valueB =>
          injection renameEq with _ valueEq
          exact congrArg RawTerm.optionSome (valueIH rhoInjective _ valueEq)
      | _ =>
          injection renameEq
  | optionMatch sA nA mA sIH nIH mIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | optionMatch sB nB mB =>
          injection renameEq with _ sEq nEq mEq
          rw [sIH rhoInjective _ sEq, nIH rhoInjective _ nEq, mIH rhoInjective _ mEq]
      | _ =>
          injection renameEq
  | eitherInl valueA valueIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | eitherInl valueB =>
          injection renameEq with _ valueEq
          exact congrArg RawTerm.eitherInl (valueIH rhoInjective _ valueEq)
      | _ =>
          injection renameEq
  | eitherInr valueA valueIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | eitherInr valueB =>
          injection renameEq with _ valueEq
          exact congrArg RawTerm.eitherInr (valueIH rhoInjective _ valueEq)
      | _ =>
          injection renameEq
  | eitherMatch sA lA rA sIH lIH rIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | eitherMatch sB lB rB =>
          injection renameEq with _ sEq lEq rEq
          rw [sIH rhoInjective _ sEq, lIH rhoInjective _ lEq, rIH rhoInjective _ rEq]
      | _ =>
          injection renameEq
  | refl witnessA witnessIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | refl witnessB =>
          injection renameEq with _ witnessEq
          exact congrArg RawTerm.refl (witnessIH rhoInjective _ witnessEq)
      | _ =>
          injection renameEq
  | idJ baseA witnessA baseIH witnessIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | idJ baseB witnessB =>
          injection renameEq with _ baseEq witnessEq
          rw [baseIH rhoInjective _ baseEq, witnessIH rhoInjective _ witnessEq]
      | _ =>
          injection renameEq
  | modIntro rawA rawIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | modIntro rawB =>
          injection renameEq with _ rawEq
          exact congrArg RawTerm.modIntro (rawIH rhoInjective _ rawEq)
      | _ =>
          injection renameEq
  | modElim rawA rawIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | modElim rawB =>
          injection renameEq with _ rawEq
          exact congrArg RawTerm.modElim (rawIH rhoInjective _ rawEq)
      | _ =>
          injection renameEq
  | subsume rawA rawIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | subsume rawB =>
          injection renameEq with _ rawEq
          exact congrArg RawTerm.subsume (rawIH rhoInjective _ rawEq)
      | _ =>
          injection renameEq
  | interval0 =>
      intro _ _ _ termB renameEq
      cases termB with
      | interval0 => rfl
      | _ =>
          injection renameEq
  | interval1 =>
      intro _ _ _ termB renameEq
      cases termB with
      | interval1 => rfl
      | _ =>
          injection renameEq
  | intervalOpp intervalA intervalIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | intervalOpp intervalB =>
          injection renameEq with _ intervalEq
          exact congrArg RawTerm.intervalOpp (intervalIH rhoInjective _ intervalEq)
      | _ =>
          injection renameEq
  | intervalMeet leftA rightA leftIH rightIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | intervalMeet leftB rightB =>
          injection renameEq with _ leftEq rightEq
          rw [leftIH rhoInjective _ leftEq, rightIH rhoInjective _ rightEq]
      | _ =>
          injection renameEq
  | intervalJoin leftA rightA leftIH rightIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | intervalJoin leftB rightB =>
          injection renameEq with _ leftEq rightEq
          rw [leftIH rhoInjective _ leftEq, rightIH rhoInjective _ rightEq]
      | _ =>
          injection renameEq
  | pathLam bodyA bodyIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | pathLam bodyB =>
          injection renameEq with _ bodyEq
          exact congrArg RawTerm.pathLam
            (bodyIH (RawRenamingInjective.lift rhoInjective) _ bodyEq)
      | _ =>
          injection renameEq
  | pathApp pathA argA pathIH argIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | pathApp pathB argB =>
          injection renameEq with _ pathEq argEq
          rw [pathIH rhoInjective _ pathEq, argIH rhoInjective _ argEq]
      | _ =>
          injection renameEq
  | glueIntro baseA partialA baseIH partialIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | glueIntro baseB partialB =>
          injection renameEq with _ baseEq partialEq
          rw [baseIH rhoInjective _ baseEq, partialIH rhoInjective _ partialEq]
      | _ =>
          injection renameEq
  | glueElim gluedA gluedIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | glueElim gluedB =>
          injection renameEq with _ gluedEq
          exact congrArg RawTerm.glueElim (gluedIH rhoInjective _ gluedEq)
      | _ =>
          injection renameEq
  | transp pathA sourceA pathIH sourceIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | transp pathB sourceB =>
          injection renameEq with _ pathEq sourceEq
          rw [pathIH rhoInjective _ pathEq, sourceIH rhoInjective _ sourceEq]
      | _ =>
          injection renameEq
  | transpFill pathTyA intervalA sourceA pathTyIH intervalIH sourceIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | transpFill pathTyB intervalB sourceB =>
          injection renameEq with _ pathTyEq intervalEq sourceEq
          rw [pathTyIH rhoInjective _ pathTyEq,
              intervalIH rhoInjective _ intervalEq,
              sourceIH rhoInjective _ sourceEq]
      | _ =>
          injection renameEq
  | hcomp sidesA capA sidesIH capIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | hcomp sidesB capB =>
          injection renameEq with _ sidesEq capEq
          rw [sidesIH rhoInjective _ sidesEq, capIH rhoInjective _ capEq]
      | _ =>
          injection renameEq
  | oeqRefl witnessA witnessIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | oeqRefl witnessB =>
          injection renameEq with _ witnessEq
          exact congrArg RawTerm.oeqRefl (witnessIH rhoInjective _ witnessEq)
      | _ =>
          injection renameEq
  | oeqJ baseA witnessA baseIH witnessIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | oeqJ baseB witnessB =>
          injection renameEq with _ baseEq witnessEq
          rw [baseIH rhoInjective _ baseEq, witnessIH rhoInjective _ witnessEq]
      | _ =>
          injection renameEq
  | oeqFunext pwA pwIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | oeqFunext pwB =>
          injection renameEq with _ pwEq
          exact congrArg RawTerm.oeqFunext (pwIH rhoInjective _ pwEq)
      | _ =>
          injection renameEq
  | idStrictRefl witnessA witnessIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | idStrictRefl witnessB =>
          injection renameEq with _ witnessEq
          exact congrArg RawTerm.idStrictRefl (witnessIH rhoInjective _ witnessEq)
      | _ =>
          injection renameEq
  | idStrictRec baseA witnessA baseIH witnessIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | idStrictRec baseB witnessB =>
          injection renameEq with _ baseEq witnessEq
          rw [baseIH rhoInjective _ baseEq, witnessIH rhoInjective _ witnessEq]
      | _ =>
          injection renameEq
  | equivIntro fwdA bwdA fwdIH bwdIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | equivIntro fwdB bwdB =>
          injection renameEq with _ fwdEq bwdEq
          rw [fwdIH rhoInjective _ fwdEq, bwdIH rhoInjective _ bwdEq]
      | _ =>
          injection renameEq
  | equivApp eA aA eIH aIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | equivApp eB aB =>
          injection renameEq with _ eEq aEq
          rw [eIH rhoInjective _ eEq, aIH rhoInjective _ aEq]
      | _ =>
          injection renameEq
  | refineIntro vA pA vIH pIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | refineIntro vB pB =>
          injection renameEq with _ vEq pEq
          rw [vIH rhoInjective _ vEq, pIH rhoInjective _ pEq]
      | _ =>
          injection renameEq
  | refineElim refinedA refinedIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | refineElim refinedB =>
          injection renameEq with _ refinedEq
          exact congrArg RawTerm.refineElim (refinedIH rhoInjective _ refinedEq)
      | _ =>
          injection renameEq
  | recordIntro firstA firstIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | recordIntro firstB =>
          injection renameEq with _ firstEq
          exact congrArg RawTerm.recordIntro (firstIH rhoInjective _ firstEq)
      | _ =>
          injection renameEq
  | recordProj recordA recordIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | recordProj recordB =>
          injection renameEq with _ recordEq
          exact congrArg RawTerm.recordProj (recordIH rhoInjective _ recordEq)
      | _ =>
          injection renameEq
  | codataUnfold initA transA initIH transIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | codataUnfold initB transB =>
          injection renameEq with _ initEq transEq
          rw [initIH rhoInjective _ initEq, transIH rhoInjective _ transEq]
      | _ =>
          injection renameEq
  | codataDest codataA codataIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | codataDest codataB =>
          injection renameEq with _ codataEq
          exact congrArg RawTerm.codataDest (codataIH rhoInjective _ codataEq)
      | _ =>
          injection renameEq
  | sessionSend cA pA cIH pIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | sessionSend cB pB =>
          injection renameEq with _ cEq pEq
          rw [cIH rhoInjective _ cEq, pIH rhoInjective _ pEq]
      | _ =>
          injection renameEq
  | sessionRecv channelA channelIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | sessionRecv channelB =>
          injection renameEq with _ channelEq
          exact congrArg RawTerm.sessionRecv (channelIH rhoInjective _ channelEq)
      | _ =>
          injection renameEq
  | effectPerform tA aA tIH aIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | effectPerform tB aB =>
          injection renameEq with _ tEq aEq
          rw [tIH rhoInjective _ tEq, aIH rhoInjective _ aEq]
      | _ =>
          injection renameEq
  | universeCode innerLevelA =>
      intro _ _ _ termB renameEq
      cases termB with
      | universeCode innerLevelB =>
          injection renameEq with _ levelEq
          exact congrArg RawTerm.universeCode levelEq
      | _ =>
          injection renameEq
  | arrowCode dA cA dIH cIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | arrowCode dB cB =>
          injection renameEq with _ dEq cEq
          rw [dIH rhoInjective _ dEq, cIH rhoInjective _ cEq]
      | _ =>
          injection renameEq
  | piTyCode dA cA dIH cIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | piTyCode dB cB =>
          injection renameEq with _ dEq cEq
          rw [dIH rhoInjective _ dEq,
              cIH (RawRenamingInjective.lift rhoInjective) _ cEq]
      | _ =>
          injection renameEq
  | sigmaTyCode dA cA dIH cIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | sigmaTyCode dB cB =>
          injection renameEq with _ dEq cEq
          rw [dIH rhoInjective _ dEq,
              cIH (RawRenamingInjective.lift rhoInjective) _ cEq]
      | _ =>
          injection renameEq
  | productCode fA sA fIH sIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | productCode fB sB =>
          injection renameEq with _ fEq sEq
          rw [fIH rhoInjective _ fEq, sIH rhoInjective _ sEq]
      | _ =>
          injection renameEq
  | sumCode lA rA lIH rIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | sumCode lB rB =>
          injection renameEq with _ lEq rEq
          rw [lIH rhoInjective _ lEq, rIH rhoInjective _ rEq]
      | _ =>
          injection renameEq
  | listCode elementA elementIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | listCode elementB =>
          injection renameEq with _ elementEq
          exact congrArg RawTerm.listCode (elementIH rhoInjective _ elementEq)
      | _ =>
          injection renameEq
  | optionCode elementA elementIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | optionCode elementB =>
          injection renameEq with _ elementEq
          exact congrArg RawTerm.optionCode (elementIH rhoInjective _ elementEq)
      | _ =>
          injection renameEq
  | eitherCode lA rA lIH rIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | eitherCode lB rB =>
          injection renameEq with _ lEq rEq
          rw [lIH rhoInjective _ lEq, rIH rhoInjective _ rEq]
      | _ =>
          injection renameEq
  | idCode tA lA rA tIH lIH rIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | idCode tB lB rB =>
          injection renameEq with _ tEq lEq rEq
          rw [tIH rhoInjective _ tEq, lIH rhoInjective _ lEq, rIH rhoInjective _ rEq]
      | _ =>
          injection renameEq
  | equivCode lA rA lIH rIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | equivCode lB rB =>
          injection renameEq with _ lEq rEq
          rw [lIH rhoInjective _ lEq, rIH rhoInjective _ rEq]
      | _ =>
          injection renameEq
  | cumulUpMarker innerA innerIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | cumulUpMarker innerB =>
          injection renameEq with _ innerEq
          exact congrArg RawTerm.cumulUpMarker (innerIH rhoInjective _ innerEq)
      | _ =>
          injection renameEq
  | uaToEquiv proofA proofIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | uaToEquiv proofB =>
          injection renameEq with _ proofEq
          exact congrArg RawTerm.uaToEquiv (proofIH rhoInjective _ proofEq)
      | _ =>
          injection renameEq
  | equivApply eA aA eIH aIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | equivApply eB aB =>
          injection renameEq with _ eEq aEq
          rw [eIH rhoInjective _ eEq, aIH rhoInjective _ aEq]
      | _ =>
          injection renameEq
  | pathCompose lA rA lIH rIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | pathCompose lB rB =>
          injection renameEq with _ lEq rEq
          rw [lIH rhoInjective _ lEq, rIH rhoInjective _ rEq]
      | _ =>
          injection renameEq
  | idToEquiv proofA proofIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | idToEquiv proofB =>
          injection renameEq with _ proofEq
          exact congrArg RawTerm.idToEquiv (proofIH rhoInjective _ proofEq)
      | _ =>
          injection renameEq
  | oeqTrans firstA secondA firstIH secondIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | oeqTrans firstB secondB =>
          injection renameEq with _ firstEq secondEq
          rw [firstIH rhoInjective _ firstEq, secondIH rhoInjective _ secondEq]
      | _ =>
          injection renameEq
  | equivCompose firstA secondA firstIH secondIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | equivCompose firstB secondB =>
          injection renameEq with _ firstEq secondEq
          rw [firstIH rhoInjective _ firstEq, secondIH rhoInjective _ secondEq]
      | _ =>
          injection renameEq

end LeanFX2

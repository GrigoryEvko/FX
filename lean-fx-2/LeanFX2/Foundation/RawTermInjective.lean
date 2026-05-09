import LeanFX2.Foundation.RawSubst

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
splits on the second term.  Non-matching ctors close via
`RawTerm.noConfusion rfl (heq_of_eq renameEq)` — the propext-clean
discharge that uses the indexed-inductive noConfusion (which
requires both index equality and HEq).  Matching ctors `injection`
to extract sub-equalities and apply IHs, lifting injectivity through
binders via `RawRenamingInjective.lift`.

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
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ positionEq
          exact congrArg RawTerm.var (rhoInjective positionA positionB positionEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | unit =>
      intro _ _ _ termB renameEq
      cases termB with
      | unit => rfl
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | lam bodyA bodyIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | lam bodyB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ bodyEq
          exact congrArg RawTerm.lam
            (bodyIH (RawRenamingInjective.lift rhoInjective) _ bodyEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | app fnA argA fnIH argIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | app fnB argB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ fnEq argEq
          rw [fnIH rhoInjective _ fnEq, argIH rhoInjective _ argEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | pair firstA secondA firstIH secondIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | pair firstB secondB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ firstEq secondEq
          rw [firstIH rhoInjective _ firstEq, secondIH rhoInjective _ secondEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | fst pairA pairIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | fst pairB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ pairEq
          exact congrArg RawTerm.fst (pairIH rhoInjective _ pairEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | snd pairA pairIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | snd pairB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ pairEq
          exact congrArg RawTerm.snd (pairIH rhoInjective _ pairEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | boolTrue =>
      intro _ _ _ termB renameEq
      cases termB with
      | boolTrue => rfl
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | boolFalse =>
      intro _ _ _ termB renameEq
      cases termB with
      | boolFalse => rfl
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | boolElim sA tA eA sIH tIH eIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | boolElim sB tB eB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ sEq tEq eEq
          rw [sIH rhoInjective _ sEq, tIH rhoInjective _ tEq, eIH rhoInjective _ eEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | natZero =>
      intro _ _ _ termB renameEq
      cases termB with
      | natZero => rfl
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | natSucc predA predIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | natSucc predB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ predEq
          exact congrArg RawTerm.natSucc (predIH rhoInjective _ predEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | natElim sA zA succA sIH zIH succIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | natElim sB zB succB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ sEq zEq succEq
          rw [sIH rhoInjective _ sEq, zIH rhoInjective _ zEq, succIH rhoInjective _ succEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | natRec sA zA succA sIH zIH succIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | natRec sB zB succB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ sEq zEq succEq
          rw [sIH rhoInjective _ sEq, zIH rhoInjective _ zEq, succIH rhoInjective _ succEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | listNil =>
      intro _ _ _ termB renameEq
      cases termB with
      | listNil => rfl
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | listCons headA tailA headIH tailIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | listCons headB tailB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ headEq tailEq
          rw [headIH rhoInjective _ headEq, tailIH rhoInjective _ tailEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | listElim sA nA cA sIH nIH cIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | listElim sB nB cB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ sEq nEq cEq
          rw [sIH rhoInjective _ sEq, nIH rhoInjective _ nEq, cIH rhoInjective _ cEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | optionNone =>
      intro _ _ _ termB renameEq
      cases termB with
      | optionNone => rfl
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | optionSome valueA valueIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | optionSome valueB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ valueEq
          exact congrArg RawTerm.optionSome (valueIH rhoInjective _ valueEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | optionMatch sA nA mA sIH nIH mIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | optionMatch sB nB mB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ sEq nEq mEq
          rw [sIH rhoInjective _ sEq, nIH rhoInjective _ nEq, mIH rhoInjective _ mEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | eitherInl valueA valueIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | eitherInl valueB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ valueEq
          exact congrArg RawTerm.eitherInl (valueIH rhoInjective _ valueEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | eitherInr valueA valueIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | eitherInr valueB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ valueEq
          exact congrArg RawTerm.eitherInr (valueIH rhoInjective _ valueEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | eitherMatch sA lA rA sIH lIH rIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | eitherMatch sB lB rB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ sEq lEq rEq
          rw [sIH rhoInjective _ sEq, lIH rhoInjective _ lEq, rIH rhoInjective _ rEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | refl witnessA witnessIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | refl witnessB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ witnessEq
          exact congrArg RawTerm.refl (witnessIH rhoInjective _ witnessEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | idJ baseA witnessA baseIH witnessIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | idJ baseB witnessB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ baseEq witnessEq
          rw [baseIH rhoInjective _ baseEq, witnessIH rhoInjective _ witnessEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | modIntro rawA rawIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | modIntro rawB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ rawEq
          exact congrArg RawTerm.modIntro (rawIH rhoInjective _ rawEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | modElim rawA rawIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | modElim rawB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ rawEq
          exact congrArg RawTerm.modElim (rawIH rhoInjective _ rawEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | subsume rawA rawIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | subsume rawB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ rawEq
          exact congrArg RawTerm.subsume (rawIH rhoInjective _ rawEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | interval0 =>
      intro _ _ _ termB renameEq
      cases termB with
      | interval0 => rfl
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | interval1 =>
      intro _ _ _ termB renameEq
      cases termB with
      | interval1 => rfl
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | intervalOpp intervalA intervalIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | intervalOpp intervalB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ intervalEq
          exact congrArg RawTerm.intervalOpp (intervalIH rhoInjective _ intervalEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | intervalMeet leftA rightA leftIH rightIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | intervalMeet leftB rightB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ leftEq rightEq
          rw [leftIH rhoInjective _ leftEq, rightIH rhoInjective _ rightEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | intervalJoin leftA rightA leftIH rightIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | intervalJoin leftB rightB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ leftEq rightEq
          rw [leftIH rhoInjective _ leftEq, rightIH rhoInjective _ rightEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | pathLam bodyA bodyIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | pathLam bodyB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ bodyEq
          exact congrArg RawTerm.pathLam
            (bodyIH (RawRenamingInjective.lift rhoInjective) _ bodyEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | pathApp pathA argA pathIH argIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | pathApp pathB argB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ pathEq argEq
          rw [pathIH rhoInjective _ pathEq, argIH rhoInjective _ argEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | glueIntro baseA partialA baseIH partialIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | glueIntro baseB partialB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ baseEq partialEq
          rw [baseIH rhoInjective _ baseEq, partialIH rhoInjective _ partialEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | glueElim gluedA gluedIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | glueElim gluedB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ gluedEq
          exact congrArg RawTerm.glueElim (gluedIH rhoInjective _ gluedEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | transp pathA sourceA pathIH sourceIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | transp pathB sourceB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ pathEq sourceEq
          rw [pathIH rhoInjective _ pathEq, sourceIH rhoInjective _ sourceEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | hcomp sidesA capA sidesIH capIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | hcomp sidesB capB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ sidesEq capEq
          rw [sidesIH rhoInjective _ sidesEq, capIH rhoInjective _ capEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | oeqRefl witnessA witnessIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | oeqRefl witnessB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ witnessEq
          exact congrArg RawTerm.oeqRefl (witnessIH rhoInjective _ witnessEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | oeqJ baseA witnessA baseIH witnessIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | oeqJ baseB witnessB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ baseEq witnessEq
          rw [baseIH rhoInjective _ baseEq, witnessIH rhoInjective _ witnessEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | oeqFunext pwA pwIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | oeqFunext pwB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ pwEq
          exact congrArg RawTerm.oeqFunext (pwIH rhoInjective _ pwEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | idStrictRefl witnessA witnessIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | idStrictRefl witnessB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ witnessEq
          exact congrArg RawTerm.idStrictRefl (witnessIH rhoInjective _ witnessEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | idStrictRec baseA witnessA baseIH witnessIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | idStrictRec baseB witnessB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ baseEq witnessEq
          rw [baseIH rhoInjective _ baseEq, witnessIH rhoInjective _ witnessEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | equivIntro fwdA bwdA fwdIH bwdIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | equivIntro fwdB bwdB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ fwdEq bwdEq
          rw [fwdIH rhoInjective _ fwdEq, bwdIH rhoInjective _ bwdEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | equivApp eA aA eIH aIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | equivApp eB aB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ eEq aEq
          rw [eIH rhoInjective _ eEq, aIH rhoInjective _ aEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | refineIntro vA pA vIH pIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | refineIntro vB pB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ vEq pEq
          rw [vIH rhoInjective _ vEq, pIH rhoInjective _ pEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | refineElim refinedA refinedIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | refineElim refinedB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ refinedEq
          exact congrArg RawTerm.refineElim (refinedIH rhoInjective _ refinedEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | recordIntro firstA firstIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | recordIntro firstB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ firstEq
          exact congrArg RawTerm.recordIntro (firstIH rhoInjective _ firstEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | recordProj recordA recordIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | recordProj recordB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ recordEq
          exact congrArg RawTerm.recordProj (recordIH rhoInjective _ recordEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | codataUnfold initA transA initIH transIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | codataUnfold initB transB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ initEq transEq
          rw [initIH rhoInjective _ initEq, transIH rhoInjective _ transEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | codataDest codataA codataIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | codataDest codataB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ codataEq
          exact congrArg RawTerm.codataDest (codataIH rhoInjective _ codataEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | sessionSend cA pA cIH pIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | sessionSend cB pB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ cEq pEq
          rw [cIH rhoInjective _ cEq, pIH rhoInjective _ pEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | sessionRecv channelA channelIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | sessionRecv channelB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ channelEq
          exact congrArg RawTerm.sessionRecv (channelIH rhoInjective _ channelEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | effectPerform tA aA tIH aIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | effectPerform tB aB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ tEq aEq
          rw [tIH rhoInjective _ tEq, aIH rhoInjective _ aEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | universeCode innerLevelA =>
      intro _ _ _ termB renameEq
      cases termB with
      | universeCode innerLevelB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ levelEq
          exact congrArg RawTerm.universeCode levelEq
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | arrowCode dA cA dIH cIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | arrowCode dB cB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ dEq cEq
          rw [dIH rhoInjective _ dEq, cIH rhoInjective _ cEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | piTyCode dA cA dIH cIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | piTyCode dB cB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ dEq cEq
          rw [dIH rhoInjective _ dEq,
              cIH (RawRenamingInjective.lift rhoInjective) _ cEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | sigmaTyCode dA cA dIH cIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | sigmaTyCode dB cB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ dEq cEq
          rw [dIH rhoInjective _ dEq,
              cIH (RawRenamingInjective.lift rhoInjective) _ cEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | productCode fA sA fIH sIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | productCode fB sB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ fEq sEq
          rw [fIH rhoInjective _ fEq, sIH rhoInjective _ sEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | sumCode lA rA lIH rIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | sumCode lB rB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ lEq rEq
          rw [lIH rhoInjective _ lEq, rIH rhoInjective _ rEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | listCode elementA elementIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | listCode elementB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ elementEq
          exact congrArg RawTerm.listCode (elementIH rhoInjective _ elementEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | optionCode elementA elementIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | optionCode elementB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ elementEq
          exact congrArg RawTerm.optionCode (elementIH rhoInjective _ elementEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | eitherCode lA rA lIH rIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | eitherCode lB rB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ lEq rEq
          rw [lIH rhoInjective _ lEq, rIH rhoInjective _ rEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | idCode tA lA rA tIH lIH rIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | idCode tB lB rB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ tEq lEq rEq
          rw [tIH rhoInjective _ tEq, lIH rhoInjective _ lEq, rIH rhoInjective _ rEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | equivCode lA rA lIH rIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | equivCode lB rB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ lEq rEq
          rw [lIH rhoInjective _ lEq, rIH rhoInjective _ rEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | cumulUpMarker innerA innerIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | cumulUpMarker innerB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ innerEq
          exact congrArg RawTerm.cumulUpMarker (innerIH rhoInjective _ innerEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | uaToEquiv proofA proofIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | uaToEquiv proofB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ proofEq
          exact congrArg RawTerm.uaToEquiv (proofIH rhoInjective _ proofEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | equivApply eA aA eIH aIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | equivApply eB aB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ eEq aEq
          rw [eIH rhoInjective _ eEq, aIH rhoInjective _ aEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | pathCompose lA rA lIH rIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | pathCompose lB rB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ lEq rEq
          rw [lIH rhoInjective _ lEq, rIH rhoInjective _ rEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | idToEquiv proofA proofIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | idToEquiv proofB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ proofEq
          exact congrArg RawTerm.idToEquiv (proofIH rhoInjective _ proofEq)
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | oeqTrans firstA secondA firstIH secondIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | oeqTrans firstB secondB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ firstEq secondEq
          rw [firstIH rhoInjective _ firstEq, secondIH rhoInjective _ secondEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)
  | equivCompose firstA secondA firstIH secondIH =>
      intro _ _ rhoInjective termB renameEq
      cases termB with
      | equivCompose firstB secondB =>
          simp only [RawTerm.rename] at renameEq
          injection renameEq with _ firstEq secondEq
          rw [firstIH rhoInjective _ firstEq, secondIH rhoInjective _ secondEq]
      | _ =>
          simp only [RawTerm.rename] at renameEq
          exact RawTerm.noConfusion rfl (heq_of_eq renameEq)

end LeanFX2

import LeanFX2.Algo.Soundness.HeadStepPayloadIota

namespace LeanFX2

/-! ## Closure soundness

`Term.headStep?_sound` combines the 6 per-case theorems above
into a single closed-over statement: whenever `headStep?` fires
(returns `some _`), the result is reachable via `Step` from the
source term.

This is the load-bearing soundness contract for `Algo/Eval`:
the typed evaluator never produces a result that disagrees with
the kernel's reduction relation.

The proof case-analyses on the source term's outer constructor:
* Value, neutral, and deferred redex ctors have `headStep? = none`
  definitionally; the
  `firedEq : none = some _` hypothesis is closed by `simp` /
  `nomatch`.
* 5 eliminator ctors (boolElim, natElim, natRec, listElim,
  optionMatch) require splitting on the scrutinee's `headCtor`
  to identify which ι-rule fired, then applying the corresponding
  per-case theorem.

Zero-axiom under strict policy. -/


variable {mode : Mode} {level : Nat}

theorem Term.headStep?_sound
    {scope : Nat} {context : Ctx mode level scope}
    {someType : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context someType raw)
    {result : Σ (resultRaw : RawTerm scope), Term context someType resultRaw}
    (firedEq : someTerm.headStep? = some result) :
    Step someTerm result.snd := by
  cases someTerm with
  | var _ => nomatch firedEq
  | unit => nomatch firedEq
  | lam _ => nomatch firedEq
  | lamPi _ => nomatch firedEq
  | pair _ _ => nomatch firedEq
  | boolTrue => nomatch firedEq
  | boolFalse => nomatch firedEq
  | natZero => nomatch firedEq
  | natSucc _ => nomatch firedEq
  | listNil => nomatch firedEq
  | listCons _ _ => nomatch firedEq
  | optionNone => nomatch firedEq
  | optionSome _ => nomatch firedEq
  | eitherInl _ => nomatch firedEq
  | eitherInr _ => nomatch firedEq
  | refl _ _ => nomatch firedEq
  | oeqRefl _ _ => nomatch firedEq
  | oeqJ _ _ => nomatch firedEq
  | oeqFunext _ _ _ _ _ => nomatch firedEq
  | modIntro _ => nomatch firedEq
  | subsume _ => nomatch firedEq
  | interval0 => nomatch firedEq
  | interval1 => nomatch firedEq
  | intervalOpp _ => nomatch firedEq
  | intervalMeet _ _ => nomatch firedEq
  | intervalJoin _ _ => nomatch firedEq
  | pathLam _ _ _ _ => nomatch firedEq
  | glueIntro _ _ _ _ => nomatch firedEq
  | transp _ _ _ _ _ _ _ _ => nomatch firedEq
  | hcomp _ _ => nomatch firedEq
  | hcompPath _ _ _ _ => nomatch firedEq
  | recordIntro _ => nomatch firedEq
  | recordProj _ => nomatch firedEq
  | refineIntro _ _ _ => nomatch firedEq
  | refineElim _ => nomatch firedEq
  | codataUnfold _ _ => nomatch firedEq
  | codataDest _ => nomatch firedEq
  | sessionSend _ _ _ => nomatch firedEq
  | sessionRecv _ => nomatch firedEq
  | effectPerform _ _ _ _ _ _ => nomatch firedEq
  | universeCode _ _ _ _ => nomatch firedEq
  | cumulUp _ _ _ _ _ _ => nomatch firedEq
  | equivReflId _ => nomatch firedEq
  | funextRefl _ _ _ => nomatch firedEq
  | equivReflIdAtId _ _ _ _ => nomatch firedEq
  | funextReflAtId _ _ _ => nomatch firedEq
  | equivIntroHet _ _ _ _ => nomatch firedEq
  | equivApp _ _ => nomatch firedEq
  | uaIntroHet _ _ _ _ _ => nomatch firedEq
  | funextIntroHet _ _ _ _ => nomatch firedEq
  -- Phase D3.6-P3: univalence-β extractor.  Returns `none` from
  -- headStep?, so `firedEq : none = some _` is contradictory.
  | uaToEquiv _ _ _ _ _ _ _ => nomatch firedEq
  -- Phase D3.6-P4: univalence-β application.  Returns `none` from
  -- headStep?, so `firedEq : none = some _` is contradictory.
  | equivApply _ _ => nomatch firedEq
  -- CUMUL-2.4 typed type-code constructors (VALUE-shaped, all return
  -- `none` from headStep?, so `firedEq : none = some _` is contradictory).
  | arrowCode _ _ _ _ => nomatch firedEq
  | piTyCode _ _ _ _ => nomatch firedEq
  | sigmaTyCode _ _ _ _ => nomatch firedEq
  | productCode _ _ _ _ => nomatch firedEq
  | sumCode _ _ _ _ => nomatch firedEq
  | listCode _ _ _ => nomatch firedEq
  | optionCode _ _ _ => nomatch firedEq
  | eitherCode _ _ _ _ => nomatch firedEq
  | idCode _ _ _ _ _ => nomatch firedEq
  | equivCode _ _ _ _ => nomatch firedEq
  -- Eliminators not yet handled by headStep? (return none)
  | app _ _ => nomatch firedEq
  | appPi _ _ => nomatch firedEq
  | pathApp _ _ => nomatch firedEq
  | glueElim _ => nomatch firedEq
  | snd _ => nomatch firedEq
  | idJ _ _ => nomatch firedEq
  | idStrictRefl _ _ => nomatch firedEq
  | idStrictRec _ _ => nomatch firedEq
  | modElim _ => nomatch firedEq
  -- Firing eliminators.  Each dispatches on the scrutinee's
  -- `headCtor` value; the firing ι-rule depends on which canonical
  -- ctor the scrutinee has reduced to.
  --
  -- Pattern (from feedback_lean_match_propext_recipe.md): use
  -- `match headEq : scrutinee.headCtor with`, then `rw [show ...
  -- from rfl, headEq]` to definitionally unfold `headStep?` and
  -- substitute the headCtor value.  Avoids `simp` and `by_cases`
  -- which both leak propext on this large dep-typed match.
  | fst pairTerm =>
    match headEq : pairTerm.headCtor with
    | .pair =>
      rw [show (Term.fst pairTerm).headStep?
            = (let pairHead := pairTerm.headCtor
               if pairHead == .pair then
                 match Term.tryDestructPair pairTerm with
                 | some ⟨_, _, firstValue, _, _⟩ => some ⟨_, firstValue⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      match destructEq : Term.tryDestructPair pairTerm with
      | some ⟨_, _, firstValue, secondValue, ⟨rawEq, pairHEq⟩⟩ =>
        rw [destructEq] at firedEq
        cases firedEq
        cases rawEq
        have pairEq : pairTerm = Term.pair firstValue secondValue :=
          eq_of_heq pairHEq
        rw [pairEq]
        exact Step.betaFstPair firstValue secondValue
      | none =>
        rw [destructEq] at firedEq
        nomatch firedEq
    | .var | .unit | .lam | .app | .lamPi | .appPi
    | .fst | .snd
    | .boolTrue | .boolFalse | .boolElim
    | .natZero | .natSucc | .natElim | .natRec
    | .listNil | .listCons | .listElim
    | .optionNone | .optionSome | .optionMatch
    | .eitherInl | .eitherInr | .eitherMatch
    | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
    | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
    | .pathLam | .pathApp
    | .glueIntro | .glueElim | .transp | .hcomp
    | .recordIntro | .recordProj | .refineIntro | .refineElim
    | .codataUnfold | .codataDest
    | .sessionSend | .sessionRecv | .effectPerform
    | .universeCode | .cumulUp
    | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
    | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet | .uaToEquiv
    | .equivApply
    | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
    | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
      rw [show (Term.fst pairTerm).headStep?
            = (let pairHead := pairTerm.headCtor
               if pairHead == .pair then
                 match Term.tryDestructPair pairTerm with
                 | some ⟨_, _, firstValue, _, _⟩ => some ⟨_, firstValue⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      nomatch firedEq
  | @boolElim _ _ _ scrutineeRaw _ _ scrutinee thenBranch elseBranch =>
    match scrutineeRaw with
    | .boolTrue =>
      change (some ⟨_, thenBranch⟩ = some result) at firedEq
      cases firedEq
      have scrutEq : scrutinee = Term.boolTrue :=
        eq_of_heq (Term.boolTrue_unique scrutinee Term.boolTrue)
      rw [scrutEq]
      exact Step.iotaBoolElimTrue thenBranch elseBranch
    | .boolFalse =>
      change (some ⟨_, elseBranch⟩ = some result) at firedEq
      cases firedEq
      have scrutEq : scrutinee = Term.boolFalse :=
        eq_of_heq (Term.boolFalse_unique scrutinee Term.boolFalse)
      rw [scrutEq]
      exact Step.iotaBoolElimFalse thenBranch elseBranch
    | .var _
    | .unit
    | .lam _
    | .app _ _
    | .pair _ _
    | .fst _
    | .snd _
    | .boolElim _ _ _
    | .natZero
    | .natSucc _
    | .natElim _ _ _
    | .natRec _ _ _
    | .listNil
    | .listCons _ _
    | .listElim _ _ _
    | .optionNone
    | .optionSome _
    | .optionMatch _ _ _
    | .eitherInl _
    | .eitherInr _
    | .eitherMatch _ _ _
    | .refl _
    | .idJ _ _
    | .oeqRefl _
    | .oeqJ _ _
    | .oeqFunext _
    | .idStrictRefl _
    | .idStrictRec _ _
    | .modIntro _
    | .modElim _
    | .subsume _
    | .interval0
    | .interval1
    | .intervalOpp _
    | .intervalMeet _ _
    | .intervalJoin _ _
    | .pathLam _
    | .pathApp _ _
    | .glueIntro _ _
    | .glueElim _
    | .transp _ _
    | .hcomp _ _
    | .recordIntro _
    | .recordProj _
    | .refineIntro _ _
    | .refineElim _
    | .codataUnfold _ _
    | .codataDest _
    | .sessionSend _ _
    | .sessionRecv _
    | .effectPerform _ _
    | .universeCode _
    | .cumulUpMarker _
    | .uaToEquiv _
    | .equivApply _ _
    | .equivIntro _ _
    | .equivApp _ _
    | .arrowCode _ _
    | .piTyCode _ _
    | .sigmaTyCode _ _
    | .productCode _ _
    | .sumCode _ _
    | .listCode _
    | .optionCode _
    | .eitherCode _ _
    | .idCode _ _ _
    | .equivCode _ _ =>
      change (none = some result) at firedEq
      nomatch firedEq
  | natElim scrutinee zeroBranch succBranch =>
    match headEq : scrutinee.headCtor with
    | .natZero =>
      rw [show (Term.natElim scrutinee zeroBranch succBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .natZero then some ⟨_, zeroBranch⟩
               else if scrutineeHead == .natSucc then
                 match Term.tryDestructNatSucc scrutinee with
                 | some ⟨_, predTerm, _⟩ => some ⟨_, Term.app succBranch predTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      cases firedEq
      exact Term.headStep?_sound_natElimZero scrutinee zeroBranch succBranch headEq
    | .natSucc =>
      rw [show (Term.natElim scrutinee zeroBranch succBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .natZero then some ⟨_, zeroBranch⟩
               else if scrutineeHead == .natSucc then
                 match Term.tryDestructNatSucc scrutinee with
                 | some ⟨_, predTerm, _⟩ => some ⟨_, Term.app succBranch predTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      match destructEq : Term.tryDestructNatSucc scrutinee with
      | some ⟨_, predTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
        rw [destructEq] at firedEq
        cases firedEq
        cases rawEq
        have scrutEq : scrutinee = Term.natSucc predTerm := eq_of_heq scrutineeHEq
        rw [scrutEq]
        exact Step.iotaNatElimSucc predTerm zeroBranch succBranch
      | none =>
        rw [destructEq] at firedEq
        nomatch firedEq
    | .var | .unit | .lam | .app | .lamPi | .appPi
    | .pair | .fst | .snd
    | .boolTrue | .boolFalse | .boolElim
    | .natElim | .natRec
    | .listNil | .listCons | .listElim
    | .optionNone | .optionSome | .optionMatch
    | .eitherInl | .eitherInr | .eitherMatch
    | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
    | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
    | .pathLam | .pathApp
    | .glueIntro | .glueElim | .transp | .hcomp
    | .recordIntro | .recordProj | .refineIntro | .refineElim
    | .codataUnfold | .codataDest
    | .sessionSend | .sessionRecv | .effectPerform
    | .universeCode | .cumulUp
    | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
    | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet | .uaToEquiv
    | .equivApply
    | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
    | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
      rw [show (Term.natElim scrutinee zeroBranch succBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .natZero then some ⟨_, zeroBranch⟩
               else if scrutineeHead == .natSucc then
                 match Term.tryDestructNatSucc scrutinee with
                 | some ⟨_, predTerm, _⟩ => some ⟨_, Term.app succBranch predTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      nomatch firedEq
  | natRec scrutinee zeroBranch succBranch =>
    match headEq : scrutinee.headCtor with
    | .natZero =>
      rw [show (Term.natRec scrutinee zeroBranch succBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .natZero then some ⟨_, zeroBranch⟩
               else if scrutineeHead == .natSucc then
                 match Term.tryDestructNatSucc scrutinee with
                 | some ⟨_, predTerm, _⟩ =>
                     some ⟨_, Term.app (Term.app succBranch predTerm)
                                        (Term.natRec predTerm zeroBranch succBranch)⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      cases firedEq
      exact Term.headStep?_sound_natRecZero scrutinee zeroBranch succBranch headEq
    | .natSucc =>
      rw [show (Term.natRec scrutinee zeroBranch succBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .natZero then some ⟨_, zeroBranch⟩
               else if scrutineeHead == .natSucc then
                 match Term.tryDestructNatSucc scrutinee with
                 | some ⟨_, predTerm, _⟩ =>
                     some ⟨_, Term.app (Term.app succBranch predTerm)
                                        (Term.natRec predTerm zeroBranch succBranch)⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      match destructEq : Term.tryDestructNatSucc scrutinee with
      | some ⟨_, predTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
        rw [destructEq] at firedEq
        cases firedEq
        cases rawEq
        have scrutEq : scrutinee = Term.natSucc predTerm := eq_of_heq scrutineeHEq
        rw [scrutEq]
        exact Step.iotaNatRecSucc predTerm zeroBranch succBranch
      | none =>
        rw [destructEq] at firedEq
        nomatch firedEq
    | .var | .unit | .lam | .app | .lamPi | .appPi
    | .pair | .fst | .snd
    | .boolTrue | .boolFalse | .boolElim
    | .natElim | .natRec
    | .listNil | .listCons | .listElim
    | .optionNone | .optionSome | .optionMatch
    | .eitherInl | .eitherInr | .eitherMatch
    | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
    | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
    | .pathLam | .pathApp
    | .glueIntro | .glueElim | .transp | .hcomp
    | .recordIntro | .recordProj | .refineIntro | .refineElim
    | .codataUnfold | .codataDest
    | .sessionSend | .sessionRecv | .effectPerform
    | .universeCode | .cumulUp
    | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
    | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet | .uaToEquiv
    | .equivApply
    | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
    | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
      rw [show (Term.natRec scrutinee zeroBranch succBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .natZero then some ⟨_, zeroBranch⟩
               else if scrutineeHead == .natSucc then
                 match Term.tryDestructNatSucc scrutinee with
                 | some ⟨_, predTerm, _⟩ =>
                     some ⟨_, Term.app (Term.app succBranch predTerm)
                                        (Term.natRec predTerm zeroBranch succBranch)⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      nomatch firedEq
  | listElim scrutinee nilBranch consBranch =>
    match headEq : scrutinee.headCtor with
    | .listNil =>
      rw [show (Term.listElim scrutinee nilBranch consBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .listNil then some ⟨_, nilBranch⟩
               else if scrutineeHead == .listCons then
                 match Term.tryDestructListCons scrutinee with
                 | some ⟨_, _, headTerm, tailTerm, _⟩ =>
                     some ⟨_, Term.app (Term.app consBranch headTerm) tailTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      cases firedEq
      exact Term.headStep?_sound_listElimNil scrutinee nilBranch consBranch headEq
    | .listCons =>
      rw [show (Term.listElim scrutinee nilBranch consBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .listNil then some ⟨_, nilBranch⟩
               else if scrutineeHead == .listCons then
                 match Term.tryDestructListCons scrutinee with
                 | some ⟨_, _, headTerm, tailTerm, _⟩ =>
                     some ⟨_, Term.app (Term.app consBranch headTerm) tailTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      match destructEq : Term.tryDestructListCons scrutinee with
      | some ⟨_, _, headTerm, tailTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
        rw [destructEq] at firedEq
        cases firedEq
        cases rawEq
        have scrutEq : scrutinee = Term.listCons headTerm tailTerm :=
          eq_of_heq scrutineeHEq
        rw [scrutEq]
        exact Step.iotaListElimCons headTerm tailTerm nilBranch consBranch
      | none =>
        rw [destructEq] at firedEq
        nomatch firedEq
    | .var | .unit | .lam | .app | .lamPi | .appPi
    | .pair | .fst | .snd
    | .boolTrue | .boolFalse | .boolElim
    | .natZero | .natSucc | .natElim | .natRec
    | .listElim
    | .optionNone | .optionSome | .optionMatch
    | .eitherInl | .eitherInr | .eitherMatch
    | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
    | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
    | .pathLam | .pathApp
    | .glueIntro | .glueElim | .transp | .hcomp
    | .recordIntro | .recordProj | .refineIntro | .refineElim
    | .codataUnfold | .codataDest
    | .sessionSend | .sessionRecv | .effectPerform
    | .universeCode | .cumulUp
    | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
    | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet | .uaToEquiv
    | .equivApply
    | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
    | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
      rw [show (Term.listElim scrutinee nilBranch consBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .listNil then some ⟨_, nilBranch⟩
               else if scrutineeHead == .listCons then
                 match Term.tryDestructListCons scrutinee with
                 | some ⟨_, _, headTerm, tailTerm, _⟩ =>
                     some ⟨_, Term.app (Term.app consBranch headTerm) tailTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      nomatch firedEq
  | optionMatch scrutinee noneBranch someBranch =>
    match headEq : scrutinee.headCtor with
    | .optionNone =>
      rw [show (Term.optionMatch scrutinee noneBranch someBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .optionNone then some ⟨_, noneBranch⟩
               else if scrutineeHead == .optionSome then
                 match Term.tryDestructOptionSome scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app someBranch valueTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      cases firedEq
      exact Term.headStep?_sound_optionMatchNone scrutinee noneBranch someBranch headEq
    | .optionSome =>
      rw [show (Term.optionMatch scrutinee noneBranch someBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .optionNone then some ⟨_, noneBranch⟩
               else if scrutineeHead == .optionSome then
                 match Term.tryDestructOptionSome scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app someBranch valueTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      match destructEq : Term.tryDestructOptionSome scrutinee with
      | some ⟨_, valueTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
        rw [destructEq] at firedEq
        cases firedEq
        cases rawEq
        have scrutEq : scrutinee = Term.optionSome valueTerm :=
          eq_of_heq scrutineeHEq
        rw [scrutEq]
        exact Step.iotaOptionMatchSome valueTerm noneBranch someBranch
      | none =>
        rw [destructEq] at firedEq
        nomatch firedEq
    | .var | .unit | .lam | .app | .lamPi | .appPi
    | .pair | .fst | .snd
    | .boolTrue | .boolFalse | .boolElim
    | .natZero | .natSucc | .natElim | .natRec
    | .listNil | .listCons | .listElim
    | .optionMatch
    | .eitherInl | .eitherInr | .eitherMatch
    | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
    | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
    | .pathLam | .pathApp
    | .glueIntro | .glueElim | .transp | .hcomp
    | .recordIntro | .recordProj | .refineIntro | .refineElim
    | .codataUnfold | .codataDest
    | .sessionSend | .sessionRecv | .effectPerform
    | .universeCode | .cumulUp
    | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
    | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet | .uaToEquiv
    | .equivApply
    | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
    | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
      rw [show (Term.optionMatch scrutinee noneBranch someBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .optionNone then some ⟨_, noneBranch⟩
               else if scrutineeHead == .optionSome then
                 match Term.tryDestructOptionSome scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app someBranch valueTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      nomatch firedEq
  | eitherMatch scrutinee leftBranch rightBranch =>
    match headEq : scrutinee.headCtor with
    | .eitherInl =>
      rw [show (Term.eitherMatch scrutinee leftBranch rightBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .eitherInl then
                 match Term.tryDestructEitherInl scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app leftBranch valueTerm⟩
                 | none => none
               else if scrutineeHead == .eitherInr then
                 match Term.tryDestructEitherInr scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app rightBranch valueTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      match destructEq : Term.tryDestructEitherInl scrutinee with
      | some ⟨_, valueTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
        rw [destructEq] at firedEq
        cases firedEq
        cases rawEq
        have scrutEq :
            scrutinee = Term.eitherInl (rightType := _) valueTerm :=
          eq_of_heq scrutineeHEq
        rw [scrutEq]
        exact Step.iotaEitherMatchInl valueTerm leftBranch rightBranch
      | none =>
        rw [destructEq] at firedEq
        nomatch firedEq
    | .eitherInr =>
      rw [show (Term.eitherMatch scrutinee leftBranch rightBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .eitherInl then
                 match Term.tryDestructEitherInl scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app leftBranch valueTerm⟩
                 | none => none
               else if scrutineeHead == .eitherInr then
                 match Term.tryDestructEitherInr scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app rightBranch valueTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      match destructEq : Term.tryDestructEitherInr scrutinee with
      | some ⟨_, valueTerm, ⟨rawEq, scrutineeHEq⟩⟩ =>
        rw [destructEq] at firedEq
        cases firedEq
        cases rawEq
        have scrutEq :
            scrutinee = Term.eitherInr (leftType := _) valueTerm :=
          eq_of_heq scrutineeHEq
        rw [scrutEq]
        exact Step.iotaEitherMatchInr valueTerm leftBranch rightBranch
      | none =>
        rw [destructEq] at firedEq
        nomatch firedEq
    | .var | .unit | .lam | .app | .lamPi | .appPi
    | .pair | .fst | .snd
    | .boolTrue | .boolFalse | .boolElim
    | .natZero | .natSucc | .natElim | .natRec
    | .listNil | .listCons | .listElim
    | .optionNone | .optionSome | .optionMatch
    | .eitherMatch
    | .refl | .idJ | .oeqRefl | .oeqJ | .oeqFunext | .idStrictRefl | .idStrictRec | .modIntro | .modElim | .subsume
    | .interval0 | .interval1 | .intervalOpp | .intervalMeet | .intervalJoin
    | .pathLam | .pathApp
    | .glueIntro | .glueElim | .transp | .hcomp
    | .recordIntro | .recordProj | .refineIntro | .refineElim
    | .codataUnfold | .codataDest
    | .sessionSend | .sessionRecv | .effectPerform
    | .universeCode | .cumulUp
    | .equivReflId | .funextRefl | .equivReflIdAtId | .funextReflAtId
    | .equivIntroHet | .equivApp | .uaIntroHet | .funextIntroHet | .uaToEquiv
    | .equivApply
    | .arrowCode | .piTyCode | .sigmaTyCode | .productCode | .sumCode
    | .listCode | .optionCode | .eitherCode | .idCode | .equivCode =>
      rw [show (Term.eitherMatch scrutinee leftBranch rightBranch).headStep?
            = (let scrutineeHead := scrutinee.headCtor
               if scrutineeHead == .eitherInl then
                 match Term.tryDestructEitherInl scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app leftBranch valueTerm⟩
                 | none => none
               else if scrutineeHead == .eitherInr then
                 match Term.tryDestructEitherInr scrutinee with
                 | some ⟨_, valueTerm, _⟩ => some ⟨_, Term.app rightBranch valueTerm⟩
                 | none => none
               else none) from rfl, headEq] at firedEq
      nomatch firedEq

end LeanFX2

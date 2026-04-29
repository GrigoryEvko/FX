import LeanFX.Syntax.Subst

namespace LeanFX.Syntax

/-! ## Tarski codes

`Code level scope` is the axiom-free substrate for a small internal
universe.  It mirrors `Ty level scope` constructor-for-constructor but
stays syntactic: interpretation into `Ty` lands in the next task. -/

/-- Tarski code syntax for the small FX type universe. -/
inductive Code : Nat → Nat → Type
  /-- Code for the unit type. -/
  | codeUnit : {level scope : Nat} → Code level scope
  /-- Code for the boolean type. -/
  | codeBool : {level scope : Nat} → Code level scope
  /-- Code for the natural-number type. -/
  | codeNat : {level scope : Nat} → Code level scope
  /-- Code for a non-dependent arrow type. -/
  | codeArrow : {level scope : Nat} →
      (domain : Code level scope) →
      (codomain : Code level scope) →
      Code level scope
  /-- Code for a dependent function type. -/
  | codePiTy : {level scope : Nat} →
      (domain : Code level scope) →
      (codomain : Code level (scope + 1)) →
      Code level scope
  /-- Code for a type variable. -/
  | codeTyVar : {level scope : Nat} → (position : Fin scope) → Code level scope
  /-- Code for a dependent pair type. -/
  | codeSigma : {level scope : Nat} →
      (firstType : Code level scope) →
      (secondType : Code level (scope + 1)) →
      Code level scope
  /-- Code for a universe type. -/
  | codeUniverse : {level scope : Nat} →
      (universeLevel : Nat) →
      (levelFits : universeLevel + 1 ≤ level) →
      Code level scope
  /-- Code for lists. -/
  | codeList : {level scope : Nat} →
      (elementType : Code level scope) →
      Code level scope
  /-- Code for optional values. -/
  | codeOption : {level scope : Nat} →
      (elementType : Code level scope) →
      Code level scope
  /-- Code for tagged sums. -/
  | codeEither : {level scope : Nat} →
      (leftType : Code level scope) →
      (rightType : Code level scope) →
      Code level scope
  /-- Code for identity types with open raw endpoints. -/
  | codeId : {level scope : Nat} →
      (carrier : Code level scope) →
      (leftEndpoint : RawTerm scope) →
      (rightEndpoint : RawTerm scope) →
      Code level scope

deriving instance DecidableEq for Code

namespace SmokeTestCode

/-- Closed code for unit. -/
example : Code 0 0 := Code.codeUnit

/-- Closed code for bool. -/
example : Code 0 0 := Code.codeBool

/-- Closed code for nat. -/
example : Code 0 0 := Code.codeNat

/-- Closed code for a simple arrow. -/
example : Code 0 0 :=
  Code.codeArrow Code.codeUnit Code.codeBool

/-- Code for a dependent function whose codomain references its binder. -/
example : Code 0 0 :=
  Code.codePiTy Code.codeUnit
    (Code.codeTyVar ⟨0, Nat.zero_lt_succ 0⟩)

/-- Code for a type variable at scope one. -/
example : Code 0 1 :=
  Code.codeTyVar ⟨0, Nat.zero_lt_succ 0⟩

/-- Code for a dependent pair whose second component references its binder. -/
example : Code 0 0 :=
  Code.codeSigma Code.codeUnit
    (Code.codeTyVar ⟨0, Nat.zero_lt_succ 0⟩)

/-- Code for `Type 0 : Type 1`. -/
example : Code 1 0 :=
  Code.codeUniverse 0 (Nat.le_refl 1)

/-- Code for a list. -/
example : Code 0 0 :=
  Code.codeList Code.codeNat

/-- Code for an option. -/
example : Code 0 0 :=
  Code.codeOption Code.codeBool

/-- Code for a tagged sum. -/
example : Code 0 0 :=
  Code.codeEither Code.codeBool Code.codeNat

/-- Code for a closed identity type. -/
example : Code 0 0 :=
  Code.codeId Code.codeBool RawTerm.boolTrue RawTerm.boolTrue

/-- Code for an open identity type under one raw binder. -/
example : Code 0 1 :=
  Code.codeId Code.codeUnit
    (RawTerm.var ⟨0, Nat.zero_lt_succ 0⟩)
    (RawTerm.var ⟨0, Nat.zero_lt_succ 0⟩)

end SmokeTestCode

/-! ## Code renaming -/

/-- Apply a renaming to a Tarski code. -/
def Code.rename {level source target : Nat} :
    Code level source → Renaming source target → Code level target
  | .codeUnit, _ => .codeUnit
  | .codeBool, _ => .codeBool
  | .codeNat, _ => .codeNat
  | .codeArrow domain codomain, rawRenaming =>
      .codeArrow (domain.rename rawRenaming) (codomain.rename rawRenaming)
  | .codePiTy domain codomain, rawRenaming =>
      .codePiTy (domain.rename rawRenaming) (codomain.rename rawRenaming.lift)
  | .codeTyVar position, rawRenaming =>
      .codeTyVar (rawRenaming position)
  | .codeSigma firstType secondType, rawRenaming =>
      .codeSigma (firstType.rename rawRenaming) (secondType.rename rawRenaming.lift)
  | .codeUniverse universeLevel levelEq, _ =>
      .codeUniverse universeLevel levelEq
  | .codeList elementType, rawRenaming =>
      .codeList (elementType.rename rawRenaming)
  | .codeOption elementType, rawRenaming =>
      .codeOption (elementType.rename rawRenaming)
  | .codeEither leftType rightType, rawRenaming =>
      .codeEither (leftType.rename rawRenaming) (rightType.rename rawRenaming)
  | .codeId carrier leftEndpoint rightEndpoint, rawRenaming =>
      .codeId (carrier.rename rawRenaming)
        (leftEndpoint.rename rawRenaming)
        (rightEndpoint.rename rawRenaming)

/-- Code weakening is renaming by successor. -/
@[reducible]
def Code.weaken {level scope : Nat} (code : Code level scope) : Code level (scope + 1) :=
  code.rename Renaming.weaken

/-- Pointwise-equivalent renamings produce equal renamed codes. -/
theorem Code.rename_congr {level source target : Nat}
    {firstRenaming secondRenaming : Renaming source target}
    (renamingsAreEquivalent : Renaming.equiv firstRenaming secondRenaming) :
    ∀ code : Code level source,
      code.rename firstRenaming = code.rename secondRenaming
  | .codeUnit => rfl
  | .codeBool => rfl
  | .codeNat => rfl
  | .codeArrow domain codomain => by
      exact congrArgTwo (function := Code.codeArrow)
        (Code.rename_congr renamingsAreEquivalent domain)
        (Code.rename_congr renamingsAreEquivalent codomain)
  | .codePiTy domain codomain => by
      exact congrArgTwo (function := Code.codePiTy)
        (Code.rename_congr renamingsAreEquivalent domain)
        (Code.rename_congr (Renaming.lift_equiv renamingsAreEquivalent) codomain)
  | .codeTyVar position =>
      congrArg Code.codeTyVar (renamingsAreEquivalent position)
  | .codeSigma firstType secondType => by
      exact congrArgTwo (function := Code.codeSigma)
        (Code.rename_congr renamingsAreEquivalent firstType)
        (Code.rename_congr (Renaming.lift_equiv renamingsAreEquivalent) secondType)
  | .codeUniverse _ _ => rfl
  | .codeList elementType => by
      exact congrArg Code.codeList (Code.rename_congr renamingsAreEquivalent elementType)
  | .codeOption elementType => by
      exact congrArg Code.codeOption (Code.rename_congr renamingsAreEquivalent elementType)
  | .codeEither leftType rightType => by
      exact congrArgTwo (function := Code.codeEither)
        (Code.rename_congr renamingsAreEquivalent leftType)
        (Code.rename_congr renamingsAreEquivalent rightType)
  | .codeId carrier leftEndpoint rightEndpoint => by
      exact congrArgThree (function := Code.codeId)
        (Code.rename_congr renamingsAreEquivalent carrier)
        (RawTerm.rename_congr renamingsAreEquivalent leftEndpoint)
        (RawTerm.rename_congr renamingsAreEquivalent rightEndpoint)

/-- Code renaming composition law. -/
theorem Code.rename_compose {level source middle target : Nat} :
    ∀ (code : Code level source)
      (firstRenaming : Renaming source middle)
      (secondRenaming : Renaming middle target),
      (code.rename firstRenaming).rename secondRenaming =
        code.rename (Renaming.compose firstRenaming secondRenaming)
  | .codeUnit, _, _ => rfl
  | .codeBool, _, _ => rfl
  | .codeNat, _, _ => rfl
  | .codeArrow domain codomain, firstRenaming, secondRenaming => by
      exact congrArgTwo (function := Code.codeArrow)
        (Code.rename_compose domain firstRenaming secondRenaming)
        (Code.rename_compose codomain firstRenaming secondRenaming)
  | .codePiTy domain codomain, firstRenaming, secondRenaming => by
      have codomainComposition :=
        Code.rename_compose codomain firstRenaming.lift secondRenaming.lift
      have liftComposition :=
        Code.rename_congr (Renaming.lift_compose_equiv firstRenaming secondRenaming) codomain
      exact congrArgTwo (function := Code.codePiTy)
        (Code.rename_compose domain firstRenaming secondRenaming)
        (codomainComposition.trans liftComposition)
  | .codeTyVar _, _, _ => rfl
  | .codeSigma firstType secondType, firstRenaming, secondRenaming => by
      have secondComposition :=
        Code.rename_compose secondType firstRenaming.lift secondRenaming.lift
      have liftComposition :=
        Code.rename_congr (Renaming.lift_compose_equiv firstRenaming secondRenaming) secondType
      exact congrArgTwo (function := Code.codeSigma)
        (Code.rename_compose firstType firstRenaming secondRenaming)
        (secondComposition.trans liftComposition)
  | .codeUniverse _ _, _, _ => rfl
  | .codeList elementType, firstRenaming, secondRenaming => by
      exact congrArg Code.codeList
        (Code.rename_compose elementType firstRenaming secondRenaming)
  | .codeOption elementType, firstRenaming, secondRenaming => by
      exact congrArg Code.codeOption
        (Code.rename_compose elementType firstRenaming secondRenaming)
  | .codeEither leftType rightType, firstRenaming, secondRenaming => by
      exact congrArgTwo (function := Code.codeEither)
        (Code.rename_compose leftType firstRenaming secondRenaming)
        (Code.rename_compose rightType firstRenaming secondRenaming)
  | .codeId carrier leftEndpoint rightEndpoint, firstRenaming, secondRenaming => by
      exact congrArgThree (function := Code.codeId)
        (Code.rename_compose carrier firstRenaming secondRenaming)
        (RawTerm.rename_compose leftEndpoint firstRenaming secondRenaming)
        (RawTerm.rename_compose rightEndpoint firstRenaming secondRenaming)

/-- Renaming by identity is neutral on codes. -/
theorem Code.rename_identity {level scope : Nat} :
    ∀ code : Code level scope, code.rename Renaming.identity = code
  | .codeUnit => rfl
  | .codeBool => rfl
  | .codeNat => rfl
  | .codeArrow domain codomain => by
      exact congrArgTwo (function := Code.codeArrow)
        (Code.rename_identity domain)
        (Code.rename_identity codomain)
  | .codePiTy domain codomain => by
      have codomainRenaming :=
        Code.rename_congr Renaming.lift_identity_equiv codomain
      exact congrArgTwo (function := Code.codePiTy)
        (Code.rename_identity domain)
        (codomainRenaming.trans (Code.rename_identity codomain))
  | .codeTyVar _ => rfl
  | .codeSigma firstType secondType => by
      have secondRenaming :=
        Code.rename_congr Renaming.lift_identity_equiv secondType
      exact congrArgTwo (function := Code.codeSigma)
        (Code.rename_identity firstType)
        (secondRenaming.trans (Code.rename_identity secondType))
  | .codeUniverse _ _ => rfl
  | .codeList elementType => by
      exact congrArg Code.codeList (Code.rename_identity elementType)
  | .codeOption elementType => by
      exact congrArg Code.codeOption (Code.rename_identity elementType)
  | .codeEither leftType rightType => by
      exact congrArgTwo (function := Code.codeEither)
        (Code.rename_identity leftType)
        (Code.rename_identity rightType)
  | .codeId carrier leftEndpoint rightEndpoint => by
      exact congrArgThree (function := Code.codeId)
        (Code.rename_identity carrier)
        (RawTerm.rename_identity (level := level) leftEndpoint)
        (RawTerm.rename_identity (level := level) rightEndpoint)

/-- Code weakening commutes with renaming. -/
theorem Code.rename_weaken_commute {level source target : Nat}
    (code : Code level source) (rawRenaming : Renaming source target) :
    (code.weaken).rename rawRenaming.lift = (code.rename rawRenaming).weaken := by
  show (code.rename Renaming.weaken).rename rawRenaming.lift =
    (code.rename rawRenaming).rename Renaming.weaken
  have renamingsCommute :
      Renaming.equiv
        (Renaming.compose Renaming.weaken rawRenaming.lift)
        (Renaming.compose rawRenaming Renaming.weaken) :=
    fun _ => rfl
  exact (Code.rename_compose code Renaming.weaken rawRenaming.lift).trans
    ((Code.rename_congr renamingsCommute code).trans
      (Code.rename_compose code rawRenaming Renaming.weaken).symm)

/-! ## Code substitution -/

/-- A code substitution maps type-code variables to codes and raw variables
to raw terms. -/
structure CodeSubst (level source target : Nat) where
  forCode : Fin source → Code level target
  forRaw : RawTermSubst source target

/-- Identity code substitution. -/
def CodeSubst.identity {level scope : Nat} : CodeSubst level scope scope where
  forCode := Code.codeTyVar
  forRaw := RawTermSubst.identity

/-- Lift a code substitution under one binder. -/
def CodeSubst.lift {level source target : Nat}
    (codeSubstitution : CodeSubst level source target) :
    CodeSubst level (source + 1) (target + 1) where
  forCode
    | ⟨0, _⟩ => Code.codeTyVar ⟨0, Nat.succ_pos target⟩
    | ⟨position + 1, isWithinSource⟩ =>
        (codeSubstitution.forCode
          ⟨position, Nat.lt_of_succ_lt_succ isWithinSource⟩).weaken
  forRaw := codeSubstitution.forRaw.lift

/-- Pointwise equivalence for code substitutions. -/
def CodeSubst.equiv {level source target : Nat}
    (firstSubstitution secondSubstitution : CodeSubst level source target) : Prop :=
  (∀ position, firstSubstitution.forCode position = secondSubstitution.forCode position) ∧
    RawTermSubst.equiv firstSubstitution.forRaw secondSubstitution.forRaw

/-- Project the code component of code-substitution equivalence. -/
theorem CodeSubst.equiv_forCode {level source target : Nat}
    {firstSubstitution secondSubstitution : CodeSubst level source target}
    (substitutionsAreEquivalent : CodeSubst.equiv firstSubstitution secondSubstitution) :
    ∀ position, firstSubstitution.forCode position = secondSubstitution.forCode position :=
  substitutionsAreEquivalent.left

/-- Project the raw component of code-substitution equivalence. -/
theorem CodeSubst.equiv_forRaw {level source target : Nat}
    {firstSubstitution secondSubstitution : CodeSubst level source target}
    (substitutionsAreEquivalent : CodeSubst.equiv firstSubstitution secondSubstitution) :
    RawTermSubst.equiv firstSubstitution.forRaw secondSubstitution.forRaw :=
  substitutionsAreEquivalent.right

/-- Build a code-substitution equivalence from code and raw components. -/
theorem CodeSubst.equiv_intro {level source target : Nat}
    {firstSubstitution secondSubstitution : CodeSubst level source target}
    (codesAreEquivalent :
      ∀ position, firstSubstitution.forCode position = secondSubstitution.forCode position)
    (rawTermsAreEquivalent :
      RawTermSubst.equiv firstSubstitution.forRaw secondSubstitution.forRaw) :
    CodeSubst.equiv firstSubstitution secondSubstitution :=
  And.intro codesAreEquivalent rawTermsAreEquivalent

/-- Lifting preserves code-substitution equivalence. -/
theorem CodeSubst.lift_equiv {level source target : Nat}
    {firstSubstitution secondSubstitution : CodeSubst level source target}
    (substitutionsAreEquivalent :
      CodeSubst.equiv firstSubstitution secondSubstitution) :
    CodeSubst.equiv firstSubstitution.lift secondSubstitution.lift :=
  CodeSubst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩ => rfl
      | ⟨position + 1, isWithinSource⟩ =>
          congrArg Code.weaken
            (CodeSubst.equiv_forCode substitutionsAreEquivalent
              ⟨position, Nat.lt_of_succ_lt_succ isWithinSource⟩))
    (RawTermSubst.lift_equiv
      (CodeSubst.equiv_forRaw substitutionsAreEquivalent))

/-- Apply a code substitution to a code. -/
def Code.subst {level source target : Nat} :
    Code level source → CodeSubst level source target → Code level target
  | .codeUnit, _ => .codeUnit
  | .codeBool, _ => .codeBool
  | .codeNat, _ => .codeNat
  | .codeArrow domain codomain, codeSubstitution =>
      .codeArrow (domain.subst codeSubstitution) (codomain.subst codeSubstitution)
  | .codePiTy domain codomain, codeSubstitution =>
      .codePiTy (domain.subst codeSubstitution) (codomain.subst codeSubstitution.lift)
  | .codeTyVar position, codeSubstitution =>
      codeSubstitution.forCode position
  | .codeSigma firstType secondType, codeSubstitution =>
      .codeSigma (firstType.subst codeSubstitution) (secondType.subst codeSubstitution.lift)
  | .codeUniverse universeLevel levelEq, _ =>
      .codeUniverse universeLevel levelEq
  | .codeList elementType, codeSubstitution =>
      .codeList (elementType.subst codeSubstitution)
  | .codeOption elementType, codeSubstitution =>
      .codeOption (elementType.subst codeSubstitution)
  | .codeEither leftType rightType, codeSubstitution =>
      .codeEither (leftType.subst codeSubstitution) (rightType.subst codeSubstitution)
  | .codeId carrier leftEndpoint rightEndpoint, codeSubstitution =>
      .codeId (carrier.subst codeSubstitution)
        (leftEndpoint.subst codeSubstitution.forRaw)
        (rightEndpoint.subst codeSubstitution.forRaw)

/-- Equivalent code substitutions produce equal substituted codes. -/
theorem Code.subst_congr {level source target : Nat}
    {firstSubstitution secondSubstitution : CodeSubst level source target}
    (substitutionsAreEquivalent :
      CodeSubst.equiv firstSubstitution secondSubstitution) :
    ∀ code : Code level source,
      code.subst firstSubstitution = code.subst secondSubstitution
  | .codeUnit => rfl
  | .codeBool => rfl
  | .codeNat => rfl
  | .codeArrow domain codomain => by
      exact congrArgTwo (function := Code.codeArrow)
        (Code.subst_congr substitutionsAreEquivalent domain)
        (Code.subst_congr substitutionsAreEquivalent codomain)
  | .codePiTy domain codomain => by
      exact congrArgTwo (function := Code.codePiTy)
        (Code.subst_congr substitutionsAreEquivalent domain)
        (Code.subst_congr (CodeSubst.lift_equiv substitutionsAreEquivalent) codomain)
  | .codeTyVar position =>
      CodeSubst.equiv_forCode substitutionsAreEquivalent position
  | .codeSigma firstType secondType => by
      exact congrArgTwo (function := Code.codeSigma)
        (Code.subst_congr substitutionsAreEquivalent firstType)
        (Code.subst_congr (CodeSubst.lift_equiv substitutionsAreEquivalent) secondType)
  | .codeUniverse _ _ => rfl
  | .codeList elementType => by
      exact congrArg Code.codeList (Code.subst_congr substitutionsAreEquivalent elementType)
  | .codeOption elementType => by
      exact congrArg Code.codeOption (Code.subst_congr substitutionsAreEquivalent elementType)
  | .codeEither leftType rightType => by
      exact congrArgTwo (function := Code.codeEither)
        (Code.subst_congr substitutionsAreEquivalent leftType)
        (Code.subst_congr substitutionsAreEquivalent rightType)
  | .codeId carrier leftEndpoint rightEndpoint => by
      exact congrArgThree (function := Code.codeId)
        (Code.subst_congr substitutionsAreEquivalent carrier)
        (RawTerm.subst_congr
          (CodeSubst.equiv_forRaw substitutionsAreEquivalent) leftEndpoint)
        (RawTerm.subst_congr
          (CodeSubst.equiv_forRaw substitutionsAreEquivalent) rightEndpoint)

/-- Lifting identity code substitution is pointwise identity. -/
theorem CodeSubst.lift_identity_equiv {level scope : Nat} :
    CodeSubst.equiv
      (CodeSubst.lift (CodeSubst.identity (level := level) (scope := scope)))
      (CodeSubst.identity (level := level) (scope := scope + 1)) :=
  CodeSubst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩ => rfl
      | ⟨_ + 1, _⟩ => rfl)
    RawTermSubst.lift_identity_equiv

/-- Substitution by identity is neutral on codes. -/
theorem Code.subst_id {level scope : Nat} :
    ∀ code : Code level scope,
      code.subst CodeSubst.identity = code
  | .codeUnit => rfl
  | .codeBool => rfl
  | .codeNat => rfl
  | .codeArrow domain codomain => by
      exact congrArgTwo (function := Code.codeArrow)
        (Code.subst_id domain)
        (Code.subst_id codomain)
  | .codePiTy domain codomain => by
      have codomainCongruence :=
        Code.subst_congr CodeSubst.lift_identity_equiv codomain
      exact congrArgTwo (function := Code.codePiTy)
        (Code.subst_id domain)
        (codomainCongruence.trans (Code.subst_id codomain))
  | .codeTyVar _ => rfl
  | .codeSigma firstType secondType => by
      have secondCongruence :=
        Code.subst_congr CodeSubst.lift_identity_equiv secondType
      exact congrArgTwo (function := Code.codeSigma)
        (Code.subst_id firstType)
        (secondCongruence.trans (Code.subst_id secondType))
  | .codeUniverse _ _ => rfl
  | .codeList elementType => by
      exact congrArg Code.codeList (Code.subst_id elementType)
  | .codeOption elementType => by
      exact congrArg Code.codeOption (Code.subst_id elementType)
  | .codeEither leftType rightType => by
      exact congrArgTwo (function := Code.codeEither)
        (Code.subst_id leftType)
        (Code.subst_id rightType)
  | .codeId carrier leftEndpoint rightEndpoint => by
      exact congrArgThree (function := Code.codeId)
        (Code.subst_id carrier)
        (RawTerm.subst_id leftEndpoint)
        (RawTerm.subst_id rightEndpoint)

/-- Rename every code and raw substituent after substitution. -/
def CodeSubst.renameAfter {level source middle target : Nat}
    (codeSubstitution : CodeSubst level source middle)
    (rawRenaming : Renaming middle target) :
    CodeSubst level source target where
  forCode := fun position => (codeSubstitution.forCode position).rename rawRenaming
  forRaw := RawTermSubst.beforeRenaming codeSubstitution.forRaw rawRenaming

/-- Precompose a code substitution with a renaming. -/
def CodeSubst.precompose {level source middle target : Nat}
    (rawRenaming : Renaming source middle)
    (codeSubstitution : CodeSubst level middle target) :
    CodeSubst level source target where
  forCode := fun position => codeSubstitution.forCode (rawRenaming position)
  forRaw := RawTermSubst.afterRenaming rawRenaming codeSubstitution.forRaw

/-- Lifting commutes with `renameAfter`. -/
theorem CodeSubst.lift_renameAfter_equiv {level source middle target : Nat}
    (codeSubstitution : CodeSubst level source middle)
    (rawRenaming : Renaming middle target) :
    CodeSubst.equiv
      (CodeSubst.lift (CodeSubst.renameAfter codeSubstitution rawRenaming))
      (CodeSubst.renameAfter codeSubstitution.lift rawRenaming.lift) :=
  CodeSubst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩ => rfl
      | ⟨position + 1, isWithinSource⟩ =>
          (Code.rename_weaken_commute
            (codeSubstitution.forCode
              ⟨position, Nat.lt_of_succ_lt_succ isWithinSource⟩)
            rawRenaming).symm)
    (RawTermSubst.lift_beforeRenaming_equiv codeSubstitution.forRaw rawRenaming)

/-- Lifting commutes with precomposition. -/
theorem CodeSubst.lift_precompose_equiv {level source middle target : Nat}
    (rawRenaming : Renaming source middle)
    (codeSubstitution : CodeSubst level middle target) :
    CodeSubst.equiv
      (CodeSubst.lift (CodeSubst.precompose rawRenaming codeSubstitution))
      (CodeSubst.precompose rawRenaming.lift codeSubstitution.lift) :=
  CodeSubst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩ => rfl
      | ⟨_ + 1, _⟩ => rfl)
    (RawTermSubst.lift_afterRenaming_equiv rawRenaming codeSubstitution.forRaw)

/-- Substitution then renaming commutes with `renameAfter`. -/
theorem Code.subst_rename_commute {level source middle target : Nat} :
    ∀ (code : Code level source)
      (codeSubstitution : CodeSubst level source middle)
      (rawRenaming : Renaming middle target),
      (code.subst codeSubstitution).rename rawRenaming =
        code.subst (CodeSubst.renameAfter codeSubstitution rawRenaming)
  | .codeUnit, _, _ => rfl
  | .codeBool, _, _ => rfl
  | .codeNat, _, _ => rfl
  | .codeArrow domain codomain, codeSubstitution, rawRenaming => by
      exact congrArgTwo (function := Code.codeArrow)
        (Code.subst_rename_commute domain codeSubstitution rawRenaming)
        (Code.subst_rename_commute codomain codeSubstitution rawRenaming)
  | .codePiTy domain codomain, codeSubstitution, rawRenaming => by
      have codomainCommute :=
        Code.subst_rename_commute codomain codeSubstitution.lift rawRenaming.lift
      have liftCommute :=
        Code.subst_congr
          (CodeSubst.lift_renameAfter_equiv codeSubstitution rawRenaming)
          codomain
      exact congrArgTwo (function := Code.codePiTy)
        (Code.subst_rename_commute domain codeSubstitution rawRenaming)
        (codomainCommute.trans liftCommute.symm)
  | .codeTyVar _, _, _ => rfl
  | .codeSigma firstType secondType, codeSubstitution, rawRenaming => by
      have secondCommute :=
        Code.subst_rename_commute secondType codeSubstitution.lift rawRenaming.lift
      have liftCommute :=
        Code.subst_congr
          (CodeSubst.lift_renameAfter_equiv codeSubstitution rawRenaming)
          secondType
      exact congrArgTwo (function := Code.codeSigma)
        (Code.subst_rename_commute firstType codeSubstitution rawRenaming)
        (secondCommute.trans liftCommute.symm)
  | .codeUniverse _ _, _, _ => rfl
  | .codeList elementType, codeSubstitution, rawRenaming => by
      exact congrArg Code.codeList
        (Code.subst_rename_commute elementType codeSubstitution rawRenaming)
  | .codeOption elementType, codeSubstitution, rawRenaming => by
      exact congrArg Code.codeOption
        (Code.subst_rename_commute elementType codeSubstitution rawRenaming)
  | .codeEither leftType rightType, codeSubstitution, rawRenaming => by
      exact congrArgTwo (function := Code.codeEither)
        (Code.subst_rename_commute leftType codeSubstitution rawRenaming)
        (Code.subst_rename_commute rightType codeSubstitution rawRenaming)
  | .codeId carrier leftEndpoint rightEndpoint, codeSubstitution, rawRenaming => by
      exact congrArgThree (function := Code.codeId)
        (Code.subst_rename_commute carrier codeSubstitution rawRenaming)
        (RawTerm.rename_subst_commute leftEndpoint codeSubstitution.forRaw rawRenaming)
        (RawTerm.rename_subst_commute rightEndpoint codeSubstitution.forRaw rawRenaming)

/-- Renaming then substitution commutes with precomposition. -/
theorem Code.rename_subst_commute {level source middle target : Nat} :
    ∀ (code : Code level source)
      (rawRenaming : Renaming source middle)
      (codeSubstitution : CodeSubst level middle target),
      (code.rename rawRenaming).subst codeSubstitution =
        code.subst (CodeSubst.precompose rawRenaming codeSubstitution)
  | .codeUnit, _, _ => rfl
  | .codeBool, _, _ => rfl
  | .codeNat, _, _ => rfl
  | .codeArrow domain codomain, rawRenaming, codeSubstitution => by
      exact congrArgTwo (function := Code.codeArrow)
        (Code.rename_subst_commute domain rawRenaming codeSubstitution)
        (Code.rename_subst_commute codomain rawRenaming codeSubstitution)
  | .codePiTy domain codomain, rawRenaming, codeSubstitution => by
      have codomainCommute :=
        Code.rename_subst_commute codomain rawRenaming.lift codeSubstitution.lift
      have liftCommute :=
        Code.subst_congr
          (CodeSubst.lift_precompose_equiv rawRenaming codeSubstitution)
          codomain
      exact congrArgTwo (function := Code.codePiTy)
        (Code.rename_subst_commute domain rawRenaming codeSubstitution)
        (codomainCommute.trans liftCommute.symm)
  | .codeTyVar _, _, _ => rfl
  | .codeSigma firstType secondType, rawRenaming, codeSubstitution => by
      have secondCommute :=
        Code.rename_subst_commute secondType rawRenaming.lift codeSubstitution.lift
      have liftCommute :=
        Code.subst_congr
          (CodeSubst.lift_precompose_equiv rawRenaming codeSubstitution)
          secondType
      exact congrArgTwo (function := Code.codeSigma)
        (Code.rename_subst_commute firstType rawRenaming codeSubstitution)
        (secondCommute.trans liftCommute.symm)
  | .codeUniverse _ _, _, _ => rfl
  | .codeList elementType, rawRenaming, codeSubstitution => by
      exact congrArg Code.codeList
        (Code.rename_subst_commute elementType rawRenaming codeSubstitution)
  | .codeOption elementType, rawRenaming, codeSubstitution => by
      exact congrArg Code.codeOption
        (Code.rename_subst_commute elementType rawRenaming codeSubstitution)
  | .codeEither leftType rightType, rawRenaming, codeSubstitution => by
      exact congrArgTwo (function := Code.codeEither)
        (Code.rename_subst_commute leftType rawRenaming codeSubstitution)
        (Code.rename_subst_commute rightType rawRenaming codeSubstitution)
  | .codeId carrier leftEndpoint rightEndpoint, rawRenaming, codeSubstitution => by
      exact congrArgThree (function := Code.codeId)
        (Code.rename_subst_commute carrier rawRenaming codeSubstitution)
        (RawTerm.subst_rename_commute leftEndpoint rawRenaming codeSubstitution.forRaw)
        (RawTerm.subst_rename_commute rightEndpoint rawRenaming codeSubstitution.forRaw)

/-- Precomposing weakening with a lifted code substitution equals renaming
substituents by weakening. -/
theorem CodeSubst.precompose_weaken_lift_equiv_renameAfter_weaken
    {level source target : Nat}
    (codeSubstitution : CodeSubst level source target) :
    CodeSubst.equiv
      (CodeSubst.precompose Renaming.weaken codeSubstitution.lift)
      (CodeSubst.renameAfter codeSubstitution Renaming.weaken) :=
  CodeSubst.equiv_intro
    (fun _ => rfl)
    (RawTermSubst.equiv_refl _)

/-- Code substitution commutes with weakening. -/
theorem Code.subst_weaken_commute {level source target : Nat}
    (code : Code level source)
    (codeSubstitution : CodeSubst level source target) :
    (code.weaken).subst codeSubstitution.lift =
      (code.subst codeSubstitution).weaken := by
  show (code.rename Renaming.weaken).subst codeSubstitution.lift =
    (code.subst codeSubstitution).rename Renaming.weaken
  exact (Code.rename_subst_commute code Renaming.weaken codeSubstitution.lift).trans
    ((Code.subst_congr
      (CodeSubst.precompose_weaken_lift_equiv_renameAfter_weaken codeSubstitution)
      code).trans
      (Code.subst_rename_commute code codeSubstitution Renaming.weaken).symm)

/-- Compose code substitutions. -/
def CodeSubst.compose {level source middle target : Nat}
    (firstSubstitution : CodeSubst level source middle)
    (secondSubstitution : CodeSubst level middle target) :
    CodeSubst level source target where
  forCode := fun position => (firstSubstitution.forCode position).subst secondSubstitution
  forRaw := RawTermSubst.compose firstSubstitution.forRaw secondSubstitution.forRaw

/-- Lifting commutes with code-substitution composition. -/
theorem CodeSubst.lift_compose_equiv {level source middle target : Nat}
    (firstSubstitution : CodeSubst level source middle)
    (secondSubstitution : CodeSubst level middle target) :
    CodeSubst.equiv
      (CodeSubst.compose firstSubstitution.lift secondSubstitution.lift)
      (CodeSubst.lift (CodeSubst.compose firstSubstitution secondSubstitution)) :=
  CodeSubst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩ => rfl
      | ⟨position + 1, isWithinSource⟩ =>
          Code.subst_weaken_commute
            (firstSubstitution.forCode
              ⟨position, Nat.lt_of_succ_lt_succ isWithinSource⟩)
            secondSubstitution)
    fun position =>
      (RawTermSubst.lift_compose_equiv
        firstSubstitution.forRaw secondSubstitution.forRaw position).symm

/-- Code substitution composition law. -/
theorem Code.subst_compose {level source middle target : Nat} :
    ∀ (code : Code level source)
      (firstSubstitution : CodeSubst level source middle)
      (secondSubstitution : CodeSubst level middle target),
      (code.subst firstSubstitution).subst secondSubstitution =
        code.subst (CodeSubst.compose firstSubstitution secondSubstitution)
  | .codeUnit, _, _ => rfl
  | .codeBool, _, _ => rfl
  | .codeNat, _, _ => rfl
  | .codeArrow domain codomain, firstSubstitution, secondSubstitution => by
      exact congrArgTwo (function := Code.codeArrow)
        (Code.subst_compose domain firstSubstitution secondSubstitution)
        (Code.subst_compose codomain firstSubstitution secondSubstitution)
  | .codePiTy domain codomain, firstSubstitution, secondSubstitution => by
      have codomainComposition :=
        Code.subst_compose codomain firstSubstitution.lift secondSubstitution.lift
      have liftComposition :=
        Code.subst_congr
          (CodeSubst.lift_compose_equiv firstSubstitution secondSubstitution)
          codomain
      exact congrArgTwo (function := Code.codePiTy)
        (Code.subst_compose domain firstSubstitution secondSubstitution)
        (codomainComposition.trans liftComposition)
  | .codeTyVar _, _, _ => rfl
  | .codeSigma firstType secondType, firstSubstitution, secondSubstitution => by
      have secondComposition :=
        Code.subst_compose secondType firstSubstitution.lift secondSubstitution.lift
      have liftComposition :=
        Code.subst_congr
          (CodeSubst.lift_compose_equiv firstSubstitution secondSubstitution)
          secondType
      exact congrArgTwo (function := Code.codeSigma)
        (Code.subst_compose firstType firstSubstitution secondSubstitution)
        (secondComposition.trans liftComposition)
  | .codeUniverse _ _, _, _ => rfl
  | .codeList elementType, firstSubstitution, secondSubstitution => by
      exact congrArg Code.codeList
        (Code.subst_compose elementType firstSubstitution secondSubstitution)
  | .codeOption elementType, firstSubstitution, secondSubstitution => by
      exact congrArg Code.codeOption
        (Code.subst_compose elementType firstSubstitution secondSubstitution)
  | .codeEither leftType rightType, firstSubstitution, secondSubstitution => by
      exact congrArgTwo (function := Code.codeEither)
        (Code.subst_compose leftType firstSubstitution secondSubstitution)
        (Code.subst_compose rightType firstSubstitution secondSubstitution)
  | .codeId carrier leftEndpoint rightEndpoint, firstSubstitution, secondSubstitution => by
      exact congrArgThree (function := Code.codeId)
        (Code.subst_compose carrier firstSubstitution secondSubstitution)
        (RawTerm.subst_compose
          leftEndpoint firstSubstitution.forRaw secondSubstitution.forRaw)
        (RawTerm.subst_compose
          rightEndpoint firstSubstitution.forRaw secondSubstitution.forRaw)

/-! ## Decoding codes into types -/

/-- Interpret a Tarski code as an intrinsic type. -/
def Code.decode {level scope : Nat} : Code level scope → Ty level scope
  | .codeUnit => Ty.unit
  | .codeBool => Ty.bool
  | .codeNat => Ty.nat
  | .codeArrow domain codomain =>
      Ty.arrow domain.decode codomain.decode
  | .codePiTy domain codomain =>
      Ty.piTy domain.decode codomain.decode
  | .codeTyVar position =>
      Ty.tyVar position
  | .codeSigma firstType secondType =>
      Ty.sigmaTy firstType.decode secondType.decode
  | .codeUniverse universeLevel levelEq =>
      Ty.universe universeLevel levelEq
  | .codeList elementType =>
      Ty.list elementType.decode
  | .codeOption elementType =>
      Ty.option elementType.decode
  | .codeEither leftType rightType =>
      Ty.either leftType.decode rightType.decode
  | .codeId carrier leftEndpoint rightEndpoint =>
      Ty.id carrier.decode leftEndpoint rightEndpoint

/-- Decoding commutes with code renaming. -/
theorem Code.decode_rename {level source target : Nat} :
    ∀ (code : Code level source) (rawRenaming : Renaming source target),
      (code.rename rawRenaming).decode = code.decode.rename rawRenaming
  | .codeUnit, _ => rfl
  | .codeBool, _ => rfl
  | .codeNat, _ => rfl
  | .codeArrow domain codomain, rawRenaming => by
      exact congrArgTwo (function := Ty.arrow)
        (Code.decode_rename domain rawRenaming)
        (Code.decode_rename codomain rawRenaming)
  | .codePiTy domain codomain, rawRenaming => by
      exact congrArgTwo (function := Ty.piTy)
        (Code.decode_rename domain rawRenaming)
        (Code.decode_rename codomain rawRenaming.lift)
  | .codeTyVar _, _ => rfl
  | .codeSigma firstType secondType, rawRenaming => by
      exact congrArgTwo (function := Ty.sigmaTy)
        (Code.decode_rename firstType rawRenaming)
        (Code.decode_rename secondType rawRenaming.lift)
  | .codeUniverse _ _, _ => rfl
  | .codeList elementType, rawRenaming => by
      exact congrArg Ty.list (Code.decode_rename elementType rawRenaming)
  | .codeOption elementType, rawRenaming => by
      exact congrArg Ty.option (Code.decode_rename elementType rawRenaming)
  | .codeEither leftType rightType, rawRenaming => by
      exact congrArgTwo (function := Ty.either)
        (Code.decode_rename leftType rawRenaming)
        (Code.decode_rename rightType rawRenaming)
  | .codeId carrier _ _, rawRenaming => by
      exact congrArg (fun decodedCarrier => Ty.id decodedCarrier _ _)
        (Code.decode_rename carrier rawRenaming)

/-- Decoding commutes with weakening. -/
theorem Code.decode_weaken {level scope : Nat} (code : Code level scope) :
    code.weaken.decode = code.decode.weaken :=
  Code.decode_rename code Renaming.weaken

/-- Decode a code substitution into a type substitution. -/
def CodeSubst.decode {level source target : Nat}
    (codeSubstitution : CodeSubst level source target) :
    Subst level source target where
  forTy := fun position => (codeSubstitution.forCode position).decode
  forRaw := codeSubstitution.forRaw

/-- Decoding a lifted code substitution agrees with lifting its decoded
type substitution. -/
theorem CodeSubst.decode_lift_equiv {level source target : Nat}
    (codeSubstitution : CodeSubst level source target) :
    Subst.equiv
      codeSubstitution.lift.decode
      codeSubstitution.decode.lift :=
  Subst.equiv_intro
    (fun position =>
      match position with
      | ⟨0, _⟩ => rfl
      | ⟨position + 1, isWithinSource⟩ =>
          Code.decode_weaken
            (codeSubstitution.forCode
              ⟨position, Nat.lt_of_succ_lt_succ isWithinSource⟩))
    (RawTermSubst.equiv_refl _)

/-- Decoding commutes with code substitution. -/
theorem Code.decode_subst {level source target : Nat} :
    ∀ (code : Code level source)
      (codeSubstitution : CodeSubst level source target),
      (code.subst codeSubstitution).decode =
        code.decode.subst codeSubstitution.decode
  | .codeUnit, _ => rfl
  | .codeBool, _ => rfl
  | .codeNat, _ => rfl
  | .codeArrow domain codomain, codeSubstitution => by
      exact congrArgTwo (function := Ty.arrow)
        (Code.decode_subst domain codeSubstitution)
        (Code.decode_subst codomain codeSubstitution)
  | .codePiTy domain codomain, codeSubstitution => by
      have codomainDecode :=
        Code.decode_subst codomain codeSubstitution.lift
      have liftDecode :=
        Ty.subst_congr (CodeSubst.decode_lift_equiv codeSubstitution) codomain.decode
      exact congrArgTwo (function := Ty.piTy)
        (Code.decode_subst domain codeSubstitution)
        (codomainDecode.trans liftDecode)
  | .codeTyVar _, _ => rfl
  | .codeSigma firstType secondType, codeSubstitution => by
      have secondDecode :=
        Code.decode_subst secondType codeSubstitution.lift
      have liftDecode :=
        Ty.subst_congr (CodeSubst.decode_lift_equiv codeSubstitution) secondType.decode
      exact congrArgTwo (function := Ty.sigmaTy)
        (Code.decode_subst firstType codeSubstitution)
        (secondDecode.trans liftDecode)
  | .codeUniverse _ _, _ => rfl
  | .codeList elementType, codeSubstitution => by
      exact congrArg Ty.list (Code.decode_subst elementType codeSubstitution)
  | .codeOption elementType, codeSubstitution => by
      exact congrArg Ty.option (Code.decode_subst elementType codeSubstitution)
  | .codeEither leftType rightType, codeSubstitution => by
      exact congrArgTwo (function := Ty.either)
        (Code.decode_subst leftType codeSubstitution)
        (Code.decode_subst rightType codeSubstitution)
  | .codeId carrier _ _, codeSubstitution => by
      exact congrArg (fun decodedCarrier => Ty.id decodedCarrier _ _)
        (Code.decode_subst carrier codeSubstitution)

end LeanFX.Syntax

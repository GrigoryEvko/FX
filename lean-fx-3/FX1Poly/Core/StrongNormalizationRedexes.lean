import FX1Poly.Core.StrongNormalizationNeutral

/-! # Foundation/PolyCell/Core/StrongNormalizationRedexes
    - first SN closure proofs for root-reducing redexes

The leaf and constructor files cover normal leaves plus congruence-only
wrappers.  This file starts the next layer: terms that can reduce at the root.
Each theorem must account for both the root reduct and congruence steps inside
the redex's children.

This is still not global SN, not a reducibility predicate, and not the
fundamental theorem.  It is a small audited bridge from congruence-only
accessibility into iota/root-reduction accessibility.
-/

namespace FX1Poly.Core
-- `RawRenaming` lives in `FX1Poly.Foundation`, which does not enclose
-- `FX1Poly.Core`, so open it explicitly.
open FX1Poly.Foundation
namespace StepStar

/-- A lambda-headed application is strongly normalizing when the lambda body is
already normal and the fixed beta contractum is strongly normalizing for every
argument reduct.

This is the first reusable beta-contractum instance builder.  It is narrower
than `appLam_isStronglyNormalizing_of_body_argument_contractum`: the body is
not allowed to move, so the beta obligation only ranges over reducts of the
argument.  That is exactly the shape needed for variable-body beta redexes and
other normal body leaves. -/
theorem appLam_isStronglyNormalizing_of_normal_body_contractum
    {scope : Nat} {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (bodyHasNoStep :
      ∀ targetBody : RawTerm (scope + 1), Step body targetBody → False)
    (contractumTerminates :
      ∀ {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentArgument →
          IsStronglyNormalizing (RawTerm.subst0 body currentArgument))
    (domainAnnTerminates : IsStronglyNormalizing domainAnn)
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentDomain =>
      ∀ {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentArgument →
          IsStronglyNormalizing
            (.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_lam ()
                  (.childCons currentDomain (.childCons body .childNil)))
                (.childCons currentArgument .childNil)) :
              RawTerm scope))
    (m := fun currentDomain currentDomainSuccessors domainIH => by
      intro currentArgument currentArgumentTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerArgument =>
            IsStronglyNormalizing
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_lam ()
                    (.childCons currentDomain (.childCons body .childNil)))
                  (.childCons innerArgument .childNil)) :
                RawTerm scope))
          (m := fun currentArgument currentArgumentSuccessors argumentIH =>
            Acc.intro
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_lam ()
                    (.childCons currentDomain (.childCons body .childNil)))
                  (.childCons currentArgument .childNil)) :
                RawTerm scope)
              (fun targetTerm applicationStep => by
                cases Step.from_app applicationStep with
                | inl betaBranch =>
                    obtain ⟨lambdaDomain, lambdaBody, lambdaEq, targetEq⟩ :=
                      betaBranch
                    cases lambdaEq
                    rw [targetEq]
                    exact
                      contractumTerminates
                        (Acc.intro currentArgument currentArgumentSuccessors)
                | inr congruenceBranch =>
                    cases congruenceBranch with
                    | inl functionBranch =>
                        obtain ⟨functionAfter, targetEq, functionStep⟩ :=
                          functionBranch
                        cases Step.from_lam functionStep with
                        | inl domainBranch =>
                            obtain ⟨domainAfter, functionAfterEq, domainStep⟩ :=
                              domainBranch
                            rw [targetEq, functionAfterEq]
                            exact
                              domainIH domainAfter domainStep
                                (Acc.intro currentArgument
                                  currentArgumentSuccessors)
                        | inr bodyBranch =>
                            obtain ⟨bodyAfter, functionAfterEq, bodyStep⟩ :=
                              bodyBranch
                            exact False.elim (bodyHasNoStep bodyAfter bodyStep)
                    | inr argumentBranch =>
                        obtain ⟨argumentAfter, targetEq, argumentStep⟩ :=
                          argumentBranch
                        rw [targetEq]
                        exact argumentIH argumentAfter argumentStep))
          currentArgumentTerminates)
    domainAnnTerminates)
    argumentTerminates

/-- A lambda-headed application is strongly normalizing when its normal body
substitutes to a fixed strongly-normalizing contractum, independent of the
argument reduct.

This packages the closed-body beta base case used by the reducibility
proof: the lambda body cannot step, and beta always lands on the same
contractum while argument congruence is handled by accessibility induction. -/
theorem appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    {scope : Nat} {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    {contractum argumentTerm : RawTerm scope}
    (bodyHasNoStep :
      ∀ targetBody : RawTerm (scope + 1), Step body targetBody → False)
    (contractumTerminates : IsStronglyNormalizing contractum)
    (bodySubst0Constant :
      ∀ currentArgument : RawTerm scope,
        RawTerm.subst0 body currentArgument = contractum)
    (domainAnnTerminates : IsStronglyNormalizing domainAnn)
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_contractum
    bodyHasNoStep
    (contractumTerminates := fun {currentArgument} _argumentTerminates => by
      rw [bodySubst0Constant currentArgument]
      exact contractumTerminates)
    domainAnnTerminates
    argumentTerminates

/-- Identity beta redexes are strongly normalizing when the argument is strongly
normalizing.

The root beta contractum is the argument itself.  Function congruence is
impossible because the body `var 0` is a normal leaf; argument congruence is
handled by accessibility induction on the argument. -/
theorem appLamVarZero_isStronglyNormalizing_of_argument
    {scope : Nat} {argumentTerm : RawTerm scope}
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1))
                .childNil)
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_contractum
    (body :=
      (.mkGen .gen_var
        (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1))
        .childNil))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_var
        (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1))
        (targetTerm := targetBody)
        bodyStep)
    (contractumTerminates := fun currentArgumentTerminates =>
      currentArgumentTerminates)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    argumentTerminates

/-- Beta redexes whose lambda body is a higher de-Bruijn variable are strongly
normalizing when the argument is strongly normalizing.

The bound variable is not used by the body, so the root beta contractum is the
corresponding variable one scope lower. -/
theorem appLamVarSucc_isStronglyNormalizing_of_argument
    {scope : Nat} (predIndex : Nat)
    (indexBound : predIndex + 1 < scope + 1)
    {argumentTerm : RawTerm scope}
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_var
                (⟨predIndex + 1, indexBound⟩ : Fin (scope + 1))
                .childNil)
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_contractum
    (body :=
      (.mkGen .gen_var
        (⟨predIndex + 1, indexBound⟩ : Fin (scope + 1))
        .childNil))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_var
        (⟨predIndex + 1, indexBound⟩ : Fin (scope + 1))
        (targetTerm := targetBody)
        bodyStep)
    (contractumTerminates := fun {_currentArgument} _argumentTerminates => by
      exact
        var_isStronglyNormalizing
          (⟨predIndex, Nat.lt_of_succ_lt_succ indexBound⟩ : Fin scope))
    (domainAnnTerminates := unit_isStronglyNormalizing)
    argumentTerminates

/-- Beta redexes whose lambda body is `unit` are strongly normalizing when the
argument is strongly normalizing. -/
theorem appLamUnit_isStronglyNormalizing_of_argument
    {scope : Nat} {argumentTerm : RawTerm scope}
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm (scope + 1))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_unit () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_unit () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_unit (targetTerm := targetBody) bodyStep)
    (contractumTerminates := unit_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    argumentTerminates

/-- Beta redexes whose lambda body is `boolTrue` are strongly normalizing when
the argument is strongly normalizing. -/
theorem appLamBoolTrue_isStronglyNormalizing_of_argument
    {scope : Nat} {argumentTerm : RawTerm scope}
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_boolTrue () .childNil : RawTerm (scope + 1))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_boolTrue () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_boolTrue () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_boolTrue (targetTerm := targetBody) bodyStep)
    (contractumTerminates := boolTrue_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    argumentTerminates

/-- Beta redexes whose lambda body is `boolFalse` are strongly normalizing when
the argument is strongly normalizing. -/
theorem appLamBoolFalse_isStronglyNormalizing_of_argument
    {scope : Nat} {argumentTerm : RawTerm scope}
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_boolFalse () .childNil : RawTerm (scope + 1))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_boolFalse () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_boolFalse () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_boolFalse (targetTerm := targetBody) bodyStep)
    (contractumTerminates := boolFalse_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    argumentTerminates

/-- Beta redexes whose lambda body is `natZero` are strongly normalizing when
the argument is strongly normalizing. -/
theorem appLamNatZero_isStronglyNormalizing_of_argument
    {scope : Nat} {argumentTerm : RawTerm scope}
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_natZero () .childNil : RawTerm (scope + 1))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_natZero () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_natZero () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_natZero (targetTerm := targetBody) bodyStep)
    (contractumTerminates := natZero_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    argumentTerminates

/-- Beta redexes whose lambda body is `listNil` are strongly normalizing when
the argument is strongly normalizing. -/
theorem appLamListNil_isStronglyNormalizing_of_argument
    {scope : Nat} {argumentTerm : RawTerm scope}
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_listNil () .childNil : RawTerm (scope + 1))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_listNil () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_listNil () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_listNil (targetTerm := targetBody) bodyStep)
    (contractumTerminates := listNil_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    argumentTerminates

/-- Beta redexes whose lambda body is `optionNone` are strongly normalizing
when the argument is strongly normalizing. -/
theorem appLamOptionNone_isStronglyNormalizing_of_argument
    {scope : Nat} {argumentTerm : RawTerm scope}
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_optionNone () .childNil : RawTerm (scope + 1))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_optionNone () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_optionNone () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_optionNone (targetTerm := targetBody) bodyStep)
    (contractumTerminates := optionNone_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    argumentTerminates

/-- Beta redexes whose lambda body is a universe-code atom are strongly
normalizing when the argument is strongly normalizing. -/
theorem appLamUniverseCode_isStronglyNormalizing_of_argument
    {scope : Nat}
    (levelCode : FX1Poly.Universe.LevelExpr × FX1Poly.Universe.UniverseFlag)
    {argumentTerm : RawTerm scope}
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_universeCode levelCode .childNil :
                RawTerm (scope + 1))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body :=
      (.mkGen .gen_universeCode levelCode .childNil :
        RawTerm (scope + 1)))
    (contractum :=
      (.mkGen .gen_universeCode levelCode .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_universeCode levelCode (targetTerm := targetBody) bodyStep)
    (contractumTerminates := universeCode_isStronglyNormalizing levelCode)
    (bodySubst0Constant := fun _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    argumentTerminates

/-- Beta redexes whose lambda body is cubical interval endpoint `0` are
strongly normalizing when the argument is strongly normalizing. -/
theorem appLamInterval0_isStronglyNormalizing_of_argument
    {scope : Nat} {argumentTerm : RawTerm scope}
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_interval0 () .childNil : RawTerm (scope + 1))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_interval0 () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_interval0 () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_interval0 (targetTerm := targetBody) bodyStep)
    (contractumTerminates := interval0_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    argumentTerminates

/-- Beta redexes whose lambda body is cubical interval endpoint `1` are
strongly normalizing when the argument is strongly normalizing. -/
theorem appLamInterval1_isStronglyNormalizing_of_argument
    {scope : Nat} {argumentTerm : RawTerm scope}
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_interval1 () .childNil : RawTerm (scope + 1))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_interval1 () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_interval1 () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_interval1 (targetTerm := targetBody) bodyStep)
    (contractumTerminates := interval1_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    argumentTerminates

/-- Beta redexes whose lambda body is the HIT circle base point are strongly
normalizing when the argument is strongly normalizing. -/
theorem appLamCircleBase_isStronglyNormalizing_of_argument
    {scope : Nat} {argumentTerm : RawTerm scope}
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_circleBase () .childNil : RawTerm (scope + 1))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_circleBase () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_circleBase () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_circleBase (targetTerm := targetBody) bodyStep)
    (contractumTerminates := circleBase_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    argumentTerminates

/-- Beta redexes whose lambda body is the HIT circle loop generator are
strongly normalizing when the argument is strongly normalizing. -/
theorem appLamCircleLoop_isStronglyNormalizing_of_argument
    {scope : Nat} {argumentTerm : RawTerm scope}
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_circleLoop () .childNil : RawTerm (scope + 1))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_circleLoop () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_circleLoop () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_circleLoop (targetTerm := targetBody) bodyStep)
    (contractumTerminates := circleLoop_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    argumentTerminates

/-- Beta redexes whose lambda body is a quantum-bit atom are strongly
normalizing when the argument is strongly normalizing. -/
theorem appLamQubit_isStronglyNormalizing_of_argument
    {scope : Nat} {argumentTerm : RawTerm scope}
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_qubit () .childNil : RawTerm (scope + 1))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_qubit () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_qubit () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_qubit (targetTerm := targetBody) bodyStep)
    (contractumTerminates := qubit_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    argumentTerminates

/-- Beta redexes whose lambda body is a hyperreal atom are strongly normalizing
when the argument is strongly normalizing. -/
theorem appLamHyperreal_isStronglyNormalizing_of_argument
    {scope : Nat} {argumentTerm : RawTerm scope}
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_hyperreal () .childNil : RawTerm (scope + 1))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_hyperreal () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_hyperreal () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_hyperreal (targetTerm := targetBody) bodyStep)
    (contractumTerminates := hyperreal_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    argumentTerminates

/-- One-child constructor bodies preserve lambda-headed application strong
normalization when the child contractum is strongly normalizing.

This packages the proof shape shared by `natSucc`, `optionSome`,
`eitherInl`, `eitherInr`, and `refl`: function congruence is inverted back to
the single child, while root beta reduces by the supplied `subst0` shape law. -/
theorem appLamOneChildBody_isStronglyNormalizing_of_child_argument_contractum
    {scope : Nat}
    (wrapBody : RawTerm (scope + 1) → RawTerm (scope + 1))
    (wrapContractum : RawTerm scope → RawTerm scope)
    (fromWrapStep :
      ∀ {currentChild targetBody : RawTerm (scope + 1)},
        Step (wrapBody currentChild) targetBody →
          ∃ targetChild : RawTerm (scope + 1),
            targetBody = wrapBody targetChild ∧
              Step currentChild targetChild)
    (wrapContractumTerminates :
      ∀ {contractum : RawTerm scope},
        IsStronglyNormalizing contractum →
          IsStronglyNormalizing (wrapContractum contractum))
    (subst0Wrap :
      ∀ (currentChild : RawTerm (scope + 1))
        (currentArgument : RawTerm scope),
        RawTerm.subst0 (wrapBody currentChild) currentArgument =
          wrapContractum
            (RawTerm.subst0 currentChild currentArgument))
    {domainAnn : RawTerm scope}
    {sourceChild : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (domainAnnTerminates : IsStronglyNormalizing domainAnn)
    (sourceChildTerminates : IsStronglyNormalizing sourceChild)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (childContractumTerminates :
      ∀ {currentChild : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentChild →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentChild currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons domainAnn (.childCons (wrapBody sourceChild) .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentDomain =>
      ∀ {currentChild : RawTerm (scope + 1)},
        IsStronglyNormalizing currentChild →
        ∀ {currentArgument : RawTerm scope},
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_lam ()
                    (.childCons currentDomain
                      (.childCons (wrapBody currentChild) .childNil)))
                  (.childCons currentArgument .childNil)) :
                RawTerm scope))
    (m := fun currentDomain currentDomainSuccessors domainIH => by
      intro currentChild currentChildTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun currentChild =>
            ∀ {currentArgument : RawTerm scope},
              IsStronglyNormalizing currentArgument →
                IsStronglyNormalizing
                  (.mkGen .gen_app ()
                    (.childCons
                      (.mkGen .gen_lam ()
                        (.childCons currentDomain
                          (.childCons (wrapBody currentChild) .childNil)))
                      (.childCons currentArgument .childNil)) :
                    RawTerm scope))
          (m := fun currentChild currentChildSuccessors childIH => by
            intro currentArgument currentArgumentTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerArgument =>
                  IsStronglyNormalizing
                    (.mkGen .gen_app ()
                      (.childCons
                        (.mkGen .gen_lam ()
                          (.childCons currentDomain
                            (.childCons (wrapBody currentChild) .childNil)))
                        (.childCons innerArgument .childNil)) :
                      RawTerm scope))
                (m := fun currentArgument currentArgumentSuccessors argumentIH =>
                  Acc.intro
                    (.mkGen .gen_app ()
                      (.childCons
                        (.mkGen .gen_lam ()
                          (.childCons currentDomain
                            (.childCons (wrapBody currentChild) .childNil)))
                        (.childCons currentArgument .childNil)) :
                      RawTerm scope)
                    (fun targetTerm applicationStep => by
                      cases Step.from_app applicationStep with
                      | inl betaBranch =>
                          obtain ⟨lambdaDomain, lambdaBody, lambdaEq, targetEq⟩ :=
                            betaBranch
                          cases lambdaEq
                          rw [targetEq, subst0Wrap currentChild currentArgument]
                          exact
                            wrapContractumTerminates
                              (childContractumTerminates
                                (Acc.intro currentChild currentChildSuccessors)
                                (Acc.intro currentArgument
                                  currentArgumentSuccessors))
                      | inr congruenceBranch =>
                          cases congruenceBranch with
                          | inl functionBranch =>
                              obtain ⟨functionAfter, targetEq, functionStep⟩ :=
                                functionBranch
                              cases Step.from_lam functionStep with
                              | inl domainBranch =>
                                  obtain
                                    ⟨domainAfter, functionAfterEq,
                                      domainStep⟩ := domainBranch
                                  rw [targetEq, functionAfterEq]
                                  exact
                                    domainIH domainAfter domainStep
                                      (Acc.intro currentChild
                                        currentChildSuccessors)
                                      (Acc.intro currentArgument
                                        currentArgumentSuccessors)
                              | inr bodyBranch =>
                                  obtain
                                    ⟨bodyAfter, functionAfterEq, bodyStep⟩ :=
                                    bodyBranch
                                  obtain ⟨childAfter, bodyAfterEq, childStep⟩ :=
                                    fromWrapStep bodyStep
                                  rw [targetEq, functionAfterEq, bodyAfterEq]
                                  exact
                                    childIH childAfter childStep
                                      (Acc.intro currentArgument
                                        currentArgumentSuccessors)
                          | inr argumentBranch =>
                              obtain ⟨argumentAfter, targetEq, argumentStep⟩ :=
                                argumentBranch
                              rw [targetEq]
                              exact argumentIH argumentAfter argumentStep))
                currentArgumentTerminates)
          currentChildTerminates))
    domainAnnTerminates)
    sourceChildTerminates
    argumentTerminates

/-- Beta redexes whose lambda body is `natSucc predecessor` are strongly
normalizing when the predecessor, argument, and every predecessor contractum
are strongly normalizing.

This is the first non-leaf beta body closure: the proof keeps the body shape
through function congruence by inverting `Step.from_natSucc`, so the beta
contractum obligation descends from the whole body to the predecessor. -/
theorem appLamNatSucc_isStronglyNormalizing_of_predecessor_argument_contractum
    {scope : Nat} {predecessor : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (predecessorTerminates : IsStronglyNormalizing predecessor)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (predecessorContractumTerminates :
      ∀ {currentPredecessor : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentPredecessor →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentPredecessor currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_natSucc ()
                (.childCons predecessor .childNil))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamOneChildBody_isStronglyNormalizing_of_child_argument_contractum
    (wrapBody := fun currentPredecessor =>
      (.mkGen .gen_natSucc ()
        (.childCons currentPredecessor .childNil) : RawTerm (scope + 1)))
    (wrapContractum := fun predecessorContractum =>
      (.mkGen .gen_natSucc ()
        (.childCons predecessorContractum .childNil) : RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_natSucc bodyStep)
    (wrapContractumTerminates := fun predecessorContractumTerminates =>
      natSucc_isStronglyNormalizing_of_predecessor
        predecessorContractumTerminates)
    (subst0Wrap := fun _currentPredecessor _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    predecessorTerminates
    argumentTerminates
    predecessorContractumTerminates

/-- Beta redexes whose lambda body is `optionSome value` are strongly
normalizing when the wrapped value, argument, and every value contractum are
strongly normalizing. -/
theorem appLamOptionSome_isStronglyNormalizing_of_value_argument_contractum
    {scope : Nat} {value : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (valueTerminates : IsStronglyNormalizing value)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (valueContractumTerminates :
      ∀ {currentValue : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentValue →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentValue currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_optionSome ()
                (.childCons value .childNil))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamOneChildBody_isStronglyNormalizing_of_child_argument_contractum
    (wrapBody := fun currentValue =>
      (.mkGen .gen_optionSome ()
        (.childCons currentValue .childNil) : RawTerm (scope + 1)))
    (wrapContractum := fun valueContractum =>
      (.mkGen .gen_optionSome ()
        (.childCons valueContractum .childNil) : RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_optionSome bodyStep)
    (wrapContractumTerminates := fun valueContractumTerminates =>
      optionSome_isStronglyNormalizing_of_value valueContractumTerminates)
    (subst0Wrap := fun _currentValue _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    valueTerminates
    argumentTerminates
    valueContractumTerminates

/-- Beta redexes whose lambda body is `eitherInl value` are strongly
normalizing when the wrapped value, argument, and every value contractum are
strongly normalizing. -/
theorem appLamEitherInl_isStronglyNormalizing_of_value_argument_contractum
    {scope : Nat} {value : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (valueTerminates : IsStronglyNormalizing value)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (valueContractumTerminates :
      ∀ {currentValue : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentValue →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentValue currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_eitherInl ()
                (.childCons value .childNil))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamOneChildBody_isStronglyNormalizing_of_child_argument_contractum
    (wrapBody := fun currentValue =>
      (.mkGen .gen_eitherInl ()
        (.childCons currentValue .childNil) : RawTerm (scope + 1)))
    (wrapContractum := fun valueContractum =>
      (.mkGen .gen_eitherInl ()
        (.childCons valueContractum .childNil) : RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_eitherInl bodyStep)
    (wrapContractumTerminates := fun valueContractumTerminates =>
      eitherInl_isStronglyNormalizing_of_value valueContractumTerminates)
    (subst0Wrap := fun _currentValue _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    valueTerminates
    argumentTerminates
    valueContractumTerminates

/-- Beta redexes whose lambda body is `eitherInr value` are strongly
normalizing when the wrapped value, argument, and every value contractum are
strongly normalizing. -/
theorem appLamEitherInr_isStronglyNormalizing_of_value_argument_contractum
    {scope : Nat} {value : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (valueTerminates : IsStronglyNormalizing value)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (valueContractumTerminates :
      ∀ {currentValue : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentValue →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentValue currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_eitherInr ()
                (.childCons value .childNil))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamOneChildBody_isStronglyNormalizing_of_child_argument_contractum
    (wrapBody := fun currentValue =>
      (.mkGen .gen_eitherInr ()
        (.childCons currentValue .childNil) : RawTerm (scope + 1)))
    (wrapContractum := fun valueContractum =>
      (.mkGen .gen_eitherInr ()
        (.childCons valueContractum .childNil) : RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_eitherInr bodyStep)
    (wrapContractumTerminates := fun valueContractumTerminates =>
      eitherInr_isStronglyNormalizing_of_value valueContractumTerminates)
    (subst0Wrap := fun _currentValue _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    valueTerminates
    argumentTerminates
    valueContractumTerminates

/-- Beta redexes whose lambda body is `refl witness` are strongly normalizing
when the witness, argument, and every witness contractum are strongly
normalizing. -/
theorem appLamRefl_isStronglyNormalizing_of_witness_argument_contractum
    {scope : Nat} {rawWitness : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (witnessTerminates : IsStronglyNormalizing rawWitness)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (witnessContractumTerminates :
      ∀ {currentWitness : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentWitness →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentWitness currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_refl ()
                (.childCons rawWitness .childNil))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamOneChildBody_isStronglyNormalizing_of_child_argument_contractum
    (wrapBody := fun currentWitness =>
      (.mkGen .gen_refl ()
        (.childCons currentWitness .childNil) : RawTerm (scope + 1)))
    (wrapContractum := fun witnessContractum =>
      (.mkGen .gen_refl ()
        (.childCons witnessContractum .childNil) : RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_refl bodyStep)
    (wrapContractumTerminates := fun witnessContractumTerminates =>
      refl_isStronglyNormalizing_of_witness witnessContractumTerminates)
    (subst0Wrap := fun _currentWitness _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    witnessTerminates
    argumentTerminates
    witnessContractumTerminates

/-- Beta redexes whose lambda body is `modIntro value` are strongly
normalizing when the modal payload, argument, and every payload contractum
are strongly normalizing. -/
theorem appLamModIntro_isStronglyNormalizing_of_value_argument_contractum
    {scope : Nat} {modalTerm : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (modalTerminates : IsStronglyNormalizing modalTerm)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (modalContractumTerminates :
      ∀ {currentModal : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentModal →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentModal currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_modIntro ()
                (.childCons modalTerm .childNil))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamOneChildBody_isStronglyNormalizing_of_child_argument_contractum
    (wrapBody := fun currentModal =>
      (.mkGen .gen_modIntro ()
        (.childCons currentModal .childNil) : RawTerm (scope + 1)))
    (wrapContractum := fun modalContractum =>
      (.mkGen .gen_modIntro ()
        (.childCons modalContractum .childNil) : RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_modIntro bodyStep)
    (wrapContractumTerminates := fun modalContractumTerminates =>
      modIntro_isStronglyNormalizing_of_value modalContractumTerminates)
    (subst0Wrap := fun _currentModal _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    modalTerminates
    argumentTerminates
    modalContractumTerminates

/-- Two-child constructor bodies preserve lambda-headed application strong
normalization when both child contracta are strongly normalizing.

This is the two-child sibling of
`appLamOneChildBody_isStronglyNormalizing_of_child_argument_contractum`, used
for `pair` and `listCons` body shapes. -/
theorem appLamTwoChildBody_isStronglyNormalizing_of_children_argument_contractum
    {scope : Nat}
    (wrapBody :
      RawTerm (scope + 1) → RawTerm (scope + 1) → RawTerm (scope + 1))
    (wrapContractum : RawTerm scope → RawTerm scope → RawTerm scope)
    (fromWrapStep :
      ∀ {currentFirst currentSecond targetBody : RawTerm (scope + 1)},
        Step (wrapBody currentFirst currentSecond) targetBody →
          (∃ targetFirst : RawTerm (scope + 1),
            targetBody = wrapBody targetFirst currentSecond ∧
              Step currentFirst targetFirst)
          ∨
          (∃ targetSecond : RawTerm (scope + 1),
            targetBody = wrapBody currentFirst targetSecond ∧
              Step currentSecond targetSecond))
    (wrapContractumTerminates :
      ∀ {firstContractum secondContractum : RawTerm scope},
        IsStronglyNormalizing firstContractum →
          IsStronglyNormalizing secondContractum →
            IsStronglyNormalizing
              (wrapContractum firstContractum secondContractum))
    (subst0Wrap :
      ∀ (currentFirst currentSecond : RawTerm (scope + 1))
        (currentArgument : RawTerm scope),
        RawTerm.subst0 (wrapBody currentFirst currentSecond)
            currentArgument =
          wrapContractum
            (RawTerm.subst0 currentFirst currentArgument)
            (RawTerm.subst0 currentSecond currentArgument))
    {domainAnn : RawTerm scope}
    {sourceFirst sourceSecond : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (domainAnnTerminates : IsStronglyNormalizing domainAnn)
    (sourceFirstTerminates : IsStronglyNormalizing sourceFirst)
    (sourceSecondTerminates : IsStronglyNormalizing sourceSecond)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (firstContractumTerminates :
      ∀ {currentFirst : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentFirst →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentFirst currentArgument))
    (secondContractumTerminates :
      ∀ {currentSecond : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentSecond →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentSecond currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons domainAnn
              (.childCons (wrapBody sourceFirst sourceSecond) .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentDomain =>
      ∀ {currentFirst : RawTerm (scope + 1)},
        IsStronglyNormalizing currentFirst →
        ∀ {currentSecond : RawTerm (scope + 1)},
          IsStronglyNormalizing currentSecond →
          ∀ {currentArgument : RawTerm scope},
            IsStronglyNormalizing currentArgument →
              IsStronglyNormalizing
                (.mkGen .gen_app ()
                  (.childCons
                    (.mkGen .gen_lam ()
                      (.childCons currentDomain
                        (.childCons
                          (wrapBody currentFirst currentSecond)
                          .childNil)))
                    (.childCons currentArgument .childNil)) :
                  RawTerm scope))
    (m := fun currentDomain currentDomainSuccessors domainIH => by
      intro currentFirst currentFirstTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun currentFirst =>
            ∀ {currentSecond : RawTerm (scope + 1)},
              IsStronglyNormalizing currentSecond →
                ∀ {currentArgument : RawTerm scope},
                  IsStronglyNormalizing currentArgument →
                    IsStronglyNormalizing
                      (.mkGen .gen_app ()
                        (.childCons
                          (.mkGen .gen_lam ()
                            (.childCons currentDomain
                              (.childCons
                                (wrapBody currentFirst currentSecond)
                                .childNil)))
                          (.childCons currentArgument .childNil)) :
                        RawTerm scope))
          (m := fun currentFirst currentFirstSuccessors firstIH => by
            intro currentSecond currentSecondTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerSecond =>
                  ∀ {currentArgument : RawTerm scope},
                    IsStronglyNormalizing currentArgument →
                      IsStronglyNormalizing
                        (.mkGen .gen_app ()
                          (.childCons
                            (.mkGen .gen_lam ()
                              (.childCons currentDomain
                                (.childCons
                                  (wrapBody currentFirst innerSecond)
                                  .childNil)))
                            (.childCons currentArgument .childNil)) :
                          RawTerm scope))
                (m := fun currentSecond currentSecondSuccessors secondIH => by
                  intro currentArgument currentArgumentTerminates
                  exact
                    Acc.ndrec
                      (r := StepSuccessor)
                      (C := fun innerArgument =>
                        IsStronglyNormalizing
                          (.mkGen .gen_app ()
                            (.childCons
                              (.mkGen .gen_lam ()
                                (.childCons currentDomain
                                  (.childCons
                                    (wrapBody currentFirst currentSecond)
                                    .childNil)))
                              (.childCons innerArgument .childNil)) :
                            RawTerm scope))
                      (m := fun currentArgument currentArgumentSuccessors
                          argumentIH =>
                        Acc.intro
                          (.mkGen .gen_app ()
                            (.childCons
                              (.mkGen .gen_lam ()
                                (.childCons currentDomain
                                  (.childCons
                                    (wrapBody currentFirst currentSecond)
                                    .childNil)))
                              (.childCons currentArgument .childNil)) :
                            RawTerm scope)
                          (fun targetTerm applicationStep => by
                            cases Step.from_app applicationStep with
                            | inl betaBranch =>
                                obtain
                                  ⟨lambdaDomain, lambdaBody, lambdaEq,
                                    targetEq⟩ := betaBranch
                                cases lambdaEq
                                rw [targetEq,
                                  subst0Wrap currentFirst currentSecond
                                    currentArgument]
                                exact
                                  wrapContractumTerminates
                                    (firstContractumTerminates
                                      (Acc.intro currentFirst
                                        currentFirstSuccessors)
                                      (Acc.intro currentArgument
                                        currentArgumentSuccessors))
                                    (secondContractumTerminates
                                      (Acc.intro currentSecond
                                        currentSecondSuccessors)
                                      (Acc.intro currentArgument
                                        currentArgumentSuccessors))
                            | inr congruenceBranch =>
                                cases congruenceBranch with
                                | inl functionBranch =>
                                    obtain
                                      ⟨functionAfter, targetEq,
                                        functionStep⟩ := functionBranch
                                    cases Step.from_lam functionStep with
                                    | inl domainBranch =>
                                        obtain
                                          ⟨domainAfter, functionAfterEq,
                                            domainStep⟩ := domainBranch
                                        rw [targetEq, functionAfterEq]
                                        exact
                                          domainIH domainAfter domainStep
                                            (Acc.intro currentFirst
                                              currentFirstSuccessors)
                                            (Acc.intro currentSecond
                                              currentSecondSuccessors)
                                            (Acc.intro currentArgument
                                              currentArgumentSuccessors)
                                    | inr bodyBranch =>
                                        obtain
                                          ⟨bodyAfter, functionAfterEq,
                                            bodyStep⟩ := bodyBranch
                                        cases fromWrapStep bodyStep with
                                        | inl firstBranch =>
                                            obtain
                                              ⟨firstAfter, bodyAfterEq,
                                                firstStep⟩ := firstBranch
                                            rw [targetEq, functionAfterEq,
                                              bodyAfterEq]
                                            exact
                                              firstIH firstAfter firstStep
                                                (Acc.intro currentSecond
                                                  currentSecondSuccessors)
                                                (Acc.intro currentArgument
                                                  currentArgumentSuccessors)
                                        | inr secondBranch =>
                                            obtain
                                              ⟨secondAfter, bodyAfterEq,
                                                secondStep⟩ := secondBranch
                                            rw [targetEq, functionAfterEq,
                                              bodyAfterEq]
                                            exact
                                              secondIH secondAfter secondStep
                                                (Acc.intro currentArgument
                                                  currentArgumentSuccessors)
                                | inr argumentBranch =>
                                    obtain
                                      ⟨argumentAfter, targetEq,
                                        argumentStep⟩ := argumentBranch
                                    rw [targetEq]
                                    exact
                                      argumentIH argumentAfter argumentStep))
                      currentArgumentTerminates)
                currentSecondTerminates)
          currentFirstTerminates))
    domainAnnTerminates)
    sourceFirstTerminates
    sourceSecondTerminates
    argumentTerminates

/-- Two-child constructor bodies whose second child is under one binder preserve
lambda-headed application strong normalization when both child contracta are
strongly normalizing.

This covers type-code binder shapes such as `piTyCode`, `sigmaTyCode`, and
`polyFunctor`: beta substitution crosses the second child binder but not the
first child. -/
theorem appLamTwoChildSecondBinderBody_isStronglyNormalizing_of_children_argument_contractum
    {scope : Nat}
    (wrapBody :
      RawTerm (scope + 1) → RawTerm ((scope + 1) + 1) →
        RawTerm (scope + 1))
    (wrapContractum : RawTerm scope → RawTerm (scope + 1) → RawTerm scope)
    (fromWrapStep :
      ∀ {currentFirst : RawTerm (scope + 1)}
        {currentSecond : RawTerm ((scope + 1) + 1)}
        {targetBody : RawTerm (scope + 1)},
        Step (wrapBody currentFirst currentSecond) targetBody →
          (∃ targetFirst : RawTerm (scope + 1),
            targetBody = wrapBody targetFirst currentSecond ∧
              Step currentFirst targetFirst)
          ∨
          (∃ targetSecond : RawTerm ((scope + 1) + 1),
            targetBody = wrapBody currentFirst targetSecond ∧
              Step currentSecond targetSecond))
    (wrapContractumTerminates :
      ∀ {firstContractum : RawTerm scope}
        {secondContractum : RawTerm (scope + 1)},
        IsStronglyNormalizing firstContractum →
          IsStronglyNormalizing secondContractum →
            IsStronglyNormalizing
              (wrapContractum firstContractum secondContractum))
    (subst0Wrap :
      ∀ (currentFirst : RawTerm (scope + 1))
        (currentSecond : RawTerm ((scope + 1) + 1))
        (currentArgument : RawTerm scope),
        RawTerm.subst0 (wrapBody currentFirst currentSecond)
            currentArgument =
          wrapContractum
            (RawTerm.subst0 currentFirst currentArgument)
            (RawTerm.subst
              (RawTermSubst.lift
                (RawTermSubst.singleton currentArgument))
              currentSecond))
    {domainAnn : RawTerm scope}
    {sourceFirst : RawTerm (scope + 1)}
    {sourceSecond : RawTerm ((scope + 1) + 1)}
    {argumentTerm : RawTerm scope}
    (domainAnnTerminates : IsStronglyNormalizing domainAnn)
    (sourceFirstTerminates : IsStronglyNormalizing sourceFirst)
    (sourceSecondTerminates : IsStronglyNormalizing sourceSecond)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (firstContractumTerminates :
      ∀ {currentFirst : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentFirst →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentFirst currentArgument))
    (secondContractumTerminates :
      ∀ {currentSecond : RawTerm ((scope + 1) + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentSecond →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst
                (RawTermSubst.lift (RawTermSubst.singleton currentArgument))
                currentSecond)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons domainAnn
              (.childCons (wrapBody sourceFirst sourceSecond) .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentDomain =>
      ∀ {currentFirst : RawTerm (scope + 1)},
        IsStronglyNormalizing currentFirst →
        ∀ {currentSecond : RawTerm ((scope + 1) + 1)},
          IsStronglyNormalizing currentSecond →
          ∀ {currentArgument : RawTerm scope},
            IsStronglyNormalizing currentArgument →
              IsStronglyNormalizing
                (.mkGen .gen_app ()
                  (.childCons
                    (.mkGen .gen_lam ()
                      (.childCons currentDomain
                        (.childCons
                          (wrapBody currentFirst currentSecond)
                          .childNil)))
                    (.childCons currentArgument .childNil)) :
                  RawTerm scope))
    (m := fun currentDomain currentDomainSuccessors domainIH => by
      intro currentFirst currentFirstTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun currentFirst =>
            ∀ {currentSecond : RawTerm ((scope + 1) + 1)},
              IsStronglyNormalizing currentSecond →
                ∀ {currentArgument : RawTerm scope},
                  IsStronglyNormalizing currentArgument →
                    IsStronglyNormalizing
                      (.mkGen .gen_app ()
                        (.childCons
                          (.mkGen .gen_lam ()
                            (.childCons currentDomain
                              (.childCons
                                (wrapBody currentFirst currentSecond)
                                .childNil)))
                          (.childCons currentArgument .childNil)) :
                        RawTerm scope))
          (m := fun currentFirst currentFirstSuccessors firstIH => by
            intro currentSecond currentSecondTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerSecond =>
                  ∀ {currentArgument : RawTerm scope},
                    IsStronglyNormalizing currentArgument →
                      IsStronglyNormalizing
                        (.mkGen .gen_app ()
                          (.childCons
                            (.mkGen .gen_lam ()
                              (.childCons currentDomain
                                (.childCons
                                  (wrapBody currentFirst innerSecond)
                                  .childNil)))
                            (.childCons currentArgument .childNil)) :
                          RawTerm scope))
                (m := fun currentSecond currentSecondSuccessors secondIH => by
                  intro currentArgument currentArgumentTerminates
                  exact
                    Acc.ndrec
                      (r := StepSuccessor)
                      (C := fun innerArgument =>
                        IsStronglyNormalizing
                          (.mkGen .gen_app ()
                            (.childCons
                              (.mkGen .gen_lam ()
                                (.childCons currentDomain
                                  (.childCons
                                    (wrapBody currentFirst currentSecond)
                                    .childNil)))
                              (.childCons innerArgument .childNil)) :
                            RawTerm scope))
                      (m := fun currentArgument currentArgumentSuccessors
                          argumentIH =>
                        Acc.intro
                          (.mkGen .gen_app ()
                            (.childCons
                              (.mkGen .gen_lam ()
                                (.childCons currentDomain
                                  (.childCons
                                    (wrapBody currentFirst currentSecond)
                                    .childNil)))
                              (.childCons currentArgument .childNil)) :
                            RawTerm scope)
                          (fun targetTerm applicationStep => by
                            cases Step.from_app applicationStep with
                            | inl betaBranch =>
                                obtain
                                  ⟨lambdaDomain, lambdaBody, lambdaEq,
                                    targetEq⟩ := betaBranch
                                cases lambdaEq
                                rw [targetEq,
                                  subst0Wrap currentFirst currentSecond
                                    currentArgument]
                                exact
                                  wrapContractumTerminates
                                    (firstContractumTerminates
                                      (Acc.intro currentFirst
                                        currentFirstSuccessors)
                                      (Acc.intro currentArgument
                                        currentArgumentSuccessors))
                                    (secondContractumTerminates
                                      (Acc.intro currentSecond
                                        currentSecondSuccessors)
                                      (Acc.intro currentArgument
                                        currentArgumentSuccessors))
                            | inr congruenceBranch =>
                                cases congruenceBranch with
                                | inl functionBranch =>
                                    obtain
                                      ⟨functionAfter, targetEq,
                                        functionStep⟩ := functionBranch
                                    cases Step.from_lam functionStep with
                                    | inl domainBranch =>
                                        obtain
                                          ⟨domainAfter, functionAfterEq,
                                            domainStep⟩ := domainBranch
                                        rw [targetEq, functionAfterEq]
                                        exact
                                          domainIH domainAfter domainStep
                                            (Acc.intro currentFirst
                                              currentFirstSuccessors)
                                            (Acc.intro currentSecond
                                              currentSecondSuccessors)
                                            (Acc.intro currentArgument
                                              currentArgumentSuccessors)
                                    | inr bodyBranch =>
                                        obtain
                                          ⟨bodyAfter, functionAfterEq,
                                            bodyStep⟩ := bodyBranch
                                        cases fromWrapStep bodyStep with
                                        | inl firstBranch =>
                                            obtain
                                              ⟨firstAfter, bodyAfterEq,
                                                firstStep⟩ := firstBranch
                                            rw [targetEq, functionAfterEq,
                                              bodyAfterEq]
                                            exact
                                              firstIH firstAfter firstStep
                                                (Acc.intro currentSecond
                                                  currentSecondSuccessors)
                                                (Acc.intro currentArgument
                                                  currentArgumentSuccessors)
                                        | inr secondBranch =>
                                            obtain
                                              ⟨secondAfter, bodyAfterEq,
                                                secondStep⟩ := secondBranch
                                            rw [targetEq, functionAfterEq,
                                              bodyAfterEq]
                                            exact
                                              secondIH secondAfter secondStep
                                                (Acc.intro currentArgument
                                                  currentArgumentSuccessors)
                                | inr argumentBranch =>
                                    obtain
                                      ⟨argumentAfter, targetEq,
                                        argumentStep⟩ := argumentBranch
                                    rw [targetEq]
                                    exact
                                      argumentIH argumentAfter argumentStep))
                      currentArgumentTerminates)
                currentSecondTerminates)
          currentFirstTerminates))
    domainAnnTerminates)
    sourceFirstTerminates
    sourceSecondTerminates
    argumentTerminates

/-- Beta redexes whose lambda body is `pair first second` are strongly
normalizing when both components, the argument, and both component contracta
are strongly normalizing. -/
theorem appLamPair_isStronglyNormalizing_of_components_argument_contractum
    {scope : Nat} {first second : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (firstTerminates : IsStronglyNormalizing first)
    (secondTerminates : IsStronglyNormalizing second)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (firstContractumTerminates :
      ∀ {currentFirst : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentFirst →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentFirst currentArgument))
    (secondContractumTerminates :
      ∀ {currentSecond : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentSecond →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentSecond currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_pair ()
                (.childCons first (.childCons second .childNil)))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamTwoChildBody_isStronglyNormalizing_of_children_argument_contractum
    (wrapBody := fun currentFirst currentSecond =>
      (.mkGen .gen_pair ()
        (.childCons currentFirst (.childCons currentSecond .childNil)) :
        RawTerm (scope + 1)))
    (wrapContractum := fun firstContractum secondContractum =>
      (.mkGen .gen_pair ()
        (.childCons firstContractum
          (.childCons secondContractum .childNil)) :
        RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_pair bodyStep)
    (wrapContractumTerminates :=
      fun firstContractumTerminates secondContractumTerminates =>
        pair_isStronglyNormalizing_of_components
          firstContractumTerminates
          secondContractumTerminates)
    (subst0Wrap := fun _currentFirst _currentSecond _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    firstTerminates
    secondTerminates
    argumentTerminates
    firstContractumTerminates
    secondContractumTerminates

/-- Beta redexes whose lambda body is `listCons head tail` are strongly
normalizing when both components, the argument, and both component contracta
are strongly normalizing. -/
theorem appLamListCons_isStronglyNormalizing_of_head_tail_argument_contractum
    {scope : Nat} {headVal tailVal : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (headTerminates : IsStronglyNormalizing headVal)
    (tailTerminates : IsStronglyNormalizing tailVal)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (headContractumTerminates :
      ∀ {currentHead : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentHead →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentHead currentArgument))
    (tailContractumTerminates :
      ∀ {currentTail : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentTail →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentTail currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_listCons ()
                (.childCons headVal (.childCons tailVal .childNil)))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamTwoChildBody_isStronglyNormalizing_of_children_argument_contractum
    (wrapBody := fun currentHead currentTail =>
      (.mkGen .gen_listCons ()
        (.childCons currentHead (.childCons currentTail .childNil)) :
        RawTerm (scope + 1)))
    (wrapContractum := fun headContractum tailContractum =>
      (.mkGen .gen_listCons ()
        (.childCons headContractum
          (.childCons tailContractum .childNil)) :
        RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_listCons bodyStep)
    (wrapContractumTerminates :=
      fun headContractumTerminates tailContractumTerminates =>
        listCons_isStronglyNormalizing_of_head_tail
          headContractumTerminates
          tailContractumTerminates)
    (subst0Wrap := fun _currentHead _currentTail _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    headTerminates
    tailTerminates
    argumentTerminates
    headContractumTerminates
    tailContractumTerminates

/-- Beta redexes whose lambda body is `glueIntro base partial` are strongly
normalizing when both payloads, the argument, and both payload contracta are
strongly normalizing. -/
theorem appLamGlueIntro_isStronglyNormalizing_of_components_argument_contractum
    {scope : Nat} {baseValue partialValue : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (baseTerminates : IsStronglyNormalizing baseValue)
    (partialTerminates : IsStronglyNormalizing partialValue)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (baseContractumTerminates :
      ∀ {currentBase : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentBase →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentBase currentArgument))
    (partialContractumTerminates :
      ∀ {currentPartial : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentPartial →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentPartial currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_glueIntro ()
                (.childCons baseValue
                  (.childCons partialValue .childNil)))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamTwoChildBody_isStronglyNormalizing_of_children_argument_contractum
    (wrapBody := fun currentBase currentPartial =>
      (.mkGen .gen_glueIntro ()
        (.childCons currentBase (.childCons currentPartial .childNil)) :
        RawTerm (scope + 1)))
    (wrapContractum := fun baseContractum partialContractum =>
      (.mkGen .gen_glueIntro ()
        (.childCons baseContractum
          (.childCons partialContractum .childNil)) :
        RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_glueIntro bodyStep)
    (wrapContractumTerminates :=
      fun baseContractumTerminates partialContractumTerminates =>
        glueIntro_isStronglyNormalizing_of_components
          baseContractumTerminates
          partialContractumTerminates)
    (subst0Wrap := fun _currentBase _currentPartial _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    baseTerminates
    partialTerminates
    argumentTerminates
    baseContractumTerminates
    partialContractumTerminates

/-- Beta redexes whose lambda body is `arrowCode domain codomain` are strongly
normalizing when both endpoint type codes, the argument, and both endpoint
contracta are strongly normalizing. -/
theorem appLamArrowCode_isStronglyNormalizing_of_domain_codomain_argument_contractum
    {scope : Nat} {domain codomain : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (domainTerminates : IsStronglyNormalizing domain)
    (codomainTerminates : IsStronglyNormalizing codomain)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (domainContractumTerminates :
      ∀ {currentDomain : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentDomain →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentDomain currentArgument))
    (codomainContractumTerminates :
      ∀ {currentCodomain : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentCodomain →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentCodomain currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_arrowCode ()
                (.childCons domain (.childCons codomain .childNil)))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamTwoChildBody_isStronglyNormalizing_of_children_argument_contractum
    (wrapBody := fun currentDomain currentCodomain =>
      (.mkGen .gen_arrowCode ()
        (.childCons currentDomain (.childCons currentCodomain .childNil)) :
        RawTerm (scope + 1)))
    (wrapContractum := fun domainContractum codomainContractum =>
      (.mkGen .gen_arrowCode ()
        (.childCons domainContractum
          (.childCons codomainContractum .childNil)) :
        RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_arrowCode bodyStep)
    (wrapContractumTerminates :=
      fun domainContractumTerminates codomainContractumTerminates =>
        arrowCode_isStronglyNormalizing_of_domain_codomain
          domainContractumTerminates
          codomainContractumTerminates)
    (subst0Wrap := fun _currentDomain _currentCodomain _currentArgument =>
      rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    domainTerminates
    codomainTerminates
    argumentTerminates
    domainContractumTerminates
    codomainContractumTerminates

/-- Beta redexes whose lambda body is `productCode leftType rightType` are
strongly normalizing when both component type codes, the argument, and both
component contracta are strongly normalizing. -/
theorem appLamProductCode_isStronglyNormalizing_of_left_right_argument_contractum
    {scope : Nat} {leftType rightType : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (leftTypeTerminates : IsStronglyNormalizing leftType)
    (rightTypeTerminates : IsStronglyNormalizing rightType)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (leftTypeContractumTerminates :
      ∀ {currentLeftType : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentLeftType →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentLeftType currentArgument))
    (rightTypeContractumTerminates :
      ∀ {currentRightType : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentRightType →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentRightType currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_productCode ()
                (.childCons leftType (.childCons rightType .childNil)))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamTwoChildBody_isStronglyNormalizing_of_children_argument_contractum
    (wrapBody := fun currentLeftType currentRightType =>
      (.mkGen .gen_productCode ()
        (.childCons currentLeftType
          (.childCons currentRightType .childNil)) :
        RawTerm (scope + 1)))
    (wrapContractum := fun leftTypeContractum rightTypeContractum =>
      (.mkGen .gen_productCode ()
        (.childCons leftTypeContractum
          (.childCons rightTypeContractum .childNil)) :
        RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_productCode bodyStep)
    (wrapContractumTerminates :=
      fun leftTypeContractumTerminates rightTypeContractumTerminates =>
        productCode_isStronglyNormalizing_of_left_right
          leftTypeContractumTerminates
          rightTypeContractumTerminates)
    (subst0Wrap := fun _currentLeftType _currentRightType _currentArgument =>
      rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    leftTypeTerminates
    rightTypeTerminates
    argumentTerminates
    leftTypeContractumTerminates
    rightTypeContractumTerminates

/-- Beta redexes whose lambda body is `sumCode leftType rightType` are
strongly normalizing when both summand type codes, the argument, and both
summand contracta are strongly normalizing. -/
theorem appLamSumCode_isStronglyNormalizing_of_left_right_argument_contractum
    {scope : Nat} {leftType rightType : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (leftTypeTerminates : IsStronglyNormalizing leftType)
    (rightTypeTerminates : IsStronglyNormalizing rightType)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (leftTypeContractumTerminates :
      ∀ {currentLeftType : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentLeftType →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentLeftType currentArgument))
    (rightTypeContractumTerminates :
      ∀ {currentRightType : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentRightType →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentRightType currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_sumCode ()
                (.childCons leftType (.childCons rightType .childNil)))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamTwoChildBody_isStronglyNormalizing_of_children_argument_contractum
    (wrapBody := fun currentLeftType currentRightType =>
      (.mkGen .gen_sumCode ()
        (.childCons currentLeftType
          (.childCons currentRightType .childNil)) :
        RawTerm (scope + 1)))
    (wrapContractum := fun leftTypeContractum rightTypeContractum =>
      (.mkGen .gen_sumCode ()
        (.childCons leftTypeContractum
          (.childCons rightTypeContractum .childNil)) :
        RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_sumCode bodyStep)
    (wrapContractumTerminates :=
      fun leftTypeContractumTerminates rightTypeContractumTerminates =>
        sumCode_isStronglyNormalizing_of_left_right
          leftTypeContractumTerminates
          rightTypeContractumTerminates)
    (subst0Wrap := fun _currentLeftType _currentRightType _currentArgument =>
      rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    leftTypeTerminates
    rightTypeTerminates
    argumentTerminates
    leftTypeContractumTerminates
    rightTypeContractumTerminates

/-- Beta redexes whose lambda body is `eitherCode leftType rightType` are
strongly normalizing when both side type codes, the argument, and both side
contracta are strongly normalizing. -/
theorem appLamEitherCode_isStronglyNormalizing_of_left_right_argument_contractum
    {scope : Nat} {leftType rightType : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (leftTypeTerminates : IsStronglyNormalizing leftType)
    (rightTypeTerminates : IsStronglyNormalizing rightType)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (leftTypeContractumTerminates :
      ∀ {currentLeftType : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentLeftType →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentLeftType currentArgument))
    (rightTypeContractumTerminates :
      ∀ {currentRightType : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentRightType →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentRightType currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_eitherCode ()
                (.childCons leftType (.childCons rightType .childNil)))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamTwoChildBody_isStronglyNormalizing_of_children_argument_contractum
    (wrapBody := fun currentLeftType currentRightType =>
      (.mkGen .gen_eitherCode ()
        (.childCons currentLeftType
          (.childCons currentRightType .childNil)) :
        RawTerm (scope + 1)))
    (wrapContractum := fun leftTypeContractum rightTypeContractum =>
      (.mkGen .gen_eitherCode ()
        (.childCons leftTypeContractum
          (.childCons rightTypeContractum .childNil)) :
        RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_eitherCode bodyStep)
    (wrapContractumTerminates :=
      fun leftTypeContractumTerminates rightTypeContractumTerminates =>
        eitherCode_isStronglyNormalizing_of_left_right
          leftTypeContractumTerminates
          rightTypeContractumTerminates)
    (subst0Wrap := fun _currentLeftType _currentRightType _currentArgument =>
      rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    leftTypeTerminates
    rightTypeTerminates
    argumentTerminates
    leftTypeContractumTerminates
    rightTypeContractumTerminates

/-- Beta redexes whose lambda body is `equivCode sourceType targetType` are
strongly normalizing when both carrier type codes, the argument, and both
carrier contracta are strongly normalizing. -/
theorem appLamEquivCode_isStronglyNormalizing_of_source_target_argument_contractum
    {scope : Nat} {sourceType targetType : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (sourceTypeTerminates : IsStronglyNormalizing sourceType)
    (targetTypeTerminates : IsStronglyNormalizing targetType)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (sourceTypeContractumTerminates :
      ∀ {currentSourceType : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentSourceType →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentSourceType currentArgument))
    (targetTypeContractumTerminates :
      ∀ {currentTargetType : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentTargetType →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentTargetType currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_equivCode ()
                (.childCons sourceType
                  (.childCons targetType .childNil)))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamTwoChildBody_isStronglyNormalizing_of_children_argument_contractum
    (wrapBody := fun currentSourceType currentTargetType =>
      (.mkGen .gen_equivCode ()
        (.childCons currentSourceType
          (.childCons currentTargetType .childNil)) :
        RawTerm (scope + 1)))
    (wrapContractum := fun sourceTypeContractum targetTypeContractum =>
      (.mkGen .gen_equivCode ()
        (.childCons sourceTypeContractum
          (.childCons targetTypeContractum .childNil)) :
        RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_equivCode bodyStep)
    (wrapContractumTerminates :=
      fun sourceTypeContractumTerminates targetTypeContractumTerminates =>
        equivCode_isStronglyNormalizing_of_source_target
          sourceTypeContractumTerminates
          targetTypeContractumTerminates)
    (subst0Wrap :=
      fun _currentSourceType _currentTargetType _currentArgument => rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    sourceTypeTerminates
    targetTypeTerminates
    argumentTerminates
    sourceTypeContractumTerminates
    targetTypeContractumTerminates

/-- Beta redexes whose lambda body is `piTyCode domain codomain` are strongly
normalizing when both children, the argument, and both child contracta are
strongly normalizing.  The codomain contractum uses the lifted singleton
substitution because it lives under the pi binder. -/
theorem appLamPiTyCode_isStronglyNormalizing_of_domain_codomain_argument_contractum
    {scope : Nat} {domain : RawTerm (scope + 1)}
    {codomain : RawTerm ((scope + 1) + 1)}
    {argumentTerm : RawTerm scope}
    (domainTerminates : IsStronglyNormalizing domain)
    (codomainTerminates : IsStronglyNormalizing codomain)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (domainContractumTerminates :
      ∀ {currentDomain : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentDomain →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentDomain currentArgument))
    (codomainContractumTerminates :
      ∀ {currentCodomain : RawTerm ((scope + 1) + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentCodomain →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst
                (RawTermSubst.lift (RawTermSubst.singleton currentArgument))
                currentCodomain)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_piTyCode ()
                (.childCons domain (.childCons codomain .childNil)))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamTwoChildSecondBinderBody_isStronglyNormalizing_of_children_argument_contractum
    (wrapBody := fun currentDomain currentCodomain =>
      (.mkGen .gen_piTyCode ()
        (.childCons currentDomain (.childCons currentCodomain .childNil)) :
        RawTerm (scope + 1)))
    (wrapContractum := fun domainContractum codomainContractum =>
      (.mkGen .gen_piTyCode ()
        (.childCons domainContractum
          (.childCons codomainContractum .childNil)) :
        RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_piTyCode bodyStep)
    (wrapContractumTerminates :=
      fun domainContractumTerminates codomainContractumTerminates =>
        piTyCode_isStronglyNormalizing_of_domain_codomain
          domainContractumTerminates
          codomainContractumTerminates)
    (subst0Wrap := fun _currentDomain _currentCodomain _currentArgument =>
      rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    domainTerminates
    codomainTerminates
    argumentTerminates
    domainContractumTerminates
    codomainContractumTerminates

/-- Beta redexes whose lambda body is `sigmaTyCode domain codomain` are
strongly normalizing under the same mixed binder contractum obligations as
`piTyCode`. -/
theorem appLamSigmaTyCode_isStronglyNormalizing_of_domain_codomain_argument_contractum
    {scope : Nat} {domain : RawTerm (scope + 1)}
    {codomain : RawTerm ((scope + 1) + 1)}
    {argumentTerm : RawTerm scope}
    (domainTerminates : IsStronglyNormalizing domain)
    (codomainTerminates : IsStronglyNormalizing codomain)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (domainContractumTerminates :
      ∀ {currentDomain : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentDomain →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentDomain currentArgument))
    (codomainContractumTerminates :
      ∀ {currentCodomain : RawTerm ((scope + 1) + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentCodomain →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst
                (RawTermSubst.lift (RawTermSubst.singleton currentArgument))
                currentCodomain)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_sigmaTyCode ()
                (.childCons domain (.childCons codomain .childNil)))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamTwoChildSecondBinderBody_isStronglyNormalizing_of_children_argument_contractum
    (wrapBody := fun currentDomain currentCodomain =>
      (.mkGen .gen_sigmaTyCode ()
        (.childCons currentDomain (.childCons currentCodomain .childNil)) :
        RawTerm (scope + 1)))
    (wrapContractum := fun domainContractum codomainContractum =>
      (.mkGen .gen_sigmaTyCode ()
        (.childCons domainContractum
          (.childCons codomainContractum .childNil)) :
        RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_sigmaTyCode bodyStep)
    (wrapContractumTerminates :=
      fun domainContractumTerminates codomainContractumTerminates =>
        sigmaTyCode_isStronglyNormalizing_of_domain_codomain
          domainContractumTerminates
          codomainContractumTerminates)
    (subst0Wrap := fun _currentDomain _currentCodomain _currentArgument =>
      rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    domainTerminates
    codomainTerminates
    argumentTerminates
    domainContractumTerminates
    codomainContractumTerminates

/-- Beta redexes whose lambda body is `polyFunctor positionType
positionFamily` are strongly normalizing under the same mixed binder
contractum obligations as the dependent type codes. -/
theorem appLamPolyFunctor_isStronglyNormalizing_of_position_type_family_argument_contractum
    {scope : Nat} {positionType : RawTerm (scope + 1)}
    {positionFamily : RawTerm ((scope + 1) + 1)}
    {argumentTerm : RawTerm scope}
    (positionTypeTerminates : IsStronglyNormalizing positionType)
    (positionFamilyTerminates : IsStronglyNormalizing positionFamily)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (positionTypeContractumTerminates :
      ∀ {currentPositionType : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentPositionType →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentPositionType currentArgument))
    (positionFamilyContractumTerminates :
      ∀ {currentPositionFamily : RawTerm ((scope + 1) + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentPositionFamily →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst
                (RawTermSubst.lift (RawTermSubst.singleton currentArgument))
                currentPositionFamily)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons
              (.mkGen .gen_unit () .childNil : RawTerm scope)
              (.childCons
              (.mkGen .gen_polyFunctor ()
                (.childCons positionType
                  (.childCons positionFamily .childNil)))
              .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamTwoChildSecondBinderBody_isStronglyNormalizing_of_children_argument_contractum
    (wrapBody := fun currentPositionType currentPositionFamily =>
      (.mkGen .gen_polyFunctor ()
        (.childCons currentPositionType
          (.childCons currentPositionFamily .childNil)) :
        RawTerm (scope + 1)))
    (wrapContractum := fun positionTypeContractum positionFamilyContractum =>
      (.mkGen .gen_polyFunctor ()
        (.childCons positionTypeContractum
          (.childCons positionFamilyContractum .childNil)) :
        RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_polyFunctor bodyStep)
    (wrapContractumTerminates :=
      fun positionTypeContractumTerminates
          positionFamilyContractumTerminates =>
        polyFunctor_isStronglyNormalizing_of_position_type_family
          positionTypeContractumTerminates
          positionFamilyContractumTerminates)
    (subst0Wrap :=
      fun _currentPositionType _currentPositionFamily _currentArgument =>
        rfl)
    (domainAnnTerminates := unit_isStronglyNormalizing)
    positionTypeTerminates
    positionFamilyTerminates
    argumentTerminates
    positionTypeContractumTerminates
    positionFamilyContractumTerminates

/-- Beta redexes whose lambda body is `pathLam body` are strongly normalizing
when the path body, argument, and every binder-lifted body contractum are
strongly normalizing.

Unlike the same-scope one-child helper, beta substitution crosses the
`pathLam` binder, so the child contractum uses the lifted singleton
substitution. -/
theorem appLamPathLam_isStronglyNormalizing_of_body_argument_contractum
    {scope : Nat} {domainAnn : RawTerm scope}
    {pathBody : RawTerm ((scope + 1) + 1)}
    {argumentTerm : RawTerm scope}
    (domainAnnTerminates : IsStronglyNormalizing domainAnn)
    (pathBodyTerminates : IsStronglyNormalizing pathBody)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (pathBodyContractumTerminates :
      ∀ {currentPathBody : RawTerm ((scope + 1) + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentPathBody →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst
                (RawTermSubst.lift (RawTermSubst.singleton currentArgument))
                currentPathBody)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons domainAnn
              (.childCons
                (.mkGen .gen_pathLam ()
                  (.childCons pathBody .childNil))
                .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentDomain =>
      ∀ {currentPathBody : RawTerm ((scope + 1) + 1)},
        IsStronglyNormalizing currentPathBody →
        ∀ {currentArgument : RawTerm scope},
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_lam ()
                    (.childCons currentDomain
                      (.childCons
                        (.mkGen .gen_pathLam ()
                          (.childCons currentPathBody .childNil))
                        .childNil)))
                  (.childCons currentArgument .childNil)) :
                RawTerm scope))
    (m := fun currentDomain currentDomainSuccessors domainIH => by
      intro currentPathBody currentPathBodyTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun currentPathBody =>
            ∀ {currentArgument : RawTerm scope},
              IsStronglyNormalizing currentArgument →
                IsStronglyNormalizing
                  (.mkGen .gen_app ()
                    (.childCons
                      (.mkGen .gen_lam ()
                        (.childCons currentDomain
                          (.childCons
                            (.mkGen .gen_pathLam ()
                              (.childCons currentPathBody .childNil))
                            .childNil)))
                      (.childCons currentArgument .childNil)) :
                    RawTerm scope))
          (m := fun currentPathBody currentPathBodySuccessors pathBodyIH => by
            intro currentArgument currentArgumentTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerArgument =>
                  IsStronglyNormalizing
                    (.mkGen .gen_app ()
                      (.childCons
                        (.mkGen .gen_lam ()
                          (.childCons currentDomain
                            (.childCons
                              (.mkGen .gen_pathLam ()
                                (.childCons currentPathBody .childNil))
                              .childNil)))
                        (.childCons innerArgument .childNil)) :
                      RawTerm scope))
                (m := fun currentArgument currentArgumentSuccessors
                    argumentIH =>
                  Acc.intro
                    (.mkGen .gen_app ()
                      (.childCons
                        (.mkGen .gen_lam ()
                          (.childCons currentDomain
                            (.childCons
                              (.mkGen .gen_pathLam ()
                                (.childCons currentPathBody .childNil))
                              .childNil)))
                        (.childCons currentArgument .childNil)) :
                      RawTerm scope)
                    (fun targetTerm applicationStep => by
                      cases Step.from_app applicationStep with
                      | inl betaBranch =>
                          obtain ⟨lambdaDomain, lambdaBody, lambdaEq,
                            targetEq⟩ := betaBranch
                          cases lambdaEq
                          rw [targetEq]
                          exact
                            pathLam_isStronglyNormalizing_of_body
                              (pathBodyContractumTerminates
                                (Acc.intro currentPathBody
                                  currentPathBodySuccessors)
                                (Acc.intro currentArgument
                                  currentArgumentSuccessors))
                      | inr congruenceBranch =>
                          cases congruenceBranch with
                          | inl functionBranch =>
                              obtain ⟨functionAfter, targetEq, functionStep⟩ :=
                                functionBranch
                              cases Step.from_lam functionStep with
                              | inl domainBranch =>
                                  obtain ⟨domainAfter, functionAfterEq,
                                    domainStep⟩ := domainBranch
                                  rw [targetEq, functionAfterEq]
                                  exact
                                    domainIH domainAfter domainStep
                                      (Acc.intro currentPathBody
                                        currentPathBodySuccessors)
                                      (Acc.intro currentArgument
                                        currentArgumentSuccessors)
                              | inr bodyBranch =>
                                  obtain ⟨bodyAfter, functionAfterEq,
                                    bodyStep⟩ := bodyBranch
                                  obtain ⟨pathBodyAfter, bodyAfterEq,
                                    pathBodyStep⟩ := Step.from_pathLam bodyStep
                                  rw [targetEq, functionAfterEq, bodyAfterEq]
                                  exact
                                    pathBodyIH pathBodyAfter pathBodyStep
                                      (Acc.intro currentArgument
                                        currentArgumentSuccessors)
                          | inr argumentBranch =>
                              obtain ⟨argumentAfter, targetEq, argumentStep⟩ :=
                                argumentBranch
                              rw [targetEq]
                              exact argumentIH argumentAfter argumentStep))
                currentArgumentTerminates)
          currentPathBodyTerminates))
    domainAnnTerminates)
    pathBodyTerminates
    argumentTerminates

/-- Beta redexes whose lambda body is another `lam body` are strongly
normalizing when the inner body, argument, and every binder-lifted body
contractum are strongly normalizing.

This is the ordinary lambda sibling of the `pathLam` endpoint above: beta
substitution crosses the inner lambda binder, so the body contractum uses the
lifted singleton substitution. -/
theorem appLamLam_isStronglyNormalizing_of_body_argument_contractum
    {scope : Nat} {domainAnn : RawTerm scope}
    {innerDomain : RawTerm (scope + 1)} {innerBody : RawTerm ((scope + 1) + 1)}
    {argumentTerm : RawTerm scope}
    (domainAnnTerminates : IsStronglyNormalizing domainAnn)
    (innerDomainTerminates : IsStronglyNormalizing innerDomain)
    (innerBodyTerminates : IsStronglyNormalizing innerBody)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (innerDomainContractumTerminates :
      ∀ {currentInnerDomain : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentInnerDomain →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentInnerDomain currentArgument))
    (innerBodyContractumTerminates :
      ∀ {currentInnerBody : RawTerm ((scope + 1) + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentInnerBody →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst
                (RawTermSubst.lift (RawTermSubst.singleton currentArgument))
                currentInnerBody)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons domainAnn
              (.childCons
                (.mkGen .gen_lam ()
                  (.childCons innerDomain (.childCons innerBody .childNil)))
                .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLamTwoChildSecondBinderBody_isStronglyNormalizing_of_children_argument_contractum
    (wrapBody := fun currentInnerDomain currentInnerBody =>
      (.mkGen .gen_lam ()
        (.childCons currentInnerDomain
          (.childCons currentInnerBody .childNil)) :
        RawTerm (scope + 1)))
    (wrapContractum := fun innerDomainContractum innerBodyContractum =>
      (.mkGen .gen_lam ()
        (.childCons innerDomainContractum
          (.childCons innerBodyContractum .childNil)) :
        RawTerm scope))
    (fromWrapStep := fun bodyStep => Step.from_lam bodyStep)
    (wrapContractumTerminates :=
      fun innerDomainContractumTerminates innerBodyContractumTerminates =>
        lam_isStronglyNormalizing_of_body
          innerDomainContractumTerminates
          innerBodyContractumTerminates)
    (subst0Wrap := fun _currentInnerDomain _currentInnerBody _currentArgument =>
      rfl)
    (domainAnnTerminates := domainAnnTerminates)
    innerDomainTerminates
    innerBodyTerminates
    argumentTerminates
    innerDomainContractumTerminates
    innerBodyContractumTerminates

/-- Beta redexes whose lambda body is `diffLambda body` are strongly
normalizing when the differential-lambda body, argument, and every
binder-lifted body contractum are strongly normalizing.

`gen_diffLambda` mirrors the ordinary lambda binder at the raw substrate
level, so beta substitution crosses its binder by lifting the singleton
substitution. -/
theorem appLamDiffLambda_isStronglyNormalizing_of_body_argument_contractum
    {scope : Nat} {domainAnn : RawTerm scope}
    {diffBody : RawTerm ((scope + 1) + 1)}
    {argumentTerm : RawTerm scope}
    (domainAnnTerminates : IsStronglyNormalizing domainAnn)
    (diffBodyTerminates : IsStronglyNormalizing diffBody)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (diffBodyContractumTerminates :
      ∀ {currentDiffBody : RawTerm ((scope + 1) + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentDiffBody →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst
                (RawTermSubst.lift (RawTermSubst.singleton currentArgument))
                currentDiffBody)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam ()
            (.childCons domainAnn
              (.childCons
                (.mkGen .gen_diffLambda ()
                  (.childCons diffBody .childNil))
                .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentDomain =>
      ∀ {currentDiffBody : RawTerm ((scope + 1) + 1)},
        IsStronglyNormalizing currentDiffBody →
        ∀ {currentArgument : RawTerm scope},
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_lam ()
                    (.childCons currentDomain
                      (.childCons
                        (.mkGen .gen_diffLambda ()
                          (.childCons currentDiffBody .childNil))
                        .childNil)))
                  (.childCons currentArgument .childNil)) :
                RawTerm scope))
    (m := fun currentDomain currentDomainSuccessors domainIH => by
      intro currentDiffBody currentDiffBodyTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun currentDiffBody =>
            ∀ {currentArgument : RawTerm scope},
              IsStronglyNormalizing currentArgument →
                IsStronglyNormalizing
                  (.mkGen .gen_app ()
                    (.childCons
                      (.mkGen .gen_lam ()
                        (.childCons currentDomain
                          (.childCons
                            (.mkGen .gen_diffLambda ()
                              (.childCons currentDiffBody .childNil))
                            .childNil)))
                      (.childCons currentArgument .childNil)) :
                    RawTerm scope))
          (m := fun currentDiffBody currentDiffBodySuccessors diffBodyIH => by
            intro currentArgument currentArgumentTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerArgument =>
                  IsStronglyNormalizing
                    (.mkGen .gen_app ()
                      (.childCons
                        (.mkGen .gen_lam ()
                          (.childCons currentDomain
                            (.childCons
                              (.mkGen .gen_diffLambda ()
                                (.childCons currentDiffBody .childNil))
                              .childNil)))
                        (.childCons innerArgument .childNil)) :
                      RawTerm scope))
                (m := fun currentArgument currentArgumentSuccessors
                    argumentIH =>
                  Acc.intro
                    (.mkGen .gen_app ()
                      (.childCons
                        (.mkGen .gen_lam ()
                          (.childCons currentDomain
                            (.childCons
                              (.mkGen .gen_diffLambda ()
                                (.childCons currentDiffBody .childNil))
                              .childNil)))
                        (.childCons currentArgument .childNil)) :
                      RawTerm scope)
                    (fun targetTerm applicationStep => by
                      cases Step.from_app applicationStep with
                      | inl betaBranch =>
                          obtain ⟨lambdaDomain, lambdaBody, lambdaEq,
                            targetEq⟩ := betaBranch
                          cases lambdaEq
                          rw [targetEq]
                          exact
                            diffLambda_isStronglyNormalizing_of_body
                              (diffBodyContractumTerminates
                                (Acc.intro currentDiffBody
                                  currentDiffBodySuccessors)
                                (Acc.intro currentArgument
                                  currentArgumentSuccessors))
                      | inr congruenceBranch =>
                          cases congruenceBranch with
                          | inl functionBranch =>
                              obtain ⟨functionAfter, targetEq, functionStep⟩ :=
                                functionBranch
                              cases Step.from_lam functionStep with
                              | inl domainBranch =>
                                  obtain ⟨domainAfter, functionAfterEq,
                                    domainStep⟩ := domainBranch
                                  rw [targetEq, functionAfterEq]
                                  exact
                                    domainIH domainAfter domainStep
                                      (Acc.intro currentDiffBody
                                        currentDiffBodySuccessors)
                                      (Acc.intro currentArgument
                                        currentArgumentSuccessors)
                              | inr bodyBranch =>
                                  obtain ⟨bodyAfter, functionAfterEq,
                                    bodyStep⟩ := bodyBranch
                                  obtain ⟨diffBodyAfter, bodyAfterEq,
                                    diffBodyStep⟩ := Step.from_diffLambda bodyStep
                                  rw [targetEq, functionAfterEq, bodyAfterEq]
                                  exact
                                    diffBodyIH diffBodyAfter diffBodyStep
                                      (Acc.intro currentArgument
                                        currentArgumentSuccessors)
                          | inr argumentBranch =>
                              obtain ⟨argumentAfter, targetEq, argumentStep⟩ :=
                                argumentBranch
                              rw [targetEq]
                              exact argumentIH argumentAfter argumentStep))
                currentArgumentTerminates)
          currentDiffBodyTerminates))
    domainAnnTerminates)
    diffBodyTerminates
    argumentTerminates

/-- Beta redexes are strongly normalizing when the lambda body and argument are
strongly normalizing and every reduct pair has a strongly-normalizing beta
contractum.

This is the lambda-headed application counterpart to the neutral-spine
theorems.  It deliberately exposes the reducibility obligation as
`contractumTerminates`: a future Tait predicate must prove that
`subst0 currentBody currentArgument` terminates for every body/argument reduct.
The theorem itself handles the operational shell: the root beta step,
congruence in the lambda body, and congruence in the argument. -/
theorem appLam_isStronglyNormalizing_of_body_argument_contractum
    {scope : Nat} {domainAnn : RawTerm scope} {body : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (domainAnnTerminates : IsStronglyNormalizing domainAnn)
    (bodyTerminates : IsStronglyNormalizing body)
    (argumentTerminates : IsStronglyNormalizing argumentTerm)
    (contractumTerminates :
      ∀ {currentBody : RawTerm (scope + 1)}
        {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentBody →
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (RawTerm.subst0 currentBody currentArgument)) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam () (.childCons domainAnn (.childCons body .childNil)))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentDomain =>
      ∀ {currentBody : RawTerm (scope + 1)},
        IsStronglyNormalizing currentBody →
        ∀ {currentArgument : RawTerm scope},
          IsStronglyNormalizing currentArgument →
            IsStronglyNormalizing
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_lam ()
                    (.childCons currentDomain
                      (.childCons currentBody .childNil)))
                  (.childCons currentArgument .childNil)) :
                RawTerm scope))
    (m := fun currentDomain currentDomainSuccessors domainIH => by
      intro currentBody currentBodyTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun currentBody =>
            ∀ {currentArgument : RawTerm scope},
              IsStronglyNormalizing currentArgument →
                IsStronglyNormalizing
                  (.mkGen .gen_app ()
                    (.childCons
                      (.mkGen .gen_lam ()
                        (.childCons currentDomain
                          (.childCons currentBody .childNil)))
                      (.childCons currentArgument .childNil)) :
                    RawTerm scope))
          (m := fun currentBody currentBodySuccessors bodyIH => by
            intro currentArgument currentArgumentTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerArgument =>
                  IsStronglyNormalizing
                    (.mkGen .gen_app ()
                      (.childCons
                        (.mkGen .gen_lam ()
                          (.childCons currentDomain
                            (.childCons currentBody .childNil)))
                        (.childCons innerArgument .childNil)) :
                      RawTerm scope))
                (m := fun currentArgument currentArgumentSuccessors
                    argumentIH =>
                  Acc.intro
                    (.mkGen .gen_app ()
                      (.childCons
                        (.mkGen .gen_lam ()
                          (.childCons currentDomain
                            (.childCons currentBody .childNil)))
                        (.childCons currentArgument .childNil)) :
                      RawTerm scope)
                    (fun targetTerm applicationStep => by
                      cases Step.from_app applicationStep with
                      | inl betaBranch =>
                          obtain ⟨lambdaDomain, lambdaBody, lambdaEq,
                            targetEq⟩ := betaBranch
                          cases lambdaEq
                          rw [targetEq]
                          exact
                            contractumTerminates
                              (Acc.intro currentBody currentBodySuccessors)
                              (Acc.intro currentArgument
                                currentArgumentSuccessors)
                      | inr congruenceBranch =>
                          cases congruenceBranch with
                          | inl functionBranch =>
                              obtain ⟨functionAfter, targetEq, functionStep⟩ :=
                                functionBranch
                              cases Step.from_lam functionStep with
                              | inl domainBranch =>
                                  obtain ⟨domainAfter, functionAfterEq,
                                    domainStep⟩ := domainBranch
                                  rw [targetEq, functionAfterEq]
                                  exact
                                    domainIH domainAfter domainStep
                                      (Acc.intro currentBody
                                        currentBodySuccessors)
                                      (Acc.intro currentArgument
                                        currentArgumentSuccessors)
                              | inr bodyBranch =>
                                  obtain ⟨bodyAfter, functionAfterEq,
                                    bodyStep⟩ := bodyBranch
                                  rw [targetEq, functionAfterEq]
                                  exact
                                    bodyIH bodyAfter bodyStep
                                      (Acc.intro currentArgument
                                        currentArgumentSuccessors)
                          | inr argumentBranch =>
                              obtain ⟨argumentAfter, targetEq, argumentStep⟩ :=
                                argumentBranch
                              rw [targetEq]
                              exact argumentIH argumentAfter argumentStep))
                currentArgumentTerminates)
          currentBodyTerminates))
    domainAnnTerminates)
    bodyTerminates
    argumentTerminates

/-- First projection of an explicitly-normalizing pair is strongly normalizing.

The root iota reduct is the first component.  Congruence steps inside the pair
are handled by nested accessibility induction on the two components. -/
theorem fstPair_isStronglyNormalizing_of_components {scope : Nat}
    {first second : RawTerm scope}
    (firstTerminates : IsStronglyNormalizing first)
    (secondTerminates : IsStronglyNormalizing second) :
    IsStronglyNormalizing
      (.mkGen .gen_fst ()
        (.childCons
          (.mkGen .gen_pair ()
            (.childCons first (.childCons second .childNil)))
          .childNil) : RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentFirst =>
      ∀ {currentSecond : RawTerm scope},
        IsStronglyNormalizing currentSecond →
          IsStronglyNormalizing
            (.mkGen .gen_fst ()
              (.childCons
                (.mkGen .gen_pair ()
                  (.childCons currentFirst
                    (.childCons currentSecond .childNil)))
                .childNil) : RawTerm scope))
    (m := fun currentFirst currentFirstSuccessors firstChildIH => by
      intro currentSecond currentSecondTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerSecond =>
            IsStronglyNormalizing
              (.mkGen .gen_fst ()
                (.childCons
                  (.mkGen .gen_pair ()
                    (.childCons currentFirst
                      (.childCons innerSecond .childNil)))
                  .childNil) : RawTerm scope))
          (m := fun currentSecond currentSecondSuccessors secondChildIH =>
            Acc.intro
              (.mkGen .gen_fst ()
                (.childCons
                  (.mkGen .gen_pair ()
                    (.childCons currentFirst
                      (.childCons currentSecond .childNil)))
                  .childNil) : RawTerm scope)
              (fun targetTerm parentStep => by
                cases Step.from_fst parentStep with
                | inl iotaBranch =>
                    obtain ⟨firstValue, secondValue, pairEq, targetEq⟩ :=
                      iotaBranch
                    cases pairEq
                    rw [targetEq]
                    exact Acc.intro currentFirst currentFirstSuccessors
                | inr congBranch =>
                    obtain ⟨argAfter, targetEq, pairStep⟩ := congBranch
                    cases Step.from_pair pairStep with
                    | inl firstBranch =>
                        obtain ⟨firstAfter, pairEq, firstStep⟩ := firstBranch
                        rw [targetEq, pairEq]
                        exact firstChildIH firstAfter firstStep
                          (Acc.intro currentSecond currentSecondSuccessors)
                    | inr secondBranch =>
                        obtain ⟨secondAfter, pairEq, secondStep⟩ :=
                          secondBranch
                        rw [targetEq, pairEq]
                        exact secondChildIH secondAfter secondStep))
          currentSecondTerminates)
    firstTerminates)
    secondTerminates

/-- Second projection of an explicitly-normalizing pair is strongly
normalizing.  Symmetric to `fstPair_isStronglyNormalizing_of_components`, with
the root iota reduct selecting the second component. -/
theorem sndPair_isStronglyNormalizing_of_components {scope : Nat}
    {first second : RawTerm scope}
    (firstTerminates : IsStronglyNormalizing first)
    (secondTerminates : IsStronglyNormalizing second) :
    IsStronglyNormalizing
      (.mkGen .gen_snd ()
        (.childCons
          (.mkGen .gen_pair ()
            (.childCons first (.childCons second .childNil)))
          .childNil) : RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentFirst =>
      ∀ {currentSecond : RawTerm scope},
        IsStronglyNormalizing currentSecond →
          IsStronglyNormalizing
            (.mkGen .gen_snd ()
              (.childCons
                (.mkGen .gen_pair ()
                  (.childCons currentFirst
                    (.childCons currentSecond .childNil)))
                .childNil) : RawTerm scope))
    (m := fun currentFirst currentFirstSuccessors firstChildIH => by
      intro currentSecond currentSecondTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerSecond =>
            IsStronglyNormalizing
              (.mkGen .gen_snd ()
                (.childCons
                  (.mkGen .gen_pair ()
                    (.childCons currentFirst
                      (.childCons innerSecond .childNil)))
                  .childNil) : RawTerm scope))
          (m := fun currentSecond currentSecondSuccessors secondChildIH =>
            Acc.intro
              (.mkGen .gen_snd ()
                (.childCons
                  (.mkGen .gen_pair ()
                    (.childCons currentFirst
                      (.childCons currentSecond .childNil)))
                  .childNil) : RawTerm scope)
              (fun targetTerm parentStep => by
                cases Step.from_snd parentStep with
                | inl iotaBranch =>
                    obtain ⟨firstValue, secondValue, pairEq, targetEq⟩ :=
                      iotaBranch
                    cases pairEq
                    rw [targetEq]
                    exact Acc.intro currentSecond currentSecondSuccessors
                | inr congBranch =>
                    obtain ⟨argAfter, targetEq, pairStep⟩ := congBranch
                    cases Step.from_pair pairStep with
                    | inl firstBranch =>
                        obtain ⟨firstAfter, pairEq, firstStep⟩ := firstBranch
                        rw [targetEq, pairEq]
                        exact firstChildIH firstAfter firstStep
                          (Acc.intro currentSecond currentSecondSuccessors)
                    | inr secondBranch =>
                        obtain ⟨secondAfter, pairEq, secondStep⟩ :=
                          secondBranch
                        rw [targetEq, pairEq]
                        exact secondChildIH secondAfter secondStep))
          currentSecondTerminates)
    firstTerminates)
    secondTerminates

/-- Boolean elimination on the literal `true` is strongly normalizing when the
motive and both branches are strongly normalizing.

The root iota reduct is the then-branch.  Congruence at the scrutinee is
impossible because `boolTrue` is a normal leaf; congruence in the motive or
either branch is handled by nested accessibility induction (motive outer,
then-branch, else-branch innermost).  Phase-Z motive shape: the children spine
is `(motive, thenBranch, elseBranch, boolTrue)`. -/
theorem boolElimTrue_isStronglyNormalizing_of_branches {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {thenBranch elseBranch : RawTerm scope}
    (motiveTerminates : IsStronglyNormalizing motive)
    (thenTerminates : IsStronglyNormalizing thenBranch)
    (elseTerminates : IsStronglyNormalizing elseBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_boolElim ()
        (.childCons motive
          (.childCons thenBranch
            (.childCons elseBranch
              (.childCons (.mkGen .gen_boolTrue () .childNil) .childNil)))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentMotive =>
      ∀ {currentThen currentElse : RawTerm scope},
        IsStronglyNormalizing currentThen → IsStronglyNormalizing currentElse →
          IsStronglyNormalizing
            (.mkGen .gen_boolElim ()
              (.childCons currentMotive
                (.childCons currentThen
                  (.childCons currentElse
                    (.childCons (.mkGen .gen_boolTrue () .childNil) .childNil)))) :
              RawTerm scope))
    (m := fun currentMotive currentMotiveSuccessors motiveBranchIH => by
      intro currentThen currentElse currentThenTerminates currentElseTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerThen =>
            ∀ {innerElse : RawTerm scope},
              IsStronglyNormalizing innerElse →
                IsStronglyNormalizing
                  (.mkGen .gen_boolElim ()
                    (.childCons currentMotive
                      (.childCons innerThen
                        (.childCons innerElse
                          (.childCons (.mkGen .gen_boolTrue () .childNil) .childNil)))) :
                    RawTerm scope))
          (m := fun currentThen currentThenSuccessors thenBranchIH => by
            intro innerElse innerElseTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerElse' =>
                  IsStronglyNormalizing
                    (.mkGen .gen_boolElim ()
                      (.childCons currentMotive
                        (.childCons currentThen
                          (.childCons innerElse'
                            (.childCons (.mkGen .gen_boolTrue () .childNil) .childNil)))) :
                      RawTerm scope))
                (m := fun currentElse currentElseSuccessors elseBranchIH =>
                  Acc.intro
                    (.mkGen .gen_boolElim ()
                      (.childCons currentMotive
                        (.childCons currentThen
                          (.childCons currentElse
                            (.childCons (.mkGen .gen_boolTrue () .childNil) .childNil)))) :
                      RawTerm scope)
                    (fun targetTerm parentStep => by
                      cases Step.from_boolElim parentStep with
                      | inl trueBranch =>
                          obtain ⟨_, targetEq⟩ := trueBranch
                          rw [targetEq]
                          exact Acc.intro currentThen currentThenSuccessors
                      | inr restAfterTrue =>
                          cases restAfterTrue with
                          | inl falseBranch =>
                              obtain ⟨scrutineeEq, _⟩ := falseBranch
                              cases scrutineeEq
                          | inr restAfterFalse =>
                              cases restAfterFalse with
                              | inl motiveStepBranch =>
                                  obtain ⟨motiveAfter, targetEq, motiveStep⟩ :=
                                    motiveStepBranch
                                  rw [targetEq]
                                  exact motiveBranchIH motiveAfter motiveStep
                                    (Acc.intro currentThen currentThenSuccessors)
                                    (Acc.intro currentElse currentElseSuccessors)
                              | inr restAfterMotive =>
                                  cases restAfterMotive with
                                  | inl thenBranchStep =>
                                      obtain ⟨thenAfter, targetEq, thenStep⟩ :=
                                        thenBranchStep
                                      rw [targetEq]
                                      exact thenBranchIH thenAfter thenStep
                                        (Acc.intro currentElse currentElseSuccessors)
                                  | inr restAfterThen =>
                                      cases restAfterThen with
                                      | inl elseBranchStep =>
                                          obtain ⟨elseAfter, targetEq, elseStep⟩ :=
                                            elseBranchStep
                                          rw [targetEq]
                                          exact elseBranchIH elseAfter elseStep
                                      | inr scrutineeBranch =>
                                          obtain ⟨_, _, scrutineeStep⟩ := scrutineeBranch
                                          exact False.elim (noStep_boolTrue scrutineeStep)))
                innerElseTerminates)
          currentThenTerminates currentElseTerminates))
    motiveTerminates)
    thenTerminates elseTerminates

/-- Boolean elimination on the literal `false` is strongly normalizing when
the motive and both branches are strongly normalizing.  Symmetric to the `true`
case, with the root iota reduct selecting the else-branch.  Phase-Z motive shape:
the children spine is `(motive, thenBranch, elseBranch, boolFalse)`. -/
theorem boolElimFalse_isStronglyNormalizing_of_branches {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {thenBranch elseBranch : RawTerm scope}
    (motiveTerminates : IsStronglyNormalizing motive)
    (thenTerminates : IsStronglyNormalizing thenBranch)
    (elseTerminates : IsStronglyNormalizing elseBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_boolElim ()
        (.childCons motive
          (.childCons thenBranch
            (.childCons elseBranch
              (.childCons (.mkGen .gen_boolFalse () .childNil) .childNil)))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentMotive =>
      ∀ {currentThen currentElse : RawTerm scope},
        IsStronglyNormalizing currentThen → IsStronglyNormalizing currentElse →
          IsStronglyNormalizing
            (.mkGen .gen_boolElim ()
              (.childCons currentMotive
                (.childCons currentThen
                  (.childCons currentElse
                    (.childCons (.mkGen .gen_boolFalse () .childNil) .childNil)))) :
              RawTerm scope))
    (m := fun currentMotive currentMotiveSuccessors motiveBranchIH => by
      intro currentThen currentElse currentThenTerminates currentElseTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerThen =>
            ∀ {innerElse : RawTerm scope},
              IsStronglyNormalizing innerElse →
                IsStronglyNormalizing
                  (.mkGen .gen_boolElim ()
                    (.childCons currentMotive
                      (.childCons innerThen
                        (.childCons innerElse
                          (.childCons (.mkGen .gen_boolFalse () .childNil) .childNil)))) :
                    RawTerm scope))
          (m := fun currentThen currentThenSuccessors thenBranchIH => by
            intro innerElse innerElseTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerElse' =>
                  IsStronglyNormalizing
                    (.mkGen .gen_boolElim ()
                      (.childCons currentMotive
                        (.childCons currentThen
                          (.childCons innerElse'
                            (.childCons (.mkGen .gen_boolFalse () .childNil) .childNil)))) :
                      RawTerm scope))
                (m := fun currentElse currentElseSuccessors elseBranchIH =>
                  Acc.intro
                    (.mkGen .gen_boolElim ()
                      (.childCons currentMotive
                        (.childCons currentThen
                          (.childCons currentElse
                            (.childCons (.mkGen .gen_boolFalse () .childNil) .childNil)))) :
                      RawTerm scope)
                    (fun targetTerm parentStep => by
                      cases Step.from_boolElim parentStep with
                      | inl trueBranch =>
                          obtain ⟨scrutineeEq, _⟩ := trueBranch
                          cases scrutineeEq
                      | inr restAfterTrue =>
                          cases restAfterTrue with
                          | inl falseBranch =>
                              obtain ⟨_, targetEq⟩ := falseBranch
                              rw [targetEq]
                              exact Acc.intro currentElse currentElseSuccessors
                          | inr restAfterFalse =>
                              cases restAfterFalse with
                              | inl motiveStepBranch =>
                                  obtain ⟨motiveAfter, targetEq, motiveStep⟩ :=
                                    motiveStepBranch
                                  rw [targetEq]
                                  exact motiveBranchIH motiveAfter motiveStep
                                    (Acc.intro currentThen currentThenSuccessors)
                                    (Acc.intro currentElse currentElseSuccessors)
                              | inr restAfterMotive =>
                                  cases restAfterMotive with
                                  | inl thenBranchStep =>
                                      obtain ⟨thenAfter, targetEq, thenStep⟩ :=
                                        thenBranchStep
                                      rw [targetEq]
                                      exact thenBranchIH thenAfter thenStep
                                        (Acc.intro currentElse currentElseSuccessors)
                                  | inr restAfterThen =>
                                      cases restAfterThen with
                                      | inl elseBranchStep =>
                                          obtain ⟨elseAfter, targetEq, elseStep⟩ :=
                                            elseBranchStep
                                          rw [targetEq]
                                          exact elseBranchIH elseAfter elseStep
                                      | inr scrutineeBranch =>
                                          obtain ⟨_, _, scrutineeStep⟩ := scrutineeBranch
                                          exact False.elim (noStep_boolFalse scrutineeStep)))
                innerElseTerminates)
          currentThenTerminates currentElseTerminates))
    motiveTerminates)
    thenTerminates elseTerminates

/-- Identity elimination on a reflexivity witness is strongly normalizing when
the base case and raw witness are strongly normalizing.

The root iota reduct is the base case.  Congruence in the base case is handled
directly, while congruence in the reflexivity witness is inverted through
`Step.from_refl` before reusing the witness accessibility induction. -/
theorem idJRefl_isStronglyNormalizing_of_base_witness {scope : Nat}
    {baseCase rawWitness : RawTerm scope}
    (baseTerminates : IsStronglyNormalizing baseCase)
    (witnessTerminates : IsStronglyNormalizing rawWitness) :
    IsStronglyNormalizing
      (.mkGen .gen_idJ ()
        (.childCons baseCase
          (.childCons
            (.mkGen .gen_refl () (.childCons rawWitness .childNil))
            .childNil)) : RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentBase =>
      ∀ {currentWitness : RawTerm scope},
        IsStronglyNormalizing currentWitness →
          IsStronglyNormalizing
            (.mkGen .gen_idJ ()
              (.childCons currentBase
                (.childCons
                  (.mkGen .gen_refl ()
                    (.childCons currentWitness .childNil))
                  .childNil)) : RawTerm scope))
    (m := fun currentBase currentBaseSuccessors baseCaseIH => by
      intro currentWitness currentWitnessTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerWitness =>
            IsStronglyNormalizing
              (.mkGen .gen_idJ ()
                (.childCons currentBase
                  (.childCons
                    (.mkGen .gen_refl ()
                      (.childCons innerWitness .childNil))
                    .childNil)) : RawTerm scope))
          (m := fun currentWitness currentWitnessSuccessors witnessIH =>
            Acc.intro
              (.mkGen .gen_idJ ()
                (.childCons currentBase
                  (.childCons
                    (.mkGen .gen_refl ()
                      (.childCons currentWitness .childNil))
                    .childNil)) : RawTerm scope)
              (fun targetTerm parentStep => by
                cases Step.from_idJ parentStep with
                | inl iotaBranch =>
                    obtain ⟨iotaWitness, witnessEq, targetEq⟩ := iotaBranch
                    cases witnessEq
                    rw [targetEq]
                    exact Acc.intro currentBase currentBaseSuccessors
                | inr restAfterIota =>
                    cases restAfterIota with
                    | inl baseBranch =>
                        obtain ⟨baseAfter, targetEq, baseStep⟩ := baseBranch
                        rw [targetEq]
                        exact baseCaseIH baseAfter baseStep
                          (Acc.intro currentWitness currentWitnessSuccessors)
                    | inr witnessBranch =>
                        obtain ⟨witnessAfter, targetEq, witnessStep⟩ :=
                          witnessBranch
                        obtain
                          ⟨rawWitnessAfter, witnessAfterEq,
                            rawWitnessStep⟩ := Step.from_refl witnessStep
                        rw [targetEq, witnessAfterEq]
                        exact witnessIH rawWitnessAfter rawWitnessStep))
          currentWitnessTerminates)
    baseTerminates)
    witnessTerminates

/-- Strict identity recursion on a reflexivity witness is strongly normalizing
when the base case and raw witness are strongly normalizing.

This is the strict-recursion sibling of
`idJRefl_isStronglyNormalizing_of_base_witness`; the substrate reduction shape
is identical, but the outer generator is `gen_idStrictRec`. -/
theorem idStrictRecRefl_isStronglyNormalizing_of_base_witness {scope : Nat}
    {baseCase rawWitness : RawTerm scope}
    (baseTerminates : IsStronglyNormalizing baseCase)
    (witnessTerminates : IsStronglyNormalizing rawWitness) :
    IsStronglyNormalizing
      (.mkGen .gen_idStrictRec ()
        (.childCons baseCase
          (.childCons
            (.mkGen .gen_refl () (.childCons rawWitness .childNil))
            .childNil)) : RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentBase =>
      ∀ {currentWitness : RawTerm scope},
        IsStronglyNormalizing currentWitness →
          IsStronglyNormalizing
            (.mkGen .gen_idStrictRec ()
              (.childCons currentBase
                (.childCons
                  (.mkGen .gen_refl ()
                    (.childCons currentWitness .childNil))
                  .childNil)) : RawTerm scope))
    (m := fun currentBase currentBaseSuccessors baseCaseIH => by
      intro currentWitness currentWitnessTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerWitness =>
            IsStronglyNormalizing
              (.mkGen .gen_idStrictRec ()
                (.childCons currentBase
                  (.childCons
                    (.mkGen .gen_refl ()
                      (.childCons innerWitness .childNil))
                    .childNil)) : RawTerm scope))
          (m := fun currentWitness currentWitnessSuccessors witnessIH =>
            Acc.intro
              (.mkGen .gen_idStrictRec ()
                (.childCons currentBase
                  (.childCons
                    (.mkGen .gen_refl ()
                      (.childCons currentWitness .childNil))
                    .childNil)) : RawTerm scope)
              (fun targetTerm parentStep => by
                cases Step.from_idStrictRec parentStep with
                | inl iotaBranch =>
                    obtain ⟨iotaWitness, witnessEq, targetEq⟩ := iotaBranch
                    cases witnessEq
                    rw [targetEq]
                    exact Acc.intro currentBase currentBaseSuccessors
                | inr restAfterIota =>
                    cases restAfterIota with
                    | inl baseBranch =>
                        obtain ⟨baseAfter, targetEq, baseStep⟩ := baseBranch
                        rw [targetEq]
                        exact baseCaseIH baseAfter baseStep
                          (Acc.intro currentWitness currentWitnessSuccessors)
                    | inr witnessBranch =>
                        obtain ⟨witnessAfter, targetEq, witnessStep⟩ :=
                          witnessBranch
                        obtain
                          ⟨rawWitnessAfter, witnessAfterEq,
                            rawWitnessStep⟩ := Step.from_refl witnessStep
                        rw [targetEq, witnessAfterEq]
                        exact witnessIH rawWitnessAfter rawWitnessStep))
          currentWitnessTerminates)
    baseTerminates)
    witnessTerminates

/-- Shared accessibility lift for projection-shaped eliminator redexes with
two reducible branches.

The parent may reduce at the root to the selected branch, or by congruence in
one of the two branches.  Scrutinee congruence and non-selected root cases are
filtered out by the caller's inversion function. -/
theorem isStronglyNormalizing_of_twoBranchProjectionRedex {scope : Nat}
    (wrapParent : RawTerm scope → RawTerm scope → RawTerm scope)
    (invertParentStep :
      ∀ {selectedBranch otherBranch targetParent : RawTerm scope},
        Step (wrapParent selectedBranch otherBranch) targetParent →
          (targetParent = selectedBranch)
          ∨
          (∃ selectedAfter : RawTerm scope,
            targetParent = wrapParent selectedAfter otherBranch ∧
              Step selectedBranch selectedAfter)
          ∨
          (∃ otherAfter : RawTerm scope,
            targetParent = wrapParent selectedBranch otherAfter ∧
              Step otherBranch otherAfter))
    {selectedBranch otherBranch : RawTerm scope}
    (selectedTerminates : IsStronglyNormalizing selectedBranch)
    (otherTerminates : IsStronglyNormalizing otherBranch) :
    IsStronglyNormalizing (wrapParent selectedBranch otherBranch) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentSelected =>
      ∀ {currentOther : RawTerm scope},
        IsStronglyNormalizing currentOther →
          IsStronglyNormalizing (wrapParent currentSelected currentOther))
    (m := fun currentSelected currentSelectedSuccessors selectedBranchIH => by
      intro currentOther currentOtherTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerOther =>
            IsStronglyNormalizing (wrapParent currentSelected innerOther))
          (m := fun currentOther currentOtherSuccessors otherBranchIH =>
            Acc.intro (wrapParent currentSelected currentOther)
              (fun targetParent parentStep => by
                cases invertParentStep parentStep with
                | inl targetEq =>
                    rw [targetEq]
                    exact
                      Acc.intro currentSelected currentSelectedSuccessors
                | inr restAfterRoot =>
                    cases restAfterRoot with
                    | inl selectedBranchStep =>
                        obtain
                          ⟨selectedAfter, targetEq, selectedStep⟩ :=
                            selectedBranchStep
                        rw [targetEq]
                        exact selectedBranchIH selectedAfter selectedStep
                          (Acc.intro currentOther currentOtherSuccessors)
                    | inr otherBranchStep =>
                        obtain ⟨otherAfter, targetEq, otherStep⟩ :=
                          otherBranchStep
                        rw [targetEq]
                        exact otherBranchIH otherAfter otherStep))
          currentOtherTerminates)
    selectedTerminates)
    otherTerminates

/-- Natural-number elimination on literal zero is strongly normalizing when
both branches are strongly normalizing.

The root iota reduct is the zero branch.  The successor iota is impossible on
the literal zero scrutinee, and scrutinee congruence is impossible because
`natZero` is a normal leaf. -/
theorem natElimZero_isStronglyNormalizing_of_branches {scope : Nat}
    {zeroBranch succBranch : RawTerm scope}
    (zeroTerminates : IsStronglyNormalizing zeroBranch)
    (succTerminates : IsStronglyNormalizing succBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_natElim ()
        (.childCons
          (.mkGen .gen_natZero () .childNil)
          (.childCons zeroBranch (.childCons succBranch .childNil))) :
        RawTerm scope) :=
  isStronglyNormalizing_of_twoBranchProjectionRedex
    (fun currentZero currentSucc =>
      (.mkGen .gen_natElim ()
        (.childCons
          (.mkGen .gen_natZero () .childNil)
          (.childCons currentZero (.childCons currentSucc .childNil))) :
        RawTerm scope))
    (fun parentStep => by
      cases Step.from_natElim parentStep with
      | inl zeroBranchStep =>
          exact Or.inl zeroBranchStep.2
      | inr restAfterZero =>
          cases restAfterZero with
          | inl succBranchStep =>
              obtain ⟨predecessor, scrutineeEq, _⟩ := succBranchStep
              cases scrutineeEq
          | inr restAfterSucc =>
              cases restAfterSucc with
              | inl scrutineeBranch =>
                  obtain ⟨_, _, scrutineeStep⟩ := scrutineeBranch
                  exact False.elim (noStep_natZero scrutineeStep)
              | inr restAfterScrutinee =>
                  cases restAfterScrutinee with
                  | inl zeroStep =>
                      obtain ⟨zeroAfter, targetEq, zeroStepInner⟩ :=
                        zeroStep
                      exact Or.inr
                        (Or.inl ⟨zeroAfter, targetEq, zeroStepInner⟩)
                  | inr succStep =>
                      obtain ⟨succAfter, targetEq, succStepInner⟩ :=
                        succStep
                      exact Or.inr
                        (Or.inr ⟨succAfter, targetEq, succStepInner⟩))
    zeroTerminates
    succTerminates

/-- Natural-number recursion on literal zero is strongly normalizing when both
branches are strongly normalizing.  This mirrors the `natElim` zero case for
the substrate's strict recursor. -/
theorem natRecZero_isStronglyNormalizing_of_branches {scope : Nat}
    {zeroBranch succBranch : RawTerm scope}
    (zeroTerminates : IsStronglyNormalizing zeroBranch)
    (succTerminates : IsStronglyNormalizing succBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_natRec ()
        (.childCons
          (.mkGen .gen_natZero () .childNil)
          (.childCons zeroBranch (.childCons succBranch .childNil))) :
        RawTerm scope) :=
  isStronglyNormalizing_of_twoBranchProjectionRedex
    (fun currentZero currentSucc =>
      (.mkGen .gen_natRec ()
        (.childCons
          (.mkGen .gen_natZero () .childNil)
          (.childCons currentZero (.childCons currentSucc .childNil))) :
        RawTerm scope))
    (fun parentStep => by
      cases Step.from_natRec parentStep with
      | inl zeroBranchStep =>
          exact Or.inl zeroBranchStep.2
      | inr restAfterZero =>
          cases restAfterZero with
          | inl succBranchStep =>
              obtain ⟨predecessor, scrutineeEq, _⟩ := succBranchStep
              cases scrutineeEq
          | inr restAfterSucc =>
              cases restAfterSucc with
              | inl scrutineeBranch =>
                  obtain ⟨_, _, scrutineeStep⟩ := scrutineeBranch
                  exact False.elim (noStep_natZero scrutineeStep)
              | inr restAfterScrutinee =>
                  cases restAfterScrutinee with
                  | inl zeroStep =>
                      obtain ⟨zeroAfter, targetEq, zeroStepInner⟩ :=
                        zeroStep
                      exact Or.inr
                        (Or.inl ⟨zeroAfter, targetEq, zeroStepInner⟩)
                  | inr succStep =>
                      obtain ⟨succAfter, targetEq, succStepInner⟩ :=
                        succStep
                      exact Or.inr
                        (Or.inr ⟨succAfter, targetEq, succStepInner⟩))
    zeroTerminates
    succTerminates

/-- Natural-number elimination on `natSucc predecessor` is strongly
normalizing when the successor branch is a neutral function head and the
recursive call on the predecessor is supplied as an explicit accessibility
hypothesis.

This is deliberately an induction-step theorem, not a global recursion proof:
the recursive obligation is visible in `recursiveCallTerminates` and will later
be discharged by the reducibility/fundamental-theorem layer.  The root iota
reduct is the two-argument application spine
`app (app succBranch predecessor) (natElim predecessor zeroBranch succBranch)`,
so beta is ruled out only by the neutral selected-branch invariant. -/
theorem natElimSucc_isStronglyNormalizing_of_neutral_succBranch
    {scope : Nat} (isNeutralHead : RawTerm scope → Prop)
    {predecessor zeroBranch succBranch : RawTerm scope}
    (predecessorTerminates : IsStronglyNormalizing predecessor)
    (zeroTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchIsNeutral : isNeutralHead succBranch)
    (neutralHeadIsNotLambda :
      ∀ {currentHead : RawTerm scope}, isNeutralHead currentHead →
        ∀ (lambdaDomain : RawTerm scope) (lambdaBody : RawTerm (scope + 1)),
          currentHead ≠ .mkGen .gen_lam ()
            (.childCons lambdaDomain (.childCons lambdaBody .childNil)))
    (neutralHeadStep :
      ∀ {currentHead targetHead : RawTerm scope},
        isNeutralHead currentHead →
          Step currentHead targetHead →
            isNeutralHead targetHead)
    (succTerminates : IsStronglyNormalizing succBranch)
    (recursiveCallTerminates :
      ∀ {currentPredecessor currentZeroBranch currentSuccBranch :
          RawTerm scope},
        IsStronglyNormalizing currentPredecessor →
          IsStronglyNormalizing currentZeroBranch →
            isNeutralHead currentSuccBranch →
              IsStronglyNormalizing currentSuccBranch →
                IsStronglyNormalizing
                  (.mkGen .gen_natElim ()
                    (.childCons currentPredecessor
                      (.childCons currentZeroBranch
                        (.childCons currentSuccBranch .childNil))) :
                    RawTerm scope)) :
    IsStronglyNormalizing
      (.mkGen .gen_natElim ()
        (.childCons
          (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
          (.childCons zeroBranch (.childCons succBranch .childNil))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentSuccBranch =>
      isNeutralHead currentSuccBranch →
        ∀ {currentPredecessor : RawTerm scope},
          IsStronglyNormalizing currentPredecessor →
            ∀ {currentZeroBranch : RawTerm scope},
              IsStronglyNormalizing currentZeroBranch →
                IsStronglyNormalizing
                  (.mkGen .gen_natElim ()
                    (.childCons
                      (.mkGen .gen_natSucc ()
                        (.childCons currentPredecessor .childNil))
                      (.childCons currentZeroBranch
                        (.childCons currentSuccBranch .childNil))) :
                    RawTerm scope))
    (m := fun currentSuccBranch currentSuccBranchSuccessors succBranchIH => by
      intro currentSuccBranchIsNeutral currentPredecessor
        currentPredecessorTerminates currentZeroBranch currentZeroTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerPredecessor =>
            ∀ {innerZeroBranch : RawTerm scope},
              IsStronglyNormalizing innerZeroBranch →
                IsStronglyNormalizing
                  (.mkGen .gen_natElim ()
                    (.childCons
                      (.mkGen .gen_natSucc ()
                        (.childCons innerPredecessor .childNil))
                      (.childCons innerZeroBranch
                        (.childCons currentSuccBranch .childNil))) :
                    RawTerm scope))
          (m := fun currentPredecessor currentPredecessorSuccessors
              predecessorIH => by
            intro currentZeroBranch currentZeroTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerZeroBranch =>
                  IsStronglyNormalizing
                    (.mkGen .gen_natElim ()
                      (.childCons
                        (.mkGen .gen_natSucc ()
                          (.childCons currentPredecessor .childNil))
                        (.childCons innerZeroBranch
                          (.childCons currentSuccBranch .childNil))) :
                      RawTerm scope))
                (m := fun currentZeroBranch currentZeroSuccessors zeroIH =>
                  Acc.intro
                    (.mkGen .gen_natElim ()
                      (.childCons
                        (.mkGen .gen_natSucc ()
                          (.childCons currentPredecessor .childNil))
                        (.childCons currentZeroBranch
                          (.childCons currentSuccBranch .childNil))) :
                      RawTerm scope)
                    (fun targetTerm parentStep => by
                      cases Step.from_natElim parentStep with
                      | inl zeroBranchStep =>
                          obtain ⟨scrutineeEq, _⟩ := zeroBranchStep
                          cases scrutineeEq
                      | inr restAfterZero =>
                          cases restAfterZero with
                          | inl succBranchStep =>
                              obtain
                                ⟨succPredecessor, scrutineeEq,
                                  targetEq⟩ := succBranchStep
                              cases scrutineeEq
                              rw [targetEq]
                              exact
                                applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_two_arguments
                                  (isNeutralHead := isNeutralHead)
                                  currentSuccBranchIsNeutral
                                  neutralHeadIsNotLambda
                                  neutralHeadStep
                                  (Acc.intro currentSuccBranch
                                    currentSuccBranchSuccessors)
                                  (Acc.intro currentPredecessor
                                    currentPredecessorSuccessors)
                                  (recursiveCallTerminates
                                    (Acc.intro currentPredecessor
                                      currentPredecessorSuccessors)
                                    (Acc.intro currentZeroBranch
                                      currentZeroSuccessors)
                                    currentSuccBranchIsNeutral
                                    (Acc.intro currentSuccBranch
                                      currentSuccBranchSuccessors))
                          | inr restAfterSucc =>
                              cases restAfterSucc with
                              | inl scrutineeBranch =>
                                  obtain
                                    ⟨scrutineeAfter, targetEq,
                                      scrutineeStep⟩ := scrutineeBranch
                                  obtain
                                    ⟨predecessorAfter, scrutineeAfterEq,
                                      predecessorStep⟩ :=
                                      Step.from_natSucc scrutineeStep
                                  rw [targetEq, scrutineeAfterEq]
                                  exact
                                    predecessorIH predecessorAfter
                                      predecessorStep
                                      (Acc.intro currentZeroBranch
                                        currentZeroSuccessors)
                              | inr restAfterScrutinee =>
                                  cases restAfterScrutinee with
                                  | inl zeroStep =>
                                      obtain
                                        ⟨zeroAfter, targetEq,
                                          zeroStepInner⟩ := zeroStep
                                      rw [targetEq]
                                      exact zeroIH zeroAfter zeroStepInner
                                  | inr succStep =>
                                      obtain
                                        ⟨succAfter, targetEq,
                                          succStepInner⟩ := succStep
                                      rw [targetEq]
                                      exact
                                        succBranchIH succAfter succStepInner
                                          (neutralHeadStep
                                            currentSuccBranchIsNeutral
                                            succStepInner)
                                          (Acc.intro currentPredecessor
                                            currentPredecessorSuccessors)
                                          (Acc.intro currentZeroBranch
                                            currentZeroSuccessors)))
                currentZeroTerminates)
          currentPredecessorTerminates
          currentZeroTerminates)
    succTerminates)
    succBranchIsNeutral
    predecessorTerminates
    zeroTerminates

/-- Natural-number recursion on `natSucc predecessor` is strongly normalizing
under the same conservative hypotheses as the `natElim` successor theorem.

The recursive call obligation is again explicit: this theorem is the substrate
induction-step accessibility lemma for `natRec`, not a closed proof of
recursive eliminator termination. -/
theorem natRecSucc_isStronglyNormalizing_of_neutral_succBranch
    {scope : Nat} (isNeutralHead : RawTerm scope → Prop)
    {predecessor zeroBranch succBranch : RawTerm scope}
    (predecessorTerminates : IsStronglyNormalizing predecessor)
    (zeroTerminates : IsStronglyNormalizing zeroBranch)
    (succBranchIsNeutral : isNeutralHead succBranch)
    (neutralHeadIsNotLambda :
      ∀ {currentHead : RawTerm scope}, isNeutralHead currentHead →
        ∀ (lambdaDomain : RawTerm scope) (lambdaBody : RawTerm (scope + 1)),
          currentHead ≠ .mkGen .gen_lam ()
            (.childCons lambdaDomain (.childCons lambdaBody .childNil)))
    (neutralHeadStep :
      ∀ {currentHead targetHead : RawTerm scope},
        isNeutralHead currentHead →
          Step currentHead targetHead →
            isNeutralHead targetHead)
    (succTerminates : IsStronglyNormalizing succBranch)
    (recursiveCallTerminates :
      ∀ {currentPredecessor currentZeroBranch currentSuccBranch :
          RawTerm scope},
        IsStronglyNormalizing currentPredecessor →
          IsStronglyNormalizing currentZeroBranch →
            isNeutralHead currentSuccBranch →
              IsStronglyNormalizing currentSuccBranch →
                IsStronglyNormalizing
                  (.mkGen .gen_natRec ()
                    (.childCons currentPredecessor
                      (.childCons currentZeroBranch
                        (.childCons currentSuccBranch .childNil))) :
                    RawTerm scope)) :
    IsStronglyNormalizing
      (.mkGen .gen_natRec ()
        (.childCons
          (.mkGen .gen_natSucc () (.childCons predecessor .childNil))
          (.childCons zeroBranch (.childCons succBranch .childNil))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentSuccBranch =>
      isNeutralHead currentSuccBranch →
        ∀ {currentPredecessor : RawTerm scope},
          IsStronglyNormalizing currentPredecessor →
            ∀ {currentZeroBranch : RawTerm scope},
              IsStronglyNormalizing currentZeroBranch →
                IsStronglyNormalizing
                  (.mkGen .gen_natRec ()
                    (.childCons
                      (.mkGen .gen_natSucc ()
                        (.childCons currentPredecessor .childNil))
                      (.childCons currentZeroBranch
                        (.childCons currentSuccBranch .childNil))) :
                    RawTerm scope))
    (m := fun currentSuccBranch currentSuccBranchSuccessors succBranchIH => by
      intro currentSuccBranchIsNeutral currentPredecessor
        currentPredecessorTerminates currentZeroBranch currentZeroTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerPredecessor =>
            ∀ {innerZeroBranch : RawTerm scope},
              IsStronglyNormalizing innerZeroBranch →
                IsStronglyNormalizing
                  (.mkGen .gen_natRec ()
                    (.childCons
                      (.mkGen .gen_natSucc ()
                        (.childCons innerPredecessor .childNil))
                      (.childCons innerZeroBranch
                        (.childCons currentSuccBranch .childNil))) :
                    RawTerm scope))
          (m := fun currentPredecessor currentPredecessorSuccessors
              predecessorIH => by
            intro currentZeroBranch currentZeroTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerZeroBranch =>
                  IsStronglyNormalizing
                    (.mkGen .gen_natRec ()
                      (.childCons
                        (.mkGen .gen_natSucc ()
                          (.childCons currentPredecessor .childNil))
                        (.childCons innerZeroBranch
                          (.childCons currentSuccBranch .childNil))) :
                      RawTerm scope))
                (m := fun currentZeroBranch currentZeroSuccessors zeroIH =>
                  Acc.intro
                    (.mkGen .gen_natRec ()
                      (.childCons
                        (.mkGen .gen_natSucc ()
                          (.childCons currentPredecessor .childNil))
                        (.childCons currentZeroBranch
                          (.childCons currentSuccBranch .childNil))) :
                      RawTerm scope)
                    (fun targetTerm parentStep => by
                      cases Step.from_natRec parentStep with
                      | inl zeroBranchStep =>
                          obtain ⟨scrutineeEq, _⟩ := zeroBranchStep
                          cases scrutineeEq
                      | inr restAfterZero =>
                          cases restAfterZero with
                          | inl succBranchStep =>
                              obtain
                                ⟨succPredecessor, scrutineeEq,
                                  targetEq⟩ := succBranchStep
                              cases scrutineeEq
                              rw [targetEq]
                              exact
                                applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_two_arguments
                                  (isNeutralHead := isNeutralHead)
                                  currentSuccBranchIsNeutral
                                  neutralHeadIsNotLambda
                                  neutralHeadStep
                                  (Acc.intro currentSuccBranch
                                    currentSuccBranchSuccessors)
                                  (Acc.intro currentPredecessor
                                    currentPredecessorSuccessors)
                                  (recursiveCallTerminates
                                    (Acc.intro currentPredecessor
                                      currentPredecessorSuccessors)
                                    (Acc.intro currentZeroBranch
                                      currentZeroSuccessors)
                                    currentSuccBranchIsNeutral
                                    (Acc.intro currentSuccBranch
                                      currentSuccBranchSuccessors))
                          | inr restAfterSucc =>
                              cases restAfterSucc with
                              | inl scrutineeBranch =>
                                  obtain
                                    ⟨scrutineeAfter, targetEq,
                                      scrutineeStep⟩ := scrutineeBranch
                                  obtain
                                    ⟨predecessorAfter, scrutineeAfterEq,
                                      predecessorStep⟩ :=
                                      Step.from_natSucc scrutineeStep
                                  rw [targetEq, scrutineeAfterEq]
                                  exact
                                    predecessorIH predecessorAfter
                                      predecessorStep
                                      (Acc.intro currentZeroBranch
                                        currentZeroSuccessors)
                              | inr restAfterScrutinee =>
                                  cases restAfterScrutinee with
                                  | inl zeroStep =>
                                      obtain
                                        ⟨zeroAfter, targetEq,
                                          zeroStepInner⟩ := zeroStep
                                      rw [targetEq]
                                      exact zeroIH zeroAfter zeroStepInner
                                  | inr succStep =>
                                      obtain
                                        ⟨succAfter, targetEq,
                                          succStepInner⟩ := succStep
                                      rw [targetEq]
                                      exact
                                        succBranchIH succAfter succStepInner
                                          (neutralHeadStep
                                            currentSuccBranchIsNeutral
                                            succStepInner)
                                          (Acc.intro currentPredecessor
                                            currentPredecessorSuccessors)
                                          (Acc.intro currentZeroBranch
                                            currentZeroSuccessors)))
                currentZeroTerminates)
          currentPredecessorTerminates
          currentZeroTerminates)
    succTerminates)
    succBranchIsNeutral
    predecessorTerminates
    zeroTerminates

/-- List elimination on literal nil is strongly normalizing when both branches
are strongly normalizing.

The cons iota is impossible on the literal nil scrutinee, and scrutinee
congruence is impossible because `listNil` is a normal leaf. -/
theorem listElimNil_isStronglyNormalizing_of_branches {scope : Nat}
    {motive : RawTerm (scope + 1)}
    {nilBranch consBranch : RawTerm scope}
    (motiveTerminates : IsStronglyNormalizing motive)
    (nilTerminates : IsStronglyNormalizing nilBranch)
    (consTerminates : IsStronglyNormalizing consBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_listElim ()
        (.childCons motive
          (.childCons nilBranch
            (.childCons consBranch
              (.childCons (.mkGen .gen_listNil () .childNil) .childNil)))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentMotive =>
      ∀ {currentNil currentCons : RawTerm scope},
        IsStronglyNormalizing currentNil → IsStronglyNormalizing currentCons →
          IsStronglyNormalizing
            (.mkGen .gen_listElim ()
              (.childCons currentMotive
                (.childCons currentNil
                  (.childCons currentCons
                    (.childCons (.mkGen .gen_listNil () .childNil) .childNil)))) :
              RawTerm scope))
    (m := fun currentMotive currentMotiveSuccessors motiveBranchIH => by
      intro currentNil currentCons currentNilTerminates currentConsTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerNil =>
            ∀ {innerCons : RawTerm scope},
              IsStronglyNormalizing innerCons →
                IsStronglyNormalizing
                  (.mkGen .gen_listElim ()
                    (.childCons currentMotive
                      (.childCons innerNil
                        (.childCons innerCons
                          (.childCons (.mkGen .gen_listNil () .childNil) .childNil)))) :
                    RawTerm scope))
          (m := fun currentNilBranch currentNilSuccessors nilBranchIH => by
            intro innerCons innerConsTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerCons' =>
                  IsStronglyNormalizing
                    (.mkGen .gen_listElim ()
                      (.childCons currentMotive
                        (.childCons currentNilBranch
                          (.childCons innerCons'
                            (.childCons (.mkGen .gen_listNil () .childNil) .childNil)))) :
                      RawTerm scope))
                (m := fun currentConsBranch currentConsSuccessors consBranchIH =>
                  Acc.intro
                    (.mkGen .gen_listElim ()
                      (.childCons currentMotive
                        (.childCons currentNilBranch
                          (.childCons currentConsBranch
                            (.childCons (.mkGen .gen_listNil () .childNil) .childNil)))) :
                      RawTerm scope)
                    (fun targetTerm parentStep => by
                      rcases Step.from_listElim parentStep with
                        ⟨_scrutineeIsNil, targetIsNil⟩ |
                        ⟨_headVal, _tailVal, scrutineeIsCons, _⟩ |
                        ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                        ⟨nilAfter, targetIsNilStep, nilStep⟩ |
                        ⟨consAfter, targetIsConsStep, consStep⟩ |
                        ⟨_scrutineeAfter, _targetIsScrutineeStep, scrutineeStep⟩
                      · rw [targetIsNil]
                        exact Acc.intro currentNilBranch currentNilSuccessors
                      · cases scrutineeIsCons
                      · rw [targetIsMotiveStep]
                        exact motiveBranchIH motiveAfter motiveStep
                          (Acc.intro currentNilBranch currentNilSuccessors)
                          (Acc.intro currentConsBranch currentConsSuccessors)
                      · rw [targetIsNilStep]
                        exact nilBranchIH nilAfter nilStep
                          (Acc.intro currentConsBranch currentConsSuccessors)
                      · rw [targetIsConsStep]
                        exact consBranchIH consAfter consStep
                      · exact False.elim (noStep_listNil scrutineeStep)))
                innerConsTerminates)
          currentNilTerminates currentConsTerminates))
    motiveTerminates)
    nilTerminates consTerminates

/-- List elimination on `listCons headVal tailVal` is strongly normalizing
when the cons branch is a neutral function head and the recursive call on the
tail is supplied as an explicit accessibility hypothesis.

This is the list analogue of the nat-successor induction-step theorem.  The
root iota reduct is the three-argument application spine
`app (app (app consBranch headVal) tailVal)
  (listElim motive nilBranch consBranch tailVal)`, so the theorem deliberately
exposes the recursive-call SN obligation instead of claiming recursive
eliminator termination globally.  Phase-Z motive shape: the motive heads the
spine (under one binder) and the scrutinee `listCons head tail` is the LAST
child; the recursive `listElim` THREADS the motive.  A FIVE-fold accessibility
induction (motive outer, then consBranch, headVal, tailVal, nilBranch). -/
theorem listElimCons_isStronglyNormalizing_of_neutral_consBranch
    {scope : Nat} (isNeutralHead : RawTerm scope → Prop)
    {motive : RawTerm (scope + 1)}
    {headVal tailVal nilBranch consBranch : RawTerm scope}
    (motiveTerminates : IsStronglyNormalizing motive)
    (headTerminates : IsStronglyNormalizing headVal)
    (tailTerminates : IsStronglyNormalizing tailVal)
    (nilTerminates : IsStronglyNormalizing nilBranch)
    (consBranchIsNeutral : isNeutralHead consBranch)
    (neutralHeadIsNotLambda :
      ∀ {currentHead : RawTerm scope}, isNeutralHead currentHead →
        ∀ (lambdaDomain : RawTerm scope) (lambdaBody : RawTerm (scope + 1)),
          currentHead ≠ .mkGen .gen_lam ()
            (.childCons lambdaDomain (.childCons lambdaBody .childNil)))
    (neutralHeadStep :
      ∀ {currentHead targetHead : RawTerm scope},
        isNeutralHead currentHead →
          Step currentHead targetHead →
            isNeutralHead targetHead)
    (consTerminates : IsStronglyNormalizing consBranch)
    (recursiveCallTerminates :
      ∀ {currentMotive : RawTerm (scope + 1)}
        {currentTailVal currentNilBranch currentConsBranch : RawTerm scope},
        IsStronglyNormalizing currentMotive →
          IsStronglyNormalizing currentTailVal →
            IsStronglyNormalizing currentNilBranch →
              isNeutralHead currentConsBranch →
                IsStronglyNormalizing currentConsBranch →
                  IsStronglyNormalizing
                    (.mkGen .gen_listElim ()
                      (.childCons currentMotive
                        (.childCons currentNilBranch
                          (.childCons currentConsBranch
                            (.childCons currentTailVal .childNil)))) :
                      RawTerm scope)) :
    IsStronglyNormalizing
      (.mkGen .gen_listElim ()
        (.childCons motive
          (.childCons nilBranch
            (.childCons consBranch
              (.childCons
                (.mkGen .gen_listCons ()
                  (.childCons headVal (.childCons tailVal .childNil)))
                .childNil)))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentMotive =>
      ∀ {currentConsBranch : RawTerm scope},
        isNeutralHead currentConsBranch →
          IsStronglyNormalizing currentConsBranch →
            ∀ {currentHeadVal : RawTerm scope},
              IsStronglyNormalizing currentHeadVal →
                ∀ {currentTailVal : RawTerm scope},
                  IsStronglyNormalizing currentTailVal →
                    ∀ {currentNilBranch : RawTerm scope},
                      IsStronglyNormalizing currentNilBranch →
                        IsStronglyNormalizing
                          (.mkGen .gen_listElim ()
                            (.childCons currentMotive
                              (.childCons currentNilBranch
                                (.childCons currentConsBranch
                                  (.childCons
                                    (.mkGen .gen_listCons ()
                                      (.childCons currentHeadVal
                                        (.childCons currentTailVal .childNil)))
                                    .childNil)))) :
                            RawTerm scope))
    (m := fun currentMotive currentMotiveSuccessors motiveIH => by
      intro currentConsBranch currentConsBranchIsNeutral currentConsBranchTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerConsBranch =>
            isNeutralHead innerConsBranch →
              ∀ {currentHeadVal : RawTerm scope},
                IsStronglyNormalizing currentHeadVal →
                  ∀ {currentTailVal : RawTerm scope},
                    IsStronglyNormalizing currentTailVal →
                      ∀ {currentNilBranch : RawTerm scope},
                        IsStronglyNormalizing currentNilBranch →
                          IsStronglyNormalizing
                            (.mkGen .gen_listElim ()
                              (.childCons currentMotive
                                (.childCons currentNilBranch
                                  (.childCons innerConsBranch
                                    (.childCons
                                      (.mkGen .gen_listCons ()
                                        (.childCons currentHeadVal
                                          (.childCons currentTailVal .childNil)))
                                      .childNil)))) :
                              RawTerm scope))
          (m := fun currentConsBranch currentConsBranchSuccessors consBranchIH => by
            intro currentConsBranchIsNeutral currentHeadVal currentHeadTerminates
              currentTailVal currentTailTerminates currentNilBranch
              currentNilTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerHeadVal =>
                  ∀ {innerTailVal : RawTerm scope},
                    IsStronglyNormalizing innerTailVal →
                      ∀ {innerNilBranch : RawTerm scope},
                        IsStronglyNormalizing innerNilBranch →
                          IsStronglyNormalizing
                            (.mkGen .gen_listElim ()
                              (.childCons currentMotive
                                (.childCons innerNilBranch
                                  (.childCons currentConsBranch
                                    (.childCons
                                      (.mkGen .gen_listCons ()
                                        (.childCons innerHeadVal
                                          (.childCons innerTailVal .childNil)))
                                      .childNil)))) :
                              RawTerm scope))
                (m := fun currentHeadVal currentHeadSuccessors headIH => by
                  intro currentTailVal currentTailTerminates currentNilBranch
                    currentNilTerminates
                  exact
                    Acc.ndrec
                      (r := StepSuccessor)
                      (C := fun innerTailVal =>
                        ∀ {innerNilBranch : RawTerm scope},
                          IsStronglyNormalizing innerNilBranch →
                            IsStronglyNormalizing
                              (.mkGen .gen_listElim ()
                                (.childCons currentMotive
                                  (.childCons innerNilBranch
                                    (.childCons currentConsBranch
                                      (.childCons
                                        (.mkGen .gen_listCons ()
                                          (.childCons currentHeadVal
                                            (.childCons innerTailVal .childNil)))
                                        .childNil)))) :
                                RawTerm scope))
                      (m := fun currentTailVal currentTailSuccessors tailIH => by
                        intro currentNilBranch currentNilTerminates
                        exact
                          Acc.ndrec
                            (r := StepSuccessor)
                            (C := fun innerNilBranch =>
                              IsStronglyNormalizing
                                (.mkGen .gen_listElim ()
                                  (.childCons currentMotive
                                    (.childCons innerNilBranch
                                      (.childCons currentConsBranch
                                        (.childCons
                                          (.mkGen .gen_listCons ()
                                            (.childCons currentHeadVal
                                              (.childCons currentTailVal .childNil)))
                                          .childNil)))) :
                                  RawTerm scope))
                            (m := fun currentNilBranch currentNilSuccessors nilIH =>
                              Acc.intro
                                (.mkGen .gen_listElim ()
                                  (.childCons currentMotive
                                    (.childCons currentNilBranch
                                      (.childCons currentConsBranch
                                        (.childCons
                                          (.mkGen .gen_listCons ()
                                            (.childCons currentHeadVal
                                              (.childCons currentTailVal .childNil)))
                                          .childNil)))) :
                                  RawTerm scope)
                                (fun targetTerm parentStep => by
                                  rcases Step.from_listElim parentStep with
                                    ⟨scrutineeIsNil, _⟩ |
                                    ⟨consHead, consTail, scrutineeIsCons, targetEq⟩ |
                                    ⟨motiveAfter, targetIsMotiveStep, motiveStep⟩ |
                                    ⟨nilAfter, targetIsNilStep, nilStepInner⟩ |
                                    ⟨consAfter, targetIsConsStep, consStepInner⟩ |
                                    ⟨scrutineeAfter, targetIsScrutineeStep, scrutineeStep⟩
                                  · cases scrutineeIsNil
                                  · cases scrutineeIsCons
                                    rw [targetEq]
                                    exact
                                      applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_three_arguments
                                        (isNeutralHead := isNeutralHead)
                                        currentConsBranchIsNeutral
                                        neutralHeadIsNotLambda
                                        neutralHeadStep
                                        (Acc.intro currentConsBranch
                                          currentConsBranchSuccessors)
                                        (Acc.intro currentHeadVal
                                          currentHeadSuccessors)
                                        (Acc.intro currentTailVal
                                          currentTailSuccessors)
                                        (recursiveCallTerminates
                                          (Acc.intro currentMotive
                                            currentMotiveSuccessors)
                                          (Acc.intro currentTailVal
                                            currentTailSuccessors)
                                          (Acc.intro currentNilBranch
                                            currentNilSuccessors)
                                          currentConsBranchIsNeutral
                                          (Acc.intro currentConsBranch
                                            currentConsBranchSuccessors))
                                  · rw [targetIsMotiveStep]
                                    exact motiveIH motiveAfter motiveStep
                                      currentConsBranchIsNeutral
                                      (Acc.intro currentConsBranch
                                        currentConsBranchSuccessors)
                                      (Acc.intro currentHeadVal
                                        currentHeadSuccessors)
                                      (Acc.intro currentTailVal
                                        currentTailSuccessors)
                                      (Acc.intro currentNilBranch
                                        currentNilSuccessors)
                                  · rw [targetIsNilStep]
                                    exact nilIH nilAfter nilStepInner
                                  · rw [targetIsConsStep]
                                    exact
                                      consBranchIH consAfter
                                        consStepInner
                                        (neutralHeadStep
                                          currentConsBranchIsNeutral
                                          consStepInner)
                                        (Acc.intro currentHeadVal
                                          currentHeadSuccessors)
                                        (Acc.intro currentTailVal
                                          currentTailSuccessors)
                                        (Acc.intro currentNilBranch
                                          currentNilSuccessors)
                                  · rw [targetIsScrutineeStep]
                                    cases Step.from_listCons scrutineeStep with
                                    | inl headBranch =>
                                        obtain
                                          ⟨headAfter, scrutineeAfterEq,
                                            headStep⟩ := headBranch
                                        rw [scrutineeAfterEq]
                                        exact
                                          headIH headAfter headStep
                                            (Acc.intro currentTailVal
                                              currentTailSuccessors)
                                            (Acc.intro currentNilBranch
                                              currentNilSuccessors)
                                    | inr tailBranch =>
                                        obtain
                                          ⟨tailAfter, scrutineeAfterEq,
                                            tailStep⟩ := tailBranch
                                        rw [scrutineeAfterEq]
                                        exact
                                          tailIH tailAfter tailStep
                                            (Acc.intro currentNilBranch
                                              currentNilSuccessors)))
                            currentNilTerminates)
                      currentTailTerminates
                      currentNilTerminates)
                currentHeadTerminates
                currentTailTerminates
                currentNilTerminates)
          currentConsBranchTerminates
          currentConsBranchIsNeutral))
    motiveTerminates)
    consBranchIsNeutral consTerminates
    headTerminates
    tailTerminates
    nilTerminates

/-- Option matching on literal none is strongly normalizing when both branches
are strongly normalizing.

The some iota is impossible on the literal none scrutinee, and scrutinee
congruence is impossible because `optionNone` is a normal leaf. -/
theorem optionMatchNone_isStronglyNormalizing_of_branches {scope : Nat}
    {noneBranch someBranch : RawTerm scope}
    (noneTerminates : IsStronglyNormalizing noneBranch)
    (someTerminates : IsStronglyNormalizing someBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_optionMatch ()
        (.childCons
          (.mkGen .gen_optionNone () .childNil)
          (.childCons noneBranch (.childCons someBranch .childNil))) :
        RawTerm scope) :=
  isStronglyNormalizing_of_twoBranchProjectionRedex
    (fun currentNone currentSome =>
      (.mkGen .gen_optionMatch ()
        (.childCons
          (.mkGen .gen_optionNone () .childNil)
          (.childCons currentNone (.childCons currentSome .childNil))) :
        RawTerm scope))
    (fun parentStep => by
      cases Step.from_optionMatch parentStep with
      | inl noneBranchStep =>
          exact Or.inl noneBranchStep.2
      | inr restAfterNone =>
          cases restAfterNone with
          | inl someBranchStep =>
              obtain ⟨value, scrutineeEq, _⟩ := someBranchStep
              cases scrutineeEq
          | inr restAfterSome =>
              cases restAfterSome with
              | inl scrutineeBranch =>
                  obtain ⟨_, _, scrutineeStep⟩ := scrutineeBranch
                  exact False.elim (noStep_optionNone scrutineeStep)
              | inr restAfterScrutinee =>
                  cases restAfterScrutinee with
                  | inl noneStep =>
                      obtain ⟨noneAfter, targetEq, noneStepInner⟩ :=
                        noneStep
                      exact Or.inr
                        (Or.inl ⟨noneAfter, targetEq, noneStepInner⟩)
                  | inr someStep =>
                      obtain ⟨someAfter, targetEq, someStepInner⟩ :=
                        someStep
                      exact Or.inr
                        (Or.inr ⟨someAfter, targetEq, someStepInner⟩))
    noneTerminates
    someTerminates

/-- Option matching on `some value` is strongly normalizing when the selected
some-branch is a neutral function head.

The root iota reduct is the one-argument application `app someBranch value`.
This theorem is deliberately not general application closure: beta is ruled out
only by the explicit neutral-head invariant supplied for `someBranch`. -/
theorem optionMatchSome_isStronglyNormalizing_of_neutral_someBranch
    {scope : Nat} (isNeutralHead : RawTerm scope → Prop)
    {value noneBranch someBranch : RawTerm scope}
    (valueTerminates : IsStronglyNormalizing value)
    (noneTerminates : IsStronglyNormalizing noneBranch)
    (someBranchIsNeutral : isNeutralHead someBranch)
    (neutralHeadIsNotLambda :
      ∀ {currentHead : RawTerm scope}, isNeutralHead currentHead →
        ∀ (lambdaDomain : RawTerm scope) (lambdaBody : RawTerm (scope + 1)),
          currentHead ≠ .mkGen .gen_lam ()
            (.childCons lambdaDomain (.childCons lambdaBody .childNil)))
    (neutralHeadStep :
      ∀ {currentHead targetHead : RawTerm scope},
        isNeutralHead currentHead →
          Step currentHead targetHead →
            isNeutralHead targetHead)
    (someTerminates : IsStronglyNormalizing someBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_optionMatch ()
        (.childCons
          (.mkGen .gen_optionSome () (.childCons value .childNil))
          (.childCons noneBranch (.childCons someBranch .childNil))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentSomeBranch =>
      isNeutralHead currentSomeBranch →
        ∀ {currentValue : RawTerm scope},
          IsStronglyNormalizing currentValue →
            ∀ {currentNoneBranch : RawTerm scope},
              IsStronglyNormalizing currentNoneBranch →
                IsStronglyNormalizing
                  (.mkGen .gen_optionMatch ()
                    (.childCons
                      (.mkGen .gen_optionSome ()
                        (.childCons currentValue .childNil))
                      (.childCons currentNoneBranch
                        (.childCons currentSomeBranch .childNil))) :
                    RawTerm scope))
    (m := fun currentSomeBranch currentSomeBranchSuccessors someBranchIH => by
      intro currentSomeBranchIsNeutral currentValue currentValueTerminates
        currentNoneBranch currentNoneTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerValue =>
            ∀ {innerNoneBranch : RawTerm scope},
              IsStronglyNormalizing innerNoneBranch →
                IsStronglyNormalizing
                  (.mkGen .gen_optionMatch ()
                    (.childCons
                      (.mkGen .gen_optionSome ()
                        (.childCons innerValue .childNil))
                      (.childCons innerNoneBranch
                        (.childCons currentSomeBranch .childNil))) :
                    RawTerm scope))
          (m := fun currentValue currentValueSuccessors valueIH => by
            intro currentNoneBranch currentNoneTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerNoneBranch =>
                  IsStronglyNormalizing
                    (.mkGen .gen_optionMatch ()
                      (.childCons
                        (.mkGen .gen_optionSome ()
                          (.childCons currentValue .childNil))
                        (.childCons innerNoneBranch
                          (.childCons currentSomeBranch .childNil))) :
                      RawTerm scope))
                (m := fun currentNoneBranch currentNoneSuccessors noneIH =>
                  Acc.intro
                    (.mkGen .gen_optionMatch ()
                      (.childCons
                        (.mkGen .gen_optionSome ()
                          (.childCons currentValue .childNil))
                        (.childCons currentNoneBranch
                          (.childCons currentSomeBranch .childNil))) :
                      RawTerm scope)
                    (fun targetTerm parentStep => by
                      cases Step.from_optionMatch parentStep with
                      | inl noneBranchStep =>
                          obtain ⟨scrutineeEq, _⟩ := noneBranchStep
                          cases scrutineeEq
                      | inr restAfterNone =>
                          cases restAfterNone with
                          | inl someBranchStep =>
                              obtain ⟨someValue, scrutineeEq, targetEq⟩ :=
                                someBranchStep
                              cases scrutineeEq
                              rw [targetEq]
                              exact
                                applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_one_argument
                                  (isNeutralHead := isNeutralHead)
                                  currentSomeBranchIsNeutral
                                  neutralHeadIsNotLambda
                                  neutralHeadStep
                                  (Acc.intro currentSomeBranch
                                    currentSomeBranchSuccessors)
                                  (Acc.intro currentValue
                                    currentValueSuccessors)
                          | inr restAfterSome =>
                              cases restAfterSome with
                              | inl scrutineeBranch =>
                                  obtain
                                    ⟨scrutineeAfter, targetEq,
                                      scrutineeStep⟩ := scrutineeBranch
                                  obtain
                                    ⟨valueAfter, scrutineeAfterEq,
                                      valueStep⟩ :=
                                      Step.from_optionSome scrutineeStep
                                  rw [targetEq, scrutineeAfterEq]
                                  exact valueIH valueAfter valueStep
                                    (Acc.intro currentNoneBranch
                                      currentNoneSuccessors)
                              | inr restAfterScrutinee =>
                                  cases restAfterScrutinee with
                                  | inl noneStep =>
                                      obtain
                                        ⟨noneAfter, targetEq,
                                          noneStepInner⟩ := noneStep
                                      rw [targetEq]
                                      exact noneIH noneAfter noneStepInner
                                  | inr someStep =>
                                      obtain
                                        ⟨someAfter, targetEq,
                                          someStepInner⟩ := someStep
                                      rw [targetEq]
                                      exact
                                        someBranchIH someAfter someStepInner
                                          (neutralHeadStep
                                            currentSomeBranchIsNeutral
                                            someStepInner)
                                          (Acc.intro currentValue
                                            currentValueSuccessors)
                                          (Acc.intro currentNoneBranch
                                            currentNoneSuccessors)))
                currentNoneTerminates)
          currentValueTerminates
          currentNoneTerminates)
    someTerminates)
    someBranchIsNeutral
    valueTerminates
    noneTerminates

/-- Either matching on `inl value` is strongly normalizing when the selected
left branch is a neutral function head.

The root iota reduct is the one-argument application `app leftBranch value`.
This is the either-left analogue of
`optionMatchSome_isStronglyNormalizing_of_neutral_someBranch`; it deliberately
does not assert general application closure. -/
theorem eitherMatchInl_isStronglyNormalizing_of_neutral_leftBranch
    {scope : Nat} (isNeutralHead : RawTerm scope → Prop)
    {value leftBranch rightBranch : RawTerm scope}
    (valueTerminates : IsStronglyNormalizing value)
    (leftBranchIsNeutral : isNeutralHead leftBranch)
    (neutralHeadIsNotLambda :
      ∀ {currentHead : RawTerm scope}, isNeutralHead currentHead →
        ∀ (lambdaDomain : RawTerm scope) (lambdaBody : RawTerm (scope + 1)),
          currentHead ≠ .mkGen .gen_lam ()
            (.childCons lambdaDomain (.childCons lambdaBody .childNil)))
    (neutralHeadStep :
      ∀ {currentHead targetHead : RawTerm scope},
        isNeutralHead currentHead →
          Step currentHead targetHead →
            isNeutralHead targetHead)
    (leftTerminates : IsStronglyNormalizing leftBranch)
    (rightTerminates : IsStronglyNormalizing rightBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_eitherMatch ()
        (.childCons
          (.mkGen .gen_eitherInl () (.childCons value .childNil))
          (.childCons leftBranch (.childCons rightBranch .childNil))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentLeftBranch =>
      isNeutralHead currentLeftBranch →
        ∀ {currentValue : RawTerm scope},
          IsStronglyNormalizing currentValue →
            ∀ {currentRightBranch : RawTerm scope},
              IsStronglyNormalizing currentRightBranch →
                IsStronglyNormalizing
                  (.mkGen .gen_eitherMatch ()
                    (.childCons
                      (.mkGen .gen_eitherInl ()
                        (.childCons currentValue .childNil))
                      (.childCons currentLeftBranch
                        (.childCons currentRightBranch .childNil))) :
                    RawTerm scope))
    (m := fun currentLeftBranch currentLeftBranchSuccessors leftBranchIH => by
      intro currentLeftBranchIsNeutral currentValue currentValueTerminates
        currentRightBranch currentRightTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerValue =>
            ∀ {innerRightBranch : RawTerm scope},
              IsStronglyNormalizing innerRightBranch →
                IsStronglyNormalizing
                  (.mkGen .gen_eitherMatch ()
                    (.childCons
                      (.mkGen .gen_eitherInl ()
                        (.childCons innerValue .childNil))
                      (.childCons currentLeftBranch
                        (.childCons innerRightBranch .childNil))) :
                    RawTerm scope))
          (m := fun currentValue currentValueSuccessors valueIH => by
            intro currentRightBranch currentRightTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerRightBranch =>
                  IsStronglyNormalizing
                    (.mkGen .gen_eitherMatch ()
                      (.childCons
                        (.mkGen .gen_eitherInl ()
                          (.childCons currentValue .childNil))
                        (.childCons currentLeftBranch
                          (.childCons innerRightBranch .childNil))) :
                      RawTerm scope))
                (m := fun currentRightBranch currentRightSuccessors rightIH =>
                  Acc.intro
                    (.mkGen .gen_eitherMatch ()
                      (.childCons
                        (.mkGen .gen_eitherInl ()
                          (.childCons currentValue .childNil))
                        (.childCons currentLeftBranch
                          (.childCons currentRightBranch .childNil))) :
                      RawTerm scope)
                    (fun targetTerm parentStep => by
                      cases Step.from_eitherMatch parentStep with
                      | inl leftBranchStep =>
                          obtain ⟨leftValue, scrutineeEq, targetEq⟩ :=
                            leftBranchStep
                          cases scrutineeEq
                          rw [targetEq]
                          exact
                            applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_one_argument
                              (isNeutralHead := isNeutralHead)
                              currentLeftBranchIsNeutral
                              neutralHeadIsNotLambda
                              neutralHeadStep
                              (Acc.intro currentLeftBranch
                                currentLeftBranchSuccessors)
                              (Acc.intro currentValue
                                currentValueSuccessors)
                      | inr restAfterLeft =>
                          cases restAfterLeft with
                          | inl rightBranchStep =>
                              obtain ⟨rightValue, scrutineeEq, _⟩ :=
                                rightBranchStep
                              cases scrutineeEq
                          | inr restAfterRight =>
                              cases restAfterRight with
                              | inl scrutineeBranch =>
                                  obtain
                                    ⟨scrutineeAfter, targetEq,
                                      scrutineeStep⟩ := scrutineeBranch
                                  obtain
                                    ⟨valueAfter, scrutineeAfterEq,
                                      valueStep⟩ :=
                                      Step.from_eitherInl scrutineeStep
                                  rw [targetEq, scrutineeAfterEq]
                                  exact valueIH valueAfter valueStep
                                    (Acc.intro currentRightBranch
                                      currentRightSuccessors)
                              | inr restAfterScrutinee =>
                                  cases restAfterScrutinee with
                                  | inl leftStep =>
                                      obtain
                                        ⟨leftAfter, targetEq,
                                          leftStepInner⟩ := leftStep
                                      rw [targetEq]
                                      exact
                                        leftBranchIH leftAfter leftStepInner
                                          (neutralHeadStep
                                            currentLeftBranchIsNeutral
                                            leftStepInner)
                                          (Acc.intro currentValue
                                            currentValueSuccessors)
                                          (Acc.intro currentRightBranch
                                            currentRightSuccessors)
                                  | inr rightStep =>
                                      obtain
                                        ⟨rightAfter, targetEq,
                                          rightStepInner⟩ := rightStep
                                      rw [targetEq]
                                      exact rightIH rightAfter rightStepInner))
                currentRightTerminates)
          currentValueTerminates
          currentRightTerminates)
    leftTerminates)
    leftBranchIsNeutral
    valueTerminates
    rightTerminates

/-- Either matching on `inr value` is strongly normalizing when the selected
right branch is a neutral function head.

The root iota reduct is the one-argument application `app rightBranch value`.
This is symmetric to
`eitherMatchInl_isStronglyNormalizing_of_neutral_leftBranch`. -/
theorem eitherMatchInr_isStronglyNormalizing_of_neutral_rightBranch
    {scope : Nat} (isNeutralHead : RawTerm scope → Prop)
    {value leftBranch rightBranch : RawTerm scope}
    (valueTerminates : IsStronglyNormalizing value)
    (leftTerminates : IsStronglyNormalizing leftBranch)
    (rightBranchIsNeutral : isNeutralHead rightBranch)
    (neutralHeadIsNotLambda :
      ∀ {currentHead : RawTerm scope}, isNeutralHead currentHead →
        ∀ (lambdaDomain : RawTerm scope) (lambdaBody : RawTerm (scope + 1)),
          currentHead ≠ .mkGen .gen_lam ()
            (.childCons lambdaDomain (.childCons lambdaBody .childNil)))
    (neutralHeadStep :
      ∀ {currentHead targetHead : RawTerm scope},
        isNeutralHead currentHead →
          Step currentHead targetHead →
            isNeutralHead targetHead)
    (rightTerminates : IsStronglyNormalizing rightBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_eitherMatch ()
        (.childCons
          (.mkGen .gen_eitherInr () (.childCons value .childNil))
          (.childCons leftBranch (.childCons rightBranch .childNil))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentRightBranch =>
      isNeutralHead currentRightBranch →
        ∀ {currentValue : RawTerm scope},
          IsStronglyNormalizing currentValue →
            ∀ {currentLeftBranch : RawTerm scope},
              IsStronglyNormalizing currentLeftBranch →
                IsStronglyNormalizing
                  (.mkGen .gen_eitherMatch ()
                    (.childCons
                      (.mkGen .gen_eitherInr ()
                        (.childCons currentValue .childNil))
                      (.childCons currentLeftBranch
                        (.childCons currentRightBranch .childNil))) :
                    RawTerm scope))
    (m := fun currentRightBranch currentRightBranchSuccessors rightBranchIH => by
      intro currentRightBranchIsNeutral currentValue currentValueTerminates
        currentLeftBranch currentLeftTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerValue =>
            ∀ {innerLeftBranch : RawTerm scope},
              IsStronglyNormalizing innerLeftBranch →
                IsStronglyNormalizing
                  (.mkGen .gen_eitherMatch ()
                    (.childCons
                      (.mkGen .gen_eitherInr ()
                        (.childCons innerValue .childNil))
                      (.childCons innerLeftBranch
                        (.childCons currentRightBranch .childNil))) :
                    RawTerm scope))
          (m := fun currentValue currentValueSuccessors valueIH => by
            intro currentLeftBranch currentLeftTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerLeftBranch =>
                  IsStronglyNormalizing
                    (.mkGen .gen_eitherMatch ()
                      (.childCons
                        (.mkGen .gen_eitherInr ()
                          (.childCons currentValue .childNil))
                        (.childCons innerLeftBranch
                          (.childCons currentRightBranch .childNil))) :
                      RawTerm scope))
                (m := fun currentLeftBranch currentLeftSuccessors leftIH =>
                  Acc.intro
                    (.mkGen .gen_eitherMatch ()
                      (.childCons
                        (.mkGen .gen_eitherInr ()
                          (.childCons currentValue .childNil))
                        (.childCons currentLeftBranch
                          (.childCons currentRightBranch .childNil))) :
                      RawTerm scope)
                    (fun targetTerm parentStep => by
                      cases Step.from_eitherMatch parentStep with
                      | inl leftBranchStep =>
                          obtain ⟨leftValue, scrutineeEq, _⟩ :=
                            leftBranchStep
                          cases scrutineeEq
                      | inr restAfterLeft =>
                          cases restAfterLeft with
                          | inl rightBranchStep =>
                              obtain ⟨rightValue, scrutineeEq, targetEq⟩ :=
                                rightBranchStep
                              cases scrutineeEq
                              rw [targetEq]
                              exact
                                applyRawArgumentsFrom_isStronglyNormalizing_of_neutral_head_one_argument
                                  (isNeutralHead := isNeutralHead)
                                  currentRightBranchIsNeutral
                                  neutralHeadIsNotLambda
                                  neutralHeadStep
                                  (Acc.intro currentRightBranch
                                    currentRightBranchSuccessors)
                                  (Acc.intro currentValue
                                    currentValueSuccessors)
                          | inr restAfterRight =>
                              cases restAfterRight with
                              | inl scrutineeBranch =>
                                  obtain
                                    ⟨scrutineeAfter, targetEq,
                                      scrutineeStep⟩ := scrutineeBranch
                                  obtain
                                    ⟨valueAfter, scrutineeAfterEq,
                                      valueStep⟩ :=
                                      Step.from_eitherInr scrutineeStep
                                  rw [targetEq, scrutineeAfterEq]
                                  exact valueIH valueAfter valueStep
                                    (Acc.intro currentLeftBranch
                                      currentLeftSuccessors)
                              | inr restAfterScrutinee =>
                                  cases restAfterScrutinee with
                                  | inl leftStep =>
                                      obtain
                                        ⟨leftAfter, targetEq,
                                          leftStepInner⟩ := leftStep
                                      rw [targetEq]
                                      exact leftIH leftAfter leftStepInner
                                  | inr rightStep =>
                                      obtain
                                        ⟨rightAfter, targetEq,
                                          rightStepInner⟩ := rightStep
                                      rw [targetEq]
                                      exact
                                        rightBranchIH rightAfter rightStepInner
                                          (neutralHeadStep
                                            currentRightBranchIsNeutral
                                            rightStepInner)
                                          (Acc.intro currentValue
                                            currentValueSuccessors)
                                          (Acc.intro currentLeftBranch
                                            currentLeftSuccessors)))
                currentLeftTerminates)
          currentValueTerminates
          currentLeftTerminates)
    rightTerminates)
    rightBranchIsNeutral
    valueTerminates
    leftTerminates

end StepStar
end FX1Poly.Core

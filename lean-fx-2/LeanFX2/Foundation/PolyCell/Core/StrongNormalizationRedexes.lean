import LeanFX2.Foundation.PolyCell.Core.StrongNormalizationNeutral

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

namespace LeanFX2.Foundation.PolyCell.Core
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
    {scope : Nat} {body : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
    (bodyHasNoStep :
      ∀ targetBody : RawTerm (scope + 1), Step body targetBody → False)
    (contractumTerminates :
      ∀ {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentArgument →
          IsStronglyNormalizing (RawTerm.subst0 body currentArgument))
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam () (.childCons body .childNil))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentArgument =>
      IsStronglyNormalizing
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_lam () (.childCons body .childNil))
            (.childCons currentArgument .childNil)) :
          RawTerm scope))
    (m := fun currentArgument currentArgumentSuccessors argumentIH =>
      Acc.intro
        (.mkGen .gen_app ()
          (.childCons
            (.mkGen .gen_lam () (.childCons body .childNil))
            (.childCons currentArgument .childNil)) :
          RawTerm scope)
        (fun targetTerm applicationStep => by
          cases Step.from_app applicationStep with
          | inl betaBranch =>
              obtain ⟨lambdaBody, lambdaEq, targetEq⟩ := betaBranch
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
                  obtain ⟨bodyAfter, functionAfterEq, bodyStep⟩ :=
                    Step.from_lam functionStep
                  exact False.elim (bodyHasNoStep bodyAfter bodyStep)
              | inr argumentBranch =>
                  obtain ⟨argumentAfter, targetEq, argumentStep⟩ :=
                    argumentBranch
                  rw [targetEq]
                  exact argumentIH argumentAfter argumentStep))
    argumentTerminates

/-- A lambda-headed application is strongly normalizing when its normal body
substitutes to a fixed strongly-normalizing contractum, independent of the
argument reduct.

This packages the closed-body beta base case used by the future reducibility
proof: the lambda body cannot step, and beta always lands on the same
contractum while argument congruence is handled by accessibility induction. -/
theorem appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    {scope : Nat} {body : RawTerm (scope + 1)}
    {contractum argumentTerm : RawTerm scope}
    (bodyHasNoStep :
      ∀ targetBody : RawTerm (scope + 1), Step body targetBody → False)
    (contractumTerminates : IsStronglyNormalizing contractum)
    (bodySubst0Constant :
      ∀ currentArgument : RawTerm scope,
        RawTerm.subst0 body currentArgument = contractum)
    (argumentTerminates : IsStronglyNormalizing argumentTerm) :
    IsStronglyNormalizing
      (.mkGen .gen_app ()
        (.childCons
          (.mkGen .gen_lam () (.childCons body .childNil))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_contractum
    bodyHasNoStep
    (contractumTerminates := fun {currentArgument} _argumentTerminates => by
      rw [bodySubst0Constant currentArgument]
      exact contractumTerminates)
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
              (.mkGen .gen_var
                (⟨0, Nat.zero_lt_succ scope⟩ : Fin (scope + 1))
                .childNil)
              .childNil))
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
              (.mkGen .gen_var
                (⟨predIndex + 1, indexBound⟩ : Fin (scope + 1))
                .childNil)
              .childNil))
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
              (.mkGen .gen_unit () .childNil : RawTerm (scope + 1))
              .childNil))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_unit () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_unit () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_unit (targetTerm := targetBody) bodyStep)
    (contractumTerminates := unit_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
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
              (.mkGen .gen_boolTrue () .childNil : RawTerm (scope + 1))
              .childNil))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_boolTrue () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_boolTrue () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_boolTrue (targetTerm := targetBody) bodyStep)
    (contractumTerminates := boolTrue_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
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
              (.mkGen .gen_boolFalse () .childNil : RawTerm (scope + 1))
              .childNil))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_boolFalse () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_boolFalse () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_boolFalse (targetTerm := targetBody) bodyStep)
    (contractumTerminates := boolFalse_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
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
              (.mkGen .gen_natZero () .childNil : RawTerm (scope + 1))
              .childNil))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_natZero () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_natZero () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_natZero (targetTerm := targetBody) bodyStep)
    (contractumTerminates := natZero_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
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
              (.mkGen .gen_listNil () .childNil : RawTerm (scope + 1))
              .childNil))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_listNil () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_listNil () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_listNil (targetTerm := targetBody) bodyStep)
    (contractumTerminates := listNil_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
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
              (.mkGen .gen_optionNone () .childNil : RawTerm (scope + 1))
              .childNil))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  appLam_isStronglyNormalizing_of_normal_body_constant_contractum
    (body := (.mkGen .gen_optionNone () .childNil : RawTerm (scope + 1)))
    (contractum := (.mkGen .gen_optionNone () .childNil : RawTerm scope))
    (bodyHasNoStep := fun targetBody bodyStep =>
      noStep_optionNone (targetTerm := targetBody) bodyStep)
    (contractumTerminates := optionNone_isStronglyNormalizing)
    (bodySubst0Constant := fun _currentArgument => rfl)
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
    {scope : Nat} {body : RawTerm (scope + 1)}
    {argumentTerm : RawTerm scope}
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
          (.mkGen .gen_lam () (.childCons body .childNil))
          (.childCons argumentTerm .childNil)) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentBody =>
      ∀ {currentArgument : RawTerm scope},
        IsStronglyNormalizing currentArgument →
          IsStronglyNormalizing
            (.mkGen .gen_app ()
              (.childCons
                (.mkGen .gen_lam ()
                  (.childCons currentBody .childNil))
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
                    (.childCons currentBody .childNil))
                  (.childCons innerArgument .childNil)) :
                RawTerm scope))
          (m := fun currentArgument currentArgumentSuccessors argumentIH =>
            Acc.intro
              (.mkGen .gen_app ()
                (.childCons
                  (.mkGen .gen_lam ()
                    (.childCons currentBody .childNil))
                  (.childCons currentArgument .childNil)) :
                RawTerm scope)
              (fun targetTerm applicationStep => by
                cases Step.from_app applicationStep with
                | inl betaBranch =>
                    obtain ⟨lambdaBody, lambdaEq, targetEq⟩ := betaBranch
                    cases lambdaEq
                    rw [targetEq]
                    exact
                      contractumTerminates
                        (Acc.intro currentBody currentBodySuccessors)
                        (Acc.intro currentArgument currentArgumentSuccessors)
                | inr congruenceBranch =>
                    cases congruenceBranch with
                    | inl functionBranch =>
                        obtain ⟨functionAfter, targetEq, functionStep⟩ :=
                          functionBranch
                        obtain ⟨bodyAfter, functionAfterEq, bodyStep⟩ :=
                          Step.from_lam functionStep
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
    bodyTerminates)
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

/-- Boolean elimination on the literal `true` is strongly normalizing when both
branches are strongly normalizing.

The root iota reduct is the then-branch.  Congruence at the scrutinee is
impossible because `boolTrue` is a normal leaf; congruence in either branch is
handled by nested accessibility induction on the branches. -/
theorem boolElimTrue_isStronglyNormalizing_of_branches {scope : Nat}
    {thenBranch elseBranch : RawTerm scope}
    (thenTerminates : IsStronglyNormalizing thenBranch)
    (elseTerminates : IsStronglyNormalizing elseBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_boolElim ()
        (.childCons
          (.mkGen .gen_boolTrue () .childNil)
          (.childCons thenBranch (.childCons elseBranch .childNil))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentThen =>
      ∀ {currentElse : RawTerm scope},
        IsStronglyNormalizing currentElse →
          IsStronglyNormalizing
            (.mkGen .gen_boolElim ()
              (.childCons
                (.mkGen .gen_boolTrue () .childNil)
                (.childCons currentThen
                  (.childCons currentElse .childNil))) : RawTerm scope))
    (m := fun currentThen currentThenSuccessors thenBranchIH => by
      intro currentElse currentElseTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerElse =>
            IsStronglyNormalizing
              (.mkGen .gen_boolElim ()
                (.childCons
                  (.mkGen .gen_boolTrue () .childNil)
                  (.childCons currentThen
                    (.childCons innerElse .childNil))) : RawTerm scope))
          (m := fun currentElse currentElseSuccessors elseBranchIH =>
            Acc.intro
              (.mkGen .gen_boolElim ()
                (.childCons
                  (.mkGen .gen_boolTrue () .childNil)
                  (.childCons currentThen
                    (.childCons currentElse .childNil))) : RawTerm scope)
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
                        | inl scrutineeBranch =>
                            obtain ⟨_, _, scrutineeStep⟩ := scrutineeBranch
                            exact False.elim (noStep_boolTrue scrutineeStep)
                        | inr restAfterScrutinee =>
                            cases restAfterScrutinee with
                            | inl thenBranchStep =>
                                obtain ⟨thenAfter, targetEq, thenStep⟩ :=
                                  thenBranchStep
                                rw [targetEq]
                                exact thenBranchIH thenAfter thenStep
                                  (Acc.intro currentElse currentElseSuccessors)
                            | inr elseBranchStep =>
                                obtain ⟨elseAfter, targetEq, elseStep⟩ :=
                                  elseBranchStep
                                rw [targetEq]
                                exact elseBranchIH elseAfter elseStep))
          currentElseTerminates)
    thenTerminates)
    elseTerminates

/-- Boolean elimination on the literal `false` is strongly normalizing when
both branches are strongly normalizing.  Symmetric to the `true` case, with the
root iota reduct selecting the else-branch. -/
theorem boolElimFalse_isStronglyNormalizing_of_branches {scope : Nat}
    {thenBranch elseBranch : RawTerm scope}
    (thenTerminates : IsStronglyNormalizing thenBranch)
    (elseTerminates : IsStronglyNormalizing elseBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_boolElim ()
        (.childCons
          (.mkGen .gen_boolFalse () .childNil)
          (.childCons thenBranch (.childCons elseBranch .childNil))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentThen =>
      ∀ {currentElse : RawTerm scope},
        IsStronglyNormalizing currentElse →
          IsStronglyNormalizing
            (.mkGen .gen_boolElim ()
              (.childCons
                (.mkGen .gen_boolFalse () .childNil)
                (.childCons currentThen
                  (.childCons currentElse .childNil))) : RawTerm scope))
    (m := fun currentThen currentThenSuccessors thenBranchIH => by
      intro currentElse currentElseTerminates
      exact
        Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerElse =>
            IsStronglyNormalizing
              (.mkGen .gen_boolElim ()
                (.childCons
                  (.mkGen .gen_boolFalse () .childNil)
                  (.childCons currentThen
                    (.childCons innerElse .childNil))) : RawTerm scope))
          (m := fun currentElse currentElseSuccessors elseBranchIH =>
            Acc.intro
              (.mkGen .gen_boolElim ()
                (.childCons
                  (.mkGen .gen_boolFalse () .childNil)
                  (.childCons currentThen
                    (.childCons currentElse .childNil))) : RawTerm scope)
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
                        | inl scrutineeBranch =>
                            obtain ⟨_, _, scrutineeStep⟩ := scrutineeBranch
                            exact False.elim (noStep_boolFalse scrutineeStep)
                        | inr restAfterScrutinee =>
                            cases restAfterScrutinee with
                            | inl thenBranchStep =>
                                obtain ⟨thenAfter, targetEq, thenStep⟩ :=
                                  thenBranchStep
                                rw [targetEq]
                                exact thenBranchIH thenAfter thenStep
                                  (Acc.intro currentElse currentElseSuccessors)
                            | inr elseBranchStep =>
                                obtain ⟨elseAfter, targetEq, elseStep⟩ :=
                                  elseBranchStep
                                rw [targetEq]
                                exact elseBranchIH elseAfter elseStep))
          currentElseTerminates)
    thenTerminates)
    elseTerminates

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
        ∀ lambdaBody : RawTerm (scope + 1),
          currentHead ≠ .mkGen .gen_lam () (.childCons lambdaBody .childNil))
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
        ∀ lambdaBody : RawTerm (scope + 1),
          currentHead ≠ .mkGen .gen_lam () (.childCons lambdaBody .childNil))
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
    {nilBranch consBranch : RawTerm scope}
    (nilTerminates : IsStronglyNormalizing nilBranch)
    (consTerminates : IsStronglyNormalizing consBranch) :
    IsStronglyNormalizing
      (.mkGen .gen_listElim ()
        (.childCons
          (.mkGen .gen_listNil () .childNil)
          (.childCons nilBranch (.childCons consBranch .childNil))) :
        RawTerm scope) :=
  isStronglyNormalizing_of_twoBranchProjectionRedex
    (fun currentNil currentCons =>
      (.mkGen .gen_listElim ()
        (.childCons
          (.mkGen .gen_listNil () .childNil)
          (.childCons currentNil (.childCons currentCons .childNil))) :
        RawTerm scope))
    (fun parentStep => by
      cases Step.from_listElim parentStep with
      | inl nilBranchStep =>
          exact Or.inl nilBranchStep.2
      | inr restAfterNil =>
          cases restAfterNil with
          | inl consBranchStep =>
              obtain ⟨headVal, tailVal, scrutineeEq, _⟩ := consBranchStep
              cases scrutineeEq
          | inr restAfterCons =>
              cases restAfterCons with
              | inl scrutineeBranch =>
                  obtain ⟨_, _, scrutineeStep⟩ := scrutineeBranch
                  exact False.elim (noStep_listNil scrutineeStep)
              | inr restAfterScrutinee =>
                  cases restAfterScrutinee with
                  | inl nilStep =>
                      obtain ⟨nilAfter, targetEq, nilStepInner⟩ := nilStep
                      exact Or.inr
                        (Or.inl ⟨nilAfter, targetEq, nilStepInner⟩)
                  | inr consStep =>
                      obtain ⟨consAfter, targetEq, consStepInner⟩ :=
                        consStep
                      exact Or.inr
                        (Or.inr ⟨consAfter, targetEq, consStepInner⟩))
    nilTerminates
    consTerminates

/-- List elimination on `listCons headVal tailVal` is strongly normalizing
when the cons branch is a neutral function head and the recursive call on the
tail is supplied as an explicit accessibility hypothesis.

This is the list analogue of the nat-successor induction-step theorem.  The
root iota reduct is the three-argument application spine
`app (app (app consBranch headVal) tailVal)
  (listElim tailVal nilBranch consBranch)`, so the theorem deliberately
exposes the recursive-call SN obligation instead of claiming recursive
eliminator termination globally. -/
theorem listElimCons_isStronglyNormalizing_of_neutral_consBranch
    {scope : Nat} (isNeutralHead : RawTerm scope → Prop)
    {headVal tailVal nilBranch consBranch : RawTerm scope}
    (headTerminates : IsStronglyNormalizing headVal)
    (tailTerminates : IsStronglyNormalizing tailVal)
    (nilTerminates : IsStronglyNormalizing nilBranch)
    (consBranchIsNeutral : isNeutralHead consBranch)
    (neutralHeadIsNotLambda :
      ∀ {currentHead : RawTerm scope}, isNeutralHead currentHead →
        ∀ lambdaBody : RawTerm (scope + 1),
          currentHead ≠ .mkGen .gen_lam () (.childCons lambdaBody .childNil))
    (neutralHeadStep :
      ∀ {currentHead targetHead : RawTerm scope},
        isNeutralHead currentHead →
          Step currentHead targetHead →
            isNeutralHead targetHead)
    (consTerminates : IsStronglyNormalizing consBranch)
    (recursiveCallTerminates :
      ∀ {currentTailVal currentNilBranch currentConsBranch : RawTerm scope},
        IsStronglyNormalizing currentTailVal →
          IsStronglyNormalizing currentNilBranch →
            isNeutralHead currentConsBranch →
              IsStronglyNormalizing currentConsBranch →
                IsStronglyNormalizing
                  (.mkGen .gen_listElim ()
                    (.childCons currentTailVal
                      (.childCons currentNilBranch
                        (.childCons currentConsBranch .childNil))) :
                    RawTerm scope)) :
    IsStronglyNormalizing
      (.mkGen .gen_listElim ()
        (.childCons
          (.mkGen .gen_listCons ()
            (.childCons headVal (.childCons tailVal .childNil)))
          (.childCons nilBranch (.childCons consBranch .childNil))) :
        RawTerm scope) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentConsBranch =>
      isNeutralHead currentConsBranch →
        ∀ {currentHeadVal : RawTerm scope},
          IsStronglyNormalizing currentHeadVal →
            ∀ {currentTailVal : RawTerm scope},
              IsStronglyNormalizing currentTailVal →
                ∀ {currentNilBranch : RawTerm scope},
                  IsStronglyNormalizing currentNilBranch →
                    IsStronglyNormalizing
                      (.mkGen .gen_listElim ()
                        (.childCons
                          (.mkGen .gen_listCons ()
                            (.childCons currentHeadVal
                              (.childCons currentTailVal .childNil)))
                          (.childCons currentNilBranch
                            (.childCons currentConsBranch .childNil))) :
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
                        (.childCons
                          (.mkGen .gen_listCons ()
                            (.childCons innerHeadVal
                              (.childCons innerTailVal .childNil)))
                          (.childCons innerNilBranch
                            (.childCons currentConsBranch .childNil))) :
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
                          (.childCons
                            (.mkGen .gen_listCons ()
                              (.childCons currentHeadVal
                                (.childCons innerTailVal .childNil)))
                            (.childCons innerNilBranch
                              (.childCons currentConsBranch .childNil))) :
                          RawTerm scope))
                (m := fun currentTailVal currentTailSuccessors tailIH => by
                  intro currentNilBranch currentNilTerminates
                  exact
                    Acc.ndrec
                      (r := StepSuccessor)
                      (C := fun innerNilBranch =>
                        IsStronglyNormalizing
                          (.mkGen .gen_listElim ()
                            (.childCons
                              (.mkGen .gen_listCons ()
                                (.childCons currentHeadVal
                                  (.childCons currentTailVal .childNil)))
                              (.childCons innerNilBranch
                                (.childCons currentConsBranch .childNil))) :
                            RawTerm scope))
                      (m := fun currentNilBranch currentNilSuccessors nilIH =>
                        Acc.intro
                          (.mkGen .gen_listElim ()
                            (.childCons
                              (.mkGen .gen_listCons ()
                                (.childCons currentHeadVal
                                  (.childCons currentTailVal .childNil)))
                              (.childCons currentNilBranch
                                (.childCons currentConsBranch .childNil))) :
                            RawTerm scope)
                          (fun targetTerm parentStep => by
                            cases Step.from_listElim parentStep with
                            | inl nilBranchStep =>
                                obtain ⟨scrutineeEq, _⟩ := nilBranchStep
                                cases scrutineeEq
                            | inr restAfterNil =>
                                cases restAfterNil with
                                | inl consBranchStep =>
                                    obtain
                                      ⟨consHead, consTail, scrutineeEq,
                                        targetEq⟩ := consBranchStep
                                    cases scrutineeEq
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
                                          (Acc.intro currentTailVal
                                            currentTailSuccessors)
                                          (Acc.intro currentNilBranch
                                            currentNilSuccessors)
                                          currentConsBranchIsNeutral
                                          (Acc.intro currentConsBranch
                                            currentConsBranchSuccessors))
                                | inr restAfterCons =>
                                    cases restAfterCons with
                                    | inl scrutineeBranch =>
                                        obtain
                                          ⟨scrutineeAfter, targetEq,
                                            scrutineeStep⟩ := scrutineeBranch
                                        cases Step.from_listCons
                                          scrutineeStep with
                                        | inl headBranch =>
                                            obtain
                                              ⟨headAfter, scrutineeAfterEq,
                                                headStep⟩ := headBranch
                                            rw [targetEq, scrutineeAfterEq]
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
                                            rw [targetEq, scrutineeAfterEq]
                                            exact
                                              tailIH tailAfter tailStep
                                                (Acc.intro currentNilBranch
                                                  currentNilSuccessors)
                                    | inr restAfterScrutinee =>
                                        cases restAfterScrutinee with
                                        | inl nilStep =>
                                            obtain
                                              ⟨nilAfter, targetEq,
                                                nilStepInner⟩ := nilStep
                                            rw [targetEq]
                                            exact nilIH nilAfter nilStepInner
                                        | inr consStep =>
                                            obtain
                                              ⟨consAfter, targetEq,
                                                consStepInner⟩ := consStep
                                            rw [targetEq]
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
                                                  currentNilSuccessors)))
                      currentNilTerminates)
                currentTailTerminates
                currentNilTerminates)
          currentHeadTerminates
          currentTailTerminates
          currentNilTerminates)
    consTerminates)
    consBranchIsNeutral
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
        ∀ lambdaBody : RawTerm (scope + 1),
          currentHead ≠ .mkGen .gen_lam () (.childCons lambdaBody .childNil))
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
        ∀ lambdaBody : RawTerm (scope + 1),
          currentHead ≠ .mkGen .gen_lam () (.childCons lambdaBody .childNil))
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
        ∀ lambdaBody : RawTerm (scope + 1),
          currentHead ≠ .mkGen .gen_lam () (.childCons lambdaBody .childNil))
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
end LeanFX2.Foundation.PolyCell.Core

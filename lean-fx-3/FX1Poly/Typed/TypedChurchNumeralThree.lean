import FX1Poly.Typed.TypedChurchNumeralDiscrimination
import FX1Poly.Core.HeadStep

/-! # FX1Poly/Typed/TypedChurchNumeralThree — the third numeral, and the {1,2,3} non-convertibility antichain

`TypedChurchNumeralDiscrimination.lean` proved `churchOne ≢ churchTwo` (the encoding distinguishes 1 from 2).
This file adds the third Church numeral and lifts that single discrimination to a triple: the numerals `one`,
`two`, `three` are PAIRWISE non-convertible — a 3-element antichain under definitional equality.  Each new
numeral genuinely types as a numeral and computes its own iterate, and each pair is separated through that
computation.

  * `churchThree = λ(A:Type@0). λ(f:A→A). λ(x:A). f (f (f x))` types at the Church Nat type
    `Π(A:Type@0). Π(f:A→A). Π(x:A). A` via a TRIPLE-nested `piElim` — extending `churchTwo`'s double nesting by
    one more `f`-application (the outer `f` applied to the churchTwo body `f (f x)`).  Fed through SN-043, it is
    strongly normalizing.
  * `churchThree_appliedReducesToIterate` — applied to `Type@0/Type@0/Type@1`, `three` β-reduces (the same three
    steps as `one`/`two`, since the reduction peels the three lambdas regardless of body) to its iterate
    `f (f (f x)) = app(Type@0, app(Type@0, app(Type@0, Type@1)))`.
  * `churchOne_notConvertible_churchThree` / `churchTwo_notConvertible_churchThree` — the new discriminations,
    by the iterate route of `TypedChurchNumeralDiscrimination`: the iterates `f x`, `f (f x)`, `f (f (f x))` are
    pairwise distinct no-step normal forms (they differ at a child that bottoms out in `Type@1` versus an
    application — distinct root generators — so `decide` separates them WITHOUT comparing de Bruijn indices,
    keeping it `propext`-free), and `Conv.app_cong ×3` plus the iteration reductions forces any convertibility of
    the numerals down onto their non-convertible iterates.
  * **`churchNumerals_oneTwoThree_pairwiseNotConvertible`** (★) — the antichain: `one`, `two`, `three` are
    pairwise non-convertible.

So the Church encoding distinguishes the iteration counts 1, 2, 3 — a concrete sample of the (general)
faithfulness "the Church encoding of ℕ injects into the term model up to `Conv`".

Zero-axiom: the typing is nested `piIntro`/`piElim` with reduced-form ascriptions (the `churchTwo` pattern); the
reductions are `StepStar.trans` chains of `Step.beta` under `gen_app` congruence; the discriminations reuse
`Conv.iff_eq_of_noStep` + `RawTerm.isStepNormalForm_blocks_step` + structural `decide` + `Conv.app_cong`.  No
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- The bare Church-`three` lambda term `λ(A:Type@0). λ(f:A→A). λ(x:A). f (f (f x))`.  Under T2 each binder
carries its domain annotation (the universe code `Type@0`, the arrow `A→A`, the type variable `A`), exactly the
domains `churchNumeralLambda` uses — so `churchNumeralLambda 3 = churchThreeLambda` holds by `rfl`. -/
abbrev churchThreeLambda : RawTerm 0 :=
  lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
    (lamCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
      (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
        (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
          (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
            (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
              (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))))))

/-- ★ The Church numeral `three`, `λ(A:Type@0). λ(f:A→A). λ(x:A). f (f (f x))`, typed at the Church Nat type —
a TRIPLE-nested `piElim`: the outer `f` (`var 1`, at the arrow `A→A`) applied to the churchTwo body `f (f x)`
(itself a double `piElim`), all under the three numeral binders.  The looked-up arrow/variable types of `f`/`x`
are ascribed to their reduced `piTyCodeCell`/`variableCell` forms so the nested `piElim`s' implicit
domain/codomain unify. -/
theorem churchThree_hasTypeDescPi {profile : PolyProfile} :
    HasTypeDescPi profile TypingContext.empty
      churchThreeLambda
      (piTyCodeCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
        (piTyCodeCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
            (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
          (piTyCodeCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))))) := by
  refine HasTypeDescPi.piIntro LevelExpr.lzero.lsucc
    (lmaxAll [lmaxAll [LevelExpr.lzero, LevelExpr.lzero], lmaxAll [LevelExpr.lzero, LevelExpr.lzero]])
    UniverseFlag.standard ?domainTyped ?codomainTyped ?bodyTyped
  · exact HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero UniverseFlag.standard)
  · exact churchNatCodomain UniverseFlag.standard
  · refine HasTypeDescPi.piIntro (lmaxAll [LevelExpr.lzero, LevelExpr.lzero])
      (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) UniverseFlag.standard
      ?midDomainTyped ?midCodomainTyped ?midBodyTyped
    · exact churchNatArrow UniverseFlag.standard
    · exact churchNatRest UniverseFlag.standard
    · refine HasTypeDescPi.piIntro LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard
        ?inDomainTyped ?inCodomainTyped ?inBodyTyped
      · exact HasTypeDescPi.ofFormation
          (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
      · exact HasTypeDescPi.ofFormation
          (HasTypeDesc.var _ (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))
      · exact HasTypeDescPi.piElim
          (functionTyped :=
            (HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3)) :
              HasTypeDescPi profile _ (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
                (piTyCodeCell
                  (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))
                  (variableCell (⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ
                    (Nat.succ_lt_succ (Nat.succ_pos 0)))⟩ : Fin 4)))))
          (argumentTyped :=
            (HasTypeDescPi.piElim
              (functionTyped :=
                (HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3)) :
                  HasTypeDescPi profile _ (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
                    (piTyCodeCell
                      (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))
                      (variableCell (⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ
                        (Nat.succ_lt_succ (Nat.succ_pos 0)))⟩ : Fin 4)))))
              (argumentTyped :=
                (HasTypeDescPi.piElim
                  (functionTyped :=
                    (HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3)) :
                      HasTypeDescPi profile _ (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
                        (piTyCodeCell
                          (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))
                          (variableCell (⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ
                            (Nat.succ_lt_succ (Nat.succ_pos 0)))⟩ : Fin 4)))))
                  (argumentTyped :=
                    (HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 2⟩ : Fin 3)) :
                      HasTypeDescPi profile _ (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))
                        (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3)))) :
                  HasTypeDescPi profile _
                    (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
                      (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))
                    (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3)))) :
              HasTypeDescPi profile _
                (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
                  (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
                    (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))))
                (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))))

/-- The Church numeral `three` is strongly normalizing — SN-043 on the triple-`piElim` derivation. -/
theorem churchThree_stronglyNormalizing {profile : PolyProfile} (_flag : UniverseFlag) :
    IsStronglyNormalizing (churchThreeLambda : RawTerm 0) :=
  HasTypeDescPi.closedStronglyNormalizing (churchThree_hasTypeDescPi (profile := profile))

/-- The thrice-iterate `f (f (f x)) = app(Type@0, app(Type@0, app(Type@0, Type@1)))` — what `churchThree`
computes on the fixtures. -/
abbrev churchThreeIterate : RawTerm 0 :=
  appCell numeralTypeZeroCode (appCell numeralTypeZeroCode (appCell numeralTypeZeroCode numeralTypeOneCode))

/-- The thrice-iterate is a no-step normal form (a stack of applications headed by universe codes). -/
theorem churchThreeIterate_isStepNormalForm : RawTerm.isStepNormalForm churchThreeIterate := rfl

/-- ★ `three A f x` β-reduces (three steps) to `f (f (f x))` — the step applied THREE times.  The reduction
peels the three numeral binders exactly as for `one`/`two`; only the substituted body (deeper by one
application) differs. -/
theorem churchThree_appliedReducesToIterate (flag : UniverseFlag) :
    StepStar
      (appCell (appCell (appCell churchThreeLambda
          (universeCodeCell LevelExpr.lzero flag))
          (universeCodeCell LevelExpr.lzero flag))
        (universeCodeCell LevelExpr.lzero.lsucc flag))
      (appCell (universeCodeCell LevelExpr.lzero flag)
        (appCell (universeCodeCell LevelExpr.lzero flag)
          (appCell (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero.lsucc flag)))) :=
  StepStar.trans
    (Step.cong .gen_app ()
      (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
        ((.childCons (universeCodeCell LevelExpr.lzero.lsucc flag) .childNil) : RawTermChildren [0] 0)
        (Step.cong .gen_app ()
          (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
            ((.childCons (universeCodeCell LevelExpr.lzero flag) .childNil) : RawTermChildren [0] 0)
            HeadStep.beta.toStep))))
    (StepStar.trans
      (Step.cong .gen_app ()
        (StepChildren.here (parentScope := 0) (headShift := 0) (restShifts := [0])
          ((.childCons (universeCodeCell LevelExpr.lzero.lsucc flag) .childNil) : RawTermChildren [0] 0)
          HeadStep.beta.toStep))
      (StepStar.trans HeadStep.beta.toStep (StepStar.refl _)))

/-- The once-iterate and the thrice-iterate are not convertible (distinct no-step normal forms; the structural
difference bottoms out in `Type@1` vs an application, so `decide` is `propext`-free). -/
theorem churchOneIterate_notConvertible_churchThreeIterate : ¬ Conv churchOneIterate churchThreeIterate :=
  fun convertibility =>
    absurd
      ((Conv.iff_eq_of_noStep
          (fun reduct step =>
            RawTerm.isStepNormalForm_blocks_step churchOneIterate_isStepNormalForm reduct step)
          (fun reduct step =>
            RawTerm.isStepNormalForm_blocks_step churchThreeIterate_isStepNormalForm reduct step)).mp
        convertibility)
      (by decide)

/-- The twice-iterate and the thrice-iterate are not convertible (distinct no-step normal forms). -/
theorem churchTwoIterate_notConvertible_churchThreeIterate : ¬ Conv churchTwoIterate churchThreeIterate :=
  fun convertibility =>
    absurd
      ((Conv.iff_eq_of_noStep
          (fun reduct step =>
            RawTerm.isStepNormalForm_blocks_step churchTwoIterate_isStepNormalForm reduct step)
          (fun reduct step =>
            RawTerm.isStepNormalForm_blocks_step churchThreeIterate_isStepNormalForm reduct step)).mp
        convertibility)
      (by decide)

/-- `churchOne ≢ churchThree` — via the iterate route: applied to the fixtures they reduce to `f x` vs
`f (f (f x))`, which are non-convertible. -/
theorem churchOne_notConvertible_churchThree : ¬ Conv churchOneLambda churchThreeLambda := by
  intro convNumerals
  have convApplied :
      Conv (appCell (appCell (appCell churchOneLambda numeralTypeZeroCode) numeralTypeZeroCode) numeralTypeOneCode)
           (appCell (appCell (appCell churchThreeLambda numeralTypeZeroCode) numeralTypeZeroCode) numeralTypeOneCode) :=
    Conv.app_cong (Conv.app_cong (Conv.app_cong convNumerals (Conv.refl _)) (Conv.refl _)) (Conv.refl _)
  have convIterates : Conv churchOneIterate churchThreeIterate :=
    Conv.trans
      (Conv.sym (Conv.fromStepStar (churchOne_appliedReducesToIterate UniverseFlag.standard)))
      (Conv.trans convApplied
        (Conv.fromStepStar (churchThree_appliedReducesToIterate UniverseFlag.standard)))
  exact churchOneIterate_notConvertible_churchThreeIterate convIterates

/-- `churchTwo ≢ churchThree` — via the iterate route: applied to the fixtures they reduce to `f (f x)` vs
`f (f (f x))`, which are non-convertible. -/
theorem churchTwo_notConvertible_churchThree : ¬ Conv churchTwoLambda churchThreeLambda := by
  intro convNumerals
  have convApplied :
      Conv (appCell (appCell (appCell churchTwoLambda numeralTypeZeroCode) numeralTypeZeroCode) numeralTypeOneCode)
           (appCell (appCell (appCell churchThreeLambda numeralTypeZeroCode) numeralTypeZeroCode) numeralTypeOneCode) :=
    Conv.app_cong (Conv.app_cong (Conv.app_cong convNumerals (Conv.refl _)) (Conv.refl _)) (Conv.refl _)
  have convIterates : Conv churchTwoIterate churchThreeIterate :=
    Conv.trans
      (Conv.sym (Conv.fromStepStar (churchTwo_appliedReducesToIterate UniverseFlag.standard)))
      (Conv.trans convApplied
        (Conv.fromStepStar (churchThree_appliedReducesToIterate UniverseFlag.standard)))
  exact churchTwoIterate_notConvertible_churchThreeIterate convIterates

/-- ★ The three Church numerals `one`, `two`, `three` form a pairwise-non-convertible 3-antichain under
definitional equality — a concrete sample of the faithfulness of the Church encoding of ℕ. -/
theorem churchNumerals_oneTwoThree_pairwiseNotConvertible :
    (¬ Conv churchOneLambda churchTwoLambda)
    ∧ (¬ Conv churchOneLambda churchThreeLambda)
    ∧ (¬ Conv churchTwoLambda churchThreeLambda) :=
  ⟨churchOne_notConvertible_churchTwo,
    churchOne_notConvertible_churchThree,
    churchTwo_notConvertible_churchThree⟩

end FX1Poly.Typed

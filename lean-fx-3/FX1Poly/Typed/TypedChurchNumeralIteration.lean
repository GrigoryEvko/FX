import FX1Poly.Typed.TypedChurchNumerals
import FX1Poly.Core.HeadStep

/-! # FX1Poly/Typed/TypedChurchNumeralIteration — the Church numerals COMPUTE their iteration

`TypedChurchNumerals.lean` (CHURCH-NAT) typed the Church numeral `one` and the Church Nat type.  Beyond typing
and SN, a numeral must COMPUTE: applied to a type `A`, a step `f : A→A`, and a base `x : A`, the numeral `n`
must iterate `f` exactly `n` times over `x`.  This file exhibits that — the numeral analogue of
`TypedChurchBooleans`' β-selection — and adds the second numeral `two` (typed via a NESTED `piElim`).

Applied to `A=Type@0`, `f=Type@0`, `x=Type@1` (concrete closed codes, as in the boolean selection fixtures):

  * **`churchOne_appliedReducesToIterate`** — `one A f x` β-reduces (three steps) to `f x` (= `app(Type@0,
    Type@1)`): the step `f` applied ONCE to the base.
  * **`churchTwo_hasTypeDescPi`** — `two = λA.λf.λx. f (f x)` typed at the Church Nat type.  Its body is a
    NESTED `piElim` (`f` applied to `f x`), the outer application's argument being the inner one — extending
    `churchOne`'s single `piElim`.  `churchTwo_stronglyNormalizing` feeds it through SN-043.
  * **`churchTwo_appliedReducesToIterate`** — `two A f x` β-reduces (three steps) to `f (f x)` (= `app(Type@0,
    app(Type@0, Type@1))`): the step `f` applied TWICE.

So `one` and `two` compute distinct iterates of the same inputs — `f x` vs `f (f x)` — exactly the iteration
COUNT the numerals encode.  The polymorphic Π-fragment expresses the naturals AND its β-reduction realizes
their iteration semantics, just as the Church booleans' β-reduction realized selection.

A de Bruijn note (as in the boolean selection): the step `f` is the NON-innermost binder (`var 1`), whose
`subst0` threads the lifting fold — which only fully computes on CONCRETE closed arguments; hence the concrete
codes here.  The numerals' universal iteration (for ARBITRARY `f`/`x`, via a substitution lemma rather than
computation) remains a natural follow-up.

NOTE on uniqueness: `churchZero = λλλ.var0` is omitted (per CHURCH-NAT) — its raw term is `churchFalseLambda`,
already typed at the Church BOOL type, and `grownTypingNotUnique` already records that the grown (Curry-style)
engine assigns non-unique types to un-annotated lambdas, so a churchZero-at-Nat witness would be redundant.

Zero-axiom: the reductions are `StepStar.trans` chains of `Step.beta` under `gen_app` congruence (mirroring the
boolean selection); `churchTwo`'s typing is nested `HasTypeDescPi.piElim` with the looked-up arrow/var types
ascribed to their reduced forms.  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.
Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- ★ `one A f x` β-reduces (three steps) to `f x` — the step applied ONCE.  At `A=Type@0`, `f=Type@0`,
`x=Type@1` the iterate is `app(Type@0, Type@1)`.  The numeral analogue of `churchTrue_selectsThenBranch`: the
encoding's β-reduction realizes iteration. -/
theorem churchOne_appliedReducesToIterate (flag : UniverseFlag) :
    StepStar
      (appCell (appCell (appCell
          (lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
            (lamCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
                (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
              (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
                (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
                  (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))))))
          (universeCodeCell LevelExpr.lzero flag))
          (universeCodeCell LevelExpr.lzero flag))
        (universeCodeCell LevelExpr.lzero.lsucc flag))
      (appCell (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero.lsucc flag)) :=
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

/-- ★ The Church numeral `two`, `λ(A:Type@0). λ(f:A→A). λ(x:A). f (f x)`, typed at the Church Nat type.  Its
body is a NESTED `piElim` — the outer `f (…)` applies `f` to the inner `f x` — extending `churchOne`'s single
application.  Both the looked-up arrow type of `f` and the inner application's result type are ascribed to their
reduced forms so the nested `piElim`s' implicit domain/codomain unify. -/
theorem churchTwo_hasTypeDescPi {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (lamCell (universeCodeCell LevelExpr.lzero flag)
        (lamCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
            (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
          (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
              (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
                (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))))))
      (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (piTyCodeCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
            (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
          (piTyCodeCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))))) := by
  refine HasTypeDescPi.piIntro LevelExpr.lzero.lsucc
    (lmaxAll [lmaxAll [LevelExpr.lzero, LevelExpr.lzero], lmaxAll [LevelExpr.lzero, LevelExpr.lzero]])
    flag ?domainTyped ?codomainTyped ?bodyTyped
  · exact HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag)
  · exact churchNatCodomain flag
  · refine HasTypeDescPi.piIntro (lmaxAll [LevelExpr.lzero, LevelExpr.lzero])
      (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) flag ?midDomainTyped ?midCodomainTyped ?midBodyTyped
    · exact churchNatArrow flag
    · exact churchNatRest flag
    · refine HasTypeDescPi.piIntro LevelExpr.lzero LevelExpr.lzero flag
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
                (HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 2⟩ : Fin 3)) :
                  HasTypeDescPi profile _ (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))
                    (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3)))) :
              HasTypeDescPi profile _
                (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
                  (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))
                (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))))

/-- The Church numeral `two` is strongly normalizing — SN-043 on the nested-`piElim` derivation. -/
theorem churchTwo_stronglyNormalizing {profile : PolyProfile} (flag : UniverseFlag) :
    IsStronglyNormalizing
      (lamCell (universeCodeCell LevelExpr.lzero flag)
        (lamCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
            (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
          (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
              (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
                (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))))) : RawTerm 0) :=
  HasTypeDescPi.closedStronglyNormalizing (churchTwo_hasTypeDescPi (profile := profile) flag)

/-- ★ `two A f x` β-reduces (three steps) to `f (f x)` — the step applied TWICE.  At `A=Type@0`, `f=Type@0`,
`x=Type@1` the iterate is `app(Type@0, app(Type@0, Type@1))`.  Together with `churchOne_appliedReducesToIterate`
(`f x`), the numerals compute distinct iterates of the same inputs — the iteration COUNT they encode. -/
theorem churchTwo_appliedReducesToIterate (flag : UniverseFlag) :
    StepStar
      (appCell (appCell (appCell
          (lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
            (lamCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
                (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
              (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
                (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
                  (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
                    (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))))))
          (universeCodeCell LevelExpr.lzero flag))
          (universeCodeCell LevelExpr.lzero flag))
        (universeCodeCell LevelExpr.lzero.lsucc flag))
      (appCell (universeCodeCell LevelExpr.lzero flag)
        (appCell (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero.lsucc flag))) :=
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

end FX1Poly.Typed

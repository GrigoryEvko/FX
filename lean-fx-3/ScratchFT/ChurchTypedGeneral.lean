import FX1Poly.Typed.TypedChurchNumeralFaithful

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- The body context `[A:Type@0, f:A→A, x:A]` (scope 3) in which the iterate is typed. -/
def churchBodyContext {profile : PolyProfile} (flag : UniverseFlag) : TypingContext profile 3 :=
  ((TypingContext.empty.cons (universeCodeCell LevelExpr.lzero flag)).cons
    (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
      (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))).cons
    (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))

/-- `iteratedApplication n f x : A` in the body context — by induction on `n` (base = `x` via the var rule;
step = `piElim` of `f : A→A` against the IH, whose `subst0`-codomain is `A` argument-independently). -/
theorem iteratedApplicationBody_hasTypeDescPi {profile : PolyProfile} (flag : UniverseFlag) (n : Nat) :
    HasTypeDescPi profile (churchBodyContext flag)
      (iteratedApplication n
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
        (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))
      (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3)) := by
  induction n with
  | zero =>
      exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 2⟩ : Fin 3))
  | succ priorDepth priorIH =>
      exact HasTypeDescPi.piElim
        (functionTyped :=
          (HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3)) :
            HasTypeDescPi profile _ (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
              (piTyCodeCell
                (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))
                (variableCell (⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ
                  (Nat.succ_lt_succ (Nat.succ_pos 0)))⟩ : Fin 4)))))
        (argumentTyped := priorIH)

/-- ★ Every Church numeral `churchNumeralLambda n = λA.λf.λx. f^n x` is typed at the Church Nat type
`Π(A:Type@0). Π(f:A→A). Π(x:A). A` — three nested `piIntro`s wrapping the general iterate body. -/
theorem churchNumeralLambda_hasTypeDescPi {profile : PolyProfile} (flag : UniverseFlag) (n : Nat) :
    HasTypeDescPi profile TypingContext.empty
      (churchNumeralLambda n)
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
      · exact iteratedApplicationBody_hasTypeDescPi flag n

theorem churchNumeralLambda_stronglyNormalizing {profile : PolyProfile} (flag : UniverseFlag) (n : Nat) :
    IsStronglyNormalizing (churchNumeralLambda n) :=
  HasTypeDescPi.closedStronglyNormalizing (churchNumeralLambda_hasTypeDescPi (profile := profile) flag n)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.iteratedApplicationBody_hasTypeDescPi
#print axioms FX1Poly.Typed.churchNumeralLambda_hasTypeDescPi
#print axioms FX1Poly.Typed.churchNumeralLambda_stronglyNormalizing

import FX1Poly.Typed.TypedChurchNumeralDiscrimination

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- The bare Church-`three` lambda `λA.λf.λx. f (f (f x))`. -/
abbrev churchThreeLambda : RawTerm 0 :=
  lamCell (lamCell (lamCell
    (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
      (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
        (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
          (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))))))

/-- `three = λA.λf.λx. f (f (f x))` typed at the Church Nat type — a TRIPLE-nested `piElim`, extending
churchTwo's double nesting by one more `f`-application. -/
theorem churchThree_hasTypeDescPi {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      churchThreeLambda
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
      · -- body f (f (f x)) : outer f applied to the churchTwo body f (f x)
        exact HasTypeDescPi.piElim
          (functionTyped :=
            (HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3)) :
              HasTypeDescPi profile _ (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
                (piTyCodeCell
                  (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))
                  (variableCell (⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ
                    (Nat.succ_lt_succ (Nat.succ_pos 0)))⟩ : Fin 4)))))
          (argumentTyped :=
            -- f (f x) : A   (churchTwo's body, as the argument)
            (HasTypeDescPi.piElim
              (functionTyped :=
                (HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3)) :
                  HasTypeDescPi profile _ (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
                    (piTyCodeCell
                      (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))
                      (variableCell (⟨3, Nat.succ_lt_succ (Nat.succ_lt_succ
                        (Nat.succ_lt_succ (Nat.succ_pos 0)))⟩ : Fin 4)))))
              (argumentTyped :=
                -- f x : A
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

theorem churchThree_stronglyNormalizing {profile : PolyProfile} (flag : UniverseFlag) :
    IsStronglyNormalizing (churchThreeLambda : RawTerm 0) :=
  HasTypeDescPi.closedStronglyNormalizing (churchThree_hasTypeDescPi (profile := profile) flag)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.churchThree_hasTypeDescPi
#print axioms FX1Poly.Typed.churchThree_stronglyNormalizing

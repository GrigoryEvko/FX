namespace FX1Poly.Modal

-- §6.8's ONLY three-way collision: classified × async × session. Each flag = true when that dimension's risky
-- capability is granted (classified info present / Async effect / session-typed channel). The triple is unsound
-- (a classified value's ordering leaks through async session interleaving) but ANY TWO compose soundly.
def IsClassifiedAsyncSessionAdmissible (classified async session : Bool) : Prop :=
  ¬ (classified = true ∧ async = true ∧ session = true)

theorem classifiedAsyncSessionCollision :
    ¬ IsClassifiedAsyncSessionAdmissible true true true :=
  fun admissible => admissible ⟨rfl, rfl, rfl⟩

theorem classifiedAsync_admissibleWithoutSession :
    IsClassifiedAsyncSessionAdmissible true true false :=
  fun conjunction => Bool.noConfusion conjunction.2.2

theorem classifiedSession_admissibleWithoutAsync :
    IsClassifiedAsyncSessionAdmissible true false true :=
  fun conjunction => Bool.noConfusion conjunction.2.1

theorem asyncSession_admissibleWithoutClassified :
    IsClassifiedAsyncSessionAdmissible false true true :=
  fun conjunction => Bool.noConfusion conjunction.1

theorem classifiedAsyncSessionIrreducible :
    IsClassifiedAsyncSessionAdmissible true true false ∧
    IsClassifiedAsyncSessionAdmissible true false true ∧
    IsClassifiedAsyncSessionAdmissible false true true :=
  ⟨classifiedAsync_admissibleWithoutSession,
   classifiedSession_admissibleWithoutAsync,
   asyncSession_admissibleWithoutClassified⟩

theorem isAdmissible_iff (classified async session : Bool) :
    IsClassifiedAsyncSessionAdmissible classified async session ↔
      (classified = false ∨ async = false ∨ session = false) := by
  unfold IsClassifiedAsyncSessionAdmissible
  constructor
  · intro notAll
    cases classified
    · exact Or.inl rfl
    · cases async
      · exact Or.inr (Or.inl rfl)
      · cases session
        · exact Or.inr (Or.inr rfl)
        · exact absurd ⟨rfl, rfl, rfl⟩ notAll
  · rintro disjunct ⟨hClassified, hAsync, hSession⟩
    cases disjunct with
    | inl h => rw [hClassified] at h; exact Bool.noConfusion h
    | inr h => cases h with
      | inl h => rw [hAsync] at h; exact Bool.noConfusion h
      | inr h => rw [hSession] at h; exact Bool.noConfusion h

end FX1Poly.Modal

#print axioms FX1Poly.Modal.classifiedAsyncSessionCollision
#print axioms FX1Poly.Modal.classifiedAsyncSessionIrreducible
#print axioms FX1Poly.Modal.isAdmissible_iff

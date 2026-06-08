import FX1Poly.Typed.WfContext
open FX1Poly.Typed FX1Poly.Core FX1Poly.Foundation

-- Test 2: induction with scope-dependent existential in goal (like OB-3)
theorem t2 {profile : PolyProfile} {scope : Nat} (context : TypingContext profile scope) :
    ∃ _s : RawTermSubst scope 1, True := by
  induction context with
  | empty => exact ⟨Fin.elim0, True.intro⟩
  | cons rest binding ih =>
      obtain ⟨s, _⟩ := ih
      exact ⟨RawTermSubst.cons (.mkGen .gen_var ⟨0, Nat.zero_lt_one⟩ .childNil) s, True.intro⟩

-- Test 3: same but with the substitution and a real reducible-env-shaped goal placeholder
theorem t3 {profile : PolyProfile} {scope : Nat} (context : TypingContext profile scope) :
    ∃ _b : Nat, ∃ _s : RawTermSubst scope 1, True := by
  induction context with
  | empty => exact ⟨0, Fin.elim0, True.intro⟩
  | cons rest binding ih =>
      obtain ⟨b, s, _⟩ := ih
      exact ⟨b, RawTermSubst.cons (.mkGen .gen_var ⟨0, Nat.zero_lt_one⟩ .childNil) s, True.intro⟩

#print axioms t2
#print axioms t3

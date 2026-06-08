import FX1Poly.Typed.FormationCanonicalForms

/-! Scratch: piElim-killing toolkit — lam reconstruction + "type-former/universe is not a Π-type member". -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- head = gen_lam → cell = lamCell body (the missing 4th head→shape reconstruction). -/
theorem eq_lamCell_of_headGenerator {scope : Nat} {cell : RawTerm scope}
    (headIsLam : RawTerm.headGenerator cell = Generator.gen_lam) :
    ∃ body : RawTerm (scope + 1), cell = lamCell body := by
  cases cell with
  | mkGen generator payload children =>
      change generator = Generator.gen_lam at headIsLam
      subst headIsLam
      change RawTermChildren [1] scope at children
      cases children with
      | childCons body tailChildren =>
          refine ⟨body, ?_⟩
          rw [RawTermChildren.eq_childNil tailChildren]
          rfl

/-- A Π-type FORMER is not a member of a Π-type: its classifier (the would-be Π-type) is Conv a universe code
(invertPiTyCode), which a Π-code is not (Conv.piTyCode_not_universeCode). -/
theorem HasTypeDescPi.piFormerNotTypedAtPiType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {innerDomain : RawTerm scope} {innerCodomain : RawTerm (scope + 1)}
    {outerDomain : RawTerm scope} {outerCodomain : RawTerm (scope + 1)}
    (typed :
      HasTypeDescPi profile context (piTyCodeCell innerDomain innerCodomain)
        (piTyCodeCell outerDomain outerCodomain))
    (wellFormed : WfContext context) :
    False := by
  obtain ⟨_, _, _, _, _, convToUniverseCode⟩ := HasTypeDescPi.invertPiTyCode typed wellFormed
  exact Conv.piTyCode_not_universeCode convToUniverseCode

/-- A Σ-type former is not a member of a Π-type — the Σ dual. -/
theorem HasTypeDescPi.sigmaFormerNotTypedAtPiType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {innerDomain : RawTerm scope} {innerCodomain : RawTerm (scope + 1)}
    {outerDomain : RawTerm scope} {outerCodomain : RawTerm (scope + 1)}
    (typed :
      HasTypeDescPi profile context (sigmaTyCodeCell innerDomain innerCodomain)
        (piTyCodeCell outerDomain outerCodomain))
    (wellFormed : WfContext context) :
    False := by
  obtain ⟨_, _, _, _, _, convToUniverseCode⟩ := HasTypeDescPi.invertSigmaTyCode typed wellFormed
  exact Conv.piTyCode_not_universeCode convToUniverseCode

/-- A universe code is not a member of a Π-type — its classifier (the would-be Π-type) is Conv the next
universe (inversionUniverseCode), which a Π-code is not. -/
theorem HasTypeDescPi.universeCodeNotTypedAtPiType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {levelExpr : LevelExpr} {flag : UniverseFlag}
    {outerDomain : RawTerm scope} {outerCodomain : RawTerm (scope + 1)}
    (typed :
      HasTypeDescPi profile context (universeCodeCell levelExpr flag)
        (piTyCodeCell outerDomain outerCodomain))
    (wellFormed : WfContext context) :
    False :=
  Conv.piTyCode_not_universeCode (HasTypeDescPi.inversionUniverseCode typed wellFormed)

#print axioms FX1Poly.Typed.eq_lamCell_of_headGenerator
#print axioms FX1Poly.Typed.HasTypeDescPi.piFormerNotTypedAtPiType
#print axioms FX1Poly.Typed.HasTypeDescPi.sigmaFormerNotTypedAtPiType
#print axioms FX1Poly.Typed.HasTypeDescPi.universeCodeNotTypedAtPiType

end FX1Poly.Typed

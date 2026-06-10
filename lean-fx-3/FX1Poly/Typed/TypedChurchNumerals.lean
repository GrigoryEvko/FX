import FX1Poly.Typed.TypedChurchBooleans

/-! # FX1Poly/Typed/TypedChurchNumerals — the Church-numeral encoding, typed by the grown engine

`TypedChurchBooleans.lean` showed the formation-only Π-fragment Church-encodes the BOOLEANS despite rejecting
the primitive `boolTrue`/`boolFalse` constructors.  This file does the same for the NATURALS — the genuinely
recursive datum — exhibiting the Church NUMERAL `one` typed end-to-end and strongly normalizing.

A Church numeral is the polymorphic iterator `Π(A:Type@0). Π(f:A→A). Π(x:A). A` — given a result type `A`, a
step `f : A→A`, and a base `x : A`, it iterates `f` over `x`.  The crucial difference from the booleans: the
SECOND binder is a FUNCTION type `A→A`, not the type variable `A`.  So:

  * the TYPE `churchNatType` (`churchNatType_formation`) is a three-level Π whose middle binder's domain is the
    arrow `A→A` (a Π-FORMATION over the type variable, `churchNatArrow`), not a variable — a strictly richer
    formation than the Church-boolean type's `churchOuterArrow` (whose binders are all variables);
  * `churchOne = λ(A:Type@0). λ(f:A→A). λ(x:A). f x` applies the step `f` once to the base `x`.  Its body
    `f x` is an APPLICATION, so it types by the `piElim` rule (not the bare `var` rule the booleans used): `f`
    (de Bruijn `var 1`) at the arrow type `A→A`, applied to `x` (`var 0`) at `A`, yields `A`.  This is the
    first Church-encoding whose body genuinely USES a bound function — `churchOne` CANNOT be typed at the
    Church-boolean type (where the middle binder `t : A` is not a function), so it is unambiguously a numeral.

Both the type and `churchOne` are fed through SN-043 (`HasTypeDescPi.closedStronglyNormalizing`): the Church
Nat type is a strongly-normalizing type code, and `churchOne` is a strongly-normalizing term.  The Π-fragment
thus encodes the naturals AND proves the encoding terminating — extending the booleans to the recursive datum.

The `churchZero = λA.λf.λx. x` numeral is DELIBERATELY OMITTED: its bare term `λλλ.var0` is identical to
`churchFalseLambda`, already typed at the Church-boolean type, so re-typing it at the Church Nat type would
interact with uniqueness-of-typing (#469) — a Curry-style subtlety worth its own investigation.  `churchOne`
sidesteps this entirely (its `f x` body forces the function binder), which is why it is the chosen witness.

Zero-axiom: every derivation is a direct constructor application.  The only non-`rfl` steps are the nested
`lmaxAll` level threading (the Church Nat type lives at `Type@(lmax 1 (lmax (lmax 0 0) (lmax 0 0)))`) and, in
`churchOne`, the `piElim` whose function/argument looked-up types are ASCRIBED to their reduced
`piTyCodeCell`/`variableCell` forms (the `TypingContext.lookup` of `f`/`x` at de Bruijn depths 1/0 computes to
`A→A`/`A`, but the ascription is needed so `piElim`'s implicit `domainCode`/`codomainCode` unify).  No
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- In context `[A:Type@0]`, the arrow `A→A = Π(_:A).A` is a Π-FORMATION at `Type@(lmax 0 0)` — the domain of
the Church numeral's step binder `f`.  Both the domain `A` (`var 0`) and the codomain `A` (`var 1`, under the
`_:A` binder) are the type variable. -/
theorem churchNatArrow {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile
      (TypingContext.empty.cons (universeCodeCell LevelExpr.lzero flag))
      (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
      (universeCodeCell (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) flag) := by
  refine HasTypeDescPi.genFormationPi _ .gen_piTyCode () _
    [LevelExpr.lzero, LevelExpr.lzero] flag { outputType := universeFormerOutput } rfl ?premises
  refine DescTelescopePi.cons _ _ _ _ _ _ ?domainTyped ?codomainTelescope
  · exact HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 0⟩ : Fin 1))
  · refine DescTelescopePi.cons _ _ _ _ _ _ ?codomainTyped ?nilTelescope
    · exact HasTypeDescPi.ofFormation
        (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
    · exact DescTelescopePi.nil _ _

/-- In context `[A:Type@0, f:A→A]`, the residual `Π(x:A).A` is a Π-FORMATION (the type variable `A` now sits
at the deeper indices `var 1` / `var 2`, past the `f` binder). -/
theorem churchNatRest {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile
      ((TypingContext.empty.cons (universeCodeCell LevelExpr.lzero flag)).cons
        (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
          (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))))
      (piTyCodeCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
        (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3)))
      (universeCodeCell (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) flag) := by
  refine HasTypeDescPi.genFormationPi _ .gen_piTyCode () _
    [LevelExpr.lzero, LevelExpr.lzero] flag { outputType := universeFormerOutput } rfl ?premises
  refine DescTelescopePi.cons _ _ _ _ _ _ ?domainTyped ?codomainTelescope
  · exact HasTypeDescPi.ofFormation
      (HasTypeDesc.var _ (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
  · refine DescTelescopePi.cons _ _ _ _ _ _ ?codomainTyped ?nilTelescope
    · exact HasTypeDescPi.ofFormation
        (HasTypeDesc.var _ (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))
    · exact DescTelescopePi.nil _ _

/-- In context `[A:Type@0]`, the Church numeral's codomain `Π(f:A→A). Π(x:A). A` is a Π-FORMATION whose FIRST
binder's domain is the arrow `A→A` (`churchNatArrow`, a former) — the distinguishing feature versus the
Church-boolean codomain (whose first binder's domain is the variable `A`). -/
theorem churchNatCodomain {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile
      (TypingContext.empty.cons (universeCodeCell LevelExpr.lzero flag))
      (piTyCodeCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
          (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
        (piTyCodeCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
          (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))))
      (universeCodeCell (lmaxAll [lmaxAll [LevelExpr.lzero, LevelExpr.lzero],
        lmaxAll [LevelExpr.lzero, LevelExpr.lzero]]) flag) := by
  refine HasTypeDescPi.genFormationPi _ .gen_piTyCode () _
    [lmaxAll [LevelExpr.lzero, LevelExpr.lzero], lmaxAll [LevelExpr.lzero, LevelExpr.lzero]]
    flag { outputType := universeFormerOutput } rfl ?premises
  refine DescTelescopePi.cons _ _ _ _ _ _ ?domainTyped ?codomainTelescope
  · exact churchNatArrow flag
  · refine DescTelescopePi.cons _ _ _ _ _ _ ?codomainTyped ?nilTelescope
    · exact churchNatRest flag
    · exact DescTelescopePi.nil _ _

/-- ★ The Church NATURAL type `Π(A:Type@0). Π(f:A→A). Π(x:A). A` is well-formed at
`Type@(lmax 1 (lmax (lmax 0 0) (lmax 0 0)))` — the polymorphic iterator type, formed by `genFormationPi` over
the universe binder `A:Type@0` and the arrow-headed codomain `churchNatCodomain`. -/
theorem churchNatType_formation {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (piTyCodeCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
            (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
          (piTyCodeCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3)))))
      (universeCodeCell (lmaxAll [LevelExpr.lzero.lsucc,
        lmaxAll [lmaxAll [LevelExpr.lzero, LevelExpr.lzero],
          lmaxAll [LevelExpr.lzero, LevelExpr.lzero]]]) flag) := by
  refine HasTypeDescPi.genFormationPi _ .gen_piTyCode () _
    [LevelExpr.lzero.lsucc, lmaxAll [lmaxAll [LevelExpr.lzero, LevelExpr.lzero],
      lmaxAll [LevelExpr.lzero, LevelExpr.lzero]]]
    flag { outputType := universeFormerOutput } rfl ?premises
  refine DescTelescopePi.cons _ _ _ _ _ _ ?domainTyped ?codomainTelescope
  · exact HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag)
  · refine DescTelescopePi.cons _ _ _ _ _ _ ?codomainTyped ?nilTelescope
    · exact churchNatCodomain flag
    · exact DescTelescopePi.nil _ _

/-- The Church NATURAL type code is strongly normalizing — SN-043 on the formation derivation. -/
theorem churchNatType_stronglyNormalizing {profile : PolyProfile} (flag : UniverseFlag) :
    IsStronglyNormalizing
      (piTyCodeCell (universeCodeCell LevelExpr.lzero flag)
        (piTyCodeCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
            (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
          (piTyCodeCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))))
        : RawTerm 0) :=
  HasTypeDescPi.closedStronglyNormalizing (churchNatType_formation (profile := profile) flag)

/-- ★ The Church numeral `one`, `λ(A:Type@0). λ(f:A→A). λ(x:A). f x`, typed at
`Π(A:Type@0). Π(f:A→A). Π(x:A). A` — applies the step `f` once to the base `x`.  Via three nested `piIntro`s
(universe binder, arrow binder `f:A→A` typed by `churchNatArrow`, base binder `x:A`); the body `f x` types by
`piElim` — `f` (`var 1`) at the arrow `A→A`, applied to `x` (`var 0`) at `A`, yielding `A`.  The looked-up
arrow/variable types of `f`/`x` are ascribed to their reduced `piTyCodeCell`/`variableCell` forms so `piElim`'s
implicit domain/codomain unify.  The first Church-encoding whose body USES a bound function — unambiguously a
numeral, not a re-typed boolean. -/
theorem churchOne_hasTypeDescPi {profile : PolyProfile} (flag : UniverseFlag) :
    HasTypeDescPi profile TypingContext.empty
      (lamCell (universeCodeCell LevelExpr.lzero flag)
        (lamCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
            (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
          (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
              (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))))))
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
            (HasTypeDescPi.ofFormation (HasTypeDesc.var _ (⟨0, Nat.succ_pos 2⟩ : Fin 3)) :
              HasTypeDescPi profile _ (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))
                (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))))

/-- The Church numeral `one` is strongly normalizing — SN-043 on the concrete nested-`piIntro`/`piElim`
derivation.  The Π-fragment encodes the naturals AND proves the encoding terminating. -/
theorem churchOne_stronglyNormalizing {profile : PolyProfile} (flag : UniverseFlag) :
    IsStronglyNormalizing
      (lamCell (universeCodeCell LevelExpr.lzero flag)
        (lamCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
            (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
          (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
              (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))))) : RawTerm 0) :=
  HasTypeDescPi.closedStronglyNormalizing (churchOne_hasTypeDescPi (profile := profile) flag)

end FX1Poly.Typed

import FX1Poly.Typed.TypedChurchNumeralFaithful

/-! # FX1Poly/Typed/TypedChurchNumeralTyping — every Church numeral is typed at the Church Nat type

`TypedChurchNumeralFaithful.lean` proved the general NON-CONVERTIBILITY (ℕ injects into the term model).  This
file proves the general TYPING — the complementary half of the Church-numeral capstone: for ALL `n`, the Church
numeral `churchNumeralLambda n = λA.λf.λx. f^n x` is well-typed at the Church Nat type
`Π(A:Type@0). Π(f:A→A). Π(x:A). A`, generalizing the concrete `churchOne`/`churchTwo`/`churchThree` derivations to
arbitrary `n` (and hence — via SN-043 — every Church numeral is strongly normalizing).

The crux is the iterate body typed UNIFORMLY in `n`:

  * `iteratedApplicationBody_hasTypeDescPi` — in the body context `[A:Type@0, f:A→A, x:A]`, the iterate
    `iteratedApplication n f x` is typed at `A` (`var 2`), by induction on `n`:
      - base `n = 0`: the iterate is the base `x` (`var 0`), typed at `A` by the `var` rule (its lookup reduces to
        `A`);
      - step `n+1`: the iterate is `f (iterate n)`, typed by `piElim` of the step `f` (`var 1`, at the arrow
        `A→A`) against the inductive hypothesis — and crucially the `piElim` output `subst0 codomainA argument` is
        `A` ARGUMENT-INDEPENDENTLY (the arrow's codomain `A` does not reference the bound variable, so the
        `subst0` merely decrements it), so the same `A`-typed conclusion threads through every step.
  * `churchNumeralLambda_hasTypeDescPi` (★) — three nested `piIntro`s (the universe binder `A`, the arrow binder
    `f:A→A` via `churchNatArrow`, the base binder `x:A`) wrapping the iterate body, typed at the Church Nat type.
  * `churchNumeralLambda_stronglyNormalizing` — SN-043 on the typing: every Church numeral terminates.

`churchOneLambda_hasTypeDescPi_viaGeneral` re-derives the concrete `churchOne` typing as the `n = 1` instance
(`churchNumeralLambda 1 = churchOneLambda` definitionally), so the general theorem subsumes the concrete ones.

Zero-axiom: the iterate induction is `var`-rule + `piElim` (with the looked-up arrow/variable types ascribed to
their reduced forms, as in the concrete numerals); the wrapper is three `piIntro`s over `churchNatArrow` /
`churchNatRest` / `churchNatCodomain`; SN via `closedStronglyNormalizing`.  No `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, or `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- The body context `[A:Type@0, f:A→A, x:A]` (scope 3) in which the Church numeral's iterate body is typed —
the context after the three `piIntro` binders of `churchNumeralLambda`. -/
def churchBodyContext {profile : PolyProfile} (flag : UniverseFlag) : TypingContext profile 3 :=
  ((TypingContext.empty.cons (universeCodeCell LevelExpr.lzero flag)).cons
    (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
      (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))).cons
    (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))

/-- The iterate body `iteratedApplication n f x` is typed at `A` (`var 2`) in the body context, uniformly in
`n`.  Base = the base `x` (`var 0`) by the `var` rule; step = `piElim` of the step `f` (`var 1`, at `A→A`)
against the IH, whose `subst0`-codomain is `A` argument-independently (the arrow codomain `A` is a free variable
not referencing the bound argument). -/
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

/-- ★ **Every Church numeral is typed at the Church Nat type.**  `churchNumeralLambda n = λA.λf.λx. f^n x` types
at `Π(A:Type@0). Π(f:A→A). Π(x:A). A` for ALL `n` — three nested `piIntro`s (universe binder `A`, arrow binder
`f:A→A` via `churchNatArrow`, base binder `x:A`) over the general iterate body.  The typing capstone of the
Church arc (complements `churchNumeralLambda_notConvertible_of_ne`). -/
theorem churchNumeralLambda_hasTypeDescPi {profile : PolyProfile} (n : Nat) :
    HasTypeDescPi profile TypingContext.empty
      (churchNumeralLambda n)
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
      · exact iteratedApplicationBody_hasTypeDescPi UniverseFlag.standard n

/-- Every Church numeral is strongly normalizing — SN-043 on the general typing.  The Π-fragment encodes the
naturals AND proves the whole family terminating. -/
theorem churchNumeralLambda_stronglyNormalizing {profile : PolyProfile} (_flag : UniverseFlag) (n : Nat) :
    IsStronglyNormalizing (churchNumeralLambda n) :=
  HasTypeDescPi.closedStronglyNormalizing (churchNumeralLambda_hasTypeDescPi (profile := profile) n)

/-- The concrete `churchOne` typing re-derived as the `n = 1` instance of the general typing
(`churchNumeralLambda 1 = churchOneLambda` definitionally) — the general theorem subsumes the concrete ones. -/
theorem churchOneLambda_hasTypeDescPi_viaGeneral {profile : PolyProfile} :
    HasTypeDescPi profile TypingContext.empty churchOneLambda
      (piTyCodeCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
        (piTyCodeCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
            (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
          (piTyCodeCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
            (variableCell (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 0))⟩ : Fin 3))))) :=
  churchNumeralLambda_hasTypeDescPi 1

end FX1Poly.Typed

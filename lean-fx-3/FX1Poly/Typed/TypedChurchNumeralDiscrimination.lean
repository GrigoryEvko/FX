import FX1Poly.Typed.TypedChurchNumeralIteration
import FX1Poly.Core.ConvCongruence

/-! # FX1Poly/Typed/TypedChurchNumeralDiscrimination — the Church numerals are faithfully distinct

`TypedChurchNumerals.lean` typed the Church numeral `one` and `TypedChurchNumeralIteration.lean` typed `two`
and showed each COMPUTES its iteration (`one A f x ↝* f x`, `two A f x ↝* f (f x)`).  This file closes the
numeral arc the way `TypedChurchBooleans.lean` closed the boolean arc: it proves the two numerals are
NON-CONVERTIBLE — `churchOne ≢ churchTwo` — so the Church encoding faithfully distinguishes the iteration count
`1` from `2`.  The numerals are not merely distinct syntax; they are distinct FUNCTIONS, distinguished through
their computation.

The proof mirrors `churchTrue_notConvertible_churchFalse` (the boolean discrimination) and routes through the
observable behaviour rather than the lambda bodies — whose only structural distinction sits one application deep
and whose shallower parts differ only in de Bruijn indices (a payload distinction that a direct `decide` would
expose only through a `propext`-risky variable-index inspection):

  * applied to identical inputs `Type@0 / Type@0 / Type@1` (the type, the step `f`, the base `x`), the two
    numerals reduce — three β-steps each (`churchOne_appliedReducesToIterate` / `churchTwo_appliedReducesToIterate`)
    — to the iterates `f x = app(Type@0, Type@1)` and `f (f x) = app(Type@0, app(Type@0, Type@1))`;
  * those two iterates are NON-CONVERTIBLE: both are no-step normal forms (applications headed by the universe
    code `Type@0`, never a β-redex), so `Conv` collapses to syntactic equality (`Conv.iff_eq_of_noStep`, the
    no-step hypotheses discharged by `RawTerm.isStepNormalForm_blocks_step` on a `decide`d structural-normality
    check), which the structural `DecidableEq` refutes — the iterates differ at their SECOND child (`Type@1`
    versus an application, distinct root generators), so `decide` separates them WITHOUT comparing de Bruijn
    indices, keeping it `propext`-free;
  * so a hypothetical `churchOne ≡ churchTwo` would — by three layers of application congruence (`Conv.app_cong`)
    plus the two iteration reductions — force the non-convertible iterates `f x ≡ f (f x)`, a contradiction.

So the kernel genuinely distinguishes the two Church numerals through the iteration COUNT they compute — the
numeral analogue of `churchTrue ≢ churchFalse`, and the faithfulness step toward "the Church encoding of ℕ
injects into the term model".

Zero-axiom: the only non-`rfl` ingredients are `Conv.iff_eq_of_noStep`, `RawTerm.isStepNormalForm_blocks_step`,
the conversion equivalence/congruence lemmas (`Conv.app_cong` / `Conv.trans` / `Conv.sym` / `Conv.fromStepStar`),
the two shipped iteration reductions, and two `decide`s over the structural normal-form / equality checks (no
`native_decide`).  No `propext`, `Quot.sound`, `Classical`, `sorry`, or `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

/-- The bare Church-`one` lambda term `λ(A:Type@0). λ(f:A→A). λ(x:A). f x` (body the single application `f x`).
Under T2 each binder carries its domain (universe code `Type@0`, arrow `A→A`, type variable `A`) — the domains
`churchNumeralLambda` uses, so `churchNumeralLambda 1 = churchOneLambda` holds by `rfl`. -/
abbrev churchOneLambda : RawTerm 0 :=
  lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
    (lamCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
      (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
        (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
          (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3)))))

/-- The bare Church-`two` lambda term `λ(A:Type@0). λ(f:A→A). λ(x:A). f (f x)` (body the nested `f (f x)`).
Under T2 each binder carries its domain, so `churchNumeralLambda 2 = churchTwoLambda` holds by `rfl`. -/
abbrev churchTwoLambda : RawTerm 0 :=
  lamCell (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
    (lamCell (piTyCodeCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
        (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2)))
      (lamCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩ : Fin 2))
        (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
          (appCell (variableCell (⟨1, Nat.succ_lt_succ (Nat.succ_pos 1)⟩ : Fin 3))
            (variableCell (⟨0, Nat.succ_pos 2⟩ : Fin 3))))))

/-- The universe code `Type@0` at the `standard` flag — the type argument and the step `f` of the iteration
fixtures. -/
abbrev numeralTypeZeroCode : RawTerm 0 := universeCodeCell LevelExpr.lzero UniverseFlag.standard

/-- The universe code `Type@1` at the `standard` flag — the base `x` of the iteration fixtures. -/
abbrev numeralTypeOneCode : RawTerm 0 := universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard

/-- The once-iterate `f x = app(Type@0, Type@1)` — what `churchOne` computes on the fixtures. -/
abbrev churchOneIterate : RawTerm 0 := appCell numeralTypeZeroCode numeralTypeOneCode

/-- The twice-iterate `f (f x) = app(Type@0, app(Type@0, Type@1))` — what `churchTwo` computes on the fixtures. -/
abbrev churchTwoIterate : RawTerm 0 :=
  appCell numeralTypeZeroCode (appCell numeralTypeZeroCode numeralTypeOneCode)

/-- The once-iterate is a no-step normal form: an application headed by the universe code `Type@0` (never a
β-redex) with normal children. -/
theorem churchOneIterate_isStepNormalForm : RawTerm.isStepNormalForm churchOneIterate := by decide

/-- The twice-iterate is a no-step normal form (both its applications are headed by universe codes). -/
theorem churchTwoIterate_isStepNormalForm : RawTerm.isStepNormalForm churchTwoIterate := by decide

/-- The two iterates `f x` and `f (f x)` are NOT convertible.  Both are no-step normal forms, so `Conv`
collapses to syntactic equality (`Conv.iff_eq_of_noStep`, the no-step hypotheses discharged by
`isStepNormalForm_blocks_step` on the `decide`d normality), which the structural `DecidableEq` refutes — the
two differ at their second child (`Type@1` versus an application — distinct root generators), so `decide`
separates them without ever comparing a de Bruijn index. -/
theorem churchOneIterate_notConvertible_churchTwoIterate : ¬ Conv churchOneIterate churchTwoIterate :=
  fun convertibility =>
    absurd
      ((Conv.iff_eq_of_noStep
          (fun reduct step =>
            RawTerm.isStepNormalForm_blocks_step churchOneIterate_isStepNormalForm reduct step)
          (fun reduct step =>
            RawTerm.isStepNormalForm_blocks_step churchTwoIterate_isStepNormalForm reduct step)).mp
        convertibility)
      (by decide)

/-- ★ `churchOne` and `churchTwo` are NOT convertible — the Church numeral encoding faithfully distinguishes
`1` from `2`.  Not through a de Bruijn payload inspection of the two lambda bodies, but through their
COMPUTATION: applied to `Type@0 / Type@0 / Type@1` they reduce to the distinct iterates `f x` vs `f (f x)`, so a
hypothetical `churchOne ≡ churchTwo` would — by three layers of application congruence plus the two iteration
reductions — force the non-convertible iterates `f x ≡ f (f x)`, contradicting
`churchOneIterate_notConvertible_churchTwoIterate`.  The iteration count the numerals exist to express is thus
also a definitional distinction — the numeral analogue of `churchTrue_notConvertible_churchFalse`. -/
theorem churchOne_notConvertible_churchTwo : ¬ Conv churchOneLambda churchTwoLambda := by
  intro convNumerals
  have convApplied :
      Conv (appCell (appCell (appCell churchOneLambda numeralTypeZeroCode) numeralTypeZeroCode) numeralTypeOneCode)
           (appCell (appCell (appCell churchTwoLambda numeralTypeZeroCode) numeralTypeZeroCode) numeralTypeOneCode) :=
    Conv.app_cong
      (Conv.app_cong (Conv.app_cong convNumerals (Conv.refl _)) (Conv.refl _))
      (Conv.refl _)
  have convIterates : Conv churchOneIterate churchTwoIterate :=
    Conv.trans
      (Conv.sym (Conv.fromStepStar (churchOne_appliedReducesToIterate UniverseFlag.standard)))
      (Conv.trans convApplied
        (Conv.fromStepStar (churchTwo_appliedReducesToIterate UniverseFlag.standard)))
  exact churchOneIterate_notConvertible_churchTwoIterate convIterates

end FX1Poly.Typed

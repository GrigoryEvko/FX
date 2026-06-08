import FX1Poly.Typed.TypedChurchBooleanOperations
import FX1Poly.Typed.TypedChurchNegation

/-! # FX1Poly/Typed/ChurchBooleanComplementLaws — the Boolean-algebra complement laws (excluded middle +
    non-contradiction), computed in the term model

The Church-boolean arc has shipped the operations (∧/∨ #1056, ¬ #1038), De Morgan (#1056) and the double-negation
involution `¬¬b = b` (#1038).  What completes the Church booleans into a recognizable BOOLEAN ALGEBRA is the pair
of COMPLEMENT (orthocomplementation) laws — the law of NON-CONTRADICTION and the law of EXCLUDED MIDDLE:

  `b ∧ ¬b ↝* false`   (non-contradiction)        `b ∨ ¬b ↝* true`   (excluded middle)

This file proves both at both Church booleans, by COMPUTATION, the Boolean-algebra analogue of #1031
(`CHURCH-SEMIRING-LAWS`, the +/× commutative-semiring axioms for Church numerals).  No new de Bruijn work — the
proofs chain the shipped negation reductions (`churchNot_negatesTrue` / `churchNot_negatesFalse`, #1038) with the
shipped AND/OR reductions (#1056) via `StepStar.appArgument` / `StepStar.trans_compose`.

The four proof SHAPES expose the dual short-circuit structure of AND / OR:

  * **`nonContradiction_true`** — `true ∧ ¬true ↝* false`: `and true _` is NOT strict, so `¬true` must reduce
    first (lifted through the AND's argument position) to `and true false`, then `churchAnd_trueFalse`.
  * **`nonContradiction_false`** — `false ∧ ¬false ↝* false`: `and false _` IS strict
    (`churchAnd_falseAnything`) — `¬false` is never reduced (short-circuit).
  * **`excludedMiddle_true`** — `true ∨ ¬true ↝* true`: `or true _` IS strict (`churchOr_trueAnything`) — `¬true`
    is never reduced (short-circuit).
  * **`excludedMiddle_false`** — `false ∨ ¬false ↝* true`: `or false _` is NOT strict, so it reduces to its
    second argument `¬false`, which then reduces to `true` (`churchNot_negatesFalse`).
  * **`churchBooleanComplementLaws`** — the bundle: both laws at both booleans.

Everything is the raw `Step` relation; no typing derivation is consulted.

## Zero-axiom verification

Each law is a `StepStar.trans_compose` of a shipped negation reduction (lifted through `StepStar.appArgument` when
the connective is non-strict) with a shipped AND/OR reduction — or a single shipped reduction when the connective
short-circuits.  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, or `omega`.  Gated per-decl in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

/-- **Law of NON-CONTRADICTION at `true`:** `true ∧ ¬true ↝* false`.  `and true _` is not strict, so the inner
`¬true` must reduce first (`churchNot_negatesTrue`, lifted through the AND's argument position) to `and true
false`, which `churchAnd_trueFalse` reduces to `false`. -/
theorem nonContradiction_true :
    StepStar (appCell (appCell churchAndLambda churchTrueLambda) (appCell churchNotLambda churchTrueLambda))
      churchFalseLambda :=
  StepStar.trans_compose
    (StepStar.appArgument (appCell churchAndLambda churchTrueLambda) churchNot_negatesTrue)
    churchAnd_trueFalse

/-- **Law of NON-CONTRADICTION at `false`:** `false ∧ ¬false ↝* false`.  `and false _` IS strict
(`churchAnd_falseAnything`), so the inner `¬false` is never reduced — short-circuit. -/
theorem nonContradiction_false :
    StepStar (appCell (appCell churchAndLambda churchFalseLambda) (appCell churchNotLambda churchFalseLambda))
      churchFalseLambda :=
  churchAnd_falseAnything (appCell churchNotLambda churchFalseLambda)

/-- **Law of EXCLUDED MIDDLE at `true`:** `true ∨ ¬true ↝* true`.  `or true _` IS strict
(`churchOr_trueAnything`), so the inner `¬true` is never reduced — short-circuit. -/
theorem excludedMiddle_true :
    StepStar (appCell (appCell churchOrLambda churchTrueLambda) (appCell churchNotLambda churchTrueLambda))
      churchTrueLambda :=
  churchOr_trueAnything (appCell churchNotLambda churchTrueLambda)

/-- **Law of EXCLUDED MIDDLE at `false`:** `false ∨ ¬false ↝* true`.  `or false _` is not strict
(`churchOr_falseAnything` reduces it to its second argument), so the result is `¬false`, which then reduces to
`true` (`churchNot_negatesFalse`). -/
theorem excludedMiddle_false :
    StepStar (appCell (appCell churchOrLambda churchFalseLambda) (appCell churchNotLambda churchFalseLambda))
      churchTrueLambda :=
  StepStar.trans_compose
    (churchOr_falseAnything (appCell churchNotLambda churchFalseLambda))
    churchNot_negatesFalse

/-- **★ The complement laws hold at BOTH booleans:** `b ∧ ¬b ↝* false` and `b ∨ ¬b ↝* true` for
`b ∈ {true, false}`.  With ∧/∨/¬ (#1056/#1038), De Morgan (#1056) and the double-negation involution (#1038), the
Church-encoded booleans satisfy the orthocomplementation laws of a BOOLEAN ALGEBRA — computed in the pure
Π-fragment, the analogue of the Church-numeral commutative-semiring laws (#1031). -/
theorem churchBooleanComplementLaws :
    (StepStar (appCell (appCell churchAndLambda churchTrueLambda) (appCell churchNotLambda churchTrueLambda))
      churchFalseLambda
    ∧ StepStar (appCell (appCell churchAndLambda churchFalseLambda) (appCell churchNotLambda churchFalseLambda))
      churchFalseLambda)
    ∧ (StepStar (appCell (appCell churchOrLambda churchTrueLambda) (appCell churchNotLambda churchTrueLambda))
      churchTrueLambda
    ∧ StepStar (appCell (appCell churchOrLambda churchFalseLambda) (appCell churchNotLambda churchFalseLambda))
      churchTrueLambda) :=
  ⟨⟨nonContradiction_true, nonContradiction_false⟩, ⟨excludedMiddle_true, excludedMiddle_false⟩⟩

end FX1Poly.Typed

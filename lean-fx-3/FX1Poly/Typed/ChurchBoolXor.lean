import FX1Poly.Typed.TypedChurchBooleanOperations
import FX1Poly.Typed.TypedChurchNegation
import FX1Poly.Core.ConvCongruence

/-! # FX1Poly/Typed/ChurchBoolXor — exclusive-or, completing the binary Boolean connectives + the GF(2) ring

The Church-boolean arc has shipped AND/OR (#1056), NOT (#1038), De Morgan (#1056), the double-negation involution
(#1038) and the orthocomplement laws (#1086).  The one binary connective still missing is EXCLUSIVE-OR — the
operation that turns the Boolean ALGEBRA into the Boolean RING `GF(2)` (`⊕` = addition, `∧` = multiplication).
This file ships it, defined from the shipped connectives with NO new de Bruijn work:

  `xor a b = (a ∨ b) ∧ ¬(a ∧ b)`

and proves its full 4-row truth table by COMPUTATION, plus the two ring-structure laws that make `⊕` the additive
group of `GF(2)`, plus the faithfulness capstone that `⊕` is a genuinely NEW connective (not `∧`/`∨` in disguise):

  * **`xorTrueTrue` / `xorTrueFalse` / `xorFalseTrue` / `xorFalseFalse`** — the truth table: `false / true / true /
    false`.  Each chains the shipped OR reduction (lifted into the AND's function position via `appFunction`), the
    shipped AND reduction inside `¬(a∧b)` (lifted into the NOT, then `churchNot_negates…`, lifted into the outer
    AND's argument position via `appArgument`), and the final shipped AND reduction.
  * **`xorSelfInverse` (★)** — `b ⊕ b ↝* false` for both booleans: the `GF(2)` additive SELF-INVERSE
    (`x + x = 0`).  Every element is its own inverse — XOR's signature property.
  * **`xorFalseIdentity`** — `b ⊕ false ↝* b` for both booleans: `false` is the `GF(2)` additive UNIT (`x + 0 = x`).
  * **`xorDiffersFromAnd` / `xorDiffersFromOr` (★)** — `⊕` is a genuinely NEW connective: `true ⊕ true ↝* false`
    while `true ∧ true ↝* true` and `true ∨ true ↝* true`, so `xor (true,true)` is convertible to NEITHER `and`
    nor `or` at `(true,true)` — else `false ≡ true` (refuted by #983).  XOR is not `∧`/`∨` renamed; the connective
    set `{∧, ∨, ⊕}` has three distinct members.

Everything is the raw `Step` / `Conv` relations; no typing derivation is consulted.

## Zero-axiom verification

`xor` is a META-level combination of the shipped `churchAndLambda` / `churchOrLambda` / `churchNotLambda` (like
`churchListAny` = `fold or`, #1084) — NO new λ, NO de Bruijn reshape.  Each truth-table row is a
`StepStar.trans_compose` chain of shipped reductions lifted through `StepStar.appFunction` / `StepStar.appArgument`;
the discrimination capstones are `Conv.fromStepStar` / `.trans` / `.sym` to the computed values +
`churchTrue_notConvertible_churchFalse` (#983).  No `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
or `omega`.  Gated per-decl in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core StepStar

/-- `xor a b = (a ∨ b) ∧ ¬(a ∧ b)` — exclusive-or, defined from the shipped ∧/∨/¬ (#1056/#1038), no new λ. -/
def churchBoolXor (a b : RawTerm 0) : RawTerm 0 :=
  appCell (appCell churchAndLambda (appCell (appCell churchOrLambda a) b))
    (appCell churchNotLambda (appCell (appCell churchAndLambda a) b))

/-- `true ⊕ true ↝* false`: `or true true ↝* true`, `¬(and true true) ↝* ¬true ↝* false`, `and true false ↝*
false`. -/
theorem xorTrueTrue :
    StepStar (churchBoolXor churchTrueLambda churchTrueLambda) churchFalseLambda := by
  have orStep : StepStar (appCell (appCell churchOrLambda churchTrueLambda) churchTrueLambda)
      churchTrueLambda := churchOr_trueAnything churchTrueLambda
  have notStep : StepStar (appCell churchNotLambda (appCell (appCell churchAndLambda churchTrueLambda)
      churchTrueLambda)) churchFalseLambda :=
    StepStar.trans_compose (StepStar.appArgument churchNotLambda churchAnd_trueTrue) churchNot_negatesTrue
  exact StepStar.trans_compose
    (StepStar.appFunction (StepStar.appArgument churchAndLambda orStep))
    (StepStar.trans_compose
      (StepStar.appArgument (appCell churchAndLambda churchTrueLambda) notStep)
      churchAnd_trueFalse)

/-- `true ⊕ false ↝* true`: `or true false ↝* true`, `¬(and true false) ↝* ¬false ↝* true`, `and true true ↝*
true`. -/
theorem xorTrueFalse :
    StepStar (churchBoolXor churchTrueLambda churchFalseLambda) churchTrueLambda := by
  have orStep : StepStar (appCell (appCell churchOrLambda churchTrueLambda) churchFalseLambda)
      churchTrueLambda := churchOr_trueAnything churchFalseLambda
  have notStep : StepStar (appCell churchNotLambda (appCell (appCell churchAndLambda churchTrueLambda)
      churchFalseLambda)) churchTrueLambda :=
    StepStar.trans_compose (StepStar.appArgument churchNotLambda churchAnd_trueFalse) churchNot_negatesFalse
  exact StepStar.trans_compose
    (StepStar.appFunction (StepStar.appArgument churchAndLambda orStep))
    (StepStar.trans_compose
      (StepStar.appArgument (appCell churchAndLambda churchTrueLambda) notStep)
      churchAnd_trueTrue)

/-- `false ⊕ true ↝* true`: `or false true ↝* true`, `¬(and false true) ↝* ¬false ↝* true`, `and true true ↝*
true`. -/
theorem xorFalseTrue :
    StepStar (churchBoolXor churchFalseLambda churchTrueLambda) churchTrueLambda := by
  have orStep : StepStar (appCell (appCell churchOrLambda churchFalseLambda) churchTrueLambda)
      churchTrueLambda := churchOr_falseAnything churchTrueLambda
  have notStep : StepStar (appCell churchNotLambda (appCell (appCell churchAndLambda churchFalseLambda)
      churchTrueLambda)) churchTrueLambda :=
    StepStar.trans_compose (StepStar.appArgument churchNotLambda (churchAnd_falseAnything churchTrueLambda))
      churchNot_negatesFalse
  exact StepStar.trans_compose
    (StepStar.appFunction (StepStar.appArgument churchAndLambda orStep))
    (StepStar.trans_compose
      (StepStar.appArgument (appCell churchAndLambda churchTrueLambda) notStep)
      churchAnd_trueTrue)

/-- `false ⊕ false ↝* false`: `or false false ↝* false`, `¬(and false false) ↝* ¬false ↝* true`, `and false true
↝* false`. -/
theorem xorFalseFalse :
    StepStar (churchBoolXor churchFalseLambda churchFalseLambda) churchFalseLambda := by
  have orStep : StepStar (appCell (appCell churchOrLambda churchFalseLambda) churchFalseLambda)
      churchFalseLambda := churchOr_falseAnything churchFalseLambda
  have notStep : StepStar (appCell churchNotLambda (appCell (appCell churchAndLambda churchFalseLambda)
      churchFalseLambda)) churchTrueLambda :=
    StepStar.trans_compose (StepStar.appArgument churchNotLambda (churchAnd_falseAnything churchFalseLambda))
      churchNot_negatesFalse
  exact StepStar.trans_compose
    (StepStar.appFunction (StepStar.appArgument churchAndLambda orStep))
    (StepStar.trans_compose
      (StepStar.appArgument (appCell churchAndLambda churchFalseLambda) notStep)
      (churchAnd_falseAnything churchTrueLambda))

/-- **★ XOR is SELF-INVERSE:** `b ⊕ b ↝* false` for both booleans — the `GF(2)` additive self-inverse `x + x = 0`,
XOR's signature property (every element is its own additive inverse). -/
theorem xorSelfInverse :
    StepStar (churchBoolXor churchTrueLambda churchTrueLambda) churchFalseLambda
    ∧ StepStar (churchBoolXor churchFalseLambda churchFalseLambda) churchFalseLambda :=
  ⟨xorTrueTrue, xorFalseFalse⟩

/-- `false` is the XOR IDENTITY: `b ⊕ false ↝* b` for both booleans — the `GF(2)` additive unit `x + 0 = x`. -/
theorem xorFalseIdentity :
    StepStar (churchBoolXor churchTrueLambda churchFalseLambda) churchTrueLambda
    ∧ StepStar (churchBoolXor churchFalseLambda churchFalseLambda) churchFalseLambda :=
  ⟨xorTrueFalse, xorFalseFalse⟩

/-- **★ XOR is a genuinely NEW connective, distinct from AND:** `true ⊕ true ↝* false` while `true ∧ true ↝* true`,
so the two are NOT convertible at `(true, true)` — else `false ≡ true` (refuted by #983). -/
theorem xorDiffersFromAnd :
    ¬ Conv (churchBoolXor churchTrueLambda churchTrueLambda)
        (appCell (appCell churchAndLambda churchTrueLambda) churchTrueLambda) := by
  intro hConv
  have convResults : Conv churchFalseLambda churchTrueLambda :=
    Conv.trans (Conv.sym (Conv.fromStepStar xorTrueTrue))
      (Conv.trans hConv (Conv.fromStepStar churchAnd_trueTrue))
  exact churchTrue_notConvertible_churchFalse (Conv.sym convResults)

/-- **★ XOR is distinct from OR** too: `true ⊕ true ↝* false` while `true ∨ true ↝* true`, so `xor (true,true)` is
convertible to NEITHER `and` nor `or` at `(true,true)` — the connective set `{∧, ∨, ⊕}` has three distinct
members. -/
theorem xorDiffersFromOr :
    ¬ Conv (churchBoolXor churchTrueLambda churchTrueLambda)
        (appCell (appCell churchOrLambda churchTrueLambda) churchTrueLambda) := by
  intro hConv
  have convResults : Conv churchFalseLambda churchTrueLambda :=
    Conv.trans (Conv.sym (Conv.fromStepStar xorTrueTrue))
      (Conv.trans hConv (Conv.fromStepStar (churchOr_trueAnything churchTrueLambda)))
  exact churchTrue_notConvertible_churchFalse (Conv.sym convResults)

end FX1Poly.Typed

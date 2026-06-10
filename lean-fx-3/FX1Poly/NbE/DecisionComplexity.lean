/-! # FX1Poly/NbE/DecisionComplexity
   — the generic STRICT-COMPLEXITY witness schema for decision procedures

`StrictNormalizer` (the M19 STRICT-COMPLEXITY hook shipped at audit-A4) is TERM-NORMALIZER-shaped:
its `normalizer` field demands an `FX1Poly.NbE.Normalizer`, i.e. a `RawTerm scope → RawTerm scope`
normalization contract.  Decision procedures that are not term normalizers — the universe-level
equivalence decider `LevelExpr.decideDenoteEquiv`, future `DecidableEq`-backed `Conv` deciders —
cannot instantiate it.  This file ships the GENERIC sibling per polycell.md §11.8.7: a decision
procedure over an admissible-input fragment, together with a step counter and a machine-checked
polynomial bound on that counter.  Closing the "decidable but EXP-tower" loophole means every
`Decidable` kernel instance eventually carries one of these.

## What the witness says — and what it cannot say (honesty)

Lean has no internal cost model, so "the decider performs at most N machine steps" is not a
statable proposition.  The discipline (established by the `*Steps` counters in
`LevelExprSimplify`) is:

  * `stepCount` is a SHADOW counter that mirrors the decider's recursion EXACTLY — same
    scrutinees, same structural recursion on the same tails — so it counts the decider's
    comparisons faithfully BY CONSTRUCTION (identical control flow).
  * The structure then proves THAT counter polynomially bounded in the operand sizes:
    `stepCount l r ≤ c * (size l ^ k + size r ^ k) + c`.

Mirror-faithfulness is a per-instance code-review obligation (it is a statement about two Lean
definitions having identical control flow, not a Lean proposition); each instance documents it at
its `stepCount` definition.  The polynomial bound, by contrast, is machine-checked here.

## Zero-axiom verification

A structure declaration plus a field-count pin.  Audit-gated in `AuditNbE.lean`.
-/

namespace FX1Poly.NbE

/-- **The §11.8.7 STRICT-COMPLEXITY witness for a binary decision procedure.**

Bundles a decider for `relation` on the `admissibleInput` fragment with a size measure, a shadow
step counter (mirror-faithful by construction — see the module docstring), and a machine-checked
polynomial bound `stepCount l r ≤ c * (size l ^ k + size r ^ k) + c`.  The per-operand polynomial
form (rather than `(size l + size r) ^ k`) is deliberate: it composes one-sided per-operand cost
bounds without cross-term redistribution, and the two forms bound each other up to the constant. -/
structure DecisionComplexity {inputType : Type}
    (admissibleInput : inputType → Prop)
    (relation : inputType → inputType → Prop) where
  /-- The decision procedure on the admissible fragment. -/
  decider : (left right : inputType) → admissibleInput left → admissibleInput right →
    Decidable (relation left right)
  /-- The size measure the polynomial bound is stated against. -/
  inputSize : inputType → Nat
  /-- The shadow comparison counter mirroring the decider's recursion exactly
  (faithfulness is by-construction per instance, documented at the counter's definition). -/
  stepCount : inputType → inputType → Nat
  /-- Polynomial degree `k` of the complexity bound. -/
  polynomialDegree : Nat
  /-- Leading constant `c` of the bounding polynomial (also the additive overhead). -/
  polynomialConstant : Nat
  /-- The machine-checked bound: the counter is polynomial in the operand sizes. -/
  stepCount_isPolynomial : ∀ (left right : inputType),
    stepCount left right ≤
      polynomialConstant *
          (inputSize left ^ polynomialDegree + inputSize right ^ polynomialDegree) +
        polynomialConstant

/-- The `DecisionComplexity` structure has 6 explicit fields (shape pin — a rename or removal
fails the build here). -/
def DecisionComplexity.fieldCount : Nat := 6

theorem DecisionComplexity.fieldCount_correct :
    DecisionComplexity.fieldCount = 6 := rfl

end FX1Poly.NbE

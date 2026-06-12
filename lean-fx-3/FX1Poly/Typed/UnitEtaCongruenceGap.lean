import FX1Poly.Typed.UnitEtaJudgmentalEquality
import FX1Poly.Typed.HasTypeDescPiDataHeadUntyped

/-! # FX1Poly/Typed/UnitEtaCongruenceGap
   — the machine-checked NON-CONGRUENCE of `DefEqUnitEta` + the #481/#364-remainder route record

`UnitEtaJudgmentalEquality` claims (honest boundary (1), docstring only until now) that
`DefEqUnitEta` is NOT congruent: it does not collapse unit-typed SUBTERMS.  This module turns that
claim into a theorem — the canonical congruence-gap pair:

  * COMPONENTS: the unit-typed variable and the unit value `unitCell` ARE `DefEqUnitEta` at
    `unitTypeCell` (the shipped strictness pair).
  * PAIRS: `pair(x, x)` and `pair(unit, unit)` — built from those very components — are
    `DefEqUnitEta` at NO classifier whatsoever:
      - the `unitEta` arm needs the pair typed at `unitTypeCell`: the nullary value layer forces a
        unit-classified subject to BE `unitCell` (`subjectIsUnitOfUnitClassifier` — head clash),
        and the grown engine types no `gen_pair` cell at all (`pairCellHasNoTyping`);
      - the `ofBetaEtaConv` arm needs `BetaEtaConv`: both pairs are βη-NORMAL (`gen_pair` η fires
        only on `pair(fst p, snd p)` shapes, and there is no β/ι redex), so a join forces them
        syntactically equal — refuted by `decide` on the structural `DecidableEq`.

Any CONGRUENT extension of unit-η must equate the pairs (componentwise-equal under a constructor),
so the gap is exactly what the η-long type-directed readback (#481) exists to close — no
rewriting-relation extension can reach it (the pairs are joint normal forms of the βη system).

## The #481 / #364-remainder route record (decision committed here)

The η-long readback is type-INDEXED by construction (the ETA-1 census, `BetaEtaConvGapStatement`):
the raw NbE quote cannot carry it.  Two routes, ordered:

  * **R1 (first): unit-only congruent collapse.**  A type-directed traversal replacing unit-TYPED
    subterms by `unitCell`.  Structural recursion on the TERM (no type-structure measure needed) —
    the hard part is supplying each subterm's classifier, which is exactly what the rule tables
    (`typingRuleDescOf` / `introRuleDescOf` / `elimRuleDescOf`) describe premise-wise; the
    whnf-directed checker substrate (STR-3/4 + route-H soundness) is the candidate driver.
    Deciding the CONGRUENT unit-η equality then = collapse-then-βη-compare.
  * **R2 (the campaign): full η-long quote at Π/Σ/Unit** (η-M15a/b/c → #481 → #364).  Needs
    recursion on classifier STRUCTURE (whnf the classifier, recurse into Π domain/codomain), hence
    a termination measure on `RawTerm` classifiers — the universe LEVEL is the predicative
    candidate, via the leveled validity substrate (`ValidTyping` / the leveled LR).

## Zero-axiom verification

The βη refutation is the shipped leaf pattern (`reduceOnceBetaEta_complete` at `rfl` + βη
star-rigidity + `decide` on closed structural inequality); the typing refutations are the shipped
`subjectIsUnitOfUnitClassifier` head clash and `pairCellHasNoTyping`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- The pair of unit-typed VARIABLES — both components are the variable bound at `unitTypeCell`
in `unitVariableContext`.  Componentwise unit-η-equal to `pairOfUnitValues`, yet (the theorems
below) related to it by NO `DefEqUnitEta` instance. -/
def pairOfUnitVariables : RawTerm 1 :=
  pairCell (variableCell ⟨0, Nat.zero_lt_one⟩) (variableCell ⟨0, Nat.zero_lt_one⟩)

/-- The pair of unit VALUES — the term any congruent unit-η must equate `pairOfUnitVariables`
with. -/
def pairOfUnitValues : RawTerm 1 :=
  pairCell unitCell unitCell

/-- **The pairs are not βη-convertible**: both are βη-normal (`gen_pair` η fires only on
`pair(fst p, snd p)` shapes; no β/ι redex anywhere), so a βη-join forces them syntactically
equal — refuted structurally. -/
theorem pairOfUnitVariables_notBetaEtaConv_pairOfUnitValues :
    ¬ BetaEtaConv pairOfUnitVariables pairOfUnitValues := by
  intro convertible
  obtain ⟨commonTerm, variablePairChain, valuePairChain⟩ := convertible
  have variablePairIsCommon :=
    Step.betaEtaStar.eq_of_noBetaEtaStep
      (RawTerm.reduceOnceBetaEta_complete (rfl :
        pairOfUnitVariables.reduceOnceBetaEta = none))
      variablePairChain
  have valuePairIsCommon :=
    Step.betaEtaStar.eq_of_noBetaEtaStep
      (RawTerm.reduceOnceBetaEta_complete (rfl :
        pairOfUnitValues.reduceOnceBetaEta = none))
      valuePairChain
  exact absurd (variablePairIsCommon.trans valuePairIsCommon.symm) (by decide)

/-- **★ `DefEqUnitEta` is NOT congruent — machine-checked** (discharges the docstring-only
boundary (1) of `UnitEtaJudgmentalEquality`).  The COMPONENTS are judgmentally equal at
`unitTypeCell` (the shipped strictness pair), yet the PAIRS built from them are `DefEqUnitEta` at
NO classifier: the `unitEta` arm is refuted on both disjuncts (the nullary value layer forces the
subject to be `unitCell`; the grown engine types no `gen_pair` cell), and the `ofBetaEtaConv` arm
is refuted by βη-normality.  Closing this gap is exactly the η-long type-directed readback
(#481), the named follow-on — no rewriting extension can reach it. -/
theorem DefEqUnitEta.isNotCongruent (profile : PolyProfile) :
    DefEqUnitEta profile (unitVariableContext profile)
      (variableCell ⟨0, Nat.zero_lt_one⟩) unitCell unitTypeCell ∧
    ∀ classifier : RawTerm 1,
      ¬ DefEqUnitEta profile (unitVariableContext profile)
          pairOfUnitVariables pairOfUnitValues classifier := by
  refine ⟨.unitEta (Or.inr (unitVariableTyped profile))
      (Or.inl (NullaryDataValueTyped.unitValueTyped (unitVariableContext profile))),
    fun classifier defEq => ?_⟩
  cases defEq with
  | ofBetaEtaConv _ _ _ convertible =>
      exact pairOfUnitVariables_notBetaEtaConv_pairOfUnitValues convertible
  | unitEta leftTypedAtUnit _ =>
      cases leftTypedAtUnit with
      | inl dataIntroTyped =>
          exact Generator.noConfusion (congrArg RawTerm.headGenerator
            (NullaryDataValueTyped.subjectIsUnitOfUnitClassifier dataIntroTyped))
      | inr grownTyped =>
          exact HasTypeDescPi.pairCellHasNoTyping grownTyped

end FX1Poly.Typed

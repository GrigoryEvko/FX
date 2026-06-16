import FX1Poly.Tier0.Context.RepresentableMapCategory
import FX1Poly.Tier0.Context.PresheafModel

/-! # context-26 — forcing as a CwF (the type-theoretic Cohen forcing), context-side residue

`context-26` is the FORCING MODEL rung (Jaber–Lewertowski–Pédrot–Tabareau–Sozeau): forcing presents a model /
syntactic translation over a POSET OF CONDITIONS, the type-theoretic analogue of Cohen forcing, and yields
INDEPENDENCE results — a generic element added by the poset makes a principle consistent (or refutes it).

## What is context-side here, and what is deferred

The category of CONTEXTS of a forcing model over a poset of conditions `P` is the presheaf category
`[Pᵒᵖ, Set]` — i.e. forcing IS the presheaf model (`context-25`) specialised to `P` a POSET (a thin site).
That base, the conditions preorder, the Kripke forcing relation, and a concrete independence are pure
context-side data; that is the residue shipped here, in full and zero-axiom:

  * **`ForcingPoset`** — the conditions: a preorder `(Condition, precedes)` (reflexive + transitive); a
    condition is a partial state of knowledge, `precedes p q` reads "`q` extends/refines `p`".
  * **`conditionCategory`** — `P` as a THIN `RawCategory` (`Hom p q = PLift (precedes p q)`, a `Prop`); the
    three laws hold by proof irrelevance, so each is `rfl`, no `funext`.
  * ★ **`forcingContextCategory := presheafCategory (conditionCategory P)`** — the forcing model's contexts
    are presheaves over the conditions: forcing is the `context-25` presheaf model at a poset site (the
    `fxForcing_subsumes_presheaf_smoke` pins this definitionally).
  * **`ForcingPredicate`** — the Kripke forcing relation `p ⊩ φ`: a MONOTONE `Prop` over conditions (forced
    stays forced under refinement).
  * ★ the CONCRETE INDEPENDENCE: `cohenBitPoset` (the conditions `none`/`some b` of a single generic bit) with
    `forcesTrue`/`forcesFalse`, `cohenBit_independence` (the bit is forced `true` by `some true`, `false` by
    `some false`, and UNDECIDED by the empty condition `none`) and
    `cohenBit_someTrue_someFalse_incompatible` (those two deciding conditions have NO common refinement) —
    genuine Cohen forcing of a generic bit: from `none` one may extend either way to incompatible
    fully-deciding conditions, so the bit is INDEPENDENT.

DEFERRED (the `×type` / full-model core, recorded by `= false` markers):
  * the FORCING TRANSLATION — the syntactic model interpreting the type theory's `Id`/`Π`/`Σ` + the generic
    element + translation soundness (well-typed ⟹ forced) — `hasForcingTranslation = false`;
  * the SYNTACTIC INDEPENDENCE THEOREM — that a principle is UNDERIVABLE because the generic forces its
    negation (needs the translation + soundness) — `hasIndependenceTheorem = false`.  What ships is the
    SEMANTIC witness (a proposition decided incompatibly by the conditions).
  * the FORCING UNIVERSE / generic filter — `hasForcingUniverse = false`.

Reference: Jaber, Lewertowski, Pédrot, Tabareau & Sozeau, "The Definitional Side of the Forcing" (LICS 2016).

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

/-! ## The conditions preorder + its thin category -/

/-- A **forcing poset** — the conditions as a PREORDER `(Condition, precedes)` (reflexive + transitive;
`precedes p q` = "`q` extends/refines `p`", `p ≤ q`).  Forcing requires only a PREORDER — antisymmetry is
inessential (one may always quotient to a partial order), so "forcing poset"/"notion of forcing" is the
conventional name for what is, in general, a preorder.  The `cohenBitPoset` instance below happens to be
antisymmetric, but the structure does not demand it. -/
structure ForcingPoset where
  /-- The conditions (partial states of knowledge). -/
  Condition : Type
  /-- The refinement preorder: `precedes p q` means `q` extends `p`. -/
  precedes : Condition → Condition → Prop
  /-- Refinement is reflexive. -/
  precedesRefl : ∀ (condition : Condition), precedes condition condition
  /-- Refinement is transitive. -/
  precedesTrans : ∀ {conditionA conditionB conditionC : Condition},
    precedes conditionA conditionB → precedes conditionB conditionC → precedes conditionA conditionC

/-- The **category of conditions** — `P` as a THIN `RawCategory` (`Hom p q = PLift (precedes p q)`, a `Prop`).
All three laws hold by definitional proof irrelevance of the `Prop` hom, so each is `rfl`, no `funext`. -/
def conditionCategory (poset : ForcingPoset) : RawCategory where
  Object := poset.Condition
  Morphism := fun conditionP conditionQ => PLift (poset.precedes conditionP conditionQ)
  identity := fun condition => PLift.up (poset.precedesRefl condition)
  compose := fun refinementOne refinementTwo => PLift.up (poset.precedesTrans refinementOne.down refinementTwo.down)
  composeAssoc := fun _ _ _ => rfl
  identityLeft := fun _ => rfl
  identityRight := fun _ => rfl

/-- ★ The forcing model's category of CONTEXTS — presheaves over the conditions.  Forcing is the
`context-25` presheaf model at the poset site `conditionCategory P`. -/
def forcingContextCategory (poset : ForcingPoset) : RawCategory.{1, 0} :=
  presheafCategory (conditionCategory poset)

/-! ## The Kripke forcing relation -/

/-- A **forcing predicate** `p ⊩ φ` — a MONOTONE `Prop` over conditions: if `p` forces `φ` and `q` extends
`p`, then `q` forces `φ` (forced stays forced under refinement).  This is a `Prop`-valued presheaf on the
conditions (the Kripke semantics of a proposition). -/
structure ForcingPredicate (poset : ForcingPoset) where
  /-- `force p` = "`p` forces the proposition". -/
  force : poset.Condition → Prop
  /-- Forcing is monotone under refinement. -/
  forceMonotone : ∀ {conditionP conditionQ : poset.Condition},
    poset.precedes conditionP conditionQ → force conditionP → force conditionQ

/-! ## Concrete Cohen forcing of a single generic bit -/

/-- The **Cohen single-bit poset**: a condition is `none` (the bit is undecided) or `some b` (decided to `b`).
`precedes p q` (`q` extends `p`) holds when `p = none` (extend the empty condition to anything) or `p = q`
(only `none` is strictly extended; the deciding conditions are maximal and incomparable). -/
def cohenBitPoset : ForcingPoset where
  Condition := Option Bool
  precedes := fun conditionP conditionQ => conditionP = none ∨ conditionP = conditionQ
  precedesRefl := fun _ => Or.inr rfl
  precedesTrans := fun hAB hBC =>
    hAB.elim
      (fun hAnone => Or.inl hAnone)
      (fun hABeq => hBC.elim
        (fun hBnone => Or.inl (hABeq.trans hBnone))
        (fun hBCeq => Or.inr (hABeq.trans hBCeq)))

/-- The forcing predicate "the generic bit is `true`" — forced exactly at the condition `some true`. -/
def forcesTrue : ForcingPredicate cohenBitPoset where
  force := fun condition => condition = some true
  forceMonotone := fun {_ _} hpq hp =>
    hpq.elim
      (fun hpnone => absurd (hpnone.symm.trans hp) (by decide))
      (fun hpqeq => hpqeq.symm.trans hp)

/-- The forcing predicate "the generic bit is `false`" — forced exactly at the condition `some false`. -/
def forcesFalse : ForcingPredicate cohenBitPoset where
  force := fun condition => condition = some false
  forceMonotone := fun {_ _} hpq hp =>
    hpq.elim
      (fun hpnone => absurd (hpnone.symm.trans hp) (by decide))
      (fun hpqeq => hpqeq.symm.trans hp)

/-- ★ **The Cohen-bit independence (semantic core).**  The bit is forced `true` by `some true` and `false` by
`some false`, but UNDECIDED by the empty condition `none` — neither `φ` nor `¬φ` is forced at `none`. -/
theorem cohenBit_independence :
    forcesTrue.force (some true) ∧ ¬ forcesTrue.force none
      ∧ forcesFalse.force (some false) ∧ ¬ forcesFalse.force none := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · show ¬ ((none : Option Bool) = some true); decide
  · show ¬ ((none : Option Bool) = some false); decide

/-- ★ The two deciding conditions are INCOMPATIBLE — `some true` and `some false` have NO common refinement.
So from `none` one may extend EITHER way to a fully-deciding condition, but not reconcile them: the generic
bit is genuinely independent (the type-theoretic Cohen forcing). -/
theorem cohenBit_someTrue_someFalse_incompatible :
    ¬ ∃ (condition : cohenBitPoset.Condition),
        cohenBitPoset.precedes (some true) condition ∧ cohenBitPoset.precedes (some false) condition := by
  intro hexists
  obtain ⟨condition, hTrue, hFalse⟩ := hexists
  have hcTrue : condition = some true := hTrue.elim (fun h => absurd h (by decide)) (fun h => h.symm)
  have hcFalse : condition = some false := hFalse.elim (fun h => absurd h (by decide)) (fun h => h.symm)
  have hcontra : (some true : Option Bool) = some false := hcTrue.symm.trans hcFalse
  exact absurd hcontra (by decide)

/-! ## The model datum + honesty markers -/

/-- The context-side datum of a forcing model: the conditions poset and its category of contexts (presheaves
over the conditions).  Forcing is CONDITIONS-INDEXED — one model per poset. -/
structure ForcingModelData where
  /-- The poset of conditions. -/
  conditions : ForcingPoset
  /-- The base of contexts — presheaves over the conditions. -/
  base : RawCategory.{1, 0}

/-- ★ The FX forcing-model datum over a poset of conditions: presheaves over the conditions as the base.
Parameterized by the poset; the faithful, non-degenerate deliverable. -/
def fxForcingModel (poset : ForcingPoset) : ForcingModelData where
  conditions := poset
  base := forcingContextCategory poset

/-- **Honesty marker.**  The FORCING TRANSLATION — the syntactic model interpreting `Id`/`Π`/`Σ` + the
generic element + translation soundness (well-typed ⟹ forced) — is `×type`, deferred.  `= false`. -/
def fxForcingModel_hasForcingTranslation : Bool := false

/-- **Honesty marker.**  The SYNTACTIC INDEPENDENCE THEOREM — a principle is UNDERIVABLE because the generic
forces its negation (needs the translation + soundness) — is `×type`.  What ships is the semantic witness
(`cohenBit_independence`).  `= false`. -/
def fxForcingModel_hasIndependenceTheorem : Bool := false

/-- **Honesty marker.**  The FORCING UNIVERSE / generic filter is `×type`, deferred.  `= false`. -/
def fxForcingModel_hasForcingUniverse : Bool := false

/-! ## Smoke -/

/-- Smoke: the forcing context category IS the `context-25` presheaf category over the conditions (the
subsumption, definitionally). -/
theorem fxForcing_subsumes_presheaf_smoke (poset : ForcingPoset) :
    forcingContextCategory poset = presheafCategory (conditionCategory poset) :=
  rfl

end FX1Poly.Tier0

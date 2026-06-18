/-! # Tier0/Term — the Fiore-Plotkin-Turi substitution monoid (term-10)

Fiore-Plotkin-Turi (1999) model abstract syntax with binding in the presheaf category `[𝔽, Set]` (`𝔽` =
contexts): an object `T : Nat → Type` (`T n` = terms in `n` variables) is a **substitution monoid** when it
carries a unit `η : V → T` (the variables) and a multiplication `μ : T ⊗ T → T` (capture-avoiding
substitution, where `⊗` is the substitution tensor — a coend over contexts) satisfying the monoid laws.  A
**Σ-monoid** additionally carries a signature-algebra structure compatible with `μ` (the substitution
lemma); the INITIAL Σ-monoid is the abstract syntax with its substitution, and SOAS completeness
(Fiore-Hur) says second-order equational logic is complete w.r.t. Σ-monoid models.

This file ships the genuine, abstract CORE in de Bruijn / `[𝔽, Set]` form: the substitution monoid with its
three laws, and the genuine FPT consequence — **the monoid laws present the substitution (Kleisli) CATEGORY**
(the base category of the model / the Lawvere theory of the syntax), pointwise (funext-free).

## What this file ships (each zero-axiom)

  * **`SubstitutionMonoid`** — a model of substitution: `carrier` (a context-indexed family), `var` (the
    unit), `subst` (the multiplication = parallel substitution), and the three monoid laws — `substVar`
    (`(var i)[σ] = σ i`, right unit), `substId` (`t[var] = t`, left unit), `substAssoc`
    (`t[σ][τ] = t[σ ; τ]`, associativity).
  * **`kleisliComp`** + **`kleisli_leftId` / `kleisli_rightId` / `kleisli_assoc`** — ★ the substitution
    CATEGORY: assignments `Fin m → carrier n` are the morphisms, `var` the identity, `kleisliComp` the
    composition; the category laws (pointwise) follow from the monoid laws.  This is the FPT point —
    substitution-as-monoid-multiplication yields the substitution category.
  * **`variableSubstitutionMonoid`** — the variables-only monoid (`carrier = Fin`, the empty-signature /
    initial Σ-monoid): a concrete non-vacuous substitution monoid, all laws by `rfl`.

## Honest scope

The substitution monoid + the substitution-category consequence + the variable-monoid witness.  DEFERRED:
the deep `[𝔽, Set]` substitution TENSOR (the coend presentation of `⊗`); the Σ-algebra compatibility making
a concrete model a full Σ-MONOID over the FX signature — the `RawTerm` instance is the SSC-algebra
reconciliation (term-26 / term-27 / context-28); and SOAS COMPLETENESS (Fiore-Hur).  `RawTerm` is the
INITIAL Σ-monoid, and its recursion principle is `term-1`'s `cata`.

## Zero-axiom verification

A model record, the `kleisliComp` definition, the three category laws (each a direct application of a monoid
law — the assignment equalities are stated POINTWISE to stay funext-free), and the variable-monoid witness
(all laws `rfl`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditTier0TermSubstitutionMonoid.lean`.
-/

namespace FX1Poly.Core

/-- A **substitution monoid** (Fiore-Plotkin-Turi, de Bruijn form): a context-indexed family with variables
(`var`, the unit) and capture-avoiding parallel substitution (`subst`, the multiplication), satisfying the
three monoid laws.  An assignment `Fin scope → carrier scope'` substitutes a term for each variable. -/
structure SubstitutionMonoid where
  /-- The terms in each context (`carrier n` = terms with `n` free variables). -/
  carrier : Nat → Type
  /-- The unit: the variable embedding `η : V → T`. -/
  var : {scope : Nat} → Fin scope → carrier scope
  /-- The multiplication: parallel substitution `t[σ]`. -/
  subst : {scope scope' : Nat} → carrier scope → (Fin scope → carrier scope') → carrier scope'
  /-- Right unit: substituting into a variable picks its assignment, `(var i)[σ] = σ i`. -/
  substVar : ∀ {scope scope' : Nat} (index : Fin scope) (assignment : Fin scope → carrier scope'),
    subst (var index) assignment = assignment index
  /-- Left unit: substituting the variable assignment is the identity, `t[var] = t`. -/
  substId : ∀ {scope : Nat} (term : carrier scope), subst term var = term
  /-- Associativity: nested substitution is substitution by the composite, `t[σ][τ] = t[σ ; τ]`. -/
  substAssoc : ∀ {scope scope' scope'' : Nat} (term : carrier scope)
    (firstAssignment : Fin scope → carrier scope')
    (secondAssignment : Fin scope' → carrier scope''),
    subst (subst term firstAssignment) secondAssignment
      = subst term (fun index => subst (firstAssignment index) secondAssignment)

/-- The **Kleisli composition** of assignments — the substitution category's morphism composition:
`(σ ; τ) i = (σ i)[τ]`. -/
def SubstitutionMonoid.kleisliComp (monoid : SubstitutionMonoid) {first second third : Nat}
    (firstAssignment : Fin first → monoid.carrier second)
    (secondAssignment : Fin second → monoid.carrier third) : Fin first → monoid.carrier third :=
  fun index => monoid.subst (firstAssignment index) secondAssignment

/-- ★ **Left identity of the substitution category**: `var ; σ = σ` (pointwise) — from the right-unit law. -/
theorem SubstitutionMonoid.kleisli_leftId (monoid : SubstitutionMonoid) {first second : Nat}
    (assignment : Fin first → monoid.carrier second) (index : Fin first) :
    monoid.kleisliComp monoid.var assignment index = assignment index :=
  monoid.substVar index assignment

/-- ★ **Right identity of the substitution category**: `σ ; var = σ` (pointwise) — from the left-unit law. -/
theorem SubstitutionMonoid.kleisli_rightId (monoid : SubstitutionMonoid) {first second : Nat}
    (assignment : Fin first → monoid.carrier second) (index : Fin first) :
    monoid.kleisliComp assignment monoid.var index = assignment index :=
  monoid.substId (assignment index)

/-- ★ **Associativity of the substitution category**: `(ρ ; σ) ; τ = ρ ; (σ ; τ)` (pointwise) — from the
substitution-associativity law.  Substitution monoid laws ⟹ the substitution (Kleisli) category. -/
theorem SubstitutionMonoid.kleisli_assoc (monoid : SubstitutionMonoid) {first second third fourth : Nat}
    (firstAssignment : Fin first → monoid.carrier second)
    (secondAssignment : Fin second → monoid.carrier third)
    (thirdAssignment : Fin third → monoid.carrier fourth) (index : Fin first) :
    monoid.kleisliComp (monoid.kleisliComp firstAssignment secondAssignment) thirdAssignment index
      = monoid.kleisliComp firstAssignment (monoid.kleisliComp secondAssignment thirdAssignment) index := by
  show monoid.subst (monoid.subst (firstAssignment index) secondAssignment) thirdAssignment
        = monoid.subst (firstAssignment index)
            (fun innerIndex => monoid.subst (secondAssignment innerIndex) thirdAssignment)
  exact monoid.substAssoc (firstAssignment index) secondAssignment thirdAssignment

/-- The **variables-only substitution monoid** (`carrier = Fin`): the empty-signature / initial Σ-monoid,
where substitution is just reindexing.  A concrete non-vacuous substitution monoid — all three laws `rfl`. -/
def variableSubstitutionMonoid : SubstitutionMonoid where
  carrier := Fin
  var := fun index => index
  subst := fun varIndex assignment => assignment varIndex
  substVar := fun _index _assignment => rfl
  substId := fun _term => rfl
  substAssoc := fun _term _firstAssignment _secondAssignment => rfl

end FX1Poly.Core

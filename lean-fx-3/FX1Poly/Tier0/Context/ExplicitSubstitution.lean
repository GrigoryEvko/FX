import FX1Poly.Tier0.Context.ComprehensionSigma
import FX1Poly.Tier0.Context.Strictification

/-! # context-8 — the explicit substitution calculus λσ (Abadi–Cardelli–Curien–Lévy)

`context-8` is the EXPLICIT SUBSTITUTION rung: λσ (Abadi–Cardelli–Curien–Lévy 1991), where substitution
is reified as first-order SYNTAX with its own rewrite rules, rather than living as a meta-level operation.
The task's two named deliverables are **confluence** and **the non-termination boundary**.

## What is context-side here, and what is not

λσ has two sorts — TERMS (`a b`, `λa`, the closure `a[s]`) and SUBSTITUTIONS (`id`, `↑`, `a · s`, `s ∘ t`).
The SUBSTITUTION sort is exactly the morphism structure of the context category: `id` is the identity
substitution, `↑` the display/weakening map, `a · s` comprehension extension, `s ∘ t` composition.  That
sort lives purely on the BASE of contexts-and-substitutions — it IS `fxBaseSubstCategory` (context-0) with
its comprehension (context-1).  This file ships the substitution-sort calculus.

The TERM sort (the closures `a[s]` and the β-rule that interact with λ-abstraction) is `×term`, and it is
where the famous failure lives — so it is the honest **non-termination boundary** (see the ledger below).

## The σ-rules as data, denoting into the proven category

`SubstExpr target source` reifies a substitution `source ⟶ target` as first-order syntax
(`identitySub`/`shiftSub`/`consSub`/`composeSub`).  `SubstExpr.denote` interprets it into the semantic
`SubstVec` category.  The seven λσ substitution rules become a rewrite relation `SubstStep`, and EACH rule
is a PROVEN equation of `fxBaseSubstCategory`:

| λσ rule        | as `SubstStep`     | sound because (the proven `SubstVec` law)          |
| -------------- | ------------------ | -------------------------------------------------- |
| `id ∘ s → s`   | `idLeft`           | `SubstVec.identity_compose`                        |
| `s ∘ id → s`   | `idRight`          | `SubstVec.compose_identity`                        |
| `(s∘t)∘u→s∘(t∘u)` | `assoc`         | `SubstVec.compose_assoc`                           |
| `↑ ∘ (a·s) → s`| `shiftCons`        | `SubstVec.weakening_compose_cons` (the p-law)      |
| `(a·s)∘t → a[t]·(s∘t)` | `mapCons`  | `SubstVec.cons_compose` (Beck–Chevalley / Frobenius)|
| `0·↑ → id`     | `varShift`         | `SubstVec.identity_succ_eq_cons`                   |
| `0[σ]·(↑∘σ) → σ` | `surjPairing`    | `SubstVec.cons_unique` + `subst_varCell` (η/surjective pairing) |

Because the term head of the `mapCons`/`surjPairing` rules is the EAGERLY-EVALUATED `RawTerm.subst …`
(terms are not reified here — only substitutions are), the term-level Clos rule `a[s][t] = a[s∘t]` is
absorbed into `RawTerm.subst_compose` and never needs to be an explicit rewrite.  This eager-head choice is
exactly what keeps the calculus strongly normalizing — the closures that break λσ's PSN cannot form.

## CONFLUENCE — delivered as denotational Church–Rosser

Since every `SubstStep` is a proven `SubstVec` equation, `denote` is INVARIANT under rewriting
(`SubstStep.denote_eq`), hence under any number of steps (`SubstStepStar.denote_eq`).  Therefore the
calculus is **Church–Rosser modulo denotation** (`substExpr_churchRosser_modulo_denote`): any two reducts
of a common expression denote to the SAME morphism of `fxBaseSubstCategory`.  The semantic `SubstVec` IS
the substitution's normal form, and rewriting can never disagree about it.

## The NON-TERMINATION BOUNDARY (honest ledger, `×term · fib`)

The substitution sort shipped here is well-behaved.  The boundary is the TERM sort: full λσ — with the
term closure `a[s]` reified syntactically and the β-rule `(λa) b → a[b · id]` — does **NOT** preserve
strong normalization (Melliès 1995, "Typed λ-calculi with explicit substitutions may not terminate"): there
is a strongly-normalizing pure λ-term whose λσ image admits an infinite reduction, because composition lets
a substitution be duplicated and re-enter a term redex.  That phenomenon is `×term` (it requires the term
closures this file deliberately does not reify) and is deferred to the term axis / `fib`.  The PSN-preserving
repairs (λυ without composition, λσ⇑, λse, λx) are the term-axis sequels.

DEFERRED to the term axis / `fib`: the term closures `a[s]`, the β-rule, the full syntactic critical-pair
Church–Rosser via Newman (this file delivers the denotational form), and the Melliès PSN counterexample.

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-! ## The explicit-substitution syntax -/

/-- **λσ substitution expressions** — a substitution `source ⟶ target` reified as first-order SYNTAX
(well-scoped).  The four λσ substitution constructors: the identity `id`, the shift/display `↑`, the
comprehension extension `a · s` (`consSub`), and composition `s ∘ t` (`composeSub`).  This is the
first-order presentation of `fxBaseSubstCategory`'s morphisms; `SubstExpr.denote` is the interpretation. -/
inductive SubstExpr : Nat → Nat → Type where
  /-- The identity substitution `id : n ⟶ n`. -/
  | identitySub {scope : Nat} : SubstExpr scope scope
  /-- The shift / display substitution `↑ : (n+1) ⟶ n` (weakening by the freshly-bound variable). -/
  | shiftSub {scope : Nat} : SubstExpr (scope + 1) scope
  /-- Comprehension extension `head · tail : target ⟶ (source+1)` — prepend an image for variable 0. -/
  | consSub {target source : Nat} (head : RawTerm target) (tail : SubstExpr target source) :
      SubstExpr target (source + 1)
  /-- Composition `first ∘ second : target ⟶ source` — apply `first` then `second` (`a[first ∘ second]
  = a[first][second]`). -/
  | composeSub {mid source target : Nat} (first : SubstExpr mid source) (second : SubstExpr target mid) :
      SubstExpr target source

/-- **The interpretation into the semantic substitution category.**  Maps each λσ substitution
constructor to its `SubstVec` (context-0/1) meaning: `id ↦ identity`, `↑ ↦ weakening`, `· ↦ cons`,
`∘ ↦ compose`.  `denote` is the unique structure-preserving map from the syntax to `fxBaseSubstCategory`. -/
def SubstExpr.denote : {target source : Nat} → SubstExpr target source → SubstVec target source
  | _, _, .identitySub => SubstVec.identity _
  | _, _, .shiftSub => SubstVec.weakening _
  | _, _, .consSub head tail => SubstVec.cons head (SubstExpr.denote tail)
  | _, _, .composeSub first second => (SubstExpr.denote first).compose (SubstExpr.denote second)

/-- `denote` unfolder: the identity expression denotes to the identity substitution. -/
@[simp] theorem SubstExpr.denote_identitySub (scope : Nat) :
    (SubstExpr.identitySub : SubstExpr scope scope).denote = SubstVec.identity scope := rfl

/-- `denote` unfolder: the shift expression denotes to the weakening/display map. -/
@[simp] theorem SubstExpr.denote_shiftSub (scope : Nat) :
    (SubstExpr.shiftSub : SubstExpr (scope + 1) scope).denote = SubstVec.weakening scope := rfl

/-- `denote` unfolder: a comprehension extension denotes to a `cons`. -/
@[simp] theorem SubstExpr.denote_consSub {target source : Nat} (head : RawTerm target)
    (tail : SubstExpr target source) :
    (SubstExpr.consSub head tail).denote = SubstVec.cons head tail.denote := rfl

/-- `denote` unfolder: a composition denotes to a `SubstVec` composition. -/
@[simp] theorem SubstExpr.denote_composeSub {mid source target : Nat} (first : SubstExpr mid source)
    (second : SubstExpr target mid) :
    (SubstExpr.composeSub first second).denote = (first.denote).compose (second.denote) := rfl

/-! ## The σ-rewrite relation (the seven λσ substitution rules + congruence) -/

/-- **The λσ substitution-rewrite relation.**  Seven oriented σ-rules (left-to-right, the computational
orientation that evaluates a substitution to a comprehension/shift normal form) plus the three congruence
closures (rewrite under either side of a composition, or under a comprehension tail).  Each rule is sound
for `fxBaseSubstCategory` — see `SubstStep.denote_eq`.  Terms are NOT rewritten here (the head of a
`consSub` is an opaque `RawTerm`); this relation rewrites the SUBSTITUTION structure only, which is the
context-side sort of λσ. -/
inductive SubstStep : {target source : Nat} → SubstExpr target source → SubstExpr target source → Prop where
  /-- `id ∘ s → s`. -/
  | idLeft {target source : Nat} (s : SubstExpr target source) :
      SubstStep (SubstExpr.composeSub SubstExpr.identitySub s) s
  /-- `s ∘ id → s`. -/
  | idRight {target source : Nat} (s : SubstExpr target source) :
      SubstStep (SubstExpr.composeSub s SubstExpr.identitySub) s
  /-- `(s ∘ t) ∘ u → s ∘ (t ∘ u)` — re-associate composition to the right. -/
  | assoc {scopeA scopeB scopeC scopeD : Nat} (s : SubstExpr scopeB scopeA)
      (t : SubstExpr scopeC scopeB) (u : SubstExpr scopeD scopeC) :
      SubstStep (SubstExpr.composeSub (SubstExpr.composeSub s t) u)
        (SubstExpr.composeSub s (SubstExpr.composeSub t u))
  /-- `↑ ∘ (head · tail) → tail` — the p-law: shift cancels the freshly-extended head. -/
  | shiftCons {target source : Nat} (head : RawTerm target) (tail : SubstExpr target source) :
      SubstStep (SubstExpr.composeSub SubstExpr.shiftSub (SubstExpr.consSub head tail)) tail
  /-- `(head · tail) ∘ t → head[t] · (tail ∘ t)` — Beck–Chevalley / Frobenius: composition distributes
  through comprehension, evaluating the head substitution eagerly. -/
  | mapCons {mid source target : Nat} (head : RawTerm mid) (tail : SubstExpr mid source)
      (t : SubstExpr target mid) :
      SubstStep (SubstExpr.composeSub (SubstExpr.consSub head tail) t)
        (SubstExpr.consSub (RawTerm.subst t.denote.toRawTermSubst head)
          (SubstExpr.composeSub tail t))
  /-- `0 · ↑ → id` — variable-shift: extending by variable 0 over shift is the identity. -/
  | varShift {scope : Nat} :
      SubstStep (SubstExpr.consSub (SubstVec.varCell ⟨0, Nat.succ_pos scope⟩)
          (SubstExpr.shiftSub : SubstExpr (scope + 1) scope)) SubstExpr.identitySub
  /-- `0[σ] · (↑ ∘ σ) → σ` — surjective pairing / η for substitutions (generalizes `varShift`). -/
  | surjPairing {target source : Nat} (sigma : SubstExpr target (source + 1)) :
      SubstStep (SubstExpr.consSub
          (RawTerm.subst sigma.denote.toRawTermSubst (SubstVec.varCell ⟨0, Nat.succ_pos source⟩))
          (SubstExpr.composeSub (SubstExpr.shiftSub : SubstExpr (source + 1) source) sigma)) sigma
  /-- Congruence: rewrite the left operand of a composition. -/
  | composeLeft {mid source target : Nat} {first first' : SubstExpr mid source}
      (second : SubstExpr target mid) (step : SubstStep first first') :
      SubstStep (SubstExpr.composeSub first second) (SubstExpr.composeSub first' second)
  /-- Congruence: rewrite the right operand of a composition. -/
  | composeRight {mid source target : Nat} (first : SubstExpr mid source)
      {second second' : SubstExpr target mid} (step : SubstStep second second') :
      SubstStep (SubstExpr.composeSub first second) (SubstExpr.composeSub first second')
  /-- Congruence: rewrite the tail of a comprehension. -/
  | consTail {target source : Nat} (head : RawTerm target) {tail tail' : SubstExpr target source}
      (step : SubstStep tail tail') :
      SubstStep (SubstExpr.consSub head tail) (SubstExpr.consSub head tail')

/-- ★ **Every σ-rewrite preserves the denotation.**  A single `SubstStep` maps to an EQUALITY of
morphisms in `fxBaseSubstCategory`: each of the seven λσ rules is one of the proven category/comprehension
laws, and the three congruence closures lift through `denote` by `congrArg`.  This is the soundness of the
λσ substitution-equational theory for the FX substitution category. -/
theorem SubstStep.denote_eq {target source : Nat} {a b : SubstExpr target source}
    (step : SubstStep a b) : a.denote = b.denote := by
  induction step with
  | idLeft s =>
      rw [SubstExpr.denote_composeSub, SubstExpr.denote_identitySub]
      exact SubstVec.identity_compose s.denote
  | idRight s =>
      rw [SubstExpr.denote_composeSub, SubstExpr.denote_identitySub]
      exact SubstVec.compose_identity s.denote
  | assoc s t u =>
      rw [SubstExpr.denote_composeSub, SubstExpr.denote_composeSub, SubstExpr.denote_composeSub,
          SubstExpr.denote_composeSub]
      exact SubstVec.compose_assoc s.denote t.denote u.denote
  | shiftCons head tail =>
      rw [SubstExpr.denote_composeSub, SubstExpr.denote_shiftSub, SubstExpr.denote_consSub]
      exact SubstVec.weakening_compose_cons head tail.denote
  | mapCons head tail t =>
      rw [SubstExpr.denote_composeSub, SubstExpr.denote_consSub, SubstExpr.denote_consSub,
          SubstExpr.denote_composeSub]
      exact SubstVec.cons_compose head tail.denote t.denote
  | varShift =>
      rw [SubstExpr.denote_consSub, SubstExpr.denote_shiftSub, SubstExpr.denote_identitySub]
      exact (SubstVec.identity_succ_eq_cons _).symm
  | surjPairing sigma =>
      rw [SubstExpr.denote_consSub, SubstExpr.denote_composeSub, SubstExpr.denote_shiftSub,
          SubstVec.subst_varCell]
      exact (SubstVec.cons_unique _ _ sigma.denote rfl rfl).symm
  | composeLeft second _ ih =>
      rw [SubstExpr.denote_composeSub, SubstExpr.denote_composeSub]
      exact congrArg (fun leftVec => leftVec.compose second.denote) ih
  | composeRight first _ ih =>
      rw [SubstExpr.denote_composeSub, SubstExpr.denote_composeSub]
      exact congrArg (fun rightVec => first.denote.compose rightVec) ih
  | consTail head _ ih =>
      rw [SubstExpr.denote_consSub, SubstExpr.denote_consSub]
      exact congrArg (SubstVec.cons head) ih

/-! ## The reflexive-transitive closure + denotational Church–Rosser -/

/-- The reflexive-transitive closure of `SubstStep` — multi-step σ-reduction. -/
inductive SubstStepStar : {target source : Nat} → SubstExpr target source → SubstExpr target source → Prop where
  /-- Zero steps. -/
  | refl {target source : Nat} (e : SubstExpr target source) : SubstStepStar e e
  /-- One step then the rest. -/
  | head {target source : Nat} {a b c : SubstExpr target source}
      (step : SubstStep a b) (rest : SubstStepStar b c) : SubstStepStar a c

/-- Multi-step σ-reduction preserves the denotation (iterate `SubstStep.denote_eq`). -/
theorem SubstStepStar.denote_eq {target source : Nat} {a b : SubstExpr target source}
    (steps : SubstStepStar a b) : a.denote = b.denote := by
  induction steps with
  | refl _ => rfl
  | head step _ ih => exact (step.denote_eq).trans ih

/-- ★ **The λσ substitution calculus is Church–Rosser modulo denotation.**  Any two σ-reducts of a common
expression denote to the SAME morphism of `fxBaseSubstCategory`.  Because the semantic `SubstVec` is the
fully-evaluated substitution, this says rewriting can never produce two reachable forms that disagree on
the substitution they represent — the confluence guarantee at the level of meaning. -/
theorem substExpr_churchRosser_modulo_denote {target source : Nat} {a b c : SubstExpr target source}
    (toB : SubstStepStar a b) (toC : SubstStepStar a c) : b.denote = c.denote :=
  (toB.denote_eq).symm.trans toC.denote_eq

/-! ## Smoke: a concrete reduction with its denotation preserved -/

/-- Smoke: `id ∘ id → id` is a `SubstStep`, and (via `denote_eq`) both sides denote to `identity`. -/
theorem SubstStep.idLeft_identity_smoke (scope : Nat) :
    SubstStep (SubstExpr.composeSub (SubstExpr.identitySub : SubstExpr scope scope) SubstExpr.identitySub)
      SubstExpr.identitySub :=
  SubstStep.idLeft SubstExpr.identitySub

/-! ## STRONG NORMALIZATION — the weight certificate

Every σ-rewrite strictly decreases a `Nat`-valued weight, so there is NO infinite reduction sequence: the
substitution-sort calculus is strongly normalizing.  The weight counts the LEFT operand of a composition
TWICE, RIGHT-ASSOCIATED — `weight (s ∘ t) = weight s + (weight s + weight t)` — which is exactly what makes
the restructuring rules strictly decrease: `assoc` `(s∘t)∘u → s∘(t∘u)` drops a doubled `weight s`, and
`mapCons` `(a·s)∘t → a[t]·(s∘t)` drops one count.

### COMMUTATIVITY-FREE — and why pure `rfl` is impossible

A per-step decrease between SYMBOLIC sub-term weights can never hold by `rfl`: `Nat.ble` is stuck on opaque
arguments, and Nat's `+` recurses on its RIGHT operand, so `weight s + weight s` does not reduce.  So SN
genuinely needs lemmas — but it needs NO commutativity.  The RIGHT-ASSOCIATION is the trick: with
`weight (s ∘ t) = weight s + (weight s + weight t)`,

  * `assoc` decreases by right-associating the left-nested RHS with explicit `rw [Nat.add_assoc …]` (a
    DIRECTIONAL rewrite, no permutation) to expose the common `weight s + (weight s + (weight t + ·))`
    prefix, peeling it with `Nat.add_lt_add_left`, down to a base discharged by `natLtAddLeft`;
  * `mapCons` decreases because both `+1`s float OUT to a `Nat.succ` tower via explicit `rw` with the
    DIRECTIONAL successor laws `Nat.add_one` / `Nat.succ_add` / `Nat.add_succ` (again no permutation);
  * the leaf rules are `natLtAddLeft` (a 2-line structural recursion whose recursive step holds because
    `amount + (offset+1)` reduces DEFINITIONALLY to `Nat.succ (amount + offset)`), and the congruences are
    plain `+`-monotonicity.

No `Nat.add_comm`, no `Nat.add_left_comm`, no `simp`-AC anywhere (the earlier `propext` leak came precisely
from `simp`'s permutative AC normalization, which is now gone).  Everything is axiom-free; it is not — and
provably cannot be — pure `rfl`, but it never appeals to commutativity (AC = associativity-commutativity,
NOT the axiom of choice; `Classical.choice` is absent, as the gate verifies).

Contrast the **non-termination boundary**: this SN holds because terms are NOT reified — the `mapCons`/
`surjPairing` heads are eagerly-evaluated `RawTerm.subst …`, so no term-closure `a[s]` can persist and be
duplicated by composition.  Reifying closures + the β-rule (full λσ) breaks exactly this and forfeits PSN
(Melliès 1995) — the `×term` boundary deferred to the term axis / `fib`. -/

/-- The strong-normalization weight: identity/shift cost 1, a comprehension costs its tail + 1, and a
composition costs its LEFT operand TWICE plus its right (the doubling is what forces `assoc`/`mapCons` to
strictly decrease). -/
def SubstExpr.weight : {target source : Nat} → SubstExpr target source → Nat
  | _, _, .identitySub => 1
  | _, _, .shiftSub => 1
  | _, _, .consSub _ tail => SubstExpr.weight tail + 1
  | _, _, .composeSub first second =>
      SubstExpr.weight first + (SubstExpr.weight first + SubstExpr.weight second)

/-- `weight` unfolder: the identity expression weighs 1. -/
@[simp] theorem SubstExpr.weight_identitySub (scope : Nat) :
    (SubstExpr.identitySub : SubstExpr scope scope).weight = 1 := rfl

/-- `weight` unfolder: the shift expression weighs 1. -/
@[simp] theorem SubstExpr.weight_shiftSub (scope : Nat) :
    (SubstExpr.shiftSub : SubstExpr (scope + 1) scope).weight = 1 := rfl

/-- `weight` unfolder: a comprehension weighs its tail + 1. -/
@[simp] theorem SubstExpr.weight_consSub {target source : Nat} (head : RawTerm target)
    (tail : SubstExpr target source) :
    (SubstExpr.consSub head tail).weight = tail.weight + 1 := rfl

/-- `weight` unfolder: a composition weighs its left operand twice plus its right, RIGHT-ASSOCIATED
(`Wf + (Wf + Wg)`).  The right association is the whole trick: it makes every decrease provable from
associativity + successor laws + monotonicity, with NO appeal to commutativity. -/
@[simp] theorem SubstExpr.weight_composeSub {mid source target : Nat} (first : SubstExpr mid source)
    (second : SubstExpr target mid) :
    (SubstExpr.composeSub first second).weight = first.weight + (first.weight + second.weight) := rfl

/-- Every substitution expression has strictly positive weight. -/
theorem SubstExpr.weight_pos {target source : Nat} (e : SubstExpr target source) : 0 < e.weight := by
  induction e with
  | identitySub => exact Nat.one_pos
  | shiftSub => exact Nat.one_pos
  | consSub _ tail _ => rw [SubstExpr.weight_consSub]; exact Nat.succ_pos _
  | composeSub first second ihFirst _ =>
      rw [SubstExpr.weight_composeSub]
      exact Nat.lt_of_lt_of_le ihFirst
        (Nat.le_add_right first.weight (first.weight + second.weight))

/-- A strictly-positive amount added ON THE LEFT strictly increases: `offset < amount + offset`.  Proved
by STRUCTURAL RECURSION on `offset` with `amount + (offset+1)` reducing DEFINITIONALLY to
`Nat.succ (amount + offset)` (`Nat.add` recurses on its right operand) — no commutativity, no `Nat.add_comm`.
This is the only arithmetic helper the decrease proofs need beyond the standard monotonicity lemmas. -/
private theorem natLtAddLeft {amount : Nat} (amountPos : 0 < amount) :
    (offset : Nat) → offset < amount + offset
  | 0 => amountPos
  | offset + 1 => Nat.succ_lt_succ (natLtAddLeft amountPos offset)

/-- ★ **Every σ-rewrite strictly decreases the weight.**  COMMUTATIVITY-FREE: with the right-associated
weight, `assoc` decreases by right-associating both sides (directional `Nat.add_assoc`) then peeling the
common `Wf + (Wf + (Wt + ·))` prefix with `Nat.add_lt_add_left`; `mapCons` decreases because both sides
collapse to a `Nat.succ` tower via the directional successor laws (`Nat.succ_add`/`Nat.add_succ`); the leaf
rules use `natLtAddLeft`; the congruences use plain `+`-monotonicity.  No `Nat.add_comm`, no `simp`-AC.
This is the termination certificate — axiom-free. -/
theorem SubstStep.weight_decreasing {target source : Nat} {a b : SubstExpr target source}
    (step : SubstStep a b) : b.weight < a.weight := by
  induction step with
  | idLeft s =>
      dsimp only [SubstExpr.weight_composeSub, SubstExpr.weight_identitySub]
      exact Nat.lt_trans (natLtAddLeft Nat.one_pos s.weight)
        (natLtAddLeft Nat.one_pos (1 + s.weight))
  | idRight s =>
      dsimp only [SubstExpr.weight_composeSub, SubstExpr.weight_identitySub]
      exact Nat.lt_add_of_pos_right (Nat.succ_pos s.weight)
  | assoc s t u =>
      dsimp only [SubstExpr.weight_composeSub]
      -- right-associate the left-nested RHS to expose the common `Ws+(Ws+(Wt+·))` prefix (no commutativity)
      rw [Nat.add_assoc s.weight (s.weight + t.weight)
            ((s.weight + (s.weight + t.weight)) + u.weight),
          Nat.add_assoc s.weight t.weight
            ((s.weight + (s.weight + t.weight)) + u.weight)]
      -- peel the prefix; base: t.weight + u.weight < (Ws+(Ws+Wt)) + u.weight
      exact Nat.add_lt_add_left (Nat.add_lt_add_left (Nat.add_lt_add_left
        (Nat.add_lt_add_right
          (Nat.lt_of_lt_of_le (natLtAddLeft s.weight_pos t.weight)
            (Nat.add_le_add_left (Nat.le_add_left t.weight s.weight) s.weight))
          u.weight)
        t.weight) s.weight) s.weight
  | shiftCons head tail =>
      dsimp only [SubstExpr.weight_composeSub, SubstExpr.weight_shiftSub, SubstExpr.weight_consSub]
      exact Nat.lt_trans (Nat.lt_succ_self tail.weight)
        (Nat.lt_trans (natLtAddLeft Nat.one_pos (tail.weight + 1))
          (natLtAddLeft Nat.one_pos (1 + (tail.weight + 1))))
  | mapCons head tail t =>
      dsimp only [SubstExpr.weight_composeSub, SubstExpr.weight_consSub]
      -- both `+1`s float OUT to a succ-tower via the directional successor laws (no commutativity)
      have collapse : (tail.weight + 1) + ((tail.weight + 1) + t.weight)
          = ((tail.weight + (tail.weight + t.weight)) + 1) + 1 := by
        rw [Nat.add_one tail.weight, Nat.succ_add, Nat.succ_add, Nat.add_succ]
      rw [collapse]
      exact Nat.lt_succ_self _
  | varShift =>
      dsimp only [SubstExpr.weight_consSub, SubstExpr.weight_shiftSub, SubstExpr.weight_identitySub]
      exact Nat.lt_succ_self 1
  | surjPairing sigma =>
      dsimp only [SubstExpr.weight_consSub, SubstExpr.weight_composeSub, SubstExpr.weight_shiftSub]
      exact Nat.lt_trans
        (Nat.lt_trans (natLtAddLeft Nat.one_pos sigma.weight)
          (natLtAddLeft Nat.one_pos (1 + sigma.weight)))
        (Nat.lt_succ_self _)
  | @composeLeft mid source target first first' second _ ih =>
      dsimp only [SubstExpr.weight_composeSub]
      exact Nat.lt_trans
        (Nat.add_lt_add_left (Nat.add_lt_add_right ih second.weight) first'.weight)
        (Nat.add_lt_add_right ih (first.weight + second.weight))
  | @composeRight mid source target first second second' _ ih =>
      dsimp only [SubstExpr.weight_composeSub]
      exact Nat.add_lt_add_left (Nat.add_lt_add_left ih first.weight) first.weight
  | @consTail target source head tail tail' _ ih =>
      dsimp only [SubstExpr.weight_consSub]
      exact Nat.succ_lt_succ ih

/-- ★ **The λσ substitution-rewrite relation is well-founded** (no infinite reduction sequence): the
"is-a-reduct-of" relation is the inverse image of `Nat.<` under the strictly-decreasing `weight`. -/
theorem SubstStep.wellFounded {target source : Nat} :
    WellFounded (fun reduct subject : SubstExpr target source => SubstStep subject reduct) :=
  Subrelation.wf
    (fun {_reduct _subject} (step : SubstStep _subject _reduct) => step.weight_decreasing)
    (InvImage.wf SubstExpr.weight Nat.lt_wfRel.wf)

/-- ★ **Strong normalization**: every substitution expression is accessible under σ-reduction — there is no
infinite chain of `SubstStep`s out of it.  Together with `substExpr_churchRosser_modulo_denote` this says
σ-reduction always terminates at a form whose denotation is the original substitution. -/
theorem SubstStep.stronglyNormalizing {target source : Nat} (e : SubstExpr target source) :
    Acc (fun reduct subject : SubstExpr target source => SubstStep subject reduct) e :=
  SubstStep.wellFounded.apply e

end FX1Poly.Tier0

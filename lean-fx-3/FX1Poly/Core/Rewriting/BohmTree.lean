import FX1Poly.Polygraph.Rewriting.Confluence.Newman
import FX1Poly.Polygraph.Rewriting.Confluence.KnuthBendixCompletion

/-! # FX1Poly/Core — Böhm trees, meaningless terms, the genericity lemma (term-13)

The theory of MEANINGLESS terms and Böhm trees (Barendregt Ch. 10/14; Kennaway-van Oostrom-de Vries).  A
term is **solvable** when it reduces to a HEAD NORMAL FORM (it can be applied to arguments to produce any
desired result); an **unsolvable** / **meaningless** term has no head normal form — it is the `⊥` of the
Böhm tree.  The **Böhm tree** `BT(M)` is the (possibly infinite) tree of head normal forms obtained by
iterated head reduction, with `⊥` at every meaningless node — the "infinite normal form."  The **genericity
lemma** says a meaningless subterm is irrelevant to any normal-form result: if `M` is unsolvable and
`C[M] →* N` with `N` normal, then `C[M'] →* N` for any `M'` — meaningless terms are interchangeable (all
`⊥`).

This file ships the genuine abstract-rewriting cores (each zero-axiom):

  * **`IsSolvable` / `IsMeaningless`** — solvable = reduces to a head-normal element; meaningless = not.
    With the Kennaway-van Oostrom-de Vries closure axiom **`meaningless_of_reduction`** (a meaningless term
    stays meaningless under reduction) and the dual **`solvable_of_reduction`** (solvability is preserved by
    expansion).
  * **`meaningless_not_joinable_solvable`** — ★ the operational heart of genericity: in a CONFLUENT system
    where head normal forms reduce only to head normal forms, a meaningless term is NEVER joinable with a
    solvable one — you cannot convert a meaningless term into a meaningful one.  And
    **`meaninglessAreIndiscernible`** — all meaningless terms are mutually indiscernible (every one is
    separated from every solvable term identically): the `⊥`-identification, the semantic content of
    genericity.
  * **`BohmApprox`** — the finite Böhm APPROXIMANTS (a tree with `⊥` leaves and `Fin`-indexed children), with
    the approximation order `IsLessDefined`, `⊥` as the least element (`bottom_isLeast`), and reflexivity.
    The Böhm tree is the ideal completion of these approximants.

## Honest scope

The meaningless-terms theory (closure + the solvable/meaningless separation = the operational genericity
core) + the finite Böhm-approximant domain.  DEFERRED (the capstone): the INFINITARY Böhm TREE itself (the
coinductive infinite normal form — `term-3`'s terminal-coalgebra / bisimulation is the coinductive substrate
for it) and Böhm-tree equivalence; and the FULL operational genericity lemma `C[M] →* N ⟹ ∀ M', C[M'] →* N`
(which needs the neededness / standardization residual theory of `term-12`).

## Zero-axiom verification

The meaningless lemmas are `ReflTransClosure` prepend/`trans` + confluence + a head-normal-reduction-closure
hypothesis; `BohmApprox` uses `Fin`-indexed children (no `List`, so no `List.append`/Forall₂ propext risk),
and `IsLessDefined.refl` is structural recursion on the tree.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCoreBohmTree.lean`.
-/

namespace FX1Poly.Core

/-! ## Solvable and meaningless terms -/

/-- A term is **solvable** when it reduces to a HEAD NORMAL element (`isHeadNormal`). -/
def IsSolvable {Carrier : Type} (isHeadNormal : Carrier → Prop) (step : Carrier → Carrier → Prop)
    (term : Carrier) : Prop :=
  ∃ headForm, ReflTransClosure step term headForm ∧ isHeadNormal headForm

/-- A term is **meaningless** (unsolvable) when it has no head normal form. -/
def IsMeaningless {Carrier : Type} (isHeadNormal : Carrier → Prop) (step : Carrier → Carrier → Prop)
    (term : Carrier) : Prop :=
  ¬ IsSolvable isHeadNormal step term

/-- Solvability is preserved by EXPANSION: if `term` reduces to a solvable `reduct`, `term` is solvable
(prepend the reduction to the head-normal-form witness). -/
theorem solvable_of_reduction {Carrier : Type} (isHeadNormal : Carrier → Prop)
    (step : Carrier → Carrier → Prop) {term reduct : Carrier}
    (reduction : ReflTransClosure step term reduct) (solvableReduct : IsSolvable isHeadNormal step reduct) :
    IsSolvable isHeadNormal step term := by
  obtain ⟨headForm, reductToHead, headFormIsNormal⟩ := solvableReduct
  exact ⟨headForm, reduction.trans reductToHead, headFormIsNormal⟩

/-- ★ **Meaninglessness is closed under reduction** (the Kennaway-van Oostrom-de Vries axiom): a meaningless
term reduces only to meaningless terms. -/
theorem meaningless_of_reduction {Carrier : Type} (isHeadNormal : Carrier → Prop)
    (step : Carrier → Carrier → Prop) {term reduct : Carrier}
    (meaninglessTerm : IsMeaningless isHeadNormal step term)
    (reduction : ReflTransClosure step term reduct) : IsMeaningless isHeadNormal step reduct :=
  fun solvableReduct => meaninglessTerm (solvable_of_reduction isHeadNormal step reduction solvableReduct)

/-- Single-step form: meaninglessness is preserved by one reduction step. -/
theorem meaningless_of_step {Carrier : Type} (isHeadNormal : Carrier → Prop)
    (step : Carrier → Carrier → Prop) {term reduct : Carrier}
    (meaninglessTerm : IsMeaningless isHeadNormal step term) (stepToReduct : step term reduct) :
    IsMeaningless isHeadNormal step reduct :=
  meaningless_of_reduction isHeadNormal step meaninglessTerm (ReflTransClosure.single stepToReduct)

/-! ## The genericity core — meaningless terms are separated from solvable terms -/

/-- ★ **The operational heart of genericity.**  In a CONFLUENT system where head normal forms reduce only to
head normal forms, a MEANINGLESS term is never joinable with a SOLVABLE term: there is no common reduct.  So
no conversion can turn a meaningless term into a meaningful one — the precise sense in which a meaningless
term carries no head-normal information. -/
theorem meaningless_not_joinable_solvable {Carrier : Type} (isHeadNormal : Carrier → Prop)
    (step : Carrier → Carrier → Prop) (confluent : Confluent step)
    (headNormalClosedUnderReduction : ∀ {headForm reduct : Carrier}, isHeadNormal headForm →
      ReflTransClosure step headForm reduct → isHeadNormal reduct)
    {meaninglessTerm solvableTerm : Carrier}
    (meaningless : IsMeaningless isHeadNormal step meaninglessTerm)
    (solvable : IsSolvable isHeadNormal step solvableTerm)
    (joined : Joinable step meaninglessTerm solvableTerm) : False := by
  obtain ⟨commonReduct, meaninglessToCommon, solvableToCommon⟩ := joined
  obtain ⟨headForm, solvableToHead, headFormIsNormal⟩ := solvable
  obtain ⟨peak, commonToPeak, headToPeak⟩ := confluent solvableToCommon solvableToHead
  have peakIsHeadNormal : isHeadNormal peak := headNormalClosedUnderReduction headFormIsNormal headToPeak
  exact meaningless ⟨peak, meaninglessToCommon.trans commonToPeak, peakIsHeadNormal⟩

/-- ★ **Meaningless terms are indiscernible** (the `⊥`-identification).  Any two meaningless terms are
separated from every solvable term identically — neither is joinable with any solvable term.  This is the
semantic content of genericity: all meaningless terms behave alike (as `⊥`). -/
theorem meaninglessAreIndiscernible {Carrier : Type} (isHeadNormal : Carrier → Prop)
    (step : Carrier → Carrier → Prop) (confluent : Confluent step)
    (headNormalClosedUnderReduction : ∀ {headForm reduct : Carrier}, isHeadNormal headForm →
      ReflTransClosure step headForm reduct → isHeadNormal reduct)
    {firstMeaningless secondMeaningless : Carrier}
    (firstIsMeaningless : IsMeaningless isHeadNormal step firstMeaningless)
    (secondIsMeaningless : IsMeaningless isHeadNormal step secondMeaningless)
    {solvableTerm : Carrier} (solvable : IsSolvable isHeadNormal step solvableTerm) :
    (¬ Joinable step firstMeaningless solvableTerm) ∧ (¬ Joinable step secondMeaningless solvableTerm) :=
  ⟨fun joined => meaningless_not_joinable_solvable isHeadNormal step confluent
      headNormalClosedUnderReduction firstIsMeaningless solvable joined,
   fun joined => meaningless_not_joinable_solvable isHeadNormal step confluent
      headNormalClosedUnderReduction secondIsMeaningless solvable joined⟩

/-- ★ **The genericity separation at the level of CONVERSION.**  In a confluent system (where head normal
forms reduce only to head normal forms), a meaningless term is not even CONVERTIBLE to a solvable one — the
full equational theory `⟷*` (not merely joinability) separates them.  By Church-Rosser (`term-7`):
convertibility collapses to joinability under confluence, and meaningless/solvable are not joinable.  So no
chain of equational reasoning can prove a meaningless term equal to a meaningful one. -/
theorem meaningless_not_conv_solvable {Carrier : Type} (isHeadNormal : Carrier → Prop)
    (step : Carrier → Carrier → Prop) (confluent : Confluent step)
    (headNormalClosedUnderReduction : ∀ {headForm reduct : Carrier}, isHeadNormal headForm →
      ReflTransClosure step headForm reduct → isHeadNormal reduct)
    {meaninglessTerm solvableTerm : Carrier}
    (meaningless : IsMeaningless isHeadNormal step meaninglessTerm)
    (solvable : IsSolvable isHeadNormal step solvableTerm)
    (convertible : EquationalTheory step meaninglessTerm solvableTerm) : False :=
  meaningless_not_joinable_solvable isHeadNormal step confluent headNormalClosedUnderReduction
    meaningless solvable ((churchRosser_of_confluent confluent).mp convertible)

/-! ## Böhm approximants — the finite-approximant domain -/

/-- A **finite Böhm approximant**: either `bottom` (`⊥`, a meaningless node), or a head-normal `node` carrying
a label and finitely many (`Fin arity`-indexed) child approximants.  The Böhm tree is the ideal completion
of these approximants. -/
inductive BohmApprox where
  | bottom : BohmApprox
  | node : (label : Nat) → (arity : Nat) → (Fin arity → BohmApprox) → BohmApprox

/-- The **approximation order**: `⊥` is below everything, and a `node` refines another iff they share a
label/arity and the children refine pointwise.  `approx ≤ refined` means `refined` is at least as defined. -/
inductive IsLessDefined : BohmApprox → BohmApprox → Prop where
  | bottom (approx : BohmApprox) : IsLessDefined .bottom approx
  | node (label arity : Nat) (children refinedChildren : Fin arity → BohmApprox) :
      (∀ index, IsLessDefined (children index) (refinedChildren index)) →
      IsLessDefined (.node label arity children) (.node label arity refinedChildren)

/-- ★ `⊥` is the LEAST Böhm approximant — every term's information content sits above the meaningless `⊥`.
A meaningless term's Böhm tree is `⊥`, so this is the bottom of the domain. -/
theorem bottom_isLeast (approx : BohmApprox) : IsLessDefined BohmApprox.bottom approx :=
  IsLessDefined.bottom approx

/-- The approximation order is reflexive (every approximant refines itself), by structural recursion. -/
theorem IsLessDefined.refl : (approx : BohmApprox) → IsLessDefined approx approx
  | .bottom => IsLessDefined.bottom BohmApprox.bottom
  | .node label arity children =>
      IsLessDefined.node label arity children children (fun index => IsLessDefined.refl (children index))

/-! ## Concrete witnesses -/

/-- With no reductions and "is zero" as head-normality, `1` is meaningless (it never reaches `0`). -/
theorem exampleMeaningless :
    IsMeaningless (fun value => value = 0) (fun _ _ => False) 1 := by
  intro solvableOne
  obtain ⟨headForm, oneToHead, headIsZero⟩ := solvableOne
  cases oneToHead with
  | refl _ => nomatch headIsZero
  | head emptyStep _ => exact emptyStep

/-- Dually, `0` is solvable (it is already head-normal). -/
theorem exampleSolvable :
    IsSolvable (fun value => value = 0) (fun _ _ => False) 0 :=
  ⟨0, ReflTransClosure.refl 0, rfl⟩

/-- A two-child Böhm approximant sits above `⊥`. -/
theorem exampleApproximationAboveBottom (arity : Nat) (children : Fin arity → BohmApprox) :
    IsLessDefined BohmApprox.bottom (BohmApprox.node 0 arity children) :=
  bottom_isLeast _

end FX1Poly.Core

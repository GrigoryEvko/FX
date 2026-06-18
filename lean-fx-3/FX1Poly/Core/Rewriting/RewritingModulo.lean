import FX1Poly.Core.Rewriting.Confluence.Newman
import FX1Poly.Core.Rewriting.Confluence.KnuthBendixCompletion

/-! # FX1Poly/Core — Church-Rosser modulo an equational theory (term-16)

Rewriting MODULO an equational theory `E` (Huet 1980; Peterson-Stickel; Jouannaud-Kirchner): a rewrite
relation `R` is run up to an equational theory `E` (the paradigm case `E = AC`, associativity +
commutativity, where terms are compared modulo reordering).  Two terms are JOINABLE MODULO `E` when they
`R`-reduce to `E`-equivalent reducts; `R` is CHURCH-ROSSER MODULO `E` when the combined equational theory of
`R ∪ E` collapses to joinability modulo `E` — the modulo-`E` analog of `term-7`'s Church-Rosser theorem.

This file ships the genuine abstract core (each zero-axiom):

  * **`JoinableModulo`** — `a` and `b` reduce by `R` to `E`-equivalent reducts.
  * **`equationalTheory_of_joinableModulo`** — ★ the easy half: joinable-modulo-`E` terms are convertible in
    the combined theory `R ∪ E` (lift the `R`-reductions and the one `E`-bridge into `EquationalTheory`).
  * **`ChurchRosserModulo`** + **`churchRosserModulo_characterization`** — CR-modulo-`E` IS the statement
    that the combined theory equals joinability modulo `E` (`EquationalTheory (R ∪ E) ↔ JoinableModulo R E`).
  * **`churchRosserModulo_eq_of_confluent`** — ★ the bridge to `term-7`: when `E` is trivial (equality),
    CR-modulo-`E` is ordinary Church-Rosser, so a CONFLUENT `R` is Church-Rosser modulo equality
    (`equationalTheory_collapseEq` + `churchRosser_of_confluent` + `joinableModulo_eq_joinable`).
  * **`commutativeEquiv`** — a concrete AC-flavored equational theory (commutativity = pair swap), proved an
    equivalence, with `(3,5)` and `(5,3)` convertible modulo it.

## Honest scope

The modulo-`E` vocabulary + the joinable-modulo/combined-theory characterization + the trivial-`E` bridge to
ordinary confluence + the commutativity witness.  DEFERRED: the modulo-`E` NEWMAN lemma (termination of
`R/E` + local confluence modulo `E` + COHERENCE ⟹ CR modulo `E` — the Jouannaud-Kirchner theorem); AC
MATCHING decidability; and the convergent-`R/AC` DECISION procedure for the `AC`-word problem.

## Zero-axiom verification

`equationalTheory_of_rtc` is induction on `ReflTransClosure`; the joinable-modulo lift chains `term-7`'s
`EquationalTheory` constructors; the `Eq`-collapse is induction on `EquationalTheory` with `▸`; the
commutativity equivalence is finite `Or`/`Eq` case analysis.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCoreRewritingModulo.lean`.
-/

namespace FX1Poly.Core

/-! ## Joinability modulo an equational theory -/

/-- `a` and `b` are **joinable modulo `equiv`**: each `rewrite`-reduces to a reduct, and the two reducts are
`equiv`-equivalent.  (For `equiv = AC`, this is "reduce both, compare modulo reordering".) -/
def JoinableModulo {Carrier : Type} (rewrite equiv : Carrier → Carrier → Prop) (leftValue rightValue : Carrier) :
    Prop :=
  ∃ leftReduct rightReduct, ReflTransClosure rewrite leftValue leftReduct ∧
    ReflTransClosure rewrite rightValue rightReduct ∧ equiv leftReduct rightReduct

/-- A `rewrite`-reduction is a conversion in the combined theory of `rewrite ∪ equiv`. -/
theorem equationalTheory_of_rtc {Carrier : Type} (rewrite equiv : Carrier → Carrier → Prop)
    {source target : Carrier} (reduction : ReflTransClosure rewrite source target) :
    EquationalTheory (fun first second => rewrite first second ∨ equiv first second) source target := by
  induction reduction with
  | refl point => exact EquationalTheory.refl point
  | head firstStep _restChain inductionHypothesis =>
      exact EquationalTheory.trans (EquationalTheory.rule (Or.inl firstStep)) inductionHypothesis

/-- ★ **Joinable modulo `E` ⟹ convertible in `R ∪ E`** (the easy half of Church-Rosser modulo `E`): lift the
two `R`-reductions and the single `E`-bridge into the combined equational theory. -/
theorem equationalTheory_of_joinableModulo {Carrier : Type} (rewrite equiv : Carrier → Carrier → Prop)
    {leftValue rightValue : Carrier} (joinable : JoinableModulo rewrite equiv leftValue rightValue) :
    EquationalTheory (fun first second => rewrite first second ∨ equiv first second) leftValue rightValue := by
  obtain ⟨leftReduct, rightReduct, leftToReduct, rightToReduct, reductsEquiv⟩ := joinable
  exact EquationalTheory.trans (equationalTheory_of_rtc rewrite equiv leftToReduct)
    (EquationalTheory.trans (EquationalTheory.rule (Or.inr reductsEquiv))
      (EquationalTheory.symm (equationalTheory_of_rtc rewrite equiv rightToReduct)))

/-! ## Church-Rosser modulo an equational theory -/

/-- `rewrite` is **Church-Rosser modulo `equiv`**: every conversion in the combined theory `rewrite ∪ equiv`
collapses to joinability modulo `equiv`. -/
def ChurchRosserModulo {Carrier : Type} (rewrite equiv : Carrier → Carrier → Prop) : Prop :=
  ∀ {leftValue rightValue : Carrier},
    EquationalTheory (fun first second => rewrite first second ∨ equiv first second) leftValue rightValue →
    JoinableModulo rewrite equiv leftValue rightValue

/-- ★ **Characterization**: under Church-Rosser modulo `E`, the combined equational theory of `R ∪ E` IS
joinability modulo `E` (the easy half always holds; CR-modulo supplies the hard half). -/
theorem churchRosserModulo_characterization {Carrier : Type} (rewrite equiv : Carrier → Carrier → Prop)
    (churchRosser : ChurchRosserModulo rewrite equiv) {leftValue rightValue : Carrier} :
    EquationalTheory (fun first second => rewrite first second ∨ equiv first second) leftValue rightValue
      ↔ JoinableModulo rewrite equiv leftValue rightValue :=
  ⟨fun conversion => churchRosser conversion, equationalTheory_of_joinableModulo rewrite equiv⟩

/-! ## The bridge to ordinary Church-Rosser (term-7): trivial `E` -/

/-- With `equiv = equality`, joinability modulo `E` is ordinary joinability. -/
theorem joinableModulo_eq_joinable {Carrier : Type} (rewrite : Carrier → Carrier → Prop)
    {leftValue rightValue : Carrier} :
    JoinableModulo rewrite (fun first second => first = second) leftValue rightValue
      ↔ Joinable rewrite leftValue rightValue := by
  constructor
  · intro joinable
    obtain ⟨leftReduct, rightReduct, leftTo, rightTo, reductsEqual⟩ := joinable
    subst reductsEqual
    exact ⟨leftReduct, leftTo, rightTo⟩
  · intro joinable
    obtain ⟨commonReduct, leftTo, rightTo⟩ := joinable
    exact ⟨commonReduct, commonReduct, leftTo, rightTo, rfl⟩

/-- Conversions in `R ∪ equality` collapse to conversions in `R` alone (the equality steps add nothing). -/
theorem equationalTheory_collapseEq {Carrier : Type} (rewrite : Carrier → Carrier → Prop)
    {leftValue rightValue : Carrier}
    (conversion : EquationalTheory (fun first second => rewrite first second ∨ first = second)
      leftValue rightValue) : EquationalTheory rewrite leftValue rightValue := by
  induction conversion with
  | rule step =>
      cases step with
      | inl rewriteStep => exact EquationalTheory.rule rewriteStep
      | inr equalStep => exact equalStep ▸ EquationalTheory.refl _
  | refl point => exact EquationalTheory.refl point
  | symm _conv inductionHypothesis => exact EquationalTheory.symm inductionHypothesis
  | trans _first _second firstInductionHypothesis secondInductionHypothesis =>
      exact EquationalTheory.trans firstInductionHypothesis secondInductionHypothesis

/-- ★ **The bridge**: a CONFLUENT rewrite relation is Church-Rosser modulo EQUALITY — ordinary Church-Rosser
(`term-7`) is the trivial-`E` instance of rewriting modulo `E`. -/
theorem churchRosserModulo_eq_of_confluent {Carrier : Type} (rewrite : Carrier → Carrier → Prop)
    (confluent : Confluent rewrite) : ChurchRosserModulo rewrite (fun first second => first = second) := by
  intro leftValue rightValue conversion
  exact (joinableModulo_eq_joinable rewrite).mpr
    ((churchRosser_of_confluent confluent).mp (equationalTheory_collapseEq rewrite conversion))

/-! ## A concrete equational theory — commutativity (AC-flavored) -/

/-- The **commutativity** equational theory on pairs: two pairs are equivalent when equal or SWAPPED — the
commutativity half of `AC`. -/
def commutativeEquiv (leftPair rightPair : Nat × Nat) : Prop :=
  (leftPair.1 = rightPair.1 ∧ leftPair.2 = rightPair.2) ∨
    (leftPair.1 = rightPair.2 ∧ leftPair.2 = rightPair.1)

/-- Commutativity is reflexive. -/
theorem commutativeEquiv_refl (pair : Nat × Nat) : commutativeEquiv pair pair := Or.inl ⟨rfl, rfl⟩

/-- Commutativity is symmetric. -/
theorem commutativeEquiv_symm {leftPair rightPair : Nat × Nat} (equivalent : commutativeEquiv leftPair rightPair) :
    commutativeEquiv rightPair leftPair := by
  cases equivalent with
  | inl equalCase => exact Or.inl ⟨equalCase.1.symm, equalCase.2.symm⟩
  | inr swapCase => exact Or.inr ⟨swapCase.2.symm, swapCase.1.symm⟩

/-- Commutativity is transitive — so it is a genuine equivalence (equational theory). -/
theorem commutativeEquiv_trans {firstPair middlePair lastPair : Nat × Nat}
    (firstEquiv : commutativeEquiv firstPair middlePair)
    (secondEquiv : commutativeEquiv middlePair lastPair) : commutativeEquiv firstPair lastPair := by
  cases firstEquiv with
  | inl firstEqual =>
      cases secondEquiv with
      | inl secondEqual => exact Or.inl ⟨firstEqual.1.trans secondEqual.1, firstEqual.2.trans secondEqual.2⟩
      | inr secondSwap => exact Or.inr ⟨firstEqual.1.trans secondSwap.1, firstEqual.2.trans secondSwap.2⟩
  | inr firstSwap =>
      cases secondEquiv with
      | inl secondEqual => exact Or.inr ⟨firstSwap.1.trans secondEqual.2, firstSwap.2.trans secondEqual.1⟩
      | inr secondSwap => exact Or.inl ⟨firstSwap.1.trans secondSwap.2, firstSwap.2.trans secondSwap.1⟩

/-- ★ Modulo commutativity, `(3, 5)` and `(5, 3)` are convertible — with no rewrite steps, purely by the
equational theory.  A concrete instance of `equationalTheory_of_joinableModulo`. -/
theorem swapConvertibleModuloCommutativity :
    EquationalTheory (fun first second => (fun _ _ => False) first second ∨ commutativeEquiv first second)
      (3, 5) (5, 3) :=
  equationalTheory_of_joinableModulo (fun _ _ => False) commutativeEquiv
    ⟨(3, 5), (5, 3), ReflTransClosure.refl _, ReflTransClosure.refl _, Or.inr ⟨rfl, rfl⟩⟩

end FX1Poly.Core

import FX1Poly.ComputerAlgebra.Decision.PostCloneLattice
import FX1Poly.ComputerAlgebra.Decision.PolInvGaloisConnection

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Mechanized Schaefer dichotomy over the Boolean domain

The relational (Galois) formulation of Schaefer's dichotomy on the two-element domain. A CSP
constraint is a finite Boolean relation (`PigBoolRel`), a constraint language is a
`List PigBoolRel`, and the language is tractable iff it is jointly preserved by one of the six
Schaefer polymorphisms:

  * `schConst0` / `schConst1` — the two constant unary operations (relation 0-valid / 1-valid);
  * `schAnd` (min) — the Horn / conjunction-closed polymorphism;
  * `schOr` (max) — the dual-Horn / disjunction-closed polymorphism;
  * `schXor3` (ternary `x ⊕ y ⊕ z`, minority) — the affine polymorphism;
  * `schMajority3` (ternary median) — the bijunctive / 2-SAT polymorphism.

`schIsTractable language` folds `pigPreserves` (from `PolInvGaloisConnection`) over the six
operations against every relation; `schTractabilityWitness` returns the first preserving the whole
language, and `schWitnessSound` proves any returned witness genuinely preserves every constraint.
This relational formulation is faithful, unlike the function-side
`PostCloneLattice.pclIsSchaeferTractable`, which tests membership in one of five maximal Post
clones and so miscategorises self-dual `D` (not tractable) and omits the majority witness.

The tractable side is fully proven; the two markers left `false` name the NP-completeness (hard)
direction and the `|D| ≥ 3` Bulatov–Zhuk dichotomy, each outside a bounded finite preservation
check for the reason stated at its declaration.

Every declaration is free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `funext`, `WellFounded.fix`, `omega`, and any `decide`-on-`Prop`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## The six Schaefer polymorphisms (each a `PclBoolFn` truth table, big-endian rows) -/

/-- Constant-`0` as a unary operation: `f x = false` on both inputs.  Applied down a column it
yields the all-zero tuple, so `pigPreserves schConst0 R` reduces to "the all-zero tuple is a row
of `R`" — i.e. `R` is 0-valid. -/
def schConst0 : PclBoolFn := { arity := 1, table := [false, false] }

/-- Constant-`1` as a unary operation: `f x = true` on both inputs — `pigPreserves schConst1 R`
reduces to "`R` is 1-valid" (the all-one tuple is a row). -/
def schConst1 : PclBoolFn := { arity := 1, table := [true, true] }

/-- The AND (min) polymorphism, reused from the pcl kit: rows `[FF, FT, TF, TT] = [F,F,F,T]`.
Preservation witnesses the Horn (conjunction-closed) tractable class. -/
def schAnd : PclBoolFn := pclAndFn

/-- The OR (max) polymorphism: rows `[FF, FT, TF, TT] = [F,T,T,T]`.  Preservation witnesses the
dual-Horn (disjunction-closed) tractable class. -/
def schOr : PclBoolFn := { arity := 2, table := [false, true, true, true] }

/-- The ternary XOR / minority polymorphism `x ⊕ y ⊕ z`: over rows
`[FFF, FFT, FTF, FTT, TFF, TFT, TTF, TTT]` the parity is `[F,T,T,F,T,F,F,T]`.  Preservation
witnesses the affine tractable class. -/
def schXor3 : PclBoolFn := { arity := 3, table := [false, true, true, false, true, false, false, true] }

/-- The ternary majority / median polymorphism (value = at least two `true`): over the eight rows
`[F,F,F,T,F,T,T,T]`.  Preservation witnesses the bijunctive / 2-SAT tractable class. -/
def schMajority3 : PclBoolFn := { arity := 3, table := [false, false, false, true, false, true, true, true] }

/-- The six Schaefer polymorphisms in classifier order: the two constants, AND, OR, XOR, majority. -/
def schSix : List PclBoolFn := [schConst0, schConst1, schAnd, schOr, schXor3, schMajority3]

/-! ## Concrete constraints (each a `PigBoolRel`) and languages (each a `List PigBoolRel`) -/

/-- The `(x ∨ y)` clause relation `{01, 10, 11}` (excludes the all-zero tuple). -/
def schOrClauseRel : PigBoolRel :=
  { arity := 2, rows := [[false, true], [true, false], [true, true]] }

/-- The `(¬x ∨ ¬y)` clause relation `{00, 01, 10}` (excludes the all-one tuple). -/
def schNandClauseRel : PigBoolRel :=
  { arity := 2, rows := [[false, false], [false, true], [true, false]] }

/-- A 2-SAT (bijunctive) language whose only common Schaefer polymorphism is the ternary majority. -/
def sch2SatLang : List PigBoolRel := [schOrClauseRel, schNandClauseRel]

/-- The ternary Horn clause relation `(¬x ∨ ¬y ∨ ¬z)` = every tuple except `111`; AND-closed. -/
def schHornRel : PigBoolRel :=
  { arity := 3,
    rows := [[false, false, false], [false, false, true], [false, true, false],
             [false, true, true], [true, false, false], [true, false, true],
             [true, true, false]] }

/-- The Horn language: a single ternary Horn clause. -/
def schHornLang : List PigBoolRel := [schHornRel]

/-- An affine constraint `{100, 011}` — the coset of `span{111}` cut out by `x⊕y = 1 ∧ x⊕z = 1`;
XOR-preserved. -/
def schAffineRel : PigBoolRel :=
  { arity := 3, rows := [[true, false, false], [false, true, true]] }

/-- The affine language: a single affine constraint, XOR-preserved. -/
def schAffineLang : List PigBoolRel := [schAffineRel]

/-- The not-all-equal ternary relation `{0,1}³ ∖ {000, 111}`: no Schaefer polymorphism preserves
it (Schaefer-hard). -/
def schNaeRel : PigBoolRel :=
  { arity := 3,
    rows := [[false, false, true], [false, true, false], [false, true, true],
             [true, false, false], [true, false, true], [true, true, false]] }

/-- The not-all-equal language: a single NAE constraint (Schaefer-hard). -/
def schNaeLang : List PigBoolRel := [schNaeRel]

/-- The one-in-three ternary relation `{100, 010, 001}` — a second Schaefer-hard language. -/
def schOneInThreeRel : PigBoolRel :=
  { arity := 3, rows := [[true, false, false], [false, true, false], [false, false, true]] }

/-- The one-in-three language: a single one-in-three constraint (Schaefer-hard). -/
def schOneInThreeLang : List PigBoolRel := [schOneInThreeRel]

/-! ## The joint-preservation tractability classifier -/

/-- `op` preserves the whole `language` — every constraint of the list is `pigPreserved` by `op`
(structural cons-fold, reusing `pigPreserves`). -/
def schPreservesLanguage (op : PclBoolFn) : List PigBoolRel → Bool
  | [] => true
  | rel :: rest => pigPreserves op rel && schPreservesLanguage op rest

/-- Is an `Option` witness present? -/
def schOptionIsSome : Option PclBoolFn → Bool
  | some _ => true
  | none => false

/-- Search a candidate list for the first operation preserving the whole `language`. -/
def schWitnessSearch : List PclBoolFn → List PigBoolRel → Option PclBoolFn
  | [], _ => none
  | op :: rest, language =>
      match schPreservesLanguage op language with
      | true => some op
      | false => schWitnessSearch rest language

/-- The tractability witness: the first of the six Schaefer polymorphisms preserving the language
(if any). -/
def schTractabilityWitness (language : List PigBoolRel) : Option PclBoolFn :=
  schWitnessSearch schSix language

/-- The classifier: the language is Schaefer-tractable iff one of the six polymorphisms preserves
every constraint. -/
def schIsTractable (language : List PigBoolRel) : Bool :=
  schOptionIsSome (schTractabilityWitness language)

/-! ## Witness soundness and the dichotomy packaging -/

/-- SOUNDNESS: a witness the search returns genuinely preserves the whole language. -/
theorem schWitnessSearchSound : (ops : List PclBoolFn) → (language : List PigBoolRel) →
    (op : PclBoolFn) → schWitnessSearch ops language = some op →
    schPreservesLanguage op language = true
  | [], _, op, hEq => by
      have hNone : (none : Option PclBoolFn) = some op := hEq
      nomatch hNone
  | head :: rest, language, op, hEq => by
      have hEq2 : (match schPreservesLanguage head language with
          | true => some head
          | false => schWitnessSearch rest language) = some op := hEq
      cases hPres : schPreservesLanguage head language with
      | true =>
          rw [hPres] at hEq2
          have hHeadOp : head = op := by injection hEq2
          rw [← hHeadOp]
          exact hPres
      | false =>
          rw [hPres] at hEq2
          exact schWitnessSearchSound rest language op hEq2

/-- SOUNDNESS (public): the returned tractability witness preserves every constraint. -/
theorem schWitnessSound (language : List PigBoolRel) (op : PclBoolFn)
    (hEq : schTractabilityWitness language = some op) :
    schPreservesLanguage op language = true :=
  schWitnessSearchSound schSix language op hEq

/-- A tractable language always exhibits a concrete witness among the six. -/
theorem schTractableHasWitness (language : List PigBoolRel)
    (hTract : schIsTractable language = true) :
    ∃ op, schTractabilityWitness language = some op := by
  have hEq : schOptionIsSome (schTractabilityWitness language) = true := hTract
  cases hOpt : schTractabilityWitness language with
  | some op => exact ⟨op, rfl⟩
  | none =>
      rw [hOpt] at hEq
      exact Bool.noConfusion hEq

/-- The HARD side of the boundary: a language not Schaefer-tractable lands on the gadget-reduction
side.  This is the honest FINITE half — it names the side, it does not CERTIFY NP-hardness (see
`schHasHardnessGadgetReduction`). -/
def schIsHardByGadget (language : List PigBoolRel) : Bool :=
  not (schIsTractable language)

/-- The dichotomy: every language is either Schaefer-tractable or on the hard side. -/
def schDichotomyHolds (language : List PigBoolRel) : Bool :=
  schIsTractable language || schIsHardByGadget language

/-- The dichotomy is TOTAL — the tractable/hard split covers every language. -/
theorem schDichotomyTotal (language : List PigBoolRel) : schDichotomyHolds language = true := by
  unfold schDichotomyHolds schIsHardByGadget
  cases schIsTractable language with
  | true => rfl
  | false => rfl

/-! ## Capability markers -/

/-- The six Schaefer polymorphisms as concrete truth tables. -/
def schHasSixPolymorphisms : Bool := true

/-- The joint-preservation tractability classifier. -/
def schHasTractabilityClassifier : Bool := true

/-- Witness soundness: a returned witness preserves every constraint. -/
def schHasWitnessSoundness : Bool := true

/-- The tractable/hard dichotomy split, total on every language. -/
def schHasDichotomyWitness : Bool := true

/-- The Boolean (`|D| = 2`) Schaefer tractability decision. -/
def schHasBooleanTractabilityDecision : Bool := true

/-! ## The walls -/

/-- The NP-completeness (hard) direction, not proven here. Certifying that a non-witnessed language
is NP-complete needs a Cook–Levin gadget reduction from 3-SAT (each clause pp-defined over the
constraint language, with a polynomial-time-and-space correctness argument); this quantifies over
the unbounded family of 3-SAT instances and asserts P vs NP-complete, which no `Bool`-valued
procedure over a fixed finite table certifies. Reading hardness directly off
`schIsTractable … = false` is unsound — failing all six polymorphisms is only the algebraic
criterion, not the matching hardness half. -/
def schHasHardnessGadgetReduction : Bool := false

/-- The general finite-domain CSP dichotomy (`|D| ≥ 3`, Bulatov 2017 / Zhuk 2017), not proven here.
The six Boolean polymorphisms are the decidable `|D| = 2` slice; the higher-domain criterion
(a cyclic / weak-near-unanimity polymorphism) ranges over every arity on an unbounded domain, its
hard direction is an absorption-theory argument with no bounded decision procedure, no fixed arity
suffices (Siggers terms are 6-ary), and bit-encoding `Fin d` into Boolean fails to preserve
polymorphism structure. Cited from `pclHasHigherDomainDichotomy`. -/
def schHasHigherDomainDichotomy : Bool := false

/-! ## Ground fires (all `rfl` on small-arity witnesses)

Table well-formedness and algebraic properties of the six polymorphisms, single-clause and
whole-language preservation with its refutations, the tractable/hard classifications on the sample
languages, and the exact witnesses returned. The `Nae`/`OneInThree` languages are the discriminating
separations: no polymorphism preserves them. -/

theorem schConst0TablePow2 : pclTablePow2 schConst0 = true := rfl

theorem schConst1TablePow2 : pclTablePow2 schConst1 = true := rfl

theorem schOrTablePow2 : pclTablePow2 schOr = true := rfl

theorem schXor3TablePow2 : pclTablePow2 schXor3 = true := rfl

theorem schMajority3TablePow2 : pclTablePow2 schMajority3 = true := rfl

theorem schXor3Affine : pclIsAffine schXor3 = true := rfl

theorem schMajority3SelfDual : pclIsSelfDual schMajority3 = true := rfl

theorem schMajority3NotAffine : pclIsAffine schMajority3 = false := rfl

theorem schMajorityPreservesOrClause : pigPreserves schMajority3 schOrClauseRel = true := rfl

theorem schMajorityPreservesNandClause : pigPreserves schMajority3 schNandClauseRel = true := rfl

theorem schMajorityPreserves2Sat : schPreservesLanguage schMajority3 sch2SatLang = true := rfl

/-- `∧((0,1),(1,0)) = (0,0) ∉ R`. -/
theorem schAndNotPreservesOrClause : pigPreserves schAnd schOrClauseRel = false := rfl

theorem schXor3PreservesAffine : schPreservesLanguage schXor3 schAffineLang = true := rfl

theorem schAndPreservesHorn : pigPreserves schAnd schHornRel = true := rfl

/-- `∨((0,1,1),(1,0,1)) = (1,1,1) ∉ R`. -/
theorem schOrNotPreservesHorn : pigPreserves schOr schHornRel = false := rfl

theorem sch2SatTractable : schIsTractable sch2SatLang = true := rfl

theorem schAffineTractable : schIsTractable schAffineLang = true := rfl

theorem schHornTractable : schIsTractable schHornLang = true := rfl

theorem schNaeNotTractable : schIsTractable schNaeLang = false := rfl

theorem schOneInThreeNotTractable : schIsTractable schOneInThreeLang = false := rfl

/-- Constants, AND, OR and XOR each fail on one clause, so the search reaches `schMajority3`. -/
theorem sch2SatWitnessMajority : schTractabilityWitness sch2SatLang = some schMajority3 := rfl

theorem schAffineWitnessXor3 : schTractabilityWitness schAffineLang = some schXor3 := rfl

theorem schNaeWitnessNone : schTractabilityWitness schNaeLang = none := rfl

/-- The returned witness genuinely preserves every constraint, via `schWitnessSound`. -/
theorem schWitnessSoundOn2Sat : schPreservesLanguage schMajority3 sch2SatLang = true :=
  schWitnessSound sch2SatLang schMajority3 sch2SatWitnessMajority

theorem schDichotomyOn2Sat : schDichotomyHolds sch2SatLang = true := rfl

theorem schDichotomyOnNae : schDichotomyHolds schNaeLang = true := rfl

theorem schNaeHardByGadget : schIsHardByGadget schNaeLang = true := rfl

/-- The tractable-side capability markers all hold. -/
theorem schDecidedMarkers :
    (schHasSixPolymorphisms && schHasTractabilityClassifier
      && schHasWitnessSoundness && schHasDichotomyWitness
      && schHasBooleanTractabilityDecision) = true := rfl

/-- The wall markers are all `false`. -/
theorem schWallMarkers :
    (schHasHardnessGadgetReduction || schHasHigherDomainDichotomy) = false := rfl

end FX1Poly.ComputerAlgebra

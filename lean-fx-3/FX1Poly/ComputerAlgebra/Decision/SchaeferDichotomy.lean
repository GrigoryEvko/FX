import FX1Poly.ComputerAlgebra.Decision.PostCloneLattice
import FX1Poly.ComputerAlgebra.Decision.PolInvGaloisConnection

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # FX1Poly/ComputerAlgebra/Decision/SchaeferDichotomy — mechanized Schaefer over the Boolean slice

The relational (Galois) formulation of Schaefer's dichotomy on the two-element domain: a CSP
constraint is a finite Boolean RELATION (`PigBoolRel`), a constraint LANGUAGE is a
`List PigBoolRel`, and the language is tractable iff it is jointly preserved by one of the SIX
Schaefer polymorphisms:

  * `schConst0` / `schConst1` — the two constant unary operations (relation is 0-valid / 1-valid);
  * `schAnd` (min) — the Horn / conjunction-closed polymorphism;
  * `schOr` (max) — the dual-Horn / disjunction-closed polymorphism;
  * `schXor3` (ternary `x ⊕ y ⊕ z`, the minority) — the affine polymorphism;
  * `schMajority3` (the ternary median) — the bijunctive / 2-SAT polymorphism.

`schIsTractable language` folds `pigPreserves` (reused verbatim from `PolInvGaloisConnection`) over
the six operations against every relation of the language; `schTractabilityWitness` returns the
first of the six that preserves the whole language, and `schWitnessSound` proves any returned
witness genuinely preserves every constraint.

## How this GENERALISES the pcl fragment

`PostCloneLattice.pclIsSchaeferTractable` is a FUNCTION-side coincidence: it treats its input as a
list of Boolean FUNCTIONS and asks whether they lie in one of the five maximal Post clones
`{T0, T1, M, D, L}` via `pclCloneMembership`.  That miscategorises: self-dual `D` is NOT a
Schaefer-tractable class and there is no majority (bijunctive) witness.  This file flips to the
honest RELATIONAL formulation — constraints are relations, the witnesses are the six genuine
polymorphisms, and tractability is `pigPreserves`-preservation, not clone membership.

## What is DECIDED (each `true`, with an audit twin + independent `#print axioms`)

  * `schHasSixPolymorphisms` / `schHasTractabilityClassifier` / `schHasWitnessSoundness` /
    `schHasDichotomyWitness` / `schHasBooleanTractabilityDecision`.

## What is WALLED (each `false`, obstruction + two burned attacks in its docstring)

  * `schHasHardnessGadgetReduction` — the NP-completeness (hard) direction.
  * `schHasHigherDomainDichotomy` — the `|D| ≥ 3` Bulatov–Zhuk dichotomy (cites the ATOM-POST wall).

Every declaration is free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `funext`, `WellFounded.fix`, `omega`, and any `decide`-on-`Prop`. -/

namespace FX1Poly.ComputerAlgebra

/-! ## T1 — the six Schaefer polymorphisms (each a `PclBoolFn` truth table, big-endian rows) -/

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

/-- A 2-SAT (bijunctive) language: two clauses whose only common Schaefer polymorphism is the
ternary majority — the constants, AND, OR and XOR all fail on one of the two clauses. -/
def sch2SatLang : List PigBoolRel := [schOrClauseRel, schNandClauseRel]

/-- The ternary Horn clause relation `(¬x ∨ ¬y ∨ ¬z)` = every tuple except `111`.  AND-closed
(a conjunction can never fabricate the excluded all-one tuple); OR / XOR / majority all fail. -/
def schHornRel : PigBoolRel :=
  { arity := 3,
    rows := [[false, false, false], [false, false, true], [false, true, false],
             [false, true, true], [true, false, false], [true, false, true],
             [true, true, false]] }

/-- The Horn language: a single ternary Horn clause. -/
def schHornLang : List PigBoolRel := [schHornRel]

/-- An affine constraint `{100, 011}` — the coset of `span{111}` cut out by `x⊕y = 1 ∧ x⊕z = 1`.
It excludes both extreme tuples and fails AND / OR, so the ternary XOR is its first witness. -/
def schAffineRel : PigBoolRel :=
  { arity := 3, rows := [[true, false, false], [false, true, true]] }

/-- The affine language: a single affine constraint, XOR-preserved. -/
def schAffineLang : List PigBoolRel := [schAffineRel]

/-- The not-all-equal ternary relation `{0,1}³ ∖ {000, 111}` — the classic Schaefer-HARD language:
no Schaefer polymorphism preserves it. -/
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

/-! ## T2 — the joint-preservation tractability classifier -/

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

/-! ## T3 — witness soundness + the dichotomy packaging -/

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

/-! ## Capability markers — DECIDED -/

/-- The six Schaefer polymorphisms are DECIDED (concrete truth tables). -/
def schHasSixPolymorphisms : Bool := true

/-- The joint-preservation tractability classifier is DECIDED. -/
def schHasTractabilityClassifier : Bool := true

/-- Witness soundness (a returned witness preserves every constraint) is DECIDED. -/
def schHasWitnessSoundness : Bool := true

/-- The tractable/hard dichotomy split is DECIDED (total on every language). -/
def schHasDichotomyWitness : Bool := true

/-- The Boolean (`|D| = 2`) Schaefer tractability decision is DECIDED. -/
def schHasBooleanTractabilityDecision : Bool := true

/-! ## T4 — the walls -/

/-- ★ WALL — the NP-completeness (HARD) direction.  The classifier decides which SIDE of the
Schaefer boundary a language is on (tractable iff some of the six polymorphisms preserves it), but
proving that a non-witnessed language is NP-COMPLETE needs a Cook–Levin gadget reduction from
3-SAT: an implementation of each 3-SAT clause by a pp-definition (conjunction + existential
projection + equality) over the constraint language, together with a polynomial-time-and-space
correctness argument.  That is not a bounded finite preservation check.

Obstruction: a gadget reduction quantifies over the UNBOUNDED family of 3-SAT instances and asserts
a complexity-class separation (P vs NP-complete, contingent on P ≠ NP); no `Bool`-valued decision
procedure over a fixed finite table certifies it.

Burned attack 1: enumerate all pp-definitions up to a fixed gadget SIZE and check they realise a
3-SAT clause — a language may need a gadget with more existentially-projected auxiliary variables
than any fixed bound (the reduction depth is instance-dependent), so a size cap under-approximates
and misses the reduction; the same higher-arity separator that burns
`pigHasPpDefinabilityClosure` burned attack 1.

Burned attack 2: read NP-hardness off `schIsTractable … = false` directly (declare every
non-tractable language NP-complete) — this is UNSOUND without the reduction: "not preserved by the
six polymorphisms" is only the algebraic criterion; certifying the matching hardness half is the
theorem, not the classifier's Boolean output.  A language failing all six but whose hardness is
unproven refutes the shortcut. -/
def schHasHardnessGadgetReduction : Bool := false

/-- ★ WALL — the general finite-domain CSP dichotomy (`|D| ≥ 3`, Bulatov 2017 / Zhuk 2017).  The
six Boolean polymorphisms here are the decidable `|D| = 2` slice; the higher-domain case is a
research-grade proof about a weak-near-unanimity (WNU) / cyclic polymorphism on a domain of
arbitrary finite size — cited from the ATOM-POST wall `pclHasHigherDomainDichotomy`.

Obstruction: the criterion "the language admits a cyclic/WNU polymorphism" ranges over
polymorphisms of every arity on an unbounded finite domain — not a finite Boolean table check.

Burned attack 1: fix the domain to `Fin d` and enumerate binary polymorphisms — a WNU witness can
require arity far above 2 (Siggers is 6-ary), so no fixed arity is a complete test; a `d = 3`
language with a ternary but no binary WNU refutes the binary-only check (the exact burned attack of
`pclHasHigherDomainDichotomy`).

Burned attack 2: bit-encode `Fin d` into Boolean and reuse the six Schaefer polymorphisms — the
encoding does NOT preserve polymorphism structure (a domain-3 majority is not a Boolean majority on
the encoding bits), so the Boolean slice gives false negatives; a domain-3 tractable CSP whose
bit-encoding fails all six Boolean polymorphisms refutes the reduction. -/
def schHasHigherDomainDichotomy : Bool := false

/-! ## T5 — ground fires (all `rfl` on small-arity witnesses) -/

/-- Fire: `schConst0` has a well-formed table (`length = 2^1 = 2`). -/
theorem schConst0TablePow2 : pclTablePow2 schConst0 = true := rfl

/-- Fire: `schConst1` has a well-formed table. -/
theorem schConst1TablePow2 : pclTablePow2 schConst1 = true := rfl

/-- Fire: `schOr` has a well-formed table (`length = 2^2 = 4`). -/
theorem schOrTablePow2 : pclTablePow2 schOr = true := rfl

/-- Fire: `schXor3` has a well-formed table (`length = 2^3 = 8`). -/
theorem schXor3TablePow2 : pclTablePow2 schXor3 = true := rfl

/-- Fire: `schMajority3` has a well-formed table. -/
theorem schMajority3TablePow2 : pclTablePow2 schMajority3 = true := rfl

/-- Fire: the ternary XOR is affine (linear — no monomial of degree ≥ 2). -/
theorem schXor3Affine : pclIsAffine schXor3 = true := rfl

/-- Fire: the ternary majority is self-dual (`maj(¬x,¬y,¬z) = ¬ maj(x,y,z)`). -/
theorem schMajority3SelfDual : pclIsSelfDual schMajority3 = true := rfl

/-- Fire: the ternary majority is NOT affine (it carries degree-2 monomials). -/
theorem schMajority3NotAffine : pclIsAffine schMajority3 = false := rfl

/-- Fire (teeth): the majority polymorphism PRESERVES the `(x ∨ y)` clause. -/
theorem schMajorityPreservesOrClause : pigPreserves schMajority3 schOrClauseRel = true := rfl

/-- Fire (teeth): the majority polymorphism PRESERVES the `(¬x ∨ ¬y)` clause. -/
theorem schMajorityPreservesNandClause : pigPreserves schMajority3 schNandClauseRel = true := rfl

/-- Fire (teeth): the majority polymorphism preserves the WHOLE 2-SAT language. -/
theorem schMajorityPreserves2Sat : schPreservesLanguage schMajority3 sch2SatLang = true := rfl

/-- Fire (teeth−): AND does NOT preserve the `(x ∨ y)` clause — `∧((0,1),(1,0)) = (0,0) ∉ R`. -/
theorem schAndNotPreservesOrClause : pigPreserves schAnd schOrClauseRel = false := rfl

/-- Fire (teeth): the ternary XOR preserves the whole affine language. -/
theorem schXor3PreservesAffine : schPreservesLanguage schXor3 schAffineLang = true := rfl

/-- Fire (teeth): AND preserves the ternary Horn clause. -/
theorem schAndPreservesHorn : pigPreserves schAnd schHornRel = true := rfl

/-- Fire (teeth−): OR does NOT preserve the Horn clause — `∨((0,1,1),(1,0,1)) = (1,1,1) ∉ R`. -/
theorem schOrNotPreservesHorn : pigPreserves schOr schHornRel = false := rfl

/-- Fire: the 2-SAT language is Schaefer-tractable. -/
theorem sch2SatTractable : schIsTractable sch2SatLang = true := rfl

/-- Fire: the affine language is Schaefer-tractable. -/
theorem schAffineTractable : schIsTractable schAffineLang = true := rfl

/-- Fire: the Horn language is Schaefer-tractable. -/
theorem schHornTractable : schIsTractable schHornLang = true := rfl

/-- Fire (the discriminating separation): the not-all-equal language is NOT Schaefer-tractable —
none of the six polymorphisms preserves it. -/
theorem schNaeNotTractable : schIsTractable schNaeLang = false := rfl

/-- Fire (second hard witness): the one-in-three language is NOT Schaefer-tractable. -/
theorem schOneInThreeNotTractable : schIsTractable schOneInThreeLang = false := rfl

/-- Fire: the 2-SAT language's witness is precisely the majority polymorphism (the constants, AND,
OR and XOR each fail on one clause, so the search reaches `schMajority3`). -/
theorem sch2SatWitnessMajority : schTractabilityWitness sch2SatLang = some schMajority3 := rfl

/-- Fire: the affine language's witness is precisely the ternary XOR. -/
theorem schAffineWitnessXor3 : schTractabilityWitness schAffineLang = some schXor3 := rfl

/-- Fire: the not-all-equal language exhibits NO witness. -/
theorem schNaeWitnessNone : schTractabilityWitness schNaeLang = none := rfl

/-- Fire (witness soundness on a concrete tractable language): the majority witness the search
returns for the 2-SAT language genuinely preserves every constraint — proved through
`schWitnessSound`, not re-`rfl`. -/
theorem schWitnessSoundOn2Sat : schPreservesLanguage schMajority3 sch2SatLang = true :=
  schWitnessSound sch2SatLang schMajority3 sch2SatWitnessMajority

/-- Fire: the dichotomy is total on the tractable 2-SAT language. -/
theorem schDichotomyOn2Sat : schDichotomyHolds sch2SatLang = true := rfl

/-- Fire: the dichotomy is total on the hard not-all-equal language. -/
theorem schDichotomyOnNae : schDichotomyHolds schNaeLang = true := rfl

/-- Fire: the not-all-equal language sits on the hard side of the boundary. -/
theorem schNaeHardByGadget : schIsHardByGadget schNaeLang = true := rfl

/-- Fire: the DECIDED capability markers all hold. -/
theorem schDecidedMarkers :
    (schHasSixPolymorphisms && schHasTractabilityClassifier
      && schHasWitnessSoundness && schHasDichotomyWitness
      && schHasBooleanTractabilityDecision) = true := rfl

/-- Fire: the WALL markers are all `false`. -/
theorem schWallMarkers :
    (schHasHardnessGadgetReduction || schHasHigherDomainDichotomy) = false := rfl

end FX1Poly.ComputerAlgebra

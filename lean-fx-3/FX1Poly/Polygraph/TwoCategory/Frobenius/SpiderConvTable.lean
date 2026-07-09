import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderAfterPrefix

/-! # WP-FROB r5 (FROB-5) — the DECIDED seed table + the GATE-FREE contextual congruence `SpiderConvTable`

The r4 prefix bridge (`SpiderAfterPrefix.lean`) ships `SpiderConvSyntactic`, whose single non-trivial generator
`relationAfterPrefix` still carries a SEMANTIC GATE: a `seedViewAgrees` Prop field quantifying over the boundary
`matchingSameComponent` view of the concrete seed states.  Every use of a spider relation-after-a-prefix has to
re-supply that view agreement.  This file REMOVES the gate for the thirteen presented rows: each row's boundary-view
fact is a CLOSED, fixed-width decidable statement (`frobXSeedView_ordered`, by `decide`), so it is decided ONCE and
BAKED into a per-row constructor of an additive congruence `SpiderConvTable`.  The remaining constructor fields are
DATA / BOOKKEEPING ONLY — the prefix word, its firing discipline (`BrauerWordInRange`), and a boundary-preservation
length equation — never a view/state quantifier.  The relation is therefore GATE-FREE: to whisker a presented row
after any boundary-preserving prefix the agent supplies only the prefix and its bookkeeping.

## The decided table (piece 1)

`frobXSeedView_ordered` for each of the thirteen rows states, at the row's own boundary `frobX.boundaryCount` and
over the fixed row boundary port indices, that the lhs-processed and rhs-processed `brauerSeed` runs agree on
`matchingSameComponent` — a CLOSED decidable statement (the widths are fixed per row; the quantifiers range over the
finite boundary indices).  Each is proved by RAW `decide` (measured sub-second even for the depth-3 Yang-Baxter row,
36 pairs).  No staging / per-row helper decomposition is needed here: a `seedViewAgrees` fact reads
`matchingSameComponent` at one index pair = two `unionFindRootOf` scans, so even the heaviest row is cheap (contrast
`extractSpiderDiagram`, whose O(total^2) union-find queries over the un-shared fold forced the r1 staging).

## Additive, not a re-index

`SpiderConvTable` is a NEW inductive; the r4 `SpiderConvSyntactic` (and its embedding / sentinels) are untouched.
Each per-row constructor embeds into `SpiderConvSyntactic.relationAfterPrefix` by feeding the row's decided
`frobXSeedView_ordered` + the shipped parallel witness `frobX_parallel` (as `seedLengthEq`) + the fixed firing
discipline; so `spiderConvTable_toSpiderConvSyntactic` is one `relationAfterPrefix` application per row, and partition
soundness composes straight through `spiderConvSyntactic_partitionSound`.

## Literature anchor

The boundary-preserving restriction is exactly the boundary-complement condition of Bonchi-Gadducci-Kissinger-
Sobocinski-Zanasi (*String Diagram Rewrite Theory II*, Thm 35): a standalone rule fires soundly in a two-sided
context iff the context is a boundary complement, unique by their Prop 31.  Our `boundaryPreserved` field is that
boundary-preservation witness at fixed per-row widths, which is why each row discharges by `decide` and the embedding
is trivial (the table PROVES the boundary hypothesis the syntactic relation assumes).  The engine is `Cospan(FinSet)`
= special-commutative-Frobenius (Lack, *Composing PROPs*), so every pushout complement is already a valid rewrite.

Raw Lean 4 + Init; structural, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The DECIDED seed-view table — thirteen closed fixed-width facts (guard-after-binder ordered form)

Each fact is stated in the `Nat.decidableBallLT`-friendly ORDERED shape (the range guard immediately after each
binder), matching the reassociation the embedding performs into the `seedViewAgrees` field of
`SpiderConvSyntactic.relationAfterPrefix`.  All by RAW `decide`. -/

/-- Associativity row `μ(μ⊗1) = μ(1⊗μ)` — seed boundary view agrees (boundary `3`, depth-2). -/
theorem frobAssocSeedView_ordered : ∀ firstIndex,
    firstIndex < frobAssoc.boundaryCount
        + (processBrauer (brauerSeed frobAssoc.boundaryCount) frobAssoc.lhs).openWires.length →
    ∀ secondIndex,
    secondIndex < frobAssoc.boundaryCount
        + (processBrauer (brauerSeed frobAssoc.boundaryCount) frobAssoc.lhs).openWires.length →
    matchingSameComponent frobAssoc.boundaryCount
        (processBrauer (brauerSeed frobAssoc.boundaryCount) frobAssoc.lhs) firstIndex secondIndex
      = matchingSameComponent frobAssoc.boundaryCount
        (processBrauer (brauerSeed frobAssoc.boundaryCount) frobAssoc.rhs) firstIndex secondIndex := by decide

/-- Left unit row `μ(η⊗1) = 1` — seed boundary view agrees (boundary `1`). -/
theorem frobUnitLeftSeedView_ordered : ∀ firstIndex,
    firstIndex < frobUnitLeft.boundaryCount
        + (processBrauer (brauerSeed frobUnitLeft.boundaryCount) frobUnitLeft.lhs).openWires.length →
    ∀ secondIndex,
    secondIndex < frobUnitLeft.boundaryCount
        + (processBrauer (brauerSeed frobUnitLeft.boundaryCount) frobUnitLeft.lhs).openWires.length →
    matchingSameComponent frobUnitLeft.boundaryCount
        (processBrauer (brauerSeed frobUnitLeft.boundaryCount) frobUnitLeft.lhs) firstIndex secondIndex
      = matchingSameComponent frobUnitLeft.boundaryCount
        (processBrauer (brauerSeed frobUnitLeft.boundaryCount) frobUnitLeft.rhs) firstIndex secondIndex := by decide

/-- Right unit row `μ(1⊗η) = 1` — seed boundary view agrees (boundary `1`). -/
theorem frobUnitRightSeedView_ordered : ∀ firstIndex,
    firstIndex < frobUnitRight.boundaryCount
        + (processBrauer (brauerSeed frobUnitRight.boundaryCount) frobUnitRight.lhs).openWires.length →
    ∀ secondIndex,
    secondIndex < frobUnitRight.boundaryCount
        + (processBrauer (brauerSeed frobUnitRight.boundaryCount) frobUnitRight.lhs).openWires.length →
    matchingSameComponent frobUnitRight.boundaryCount
        (processBrauer (brauerSeed frobUnitRight.boundaryCount) frobUnitRight.lhs) firstIndex secondIndex
      = matchingSameComponent frobUnitRight.boundaryCount
        (processBrauer (brauerSeed frobUnitRight.boundaryCount) frobUnitRight.rhs) firstIndex secondIndex := by decide

/-- Coassociativity row `(δ⊗1)δ = (1⊗δ)δ` — seed boundary view agrees (boundary `1`, depth-2). -/
theorem frobCoassocSeedView_ordered : ∀ firstIndex,
    firstIndex < frobCoassoc.boundaryCount
        + (processBrauer (brauerSeed frobCoassoc.boundaryCount) frobCoassoc.lhs).openWires.length →
    ∀ secondIndex,
    secondIndex < frobCoassoc.boundaryCount
        + (processBrauer (brauerSeed frobCoassoc.boundaryCount) frobCoassoc.lhs).openWires.length →
    matchingSameComponent frobCoassoc.boundaryCount
        (processBrauer (brauerSeed frobCoassoc.boundaryCount) frobCoassoc.lhs) firstIndex secondIndex
      = matchingSameComponent frobCoassoc.boundaryCount
        (processBrauer (brauerSeed frobCoassoc.boundaryCount) frobCoassoc.rhs) firstIndex secondIndex := by decide

/-- Left counit row `(ε⊗1)δ = 1` — seed boundary view agrees (boundary `1`). -/
theorem frobCounitLeftSeedView_ordered : ∀ firstIndex,
    firstIndex < frobCounitLeft.boundaryCount
        + (processBrauer (brauerSeed frobCounitLeft.boundaryCount) frobCounitLeft.lhs).openWires.length →
    ∀ secondIndex,
    secondIndex < frobCounitLeft.boundaryCount
        + (processBrauer (brauerSeed frobCounitLeft.boundaryCount) frobCounitLeft.lhs).openWires.length →
    matchingSameComponent frobCounitLeft.boundaryCount
        (processBrauer (brauerSeed frobCounitLeft.boundaryCount) frobCounitLeft.lhs) firstIndex secondIndex
      = matchingSameComponent frobCounitLeft.boundaryCount
        (processBrauer (brauerSeed frobCounitLeft.boundaryCount) frobCounitLeft.rhs) firstIndex secondIndex := by decide

/-- Right counit row `(1⊗ε)δ = 1` — seed boundary view agrees (boundary `1`). -/
theorem frobCounitRightSeedView_ordered : ∀ firstIndex,
    firstIndex < frobCounitRight.boundaryCount
        + (processBrauer (brauerSeed frobCounitRight.boundaryCount) frobCounitRight.lhs).openWires.length →
    ∀ secondIndex,
    secondIndex < frobCounitRight.boundaryCount
        + (processBrauer (brauerSeed frobCounitRight.boundaryCount) frobCounitRight.lhs).openWires.length →
    matchingSameComponent frobCounitRight.boundaryCount
        (processBrauer (brauerSeed frobCounitRight.boundaryCount) frobCounitRight.lhs) firstIndex secondIndex
      = matchingSameComponent frobCounitRight.boundaryCount
        (processBrauer (brauerSeed frobCounitRight.boundaryCount) frobCounitRight.rhs) firstIndex secondIndex := by decide

/-- Frobenius law row `(μ⊗1)(1⊗δ) = δμ` — seed boundary view agrees (boundary `2`, depth-2). -/
theorem frobLeftSeedView_ordered : ∀ firstIndex,
    firstIndex < frobLeft.boundaryCount
        + (processBrauer (brauerSeed frobLeft.boundaryCount) frobLeft.lhs).openWires.length →
    ∀ secondIndex,
    secondIndex < frobLeft.boundaryCount
        + (processBrauer (brauerSeed frobLeft.boundaryCount) frobLeft.lhs).openWires.length →
    matchingSameComponent frobLeft.boundaryCount
        (processBrauer (brauerSeed frobLeft.boundaryCount) frobLeft.lhs) firstIndex secondIndex
      = matchingSameComponent frobLeft.boundaryCount
        (processBrauer (brauerSeed frobLeft.boundaryCount) frobLeft.rhs) firstIndex secondIndex := by decide

/-- Frobenius law row, other orientation `(1⊗μ)(δ⊗1) = δμ` — seed boundary view agrees (boundary `2`, depth-2). -/
theorem frobRightSeedView_ordered : ∀ firstIndex,
    firstIndex < frobRight.boundaryCount
        + (processBrauer (brauerSeed frobRight.boundaryCount) frobRight.lhs).openWires.length →
    ∀ secondIndex,
    secondIndex < frobRight.boundaryCount
        + (processBrauer (brauerSeed frobRight.boundaryCount) frobRight.lhs).openWires.length →
    matchingSameComponent frobRight.boundaryCount
        (processBrauer (brauerSeed frobRight.boundaryCount) frobRight.lhs) firstIndex secondIndex
      = matchingSameComponent frobRight.boundaryCount
        (processBrauer (brauerSeed frobRight.boundaryCount) frobRight.rhs) firstIndex secondIndex := by decide

/-- Commutativity of `μ` row `μσ = μ` — seed boundary view agrees (boundary `2`). -/
theorem frobCommMultSeedView_ordered : ∀ firstIndex,
    firstIndex < frobCommMult.boundaryCount
        + (processBrauer (brauerSeed frobCommMult.boundaryCount) frobCommMult.lhs).openWires.length →
    ∀ secondIndex,
    secondIndex < frobCommMult.boundaryCount
        + (processBrauer (brauerSeed frobCommMult.boundaryCount) frobCommMult.lhs).openWires.length →
    matchingSameComponent frobCommMult.boundaryCount
        (processBrauer (brauerSeed frobCommMult.boundaryCount) frobCommMult.lhs) firstIndex secondIndex
      = matchingSameComponent frobCommMult.boundaryCount
        (processBrauer (brauerSeed frobCommMult.boundaryCount) frobCommMult.rhs) firstIndex secondIndex := by decide

/-- Cocommutativity of `δ` row `σδ = δ` — seed boundary view agrees (boundary `1`). -/
theorem frobCommComultSeedView_ordered : ∀ firstIndex,
    firstIndex < frobCommComult.boundaryCount
        + (processBrauer (brauerSeed frobCommComult.boundaryCount) frobCommComult.lhs).openWires.length →
    ∀ secondIndex,
    secondIndex < frobCommComult.boundaryCount
        + (processBrauer (brauerSeed frobCommComult.boundaryCount) frobCommComult.lhs).openWires.length →
    matchingSameComponent frobCommComult.boundaryCount
        (processBrauer (brauerSeed frobCommComult.boundaryCount) frobCommComult.lhs) firstIndex secondIndex
      = matchingSameComponent frobCommComult.boundaryCount
        (processBrauer (brauerSeed frobCommComult.boundaryCount) frobCommComult.rhs) firstIndex secondIndex := by decide

/-- Symmetry involutivity row `σσ = 1⊗1` — seed boundary view agrees (boundary `2`). -/
theorem frobCrossingInvolutionSeedView_ordered : ∀ firstIndex,
    firstIndex < frobCrossingInvolution.boundaryCount
        + (processBrauer (brauerSeed frobCrossingInvolution.boundaryCount) frobCrossingInvolution.lhs).openWires.length →
    ∀ secondIndex,
    secondIndex < frobCrossingInvolution.boundaryCount
        + (processBrauer (brauerSeed frobCrossingInvolution.boundaryCount) frobCrossingInvolution.lhs).openWires.length →
    matchingSameComponent frobCrossingInvolution.boundaryCount
        (processBrauer (brauerSeed frobCrossingInvolution.boundaryCount) frobCrossingInvolution.lhs) firstIndex secondIndex
      = matchingSameComponent frobCrossingInvolution.boundaryCount
        (processBrauer (brauerSeed frobCrossingInvolution.boundaryCount) frobCrossingInvolution.rhs) firstIndex secondIndex := by decide

/-- Yang-Baxter row (R3, three strands) — seed boundary view agrees (boundary `3`, depth-3, 36 pairs). -/
theorem frobYangBaxterSeedView_ordered : ∀ firstIndex,
    firstIndex < frobYangBaxter.boundaryCount
        + (processBrauer (brauerSeed frobYangBaxter.boundaryCount) frobYangBaxter.lhs).openWires.length →
    ∀ secondIndex,
    secondIndex < frobYangBaxter.boundaryCount
        + (processBrauer (brauerSeed frobYangBaxter.boundaryCount) frobYangBaxter.lhs).openWires.length →
    matchingSameComponent frobYangBaxter.boundaryCount
        (processBrauer (brauerSeed frobYangBaxter.boundaryCount) frobYangBaxter.lhs) firstIndex secondIndex
      = matchingSameComponent frobYangBaxter.boundaryCount
        (processBrauer (brauerSeed frobYangBaxter.boundaryCount) frobYangBaxter.rhs) firstIndex secondIndex := by decide

/-- ★ The special law row `μδ = 1` — seed boundary view agrees (boundary `1`).  The r1 sentinel; its two seed runs
carry UNEQUAL loop counts, so only the loops-free boundary view (not the full Cospan diagram) transports. -/
theorem frobSpecialSeedView_ordered : ∀ firstIndex,
    firstIndex < frobSpecial.boundaryCount
        + (processBrauer (brauerSeed frobSpecial.boundaryCount) frobSpecial.lhs).openWires.length →
    ∀ secondIndex,
    secondIndex < frobSpecial.boundaryCount
        + (processBrauer (brauerSeed frobSpecial.boundaryCount) frobSpecial.lhs).openWires.length →
    matchingSameComponent frobSpecial.boundaryCount
        (processBrauer (brauerSeed frobSpecial.boundaryCount) frobSpecial.lhs) firstIndex secondIndex
      = matchingSameComponent frobSpecial.boundaryCount
        (processBrauer (brauerSeed frobSpecial.boundaryCount) frobSpecial.rhs) firstIndex secondIndex := by decide

/-! ## Per-word firing-discipline witnesses (fixed, private plumbing)

`BrauerWordInRange` is an inductive discipline (not auto-decidable), so each distinct row word's in-range proof is a
fixed cons/nil term with `rfl` window fits + `decide` tag-well-formedness — exactly the r4 pattern.  Empty-word sides
use `BrauerWordInRange.nil _` inline in the embedding. -/

private theorem inRange_multMult : BrauerWordInRange 3 [multAt 0, multAt 0] :=
  BrauerWordInRange.cons (multAt 0) 1 rfl (by decide)
    (BrauerWordInRange.cons (multAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 1))

private theorem inRange_mult1Mult : BrauerWordInRange 3 [multAt 1, multAt 0] :=
  BrauerWordInRange.cons (multAt 1) 0 rfl (by decide)
    (BrauerWordInRange.cons (multAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 1))

private theorem inRange_unit0Mult : BrauerWordInRange 1 [unitAt 0, multAt 0] :=
  BrauerWordInRange.cons (unitAt 0) 1 rfl (by decide)
    (BrauerWordInRange.cons (multAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 1))

private theorem inRange_unit1Mult : BrauerWordInRange 1 [unitAt 1, multAt 0] :=
  BrauerWordInRange.cons (unitAt 1) 0 rfl (by decide)
    (BrauerWordInRange.cons (multAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 1))

private theorem inRange_comultComult : BrauerWordInRange 1 [comultAt 0, comultAt 0] :=
  BrauerWordInRange.cons (comultAt 0) 0 rfl (by decide)
    (BrauerWordInRange.cons (comultAt 0) 1 rfl (by decide) (BrauerWordInRange.nil 3))

private theorem inRange_comultComult1 : BrauerWordInRange 1 [comultAt 0, comultAt 1] :=
  BrauerWordInRange.cons (comultAt 0) 0 rfl (by decide)
    (BrauerWordInRange.cons (comultAt 1) 0 rfl (by decide) (BrauerWordInRange.nil 3))

private theorem inRange_comultCounit0 : BrauerWordInRange 1 [comultAt 0, counitAt 0] :=
  BrauerWordInRange.cons (comultAt 0) 0 rfl (by decide)
    (BrauerWordInRange.cons (counitAt 0) 1 rfl (by decide) (BrauerWordInRange.nil 1))

private theorem inRange_comultCounit1 : BrauerWordInRange 1 [comultAt 0, counitAt 1] :=
  BrauerWordInRange.cons (comultAt 0) 0 rfl (by decide)
    (BrauerWordInRange.cons (counitAt 1) 0 rfl (by decide) (BrauerWordInRange.nil 1))

private theorem inRange_comult1Mult : BrauerWordInRange 2 [comultAt 1, multAt 0] :=
  BrauerWordInRange.cons (comultAt 1) 0 rfl (by decide)
    (BrauerWordInRange.cons (multAt 0) 1 rfl (by decide) (BrauerWordInRange.nil 2))

private theorem inRange_multComult : BrauerWordInRange 2 [multAt 0, comultAt 0] :=
  BrauerWordInRange.cons (multAt 0) 0 rfl (by decide)
    (BrauerWordInRange.cons (comultAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 2))

private theorem inRange_comultMult1 : BrauerWordInRange 2 [comultAt 0, multAt 1] :=
  BrauerWordInRange.cons (comultAt 0) 1 rfl (by decide)
    (BrauerWordInRange.cons (multAt 1) 0 rfl (by decide) (BrauerWordInRange.nil 2))

private theorem inRange_crossMult : BrauerWordInRange 2 [crossingAt 0, multAt 0] :=
  BrauerWordInRange.cons (crossingAt 0) 0 rfl (by decide)
    (BrauerWordInRange.cons (multAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 1))

private theorem inRange_multSingle : BrauerWordInRange 2 [multAt 0] :=
  BrauerWordInRange.cons (multAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 1)

private theorem inRange_comultCross : BrauerWordInRange 1 [comultAt 0, crossingAt 0] :=
  BrauerWordInRange.cons (comultAt 0) 0 rfl (by decide)
    (BrauerWordInRange.cons (crossingAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 2))

private theorem inRange_comultSingle : BrauerWordInRange 1 [comultAt 0] :=
  BrauerWordInRange.cons (comultAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 2)

private theorem inRange_crossCross : BrauerWordInRange 2 [crossingAt 0, crossingAt 0] :=
  BrauerWordInRange.cons (crossingAt 0) 0 rfl (by decide)
    (BrauerWordInRange.cons (crossingAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 2))

private theorem inRange_ybLhs : BrauerWordInRange 3 [crossingAt 0, crossingAt 1, crossingAt 0] :=
  BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide)
    (BrauerWordInRange.cons (crossingAt 1) 0 rfl (by decide)
      (BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide) (BrauerWordInRange.nil 3)))

private theorem inRange_ybRhs : BrauerWordInRange 3 [crossingAt 1, crossingAt 0, crossingAt 1] :=
  BrauerWordInRange.cons (crossingAt 1) 0 rfl (by decide)
    (BrauerWordInRange.cons (crossingAt 0) 1 rfl (by decide)
      (BrauerWordInRange.cons (crossingAt 1) 0 rfl (by decide) (BrauerWordInRange.nil 3)))

private theorem inRange_comultMult_at1 : BrauerWordInRange 1 [comultAt 0, multAt 0] :=
  BrauerWordInRange.cons (comultAt 0) 0 rfl (by decide)
    (BrauerWordInRange.cons (multAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 1))

/-! ## The GATE-FREE contextual congruence (piece 1)

`SpiderConvTable n a b` — the additive congruence generated by the equivalence closure together with the thirteen
presented rows whiskered after a boundary-preserving prefix.  Every per-row constructor takes ONLY the prefix word,
its firing discipline (`prefixInRange`), and a boundary-preservation length equation (`boundaryPreserved`) — NO field
quantifies over the boundary view or the concrete post-prefix state (contrast `SpiderConvSyntactic.relationAfterPrefix`,
which still carries a `seedViewAgrees` view quantifier).  The row's decided seed view is supplied INTERNALLY by the
embedding from the table `frobXSeedView_ordered`. -/
inductive SpiderConvTable : Nat → List BrauerAtom → List BrauerAtom → Prop
  /-- Reflexivity. -/
  | refl (bottomCount : Nat) (word : List BrauerAtom) : SpiderConvTable bottomCount word word
  /-- Symmetry. -/
  | symm {bottomCount : Nat} {leftWord rightWord : List BrauerAtom} :
      SpiderConvTable bottomCount leftWord rightWord → SpiderConvTable bottomCount rightWord leftWord
  /-- Transitivity. -/
  | trans {bottomCount : Nat} {leftWord midWord rightWord : List BrauerAtom} :
      SpiderConvTable bottomCount leftWord midWord → SpiderConvTable bottomCount midWord rightWord →
      SpiderConvTable bottomCount leftWord rightWord
  /-- Associativity `μ(μ⊗1) = μ(1⊗μ)` after a boundary-preserving prefix. -/
  | rowAssoc (prefixAtoms : List BrauerAtom)
      (prefixInRange : BrauerWordInRange frobAssoc.boundaryCount prefixAtoms)
      (boundaryPreserved :
        (processBrauer (brauerSeed frobAssoc.boundaryCount) prefixAtoms).openWires.length = frobAssoc.boundaryCount) :
      SpiderConvTable frobAssoc.boundaryCount (prefixAtoms ++ frobAssoc.lhs) (prefixAtoms ++ frobAssoc.rhs)
  /-- Left unit `μ(η⊗1) = 1` after a boundary-preserving prefix. -/
  | rowUnitLeft (prefixAtoms : List BrauerAtom)
      (prefixInRange : BrauerWordInRange frobUnitLeft.boundaryCount prefixAtoms)
      (boundaryPreserved :
        (processBrauer (brauerSeed frobUnitLeft.boundaryCount) prefixAtoms).openWires.length = frobUnitLeft.boundaryCount) :
      SpiderConvTable frobUnitLeft.boundaryCount (prefixAtoms ++ frobUnitLeft.lhs) (prefixAtoms ++ frobUnitLeft.rhs)
  /-- Right unit `μ(1⊗η) = 1` after a boundary-preserving prefix. -/
  | rowUnitRight (prefixAtoms : List BrauerAtom)
      (prefixInRange : BrauerWordInRange frobUnitRight.boundaryCount prefixAtoms)
      (boundaryPreserved :
        (processBrauer (brauerSeed frobUnitRight.boundaryCount) prefixAtoms).openWires.length = frobUnitRight.boundaryCount) :
      SpiderConvTable frobUnitRight.boundaryCount (prefixAtoms ++ frobUnitRight.lhs) (prefixAtoms ++ frobUnitRight.rhs)
  /-- Coassociativity `(δ⊗1)δ = (1⊗δ)δ` after a boundary-preserving prefix. -/
  | rowCoassoc (prefixAtoms : List BrauerAtom)
      (prefixInRange : BrauerWordInRange frobCoassoc.boundaryCount prefixAtoms)
      (boundaryPreserved :
        (processBrauer (brauerSeed frobCoassoc.boundaryCount) prefixAtoms).openWires.length = frobCoassoc.boundaryCount) :
      SpiderConvTable frobCoassoc.boundaryCount (prefixAtoms ++ frobCoassoc.lhs) (prefixAtoms ++ frobCoassoc.rhs)
  /-- Left counit `(ε⊗1)δ = 1` after a boundary-preserving prefix. -/
  | rowCounitLeft (prefixAtoms : List BrauerAtom)
      (prefixInRange : BrauerWordInRange frobCounitLeft.boundaryCount prefixAtoms)
      (boundaryPreserved :
        (processBrauer (brauerSeed frobCounitLeft.boundaryCount) prefixAtoms).openWires.length = frobCounitLeft.boundaryCount) :
      SpiderConvTable frobCounitLeft.boundaryCount (prefixAtoms ++ frobCounitLeft.lhs) (prefixAtoms ++ frobCounitLeft.rhs)
  /-- Right counit `(1⊗ε)δ = 1` after a boundary-preserving prefix. -/
  | rowCounitRight (prefixAtoms : List BrauerAtom)
      (prefixInRange : BrauerWordInRange frobCounitRight.boundaryCount prefixAtoms)
      (boundaryPreserved :
        (processBrauer (brauerSeed frobCounitRight.boundaryCount) prefixAtoms).openWires.length = frobCounitRight.boundaryCount) :
      SpiderConvTable frobCounitRight.boundaryCount (prefixAtoms ++ frobCounitRight.lhs) (prefixAtoms ++ frobCounitRight.rhs)
  /-- Frobenius law `(μ⊗1)(1⊗δ) = δμ` after a boundary-preserving prefix. -/
  | rowFrobLeft (prefixAtoms : List BrauerAtom)
      (prefixInRange : BrauerWordInRange frobLeft.boundaryCount prefixAtoms)
      (boundaryPreserved :
        (processBrauer (brauerSeed frobLeft.boundaryCount) prefixAtoms).openWires.length = frobLeft.boundaryCount) :
      SpiderConvTable frobLeft.boundaryCount (prefixAtoms ++ frobLeft.lhs) (prefixAtoms ++ frobLeft.rhs)
  /-- Frobenius law, other orientation `(1⊗μ)(δ⊗1) = δμ` after a boundary-preserving prefix. -/
  | rowFrobRight (prefixAtoms : List BrauerAtom)
      (prefixInRange : BrauerWordInRange frobRight.boundaryCount prefixAtoms)
      (boundaryPreserved :
        (processBrauer (brauerSeed frobRight.boundaryCount) prefixAtoms).openWires.length = frobRight.boundaryCount) :
      SpiderConvTable frobRight.boundaryCount (prefixAtoms ++ frobRight.lhs) (prefixAtoms ++ frobRight.rhs)
  /-- Commutativity of `μ` `μσ = μ` after a boundary-preserving prefix. -/
  | rowCommMult (prefixAtoms : List BrauerAtom)
      (prefixInRange : BrauerWordInRange frobCommMult.boundaryCount prefixAtoms)
      (boundaryPreserved :
        (processBrauer (brauerSeed frobCommMult.boundaryCount) prefixAtoms).openWires.length = frobCommMult.boundaryCount) :
      SpiderConvTable frobCommMult.boundaryCount (prefixAtoms ++ frobCommMult.lhs) (prefixAtoms ++ frobCommMult.rhs)
  /-- Cocommutativity of `δ` `σδ = δ` after a boundary-preserving prefix. -/
  | rowCommComult (prefixAtoms : List BrauerAtom)
      (prefixInRange : BrauerWordInRange frobCommComult.boundaryCount prefixAtoms)
      (boundaryPreserved :
        (processBrauer (brauerSeed frobCommComult.boundaryCount) prefixAtoms).openWires.length = frobCommComult.boundaryCount) :
      SpiderConvTable frobCommComult.boundaryCount (prefixAtoms ++ frobCommComult.lhs) (prefixAtoms ++ frobCommComult.rhs)
  /-- Symmetry involutivity `σσ = 1⊗1` after a boundary-preserving prefix. -/
  | rowCrossingInvolution (prefixAtoms : List BrauerAtom)
      (prefixInRange : BrauerWordInRange frobCrossingInvolution.boundaryCount prefixAtoms)
      (boundaryPreserved :
        (processBrauer (brauerSeed frobCrossingInvolution.boundaryCount) prefixAtoms).openWires.length
          = frobCrossingInvolution.boundaryCount) :
      SpiderConvTable frobCrossingInvolution.boundaryCount
        (prefixAtoms ++ frobCrossingInvolution.lhs) (prefixAtoms ++ frobCrossingInvolution.rhs)
  /-- Yang-Baxter (R3, three strands) after a boundary-preserving prefix. -/
  | rowYangBaxter (prefixAtoms : List BrauerAtom)
      (prefixInRange : BrauerWordInRange frobYangBaxter.boundaryCount prefixAtoms)
      (boundaryPreserved :
        (processBrauer (brauerSeed frobYangBaxter.boundaryCount) prefixAtoms).openWires.length = frobYangBaxter.boundaryCount) :
      SpiderConvTable frobYangBaxter.boundaryCount (prefixAtoms ++ frobYangBaxter.lhs) (prefixAtoms ++ frobYangBaxter.rhs)
  /-- ★ The special law `μδ = 1` after a boundary-preserving prefix. -/
  | rowSpecial (prefixAtoms : List BrauerAtom)
      (prefixInRange : BrauerWordInRange frobSpecial.boundaryCount prefixAtoms)
      (boundaryPreserved :
        (processBrauer (brauerSeed frobSpecial.boundaryCount) prefixAtoms).openWires.length = frobSpecial.boundaryCount) :
      SpiderConvTable frobSpecial.boundaryCount (prefixAtoms ++ frobSpecial.lhs) (prefixAtoms ++ frobSpecial.rhs)

/-! ## The embedding into the r4 syntactic surface (piece 1)

Each per-row constructor becomes one `SpiderConvSyntactic.relationAfterPrefix`: the fixed firing discipline
(`inRange_*`), the shipped parallel witness `frobX_parallel` (as `seedLengthEq`), and the decided
`frobXSeedView_ordered` (reassociated into the field's binder order) discharge the r4 generator's obligations from the
row DATA alone. -/
theorem spiderConvTable_toSpiderConvSyntactic {bottomCount : Nat} {leftWord rightWord : List BrauerAtom}
    (conv : SpiderConvTable bottomCount leftWord rightWord) :
    SpiderConvSyntactic bottomCount leftWord rightWord := by
  induction conv with
  | refl bottomCount word => exact SpiderConvSyntactic.refl bottomCount word
  | symm _ ih => exact ih.symm
  | trans _ _ ihLeft ihRight => exact ihLeft.trans ihRight
  | rowAssoc prefixAtoms prefixInRange boundaryPreserved =>
      exact SpiderConvSyntactic.relationAfterPrefix frobAssoc.boundaryCount (by decide)
        prefixAtoms frobAssoc.lhs frobAssoc.rhs prefixInRange boundaryPreserved
        inRange_multMult inRange_mult1Mult frobAssoc_parallel
        (fun firstIndex secondIndex firstBelow secondBelow =>
          frobAssocSeedView_ordered firstIndex firstBelow secondIndex secondBelow)
  | rowUnitLeft prefixAtoms prefixInRange boundaryPreserved =>
      exact SpiderConvSyntactic.relationAfterPrefix frobUnitLeft.boundaryCount (by decide)
        prefixAtoms frobUnitLeft.lhs frobUnitLeft.rhs prefixInRange boundaryPreserved
        inRange_unit0Mult (BrauerWordInRange.nil _) frobUnitLeft_parallel
        (fun firstIndex secondIndex firstBelow secondBelow =>
          frobUnitLeftSeedView_ordered firstIndex firstBelow secondIndex secondBelow)
  | rowUnitRight prefixAtoms prefixInRange boundaryPreserved =>
      exact SpiderConvSyntactic.relationAfterPrefix frobUnitRight.boundaryCount (by decide)
        prefixAtoms frobUnitRight.lhs frobUnitRight.rhs prefixInRange boundaryPreserved
        inRange_unit1Mult (BrauerWordInRange.nil _) frobUnitRight_parallel
        (fun firstIndex secondIndex firstBelow secondBelow =>
          frobUnitRightSeedView_ordered firstIndex firstBelow secondIndex secondBelow)
  | rowCoassoc prefixAtoms prefixInRange boundaryPreserved =>
      exact SpiderConvSyntactic.relationAfterPrefix frobCoassoc.boundaryCount (by decide)
        prefixAtoms frobCoassoc.lhs frobCoassoc.rhs prefixInRange boundaryPreserved
        inRange_comultComult inRange_comultComult1 frobCoassoc_parallel
        (fun firstIndex secondIndex firstBelow secondBelow =>
          frobCoassocSeedView_ordered firstIndex firstBelow secondIndex secondBelow)
  | rowCounitLeft prefixAtoms prefixInRange boundaryPreserved =>
      exact SpiderConvSyntactic.relationAfterPrefix frobCounitLeft.boundaryCount (by decide)
        prefixAtoms frobCounitLeft.lhs frobCounitLeft.rhs prefixInRange boundaryPreserved
        inRange_comultCounit0 (BrauerWordInRange.nil _) frobCounitLeft_parallel
        (fun firstIndex secondIndex firstBelow secondBelow =>
          frobCounitLeftSeedView_ordered firstIndex firstBelow secondIndex secondBelow)
  | rowCounitRight prefixAtoms prefixInRange boundaryPreserved =>
      exact SpiderConvSyntactic.relationAfterPrefix frobCounitRight.boundaryCount (by decide)
        prefixAtoms frobCounitRight.lhs frobCounitRight.rhs prefixInRange boundaryPreserved
        inRange_comultCounit1 (BrauerWordInRange.nil _) frobCounitRight_parallel
        (fun firstIndex secondIndex firstBelow secondBelow =>
          frobCounitRightSeedView_ordered firstIndex firstBelow secondIndex secondBelow)
  | rowFrobLeft prefixAtoms prefixInRange boundaryPreserved =>
      exact SpiderConvSyntactic.relationAfterPrefix frobLeft.boundaryCount (by decide)
        prefixAtoms frobLeft.lhs frobLeft.rhs prefixInRange boundaryPreserved
        inRange_comult1Mult inRange_multComult frobLeft_parallel
        (fun firstIndex secondIndex firstBelow secondBelow =>
          frobLeftSeedView_ordered firstIndex firstBelow secondIndex secondBelow)
  | rowFrobRight prefixAtoms prefixInRange boundaryPreserved =>
      exact SpiderConvSyntactic.relationAfterPrefix frobRight.boundaryCount (by decide)
        prefixAtoms frobRight.lhs frobRight.rhs prefixInRange boundaryPreserved
        inRange_comultMult1 inRange_multComult frobRight_parallel
        (fun firstIndex secondIndex firstBelow secondBelow =>
          frobRightSeedView_ordered firstIndex firstBelow secondIndex secondBelow)
  | rowCommMult prefixAtoms prefixInRange boundaryPreserved =>
      exact SpiderConvSyntactic.relationAfterPrefix frobCommMult.boundaryCount (by decide)
        prefixAtoms frobCommMult.lhs frobCommMult.rhs prefixInRange boundaryPreserved
        inRange_crossMult inRange_multSingle frobCommMult_parallel
        (fun firstIndex secondIndex firstBelow secondBelow =>
          frobCommMultSeedView_ordered firstIndex firstBelow secondIndex secondBelow)
  | rowCommComult prefixAtoms prefixInRange boundaryPreserved =>
      exact SpiderConvSyntactic.relationAfterPrefix frobCommComult.boundaryCount (by decide)
        prefixAtoms frobCommComult.lhs frobCommComult.rhs prefixInRange boundaryPreserved
        inRange_comultCross inRange_comultSingle frobCommComult_parallel
        (fun firstIndex secondIndex firstBelow secondBelow =>
          frobCommComultSeedView_ordered firstIndex firstBelow secondIndex secondBelow)
  | rowCrossingInvolution prefixAtoms prefixInRange boundaryPreserved =>
      exact SpiderConvSyntactic.relationAfterPrefix frobCrossingInvolution.boundaryCount (by decide)
        prefixAtoms frobCrossingInvolution.lhs frobCrossingInvolution.rhs prefixInRange boundaryPreserved
        inRange_crossCross (BrauerWordInRange.nil _) frobCrossingInvolution_parallel
        (fun firstIndex secondIndex firstBelow secondBelow =>
          frobCrossingInvolutionSeedView_ordered firstIndex firstBelow secondIndex secondBelow)
  | rowYangBaxter prefixAtoms prefixInRange boundaryPreserved =>
      exact SpiderConvSyntactic.relationAfterPrefix frobYangBaxter.boundaryCount (by decide)
        prefixAtoms frobYangBaxter.lhs frobYangBaxter.rhs prefixInRange boundaryPreserved
        inRange_ybLhs inRange_ybRhs frobYangBaxter_parallel
        (fun firstIndex secondIndex firstBelow secondBelow =>
          frobYangBaxterSeedView_ordered firstIndex firstBelow secondIndex secondBelow)
  | rowSpecial prefixAtoms prefixInRange boundaryPreserved =>
      exact SpiderConvSyntactic.relationAfterPrefix frobSpecial.boundaryCount (by decide)
        prefixAtoms frobSpecial.lhs frobSpecial.rhs prefixInRange boundaryPreserved
        inRange_comultMult_at1 (BrauerWordInRange.nil _) frobSpecial_parallel
        (fun firstIndex secondIndex firstBelow secondBelow =>
          frobSpecialSeedView_ordered firstIndex firstBelow secondIndex secondBelow)

/-- ★ **`SpiderConvTable` embeds into `SpiderConv`** — through the r4 syntactic surface + its bridge. -/
theorem spiderConvTable_toSpiderConv {bottomCount : Nat} {leftWord rightWord : List BrauerAtom}
    (conv : SpiderConvTable bottomCount leftWord rightWord) :
    SpiderConv bottomCount leftWord rightWord :=
  spiderConvSyntactic_toSpiderConv (spiderConvTable_toSpiderConvSyntactic conv)

/-- ★ **`SpiderConvTable` is partition-sound** (piece 4) — GATE-FREE full syntactic soundness: any two words related
by the gate-free table induce the SAME boundary partition (`extraSpiderDiagramOf`, the extraspecial / corelation
invariant), routed through the r4 bridge (`spiderConvSyntactic_partitionSound`).  The per-row view obligations were
discharged ONCE by the decided table, so no per-instance gate appears. -/
theorem spiderConvTable_partitionSound {bottomCount : Nat} {leftWord rightWord : List BrauerAtom}
    (conv : SpiderConvTable bottomCount leftWord rightWord) :
    extraSpiderDiagramOf bottomCount leftWord = extraSpiderDiagramOf bottomCount rightWord :=
  spiderConvSyntactic_partitionSound (spiderConvTable_toSpiderConvSyntactic conv)

/-! ## Non-vacuity — the sentinel through the gate-free constructor + a composed identification -/

/-- ★ **The special law whiskered after a non-empty prefix, through the GATE-FREE constructor.**  After an identity
strand (boundary `1` preserved), `μδ = 1` on the produced strand is `SpiderConvTable` — supplied by DATA ONLY (the
prefix, its in-range cons, the boundary-preservation `decide`); the row's seed view is baked into `rowSpecial`, never
re-supplied at the call site.  Contrast the r4 `spiderConvSyntactic_special_afterIdentityPrefix`, whose call site
still hands the generator a `seedViewAgrees` view function. -/
theorem spiderConvTable_special_afterIdentityPrefix :
    SpiderConvTable 1 ([identityStrandAt 0] ++ frobSpecial.lhs) ([identityStrandAt 0] ++ frobSpecial.rhs) :=
  SpiderConvTable.rowSpecial [identityStrandAt 0]
    (BrauerWordInRange.cons (identityStrandAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 1))
    (by decide)

/-- The special-after-identity-prefix move genuinely relates DISTINCT words. -/
theorem spiderConvTable_special_identifies_distinct :
    ([identityStrandAt 0] ++ frobSpecial.lhs) ≠ ([identityStrandAt 0] ++ frobSpecial.rhs)
      ∧ SpiderConvTable 1 ([identityStrandAt 0] ++ frobSpecial.lhs) ([identityStrandAt 0] ++ frobSpecial.rhs) :=
  ⟨by decide, spiderConvTable_special_afterIdentityPrefix⟩

/-- ★ **The gate-free identification is partition-real** — the two distinct special-after-prefix words induce the
SAME boundary partition, via `spiderConvTable_partitionSound` (the FUNCTORIAL soundness, not a per-instance decide). -/
theorem spiderConvTable_special_partitionAgrees :
    extraSpiderDiagramOf 1 ([identityStrandAt 0] ++ frobSpecial.lhs)
      = extraSpiderDiagramOf 1 ([identityStrandAt 0] ++ frobSpecial.rhs) :=
  spiderConvTable_partitionSound spiderConvTable_special_afterIdentityPrefix

/-- The Frobenius law fired at the seed (empty prefix) through `rowFrobLeft`. -/
private theorem tableFrobLeftAtSeed : SpiderConvTable 2 frobLeft.lhs frobLeft.rhs :=
  SpiderConvTable.rowFrobLeft [] (BrauerWordInRange.nil 2) (by decide)

/-- The other Frobenius orientation fired at the seed (empty prefix) through `rowFrobRight`. -/
private theorem tableFrobRightAtSeed : SpiderConvTable 2 frobRight.lhs frobRight.rhs :=
  SpiderConvTable.rowFrobRight [] (BrauerWordInRange.nil 2) (by decide)

/-- ★ **A composed (two-row) identification through the gate-free table.**  Both Frobenius orientations converge on
the shared H element `δμ` (`frobLeft.rhs = frobRight.rhs`), so `trans`/`symm` chain them into a `SpiderConvTable`
between the two DISTINCT lhs words `(μ⊗1)(1⊗δ)` and `(1⊗μ)(δ⊗1)` — a genuinely non-reflexive, multi-row
identification the equivalence closure supplies. -/
theorem spiderConvTable_frobLeft_frobRight_lhs :
    SpiderConvTable 2 frobLeft.lhs frobRight.lhs :=
  SpiderConvTable.trans tableFrobLeftAtSeed (SpiderConvTable.symm tableFrobRightAtSeed)

/-- The composed identification genuinely relates DISTINCT words. -/
theorem spiderConvTable_frobLeft_frobRight_identifies_distinct :
    frobLeft.lhs ≠ frobRight.lhs ∧ SpiderConvTable 2 frobLeft.lhs frobRight.lhs :=
  ⟨by decide, spiderConvTable_frobLeft_frobRight_lhs⟩

/-- ★ **`SpiderConvTable` is a PROPER relation** — the Frobenius H element `δμ` is NOT table-related to the identity
pair.  If it were, `spiderConvTable_partitionSound` would equate their genuinely-distinct partitions
(`extraSpiderDiagram_H_ne_identity`).  So the gate-free table genuinely constrains convertibility (it is not the total
relation). -/
theorem spiderConvTable_H_not_identity :
    ¬ SpiderConvTable 2 [multAt 0, comultAt 0] [identityStrandAt 0, identityStrandAt 1] :=
  fun conv => extraSpiderDiagram_H_ne_identity (spiderConvTable_partitionSound conv)

/-! ## The two-sided context — a concrete DECIDED witness (piece 2, partial)

`SpiderConvTable` whiskers a presented row after a PREFIX.  A genuinely TWO-SIDED context `prefix ++ side ++ suffix`
is reachable PER-INSTANCE through the SAME r4 bridge (`SpiderConvSyntactic.relationAfterPrefix`): treat `side ++
suffix` as the bridge's word and supply the seed-local two-sided view fact by `decide`.  The special law `μδ = 1`
under a prefix identity strand AND a suffix comultiplication — `δμδ ≡ δ` — is such a witness: it is sound because the
seed runs of `δμδ` and `δ` agree on the boundary partition view (`specialTwoSidedSeedView_ordered`, `decide`).

What this DOES demonstrate: the machinery handles two-sided contexts whenever the seed-local two-sided view is
decided.  What it does NOT give: the GENERAL suffix congruence UNIFORM over all suffixes — that
(`SpiderConvTable n a b → SpiderConvTable n (a ++ suffix) (b ++ suffix)`) needs the forward `stepWiring`
view-functoriality brick (`fxFrob_hasSpiderSuffixCongruence`, r6), NOT a second application of the r4 keystone (which
fixes one mid-state and varies the word, the transpose of what the suffix leg needs). -/

/-- Firing discipline for the two-sided witness word `δμδ` at boundary `1`. -/
private theorem inRange_comultMultComult : BrauerWordInRange 1 [comultAt 0, multAt 0, comultAt 0] :=
  BrauerWordInRange.cons (comultAt 0) 0 rfl (by decide)
    (BrauerWordInRange.cons (multAt 0) 0 rfl (by decide)
      (BrauerWordInRange.cons (comultAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 2)))

/-- The seed-local two-sided boundary view: `δμδ` and `δ` agree on `matchingSameComponent` (boundary `1`), in the
guard-after-binder order.  By `decide` — the special row survives a suffix comultiplication at the partition level. -/
private theorem specialTwoSidedSeedView_ordered : ∀ firstIndex,
    firstIndex < 1 + (processBrauer (brauerSeed 1) [comultAt 0, multAt 0, comultAt 0]).openWires.length →
    ∀ secondIndex,
    secondIndex < 1 + (processBrauer (brauerSeed 1) [comultAt 0, multAt 0, comultAt 0]).openWires.length →
    matchingSameComponent 1 (processBrauer (brauerSeed 1) [comultAt 0, multAt 0, comultAt 0]) firstIndex secondIndex
      = matchingSameComponent 1 (processBrauer (brauerSeed 1) [comultAt 0]) firstIndex secondIndex := by decide

/-- ★ **A concrete TWO-SIDED context identification.**  The special law `μδ = 1` fired between a prefix identity
strand (left context) and a suffix comultiplication (right context) — `δμδ ≡ δ` — is a `SpiderConv` theorem, routed
through the r4 bridge with the seed-local two-sided view decided.  Genuinely two-sided: BOTH the left context
`[identityStrandAt 0]` and the right context `[comultAt 0]` are non-empty. -/
theorem spiderConv_special_twoSidedContext :
    SpiderConv 1 (([identityStrandAt 0] ++ [comultAt 0, multAt 0]) ++ [comultAt 0])
      (([identityStrandAt 0] ++ ([] : List BrauerAtom)) ++ [comultAt 0]) :=
  spiderConvSyntactic_toSpiderConv
    (SpiderConvSyntactic.relationAfterPrefix 1 (by decide) [identityStrandAt 0]
      ([comultAt 0, multAt 0] ++ [comultAt 0]) (([] : List BrauerAtom) ++ [comultAt 0])
      (BrauerWordInRange.cons (identityStrandAt 0) 0 rfl (by decide) (BrauerWordInRange.nil 1))
      (by decide)
      inRange_comultMultComult inRange_comultSingle rfl
      (fun firstIndex secondIndex firstBelow secondBelow =>
        specialTwoSidedSeedView_ordered firstIndex firstBelow secondIndex secondBelow))

/-- The two-sided witness genuinely relates DISTINCT words. -/
theorem spiderConv_special_twoSidedContext_distinct :
    (([identityStrandAt 0] ++ [comultAt 0, multAt 0]) ++ [comultAt 0])
      ≠ (([identityStrandAt 0] ++ ([] : List BrauerAtom)) ++ [comultAt 0]) := by decide

/-- ★ **The two-sided identification is partition-real** — `δμδ` and `δ` in the doubled context induce the SAME
boundary partition, via `spiderConv_partitionSound`. -/
theorem spiderConv_special_twoSidedContext_partitionAgrees :
    extraSpiderDiagramOf 1 (([identityStrandAt 0] ++ [comultAt 0, multAt 0]) ++ [comultAt 0])
      = extraSpiderDiagramOf 1 (([identityStrandAt 0] ++ ([] : List BrauerAtom)) ++ [comultAt 0]) :=
  spiderConv_partitionSound spiderConv_special_twoSidedContext

/-! ## Honesty markers — the gate-free table (shipped) and the two-sided residuals (walled) -/

/-- ★ **Honesty marker — the DECIDED per-row seed-view table is SHIPPED.**  The thirteen `frobXSeedView_ordered`
facts state, at each row's own boundary and over its fixed finite boundary indices, that the lhs- and rhs-processed
`brauerSeed` runs agree on `matchingSameComponent`; each is proved by RAW `decide` (measured sub-second even for the
depth-3 Yang-Baxter row).  This is the finite decidable representation of the presentation's boundary-view content,
decided ONCE for reuse.  `= true`. -/
def fxFrob_hasSpiderSeedViewTable : Bool := true

/-- ★ **Honesty marker — the GATE-FREE contextual congruence `SpiderConvTable` is SHIPPED partition-sound.**  Every
per-row constructor takes ONLY the prefix word + its firing discipline + a boundary-preservation length equation — NO
field quantifies over the boundary view or the post-prefix state (contrast `SpiderConvSyntactic.relationAfterPrefix`'s
`seedViewAgrees` gate).  The decided table supplies the row view internally, so `spiderConvTable_toSpiderConvSyntactic`
is one `relationAfterPrefix` per row and `spiderConvTable_partitionSound` composes straight through the r4 bridge.
NON-VACUOUS: it identifies distinct words after a real prefix (`spiderConvTable_special_identifies_distinct`), a
composed two-row identification (`spiderConvTable_frobLeft_frobRight_identifies_distinct`), and is proper
(`spiderConvTable_H_not_identity`).  This is the boundary-COMPLEMENT-restricted (BGKSZ Thm 35) contextual rewrite,
finite-decided per row.  `= true`. -/
def fxFrob_hasSpiderConvTable : Bool := true

/-- ★ **Honesty marker — a concrete TWO-SIDED context witness is SHIPPED (piece 2, partial).**
`spiderConv_special_twoSidedContext` identifies `δμδ ≡ δ` between a non-empty prefix (identity strand) AND a non-empty
suffix (comultiplication), routed through the r4 bridge with the seed-local two-sided view decided
(`specialTwoSidedSeedView_ordered`); partition-real (`spiderConv_special_twoSidedContext_partitionAgrees`).  So the
machinery DOES handle two-sided contexts per-instance whenever the seed-local two-sided view is decided.  The GENERAL
(uniform-over-all-suffixes) congruence is the separate `fxFrob_hasSpiderSuffixCongruence` residual.  `= true`. -/
def fxFrob_hasTwoSidedContextWitness : Bool := true

/-- ★ **Honesty marker — the UNIFORM two-sided SUFFIX congruence is SHIPPED (r6, flag flipped `false → true`).**  A
concrete two-sided context was decided per-instance in r5 (`fxFrob_hasTwoSidedContextWitness`); the UNIFORM congruence
`SpiderConv n a b → (in-range suffix) → SpiderConv n (a ++ suffix) (b ++ suffix)` is now shipped in
`Frobenius/SpiderSuffixCongruence.lean` (`spiderConv_suffixCongruence`, and the table-level
`spiderConvTable_suffixCongruence`).  The one missing ingredient this marker named — the FORWARD `stepWiring`
view-functoriality (view-equal inputs give view-equal outputs) — was built from scratch: NOT the r4 keystone
`processBrauer_forgetView_eq_ofCanonicalViewParts` (which fixes ONE mid-state and varies the WORD under a single
rename; the suffix leg fixes ONE word and varies the MID-STATE under two renames — transposed, no reuse), and NOT a
global `sigma`-relabeling (the two states agree only on the boundary VIEW).  Instead a `StepNodeCorr` correspondence
invariant is carried through the whole generic `stepWiringArcs` fold (`stepWiringArcs_viewInvariant`), from the
fresh-separation base (`stepNodeCorr_baseSameComp`) and the four-zone post-step classifier
(`stepWiring_boundaryRead_stepNodeCorr`), assembled into `stepWiring_viewCongruence` and folded over an in-range
suffix (`processBrauer_viewCongruence`).  The loops-free reconstruction `spiderConv_stateViewEq` supplies the two seed
states' view (carrying the special row `μδ = 1`, unequal loops), and the empty-prefix `whisker` re-packages.  Uniform
over ALL in-range suffixes — no per-suffix semantic gate (the `BrauerWordInRange` datum is the same gate-free
bookkeeping the table's own constructors carry).  See `fxFrob_hasSpiderSuffixCongruenceShipped`.  `= true`. -/
def fxFrob_hasSpiderSuffixCongruence : Bool := true

/-- ★ **Honesty marker — the BOUNDARY-CHANGING (nonzero left-offset) leg is SHIPPED (r6, flag flipped
`false → true`).**  The FROB-3 pad machinery (`SpiderPadCongruence`, `fxFrob_hasSpiderPadCongruence`) lifted only the
RIGHT-pad offset-`0` case (extra strands to the RIGHT of a wider seed, same firing positions).  The complementary
boundary-CHANGING leg this marker named as its residual — the nonzero-offset `shiftBrauerWord` LEFT pad (extra
strands to the LEFT, every firing position shifted by `delta`, boundary widened to `delta + threshold`) — is now
shipped in `Frobenius/SpiderLeftPadCongruence.lean` (`fxFrob_hasSpiderBoundaryChangingPadLeft`):
`spiderConv_relation_inWiderBoundary_leftOffset` packages a spider relation fired at ANY nonzero left offset as a
`SpiderConv`, discharged by the whole-word left-pad simulation `processBrauer_leftPadSim` + the leaner loops-free
payoff `matchingSameComponent_ofSpiderLeftPadSimPair` (which carries the special row `μδ = 1`, unequal loops but
equal partition) through the empty-prefix `whisker`.  NON-VACUOUS + genuinely boundary-CHANGING + genuinely
NONZERO-OFFSET: the special law (`spiderConv_special_atLeftOffset`, boundary `1 → 2`, positions shifted) and the
Frobenius law (`spiderConv_frobLeft_atLeftOffset`, boundary `2 → 3`) are convertible at the shifted positions,
partition-real (`spiderConv_special_atLeftOffset_partitionAgrees`).  So the right pad (offset `0`) and this left pad
(nonzero offset) together close BOTH horizontal pad directions (BGKSZ II two-sided Frobenius context closure).  What
this leg does NOT subsume — the mechanical composition of the r4 prefix BRIDGE with this left pad for an ARBITRARY
boundary-changing prefix WORD whose post-prefix reachable state is not itself a `shiftBrauerWord` embedding — remains
open under `fxFrob_hasSpiderAfterPrefixContext`.  `= true`. -/
def fxFrob_hasSpiderBoundaryChangingPrefix : Bool := true

end FX1Poly.Polygraph

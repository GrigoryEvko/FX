import FX1Poly.Typed.ConvCodeInjectivity

/-! # FX1Poly/Typed/ConvFlatCodeInjectivity — `Conv` structural characterization for the FLAT
    (non-dependent, binary) data type-code formers, proved SN-FREE.

`ConvCodeInjectivity.lean` ships the `Conv`-injectivity + congruence characterization for the
DEPENDENT (binding) type-code formers Π and Σ (`Conv.piTyCode_inj` / `Conv.sigmaTyCode_inj`, the SR
ingredient).  This file is its FLAT twin: the same characterization for the five NON-DEPENDENT binary
data type-code formers — `arrowCode`, `productCode`, `sumCode`, `eitherCode`, `equivCode` — exactly the
formers the flat description engine `HasTypeDescFlat` types (the `[0,0]`-binderShift formers of
TELESCOPE-REACH / FLAT-ENGINE).  Both children live at the SAME scope (no binder, no scope shift), so
the proofs are LIGHTER than the Π/Σ versions: no `scope + 1` codomain bookkeeping.

`Conv (arrowCodeCell A B) (arrowCodeCell A' B') ↔ Conv A A' ∧ Conv B B'` (and the four siblings).  The
INJECTIVITY direction is the inversion ingredient typed metatheory consumes to relate a conv-disguised
flat code to its actual components; the CONGRUENCE direction is the `Conv.ofChildren` lift.

## Why this is SN-free (same crack as the Π/Σ version)

`Conv` is `StepStar.Join`.  Each `gen_*Code` here is a CONGRUENCE-ONLY former: a `Step` out of it can
only reduce a child (`Step.from_arrowCode` etc.; `beta`/`iota` fire on other heads).  So the head is
STABLE under `StepStar` — a flat code only ever reduces to the SAME flat code with reduced children
(`StepStar.shapeStable_*`).  Two joinable codes share a common flat-code reduct, and componentwise
joinability (= `Conv` on the components) drops out.  No confluence, no strong normalization, no
`Conv.trans` — just head-stability + the `Join` definition (the `Step.from_*` inversions live in
`StepInversion.lean`).

## Contents (per former: arrow / product / sum / either / equiv)

* `StepStar.shapeStable_<former>General` — head-stability under reduction (the `StepStar` induction).
* `<former>Cell_inj` — the raw cell is injective (`cases` on the cell equality).
* `Conv.<former>_inj` — `Conv`-injectivity (the → direction), the inversion ingredient.
* `Conv.<former>_cong` — `Conv`-congruence (the ← direction) via `Conv.ofChildren`.
* `Conv.<former>_iff` — the structural characterization.

## Zero-axiom

`Step.from_<former>` + `StepStar` induction + the `Join` unpack + `cases`-form cell injectivity +
`Conv.ofChildren`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## arrowCode (the non-dependent function-type former `A -> B`) -/

/-- Subject-generalised head-stability for `arrowCode` under `StepStar`: a reduction sequence out of an
arrow code preserves the `gen_arrowCode` head, reducing the two same-scope children pointwise. -/
theorem StepStar.shapeStable_arrowCodeGeneral {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) :
    ∀ (firstType secondType : RawTerm scope),
      source = (.mkGen .gen_arrowCode () (.childCons firstType (.childCons secondType .childNil))) →
      ∃ (firstAfter secondAfter : RawTerm scope),
        target = (.mkGen .gen_arrowCode () (.childCons firstAfter (.childCons secondAfter .childNil))) ∧
        StepStar firstType firstAfter ∧ StepStar secondType secondAfter := by
  induction chain with
  | refl _term =>
      intro firstType secondType sourceEq
      exact ⟨firstType, secondType, sourceEq, StepStar.refl _, StepStar.refl _⟩
  | trans headStep _tail tailIH =>
      intro firstType secondType sourceEq
      subst sourceEq
      rcases Step.from_arrowCode headStep with
        ⟨firstAfter, midEq, firstStep⟩ | ⟨secondAfter, midEq, secondStep⟩
      · obtain ⟨fFinal, sFinal, targetEq, firstStar, secondStar⟩ :=
          tailIH firstAfter secondType midEq
        exact ⟨fFinal, sFinal, targetEq, StepStar.trans firstStep firstStar, secondStar⟩
      · obtain ⟨fFinal, sFinal, targetEq, firstStar, secondStar⟩ :=
          tailIH firstType secondAfter midEq
        exact ⟨fFinal, sFinal, targetEq, firstStar, StepStar.trans secondStep secondStar⟩

/-- The raw `arrowCode` cell is injective. -/
theorem arrowCodeCell_inj {scope : Nat} {firstType firstType' secondType secondType' : RawTerm scope}
    (cellsEqual :
      (.mkGen .gen_arrowCode () (.childCons firstType (.childCons secondType .childNil)) : RawTerm scope)
        = .mkGen .gen_arrowCode () (.childCons firstType' (.childCons secondType' .childNil))) :
    firstType = firstType' ∧ secondType = secondType' := by
  cases cellsEqual
  exact ⟨rfl, rfl⟩

/-- **arrowCode `Conv`-injectivity** (SN-free): convertible arrow codes have convertible components. -/
theorem Conv.arrowCode_inj {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope}
    (convertibility :
      Conv (.mkGen .gen_arrowCode () (.childCons firstType (.childCons secondType .childNil)))
        (.mkGen .gen_arrowCode () (.childCons firstType' (.childCons secondType' .childNil)))) :
    Conv firstType firstType' ∧ Conv secondType secondType' := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨leftFirst, leftSecond, leftCommonEq, leftFirstStar, leftSecondStar⟩ :=
    StepStar.shapeStable_arrowCodeGeneral leftChain firstType secondType rfl
  obtain ⟨_rightFirst, _rightSecond, rightCommonEq, rightFirstStar, rightSecondStar⟩ :=
    StepStar.shapeStable_arrowCodeGeneral rightChain firstType' secondType' rfl
  rw [leftCommonEq] at rightCommonEq
  obtain ⟨firstAgree, secondAgree⟩ := arrowCodeCell_inj rightCommonEq
  refine ⟨⟨leftFirst, leftFirstStar, ?_⟩, ⟨leftSecond, leftSecondStar, ?_⟩⟩
  · rw [firstAgree]; exact rightFirstStar
  · rw [secondAgree]; exact rightSecondStar

/-- **arrowCode `Conv`-congruence** (the ← direction): convertible components give convertible codes. -/
theorem Conv.arrowCode_cong {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope}
    (firstConv : Conv firstType firstType') (secondConv : Conv secondType secondType') :
    Conv (.mkGen .gen_arrowCode () (.childCons firstType (.childCons secondType .childNil)))
      (.mkGen .gen_arrowCode () (.childCons firstType' (.childCons secondType' .childNil))) :=
  Conv.ofChildren (ConvChildren.consC firstConv (ConvChildren.consC secondConv ConvChildren.nilC))

/-- **The arrowCode `Conv` structural characterization.** -/
theorem Conv.arrowCode_iff {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope} :
    Conv (.mkGen .gen_arrowCode () (.childCons firstType (.childCons secondType .childNil)))
        (.mkGen .gen_arrowCode () (.childCons firstType' (.childCons secondType' .childNil)))
      ↔ Conv firstType firstType' ∧ Conv secondType secondType' :=
  ⟨Conv.arrowCode_inj, fun ⟨firstConv, secondConv⟩ => Conv.arrowCode_cong firstConv secondConv⟩

/-! ## productCode (the non-dependent product former `A * B`) -/

/-- Head-stability for `productCode` under `StepStar`. -/
theorem StepStar.shapeStable_productCodeGeneral {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) :
    ∀ (firstType secondType : RawTerm scope),
      source = (.mkGen .gen_productCode () (.childCons firstType (.childCons secondType .childNil))) →
      ∃ (firstAfter secondAfter : RawTerm scope),
        target = (.mkGen .gen_productCode () (.childCons firstAfter (.childCons secondAfter .childNil))) ∧
        StepStar firstType firstAfter ∧ StepStar secondType secondAfter := by
  induction chain with
  | refl _term =>
      intro firstType secondType sourceEq
      exact ⟨firstType, secondType, sourceEq, StepStar.refl _, StepStar.refl _⟩
  | trans headStep _tail tailIH =>
      intro firstType secondType sourceEq
      subst sourceEq
      rcases Step.from_productCode headStep with
        ⟨firstAfter, midEq, firstStep⟩ | ⟨secondAfter, midEq, secondStep⟩
      · obtain ⟨fFinal, sFinal, targetEq, firstStar, secondStar⟩ :=
          tailIH firstAfter secondType midEq
        exact ⟨fFinal, sFinal, targetEq, StepStar.trans firstStep firstStar, secondStar⟩
      · obtain ⟨fFinal, sFinal, targetEq, firstStar, secondStar⟩ :=
          tailIH firstType secondAfter midEq
        exact ⟨fFinal, sFinal, targetEq, firstStar, StepStar.trans secondStep secondStar⟩

/-- The raw `productCode` cell is injective. -/
theorem productCodeCell_inj {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope}
    (cellsEqual :
      (.mkGen .gen_productCode () (.childCons firstType (.childCons secondType .childNil)) : RawTerm scope)
        = .mkGen .gen_productCode () (.childCons firstType' (.childCons secondType' .childNil))) :
    firstType = firstType' ∧ secondType = secondType' := by
  cases cellsEqual
  exact ⟨rfl, rfl⟩

/-- **productCode `Conv`-injectivity** (SN-free). -/
theorem Conv.productCode_inj {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope}
    (convertibility :
      Conv (.mkGen .gen_productCode () (.childCons firstType (.childCons secondType .childNil)))
        (.mkGen .gen_productCode () (.childCons firstType' (.childCons secondType' .childNil)))) :
    Conv firstType firstType' ∧ Conv secondType secondType' := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨leftFirst, leftSecond, leftCommonEq, leftFirstStar, leftSecondStar⟩ :=
    StepStar.shapeStable_productCodeGeneral leftChain firstType secondType rfl
  obtain ⟨_rightFirst, _rightSecond, rightCommonEq, rightFirstStar, rightSecondStar⟩ :=
    StepStar.shapeStable_productCodeGeneral rightChain firstType' secondType' rfl
  rw [leftCommonEq] at rightCommonEq
  obtain ⟨firstAgree, secondAgree⟩ := productCodeCell_inj rightCommonEq
  refine ⟨⟨leftFirst, leftFirstStar, ?_⟩, ⟨leftSecond, leftSecondStar, ?_⟩⟩
  · rw [firstAgree]; exact rightFirstStar
  · rw [secondAgree]; exact rightSecondStar

/-- **productCode `Conv`-congruence** (the ← direction). -/
theorem Conv.productCode_cong {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope}
    (firstConv : Conv firstType firstType') (secondConv : Conv secondType secondType') :
    Conv (.mkGen .gen_productCode () (.childCons firstType (.childCons secondType .childNil)))
      (.mkGen .gen_productCode () (.childCons firstType' (.childCons secondType' .childNil))) :=
  Conv.ofChildren (ConvChildren.consC firstConv (ConvChildren.consC secondConv ConvChildren.nilC))

/-- **The productCode `Conv` structural characterization.** -/
theorem Conv.productCode_iff {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope} :
    Conv (.mkGen .gen_productCode () (.childCons firstType (.childCons secondType .childNil)))
        (.mkGen .gen_productCode () (.childCons firstType' (.childCons secondType' .childNil)))
      ↔ Conv firstType firstType' ∧ Conv secondType secondType' :=
  ⟨Conv.productCode_inj, fun ⟨firstConv, secondConv⟩ => Conv.productCode_cong firstConv secondConv⟩

/-! ## sumCode (the non-dependent coproduct former `A + B`) -/

/-- Head-stability for `sumCode` under `StepStar`. -/
theorem StepStar.shapeStable_sumCodeGeneral {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) :
    ∀ (firstType secondType : RawTerm scope),
      source = (.mkGen .gen_sumCode () (.childCons firstType (.childCons secondType .childNil))) →
      ∃ (firstAfter secondAfter : RawTerm scope),
        target = (.mkGen .gen_sumCode () (.childCons firstAfter (.childCons secondAfter .childNil))) ∧
        StepStar firstType firstAfter ∧ StepStar secondType secondAfter := by
  induction chain with
  | refl _term =>
      intro firstType secondType sourceEq
      exact ⟨firstType, secondType, sourceEq, StepStar.refl _, StepStar.refl _⟩
  | trans headStep _tail tailIH =>
      intro firstType secondType sourceEq
      subst sourceEq
      rcases Step.from_sumCode headStep with
        ⟨firstAfter, midEq, firstStep⟩ | ⟨secondAfter, midEq, secondStep⟩
      · obtain ⟨fFinal, sFinal, targetEq, firstStar, secondStar⟩ :=
          tailIH firstAfter secondType midEq
        exact ⟨fFinal, sFinal, targetEq, StepStar.trans firstStep firstStar, secondStar⟩
      · obtain ⟨fFinal, sFinal, targetEq, firstStar, secondStar⟩ :=
          tailIH firstType secondAfter midEq
        exact ⟨fFinal, sFinal, targetEq, firstStar, StepStar.trans secondStep secondStar⟩

/-- The raw `sumCode` cell is injective. -/
theorem sumCodeCell_inj {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope}
    (cellsEqual :
      (.mkGen .gen_sumCode () (.childCons firstType (.childCons secondType .childNil)) : RawTerm scope)
        = .mkGen .gen_sumCode () (.childCons firstType' (.childCons secondType' .childNil))) :
    firstType = firstType' ∧ secondType = secondType' := by
  cases cellsEqual
  exact ⟨rfl, rfl⟩

/-- **sumCode `Conv`-injectivity** (SN-free). -/
theorem Conv.sumCode_inj {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope}
    (convertibility :
      Conv (.mkGen .gen_sumCode () (.childCons firstType (.childCons secondType .childNil)))
        (.mkGen .gen_sumCode () (.childCons firstType' (.childCons secondType' .childNil)))) :
    Conv firstType firstType' ∧ Conv secondType secondType' := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨leftFirst, leftSecond, leftCommonEq, leftFirstStar, leftSecondStar⟩ :=
    StepStar.shapeStable_sumCodeGeneral leftChain firstType secondType rfl
  obtain ⟨_rightFirst, _rightSecond, rightCommonEq, rightFirstStar, rightSecondStar⟩ :=
    StepStar.shapeStable_sumCodeGeneral rightChain firstType' secondType' rfl
  rw [leftCommonEq] at rightCommonEq
  obtain ⟨firstAgree, secondAgree⟩ := sumCodeCell_inj rightCommonEq
  refine ⟨⟨leftFirst, leftFirstStar, ?_⟩, ⟨leftSecond, leftSecondStar, ?_⟩⟩
  · rw [firstAgree]; exact rightFirstStar
  · rw [secondAgree]; exact rightSecondStar

/-- **sumCode `Conv`-congruence** (the ← direction). -/
theorem Conv.sumCode_cong {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope}
    (firstConv : Conv firstType firstType') (secondConv : Conv secondType secondType') :
    Conv (.mkGen .gen_sumCode () (.childCons firstType (.childCons secondType .childNil)))
      (.mkGen .gen_sumCode () (.childCons firstType' (.childCons secondType' .childNil))) :=
  Conv.ofChildren (ConvChildren.consC firstConv (ConvChildren.consC secondConv ConvChildren.nilC))

/-- **The sumCode `Conv` structural characterization.** -/
theorem Conv.sumCode_iff {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope} :
    Conv (.mkGen .gen_sumCode () (.childCons firstType (.childCons secondType .childNil)))
        (.mkGen .gen_sumCode () (.childCons firstType' (.childCons secondType' .childNil)))
      ↔ Conv firstType firstType' ∧ Conv secondType secondType' :=
  ⟨Conv.sumCode_inj, fun ⟨firstConv, secondConv⟩ => Conv.sumCode_cong firstConv secondConv⟩

/-! ## eitherCode (the tagged-coproduct former `Either A B`) -/

/-- Head-stability for `eitherCode` under `StepStar`. -/
theorem StepStar.shapeStable_eitherCodeGeneral {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) :
    ∀ (firstType secondType : RawTerm scope),
      source = (.mkGen .gen_eitherCode () (.childCons firstType (.childCons secondType .childNil))) →
      ∃ (firstAfter secondAfter : RawTerm scope),
        target = (.mkGen .gen_eitherCode () (.childCons firstAfter (.childCons secondAfter .childNil))) ∧
        StepStar firstType firstAfter ∧ StepStar secondType secondAfter := by
  induction chain with
  | refl _term =>
      intro firstType secondType sourceEq
      exact ⟨firstType, secondType, sourceEq, StepStar.refl _, StepStar.refl _⟩
  | trans headStep _tail tailIH =>
      intro firstType secondType sourceEq
      subst sourceEq
      rcases Step.from_eitherCode headStep with
        ⟨firstAfter, midEq, firstStep⟩ | ⟨secondAfter, midEq, secondStep⟩
      · obtain ⟨fFinal, sFinal, targetEq, firstStar, secondStar⟩ :=
          tailIH firstAfter secondType midEq
        exact ⟨fFinal, sFinal, targetEq, StepStar.trans firstStep firstStar, secondStar⟩
      · obtain ⟨fFinal, sFinal, targetEq, firstStar, secondStar⟩ :=
          tailIH firstType secondAfter midEq
        exact ⟨fFinal, sFinal, targetEq, firstStar, StepStar.trans secondStep secondStar⟩

/-- The raw `eitherCode` cell is injective. -/
theorem eitherCodeCell_inj {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope}
    (cellsEqual :
      (.mkGen .gen_eitherCode () (.childCons firstType (.childCons secondType .childNil)) : RawTerm scope)
        = .mkGen .gen_eitherCode () (.childCons firstType' (.childCons secondType' .childNil))) :
    firstType = firstType' ∧ secondType = secondType' := by
  cases cellsEqual
  exact ⟨rfl, rfl⟩

/-- **eitherCode `Conv`-injectivity** (SN-free). -/
theorem Conv.eitherCode_inj {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope}
    (convertibility :
      Conv (.mkGen .gen_eitherCode () (.childCons firstType (.childCons secondType .childNil)))
        (.mkGen .gen_eitherCode () (.childCons firstType' (.childCons secondType' .childNil)))) :
    Conv firstType firstType' ∧ Conv secondType secondType' := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨leftFirst, leftSecond, leftCommonEq, leftFirstStar, leftSecondStar⟩ :=
    StepStar.shapeStable_eitherCodeGeneral leftChain firstType secondType rfl
  obtain ⟨_rightFirst, _rightSecond, rightCommonEq, rightFirstStar, rightSecondStar⟩ :=
    StepStar.shapeStable_eitherCodeGeneral rightChain firstType' secondType' rfl
  rw [leftCommonEq] at rightCommonEq
  obtain ⟨firstAgree, secondAgree⟩ := eitherCodeCell_inj rightCommonEq
  refine ⟨⟨leftFirst, leftFirstStar, ?_⟩, ⟨leftSecond, leftSecondStar, ?_⟩⟩
  · rw [firstAgree]; exact rightFirstStar
  · rw [secondAgree]; exact rightSecondStar

/-- **eitherCode `Conv`-congruence** (the ← direction). -/
theorem Conv.eitherCode_cong {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope}
    (firstConv : Conv firstType firstType') (secondConv : Conv secondType secondType') :
    Conv (.mkGen .gen_eitherCode () (.childCons firstType (.childCons secondType .childNil)))
      (.mkGen .gen_eitherCode () (.childCons firstType' (.childCons secondType' .childNil))) :=
  Conv.ofChildren (ConvChildren.consC firstConv (ConvChildren.consC secondConv ConvChildren.nilC))

/-- **The eitherCode `Conv` structural characterization.** -/
theorem Conv.eitherCode_iff {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope} :
    Conv (.mkGen .gen_eitherCode () (.childCons firstType (.childCons secondType .childNil)))
        (.mkGen .gen_eitherCode () (.childCons firstType' (.childCons secondType' .childNil)))
      ↔ Conv firstType firstType' ∧ Conv secondType secondType' :=
  ⟨Conv.eitherCode_inj, fun ⟨firstConv, secondConv⟩ => Conv.eitherCode_cong firstConv secondConv⟩

/-! ## equivCode (the equivalence-type former `A ~= B`) -/

/-- Head-stability for `equivCode` under `StepStar`. -/
theorem StepStar.shapeStable_equivCodeGeneral {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) :
    ∀ (firstType secondType : RawTerm scope),
      source = (.mkGen .gen_equivCode () (.childCons firstType (.childCons secondType .childNil))) →
      ∃ (firstAfter secondAfter : RawTerm scope),
        target = (.mkGen .gen_equivCode () (.childCons firstAfter (.childCons secondAfter .childNil))) ∧
        StepStar firstType firstAfter ∧ StepStar secondType secondAfter := by
  induction chain with
  | refl _term =>
      intro firstType secondType sourceEq
      exact ⟨firstType, secondType, sourceEq, StepStar.refl _, StepStar.refl _⟩
  | trans headStep _tail tailIH =>
      intro firstType secondType sourceEq
      subst sourceEq
      rcases Step.from_equivCode headStep with
        ⟨firstAfter, midEq, firstStep⟩ | ⟨secondAfter, midEq, secondStep⟩
      · obtain ⟨fFinal, sFinal, targetEq, firstStar, secondStar⟩ :=
          tailIH firstAfter secondType midEq
        exact ⟨fFinal, sFinal, targetEq, StepStar.trans firstStep firstStar, secondStar⟩
      · obtain ⟨fFinal, sFinal, targetEq, firstStar, secondStar⟩ :=
          tailIH firstType secondAfter midEq
        exact ⟨fFinal, sFinal, targetEq, firstStar, StepStar.trans secondStep secondStar⟩

/-- The raw `equivCode` cell is injective. -/
theorem equivCodeCell_inj {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope}
    (cellsEqual :
      (.mkGen .gen_equivCode () (.childCons firstType (.childCons secondType .childNil)) : RawTerm scope)
        = .mkGen .gen_equivCode () (.childCons firstType' (.childCons secondType' .childNil))) :
    firstType = firstType' ∧ secondType = secondType' := by
  cases cellsEqual
  exact ⟨rfl, rfl⟩

/-- **equivCode `Conv`-injectivity** (SN-free). -/
theorem Conv.equivCode_inj {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope}
    (convertibility :
      Conv (.mkGen .gen_equivCode () (.childCons firstType (.childCons secondType .childNil)))
        (.mkGen .gen_equivCode () (.childCons firstType' (.childCons secondType' .childNil)))) :
    Conv firstType firstType' ∧ Conv secondType secondType' := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨leftFirst, leftSecond, leftCommonEq, leftFirstStar, leftSecondStar⟩ :=
    StepStar.shapeStable_equivCodeGeneral leftChain firstType secondType rfl
  obtain ⟨_rightFirst, _rightSecond, rightCommonEq, rightFirstStar, rightSecondStar⟩ :=
    StepStar.shapeStable_equivCodeGeneral rightChain firstType' secondType' rfl
  rw [leftCommonEq] at rightCommonEq
  obtain ⟨firstAgree, secondAgree⟩ := equivCodeCell_inj rightCommonEq
  refine ⟨⟨leftFirst, leftFirstStar, ?_⟩, ⟨leftSecond, leftSecondStar, ?_⟩⟩
  · rw [firstAgree]; exact rightFirstStar
  · rw [secondAgree]; exact rightSecondStar

/-- **equivCode `Conv`-congruence** (the ← direction). -/
theorem Conv.equivCode_cong {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope}
    (firstConv : Conv firstType firstType') (secondConv : Conv secondType secondType') :
    Conv (.mkGen .gen_equivCode () (.childCons firstType (.childCons secondType .childNil)))
      (.mkGen .gen_equivCode () (.childCons firstType' (.childCons secondType' .childNil))) :=
  Conv.ofChildren (ConvChildren.consC firstConv (ConvChildren.consC secondConv ConvChildren.nilC))

/-- **The equivCode `Conv` structural characterization.** -/
theorem Conv.equivCode_iff {scope : Nat}
    {firstType firstType' secondType secondType' : RawTerm scope} :
    Conv (.mkGen .gen_equivCode () (.childCons firstType (.childCons secondType .childNil)))
        (.mkGen .gen_equivCode () (.childCons firstType' (.childCons secondType' .childNil)))
      ↔ Conv firstType firstType' ∧ Conv secondType secondType' :=
  ⟨Conv.equivCode_inj, fun ⟨firstConv, secondConv⟩ => Conv.equivCode_cong firstConv secondConv⟩

end FX1Poly.Typed

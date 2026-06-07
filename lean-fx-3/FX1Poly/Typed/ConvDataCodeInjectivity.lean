import FX1Poly.Typed.ConvFlatCodeInjectivity
import FX1Poly.Core.StrongNormalizationCodeFormers

/-! # FX1Poly/Typed/ConvDataCodeInjectivity — `Conv` structural characterization for the UNARY
    (list/option) and TERNARY (id) data type-code formers, proved SN-FREE.

This COMPLETES the `Conv`-injectivity coverage of the type-code formers.  `ConvCodeInjectivity.lean`
shipped the DEPENDENT binary formers Π/Σ (#865/866); `ConvFlatCodeInjectivity.lean` shipped the five FLAT
binary data formers arrow/product/sum/either/equiv (#947).  This file ships the remaining arities:

  * the UNARY (one-child) data formers `listCode` and `optionCode` — `List A` and `Option A`;
  * the TERNARY (three-child) identity-type former `idCode` — `Id A x y` (a type code `A` and two terms
    `x`, `y`).

Together with the binary files, every congruence-only type-code former now has its `Conv`-injectivity
+ congruence + iff structural characterization.  (The `universeCode` leaf is handled separately by
`universeCodeCell_inj_of_conv` in `KnownUnsoundnessCorpus`, since it has no children.)

`Conv (listCode A) (listCode A') ↔ Conv A A'`; `Conv (idCode A x y) (idCode A' x' y') ↔ Conv A A' ∧
Conv x x' ∧ Conv y y'`; and the `optionCode` twin.  The INJECTIVITY direction is the inversion ingredient
typed metatheory consumes; the CONGRUENCE direction is the `Conv.ofChildren` lift.

## Why this is SN-free (same crack as the binary versions)

`Conv` is `StepStar.Join`.  Each `gen_*Code` here is a CONGRUENCE-ONLY former: a `Step` out of it reduces
exactly one child (`Step.from_listCode` / `from_optionCode` / `from_idCode` in
`StrongNormalizationCodeFormers.lean`).  So the head is STABLE under `StepStar` — a code only ever reduces
to the SAME code with reduced children.  Two joinable codes share a common reduct, and componentwise
joinability (= `Conv` on the components) drops out.  No confluence, no strong normalization, no
`Conv.trans` — just head-stability + the `Join` definition.

## Zero-axiom

`Step.from_<former>` + `StepStar` induction + the `Join` unpack + `cases`-form cell injectivity +
`Conv.ofChildren`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## listCode (the list-type former `List A`) — one child -/

/-- Subject-generalised head-stability for `listCode` under `StepStar`: a reduction sequence out of a
list code preserves the `gen_listCode` head, reducing the single element child. -/
theorem StepStar.shapeStable_listCodeGeneral {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) :
    ∀ (elementCode : RawTerm scope),
      source = (.mkGen .gen_listCode () (.childCons elementCode .childNil)) →
      ∃ (elementAfter : RawTerm scope),
        target = (.mkGen .gen_listCode () (.childCons elementAfter .childNil)) ∧
        StepStar elementCode elementAfter := by
  induction chain with
  | refl _term =>
      intro elementCode sourceEq
      exact ⟨elementCode, sourceEq, StepStar.refl _⟩
  | trans headStep _tail tailIH =>
      intro elementCode sourceEq
      subst sourceEq
      obtain ⟨elementAfter, midEq, elementStep⟩ := Step.from_listCode headStep
      obtain ⟨elementFinal, targetEq, elementStar⟩ := tailIH elementAfter midEq
      exact ⟨elementFinal, targetEq, StepStar.trans elementStep elementStar⟩

/-- The raw `listCode` cell is injective. -/
theorem listCodeCell_inj {scope : Nat} {elementCode elementCode' : RawTerm scope}
    (cellsEqual :
      (.mkGen .gen_listCode () (.childCons elementCode .childNil) : RawTerm scope)
        = .mkGen .gen_listCode () (.childCons elementCode' .childNil)) :
    elementCode = elementCode' := by
  cases cellsEqual
  rfl

/-- **listCode `Conv`-injectivity** (SN-free): convertible list codes have convertible elements. -/
theorem Conv.listCode_inj {scope : Nat} {elementCode elementCode' : RawTerm scope}
    (convertibility :
      Conv (.mkGen .gen_listCode () (.childCons elementCode .childNil))
        (.mkGen .gen_listCode () (.childCons elementCode' .childNil))) :
    Conv elementCode elementCode' := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨leftElement, leftCommonEq, leftElementStar⟩ :=
    StepStar.shapeStable_listCodeGeneral leftChain elementCode rfl
  obtain ⟨_rightElement, rightCommonEq, rightElementStar⟩ :=
    StepStar.shapeStable_listCodeGeneral rightChain elementCode' rfl
  rw [leftCommonEq] at rightCommonEq
  rw [listCodeCell_inj rightCommonEq] at leftElementStar
  exact ⟨_, leftElementStar, rightElementStar⟩

/-- **listCode `Conv`-congruence** (the ← direction). -/
theorem Conv.listCode_cong {scope : Nat} {elementCode elementCode' : RawTerm scope}
    (elementConv : Conv elementCode elementCode') :
    Conv (.mkGen .gen_listCode () (.childCons elementCode .childNil))
      (.mkGen .gen_listCode () (.childCons elementCode' .childNil)) :=
  Conv.ofChildren (ConvChildren.consC elementConv ConvChildren.nilC)

/-- **The listCode `Conv` structural characterization.** -/
theorem Conv.listCode_iff {scope : Nat} {elementCode elementCode' : RawTerm scope} :
    Conv (.mkGen .gen_listCode () (.childCons elementCode .childNil))
        (.mkGen .gen_listCode () (.childCons elementCode' .childNil))
      ↔ Conv elementCode elementCode' :=
  ⟨Conv.listCode_inj, Conv.listCode_cong⟩

/-! ## optionCode (the option-type former `Option A`) — one child -/

/-- Head-stability for `optionCode` under `StepStar`. -/
theorem StepStar.shapeStable_optionCodeGeneral {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) :
    ∀ (elementCode : RawTerm scope),
      source = (.mkGen .gen_optionCode () (.childCons elementCode .childNil)) →
      ∃ (elementAfter : RawTerm scope),
        target = (.mkGen .gen_optionCode () (.childCons elementAfter .childNil)) ∧
        StepStar elementCode elementAfter := by
  induction chain with
  | refl _term =>
      intro elementCode sourceEq
      exact ⟨elementCode, sourceEq, StepStar.refl _⟩
  | trans headStep _tail tailIH =>
      intro elementCode sourceEq
      subst sourceEq
      obtain ⟨elementAfter, midEq, elementStep⟩ := Step.from_optionCode headStep
      obtain ⟨elementFinal, targetEq, elementStar⟩ := tailIH elementAfter midEq
      exact ⟨elementFinal, targetEq, StepStar.trans elementStep elementStar⟩

/-- The raw `optionCode` cell is injective. -/
theorem optionCodeCell_inj {scope : Nat} {elementCode elementCode' : RawTerm scope}
    (cellsEqual :
      (.mkGen .gen_optionCode () (.childCons elementCode .childNil) : RawTerm scope)
        = .mkGen .gen_optionCode () (.childCons elementCode' .childNil)) :
    elementCode = elementCode' := by
  cases cellsEqual
  rfl

/-- **optionCode `Conv`-injectivity** (SN-free). -/
theorem Conv.optionCode_inj {scope : Nat} {elementCode elementCode' : RawTerm scope}
    (convertibility :
      Conv (.mkGen .gen_optionCode () (.childCons elementCode .childNil))
        (.mkGen .gen_optionCode () (.childCons elementCode' .childNil))) :
    Conv elementCode elementCode' := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨leftElement, leftCommonEq, leftElementStar⟩ :=
    StepStar.shapeStable_optionCodeGeneral leftChain elementCode rfl
  obtain ⟨_rightElement, rightCommonEq, rightElementStar⟩ :=
    StepStar.shapeStable_optionCodeGeneral rightChain elementCode' rfl
  rw [leftCommonEq] at rightCommonEq
  rw [optionCodeCell_inj rightCommonEq] at leftElementStar
  exact ⟨_, leftElementStar, rightElementStar⟩

/-- **optionCode `Conv`-congruence** (the ← direction). -/
theorem Conv.optionCode_cong {scope : Nat} {elementCode elementCode' : RawTerm scope}
    (elementConv : Conv elementCode elementCode') :
    Conv (.mkGen .gen_optionCode () (.childCons elementCode .childNil))
      (.mkGen .gen_optionCode () (.childCons elementCode' .childNil)) :=
  Conv.ofChildren (ConvChildren.consC elementConv ConvChildren.nilC)

/-- **The optionCode `Conv` structural characterization.** -/
theorem Conv.optionCode_iff {scope : Nat} {elementCode elementCode' : RawTerm scope} :
    Conv (.mkGen .gen_optionCode () (.childCons elementCode .childNil))
        (.mkGen .gen_optionCode () (.childCons elementCode' .childNil))
      ↔ Conv elementCode elementCode' :=
  ⟨Conv.optionCode_inj, Conv.optionCode_cong⟩

/-! ## idCode (the identity-type former `Id A x y`) — three children (one type, two terms) -/

/-- Subject-generalised head-stability for `idCode` under `StepStar`: a reduction sequence out of an
identity code preserves the `gen_idCode` head, reducing the three same-scope children pointwise. -/
theorem StepStar.shapeStable_idCodeGeneral {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) :
    ∀ (typeCode leftTerm rightTerm : RawTerm scope),
      source = (.mkGen .gen_idCode ()
        (.childCons typeCode (.childCons leftTerm (.childCons rightTerm .childNil)))) →
      ∃ (typeAfter leftAfter rightAfter : RawTerm scope),
        target = (.mkGen .gen_idCode ()
          (.childCons typeAfter (.childCons leftAfter (.childCons rightAfter .childNil)))) ∧
        StepStar typeCode typeAfter ∧ StepStar leftTerm leftAfter ∧ StepStar rightTerm rightAfter := by
  induction chain with
  | refl _term =>
      intro typeCode leftTerm rightTerm sourceEq
      exact ⟨typeCode, leftTerm, rightTerm, sourceEq,
        StepStar.refl _, StepStar.refl _, StepStar.refl _⟩
  | trans headStep _tail tailIH =>
      intro typeCode leftTerm rightTerm sourceEq
      subst sourceEq
      rcases Step.from_idCode headStep with
        ⟨typeAfter, midEq, typeStep⟩ | ⟨leftAfter, midEq, leftStep⟩ | ⟨rightAfter, midEq, rightStep⟩
      · obtain ⟨tFinal, lFinal, rFinal, targetEq, tStar, lStar, rStar⟩ :=
          tailIH typeAfter leftTerm rightTerm midEq
        exact ⟨tFinal, lFinal, rFinal, targetEq, StepStar.trans typeStep tStar, lStar, rStar⟩
      · obtain ⟨tFinal, lFinal, rFinal, targetEq, tStar, lStar, rStar⟩ :=
          tailIH typeCode leftAfter rightTerm midEq
        exact ⟨tFinal, lFinal, rFinal, targetEq, tStar, StepStar.trans leftStep lStar, rStar⟩
      · obtain ⟨tFinal, lFinal, rFinal, targetEq, tStar, lStar, rStar⟩ :=
          tailIH typeCode leftTerm rightAfter midEq
        exact ⟨tFinal, lFinal, rFinal, targetEq, tStar, lStar, StepStar.trans rightStep rStar⟩

/-- The raw `idCode` cell is injective. -/
theorem idCodeCell_inj {scope : Nat}
    {typeCode typeCode' leftTerm leftTerm' rightTerm rightTerm' : RawTerm scope}
    (cellsEqual :
      (.mkGen .gen_idCode () (.childCons typeCode (.childCons leftTerm (.childCons rightTerm .childNil)))
        : RawTerm scope)
        = .mkGen .gen_idCode ()
            (.childCons typeCode' (.childCons leftTerm' (.childCons rightTerm' .childNil)))) :
    typeCode = typeCode' ∧ leftTerm = leftTerm' ∧ rightTerm = rightTerm' := by
  cases cellsEqual
  exact ⟨rfl, rfl, rfl⟩

/-- **idCode `Conv`-injectivity** (SN-free): convertible identity codes have convertible type and both
endpoint terms. -/
theorem Conv.idCode_inj {scope : Nat}
    {typeCode typeCode' leftTerm leftTerm' rightTerm rightTerm' : RawTerm scope}
    (convertibility :
      Conv (.mkGen .gen_idCode ()
          (.childCons typeCode (.childCons leftTerm (.childCons rightTerm .childNil))))
        (.mkGen .gen_idCode ()
          (.childCons typeCode' (.childCons leftTerm' (.childCons rightTerm' .childNil))))) :
    Conv typeCode typeCode' ∧ Conv leftTerm leftTerm' ∧ Conv rightTerm rightTerm' := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨leftType, leftLeft, leftRight, leftCommonEq, leftTypeStar, leftLeftStar, leftRightStar⟩ :=
    StepStar.shapeStable_idCodeGeneral leftChain typeCode leftTerm rightTerm rfl
  obtain ⟨_rightType, _rightLeft, _rightRight, rightCommonEq,
      rightTypeStar, rightLeftStar, rightRightStar⟩ :=
    StepStar.shapeStable_idCodeGeneral rightChain typeCode' leftTerm' rightTerm' rfl
  rw [leftCommonEq] at rightCommonEq
  obtain ⟨typeAgree, leftAgree, rightAgree⟩ := idCodeCell_inj rightCommonEq
  refine ⟨⟨leftType, leftTypeStar, ?_⟩, ⟨leftLeft, leftLeftStar, ?_⟩, ⟨leftRight, leftRightStar, ?_⟩⟩
  · rw [typeAgree]; exact rightTypeStar
  · rw [leftAgree]; exact rightLeftStar
  · rw [rightAgree]; exact rightRightStar

/-- **idCode `Conv`-congruence** (the ← direction). -/
theorem Conv.idCode_cong {scope : Nat}
    {typeCode typeCode' leftTerm leftTerm' rightTerm rightTerm' : RawTerm scope}
    (typeConv : Conv typeCode typeCode') (leftConv : Conv leftTerm leftTerm')
    (rightConv : Conv rightTerm rightTerm') :
    Conv (.mkGen .gen_idCode ()
        (.childCons typeCode (.childCons leftTerm (.childCons rightTerm .childNil))))
      (.mkGen .gen_idCode ()
        (.childCons typeCode' (.childCons leftTerm' (.childCons rightTerm' .childNil)))) :=
  Conv.ofChildren
    (ConvChildren.consC typeConv (ConvChildren.consC leftConv (ConvChildren.consC rightConv ConvChildren.nilC)))

/-- **The idCode `Conv` structural characterization.** -/
theorem Conv.idCode_iff {scope : Nat}
    {typeCode typeCode' leftTerm leftTerm' rightTerm rightTerm' : RawTerm scope} :
    Conv (.mkGen .gen_idCode ()
        (.childCons typeCode (.childCons leftTerm (.childCons rightTerm .childNil))))
        (.mkGen .gen_idCode ()
          (.childCons typeCode' (.childCons leftTerm' (.childCons rightTerm' .childNil))))
      ↔ Conv typeCode typeCode' ∧ Conv leftTerm leftTerm' ∧ Conv rightTerm rightTerm' :=
  ⟨Conv.idCode_inj,
    fun ⟨typeConv, leftConv, rightConv⟩ => Conv.idCode_cong typeConv leftConv rightConv⟩

end FX1Poly.Typed

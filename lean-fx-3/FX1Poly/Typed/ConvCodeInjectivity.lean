import FX1Poly.Typed.UniverseCodeShape
import FX1Poly.Core.ConvCongruence

/-! # FX1Poly/Typed/ConvCodeInjectivity — the Π/Σ-CODE `Conv` structural characterization
    (injectivity + congruence), proved SN-FREE.

`Conv (piTyCodeCell A B) (piTyCodeCell A' B') ↔ Conv A A' ∧ Conv B B'` (and the Σ dual).  This is
the decidable-`Conv` STRUCTURAL RECURSION for the dependent type-code formers — and the INJECTIVITY
direction is precisely the ingredient typed subject reduction needs to relate the codomain of a
conv-disguised Π-type to the actual codomain.

## Why this is SN-free (the crack)

`Conv` is `StepStar.Join` — joinability via a common reduct (`StepStarConfluence`).  And
`gen_piTyCode` is NOT a redex root: a `Step` out of a `piTyCodeCell` can only be a child
CONGRUENCE (the `cong` arm; `beta`/`iota` fire on other heads), as `Step.from_piTyCode` already
witnesses.  Hence a `piTyCodeCell`'s head is STABLE under `StepStar` — it only ever reduces to
another `piTyCodeCell` with reduced children (`StepStar.shapeStable_piTyCode`).  Two joinable Π-codes
therefore share a `piTyCodeCell` common reduct, and componentwise joinability (= `Conv` on the
components) drops out.  No confluence, no strong normalization, no `Conv.trans` — just head-stability
+ the `Join` definition.

(The FULLY-GENERAL inverted β subject reduction additionally needs `Conv.trans` to compose a
conversion chain, which IS gated on confluence/SN — a separate obligation.  This file delivers the
injectivity ingredient that obligation will consume, plus the standalone decidable-`Conv` recursion.)

## Contents

* `StepStar.shapeStable_piTyCode` / `…_sigmaTyCode` — head-stability under reduction: a `StepStar`
  out of a type code lands on a type code with the same head and `StepStar`-reduced children.
* `sigmaTyCodeCell_inj` — the Σ cell is injective (the Π version `piTyCodeCell_inj` is in
  `UniverseCodeShape`).
* `Conv.piTyCode_inj` / `…_sigmaTyCode_inj` — `Conv`-injectivity (the → direction), the SR ingredient.
* `Conv.piTyCode_cong` / `…_sigmaTyCode_cong` — `Conv`-congruence (the ← direction) via `ofChildren`.
* `Conv.piTyCode_iff` / `…_sigmaTyCode_iff` — the structural characterization.

## Zero-axiom

`Step.from_piTyCode` + `StepStar` induction + the `Join` unpack + `cases`-form cell injectivity +
`Conv.ofChildren`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- The `sigmaTyCodeCell` cell is injective — the Σ dual of `piTyCodeCell_inj` (in
`UniverseCodeShape`).  `cases` on the cell equality unifies the spines (the propext-free route; raw
`injection` surfaces the dependent `childCons` scope index). -/
theorem sigmaTyCodeCell_inj {scope : Nat}
    {firstDomain secondDomain : RawTerm scope}
    {firstCodomain secondCodomain : RawTerm (scope + 1)}
    (cellsEqual :
      sigmaTyCodeCell firstDomain firstCodomain
        = sigmaTyCodeCell secondDomain secondCodomain) :
    firstDomain = secondDomain ∧ firstCodomain = secondCodomain := by
  cases cellsEqual
  exact ⟨rfl, rfl⟩

/-- Subject-generalised head-stability for `piTyCodeCell` under `StepStar`: a reduction sequence out
of a Π-code preserves the `gen_piTyCode` head, reducing the two children pointwise. -/
theorem StepStar.shapeStable_piTyCodeGeneral {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) :
    ∀ (domain : RawTerm scope) (codomain : RawTerm (scope + 1)),
      source = piTyCodeCell domain codomain →
      ∃ (domainAfter : RawTerm scope) (codomainAfter : RawTerm (scope + 1)),
        target = piTyCodeCell domainAfter codomainAfter ∧
        StepStar domain domainAfter ∧ StepStar codomain codomainAfter := by
  induction chain with
  | refl _term =>
      intro domain codomain sourceEq
      exact ⟨domain, codomain, sourceEq, StepStar.refl _, StepStar.refl _⟩
  | trans headStep _tail tailIH =>
      intro domain codomain sourceEq
      subst sourceEq
      rcases Step.from_piTyCode headStep with
        ⟨domainAfter, midEq, domainStep⟩ | ⟨codomainAfter, midEq, codomainStep⟩
      · obtain ⟨dFinal, cFinal, targetEq, domainStar, codomainStar⟩ :=
          tailIH domainAfter codomain midEq
        exact ⟨dFinal, cFinal, targetEq, StepStar.trans domainStep domainStar, codomainStar⟩
      · obtain ⟨dFinal, cFinal, targetEq, domainStar, codomainStar⟩ :=
          tailIH domain codomainAfter midEq
        exact ⟨dFinal, cFinal, targetEq, domainStar, StepStar.trans codomainStep codomainStar⟩

/-- Head-stability for `piTyCodeCell` under `StepStar` (the wrapper). -/
theorem StepStar.shapeStable_piTyCode {scope : Nat}
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)} {target : RawTerm scope}
    (chain : StepStar (piTyCodeCell domain codomain) target) :
    ∃ (domainAfter : RawTerm scope) (codomainAfter : RawTerm (scope + 1)),
      target = piTyCodeCell domainAfter codomainAfter ∧
      StepStar domain domainAfter ∧ StepStar codomain codomainAfter :=
  StepStar.shapeStable_piTyCodeGeneral chain domain codomain rfl

/-- Subject-generalised head-stability for `sigmaTyCodeCell` under `StepStar` — the Σ dual. -/
theorem StepStar.shapeStable_sigmaTyCodeGeneral {scope : Nat} {source target : RawTerm scope}
    (chain : StepStar source target) :
    ∀ (domain : RawTerm scope) (codomain : RawTerm (scope + 1)),
      source = sigmaTyCodeCell domain codomain →
      ∃ (domainAfter : RawTerm scope) (codomainAfter : RawTerm (scope + 1)),
        target = sigmaTyCodeCell domainAfter codomainAfter ∧
        StepStar domain domainAfter ∧ StepStar codomain codomainAfter := by
  induction chain with
  | refl _term =>
      intro domain codomain sourceEq
      exact ⟨domain, codomain, sourceEq, StepStar.refl _, StepStar.refl _⟩
  | trans headStep _tail tailIH =>
      intro domain codomain sourceEq
      subst sourceEq
      rcases Step.from_sigmaTyCode headStep with
        ⟨domainAfter, midEq, domainStep⟩ | ⟨codomainAfter, midEq, codomainStep⟩
      · obtain ⟨dFinal, cFinal, targetEq, domainStar, codomainStar⟩ :=
          tailIH domainAfter codomain midEq
        exact ⟨dFinal, cFinal, targetEq, StepStar.trans domainStep domainStar, codomainStar⟩
      · obtain ⟨dFinal, cFinal, targetEq, domainStar, codomainStar⟩ :=
          tailIH domain codomainAfter midEq
        exact ⟨dFinal, cFinal, targetEq, domainStar, StepStar.trans codomainStep codomainStar⟩

/-- Head-stability for `sigmaTyCodeCell` under `StepStar` (the wrapper). -/
theorem StepStar.shapeStable_sigmaTyCode {scope : Nat}
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)} {target : RawTerm scope}
    (chain : StepStar (sigmaTyCodeCell domain codomain) target) :
    ∃ (domainAfter : RawTerm scope) (codomainAfter : RawTerm (scope + 1)),
      target = sigmaTyCodeCell domainAfter codomainAfter ∧
      StepStar domain domainAfter ∧ StepStar codomain codomainAfter :=
  StepStar.shapeStable_sigmaTyCodeGeneral chain domain codomain rfl

/-- **Π-code `Conv`-injectivity** (SN-free): convertible Π-codes have convertible domains and
codomains.  Both sides reduce to a SHARED `piTyCodeCell` common reduct (head-stability), and the
componentwise reducts join the components.  The ingredient typed SR consumes to peel a conv-disguised
Π-type. -/
theorem Conv.piTyCode_inj {scope : Nat}
    {domain domain' : RawTerm scope} {codomain codomain' : RawTerm (scope + 1)}
    (convertibility :
      Conv (piTyCodeCell domain codomain) (piTyCodeCell domain' codomain')) :
    Conv domain domain' ∧ Conv codomain codomain' := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨leftDomain, leftCodomain, leftCommonEq, leftDomainStar, leftCodomainStar⟩ :=
    StepStar.shapeStable_piTyCode leftChain
  obtain ⟨_rightDomain, _rightCodomain, rightCommonEq, rightDomainStar, rightCodomainStar⟩ :=
    StepStar.shapeStable_piTyCode rightChain
  rw [leftCommonEq] at rightCommonEq
  obtain ⟨domainsAgree, codomainsAgree⟩ := piTyCodeCell_inj rightCommonEq
  refine ⟨⟨leftDomain, leftDomainStar, ?_⟩, ⟨leftCodomain, leftCodomainStar, ?_⟩⟩
  · rw [domainsAgree]; exact rightDomainStar
  · rw [codomainsAgree]; exact rightCodomainStar

/-- **Σ-code `Conv`-injectivity** — the Σ dual of `Conv.piTyCode_inj`. -/
theorem Conv.sigmaTyCode_inj {scope : Nat}
    {domain domain' : RawTerm scope} {codomain codomain' : RawTerm (scope + 1)}
    (convertibility :
      Conv (sigmaTyCodeCell domain codomain) (sigmaTyCodeCell domain' codomain')) :
    Conv domain domain' ∧ Conv codomain codomain' := by
  obtain ⟨_commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨leftDomain, leftCodomain, leftCommonEq, leftDomainStar, leftCodomainStar⟩ :=
    StepStar.shapeStable_sigmaTyCode leftChain
  obtain ⟨_rightDomain, _rightCodomain, rightCommonEq, rightDomainStar, rightCodomainStar⟩ :=
    StepStar.shapeStable_sigmaTyCode rightChain
  rw [leftCommonEq] at rightCommonEq
  obtain ⟨domainsAgree, codomainsAgree⟩ := sigmaTyCodeCell_inj rightCommonEq
  refine ⟨⟨leftDomain, leftDomainStar, ?_⟩, ⟨leftCodomain, leftCodomainStar, ?_⟩⟩
  · rw [domainsAgree]; exact rightDomainStar
  · rw [codomainsAgree]; exact rightCodomainStar

/-- **Π-code `Conv`-congruence** (the ← direction): convertible components give convertible Π-codes.
A `Conv.ofChildren` lift over the two-child `gen_piTyCode` spine. -/
theorem Conv.piTyCode_cong {scope : Nat}
    {domain domain' : RawTerm scope} {codomain codomain' : RawTerm (scope + 1)}
    (domainConv : Conv domain domain') (codomainConv : Conv codomain codomain') :
    Conv (piTyCodeCell domain codomain) (piTyCodeCell domain' codomain') :=
  Conv.ofChildren (ConvChildren.consC domainConv (ConvChildren.consC codomainConv ConvChildren.nilC))

/-- **Σ-code `Conv`-congruence** — the Σ dual of `Conv.piTyCode_cong`. -/
theorem Conv.sigmaTyCode_cong {scope : Nat}
    {domain domain' : RawTerm scope} {codomain codomain' : RawTerm (scope + 1)}
    (domainConv : Conv domain domain') (codomainConv : Conv codomain codomain') :
    Conv (sigmaTyCodeCell domain codomain) (sigmaTyCodeCell domain' codomain') :=
  Conv.ofChildren (ConvChildren.consC domainConv (ConvChildren.consC codomainConv ConvChildren.nilC))

/-- **The Π-code `Conv` structural characterization**: a Π-code conversion holds iff both components
convert.  The decidable-`Conv` recursion for the dependent function-type former, SN-free. -/
theorem Conv.piTyCode_iff {scope : Nat}
    {domain domain' : RawTerm scope} {codomain codomain' : RawTerm (scope + 1)} :
    Conv (piTyCodeCell domain codomain) (piTyCodeCell domain' codomain')
      ↔ Conv domain domain' ∧ Conv codomain codomain' :=
  ⟨Conv.piTyCode_inj, fun ⟨domainConv, codomainConv⟩ => Conv.piTyCode_cong domainConv codomainConv⟩

/-- **The Σ-code `Conv` structural characterization** — the Σ dual of `Conv.piTyCode_iff`. -/
theorem Conv.sigmaTyCode_iff {scope : Nat}
    {domain domain' : RawTerm scope} {codomain codomain' : RawTerm (scope + 1)} :
    Conv (sigmaTyCodeCell domain codomain) (sigmaTyCodeCell domain' codomain')
      ↔ Conv domain domain' ∧ Conv codomain codomain' :=
  ⟨Conv.sigmaTyCode_inj,
    fun ⟨domainConv, codomainConv⟩ => Conv.sigmaTyCode_cong domainConv codomainConv⟩

end FX1Poly.Typed

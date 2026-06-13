import FX1Poly.Core.StrongNormalizationConstructors
import FX1Poly.Core.StepTable

/-! # FX1Poly/Core/StrongNormalizationCodeFormers
    — structural SN closure for the remaining universe-code formers

`StrongNormalizationConstructors.lean` ships the congruence-only structural strong-normalization closures for
the two-child universe-code formers (`arrowCode`, `productCode`, `sumCode`, `eitherCode`, `equivCode`,
`piTyCode`, `sigmaTyCode`, `polyFunctor`) via `isStronglyNormalizing_of_twoChildCong`, and for the one-child
constructors via `isStronglyNormalizing_of_oneChildCong`.  Three further universe-code formers are covered
here:

* `gen_listCode` — one child (the element type code);
* `gen_optionCode` — one child (the element type code);
* `gen_idCode` — three children (the type code, and the two endpoint raw terms).

This file completes the universe-code family.  The two one-child formers reuse the shipped
`isStronglyNormalizing_of_oneChildCong`; `idCode` is the FIRST three-child pure-former, so it needs a new
reusable combinator `isStronglyNormalizing_of_threeChildCong` — the three-child analogue of the shipped
one/two-child congruence closures.  All are the SN-half ingredient of "the code is a reducible member of `El`";
SN is a fuel-independent raw property, so none of this touches the stratified reducibility candidate
or the universe-domain-Π fundamental theorem (the open crux).

Each former is congruence-only: `gen_listCode` / `gen_optionCode` / `gen_idCode` are type-code formers, not
eliminators, so no `beta`/`iota` rule has them as the outer redex head — a `Step` out of the parent reduces
exactly one child.  The `Step.from_*` inversion lemmas (here) record exactly that, mirroring the shipped
one/two-child code inversions in `StepInversion.lean`.

## Zero-axiom verification

The inversions are `cases reduction` + nested `cases childStep` down the `StepChildren` spine, closing the
empty-spine tail with `StepChildren.no_step_at_empty_spine`; the combinator is a triple-nested `Acc.ndrec`
exactly as `isStronglyNormalizing_of_twoChildCong` is a double nest; the SN theorems are direct combinator
applications.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **Inversion for `listCode`-rooted Step.**  `gen_listCode` is a one-child type-code former (the element
code), congruence-only: a `Step` out of it reduces exactly the element child. -/
theorem Step.from_listCode
    {scope : Nat} {elementCode : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_listCode () (.childCons elementCode .childNil)) target) :
    ∃ (elementAfter : RawTerm scope),
      target = .mkGen .gen_listCode () (.childCons elementAfter .childNil) ∧
      Step elementCode elementAfter := by
  cases Step.weakHeadOrChildCong reduction with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨childrenAfter, targetEq, childStep⟩ := congShape
      cases childStep with
      | here _ elementStep =>
          rename_i elementAfter
          exact ⟨elementAfter, targetEq, elementStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `optionCode`-rooted Step.**  `gen_optionCode` is a one-child type-code former (the element
code), congruence-only. -/
theorem Step.from_optionCode
    {scope : Nat} {elementCode : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_optionCode () (.childCons elementCode .childNil)) target) :
    ∃ (elementAfter : RawTerm scope),
      target = .mkGen .gen_optionCode () (.childCons elementAfter .childNil) ∧
      Step elementCode elementAfter := by
  cases Step.weakHeadOrChildCong reduction with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨childrenAfter, targetEq, childStep⟩ := congShape
      cases childStep with
      | here _ elementStep =>
          rename_i elementAfter
          exact ⟨elementAfter, targetEq, elementStep⟩
      | there _ restStep =>
          exact absurd restStep StepChildren.no_step_at_empty_spine

/-- **Inversion for `idCode`-rooted Step.**  `gen_idCode` is a three-child type-code former (the type code,
and the two endpoint raw terms), congruence-only: a `Step` out of it reduces exactly one of the three children,
giving a three-way disjunction. -/
theorem Step.from_idCode
    {scope : Nat} {typeCode leftRaw rightRaw : RawTerm scope} {target : RawTerm scope}
    (reduction :
      Step (.mkGen .gen_idCode ()
              (.childCons typeCode (.childCons leftRaw (.childCons rightRaw .childNil))))
           target) :
    (∃ (typeAfter : RawTerm scope),
        target = .mkGen .gen_idCode ()
          (.childCons typeAfter (.childCons leftRaw (.childCons rightRaw .childNil))) ∧
        Step typeCode typeAfter)
    ∨ (∃ (leftAfter : RawTerm scope),
        target = .mkGen .gen_idCode ()
          (.childCons typeCode (.childCons leftAfter (.childCons rightRaw .childNil))) ∧
        Step leftRaw leftAfter)
    ∨ (∃ (rightAfter : RawTerm scope),
        target = .mkGen .gen_idCode ()
          (.childCons typeCode (.childCons leftRaw (.childCons rightAfter .childNil))) ∧
        Step rightRaw rightAfter) := by
  cases Step.weakHeadOrChildCong reduction with
  | inl weakHeadStep =>
      cases weakHeadStep with
      | rootIota iotaHead => cases iotaHead
  | inr congShape =>
      obtain ⟨childrenAfter, targetEq, childStep⟩ := congShape
      cases childStep with
      | here _ typeStep =>
          rename_i typeAfter
          exact Or.inl ⟨typeAfter, targetEq, typeStep⟩
      | there _ tailStep1 =>
          cases tailStep1 with
          | here _ leftStep =>
              rename_i leftAfter
              exact Or.inr (Or.inl ⟨leftAfter, targetEq, leftStep⟩)
          | there _ tailStep2 =>
              cases tailStep2 with
              | here _ rightStep =>
                  rename_i rightAfter
                  exact Or.inr (Or.inr ⟨rightAfter, targetEq, rightStep⟩)
              | there _ restStep =>
                  exact absurd restStep StepChildren.no_step_at_empty_spine

namespace StepStar

/-- If every parent step is exactly a step in one of three children, accessibility of all three children lifts
to accessibility of the wrapped parent.  The three-child analogue of `isStronglyNormalizing_of_oneChildCong` /
`isStronglyNormalizing_of_twoChildCong`: a triple-nested well-founded recursion, with the inner two children's
accessibility threaded through the motives.  In the `Acc.intro` step a parent reduction is inverted to a
one-of-three child step, and the corresponding child's induction hypothesis is applied (re-supplying the
other children's accessibility, which is in scope as the enclosing `Acc.intro` predecessor witnesses). -/
theorem isStronglyNormalizing_of_threeChildCong
    {firstScope secondScope thirdScope parentScope : Nat}
    (wrapParent :
      RawTerm firstScope → RawTerm secondScope → RawTerm thirdScope → RawTerm parentScope)
    (invertParentStep :
      ∀ {firstChild : RawTerm firstScope} {secondChild : RawTerm secondScope}
        {thirdChild : RawTerm thirdScope} {targetParent : RawTerm parentScope},
        Step (wrapParent firstChild secondChild thirdChild) targetParent →
          (∃ targetFirst : RawTerm firstScope,
            targetParent = wrapParent targetFirst secondChild thirdChild ∧
              Step firstChild targetFirst)
          ∨ (∃ targetSecond : RawTerm secondScope,
            targetParent = wrapParent firstChild targetSecond thirdChild ∧
              Step secondChild targetSecond)
          ∨ (∃ targetThird : RawTerm thirdScope,
            targetParent = wrapParent firstChild secondChild targetThird ∧
              Step thirdChild targetThird))
    {firstChild : RawTerm firstScope}
    (firstTerminates : IsStronglyNormalizing firstChild)
    {secondChild : RawTerm secondScope}
    (secondTerminates : IsStronglyNormalizing secondChild)
    {thirdChild : RawTerm thirdScope}
    (thirdTerminates : IsStronglyNormalizing thirdChild) :
    IsStronglyNormalizing (wrapParent firstChild secondChild thirdChild) :=
  (Acc.ndrec
    (r := StepSuccessor)
    (C := fun currentFirst =>
      ∀ {currentSecond : RawTerm secondScope} {currentThird : RawTerm thirdScope},
        IsStronglyNormalizing currentSecond → IsStronglyNormalizing currentThird →
          IsStronglyNormalizing (wrapParent currentFirst currentSecond currentThird))
    (m := fun currentFirst _ firstChildIH => by
      intro currentSecond currentThird currentSecondTerminates currentThirdTerminates
      exact
        (Acc.ndrec
          (r := StepSuccessor)
          (C := fun innerSecond =>
            ∀ {innerThird : RawTerm thirdScope},
              IsStronglyNormalizing innerThird →
                IsStronglyNormalizing (wrapParent currentFirst innerSecond innerThird))
          (m := fun midSecond midSecondSuccessors secondChildIH => by
            intro innerThird innerThirdTerminates
            exact
              Acc.ndrec
                (r := StepSuccessor)
                (C := fun innerThird =>
                  IsStronglyNormalizing (wrapParent currentFirst midSecond innerThird))
                (m := fun currentThirdValue currentThirdSuccessors thirdChildIH =>
                  Acc.intro (wrapParent currentFirst midSecond currentThirdValue)
                    (fun targetParent parentStep => by
                      rcases invertParentStep parentStep with
                        ⟨targetFirst, targetEq, firstStep⟩ |
                        ⟨targetSecond, targetEq, secondStep⟩ |
                        ⟨targetThird, targetEq, thirdStep⟩
                      · rw [targetEq]
                        exact firstChildIH targetFirst firstStep
                          (Acc.intro midSecond midSecondSuccessors)
                          (Acc.intro currentThirdValue currentThirdSuccessors)
                      · rw [targetEq]
                        exact secondChildIH targetSecond secondStep
                          (Acc.intro currentThirdValue currentThirdSuccessors)
                      · rw [targetEq]
                        exact thirdChildIH targetThird thirdStep))
                innerThirdTerminates)
          currentSecondTerminates)
        currentThirdTerminates)
    firstTerminates)
    secondTerminates
    thirdTerminates

/-- List type codes are strongly normalizing when their element type code is strongly normalizing. -/
theorem listCode_isStronglyNormalizing_of_element {scope : Nat}
    {elementCode : RawTerm scope}
    (elementTerminates : IsStronglyNormalizing elementCode) :
    IsStronglyNormalizing
      (.mkGen .gen_listCode () (.childCons elementCode .childNil) : RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope)
    (parentScope := scope)
    (fun currentElement =>
      (.mkGen .gen_listCode () (.childCons currentElement .childNil) : RawTerm scope))
    (fun parentStep => Step.from_listCode parentStep)
    elementTerminates

/-- Option type codes are strongly normalizing when their element type code is strongly normalizing. -/
theorem optionCode_isStronglyNormalizing_of_element {scope : Nat}
    {elementCode : RawTerm scope}
    (elementTerminates : IsStronglyNormalizing elementCode) :
    IsStronglyNormalizing
      (.mkGen .gen_optionCode () (.childCons elementCode .childNil) : RawTerm scope) :=
  isStronglyNormalizing_of_oneChildCong
    (childScope := scope)
    (parentScope := scope)
    (fun currentElement =>
      (.mkGen .gen_optionCode () (.childCons currentElement .childNil) : RawTerm scope))
    (fun parentStep => Step.from_optionCode parentStep)
    elementTerminates

/-- Identity type codes are strongly normalizing when their type code and both endpoint raw terms are strongly
normalizing.  The first three-child pure-former SN constructor, via `isStronglyNormalizing_of_threeChildCong`. -/
theorem idCode_isStronglyNormalizing_of_type_endpoints {scope : Nat}
    {typeCode leftRaw rightRaw : RawTerm scope}
    (typeTerminates : IsStronglyNormalizing typeCode)
    (leftTerminates : IsStronglyNormalizing leftRaw)
    (rightTerminates : IsStronglyNormalizing rightRaw) :
    IsStronglyNormalizing
      (.mkGen .gen_idCode ()
        (.childCons typeCode (.childCons leftRaw (.childCons rightRaw .childNil))) :
        RawTerm scope) :=
  isStronglyNormalizing_of_threeChildCong
    (firstScope := scope) (secondScope := scope) (thirdScope := scope) (parentScope := scope)
    (fun currentType currentLeft currentRight =>
      (.mkGen .gen_idCode ()
        (.childCons currentType (.childCons currentLeft (.childCons currentRight .childNil))) :
        RawTerm scope))
    (fun parentStep => Step.from_idCode parentStep)
    typeTerminates leftTerminates rightTerminates

end StepStar
end FX1Poly.Core

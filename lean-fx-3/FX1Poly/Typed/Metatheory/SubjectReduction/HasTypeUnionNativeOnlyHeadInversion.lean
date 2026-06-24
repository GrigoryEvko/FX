import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnlyAdmissibility
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionSubjectReduction

/-! # HasTypeUnionNativeOnlyHeadInversion — value-head inversion for the OFGROWN-FREE union (TYTAB-2 RETIRE)

The native-only (`ofGrown`-free) twins of the value-introducer head-inversion masters
(`HasTypeUnion.invertAtPairHead` / `invertAtOptionSomeHead` / `invertAtEitherInlHead` /
`invertAtEitherInrHead` / `invertAtListConsHead`).  Each kernel master is an `induction` over
`HasTypeUnion` whose tree includes the `ofGrown` host-embedding arm; the consistency / canonicity consumers
that call them must move onto the `ofGrown`-free judgment `HasTypeUnionNativeOnly` so that — once the arm is
physically retired (#1698) — nothing references it.

This file is the **rename-reflection layer**: every native-only inversion is the kernel master reflected
through the zero-axiom equivalence `HasTypeUnion.iff_nativeOnly` (forward `HasTypeUnionNativeOnly.toUnion`,
backward `HasTypeUnion.toNativeOnly` on each extracted sub-derivation).  No `ofGrown` constructor and no grown
master `HasTypeDescPi.subjectReduction` appears — the reflection routes purely through the admissibility
equivalence proving `ofGrown` redundant.  Consumers bind the STABLE native-only name; when `HasTypeUnion`'s
own proofs later swap from the host engine to a direct native induction (arm-deletion time), only the kernel
master changes, never these twins' call sites.

## Zero-axiom

A composition of the shipped `HasTypeUnionNativeOnly.toUnion`, `HasTypeUnion.toNativeOnly`, and the kernel
head-inversion masters (themselves zero-axiom).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **★ Native-only pair-head inversion.**  The `ofGrown`-free twin of `HasTypeUnion.invertAtPairHead`: a
native-only-typed `pairCell` is a product of native-only-typed components, the product type `Conv`-equal to
the classifier.  Reflected through the redundancy equivalence (`toUnion` in, `toNativeOnly` on each component
out). -/
theorem HasTypeUnionNativeOnly.invertAtPairHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {firstValue secondValue : RawTerm scope}
    (derivation : HasTypeUnionNativeOnly profile context subject classifier)
    (subjectShape : subject = pairCell firstValue secondValue) :
    ∃ firstType secondType : RawTerm scope,
      HasTypeUnionNativeOnly profile context firstValue firstType ∧
      HasTypeUnionNativeOnly profile context secondValue secondType ∧
      Conv (productTypeCell firstType secondType) classifier := by
  obtain ⟨firstType, secondType, firstTyped, secondTyped, converts⟩ :=
    HasTypeUnion.invertAtPairHead derivation.toUnion subjectShape
  exact ⟨firstType, secondType, firstTyped.toNativeOnly, secondTyped.toNativeOnly, converts⟩

/-- **★ Native-only option-Some-head inversion.**  The `ofGrown`-free twin of
`HasTypeUnion.invertAtOptionSomeHead`. -/
theorem HasTypeUnionNativeOnly.invertAtOptionSomeHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {payloadValue : RawTerm scope}
    (derivation : HasTypeUnionNativeOnly profile context subject classifier)
    (subjectShape : subject = optionSomeCell payloadValue) :
    ∃ payloadType : RawTerm scope,
      HasTypeUnionNativeOnly profile context payloadValue payloadType ∧
      Conv (optionTypeCell payloadType) classifier := by
  obtain ⟨payloadType, payloadTyped, converts⟩ :=
    HasTypeUnion.invertAtOptionSomeHead derivation.toUnion subjectShape
  exact ⟨payloadType, payloadTyped.toNativeOnly, converts⟩

/-- **★ Native-only either-Inl-head inversion.**  The `ofGrown`-free twin of
`HasTypeUnion.invertAtEitherInlHead`. -/
theorem HasTypeUnionNativeOnly.invertAtEitherInlHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {payloadValue : RawTerm scope}
    (derivation : HasTypeUnionNativeOnly profile context subject classifier)
    (subjectShape : subject = eitherInlCell payloadValue) :
    ∃ leftType rightType : RawTerm scope,
      HasTypeUnionNativeOnly profile context payloadValue leftType ∧
      Conv (eitherTypeCell leftType rightType) classifier := by
  obtain ⟨leftType, rightType, payloadTyped, converts⟩ :=
    HasTypeUnion.invertAtEitherInlHead derivation.toUnion subjectShape
  exact ⟨leftType, rightType, payloadTyped.toNativeOnly, converts⟩

/-- **★ Native-only either-Inr-head inversion.**  The `ofGrown`-free twin of
`HasTypeUnion.invertAtEitherInrHead`. -/
theorem HasTypeUnionNativeOnly.invertAtEitherInrHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {payloadValue : RawTerm scope}
    (derivation : HasTypeUnionNativeOnly profile context subject classifier)
    (subjectShape : subject = eitherInrCell payloadValue) :
    ∃ leftType rightType : RawTerm scope,
      HasTypeUnionNativeOnly profile context payloadValue rightType ∧
      Conv (eitherTypeCell leftType rightType) classifier := by
  obtain ⟨leftType, rightType, payloadTyped, converts⟩ :=
    HasTypeUnion.invertAtEitherInrHead derivation.toUnion subjectShape
  exact ⟨leftType, rightType, payloadTyped.toNativeOnly, converts⟩

/-- **★ Native-only list-cons-head inversion.**  The `ofGrown`-free twin of
`HasTypeUnion.invertAtListConsHead`: a native-only-typed `listConsCell` has a native-only-typed head and a
native-only-typed tail list at the same element type, the list type `Conv`-equal to the classifier. -/
theorem HasTypeUnionNativeOnly.invertAtListConsHead {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {headValue tailList : RawTerm scope}
    (derivation : HasTypeUnionNativeOnly profile context subject classifier)
    (subjectShape : subject = listConsCell headValue tailList) :
    ∃ elementType : RawTerm scope,
      HasTypeUnionNativeOnly profile context headValue elementType ∧
      HasTypeUnionNativeOnly profile context tailList (listTypeCell elementType) ∧
      Conv (listTypeCell elementType) classifier := by
  obtain ⟨elementType, headTyped, tailTyped, converts⟩ :=
    HasTypeUnion.invertAtListConsHead derivation.toUnion subjectShape
  exact ⟨elementType, headTyped.toNativeOnly, tailTyped.toNativeOnly, converts⟩

end FX1Poly.Typed

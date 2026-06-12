import FX1Poly.Typed.HasTypeDescNatIntro
import FX1Poly.Typed.HasTypeDescOptionIntro
import FX1Poly.Typed.HasTypeDescEitherIntro
import FX1Poly.Typed.HasTypeDescPairIntro
import FX1Poly.Typed.HasTypeDescIdIntro
import FX1Poly.Typed.HasTypeDescListIntro
import FX1Poly.Typed.HasTypeNativeUnion

/-! # FX1Poly/Typed/DataIntroNativeRowConversion — every zoo intro derivation
through the NATIVE rows alone

The per-family conversion theorems the embedding-arm retirement needs:
each standalone intro-engine derivation (the NATIVE-42 zoo) rebuilds as a
`HasTypeNativeUnion` derivation using ONLY the native table-row arms —
`ofDataIntro` (natZero through the NATIVE-42 nullary row),
`recursiveUnaryIntro` (natSucc), `nullaryFreeTypeIntro` (optionNone,
listNil), `pinnedUnaryIntro` (optionSome), `coproductIntro` (eitherInl /
eitherInr), `nonDependentBinaryIntro` (pair), `reflexiveIntro` (refl),
`recursiveBinaryIntro` (listCons).  NO `of*Intro` embedding arm appears in
any conversion, so once every union-derivation BUILDER routes through
these theorems the six interim embedding arms have no remaining producers
and delete.

The premise shapes line up BY CONSTRUCTION (the native rules were lifted
from the zoo arms): grown value/formedness premises transfer verbatim;
the recursive nat/list tail premises convert by structural recursion on
the zoo derivation — landing in the union's OWN recursion, which is
exactly the recursion the embedding arms short-circuited.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditDataIntroNativeRowConversion.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Nat intro through the native rows**: `natZero` through the NATIVE-42
nullary data-intro row, `natSucc` through the recursive-unary arm with the
predecessor converted recursively. -/
theorem HasTypeDescNatIntro.toNativeRows {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (natTyped : HasTypeDescNatIntro profile context subject classifier) :
    HasTypeNativeUnion profile context subject classifier := by
  induction natTyped with
  | natZeroIntro =>
      exact HasTypeNativeUnion.ofDataIntro
        (HasTypeDescDataIntro.nullaryIntro _ .gen_natZero () .childNil
          { outputTypeCode := fun _ => natTypeCell } rfl)
  | natSuccIntro predecessor _predecessorTyped predecessorConverted =>
      exact HasTypeNativeUnion.recursiveUnaryIntro _ .gen_natSucc
        natSuccNativeRecursiveUnaryRule predecessor rfl predecessorConverted

/-- **Option intro through the native rows**: `optionNone` through the
nullary-free-type row, `optionSome` through the pinned-unary row. -/
theorem HasTypeDescOptionIntro.toNativeRows {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (optionTyped : HasTypeDescOptionIntro profile context subject classifier) :
    HasTypeNativeUnion profile context subject classifier := by
  cases optionTyped with
  | optionNoneIntro elementType elementLevel flag elementTypeFormed =>
      exact HasTypeNativeUnion.nullaryFreeTypeIntro _ .gen_optionNone
        optionNoneNativeNullaryFreeTypeRule elementType elementLevel flag rfl
        elementTypeFormed
  | optionSomeIntro value elementType valueTyped =>
      exact HasTypeNativeUnion.pinnedUnaryIntro _ .gen_optionSome
        optionSomeNativePinnedUnaryRule value elementType rfl valueTyped

/-- **Either intro through the native rows**: both injections through the
coproduct arm (the Inl row pins the left type, the Inr row the right). -/
theorem HasTypeDescEitherIntro.toNativeRows {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (eitherTyped : HasTypeDescEitherIntro profile context subject classifier) :
    HasTypeNativeUnion profile context subject classifier := by
  cases eitherTyped with
  | eitherInlIntro leftValue leftType rightType rightLevel flag leftTyped rightTypeFormed =>
      exact HasTypeNativeUnion.coproductIntro _ .gen_eitherInl
        eitherInlNativeCoproductRule leftValue leftType rightType rightLevel flag rfl
        leftTyped rightTypeFormed
  | eitherInrIntro rightValue leftType rightType leftLevel flag rightTyped leftTypeFormed =>
      exact HasTypeNativeUnion.coproductIntro _ .gen_eitherInr
        eitherInrNativeCoproductRule rightValue rightType leftType leftLevel flag rfl
        rightTyped leftTypeFormed

/-- **Pair intro through the native row**: the non-dependent-binary arm. -/
theorem HasTypeDescPairIntro.toNativeRows {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (pairTyped : HasTypeDescPairIntro profile context subject classifier) :
    HasTypeNativeUnion profile context subject classifier := by
  cases pairTyped with
  | pairIntro firstValue secondValue firstType secondType firstTyped secondTyped =>
      exact HasTypeNativeUnion.nonDependentBinaryIntro _ .gen_pair
        pairNativeNonDependentBinaryRule firstValue secondValue firstType secondType rfl
        firstTyped secondTyped

/-- **Identity intro through the native row**: the reflexive arm. -/
theorem HasTypeDescIdIntro.toNativeRows {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (idTyped : HasTypeDescIdIntro profile context subject classifier) :
    HasTypeNativeUnion profile context subject classifier := by
  cases idTyped with
  | reflIntro witness typeCode witnessTyped =>
      exact HasTypeNativeUnion.reflexiveIntro _ .gen_refl
        reflNativeReflexiveRule witness typeCode rfl witnessTyped

/-- **List intro through the native rows**: `listNil` through the NATIVE-42
nullary-free-type row, `listCons` through the recursive-binary arm with the
tail converted recursively. -/
theorem HasTypeDescListIntro.toNativeRows {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (listTyped : HasTypeDescListIntro profile context subject classifier) :
    HasTypeNativeUnion profile context subject classifier := by
  induction listTyped with
  | listNilIntro elementType elementLevel flag elementTypeFormed =>
      exact HasTypeNativeUnion.nullaryFreeTypeIntro _ .gen_listNil
        listNilNativeNullaryFreeTypeRule elementType elementLevel flag rfl
        elementTypeFormed
  | listConsIntro headValue tailList elementType headTyped _tailTyped tailConverted =>
      exact HasTypeNativeUnion.recursiveBinaryIntro _ .gen_listCons
        listConsNativeRecursiveBinaryRule headValue tailList elementType rfl
        headTyped tailConverted

end FX1Poly.Typed

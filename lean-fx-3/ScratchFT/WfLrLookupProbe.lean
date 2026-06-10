import FX1Poly.Typed.WfContextTypedLrValid
import FX1Poly.Typed.TypedTypeValidityBoxedRename

/-! Probe: the typed-LR lookup lemma — in a WfContextTypedLrValid context, looking up a variable gives a
    TypedTypeValidityBoxed for that entry's (iterated-weakened) type. Mirrors WfContextDescPi.lookupIsType,
    folding TypedTypeValidityBoxed.weakenUnderBinding down the telescope. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

theorem WfContextTypedLrValid.lookupLrValid {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    WfContextTypedLrValid context →
      ∀ index : Fin scope,
        ∃ box : KripkeCandBox scope,
          TypedTypeValidityBoxed profile context (context.lookup index) box := by
  induction context with
  | empty =>
      intro _ index
      exact absurd index.isLt (Nat.not_lt_zero index.val)
  | cons restContext bindingType ih =>
      intro wellFormed index
      obtain ⟨indexValue, indexBound⟩ := index
      cases indexValue with
      | zero =>
          obtain ⟨_box, headValid⟩ := WfContextTypedLrValid.headLrValid wellFormed
          exact headValid.weakenUnderBinding bindingType
      | succ k =>
          obtain ⟨_box, tailValid⟩ :=
            ih (WfContextTypedLrValid.tailValid wellFormed)
              ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩
          exact tailValid.weakenUnderBinding bindingType

end FX1Poly.Typed

#print axioms FX1Poly.Typed.WfContextTypedLrValid.lookupLrValid

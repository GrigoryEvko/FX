import FX1Poly.Polygraph.TwoCategory.WalkingInvolution.InvolutionOneCellConv

/-! # WalkingInvolution/InvolutionParity — the Z/2 model and SOUNDNESS of the parity invariant

The walking involution `⟨s | s.s = id⟩` has 1-cell monoid `Z/2`: a word in `s` is determined, modulo `s.s = id`,
by its LENGTH mod 2 (the parity).  This file ships the Z/2 model `involutionParityOf` (word length mod 2, as a
`Bool` under `xor`, `s ↦ true`) and SOUNDNESS: convertible words have EQUAL parity (`s.s ≈ id` respects Z/2
because `parity(s.s) = false = parity(id)`).  Completeness (equal parity ⟹ convertible) and the decision are in
`InvolutionDecision`.

Raw Lean 4 + Init; `involutionParityOf` is a structural recursion (total `nil`/`cons .s` match — the sole
modality `s` is forced), soundness is an induction on the `Prop`-valued convertibility with `Bool` case splits, so
every declaration is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-- Double negation on `Bool` is the identity (the `Z/2` relation `parity(s.s) = parity(id)`), by the two-case
split — propext-free. -/
theorem involutionBoolNotNot (bit : Bool) : (!(!bit)) = bit := by
  cases bit with
  | false => rfl
  | true => rfl

/-! ## The Z/2 model: word length parity, `s ↦ true` -/

/-- Parity of a natural number as a `Bool` (`Z/2`): `0 ↦ false`, and each successor FLIPS.  Plain `Nat` structural
recursion, so its defining equations hold DEFINITIONALLY — the reason the model is routed through `length`. -/
def natParity : Nat → Bool
  | 0 => false
  | count + 1 => !(natParity count)

/-- ★ The **Z/2 model** of the walking involution: the parity of a word in `s` — `false` for the identity, and
each leading `s` FLIPS the parity (`s ↦ true`, `xor`).  Computed as `natParity` of the word's LENGTH (matching
`cons` generically through the already-clean `length`, so `involutionParityOf (s.rest) = !(involutionParityOf rest)`
holds DEFINITIONALLY — unlike a direct modality-refining recursion whose matcher would not reduce).  This is the
invariant that decides the 1-cell word problem, because `s.s = id` preserves it (`!!b = b`). -/
def involutionParityOf
    (word : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point) : Bool :=
  natParity word.length

/-- The defining equation on `nil` — the identity has EVEN parity. -/
theorem involutionParityOf_nil :
    involutionParityOf (involutionNil) = false := rfl

/-- The defining equation on `cons s` — a leading `s` flips the parity. -/
theorem involutionParityOf_cons
    (rest : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point) :
    involutionParityOf (ModalityPath.cons InvolutionModality.s rest) = !(involutionParityOf rest) := rfl

/-- Smoke: `s` has ODD parity (`true`) — the single dual is not the identity. -/
theorem involutionParityOf_involutionS : involutionParityOf involutionS = true := rfl

/-- Smoke: `s.s` has EVEN parity (`false`) — the double dual IS the identity in Z/2. -/
theorem involutionParityOf_involutionSThenS :
    involutionParityOf (ModalityPath.cons InvolutionModality.s involutionS) = false := rfl

/-! ## SOUNDNESS: convertible words have equal parity -/

/-- ★ **Soundness of the Z/2 model**: `s.s = id`-convertible words have EQUAL parity.  By induction on the
convertibility: the involution law `ssId` is exactly `!!b = b` (`involutionBoolNotNot`), the `cons`-congruence
flips both sides equally (`congrArg Bool.not`), and `refl`/`symm`/`trans` are the equivalence closure.  This is the
NO-direction of the decision (distinct parity ⟹ not convertible). -/
theorem involutionParityOf_congr_of_conv
    {word1 word2 : ModalityPath involutionGraph InvolutionMode.point InvolutionMode.point}
    (conv : InvolutionOneCellConv word1 word2) :
    involutionParityOf word1 = involutionParityOf word2 := by
  induction conv with
  | ssId rest => exact involutionBoolNotNot (involutionParityOf rest)
  | consCongr _ ih => exact congrArg Bool.not ih
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end FX1Poly.Polygraph

import FX1Poly.Typed.ConsistencyTargetSignature

/-! Make-or-break validation of the candidate-bridge model edit (#1049/#810).

The real `ReducibleTypeStepBounded.neutral` over-fires on `gen_emptyCode` and `deterministic` then
FORCES emptyTypeCell's candidate to the whole SN set (ConsistencyTargetSignature.lean:190).  The
proposed fix GATES `neutral` (add `rootGenerator ≠ gen_emptyCode`) and adds a `dataEmpty` arm pinning
emptyTypeCell to the empty Tait candidate.  The ONLY genuinely-new determinism concern is the
`neutral × dataEmpty` cross-case.  This file replays that edit on a faithful miniature using the REAL
`RawTerm`/`Generator`/`WeakHeadStep`/`rootGenerator`/`emptyTypeCell` so the rootGenerator facts transfer
directly, and PROVES the three load-bearing claims hold:
  1. determinism SURVIVES (the cross-case is ruled out by the rootGenerator contradiction),
  2. emptyTypeCell routes through `dataEmpty` to the empty candidate,
  3. consistency follows (the empty candidate is member-free).
-/

namespace FX1Poly.Typed
open FX1Poly.Core

-- Faithful miniature of the EDITED reducibility-as-type relation: the gated `neutral` (now excluding
-- gen_emptyCode) + the new `dataEmpty` arm.  Parameterized over the empty candidate so the validation
-- is candidate-agnostic.
inductive ScratchReducibleTypeEdited {scope : Nat} (emptyCandidate : RawTerm scope → Prop) :
    RawTerm scope → (RawTerm scope → Prop) → Prop where
  | neutral {typeCode : RawTerm scope} :
      (∀ reduct, ¬ WeakHeadStep typeCode reduct) →
      typeCode.rootGenerator ≠ Generator.gen_piTyCode →
      typeCode.rootGenerator ≠ Generator.gen_universeCode →
      typeCode.rootGenerator ≠ Generator.gen_emptyCode →
      ScratchReducibleTypeEdited emptyCandidate typeCode StepStar.IsStronglyNormalizing
  | dataEmpty {typeCode : RawTerm scope} :
      typeCode.rootGenerator = Generator.gen_emptyCode →
      ScratchReducibleTypeEdited emptyCandidate typeCode emptyCandidate

-- CLAIM 1 (★ make-or-break): determinism SURVIVES the edit.  The neutral×dataEmpty cross-case is the
-- only new interaction; it is ruled out by `notEmpty` (neutral's new gate) vs `isEmpty` (dataEmpty's
-- premise), a direct rootGenerator contradiction.
theorem ScratchReducibleTypeEdited.deterministic {scope : Nat} {emptyCandidate : RawTerm scope → Prop}
    {typeCode : RawTerm scope} {candidate1 candidate2 : RawTerm scope → Prop}
    (reducible1 : ScratchReducibleTypeEdited emptyCandidate typeCode candidate1)
    (reducible2 : ScratchReducibleTypeEdited emptyCandidate typeCode candidate2) :
    PointwiseIff candidate1 candidate2 := by
  cases reducible1 with
  | neutral _ _ _ notEmpty1 =>
      cases reducible2 with
      | neutral _ _ _ _ => exact fun _ => Iff.rfl
      | dataEmpty isEmpty2 => exact absurd isEmpty2 notEmpty1
  | dataEmpty isEmpty1 =>
      cases reducible2 with
      | neutral _ _ _ notEmpty2 => exact absurd isEmpty1 notEmpty2
      | dataEmpty _ => exact fun _ => Iff.rfl

-- CLAIM 2: emptyTypeCell routes through `dataEmpty` to the empty candidate — so ANY candidate it is
-- reducible-as-type to IS the empty candidate (the exact opposite of the current SN-forcing).
theorem ScratchReducibleTypeEdited.emptyCodeCandidateIsEmpty {scope : Nat}
    {emptyCandidate : RawTerm scope → Prop} {candidate : RawTerm scope → Prop}
    (reducible : ScratchReducibleTypeEdited emptyCandidate (emptyTypeCell (scope := scope)) candidate) :
    PointwiseIff candidate emptyCandidate :=
  ScratchReducibleTypeEdited.deterministic reducible
    (ScratchReducibleTypeEdited.dataEmpty
      (by show Generator.gen_emptyCode = Generator.gen_emptyCode; rfl))

-- CLAIM 3: consistency core — with the edit, a fundamental-theorem-produced member of emptyTypeCell's
-- candidate yields False, because that candidate IS the (member-free) empty candidate.  This is the
-- canonicity/consistency bridge the current model blocks; the edit makes it provable.
theorem ScratchReducibleTypeEdited.consistencyCore {scope : Nat}
    {emptyCandidate : RawTerm scope → Prop} (memberFree : ∀ term, ¬ emptyCandidate term)
    {candidate : RawTerm scope → Prop}
    (reducible : ScratchReducibleTypeEdited emptyCandidate (emptyTypeCell (scope := scope)) candidate)
    (closedTerm : RawTerm scope) (member : candidate closedTerm) :
    False :=
  memberFree closedTerm
    ((ScratchReducibleTypeEdited.emptyCodeCandidateIsEmpty reducible closedTerm).mp member)

-- CLAIM 4: the edit does NOT disturb non-empty neutral codes — a neutral non-empty code still gets the
-- SN candidate (the existing behavior for every non-data type code is preserved).
theorem ScratchReducibleTypeEdited.nonEmptyNeutralStillSN {scope : Nat}
    {emptyCandidate : RawTerm scope → Prop} {typeCode : RawTerm scope}
    (noWeakHeadStep : ∀ reduct, ¬ WeakHeadStep typeCode reduct)
    (notPi : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode)
    (notEmpty : typeCode.rootGenerator ≠ Generator.gen_emptyCode) :
    ScratchReducibleTypeEdited emptyCandidate typeCode StepStar.IsStronglyNormalizing :=
  ScratchReducibleTypeEdited.neutral noWeakHeadStep notPi notUniverse notEmpty

end FX1Poly.Typed

#print axioms FX1Poly.Typed.ScratchReducibleTypeEdited.deterministic
#print axioms FX1Poly.Typed.ScratchReducibleTypeEdited.emptyCodeCandidateIsEmpty
#print axioms FX1Poly.Typed.ScratchReducibleTypeEdited.consistencyCore
#print axioms FX1Poly.Typed.ScratchReducibleTypeEdited.nonEmptyNeutralStillSN

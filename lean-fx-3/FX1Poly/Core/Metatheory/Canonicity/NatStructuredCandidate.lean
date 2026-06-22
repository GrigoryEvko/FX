import FX1Poly.Core.Metatheory.Canonicity.RecursiveDataIntroDataTaitMembers

/-! # FX1Poly/Core/NatStructuredCandidate
    — the OPEN-SCOPE nat reducibility candidate (succ-closure without closedness), zero-axiom

`NatCanonicalFormsCandidate.lean` builds the nat candidate over the numeral value predicate `IsNatValue`
(= `succ^k zero`).  `RecursiveDataIntroDataTaitMembers.natSuccDataTaitMember` shows that
`dataTaitCandidate IsNatValue` is closed under `natSucc` ONLY at scope `0`: its proof rules the neutral
disjunct out with `IsNeutral.noClosed`, because at open scope `natSucc (someNeutral)` is neither a numeral
(its predecessor is not `IsNatValue`) NOR neutral (`natSucc` is a constructor, no `IsNeutral` arm) — so it
escapes `dataTaitCandidate IsNatValue` and the recursive intro arm cannot fire.

That is the obstruction the dependent `natElim` / `natRec` reducibility hits: an eliminator dispatches by
its scrutinee's candidate, so the scrutinee type must pin to a value-dispatching candidate; but the SAME
candidate must be closed under the constructors at OPEN scope for the introduction rows.  `IsNatValue`
dispatches but is not succ-closed open; the plain `IsStronglyNormalizing` candidate is succ-closed but does
not dispatch.

The resolution is the standard Tait/Girard nat reducibility set in its open-scope form: widen the value
predicate to `IsNatStructured` = `succ^k` applied to `zero` OR to a NORMAL neutral.  This:

  * **is closed under `natSucc` at every scope** (`natSuccStructuredMember`, the headline) — `natSucc` of a
    member's reachable normal form is structured whether that normal form is structured (the `succ` arm) or
    a normal neutral (the `neutralNormal` arm then `succ` arm).  No closedness needed.
  * **still dispatches and is sound for canonicity** (`natStructuredClosedReducesToNumeral`) — at scope `0`
    no neutrals exist (`IsNeutral.noClosed`), so a closed structured normal form collapses to a genuine
    numeral (`isNatStructured_closed_isNatValue`); the widening adds nothing closed.
  * **subsumes `IsNatValue`** (`isNatValue_implies_isNatStructured`) — every numeral is structured, so every
    existing numeral member transports to the wider candidate.

`dataTaitCandidate IsNatStructured` is the single candidate the model can pin `natTypeCell` to for BOTH the
introduction and elimination FT rows; this file is its Core substrate.  All candidate metatheory (CR1/CR2/CR3,
head-expansion closure) is inherited from the generic `dataTaitCandidate` bundle uniformly in the value
predicate.

## Zero-axiom verification

`IsNatStructured` is a three-constructor inductive eliminated by full-enumeration `induction`; value-normality
and the numeral / closed bridges are structural inductions; the succ-closure reuses the shipped
`stepStar_under_unaryCell natSuccCell Step.from_natSucc` decomposition and
`natSucc_isStronglyNormalizing_of_predecessor`, replacing the scope-0 `IsNeutral.noClosed` elimination with
the genuine `neutralNormal` constructor.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **The open-scope nat structural-value predicate.**  A term is structured when it is `succ^k` applied to
`zero` or to a NORMAL neutral — the widening of `IsNatValue` (numerals) that admits `natSucc` of a stuck
(but normal) neutral predecessor.  This is the value predicate whose `dataTaitCandidate` is closed under
`natSucc` at every scope, not only at scope `0`. -/
inductive IsNatStructured {scope : Nat} : RawTerm scope → Prop where
  /-- `zero` is structured. -/
  | zero : IsNatStructured natZeroCell
  /-- A NORMAL neutral is structured — the open-scope base case `IsNatValue` lacks. -/
  | neutralNormal {neutralTerm : RawTerm scope} (isNeutral : IsNeutral neutralTerm)
      (isNormal : RawTerm.isStepNormalForm neutralTerm) : IsNatStructured neutralTerm
  /-- The successor of a structured term is structured. -/
  | succ {predecessor : RawTerm scope} (predecessorIsStructured : IsNatStructured predecessor) :
      IsNatStructured (natSuccCell predecessor)

/-- **Structured values are structural normal forms.**  `zero` is normal; a normal neutral is normal by its
hypothesis; a `natSucc` cell is no redex root and its `isStepNormalFormBool` reduces to that of its
predecessor (normal by the induction hypothesis).  The value-normality obligation the generic data candidate
consumes through `dataTaitCandidate.memberOfValue`. -/
theorem isNatStructured_impliesStepNormalForm {scope : Nat} {value : RawTerm scope}
    (valueIsStructured : IsNatStructured value) : RawTerm.isStepNormalForm value := by
  induction valueIsStructured with
  | zero => rfl
  | neutralNormal _isNeutral isNormal => exact isNormal
  | @succ predecessor _predecessorIsStructured predecessorIH =>
      -- `isStepNormalFormBool (natSucc predecessor)` reduces to `isStepNormalFormBool predecessor && true`
      -- (natSucc is no redex root, single child); the IH gives the predecessor normal.
      show (RawTerm.isStepNormalFormBool predecessor && true) = true
      rw [Bool.and_true]
      exact predecessorIH

/-- **Every numeral is structured** — `IsNatStructured` subsumes `IsNatValue`, so every numeral member of the
narrow candidate transports to the wide candidate.  Structural induction over the numeral. -/
theorem isNatValue_implies_isNatStructured {scope : Nat} {value : RawTerm scope}
    (valueIsNat : IsNatValue value) : IsNatStructured value := by
  induction valueIsNat with
  | zero => exact IsNatStructured.zero
  | succ _predecessorIsValue predecessorIH => exact IsNatStructured.succ predecessorIH

/-- **A closed structured value is a numeral.**  At scope `0` no neutral exists (`IsNeutral.noClosed`), so the
`neutralNormal` base case is vacuous and structure collapses to numeral structure.  This is why widening to
`IsNatStructured` is conservative for closed canonicity: the closed members are exactly the numerals. -/
theorem isNatStructured_closed_isNatValue {value : RawTerm 0}
    (valueIsStructured : IsNatStructured value) : IsNatValue value := by
  induction valueIsStructured with
  | zero => exact IsNatValue.zero
  | neutralNormal isNeutral _isNormal => exact (IsNeutral.noClosed isNeutral).elim
  | succ _predecessorIsStructured predecessorIH => exact IsNatValue.succ predecessorIH

/-- **The nat structural Tait candidate is a Girard reducibility candidate** (CR1+CR2+CR3) — instant from the
generic `dataTaitCandidate` bundle, uniformly in the value predicate. -/
theorem natStructuredCandidate_isReducibilityCandidate {scope : Nat} :
    IsReducibilityCandidate (dataTaitCandidate (IsNatStructured (scope := scope))) :=
  dataTaitCandidate_isReducibilityCandidate

/-- **The nat structural Tait candidate is head-expansion-closed** — the Pi-codomain property the FT consumes,
instant from the generic theorem. -/
theorem natStructuredCandidate_headExpansionClosed {scope : Nat} :
    HeadExpansionClosed (dataTaitCandidate (IsNatStructured (scope := scope))) :=
  dataTaitCandidate_headExpansionClosed

/-- **Every numeral is a member of the nat structural candidate.**  A numeral is a normal structured value,
so `dataTaitCandidate.memberOfValue` places it in the candidate.  The constructor reducibility for `zero` and
already-evaluated numerals. -/
theorem isNatValue_structuredMember {scope : Nat} {value : RawTerm scope}
    (valueIsNat : IsNatValue value) : dataTaitCandidate IsNatStructured value :=
  dataTaitCandidate.memberOfValue (isNatStructured_impliesStepNormalForm
    (isNatValue_implies_isNatStructured valueIsNat)) (isNatValue_implies_isNatStructured valueIsNat)

/-- **`zero` is a member of the nat structural candidate.** -/
theorem natZeroStructuredMember {scope : Nat} :
    dataTaitCandidate (IsNatStructured (scope := scope)) natZeroCell :=
  isNatValue_structuredMember IsNatValue.zero

/-- **★ Open-scope recursive nat intro: `natSucc` of a structural-candidate member is a member.**  THE
headline this file exists for — the succ-closure the narrow `dataTaitCandidate IsNatValue` achieves only at
scope `0`.  The predecessor is strongly normalizing, so the successor is
(`natSucc_isStronglyNormalizing_of_predecessor`); each reachable normal form of `natSucc predecessor`
decomposes (`stepStar_under_unaryCell`) into `natSucc predecessorAfter` for a reachable normal form
`predecessorAfter` of the predecessor, which the member classifies as structured (the `succ` arm applies) or
NORMAL neutral (the `neutralNormal` then `succ` arms apply) — in both cases the successor is structured, with
NO appeal to closedness. -/
theorem natSuccStructuredMember {scope : Nat} {predecessor : RawTerm scope}
    (predecessorMember : dataTaitCandidate IsNatStructured predecessor) :
    dataTaitCandidate IsNatStructured (natSuccCell predecessor) := by
  refine ⟨natSucc_isStronglyNormalizing_of_predecessor predecessorMember.1, ?_⟩
  intro normalForm reaches normalFormIsNormal
  obtain ⟨predecessorAfter, targetEq, predecessorChain⟩ :=
    stepStar_under_unaryCell natSuccCell Step.from_natSucc reaches predecessor rfl
  subst targetEq
  have predecessorAfterNormal : RawTerm.isStepNormalForm predecessorAfter := by
    have folded : (RawTerm.isStepNormalFormBool predecessorAfter && true) = true := normalFormIsNormal
    rw [Bool.and_true] at folded
    exact folded
  rcases predecessorMember.2 predecessorAfter predecessorChain predecessorAfterNormal with
      predecessorIsStructured | predecessorIsNeutral
  · exact Or.inl (IsNatStructured.succ predecessorIsStructured)
  · exact Or.inl (IsNatStructured.succ (IsNatStructured.neutralNormal predecessorIsNeutral
      predecessorAfterNormal))

/-- **Closed nat structural-candidate canonicity: a closed member reduces to a numeral.**  The closed member
reaches a structured normal value (`dataTaitCandidate.closedReducesToValue`), which at scope `0` is a numeral
(`isNatStructured_closed_isNatValue`).  Confirms the wide candidate is sound for canonicity exactly as the
narrow `IsNatValue` candidate. -/
theorem natStructuredClosedReducesToNumeral {term : RawTerm 0}
    (member : dataTaitCandidate IsNatStructured term) :
    ∃ value : RawTerm 0, StepStar term value ∧ IsNatValue value := by
  obtain ⟨value, reaches, valueIsStructured, _valueIsNormal⟩ := dataTaitCandidate.closedReducesToValue member
  exact ⟨value, reaches, isNatStructured_closed_isNatValue valueIsStructured⟩

end FX1Poly.Core

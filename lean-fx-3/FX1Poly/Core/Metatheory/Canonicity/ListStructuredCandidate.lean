import FX1Poly.Core.Metatheory.Canonicity.RecursiveDataIntroDataTaitMembers

/-! # FX1Poly/Core/ListStructuredCandidate
    — the OPEN-SCOPE list reducibility candidate (cons-closure without closedness), zero-axiom

`ListCanonicalFormsCandidate.lean` builds the list candidate over the strict value predicate `IsListValue`
(`nil`, or `cons head tail` with `head` normal and `tail` itself a value).  `RecursiveDataIntroDataTait\
Members.listConsDataTaitMember` shows `dataTaitCandidate IsListValue` is closed under `listCons` ONLY at scope
`0`: its proof rules the neutral disjunct of the tail out with `IsNeutral.noClosed`, because at open scope
`cons head (someNeutral)` is neither a list value (its tail is not `IsListValue`) NOR neutral (`listCons` is a
constructor, no `IsNeutral` arm) — so it escapes `dataTaitCandidate IsListValue` and the recursive intro arm
cannot fire.

This is the exact obstruction the nat candidate hit (`NatStructuredCandidate`), here on the BINARY recursive
constructor: an eliminator dispatches by its scrutinee's candidate, so the scrutinee type must pin to a
value-dispatching candidate; but the SAME candidate must be closed under the constructors at OPEN scope for the
introduction rows.  The resolution is the standard Tait/Girard list reducibility set in its open-scope form:
widen the value predicate to `IsListStructured` = `nil`, a NORMAL neutral, or `cons` of a normal head onto a
structured tail.  This is the list twin of `IsNatStructured`, the `cons` recursion taking the place of `succ`
and the `head` carried structurally (like a `pair` component).

  * **closed under `listCons` at every scope** (`listConsStructuredMember`, the headline) — `cons` of a normal
    head onto a member's reachable normal-form tail is structured whether that tail is structured (the `cons`
    arm) or a normal neutral (the `neutralNormal` then `cons` arms).  No closedness needed.
  * **still dispatches and is sound for canonicity** (`listStructuredClosedReducesToValue`) — at scope `0` no
    neutral exists, so a closed structured normal form collapses to a strict list value.
  * **subsumes `IsListValue`** (`isListValue_implies_isListStructured`) — every strict value is structured.

`dataTaitCandidate IsListStructured` is the single candidate the model can pin `listTypeCell` to for BOTH the
introduction and elimination FT rows; this file is its Core substrate (DEP-LIST-MODEL).  All candidate
metatheory (CR1/CR2/CR3, head-expansion closure) is inherited from the generic `dataTaitCandidate` bundle
uniformly in the value predicate.

## Zero-axiom verification

`IsListStructured` is a three-constructor inductive eliminated by full-enumeration `induction`; value-normality
and the strict-value / closed bridges are structural inductions; the cons-closure reuses the shipped
`stepStar_under_binaryCell listConsCell Step.from_listCons` decomposition and
`listCons_isStronglyNormalizing_of_head_tail`, replacing the scope-0 `IsNeutral.noClosed` elimination with the
genuine `neutralNormal` constructor (the nat-structured recipe, binary).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Core

open StepStar

/-- Left projection of a Bool conjunction equal to `true` (propext-clean; `Bool.and_eq_true` leaks `propext`). -/
private theorem listBoolConjLeft {leftFlag rightFlag : Bool}
    (conjunction : (leftFlag && rightFlag) = true) : leftFlag = true := by
  cases leftFlag with
  | true => rfl
  | false => exact conjunction

/-- Right projection of a Bool conjunction equal to `true`. -/
private theorem listBoolConjRight {leftFlag rightFlag : Bool}
    (conjunction : (leftFlag && rightFlag) = true) : rightFlag = true := by
  cases leftFlag with
  | true => exact conjunction
  | false => nomatch conjunction

/-- **The open-scope list structural-value predicate.**  A term is structured when it is `nil`, a NORMAL
neutral, or `cons` of a normal head onto a structured tail — the widening of `IsListValue` that admits `listCons`
of a stuck (but normal) neutral tail.  The list twin of `IsNatStructured`: the `cons` recursion in place of
`succ`, the head carried structurally. -/
inductive IsListStructured {scope : Nat} : RawTerm scope → Prop where
  /-- `nil` is structured. -/
  | nil : IsListStructured listNilCell
  /-- A NORMAL neutral is structured — the open-scope base case `IsListValue` lacks. -/
  | neutralNormal {neutralTerm : RawTerm scope} (isNeutral : IsNeutral neutralTerm)
      (isNormal : RawTerm.isStepNormalForm neutralTerm) : IsListStructured neutralTerm
  /-- `cons` of a normal head onto a structured tail is structured. -/
  | cons {head tail : RawTerm scope} (headNormal : RawTerm.isStepNormalForm head)
      (tailIsStructured : IsListStructured tail) : IsListStructured (listConsCell head tail)

/-- **Structured values are structural normal forms.**  `nil` is normal; a normal neutral is normal by its
hypothesis; a `listCons` cell is no redex root and its `isStepNormalFormBool` reduces to the conjunction of the
head's and tail's (the two-child spine recursion), closed by the head's normality and the tail's induction
hypothesis.  The value-normality obligation the generic data candidate consumes through
`dataTaitCandidate.memberOfValue`. -/
theorem isListStructured_impliesStepNormalForm {scope : Nat} {value : RawTerm scope}
    (valueIsStructured : IsListStructured value) : RawTerm.isStepNormalForm value := by
  induction valueIsStructured with
  | nil => rfl
  | neutralNormal _isNeutral isNormal => exact isNormal
  | @cons head tail headNormal _tailIsStructured tailIH =>
      show (RawTerm.isStepNormalFormBool head
          && (RawTerm.isStepNormalFormBool tail && true)) = true
      rw [show RawTerm.isStepNormalFormBool head = true from headNormal,
        show RawTerm.isStepNormalFormBool tail = true from tailIH]
      rfl

/-- **Every strict list value is structured** — `IsListStructured` subsumes `IsListValue`, so every strict-value
member transports to the wide candidate.  Structural induction over the value. -/
theorem isListValue_implies_isListStructured {scope : Nat} {value : RawTerm scope}
    (valueIsList : IsListValue value) : IsListStructured value := by
  induction valueIsList with
  | nil => exact IsListStructured.nil
  | cons headNormal _tailIsValue tailIH => exact IsListStructured.cons headNormal tailIH

/-- **A closed structured value is a strict list value.**  At scope `0` no neutral exists (`IsNeutral.noClosed`),
so the `neutralNormal` base case is vacuous and structure collapses to strict-value structure.  This is why
widening to `IsListStructured` is conservative for closed canonicity. -/
theorem isListStructured_closed_isListValue {value : RawTerm 0}
    (valueIsStructured : IsListStructured value) : IsListValue value := by
  induction valueIsStructured with
  | nil => exact IsListValue.nil
  | neutralNormal isNeutral _isNormal => exact (IsNeutral.noClosed isNeutral).elim
  | cons headNormal _tailIsStructured tailIH => exact IsListValue.cons headNormal tailIH

/-- **The list structural Tait candidate is a Girard reducibility candidate** (CR1+CR2+CR3) — instant from the
generic `dataTaitCandidate` bundle, uniformly in the value predicate. -/
theorem listStructuredCandidate_isReducibilityCandidate {scope : Nat} :
    IsReducibilityCandidate (dataTaitCandidate (IsListStructured (scope := scope))) :=
  dataTaitCandidate_isReducibilityCandidate

/-- **The list structural Tait candidate is head-expansion-closed** — the Pi-codomain property the FT consumes,
instant from the generic theorem. -/
theorem listStructuredCandidate_headExpansionClosed {scope : Nat} :
    HeadExpansionClosed (dataTaitCandidate (IsListStructured (scope := scope))) :=
  dataTaitCandidate_headExpansionClosed

/-- **Every strict list value is a member of the list structural candidate.**  A strict value is a normal
structured value, so `dataTaitCandidate.memberOfValue` places it in the candidate. -/
theorem isListValue_structuredMember {scope : Nat} {value : RawTerm scope}
    (valueIsList : IsListValue value) : dataTaitCandidate IsListStructured value :=
  dataTaitCandidate.memberOfValue (isListStructured_impliesStepNormalForm
    (isListValue_implies_isListStructured valueIsList)) (isListValue_implies_isListStructured valueIsList)

/-- **`nil` is a member of the list structural candidate.** -/
theorem listNilStructuredMember {scope : Nat} :
    dataTaitCandidate (IsListStructured (scope := scope)) listNilCell :=
  isListValue_structuredMember IsListValue.nil

/-- **★ Open-scope recursive list intro: `listCons` of a normal head onto a structural-candidate tail is a
member.**  THE headline this file exists for — the cons-closure the narrow `dataTaitCandidate IsListValue`
achieves only at scope `0`.  Both children are strongly normalizing, so the `cons` cell is
(`listCons_isStronglyNormalizing_of_head_tail`); each reachable normal form of `cons head tail` decomposes
(`stepStar_under_binaryCell`) into `cons headAfter tailAfter` for reachable normal forms of head and tail; the
head's is normal directly and the tail member classifies its reduct as structured (the `cons` arm) or NORMAL
neutral (the `neutralNormal` then `cons` arms) — in both cases the `cons` is structured, with NO appeal to
closedness.  The binary twin of `natSuccStructuredMember`. -/
theorem listConsStructuredMember {scope : Nat} {headValue tailValue : RawTerm scope}
    (headStronglyNormalizing : IsStronglyNormalizing headValue)
    (tailMember : dataTaitCandidate IsListStructured tailValue) :
    dataTaitCandidate IsListStructured (listConsCell headValue tailValue) := by
  refine ⟨listCons_isStronglyNormalizing_of_head_tail headStronglyNormalizing tailMember.1, ?_⟩
  intro normalForm reaches normalFormIsNormal
  obtain ⟨headAfter, tailAfter, targetEq, _headChain, tailChain⟩ :=
    stepStar_under_binaryCell listConsCell Step.from_listCons reaches headValue tailValue rfl
  subst targetEq
  have headAfterNormal : RawTerm.isStepNormalForm headAfter := by
    have folded : (RawTerm.isStepNormalFormBool headAfter &&
        (RawTerm.isStepNormalFormBool tailAfter && true)) = true := normalFormIsNormal
    exact listBoolConjLeft folded
  have tailAfterNormal : RawTerm.isStepNormalForm tailAfter := by
    have folded : (RawTerm.isStepNormalFormBool headAfter &&
        (RawTerm.isStepNormalFormBool tailAfter && true)) = true := normalFormIsNormal
    exact listBoolConjLeft (listBoolConjRight folded)
  rcases tailMember.2 tailAfter tailChain tailAfterNormal with tailIsStructured | tailIsNeutral
  · exact Or.inl (IsListStructured.cons headAfterNormal tailIsStructured)
  · exact Or.inl (IsListStructured.cons headAfterNormal
      (IsListStructured.neutralNormal tailIsNeutral tailAfterNormal))

/-- **Closed list structural-candidate canonicity: a closed member reduces to a strict list value.**  The closed
member reaches a structured normal value (`dataTaitCandidate.closedReducesToValue`), which at scope `0` is a
strict list value (`isListStructured_closed_isListValue`).  Confirms the wide candidate is sound for canonicity
exactly as the narrow `IsListValue` candidate. -/
theorem listStructuredClosedReducesToValue {term : RawTerm 0}
    (member : dataTaitCandidate IsListStructured term) :
    ∃ value : RawTerm 0, StepStar term value ∧ IsListValue value := by
  obtain ⟨value, reaches, valueIsStructured, _valueIsNormal⟩ := dataTaitCandidate.closedReducesToValue member
  exact ⟨value, reaches, isListStructured_closed_isListValue valueIsStructured⟩

end FX1Poly.Core

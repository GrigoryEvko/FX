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

/-! ## Eliminator-side stones (DEP-LIST #1729) — the binary-cons twins of the nat eliminator stones

The dependent `listElim` reducibility member dispatches by the scrutinee's `IsListStructured` structure and recurses
on the TAIL; these are the candidate-side facts it consumes — the binary-constructor analogues of the
`NatStructuredCandidate` eliminator stones, with the two-child injection drilling, the two-child SN reflection, and
the both-children-normal lift the binary `listCons` cell forces. -/

/-- Forward head-congruence: a head reduction lifts under `listCons` (tail fixed). -/
private theorem listConsStepStarHead {scope : Nat} {head headAfter tail : RawTerm scope}
    (headReaches : StepStar head headAfter) :
    StepStar (listConsCell head tail) (listConsCell headAfter tail) := by
  induction headReaches with
  | refl _ => exact StepStar.refl _
  | trans firstStep _restChain restInductiveHypothesis =>
      exact StepStar.trans
        (Step.cong .gen_listCons ()
          (StepChildren.here (.childCons tail .childNil : RawTermChildren [0] scope) firstStep))
        restInductiveHypothesis

/-- Forward tail-congruence: a tail reduction lifts under `listCons` (head fixed). -/
private theorem listConsStepStarTail {scope : Nat} {head tail tailAfter : RawTerm scope}
    (tailReaches : StepStar tail tailAfter) :
    StepStar (listConsCell head tail) (listConsCell head tailAfter) := by
  induction tailReaches with
  | refl _ => exact StepStar.refl _
  | trans firstStep _restChain restInductiveHypothesis =>
      exact StepStar.trans
        (Step.cong .gen_listCons ()
          (@StepChildren.there scope 0 [0] head _ _
            (StepChildren.here (.childNil : RawTermChildren [] scope) firstStep)))
        restInductiveHypothesis

/-- **A neutral term's head is never the `listCons` constructor.**  Local copy of the `listCons` ι-vacuity
discriminator (the `Eliminators` layer's version is not importable from `Canonicity`, which it sits below): casing
the neutrality witness sends each arm's `rootGenerator` to a concrete elimination generator, refuted against
`gen_listCons` by `Generator.noConfusion`. -/
theorem isNeutral_rootGenerator_ne_listCons {scope : Nat} {term : RawTerm scope}
    (neutral : IsNeutral term) : term.rootGenerator ≠ Generator.gen_listCons := by
  cases neutral <;> exact fun shapeEquation => Generator.noConfusion shapeEquation

/-- **Constructor-shape recovery: a `listNil`-headed term is the `listNil` cell.**  A `RawTerm` is `mkGen` of its
head generator, payload, and children; when the head is `gen_listNil` the payload type is `Unit` and the children
shape is empty, so the term is structurally `listNilCell`.  The dependent `listElim` value-handler consumes this to
fire the `iotaListElimNil` reduction once the trichotomy reports a `listNil`-headed focus. -/
theorem eq_listNilCell_of_rootGenerator {scope : Nat} {term : RawTerm scope}
    (headEquation : term.rootGenerator = Generator.gen_listNil) :
    term = listNilCell := by
  cases term with
  | mkGen generator payload children =>
      cases headEquation
      cases payload
      cases children
      rfl

/-- **Constructor-shape recovery: a `listCons`-headed term is a `listCons` cell over its two children.**  As
`eq_listNilCell_of_rootGenerator`, but `gen_listCons`'s child shape is two non-binding children, recovered as the
head and tail.  The dependent `listElim` value-handler consumes this to fire the `iotaListElimCons` reduction and
descend onto the tail once the trichotomy reports a `listCons`-headed focus. -/
theorem exists_head_tail_of_rootGenerator_listCons {scope : Nat} {term : RawTerm scope}
    (headEquation : term.rootGenerator = Generator.gen_listCons) :
    ∃ head tail : RawTerm scope, term = listConsCell head tail := by
  cases term with
  | mkGen generator payload children =>
      cases headEquation
      cases payload
      cases children with
      | childCons childHead childRest =>
          cases childRest with
          | childCons childTail childRestRest =>
              cases childRestRest
              exact ⟨childHead, childTail, rfl⟩

/-- **The candidate-side trichotomy bridge for `IsListStructured`.**  A structured value is a `listNil`-headed or
`listCons`-headed constructor form, OR a bare normal neutral (the `neutralNormal` base case).  The
`valueHeadOrNeutralOfCandidateValue` premise the generic `dataTaitFocusTrichotomyOfValueHeadOrNeutral` consumes to
classify a `dataTaitCandidate IsListStructured` focus into constructor-headed / weak-head-reducible / neutral — full
enumeration over the three structured constructors, the head read off by `rfl`. -/
theorem isListStructured_valueHeadOrNeutral {scope : Nat} {term : RawTerm scope}
    (structured : IsListStructured term) :
    (term.rootGenerator = Generator.gen_listNil ∨ term.rootGenerator = Generator.gen_listCons)
      ∨ IsNeutral term := by
  cases structured with
  | nil => exact Or.inl (Or.inl rfl)
  | neutralNormal isNeutral _isNormal => exact Or.inr isNeutral
  | cons _headNormal _tailIsStructured => exact Or.inl (Or.inr rfl)

/-- **A strongly-normalizing `listCons` cell's head is strongly normalizing.**  The first child reflects strong
normalization along the `listCons` congruence: an infinite head reduction lifts step-by-step (each `Step head
head'` to `Step (listCons head tail) (listCons head' tail)` via `Step.cong` at the `here` child position),
contradicting the cons cell's accessibility.  Inlined one-child accessibility reflection (the generic helper lives
in the eliminator layer, above `Canonicity`). -/
theorem listConsCell_head_isStronglyNormalizing {scope : Nat} {head tail : RawTerm scope}
    (consStronglyNormalizing : IsStronglyNormalizing (listConsCell head tail)) :
    IsStronglyNormalizing head := by
  suffices general : ∀ {parentTerm : RawTerm scope}, Acc StepSuccessor parentTerm →
      ∀ {currentHead : RawTerm scope}, parentTerm = listConsCell currentHead tail →
        Acc StepSuccessor currentHead from
    general consStronglyNormalizing rfl
  intro parentTerm parentAccessible
  induction parentAccessible with
  | intro _parentWitness _parentPredecessors parentInductiveHypothesis =>
      intro currentHead witnessEquation
      subst witnessEquation
      apply Acc.intro
      intro headAfter headStep
      exact parentInductiveHypothesis (listConsCell headAfter tail)
        (Step.cong .gen_listCons ()
          (StepChildren.here (.childCons tail .childNil : RawTermChildren [0] scope) headStep)) rfl

/-- **A strongly-normalizing `listCons` cell's tail is strongly normalizing.**  The second child reflects strong
normalization along the `listCons` congruence at the `there ∘ here` child position (head held fixed).  Inlined
two-position accessibility reflection, the binary twin of `natSuccCell_predecessor_isStronglyNormalizing`. -/
theorem listConsCell_tail_isStronglyNormalizing {scope : Nat} {head tail : RawTerm scope}
    (consStronglyNormalizing : IsStronglyNormalizing (listConsCell head tail)) :
    IsStronglyNormalizing tail := by
  suffices general : ∀ {parentTerm : RawTerm scope}, Acc StepSuccessor parentTerm →
      ∀ {currentTail : RawTerm scope}, parentTerm = listConsCell head currentTail →
        Acc StepSuccessor currentTail from
    general consStronglyNormalizing rfl
  intro parentTerm parentAccessible
  induction parentAccessible with
  | intro _parentWitness _parentPredecessors parentInductiveHypothesis =>
      intro currentTail witnessEquation
      subst witnessEquation
      apply Acc.intro
      intro tailAfter tailStep
      exact parentInductiveHypothesis (listConsCell head tailAfter)
        (Step.cong .gen_listCons ()
          (@StepChildren.there scope 0 [0] head _ _
            (StepChildren.here (.childNil : RawTermChildren [] scope) tailStep))) rfl

/-- **`IsListStructured` cons-inversion.**  If `listCons head tail` is structured then the head is a normal form and
the tail is structured: the `nil` arm is refuted by the head generator (`gen_listCons ≠ gen_listNil`), the
`neutralNormal` arm because a `listCons` cell is never neutral (`ne_listCons`), and the `cons` arm delivers the
head-normality and tail-structure (drilling the two `childCons` injection levels).  The index is generalized to a
free variable BEFORE casing, so the eliminator is full-enumeration (no partial-index `propext` leak — the lean-fx-3
cell-index inversion recipe). -/
theorem isListStructured_cons_inversion {scope : Nat} {head tail : RawTerm scope}
    (structured : IsListStructured (listConsCell head tail)) :
    RawTerm.isStepNormalForm head ∧ IsListStructured tail := by
  generalize subjectEquation : listConsCell head tail = subject at structured
  cases structured with
  | nil =>
      exact Generator.noConfusion (congrArg RawTerm.rootGenerator subjectEquation)
  | neutralNormal isNeutral _isNormal =>
      exact (isNeutral_rootGenerator_ne_listCons isNeutral
        (congrArg RawTerm.rootGenerator subjectEquation).symm).elim
  | @cons consHead consTail headNormal tailStructured =>
      injection subjectEquation with _equationOne _equationTwo _equationThree childrenEquation
      injection childrenEquation with _scopeEq _shiftEq _restShiftsEq headEquation restEquation
      injection restEquation with _scopeEq2 _shiftEq2 _restShiftsEq2 tailEquation
      subst headEquation
      subst tailEquation
      exact ⟨headNormal, tailStructured⟩

/-- **★ Backward tail extraction: a structured-candidate `listCons` cell's tail is a structured candidate member.**
The recursion-descent stone the dependent `listElim` member's cons case consumes to recurse on the tail (the binary
twin of `natSuccStructuredMember_predecessor`).  Both children are strongly normalizing
(`listConsCell_head/tail_isStronglyNormalizing`); each reachable normal form `tailNormal` of the tail, together
with a normal form `headNormal` of the head, lifts under `listCons` to the reachable NORMAL form
`listCons headNormal tailNormal` of the cons cell (BOTH children must be normal for the cell to be — the key binary
difference from nat), which the cons-member classifies as structured (cons-inversion descends to `tailNormal`) or as
neutral (impossible — a `listCons` cell is never neutral). -/
theorem listConsStructuredMember_tail {scope : Nat} {head tail : RawTerm scope}
    (consMember : dataTaitCandidate IsListStructured (listConsCell head tail)) :
    dataTaitCandidate IsListStructured tail := by
  have headSN : IsStronglyNormalizing head := listConsCell_head_isStronglyNormalizing consMember.1
  refine ⟨listConsCell_tail_isStronglyNormalizing consMember.1, ?_⟩
  intro tailNormal tailReaches tailNormalIsNormal
  obtain ⟨headNormal, headReaches, headNormalIsNormal⟩ := exists_normalForm_of_isStronglyNormalizing headSN
  have consReaches : StepStar (listConsCell head tail) (listConsCell headNormal tailNormal) :=
    (listConsStepStarHead headReaches).trans_compose (listConsStepStarTail tailReaches)
  have consNormal : RawTerm.isStepNormalForm (listConsCell headNormal tailNormal) := by
    show (RawTerm.isStepNormalFormBool headNormal
        && (RawTerm.isStepNormalFormBool tailNormal && true)) = true
    rw [show RawTerm.isStepNormalFormBool headNormal = true from headNormalIsNormal,
      show RawTerm.isStepNormalFormBool tailNormal = true from tailNormalIsNormal]
    rfl
  rcases consMember.2 (listConsCell headNormal tailNormal) consReaches consNormal with
      consStructured | consNeutral
  · exact Or.inl (isListStructured_cons_inversion consStructured).2
  · exact (isNeutral_rootGenerator_ne_listCons consNeutral rfl).elim

/-- **A structural-candidate member reaches a structured value.**  The member is strongly normalizing so it reaches
some normal form (`exists_normalForm`), which the membership classifies as structured directly or as a normal
neutral — absorbed into the `neutralNormal` structured constructor.  The structured value the dependent `listElim`
member's outer structural recursion is keyed on.  Identical to the nat twin. -/
theorem listStructuredMemberReachesStructuredValue {scope : Nat} {term : RawTerm scope}
    (member : dataTaitCandidate IsListStructured term) :
    ∃ structuredValue : RawTerm scope, StepStar term structuredValue ∧ IsListStructured structuredValue := by
  obtain ⟨normalForm, reaches, normalFormIsNormal⟩ :=
    exists_normalForm_of_isStronglyNormalizing member.1
  rcases member.2 normalForm reaches normalFormIsNormal with structured | neutral
  · exact ⟨normalForm, reaches, structured⟩
  · exact ⟨normalForm, reaches, IsListStructured.neutralNormal neutral normalFormIsNormal⟩

end FX1Poly.Core

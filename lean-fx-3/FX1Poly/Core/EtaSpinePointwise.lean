import FX1Poly.Core.EtaTableStar

/-! # EtaSpinePointwise — ETA-T5 increment 4.2: the pointwise spine
relation and its lookup bricks

The cong-case stability induction reads an eliminator spine that
differs from the fired spine by ONE eta step in one child.  The
uniform spine hypothesis is pointwise refl-or-step: every position is
either unchanged or related by a single table eta step.  This file
ships the relation, the embedding of one-position steps, and the
shift-0/1/2 lookup bricks (the spine reads the template interpreter
performs).

Unlike the parallel-iota substrate, NO rigid-head inversion is possible
here: the eta intro roots (`gen_lam`, `gen_pair`, …) ARE iota scrutinee
heads, so an eta step at a scrutinee slot may legitimately contract at
the root and change the head — that is the eta/iota duality case,
handled separately by the quasi-commutation's case split (the
`invertOrCong` freed-subject inversion), never by a rigidity
certificate.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaSpinePointwise.lean`. -/

namespace FX1Poly.Core

/-! ## The pointwise refl-or-step relation -/

/-- Pointwise refl-or-step: every spine position is unchanged or
related by ONE table eta step. -/
inductive EtaChildrenPointwise (etaTable : List EtaRuleDesc) :
    {parentScope : Nat} → {binderShifts : List Nat} →
    RawTermChildren binderShifts parentScope →
    RawTermChildren binderShifts parentScope → Prop where
  | nil {parentScope : Nat} :
      EtaChildrenPointwise etaTable
        (RawTermChildren.childNil (scope := parentScope))
        RawTermChildren.childNil
  | consEqual {parentScope headShift : Nat} {restShifts : List Nat}
      (head : RawTerm (parentScope + headShift))
      {rest rest' : RawTermChildren restShifts parentScope}
      (tailRelated : EtaChildrenPointwise etaTable rest rest') :
      EtaChildrenPointwise etaTable
        (RawTermChildren.childCons head rest)
        (RawTermChildren.childCons head rest')
  | consStep {parentScope headShift : Nat} {restShifts : List Nat}
      {head head' : RawTerm (parentScope + headShift)}
      (headStep : StepEtaOverTable etaTable head head')
      {rest rest' : RawTermChildren restShifts parentScope}
      (tailRelated : EtaChildrenPointwise etaTable rest rest') :
      EtaChildrenPointwise etaTable
        (RawTermChildren.childCons head rest)
        (RawTermChildren.childCons head' rest')

/-- Pointwise refl-or-step is reflexive. -/
theorem EtaChildrenPointwise.refl {etaTable : List EtaRuleDesc}
    {parentScope : Nat} :
    {binderShifts : List Nat} →
    (children : RawTermChildren binderShifts parentScope) →
    EtaChildrenPointwise etaTable children children
  | _, .childNil => .nil
  | _, .childCons head rest =>
      .consEqual head (EtaChildrenPointwise.refl rest)

/-- A one-position spine step embeds: the stepped position carries the
step, every other position is unchanged. -/
theorem EtaChildrenPointwise.ofChildrenStep {etaTable : List EtaRuleDesc}
    {parentScope : Nat} :
    {binderShifts : List Nat} →
    {children children' : RawTermChildren binderShifts parentScope} →
    StepEtaOverTableChildren etaTable children children' →
    EtaChildrenPointwise etaTable children children'
  | _, _, _, .here rest headStep =>
      .consStep headStep (EtaChildrenPointwise.refl rest)
  | _, _, _, .there head restStep =>
      .consEqual head
        (EtaChildrenPointwise.ofChildrenStep restStep)

/-! ## The lookup bricks -/

/-- A shift-0 slot read across a pointwise spine: the related spine's
slot holds an equal-or-one-step child. -/
theorem EtaChildrenPointwise.lookupAtShiftZeroRelated
    {etaTable : List EtaRuleDesc} :
    {binderShifts : List Nat} → {scope : Nat} →
    {children children' : RawTermChildren binderShifts scope} →
    EtaChildrenPointwise etaTable children children' →
    (slot : Nat) → {sourceTerm : RawTerm scope} →
    (scopedChildAt? children.toScopedChildren slot).bind
        ScopedChild.atShiftZero?
      = some sourceTerm →
    ∃ targetTerm : RawTerm scope,
      (scopedChildAt? children'.toScopedChildren slot).bind
          ScopedChild.atShiftZero?
        = some targetTerm
      ∧ (sourceTerm = targetTerm
          ∨ StepEtaOverTable etaTable sourceTerm targetTerm)
  | _, _, _, _, .nil, _, _, lookupEq => nomatch lookupEq
  | _, _, _, _,
      @EtaChildrenPointwise.consEqual _ _ headShift _ head _ _
        _tailRelated, 0, _, lookupEq => by
      cases headShift with
      | zero =>
          obtain rfl := Option.some.inj lookupEq
          exact ⟨head, rfl, Or.inl rfl⟩
      | succ _ => exact nomatch lookupEq
  | _, _, _, _,
      @EtaChildrenPointwise.consStep _ _ headShift _ _ _ headStep _ _
        _tailRelated, 0, _, lookupEq => by
      cases headShift with
      | zero =>
          obtain rfl := Option.some.inj lookupEq
          exact ⟨_, rfl, Or.inr headStep⟩
      | succ _ => exact nomatch lookupEq
  | _, _, _, _, .consEqual _ tailRelated, slot + 1, _, lookupEq =>
      EtaChildrenPointwise.lookupAtShiftZeroRelated tailRelated slot
        lookupEq
  | _, _, _, _, .consStep _ tailRelated, slot + 1, _, lookupEq =>
      EtaChildrenPointwise.lookupAtShiftZeroRelated tailRelated slot
        lookupEq

/-- A shift-1 slot read across a pointwise spine. -/
theorem EtaChildrenPointwise.lookupAtShiftOneRelated
    {etaTable : List EtaRuleDesc} :
    {binderShifts : List Nat} → {scope : Nat} →
    {children children' : RawTermChildren binderShifts scope} →
    EtaChildrenPointwise etaTable children children' →
    (slot : Nat) → {sourceBody : RawTerm (scope + 1)} →
    (scopedChildAt? children.toScopedChildren slot).bind
        ScopedChild.atShiftOne?
      = some sourceBody →
    ∃ targetBody : RawTerm (scope + 1),
      (scopedChildAt? children'.toScopedChildren slot).bind
          ScopedChild.atShiftOne?
        = some targetBody
      ∧ (sourceBody = targetBody
          ∨ StepEtaOverTable etaTable sourceBody targetBody)
  | _, _, _, _, .nil, _, _, lookupEq => nomatch lookupEq
  | _, _, _, _,
      @EtaChildrenPointwise.consEqual _ _ headShift _ head _ _
        _tailRelated, 0, _, lookupEq => by
      cases headShift with
      | zero => exact nomatch lookupEq
      | succ priorShift =>
          cases priorShift with
          | zero =>
              obtain rfl := Option.some.inj lookupEq
              exact ⟨head, rfl, Or.inl rfl⟩
          | succ _ => exact nomatch lookupEq
  | _, _, _, _,
      @EtaChildrenPointwise.consStep _ _ headShift _ _ _ headStep _ _
        _tailRelated, 0, _, lookupEq => by
      cases headShift with
      | zero => exact nomatch lookupEq
      | succ priorShift =>
          cases priorShift with
          | zero =>
              obtain rfl := Option.some.inj lookupEq
              exact ⟨_, rfl, Or.inr headStep⟩
          | succ _ => exact nomatch lookupEq
  | _, _, _, _, .consEqual _ tailRelated, slot + 1, _, lookupEq =>
      EtaChildrenPointwise.lookupAtShiftOneRelated tailRelated slot
        lookupEq
  | _, _, _, _, .consStep _ tailRelated, slot + 1, _, lookupEq =>
      EtaChildrenPointwise.lookupAtShiftOneRelated tailRelated slot
        lookupEq

/-- A shift-2 slot read across a pointwise spine. -/
theorem EtaChildrenPointwise.lookupAtShiftTwoRelated
    {etaTable : List EtaRuleDesc} :
    {binderShifts : List Nat} → {scope : Nat} →
    {children children' : RawTermChildren binderShifts scope} →
    EtaChildrenPointwise etaTable children children' →
    (slot : Nat) → {sourceBody : RawTerm (scope + 2)} →
    (scopedChildAt? children.toScopedChildren slot).bind
        ScopedChild.atShiftTwo?
      = some sourceBody →
    ∃ targetBody : RawTerm (scope + 2),
      (scopedChildAt? children'.toScopedChildren slot).bind
          ScopedChild.atShiftTwo?
        = some targetBody
      ∧ (sourceBody = targetBody
          ∨ StepEtaOverTable etaTable sourceBody targetBody)
  | _, _, _, _, .nil, _, _, lookupEq => nomatch lookupEq
  | _, _, _, _,
      @EtaChildrenPointwise.consEqual _ _ headShift _ head _ _
        _tailRelated, 0, _, lookupEq => by
      cases headShift with
      | zero => exact nomatch lookupEq
      | succ priorShift =>
          cases priorShift with
          | zero => exact nomatch lookupEq
          | succ priorPriorShift =>
              cases priorPriorShift with
              | zero =>
                  obtain rfl := Option.some.inj lookupEq
                  exact ⟨head, rfl, Or.inl rfl⟩
              | succ _ => exact nomatch lookupEq
  | _, _, _, _,
      @EtaChildrenPointwise.consStep _ _ headShift _ _ _ headStep _ _
        _tailRelated, 0, _, lookupEq => by
      cases headShift with
      | zero => exact nomatch lookupEq
      | succ priorShift =>
          cases priorShift with
          | zero => exact nomatch lookupEq
          | succ priorPriorShift =>
              cases priorPriorShift with
              | zero =>
                  obtain rfl := Option.some.inj lookupEq
                  exact ⟨_, rfl, Or.inr headStep⟩
              | succ _ => exact nomatch lookupEq
  | _, _, _, _, .consEqual _ tailRelated, slot + 1, _, lookupEq =>
      EtaChildrenPointwise.lookupAtShiftTwoRelated tailRelated slot
        lookupEq
  | _, _, _, _, .consStep _ tailRelated, slot + 1, _, lookupEq =>
      EtaChildrenPointwise.lookupAtShiftTwoRelated tailRelated slot
        lookupEq

end FX1Poly.Core

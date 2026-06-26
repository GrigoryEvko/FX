import FX1Poly.Typed.Metatheory.SubjectReduction.FlatFormationObligationSize

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/FormationObligationSize
    — every formation obligation's subject is a child of the spine (SR-WF-TIEOFF step 2, all families)

The bounded congruence gates (SR-WF-TIEOFF) construct the per-obligation single-step-SR form from the fuel-bounded
`UnionChildSubjectReductionBelow profile cell.size`, applied to each obligation's `subject`.  That needs every
formation obligation to satisfy `obligation.subject.size < children.size` (then `children.size < cell.size` is the
`mkGen` size step `Nat.lt_succ_self`).  This file discharges that for ALL formation families, keyed on the
`FormationRule` enum — the data-table-driven shape: a new former is a new row whose obligation subjects are, by
construction, structural children of its spine, so the generic combiner `formationRuleObligationSubjectSizeBound`
covers it with no new proof.

The three families beyond `flat` (shipped in `FlatFormationObligationSize`):

  * `termIndexedEndpointObligations` — RECURSIVE over the endpoint spine (each endpoint at shift `0`); every
    subject is a spine head, so `< children.size` by induction (mirrors the flat proof).
  * `cumulativeFormationObligations` — a FINITE dispatch (no recursion): the element subject is the spine head
    (List/Option), or the Π/Σ domain (`firstChild`, head) and the binder-crossing codomain (`secondChild`, the
    head of the tail) — all structural children, so `< children.size` (the codomain via transitivity through the
    tail spine).
  * `FormationRule.obligations` — the table combiner: `baseType` demands nothing; `flat` / `cumulative` forward to
    their per-family bounds; `termIndexed` adds the carrier (the spine head) then the endpoints.

## Zero-axiom

Induction on the endpoint spine + `cases` on children / shifts / level lists / `List.Mem` + the `RawSize`
child-decrease lemmas (`size_lt_childCons_head` / `_tail`) + `Nat.lt_trans`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- ★ **Term-indexed endpoint obligation subjects are children.**  `termIndexedEndpointObligations` types every
later child at the fixed `carrier`; each obligation's `subject` is a spine head (at shift `0`), so its size is
strictly below the endpoint spine's.  Recursive — induction on the spine, mirroring the flat proof. -/
theorem termIndexedEndpointObligationSubjectSizeBound {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (carrier : RawTerm scope) :
    ∀ {shifts : List Nat} (children : RawTermChildren shifts scope),
      ∀ obligation ∈ termIndexedEndpointObligations profile context carrier children,
        obligation.subject.size < children.size := by
  intro shifts
  induction shifts with
  | nil =>
      intro children _obligation obligationMem
      cases children
      cases obligationMem
  | cons childShift _restShifts restIH =>
      intro children obligation obligationMem
      cases children with
      | childCons head rest =>
          cases childShift with
          | succ _childShiftPredecessor => cases obligationMem
          | zero =>
              cases obligationMem with
              | head => exact RawTermChildren.size_lt_childCons_head head rest
              | tail _ tailMem =>
                  exact Nat.lt_trans (restIH rest obligation tailMem)
                    (RawTermChildren.size_lt_childCons_tail head rest)

/-- ★ **Cumulative formation obligation subjects are children.**  A List/Option spine yields the single element
obligation (the head); a Π/Σ spine yields the domain (head) and the binder-crossing codomain (head of the tail).
Each subject is a structural child of `children`, so `< children.size` — the codomain through transitivity
(`secondChild < tail spine < children`).  Finite dispatch — no recursion, just exhaustive `cases`. -/
theorem cumulativeFormationObligationSubjectSizeBound {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag) :
    ∀ {binderShifts : List Nat} (children : RawTermChildren binderShifts scope) (levels : List LevelExpr),
      ∀ obligation ∈ cumulativeFormationObligations profile context flag children levels,
        obligation.subject.size < children.size := by
  intro binderShifts
  cases binderShifts with
  | nil =>
      intro children _levels _obligation obligationMem
      cases children
      cases obligationMem
  | cons firstShift restShifts =>
      intro children levels obligation obligationMem
      cases children with
      | childCons firstChild restChildren =>
          cases firstShift with
          | succ _firstShiftPredecessor => cases obligationMem
          | zero =>
              cases restShifts with
              | nil =>
                  cases restChildren with
                  | childNil =>
                      cases levels with
                      | nil =>
                          cases obligationMem with
                          | head =>
                              exact RawTermChildren.size_lt_childCons_head firstChild RawTermChildren.childNil
                          | tail _ emptyMem => cases emptyMem
                      | cons _elementLevel _restLevels =>
                          cases obligationMem with
                          | head =>
                              exact RawTermChildren.size_lt_childCons_head firstChild RawTermChildren.childNil
                          | tail _ emptyMem => cases emptyMem
              | cons secondShift _tailShifts =>
                  cases restChildren with
                  | childCons secondChild tailChildren =>
                      cases secondShift with
                      | zero => cases obligationMem
                      | succ secondShiftPredecessor =>
                          cases secondShiftPredecessor with
                          | succ _ => cases obligationMem
                          | zero =>
                              cases tailChildren with
                              | childCons _ _ => cases obligationMem
                              | childNil =>
                                  cases levels with
                                  | nil =>
                                      cases obligationMem with
                                      | head =>
                                          exact RawTermChildren.size_lt_childCons_head firstChild
                                            (RawTermChildren.childCons secondChild RawTermChildren.childNil)
                                      | tail _ tailMem =>
                                          cases tailMem with
                                          | head =>
                                              exact Nat.lt_trans
                                                (RawTermChildren.size_lt_childCons_head secondChild
                                                  RawTermChildren.childNil)
                                                (RawTermChildren.size_lt_childCons_tail firstChild
                                                  (RawTermChildren.childCons secondChild RawTermChildren.childNil))
                                          | tail _ emptyMem => cases emptyMem
                                  | cons _domainLevel restLevels =>
                                      cases restLevels with
                                      | nil =>
                                          cases obligationMem with
                                          | head =>
                                              exact RawTermChildren.size_lt_childCons_head firstChild
                                                (RawTermChildren.childCons secondChild RawTermChildren.childNil)
                                          | tail _ tailMem =>
                                              cases tailMem with
                                              | head =>
                                                  exact Nat.lt_trans
                                                    (RawTermChildren.size_lt_childCons_head secondChild
                                                      RawTermChildren.childNil)
                                                    (RawTermChildren.size_lt_childCons_tail firstChild
                                                      (RawTermChildren.childCons secondChild
                                                        RawTermChildren.childNil))
                                              | tail _ emptyMem => cases emptyMem
                                      | cons _codomainLevel _restRestLevels =>
                                          cases obligationMem with
                                          | head =>
                                              exact RawTermChildren.size_lt_childCons_head firstChild
                                                (RawTermChildren.childCons secondChild RawTermChildren.childNil)
                                          | tail _ tailMem =>
                                              cases tailMem with
                                              | head =>
                                                  exact Nat.lt_trans
                                                    (RawTermChildren.size_lt_childCons_head secondChild
                                                      RawTermChildren.childNil)
                                                    (RawTermChildren.size_lt_childCons_tail firstChild
                                                      (RawTermChildren.childCons secondChild
                                                        RawTermChildren.childNil))
                                              | tail _ emptyMem => cases emptyMem

/-- ★ **The table-driven formation obligation size bound.**  Keyed on the `FormationRule` enum: `baseType`
demands nothing; `flat` / `cumulative` forward to their per-family bounds; `termIndexed` adds the carrier (the
spine head) then forwards the endpoints.  EVERY formation obligation's subject is a structural child of the
former's children spine, so its size is `< children.size`.  Composed with `Nat.lt_succ_self` (the `mkGen` size
step `children.size < cell.size`) at the bounded gate, this gives the `< cell.size` bound the fuel-bounded
single-step SR consumes.  A NEW formation row is covered automatically — its obligation subjects are children by
construction. -/
theorem formationRuleObligationSubjectSizeBound {profile : PolyProfile} {scope : Nat}
    (rule : FormationRule) (context : TypingContext profile scope) (carrier : RawTerm scope)
    (level : LevelExpr) (flag : UniverseFlag) :
    ∀ {binderShifts : List Nat} (children : RawTermChildren binderShifts scope) (levels : List LevelExpr),
      ∀ obligation ∈ rule.obligations profile context children levels carrier level flag,
        obligation.subject.size < children.size := by
  cases rule with
  | baseType _ =>
      intro _binderShifts _children _levels _obligation obligationMem
      cases obligationMem
  | flat _ =>
      intro _binderShifts children levels
      exact flatFormationObligationSubjectSizeBound context flag children levels
  | cumulative _ =>
      intro _binderShifts children levels
      exact cumulativeFormationObligationSubjectSizeBound context flag children levels
  | termIndexed _ =>
      intro binderShifts
      cases binderShifts with
      | nil =>
          intro children _levels _obligation obligationMem
          cases children
          cases obligationMem
      | cons carrierShift _restShifts =>
          intro children _levels obligation obligationMem
          cases children with
          | childCons carrierHead rest =>
              cases carrierShift with
              | succ _carrierShiftPredecessor => cases obligationMem
              | zero =>
                  cases obligationMem with
                  | head => exact RawTermChildren.size_lt_childCons_head carrierHead rest
                  | tail _ tailMem =>
                      exact Nat.lt_trans
                        (termIndexedEndpointObligationSubjectSizeBound context carrier rest obligation tailMem)
                        (RawTermChildren.size_lt_childCons_tail carrierHead rest)

end FX1Poly.Typed

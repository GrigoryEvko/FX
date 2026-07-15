import FX1Poly.Typed.Engine.RuleTables.FormationRuleTable
import FX1Poly.Axis.Term.Core.RawSize

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/FlatFormationObligationSize
    — flat-formation obligation subjects are strictly smaller than the cell (SR-WF-TIEOFF step 2, flat family)

The bounded congruence gates (SR-WF-TIEOFF) construct the per-obligation single-step-SR form from the fuel-bounded
`UnionChildSubjectReductionBelow profile cell.size`, applied to each obligation's subject.  That needs
`obligation.subject.size < cell.size`.  For the FLAT formation family this holds UNIFORMLY: every obligation
produced by `flatFormationObligations` has `subject := head` for a `head` of the children spine (a structural
child, never an existential type param), so its size is strictly below the children spine's, hence strictly below
the `mkGen` cell's (`RawSize` child-decrease).

`flatFormationObligationSubjectSizeBound` proves exactly this — by induction on the spine length `binderShifts`,
mirroring `flatFormationObligations`'s own recursion: the head obligation's subject is the head child
(`size_lt_childCons_head`), tail obligations recurse into the smaller tail spine (`size_lt_childCons_tail` +
transitivity).  This is the per-family size discharge the bounded flat-formation gate consumes; the proof that the
bounded approach mechanically closes for a whole family (de-risking the remaining termIndexed / cumulative / intro
/ elim families).

## Zero-axiom

`induction binderShifts` + `cases` on children / level list / `List.Mem` + the `RawSize` child-decrease lemmas +
`Nat.lt_trans`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- ★ **Flat-formation obligation subjects are strictly smaller than the children spine.**  Every obligation in
`flatFormationObligations` has its `subject` a structural child of `children` (the spine head at some depth), so
its size is `< children.size`.  Composed with the `mkGen` size step (`children.size < cell.size`,
`Nat.lt_succ_self`) at the gate, this gives the `< cell.size` bound the fuel-bounded child-SR needs. -/
theorem flatFormationObligationSubjectSizeBound {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag) :
    ∀ {binderShifts : List Nat} (children : RawTermChildren binderShifts scope) (levels : List LevelExpr),
      ∀ obligation ∈ flatFormationObligations profile context flag children levels,
        obligation.subject.size < children.size := by
  intro binderShifts
  induction binderShifts with
  | nil =>
      intro children _levels _obligation obligationMem
      cases children
      cases obligationMem
  | cons childShift _restShifts restIH =>
      intro children levels obligation obligationMem
      cases children with
      | childCons head rest =>
          cases childShift with
          | succ _childShiftPredecessor => cases obligationMem
          | zero =>
              cases levels with
              | nil =>
                  cases obligationMem with
                  | head => exact RawTermChildren.size_lt_childCons_head head rest
                  | tail _ tailMem =>
                      exact Nat.lt_trans (restIH rest [] obligation tailMem)
                        (RawTermChildren.size_lt_childCons_tail head rest)
              | cons _headLevel restLevels =>
                  cases obligationMem with
                  | head => exact RawTermChildren.size_lt_childCons_head head rest
                  | tail _ tailMem =>
                      exact Nat.lt_trans (restIH rest restLevels obligation tailMem)
                        (RawTermChildren.size_lt_childCons_tail head rest)

end FX1Poly.Typed

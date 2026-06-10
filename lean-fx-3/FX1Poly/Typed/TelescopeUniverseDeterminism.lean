import FX1Poly.Typed.NormalAppNeutral
import FX1Poly.Typed.PlateauDescentSubstrate

/-! # FX1Poly/Typed/TelescopeUniverseDeterminism — grown telescope universe determinism
     (route-H reflection, E2.7 former-arm core — table-generic, IH-parameterized)

Two `DescTelescopePi` telescopes over the SAME children agree on the level list, and on the flag
whenever the children are nonempty — the determinism that makes the row-bearing former arm of
same-subject universe-classification uniqueness provable.  Parameterized by the child IH (the
strong-size-induction seam): the head child is classified by BOTH telescopes at their respective
(level, flag), the IH negotiates them equal, and the level list follows pointwise; the budget
descends through `RawTermChildren.size` peeling (`head.size + rest.size + 1`), normality through
the `areStepNormalFormsBool` head/tail peels.  Nil telescopes agree on levels trivially; their
flag clause is vacuous (and unreachable from row-bearing formers — all rows are ≥1-child, the
nullary formers having NO `typingRuleDescOf` row).

Mechanics: term-mode match on the FIRST telescope (the mutual block forbids `induction`), the
second ∀-quantified in the conclusion and inverted per-arm by `cases` at the then-concrete
children index — the `convTelescopeFromChildIH` template.

## Zero-axiom verification

No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

theorem DescTelescopePi.universeDeterminismOfChildIH {profile : PolyProfile} {budget : Nat}
    (childIH : ∀ {childScope : Nat} (childContext : TypingContext profile childScope)
        (child : RawTerm childScope) {firstLevel secondLevel : LevelExpr}
        {firstFlag secondFlag : UniverseFlag},
        child.size ≤ budget → RawTerm.isStepNormalForm child →
        HasTypeDescPi profile childContext child (universeCodeCell firstLevel firstFlag) →
        HasTypeDescPi profile childContext child (universeCodeCell secondLevel secondFlag) →
        firstLevel = secondLevel ∧ firstFlag = secondFlag)
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {firstLevels : List LevelExpr} {firstFlag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (firstTelescope : DescTelescopePi profile context firstLevels firstFlag children) :
    ∀ {secondLevels : List LevelExpr} {secondFlag : UniverseFlag},
      DescTelescopePi profile context secondLevels secondFlag children →
      RawTermChildren.size children ≤ budget →
      RawTermChildren.areStepNormalFormsBool children = true →
      firstLevels = secondLevels ∧ (firstLevels ≠ [] → firstFlag = secondFlag) :=
  match firstTelescope with
  | .nil _context _flag =>
      fun secondTelescope _sizeBound _childrenNormal => by
        cases secondTelescope
        exact ⟨rfl, fun nonempty => absurd rfl nonempty⟩
  | .cons _context head headLevel restLevels _flag rest headTyped restTyped =>
      fun secondTelescope sizeBound childrenNormal => by
        cases secondTelescope with
        | cons _context₂ _head₂ secondHeadLevel secondRestLevels _flag₂ _rest₂
            secondHeadTyped secondRestTyped =>
          have headSizeBound : head.size ≤ budget :=
            Nat.le_trans
              (Nat.le_succ_of_le (Nat.le_add_right head.size (RawTermChildren.size rest)))
              sizeBound
          have restSizeBound : RawTermChildren.size rest ≤ budget :=
            Nat.le_trans
              (Nat.le_succ_of_le (Nat.le_add_left (RawTermChildren.size rest) head.size))
              sizeBound
          have headNormal : RawTerm.isStepNormalForm head :=
            RawTermChildren.areStepNormalFormsBool_head childrenNormal
          have restNormal : RawTermChildren.areStepNormalFormsBool rest = true :=
            RawTermChildren.areStepNormalFormsBool_tail childrenNormal
          obtain ⟨headLevelsAgree, flagsAgree⟩ :=
            childIH _ head headSizeBound headNormal headTyped secondHeadTyped
          subst flagsAgree
          obtain ⟨restLevelsAgree, _restFlags⟩ :=
            DescTelescopePi.universeDeterminismOfChildIH childIH
              restTyped secondRestTyped restSizeBound restNormal
          exact ⟨by rw [headLevelsAgree, restLevelsAgree], fun _ => rfl⟩

end FX1Poly.Typed


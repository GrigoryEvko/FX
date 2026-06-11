import FX1Poly.Typed.BoolElimValueCanonicity
import FX1Poly.Typed.NatElimComputingCanonicity
import FX1Poly.Typed.ListElimComputingCanonicity
import FX1Poly.Typed.MatchElimComputingCanonicityTyped

/-! # FX1Poly/Typed/MilestoneAEliminatorLayerSpine
    — the ELIMINATOR-LAYER canonicity spine: every data eliminator computes its closed instances to a value

`MilestoneASpineValueLayer` (firing-62) bundled the three VALUE-layer soundness pillars (SN / consistency /
value-layer bool canonicity) and explicitly named the **eliminator layer** as the deferred frontier:

  > `boolCanonicity` covers closed terms typed at `boolType` by the three value/formation engines.  It does NOT
  > yet cover ELIMINATOR-typed bools (`boolElim …`) … fully-non-vacuous eliminator-computing canonicity is the
  > follow-on (CANON-1).

That follow-on is now SHIPPED per-eliminator — across five distinct files, one per data eliminator — and this
file bundles them into ONE checked capstone, discharging the deferred eliminator-layer frontier:

  1. **bool** — `boolElimValueCanonicity`: a closed `boolElim b t e : Bool` (data-VALUE branches, via the
     non-vacuous `HasTypeDescBoolElimValue` engine) computes by a single ι-step to a bool value.
  2. **nat** (RECURSIVE) — `natElimCopyComputesToNumeral`: a closed `natElim(motive, natZero, natSucc (var 0), n)`
     (Phase-Z SUBSTITUTING shape — the succ-branch `natSucc (var 0)` is a two-binder term, the succ-ι substitutes
     the recursive call into `var 0`) computes to a numeral for every closed numeral `n` — the
     recursive-result-USING fold (IH-threaded, not discarded), the genuinely recursive eliminator.
  3. **list** (RECURSIVE) — `listElimLengthComputesToNumeral`: a closed `listElim(motive, xs, natZero,
     lengthStep)` computes to a numeral (the length) for every closed list value `xs` (Phase-Z motive shape —
     the stored motive head child is ignored by the length fold).
  4. **option** — `closedOptionMatchIntoBoolComputes` (firing-64): a closed `optionMatch(m, boolTrue,
     λ_.boolTrue, scrutinee)` with a typed option scrutinee computes to a bool value (Phase-Z motive shape —
     the stored motive head child is discarded by the ι).
  5. **either** — `closedEitherMatchIntoBoolComputes` (firing-64): the either twin.

## Honest scope — what this is and is NOT

  * **This is the COMPUTING-canonicity layer**, the eliminator analogue of value-layer canonicity: every CLOSED
    WELL-FORMED eliminator instance reduces to a canonical value.  It covers all five data eliminators with
    representative branches (the bool value-branch engine; the recursive nat/list folds; the option/either
    constant-bool match).  Each field is a shipped unconditional theorem.
  * **This is NOT a single unified `eliminator … : dataType` typing judgment.**  The bool eliminator uses its
    dedicated value-branch engine `HasTypeDescBoolElimValue`; the nat/list/option/either eliminators are stated
    operationally (scrutinee well-formedness + the shipped ι/β computation).  Folding all data eliminators into
    ONE combined intro/elim table judgment (so `natElim … : Nat` is a first-class derivation feeding its branch
    typing unconditionally into the step obligation) remains the GTL table-residency integration — the formation/
    grown half of which (`GTL-18`/`GTL-20`) is shipped, the data-elim half of which is the open extension.
  * **The fully-GENERAL branch case** (a payload-USING option/either branch, or an arbitrary `stepProduces` for
    nat/list) is captured ABSTRACTLY in the per-eliminator files (`natElimComputesToNumeral` /
    `optionMatchComputesToValue` take the step/branch behavior as a hypothesis); this spine bundles the
    UNCONDITIONAL concrete instances.

So this is the honest eliminator-layer sign-off: every data eliminator computes its closed instances to a value,
zero-axiom — the deferred frontier of the value-layer spine, now discharged, with the unified combined-engine
judgment the named remaining integration.

## Zero-axiom verification

`eliminatorLayerCanonicitySpineHolds` is a five-field record whose fields are the shipped
`boolElimValueCanonicity` / `natElimCopyComputesToNumeral` / `listElimLengthComputesToNumeral` /
`closedOptionMatchIntoBoolComputes` / `closedEitherMatchIntoBoolComputes`.  Confirmed `#print axioms`-clean.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The eliminator-layer canonicity spine.**  Five fields, one per data eliminator (bool / nat / list / option
/ either), each asserting that a closed well-formed instance of that eliminator reduces to a canonical value.  A
`Prop` record — the joint eliminator-layer computing-canonicity claim as a single object, the eliminator analogue
of `MilestoneAValueLayerSpine`. -/
structure EliminatorLayerCanonicitySpine (profile : PolyProfile) : Prop where
  /-- bool: a closed `boolElim b t e : Bool` (value-branch engine) computes to a bool value. -/
  boolElimComputes : ∀ {subject : RawTerm 0},
    HasTypeDescBoolElimValue profile (TypingContext.empty : TypingContext profile 0) subject boolTypeCell →
      ∃ value : RawTerm 0, StepStar subject value ∧ (value = boolTrueCell ∨ value = boolFalseCell)
  /-- nat (recursive): the recursive-result-using copy fold computes every closed numeral to a numeral.  Phase-Z
  motive shape: the `natElim` cell carries a stored motive head child (any motive — the copy fold ignores it). -/
  natElimComputes : ∀ {motive : RawTerm 1} {scrutinee : RawTerm 0}, IsNatNumeral scrutinee →
      ∃ out : RawTerm 0,
        StepStar (natElimCell motive natZeroCell copyNatBranch scrutinee) out ∧ IsNatNumeral out
  /-- list (recursive): the length fold computes every closed list value to a numeral.  Phase-Z motive shape:
  the `listElim` cell carries a stored motive head child (any motive — the length fold ignores it). -/
  listElimComputes : ∀ {motive : RawTerm 1} {scrutinee : RawTerm 0}, IsListValue scrutinee →
      ∃ out : RawTerm 0,
        StepStar (listElimCell motive scrutinee natZeroCell lengthNatStep) out ∧ IsNatNumeral out
  /-- option: a closed `optionMatch` with a typed option scrutinee and constant bool branches computes to a bool.
  Phase-Z motive shape: the `optionMatch` cell carries a stored motive head child (any motive — the ι discards it). -/
  optionMatchComputes : ∀ {motive : RawTerm 1} {scrutinee elementType : RawTerm 0},
    (HasTypeDescOptionIntro profile (TypingContext.empty : TypingContext profile 0) scrutinee
        (optionTypeCell elementType) ∨
     HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) scrutinee
        (optionTypeCell elementType)) →
      ∃ out : RawTerm 0,
        StepStar (optionMatchCell motive boolTrueCell
          (lamCell boolTrueCell (boolTrueCell : RawTerm 1)) scrutinee) out ∧
        (out = boolTrueCell ∨ out = boolFalseCell)
  /-- either: the either twin of `optionMatchComputes`. -/
  eitherMatchComputes : ∀ {motive : RawTerm 1} {scrutinee leftType rightType : RawTerm 0},
    (HasTypeDescEitherIntro profile (TypingContext.empty : TypingContext profile 0) scrutinee
        (eitherTypeCell leftType rightType) ∨
     HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0) scrutinee
        (eitherTypeCell leftType rightType)) →
      ∃ out : RawTerm 0,
        StepStar (eitherMatchCell motive (lamCell boolTrueCell (boolTrueCell : RawTerm 1))
          (lamCell boolTrueCell (boolFalseCell : RawTerm 1)) scrutinee) out ∧
        (out = boolTrueCell ∨ out = boolFalseCell)

/-- **★ The eliminator-layer canonicity spine holds, unconditionally, zero-axiom.**  Each field is the shipped
unconditional computing-canonicity theorem for that data eliminator.  The eliminator-layer sign-off discharging
the frontier `MilestoneAValueLayerSpine` (firing-62) deferred — with the unified combined intro/elim judgment the
named remaining integration (see the file docstring). -/
theorem eliminatorLayerCanonicitySpineHolds {profile : PolyProfile} :
    EliminatorLayerCanonicitySpine profile where
  boolElimComputes derivation := boolElimValueCanonicity derivation
  natElimComputes scrutineeNumeral := natElimCopyComputesToNumeral scrutineeNumeral
  listElimComputes scrutineeValue := listElimLengthComputesToNumeral scrutineeValue
  optionMatchComputes scrutineeTyped := closedOptionMatchIntoBoolComputes scrutineeTyped
  eitherMatchComputes scrutineeTyped := closedEitherMatchIntoBoolComputes scrutineeTyped

end FX1Poly.Typed

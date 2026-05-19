import Lean
import LeanFX2.Term.Pointwise.PointwiseAndCompositionInfrastructure

/-! # Tools/Tactics/Choreography

Small project-wide proof choreography helpers.

These tactics are deliberately thin syntax shorthands over kernel-checked
proof terms.  They do not search broadly, install global simp rules, or
change production import boundaries.  The intended use is to remove repeated
Option, HEq, cast, and `rfl` boilerplate while keeping every proof obligation
visible to Lean's kernel.
-/

namespace LeanFX2

universe tacticUniverse

/-- A known `some` result contradicts a later `none` branch for the same
Option computation. -/
theorem optionSomeContradictsNone {someType : Type tacticUniverse}
    {someValue : someType} {optionValue : Option someType}
    (someSuccess : optionValue = some someValue)
    (noneSuccess : optionValue = none) : False := by
  cases someSuccess.symm.trans noneSuccess

/-- Two successful `some` observations of the same Option computation have
equal payloads. -/
theorem optionSomePayloadEq_of_sameOptionSuccess
    {someType : Type tacticUniverse}
    {leftValue rightValue : someType}
    {optionValue : Option someType}
    (leftSuccess : optionValue = some leftValue)
    (rightSuccess : optionValue = some rightValue) :
    leftValue = rightValue :=
  Option.some.inj (leftSuccess.symm.trans rightSuccess)

/-- `none.isSome = true` is impossible. -/
theorem optionNoneIsSomeContradictsTrue {someType : Type tacticUniverse}
    (isSomeNone : Option.isSome (none : Option someType) = true) : False := by
  cases isSomeNone

namespace Tools.Tactics

/-- Close a goal by `rfl` or `HEq.rfl`. -/
macro "fx_rfl" : tactic =>
  `(tactic| first | rfl | exact HEq.rfl)

/-- Destruct one proof/object and close all generated goals by `rfl` or
`HEq.rfl`.  Useful for local constructor-injectivity and cast-erasure
micro-goals. -/
syntax "fx_cases_rfl " Lean.Parser.Tactic.elimTarget : tactic
macro_rules
  | `(tactic| fx_cases_rfl $scrutinee) =>
      `(tactic| cases $scrutinee <;> first | rfl | exact HEq.rfl)

/-- Close an arbitrary goal from incompatible `some` and `none` observations
of the same Option expression. -/
syntax "fx_contradict_none " term " with " term : tactic
macro_rules
  | `(tactic| fx_contradict_none $someSuccess with $noneSuccess) =>
      `(tactic|
        exact False.elim
          (LeanFX2.optionSomeContradictsNone $someSuccess $noneSuccess))

/-- Create the payload equality from two successful observations of the same
Option expression. -/
syntax "fx_some_payload_eq " ident " from " term " and " term : tactic
macro_rules
  | `(tactic| fx_some_payload_eq $equalName from $leftSuccess and $rightSuccess) =>
      `(tactic|
        have $equalName :=
          LeanFX2.optionSomePayloadEq_of_sameOptionSuccess
            $leftSuccess $rightSuccess)

/-- Create and immediately substitute the payload equality from two
successful observations of the same Option expression. -/
syntax "fx_subst_some_payload " ident " from " term " and " term : tactic
macro_rules
  | `(tactic|
      fx_subst_some_payload $equalName from $leftSuccess and $rightSuccess) =>
      `(tactic|
        have $equalName :=
          LeanFX2.optionSomePayloadEq_of_sameOptionSuccess
            $leftSuccess $rightSuccess;
        subst $equalName)

/-- Close an arbitrary goal from a proof that `none.isSome = true`. -/
syntax "fx_contradict_none_isSome " term : tactic
macro_rules
  | `(tactic| fx_contradict_none_isSome $isSomeNone) =>
      `(tactic|
        exact False.elim
          (LeanFX2.optionNoneIsSomeContradictsTrue $isSomeNone))

/-- Expose the common strengthening dispatcher head.  This is intentionally
only an unfold step plus `split`; it does not try to solve the generated
branches. -/
macro "fx_split_strength_dispatcher" : tactic =>
  `(tactic|
    unfold strengthenTyped?
    unfold partialStrengthenTyped?
    split)

/-- Close one-step Term cast HEq goals using the audited cast lemmas already
present in the Term pointwise infrastructure.  This tactic performs no broad
search; it tries only the known cast-erasure helper family. -/
macro "fx_heq_cast" : tactic =>
  `(tactic|
    first
      | exact Term.type_eq_cast_heq _ _
      | exact Term.type_eq_symm_cast_heq _
      | exact Term.raw_eq_cast_heq _ _
      | exact Term.type_raw_eq_cast_heq _ _ _
      | exact Term.subst_type_eq_cast_heq _ _ _
      | exact Term.rename_type_eq_cast_heq _ _ _
      | exact Term.rename_type_eq_symm_cast_heq _ _
      | exact cast_heq _ _)

end Tools.Tactics

end LeanFX2

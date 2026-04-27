import FX.Elab.Elaborate
import FX.Kernel.Grade

/-!
# Q53 — `modeToGrade` surface→kernel mapping tests

Pins the refined surface `ParamMode` → kernel `Grade` mapping
defined in `FX/Elab/Elaborate.lean` against accidental
regression.  Every arm of the table is exercised and the
resulting `Grade.usage` inspected.

Historical defect caught here: pre-Q53, every non-ghost mode
collapsed to `Grade.default` (usage = 1), so `ref x: Nat` was
indistinguishable from `own x: Nat` at the kernel layer.  A
future refactor that re-merges arms or drops the `.ref_ →
Grade.shared` arm will break the multi-use parameter pattern
(`times`, `mul`, etc.) from conformance 34 — this file fires
the canary before the conformance runner does.
-/

namespace Tests.Elab.ModeToGradeTests

open FX.Elab
open FX.Kernel
open FX.Syntax.Ast

/-! ## usage per mode -/

example : (modeToGrade ParamMode.ghost).usage = Usage.zero := by
  native_decide

example : (modeToGrade ParamMode.ref_).usage = Usage.omega := by
  native_decide

example : (modeToGrade ParamMode.affine).usage = Usage.omega := by
  native_decide

example : (modeToGrade ParamMode.own).usage = Usage.one := by
  native_decide

example : (modeToGrade ParamMode.refMut).usage = Usage.one := by
  native_decide

example : (modeToGrade ParamMode.linear).usage = Usage.one := by
  native_decide

example : (modeToGrade ParamMode.secret).usage = Usage.one := by
  native_decide

example : (modeToGrade ParamMode.default_).usage = Usage.one := by
  native_decide

/-! ## equality to named grades (via BEq — `Grade` derives only
`Repr`, not `DecidableEq`, so direct `=` won't decide; the kernel
provides `instance : BEq Grade` and the tests use `==`). -/

example : (modeToGrade ParamMode.ghost == Grade.ghost) = true := by native_decide

example : (modeToGrade ParamMode.ref_ == Grade.shared) = true := by native_decide

example : (modeToGrade ParamMode.affine == Grade.shared) = true := by native_decide

example : (modeToGrade ParamMode.own == Grade.default) = true := by native_decide

example : (modeToGrade ParamMode.refMut == Grade.default) = true := by native_decide

example : (modeToGrade ParamMode.linear == Grade.default) = true := by native_decide

example : (modeToGrade ParamMode.secret == Grade.default) = true := by native_decide

example : (modeToGrade ParamMode.default_ == Grade.default) = true := by native_decide

/-! ## `Grade.shared` is `Grade.default` except on usage —
other 20 dims untouched, so security / trust / effect defaults
still apply to ref-bound bindings. -/

example : Grade.shared.security = Grade.default.security := by native_decide

example : Grade.shared.trust = Grade.default.trust := by native_decide

example : Grade.shared.effect = Grade.default.effect := by native_decide

example : Grade.shared.clock = Grade.default.clock := by native_decide

example : Grade.shared.usage = Usage.omega := by native_decide

example : (Grade.shared == Grade.default) = false := by native_decide

example : (Grade.shared == Grade.ghost) = false := by native_decide

end Tests.Elab.ModeToGradeTests

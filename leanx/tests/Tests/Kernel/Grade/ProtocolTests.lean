import FX.Kernel.Grade.Protocol

/-!
# Protocol dimension tests

Session-type state — `{consumed, active}` carrier.  Phase-1
coarse algebra: `add` and `mul` both require the two arms to
agree on state, else return `none`.  The full session-type
algebra (with send/receive/branch and per-step state) is
Phase-6 work sitting above this kernel interface.
-/

namespace Tests.Kernel.Grade.Protocol

open FX.Kernel
open FX.Kernel.Protocol

/-! ## `add` — parallel combine

Agreement on state is required.  Mixed combinations signal
session divergence across parallel arms (e.g., two branches of
an `if` sharing a channel binding disagree on whether the
channel was terminated).
-/

example : add consumed consumed = some consumed := rfl
example : add active   active   = some active   := rfl

example : add consumed active   = none := rfl
example : add active   consumed = none := rfl

/-! ## `mul` — sequential combine

Same algebra as `add` in the coarse Phase-1 carrier.
-/

example : mul consumed consumed = some consumed := rfl
example : mul active   active   = some active   := rfl

example : mul consumed active   = none := rfl
example : mul active   consumed = none := rfl

/-! ## Subsumption — refl only

Phase-1 coarse carrier admits only reflexive `LessEq`.  The
two carrier elements describe genuinely different protocol
lifetimes and cannot substitute for each other.
-/

example : LessEq consumed consumed := LessEq.refl _
example : LessEq active   active   := LessEq.refl _

example : ¬ LessEq consumed active := by decide
example : ¬ LessEq active   consumed := by decide

/-! ## Laws -/

example : add consumed consumed = add consumed consumed := add_comm _ _
example : add active   active   = add active   active   := add_comm _ _
example : add consumed active   = add active   consumed := by native_decide

example : add consumed consumed = some consumed := add_idem _
example : add active   active   = some active   := add_idem _

example : mul consumed consumed = mul consumed consumed := mul_comm _ _
example : mul consumed consumed = some consumed := mul_idem _
example : mul active   active   = some active   := mul_idem _

/-! ## DecidableEq — used by aggregator `Grade.beq` -/

example : (consumed == consumed) = true  := by native_decide
example : (active   == active)   = true  := by native_decide
example : (consumed == active)   = false := by native_decide

end Tests.Kernel.Grade.Protocol

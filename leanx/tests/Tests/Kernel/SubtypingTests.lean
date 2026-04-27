import FX.Kernel.Subtyping
import FX.Kernel.Term

/-!
# Subtyping tests (A7, Appendix H.9 T-sub)

Compile-time tests for the Pi and Sigma subtyping arms added to
`subOrConv`.  Universe-cumulativity tests already live in
`ConversionTests.lean`; this file focuses on the A7 additions.

## Sections

 1. Pi domain contravariance — broader callee domain accepts
    caller passing narrower-typed arguments.
 2. Pi codomain covariance — narrower callee return fits where
    broader return expected.
 3. Pi composed contra+co — both positions vary together.
 4. Sigma covariance in both positions.
 5. Rejection cases — wrong variance direction fails.
 6. Grade-mismatch — strict grade equality on binders (no
    grade-subsumption bridging across direct Pi/Sigma).
 7. `Term.sub` alias from `FX.Kernel.Subtyping` resolves.

## De Bruijn convention

Inside a Pi/Sigma, `var 0` in the body refers to the Pi's own
binder.  For the tests we use "constant body" Pi/Sigma where the
body is a ground type with no free references to the binder —
this avoids the distraction of different binder indexes mattering
to the subtyping result.
-/

namespace Tests.Kernel.SubtypingTests

open FX.Kernel
open FX.Kernel.Term

/-! ## Fixtures -/

def typeZero : Term := .type .zero
def typeOne  : Term := .type (.succ .zero)
def typeTwo  : Term := .type (.succ (.succ .zero))

/-- Helper: `Term.subOrConv defaultFuel left right` with the
    default empty `GlobalEnv`.  Returns a `Bool`. -/
def subs (left right : Term) : Bool :=
  Term.subOrConv Term.defaultFuel left right

/-- Same using the `Term.sub` alias from `FX.Kernel.Subtyping`. -/
def subsViaAlias (left right : Term) : Bool :=
  Term.sub Term.defaultFuel left right

/-! ## 1. Pi domain contravariance

`Pi(_:A)→B <: Pi(_:A')→B`  iff  `A' <: A`.  Callee accepts a
broader domain, caller passes a narrower one — safe. -/

-- Type<0> <: Type<1> via U-cumul, so reversing that domain gives
-- Pi(_:Type<1>)→B <: Pi(_:Type<0>)→B.
example :
  subs (.piTot Grade.default typeOne  typeZero)
       (.piTot Grade.default typeZero typeZero) = true := by native_decide

-- Trivially a subtype when domains are equal.
example :
  subs (.piTot Grade.default typeZero typeZero)
       (.piTot Grade.default typeZero typeZero) = true := by native_decide

-- Wrong direction: Pi(_:Type<0>)→B ≮: Pi(_:Type<1>)→B.
example :
  subs (.piTot Grade.default typeZero typeZero)
       (.piTot Grade.default typeOne  typeZero) = false := by native_decide

/-! ## 2. Pi codomain covariance

`Pi(_:A)→B <: Pi(_:A)→B'` iff `B <: B'`.  Callee produces a
narrower return, caller expects a broader one. -/

-- Type<0> <: Type<1>, so
-- Pi(_:A)→Type<0> <: Pi(_:A)→Type<1>.
example :
  subs (.piTot Grade.default typeZero typeZero)
       (.piTot Grade.default typeZero typeOne) = true := by native_decide

-- Wrong direction: Pi(_:A)→Type<1> ≮: Pi(_:A)→Type<0>.
example :
  subs (.piTot Grade.default typeZero typeOne)
       (.piTot Grade.default typeZero typeZero) = false := by native_decide

/-! ## 3. Composed contra + co

`Pi(_:Type<1>)→Type<0> <: Pi(_:Type<0>)→Type<1>` — both bounds
tighten in the "safe" direction. -/

example :
  subs (.piTot Grade.default typeOne  typeZero)
       (.piTot Grade.default typeZero typeOne) = true := by native_decide

-- Reverse: both directions wrong.
example :
  subs (.piTot Grade.default typeZero typeOne)
       (.piTot Grade.default typeOne  typeZero) = false := by native_decide

/-! ## 4. Sigma covariance in both positions

`Sigma(_:A)×B <: Sigma(_:A')×B'` iff `A <: A'` and `B <: B'`.
Unlike Pi, Sigma's first component is an INPUT to construction
(positive position), so covariance matches intuition. -/

-- Sigma(_:Type<0>)×Type<0> <: Sigma(_:Type<1>)×Type<1> — both widen.
example :
  subs (.sigma Grade.default typeZero typeZero)
       (.sigma Grade.default typeOne  typeOne) = true := by native_decide

-- Sigma(_:Type<1>)×Type<0> ≮: Sigma(_:Type<0>)×Type<1> — first
-- position needs to widen (or stay equal), not narrow.
example :
  subs (.sigma Grade.default typeOne  typeZero)
       (.sigma Grade.default typeZero typeOne) = false := by native_decide

-- Only second position widens — that alone is enough.
example :
  subs (.sigma Grade.default typeZero typeZero)
       (.sigma Grade.default typeZero typeOne) = true := by native_decide

-- Only first position widens.
example :
  subs (.sigma Grade.default typeZero typeZero)
       (.sigma Grade.default typeOne  typeZero) = true := by native_decide

/-! ## 5. Rejections

Cross-head-constructor pairs and unrelated mismatches must
return `false`. -/

-- Pi vs Sigma — different type formers.
example :
  subs (.piTot Grade.default typeZero typeZero)
       (.sigma Grade.default typeZero typeZero) = false := by native_decide

example :
  subs (.sigma Grade.default typeZero typeZero)
       (.piTot Grade.default typeZero typeZero) = false := by native_decide

-- Type vs Pi.
example :
  subs typeZero (.piTot Grade.default typeZero typeZero) = false := by native_decide

-- Deep mismatch: outer Pi covariance fine, but inner Pi
-- contravariance wrong — overall rejected.
example :
  subs (.piTot Grade.default typeZero (.piTot Grade.default typeZero typeOne))
       (.piTot Grade.default typeZero (.piTot Grade.default typeOne  typeZero))
    = false := by native_decide

-- Deep match: outer co, inner contra+co, all correct.
example :
  subs (.piTot Grade.default typeOne  (.piTot Grade.default typeOne  typeZero))
       (.piTot Grade.default typeZero (.piTot Grade.default typeZero typeOne))
    = true := by native_decide

/-! ## 6. Grade-mismatch strictness

Pi (or Sigma) with different grade annotations on the binder are
NOT in the subtyping relation under the A7-core rules.  Grade
subsumption on binders is deferred until the Wood-Atkey direction
is clarified; this test pins the strict behavior so a future
change is visible.

`Grade.default` is the most-restrictive grade per §6.3.  We
construct an alternate grade by bumping the `usage` field
(which has decidable equality) and verify that subtyping rejects
the mismatch. -/

-- Build a "looser usage" grade for the test.  Grade has a
-- `usage : Usage` field and `.omega` is the most permissive
-- (unrestricted).  Default is `.one`.
def omegaUsageGrade : Grade :=
  { Grade.default with usage := Usage.omega }

example :
  subs (.piTot omegaUsageGrade     typeZero typeZero)
       (.piTot Grade.default        typeZero typeZero) = false := by native_decide

example :
  subs (.piTot Grade.default        typeZero typeZero)
       (.piTot omegaUsageGrade     typeZero typeZero) = false := by native_decide

-- Same with Sigma.
example :
  subs (.sigma omegaUsageGrade     typeZero typeZero)
       (.sigma Grade.default        typeZero typeZero) = false := by
  native_decide

-- Matching grades: subtyping still follows via Pi/Sigma rules.
example :
  subs (.piTot omegaUsageGrade     typeOne  typeZero)
       (.piTot omegaUsageGrade     typeZero typeOne) = true := by native_decide

/-! ### E-1: Pi return-effect subsumption (§9.3)

A Pi's return-effect is covariant in subtyping per Appendix B
E-Sub: a function type `→{e1}` is a subtype of `→{e2}` iff
`e1 ≤ e2` in the effect lattice.  Tot (empty row) is bottom,
so a Tot function satisfies any declared effect row.

These tests pin the subsumption direction through
`Subtyping.subOrConv`'s Pi arm. -/

-- Tot ≤ IO: a pure Pi is a subtype of an IO-declaring Pi.
example :
  subs (Term.pi Grade.default typeZero typeZero Effect.tot)
       (Term.pi Grade.default typeZero typeZero Effect.io_) = true := by
  native_decide

-- IO ≰ Tot: an effectful Pi is NOT a subtype of a pure Pi.
example :
  subs (Term.pi Grade.default typeZero typeZero Effect.io_)
       (Term.pi Grade.default typeZero typeZero Effect.tot) = false := by
  native_decide

-- Read ≤ Write via `write_`'s pre-saturation (§9.3).
example :
  subs (Term.pi Grade.default typeZero typeZero Effect.read_)
       (Term.pi Grade.default typeZero typeZero Effect.write_) = true := by
  native_decide

-- Write ≰ Read — the reverse does not hold.
example :
  subs (Term.pi Grade.default typeZero typeZero Effect.write_)
       (Term.pi Grade.default typeZero typeZero Effect.read_) = false := by
  native_decide

-- Exact-match effects are subtypes of themselves (reflexivity).
example :
  subs (Term.pi Grade.default typeZero typeZero Effect.io_)
       (Term.pi Grade.default typeZero typeZero Effect.io_) = true := by
  native_decide

-- Unrelated labels don't subsume (IO ≰ Alloc).
example :
  subs (Term.pi Grade.default typeZero typeZero Effect.io_)
       (Term.pi Grade.default typeZero typeZero Effect.alloc_) = false := by
  native_decide

/-! ## 7. `Term.sub` alias from FX.Kernel.Subtyping resolves and
     matches `subs` on representative inputs.

The alias is a thin wrapper; these tests pin it so callers
importing via `FX.Kernel.Subtyping` get identical behavior. -/

example :
  subsViaAlias (.piTot Grade.default typeOne typeZero)
               (.piTot Grade.default typeZero typeOne) = true := by
  native_decide

example :
  subsViaAlias typeZero typeOne = true := by native_decide

example :
  subsViaAlias (.sigma Grade.default typeOne typeOne)
               (.sigma Grade.default typeZero typeZero) = false := by
  native_decide

end Tests.Kernel.SubtypingTests

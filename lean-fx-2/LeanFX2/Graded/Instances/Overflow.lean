import LeanFX2.Graded.Semiring

/-! # Graded/Instances/Overflow — overflow-mode join-semilattice

`OverflowGrade` tracks the overflow behavior a computation is allowed
to use.  The default `exact` mode means arbitrary-precision or
statically-proven non-overflowing arithmetic.  The non-default runtime
behaviors `wrap`, `trap`, and `saturate` are distinct grants and are
incomparable: mixing two different behaviors is a static conflict, not
a stronger arithmetic law.

This dimension is therefore a bounded join-semilattice, not a
`GradeSemiring`.  The lattice is the partial-join completion:

```text
             conflict
           /    |    \
        wrap   trap   saturate
           \    |    /
              exact
```

`join` accumulates overflow-mode requirements.  Joining distinct
non-default modes yields `conflict`, which downstream typing rules must
reject before code generation.

Per `fx_design.md` §6.3 dim 16 and §3.8.  Zero-axiom verified per
declaration. -/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-- Overflow grade: exact arithmetic, one explicit runtime overflow
mode, or a detected mixed-mode conflict. -/
inductive OverflowGrade : Type
  /-- Exact arithmetic or a statically discharged non-overflow proof. -/
  | exact
  /-- Wrapping fixed-width overflow. -/
  | wrap
  /-- Trapping fixed-width overflow. -/
  | trap
  /-- Saturating fixed-width overflow. -/
  | saturate
  /-- Incompatible overflow modes were joined. -/
  | conflict
  deriving DecidableEq, Repr

namespace OverflowGrade

/-- Join overflow requirements; incompatible runtime modes produce a
conflict. -/
def join : OverflowGrade → OverflowGrade → OverflowGrade
  | .exact, .exact => .exact
  | .exact, .wrap => .wrap
  | .exact, .trap => .trap
  | .exact, .saturate => .saturate
  | .exact, .conflict => .conflict
  | .wrap, .exact => .wrap
  | .wrap, .wrap => .wrap
  | .wrap, .trap => .conflict
  | .wrap, .saturate => .conflict
  | .wrap, .conflict => .conflict
  | .trap, .exact => .trap
  | .trap, .wrap => .conflict
  | .trap, .trap => .trap
  | .trap, .saturate => .conflict
  | .trap, .conflict => .conflict
  | .saturate, .exact => .saturate
  | .saturate, .wrap => .conflict
  | .saturate, .trap => .conflict
  | .saturate, .saturate => .saturate
  | .saturate, .conflict => .conflict
  | .conflict, .exact => .conflict
  | .conflict, .wrap => .conflict
  | .conflict, .trap => .conflict
  | .conflict, .saturate => .conflict
  | .conflict, .conflict => .conflict

/-- Overflow subsumption preorder.  `exact` fits every overflow
allowance; each runtime mode fits itself and the explicit conflict
completion; conflict fits only conflict. -/
def le : OverflowGrade → OverflowGrade → Prop
  | .exact, .exact => True
  | .exact, .wrap => True
  | .exact, .trap => True
  | .exact, .saturate => True
  | .exact, .conflict => True
  | .wrap, .exact => False
  | .wrap, .wrap => True
  | .wrap, .trap => False
  | .wrap, .saturate => False
  | .wrap, .conflict => True
  | .trap, .exact => False
  | .trap, .wrap => False
  | .trap, .trap => True
  | .trap, .saturate => False
  | .trap, .conflict => True
  | .saturate, .exact => False
  | .saturate, .wrap => False
  | .saturate, .trap => False
  | .saturate, .saturate => True
  | .saturate, .conflict => True
  | .conflict, .exact => False
  | .conflict, .wrap => False
  | .conflict, .trap => False
  | .conflict, .saturate => False
  | .conflict, .conflict => True

end OverflowGrade

/-- Overflow modes form a bounded join-semilattice with explicit
mixed-mode conflict. -/
instance : GradeJoinSemilattice OverflowGrade where
  bottom := .exact
  join := OverflowGrade.join
  le := OverflowGrade.le

  le_refl := by
    intro value
    cases value <;> exact True.intro

  le_trans := by
    intro first second third firstLeSecond secondLeThird
    cases first <;> cases second <;> cases third <;>
      first | exact True.intro | contradiction

  bottom_le := by
    intro value
    cases value <;> exact True.intro

  le_join_left := by
    intro left right
    cases left <;> cases right <;> exact True.intro

  le_join_right := by
    intro left right
    cases left <;> cases right <;> exact True.intro

  join_least_upper_bound := by
    intro left right upper leftLeUpper rightLeUpper
    cases left <;> cases right <;> cases upper <;>
      first | exact True.intro | contradiction

  join_idempotent_le := by
    intro value
    cases value <;> exact True.intro

  join_comm_le := by
    intro left right
    cases left <;> cases right <;> exact True.intro

  join_assoc_le := by
    intro first second third
    cases first <;> cases second <;> cases third <;> exact True.intro

/-! ## Smoke samples -/

/-- Exact arithmetic contributes no runtime overflow grant. -/
example :
    OverflowGrade.join .exact .wrap = .wrap := rfl

/-- Mixing wrap and trap is an explicit static conflict. -/
example :
    OverflowGrade.join .wrap .trap = .conflict := rfl

/-- Exact arithmetic fits where wrapping overflow is allowed. -/
example :
    OverflowGrade.le .exact .wrap := True.intro

/-- Wrapping arithmetic does not fit where trapping arithmetic is
required. -/
example :
    ¬ OverflowGrade.le .wrap .trap :=
  fun impossibleLe => impossibleLe.elim

end LeanFX2.Graded.Instances

import LeanFX2.Algo.WHNF
import LeanFX2.Algo.WHNF.HeadCtorBridge
import LeanFX2.Term.Inversion
import LeanFX2.Reduction.Step.Inductive

/-! # LeanFX2.Algo.Progress.CanonicalInterval

Canonical-form raw inversions for cubical-interval head ctors.
Given a typed Term whose `headCtor` is an interval value
(`interval0`, `interval1`, `intervalOpp`, `intervalMeet`,
`intervalJoin`), extract the raw shape `RawTerm.<intervalCtor>`.

## Root status

Interval-value canonical-form inversions; feed the headline
Progress proof for cubical β-rules. Zero-axiom under strict
policy. -/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat}

/-- If a term's `headCtor` is `interval0`, its raw is the niladic
constructor `RawTerm.interval0`.  Cubical-interval endpoint canonical
form (zero endpoint) needed by the Progress proof for cubical
path-elim / interval-meet / interval-join / interval-opp beta-rules
(scrutinee inversion when the scrutinee head is `interval0`).
Niladic-payload pattern (no schematic raws); first of the M05.A.2
interval-value cohort. -/
theorem Term.headCtor_interval0_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.interval0) :
    raw = RawTerm.interval0 := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | rfl | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If a term's `headCtor` is `interval1`, its raw is the niladic
constructor `RawTerm.interval1`.  Cubical-interval endpoint canonical
form (one endpoint) needed by the Progress proof for cubical
path-elim / interval-meet / interval-join / interval-opp beta-rules
(scrutinee inversion when the scrutinee head is `interval1`).
Niladic-payload pattern; mirror of `interval0`.  Second of the
M05.A.2 interval-value cohort. -/
theorem Term.headCtor_interval1_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.interval1) :
    raw = RawTerm.interval1 := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | rfl | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If a term's `headCtor` is `intervalOpp`, its raw is
`RawTerm.intervalOpp` of an inner interval raw at the outer scope.
Cubical-interval involution canonical form needed by the Progress
proof for cubical interval-opp-of-zero / interval-opp-of-one /
double-involution beta-rules (scrutinee inversion when the scrutinee
head is `intervalOpp`).  Unary-payload pattern with the inner
interval raw at outer scope (no scope shift); mirror of `natSucc`
unary intro shape from the M05.A.0 cohort.  Third of the M05.A.2
interval-value cohort. -/
theorem Term.headCtor_intervalOpp_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.intervalOpp) :
    ∃ innerRaw : RawTerm scope, raw = RawTerm.intervalOpp innerRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | rfl | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If a term's `headCtor` is `intervalMeet`, its raw is
`RawTerm.intervalMeet` of a left interval raw and a right interval
raw (both at the outer scope).  Cubical-interval lattice-meet
canonical form needed by the Progress proof for cubical
intervalMeet-of-zero / intervalMeet-of-one / commutativity /
associativity beta-rules (scrutinee inversion when the scrutinee
head is `intervalMeet`).  Binary-payload pattern with both raws at
outer scope (no scope shift); SCHEMATIC raw fields discharged via
`exact ⟨_, _, rfl⟩`.  Fourth of the M05.A.2 interval-value cohort. -/
theorem Term.headCtor_intervalMeet_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.intervalMeet) :
    ∃ leftRaw rightRaw : RawTerm scope,
      raw = RawTerm.intervalMeet leftRaw rightRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | rfl | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge

/-- If a term's `headCtor` is `intervalJoin`, its raw is
`RawTerm.intervalJoin` of a left interval raw and a right interval
raw (both at the outer scope).  Cubical-interval lattice-join
canonical form needed by the Progress proof for cubical
intervalJoin-of-zero / intervalJoin-of-one / commutativity /
associativity beta-rules (scrutinee inversion when the scrutinee
head is `intervalJoin`).  Binary-payload pattern with both raws at
outer scope (no scope shift); SCHEMATIC raw fields discharged via
`exact ⟨_, _, rfl⟩`.  Mirror of `intervalMeet`.  Fifth and final of
the M05.A.2 interval-value cohort, closing the cohort. -/
theorem Term.headCtor_intervalJoin_raw {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (someTerm : Term context ty raw)
    (headEq : someTerm.headCtor = Term.HeadCtor.intervalJoin) :
    ∃ leftRaw rightRaw : RawTerm scope,
      raw = RawTerm.intervalJoin leftRaw rightRaw := by
  have bridge := someTerm.headCtor_toRawTag
  rw [headEq] at bridge
  cases raw <;> first | rfl | exact ⟨_, rfl⟩ | exact ⟨_, _, rfl⟩ | nomatch bridge


end LeanFX2

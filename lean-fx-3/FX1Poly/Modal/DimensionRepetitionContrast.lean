import FX1Poly.Modal.ResourceGraded

/-! # Foundation/PolyCell/Modal/DimensionRepetitionContrast
    — the usage and security dimensions check GENUINELY DIFFERENT disciplines (§6.1 / §6.3 / §6.8)

The graded type system composes all dimensions POINTWISE: "Product of all forms the grade vector every
binding carries" (§6.1), and the per-dimension checks run independently against the declared grades.  The
DIM track has, so far, built each dimension's algebra in isolation (usage `{0,1,ω}`, security
`{unclassified < classified}`, …).  This file is the FIRST CROSS-DIMENSION COMPARISON: it contrasts how two
dimensions' addition operations behave on the SAME phenomenon — REPEATED USE of a resource — and shows they
enforce qualitatively different disciplines.

The distinction is at the unit `R.one` of each semiring (`semiringUnits_eq`: `fxUsageSemiring.one = .one`,
`fxSecuritySemiring.one = .classified`):

  * **Usage `+` is NON-idempotent at the unit** (`usageAddUnitUnit_eq_omega`: `1 + 1 = ω ≠ 1`).  Usage is
    OCCURRENCE-COUNTING — each additional use strictly increases the grade, so repetition is PENALIZED.
    Combining a linear resource with itself EXCEEDS the linear bound (`usageRepetitionExceedsLinear`:
    `ω ≤ 1` is false).  This is the linearity discipline.
  * **Security `+` IS idempotent at the unit** (`securityAddUnitUnit_idempotent`:
    `classified + classified = classified`).  Security is an INFORMATION-FLOW JOIN — combining a secrecy
    label with itself is stable, so repetition is NOT penalized.  Combining a classified resource with
    itself STAYS WITHIN the classified bound (`securityRepetitionStaysWithinUnit`).  This is the
    information-flow discipline.

`usageAndSecurityDifferOnRepetition` is the headline: the SAME "combine a resource with itself" operation
exceeds the usage bound but stays within the security bound — so when the two dimensions compose pointwise
in one grade vector, each enforces its own discipline (linearity vs information flow), neither subsuming the
other's behavior on repetition.  This is the algebraic root of §6.8's "the dimensions are NOT orthogonal":
they share the graded-semiring SHAPE (§6.1) but their `+` operations are genuinely different, so a program
acceptable to one dimension's check can be rejected by another's.

The term-level faces of these two disciplines ship elsewhere: usage rejects the double-use `g g`
(`FX1Poly.Modal.dupReduct` is ill-graded at a linear declaration), while security propagates a classified
selector's secrecy through application (the App-scaling poison, `SecurityGrade.classified_poisons_add`) — a
flow that the occurrence-blind usage check ignores.

Zero-axiom: every fact is a concrete `rfl` over the propext-free enum tables `UsageGrade.add` / `.le` and
`SecurityGrade.add` / `.le`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- The units coincide with `R.one` of each semiring: `fxUsageSemiring.one = .one`,
`fxSecuritySemiring.one = .classified` — the "single linear use" / "single classified use" baselines the
repetition contrast is measured against. -/
theorem semiringUnits_eq :
    fxUsageSemiring.one = UsageGrade.one ∧ fxSecuritySemiring.one = SecurityGrade.classified :=
  ⟨rfl, rfl⟩

/-- **Usage `+` is non-idempotent at the unit.**  Combining a linear resource with itself yields `ω` — each
additional use strictly increases the grade (occurrence counting). -/
theorem usageAddUnitUnit_eq_omega :
    UsageGrade.add UsageGrade.one UsageGrade.one = UsageGrade.omega :=
  rfl

/-- **Usage penalizes repetition.**  `1 + 1 = ω` exceeds the linear bound `1` (`ω ≤ 1` is false) — a linear
resource may not be used twice.  The linearity discipline. -/
theorem usageRepetitionExceedsLinear :
    UsageGrade.le (UsageGrade.add UsageGrade.one UsageGrade.one) UsageGrade.one = false :=
  rfl

/-- **Security `+` is idempotent at the unit.**  Combining a classified label with itself stays classified —
joining a secrecy level with itself is stable. -/
theorem securityAddUnitUnit_idempotent :
    SecurityGrade.add SecurityGrade.classified SecurityGrade.classified = SecurityGrade.classified :=
  rfl

/-- **Security does NOT penalize repetition.**  `classified + classified = classified` stays within the
classified bound (`classified ≤ classified`) — using a classified resource twice is fine.  The
information-flow discipline. -/
theorem securityRepetitionStaysWithinUnit :
    SecurityGrade.le (SecurityGrade.add SecurityGrade.classified SecurityGrade.classified)
      SecurityGrade.classified = true :=
  rfl

/-- ★ **The usage and security dimensions enforce genuinely different disciplines on repetition.**  The SAME
"combine a resource with itself" operation EXCEEDS the usage bound (occurrence-counting: `1+1 = ω ≰ 1`) but
STAYS WITHIN the security bound (idempotent flow-join: `c+c = c ≤ c`).  Composing pointwise in one grade
vector (§6.1), each dimension's `+` enforces its own discipline — linearity vs information flow — so the
21-dimension product is NOT a single check repeated, but genuinely heterogeneous (§6.8). -/
theorem usageAndSecurityDifferOnRepetition :
    (UsageGrade.le (UsageGrade.add UsageGrade.one UsageGrade.one) UsageGrade.one = false) ∧
    (SecurityGrade.le (SecurityGrade.add SecurityGrade.classified SecurityGrade.classified)
      SecurityGrade.classified = true) :=
  ⟨rfl, rfl⟩

end FX1Poly.Modal

import FX1Poly.Modal.ResourceGraded

/-! # Foundation/PolyCell/Modal/DimensionMultiplicationContrast
    — the MULTIPLICATIVE sibling of `DimensionRepetitionContrast`: usage and security differ on the
      MULTIPLICATIVE monoid `(R, ×, 1)` and where its unit sits in the order (§6.1 / §6.3 / §6.8)

`DimensionRepetitionContrast.lean` contrasted the two dimensions' ADDITION on the same phenomenon
(repeated use): usage's `+` is occurrence-counting (`1 + 1 = ω`, repetition penalized) while security's
`+` is an idempotent information-flow join (`c + c = c`, repetition free).  This file is its multiplicative
twin — it contrasts the other half of each semiring, the MULTIPLICATIVE monoid `(R, ×, 1)`, along two
axes: where the multiplicative UNIT sits in the order, and what the multiplicative ANNIHILATOR means.

The multiplicative units are `fxUsageSemiring.one = .one` and `fxSecuritySemiring.one = .classified`
(`semiringUnits_eq`, the repetition file).  They sit at OPPOSITE positions in their dimension's order:

  * **Usage's `×`-unit `1` is SUB-MAXIMAL** (`usageUnitIsSubMaximal`: `1 ≤ ω` and `1 ≠ ω`).  Linear use
    is NOT the top of the usage order — unrestricted use `ω` strictly exceeds it.  Usage GRANTS a
    beyond-unit capability: a binding may be promoted from linear `1` to unrestricted `ω` (the `@[copy]`
    grant, §6.3 dim 3).  There is a strictly-greater grade than the unit.
  * **Security's `×`-unit `classified` is MAXIMAL** (`securityUnitIsMaximal`: `classified ≰ unclassified`
    and `unclassified ≤ classified`).  Classified is the TOP of the secrecy order — nothing exceeds it.
    There is no "beyond classified" grant; secrecy only ever flows DOWN via an explicit, audited
    `declassify` (§12.4), never up past the unit.

The multiplicative ANNIHILATOR is each semiring's additive `0` (the law `r × 0 = 0` holds in EVERY
semiring), but the `0` MEANS something different in each dimension, so the absorption lands on a
qualitatively different grade:

  * **Usage `×` annihilates at `0` = erased/ghost** (`usageMulAnnihilatesAtZero`: `0 × ω = 0`).  An
    erased binding (grade `0`, §1.5 compile-time erasure) scales any use down to nothing — `1/ω = 0`
    context division (the corrected Wood/Atkey Lam, §6.2) is the same `0` absorbing a linear variable out
    of a replicable closure.
  * **Security `×` (the MEET) annihilates at `0` = `unclassified` = public** (`securityMulAnnihilatesAt­
    Unclassified`: `classified × unclassified = unclassified`).  Composing a secret with a grade-`0`
    (ghost / erased) computation yields the `0` grade, which here is PUBLIC — "ghost computation on a
    secret leaks nothing" (§6.3 dim 5).  Same `r × 0 = 0` law, but absorption lands on `unclassified`
    rather than on an erased `0`.

`usageAndSecurityDifferOnUnitMaximality` is the headline (the multiplicative analogue of the repetition
file's `usageAndSecurityDifferOnRepetition`): the two dimensions' multiplicative units occupy OPPOSITE
order positions — usage's is sub-maximal (a strictly-greater grade exists, capability can be granted),
security's is maximal (it is the top, no further secrecy).  So when the dimensions compose pointwise in
one grade vector (§6.1), the multiplicative structure is genuinely heterogeneous too: this is the same
§6.8 "the dimensions are NOT orthogonal" root the additive contrast exposed, now on `×` and `≤`.

Zero-axiom: every fact is a concrete `rfl` / `decide` over the propext-free enum tables `UsageGrade.mul`
/ `.le` and `SecurityGrade.mul` / `.le`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditModal.lean`.
-/

namespace FX1Poly.Modal

/-- **Usage's multiplicative unit `1` is SUB-MAXIMAL.**  `1 ≤ ω` and `1 ≠ ω`, so unrestricted use `ω`
strictly EXCEEDS linear use — linear is not the top of the usage order.  Usage GRANTS a beyond-unit
capability: a binding may be promoted from `1` to the strictly-greater `ω` (the `@[copy]` grant, §6.3
dim 3).  There is a grade strictly above the multiplicative unit. -/
theorem usageUnitIsSubMaximal :
    UsageGrade.le UsageGrade.one UsageGrade.omega = true ∧ UsageGrade.one ≠ UsageGrade.omega :=
  ⟨rfl, by decide⟩

/-- **Security's multiplicative unit `classified` is MAXIMAL.**  Nothing exceeds it
(`classified ≰ unclassified`) and everything is below it (`unclassified ≤ classified`) — classified is
the TOP of the secrecy order.  There is no "beyond classified" grant; secrecy only flows DOWN via an
explicit audited `declassify` (§12.4), never above the unit. -/
theorem securityUnitIsMaximal :
    SecurityGrade.le SecurityGrade.classified SecurityGrade.unclassified = false ∧
    SecurityGrade.le SecurityGrade.unclassified SecurityGrade.classified = true :=
  ⟨rfl, rfl⟩

/-- **Usage `×` annihilates at `0` = erased/ghost.**  `0 × ω = 0` — an erased binding (grade `0`, the
§1.5 compile-time erasure) scales ANY use down to nothing.  This is the same `0` that the corrected
Wood/Atkey Lam rule's context division `1/ω = 0` (§6.2) uses to absorb a linear variable out of a
replicable closure. -/
theorem usageMulAnnihilatesAtZero :
    UsageGrade.mul UsageGrade.zero UsageGrade.omega = UsageGrade.zero :=
  rfl

/-- **Security `×` (the MEET) annihilates at `0` = `unclassified` = public.**  `classified × unclassified
= unclassified` — composing a secret with a grade-`0` (ghost / erased) computation yields the `0` grade,
which in the security dimension is PUBLIC: "ghost computation on a secret leaks nothing" (§6.3 dim 5).
The same semiring law `r × 0 = 0` as usage, but the absorbing `0` lands on `unclassified`, not on an
erased grade. -/
theorem securityMulAnnihilatesAtUnclassified :
    SecurityGrade.mul SecurityGrade.classified SecurityGrade.unclassified = SecurityGrade.unclassified :=
  rfl

/-- ★ **The usage and security multiplicative units sit at OPPOSITE order positions.**  Usage's `×`-unit
is SUB-MAXIMAL (`1 < ω` — a strictly-greater grade exists, so capability can be GRANTED beyond the unit)
while security's `×`-unit is MAXIMAL (`classified` is the top secrecy — there is no grade beyond it).  The
multiplicative analogue of the repetition contrast: composing pointwise in one grade vector (§6.1), each
dimension's `(R, ×, 1)` monoid relates to its order differently — usage's unit admits a strict
over-grade, security's does not — so the 21-dimension product is heterogeneous on `×`/`≤` as well as on
`+` (§6.8). -/
theorem usageAndSecurityDifferOnUnitMaximality :
    (UsageGrade.le UsageGrade.one UsageGrade.omega = true ∧ UsageGrade.one ≠ UsageGrade.omega) ∧
    (SecurityGrade.le SecurityGrade.classified SecurityGrade.unclassified = false) :=
  ⟨⟨rfl, by decide⟩, rfl⟩

end FX1Poly.Modal

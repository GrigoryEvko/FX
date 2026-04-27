import FX.Kernel.Grade.Tier

/-!
# Security (dimension 5) — information-flow label

Per `fx_design.md` §6.3 (dim 5).  Tier S in the design doc,
though see the structural note below.

  * `unclassified` — public; may flow to IO, logs, network.
  * `classified`   — secret; requires explicit `declassify`
                     with an auditable policy to escape.

## Surface-syntax mapping

Per `fx_design.md` §12.1, the three source-level keywords map
as follows:

  * `unclassified x`  → `unclassified`  (explicit public)
  * (no annotation)   → `classified`    (default — deny-by-default)
  * `secret x`        → `classified`    (explicit high label)

"Classified by default" is the core design principle: unannotated
data is never trusted to be safe, so it cannot flow to IO/logs
without an explicit `declassify` under an audited policy (§12.4).

## Algebraic structure

Two-element bounded chain `unclassified ≤ classified` with
parallel combine = join (max).  The design doc calls this a
"Tier S semiring", but a 2-element join-semilattice is **not**
a strict commutative semiring with zero annihilator: under
`add = mul = join`, the additive identity is the bottom
(`unclassified`), and we would need it to also be a
multiplicative annihilator, which contradicts `unclassified *
classified = classified` under join.

The design doc (§6.3 dim 5) states the asymmetry explicitly:
"Multiplication is also join for non-zero grades; `classified *
0 = 0` (ghost computation on secret data is erased and leaks
nothing)."  Here `0` refers to `Usage.zero`, not a zero in the
Security carrier — Security has no zero element.  The
"annihilator" lives in the grade-vector interaction (Usage.zero
erases the binding entirely, so its Security grade does not
matter), not in Security alone.

We therefore model Security as an **idempotent commutative
monoid** for both `add` and `mul`, both being `join`.  This is
the honest structure.  Noninterference (§12.2) is enforced by
the interaction with the Usage dimension: a value at
`(Usage.zero, Security.classified)` is ghost-erased, so the
classification contributes nothing to the runtime leak.

## Axioms realized

Grade-semiring-laws (the subset that actually holds: idempotent
comm monoid laws, distributivity is trivial under add=mul);
Grade-subsumption via `LessEq`.
-/

namespace FX.Kernel

/--
The two security labels.  `unclassified` is the bottom (public),
`classified` is the top (secret).
-/
inductive Security : Type where
  | unclassified : Security
  | classified   : Security
  deriving DecidableEq, Repr

namespace Security

/-- Join (parallel combine).  Combining public and secret yields
    secret — the classic "high-water mark" information flow rule. -/
def add : Security → Security → Security
  | unclassified, rightSecurity => rightSecurity
  | leftSecurity, unclassified => leftSecurity
  | classified, _              => classified

/-- Sequential combine: same join operation.  Sequencing through
    a secret value does not downgrade the secrecy — only an
    explicit `declassify` does. -/
def mul : Security → Security → Security := add

/--
Subsumption order: `unclassified ≤ classified`.

A value at `unclassified` is usable where `classified` is
expected (generalizing public data to a secret context is
always safe).  The reverse is the noninterference violation.
-/
inductive LessEq : Security → Security → Prop where
  | refl  : ∀ sec, LessEq sec sec
  | botLe : LessEq unclassified classified

instance : LE Security := ⟨LessEq⟩

theorem LessEq.trans {leftSecurity midSecurity rightSecurity : Security}
    (leftLeMid : leftSecurity ≤ midSecurity) (midLeRight : midSecurity ≤ rightSecurity) :
    leftSecurity ≤ rightSecurity := by
  cases leftLeMid with
  | refl  => exact midLeRight
  | botLe =>
    -- midLeRight : LessEq classified rightSecurity; only `refl` can construct that
    -- (botLe produces `LessEq unclassified _`).
    cases midLeRight with
    | refl => exact LessEq.botLe

instance decLe : (leftSecurity rightSecurity : Security) → Decidable (LessEq leftSecurity rightSecurity)
  | unclassified, unclassified => isTrue (LessEq.refl _)
  | unclassified, classified   => isTrue LessEq.botLe
  | classified,   unclassified => isFalse (fun absurdLe => by cases absurdLe)
  | classified,   classified   => isTrue (LessEq.refl _)

/-! ### Idempotent commutative monoid laws -/

theorem add_comm (leftSecurity rightSecurity : Security) :
    add leftSecurity rightSecurity = add rightSecurity leftSecurity := by
  cases leftSecurity <;> cases rightSecurity <;> rfl

theorem add_assoc (leftSecurity midSecurity rightSecurity : Security) :
    add (add leftSecurity midSecurity) rightSecurity
      = add leftSecurity (add midSecurity rightSecurity) := by
  cases leftSecurity <;> cases midSecurity <;> cases rightSecurity <;> rfl

theorem add_idem (security : Security) : add security security = security := by
  cases security <;> rfl

theorem zero_add (security : Security) : add unclassified security = security := by
  cases security <;> rfl

theorem add_zero (security : Security) : add security unclassified = security := by
  cases security <;> rfl

theorem mul_assoc (leftSecurity midSecurity rightSecurity : Security) :
    mul (mul leftSecurity midSecurity) rightSecurity
      = mul leftSecurity (mul midSecurity rightSecurity) :=
  add_assoc leftSecurity midSecurity rightSecurity

/-- Security mul is commutative.  Tier S (noninterference
    lattice); `mul := add := join`.  Q48. -/
theorem mul_comm (leftSecurity rightSecurity : Security) :
    mul leftSecurity rightSecurity = mul rightSecurity leftSecurity :=
  add_comm leftSecurity rightSecurity

theorem one_mul (security : Security) : mul unclassified security = security :=
  zero_add security

theorem mul_one (security : Security) : mul security unclassified = security :=
  add_zero security

/-- Degenerate distributivity: both sides reduce to the same
    three-way join by idempotence. -/
theorem left_distrib (leftSecurity midSecurity rightSecurity : Security) :
    mul leftSecurity (add midSecurity rightSecurity)
      = add (mul leftSecurity midSecurity) (mul leftSecurity rightSecurity) := by
  cases leftSecurity <;> cases midSecurity <;> cases rightSecurity <;> rfl

theorem right_distrib (leftSecurity midSecurity rightSecurity : Security) :
    mul (add leftSecurity midSecurity) rightSecurity
      = add (mul leftSecurity rightSecurity) (mul midSecurity rightSecurity) := by
  cases leftSecurity <;> cases midSecurity <;> cases rightSecurity <;> rfl

/-! ### Further laws over the finite carrier -/

/-- Antisymmetry: `LessEq` is a genuine partial order on the two-element
    carrier. -/
theorem LessEq.antisymm {leftSecurity rightSecurity : Security}
    (leftLeRight : leftSecurity ≤ rightSecurity) (rightLeLeft : rightSecurity ≤ leftSecurity) :
    leftSecurity = rightSecurity := by
  cases leftLeRight with
  | refl  => rfl
  | botLe => cases rightLeLeft

/-- `classified` is the top: every grade subsumes into `classified`. -/
theorem le_classified (security : Security) : security ≤ classified := by
  cases security
  · exact LessEq.botLe
  · exact LessEq.refl _

/-- `unclassified` is the bottom: `unclassified` subsumes into
    every grade. -/
theorem unclassified_le (security : Security) : unclassified ≤ security := by
  cases security
  · exact LessEq.refl _
  · exact LessEq.botLe

/-- Monotonicity of `add` (= join): if `smaller ≤ bigger`, then combining
    with any `other` preserves the inequality. -/
theorem add_mono_left {smallerSecurity biggerSecurity : Security} (otherSecurity : Security)
    (smallerLeBigger : smallerSecurity ≤ biggerSecurity) :
    add smallerSecurity otherSecurity ≤ add biggerSecurity otherSecurity := by
  cases smallerSecurity <;> cases biggerSecurity <;> cases otherSecurity <;>
    first
      | exact LessEq.refl _
      | exact LessEq.botLe
      | (cases smallerLeBigger)

/-- `add` absorbs into `classified` on either side.  Witnesses the
    "high-water mark" rule for noninterference: combining ANY value
    with a classified one produces classified. -/
theorem add_classified_left (security : Security) : add classified security = classified := by
  cases security <;> rfl
theorem add_classified_right (security : Security) : add security classified = classified := by
  cases security <;> rfl

end Security

/-! ## TierSIdem instance (T2)

Security fits the idempotent join shape: `add = mul = join` over the
2-element lattice, `unclassified` is the join-identity and
`classified` absorbs.  Strict annihilation `mul unclassified x =
unclassified` does NOT hold (`mul unclassified classified = classified`).

Per §12.1 the carrier `default` is `classified` (deny-by-default —
data cannot flow to IO without explicit declassification). -/
instance : TierSIdem Security where
  default      := Security.classified
  le           := Security.LessEq
  le_refl      := Security.LessEq.refl
  le_trans     := Security.LessEq.trans
  add          := Security.add
  mul          := Security.mul
  zero         := Security.unclassified
  add_comm     := Security.add_comm
  add_assoc    := Security.add_assoc
  add_zero     := Security.add_zero
  zero_add     := Security.zero_add
  mul_assoc    := Security.mul_assoc
  mul_comm     := Security.mul_comm
  add_idem     := Security.add_idem
  mul_eq_add   := fun _ _ => rfl

end FX.Kernel

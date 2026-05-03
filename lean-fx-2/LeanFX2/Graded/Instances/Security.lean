import LeanFX2.Graded.Semiring

/-! # Graded/Instances/Security — security lattice as Boolean-algebra semiring

Two-element security lattice for information-flow tracking, encoded
as the canonical 2-element Boolean algebra `B = {u, c}` with:

* `+` = `∨` (join, OR)             — combining yields the worst case
* `*` = `∧` (meet, AND)            — scaling annihilates with `0`
* `0` = `unclassified`             — additive identity, lattice bottom
* `1` = `classified`               — multiplicative identity, lattice top
* `≤` = `u ≤ c` only               — no implicit downgrade

Per `fx_design.md` §6.1 — "Mixing public and secret yields secret"
captures `c + u = c`; "ghost computation on secret leaks nothing"
captures `c * 0 = c ∧ u = u = 0` (annihilation by additive zero).

## Why Boolean algebra is the right semiring

A bounded distributive lattice with bottom-as-additive-identity and
top-as-multiplicative-identity satisfies every semiring law:
* Additive monoid laws: from `∨` (join) being associative,
  commutative, idempotent (with `u` as identity)
* Multiplicative monoid laws: from `∧` (meet) being associative,
  with `c` as identity
* Distribution: lattice distributivity `x ∧ (a ∨ b) = (x ∧ a) ∨
  (x ∧ b)` (holds for any distributive lattice; the 2-element case
  is the canonical Boolean algebra)
* Annihilation: `0 ∧ x = 0` and `x ∧ 0 = 0` (lattice bottom is
  meet-absorbing)
* Preorder laws and monotonicity: from lattice order structure

All 17 laws discharged by full case enumeration (2, 4, or 8 cases
each over the closed 2-element enum) — no `decide`, no tactics that
risk axiom emission.

## Surface mode mapping

Per `fx_design.md` §1.1 / §12 / §6.3:
* default (no annotation)        → `classified` (default-deny)
* `unclassified x`               → `unclassified`
* `secret x`                     → `classified` (explicit high)
* `declassify(x, policy)`        → permits `c → u` only via the
  named policy with audit trail (§12.4)

## Cross-dimension interactions (§6.8)

* `classified × Async`           — soundness collision
* `classified × Fail` on secret  — error variant leaks secret
* `classified × CT`              — secret-dependent control flow
  forbidden in CT context

These interactions are checked at the `GradeVector` level, not in
this single-dimension instance.

## Dependencies

* `Graded/Semiring.lean` — the typeclass `GradeSemiring` with all
  17 algebra laws

## Downstream

* `Graded/Rules.lean` — security grade tracked via App/Let/If rules
* `Graded/AtkeyAttack.lean` — Wood-Atkey context division on
  `SecurityGrade` (security-secret-bound captured in low-security
  closure forces classification erasure)
* `fx_design.md` §12 — full IFC semantics

Zero-axiom verified per declaration. -/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-- Security grade: the 2-element lattice `unclassified < classified`.
Closed enum — full pattern matches over `cases` produce `rfl` arms.

* `unclassified` — public data; the additive identity (lattice
  bottom).  Default for `unclassified` declarations only; everywhere
  else, the default is `classified`.

* `classified` — secret data; the multiplicative identity (lattice
  top).  Default for any binding without an explicit annotation. -/
inductive SecurityGrade : Type
  /-- Public data; lattice bottom; additive identity. -/
  | unclassified
  /-- Secret data; lattice top; multiplicative identity. -/
  | classified
  deriving DecidableEq, Repr

namespace SecurityGrade

/-- Combining (parallel) is lattice join — `u ∨ x = x`, `c ∨ x = c`.
Mixing public and secret yields secret. -/
def add : SecurityGrade → SecurityGrade → SecurityGrade
  | .unclassified, rightOperand  => rightOperand
  | .classified,   _              => .classified

/-- Scaling (sequential) is lattice meet — `u ∧ x = u`, `c ∧ x = x`.
Annihilation: any scaling involving `unclassified` yields
`unclassified` (a ghost computation on secret data leaks nothing). -/
def mul : SecurityGrade → SecurityGrade → SecurityGrade
  | .unclassified, _              => .unclassified
  | .classified,   rightOperand   => rightOperand

/-- Subsumption preorder: `unclassified ≤ classified` (the only
non-reflexive `≤` edge).  Public data fits where secret expected;
the reverse requires `declassify`. -/
def le : SecurityGrade → SecurityGrade → Prop
  | .unclassified, _              => True
  | .classified,   .unclassified  => False
  | .classified,   .classified    => True

end SecurityGrade

/-- The security `{u, c}` Boolean-algebra semiring.  All 17
algebra/preorder laws discharged by full case enumeration (2, 4, or
8 sub-cases each) over the non-indexed 2-element inductive — no
`decide`, no tactics that risk axiom emission. -/
instance : GradeSemiring SecurityGrade where
  zero := .unclassified
  one  := .classified
  add  := SecurityGrade.add
  mul  := SecurityGrade.mul
  le   := SecurityGrade.le

  add_assoc := fun first second third => match first, second, third with
    | .unclassified, _,              _              => rfl
    | .classified,   _,              _              => rfl

  add_comm := fun first second => match first, second with
    | .unclassified, .unclassified => rfl
    | .unclassified, .classified   => rfl
    | .classified,   .unclassified => rfl
    | .classified,   .classified   => rfl

  add_zero_left  := fun _ => rfl
  add_zero_right := fun value => match value with
    | .unclassified => rfl
    | .classified   => rfl

  mul_assoc := fun first second third => match first, second, third with
    | .unclassified, _,              _              => rfl
    | .classified,   .unclassified, _              => rfl
    | .classified,   .classified,   _              => rfl

  mul_one_left  := fun value => match value with
    | .unclassified => rfl
    | .classified   => rfl
  mul_one_right := fun value => match value with
    | .unclassified => rfl
    | .classified   => rfl

  mul_distrib_left := fun scalar leftAddend rightAddend =>
    match scalar, leftAddend, rightAddend with
    | .unclassified, _,              _              => rfl
    | .classified,   .unclassified, .unclassified  => rfl
    | .classified,   .unclassified, .classified    => rfl
    | .classified,   .classified,   .unclassified  => rfl
    | .classified,   .classified,   .classified    => rfl

  mul_distrib_right := fun leftAddend rightAddend scalar =>
    match leftAddend, rightAddend, scalar with
    | .unclassified, .unclassified, .unclassified => rfl
    | .unclassified, .unclassified, .classified   => rfl
    | .unclassified, .classified,   .unclassified => rfl
    | .unclassified, .classified,   .classified   => rfl
    | .classified,   .unclassified, .unclassified => rfl
    | .classified,   .unclassified, .classified   => rfl
    | .classified,   .classified,   .unclassified => rfl
    | .classified,   .classified,   .classified   => rfl

  mul_zero_left  := fun _ => rfl
  mul_zero_right := fun value => match value with
    | .unclassified => rfl
    | .classified   => rfl

  le_refl := fun value => match value with
    | .unclassified => True.intro
    | .classified   => True.intro

  le_trans := fun first second third firstLeSecond secondLeThird =>
    match first, second, third, firstLeSecond, secondLeThird with
    | .unclassified, _,              _,              _, _ => True.intro
    | .classified,   .classified,   .classified,   _, _ => True.intro

  add_mono := fun leftLow leftHigh rightLow rightHigh leftLeq rightLeq =>
    match leftLow, leftHigh, rightLow, rightHigh, leftLeq, rightLeq with
    | .unclassified, .unclassified, .unclassified, .unclassified, _, _ => True.intro
    | .unclassified, .unclassified, .unclassified, .classified,   _, _ => True.intro
    | .unclassified, .unclassified, .classified,   .classified,   _, _ => True.intro
    | .unclassified, .classified,   .unclassified, .unclassified, _, _ => True.intro
    | .unclassified, .classified,   .unclassified, .classified,   _, _ => True.intro
    | .unclassified, .classified,   .classified,   .classified,   _, _ => True.intro
    | .classified,   .classified,   .unclassified, .unclassified, _, _ => True.intro
    | .classified,   .classified,   .unclassified, .classified,   _, _ => True.intro
    | .classified,   .classified,   .classified,   .classified,   _, _ => True.intro

  mul_mono := fun leftLow leftHigh rightLow rightHigh leftLeq rightLeq =>
    match leftLow, leftHigh, rightLow, rightHigh, leftLeq, rightLeq with
    -- leftLow = unclassified (mul .unclassified _ = .unclassified, le .unclassified _ = True)
    | .unclassified, _,              _,              _,              _, _ => True.intro
    -- leftLow = classified, leftHigh = classified (only valid by le)
    | .classified,   .classified,   .unclassified, .unclassified, _, _ => True.intro
    | .classified,   .classified,   .unclassified, .classified,   _, _ => True.intro
    | .classified,   .classified,   .classified,   .classified,   _, _ => True.intro

/-! ## Smoke: combining vs scaling asymmetry

The canonical IFC scenarios verifying the semiring's intended
behaviour: combining classified data into anything yields
classified; scaling unclassified by anything yields unclassified
(annihilation). -/

/-- Combining unclassified with classified yields classified
("Mixing public and secret yields secret"). -/
example : SecurityGrade.add .unclassified .classified = .classified := rfl

/-- Combining classified with unclassified yields classified
(commutative). -/
example : SecurityGrade.add .classified .unclassified = .classified := rfl

/-- Scaling unclassified by classified yields unclassified
(annihilation: `0 * c = 0`). -/
example : SecurityGrade.mul .unclassified .classified = .unclassified := rfl

/-- Scaling classified by unclassified yields unclassified
("ghost computation on secret leaks nothing": `c * 0 = 0`). -/
example : SecurityGrade.mul .classified .unclassified = .unclassified := rfl

/-! ## Smoke: subsumption is uni-directional

Per `fx_design.md` §12 — public data fits where secret expected
("safe upgrade"); secret data does NOT fit where public expected
("unsafe downgrade requires declassify"). -/

/-- Public data fits where secret is expected. -/
example : SecurityGrade.le .unclassified .classified := True.intro

/-- Public is reflexively `≤` itself. -/
example : SecurityGrade.le .unclassified .unclassified := True.intro

/-- Secret is reflexively `≤` itself. -/
example : SecurityGrade.le .classified .classified := True.intro

/-- Secret does NOT fit where public expected. -/
example : ¬ SecurityGrade.le .classified .unclassified :=
  fun absurdLe => absurdLe.elim

end LeanFX2.Graded.Instances

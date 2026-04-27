import FX.Kernel.Grade.Tier

/-!
# Observability (dimension 11) — access-pattern opacity

Per `fx_design.md` §6.3 (dim 11).  Two-element chain
`opaq < transparent` (surface spelling is `opaque`; in the
kernel we write `opaq` because `opaque` is a reserved keyword
in Lean 4 that blocks `rfl` reduction on auto-escaped
constructors).

  * `opaq`        — access pattern may not depend on content.
                    Default; mandatory inside `with CT` (§12.5).
  * `transparent` — grant; access pattern may leak content.

## Surface-syntax mapping

Per `fx_design.md` §6.3 dim 11, the source keywords are:

  * (no annotation) → `opaq`        (default — deny-by-default)
  * `transparent`   → `transparent` (explicit grant to leak access)

Inside `with CT`, every value must have observability `opaq`;
the grant cannot be used.

## Combining

The design doc §6.3 dim 11 is terminologically ambiguous: it
says "Addition is join" but the worked example specifies
"combining opaque and transparent yields opaque (the more
restrictive choice)" — which is **meet** under the stated
ordering `opaque < transparent`.  We follow the example's
explicit truth table (meet) since that matches the stated
semantic intent ("the more restrictive choice").

So: parallel/sequential combine is **meet** = pointwise min.
If any sub-expression is opaque, the whole expression is opaque.

## Algebra

Two-element idempotent commutative monoid for both `add` and
`mul`, both being `meet` with `transparent` as the identity.

Subsumption `LessEq` has `opaq ≤ transparent`: an opaque value
is usable wherever a transparent one is expected (weakening
the grant is always safe).  The reverse — using a transparent
value in an opaque-required context — is the CT violation.
-/

namespace FX.Kernel

/--
`opaq` is the bottom (more restrictive); `transparent` is the
top (granting content-dependent access).  Default is `opaq`.
-/
inductive Observability : Type where
  | opaq        : Observability
  | transparent : Observability
  deriving DecidableEq, Repr

namespace Observability

/-- Meet.  Fully enumerated so `rfl` reduces every case. -/
def add : Observability → Observability → Observability
  | opaq,        opaq        => opaq
  | opaq,        transparent => opaq
  | transparent, opaq        => opaq
  | transparent, transparent => transparent

def mul : Observability → Observability → Observability := add

inductive LessEq : Observability → Observability → Prop where
  | refl    : ∀ observability, LessEq observability observability
  | opaqLe  : LessEq opaq transparent

instance : LE Observability := ⟨LessEq⟩

theorem LessEq.trans {leftObs midObs rightObs : Observability}
    (hLeftMid : leftObs ≤ midObs) (hMidRight : midObs ≤ rightObs) :
    leftObs ≤ rightObs := by
  cases hLeftMid with
  | refl   => exact hMidRight
  | opaqLe =>
    cases hMidRight with
    | refl => exact LessEq.opaqLe

instance decLe : (leftObs rightObs : Observability) → Decidable (LessEq leftObs rightObs)
  | opaq,        opaq        => isTrue (LessEq.refl _)
  | opaq,        transparent => isTrue LessEq.opaqLe
  | transparent, opaq        => isFalse (fun hContra => by cases hContra)
  | transparent, transparent => isTrue (LessEq.refl _)

theorem add_comm (leftObs rightObs : Observability) :
    add leftObs rightObs = add rightObs leftObs := by
  cases leftObs <;> cases rightObs <;> rfl

theorem add_assoc (leftObs midObs rightObs : Observability) :
    add (add leftObs midObs) rightObs = add leftObs (add midObs rightObs) := by
  cases leftObs <;> cases midObs <;> cases rightObs <;> rfl

theorem add_idem (observability : Observability) : add observability observability = observability := by
  cases observability <;> rfl

theorem transparent_add (observability : Observability) : add transparent observability = observability := by
  cases observability <;> rfl

theorem add_transparent (observability : Observability) : add observability transparent = observability := by
  cases observability <;> rfl

theorem mul_assoc (leftObs midObs rightObs : Observability) :
    mul (mul leftObs midObs) rightObs = mul leftObs (mul midObs rightObs) :=
  add_assoc leftObs midObs rightObs

theorem mul_idem (observability : Observability) : mul observability observability = observability := add_idem observability

/-- Observability mul is commutative — `mul := add := meet` and
    `add_comm` already proven.  Used by tier-generic theorems
    that quantify over `TierSComm` (T2/T7). -/
theorem mul_comm (leftObs rightObs : Observability) :
    mul leftObs rightObs = mul rightObs leftObs :=
  add_comm leftObs rightObs

/-- Distributivity is degenerate under `add = mul = meet`: both
    sides reduce to the same three-way meet by idempotence. -/
theorem left_distrib (leftObs midObs rightObs : Observability) :
    mul leftObs (add midObs rightObs) = add (mul leftObs midObs) (mul leftObs rightObs) := by
  cases leftObs <;> cases midObs <;> cases rightObs <;> rfl
theorem right_distrib (leftObs midObs rightObs : Observability) :
    mul (add leftObs midObs) rightObs = add (mul leftObs rightObs) (mul midObs rightObs) := by
  cases leftObs <;> cases midObs <;> cases rightObs <;> rfl

/-- Antisymmetry — `LessEq` is a genuine partial order. -/
theorem LessEq.antisymm {leftObs rightObs : Observability}
    (hLeftRight : leftObs ≤ rightObs) (hRightLeft : rightObs ≤ leftObs) :
    leftObs = rightObs := by
  cases hLeftRight with
  | refl   => rfl
  | opaqLe => cases hRightLeft

/-- `transparent` is the top: every grade subsumes into `transparent`. -/
theorem le_transparent (observability : Observability) : observability ≤ transparent := by
  cases observability
  · exact LessEq.opaqLe
  · exact LessEq.refl _

/-- `opaq` is the bottom: `opaq` subsumes into every grade. -/
theorem opaq_le (observability : Observability) : opaq ≤ observability := by
  cases observability
  · exact LessEq.refl _
  · exact LessEq.opaqLe

/-- `opaq` absorbs into either side of `add` — witness that
    combining anything with an opaque sub-expression yields an
    opaque expression (the CT propagation rule). -/
theorem add_opaq_left  (observability : Observability) : add opaq observability = opaq := by
  cases observability <;> rfl
theorem add_opaq_right (observability : Observability) : add observability opaq = opaq := by
  cases observability <;> rfl

/-- Monotonicity of `add` in both arguments.  Key property for
    the grade-checker's compositional treatment of CT. -/
theorem add_mono_left {leftObs leftObs' : Observability} (rightObs : Observability)
    (hLeftLe : leftObs ≤ leftObs') :
    add leftObs rightObs ≤ add leftObs' rightObs := by
  cases leftObs <;> cases leftObs' <;> cases rightObs <;>
    first
      | exact LessEq.refl _
      | exact LessEq.opaqLe
      | (cases hLeftLe)

end Observability

/-! ## TierSIdem instance (T2)

Observability fits the idempotent-with-meet shape: `add = mul = meet`
over the 2-element lattice, `transparent` is the meet-identity
(`transparent ⊓ x = x`) and `opaq` is the bottom absorber (used at
join sites to enforce CT: once any sub-expression is opaque, the
whole thing is).  Doesn't satisfy strict annihilation — `mul
transparent x = x`, not `transparent`.

Per §12.5's deny-by-default, source-level Observability defaults to
`opaq`.  We set the carrier `default` to `opaq` accordingly (more
restrictive than the algebraic identity). -/
instance : TierSIdem Observability where
  default      := Observability.opaq
  le           := Observability.LessEq
  le_refl      := Observability.LessEq.refl
  le_trans     := Observability.LessEq.trans
  add          := Observability.add
  mul          := Observability.mul
  zero         := Observability.transparent
  add_comm     := Observability.add_comm
  add_assoc    := Observability.add_assoc
  add_zero     := Observability.add_transparent
  zero_add     := Observability.transparent_add
  mul_assoc    := Observability.mul_assoc
  mul_comm     := Observability.mul_comm
  add_idem     := Observability.add_idem
  mul_eq_add   := fun _ _ => rfl

end FX.Kernel

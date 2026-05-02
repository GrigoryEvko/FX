import LeanFX2.Term
import LeanFX2.Term.ToRaw

/-! # Smoke/Term — concrete typed Term examples.

Verifies Layer 1 Term inductive constructs typed terms with raw forms
recovered as `rfl`. -/

namespace LeanFX2.Smoke.TermDemo

open LeanFX2

-- Identity function: λx. x at type unit → unit
example : Term (Ctx.empty Mode.software 0) (Ty.arrow Ty.unit Ty.unit)
              (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩)) :=
  Term.lam (Term.var ⟨0, Nat.zero_lt_succ _⟩)

-- Application: (λx. x) ()
example : Term (Ctx.empty Mode.software 0) Ty.unit
              (RawTerm.app
                (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
                RawTerm.unit) :=
  Term.app (Term.lam (Term.var ⟨0, Nat.zero_lt_succ _⟩)) Term.unit

-- toRaw is rfl (the load-bearing architectural commitment)
example {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (term : Term context ty raw) : term.toRaw = raw := rfl

-- toRaw on a complex term recovers via rfl — no induction
example :
    (Term.app
      (Term.lam (Term.var ⟨0, Nat.zero_lt_succ _⟩))
      (Term.unit (context := Ctx.empty Mode.software 0))).toRaw
    = RawTerm.app (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ _⟩))
                  RawTerm.unit := rfl

-- Identity type: refl carries its raw witness
example :
    Term (Ctx.empty Mode.software 0) (Ty.id Ty.unit RawTerm.unit RawTerm.unit)
         (RawTerm.refl RawTerm.unit) :=
  Term.refl Ty.unit RawTerm.unit

-- Modal intro/elim: round-trips raw form (Layer 6 will add reduction rules)
example {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {ty : Ty level scope} {raw : RawTerm scope}
    (term : Term context ty raw) :
    (Term.modElim (Term.modIntro term)).toRaw =
      RawTerm.modElim (RawTerm.modIntro raw) := rfl

end LeanFX2.Smoke.TermDemo

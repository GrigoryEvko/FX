import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Typed.HasTypeDescClosedForms
import FX1Poly.Typed.FormationCanonicalForms

/-! # FX1Poly/Typed/ContextValidityFails
    — the WfContextDesc hypothesis in open SN is NECESSARY (the honest negative result)

Open SN (`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`) carries `WfContextDesc Γ` as a hypothesis.
Whether that hypothesis is REDUNDANT — i.e. whether the grown engine presupposes context well-formedness, so
that `HasTypeDescPi Γ t T → WfContextDesc Γ` — it does NOT: this file REFUTES the presupposition, proving the
`WfContextDesc` hypothesis genuinely cannot be dropped.

The witness is the variable rule.  The native `var` rule (`HasTypeDesc.var`, lifted into the grown engine by
`HasTypeDesc.toHasTypeDescPi`) types `var i : Γ.lookup i` in ANY context `Γ`, well-formed or not — it never
inspects the binding types.  So take `Γ = (.empty).cons (λx.x)`, binding the lambda `lamCell (var 0)`.  A lambda
is never a TYPE (`lamCell_isNotType`: by `HasTypeDesc.subjectIsVariableOrFormerHead`, every formation-typed
subject is a variable / Π-code / Σ-code / universe code, and a `lamCell` is none of these — head `gen_lam`), so
`Γ` is ill-formed; yet `var 0` is grown-engine-typed in it.  Hence `HasTypeDescPi Γ t T → WfContextDesc Γ` is
false.

The `WfContextDesc` qualifier on open SN (and on the conversion-decidability / convergence
results built atop it) is a real, irreducible presupposition — "well-typed" in the dependent setting genuinely
means "well-typed in a well-formed context", exactly as the standard metatheory has it.  The CLOSED instance
(`Γ = .empty`, `WfContextDesc.emptyIsWellFormed`) that canonicity / consistency consume is unaffected — it is
trivially well-formed.

## Zero-axiom verification

`lamCell_isNotType` is the formation canonical-forms inversion (`subjectIsVariableOrFormerHead`) plus four
`Generator.noConfusion` head-mismatches — a propext-free pattern.  The counterexample composes it with the
native formation→grown `var` lift (`HasTypeDesc.toHasTypeDescPi`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **A lambda cell is never a formation type.**  `IsTypeDesc` requires the subject to be classified by a
universe code, but `HasTypeDesc.subjectIsVariableOrFormerHead` forces every formation-typed subject to be a
variable cell, a Π-type code, a Σ-type code, or a universe code — and `lamCell body` is none of these (head
generator `gen_lam` differs from each, by `Generator.noConfusion` on `RawTerm.headGenerator`).  The reusable
lemma that makes a context binding a lambda ill-formed. -/
theorem lamCell_isNotType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)} :
    ¬ IsTypeDesc profile context (lamCell body) := by
  rintro ⟨levelExpr, flag, typed⟩
  rcases HasTypeDesc.subjectIsVariableOrFormerHead typed with
    ⟨index, subjectEq⟩ | headIsPi | headIsSigma | headIsUniverse | headIsList | headIsOption
  · exact Generator.noConfusion (congrArg RawTerm.headGenerator subjectEq)
  · exact Generator.noConfusion headIsPi
  · exact Generator.noConfusion headIsSigma
  · exact Generator.noConfusion headIsUniverse
  · exact Generator.noConfusion headIsList
  · exact Generator.noConfusion headIsOption

/-- **A grown-engine typing derivation in a genuinely ill-formed context.**  In `Γ = (.empty).cons (λx.x)`
— ill-formed because its binding `λx.x` is not a formation type (`lamCell_isNotType`) — the variable `var 0` is
grown-engine-typed at `Γ.lookup 0` (the native `HasTypeDesc.var` rule, which ignores binding well-formedness,
lifted to the grown engine by `HasTypeDesc.toHasTypeDescPi`).  The concrete counterexample to the
context-validity presupposition. -/
theorem wellTypedInIllFormedContext {profile : PolyProfile} :
    ∃ (context : TypingContext profile 1) (subject classifier : RawTerm 1),
      HasTypeDescPi profile context subject classifier ∧ ¬ WfContextDesc context :=
  ⟨(TypingContext.empty : TypingContext profile 0).cons
      (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))),
   variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1),
   _,
   HasTypeDesc.toHasTypeDescPi
     (HasTypeDesc.var
       ((TypingContext.empty : TypingContext profile 0).cons
         (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))))
       (⟨0, Nat.succ_pos 0⟩ : Fin 1)),
   fun contextWellFormed => lamCell_isNotType contextWellFormed.2⟩

/-- **The context-validity presupposition FAILS.**  `HasTypeDescPi Γ t T → WfContextDesc Γ`
is NOT provable — the grown engine types terms in ill-formed contexts (`wellTypedInIllFormedContext`).  Hence
the `WfContextDesc` hypothesis on open SN cannot be dropped: it is a genuine, irreducible
presupposition, not a removable artifact.  (The CLOSED `Γ = .empty` instance consumed by canonicity /
consistency is trivially well-formed and so unaffected.) -/
theorem contextValidityPresuppositionFails {profile : PolyProfile} :
    ¬ (∀ {scope : Nat} {context : TypingContext profile scope}
        {subject classifier : RawTerm scope},
        HasTypeDescPi profile context subject classifier → WfContextDesc context) := by
  intro presupposition
  obtain ⟨context, subject, classifier, typed, contextIllFormed⟩ :=
    wellTypedInIllFormedContext (profile := profile)
  exact contextIllFormed (presupposition typed)

end FX1Poly.Typed

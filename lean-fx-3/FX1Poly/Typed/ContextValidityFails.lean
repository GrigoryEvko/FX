import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Typed.HasTypeDescClosedForms
import FX1Poly.Typed.HasTypeHonesty
import FX1Poly.Typed.WfContext

/-! # FX1Poly/Typed/ContextValidityFails
    — the WfContext hypothesis in open SN-043 is NECESSARY (OB-6, the honest negative result)

Open SN-043 (`HasTypeDescPi.stronglyNormalizingOfWfContext`, OB-5) carries `WfContext Γ` as a hypothesis.
OB-6 asks whether that hypothesis is REDUNDANT — i.e. whether the grown engine presupposes context
well-formedness, so that `HasTypeDescPi Γ t T → WfContext Γ`.  It does NOT: this file REFUTES the
presupposition, proving the `WfContext` hypothesis genuinely cannot be dropped.

The witness is the variable rule.  The bespoke `var` rule (`HasType.var`, bridged into the grown engine)
types `var i : Γ.lookup i` in ANY context `Γ`, well-formed or not — it never inspects the binding types.
So take `Γ = (.empty).cons (λx.x)`, binding the lambda `lamCell (var 0)`.  A lambda is never a TYPE
(`lamCell_isNotType`: by `HasType.subjectIsVariableOrTypeFormerCode`, every bespoke-typed subject is a
variable / universe code / Π-code / Σ-code, and a `lamCell` is none of these), so `Γ` is ill-formed; yet
`var 0` is grown-engine-typed in it.  Hence `HasTypeDescPi Γ t T → WfContext Γ` is false.

This sharpens the milestone's honesty: the `WfContext` qualifier on OB-5 (and on the SN-051 / convergence
harvest built atop it) is a real, irreducible presupposition — "well-typed" in the dependent setting
genuinely means "well-typed in a well-formed context", exactly as the standard metatheory has it.  The
CLOSED instance (`Γ = .empty`, `WfContext.emptyIsWellFormed`) that canonicity / consistency consume is
unaffected — it is trivially well-formed.

## Zero-axiom verification

`lamCell_isNotType` is the honesty inversion (`subjectIsVariableOrTypeFormerCode`) plus four
`Generator.noConfusion` head-mismatches — the same propext-free pattern as `appUnitUnit_hasNoTyping`.  The
counterexample composes it with the bespoke→grown `var` bridge.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **A lambda cell is never a type.**  `IsType` requires the subject to be classified by a universe code,
but `HasType.subjectIsVariableOrTypeFormerCode` forces every bespoke-typed subject to be a variable cell, a
universe code, a Π-type code, or a Σ-type code — and `lamCell body` is none of these (head generator
`gen_lam` differs from each, by `Generator.noConfusion` on `RawTerm.headGenerator`).  The reusable lemma
that makes a context binding a lambda ill-formed. -/
theorem lamCell_isNotType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {body : RawTerm (scope + 1)} :
    ¬ IsType profile context (lamCell body) := by
  rintro ⟨levelExpr, flag, typed⟩
  rcases typed.subjectIsVariableOrTypeFormerCode with
    ⟨index, subjectEq⟩ | ⟨lvl, flg, subjectEq⟩ |
      ⟨domainCode, codomainCode, subjectEq⟩ | ⟨domainCode, codomainCode, subjectEq⟩
  · exact Generator.noConfusion (congrArg RawTerm.headGenerator subjectEq)
  · exact Generator.noConfusion (congrArg RawTerm.headGenerator subjectEq)
  · exact Generator.noConfusion (congrArg RawTerm.headGenerator subjectEq)
  · exact Generator.noConfusion (congrArg RawTerm.headGenerator subjectEq)

/-- **A grown-engine typing derivation in a genuinely ill-formed context.**  In `Γ = (.empty).cons (λx.x)`
— ill-formed because its binding `λx.x` is not a type (`lamCell_isNotType`) — the variable `var 0` is
grown-engine-typed at `Γ.lookup 0` (the native `HasTypeDesc.var` rule, which ignores binding well-formedness,
lifted to the grown engine by `HasTypeDesc.toHasTypeDescPi` — no `HasType` bridge).  The concrete counterexample to the
context-validity presupposition. -/
theorem wellTypedInIllFormedContext {profile : PolyProfile} :
    ∃ (context : TypingContext profile 1) (subject classifier : RawTerm 1),
      HasTypeDescPi profile context subject classifier ∧ ¬ WfContext context :=
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

/-- **OB-6, the honest answer: the context-validity presupposition FAILS.**  `HasTypeDescPi Γ t T → WfContext Γ`
is NOT provable — the grown engine types terms in ill-formed contexts (`wellTypedInIllFormedContext`).  Hence
the `WfContext` hypothesis on open SN-043 (OB-5) cannot be dropped: it is a genuine, irreducible
presupposition, not a removable artifact.  (The CLOSED `Γ = .empty` instance consumed by canonicity /
consistency is trivially well-formed and so unaffected.) -/
theorem contextValidityPresuppositionFails {profile : PolyProfile} :
    ¬ (∀ {scope : Nat} {context : TypingContext profile scope}
        {subject classifier : RawTerm scope},
        HasTypeDescPi profile context subject classifier → WfContext context) := by
  intro presupposition
  obtain ⟨context, subject, classifier, typed, contextIllFormed⟩ :=
    wellTypedInIllFormedContext (profile := profile)
  exact contextIllFormed (presupposition typed)

end FX1Poly.Typed

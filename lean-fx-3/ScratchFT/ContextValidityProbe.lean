import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Typed.HasTypeDescClosedForms
import FX1Poly.Typed.HasTypeHonesty
import FX1Poly.Typed.WfContext

/-! Probe (NEVER committed): OB-6 — is the WfContext hypothesis in OB-5 droppable?
    Claim under test: HasTypeDescPi Γ t T → WfContext Γ.  REFUTED: a lamCell is never a
    type (subjectIsVariableOrTypeFormerCode), so Γ = (.empty).cons (λx.x) is ill-formed,
    yet the bespoke var rule types var 0 in it (bridged into the grown engine). -/

namespace FX1Poly.Typed.Spike

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

-- A lambda cell is never a type: it is neither a variable nor a type-former code.
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

-- The counterexample: a typing derivation in a genuinely ill-formed context.
theorem wellTypedInIllFormedContext {profile : PolyProfile} :
    ∃ (context : TypingContext profile 1) (subject classifier : RawTerm 1),
      HasTypeDescPi profile context subject classifier ∧ ¬ WfContext context :=
  ⟨(TypingContext.empty : TypingContext profile 0).cons
      (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))),
   variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1),
   _,
   HasTypeDesc.toHasTypeDescPi
     (HasType.toHasTypeDesc
       (HasType.var
         ((TypingContext.empty : TypingContext profile 0).cons
           (lamCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))))
         (⟨0, Nat.succ_pos 0⟩ : Fin 1))),
   fun wf => lamCell_isNotType wf.2⟩

-- Hence the universal presupposition fails: WfContext cannot be dropped from OB-5.
theorem contextValidityPresuppositionFails {profile : PolyProfile} :
    ¬ (∀ {scope : Nat} {context : TypingContext profile scope}
        {subject classifier : RawTerm scope},
        HasTypeDescPi profile context subject classifier → WfContext context) := by
  intro presupposition
  obtain ⟨context, subject, classifier, typed, contextIllFormed⟩ :=
    wellTypedInIllFormedContext (profile := profile)
  exact contextIllFormed (presupposition typed)

end FX1Poly.Typed.Spike

#print axioms FX1Poly.Typed.Spike.lamCell_isNotType
#print axioms FX1Poly.Typed.Spike.wellTypedInIllFormedContext
#print axioms FX1Poly.Typed.Spike.contextValidityPresuppositionFails

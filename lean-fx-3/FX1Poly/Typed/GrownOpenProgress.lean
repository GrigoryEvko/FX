import FX1Poly.Typed.GrownCanonicalForms
import FX1Poly.Typed.GrownTypeSafety
import FX1Poly.Core.NeutralTerm

/-! # FX1Poly/Typed/GrownOpenProgress — OPEN progress for the grown engine `HasTypeDescPi`
    (five-layer-defense L4, §27.3: progress generalized off the empty context, with neutrals)

`GrownTypeSafety.closedProgress` proves progress for CLOSED grown-typed terms: a closed grown-typed term is a
canonical value or it steps.  Closedness is load-bearing there — the empty context has no variables, so the only
normal forms are canonical heads (λ / Π-code / Σ-code / universe-code).  The standard **open** progress / canonical
forms lemma drops closedness and admits the extra normal form that variables introduce: a **neutral** term (a
variable, or an application whose function head is itself neutral, so β can never fire).  This file ships the open
statements over the shipped `Core.IsNeutral` predicate — no new inductive.

  * `HasTypeDescPi.openNormalSubjectCanonicalOrNeutral` — **open canonical forms.**  A grown-typed NORMAL term in
    ANY well-formed context is a canonical head (`IsGrownCanonicalHead`: λ / Π-code / Σ-code / universe-code) or a
    `Core.IsNeutral` term.  The recursor mirrors `closedNormalSubjectHead` but drops the `(Fin scope → False)`
    premise: the `var` arm now concludes `IsNeutral.var` instead of an absurdity, and the `piElim` arm whose
    function head is neutral concludes `IsNeutral.app` (the function cannot be a λ — that would be a β-redex,
    contradicting normality — nor a type former / universe code — those are typed at a universe, never at the Π
    the function inhabits — so by induction it is neutral, and the application inherits neutrality).

  * `HasTypeDescPi.openProgress` — **open progress (unconditional).**  A grown-typed term in any well-formed
    context is either a normal form that is a canonical value OR a neutral (`(IsGrownCanonicalHead ∨ IsNeutral) ∧
    isStepNormalForm`), or it takes a `Step`.  Dispatches on decidable normality: normal ⟹ canonical-or-neutral
    by the open canonical-forms lemma, non-normal ⟹ steps by `exists_step_of_not_isStepNormalForm`.  The open
    generalization of `closedProgress` — no closed terms exist that are stuck, in ANY context.

This is the open form of the §27.3 five-layer-defense L4 progress statement: `closedProgress` is its specialization
to the empty context, where the neutral disjunct is vacuous (no variables) and the canonical-value disjunct
suffices.  `#672`-independent — pure inversion over the shipped closed-canonical-forms recursor, generalized to
admit variable leaves.

## Zero-axiom verification

The recursor mirrors `closedNormalSubjectHead`; the new content is the two leaf reroutings (`var` →
`IsNeutral.var`, neutral-function `app` → `IsNeutral.app`), where `variableCell index` and `appCell f a` are
definitionally the `mkGen gen_var …` / `mkGen gen_app …` cells the `IsNeutral` constructors expect.  Open progress
is a `by_cases` on the decidable `isStepNormalForm`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega` (verified by `#print axioms` in scratch before landing).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **Open canonical forms for the grown engine.**  A grown-typed NORMAL term in any well-formed context is a
canonical head (`IsGrownCanonicalHead`) or a neutral (`Core.IsNeutral`).  The open analogue of
`closedNormalSubjectHead`: dropping closedness admits the variable leaf (`IsNeutral.var`) and the neutral
application (`IsNeutral.app`).  Proof by the `HasTypeDescPi` recursor — the same arm structure as the closed
version, routing the two leaves that closedness would eliminate. -/
theorem HasTypeDescPi.openNormalSubjectCanonicalOrNeutral {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDesc context)
    (normal : RawTerm.isStepNormalForm subject) :
    RawTerm.IsGrownCanonicalHead subject ∨ IsNeutral subject := by
  refine HasTypeDescPi.rec
    (motive_1 := fun {armScope} armContext armSubject _armClassifier _armTyped =>
      WfContextDesc armContext → RawTerm.isStepNormalForm armSubject →
      (RawTerm.IsGrownCanonicalHead armSubject ∨ IsNeutral armSubject))
    (motive_2 := fun _armContext _armLevels _armFlag _armChildren _armTelescope => True)
    ?ofFormation ?conv ?piIntro ?piElim ?genFormationPi ?nilTelescope ?consTelescope
    typed wellFormed normal
  · intro _armScope _armContext _armSubject _armClassifier formationTyped _armWf _armNormal
    rcases HasTypeDesc.subjectIsVariableOrFormerHead formationTyped with ⟨index, subjectEq⟩ | rest
    · rw [subjectEq]
      exact Or.inr (IsNeutral.var index)
    · exact Or.inl (Or.inr rest)
  · intro _armScope _armContext _armSubject _armClassifier _reclassifier _levelExpr _flag _typed
      _converts _reclassifierTyped subjectIH _reclassifierIH armWf armNormal
    exact subjectIH armWf armNormal
  · intro _armScope _armContext _domainCode _codomainCode _body _domainLevel _codomainLevel _flag
      _domainTyped _codomainTyped _bodyTyped _domainIH _codomainIH _bodyIH _armWf _armNormal
    exact Or.inl (Or.inl rfl)
  · intro _armScope _armContext functionTerm argument _domainCode _codomainCode functionTyped
      _argumentTyped functionIH _argumentIH armWf armNormal
    have functionNormal : RawTerm.isStepNormalForm functionTerm :=
      appNormal_functionNormal functionTerm argument armNormal
    rcases functionIH armWf functionNormal with
        (headLam | headPi | headSigma | headUniverse | headList | headOption) | functionNeutral
    · exfalso
      obtain ⟨domainAnn, body, bodyEq⟩ := eq_lamCell_of_headGenerator headLam
      rw [bodyEq] at armNormal
      exact RawTerm.not_isStepNormalForm_beta_smoke domainAnn body argument armNormal
    · exfalso
      obtain ⟨_innerDomain, _innerCodomain, piEq⟩ := eq_piTyCodeCell_of_headGenerator headPi
      rw [piEq] at functionTyped
      exact HasTypeDescPi.piFormerNotTypedAtPiType functionTyped
    · exfalso
      obtain ⟨_innerDomain, _innerCodomain, sigmaEq⟩ := eq_sigmaTyCodeCell_of_headGenerator headSigma
      rw [sigmaEq] at functionTyped
      exact HasTypeDescPi.sigmaFormerNotTypedAtPiType functionTyped
    · exfalso
      obtain ⟨_levelExpr, _flag, universeEq⟩ := eq_universeCodeCell_of_headGenerator headUniverse
      rw [universeEq] at functionTyped
      exact HasTypeDescPi.universeCodeNotTypedAtPiType functionTyped
    · exfalso
      obtain ⟨_element, listEq⟩ := eq_listCodeCell_of_headGenerator headList
      rw [listEq] at functionTyped
      exact HasTypeDescPi.listFormerNotTypedAtPiType functionTyped
    · exfalso
      obtain ⟨_element, optionEq⟩ := eq_optionCodeCell_of_headGenerator headOption
      rw [optionEq] at functionTyped
      exact HasTypeDescPi.optionFormerNotTypedAtPiType functionTyped
    · exact Or.inr (IsNeutral.app functionNeutral)
  · intro _armScope _armContext generator _payload _children _levels _flag _rule isFormation _premises
      _premisesIH _armWf _armNormal
    by_cases isPi : generator = Generator.gen_piTyCode
    · exact Or.inl (Or.inr (Or.inl (by subst isPi; rfl)))
    · by_cases isSigma : generator = Generator.gen_sigmaTyCode
      · exact Or.inl (Or.inr (Or.inr (Or.inl (by subst isSigma; rfl))))
      · by_cases isList : generator = Generator.gen_listCode
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by subst isList; rfl))))))
        · by_cases isOption : generator = Generator.gen_optionCode
          · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by subst isOption; rfl))))))
          · exfalso
            unfold typingRuleDescOf at isFormation
            rw [if_neg isPi, if_neg isSigma, if_neg isList, if_neg isOption] at isFormation
            contradiction
  · intro _armBaseScope _armCurrentDepth _armContext _armFlag
    exact True.intro
  · intro _armBaseScope _armCurrentDepth _armRestShifts _armContext _armHead _armHeadLevel
      _armRestLevels _armFlag _armRest _armHeadTyped _armRestTyped _armHeadIH _armRestIH
    exact True.intro

/-- **Open progress (unconditional).**  A grown-typed term in any well-formed context is either a normal form that
is a canonical value or a neutral, or it takes a `Step` — there are no stuck grown-typed terms in any context.
Dispatches on decidable normality: a normal subject is canonical-or-neutral by
`openNormalSubjectCanonicalOrNeutral`; a non-normal subject steps by `exists_step_of_not_isStepNormalForm`.  The
open generalization of `closedProgress`, whose empty-context specialization drops the (then-vacuous) neutral
disjunct. -/
theorem HasTypeDescPi.openProgress {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier)
    (wellFormed : WfContextDesc context) :
    ((RawTerm.IsGrownCanonicalHead subject ∨ IsNeutral subject) ∧ RawTerm.isStepNormalForm subject)
    ∨ (∃ reduct : RawTerm scope, Step subject reduct) := by
  by_cases isNormal : RawTerm.isStepNormalForm subject
  · exact Or.inl ⟨HasTypeDescPi.openNormalSubjectCanonicalOrNeutral typed wellFormed isNormal, isNormal⟩
  · exact Or.inr (exists_step_of_not_isStepNormalForm isNormal)

end FX1Poly.Typed

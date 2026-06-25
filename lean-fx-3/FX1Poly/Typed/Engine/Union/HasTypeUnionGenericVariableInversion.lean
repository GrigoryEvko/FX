import FX1Poly.Typed.Engine.Union.HasTypeUnionGenericElimInversion

/-! # FX1Poly/Typed/Engine/Union/HasTypeUnionGenericVariableInversion
    — the generic native variable-head inversion (foundational leaf of universe-flag-uniqueness)

The `var`-surviving twin of `HasTypeUnion.invertAtElimHeadGeneric`: when the subject's root generator is
`gen_var`, the subject IS a `variableCell` and its context lookup converts TO the classifier.  Reflected to
`toNativeOnly` and inducted over the six native arms — `universeFormation` refutes by literal head
distinctness (`Generator.noConfusion`); `formationRule` / `intro` / `elim` refute by root-generator
coherence (`rootGenerator (memberCell) = <their generator>`, pinned to `gen_var`, then the `*RuleOf gen_var
= none` definitional reductions); `conv` recurses, composing the conversion; only `var` survives, contributing
`Conv.refl`.

This is the foundational leaf the native universe-flag-uniqueness metatheorem (the consistency-leg keystone,
TYTAB-2-FT #1697 / TYTAB-2-FT-SR #1740) builds on: two universe-code classifiers of one variable are each
`Conv` from the SAME context lookup, hence `Conv` to each other.  The native port of the grown
`HasTypeDescPi.variableUniverseClassificationUnique` leaf.

## Zero-axiom verification

`toNativeOnly`, the root-generator coherences (`introMemberCellRootGenerator` / `elimMemberCellRootGenerator`),
the `*RuleOf gen_var = none` reductions, `Generator.noConfusion`, `Conv.refl` / `Conv.trans`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **★ The generic native variable-head inversion.**  When `RawTerm.rootGenerator subject = gen_var`, the
subject is a `variableCell index` whose context lookup `context.lookup index` converts to the classifier.  The
`var`-surviving mirror of `invertAtElimHeadGeneric`. -/
theorem HasTypeUnion.invertAtVarHeadGeneric {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (headIsVar : RawTerm.rootGenerator subject = Generator.gen_var) :
    ∃ index : Fin scope,
      subject = variableCell index ∧ Conv (context.lookup index) classifier := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _ctx index => exact ⟨index, rfl, Conv.refl _⟩
  | universeFormation _ctx _levelExpr _flag =>
      have headEq : Generator.gen_universeCode = Generator.gen_var := headIsVar
      exact Generator.noConfusion headEq
  | formationRule _ctx formGen _payload _children _formRule _levels _carrier _level _flag
      isFormationRule _premisesHold _ihPremises =>
      have headEq : formGen = Generator.gen_var := headIsVar
      subst headEq
      rw [show formationRuleOf Generator.gen_var = none from rfl] at isFormationRule
      cases isFormationRule
  | intro _ctx introGen _introRule introArgs _params _level0 _level1 _flag isIntro _sideHolds
      _premisesHold _ihPremises =>
      have headEq : introGen = Generator.gen_var :=
        (introMemberCellRootGenerator isIntro introArgs).symm.trans headIsVar
      subst headEq
      rw [show introRuleOf Generator.gen_var = none from rfl] at isIntro
      cases isIntro
  | elim _ctx elimGen _elimRule elimArgs _elimParams _elimLevel0 _elimLevel1 _elimFlag isElim
      _premisesHold _ihPremises =>
      have headEq : elimGen = Generator.gen_var :=
        (elimMemberCellRootGenerator isElim elimArgs).symm.trans headIsVar
      subst headEq
      rw [show elimRuleOf Generator.gen_var = none from rfl] at isElim
      cases isElim
  | conv _levelExpr _flag _typed converts _reclassifierTyped typedIH _reclassifierIH =>
      obtain ⟨index, subjectShape, lookupConv⟩ := typedIH headIsVar
      exact ⟨index, subjectShape, lookupConv.trans converts⟩

end FX1Poly.Typed

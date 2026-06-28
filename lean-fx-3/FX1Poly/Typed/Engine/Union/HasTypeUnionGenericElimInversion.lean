import FX1Poly.Typed.Engine.Union.HasTypeUnionMemberCellRootGenerator
import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnlyAdmissibility

/-! # FX1Poly/Typed/Engine/Union/HasTypeUnionGenericElimInversion
    — the ONE table-driven eliminator-head inversion (TYTAB-2, subsumes the 11 bespoke `invertAt<X>Head`)

Every per-eliminator head inversion (`invertAtAppHead`, `invertAtBoolElimHead`, the `…AllPremises`
companions, …) is the SAME induction over the six native union arms: refute var / universe / formation /
intro / the ten non-matching elim rows, survive the one matching elim row, thread the `conv` arm.  Rather
than re-spell that induction once per generator, this file proves it ONCE, generically over an arbitrary
`ElimRule` selected by `elimRuleOf generator = some rule`.

The conclusion is stated EXISTENTIALLY in the row's own data — the children `args`, the type-index `params`,
the universe levels / flag — together with `subject = rule.memberCell scope args` (the cell shape) and the
full obligation list typed at the union judgment plus the output `Conv`.  Concluding `args` / `params`
existentially is what keeps the proof table-generic: no per-rule `memberCell`-injectivity is needed here
(the survivor simply hands back its own `args'`); the thin per-eliminator wrappers recover the named children
by matching `subject = <specificCell> = rule.memberCell scope args` at the CONCRETE rule, where the cell
constructor is injective.

The two refutation halves use the rule-table disjointness lemmas below (`introRuleOf` / `formationRuleOf`
collapse to `none` on any elim generator), themselves one `elimRuleOf_cases` enumeration discharged by `rfl`
per row — the enumeration is paid ONCE here, not once per bespoke inversion.

## Zero-axiom verification

Free-subject `induction` over `HasTypeUnionNativeOnly` (via `toNativeOnly`) + the head-projection helpers +
the disjointness `rfl`s + `Option`/`Generator` no-confusion.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **An elim generator has no introducer row.**  `introRuleOf` and `elimRuleOf` are disjoint: enumerate the
eleven elim generators (via `elimRuleOf_cases`); each has `introRuleOf … = none` by `rfl`. -/
theorem introRuleOf_eq_none_ofElim {generator : Generator} {rule : ElimRule}
    (isElim : elimRuleOf generator = some rule) : introRuleOf generator = none := by
  rcases elimRuleOf_cases isElim with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- **An elim generator has no formation row.**  `formationRuleOf` and `elimRuleOf` are disjoint: enumerate
the eleven elim generators; each has `formationRuleOf … = none` by `rfl`. -/
theorem formationRuleOf_eq_none_ofElim {generator : Generator} {rule : ElimRule}
    (isElim : elimRuleOf generator = some rule) : formationRuleOf generator = none := by
  rcases elimRuleOf_cases isElim with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- **An intro generator has no elim row.**  Dual of `introRuleOf_eq_none_ofElim`: enumerate the seventeen
intro generators; each has `elimRuleOf … = none` by `rfl`. -/
theorem elimRuleOf_eq_none_ofIntro {generator : Generator} {rule : IntroRule}
    (isIntro : introRuleOf generator = some rule) : elimRuleOf generator = none := by
  rcases introRuleOf_cases isIntro with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- **An intro generator has no formation row.**  Dual of `formationRuleOf_eq_none_ofElim`. -/
theorem formationRuleOf_eq_none_ofIntro {generator : Generator} {rule : IntroRule}
    (isIntro : introRuleOf generator = some rule) : formationRuleOf generator = none := by
  rcases introRuleOf_cases isIntro with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- **★ The ONE table-driven eliminator-head inversion.**  A union typing of an elim-row-headed subject
(`rootGenerator subject = generator`, `elimRuleOf generator = some rule`) is EXACTLY that row's typing: for
some children `args`, type-index `params`, levels, and flag, the subject IS the row's member cell, every one
of the row's obligations is union-typed, and the row's output type is `Conv`-equal to the ambient classifier.
The generic substrate the per-eliminator inversions specialize. -/
theorem HasTypeUnion.invertAtElimHeadGeneric {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {generator : Generator} {rule : ElimRule}
    (isElim : elimRuleOf generator = some rule)
    (derivation : HasTypeUnion profile context subject classifier)
    (headIsGenerator : RawTerm.rootGenerator subject = generator) :
    ∃ (args : RawTermChildren rule.argShifts scope)
      (params : RawTermChildren rule.paramShifts scope)
      (level0 level1 : LevelExpr) (flag : UniverseFlag),
      subject = rule.memberCell scope args ∧
      (∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
        HasTypeUnion profile obligation.context obligation.subject obligation.classifier) ∧
      (∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
        obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true) ∧
      Conv (rule.outputType scope args params) classifier := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _ctx index =>
      have headEq : Generator.gen_var = generator := headIsGenerator
      rw [← headEq, show elimRuleOf Generator.gen_var = none from rfl] at isElim
      cases isElim
  | universeFormation _ctx _levelExpr _flag =>
      have headEq : Generator.gen_universeCode = generator := headIsGenerator
      rw [← headEq, show elimRuleOf Generator.gen_universeCode = none from rfl] at isElim
      cases isElim
  | formationRule _ctx formGen _payload _children _formRule _levels _carrier _level _flag
      isFormationRule _premisesHold _ihPremises =>
      -- The formation member cell `.mkGen formGen …` head is `formGen`; pin it to `generator`.
      have headEq : formGen = generator := headIsGenerator
      subst headEq
      rw [formationRuleOf_eq_none_ofElim isElim] at isFormationRule
      cases isFormationRule
  | intro _ctx introGen introRule introArgs _params _level0 _level1 _flag isIntro _sideHolds
      _premisesHold _ihPremises =>
      have headEq : introGen = generator :=
        (introMemberCellRootGenerator isIntro introArgs).symm.trans headIsGenerator
      subst headEq
      rw [introRuleOf_eq_none_ofElim isElim] at isIntro
      cases isIntro
  | elim _ctx elimGen elimRule elimArgs elimParams elimLevel0 elimLevel1 elimFlag isElim' premisesHold
      usabilityHolds =>
      -- The surviving row: pin `elimGen = generator`, then `elimRule = rule` by `elimRuleOf` injectivity.
      have headEq : elimGen = generator :=
        (elimMemberCellRootGenerator isElim' elimArgs).symm.trans headIsGenerator
      subst headEq
      have ruleEq : rule = elimRule := Option.some.inj (isElim.symm.trans isElim')
      subst ruleEq
      exact ⟨elimArgs, elimParams, elimLevel0, elimLevel1, elimFlag, rfl,
        fun obligation hmem => (premisesHold obligation hmem).toUnion, usabilityHolds, Conv.refl _⟩
  | conv _levelExpr _flag _typed converts _reclassifierTyped typedIH _reclassifierIH =>
      obtain ⟨args, params, level0, level1, flag, subjectShape, obligationsHold, usableHold, outputConv⟩ :=
        typedIH headIsGenerator
      exact ⟨args, params, level0, level1, flag, subjectShape, obligationsHold, usableHold,
        outputConv.trans converts⟩

/-- **★ The table-driven INTRODUCER-head usability inversion (A1-CONJUNCT-WIRE).**  A union typing of an
intro-row-headed subject surfaces the introducer's `usabilityHolds` conjunct: for the row's children `args`,
type-index `params`, levels, and flag, the subject IS the row's member cell, and every obligation is
fibrantly/dimensionally usable at its declared modality.  The introducer twin of `invertAtElimHeadGeneric`'s
usability half — the construction-site use-site conjunct, recovered from the redex's own derivation so the
data-constructor ι reducts can feed the payload usability with NO extra hypothesis.  Same one-pass induction
over `toNativeOnly`: the four non-intro arms refute (`introRuleOf`/`elimRuleOf`/`formationRuleOf` disjointness),
the `intro` arm yields its `usabilityHolds` field, the `conv` arm recurses (the subject is conv-stable). -/
theorem HasTypeUnion.invertAtIntroHeadGenericUsable {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {generator : Generator} {rule : IntroRule}
    (isIntro : introRuleOf generator = some rule)
    (derivation : HasTypeUnion profile context subject classifier)
    (headIsGenerator : RawTerm.rootGenerator subject = generator) :
    ∃ (args : RawTermChildren rule.argShifts scope)
      (params : RawTermChildren rule.paramShifts scope)
      (level0 level1 : LevelExpr) (flag : UniverseFlag),
      subject = rule.memberCell scope args ∧
      (∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
        obligation.context.isSubjectUsableAtModality obligation.subject obligation.modality = true) := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _ctx index =>
      have headEq : Generator.gen_var = generator := headIsGenerator
      rw [← headEq, show introRuleOf Generator.gen_var = none from rfl] at isIntro
      cases isIntro
  | universeFormation _ctx _levelExpr _flag =>
      have headEq : Generator.gen_universeCode = generator := headIsGenerator
      rw [← headEq, show introRuleOf Generator.gen_universeCode = none from rfl] at isIntro
      cases isIntro
  | formationRule _ctx formGen _payload _children _formRule _levels _carrier _level _flag
      isFormationRule _premisesHold _ihPremises =>
      have headEq : formGen = generator := headIsGenerator
      subst headEq
      rw [formationRuleOf_eq_none_ofIntro isIntro] at isFormationRule
      cases isFormationRule
  | intro _ctx introGen introRule introArgs introParams introLevel0 introLevel1 introFlag isIntro'
      _sideHolds _premisesHold usabilityHolds =>
      have headEq : introGen = generator :=
        (introMemberCellRootGenerator isIntro' introArgs).symm.trans headIsGenerator
      subst headEq
      have ruleEq : rule = introRule := Option.some.inj (isIntro.symm.trans isIntro')
      subst ruleEq
      exact ⟨introArgs, introParams, introLevel0, introLevel1, introFlag, rfl, usabilityHolds⟩
  | elim _ctx elimGen _elimRule elimArgs _elimParams _elimLevel0 _elimLevel1 _elimFlag isElim'
      _premisesHold _usabilityHolds =>
      have headEq : elimGen = generator :=
        (elimMemberCellRootGenerator isElim' elimArgs).symm.trans headIsGenerator
      subst headEq
      rw [elimRuleOf_eq_none_ofIntro isIntro] at isElim'
      cases isElim'
  | conv _levelExpr _flag _typed _converts _reclassifierTyped typedIH _reclassifierIH =>
      obtain ⟨args, params, level0, level1, flag, subjectShape, usableHold⟩ :=
        typedIH headIsGenerator
      exact ⟨args, params, level0, level1, flag, subjectShape, usableHold⟩

end FX1Poly.Typed

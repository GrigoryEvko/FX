import FX1Poly.Typed.Engine.Union.HasTypeUnionGenericVariableInversion
import FX1Poly.Typed.Engine.Classifier.DimensionLockAccessibility
import FX1Poly.Tier0.Term.Rename.RawTermWeaken

/-! # FX1Poly/Typed/Metatheory/SubjectReduction/PathLamStructuralAffinity — the structural-affinity theorem

The structural foundation for the FIBRANT leg of `pathLam`'s affineness: the Fitch dimension-lock
accessibility discipline (`DimensionLockAccessibility`) blocks fibrant use of the interval variable.  This
COMPLEMENTS — it does NOT replace — the affine multiplicity count, which additionally bounds DIMENSIONAL use
(see "Why it matters" below).

## What the theorem says

Under a `lockCons` context — the context the bridge body sees, where the interval dimension is bound as the
single UNPOINTED AFFINE variable `var 0` — the newest de Bruijn variable `var 0`
(`RawTerm.newestVar`) is NOT union-typeable as a fibrant value.  Formally,
`lockedDimensionVar_isNotFibrantlyTypeable` shows that no `HasTypeUnion` derivation can type
`var 0` under `restContext.lockCons dimensionType`.

## Why it matters (the FIBRANT leg of affineness)

The native variable leaf `HasTypeUnionNativeOnly.var` carries the side condition
`context.isFibrantlyAccessibleAt index = true` (the Fitch fibrant-accessibility premise).  The locked
interval variable is fibrantly INACCESSIBLE: `dimensionIsNotFibrantlyAccessible` proves
`(restContext.lockCons dimensionType).isFibrantlyAccessibleAt ⟨0, _⟩ = false` (the unpointed affine
multiplier has no 2-cell `mu_affine => 1`).  So a derivation that tries to use `var 0` as a fibrant value
discharges an unsatisfiable premise, and no such derivation exists.

The consequence is that the canonical FIBRANT subject-reduction breaker `pair (var 0) (var 0)` — a fibrant
pair whose component obligations demand `var 0` at the fibrant modality — is STRUCTURALLY untypeable under the
lock, with no reference to occurrence count.  This is the FIBRANT leg of affineness, and it is beta-stable.

It does NOT, however, make the count redundant.  The affine restriction is NO-DIAGONAL (no contraction of the
dimension variable; transpension LICS 2008.08533 §2.1.1), which must ALSO reject the DIMENSIONAL diagonal
`f (b1@i) (b2@i)` — a term that factors through the diagonal `I -> I x I`.  `pathLam`'s
`gradedBinderChecks UsageGrade.one = (occurrenceCountAt body 0 <= 1)` bounds `var 0` occurrences in BOTH
fibrant AND dimensional positions, so it catches that dimensional diagonal; the lock does NOT (pathApp's
interval argument uses the `.dimensional` modality, a Boolean accessibility with no count).  So the lock
(fibrant ACCESSIBILITY) and the count (affine MULTIPLICITY) are COMPLEMENTARY legs.  The count retires only
once its multiplicity job moves to a beta-stable STRUCTURAL mechanism — the usage grade (`HasGradeOver`) or
the no-contraction substitution discipline — the genuine affine lock (A1-NEG-LOCK).

## Proof shape

The work is the free-context inversion `HasTypeUnion.varSubjectIsFibrantlyAccessible`: a union typing of any
variable-headed subject exhibits the variable's index together with the leaf's fibrant-accessibility premise.
Its induction mirrors `HasTypeUnion.invertAtVarHeadGeneric` exactly — reflected to `toNativeOnly`, the
`universeFormation` / `formationRule` / `intro` / `elim` arms all die by root-generator head mismatch against
`gen_var`, `conv` recurses, and only the `var` arm survives, returning its own bound index and accessibility
premise.  The headline theorem then specialises the context to the lock, matches the recovered index against
`var 0` via `mkGen` injectivity (at a single fixed scope, so a plain equality), and contradicts the recovered
`= true` premise with `dimensionIsNotFibrantlyAccessible`'s `= false`.  Keeping the inversion's context FREE
and returning the index as an existential — rather than comparing against a fixed index INSIDE the induction —
sidesteps both inducting over a concrete `lockCons` index and the cross-scope heterogeneity the generalised
induction would otherwise introduce.

## Zero-axiom

`toNativeOnly`, the root-generator coherences (`introMemberCellRootGenerator` / `elimMemberCellRootGenerator`),
the `*RuleOf gen_var = none` reductions, `Generator.noConfusion`, `mkGen` injectivity, and `Bool.noConfusion`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **★ The variable-head fibrant-accessibility inversion.**  A union typing whose subject's root generator is
`gen_var` exhibits the de Bruijn index of that variable together with the Fitch fibrant-accessibility premise
`context.isFibrantlyAccessibleAt index = true`: every typed variable use was admitted by the native `var`
leaf, whose side condition this recovers.  Free context (so no concrete-context induction is needed); the
`var`-surviving mirror of `HasTypeUnion.invertAtVarHeadGeneric`, but returning the accessibility witness the
generic inversion discards.  The index is returned existentially (the surviving `var` arm uses its OWN bound
index) so the caller compares it against a fixed index at a single scope, avoiding the cross-scope
heterogeneity a comparison inside the generalised induction would introduce. -/
theorem HasTypeUnion.varSubjectIsFibrantlyAccessible {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier)
    (headIsVar : RawTerm.rootGenerator subject = Generator.gen_var) :
    ∃ index : Fin scope,
      subject = variableCell index ∧ context.isFibrantlyAccessibleAt index = true := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var _armContext armIndex isAccessible =>
      -- The only surviving arm: the subject IS a variable, so its own index and the leaf's accessibility
      -- premise discharge the existential.
      exact ⟨armIndex, rfl, isAccessible⟩
  | universeFormation _armContext _levelExpr _flag =>
      have headEq : Generator.gen_universeCode = Generator.gen_var := headIsVar
      exact Generator.noConfusion headEq
  | formationRule _armContext formGenerator _payload _children _formRule _levels _carrier _level _flag
      isFormationRule _premisesHold _ihPremises =>
      have headEq : formGenerator = Generator.gen_var := headIsVar
      subst headEq
      rw [show formationRuleOf Generator.gen_var = none from rfl] at isFormationRule
      cases isFormationRule
  | intro _armContext introGenerator _introRule introArgs _params _level0 _level1 _flag isIntro _sideHolds
      _premisesHold _ihPremises =>
      have headEq : introGenerator = Generator.gen_var :=
        (introMemberCellRootGenerator isIntro introArgs).symm.trans headIsVar
      subst headEq
      rw [show introRuleOf Generator.gen_var = none from rfl] at isIntro
      cases isIntro
  | elim _armContext elimGenerator _elimRule elimArgs _elimParams _elimLevel0 _elimLevel1 _elimFlag isElim
      _premisesHold _ihPremises =>
      have headEq : elimGenerator = Generator.gen_var :=
        (elimMemberCellRootGenerator isElim elimArgs).symm.trans headIsVar
      subst headEq
      rw [show elimRuleOf Generator.gen_var = none from rfl] at isElim
      cases isElim
  | conv _levelExpr _flag _typed _converts _reclassifierTyped typedIH _reclassifierIH =>
      -- The conversion arm preserves the subject, so the inner derivation has the same variable head.
      exact typedIH headIsVar

/-- **★ The structural-affinity theorem.**  Under a `lockCons` context — where the interval dimension is the
single unpointed affine `var 0` — the newest de Bruijn variable `RawTerm.newestVar` (`var 0`) is NOT
union-typeable.  Any derivation would discharge the native `var` leaf's fibrant-accessibility premise
`(restContext.lockCons dimensionType).isFibrantlyAccessibleAt ⟨0, _⟩ = true`, which
`dimensionIsNotFibrantlyAccessible` refutes (`= false`).

So the locked dimension cannot be used as a fibrant value, and the canonical FIBRANT subject-reduction breaker
`pair (var 0) (var 0)` is structurally untypeable under the lock.  This is the FIBRANT leg of affineness —
beta-stable, unlike the occurrence count.  It does NOT subsume `pathLam`'s `gradedBinderChecks UsageGrade.one`,
which additionally bounds the DIMENSIONAL occurrences the lock leaves free (the dimensional diagonal
`f (b1@i) (b2@i)`); the two are complementary legs of the affine discipline. -/
theorem lockedDimensionVar_isNotFibrantlyTypeable {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {dimensionType : RawTerm scope}
    {subject classifier : RawTerm (scope + 1)}
    (derivation : HasTypeUnion profile (restContext.lockCons dimensionType) subject classifier)
    (subjectShape : subject = RawTerm.newestVar) : False := by
  have headIsVar : RawTerm.rootGenerator subject = Generator.gen_var :=
    congrArg RawTerm.rootGenerator subjectShape
  obtain ⟨recoveredIndex, subjectIsVar, accessible⟩ :=
    HasTypeUnion.varSubjectIsFibrantlyAccessible derivation headIsVar
  -- `subjectIsVar` and `subjectShape` agree on the subject, so the recovered index IS `var 0` — and since both
  -- live at the fixed scope `scope + 1`, `mkGen` injectivity yields a plain equality (no cross-scope `HEq`).
  have varCellEq : (variableCell recoveredIndex : RawTerm (scope + 1))
      = variableCell ⟨0, Nat.zero_lt_succ scope⟩ :=
    subjectIsVar.symm.trans subjectShape
  injection varCellEq with _scopeEq _generatorEq indexEq _childrenEq
  subst indexEq
  exact Bool.noConfusion
    (accessible.symm.trans
      (dimensionIsNotFibrantlyAccessible restContext dimensionType (Nat.zero_lt_succ scope)))

end FX1Poly.Typed

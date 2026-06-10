import FX1Poly.Typed.GrownStrengthening

/-! Probe: refute the EXISTENTIAL form of grown strengthening and pin the image-constrained target.

The naive strengthening claim — "any grown typing of a weakened subject has its classifier in the
weaken image" — is FALSE: the grown `conv` arm can reclassify a weakened subject at a β-expansion
of its natural classifier whose argument is `variableCell 0`, a term that syntactically mentions the
fresh binder and therefore escapes the weaken image.  Counterexample: in `[Type@0]`, the weakened
subject `weaken Type@0` types at `Type@1` and `conv`-reclassifies at
`(λ. Type@1) (var 0)` (β-convertible to `Type@1`, typed at `Type@2` via `piElim ∘ piIntro`).

Consequence: derivation induction on the BOTH-PINNED statement (weakened subject AND weakened
classifier) cannot keep intermediate classifiers inside the weaken image — the committed route is
checker completeness ∘ rename-equivariance ∘ soundness.  The both-pinned statement is pinned here
as `GrownStrengtheningUnderBindingTarget`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation FX1Poly.Universe

/-- The closed `Type@0` code — binder type, subject, and domain of the counterexample. -/
def probeTypeZeroCode {scope : Nat} : RawTerm scope :=
  universeCodeCell LevelExpr.lzero UniverseFlag.standard

/-- The escaping reclassifier `(λ. Type@1) (var 0)` — β-convertible to `Type@1` but syntactically
mentioning the fresh variable, hence outside the weaken image from scope 0. -/
def probeEscapingReclassifier : RawTerm 1 :=
  appCell (lamCell (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard))
    (variableCell ⟨0, Nat.zero_lt_succ 0⟩)

/-- The counterexample typing: in `[Type@0]`, the WEAKENED subject `weaken Type@0` grown-types at
the escaping reclassifier via the `conv` arm. -/
theorem weakenedSubjectGrownTypedAtEscapingClassifier (profile : PolyProfile) :
    HasTypeDescPi profile
      ((TypingContext.empty (profile := profile)).cons probeTypeZeroCode)
      (RawTerm.weaken probeTypeZeroCode)
      probeEscapingReclassifier := by
  -- natural typing of the weakened subject at Type@1 (weaken of the closed cell is rfl)
  have baseTyped : HasTypeDescPi profile
      ((TypingContext.empty (profile := profile)).cons probeTypeZeroCode)
      (RawTerm.weaken probeTypeZeroCode)
      (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) :=
    HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation _ LevelExpr.lzero UniverseFlag.standard)
  -- the function part (λ. Type@1) : Π Type@0. Type@2 via piIntro
  have functionTyped : HasTypeDescPi profile
      ((TypingContext.empty (profile := profile)).cons probeTypeZeroCode)
      (lamCell (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard))
      (piTyCodeCell probeTypeZeroCode
        (universeCodeCell LevelExpr.lzero.lsucc.lsucc UniverseFlag.standard)) :=
    HasTypeDescPi.piIntro LevelExpr.lzero.lsucc LevelExpr.lzero.lsucc.lsucc.lsucc
      UniverseFlag.standard
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.universeFormation _ LevelExpr.lzero UniverseFlag.standard))
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.universeFormation _ LevelExpr.lzero.lsucc.lsucc UniverseFlag.standard))
      (HasTypeDescPi.ofFormation
        (HasTypeDesc.universeFormation _ LevelExpr.lzero.lsucc UniverseFlag.standard))
  -- the argument (var 0) : Type@0 (the lookup is the weakened binding, rfl-defeq to Type@0)
  have argumentTyped : HasTypeDescPi profile
      ((TypingContext.empty (profile := profile)).cons probeTypeZeroCode)
      (variableCell ⟨0, Nat.zero_lt_succ 0⟩)
      probeTypeZeroCode :=
    HasTypeDescPi.ofFormation (HasTypeDesc.var _ ⟨0, Nat.zero_lt_succ 0⟩)
  -- the escaping reclassifier types at Type@2 (subst0 of the closed codomain is rfl)
  have reclassifierTyped : HasTypeDescPi profile
      ((TypingContext.empty (profile := profile)).cons probeTypeZeroCode)
      probeEscapingReclassifier
      (universeCodeCell LevelExpr.lzero.lsucc.lsucc UniverseFlag.standard) :=
    HasTypeDescPi.piElim functionTyped argumentTyped
  -- the escaping reclassifier β-reduces to Type@1 (subst0 of the closed body is rfl)
  have betaStep : Step probeEscapingReclassifier
      (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) :=
    Step.beta
  exact HasTypeDescPi.conv LevelExpr.lzero.lsucc.lsucc UniverseFlag.standard
    baseTyped (Conv.fromStep betaStep).sym reclassifierTyped

/-- The escape: no scope-0 term weakens to the reclassifier — its argument child is `var 0`, and a
weakened argument is either a `Fin 0`-payload variable (uninhabited) or a non-variable head. -/
theorem escapingReclassifier_isOutsideWeakenImage (candidate : RawTerm 0) :
    RawTerm.weaken candidate ≠ probeEscapingReclassifier := by
  intro hEq
  cases candidate with
  | mkGen generator payload children =>
    by_cases hVar : generator = Generator.gen_var
    · subst hVar
      exact payload.elim0
    · rw [RawTerm.weaken_eq_rename, RawTerm.rename_mkGen_of_ne_var _ hVar] at hEq
      injection hEq with hScope hGenerator hPayload hChildren
      subst hGenerator
      have hChildrenEq := eq_of_heq hChildren
      cases children with
      | childCons functionChild restChildren =>
        cases restChildren with
        | childCons argumentChild nilChildren =>
          cases nilChildren with
          | childNil =>
            dsimp only [RawTermChildren.rename, foldChildren, iterateLiftRaw] at hChildrenEq
            injection hChildrenEq with hHeadScope hHeadShift hRestShifts hFunctionChild
              hTailChildren
            injection hTailChildren with hTailScope hTailShift hTailRestShifts hArgumentChild
              hNilChildren
            cases argumentChild with
            | mkGen argumentGenerator argumentPayload argumentChildren =>
              by_cases hArgVar : argumentGenerator = Generator.gen_var
              · subst hArgVar
                exact argumentPayload.elim0
              · rw [fold_mkGen_of_ne_var GenAlgebra.canonical _ hArgVar,
                  GenAlgebra.canonical_algebra_eq_mkGen] at hArgumentChild
                injection hArgumentChild with hArgScope hArgGenerator hArgPayload hArgChildren
                exact hArgVar hArgGenerator

/-- ★ The EXISTENTIAL form of grown strengthening is FALSE: a grown typing of a weakened subject
does NOT force the classifier into the weaken image.  The `conv` arm escapes via β-expansion. -/
theorem grownStrengtheningExistentialForm_isFalse (profile : PolyProfile) :
    ¬ (∀ (context : TypingContext profile 0) (bindingType subject : RawTerm 0)
        (classifier : RawTerm 1),
        HasTypeDescPi profile (context.cons bindingType) (RawTerm.weaken subject) classifier →
        ∃ classifierBase : RawTerm 0, classifier = RawTerm.weaken classifierBase) := by
  intro existentialClaim
  obtain ⟨classifierBase, hInImage⟩ :=
    existentialClaim TypingContext.empty probeTypeZeroCode probeTypeZeroCode
      probeEscapingReclassifier
      (weakenedSubjectGrownTypedAtEscapingClassifier profile)
  exact escapingReclassifier_isOutsideWeakenImage classifierBase hInImage.symm

/-- ★ The image-constrained target the refutation pins: BOTH subject and classifier weakened —
the exact converse of `weakenUnderBinding`, immune to the `conv`-escape above because the
classifier is pinned into the image by hypothesis.  STR-2..9 prove this via checker completeness ∘
rename-equivariance ∘ soundness (derivation induction alone cannot, per the refutation). -/
def GrownStrengtheningUnderBindingTarget : Prop :=
  ∀ {profile : PolyProfile} {scope : Nat} (context : TypingContext profile scope)
    (bindingType subject classifier : RawTerm scope),
    HasTypeDescPi profile (context.cons bindingType)
      (RawTerm.weaken subject) (RawTerm.weaken classifier) →
    HasTypeDescPi profile context subject classifier

#print axioms FX1Poly.Typed.weakenedSubjectGrownTypedAtEscapingClassifier
#print axioms FX1Poly.Typed.escapingReclassifier_isOutsideWeakenImage
#print axioms FX1Poly.Typed.grownStrengtheningExistentialForm_isFalse

end FX1Poly.Typed

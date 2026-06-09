import FX1Poly.Typed.GrownStrengthening
import FX1Poly.Typed.SimplyTypedTermInhabitationLevelFree

/-! # FX1Poly/Typed/GrownStrengtheningRefutation — the existential form of grown strengthening is FALSE

Grown strengthening (the inverse of `weakenUnderBinding`) has two candidate statements.  The
EXISTENTIAL form — "any grown typing of a weakened subject forces the classifier into the weaken
image" — would make the full theorem a one-induction corollary.  This file refutes it, and pins the
IMAGE-CONSTRAINED form (both subject and classifier weakened) as the campaign target.

The counterexample is the grown `conv` arm escaping through β-EXPANSION: in context `[Type@0]`, the
weakened subject `weaken Type@0` types naturally at `Type@1`, and `conv` reclassifies it at
`(λ. Type@1) (var 0)` — β-convertible to `Type@1`, itself typed at `Type@2` via `piElim ∘ piIntro`
with the fresh variable as argument.  That reclassifier syntactically mentions `var 0`, so no
scope-0 term weakens to it.

  * `escapingReclassifier` — the witness classifier `(λ. Type@1) (var 0)` at scope 1.
  * `weakenedSubjectGrownTypedAtEscapingClassifier` — the counterexample typing, for EVERY profile.
  * `escapingReclassifier_isOutsideWeakenImage` — no scope-0 term weakens to the witness: the
    argument child of a weakened application is either a `Fin 0`-payload variable (uninhabited) or
    a non-variable head, never `var 0`.
  * `grownStrengtheningExistentialForm_isFalse` — ★ the refutation.
  * `GrownStrengtheningUnderBindingTarget` — ★ the pinned target: BOTH subject and classifier
    weakened, the exact converse of `weakenUnderBinding`.  Immune to the `conv` escape (the
    classifier is pinned into the image by hypothesis), but derivation induction alone still cannot
    reach it — `conv`-arm INTERMEDIATE classifiers escape the image exactly as above, so the
    induction loses its own hypothesis shape.  The committed route is checker completeness ∘
    rename-equivariance ∘ soundness; the shipped variable leaf is
    `HasTypeDescPi.strengthenVariableUnderBinding`.

## Zero-axiom verification

The counterexample typing composes `ofFormation`/`universeFormation`/`var`/`piIntro`/`piElim`/
`conv` with `(Conv.fromStep Step.beta).sym` — all rfl-defeq on the closed cells (weaken, `subst0`,
and the cons-lookup all reduce definitionally).  The image escape is two levels of
`fold_mkGen_of_ne_var` drilling with `Fin 0` elimination at the variable arms.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation FX1Poly.Universe

/-- The escaping reclassifier `(λ. Type@1) (var 0)` — β-convertible to `Type@1` but syntactically
mentioning the fresh variable, hence outside the weaken image from scope 0. -/
def escapingReclassifier : RawTerm 1 :=
  appCell (lamCell (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard))
    (variableCell ⟨0, Nat.zero_lt_succ 0⟩)

/-- **The counterexample typing**: in `[Type@0]`, the WEAKENED subject `weaken Type@0` grown-types
at the escaping reclassifier, for every profile — natural typing at `Type@1`, then the grown `conv`
arm reclassifies across the β-expansion `(λ. Type@1) (var 0)`, whose own typing is
`piElim ∘ piIntro` with the fresh variable as argument. -/
theorem weakenedSubjectGrownTypedAtEscapingClassifier (profile : PolyProfile) :
    HasTypeDescPi profile
      ((TypingContext.empty (profile := profile)).cons (typeZeroCode 0))
      (RawTerm.weaken (typeZeroCode 0))
      escapingReclassifier := by
  -- natural typing of the weakened subject at Type@1 (weaken of the closed cell is rfl)
  have baseTyped : HasTypeDescPi profile
      ((TypingContext.empty (profile := profile)).cons (typeZeroCode 0))
      (RawTerm.weaken (typeZeroCode 0))
      (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) :=
    HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation _ LevelExpr.lzero UniverseFlag.standard)
  -- the function part (λ. Type@1) : Π Type@0. Type@2 via piIntro
  have functionTyped : HasTypeDescPi profile
      ((TypingContext.empty (profile := profile)).cons (typeZeroCode 0))
      (lamCell (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard))
      (piTyCodeCell (typeZeroCode 1)
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
      ((TypingContext.empty (profile := profile)).cons (typeZeroCode 0))
      (variableCell ⟨0, Nat.zero_lt_succ 0⟩)
      (typeZeroCode 1) :=
    HasTypeDescPi.ofFormation (HasTypeDesc.var _ ⟨0, Nat.zero_lt_succ 0⟩)
  -- the escaping reclassifier types at Type@2 (subst0 of the closed codomain is rfl)
  have reclassifierTyped : HasTypeDescPi profile
      ((TypingContext.empty (profile := profile)).cons (typeZeroCode 0))
      escapingReclassifier
      (universeCodeCell LevelExpr.lzero.lsucc.lsucc UniverseFlag.standard) :=
    HasTypeDescPi.piElim functionTyped argumentTyped
  -- the escaping reclassifier β-reduces to Type@1 (subst0 of the closed body is rfl)
  have betaStep : Step escapingReclassifier
      (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard) :=
    Step.beta
  exact HasTypeDescPi.conv LevelExpr.lzero.lsucc.lsucc UniverseFlag.standard
    baseTyped (Conv.fromStep betaStep).sym reclassifierTyped

/-- **The escape**: no scope-0 term weakens to the reclassifier — drilling two levels through the
fold, the application's argument child is either a `Fin 0`-payload variable (uninhabited) or a
non-variable head, never `var 0`. -/
theorem escapingReclassifier_isOutsideWeakenImage (candidate : RawTerm 0) :
    RawTerm.weaken candidate ≠ escapingReclassifier := by
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

/-- ★ **The EXISTENTIAL form of grown strengthening is FALSE**: a grown typing of a weakened
subject does NOT force its classifier into the weaken image — the `conv` arm escapes via
β-expansion over the fresh variable. -/
theorem grownStrengtheningExistentialForm_isFalse (profile : PolyProfile) :
    ¬ (∀ (context : TypingContext profile 0) (bindingType subject : RawTerm 0)
        (classifier : RawTerm 1),
        HasTypeDescPi profile (context.cons bindingType) (RawTerm.weaken subject) classifier →
        ∃ classifierBase : RawTerm 0, classifier = RawTerm.weaken classifierBase) := by
  intro existentialClaim
  obtain ⟨classifierBase, hInImage⟩ :=
    existentialClaim TypingContext.empty (typeZeroCode 0) (typeZeroCode 0)
      escapingReclassifier
      (weakenedSubjectGrownTypedAtEscapingClassifier profile)
  exact escapingReclassifier_isOutsideWeakenImage classifierBase hInImage.symm

/-- ★ **The pinned image-constrained target**: BOTH subject and classifier weakened — the exact
converse of `weakenUnderBinding`, immune to the `conv` escape because the classifier is pinned
into the image by hypothesis.  Derivation induction alone still cannot reach it (intermediate
classifiers escape per the refutation above); the campaign proves it via checker completeness ∘
rename-equivariance ∘ soundness.  The shipped base case is
`HasTypeDescPi.strengthenVariableUnderBinding`. -/
def GrownStrengtheningUnderBindingTarget : Prop :=
  ∀ {profile : PolyProfile} {scope : Nat} (context : TypingContext profile scope)
    (bindingType subject classifier : RawTerm scope),
    HasTypeDescPi profile (context.cons bindingType)
      (RawTerm.weaken subject) (RawTerm.weaken classifier) →
    HasTypeDescPi profile context subject classifier

end FX1Poly.Typed

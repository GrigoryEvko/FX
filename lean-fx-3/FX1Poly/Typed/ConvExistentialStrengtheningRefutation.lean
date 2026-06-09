import FX1Poly.Typed.GrownCheckSoundnessRefutation
import FX1Poly.Typed.ReduceSmokeCorpus
import FX1Poly.Core.ConvNormalForm

/-! # FX1Poly/Typed/ConvExistentialStrengtheningRefutation — the Conv-existential is ALSO false unpinned

The strengthening campaign's THIRD refutation, completing the design-space fence:

  * `GrownStrengtheningRefutation` (STR-1) — the SYNTACTIC-image existential is false (the `conv`
    arm escapes via β-expansion, but `Conv` to a weakening survives there).
  * `GrownCheckSoundnessRefutation` (STR-5) — the raw checking relation is unsound (typehood must
    enter the pipeline).
  * THIS FILE — even the CONV-existential strengthening is false WITHOUT a pinned classifier: a
    grown typing of a weakened subject does not force its classifier into the weaken image even up
    to `Conv`.

The witness is Curry-style λ-typing non-uniqueness at its purest: the weakened identity λ is
grown-typed at `Π (var 0). (var 1)` in `[Type@0]` — the binder's type IS the fresh variable (a
perfectly valid domain there, since `var 0`'s lookup is `Type@0`), every `piIntro` side condition
is rfl-defeq, and the classifier is a NORMAL form whose domain mentions the fresh variable
irreducibly:

  * `variableDomainPi` / `variableDomainPi_isStepNormalForm` — the classifier and its normality
    (`by decide`).
  * `weakenedIdentityTypedAtVariableDomainPi` — the typing (pure `piIntro`, three `var` leaves).
  * `variableDomainPi_notConvWeakenImage` — the escape up to `Conv`: normality collapses the join
    (`StepStar.eq_of_noStep`), `StepStar.reflectRename` pulls the weakening's chain back, and the
    STR-1 drilling shows the Π-code's `var 0` domain cannot be a weakening's image.
  * `convExistentialStrengthening_isFalse` — ★ the refutation.

## Consequence (the STR-5b route decision)

The strengthening reflection's conclusion `∃ S₀, Conv S (weaken S₀) ∧ …` is UNPROVABLE as a
standalone ∀-statement over all classifiers — the image-pinned-classifier premise
(`∃ S_img, Conv S (weaken S_img)`) is MANDATORY, not an artifact of any proof strategy.  Together
with the Ω-unsoundness this pins the surviving route: image-pinned, NF-annotated ENGINE-derivation
reflection (campaign log, firing 247d900a), whose remaining open core is pinning the function's Π
at `piElim`.  The η-SR consumer (#850) supplies its root pinning partially (the `(var 0)` argument
pins the domain via `inversionVariable`); its codomain pinning threads the same open core. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- The variable-domain Π-code `Π (var 0). (var 1)` at scope 1 — a NORMAL classifier whose domain is
the fresh variable itself. -/
def variableDomainPi : RawTerm 1 :=
  piTyCodeCell (variableCell ⟨0, Nat.succ_pos 0⟩)
    (variableCell ⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩)

/-- `Π (var 0). (var 1)` is a structural normal form. -/
theorem variableDomainPi_isStepNormalForm :
    RawTerm.isStepNormalForm variableDomainPi := by decide

/-- The weakened identity λ is grown-typed at `Π (var 0). (var 1)` in `[Type@0]`: the binder's type
`var 0` IS a type there (its lookup is `Type@0`), the codomain `var 1` likewise, and the body's
natural type is exactly the codomain — a pure `piIntro` whose every side condition is rfl-defeq. -/
theorem weakenedIdentityTypedAtVariableDomainPi (profile : PolyProfile) :
    HasTypeDescPi profile
      ((TypingContext.empty (profile := profile)).cons (typeZeroCode 0))
      (RawTerm.weaken identityLambda)
      variableDomainPi :=
  HasTypeDescPi.piIntro LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard
    (HasTypeDescPi.ofFormation (HasTypeDesc.var _ ⟨0, Nat.succ_pos 0⟩))
    (HasTypeDescPi.ofFormation (HasTypeDesc.var _ ⟨1, Nat.succ_lt_succ (Nat.succ_pos 0)⟩))
    (HasTypeDescPi.ofFormation (HasTypeDesc.var _ ⟨0, Nat.succ_pos 1⟩))

/-- The escape, now up to CONV: `Π (var 0). (var 1)` is not convertible to ANY weakening.  It is
normal, so a `Conv` join collapses to a reduction chain out of the weakening reaching it exactly;
`StepStar.reflectRename` pulls that chain back through the weakening, forcing the Π-code itself
into the weaken image — but its domain child is `var 0`, which no scope-0 term weakens to. -/
theorem variableDomainPi_notConvWeakenImage (classifierBase : RawTerm 0) :
    ¬ Conv variableDomainPi (RawTerm.weaken classifierBase) := by
  intro convToWeaken
  obtain ⟨commonReduct, piChain, weakenChain⟩ := convToWeaken
  have commonIsPi : commonReduct = variableDomainPi :=
    StepStar.eq_of_noStep
      (fun reduct step =>
        RawTerm.isStepNormalForm_blocks_step variableDomainPi_isStepNormalForm reduct step)
      piChain
  rw [commonIsPi] at weakenChain
  obtain ⟨reflected, _sourceChain, imageEq⟩ :=
    StepStar.reflectRename RawRenaming.weaken
      (show StepStar (RawTerm.rename RawRenaming.weaken classifierBase) variableDomainPi
        from weakenChain)
  cases reflected with
  | mkGen generator payload children =>
    by_cases hVar : generator = Generator.gen_var
    · subst hVar
      exact payload.elim0
    · rw [RawTerm.rename_mkGen_of_ne_var _ hVar] at imageEq
      injection imageEq with hScope hGenerator hPayload hChildren
      subst hGenerator
      have hChildrenEq := eq_of_heq hChildren
      cases children with
      | childCons domainChild restChildren =>
        cases restChildren with
        | childCons codomainChild nilChildren =>
          cases nilChildren with
          | childNil =>
            dsimp only [RawTermChildren.rename, foldChildren, iterateLiftRaw] at hChildrenEq
            injection hChildrenEq with hHeadScope hHeadShift hRestShifts hDomainChild
              hTailChildren
            cases domainChild with
            | mkGen domainGenerator domainPayload domainChildren =>
              by_cases hDomainVar : domainGenerator = Generator.gen_var
              · subst hDomainVar
                exact domainPayload.elim0
              · rw [fold_mkGen_of_ne_var GenAlgebra.canonical _ hDomainVar,
                  GenAlgebra.canonical_algebra_eq_mkGen] at hDomainChild
                injection hDomainChild with hDomScope hDomGenerator hDomPayload hDomChildren
                exact hDomainVar hDomGenerator

/-- ★ **The CONV-existential strengthening is FALSE without a pinned classifier** — sharpening
STR-1's syntactic-image refutation: a grown typing of a weakened subject does not even force its
classifier into the weaken image UP TO CONV.  The strengthening reflection MUST carry the
image-pinned-classifier premise. -/
theorem convExistentialStrengthening_isFalse (profile : PolyProfile) :
    ¬ (∀ (bindingType subject : RawTerm 0) (classifier : RawTerm 1),
        HasTypeDescPi profile
          ((TypingContext.empty (profile := profile)).cons bindingType)
          (RawTerm.weaken subject) classifier →
        ∃ classifierBase : RawTerm 0,
          Conv classifier (RawTerm.weaken classifierBase)) := by
  intro convExistentialClaim
  obtain ⟨classifierBase, convToWeaken⟩ :=
    convExistentialClaim (typeZeroCode 0) identityLambda variableDomainPi
      (weakenedIdentityTypedAtVariableDomainPi profile)
  exact variableDomainPi_notConvWeakenImage classifierBase convToWeaken

end FX1Poly.Typed

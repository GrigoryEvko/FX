import FX1Poly.Typed.GrownCheckSoundnessRefutation
import FX1Poly.Typed.ReduceSmokeCorpus
import FX1Poly.Core.ConvNormalForm

/-! # FX1Poly/Typed/ConvExistentialStrengtheningRefutation — RETIRED refutation (T2 flipped it)

PRE-T2 this file was the strengthening campaign's THIRD refutation: under Curry-style λ the
weakened identity could be grown-typed at the variable-domain Π `Π (var 0). (var 1)` (the λ's
domain was invisible, so the classifier floated), and that classifier is not `Conv` to any
weakening — refuting the unpinned Conv-existential strengthening.

UNDER T2 (Church-style two-child λ) THE REFUTATION IS DEAD, and honestly so: `piIntro` pins the
λ's domain ANNOTATION to the Π domain (`HasTypeDescPi.invertLam`), so the only inhabitant of a
`var 0`-domain Π is the `var 0`-ANNOTATED identity `lamCell (var 0) (var 0)` — which is NOT a
weaken-image of any scope-0 term (weakening shifts every variable away from slot 0).  The old
witness `weaken identityLambda` (a `unitCell`-annotated λ) is untypeable here, and no replacement
witness exists: the float the refutation exploited is structurally impossible.  The refuted claim
(the Conv-existential strengthening) is consequently EXPECTED TO BE TRUE under T2; its positive
proof is the pinned-reflection λ-reduct discharge (the campaign's open core).

What SURVIVES, still true and load-bearing:

  * `variableDomainPi` / `variableDomainPi_isStepNormalForm` — the variable-domain classifier and
    its normality (`by decide`).
  * `weakenedIdentityTypedAtVariableDomainPi` — the typing witness, RESTATED for T2: the
    `var 0`-annotated identity (the name records its pre-T2 ancestry; the audited claim is the
    restated one).
  * `variableDomainPi_notConvWeakenImage` — the classifier-side escape is STILL a fact: the
    variable-domain Π is not `Conv` to any weakening.  Under T2 this no longer refutes
    strengthening (no weaken-image subject inhabits it); instead it documents exactly WHY the
    annotation pin is load-bearing.

RETIRED (user-approved deletion, 2026-06-10): `convExistentialStrengthening_isFalse` and its
consumer `pinnedReflectionLamClassifierResidual_isFalse` — the refuted statements are plausibly
TRUE under T2; keeping `_isFalse` theorems for them would be dishonest. -/

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

/-- The variable-domain identity λ is grown-typed at `Π (var 0). (var 1)` in `[Type@0]`: the
binder's type `var 0` IS a type there (its lookup is `Type@0`), the codomain `var 1` likewise, and
the body's natural type is exactly the codomain — a pure `piIntro` whose every side condition is
rfl-defeq.

T2 RESTATEMENT: a Church-style `piIntro` pins the λ's domain ANNOTATION to the Π domain
(`HasTypeDescPi.invertLam`), so the inhabitant of a `var 0`-domain Π must itself be the
`var 0`-ANNOTATED identity `lamCell (var 0) (var 0)` — NOT the pre-T2 `weaken identityLambda`
(whose domain is the smoke-corpus `unitCell`), which is untypeable here.  Crucially,
`lamCell (var 0) (var 0)` is NOT a weaken-image of any scope-0 term, so this typing no longer
yields a strengthening counterexample — see the file header. -/
theorem weakenedIdentityTypedAtVariableDomainPi (profile : PolyProfile) :
    HasTypeDescPi profile
      ((TypingContext.empty (profile := profile)).cons (typeZeroCode 0))
      (lamCell (variableCell (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1))
        (variableCell (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2)))
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

/- RETIRED: `convExistentialStrengthening_isFalse` lived here pre-T2.  Its witness fed
`weaken identityLambda` typed at `variableDomainPi` to the Conv-existential strengthening claim;
under T2 that typing is impossible (the annotation pin) and no weaken-image subject inhabits a
variable-domain Π, so the refutation has no witness and the refuted claim is expected TRUE.
Deleted with user approval 2026-06-10; the positive successor is the pinned-reflection λ-reduct
discharge. -/

end FX1Poly.Typed

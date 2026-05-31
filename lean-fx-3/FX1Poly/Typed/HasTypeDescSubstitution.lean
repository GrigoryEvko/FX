import FX1Poly.Typed.HasTypeDesc
import FX1Poly.Typed.HasTypeDescWeakening
import FX1Poly.Typed.HasTypeSubstitution
import FX1Poly.Core.RawTermSubst0
import FX1Poly.Core.RawTermSubst0Commute
import FX1Poly.Core.ConvSubstRename

/-! # FX1Poly/Typed/HasTypeDescSubstitution — INTRINSIC substitution (P6, the β-engine)
    for the description engine.

polycell.md §11.8.5 P6 ("Substitution / weakening = whiskering, the β-engine"): typing is
preserved along a context morphism.  This file ships the SUBSTITUTION half — `HasTypeDesc`
is preserved along ANY substitution whose substituents are target-typed at the substituted
source-binding types — and the single-substitution (`subst0`) corollary the β-rule cites.

## The keystone β-engine, INTRINSIC

Sibling to intrinsic weakening (`HasTypeDescWeakening`): weakening is the RENAMING action
on a `HasTypeDesc` derivation, substitution the full SUBSTITUTION action.  Same clean mutual
shape (`HasTypeDesc.substRespectingContext ⋈ DescTelescope.substRespectingTelescope`) — NO
second-derivation inversion, so cross-calls sit on PRISTINE `match`-bound subterms and
Lean's structural recursion lands it without `termination_by` (the genFormation companion
cross-call HOISTED before `by_cases`).  Proved BY INDUCTION on `HasTypeDesc`, NOT routed
through the `⟺` maps.  `Conv.subst` (#370) rides the `conv` arm; no `Conv.trans`, so the
β-engine is UNBLOCKED ahead of raw confluence.

The decouple COMPOUNDS: the telescope companion's `cons` successor case reuses the INTRINSIC
`HasTypeDesc.weakenUnderBinding` (last fire) to weaken the substituent across the binder —
intrinsic substitution standing on intrinsic weakening, no `HasType` in either.

## The telescope companion's lifted substitution-condition

The companion's side condition is a TYPING (substituents are terms that must be typed),
stated at the telescope's `currentDepth` via `iterateLiftRaw substitution currentDepth`.
The `cons` arm fires the head recursion with that depth-`cd` substitution (condition passes
verbatim) and recurses on the tail at `cd+1` with the LIFTED condition — split `0`/successor
(fresh `var` at `0`, weakened substituent at `k+1` via `HasTypeDesc.weakenUnderBinding`),
the N-binder generalization of the bespoke `HasType.substRespectingContext` single-binder
`piFormation` codomain handling.  `iterateLiftRaw σ (cd+1) ≡ RawTermSubst.lift (iterateLiftRaw
σ cd)` (`iterateLiftRaw_succ_unfolds`; `liftForRaw := RawTermSubst.lift` definitionally), so a
`show` restates it in `lift` form and `subst_lift_weaken_commute` fires.

## Zero-axiom

Mutual structural recursion + the reused bespoke `subst_{variableCell,universeCodeCell,
lift_weaken_commute,singleton_renameWeaken_cancel}` bricks + `Conv.subst` (#370) +
`HasTypeDesc.weakenUnderBinding` + the nested-`if` generator pin (propext-free via
`DecidableEq Generator`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

mutual

/-- INTRINSIC general substitution (P6): `HasTypeDesc` is preserved along any substitution
whose substituents are target-typed at the substituted source-binding types.  Term-mode
recursive `match` mutual with `DescTelescope.substRespectingTelescope`; the cross-calls sit
on pristine `match`-bound subterms (`typedPremise`, `premises`), the genFormation companion
cross-call hoisted before the `by_cases` — so structural recursion lands it (no
`termination_by`).  Proved NOT through the `⟺` maps. -/
theorem HasTypeDesc.substRespectingContext {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDesc profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      (∀ index : Fin sourceScope,
        HasTypeDesc profile targetContext (substitution index)
          (RawTerm.subst substitution (sourceContext.lookup index))) →
      HasTypeDesc profile targetContext
        (RawTerm.subst substitution subject)
        (RawTerm.subst substitution classifier) :=
  match derivation with
  | .var _sourceContext index => fun _targetContext substitution substitutionTyped => by
      rw [subst_variableCell]
      exact substitutionTyped index
  | .conv levelExpr flag typedPremise converts reclassifierTyped =>
      fun targetContext substitution substitutionTyped => by
        have premiseTyped :=
          HasTypeDesc.substRespectingContext typedPremise targetContext substitution
            substitutionTyped
        have reclassifierTypedSubst :=
          HasTypeDesc.substRespectingContext reclassifierTyped targetContext substitution
            substitutionTyped
        rw [subst_universeCodeCell] at reclassifierTypedSubst
        exact HasTypeDesc.conv levelExpr flag premiseTyped
          (Conv.subst substitution converts) reclassifierTypedSubst
  | .universeFormation _sourceContext levelExpr flag =>
      fun targetContext substitution _substitutionTyped => by
        rw [subst_universeCodeCell, subst_universeCodeCell]
        exact HasTypeDesc.universeFormation targetContext levelExpr flag
  | .genFormation _sourceContext generator payload children levels flag rule
      isFormation premises => fun targetContext substitution substitutionTyped => by
      -- Hoist the companion cross-call on PRISTINE `premises` BEFORE the `by_cases`, so the
      -- structural-recursion checker recognises it as a sub-derivation (the `toHasType`
      -- discipline).  The substituted premises do not depend on the generator.
      have substPremises :=
        DescTelescope.substRespectingTelescope premises targetContext substitution
          substitutionTyped
      by_cases hPi : generator = .gen_piTyCode
      · subst hPi
        obtain rfl : rule = { outputType := universeFormerOutput } :=
          Option.some.inj isFormation.symm
        show HasTypeDesc profile targetContext
          (RawTerm.subst substitution (RawTerm.mkGen .gen_piTyCode payload children))
          (RawTerm.subst substitution (universeCodeCell (lmaxAll levels) flag))
        rw [subst_universeCodeCell]
        exact HasTypeDesc.genFormation targetContext .gen_piTyCode payload
          (RawTermChildren.subst substitution children) levels flag
          { outputType := universeFormerOutput } typingRuleDescOf_piTyCode substPremises
      · by_cases hSigma : generator = .gen_sigmaTyCode
        · subst hSigma
          obtain rfl : rule = { outputType := universeFormerOutput } :=
            Option.some.inj isFormation.symm
          show HasTypeDesc profile targetContext
            (RawTerm.subst substitution (RawTerm.mkGen .gen_sigmaTyCode payload children))
            (RawTerm.subst substitution (universeCodeCell (lmaxAll levels) flag))
          rw [subst_universeCodeCell]
          exact HasTypeDesc.genFormation targetContext .gen_sigmaTyCode payload
            (RawTermChildren.subst substitution children) levels flag
            { outputType := universeFormerOutput } typingRuleDescOf_sigmaTyCode substPremises
        · exfalso
          unfold typingRuleDescOf at isFormation
          rw [if_neg hPi, if_neg hSigma] at isFormation
          contradiction

/-- Companion: substitute the premise spine.  Structural recursion on the telescope; the
`cons` arm fires the head recursion through `HasTypeDesc.substRespectingContext` (the
companion's depth-`cd` substitution-condition passes verbatim) and recurses on the tail at
`cd+1` with the LIFTED substitution-condition (`0` → fresh `var`; `k+1` → the substituent
weakened across the binder via the INTRINSIC `HasTypeDesc.weakenUnderBinding`). -/
theorem DescTelescope.substRespectingTelescope {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile sourceContext levels flag children) :
    ∀ {targetBaseScope : Nat}
      (targetContext : TypingContext profile (targetBaseScope + currentDepth))
      (substitution : RawTermSubst baseScope targetBaseScope),
      (∀ index : Fin (baseScope + currentDepth),
        HasTypeDesc profile targetContext
          (iterateLiftRaw substitution currentDepth index)
          (RawTerm.subst (iterateLiftRaw substitution currentDepth)
            (sourceContext.lookup index))) →
      DescTelescope profile targetContext levels flag
        (RawTermChildren.subst substitution children) :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _substitution _substitutionTyped =>
      DescTelescope.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext substitution substitutionTyped => by
        have substHeadTyped :
            HasTypeDesc profile targetContext
              (RawTerm.subst (iterateLiftRaw substitution currentDepth) head)
              (universeCodeCell headLevel flag) := by
          have headSubst :=
            HasTypeDesc.substRespectingContext headTyped targetContext
              (iterateLiftRaw substitution currentDepth) substitutionTyped
          rwa [subst_universeCodeCell] at headSubst
        refine DescTelescope.cons targetContext
          (RawTerm.subst (iterateLiftRaw substitution currentDepth) head) headLevel
          restLevels flag (RawTermChildren.subst substitution rest) substHeadTyped ?_
        refine DescTelescope.substRespectingTelescope restTyped
          (targetContext.cons
            (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
          substitution ?_
        intro index
        obtain ⟨indexValue, indexBound⟩ := index
        cases indexValue with
        | zero =>
            show HasTypeDesc profile
              (targetContext.cons
                (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
              (RawTermSubst.lift (iterateLiftRaw substitution currentDepth) ⟨0, indexBound⟩)
              (RawTerm.subst (RawTermSubst.lift (iterateLiftRaw substitution currentDepth))
                ((_sourceContext.cons head).lookup ⟨0, indexBound⟩))
            rw [TypingContext.lookup_cons_zero, subst_lift_weaken_commute]
            exact HasTypeDesc.var
              (targetContext.cons
                (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
              ⟨0, Nat.succ_pos _⟩
        | succ k =>
            show HasTypeDesc profile
              (targetContext.cons
                (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
              (RawTermSubst.lift (iterateLiftRaw substitution currentDepth)
                ⟨k + 1, indexBound⟩)
              (RawTerm.subst (RawTermSubst.lift (iterateLiftRaw substitution currentDepth))
                ((_sourceContext.cons head).lookup ⟨k + 1, indexBound⟩))
            rw [TypingContext.lookup_cons_succ, subst_lift_weaken_commute]
            exact (substitutionTyped ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding
              (RawTerm.subst (iterateLiftRaw substitution currentDepth) head)

end

/-- Typed single-substitution (the β-engine) for the description engine: substituting a
well-typed `argument` for de Bruijn 0 preserves `HasTypeDesc`.  The corollary the β-rule
`app(lam(b), a) ↝ b[a]` cites — `HasTypeDesc (Γ.cons argType) subject classifier` and
`HasTypeDesc Γ argument argType` give `HasTypeDesc Γ (subject[argument]) (classifier[argument])`.
The side condition splits `Fin` `0`/successor: position `0` returns the argument
(`argumentTyped`, after the singleton cancels the weakening), position `k+1` a shifted
variable (`var`).  INTRINSIC — no route through `HasType`. -/
theorem HasTypeDesc.substituteUnderBinding {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {argType : RawTerm scope}
    {subject classifier : RawTerm (scope + 1)} (argument : RawTerm scope)
    (derivation : HasTypeDesc profile (context.cons argType) subject classifier)
    (argumentTyped : HasTypeDesc profile context argument argType) :
    HasTypeDesc profile context
      (RawTerm.subst0 subject argument)
      (RawTerm.subst0 classifier argument) := by
  refine derivation.substRespectingContext context
    (RawTermSubst.singleton argument) ?_
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show HasTypeDesc profile context argument
        (RawTerm.subst (RawTermSubst.singleton argument)
          (RawTerm.rename RawRenaming.weaken argType))
      rw [subst_singleton_renameWeaken_cancel]
      exact argumentTyped
  | succ k =>
      show HasTypeDesc profile context
          (variableCell ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)
        (RawTerm.subst (RawTermSubst.singleton argument)
          (RawTerm.rename RawRenaming.weaken
            (context.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩)))
      rw [subst_singleton_renameWeaken_cancel]
      exact HasTypeDesc.var context ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩

end FX1Poly.Typed

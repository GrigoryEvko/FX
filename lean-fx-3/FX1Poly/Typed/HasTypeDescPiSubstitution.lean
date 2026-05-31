import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Typed.HasTypeDescSubstitution

/-! # FX1Poly/Typed/HasTypeDescPiSubstitution — the GROWN engine's term-substitution fibration leg
    (the β-engine "whiskering"), dual to `HasTypeDescPiWeakening`'s renaming (cartesian-lift) leg.

polycell.md §11.8.5 P6: typing is preserved along a context morphism.  This file carries the
SUBSTITUTION half for the grown engine `HasTypeDescPi` — preserved along ANY substitution whose
substituents are grown-typed at the substituted source bindings — plus the formation-leg helper it
rests on.  Renaming preserves formation-ness (it introduces no eliminations); SUBSTITUTION does NOT
(a variable may be replaced by an application, a former's component by a non-formation term), so the
result lands in `HasTypeDescPi`, never `HasTypeDesc`.

## Contents

* `HasTypeDesc.substIntoGrown ⋈ DescTelescope.substIntoGrown` — substitute a FORMATION derivation
  under a grown substitution, producing a GROWN derivation.  The `ofFormation` leg the full grown
  substitution rests on: a formation subject substituted by a grown substitution is in general no
  longer a formation term, so it must retype in the grown engine.  Mutual structural recursion on
  the FORMATION derivation; the genFormation case rebuilds through the GENERIC `genFormationPi`
  (substitute the spine, pin the universe-former OUTPUT, re-fire), so no per-former child projection
  — a per-former arm would force a partial-match on the substituted child telescope (the
  indexed-inductive propext trap).

* `subst_lamCell`, `subst_appCell` — rfl bricks: substitution distributes over the grown term-formers
  (body under one lift; both app children directly).  The substitution-side companions to
  `rename_{lamCell,appCell}`.

* `substContextCondition_cons` — the one-binder lift of a grown substitution-condition (the lone
  non-telescope binder-crosser the `piIntro` arm needs).

* `HasTypeDescPi.substRespectingContext ⋈ DescTelescopePi.substRespectingTelescope` — the FULL grown
  substitution leg: `HasTypeDescPi` preserved along any grown-typed substitution.  Mirrors
  `renameRespectingContext`'s five arms — except `ofFormation` routes through `substIntoGrown`
  (returning a grown derivation), not a re-wrap.  `conv` carries `Conv.subst`; `piIntro` recurses the
  body under the lifted condition and reassembles via `subst_{lamCell,piTyCodeCell}`; `piElim`
  reshapes the dependent output by `RawTerm.subst0_subst_commute` and reassembles via `subst_appCell`;
  `genFormationPi` substitutes the spine through the companion and re-fires generically.

## Why two mutual blocks, not one

Each block stays WITHIN one inductive family — `substIntoGrown` over `HasTypeDesc`/`DescTelescope`,
`substRespectingContext` over `HasTypeDescPi`/`DescTelescopePi` — with the cross-engine hop
(`ofFormation` → `substIntoGrown`) routed through the COMPLETED `substIntoGrown` on the formation
subterm, never a live recursion spanning both families.  That sidesteps the v4.29.1
cross-inductive-boundary termination gap.  Each block's other cross-calls sit on pristine
`match`-bound subterms (the genFormation/genFormationPi companion cross-call hoisted before its
`by_cases`), so Lean's structural recursion lands both without `termination_by`.

## Zero-axiom

Mutual structural recursion + the reused `subst_{variableCell,universeCodeCell,piTyCodeCell,
lift_weaken_commute}` bricks + the rfl `subst_{lamCell,appCell}` + `RawTerm.subst0_subst_commute` +
`Conv.subst` + `HasTypeDescPi.weakenUnderBinding` + the generic `genFormationPi` rebuild + the
nested-`if` generator pin (propext-free via `DecidableEq Generator`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

mutual

/-- Substitute a FORMATION derivation under a GROWN substitution, producing a GROWN derivation:
`HasTypeDesc` is carried along any substitution whose substituents are `HasTypeDescPi`-typed at the
substituted source-binding types, with the result in `HasTypeDescPi`.  The `ofFormation` leg of the
grown β-engine. -/
theorem HasTypeDesc.substIntoGrown {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDesc profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      (∀ index : Fin sourceScope,
        HasTypeDescPi profile targetContext (substitution index)
          (RawTerm.subst substitution (sourceContext.lookup index))) →
      HasTypeDescPi profile targetContext
        (RawTerm.subst substitution subject)
        (RawTerm.subst substitution classifier) :=
  match derivation with
  | .var _sourceContext index => fun _targetContext substitution substitutionTyped => by
      rw [subst_variableCell]
      exact substitutionTyped index
  | .conv levelExpr flag typedPremise converts reclassifierTyped =>
      fun targetContext substitution substitutionTyped => by
        have premiseTyped :=
          HasTypeDesc.substIntoGrown typedPremise targetContext substitution
            substitutionTyped
        have reclassifierTypedSubst :=
          HasTypeDesc.substIntoGrown reclassifierTyped targetContext substitution
            substitutionTyped
        rw [subst_universeCodeCell] at reclassifierTypedSubst
        exact HasTypeDescPi.conv levelExpr flag premiseTyped
          (Conv.subst substitution converts) reclassifierTypedSubst
  | .universeFormation _sourceContext levelExpr flag =>
      fun targetContext substitution _substitutionTyped => by
        rw [subst_universeCodeCell, subst_universeCodeCell]
        exact HasTypeDescPi.ofFormation
          (HasTypeDesc.universeFormation targetContext levelExpr flag)
  | .genFormation _sourceContext generator payload children levels flag rule
      isFormation premises => fun targetContext substitution substitutionTyped => by
      have substPremises :=
        DescTelescope.substIntoGrown premises targetContext substitution
          substitutionTyped
      by_cases hPi : generator = .gen_piTyCode
      · subst hPi
        obtain rfl : rule = { outputType := universeFormerOutput } :=
          Option.some.inj isFormation.symm
        show HasTypeDescPi profile targetContext
          (RawTerm.subst substitution (RawTerm.mkGen .gen_piTyCode payload children))
          (RawTerm.subst substitution (universeCodeCell (lmaxAll levels) flag))
        rw [subst_universeCodeCell]
        exact HasTypeDescPi.genFormationPi targetContext .gen_piTyCode payload
          (RawTermChildren.subst substitution children) levels flag
          { outputType := universeFormerOutput } typingRuleDescOf_piTyCode substPremises
      · by_cases hSigma : generator = .gen_sigmaTyCode
        · subst hSigma
          obtain rfl : rule = { outputType := universeFormerOutput } :=
            Option.some.inj isFormation.symm
          show HasTypeDescPi profile targetContext
            (RawTerm.subst substitution (RawTerm.mkGen .gen_sigmaTyCode payload children))
            (RawTerm.subst substitution (universeCodeCell (lmaxAll levels) flag))
          rw [subst_universeCodeCell]
          exact HasTypeDescPi.genFormationPi targetContext .gen_sigmaTyCode payload
            (RawTermChildren.subst substitution children) levels flag
            { outputType := universeFormerOutput } typingRuleDescOf_sigmaTyCode substPremises
        · exfalso
          unfold typingRuleDescOf at isFormation
          rw [if_neg hPi, if_neg hSigma] at isFormation
          contradiction

/-- Companion: substitute a formation premise spine under a grown substitution, producing a grown
`DescTelescopePi` spine.  Head via `HasTypeDesc.substIntoGrown`; tail under the binder with the
lifted grown condition (`0` → the fresh `var` via `ofFormation`; `k+1` → the grown substituent
weakened via `HasTypeDescPi.weakenUnderBinding`). -/
theorem DescTelescope.substIntoGrown {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile sourceContext levels flag children) :
    ∀ {targetBaseScope : Nat}
      (targetContext : TypingContext profile (targetBaseScope + currentDepth))
      (substitution : RawTermSubst baseScope targetBaseScope),
      (∀ index : Fin (baseScope + currentDepth),
        HasTypeDescPi profile targetContext
          (iterateLiftRaw substitution currentDepth index)
          (RawTerm.subst (iterateLiftRaw substitution currentDepth)
            (sourceContext.lookup index))) →
      DescTelescopePi profile targetContext levels flag
        (RawTermChildren.subst substitution children) :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _substitution _substitutionTyped =>
      DescTelescopePi.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext substitution substitutionTyped => by
        have substHeadTyped :
            HasTypeDescPi profile targetContext
              (RawTerm.subst (iterateLiftRaw substitution currentDepth) head)
              (universeCodeCell headLevel flag) := by
          have headSubst :=
            HasTypeDesc.substIntoGrown headTyped targetContext
              (iterateLiftRaw substitution currentDepth) substitutionTyped
          rwa [subst_universeCodeCell] at headSubst
        refine DescTelescopePi.cons targetContext
          (RawTerm.subst (iterateLiftRaw substitution currentDepth) head) headLevel
          restLevels flag (RawTermChildren.subst substitution rest) substHeadTyped ?_
        refine DescTelescope.substIntoGrown restTyped
          (targetContext.cons
            (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
          substitution ?_
        intro index
        obtain ⟨indexValue, indexBound⟩ := index
        cases indexValue with
        | zero =>
            show HasTypeDescPi profile
              (targetContext.cons
                (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
              (RawTermSubst.lift (iterateLiftRaw substitution currentDepth) ⟨0, indexBound⟩)
              (RawTerm.subst (RawTermSubst.lift (iterateLiftRaw substitution currentDepth))
                ((_sourceContext.cons head).lookup ⟨0, indexBound⟩))
            rw [TypingContext.lookup_cons_zero, subst_lift_weaken_commute]
            exact HasTypeDescPi.ofFormation
              (HasTypeDesc.var
                (targetContext.cons
                  (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
                ⟨0, Nat.succ_pos _⟩)
        | succ k =>
            show HasTypeDescPi profile
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

/-- Substitution distributes over `lamCell`: the body (child shift `1`) is substituted under one
lift (`iterateLiftRaw substitution 1 ≡ RawTermSubst.lift substitution`).  rfl — `RawTerm.subst` is
`fold GenAlgebra.canonical`, threading the lift at the shift-`1` child.  The substitution-side
companion to `rename_lamCell`. -/
theorem subst_lamCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope) (body : RawTerm (sourceScope + 1)) :
    RawTerm.subst substitution (lamCell body)
      = lamCell (RawTerm.subst (iterateLiftRaw substitution 1) body) :=
  rfl

/-- Substitution distributes over `appCell`: both children (shifts `[0, 0]`) are substituted by the
substitution itself.  rfl.  The substitution-side companion to `rename_appCell`. -/
theorem subst_appCell {sourceScope targetScope : Nat}
    (substitution : RawTermSubst sourceScope targetScope)
    (functionTerm argument : RawTerm sourceScope) :
    RawTerm.subst substitution (appCell functionTerm argument)
      = appCell (RawTerm.subst substitution functionTerm)
          (RawTerm.subst substitution argument) :=
  rfl

/-- The one-binder lift of a GROWN substitution-condition: if `substitution`'s substituents are
`HasTypeDescPi`-typed at the substituted source bindings, then its single lift's substituents are
`HasTypeDescPi`-typed at the context extended by `domainCode` (substituted).  The binder-crossing
condition the `piIntro` arm of `substRespectingContext` needs (the lone non-telescope binder-crosser;
`genFormationPi` crosses binders via its telescope companion) — `0` resolves to the fresh `var`
(via `ofFormation`) after `lookup_cons_zero` + `subst_lift_weaken_commute`, `k+1` to the base
substituent weakened (`HasTypeDescPi.weakenUnderBinding`) after `lookup_cons_succ` +
`subst_lift_weaken_commute` (`iterateLiftRaw σ 1 ≡ RawTermSubst.lift σ` defeq throughout). -/
theorem substContextCondition_cons {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (domainCode : RawTerm sourceScope) (substitution : RawTermSubst sourceScope targetScope)
    (substitutionTyped : ∀ index : Fin sourceScope,
      HasTypeDescPi profile targetContext (substitution index)
        (RawTerm.subst substitution (sourceContext.lookup index))) :
    ∀ index : Fin (sourceScope + 1),
      HasTypeDescPi profile
        (targetContext.cons (RawTerm.subst substitution domainCode))
        (iterateLiftRaw substitution 1 index)
        (RawTerm.subst (iterateLiftRaw substitution 1)
          ((sourceContext.cons domainCode).lookup index)) := by
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show HasTypeDescPi profile
        (targetContext.cons (RawTerm.subst substitution domainCode))
        (RawTermSubst.lift substitution ⟨0, indexBound⟩)
        (RawTerm.subst (RawTermSubst.lift substitution)
          ((sourceContext.cons domainCode).lookup ⟨0, indexBound⟩))
      rw [TypingContext.lookup_cons_zero, subst_lift_weaken_commute]
      exact HasTypeDescPi.ofFormation
        (HasTypeDesc.var
          (targetContext.cons (RawTerm.subst substitution domainCode))
          ⟨0, Nat.succ_pos _⟩)
  | succ k =>
      show HasTypeDescPi profile
        (targetContext.cons (RawTerm.subst substitution domainCode))
        (RawTermSubst.lift substitution ⟨k + 1, indexBound⟩)
        (RawTerm.subst (RawTermSubst.lift substitution)
          ((sourceContext.cons domainCode).lookup ⟨k + 1, indexBound⟩))
      rw [TypingContext.lookup_cons_succ, subst_lift_weaken_commute]
      exact (substitutionTyped ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding
        (RawTerm.subst substitution domainCode)

mutual

/-- INTRINSIC term-substitution for the grown engine (the β-engine "whiskering" fibration leg):
`HasTypeDescPi` is preserved along ANY substitution whose substituents are `HasTypeDescPi`-typed at
the substituted source bindings, with subject and classifier substituted.  The dual of
`renameRespectingContext` (the cartesian-lift leg).  Unlike renaming, substitution does NOT preserve
formation-ness — so the `ofFormation` arm routes through `HasTypeDesc.substIntoGrown` (which returns
a GROWN derivation), not a re-wrap. -/
theorem HasTypeDescPi.substRespectingContext {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescPi profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      (∀ index : Fin sourceScope,
        HasTypeDescPi profile targetContext (substitution index)
          (RawTerm.subst substitution (sourceContext.lookup index))) →
      HasTypeDescPi profile targetContext
        (RawTerm.subst substitution subject)
        (RawTerm.subst substitution classifier) :=
  match derivation with
  | .ofFormation formationTyped => fun targetContext substitution substitutionTyped =>
      formationTyped.substIntoGrown targetContext substitution substitutionTyped
  | .conv levelExpr flag typed converts reclassifierTyped =>
      fun targetContext substitution substitutionTyped => by
        have typedSubst :=
          HasTypeDescPi.substRespectingContext typed targetContext substitution substitutionTyped
        have reclassifierSubst :=
          HasTypeDescPi.substRespectingContext reclassifierTyped targetContext substitution
            substitutionTyped
        rw [subst_universeCodeCell] at reclassifierSubst
        exact HasTypeDescPi.conv levelExpr flag typedSubst
          (Conv.subst substitution converts) reclassifierSubst
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel domainFlag
      domainTyped bodyTyped => fun targetContext substitution substitutionTyped => by
      have domainSubst :=
        HasTypeDescPi.substRespectingContext domainTyped targetContext substitution
          substitutionTyped
      rw [subst_universeCodeCell] at domainSubst
      have bodySubst :=
        HasTypeDescPi.substRespectingContext bodyTyped
          (targetContext.cons (RawTerm.subst substitution domainCode))
          (iterateLiftRaw substitution 1)
          (substContextCondition_cons domainCode substitution substitutionTyped)
      rw [subst_lamCell, subst_piTyCodeCell]
      exact HasTypeDescPi.piIntro domainLevel domainFlag domainSubst bodySubst
  | @HasTypeDescPi.piElim _ _ _ functionTerm argument domainCode codomainCode
      functionTyped argumentTyped => fun targetContext substitution substitutionTyped => by
      have functionSubst :=
        HasTypeDescPi.substRespectingContext functionTyped targetContext substitution
          substitutionTyped
      rw [subst_piTyCodeCell] at functionSubst
      have argumentSubst :=
        HasTypeDescPi.substRespectingContext argumentTyped targetContext substitution
          substitutionTyped
      rw [subst_appCell, RawTerm.subst0_subst_commute]
      exact HasTypeDescPi.piElim functionSubst argumentSubst
  | .genFormationPi _sourceContext generator payload children levels flag rule
      isFormation premises => fun targetContext substitution substitutionTyped => by
      have substPremises :=
        DescTelescopePi.substRespectingTelescope premises targetContext substitution
          substitutionTyped
      by_cases hPi : generator = .gen_piTyCode
      · subst hPi
        obtain rfl : rule = { outputType := universeFormerOutput } :=
          Option.some.inj isFormation.symm
        show HasTypeDescPi profile targetContext
          (RawTerm.subst substitution (RawTerm.mkGen .gen_piTyCode payload children))
          (RawTerm.subst substitution (universeCodeCell (lmaxAll levels) flag))
        rw [subst_universeCodeCell]
        exact HasTypeDescPi.genFormationPi targetContext .gen_piTyCode payload
          (RawTermChildren.subst substitution children) levels flag
          { outputType := universeFormerOutput } typingRuleDescOf_piTyCode substPremises
      · by_cases hSigma : generator = .gen_sigmaTyCode
        · subst hSigma
          obtain rfl : rule = { outputType := universeFormerOutput } :=
            Option.some.inj isFormation.symm
          show HasTypeDescPi profile targetContext
            (RawTerm.subst substitution (RawTerm.mkGen .gen_sigmaTyCode payload children))
            (RawTerm.subst substitution (universeCodeCell (lmaxAll levels) flag))
          rw [subst_universeCodeCell]
          exact HasTypeDescPi.genFormationPi targetContext .gen_sigmaTyCode payload
            (RawTermChildren.subst substitution children) levels flag
            { outputType := universeFormerOutput } typingRuleDescOf_sigmaTyCode substPremises
        · exfalso
          unfold typingRuleDescOf at isFormation
          rw [if_neg hPi, if_neg hSigma] at isFormation
          contradiction

/-- Companion: substitute a GROWN premise spine under a grown substitution, producing a grown
`DescTelescopePi`.  Head via `HasTypeDescPi.substRespectingContext`; tail under the binder with the
lifted grown condition (`0` → the fresh `var` via `ofFormation`; `k+1` → the grown substituent
weakened via `HasTypeDescPi.weakenUnderBinding`).  The grown mirror of `DescTelescope.substIntoGrown`'s
cons arm, with the head recursing the grown engine instead of the formation engine. -/
theorem DescTelescopePi.substRespectingTelescope {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile sourceContext levels flag children) :
    ∀ {targetBaseScope : Nat}
      (targetContext : TypingContext profile (targetBaseScope + currentDepth))
      (substitution : RawTermSubst baseScope targetBaseScope),
      (∀ index : Fin (baseScope + currentDepth),
        HasTypeDescPi profile targetContext
          (iterateLiftRaw substitution currentDepth index)
          (RawTerm.subst (iterateLiftRaw substitution currentDepth)
            (sourceContext.lookup index))) →
      DescTelescopePi profile targetContext levels flag
        (RawTermChildren.subst substitution children) :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _substitution _substitutionTyped =>
      DescTelescopePi.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext substitution substitutionTyped => by
        have substHeadTyped :
            HasTypeDescPi profile targetContext
              (RawTerm.subst (iterateLiftRaw substitution currentDepth) head)
              (universeCodeCell headLevel flag) := by
          have headSubst :=
            HasTypeDescPi.substRespectingContext headTyped targetContext
              (iterateLiftRaw substitution currentDepth) substitutionTyped
          rwa [subst_universeCodeCell] at headSubst
        refine DescTelescopePi.cons targetContext
          (RawTerm.subst (iterateLiftRaw substitution currentDepth) head) headLevel
          restLevels flag (RawTermChildren.subst substitution rest) substHeadTyped ?_
        refine DescTelescopePi.substRespectingTelescope restTyped
          (targetContext.cons
            (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
          substitution ?_
        intro index
        obtain ⟨indexValue, indexBound⟩ := index
        cases indexValue with
        | zero =>
            show HasTypeDescPi profile
              (targetContext.cons
                (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
              (RawTermSubst.lift (iterateLiftRaw substitution currentDepth) ⟨0, indexBound⟩)
              (RawTerm.subst (RawTermSubst.lift (iterateLiftRaw substitution currentDepth))
                ((_sourceContext.cons head).lookup ⟨0, indexBound⟩))
            rw [TypingContext.lookup_cons_zero, subst_lift_weaken_commute]
            exact HasTypeDescPi.ofFormation
              (HasTypeDesc.var
                (targetContext.cons
                  (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
                ⟨0, Nat.succ_pos _⟩)
        | succ k =>
            show HasTypeDescPi profile
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

end FX1Poly.Typed

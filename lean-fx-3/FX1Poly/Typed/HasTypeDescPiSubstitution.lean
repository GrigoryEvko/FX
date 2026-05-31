import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Typed.HasTypeDescSubstitution

/-! # FX1Poly/Typed/HasTypeDescPiSubstitution — substituting a formation derivation under a
    GROWN substitution (the `ofFormation` leg of the grown β-engine).

`HasTypeDesc.substIntoGrown` carries a formation derivation along ANY substitution whose
substituents are GROWN-typed (`HasTypeDescPi`) at the substituted source-binding types, and
produces a GROWN derivation.  It is the substitution action a grown β-engine needs on its
`ofFormation` case: a formation subject substituted by a grown substitution is in general no
longer a formation term (a variable may be replaced by an application), so the result lands in
`HasTypeDescPi`, not `HasTypeDesc`.

## The generic-arm payoff

The `genFormation` case rebuilds through the GENERIC `genFormationPi` arm: it substitutes the
premise spine (`DescTelescope.substIntoGrown`, producing a grown `DescTelescopePi`) and re-fires
`genFormationPi` with that grown spine.  No per-former projection of the children is needed — the
`by_cases` only pins the universe-former OUTPUT (`universeFormerOutput`, which is scope-independent
and substitution-fixed).  A per-former (binary) arm would instead force a partial-match on the
substituted child telescope (the indexed-inductive propext trap); the generic arm sidesteps it.

## Structure

Mutual structural recursion `HasTypeDesc.substIntoGrown ⋈ DescTelescope.substIntoGrown` on the
FORMATION derivation (input), producing the GROWN engine (output).  Cross-calls sit on pristine
`match`-bound subterms (`typedPremise`/`reclassifierTyped`, `premises`, `head`/`restTyped`), the
genFormation companion cross-call hoisted before the `by_cases`, so Lean's structural recursion
lands it without `termination_by`.  The recursion stays within the `HasTypeDesc`/`DescTelescope`
family (output type does not affect termination), so there is no cross-inductive boundary issue.

* `var` — the substituent at that index, supplied by the grown substitution-typing condition.
* `conv` — recurse both premises; `Conv.subst` carries the conversion; rebuild `HasTypeDescPi.conv`.
* `universeFormation` — substitution-fixed; embed via `ofFormation`.
* `genFormation` — substitute the spine to a `DescTelescopePi`, pin the output universe code, rebuild
  via `genFormationPi`.
* telescope `cons` — head via `HasTypeDesc.substIntoGrown`; tail under the binder with the LIFTED
  grown condition (`0` → the fresh `var` embedded via `ofFormation`; `k+1` → the grown substituent
  weakened via `HasTypeDescPi.weakenUnderBinding`).

## Zero-axiom

Mutual structural recursion + the reused `subst_{variableCell,universeCodeCell,lift_weaken_commute}`
bricks + `Conv.subst` + `HasTypeDescPi.weakenUnderBinding` + the generic `genFormationPi` rebuild +
the nested-`if` generator pin (propext-free via `DecidableEq Generator`).  No `axiom`, `sorry`,
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

end FX1Poly.Typed

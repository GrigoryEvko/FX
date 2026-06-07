import FX1Poly.Typed.BoundedFormationLeafArms
import FX1Poly.Typed.BoundedGrownDispatch
import FX1Poly.Typed.BoundExceedsDischarge

/-! # FX1Poly/Typed/BoundedFormationDispatch
    — the bounded FORMATION-engine fundamental theorem (BFT-10 + BFT-11), via the budget recursor

This discharges the `formationFundamental` premise shape of the bounded grown dispatch
(`HasTypeDescPi.fundamentalAtBoundedSuccFromFormation`, BFT-6): every `HasTypeDesc` formation derivation `d`,
GIVEN a `BoundExceeds env bound d` budget, satisfies the `+1`-closing bound-reducible-member conclusion
`FundamentalConclusionAtBoundedSucc`.  It is the formation analogue of BFT-6, structurally SIMPLER (the formation
engine has only `var` / `conv` / `universeFormation` / `genFormation` — no `ofFormation` / `piIntro` / `piElim`).

## The budget-recursor insight (why no inversion is needed)

The `universeFormation` LEAF needs `belowBound : denote (lsucc levelExpr) env < bound` — the only per-term "fuel"
the bounded route consumes (every other arm gate-EXTRACTS its level bound from a reducible universe member produced
by an IH).  Reading `belowBound` off a separately-supplied budget would require INVERTING `BoundExceeds (ctor …)`
at a fixed `HasTypeDesc` index — and a `match`/`cases` there hits the opaque-index wall (the matcher can't rule out
the `genFormation` budget-ctor whose index is the opaque `rule.outputType …`).

The resolution: induct on the BUDGET, not on the derivation.  `BoundExceeds.rec` dispatches on the budget's own
constructor and hands each arm the budget's fields AS NAMED ARGUMENTS — the `universeFormation` arm receives
`belowBound` directly, the `genFormation` arm receives `premisesBudget` + the telescope IH, the `conv` arm receives
the two sub-budgets + the two IHs.  The HasTypeDesc derivation rides along as the budget ctor's index argument; the
conclusion motive ignores it.  The primitive recursor is propext-free, so the whole dispatch is zero-axiom with NO
index-equality-witness machinery.

## The arms (every callee shipped; mirror of BFT-6 minus the grown-only ctors)

* `var` — `fundamentalVarAtBoundedSucc` (BFT-7).
* `conv` — inline: read the reclassifier universe member off its IH, gate-extract `belowBound`, transport the
  subject member along the conversion (`convMemberUnderClosingSubstitutionBounded` +
  `reducibleTypeAtBoundFromUniverseMemberBounded`).  The sub-budgets are unused (the gate comes from the IH).
* `universeFormation` — `fundamentalUniverseFormationAtBoundedSucc` (BFT-9) fed the budget's `belowBound`.  THE one
  budget-consuming arm.
* `genFormation` — the Π/Σ former branches feed `fundamentalGenFormationPiFromTelescopeAtBoundedSucc` (BFT-4) /
  `fundamentalGenFormationSigmaFromTelescopeAtBoundedSucc` (the Σ twin) the output-level telescope, via the same
  double-apply-`premisesFundamental` dance as BFT-6 (read members at `argLevel = bound`, gate-extract
  `output < bound`, re-apply at `argLevel = output`).  Non-Π/Σ generators are impossible (`typingRuleDescOf`).
* `nilTelescope` / `consTelescope` — the motive_2 (`IsFormationTelescopeReducibleAtBoundedSucc`, BFT-10) arms,
  identical to BFT-6's telescope arms (the cons arm lifts the head member `argLevel → bound` via `.cumulative`).

## Zero-axiom verification

One `BoundExceeds.rec` application (mutual with `BoundExceedsTelescope.rec` for the telescope motive_2); the arms
reuse the shipped bounded building blocks (`subst_universeCodeCell` / `ReducibleEnvAtBounded.cons` /
`IsReducibleMemberAtBounded.cumulative` / `DescTelescope.twoChildLevels` / `levelMax_lt`).  No `funext`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega` (checked: depends on no
axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **Bounded telescope reducibility for a FORMATION premise telescope (motive_2 of the BFT-11 dispatch, BFT-10).**
The formation-engine analogue of `IsTelescopeReducibleAtBoundedSucc` (over `DescTelescope` rather than
`DescTelescopePi`).  The body is identical — it depends only on `children` / `levelsList` / `flag`, not on the
telescope type — so only the index argument's type differs.  `_argLevelLeBound` is the cumulativity gate the
`consTelescope` arm consumes. -/
abbrev IsFormationTelescopeReducibleAtBoundedSucc {profile : PolyProfile} {baseScope currentDepth : Nat}
    {binderShifts : List Nat}
    (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile (baseScope + currentDepth)) (levelsList : List LevelExpr)
    (flag : UniverseFlag) (children : RawTermChildren binderShifts baseScope)
    (_telescope : DescTelescope profile context levelsList flag children) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1))
    (argLevel : Nat) (_argLevelLeBound : argLevel ≤ bound)
    (_env : ReducibleEnvAtBounded env bound context substitution)
    (shapeEq : binderShifts = consecutiveShifts currentDepth levelsList.length),
    TelescopeReducibleAtBounded env bound argLevel flag currentDepth levelsList.length
      substitution levelsList (shapeEq ▸ children)

/-- **The bounded formation-engine fundamental theorem (BFT-11).**  Under a `BoundExceeds env bound d` budget, every
`HasTypeDesc` formation derivation `d` satisfies the `+1`-closing bound-reducible-member conclusion.  Proved by
`BoundExceeds.rec` (induction on the BUDGET, not the derivation) so each arm receives the budget's fields named — in
particular the `universeFormation` arm gets `belowBound` directly, sidestepping the opaque-`outputType`-index
inversion that blocks a `match` on the budget.  This is the `formationFundamental` premise of BFT-6 (modulo its
budget argument), discharged unconditionally up to the budget. -/
theorem HasTypeDesc.fundamentalAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat) :
    ∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
      (d : HasTypeDesc profile context subject classifier),
      BoundExceeds env bound d →
        FundamentalConclusionAtBoundedSucc env bound context subject classifier := by
  intro scope context subject classifier d budget
  refine BoundExceeds.rec
    (motive_1 := fun {_scope} {_context} {_subject} {_classifier} _d _budget =>
      FundamentalConclusionAtBoundedSucc env bound _context _subject _classifier)
    (motive_2 := fun {_baseScope _currentDepth _binderShifts} {_context} {_levels} {_flag} {_children}
        telescope _telescopeBudget =>
      IsFormationTelescopeReducibleAtBoundedSucc env bound _context _levels _flag _children telescope)
    ?var ?conv ?universeFormation ?genFormation ?nilTelescope ?consTelescope budget
  · -- var
    intro _scope context index
    exact fundamentalVarAtBoundedSucc env bound context index
  · -- conv (sub-budgets unused; the level gate is extracted from the reclassifier IH)
    intro _scope _context _subject _classifier _reclassifier levelExpr flag _typed converts
      _reclassifierTyped _subjectBudget _reclassifierBudget subjectFundamental reclassifierFundamental
    intro _targetScope substitution envReducible
    have reMember := reclassifierFundamental substitution envReducible
    rw [subst_universeCodeCell] at reMember
    obtain ⟨reCand, reCandReducible, reCandIn⟩ := reMember
    have belowBound := universeCodeReducibleAtBounded_belowBound reCandReducible
    exact convMemberUnderClosingSubstitutionBounded env bound
      (subjectFundamental substitution envReducible)
      (reducibleTypeAtBoundFromUniverseMemberBounded env bound ⟨reCand, reCandReducible, reCandIn⟩ belowBound)
      converts
  · -- universeFormation (the only budget-consuming arm: belowBound arrives named from the budget ctor)
    intro _scope context levelExpr flag belowBound
    exact fundamentalUniverseFormationAtBoundedSucc env bound context levelExpr flag belowBound
  · -- genFormation (Π/Σ former dispatch)
    intro _scope _context generator _payload children levelsList flag rule isFormation premises
      _premisesBudget premisesFundamental
    by_cases isPiFormer : generator = .gen_piTyCode
    · subst isPiFormer
      obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
      match children with
      | .childCons domain (.childCons codomain .childNil) =>
          obtain ⟨domainLevel, codomainLevel, levelsShape⟩ :=
            DescTelescope.twoChildLevels premises
          subst levelsShape
          dsimp only [universeFormerOutput]
          exact fundamentalGenFormationPiFromTelescopeAtBoundedSucc env bound _context
            domainLevel codomainLevel flag
            (fun substitution envReducible => by
              have throwaway := premisesFundamental substitution bound (Nat.le_refl bound) envReducible
                Generator.gen_piTyCode_binderShifts_eq
              obtain ⟨domM, codMFn⟩ := throwaway.twoChildMembers
              have domBB : LevelExpr.denote domainLevel env < bound := by
                obtain ⟨_, dr, _⟩ := domM
                exact universeCodeReducibleAtBounded_belowBound dr
              have variableZero :=
                variableZeroMemberOfBoundedUniverseMember domM domBB (Nat.le_of_lt domBB)
              have codM := codMFn _ variableZero
              have codBB : LevelExpr.denote codomainLevel env < bound := by
                obtain ⟨_, cr, _⟩ := codM
                exact universeCodeReducibleAtBounded_belowBound cr
              have outBB : LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env < bound :=
                levelMax_lt domBB codBB
              exact premisesFundamental substitution
                (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env) (Nat.le_of_lt outBB)
                envReducible Generator.gen_piTyCode_binderShifts_eq)
    · by_cases isSigmaFormer : generator = .gen_sigmaTyCode
      · subst isSigmaFormer
        obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
        match children with
        | .childCons domain (.childCons codomain .childNil) =>
            obtain ⟨domainLevel, codomainLevel, levelsShape⟩ :=
              DescTelescope.twoChildLevels premises
            subst levelsShape
            dsimp only [universeFormerOutput]
            exact fundamentalGenFormationSigmaFromTelescopeAtBoundedSucc env bound _context
              domainLevel codomainLevel flag
              (fun substitution envReducible => by
                have throwaway := premisesFundamental substitution bound (Nat.le_refl bound) envReducible
                  Generator.gen_sigmaTyCode_binderShifts_eq
                obtain ⟨domM, codMFn⟩ := throwaway.twoChildMembers
                have domBB : LevelExpr.denote domainLevel env < bound := by
                  obtain ⟨_, dr, _⟩ := domM
                  exact universeCodeReducibleAtBounded_belowBound dr
                have variableZero :=
                  variableZeroMemberOfBoundedUniverseMember domM domBB (Nat.le_of_lt domBB)
                have codM := codMFn _ variableZero
                have codBB : LevelExpr.denote codomainLevel env < bound := by
                  obtain ⟨_, cr, _⟩ := codM
                  exact universeCodeReducibleAtBounded_belowBound cr
                have outBB : LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env < bound :=
                  levelMax_lt domBB codBB
                exact premisesFundamental substitution
                  (LevelExpr.denote (lmaxAll [domainLevel, codomainLevel]) env) (Nat.le_of_lt outBB)
                  envReducible Generator.gen_sigmaTyCode_binderShifts_eq)
      · by_cases isListFormer : generator = .gen_listCode
        · subst isListFormer
          obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
          match children with
          | .childCons element .childNil =>
              obtain ⟨elementLevel, levelsShape⟩ := DescTelescope.oneChildLevel premises
              subst levelsShape
              dsimp only [universeFormerOutput]
              exact fundamentalGenFormationListFromTelescopeAtBoundedSucc env bound _context
                elementLevel flag
                (fun substitution envReducible => by
                  have memberTelescope := premisesFundamental substitution bound (Nat.le_refl bound)
                    envReducible Generator.gen_listCode_binderShifts_eq
                  have elementMember := memberTelescope.oneChildMember
                  have elementBelowBound : LevelExpr.denote elementLevel env < bound := by
                    obtain ⟨_, elementReducible, _⟩ := elementMember
                    exact universeCodeReducibleAtBounded_belowBound elementReducible
                  have outputBelowBound :
                      LevelExpr.denote (lmaxAll [elementLevel]) env < bound := elementBelowBound
                  exact premisesFundamental substitution
                    (LevelExpr.denote (lmaxAll [elementLevel]) env) (Nat.le_of_lt outputBelowBound)
                    envReducible Generator.gen_listCode_binderShifts_eq)
        · by_cases isOptionFormer : generator = .gen_optionCode
          · subst isOptionFormer
            obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
            match children with
            | .childCons element .childNil =>
                obtain ⟨elementLevel, levelsShape⟩ := DescTelescope.oneChildLevel premises
                subst levelsShape
                dsimp only [universeFormerOutput]
                exact fundamentalGenFormationOptionFromTelescopeAtBoundedSucc env bound _context
                  elementLevel flag
                  (fun substitution envReducible => by
                    have memberTelescope := premisesFundamental substitution bound (Nat.le_refl bound)
                      envReducible Generator.gen_optionCode_binderShifts_eq
                    have elementMember := memberTelescope.oneChildMember
                    have elementBelowBound : LevelExpr.denote elementLevel env < bound := by
                      obtain ⟨_, elementReducible, _⟩ := elementMember
                      exact universeCodeReducibleAtBounded_belowBound elementReducible
                    have outputBelowBound :
                        LevelExpr.denote (lmaxAll [elementLevel]) env < bound := elementBelowBound
                    exact premisesFundamental substitution
                      (LevelExpr.denote (lmaxAll [elementLevel]) env) (Nat.le_of_lt outputBelowBound)
                      envReducible Generator.gen_optionCode_binderShifts_eq)
          · exfalso
            unfold typingRuleDescOf at isFormation
            rw [if_neg isPiFormer, if_neg isSigmaFormer, if_neg isListFormer, if_neg isOptionFormer] at isFormation
            contradiction
  · -- nilTelescope
    intro _baseScope _currentDepth _context _flag
    intro _targetScope _substitution _argLevel _argLevelLeBound _env _shapeEq
    exact True.intro
  · -- consTelescope
    intro _baseScope _currentDepth _restShifts _context _head _headLevel _restLevels _flag _rest
      _headTyped _restTyped _headBudget _restBudget headFundamental restFundamental
    intro _targetScope substitution argLevel argLevelLeBound envReducible shapeEq
    simp only [List.length_cons, consecutiveShifts] at shapeEq
    obtain ⟨_headShiftEq, restShapeEq⟩ := List.cons.inj shapeEq
    subst restShapeEq
    exact fundamentalTelescopeConsAtBoundedSucc env bound argLevel envReducible headFundamental
      (fun argument argumentMember =>
        restFundamental (RawTermSubst.cons argument substitution) argLevel argLevelLeBound
          (ReducibleEnvAtBounded.cons envReducible (argumentMember.cumulative argLevelLeBound)) rfl)

end FX1Poly.Typed

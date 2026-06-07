import FX1Poly.Typed.BoundedGrownDispatch
import FX1Poly.Typed.BoundedFormationDispatch
import FX1Poly.Typed.BoundExceedsPi

/-! # FX1Poly/Typed/BoundedGrownFundamental
    — the unconditional (up to budget) GROWN-engine fundamental theorem (BFT-12c)

`HasTypeDescPi.fundamentalAtBoundedSucc`: given a `BoundExceedsPi env bound d` budget, every grown-engine derivation
`d` satisfies the `+1`-closing bound-reducible-member conclusion `FundamentalConclusionAtBoundedSucc`.  This is the
budget-discharged form of BFT-6 (`HasTypeDescPi.fundamentalAtBoundedSuccFromFormation`): BFT-6 took the formation
fundamental theorem as an explicit `formationFundamental` PREMISE; here that premise is discharged INLINE.

## The discharge: induct on the BUDGET, ofFormation feeds BFT-11

Proved by `BoundExceedsPi.rec` (induction on the budget, not the derivation — the same unlock as BFT-11).  Every
arm is the SAME body as BFT-6's corresponding arm (the conv/piIntro/piElim/genFormationPi arms ignore their
sub-budgets, gate-extracting their level bounds from the reducible members produced by the IHs, exactly as before;
the telescope motive_2 is the shipped `IsTelescopeReducibleAtBoundedSucc`).  The ONE changed arm is `ofFormation`:
where BFT-6 wrote `formationFundamental formationTyped`, this feeds the budget's CARRIED embedded `BoundExceeds`
(named by the `BoundExceedsPi.ofFormation` constructor) straight into `HasTypeDesc.fundamentalAtBoundedSucc`
(BFT-11) — `HasTypeDesc.fundamentalAtBoundedSucc env bound formationTyped formationBudget`.  So the formation
premise of BFT-6 is replaced by the genuine formation FT, and the whole grown FT becomes conditional only on the
single `BoundExceedsPi` budget.

## What remains to SN-043

`BoundExceedsPi.existsBound` (BFT-12b) supplies the budget for any concrete grown derivation, so for a CLOSED
`HasTypeDescPi .empty t T` we will (BFT-13) pick `⟨bound, budget⟩ := existsBound` and apply this theorem at that
bound to get a closed bound-reducible member, then (BFT-14) reflect it to `IsStronglyNormalizing t` via scope+1
CR1 = SN-043.

## Zero-axiom verification

One `BoundExceedsPi.rec` application; arms reuse the shipped bounded building blocks
(`fundamentalPiIntroAtBoundedSucc` / `fundamentalPiElimAtBoundedSucc` / `fundamentalGenFormationPi`-&-`Sigma` /
`fundamentalTelescopeConsAtBoundedSucc` / `IsTelescopeReducibleAtBoundedSucc` / `HasTypeDesc.fundamentalAt\
BoundedSucc`).  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega` (checked: depends on no axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **The bounded grown-engine fundamental theorem, unconditional up to the budget (BFT-12c).**  Under a
`BoundExceedsPi env bound d` budget, every `HasTypeDescPi` derivation satisfies the `+1`-closing bound-reducible
conclusion.  `BoundExceedsPi.rec` dispatch: the `ofFormation` arm feeds the carried embedded `BoundExceeds` into
`HasTypeDesc.fundamentalAtBoundedSucc` (BFT-11), discharging BFT-6's `formationFundamental` premise inline; every
other arm mirrors BFT-6 (budgets unused — levels gate-extracted from members). -/
theorem HasTypeDescPi.fundamentalAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat) :
    ∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope}
      (d : HasTypeDescPi profile context subject classifier),
      BoundExceedsPi env bound d →
        FundamentalConclusionAtBoundedSucc env bound context subject classifier := by
  intro scope context subject classifier d budget
  refine BoundExceedsPi.rec
    (motive_1 := fun {_scope} {_context} {_subject} {_classifier} _d _budget =>
      FundamentalConclusionAtBoundedSucc env bound _context _subject _classifier)
    (motive_2 := fun {_baseScope _currentDepth _binderShifts} {_context} {_levels} {_flag} {_children}
        telescope _telescopeBudget =>
      IsTelescopeReducibleAtBoundedSucc env bound _context _levels _flag _children telescope)
    ?ofFormation ?conv ?piIntro ?piElim ?genFormationPi ?nilTelescope ?consTelescope budget
  · -- ofFormation: the budget-consuming arm — feed BFT-11 the carried embedded BoundExceeds
    intro _scope _context _subject _classifier formationTyped formationBudget
    exact HasTypeDesc.fundamentalAtBoundedSucc env bound formationTyped formationBudget
  · -- conv (mirror of BFT-6; sub-budgets unused)
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
  · -- piIntro
    intro _scope _context _domainCode _codomainCode _body _domainLevel _codomainLevel _flag
      _domainTyped _codomainTyped _bodyTyped _domainBudget _codomainBudget _bodyBudget
      domainFundamental codomainFundamental bodyFundamental
    refine fundamentalPiIntroAtBoundedSucc env bound _context
      (fun substitution envReducible => ?_)
      (fun substitution envReducible argument argumentMember => ?_)
      bodyFundamental
    · have m := domainFundamental substitution envReducible
      rw [subst_universeCodeCell] at m
      obtain ⟨c, cr, ci⟩ := m
      exact reducibleTypeAtBoundFromUniverseMemberBounded env bound ⟨c, cr, ci⟩
        (universeCodeReducibleAtBounded_belowBound cr)
    · have m := codomainFundamental (RawTermSubst.cons argument substitution)
        (ReducibleEnvAtBounded.cons envReducible argumentMember)
      rw [subst_universeCodeCell] at m
      obtain ⟨c, cr, ci⟩ := m
      exact reducibleTypeAtBoundFromUniverseMemberBounded env bound ⟨c, cr, ci⟩
        (universeCodeReducibleAtBounded_belowBound cr)
  · -- piElim
    intro _scope _context _functionTerm _argument _domainCode _codomainCode _functionTyped
      _argumentTyped _functionBudget _argumentBudget functionFundamental argumentFundamental
    exact fundamentalPiElimAtBoundedSucc env bound _context functionFundamental argumentFundamental
  · -- genFormationPi (mirror of BFT-6)
    intro _scope _context generator _payload children levelsList flag rule isFormation premises
      _premisesBudget premisesFundamental
    by_cases isPiFormer : generator = .gen_piTyCode
    · subst isPiFormer
      obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
      match children with
      | .childCons domain (.childCons codomain .childNil) =>
          obtain ⟨domainLevel, codomainLevel, levelsShape⟩ :=
            DescTelescopePi.twoChildLevels premises
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
              DescTelescopePi.twoChildLevels premises
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
              obtain ⟨elementLevel, levelsShape⟩ := DescTelescopePi.oneChildLevel premises
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
        · exfalso
          unfold typingRuleDescOf at isFormation
          rw [if_neg isPiFormer, if_neg isSigmaFormer, if_neg isListFormer] at isFormation
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

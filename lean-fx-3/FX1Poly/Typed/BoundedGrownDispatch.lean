import FX1Poly.Typed.BoundedGenFormationPiFromTelescope
import FX1Poly.Typed.BoundedGenFormationSigmaFromTelescope
import FX1Poly.Typed.BoundedGenFormationListFromTelescope
import FX1Poly.Typed.BoundedTelescopeConsSucc
import FX1Poly.Typed.DescTelescopeInversion

/-! # FX1Poly/Typed/BoundedGrownDispatch
    — the bounded grown-engine fundamental theorem (BFT-6), conditional on a bounded formation premise

This is the bounded analogue of the denote `HasTypeDescPi.fundamentalVectorFromFormation`
(`HasTypeDescPiFundamentalVectorFromFormation.lean`): the `HasTypeDescPi.rec` dispatch with
`motive_1 = FundamentalConclusionAtBoundedSucc` and `motive_2 = IsTelescopeReducibleAtBoundedSucc`, taking the
embedded `HasTypeDesc` formation arm (`ofFormation`) as an explicit premise.  Every other arm is discharged from
shipped bounded building blocks; the dispatch introduces NO new lemmas — it is pure assembly.

## The motive_2 wrapper (BFT-5) and the argLevel→bound gate

`IsTelescopeReducibleAtBoundedSucc` is the `+1`-closing bound-carrying telescope predicate.  It mirrors the denote
`IsTelescopeReducibleAtVector` with ONE structural change: the bounded `TelescopeReducibleAtBounded` carries an
argument-quantification level `argLevel` (the former's decoded OUTPUT level, where `twoChildMembers` reads the
codomain member), distinct from the membership bound `bound`.  The wrapper carries `_argLevelLeBound : argLevel ≤
bound` — a hypothesis that does NOT appear in the telescope conclusion (hence the underscore, exactly like the
denote wrapper's unused `_predLevel`) but WEAKENS the obligation to argLevels at or below `bound`.  This is exactly
what the `consTelescope` arm needs: to cons an argument that is a member at `argLevel` into the bound-uniform
`ReducibleEnvAtBounded`, it lifts the member from `argLevel` to `bound` via `IsReducibleMemberAtBounded.cumulative
_argLevelLeBound`.  The `genFormationPi` arm only ever uses the telescope at `argLevel = output ≤ bound`, so it can
always supply the gate.

## The dispatch arms (every callee shipped)

* `ofFormation` — the explicit `formationFundamental` premise (a bounded `HasTypeDesc → FundamentalConclusion\
  AtBoundedSucc`).  Discharged unconditionally by BFT-11/12; here it is a hypothesis.
* `conv` — inline: read the reclassifier universe member off its IH, gate-extract `belowBound`, transport the
  subject member along the conversion (`convMemberUnderClosingSubstitutionBounded` +
  `reducibleTypeAtBoundFromUniverseMemberBounded`).  The ready `fundamentalConvArmBoundedSucc` is NOT used because
  it wants `belowBound` up front (unavailable before intro-ing the substitution).
* `piIntro` — `fundamentalPiIntroAtBoundedSucc` fed the domain/codomain reducible-as-type premises, each built by
  decoding the corresponding universe-member IH inside its own `∀` (gate-extracting `belowBound` per substitution).
* `piElim` — `fundamentalPiElimAtBoundedSucc` on the two IHs directly.
* `genFormationPi` — the Π/Σ former branches feed `fundamentalGenFormationPiFromTelescopeAtBoundedSucc` (BFT-4) /
  `fundamentalGenFormationSigmaFromTelescopeAtBoundedSucc` (the Σ twin) the output-level telescope.  Because BFT-4
  / the Σ-twin take the telescope at `argLevel = output` (their codomain-member fn quantifies arguments at the
  output level), the builder must supply `output ≤ bound` — which needs the children's level bounds, which live
  IN the telescope.  Resolution: DOUBLE-APPLY `premisesFundamental` — first at `argLevel = bound` (trivial
  `Nat.le_refl`) to read the domain/codomain members and gate-extract `output < bound` (`levelMax_lt`), then again
  at `argLevel = output` with `Nat.le_of_lt` for the real telescope.  `premisesFundamental` is ∀-reusable, so the
  double application is free.
* `nilTelescope` — `True.intro`.
* `consTelescope` — `fundamentalTelescopeConsAtBoundedSucc` with the tail IH threaded through
  `ReducibleEnvAtBounded.cons` after the argument member is lifted `argLevel → bound` by `.cumulative`.

## Zero-axiom verification

One `HasTypeDescPi.rec` application; the binder arms use `subst_universeCodeCell` / `ReducibleEnvAtBounded.cons` /
`IsReducibleMemberAtBounded.cumulative`; the telescope arm uses `simp only [List.length_cons, consecutiveShifts]`
+ `List.cons.inj` + the shipped cons companion.  No `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega` (checked: depends on no axioms).  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **Bounded telescope reducibility for a grown premise telescope (motive_2 of the BFT-6 dispatch).**  Under
every `+1`-closing bound-reducible environment, the former's child spine is bound-telescope-reducible at every
argument level at or below `bound` (`_argLevelLeBound`).  The bound-carrying analogue of the denote
`IsTelescopeReducibleAtVector`; `_argLevelLeBound` is the cumulativity gate the `consTelescope` arm consumes. -/
abbrev IsTelescopeReducibleAtBoundedSucc {profile : PolyProfile} {baseScope currentDepth : Nat}
    {binderShifts : List Nat}
    (env : Nat → Nat) (bound : Nat)
    (context : TypingContext profile (baseScope + currentDepth)) (levelsList : List LevelExpr)
    (flag : UniverseFlag) (children : RawTermChildren binderShifts baseScope)
    (_telescope : DescTelescopePi profile context levelsList flag children) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1))
    (argLevel : Nat) (_argLevelLeBound : argLevel ≤ bound)
    (_env : ReducibleEnvAtBounded env bound context substitution)
    (shapeEq : binderShifts = consecutiveShifts currentDepth levelsList.length),
    TelescopeReducibleAtBounded env bound argLevel flag currentDepth levelsList.length
      substitution levelsList (shapeEq ▸ children)

/-- **The bounded grown-engine fundamental theorem, conditional on a bounded formation premise (BFT-6).**  Under
the explicit `formationFundamental` hypothesis for the embedded `HasTypeDesc` arm, every `HasTypeDescPi`
derivation satisfies the `+1`-closing bound-reducible-member conclusion.  This is the full `HasTypeDescPi.rec`
assembly; the formation premise is discharged unconditionally downstream (BFT-11/12). -/
theorem HasTypeDescPi.fundamentalAtBoundedSuccFromFormation {profile : PolyProfile}
    (env : Nat → Nat) (bound : Nat)
    (formationFundamental :
      ∀ {scope : Nat} {context : TypingContext profile scope}
        {subject classifier : RawTerm scope},
        HasTypeDesc profile context subject classifier →
          FundamentalConclusionAtBoundedSucc env bound context subject classifier) :
    ∀ {scope : Nat} {context : TypingContext profile scope} {subject classifier : RawTerm scope},
      HasTypeDescPi profile context subject classifier →
        FundamentalConclusionAtBoundedSucc env bound context subject classifier := by
  intro scope context subject classifier typed
  refine HasTypeDescPi.rec
    (motive_1 := fun context subject classifier _typed =>
      FundamentalConclusionAtBoundedSucc env bound context subject classifier)
    (motive_2 := IsTelescopeReducibleAtBoundedSucc env bound)
    ?ofFormation ?conv ?piIntro ?piElim ?genFormationPi ?nilTelescope ?consTelescope typed
  · -- ofFormation
    intro _scope _context _subject _classifier formationTyped
    exact formationFundamental formationTyped
  · -- conv
    intro _scope _context _subject _classifier _reclassifier levelExpr flag _typed converts
      _reclassifierTyped subjectFundamental reclassifierFundamental
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
      _domainTyped _codomainTyped _bodyTyped domainFundamental codomainFundamental bodyFundamental
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
      _argumentTyped functionFundamental argumentFundamental
    exact fundamentalPiElimAtBoundedSucc env bound _context functionFundamental argumentFundamental
  · -- genFormationPi
    intro _scope _context generator _payload children levelsList flag rule isFormation premises
      premisesFundamental
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
      _headTyped _restTyped headFundamental restFundamental
    intro _targetScope substitution argLevel argLevelLeBound envReducible shapeEq
    simp only [List.length_cons, consecutiveShifts] at shapeEq
    obtain ⟨_headShiftEq, restShapeEq⟩ := List.cons.inj shapeEq
    subst restShapeEq
    exact fundamentalTelescopeConsAtBoundedSucc env bound argLevel envReducible headFundamental
      (fun argument argumentMember =>
        restFundamental (RawTermSubst.cons argument substitution) argLevel argLevelLeBound
          (ReducibleEnvAtBounded.cons envReducible (argumentMember.cumulative argLevelLeBound)) rfl)

end FX1Poly.Typed

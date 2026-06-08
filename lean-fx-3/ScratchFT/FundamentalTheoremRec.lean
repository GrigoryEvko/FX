import FX1Poly.Typed.ReducibleSemanticRules
import FX1Poly.Typed.ReducibleEnvVec
import FX1Poly.Typed.TelescopeReducible
import FX1Poly.Typed.FormerChildrenReducible

/-! # ScratchFT/FundamentalTheoremRec — recursor-based dependent FT (WIP, NOT in the lib build)

The match-based assembly hit a fundamental knot: the dependent telescope's reducibility needs the
non-variable `consecutiveShifts` index (for substitution-scope alignment across binders), which fights Lean's
mutual structural-recursion inference; the transport workaround needs casts that need `subst`, and `subst`
reverts the recursive-call argument, breaking termination.

The RIGOROUS resolution is to prove the FT by the kernel's own mutual induction principle, `@HasTypeDescPi.rec`
(induction on derivations).  The recursor threads the mutual induction NATIVELY: the `genFormationPi` minor
premise receives `motive₂ … premises` (the telescope IH) directly; the `cons` minor premise receives the head
IH (`motive₁ … headTyped`) and tail IH (`motive₂ … restTyped`) directly.  There is no structural-recursion
inference to fail.  The residual consecutive-shift alignment now lives in a NON-recursive motive statement
(`TelescopeMotive` below carries a `shapeEq` witness) discharged by the `nil`/`cons` minor premises — where the
telescope's real structure makes the shifts genuinely consecutive — NOT in a recursion body, so the cast no
longer breaks termination.

`sorry` is a transient scaffold here (never committed to the lib).  Built via
`lake env lean ScratchFT/FundamentalTheoremRec.lean`; moved to `FX1Poly/Typed/` + gated + committed green only
when sorry-free.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The term fundamental-theorem motive.**  A well-typed subject, under any closing substitution and a
per-variable-level reducible environment, is a reducible member of its classifier at `predLevel + 1`.  Quantifying
the substitution/env/level INSIDE the motive lets a single `motive₁` carry the whole FT; the type-formation FT is
a `tarskiDecode` corollary, inlined where a type-premise's reducibility is needed (no two-FT split). -/
abbrev FundamentalMotive {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (subject classifier : RawTerm scope)
    (_typed : HasTypeDescPi profile context subject classifier) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst scope (targetScope + 1))
    {envLevels : Fin scope → Nat} (predLevel : Nat)
    (_env : ReducibleEnvVec envLevels context substitution),
    IsReducibleMemberAt (predLevel + 1) (RawTerm.subst substitution classifier)
      (RawTerm.subst substitution subject)

/-- **The premise-telescope motive.**  Under a closing substitution + env, the children form a reducible
telescope (`TelescopeReducible`).  Because the recursor's `motive₂` is indexed by a VARIABLE `binderShifts`,
the statement carries a `shapeEq : binderShifts = consecutiveShifts currentDepth levelsList.length` witness and
transports `children` along it — `rfl` / `gen_*TyCode_binderShifts_eq` at the `genFormationPi` use site, and
discharged from the real telescope structure in the `cons` minor premise. -/
abbrev TelescopeMotive {profile : PolyProfile} {baseScope currentDepth : Nat} {binderShifts : List Nat}
    (context : TypingContext profile (baseScope + currentDepth)) (levelsList : List LevelExpr)
    (flag : UniverseFlag) (children : RawTermChildren binderShifts baseScope)
    (_telescope : DescTelescopePi profile context levelsList flag children) : Prop :=
  ∀ {targetScope : Nat} (substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1))
    {envLevels : Fin (baseScope + currentDepth) → Nat} (predLevel : Nat)
    (_env : ReducibleEnvVec envLevels context substitution)
    (shapeEq : binderShifts = consecutiveShifts currentDepth levelsList.length),
    TelescopeReducible flag currentDepth levelsList.length substitution levelsList (shapeEq ▸ children)

/-- A depth-0 former telescope over the concrete two-child spine has exactly a two-element level list.
Non-recursive (a standalone inversion); the child spine fixes the index so the `nil` arms are refuted
definitionally (no propext leak).  The `genFormationPi` arm uses it to recover `levels = [_, _]`. -/
theorem descTelescopePiTwoLevels {profile : PolyProfile} {baseScope : Nat}
    {context : TypingContext profile baseScope} {levelsList : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren [0, 1] baseScope}
    (telescope : DescTelescopePi profile (currentDepth := 0) context levelsList flag children) :
    ∃ domainLevel codomainLevel, levelsList = [domainLevel, codomainLevel] := by
  cases telescope with
  | cons _ctx _head domainLevel _restLevels _flag _rest _headTyped restTyped =>
      cases restTyped with
      | cons _ctx2 _head2 codomainLevel _restLevels2 _flag2 _rest2 _headTyped2 tailTel =>
          cases tailTel with
          | nil => exact ⟨domainLevel, codomainLevel, rfl⟩

/-- **The dependent fundamental theorem, by the kernel mutual recursor (WIP scaffold).**  Motives well-formed +
the `@HasTypeDescPi.rec` application typechecks; the seven minor premises are transient `sorry` to be filled. -/
theorem HasTypeDescPi.fundamental {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context subject classifier) :
    FundamentalMotive context subject classifier typed := by
  refine HasTypeDescPi.rec (motive_1 := FundamentalMotive) (motive_2 := TelescopeMotive)
    ?ofFormation ?conv ?piIntro ?piElim ?genFormationPi ?nilTel ?consTel typed
  · -- ofFormation
    sorry
  · -- conv: reclassifier reducibility from its IH ONE LEVEL UP (tarskiDecode), subject membership cast across Conv
    intro _scope _context _subject _classifier _reclassifier levelExpr flag _typed converts _reclassifierTyped
      ihTyped ihReclassifier
    intro _targetScope substitution _envLevels predLevel env
    have reclassifierMember := ihReclassifier substitution (predLevel + 1) env
    rw [subst_universeCodeCell] at reclassifierMember
    obtain ⟨_candidate, reclassifierReducible⟩ := reclassifierMember.tarskiDecode
    exact IsReducibleMemberAt.castAlongConvUnderSubst substitution
      (ihTyped substitution predLevel env) reclassifierReducible converts
  · -- piIntro: choice-free dependent Π-introduction.  Domain candidate from its IH one level up (tarskiDecode);
    -- CR1 supplies domain-members-are-SN; codomain + body run their IHs under the cons-extended environment,
    -- reshaped by the `subst_cons_eq_subst0_lift` keystone.
    intro _scope _context _domainCode _codomainCode _body _domainLevel _codomainLevel _flag
      _domainTyped _codomainTyped _bodyTyped ihDomain ihCodomain ihBody
    intro _targetScope substitution _envLevels predLevel env
    have domainMember := ihDomain substitution (predLevel + 1) env
    rw [subst_universeCodeCell] at domainMember
    obtain ⟨domainCandidate, domainReducible⟩ := domainMember.tarskiDecode
    refine IsReducibleMemberAt.abstractionCanonicalUnderSubst substitution domainReducible
      (fun _argument argumentInDomain =>
        domainReducible.isReducibilityCandidate.stronglyNormalizing argumentInDomain)
      (fun argument argumentInDomain => ?_) (fun argument argumentInDomain => ?_)
    · rw [← RawTerm.subst_cons_eq_subst0_lift _ argument substitution]
      have codomainMember := ihCodomain (RawTermSubst.cons argument substitution) (predLevel + 1)
        (ReducibleEnvVec.cons env ⟨domainCandidate, domainReducible, argumentInDomain⟩)
      rw [subst_universeCodeCell] at codomainMember
      exact codomainMember.tarskiDecode
    · rw [← RawTerm.subst_cons_eq_subst0_lift _ argument substitution,
        ← RawTerm.subst_cons_eq_subst0_lift _ argument substitution]
      exact ihBody (RawTermSubst.cons argument substitution) predLevel
        (ReducibleEnvVec.cons env ⟨domainCandidate, domainReducible, argumentInDomain⟩)
  · -- piElim: apply the function IH to the argument IH under the substitution
    intro _scope _context _functionTerm _argument _domainCode _codomainCode _functionTyped _argumentTyped
      ihFunction ihArgument
    intro _targetScope substitution _envLevels predLevel env
    exact IsReducibleMemberAt.applicationUnderSubst substitution
      (ihFunction substitution predLevel env) (ihArgument substitution predLevel env)
  · -- genFormationPi: dispatch the former membership from the telescope IH the recursor handed us
    -- (motive₂ on `premises`) — no companion recursion, no cast in a recursion body.  Π → toPiMember,
    -- Σ → toSigmaMember; non-Π/Σ generators refuted by `typingRuleDescOf = none`.
    intro _scope _context generator _payload children levels flag rule isFormation premises ihPremises
    intro _targetScope substitution _envLevels predLevel env
    by_cases isPiFormer : generator = .gen_piTyCode
    · subst isPiFormer
      obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
      match children with
      | .childCons _domainCode (.childCons _codomainCode .childNil) =>
          obtain ⟨_domainLevel, _codomainLevel, levelsShape⟩ := descTelescopePiTwoLevels premises
          subst levelsShape
          dsimp only [universeFormerOutput]
          rw [subst_universeCodeCell]
          exact (FormerChildrenReducible.ofTelescopeReducible predLevel
            (ihPremises substitution predLevel env Generator.gen_piTyCode_binderShifts_eq)).toPiMember
    · by_cases isSigmaFormer : generator = .gen_sigmaTyCode
      · subst isSigmaFormer
        obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
        match children with
        | .childCons _domainCode (.childCons _codomainCode .childNil) =>
            obtain ⟨_domainLevel, _codomainLevel, levelsShape⟩ := descTelescopePiTwoLevels premises
            subst levelsShape
            dsimp only [universeFormerOutput]
            rw [subst_universeCodeCell]
            exact (FormerChildrenReducible.ofTelescopeReducible predLevel
              (ihPremises substitution predLevel env Generator.gen_sigmaTyCode_binderShifts_eq)).toSigmaMember
      · exfalso
        unfold typingRuleDescOf at isFormation
        rw [if_neg isPiFormer, if_neg isSigmaFormer] at isFormation
        contradiction
  · -- DescTelescopePi.nil: the empty telescope is reducible at count 0 (TelescopeReducible reduces to True)
    intro _baseScope _currentDepth _context _flag
    intro _targetScope _substitution _envLevels _predLevel _env _shapeEq
    exact True.intro
  · -- DescTelescopePi.cons: head reducible (its IH), tail reducible under the cons-extended env (the tail
    -- IH); the shape witness collapses by proof irrelevance once `restShifts` is pinned (NOT in a recursion
    -- body, so the discharging `subst` is free).
    intro _baseScope currentDepth restShifts _context head _headLevel restLevels flag rest
      _headTyped _restTyped ihHead ihRest
    intro _targetScope substitution _envLevels predLevel env shapeEq
    simp only [List.length_cons, consecutiveShifts] at shapeEq
    obtain ⟨_, restShapeEq⟩ := List.cons.inj shapeEq
    subst restShapeEq
    refine ⟨fun level => ?_, fun {_memberLevel} argument argumentMember => ?_⟩
    · have headMember := ihHead substitution level env
      rwa [subst_universeCodeCell] at headMember
    · exact ihRest (RawTermSubst.cons argument substitution) predLevel
        (ReducibleEnvVec.cons env argumentMember) rfl

end FX1Poly.Typed

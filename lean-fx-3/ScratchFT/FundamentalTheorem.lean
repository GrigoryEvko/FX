import FX1Poly.Typed.ReducibleSemanticRules
import FX1Poly.Typed.ReducibleEnvVec
import FX1Poly.Typed.TelescopeReducible
import FX1Poly.Typed.FormerChildrenReducible

/-! # ScratchFT/FundamentalTheorem — WIP dedicated FT assembly (NOT in the lib build)

OUTSIDE the lib globs; built only via `lake env lean ScratchFT/FundamentalTheorem.lean`; kept UNTRACKED;
`sorry` is a transient scaffold (never committed to the lib).  Moved to `FX1Poly/Typed/` + gated + committed
green ONLY when the whole mutual block closes sorry-free.

THE TWO-FT DESIGN (resolves FX's non-cumulativity): two mutually-recursive fundamental theorems over the
SAME `HasTypeDescPi` derivation —
  * `fundamentalType`  : a universe-classified subject is a reducible TYPE at `predLevel + 1` (no `+1`
    membership recursion — this dissolves the cumulativity wall the conv/piIntro type-premises hit).
  * `fundamentalTerm`  : a well-typed subject is a reducible MEMBER of its classifier at `predLevel + 1`.
conv/piIntro call `fundamentalType` on their `Type@e` premises to get reducible types at the level directly.

LEVEL + SCOPE CONVENTION.  The level is fixed at `predLevel + 1` and the target scope at `targetScope + 1`
because the `piIntro` binder arm needs CR1 (`ReducibleTypeAt.isReducibilityCandidate`, the "members of a
reducible domain are strongly normalizing" leg), which is available ONLY at a positive level and a non-empty
scope (at level 0 the universe candidate is not a genuine CR; at the empty scope there is no variable to
feed neutral closure).  Both restrictions thread unchanged through every recursive call (substitution target
scope is invariant; the body recursion cons-extends the SOURCE scope only).

Term-mode STRUCTURAL recursion (`match typed with`) sidesteps the mutual-induction rejection.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- A depth-0 former telescope over the concrete two-child spine `childCons domain (childCons codomain
childNil)` has exactly a two-element level list.  Non-recursive (a standalone inversion, NOT part of the FT
mutual block), so casing `telescope` here is free of the FT's structural-recursion constraint; the child
spine fixes the index so the `nil` arms are refuted definitionally (no propext leak).  The `genFormationPi`
FT arm uses this to recover `levels = [domainLevel, codomainLevel]` WITHOUT casing the premise telescope
itself (which would rewrite the `fundamentalTelescope` recursive-call argument off the structural field). -/
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

mutual

/-- **Type-formation FT (WIP).**  A subject classified by a universe code is a reducible TYPE at
`predLevel + 1`.  General classifier + `classifierIsUniverse` equation (match-with-equation pattern) so each
arm sees the universe-classifier as a rewritable equation, not a unification constraint. -/
theorem HasTypeDescPi.fundamentalType {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {typeSubject classifier : RawTerm scope}
    {universeLevel : LevelExpr} {flag : UniverseFlag}
    {substitution : RawTermSubst scope (targetScope + 1)} {levels : Fin scope → Nat}
    (predLevel : Nat)
    (typed : HasTypeDescPi profile context typeSubject classifier)
    (classifierIsUniverse : classifier = universeCodeCell universeLevel flag)
    (env : ReducibleEnvVec levels context substitution) :
    IsReducibleTypeAt (predLevel + 1) (RawTerm.subst substitution typeSubject) :=
  match typed, classifierIsUniverse with
  | .ofFormation _formationTyped, _heq => sorry
  | .conv _levelExpr _flag typedPremise converts reclassifierTyped, heq => by
      -- Same structural shape as piElim: the subject is a member of its (inner) classifier — run the term IH
      -- on the SMALLER `typedPremise` one level up, cast it across the substituted conversion to the
      -- reclassifier (whose reducibility-as-a-type the type IH supplies from the SMALLER `reclassifierTyped`),
      -- rewrite that reclassifier to the universe via `classifierIsUniverse`, and `tarskiDecode` drops it to a
      -- reducible TYPE at `predLevel + 1`.  Structural — both IHs are on premises.
      obtain ⟨_candidateRight, reclassifierReducible⟩ :=
        HasTypeDescPi.fundamentalType (predLevel + 1) reclassifierTyped rfl env
      have castMember := IsReducibleMemberAt.castAlongConvUnderSubst substitution
        (HasTypeDescPi.fundamentalTerm (predLevel + 1) typedPremise env)
        reclassifierReducible converts
      rw [heq, subst_universeCodeCell] at castMember
      exact castMember.tarskiDecode
  | .piIntro _domainLevel _codomainLevel _flag _domainTyped _codomainTyped _bodyTyped, heq =>
      -- piIntro's classifier is `piTyCodeCell domainCode codomainCode`; the equation says it equals a
      -- `universeCodeCell` — impossible (distinct root generators).  A λ is never a type.
      absurd (congrArg RawTerm.rootGenerator heq)
        (by decide : Generator.gen_piTyCode ≠ Generator.gen_universeCode)
  | .piElim functionTyped argumentTyped, heq => by
      -- `F a : Type` (a type-valued application).  NOT a same-derivation cross-call: run the term IH on the
      -- SMALLER premises `functionTyped`/`argumentTyped` ONE LEVEL UP (param `predLevel + 1` → membership at
      -- `predLevel + 2`), apply (`applicationUnderSubst`) to land `F a` in the substituted codomain
      -- `subst0 codomainCode argument`, rewrite that classifier to the universe via the `classifierIsUniverse`
      -- equation, then `tarskiDecode` drops `F a ∈ Type@_` (at `predLevel + 2`) to a reducible TYPE at
      -- `predLevel + 1`.  Structural on the derivation — the level rises but the derivation strictly shrinks.
      have appMember := IsReducibleMemberAt.applicationUnderSubst substitution
        (HasTypeDescPi.fundamentalTerm (predLevel + 1) functionTyped env)
        (HasTypeDescPi.fundamentalTerm (predLevel + 1) argumentTyped env)
      rw [heq, subst_universeCodeCell] at appMember
      exact appMember.tarskiDecode
  | .genFormationPi _context _generator _payload _children _levels _flag _rule _isFormation _premises,
      _heq => sorry
termination_by structural typed

/-- **Term FT (WIP).**  A well-typed subject is a reducible member of its classifier at `predLevel + 1`. -/
theorem HasTypeDescPi.fundamentalTerm {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    {substitution : RawTermSubst scope (targetScope + 1)} {levels : Fin scope → Nat}
    (predLevel : Nat)
    (typed : HasTypeDescPi profile context subject classifier)
    (env : ReducibleEnvVec levels context substitution) :
    IsReducibleMemberAt (predLevel + 1)
      (RawTerm.subst substitution classifier) (RawTerm.subst substitution subject) :=
  match typed with
  | .ofFormation _formationTyped => sorry
  | .conv _levelExpr _flag typedPremise converts reclassifierTyped =>
      -- reclassifier : Type@e → fundamentalType (on the SMALLER reclassifierTyped) gives it as a reducible
      -- type at the level; castAlongConvUnderSubst transports the subject's membership across the
      -- substituted conversion.  No same-derivation cross-call here.
      let ⟨_candidateRight, reclassifierReducible⟩ :=
        HasTypeDescPi.fundamentalType predLevel reclassifierTyped rfl env
      IsReducibleMemberAt.castAlongConvUnderSubst substitution
        (HasTypeDescPi.fundamentalTerm predLevel typedPremise env)
        reclassifierReducible converts
  | .piIntro _domainLevel _codomainLevel _flag domainTyped codomainTyped bodyTyped =>
      -- The binder arm: dispatch to the choice-free dependent Π-introduction under the substitution.  The
      -- domain's fundamental-type IH gives its candidate + reducibility; CR1 supplies that domain members
      -- are strongly normalizing (`domainArgumentsSN` — available because the level is `predLevel + 1` and
      -- the target scope `targetScope + 1`).  For each reducible argument, the codomain / body premises run
      -- the IHs under the `cons`-extended env (the argument lands at variable 0 as a domain member), then
      -- the `subst_cons_eq_subst0_lift` keystone rewrites the `cons`-substitution output into the
      -- `subst0 (subst (lift …) …) argument` shape the dependent Π-introduction demands.
      let ⟨domainCandidate, domainReducible⟩ :=
        HasTypeDescPi.fundamentalType predLevel domainTyped rfl env
      IsReducibleMemberAt.abstractionCanonicalUnderSubst substitution
        domainReducible
        (fun _argument argumentInDomain =>
          domainReducible.isReducibilityCandidate.stronglyNormalizing argumentInDomain)
        (fun argument argumentInDomain => by
          rw [← RawTerm.subst_cons_eq_subst0_lift _ argument substitution]
          exact HasTypeDescPi.fundamentalType predLevel codomainTyped rfl
            (ReducibleEnvVec.cons env ⟨domainCandidate, domainReducible, argumentInDomain⟩))
        (fun argument argumentInDomain => by
          rw [← RawTerm.subst_cons_eq_subst0_lift _ argument substitution,
            ← RawTerm.subst_cons_eq_subst0_lift _ argument substitution]
          exact HasTypeDescPi.fundamentalTerm predLevel bodyTyped
            (ReducibleEnvVec.cons env ⟨domainCandidate, domainReducible, argumentInDomain⟩))
  | .piElim functionTyped argumentTyped =>
      IsReducibleMemberAt.applicationUnderSubst substitution
        (HasTypeDescPi.fundamentalTerm predLevel functionTyped env)
        (HasTypeDescPi.fundamentalTerm predLevel argumentTyped env)
  | .genFormationPi _context generator _payload children levels flag rule isFormation premises => by
      -- Dispatch the dependent type-former membership via the `fundamentalTelescope` companion (a direct
      -- `fundamentalTerm` on a cased telescope child does NOT pass structural recursion across the
      -- HasTypeDescPi / DescTelescopePi mutual boundary — verified — so the companion is load-bearing).
      by_cases isPiFormer : generator = .gen_piTyCode
      · subst isPiFormer
        obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
        match children with
        | .childCons _domainCode (.childCons _codomainCode .childNil) =>
            have telResult :=
              HasTypeDescPi.fundamentalTelescope (currentDepth := 0) (count := 2) predLevel
                Generator.gen_piTyCode_binderShifts_eq premises env
            obtain ⟨_domainLevel, _codomainLevel, levelsShape⟩ := descTelescopePiTwoLevels premises
            subst levelsShape
            dsimp only [universeFormerOutput]
            rw [subst_universeCodeCell]
            exact (FormerChildrenReducible.ofTelescopeReducible predLevel telResult).toPiMember
      · by_cases isSigmaFormer : generator = .gen_sigmaTyCode
        · subst isSigmaFormer
          obtain rfl : rule = { outputType := universeFormerOutput } := Option.some.inj isFormation.symm
          match children with
          | .childCons _domainCode (.childCons _codomainCode .childNil) =>
              have telResult :=
                HasTypeDescPi.fundamentalTelescope (currentDepth := 0) (count := 2) predLevel
                  Generator.gen_sigmaTyCode_binderShifts_eq premises env
              obtain ⟨_domainLevel, _codomainLevel, levelsShape⟩ := descTelescopePiTwoLevels premises
              subst levelsShape
              dsimp only [universeFormerOutput]
              rw [subst_universeCodeCell]
              exact (FormerChildrenReducible.ofTelescopeReducible predLevel telResult).toSigmaMember
        · exfalso
          unfold typingRuleDescOf at isFormation
          rw [if_neg isPiFormer, if_neg isSigmaFormer] at isFormation
          contradiction
termination_by structural typed

/-- The premise-telescope companion of the term FT: each child is a reducible member of its universe code,
the tail reducible under a `cons`-extended substitution.  Mutual with `fundamentalType`/`fundamentalTerm`.
Structural recursion across the mutual family requires `telescope`'s indices to be VARIABLES, so the child
`binderShifts` is a free variable plus a `shapeEq : binderShifts = consecutiveShifts currentDepth count`
witness (`rfl` / `gen_*TyCode_binderShifts_eq` at the call site); the conclusion transports `children` along
it.  The cast collapses by proof irrelevance once `shapeEq` is reduced to a reflexivity in each arm. -/
theorem HasTypeDescPi.fundamentalTelescope {profile : PolyProfile}
    {baseScope currentDepth count targetScope : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levelsList : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    {substitution : RawTermSubst (baseScope + currentDepth) (targetScope + 1)}
    {levels : Fin (baseScope + currentDepth) → Nat}
    (predLevel : Nat)
    (shapeEq : binderShifts = consecutiveShifts currentDepth count)
    (telescope : DescTelescopePi profile context levelsList flag children)
    (env : ReducibleEnvVec levels context substitution) :
    TelescopeReducible flag currentDepth count substitution levelsList (shapeEq ▸ children) := by
  cases telescope with
  | nil _context _flag =>
      cases count with
      | zero => trivial
      | succ _n => nomatch shapeEq
  | cons _context _head _headLevel _restLevels _flag _rest headTyped restTyped =>
      cases count with
      | zero => nomatch shapeEq
      | succ n =>
          dsimp only [consecutiveShifts] at shapeEq
          obtain ⟨_headShiftEq, restShapeEq⟩ := List.cons.inj shapeEq
          subst restShapeEq
          refine ⟨fun level => ?_, fun {_memberLevel} _argument argumentMember => ?_⟩
          · have headResult := HasTypeDescPi.fundamentalTerm level headTyped env
            rwa [subst_universeCodeCell] at headResult
          · exact HasTypeDescPi.fundamentalTelescope predLevel rfl restTyped
              (ReducibleEnvVec.cons env argumentMember)
termination_by structural telescope

end

end FX1Poly.Typed

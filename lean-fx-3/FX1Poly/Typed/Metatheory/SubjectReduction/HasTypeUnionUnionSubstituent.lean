import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.Union.HasTypeUnionFormationObligations
import FX1Poly.Typed.Engine.Union.HasTypeUnionSubstitution
import FX1Poly.Typed.Engine.Union.HasTypeUnionWeakening
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiSubstitution
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescSubstitution

/-! # FX1Poly/Typed/HasTypeUnionUnionSubstituent — TYTAB-2 W4: the UNION-SUBSTITUENT single- and
    two-binder substitution lemmas (discharging the β-family subject-reduction residuals)

The W2 wave shipped `HasTypeUnion.substRespectingContext` (substitution preserved along ANY HOST-typed
substitution).  For β / endpoint-β / the natElim·natRec succ rows the argument is only UNION-typed
(e.g. `fst pair` is union-typed at a universe but has NO host typing — the NATIVE-08 wall), so the
host-substituent formulation cannot supply it, and those subject-reduction rows took the substitution
transport (`UnionSubst0Transports` / `UnionSubstPairTransports`) as a RESIDUAL HYPOTHESIS, leaving the
rows conditional.

This file GENERALIZES the substituent discipline: substituent images may be UNION-typed
(`SubstUnionTyped`, the union mirror of `SubstHostTyped`).  Then the β-family transports become genuine
INSTANCES, discharging the residuals.

## The honest residual (precisely named, NOT faked)

The ONE arm that does not close generically is the cumulative-formation-former arm
(`HasTypeDescPi.genFormationPi` / `HasTypeDesc.genFormation`) at the four cumulative type-code formers
`gen_piTyCode` / `gen_sigmaTyCode` / `gen_listCode` / `gen_optionCode` (the `typingRuleDescOf` table,
EXCLUDING the nullary `gen_unitCode` which is a `formationRule` base-type row).  These four formers are
NOT in the union's `formationRuleOf` table (`flatTypingRuleDescOf` covers
arrow/product/sum/either/equiv/modalities, not pi/sigma/list/option), so a substituted former whose
child carries a UNION-ONLY image cannot be rebuilt — there is no union→grown reflection at universe
codes.  This is EXACTLY the documented `UnionDataFormerValidity` wall (HasTypeUnionValidity.lean): a
permanently-isolated residual, never discharged anywhere, the price of the seed union deliberately
omitting these four rows from its native formation table to keep consistency (the
`typingRuleDescOf_*_none` partition).

We isolate it as the single named oracle `UnionCumulativeFormerCloses`: given the substituted children
union-typed at their universe codes (which the IH delivers), the substituted cumulative former is
union-typed at its substituted output.  Threaded through `hostSubstWithUnionImages` exactly as
`HasTypeUnion.classifierIsType` threads `dataFormers`.  Every OTHER host and union arm — var leaf,
universe leaf, conv, piIntro (λ), piElim (app), the base-type / flat / term-indexed formation families
through `formationRuleOfObligations`, and the union intro / elim / formationRule / conv arms — closes
UNCONDITIONALLY through the union's own arms.

## Zero-axiom

`match` / `induction` over the host and union derivations + the cell-subst `rfl` commutations + the
`FormationRule.obligations_pushSubst` obligation push + `HasTypeUnion.weakenUnderBinding` for the
binder-lift + `Conv.subst` + `RawTerm.subst0_subst_commute`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditUnionSubstitution.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax FX1Poly.Modal

/-- **The union-substituent context condition.**  Every variable image is UNION-typed at the substituted
lookup type — the union mirror of `HasTypeUnion.SubstHostTyped`, weakening the requirement from
`HasTypeDescPi` to `HasTypeUnion` (every host image is a union image via `ofGrown`, so this condition is
strictly weaker, the one β needs). -/
abbrev HasTypeUnion.SubstUnionTyped {profile : PolyProfile} {sourceScope targetScope : Nat}
    (sourceContext : TypingContext profile sourceScope)
    (targetContext : TypingContext profile targetScope)
    (substitution : RawTermSubst sourceScope targetScope) : Prop :=
  ∀ index : Fin sourceScope,
    HasTypeUnion profile targetContext (substitution index)
      (RawTerm.subst substitution (sourceContext.lookup index))

/-- **The one-binder lift of the union-substituent condition.**  If `substitution`'s images are
union-typed at the substituted source bindings, then its single lift's images are union-typed at the
context extended by `domainCode` (substituted).  The union mirror of `substContextCondition_cons`: `0`
resolves to the fresh `var` (via `ofGrown ∘ ofFormation`), `k+1` to the base union image weakened
(`HasTypeUnion.weakenUnderBinding`). -/
theorem HasTypeUnion.SubstUnionTyped.cons {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (domainCode : RawTerm sourceScope) (substitution : RawTermSubst sourceScope targetScope)
    (condition : HasTypeUnion.SubstUnionTyped sourceContext targetContext substitution) :
    HasTypeUnion.SubstUnionTyped (sourceContext.cons domainCode)
      (targetContext.cons (RawTerm.subst substitution domainCode))
      (iterateLiftRaw substitution 1) := by
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show HasTypeUnion profile
        (targetContext.cons (RawTerm.subst substitution domainCode))
        (RawTermSubst.lift substitution ⟨0, indexBound⟩)
        (RawTerm.subst (RawTermSubst.lift substitution)
          ((sourceContext.cons domainCode).lookup ⟨0, indexBound⟩))
      rw [TypingContext.lookup_cons_zero, subst_lift_weaken_commute]
      exact HasTypeUnion.ofGrown
        (HasTypeDescPi.ofFormation
          (HasTypeDesc.var
            (targetContext.cons (RawTerm.subst substitution domainCode))
            ⟨0, Nat.succ_pos _⟩))
  | succ priorValue =>
      show HasTypeUnion profile
        (targetContext.cons (RawTerm.subst substitution domainCode))
        (RawTermSubst.lift substitution ⟨priorValue + 1, indexBound⟩)
        (RawTerm.subst (RawTermSubst.lift substitution)
          ((sourceContext.cons domainCode).lookup ⟨priorValue + 1, indexBound⟩))
      rw [TypingContext.lookup_cons_succ, subst_lift_weaken_commute]
      exact (condition ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding
        (RawTerm.subst substitution domainCode)

/-- **The two-binder lift of the union-substituent condition** (the recursiveElim / idJ succ-branch
shape): the double lift of a union condition is a union condition at the context extended by the two
domains.  An iterate of `SubstUnionTyped.cons` — the union mirror of
`HasTypeUnion.SubstHostTyped.consTwice`. -/
theorem HasTypeUnion.SubstUnionTyped.consTwice {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (outerType : RawTerm sourceScope) (innerType : RawTerm (sourceScope + 1))
    {substitution : RawTermSubst sourceScope targetScope}
    (condition : HasTypeUnion.SubstUnionTyped sourceContext targetContext substitution) :
    HasTypeUnion.SubstUnionTyped ((sourceContext.cons outerType).cons innerType)
      ((targetContext.cons (RawTerm.subst substitution outerType)).cons
        (RawTerm.subst (iterateLiftRaw substitution 1) innerType))
      (iterateLiftRaw substitution 2) :=
  HasTypeUnion.SubstUnionTyped.cons innerType (iterateLiftRaw substitution 1)
    (HasTypeUnion.SubstUnionTyped.cons outerType substitution condition)

/-- **The union-typed formation telescope.**  The children form a cumulative dependent telescope of
TYPES at `levels`, each head typed by `HasTypeUnion` (so children may be UNION terms — applications,
projections, nested formers — not only host terms).  The union mirror of `DescTelescopePi`, with the same
fixed-`baseScope` / growing-`currentDepth` rebasing discipline.  Its index signature references only
`PolyProfile` / `Nat` / `List Nat` / `LevelExpr` / `UniverseFlag` / `TypingContext` / `RawTermChildren`,
never `HasTypeUnionOver`, and `HasTypeUnion` appears only POSITIVELY in `cons`'s `headTyped` (so it is
strictly positive). -/
inductive DescTelescopeUnion (profile : PolyProfile) :
    {baseScope : Nat} → {currentDepth : Nat} → {binderShifts : List Nat} →
      TypingContext profile (baseScope + currentDepth) →
      List LevelExpr → UniverseFlag →
      RawTermChildren binderShifts baseScope → Prop where
  | nil {baseScope : Nat} {currentDepth : Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (flag : UniverseFlag) :
      DescTelescopeUnion profile context [] flag .childNil
  | cons {baseScope : Nat} {currentDepth : Nat} {restShifts : List Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (head : RawTerm (baseScope + currentDepth))
      (headLevel : LevelExpr) (restLevels : List LevelExpr) (flag : UniverseFlag)
      (rest : RawTermChildren restShifts baseScope)
      (headTyped :
        HasTypeUnion profile context head (universeCodeCell headLevel flag))
      (restTyped :
        DescTelescopeUnion profile (currentDepth := currentDepth + 1)
          (context.cons head) restLevels flag rest) :
      DescTelescopeUnion profile context (headLevel :: restLevels) flag
        (.childCons head rest)

/-! ## The honest residual oracle — the cumulative-formation-former wall

`hostSubstWithUnionImages` substitutes UNION images into a host `HasTypeDescPi` derivation.  Every arm
closes through the union's own arms EXCEPT the cumulative-formation-former arm
(`HasTypeDescPi.genFormationPi` / `HasTypeDesc.genFormation`) at the four `typingRuleDescOf` cumulative
codes `gen_piTyCode` / `gen_sigmaTyCode` / `gen_listCode` / `gen_optionCode` — these are NOT in the
union's `formationRuleOf` table, and there is no union→grown reflection at universe codes (the documented
`UnionDataFormerValidity` wall).  We isolate it as ONE oracle: given the substituted children union-typed
at their universe-code premises (which the IH delivers, threaded as a `DescTelescopePi` whose heads now
carry union typings), the substituted cumulative former is union-typed at its substituted output.

The oracle's hypothesis is precisely the per-child union typing the companion telescope recursion would
deliver: a function delivering, for each child of the cumulative former, its substituted union typing at
its level's universe code (the union mirror of `DescTelescopePi`'s `headTyped` premises).  Everything else
in `hostSubstWithUnionImages` is shipped and unconditional. -/

/-- **The cumulative-formation-former closing oracle.**  For any generator carrying a `typingRuleDescOf`
cumulative formation rule (`gen_piTyCode` / `gen_sigmaTyCode` / `gen_listCode` / `gen_optionCode` /
`gen_unitCode`), given a children spine each child of which is union-typed at its level's universe code
(in the per-child context the dependent telescope pins), the former `.mkGen generator payload children`
is union-typed at the rule's output universe.

This is the SOLE residual of `hostSubstWithUnionImages`: the four non-nullary cumulative codes are absent
from the union's native formation table, so a former whose child carries a union-only image cannot be
rebuilt natively.  Identical in spirit to `UnionDataFormerValidity` (HasTypeUnionValidity.lean): a
precisely-named oracle, never witnessed, the price of the seed union omitting these rows.  An instance is
the `genFormationPi` reconstruction once the union grows a formation route (NATIVE-46 / the conv-closure
work) for these four codes. -/
abbrev UnionCumulativeFormerCloses (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} (context : TypingContext profile scope)
    (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope)
    (levels : List LevelExpr) (flag : UniverseFlag) (rule : TypingRuleDesc),
    typingRuleDescOf generator = some rule →
    DescTelescopeUnion profile (currentDepth := 0) context levels flag children →
    HasTypeUnion profile context (.mkGen generator payload children)
      (rule.outputType scope levels flag)

/-! ## The base-engine leg: substitute a FORMATION derivation under union images

`baseFormationSubstWithUnionImages` carries a `HasTypeDesc` derivation along a substitution whose images
are UNION-typed, landing in `HasTypeUnion`.  The `ofFormation` leg the grown union substitution rests on:
a formation subject substituted by a union substitution is in general neither a formation term nor a host
term (a child may become a union-only image), so it retypes in the UNION.  Mutual with the companion
telescope substitution producing a `DescTelescopeUnion`.  The var leaf returns the union image; the
universe leaf re-embeds via `ofGrown`; `conv` recurses + `Conv.subst`; `genFormation` substitutes the
spine through the companion and closes via the residual oracle. -/

mutual

/-- Substitute a FORMATION derivation under a UNION-image substitution, producing a UNION derivation.
Mutual structural recursion on the FORMATION derivation; the genFormation case substitutes the spine
through the companion (producing a `DescTelescopeUnion`) and closes via the cumulative-former oracle. -/
theorem baseFormationSubstWithUnionImages {profile : PolyProfile}
    (formerCloses : UnionCumulativeFormerCloses profile)
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDesc profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      HasTypeUnion.SubstUnionTyped sourceContext targetContext substitution →
      HasTypeUnion profile targetContext
        (RawTerm.subst substitution subject)
        (RawTerm.subst substitution classifier) :=
  match derivation with
  | .var _sourceContext index => fun _targetContext substitution substitutionTyped => by
      rw [subst_variableCell]
      exact substitutionTyped index
  | .conv levelExpr flag typedPremise converts reclassifierTyped =>
      fun targetContext substitution substitutionTyped => by
        have premiseTyped :=
          baseFormationSubstWithUnionImages formerCloses typedPremise targetContext substitution
            substitutionTyped
        have reclassifierTypedSubst :=
          baseFormationSubstWithUnionImages formerCloses reclassifierTyped targetContext substitution
            substitutionTyped
        rw [subst_universeCodeCell] at reclassifierTypedSubst
        exact HasTypeUnion.conv levelExpr flag premiseTyped
          (Conv.subst substitution converts) reclassifierTypedSubst
  | .universeFormation _sourceContext levelExpr flag =>
      fun targetContext substitution _substitutionTyped => by
        rw [subst_universeCodeCell, subst_universeCodeCell]
        exact HasTypeUnion.ofGrown
          (HasTypeDescPi.ofFormation
            (HasTypeDesc.universeFormation targetContext levelExpr flag))
  | .genFormation _sourceContext generator payload children levels flag rule
      isFormation premises => fun targetContext substitution substitutionTyped => by
      have substPremises :=
        baseTelescopeSubstWithUnionImages formerCloses premises targetContext substitution
          substitutionTyped
      have hNotVar : generator ≠ Generator.gen_var := formationRuleImpliesNotVariable isFormation
      rw [typingRuleDescOf_output_substStable isFormation substitution levels flag,
        RawTerm.subst_mkGen_of_ne_var substitution hNotVar]
      exact formerCloses targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.subst substitution children) levels flag rule isFormation substPremises

/-- Companion: substitute a FORMATION premise spine under union images, producing a `DescTelescopeUnion`.
Head via `baseFormationSubstWithUnionImages` (reshaped to the universe code); tail under the binder with
the LIFTED union condition (`0` → the fresh `var` via `ofGrown ∘ ofFormation`; `k+1` → the union image
weakened via `HasTypeUnion.weakenUnderBinding`). -/
theorem baseTelescopeSubstWithUnionImages {profile : PolyProfile}
    (formerCloses : UnionCumulativeFormerCloses profile)
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile sourceContext levels flag children) :
    ∀ {targetBaseScope : Nat}
      (targetContext : TypingContext profile (targetBaseScope + currentDepth))
      (substitution : RawTermSubst baseScope targetBaseScope),
      (∀ index : Fin (baseScope + currentDepth),
        HasTypeUnion profile targetContext
          (iterateLiftRaw substitution currentDepth index)
          (RawTerm.subst (iterateLiftRaw substitution currentDepth)
            (sourceContext.lookup index))) →
      DescTelescopeUnion profile targetContext levels flag
        (RawTermChildren.subst substitution children) :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _substitution _substitutionTyped =>
      DescTelescopeUnion.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext substitution substitutionTyped => by
        have substHeadTyped :
            HasTypeUnion profile targetContext
              (RawTerm.subst (iterateLiftRaw substitution currentDepth) head)
              (universeCodeCell headLevel flag) := by
          have headSubst :=
            baseFormationSubstWithUnionImages formerCloses headTyped targetContext
              (iterateLiftRaw substitution currentDepth) substitutionTyped
          rwa [subst_universeCodeCell] at headSubst
        refine DescTelescopeUnion.cons targetContext
          (RawTerm.subst (iterateLiftRaw substitution currentDepth) head) headLevel
          restLevels flag (RawTermChildren.subst substitution rest) substHeadTyped ?_
        refine baseTelescopeSubstWithUnionImages formerCloses restTyped
          (targetContext.cons
            (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
          substitution ?_
        intro index
        obtain ⟨indexValue, indexBound⟩ := index
        cases indexValue with
        | zero =>
            show HasTypeUnion profile
              (targetContext.cons
                (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
              (RawTermSubst.lift (iterateLiftRaw substitution currentDepth) ⟨0, indexBound⟩)
              (RawTerm.subst (RawTermSubst.lift (iterateLiftRaw substitution currentDepth))
                ((_sourceContext.cons head).lookup ⟨0, indexBound⟩))
            rw [TypingContext.lookup_cons_zero, subst_lift_weaken_commute]
            exact HasTypeUnion.ofGrown
              (HasTypeDescPi.ofFormation
                (HasTypeDesc.var
                  (targetContext.cons
                    (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
                  ⟨0, Nat.succ_pos _⟩))
        | succ priorValue =>
            show HasTypeUnion profile
              (targetContext.cons
                (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
              (RawTermSubst.lift (iterateLiftRaw substitution currentDepth)
                ⟨priorValue + 1, indexBound⟩)
              (RawTerm.subst (RawTermSubst.lift (iterateLiftRaw substitution currentDepth))
                ((_sourceContext.cons head).lookup ⟨priorValue + 1, indexBound⟩))
            rw [TypingContext.lookup_cons_succ, subst_lift_weaken_commute]
            exact (substitutionTyped ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding
              (RawTerm.subst (iterateLiftRaw substitution currentDepth) head)

end

/-! ## The grown-engine leg: substitute a HOST `HasTypeDescPi` derivation under union images

`hostSubstWithUnionImages` carries a `HasTypeDescPi` derivation along a union-image substitution, landing
in `HasTypeUnion`.  Mirrors the host `HasTypeDescPi.substRespectingContext`'s five arms — except
`ofFormation` routes through the COMPLETED `baseFormationSubstWithUnionImages` (returning a union
derivation), `piIntro` rebuilds the λ via the union `intro` arm at `gen_lam`, `piElim` rebuilds the app
via the union `elim` arm at `gen_app`, and `genFormationPi` closes the cumulative former through the
residual oracle.  Mutual with the companion telescope substitution producing a `DescTelescopeUnion`. -/

mutual

/-- **★ Substitute a HOST `HasTypeDescPi` derivation under UNION images, landing in `HasTypeUnion`.**  The
union-image generalization of `HasTypeDescPi.substRespectingContext` — the `ofGrown` leg of the union
substitution lemma.  Substituent images may be UNION-typed (the `SubstUnionTyped` condition), so the
result lands in `HasTypeUnion`.  The sole residual is the cumulative-former oracle `formerCloses`,
consumed ONLY at the `genFormationPi` arm. -/
theorem hostSubstWithUnionImages {profile : PolyProfile}
    (formerCloses : UnionCumulativeFormerCloses profile)
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeDescPi profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      HasTypeUnion.SubstUnionTyped sourceContext targetContext substitution →
      HasTypeUnion profile targetContext
        (RawTerm.subst substitution subject)
        (RawTerm.subst substitution classifier) :=
  match derivation with
  | .ofFormation formationTyped => fun targetContext substitution substitutionTyped =>
      baseFormationSubstWithUnionImages formerCloses formationTyped targetContext substitution
        substitutionTyped
  | .conv levelExpr flag typed converts reclassifierTyped =>
      fun targetContext substitution substitutionTyped => by
        have typedSubst :=
          hostSubstWithUnionImages formerCloses typed targetContext substitution substitutionTyped
        have reclassifierSubst :=
          hostSubstWithUnionImages formerCloses reclassifierTyped targetContext substitution
            substitutionTyped
        rw [subst_universeCodeCell] at reclassifierSubst
        exact HasTypeUnion.conv levelExpr flag typedSubst
          (Conv.subst substitution converts) reclassifierSubst
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => fun targetContext substitution substitutionTyped => by
      have liftedCondition :
          HasTypeUnion.SubstUnionTyped (sourceContext.cons domainCode)
            (targetContext.cons (RawTerm.subst substitution domainCode))
            (iterateLiftRaw substitution 1) :=
        HasTypeUnion.SubstUnionTyped.cons domainCode substitution substitutionTyped
      have domainSubst :=
        hostSubstWithUnionImages formerCloses domainTyped targetContext substitution substitutionTyped
      rw [subst_universeCodeCell] at domainSubst
      have codomainSubst :=
        hostSubstWithUnionImages formerCloses codomainTyped
          (targetContext.cons (RawTerm.subst substitution domainCode))
          (iterateLiftRaw substitution 1) liftedCondition
      rw [subst_universeCodeCell] at codomainSubst
      have bodySubst :=
        hostSubstWithUnionImages formerCloses bodyTyped
          (targetContext.cons (RawTerm.subst substitution domainCode))
          (iterateLiftRaw substitution 1) liftedCondition
      show HasTypeUnion profile targetContext
        (RawTerm.subst substitution (lamCell domainCode body))
        (RawTerm.subst substitution (piTyCodeCell domainCode codomainCode))
      rw [subst_lamCell, subst_piTyCodeCell]
      refine HasTypeUnion.intro targetContext .gen_lam lamIntroRule
        (.childCons (RawTerm.subst substitution domainCode)
          (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) body) .childNil))
        (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) codomainCode) .childNil)
        domainLevel codomainLevel flag rfl trivial ?_
      intro obligation hmem
      cases hmem with
      | head => exact domainSubst
      | tail _ hmem => cases hmem with
        | head => exact codomainSubst
        | tail _ hmem => cases hmem with
          | head => exact bodySubst
          | tail _ hmem => cases hmem
  | @HasTypeDescPi.piElim _ _ _ functionTerm argument domainCode codomainCode
      functionTyped argumentTyped => fun targetContext substitution substitutionTyped => by
      have functionSubst :=
        hostSubstWithUnionImages formerCloses functionTyped targetContext substitution
          substitutionTyped
      rw [subst_piTyCodeCell] at functionSubst
      have argumentSubst :=
        hostSubstWithUnionImages formerCloses argumentTyped targetContext substitution
          substitutionTyped
      show HasTypeUnion profile targetContext
        (RawTerm.subst substitution (appCell functionTerm argument))
        (RawTerm.subst substitution (RawTerm.subst0 codomainCode argument))
      rw [subst_appCell, RawTerm.subst0_subst_commute]
      refine HasTypeUnion.elim targetContext .gen_app appElimRule
        (.childCons (RawTerm.subst substitution functionTerm)
          (.childCons (RawTerm.subst substitution argument) .childNil))
        (.childCons (RawTerm.subst substitution domainCode)
          (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) codomainCode) .childNil))
        rfl ?_
      intro obligation hmem
      cases hmem with
      | head => exact functionSubst
      | tail _ hmem => cases hmem with
        | head => exact argumentSubst
        | tail _ hmem => cases hmem
  | .genFormationPi _sourceContext generator payload children levels flag rule
      isFormation premises => fun targetContext substitution substitutionTyped => by
      have substPremises :=
        hostTelescopeSubstWithUnionImages formerCloses premises targetContext substitution
          substitutionTyped
      have hNotVar : generator ≠ Generator.gen_var := formationRuleImpliesNotVariable isFormation
      rw [typingRuleDescOf_output_substStable isFormation substitution levels flag,
        RawTerm.subst_mkGen_of_ne_var substitution hNotVar]
      exact formerCloses targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.subst substitution children) levels flag rule isFormation substPremises

/-- Companion: substitute a GROWN premise spine under union images, producing a `DescTelescopeUnion`.  The
grown mirror of `baseTelescopeSubstWithUnionImages`, with the head recursing the grown engine. -/
theorem hostTelescopeSubstWithUnionImages {profile : PolyProfile}
    (formerCloses : UnionCumulativeFormerCloses profile)
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile sourceContext levels flag children) :
    ∀ {targetBaseScope : Nat}
      (targetContext : TypingContext profile (targetBaseScope + currentDepth))
      (substitution : RawTermSubst baseScope targetBaseScope),
      (∀ index : Fin (baseScope + currentDepth),
        HasTypeUnion profile targetContext
          (iterateLiftRaw substitution currentDepth index)
          (RawTerm.subst (iterateLiftRaw substitution currentDepth)
            (sourceContext.lookup index))) →
      DescTelescopeUnion profile targetContext levels flag
        (RawTermChildren.subst substitution children) :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _substitution _substitutionTyped =>
      DescTelescopeUnion.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext substitution substitutionTyped => by
        have substHeadTyped :
            HasTypeUnion profile targetContext
              (RawTerm.subst (iterateLiftRaw substitution currentDepth) head)
              (universeCodeCell headLevel flag) := by
          have headSubst :=
            hostSubstWithUnionImages formerCloses headTyped targetContext
              (iterateLiftRaw substitution currentDepth) substitutionTyped
          rwa [subst_universeCodeCell] at headSubst
        refine DescTelescopeUnion.cons targetContext
          (RawTerm.subst (iterateLiftRaw substitution currentDepth) head) headLevel
          restLevels flag (RawTermChildren.subst substitution rest) substHeadTyped ?_
        refine hostTelescopeSubstWithUnionImages formerCloses restTyped
          (targetContext.cons
            (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
          substitution ?_
        intro index
        obtain ⟨indexValue, indexBound⟩ := index
        cases indexValue with
        | zero =>
            show HasTypeUnion profile
              (targetContext.cons
                (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
              (RawTermSubst.lift (iterateLiftRaw substitution currentDepth) ⟨0, indexBound⟩)
              (RawTerm.subst (RawTermSubst.lift (iterateLiftRaw substitution currentDepth))
                ((_sourceContext.cons head).lookup ⟨0, indexBound⟩))
            rw [TypingContext.lookup_cons_zero, subst_lift_weaken_commute]
            exact HasTypeUnion.ofGrown
              (HasTypeDescPi.ofFormation
                (HasTypeDesc.var
                  (targetContext.cons
                    (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
                  ⟨0, Nat.succ_pos _⟩))
        | succ priorValue =>
            show HasTypeUnion profile
              (targetContext.cons
                (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
              (RawTermSubst.lift (iterateLiftRaw substitution currentDepth)
                ⟨priorValue + 1, indexBound⟩)
              (RawTerm.subst (RawTermSubst.lift (iterateLiftRaw substitution currentDepth))
                ((_sourceContext.cons head).lookup ⟨priorValue + 1, indexBound⟩))
            rw [TypingContext.lookup_cons_succ, subst_lift_weaken_commute]
            exact (substitutionTyped ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding
              (RawTerm.subst (iterateLiftRaw substitution currentDepth) head)

end

/-! ## ★ The pointwise UNION-substituent substitution lemma over the native union

The union-image generalization of `HasTypeUnion.substRespectingContext`: a union derivation, substituted
by ANY UNION-typed substitution, gives a union derivation of the substituted subject at the substituted
classifier.  By `induction` over the 5 union arms — IDENTICAL to `substRespectingContext` EXCEPT the
condition is `SubstUnionTyped` (so the binder lifts are `SubstUnionTyped.cons`/`consTwice` and the leaf
images are union typings), and the `ofGrown` arm routes through `hostSubstWithUnionImages` (the host
derivation substituted under union images) instead of the host engine's own substitution.  The
`formationRule` / `intro` / `elim` / `conv` arms are unchanged — they thread their premises entirely
through `ihPremises` and the lifts, agnostic to the image typing.  The sole residual is `formerCloses`,
consumed only at the `ofGrown` arm's cumulative-former leg. -/
theorem HasTypeUnion.substRespectingContextUnionImages {profile : PolyProfile}
    (formerCloses : UnionCumulativeFormerCloses profile)
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeUnion profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      HasTypeUnion.SubstUnionTyped sourceContext targetContext substitution →
      HasTypeUnion profile targetContext
        (RawTerm.subst substitution subject)
        (RawTerm.subst substitution classifier) := by
  induction derivation with
  | conv levelExpr flag typed converts reclassifierTyped typedIH reclassifierIH =>
      intro targetScope targetContext substitution condition
      have typedSubst := typedIH targetContext substitution condition
      have reclassifierSubst := reclassifierIH targetContext substitution condition
      rw [subst_universeCodeCell] at reclassifierSubst
      exact HasTypeUnion.conv levelExpr flag typedSubst
        (Conv.subst substitution converts) reclassifierSubst
  | ofGrown hostTyped =>
      intro targetScope targetContext substitution condition
      exact hostSubstWithUnionImages formerCloses hostTyped targetContext substitution condition
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      premisesHold ihPremises =>
      intro targetScope targetContext substitution condition
      cases rule with
      | baseType baseRule =>
          have isBaseType : baseTypeRuleDescOf generator = some baseRule :=
            formationRuleOf_baseType_inv isFormationRule
          have hNotVar : generator ≠ Generator.gen_var := baseTypeRuleImpliesNotVariable isBaseType
          dsimp only [FormationRule.outputType]
          rw [RawTerm.subst_mkGen_of_ne_var substitution hNotVar,
            baseTypeRuleDescOf_outputSubstStable isBaseType substitution]
          exact HasTypeUnion.formationRule targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.subst substitution children) (.baseType baseRule)
            levels (RawTerm.subst substitution carrier) level flag isFormationRule trivial
      | flat flatRule =>
          have isFlatFormation : flatTypingRuleDescOf generator = some flatRule :=
            formationRuleOf_flat_inv isFormationRule
          have hNotVar : generator ≠ Generator.gen_var :=
            flatFormationRuleImpliesNotVariable isFlatFormation
          obtain rfl : flatRule = { outputType := universeFormerOutput } :=
            flatFormationRuleIsUniverseFormer isFlatFormation
          dsimp only [FormationRule.outputType, universeFormerOutput]
          rw [subst_universeCodeCell, RawTerm.subst_mkGen_of_ne_var substitution hNotVar]
          exact HasTypeUnion.formationRuleOfObligations targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.subst substitution children)
            (.flat { outputType := universeFormerOutput })
            levels (RawTerm.subst substitution carrier) level flag isFormationRule
            (FormationRule.obligations_pushSubst (.flat { outputType := universeFormerOutput })
              targetContext substitution children levels carrier level flag
              (fun subject classifier member =>
                ihPremises _ member targetContext substitution condition))
      | termIndexed termRule =>
          have isTermIndexed : termIndexedFormerDescOf generator = some termRule :=
            formationRuleOf_termIndexed_inv isFormationRule
          have hNotVar : generator ≠ Generator.gen_var :=
            termIndexedFormerRuleImpliesNotVariable isTermIndexed
          obtain rfl : termRule = { outputType := termIndexedCarrierOutput } :=
            termIndexedFormerRuleIsCarrierOutput isTermIndexed
          dsimp only [FormationRule.outputType, termIndexedCarrierOutput]
          rw [subst_universeCodeCell, RawTerm.subst_mkGen_of_ne_var substitution hNotVar]
          exact HasTypeUnion.formationRuleOfObligations targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.subst substitution children)
            (.termIndexed { outputType := termIndexedCarrierOutput })
            levels (RawTerm.subst substitution carrier) level flag isFormationRule
            (FormationRule.obligations_pushSubst (.termIndexed { outputType := termIndexedCarrierOutput })
              targetContext substitution children levels carrier level flag
              (fun subject classifier member =>
                ihPremises _ member targetContext substitution condition))
  | elim context generator rule args params isElim premisesHold ihPremises =>
      intro targetScope targetContext substitution condition
      have isElimUnwrapped : elimRuleOf generator = some rule := isElim
      rcases elimRuleOf_cases isElimUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- app row
      · match args, params with
        | .childCons eliminated (.childCons argument .childNil),
          .childCons typeParamA (.childCons typeParamB .childNil) =>
          have eliminatedSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have argumentSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          rw [subst_piTyCodeCell] at eliminatedSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (appCell eliminated argument))
            (RawTerm.subst substitution (RawTerm.subst0 typeParamB argument))
          rw [subst_appCell, RawTerm.subst0_subst_commute]
          refine HasTypeUnion.elim targetContext .gen_app appElimRule
            (.childCons (RawTerm.subst substitution eliminated)
              (.childCons (RawTerm.subst substitution argument) .childNil))
            (.childCons (RawTerm.subst substitution typeParamA)
              (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) typeParamB) .childNil))
            rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact eliminatedSubst
          | tail _ hmem => cases hmem with
            | head => exact argumentSubst
            | tail _ hmem => cases hmem
      -- pathApp row
      · match args, params with
        | .childCons eliminated (.childCons argument .childNil),
          .childCons typeParamA (.childCons typeParamC (.childCons typeParamD .childNil)) =>
          have eliminatedSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have argumentSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          rw [subst_bridgeTypeCell] at eliminatedSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (pathAppCell eliminated argument))
            (RawTerm.subst substitution typeParamA)
          rw [subst_pathAppCell]
          refine HasTypeUnion.elim targetContext .gen_pathApp pathAppElimRule
            (.childCons (RawTerm.subst substitution eliminated)
              (.childCons (RawTerm.subst substitution argument) .childNil))
            (.childCons (RawTerm.subst substitution typeParamA)
              (.childCons (RawTerm.subst substitution typeParamC)
                (.childCons (RawTerm.subst substitution typeParamD) .childNil)))
            rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact eliminatedSubst
          | tail _ hmem => cases hmem with
            | head => exact argumentSubst
            | tail _ hmem => cases hmem
      -- natElim row
      · match args, params with
        | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))),
          .childCons resultType .childNil =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have baseBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have stepLiftedCondition :=
            HasTypeUnion.SubstUnionTyped.consTwice natTypeCell
              (RawTerm.weaken resultType) condition
          have stepBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) _
              (iterateLiftRaw substitution 2) stepLiftedCondition
          rw [subst_natTypeCell] at scrutineeSubst
          dsimp only [RawTerm.weaken] at stepBranchSubst
          rw [subst_iterateLift_one_renameWeaken_commute,
            subst_iterateLift_two_weaken_weaken_commute] at stepBranchSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (natElimCell motive baseBranch stepBranch scrutinee))
            (RawTerm.subst substitution resultType)
          rw [subst_natElimCell]
          refine HasTypeUnion.elim targetContext .gen_natElim natElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution baseBranch)
                (.childCons (RawTerm.subst (iterateLiftRaw substitution 2) stepBranch)
                  (.childCons (RawTerm.subst substitution scrutinee) .childNil))))
            (.childCons (RawTerm.subst substitution resultType) .childNil) rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact baseBranchSubst
            | tail _ hmem => cases hmem with
              | head => exact stepBranchSubst
              | tail _ hmem => cases hmem
      -- natRec row
      · match args, params with
        | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))),
          .childCons resultType .childNil =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have baseBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have stepLiftedCondition :=
            HasTypeUnion.SubstUnionTyped.consTwice natTypeCell
              (RawTerm.weaken resultType) condition
          have stepBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) _
              (iterateLiftRaw substitution 2) stepLiftedCondition
          rw [subst_natTypeCell] at scrutineeSubst
          dsimp only [RawTerm.weaken] at stepBranchSubst
          rw [subst_iterateLift_one_renameWeaken_commute,
            subst_iterateLift_two_weaken_weaken_commute] at stepBranchSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (natRecCell motive baseBranch stepBranch scrutinee))
            (RawTerm.subst substitution resultType)
          rw [subst_natRecCell]
          refine HasTypeUnion.elim targetContext .gen_natRec natRecElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution baseBranch)
                (.childCons (RawTerm.subst (iterateLiftRaw substitution 2) stepBranch)
                  (.childCons (RawTerm.subst substitution scrutinee) .childNil))))
            (.childCons (RawTerm.subst substitution resultType) .childNil) rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact baseBranchSubst
            | tail _ hmem => cases hmem with
              | head => exact stepBranchSubst
              | tail _ hmem => cases hmem
      -- boolElim row
      · match args, params with
        | .childCons motive (.childCons scrutinee (.childCons firstBranch (.childCons secondBranch .childNil))),
          .childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil)) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have firstBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have secondBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (boolElimCell motive scrutinee firstBranch secondBranch))
            (RawTerm.subst substitution resultType)
          rw [subst_boolElimCell]
          refine HasTypeUnion.elim targetContext .gen_boolElim boolElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution scrutinee)
                (.childCons (RawTerm.subst substitution firstBranch)
                  (.childCons (RawTerm.subst substitution secondBranch) .childNil))))
            (.childCons (RawTerm.subst substitution typeParamA)
              (.childCons (RawTerm.subst substitution typeParamB)
                (.childCons (RawTerm.subst substitution resultType) .childNil)))
            rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact firstBranchSubst
            | tail _ hmem => cases hmem with
              | head => exact secondBranchSubst
              | tail _ hmem => cases hmem
      -- optionMatch row
      · match args, params with
        | .childCons motive (.childCons firstBranch (.childCons secondBranch (.childCons scrutinee .childNil))),
          .childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil)) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have firstBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have secondBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          rw [subst_optionTypeCell] at scrutineeSubst
          rw [subst_nonDependentArrow] at secondBranchSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (optionMatchCell motive firstBranch secondBranch scrutinee))
            (RawTerm.subst substitution resultType)
          rw [subst_optionMatchCell]
          refine HasTypeUnion.elim targetContext .gen_optionMatch optionMatchElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution firstBranch)
                (.childCons (RawTerm.subst substitution secondBranch)
                  (.childCons (RawTerm.subst substitution scrutinee) .childNil))))
            (.childCons (RawTerm.subst substitution typeParamA)
              (.childCons (RawTerm.subst substitution typeParamB)
                (.childCons (RawTerm.subst substitution resultType) .childNil)))
            rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact firstBranchSubst
            | tail _ hmem => cases hmem with
              | head => exact secondBranchSubst
              | tail _ hmem => cases hmem
      -- eitherMatch row
      · match args, params with
        | .childCons motive (.childCons firstBranch (.childCons secondBranch (.childCons scrutinee .childNil))),
          .childCons typeParamA (.childCons typeParamB (.childCons resultType .childNil)) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have firstBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have secondBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          rw [subst_eitherTypeCell] at scrutineeSubst
          rw [subst_nonDependentArrow] at firstBranchSubst
          rw [subst_nonDependentArrow] at secondBranchSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (eitherMatchCell motive firstBranch secondBranch scrutinee))
            (RawTerm.subst substitution resultType)
          rw [subst_eitherMatchCell]
          refine HasTypeUnion.elim targetContext .gen_eitherMatch eitherMatchElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution firstBranch)
                (.childCons (RawTerm.subst substitution secondBranch)
                  (.childCons (RawTerm.subst substitution scrutinee) .childNil))))
            (.childCons (RawTerm.subst substitution typeParamA)
              (.childCons (RawTerm.subst substitution typeParamB)
                (.childCons (RawTerm.subst substitution resultType) .childNil)))
            rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact firstBranchSubst
            | tail _ hmem => cases hmem with
              | head => exact secondBranchSubst
              | tail _ hmem => cases hmem
      -- idJ row
      · match args, params with
        | .childCons motive (.childCons baseCase (.childCons witness .childNil)),
          .childCons typeCode (.childCons endpoint (.childCons resultType .childNil)) =>
          have witnessSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have baseCaseSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          rw [subst_idTypeCell] at witnessSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (idJCell motive baseCase witness))
            (RawTerm.subst substitution resultType)
          rw [subst_idJCell]
          refine HasTypeUnion.elim targetContext .gen_idJ idJElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 2) motive)
              (.childCons (RawTerm.subst substitution baseCase)
                (.childCons (RawTerm.subst substitution witness) .childNil)))
            (.childCons (RawTerm.subst substitution typeCode)
              (.childCons (RawTerm.subst substitution endpoint)
                (.childCons (RawTerm.subst substitution resultType) .childNil)))
            rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact witnessSubst
          | tail _ hmem => cases hmem with
            | head => exact baseCaseSubst
            | tail _ hmem => cases hmem
      -- fst row
      · match args, params with
        | .childCons pairTerm .childNil,
          .childCons firstType (.childCons secondType .childNil) =>
          have pairSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          rw [subst_productTypeCell] at pairSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (fstCell pairTerm)) (RawTerm.subst substitution firstType)
          rw [subst_fstCell]
          refine HasTypeUnion.elim targetContext .gen_fst fstElimRule
            (.childCons (RawTerm.subst substitution pairTerm) .childNil)
            (.childCons (RawTerm.subst substitution firstType)
              (.childCons (RawTerm.subst substitution secondType) .childNil))
            rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact pairSubst
          | tail _ hmem => cases hmem
      -- snd row
      · match args, params with
        | .childCons pairTerm .childNil,
          .childCons firstType (.childCons secondType .childNil) =>
          have pairSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          rw [subst_productTypeCell] at pairSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (sndCell pairTerm)) (RawTerm.subst substitution secondType)
          rw [subst_sndCell]
          refine HasTypeUnion.elim targetContext .gen_snd sndElimRule
            (.childCons (RawTerm.subst substitution pairTerm) .childNil)
            (.childCons (RawTerm.subst substitution firstType)
              (.childCons (RawTerm.subst substitution secondType) .childNil))
            rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact pairSubst
          | tail _ hmem => cases hmem
      -- listElim row
      · match args, params with
        | .childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))),
          .childCons elementType (.childCons resultType .childNil) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have nilSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have consSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          rw [subst_listTypeCell] at scrutineeSubst
          rw [subst_listStepFunctionType] at consSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (listElimCell motive scrutinee nilBranch consBranch))
            (RawTerm.subst substitution resultType)
          rw [subst_listElimCell]
          refine HasTypeUnion.elim targetContext .gen_listElim listElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution scrutinee)
                (.childCons (RawTerm.subst substitution nilBranch)
                  (.childCons (RawTerm.subst substitution consBranch) .childNil))))
            (.childCons (RawTerm.subst substitution elementType)
              (.childCons (RawTerm.subst substitution resultType) .childNil)) rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact nilSubst
            | tail _ hmem => cases hmem with
              | head => exact consSubst
              | tail _ hmem => cases hmem
  | intro context generator rule args params level0 level1 flag isIntro sideHolds premisesHold
      ihPremises =>
      intro targetScope targetContext substitution condition
      have isIntroUnwrapped : introRuleOf generator = some rule := isIntro
      rcases introRuleOf_cases isIntroUnwrapped with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      -- boolTrue row
      · match args, params with
        | .childNil, .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (RawTerm.mkGen .gen_boolTrue () .childNil))
            (RawTerm.subst substitution boolTypeCell)
          rw [subst_boolTypeCell, RawTerm.subst_mkGen_of_ne_var substitution
            (by intro hit; cases hit)]
          refine HasTypeUnion.intro targetContext .gen_boolTrue boolTrueIntroRule .childNil .childNil
            level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- boolFalse row
      · match args, params with
        | .childNil, .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (RawTerm.mkGen .gen_boolFalse () .childNil))
            (RawTerm.subst substitution boolTypeCell)
          rw [subst_boolTypeCell, RawTerm.subst_mkGen_of_ne_var substitution
            (by intro hit; cases hit)]
          refine HasTypeUnion.intro targetContext .gen_boolFalse boolFalseIntroRule .childNil .childNil
            level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- unit row
      · match args, params with
        | .childNil, .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution unitCell) (RawTerm.subst substitution unitTypeCell)
          refine HasTypeUnion.intro targetContext .gen_unit unitIntroRule .childNil .childNil
            level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- interval0 row
      · match args, params with
        | .childNil, .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution intervalZeroCell)
            (RawTerm.subst substitution intervalTypeCell)
          refine HasTypeUnion.intro targetContext .gen_interval0 interval0IntroRule .childNil .childNil
            level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- interval1 row
      · match args, params with
        | .childNil, .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution intervalOneCell)
            (RawTerm.subst substitution intervalTypeCell)
          refine HasTypeUnion.intro targetContext .gen_interval1 interval1IntroRule .childNil .childNil
            level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- natZero row
      · match args, params with
        | .childNil, .childNil =>
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution natZeroCell) (RawTerm.subst substitution natTypeCell)
          rw [subst_natTypeCell, subst_natZeroCell]
          refine HasTypeUnion.intro targetContext .gen_natZero natZeroIntroRule .childNil .childNil
            level0 level1 flag rfl trivial ?_
          intro obligation hmem; cases hmem
      -- lam row
      · match args, params with
        | .childCons domainCode (.childCons body .childNil), .childCons codomainCode .childNil =>
          have liftedCondition :
              HasTypeUnion.SubstUnionTyped (context.cons domainCode)
                (targetContext.cons (RawTerm.subst substitution domainCode))
                (iterateLiftRaw substitution 1) :=
            HasTypeUnion.SubstUnionTyped.cons domainCode substitution condition
          have domainSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have codomainSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _))
              (targetContext.cons (RawTerm.subst substitution domainCode))
              (iterateLiftRaw substitution 1) liftedCondition
          have bodySubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              (targetContext.cons (RawTerm.subst substitution domainCode))
              (iterateLiftRaw substitution 1) liftedCondition
          rw [subst_universeCodeCell] at domainSubst codomainSubst
          have binderGradedSubst :
              gradedBinderChecks UsageGrade.omega
                (RawTerm.subst (iterateLiftRaw substitution 1) body) :=
            gradedBinderChecks_subst_lift UsageGrade.omega substitution body sideHolds
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (lamCell domainCode body))
            (RawTerm.subst substitution (piTyCodeCell domainCode codomainCode))
          rw [subst_lamCell, subst_piTyCodeCell]
          refine HasTypeUnion.intro targetContext .gen_lam lamIntroRule
            (.childCons (RawTerm.subst substitution domainCode)
              (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) body) .childNil))
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) codomainCode) .childNil)
            level0 level1 flag rfl binderGradedSubst ?_
          intro obligation hmem
          cases hmem with
          | head => exact domainSubst
          | tail _ hmem => cases hmem with
            | head => exact codomainSubst
            | tail _ hmem => cases hmem with
              | head => exact bodySubst
              | tail _ hmem => cases hmem
      -- pathLam row
      · match args, params with
        | .childCons body .childNil, .childCons carrierCode .childNil =>
          have liftedCondition :
              HasTypeUnion.SubstUnionTyped (context.cons intervalTypeCell)
                (targetContext.cons (RawTerm.subst substitution intervalTypeCell))
                (iterateLiftRaw substitution 1) :=
            HasTypeUnion.SubstUnionTyped.cons intervalTypeCell substitution condition
          have bodySubst :=
            ihPremises _ (List.Mem.head _)
              (targetContext.cons (RawTerm.subst substitution intervalTypeCell))
              (iterateLiftRaw substitution 1) liftedCondition
          rw [show RawTerm.weaken carrierCode = RawTerm.rename RawRenaming.weaken carrierCode from rfl,
            subst_iterateLift_one_renameWeaken_commute] at bodySubst
          have binderGradedSubst :
              gradedBinderChecks UsageGrade.one
                (RawTerm.subst (iterateLiftRaw substitution 1) body) :=
            gradedBinderChecks_subst_lift UsageGrade.one substitution body sideHolds
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (pathLamCell body))
            (RawTerm.subst substitution
              (bridgeTypeCell carrierCode (RawTerm.subst0 body intervalZeroCell)
                (RawTerm.subst0 body intervalOneCell)))
          rw [subst_pathLamCell, subst_bridgeTypeCell, RawTerm.subst0_subst_commute,
            RawTerm.subst0_subst_commute]
          refine HasTypeUnion.intro targetContext .gen_pathLam pathLamIntroRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) body) .childNil)
            (.childCons (RawTerm.subst substitution carrierCode) .childNil)
            level0 level1 flag rfl binderGradedSubst ?_
          intro obligation hmem
          cases hmem with
          | head =>
              show HasTypeUnion profile (targetContext.cons (RawTerm.subst substitution intervalTypeCell))
                (RawTerm.subst (iterateLiftRaw substitution 1) body)
                (RawTerm.weaken (RawTerm.subst substitution carrierCode))
              rw [show RawTerm.weaken (RawTerm.subst substitution carrierCode)
                    = RawTerm.rename RawRenaming.weaken (RawTerm.subst substitution carrierCode)
                    from rfl]
              exact bodySubst
          | tail _ hmem => cases hmem
      -- natSucc row
      · match args, params with
        | .childCons child .childNil, .childNil =>
          have childSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          rw [subst_natTypeCell] at childSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (natSuccCell child)) (RawTerm.subst substitution natTypeCell)
          rw [subst_natSuccCell, subst_natTypeCell]
          refine HasTypeUnion.intro targetContext .gen_natSucc natSuccIntroRule
            (.childCons (RawTerm.subst substitution child) .childNil) .childNil
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head => exact childSubst
          | tail _ hmem => cases hmem
      -- listCons row
      · match args, params with
        | .childCons head (.childCons tail .childNil), .childCons elementType .childNil =>
          have headSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have tailSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          rw [subst_listTypeCell] at tailSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (listConsCell head tail))
            (RawTerm.subst substitution (listTypeCell elementType))
          rw [subst_listConsCell, subst_listTypeCell]
          refine HasTypeUnion.intro targetContext .gen_listCons listConsIntroRule
            (.childCons (RawTerm.subst substitution head)
              (.childCons (RawTerm.subst substitution tail) .childNil))
            (.childCons (RawTerm.subst substitution elementType) .childNil)
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head => exact headSubst
          | tail _ hmem => cases hmem with
            | head => exact tailSubst
            | tail _ hmem => cases hmem
      -- optionSome row
      · match args, params with
        | .childCons value .childNil, .childCons typeParam0 .childNil =>
          have valueSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (optionSomeCell value))
            (RawTerm.subst substitution (optionTypeCell typeParam0))
          rw [subst_optionSomeCell, subst_optionTypeCell]
          refine HasTypeUnion.intro targetContext .gen_optionSome optionSomeIntroRule
            (.childCons (RawTerm.subst substitution value) .childNil)
            (.childCons (RawTerm.subst substitution typeParam0) .childNil)
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head => exact valueSubst
          | tail _ hmem => cases hmem
      -- optionNone row
      · match args, params with
        | .childNil, .childCons typeParam0 .childNil =>
          have formSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          rw [subst_universeCodeCell] at formSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution optionNoneCell)
            (RawTerm.subst substitution (optionTypeCell typeParam0))
          rw [subst_optionNoneCell, subst_optionTypeCell]
          refine HasTypeUnion.intro targetContext .gen_optionNone optionNoneIntroRule .childNil
            (.childCons (RawTerm.subst substitution typeParam0) .childNil)
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head => exact formSubst
          | tail _ hmem => cases hmem
      -- listNil row
      · match args, params with
        | .childNil, .childCons typeParam0 .childNil =>
          have formSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          rw [subst_universeCodeCell] at formSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution listNilCell)
            (RawTerm.subst substitution (listTypeCell typeParam0))
          rw [subst_listNilCell, subst_listTypeCell]
          refine HasTypeUnion.intro targetContext .gen_listNil listNilIntroRule .childNil
            (.childCons (RawTerm.subst substitution typeParam0) .childNil)
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head => exact formSubst
          | tail _ hmem => cases hmem
      -- eitherInl row
      · match args, params with
        | .childCons value .childNil, .childCons typeParam0 (.childCons typeParam1 .childNil) =>
          have valueSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have formSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          rw [subst_universeCodeCell] at formSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (eitherInlCell value))
            (RawTerm.subst substitution (eitherTypeCell typeParam0 typeParam1))
          rw [subst_eitherInlCell, subst_eitherTypeCell]
          refine HasTypeUnion.intro targetContext .gen_eitherInl eitherInlIntroRule
            (.childCons (RawTerm.subst substitution value) .childNil)
            (.childCons (RawTerm.subst substitution typeParam0)
              (.childCons (RawTerm.subst substitution typeParam1) .childNil))
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head => exact valueSubst
          | tail _ hmem => cases hmem with
            | head => exact formSubst
            | tail _ hmem => cases hmem
      -- eitherInr row
      · match args, params with
        | .childCons value .childNil, .childCons typeParam0 (.childCons typeParam1 .childNil) =>
          have valueSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have formSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          rw [subst_universeCodeCell] at formSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (eitherInrCell value))
            (RawTerm.subst substitution (eitherTypeCell typeParam1 typeParam0))
          rw [subst_eitherInrCell, subst_eitherTypeCell]
          refine HasTypeUnion.intro targetContext .gen_eitherInr eitherInrIntroRule
            (.childCons (RawTerm.subst substitution value) .childNil)
            (.childCons (RawTerm.subst substitution typeParam0)
              (.childCons (RawTerm.subst substitution typeParam1) .childNil))
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head => exact valueSubst
          | tail _ hmem => cases hmem with
            | head => exact formSubst
            | tail _ hmem => cases hmem
      -- pair row
      · match args, params with
        | .childCons child0 (.childCons child1 .childNil),
          .childCons typeParam0 (.childCons typeParam1 .childNil) =>
          have child0Subst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have child1Subst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (pairCell child0 child1))
            (RawTerm.subst substitution (productTypeCell typeParam0 typeParam1))
          rw [subst_pairCell, subst_productTypeCell]
          refine HasTypeUnion.intro targetContext .gen_pair pairIntroRule
            (.childCons (RawTerm.subst substitution child0)
              (.childCons (RawTerm.subst substitution child1) .childNil))
            (.childCons (RawTerm.subst substitution typeParam0)
              (.childCons (RawTerm.subst substitution typeParam1) .childNil))
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head => exact child0Subst
          | tail _ hmem => cases hmem with
            | head => exact child1Subst
            | tail _ hmem => cases hmem
      -- refl row
      · match args, params with
        | .childCons witness .childNil, .childCons typeParam0 .childNil =>
          have witnessSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (reflCell witness))
            (RawTerm.subst substitution (idTypeCell typeParam0 witness witness))
          rw [subst_reflCell, subst_idTypeCell]
          refine HasTypeUnion.intro targetContext .gen_refl reflIntroRule
            (.childCons (RawTerm.subst substitution witness) .childNil)
            (.childCons (RawTerm.subst substitution typeParam0) .childNil)
            level0 level1 flag rfl trivial ?_
          intro obligation hmem
          cases hmem with
          | head => exact witnessSubst
          | tail _ hmem => cases hmem

/-! ## ★ The 1- and 2-binder UNION-substituent corollaries (the β-family transports)

The single-substituent `subst0` and the two-binder `cons (singleton)` instantiations of
`substRespectingContextUnionImages` — the union mirrors of `HasTypeDescPi.substituteUnderBinding` and
`HasTypeUnion.substPairNonDependent`, but with UNION-typed substituents.  These ARE the
`UnionSubst0Transports` / `UnionSubstPairTransports` shapes the β / endpoint-β / succ subject-reduction
rows took as residuals — now genuine theorems, conditional ONLY on the cumulative-former oracle
`formerCloses` (strictly smaller than the whole-transport residual it replaces). -/

/-- **★ The union-substituent single-substitution lemma (the β / endpoint-β transport).**  A union body
typed at `codomain` under one binder, substituted at `var 0 := argument` with a UNION-typed `argument`, is
union-typed at the substituted codomain — `subst0 body argument : subst0 codomain argument`.  The exact
`UnionSubst0Transports` shape, discharged by instantiating `substRespectingContextUnionImages` at
`RawTermSubst.singleton argument` (`subst0 = subst (singleton _)` definitionally), the `Fin` `0` / `k+1`
split verbatim the host `substituteUnderBinding`'s with union images.  Conditional only on the
cumulative-former oracle. -/
theorem HasTypeUnion.subst0WithUnionImage {profile : PolyProfile}
    (formerCloses : UnionCumulativeFormerCloses profile)
    {scope : Nat} {context : TypingContext profile scope} {domain : RawTerm scope}
    {body codomain : RawTerm (scope + 1)} (argument : RawTerm scope)
    (bodyTyped : HasTypeUnion profile (context.cons domain) body codomain)
    (argumentTyped : HasTypeUnion profile context argument domain) :
    HasTypeUnion profile context
      (RawTerm.subst0 body argument) (RawTerm.subst0 codomain argument) := by
  refine bodyTyped.substRespectingContextUnionImages formerCloses context
    (RawTermSubst.singleton argument) ?_
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show HasTypeUnion profile context argument
        (RawTerm.subst (RawTermSubst.singleton argument)
          (RawTerm.rename RawRenaming.weaken domain))
      rw [subst_singleton_renameWeaken_cancel]
      exact argumentTyped
  | succ priorValue =>
      show HasTypeUnion profile context
          (variableCell ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩)
        (RawTerm.subst (RawTermSubst.singleton argument)
          (RawTerm.rename RawRenaming.weaken
            (context.lookup ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩)))
      rw [subst_singleton_renameWeaken_cancel]
      exact HasTypeUnion.ofGrown
        (HasTypeDescPi.ofFormation
          (HasTypeDesc.var context ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩))

/-- **★ The union-substituent two-binder substitution lemma.**  A union derivation under two binders,
substituted simultaneously at `var 0 := innerArg, var 1 := outerArg` with BOTH substituents UNION-typed,
preserves `HasTypeUnion` with subject and classifier substituted.  The union-image mirror of
`HasTypeUnion.substPairUnderTwoBindings`, instantiating `substRespectingContextUnionImages` at
`cons innerArg (singleton outerArg)`.  Conditional only on the cumulative-former oracle. -/
theorem HasTypeUnion.substPairUnderTwoBindingsUnionImages {profile : PolyProfile}
    (formerCloses : UnionCumulativeFormerCloses profile)
    {scope : Nat} {context : TypingContext profile scope} {outerType : RawTerm scope}
    {innerType : RawTerm (scope + 1)} {subject classifier : RawTerm (scope + 2)}
    (innerArg outerArg : RawTerm scope)
    (derivation :
      HasTypeUnion profile ((context.cons outerType).cons innerType) subject classifier)
    (innerArgTyped : HasTypeUnion profile context innerArg
      (RawTerm.subst (RawTermSubst.singleton outerArg) innerType))
    (outerArgTyped : HasTypeUnion profile context outerArg outerType) :
    HasTypeUnion profile context
      (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) subject)
      (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) classifier) := by
  refine derivation.substRespectingContextUnionImages formerCloses context
    (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) ?_
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      show HasTypeUnion profile context innerArg
        (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg))
          (RawTerm.rename RawRenaming.weaken innerType))
      rw [RawTerm.weaken_subst_cons]
      exact innerArgTyped
  | succ tailValue =>
      cases tailValue with
      | zero =>
          show HasTypeUnion profile context outerArg
            (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg))
              (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken outerType)))
          rw [RawTerm.weaken_subst_cons, subst_singleton_renameWeaken_cancel]
          exact outerArgTyped
      | succ priorValue =>
          show HasTypeUnion profile context
            (variableCell ⟨priorValue,
              Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ indexBound)⟩)
            (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg))
              (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken
                (context.lookup ⟨priorValue,
                  Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ indexBound)⟩))))
          rw [RawTerm.weaken_subst_cons, subst_singleton_renameWeaken_cancel]
          exact HasTypeUnion.ofGrown
            (HasTypeDescPi.ofFormation
              (HasTypeDesc.var context ⟨priorValue,
                Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ indexBound)⟩))

/-- **★ The recursor-step-shaped two-binder corollary (the natElim·natRec succ transport).**  A branch
typed in the UNION at a TWICE-WEAKENED result type under two binders, substituted at a UNION-typed
recursive result and a UNION-typed outer argument, is union-typed at the result type on the nose — both
weakenings cancel against the two substituents.  The exact `UnionSubstPairTransports` shape, the
union-image mirror of `HasTypeUnion.substPairNonDependent`.  Conditional only on the cumulative-former
oracle. -/
theorem HasTypeUnion.substPairNonDependentUnionImages {profile : PolyProfile}
    (formerCloses : UnionCumulativeFormerCloses profile)
    {scope : Nat} {context : TypingContext profile scope} {outerType resultType : RawTerm scope}
    {branch : RawTerm (scope + 2)}
    (innerArg outerArg : RawTerm scope)
    (branchTyped : HasTypeUnion profile
      ((context.cons outerType).cons (RawTerm.rename RawRenaming.weaken resultType))
      branch
      (RawTerm.rename RawRenaming.weaken (RawTerm.rename RawRenaming.weaken resultType)))
    (innerArgTyped : HasTypeUnion profile context innerArg resultType)
    (outerArgTyped : HasTypeUnion profile context outerArg outerType) :
    HasTypeUnion profile context
      (RawTerm.subst (RawTermSubst.cons innerArg (RawTermSubst.singleton outerArg)) branch)
      resultType := by
  have innerAtSubstituted : HasTypeUnion profile context innerArg
      (RawTerm.subst (RawTermSubst.singleton outerArg)
        (RawTerm.rename RawRenaming.weaken resultType)) := by
    rw [subst_singleton_renameWeaken_cancel]
    exact innerArgTyped
  have substituted :=
    HasTypeUnion.substPairUnderTwoBindingsUnionImages formerCloses innerArg outerArg branchTyped
      innerAtSubstituted outerArgTyped
  rwa [RawTerm.weaken_subst_cons, subst_singleton_renameWeaken_cancel] at substituted

/-! ## ★ The `UnionSubstPairTransports` residual, DISCHARGED from the cumulative-former oracle

The two-binder transport abbrev the succ subject-reduction rows premise (`UnionSubstPairTransports`, defined
in `HasTypeUnionSubstitution`) is an instance of `substPairNonDependentUnionImages`.  Supplying
`formerCloses` makes the succ-ι discharges (`natElimSuccIotaComputesTypedInUnion` /
`natRecSuccIotaComputesTypedInUnion`) — and thereby the natElim·natRec succ subject-reduction rows —
unconditional MODULO the precise, documented cumulative-former wall (strictly smaller than the
whole-transport residual). -/

/-- The `UnionSubstPairTransports` shape is an instance of `substPairNonDependentUnionImages` — the
natElim·natRec succ 2-binder transport, derived from the cumulative-former oracle. -/
theorem unionSubstPairTransports_ofFormerCloses {profile : PolyProfile}
    (formerCloses : UnionCumulativeFormerCloses profile)
    {scope : Nat} (context : TypingContext profile scope) (outerType resultType : RawTerm scope) :
    UnionSubstPairTransports profile context outerType resultType :=
  fun branch innerArg outerArg branchTyped innerArgTyped outerArgTyped =>
    HasTypeUnion.substPairNonDependentUnionImages formerCloses innerArg outerArg branchTyped
      innerArgTyped outerArgTyped

end FX1Poly.Typed

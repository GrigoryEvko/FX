import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.Union.HasTypeUnionFormationObligations
import FX1Poly.Typed.Engine.Union.HasTypeUnionSubstitution
import FX1Poly.Typed.Engine.Union.HasTypeUnionWeakening
import FX1Poly.Typed.Engine.Union.HasTypeUnionSubstUnionTyped
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPiSubstitution
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDescSubstitution

/-! # FX1Poly/Typed/HasTypeUnionUnionSubstituent — the UNION-SUBSTITUENT single- and two-binder
    substitution lemmas (the β-family subject-reduction transports, now UNCONDITIONAL)

The W2 wave shipped `HasTypeUnion.substRespectingContext` (substitution preserved along ANY HOST-typed
substitution).  For β / endpoint-β / the natElim·natRec succ rows the argument is only UNION-typed
(e.g. `fst pair` is union-typed at a universe but has NO host typing — the NATIVE-08 wall), so the
host-substituent formulation cannot supply it.

This file GENERALIZES the substituent discipline: substituent images may be UNION-typed
(`SubstUnionTyped`, the union mirror of `SubstHostTyped`).  Then the β-family transports become genuine
INSTANCES.

## The cumulative-former arm — now CLOSED (TYTAB-2 wave U3)

The one arm that does not close through the union's pre-U2 arms is the cumulative-formation-former arm
(`HasTypeDescPi.genFormationPi` / `HasTypeDesc.genFormation`) at the four cumulative type-code formers
`gen_piTyCode` / `gen_sigmaTyCode` / `gen_listCode` / `gen_optionCode` (the `typingRuleDescOf` table,
plus the nullary `gen_unitCode` which routes through its `formationRule` base-type row).  Wave U2 wired
all five into the union's `formationRuleOf` table (the `.cumulative` formation family), so a substituted
former whose child carries a UNION-ONLY image is now rebuilt DIRECTLY in the union via
`formationRuleOfObligations` — no host reflection, no oracle.

`UnionCumulativeFormerCloses` (the property "the cumulative former closes from union children") is
therefore DISCHARGED by the theorem `unionCumulativeFormerCloses` below, and every substituent lemma in
this file is UNCONDITIONAL.  Every host and union arm — var leaf, universe leaf, conv, piIntro (λ),
piElim (app), the base-type / flat / term-indexed / cumulative formation families through
`formationRuleOfObligations`, and the union intro / elim / formationRule / conv arms — closes through the
union's own arms.

## Zero-axiom

`match` / `induction` over the host and union derivations + the cell-subst `rfl` commutations + the
`FormationRule.obligations_pushSubst` obligation push + `HasTypeUnion.weakenUnderBinding` for the
binder-lift + `Conv.subst` + `RawTerm.subst0_subst_commute`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditUnionSubstitution.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax FX1Poly.Modal

/-! `HasTypeUnion.SubstUnionTyped` (the native substitution-context condition) + its one/two-binder lift
API (`cons` / `consTwice`) now live upstream in `FX1Poly.Typed.Engine.Union.HasTypeUnionSubstUnionTyped`
(imported above), so both substitution masters re-base on the native condition without an import cycle.
The `cons` zero-case there types the fresh `var 0` through the NATIVE `HasTypeUnion.var` (no `ofGrown`). -/

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

/-! ## The cumulative-formation-former property — DISCHARGED (TYTAB-2 wave U3)

`hostSubstWithUnionImages` substitutes UNION images into a host `HasTypeDescPi` derivation.  Every arm
closes through the union's own arms; the cumulative-formation-former arm
(`HasTypeDescPi.genFormationPi` / `HasTypeDesc.genFormation`) at the five `typingRuleDescOf` cumulative
codes `gen_piTyCode` / `gen_sigmaTyCode` / `gen_listCode` / `gen_optionCode` / `gen_unitCode` closes
through the wave-U2 `.cumulative` formation table: given the substituted children union-typed at their
universe-code premises (which the companion telescope recursion delivers, threaded as a
`DescTelescopeUnion`), the substituted cumulative former is union-typed at its substituted output via
`formationRuleOfObligations`.

The property is named `UnionCumulativeFormerCloses` and DISCHARGED below by the theorem
`unionCumulativeFormerCloses`, so `hostSubstWithUnionImages` and every downstream substituent lemma are
UNCONDITIONAL. -/

/-- **The cumulative-formation-former closing property.**  For any generator carrying a `typingRuleDescOf`
cumulative formation rule (`gen_piTyCode` / `gen_sigmaTyCode` / `gen_listCode` / `gen_optionCode` /
`gen_unitCode`), given a children spine each child of which is union-typed at its level's universe code
(in the per-child context the dependent telescope pins), the former `.mkGen generator payload children`
is union-typed at the rule's output universe.

Discharged unconditionally by `unionCumulativeFormerCloses` (wave U3): the four ≥1-child codes rebuild
through their `.cumulative` `formationRuleOf` row (wave U2), the nullary `gen_unitCode` through its
`baseType` row.  The named property is kept so the proof structure reads as "this arm's obligation, now
proven" rather than inlining the reconstruction at every call site. -/
abbrev UnionCumulativeFormerCloses (profile : PolyProfile) : Prop :=
  ∀ {scope : Nat} (context : TypingContext profile scope)
    (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope)
    (levels : List LevelExpr) (flag : UniverseFlag) (rule : TypingRuleDesc),
    typingRuleDescOf generator = some rule →
    DescTelescopeUnion profile (currentDepth := 0) context levels flag children →
    HasTypeUnion profile context (.mkGen generator payload children)
      (rule.outputType scope levels flag)

/-! ## ★ TYTAB-2 wave U3: discharging the cumulative-former oracle as a THEOREM

After wave U2 the four cumulative type-code formers (`gen_piTyCode` / `gen_sigmaTyCode` / `gen_listCode` /
`gen_optionCode`) ARE `formationRuleOf` rows (the `.cumulative` family), so a former whose children carry
UNION-only images is now rebuildable DIRECTLY in the union via `formationRuleOfObligations` — no host
reflection.  The bridge below transports a UNION telescope (`DescTelescopeUnion`) into the cumulative
obligation list (the union mirror of the retired grown cumulative-formation premise bridge, with the heads
already union-typed so no `ofGrown`).  The nullary `gen_unitCode` is NOT a `.cumulative` row
(`formationRuleOf` finds its `baseType` row first), so it routes through the base-type formation row instead
— its output is `Type@0` either way (`typingRuleDescOf_unitCode_outputConstant`). -/

/-- **The cumulative-family UNION bridge.**  A UNION cumulative dependent telescope (`DescTelescopeUnion`)
discharges every cumulative-family obligation: the binder-shape Π/Σ spine `[0, 1]` exposes the domain typing
at the ambient context and the codomain typing at the domain-extended context (each already a
`HasTypeUnion`), matching the two obligations of `cumulativeFormationObligations`; the element-shape
List/Option spine `[0]` exposes the single element typing.  The union analogue of the retired grown
cumulative-formation premise bridge, sans the `ofGrown` lift (the heads are union-typed already). -/
theorem cumulativeFormationUnionPremiseToObligations {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag} {binderShifts : List Nat}
    {levels : List LevelExpr} {children : RawTermChildren binderShifts scope}
    (telescope : DescTelescopeUnion profile (currentDepth := 0) context levels flag children) :
    ∀ obligation ∈ cumulativeFormationObligations profile context flag children levels,
      HasTypeUnion profile obligation.context obligation.subject obligation.classifier := by
  cases telescope with
  | nil _context _flag =>
      intro obligation hmem
      cases hmem
  | cons _context domain domainLevel restLevels _flag rest domainTyped restTyped =>
      cases rest with
      | childNil =>
          intro obligation hmem
          cases hmem with
          | head => exact domainTyped
          | tail _ tailMember => cases tailMember
      | childCons codomain deeperRest =>
          rename_i codomainShift _deeperShifts
          cases codomainShift with
          | succ priorShift =>
              cases priorShift with
              | zero =>
                  cases deeperRest with
                  | childNil =>
                      cases restTyped with
                      | cons _context _codomain _codomainLevel _restLevels2 _flag _rest2
                          codomainTyped _restTyped2 =>
                          intro obligation hmem
                          cases hmem with
                          | head => exact domainTyped
                          | tail _ tailMember =>
                              cases tailMember with
                              | head => exact codomainTyped
                              | tail _ deeperMember => cases deeperMember
                  | childCons _deeper2 _deeper3 =>
                      intro obligation hmem
                      cases hmem
              | succ _ =>
                  intro obligation hmem
                  cases hmem
          | zero =>
              intro obligation hmem
              cases hmem

/-- ★ **The cumulative-former oracle, now a THEOREM (TYTAB-2 wave U3).**  The former `.mkGen generator
payload children` is union-typed at its output universe, for any `typingRuleDescOf` cumulative former
(`gen_piTyCode` / `gen_sigmaTyCode` / `gen_listCode` / `gen_optionCode` / `gen_unitCode`), given the children
form a UNION telescope.  The four ≥1-child codes route through `formationRuleOfObligations` at their
`.cumulative` formation row (wave U2) fed the bridged obligations; the nullary `gen_unitCode` routes through
its `baseType` formation row (the row `formationRuleOf` finds first), its output pinned to `Type@0` either
way.  Discharges the former-residual that `hostSubstWithUnionImages` / `substRespectingContextUnionImages`
took as a hypothesis — making them UNCONDITIONAL.  Zero-axiom. -/
theorem unionCumulativeFormerCloses {profile : PolyProfile} :
    UnionCumulativeFormerCloses profile := by
  intro scope context generator payload children levels flag rule isCumulative telescope
  by_cases isUnit : generator = Generator.gen_unitCode
  · -- Nullary unit code: route through the base-type formation row; output is Type@0 both ways.
    subst isUnit
    obtain ⟨baseRule, isBaseType⟩ : ∃ baseRule, baseTypeRuleDescOf Generator.gen_unitCode = some baseRule :=
      ⟨_, rfl⟩
    have isBaseRow : formationRuleOf Generator.gen_unitCode = some (FormationRule.baseType baseRule) := by
      unfold formationRuleOf; rw [isBaseType]
    rw [typingRuleDescOf_unitCode_outputConstant isCumulative scope levels flag]
    have formed :
        HasTypeUnion profile context (.mkGen Generator.gen_unitCode payload children)
          ((FormationRule.baseType baseRule).outputType scope levels LevelExpr.lzero flag) :=
      HasTypeUnion.formationRuleOfObligations context Generator.gen_unitCode payload children
        (.baseType baseRule) levels (.mkGen Generator.gen_unitCode payload children) LevelExpr.lzero flag
        isBaseRow (fun _obligation hmem => by cases hmem)
    have outputIsType0 :
        (FormationRule.baseType baseRule).outputType scope levels LevelExpr.lzero flag
          = universeCodeCell LevelExpr.lzero UniverseFlag.standard := by
      show baseRule.outputUniverse scope = universeCodeCell LevelExpr.lzero UniverseFlag.standard
      rw [baseTypeRuleTableOutputIsType0 isBaseType]
    rwa [outputIsType0] at formed
  · -- The four ≥1-child cumulative codes: rebuild through the `.cumulative` formation row.
    have isCumulativeRow : formationRuleOf generator = some (FormationRule.cumulative rule) :=
      formationRuleOf_cumulative isCumulative isUnit
    exact HasTypeUnion.formationRuleOfObligations context generator payload children
      (.cumulative rule) levels (.mkGen generator payload children) LevelExpr.lzero flag isCumulativeRow
      (cumulativeFormationUnionPremiseToObligations telescope)

/-! ## The base-engine leg: substitute a FORMATION derivation under union images

`baseFormationSubstWithUnionImages` carries a `HasTypeDesc` derivation along a substitution whose images
are UNION-typed, landing in `HasTypeUnion`.  The `ofFormation` leg the grown union substitution rests on:
a formation subject substituted by a union substitution is in general neither a formation term nor a host
term (a child may become a union-only image), so it retypes in the UNION.  Mutual with the companion
telescope substitution producing a `DescTelescopeUnion`.  The var leaf returns the union image; the
universe leaf re-embeds via `ofGrown`; `conv` recurses + `Conv.subst`; `genFormation` substitutes the
spine through the companion and closes via `unionCumulativeFormerCloses`. -/

mutual

/-- Substitute a FORMATION derivation under a UNION-image substitution, producing a UNION derivation.
Mutual structural recursion on the FORMATION derivation; the genFormation case substitutes the spine
through the companion (producing a `DescTelescopeUnion`) and closes via `unionCumulativeFormerCloses`. -/
theorem baseFormationSubstWithUnionImages {profile : PolyProfile}
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
          baseFormationSubstWithUnionImages typedPremise targetContext substitution
            substitutionTyped
        have reclassifierTypedSubst :=
          baseFormationSubstWithUnionImages reclassifierTyped targetContext substitution
            substitutionTyped
        rw [subst_universeCodeCell] at reclassifierTypedSubst
        exact HasTypeUnion.conv levelExpr flag premiseTyped
          (Conv.subst substitution converts) reclassifierTypedSubst
  | .universeFormation _sourceContext levelExpr flag =>
      fun targetContext substitution _substitutionTyped => by
        rw [subst_universeCodeCell, subst_universeCodeCell]
        exact HasTypeUnion.universeFormation targetContext levelExpr flag
  | .genFormation _sourceContext generator payload children levels flag rule
      isFormation premises => fun targetContext substitution substitutionTyped => by
      have substPremises :=
        baseTelescopeSubstWithUnionImages premises targetContext substitution
          substitutionTyped
      have hNotVar : generator ≠ Generator.gen_var := formationRuleImpliesNotVariable isFormation
      rw [typingRuleDescOf_output_substStable isFormation substitution levels flag,
        RawTerm.subst_mkGen_of_ne_var substitution hNotVar]
      exact unionCumulativeFormerCloses targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.subst substitution children) levels flag rule isFormation substPremises

/-- Companion: substitute a FORMATION premise spine under union images, producing a `DescTelescopeUnion`.
Head via `baseFormationSubstWithUnionImages` (reshaped to the universe code); tail under the binder with
the LIFTED union condition (`0` → the fresh `var` via `ofGrown ∘ ofFormation`; `k+1` → the union image
weakened via `HasTypeUnion.weakenUnderBinding`). -/
theorem baseTelescopeSubstWithUnionImages {profile : PolyProfile}
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
            baseFormationSubstWithUnionImages headTyped targetContext
              (iterateLiftRaw substitution currentDepth) substitutionTyped
          rwa [subst_universeCodeCell] at headSubst
        refine DescTelescopeUnion.cons targetContext
          (RawTerm.subst (iterateLiftRaw substitution currentDepth) head) headLevel
          restLevels flag (RawTermChildren.subst substitution rest) substHeadTyped ?_
        refine baseTelescopeSubstWithUnionImages restTyped
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
            exact HasTypeUnion.var
              (targetContext.cons
                (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
              ⟨0, Nat.succ_pos _⟩
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
via the union `elim` arm at `gen_app`, and `genFormationPi` closes the cumulative former through
`unionCumulativeFormerCloses`.  Mutual with the companion telescope substitution producing a
`DescTelescopeUnion`. -/

mutual

/-- **★ Substitute a HOST `HasTypeDescPi` derivation under UNION images, landing in `HasTypeUnion`.**  The
union-image generalization of `HasTypeDescPi.substRespectingContext` — the `ofGrown` leg of the union
substitution lemma.  Substituent images may be UNION-typed (the `SubstUnionTyped` condition), so the
result lands in `HasTypeUnion`.  UNCONDITIONAL: the `genFormationPi` arm closes the cumulative former
through `unionCumulativeFormerCloses` (wave U3). -/
theorem hostSubstWithUnionImages {profile : PolyProfile}
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
      baseFormationSubstWithUnionImages formationTyped targetContext substitution
        substitutionTyped
  | .conv levelExpr flag typed converts reclassifierTyped =>
      fun targetContext substitution substitutionTyped => by
        have typedSubst :=
          hostSubstWithUnionImages typed targetContext substitution substitutionTyped
        have reclassifierSubst :=
          hostSubstWithUnionImages reclassifierTyped targetContext substitution
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
        hostSubstWithUnionImages domainTyped targetContext substitution substitutionTyped
      rw [subst_universeCodeCell] at domainSubst
      have codomainSubst :=
        hostSubstWithUnionImages codomainTyped
          (targetContext.cons (RawTerm.subst substitution domainCode))
          (iterateLiftRaw substitution 1) liftedCondition
      rw [subst_universeCodeCell] at codomainSubst
      have bodySubst :=
        hostSubstWithUnionImages bodyTyped
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
        hostSubstWithUnionImages functionTyped targetContext substitution
          substitutionTyped
      rw [subst_piTyCodeCell] at functionSubst
      have argumentSubst :=
        hostSubstWithUnionImages argumentTyped targetContext substitution
          substitutionTyped
      show HasTypeUnion profile targetContext
        (RawTerm.subst substitution (appCell functionTerm argument))
        (RawTerm.subst substitution (RawTerm.subst0 codomainCode argument))
      rw [subst_appCell, RawTerm.subst0_subst_commute]
      -- `app` is the ONE non-self-certifying elim row (see `appElimRule`): the host-substitution path needs
      -- only the substituted function + argument premises — the output formedness is NOT a table obligation
      -- (it is discharged in `classifierIsType` where `WfContextUnion` lives, NOT in this UNCONDITIONAL
      -- substituent, which cannot supply it for a bare-variable function — the var-leaf wall).  The
      -- level/flag args are immaterial (the 2-entry obligation list ignores them).
      refine HasTypeUnion.elim targetContext .gen_app appElimRule
        (.childCons (RawTerm.subst substitution functionTerm)
          (.childCons (RawTerm.subst substitution argument) .childNil))
        (.childCons (RawTerm.subst substitution domainCode)
          (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) codomainCode) .childNil))
        LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl ?_
      intro obligation hmem
      cases hmem with
      | head => exact functionSubst
      | tail _ hmem => cases hmem with
        | head => exact argumentSubst
        | tail _ hmem => cases hmem
  | .genFormationPi _sourceContext generator payload children levels flag rule
      isFormation premises => fun targetContext substitution substitutionTyped => by
      have substPremises :=
        hostTelescopeSubstWithUnionImages premises targetContext substitution
          substitutionTyped
      have hNotVar : generator ≠ Generator.gen_var := formationRuleImpliesNotVariable isFormation
      rw [typingRuleDescOf_output_substStable isFormation substitution levels flag,
        RawTerm.subst_mkGen_of_ne_var substitution hNotVar]
      exact unionCumulativeFormerCloses targetContext generator
        (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
        (RawTermChildren.subst substitution children) levels flag rule isFormation substPremises

/-- Companion: substitute a GROWN premise spine under union images, producing a `DescTelescopeUnion`.  The
grown mirror of `baseTelescopeSubstWithUnionImages`, with the head recursing the grown engine. -/
theorem hostTelescopeSubstWithUnionImages {profile : PolyProfile}
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
            hostSubstWithUnionImages headTyped targetContext
              (iterateLiftRaw substitution currentDepth) substitutionTyped
          rwa [subst_universeCodeCell] at headSubst
        refine DescTelescopeUnion.cons targetContext
          (RawTerm.subst (iterateLiftRaw substitution currentDepth) head) headLevel
          restLevels flag (RawTermChildren.subst substitution rest) substHeadTyped ?_
        refine hostTelescopeSubstWithUnionImages restTyped
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
            exact HasTypeUnion.var
              (targetContext.cons
                (RawTerm.subst (iterateLiftRaw substitution currentDepth) head))
              ⟨0, Nat.succ_pos _⟩
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

/-- **★ The pointwise UNION-substituent substitution lemma over the native union.**

The union-image generalization of `HasTypeUnion.substRespectingContext`: a union derivation, substituted
by ANY UNION-typed substitution, gives a union derivation of the substituted subject at the substituted
classifier.  By `induction` over the 5 union arms — IDENTICAL to `substRespectingContext` EXCEPT the
condition is `SubstUnionTyped` (so the binder lifts are `SubstUnionTyped.cons`/`consTwice` and the leaf
images are union typings), and the `ofGrown` arm routes through `hostSubstWithUnionImages` (the host
derivation substituted under union images) instead of the host engine's own substitution.  UNCONDITIONAL. -/
theorem HasTypeUnion.substRespectingContextUnionImages {profile : PolyProfile}
    {sourceScope : Nat} {sourceContext : TypingContext profile sourceScope}
    {subject classifier : RawTerm sourceScope}
    (derivation : HasTypeUnion profile sourceContext subject classifier) :
    ∀ {targetScope : Nat} (targetContext : TypingContext profile targetScope)
      (substitution : RawTermSubst sourceScope targetScope),
      HasTypeUnion.SubstUnionTyped sourceContext targetContext substitution →
      HasTypeUnion profile targetContext
        (RawTerm.subst substitution subject)
        (RawTerm.subst substitution classifier) := by
  have nativeDerivation := derivation.toNativeOnly
  clear derivation
  induction nativeDerivation with
  | var context index =>
      intro targetScope targetContext substitution condition
      rw [subst_variableCell]
      exact condition index
  | universeFormation context levelExpr flag =>
      intro targetScope targetContext substitution condition
      rw [subst_universeCodeCell, subst_universeCodeCell]
      exact HasTypeUnion.universeFormation targetContext levelExpr flag
  | conv levelExpr flag typed converts reclassifierTyped typedIH reclassifierIH =>
      intro targetScope targetContext substitution condition
      have typedSubst := typedIH targetContext substitution condition
      have reclassifierSubst := reclassifierIH targetContext substitution condition
      rw [subst_universeCodeCell] at reclassifierSubst
      exact HasTypeUnion.conv levelExpr flag typedSubst
        (Conv.subst substitution converts) reclassifierSubst
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
          exact HasTypeUnion.formationRuleOfObligations targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.subst substitution children) (.baseType baseRule)
            levels (RawTerm.subst substitution carrier) level flag isFormationRule
            (fun _obligation hmem => by cases hmem)
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
                ihPremises _ member targetContext substitution condition)
              (fun domain subject classifier member =>
                ihPremises _ member (targetContext.cons (RawTerm.subst substitution domain))
                  (iterateLiftRaw substitution 1)
                  (HasTypeUnion.SubstUnionTyped.cons domain substitution condition)))
      | cumulative cumulativeRule =>
          -- TYTAB-2 wave U2 (union-image twin): the four cumulative codes (Π / Σ / list / option) plus the
          -- nullary unit code are now `formationRuleOf` rows, rebuilt directly in the UNION from the pushed
          -- obligation list (no host reflection needed for a formationRule subject — the children union typings
          -- come from `ihPremises`).  ROW-SHAPE-AGNOSTIC output rewrite via `typingRuleDescOf_output_substStable`;
          -- the `crossingTypings` clause threads the Π/Σ binder-crossing codomain at the lifted union
          -- substitution (`SubstUnionTyped.cons`).
          have isCumulative : typingRuleDescOf generator = some cumulativeRule :=
            formationRuleOf_cumulative_inv isFormationRule
          have hNotVar : generator ≠ Generator.gen_var :=
            cumulativeFormationRuleImpliesNotVariable isCumulative
          dsimp only [FormationRule.outputType]
          rw [typingRuleDescOf_output_substStable isCumulative substitution levels flag,
            RawTerm.subst_mkGen_of_ne_var substitution hNotVar]
          exact HasTypeUnion.formationRuleOfObligations targetContext generator
            (Generator.payload_scope_invariant_of_not_var hNotVar _ _ ▸ payload)
            (RawTermChildren.subst substitution children)
            (.cumulative cumulativeRule)
            levels (RawTerm.subst substitution carrier) level flag isFormationRule
            (FormationRule.obligations_pushSubst (.cumulative cumulativeRule)
              targetContext substitution children levels carrier level flag
              (fun subject classifier member =>
                ihPremises _ member targetContext substitution condition)
              (fun domain subject classifier member =>
                ihPremises _ member (targetContext.cons (RawTerm.subst substitution domain))
                  (iterateLiftRaw substitution 1)
                  (HasTypeUnion.SubstUnionTyped.cons domain substitution condition)))
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
                ihPremises _ member targetContext substitution condition)
              (fun domain subject classifier member =>
                ihPremises _ member (targetContext.cons (RawTerm.subst substitution domain))
                  (iterateLiftRaw substitution 1)
                  (HasTypeUnion.SubstUnionTyped.cons domain substitution condition)))
  | elim context generator rule args params level0 level1 flag isElim premisesHold ihPremises =>
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
          -- `app` is non-self-certifying (2 obligations): only function + argument premises.
          refine HasTypeUnion.elim targetContext .gen_app appElimRule
            (.childCons (RawTerm.subst substitution eliminated)
              (.childCons (RawTerm.subst substitution argument) .childNil))
            (.childCons (RawTerm.subst substitution typeParamA)
              (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) typeParamB) .childNil))
            level0 level1 flag rfl ?_
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
          have resultSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          rw [subst_universeCodeCell] at resultSubst
          refine HasTypeUnion.elim targetContext .gen_pathApp pathAppElimRule
            (.childCons (RawTerm.subst substitution eliminated)
              (.childCons (RawTerm.subst substitution argument) .childNil))
            (.childCons (RawTerm.subst substitution typeParamA)
              (.childCons (RawTerm.subst substitution typeParamC)
                (.childCons (RawTerm.subst substitution typeParamD) .childNil)))
            level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact eliminatedSubst
          | tail _ hmem => cases hmem with
            | head => exact argumentSubst
            | tail _ hmem => cases hmem with
              | head => exact resultSubst
              | tail _ hmem => cases hmem
      -- natElim row: DEPENDENT (union-substituent twin) — output `subst0 motive scrutinee`, base branch at
      -- zero (`subst0_subst_commute`, closed `natZeroCell`), step branch under TWO binders at
      -- `natElimDependentSuccBranchType motive` (reshaped by the substitution-naturality corollary), motive
      -- under one `natTypeCell` binder (lifted via `SubstUnionTyped.cons`).
      · match args with
        | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have baseBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have stepBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) _
              (iterateLiftRaw substitution 2)
              (HasTypeUnion.SubstUnionTyped.consTwice natTypeCell motive condition)
          have motiveSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) _
              (iterateLiftRaw substitution 1)
              (HasTypeUnion.SubstUnionTyped.cons natTypeCell substitution condition)
          rw [subst_natTypeCell] at scrutineeSubst
          rw [RawTerm.subst0_subst_commute] at baseBranchSubst
          rw [subst_natElimDependentSuccBranchType_iterateLift] at stepBranchSubst
          rw [subst_universeCodeCell] at motiveSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (natElimCell motive baseBranch stepBranch scrutinee))
            (RawTerm.subst substitution (RawTerm.subst0 motive scrutinee))
          rw [subst_natElimCell, RawTerm.subst0_subst_commute]
          refine HasTypeUnion.elim targetContext .gen_natElim natElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution baseBranch)
                (.childCons (RawTerm.subst (iterateLiftRaw substitution 2) stepBranch)
                  (.childCons (RawTerm.subst substitution scrutinee) .childNil))))
            .childNil level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact baseBranchSubst
            | tail _ hmem => cases hmem with
              | head => exact stepBranchSubst
              | tail _ hmem => cases hmem with
                | head => exact motiveSubst
                | tail _ hmem => cases hmem
      -- natRec row: DEPENDENT (union-substituent twin) — verbatim twin of the `natElim` row; only the cell
      -- former (`natRecCell`) and generator (`gen_natRec`) differ.
      · match args with
        | .childCons motive (.childCons baseBranch (.childCons stepBranch (.childCons scrutinee .childNil))) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have baseBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have stepBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) _
              (iterateLiftRaw substitution 2)
              (HasTypeUnion.SubstUnionTyped.consTwice natTypeCell motive condition)
          have motiveSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) _
              (iterateLiftRaw substitution 1)
              (HasTypeUnion.SubstUnionTyped.cons natTypeCell substitution condition)
          rw [subst_natTypeCell] at scrutineeSubst
          rw [RawTerm.subst0_subst_commute] at baseBranchSubst
          rw [subst_natElimDependentSuccBranchType_iterateLift] at stepBranchSubst
          rw [subst_universeCodeCell] at motiveSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (natRecCell motive baseBranch stepBranch scrutinee))
            (RawTerm.subst substitution (RawTerm.subst0 motive scrutinee))
          rw [subst_natRecCell, RawTerm.subst0_subst_commute]
          refine HasTypeUnion.elim targetContext .gen_natRec natRecElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution baseBranch)
                (.childCons (RawTerm.subst (iterateLiftRaw substitution 2) stepBranch)
                  (.childCons (RawTerm.subst substitution scrutinee) .childNil))))
            .childNil level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact baseBranchSubst
            | tail _ hmem => cases hmem with
              | head => exact stepBranchSubst
              | tail _ hmem => cases hmem with
                | head => exact motiveSubst
                | tail _ hmem => cases hmem
      -- boolElim row: DEPENDENT — output `subst0 motive scrutinee`, branches at the motive over the
      -- boolean values (reshaped via `subst0_subst_commute`); motive obligation under one `boolTypeCell`
      -- binder (lifted via `SubstUnionTyped.cons`).  No type-index params (paramShifts []).
      · match args, params with
        | .childCons motive (.childCons scrutinee (.childCons firstBranch (.childCons secondBranch .childNil))),
          .childNil =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have firstBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have secondBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          have motiveSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) _
              (iterateLiftRaw substitution 1)
              (HasTypeUnion.SubstUnionTyped.cons boolTypeCell substitution condition)
          rw [RawTerm.subst0_subst_commute] at firstBranchSubst secondBranchSubst
          rw [subst_universeCodeCell] at motiveSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (boolElimCell motive scrutinee firstBranch secondBranch))
            (RawTerm.subst substitution (RawTerm.subst0 motive scrutinee))
          rw [subst_boolElimCell, RawTerm.subst0_subst_commute]
          refine HasTypeUnion.elim targetContext .gen_boolElim boolElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution scrutinee)
                (.childCons (RawTerm.subst substitution firstBranch)
                  (.childCons (RawTerm.subst substitution secondBranch) .childNil))))
            .childNil level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact firstBranchSubst
            | tail _ hmem => cases hmem with
              | head => exact secondBranchSubst
              | tail _ hmem => cases hmem with
                | head => exact motiveSubst
                | tail _ hmem => cases hmem
      -- optionMatch row: DEPENDENT (union-substituent twin) — output `subst0 motive scrutinee`; the none
      -- branch is nullary at `subst0 motive optionNoneCell` (reshaped via `subst0_subst_commute`, the closed
      -- `optionNoneCell` defeq-erases), the some branch at the dependent some branch type (reshaped by
      -- `subst_optionMatchDependentSomeBranchType_iterateLift`), motive under one `optionTypeCell` binder
      -- (lifted via `SubstUnionTyped.cons`).
      · match args, params with
        | .childCons motive (.childCons noneBranch (.childCons someBranch (.childCons scrutinee .childNil))),
          .childCons typeParamA (.childCons typeParamB .childNil) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have noneBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have someBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          have motiveSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) _
              (iterateLiftRaw substitution 1)
              (HasTypeUnion.SubstUnionTyped.cons (optionTypeCell typeParamA) substitution condition)
          rw [subst_optionTypeCell] at scrutineeSubst
          rw [RawTerm.subst0_subst_commute] at noneBranchSubst
          rw [subst_optionMatchDependentSomeBranchType_iterateLift] at someBranchSubst
          rw [subst_universeCodeCell] at motiveSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (optionMatchCell motive noneBranch someBranch scrutinee))
            (RawTerm.subst substitution (RawTerm.subst0 motive scrutinee))
          rw [subst_optionMatchCell, RawTerm.subst0_subst_commute]
          refine HasTypeUnion.elim targetContext .gen_optionMatch optionMatchElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution noneBranch)
                (.childCons (RawTerm.subst substitution someBranch)
                  (.childCons (RawTerm.subst substitution scrutinee) .childNil))))
            (.childCons (RawTerm.subst substitution typeParamA)
              (.childCons (RawTerm.subst substitution typeParamB) .childNil))
            level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact noneBranchSubst
            | tail _ hmem => cases hmem with
              | head => exact someBranchSubst
              | tail _ hmem => cases hmem with
                | head => exact motiveSubst
                | tail _ hmem => cases hmem
      -- eitherMatch row: DEPENDENT (union-substituent twin) — output `subst0 motive scrutinee`; branches at
      -- the dependent inl/inr branch types (reshaped by the substitution-naturality corollaries), motive
      -- under one `eitherTypeCell` binder (lifted via `SubstUnionTyped.cons`).
      · match args, params with
        | .childCons motive (.childCons leftBranch (.childCons rightBranch (.childCons scrutinee .childNil))),
          .childCons typeParamA (.childCons typeParamB .childNil) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have leftBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have rightBranchSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          have motiveSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) _
              (iterateLiftRaw substitution 1)
              (HasTypeUnion.SubstUnionTyped.cons (eitherTypeCell typeParamA typeParamB) substitution condition)
          rw [subst_eitherTypeCell] at scrutineeSubst
          rw [subst_eitherMatchDependentInlBranchType_iterateLift] at leftBranchSubst
          rw [subst_eitherMatchDependentInrBranchType_iterateLift] at rightBranchSubst
          rw [subst_universeCodeCell] at motiveSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (eitherMatchCell motive leftBranch rightBranch scrutinee))
            (RawTerm.subst substitution (RawTerm.subst0 motive scrutinee))
          rw [subst_eitherMatchCell, RawTerm.subst0_subst_commute]
          refine HasTypeUnion.elim targetContext .gen_eitherMatch eitherMatchElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution leftBranch)
                (.childCons (RawTerm.subst substitution rightBranch)
                  (.childCons (RawTerm.subst substitution scrutinee) .childNil))))
            (.childCons (RawTerm.subst substitution typeParamA)
              (.childCons (RawTerm.subst substitution typeParamB) .childNil))
            level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact leftBranchSubst
            | tail _ hmem => cases hmem with
              | head => exact rightBranchSubst
              | tail _ hmem => cases hmem with
                | head => exact motiveSubst
                | tail _ hmem => cases hmem
      -- idJ row: DEPENDENT (union-substituent twin) — GENUINE Paulin-Mohring; output
      -- `idJMotiveAt motive right witness`, witness at the GENERAL `idTypeCell typeCode left right`, right
      -- endpoint at `typeCode`, base case at the diagonal `idJMotiveAt motive left (refl left)` (reshaped via
      -- `subst_idJMotiveAt_iterateLift` + `subst_reflCell`), motive under TWO binders (`typeCode`, then
      -- `idJMotiveSecondBinderType typeCode left`) at a universe (host condition via
      -- `SubstUnionTyped.consTwice`, inner binding reshaped via `subst_iterateLift_idJMotiveSecondBinderType`).
      · match args, params with
        | .childCons motive (.childCons baseCase (.childCons witness .childNil)),
          .childCons typeCode (.childCons leftEndpoint (.childCons rightEndpoint .childNil)) =>
          have witnessSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have rightEndpointSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have baseCaseSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          have motiveSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) _
              (iterateLiftRaw substitution 2)
              (HasTypeUnion.SubstUnionTyped.consTwice typeCode
                (idJMotiveSecondBinderType typeCode leftEndpoint) condition)
          rw [subst_idTypeCell] at witnessSubst
          rw [subst_idJMotiveAt_iterateLift, subst_reflCell] at baseCaseSubst
          rw [subst_iterateLift_idJMotiveSecondBinderType, subst_universeCodeCell] at motiveSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (idJCell motive baseCase witness))
            (RawTerm.subst substitution (idJMotiveAt motive rightEndpoint witness))
          rw [subst_idJCell, subst_idJMotiveAt_iterateLift]
          refine HasTypeUnion.elim targetContext .gen_idJ idJElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 2) motive)
              (.childCons (RawTerm.subst substitution baseCase)
                (.childCons (RawTerm.subst substitution witness) .childNil)))
            (.childCons (RawTerm.subst substitution typeCode)
              (.childCons (RawTerm.subst substitution leftEndpoint)
                (.childCons (RawTerm.subst substitution rightEndpoint) .childNil)))
            level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact witnessSubst
          | tail _ hmem => cases hmem with
            | head => exact rightEndpointSubst
            | tail _ hmem => cases hmem with
              | head => exact baseCaseSubst
              | tail _ hmem => cases hmem with
                | head => exact motiveSubst
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
          have resultSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          rw [subst_universeCodeCell] at resultSubst
          refine HasTypeUnion.elim targetContext .gen_fst fstElimRule
            (.childCons (RawTerm.subst substitution pairTerm) .childNil)
            (.childCons (RawTerm.subst substitution firstType)
              (.childCons (RawTerm.subst substitution secondType) .childNil))
            level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact pairSubst
          | tail _ hmem => cases hmem with
            | head => exact resultSubst
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
          have resultSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          rw [subst_universeCodeCell] at resultSubst
          refine HasTypeUnion.elim targetContext .gen_snd sndElimRule
            (.childCons (RawTerm.subst substitution pairTerm) .childNil)
            (.childCons (RawTerm.subst substitution firstType)
              (.childCons (RawTerm.subst substitution secondType) .childNil))
            level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact pairSubst
          | tail _ hmem => cases hmem with
            | head => exact resultSubst
            | tail _ hmem => cases hmem
      -- listElim row: DEPENDENT (union-substituent twin) — output `subst0 motive scrutinee`; the nil branch
      -- is nullary at `subst0 motive listNilCell` (reshaped via `subst0_subst_commute`, the closed `listNilCell`
      -- defeq-erases), the cons branch at the dependent cons-branch type (reshaped by
      -- `subst_listElimDependentConsBranchType_iterateLift`), motive under one `listTypeCell` binder (lifted via
      -- `SubstUnionTyped.cons`).  The list (recursive) twin of the optionMatch row; 2nd param vestigial.
      · match args, params with
        | .childCons motive (.childCons scrutinee (.childCons nilBranch (.childCons consBranch .childNil))),
          .childCons elementType (.childCons _resultType .childNil) =>
          have scrutineeSubst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have nilSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have consSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          have motiveSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) _
              (iterateLiftRaw substitution 1)
              (HasTypeUnion.SubstUnionTyped.cons (listTypeCell elementType) substitution condition)
          rw [subst_listTypeCell] at scrutineeSubst
          rw [RawTerm.subst0_subst_commute] at nilSubst
          rw [subst_listElimDependentConsBranchType_iterateLift] at consSubst
          rw [subst_universeCodeCell] at motiveSubst
          show HasTypeUnion profile targetContext
            (RawTerm.subst substitution (listElimCell motive scrutinee nilBranch consBranch))
            (RawTerm.subst substitution (RawTerm.subst0 motive scrutinee))
          rw [subst_listElimCell, RawTerm.subst0_subst_commute]
          refine HasTypeUnion.elim targetContext .gen_listElim listElimRule
            (.childCons (RawTerm.subst (iterateLiftRaw substitution 1) motive)
              (.childCons (RawTerm.subst substitution scrutinee)
                (.childCons (RawTerm.subst substitution nilBranch)
                  (.childCons (RawTerm.subst substitution consBranch) .childNil))))
            (.childCons (RawTerm.subst substitution elementType)
              (.childCons (RawTerm.subst substitution elementType) .childNil)) level0 level1 flag rfl ?_
          intro obligation hmem
          cases hmem with
          | head => exact scrutineeSubst
          | tail _ hmem => cases hmem with
            | head => exact nilSubst
            | tail _ hmem => cases hmem with
              | head => exact consSubst
              | tail _ hmem => cases hmem with
                | head => exact motiveSubst
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
          have leftFormSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          rw [subst_universeCodeCell] at leftFormSubst
          intro obligation hmem
          cases hmem with
          | head => exact valueSubst
          | tail _ hmem => cases hmem with
            | head => exact formSubst
            | tail _ hmem => cases hmem with
              | head => exact leftFormSubst
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
          have rightFormSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          rw [subst_universeCodeCell] at rightFormSubst
          intro obligation hmem
          cases hmem with
          | head => exact valueSubst
          | tail _ hmem => cases hmem with
            | head => exact formSubst
            | tail _ hmem => cases hmem with
              | head => exact rightFormSubst
              | tail _ hmem => cases hmem
      -- pair row
      · match args, params with
        | .childCons child0 (.childCons child1 .childNil),
          .childCons typeParam0 (.childCons typeParam1 .childNil) =>
          have child0Subst := ihPremises _ (List.Mem.head _) targetContext substitution condition
          have child1Subst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.head _)) targetContext substitution condition
          have firstFormSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
              targetContext substitution condition
          rw [subst_universeCodeCell] at firstFormSubst
          have secondFormSubst :=
            ihPremises _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
              targetContext substitution condition
          rw [subst_universeCodeCell] at secondFormSubst
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
            | tail _ hmem => cases hmem with
              | head => exact firstFormSubst
              | tail _ hmem => cases hmem with
                | head => exact secondFormSubst
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
rows took as residuals. -/

/-- **★ The union-substituent single-substitution lemma (the β / endpoint-β transport).**  A union body
typed at `codomain` under one binder, substituted at `var 0 := argument` with a UNION-typed `argument`, is
union-typed at the substituted codomain — `subst0 body argument : subst0 codomain argument`.  The exact
`UnionSubst0Transports` shape, discharged by instantiating `substRespectingContextUnionImages` at
`RawTermSubst.singleton argument` (`subst0 = subst (singleton _)` definitionally), the `Fin` `0` / `k+1`
split verbatim the host `substituteUnderBinding`'s with union images.  UNCONDITIONAL (wave U3). -/
theorem HasTypeUnion.subst0WithUnionImage {profile : PolyProfile}
    {scope : Nat} {context : TypingContext profile scope} {domain : RawTerm scope}
    {body codomain : RawTerm (scope + 1)} (argument : RawTerm scope)
    (bodyTyped : HasTypeUnion profile (context.cons domain) body codomain)
    (argumentTyped : HasTypeUnion profile context argument domain) :
    HasTypeUnion profile context
      (RawTerm.subst0 body argument) (RawTerm.subst0 codomain argument) := by
  refine bodyTyped.substRespectingContextUnionImages context
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
      exact HasTypeUnion.var context ⟨priorValue, Nat.lt_of_succ_lt_succ indexBound⟩

/-- **★ The union-substituent two-binder substitution lemma.**  A union derivation under two binders,
substituted simultaneously at `var 0 := innerArg, var 1 := outerArg` with BOTH substituents UNION-typed,
preserves `HasTypeUnion` with subject and classifier substituted.  The union-image mirror of
`HasTypeUnion.substPairUnderTwoBindings`, instantiating `substRespectingContextUnionImages` at
`cons innerArg (singleton outerArg)`.  UNCONDITIONAL (wave U3). -/
theorem HasTypeUnion.substPairUnderTwoBindingsUnionImages {profile : PolyProfile}
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
  refine derivation.substRespectingContextUnionImages context
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
          exact HasTypeUnion.var context ⟨priorValue,
            Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ indexBound)⟩

/-- **★ The recursor-step-shaped two-binder corollary (the natElim·natRec succ transport).**  A branch
typed in the UNION at a TWICE-WEAKENED result type under two binders, substituted at a UNION-typed
recursive result and a UNION-typed outer argument, is union-typed at the result type on the nose — both
weakenings cancel against the two substituents.  The exact `UnionSubstPairTransports` shape, the
union-image mirror of `HasTypeUnion.substPairNonDependent`.  UNCONDITIONAL (wave U3). -/
theorem HasTypeUnion.substPairNonDependentUnionImages {profile : PolyProfile}
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
    HasTypeUnion.substPairUnderTwoBindingsUnionImages innerArg outerArg branchTyped
      innerAtSubstituted outerArgTyped
  rwa [RawTerm.weaken_subst_cons, subst_singleton_renameWeaken_cancel] at substituted

/-! ## ★ The `UnionSubstPairTransports` shape, UNCONDITIONAL

The two-binder transport the succ subject-reduction rows premise (`UnionSubstPairTransports`, defined
in `HasTypeUnionSubstitution`) is an instance of `substPairNonDependentUnionImages`, which is itself
unconditional (wave U3).  So the succ-ι discharges (`natElimSuccIotaComputesTypedInUnion` /
`natRecSuccIotaComputesTypedInUnion`) — and thereby the natElim·natRec succ subject-reduction rows —
are unconditional. -/

/-- The DEPENDENT `UnionSubstPairTransports` shape is an instance of the general two-binder union-image
transport `substPairUnderTwoBindingsUnionImages` — the natElim·natRec succ 2-binder transport,
UNCONDITIONAL (wave U3).  The crux yields the reduct typed at `subst (cons innerArg (singleton outerArg))
(natElimDependentSuccBranchType motive)`, which `subst_natElimDependentSuccBranchType_succIota` collapses to
the dependent succ output `subst0 motive (natSuccCell outerArg)` (the second premise feeds directly since
`subst0 motive outerArg ≡ subst (singleton outerArg) motive`). -/
theorem unionSubstPairTransports {profile : PolyProfile}
    {scope : Nat} (context : TypingContext profile scope) (motive : RawTerm (scope + 1)) :
    UnionSubstPairTransports profile context motive :=
  fun branch innerArg outerArg branchTyped innerArgTyped outerArgTyped => by
    have substituted :=
      HasTypeUnion.substPairUnderTwoBindingsUnionImages innerArg outerArg branchTyped
        innerArgTyped outerArgTyped
    rwa [subst_natElimDependentSuccBranchType_succIota] at substituted

end FX1Poly.Typed

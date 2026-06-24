import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnly
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPi
import FX1Poly.Typed.Engine.RuleTables.IntroRuleTable
import FX1Poly.Typed.Engine.RuleTables.FormationRuleTable

/-! # FX1Poly/Typed/Engine/Union/HasTypeUnionNativeOnlyAdmissibility — host-engine admissibility (TYTAB-2 ADMIT)

The HEADLINE of TYTAB-2 ADMIT: every HOST `HasTypeDescPi` derivation is reproducible from the SIX native
arms alone (`var` / `universeFormation` / `formationRule` / `intro` / `elim` / `conv`), with NO `ofGrown`
embedding anywhere in the reflected tree.  Together with `HasTypeUnionNativeOnly.toUnion` (the easy
embedding, shipped in the foundation), this makes `ofGrown` PROVABLY REDUNDANT: `HasTypeUnion` (the kernel
judgment WITH `ofGrown`) and `HasTypeUnionNativeOnly` (WITHOUT it) classify exactly the same subjects.

## The reflection is the identity-substitution specialization of the substituent machinery

`HasTypeUnionUnionSubstituent` already carries a HOST derivation along a UNION-image SUBSTITUTION, landing
in `HasTypeUnion` through the native arms (`piIntro` → `intro@gen_lam`, `piElim` → `elim@gen_app`,
`genFormationPi` → the `.cumulative` `formationRule` row via `unionCumulativeFormerCloses`).  Its ONLY
`ofGrown` uses are the variable and universe LEAVES — which the TYTAB-2 VAR/UNIV wave replaced with native
arms.  ADMIT is that machinery at the IDENTITY substitution (so every `subst_*` commutation vanishes — the
reflection is strictly simpler) retargeted to `HasTypeUnionNativeOnly`, with the var/universe leaves taking
the native `var` / `universeFormation` arms.

## The four-relation reflection

`HasTypeDescPi` embeds the formation engine `HasTypeDesc` (via `ofFormation`), and each carries a cumulative
premise telescope (`DescTelescopePi` / `DescTelescope`).  So admissibility is a reflection over FOUR
relations.  Each formation telescope reflects FIRST into a native-headed mirror `DescTelescopeNativeOnly`
(cons-by-cons, clean structural recursion), and the standalone
`cumulativeFormationNativeOnlyPremiseToObligations` then discharges the (≤ 2) cumulative obligations from
that mirror — the union analogue's exact structure, sans `ofGrown`.  The cumulative former closes through
`nativeOnlyCumulativeFormerCloses` (the four ≥1-child codes via their `.cumulative` row; the nullary
`gen_unitCode` via its `baseType` row, output `Type@0` either way).

## Zero-axiom

`match` / `induction` over the host and union derivations + the cumulative-former dispatch + the native-arm
constructor applications.  The `lam` side condition is `gradedBinderChecks UsageGrade.omega body`, discharged
by `(gradedBinderChecks_spectrum body).1` (unconstrained at `omega`).  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditHasTypeUnionNativeOnlyAdmissibility.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax FX1Poly.Modal

/-- **The native-only formation telescope.**  The children form a cumulative dependent telescope of TYPES
at `levels`, each head typed by `HasTypeUnionNativeOnly` (the `ofGrown`-free judgment).  The native-only
mirror of `DescTelescopeUnion`, with the same fixed-`baseScope` / growing-`currentDepth` rebasing
discipline.  Its index signature references only first-order data (never `HasTypeUnionOver`), and
`HasTypeUnionNativeOnly` appears only POSITIVELY in `cons`'s `headTyped` — so it is strictly positive. -/
inductive DescTelescopeNativeOnly (profile : PolyProfile) :
    {baseScope : Nat} → {currentDepth : Nat} → {binderShifts : List Nat} →
      TypingContext profile (baseScope + currentDepth) →
      List LevelExpr → UniverseFlag →
      RawTermChildren binderShifts baseScope → Prop where
  | nil {baseScope : Nat} {currentDepth : Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (flag : UniverseFlag) :
      DescTelescopeNativeOnly profile context [] flag .childNil
  | cons {baseScope : Nat} {currentDepth : Nat} {restShifts : List Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (head : RawTerm (baseScope + currentDepth))
      (headLevel : LevelExpr) (restLevels : List LevelExpr) (flag : UniverseFlag)
      (rest : RawTermChildren restShifts baseScope)
      (headTyped :
        HasTypeUnionNativeOnly profile context head (universeCodeCell headLevel flag))
      (restTyped :
        DescTelescopeNativeOnly profile (currentDepth := currentDepth + 1)
          (context.cons head) restLevels flag rest) :
      DescTelescopeNativeOnly profile context (headLevel :: restLevels) flag
        (.childCons head rest)

/-- **The cumulative-family native-only bridge.**  A native-only cumulative dependent telescope discharges
every cumulative-family obligation: the binder-shape Π/Σ spine `[0, 1]` exposes the domain typing at the
ambient context and the codomain typing at the domain-extended context (each a `HasTypeUnionNativeOnly`),
matching the two obligations of `cumulativeFormationObligations`; the element-shape List/Option spine `[0]`
exposes the single element typing.  The native-only analogue of `cumulativeFormationUnionPremiseToObligations`,
sans the `ofGrown` lift (the heads are native-only-typed already).  Standalone (non-recursive: the obligation
list is bounded to ≤ 2 entries), so the cumulative dispatch reads cleanly. -/
theorem cumulativeFormationNativeOnlyPremiseToObligations {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {flag : UniverseFlag} {binderShifts : List Nat}
    {levels : List LevelExpr} {children : RawTermChildren binderShifts scope}
    (telescope : DescTelescopeNativeOnly profile (currentDepth := 0) context levels flag children) :
    ∀ obligation ∈ cumulativeFormationObligations profile context flag children levels,
      HasTypeUnionNativeOnly profile obligation.context obligation.subject obligation.classifier := by
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

/-- **The cumulative-former closes natively.**  The former `.mkGen generator payload children` is
native-only-typed at its output universe, for any `typingRuleDescOf` cumulative former (`gen_piTyCode` /
`gen_sigmaTyCode` / `gen_listCode` / `gen_optionCode` / `gen_unitCode`), given the children form a
NATIVE-ONLY telescope.  The four ≥1-child codes route through `HasTypeUnionNativeOnly.formationRule` at
their `.cumulative` formation row fed the bridged obligations; the nullary `gen_unitCode` routes through its
`baseType` formation row (the row `formationRuleOf` finds first), its output pinned to `Type@0` either way.
The native-only mirror of `unionCumulativeFormerCloses`. -/
theorem nativeOnlyCumulativeFormerCloses {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (generator : Generator)
    (payload : generator.payload scope) (children : RawTermChildren generator.binderShifts scope)
    (levels : List LevelExpr) (flag : UniverseFlag) (rule : TypingRuleDesc)
    (isCumulative : typingRuleDescOf generator = some rule)
    (telescope : DescTelescopeNativeOnly profile (currentDepth := 0) context levels flag children) :
    HasTypeUnionNativeOnly profile context (.mkGen generator payload children)
      (rule.outputType scope levels flag) := by
  by_cases isUnit : generator = Generator.gen_unitCode
  · -- Nullary unit code: route through the base-type formation row; output is Type@0 both ways.
    subst isUnit
    obtain ⟨baseRule, isBaseType⟩ :
        ∃ baseRule, baseTypeRuleDescOf Generator.gen_unitCode = some baseRule := ⟨_, rfl⟩
    have isBaseRow :
        formationRuleOf Generator.gen_unitCode = some (FormationRule.baseType baseRule) := by
      unfold formationRuleOf; rw [isBaseType]
    rw [typingRuleDescOf_unitCode_outputConstant isCumulative scope levels flag]
    have formed :
        HasTypeUnionNativeOnly profile context (.mkGen Generator.gen_unitCode payload children)
          ((FormationRule.baseType baseRule).outputType scope levels LevelExpr.lzero flag) :=
      HasTypeUnionNativeOnly.formationRule context Generator.gen_unitCode payload children
        (.baseType baseRule) levels (.mkGen Generator.gen_unitCode payload children) LevelExpr.lzero
        flag isBaseRow (by intro obligation hmem; cases hmem)
    have outputIsType0 :
        (FormationRule.baseType baseRule).outputType scope levels LevelExpr.lzero flag
          = universeCodeCell LevelExpr.lzero UniverseFlag.standard := by
      show baseRule.outputUniverse scope = universeCodeCell LevelExpr.lzero UniverseFlag.standard
      rw [baseTypeRuleTableOutputIsType0 isBaseType]
    rwa [outputIsType0] at formed
  · -- The four ≥1-child cumulative codes: rebuild through the `.cumulative` formation row.
    have isCumulativeRow : formationRuleOf generator = some (FormationRule.cumulative rule) :=
      formationRuleOf_cumulative isCumulative isUnit
    exact HasTypeUnionNativeOnly.formationRule context generator payload children
      (.cumulative rule) levels (.mkGen generator payload children) LevelExpr.lzero flag
      isCumulativeRow (cumulativeFormationNativeOnlyPremiseToObligations telescope)

/-! ## The base-engine leg: reflect a FORMATION `HasTypeDesc` derivation into the native arms -/

mutual

/-- Reflect a FORMATION derivation into the native-only judgment.  Mutual structural recursion on the
derivation; `var` → native `var`, `conv` → native `conv`, `universeFormation` → native `universeFormation`,
`genFormation` → the cumulative former closes through `nativeOnlyCumulativeFormerCloses` fed the companion's
native-only telescope.  ZERO `ofGrown`. -/
theorem HasTypeDesc.toNativeOnly {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDesc profile context subject classifier) :
    HasTypeUnionNativeOnly profile context subject classifier :=
  match derivation with
  | .var context index => HasTypeUnionNativeOnly.var context index
  | .conv levelExpr flag typed converts reclassifierTyped =>
      HasTypeUnionNativeOnly.conv levelExpr flag
        (HasTypeDesc.toNativeOnly typed) converts
        (HasTypeDesc.toNativeOnly reclassifierTyped)
  | .universeFormation context levelExpr flag =>
      HasTypeUnionNativeOnly.universeFormation context levelExpr flag
  | .genFormation context generator payload children levels flag rule isFormation premises =>
      nativeOnlyCumulativeFormerCloses context generator payload children levels flag rule
        isFormation (DescTelescope.toNativeOnlyTelescope premises)

/-- Companion: reflect a FORMATION premise spine into a native-only telescope.  Cons-by-cons: the head
through `HasTypeDesc.toNativeOnly`, the tail recursing under the binder. -/
theorem DescTelescope.toNativeOnlyTelescope {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile context levels flag children) :
    DescTelescopeNativeOnly profile context levels flag children :=
  match telescope with
  | .nil context flag => DescTelescopeNativeOnly.nil context flag
  | .cons context head headLevel restLevels flag rest headTyped restTyped =>
      DescTelescopeNativeOnly.cons context head headLevel restLevels flag rest
        (HasTypeDesc.toNativeOnly headTyped)
        (DescTelescope.toNativeOnlyTelescope restTyped)

end

/-! ## The grown-engine leg: reflect a HOST `HasTypeDescPi` derivation into the native arms -/

mutual

/-- **★ Reflect a HOST `HasTypeDescPi` derivation into the native-only judgment (TYTAB-2 ADMIT headline).**
The identity-substitution specialization of `hostSubstWithUnionImages`, retargeted to the `ofGrown`-free
judgment.  `ofFormation` routes through `HasTypeDesc.toNativeOnly`; `piIntro` rebuilds the λ via the native
`intro` arm at `gen_lam` (side condition `gradedBinderChecks omega` trivially holds); `piElim` rebuilds the
app via the native `elim` arm at `gen_app`; `genFormationPi` closes the cumulative former through
`nativeOnlyCumulativeFormerCloses`.  ZERO `ofGrown` — so every host derivation is reproducible from the
native arms alone, making `ofGrown` provably eliminable. -/
theorem HasTypeDescPi.toNativeOnly {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescPi profile context subject classifier) :
    HasTypeUnionNativeOnly profile context subject classifier :=
  match derivation with
  | .ofFormation formationTyped => HasTypeDesc.toNativeOnly formationTyped
  | .conv levelExpr flag typed converts reclassifierTyped =>
      HasTypeUnionNativeOnly.conv levelExpr flag
        (HasTypeDescPi.toNativeOnly typed) converts
        (HasTypeDescPi.toNativeOnly reclassifierTyped)
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => by
      refine HasTypeUnionNativeOnly.intro context .gen_lam lamIntroRule
        (.childCons domainCode (.childCons body .childNil))
        (.childCons codomainCode .childNil)
        domainLevel codomainLevel flag rfl (gradedBinderChecks_spectrum body).1 ?_
      intro obligation hmem
      cases hmem with
      | head => exact HasTypeDescPi.toNativeOnly domainTyped
      | tail _ hmem => cases hmem with
        | head => exact HasTypeDescPi.toNativeOnly codomainTyped
        | tail _ hmem => cases hmem with
          | head => exact HasTypeDescPi.toNativeOnly bodyTyped
          | tail _ hmem => cases hmem
  | @HasTypeDescPi.piElim _ _ _ functionTerm argument domainCode codomainCode
      functionTyped argumentTyped => by
      refine HasTypeUnionNativeOnly.elim context .gen_app appElimRule
        (.childCons functionTerm (.childCons argument .childNil))
        (.childCons domainCode (.childCons codomainCode .childNil))
        LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl ?_
      intro obligation hmem
      cases hmem with
      | head => exact HasTypeDescPi.toNativeOnly functionTyped
      | tail _ hmem => cases hmem with
        | head => exact HasTypeDescPi.toNativeOnly argumentTyped
        | tail _ hmem => cases hmem
  | .genFormationPi context generator payload children levels flag rule isFormation premises =>
      nativeOnlyCumulativeFormerCloses context generator payload children levels flag rule
        isFormation (DescTelescopePi.toNativeOnlyTelescope premises)

/-- Companion: reflect a GROWN premise spine into a native-only telescope.  The grown mirror of
`DescTelescope.toNativeOnlyTelescope`, head recursing the grown engine. -/
theorem DescTelescopePi.toNativeOnlyTelescope {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile context levels flag children) :
    DescTelescopeNativeOnly profile context levels flag children :=
  match telescope with
  | .nil context flag => DescTelescopeNativeOnly.nil context flag
  | .cons context head headLevel restLevels flag rest headTyped restTyped =>
      DescTelescopeNativeOnly.cons context head headLevel restLevels flag rest
        (HasTypeDescPi.toNativeOnly headTyped)
        (DescTelescopePi.toNativeOnlyTelescope restTyped)

end

/-! ## The redundancy of `ofGrown`: `HasTypeUnion` reflects fully into `HasTypeUnionNativeOnly` -/

/-- **★ Every kernel union derivation reflects into the native-only judgment (the inverse of `toUnion`).**
Each of the six native arms maps to its native-only twin (the recursive premises supplied by the induction
hypotheses).  Together with `HasTypeUnionNativeOnly.toUnion` this is a LOGICAL EQUIVALENCE `HasTypeUnion ↔
HasTypeUnionNativeOnly`.  This was the TYTAB-2 ADMIT capstone that proved `ofGrown` redundant — the
prerequisite for physically retiring the arm; with the arm now retired the two judgments are arm-aligned and
this reflection is the trivial structural map. -/
theorem HasTypeUnion.toNativeOnly {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeUnion profile context subject classifier) :
    HasTypeUnionNativeOnly profile context subject classifier := by
  induction derivation with
  | var context index => exact HasTypeUnionNativeOnly.var context index
  | universeFormation context levelExpr flag =>
      exact HasTypeUnionNativeOnly.universeFormation context levelExpr flag
  | conv levelExpr flag _typed converts _reclassifierTyped typedIH reclassifierIH =>
      exact HasTypeUnionNativeOnly.conv levelExpr flag typedIH converts reclassifierIH
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      _premisesHold ihPremises =>
      exact HasTypeUnionNativeOnly.formationRule context generator payload children rule levels carrier
        level flag isFormationRule ihPremises
  | intro context generator rule args params level0 level1 flag isIntro sideHolds _premisesHold
      ihPremises =>
      exact HasTypeUnionNativeOnly.intro context generator rule args params level0 level1 flag isIntro
        sideHolds ihPremises
  | elim context generator rule args params level0 level1 flag isElim _premisesHold ihPremises =>
      exact HasTypeUnionNativeOnly.elim context generator rule args params level0 level1 flag isElim
        ihPremises

/-! ## The packaged equivalence: `HasTypeUnion` and `HasTypeUnionNativeOnly` classify EXACTLY the same triples -/

/-- **★ THE TYTAB-2 ADMIT CAPSTONE — `HasTypeUnion` and `HasTypeUnionNativeOnly` classify the same triples.**
This equivalence was the formal prerequisite for physically retiring the host-engine escape hatch `ofGrown`:
it proved that the (then 7-arm) `HasTypeUnion` classified nothing beyond `HasTypeUnionNativeOnly`'s six native
arms, so the `ofGrown` arm carried no classifying power.  With the arm now retired both judgments are six-arm
and arm-aligned; the forward direction `toNativeOnly` reflects each native arm to its native-only twin and the
backward direction `toUnion` re-embeds.  Every consequence proved over one transports to the other by
rewriting along this `Iff`. -/
theorem HasTypeUnion.iff_nativeOnly {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope} :
    HasTypeUnion profile context subject classifier ↔
      HasTypeUnionNativeOnly profile context subject classifier :=
  ⟨HasTypeUnion.toNativeOnly, HasTypeUnionNativeOnly.toUnion⟩

end FX1Poly.Typed

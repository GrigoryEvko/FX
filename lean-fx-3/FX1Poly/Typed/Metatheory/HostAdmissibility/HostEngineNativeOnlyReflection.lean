import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnly
import FX1Poly.Typed.Engine.HasTypeDescPi.Core.HasTypeDescPi
import FX1Poly.Typed.Engine.RuleTables.IntroRuleTable
import FX1Poly.Typed.Engine.RuleTables.FormationRuleTable

/-! # FX1Poly/Typed/Metatheory/HostAdmissibility/HostEngineNativeOnlyReflection — host-engine → native-only reflection (TYTAB-2 ADMIT bridge)

Relocated out of `HasTypeUnionNativeOnlyAdmissibility` (B0-b) so the native union's `Union/` directory no
longer imports the grown engine.  These reflections carry a HOST `HasTypeDescPi` / formation `HasTypeDesc`
derivation into the `ofGrown`-free `HasTypeUnionNativeOnly` judgment — the scaffolding that proved `ofGrown`
redundant (the arm is now retired).  The native-only equivalence capstones (`HasTypeUnion.toNativeOnly`,
`HasTypeUnion.iff_nativeOnly`) stay in `HasTypeUnionNativeOnlyAdmissibility`, grown-engine-free.

## Zero-axiom

`match` / `induction` over the host and union derivations + the cumulative-former dispatch + the native-arm
constructor applications.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in
`FX1PolyAudit/Typed/Metatheory/HostAdmissibility/HostEngineNativeOnlyReflection.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax FX1Poly.Modal

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
    (telescope : DescTelescopeNativeOnly profile (currentDepth := 0) context levels flag children)
    (contextLockFree : context.isLockFreeContext = true) :
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
        (by intro obligation hmem; cases hmem)
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
      (FormationRule.obligationsUsableOfLockFree (.cumulative rule) context contextLockFree children
        levels (.mkGen generator payload children) LevelExpr.lzero flag)

/-! ## The base-engine leg: reflect a FORMATION `HasTypeDesc` derivation into the native arms -/

mutual

/-- Reflect a FORMATION derivation into the native-only judgment.  Mutual structural recursion on the
derivation; `var` → native `var`, `conv` → native `conv`, `universeFormation` → native `universeFormation`,
`genFormation` → the cumulative former closes through `nativeOnlyCumulativeFormerCloses` fed the companion's
native-only telescope.  ZERO `ofGrown`. -/
theorem HasTypeDesc.toNativeOnly {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDesc profile context subject classifier)
    (contextLockFree : context.isLockFreeContext = true) :
    HasTypeUnionNativeOnly profile context subject classifier :=
  match derivation with
  | .var context index =>
      HasTypeUnionNativeOnly.var context index (useModality := .fibrant)
        (context.lockFreeImpliesFibrantlyAccessible contextLockFree index)
  | .conv levelExpr flag typed converts reclassifierTyped =>
      HasTypeUnionNativeOnly.conv levelExpr flag
        (HasTypeDesc.toNativeOnly typed contextLockFree) converts
        (HasTypeDesc.toNativeOnly reclassifierTyped contextLockFree)
  | .universeFormation context levelExpr flag =>
      HasTypeUnionNativeOnly.universeFormation context levelExpr flag
  | .genFormation context generator payload children levels flag rule isFormation premises =>
      nativeOnlyCumulativeFormerCloses context generator payload children levels flag rule
        isFormation (DescTelescope.toNativeOnlyTelescope premises contextLockFree) contextLockFree

/-- Companion: reflect a FORMATION premise spine into a native-only telescope.  Cons-by-cons: the head
through `HasTypeDesc.toNativeOnly`, the tail recursing under the binder (which preserves lock-freeness). -/
theorem DescTelescope.toNativeOnlyTelescope {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescope profile context levels flag children)
    (contextLockFree : context.isLockFreeContext = true) :
    DescTelescopeNativeOnly profile context levels flag children :=
  match telescope with
  | .nil context flag => DescTelescopeNativeOnly.nil context flag
  | .cons context head headLevel restLevels flag rest headTyped restTyped =>
      DescTelescopeNativeOnly.cons context head headLevel restLevels flag rest
        (HasTypeDesc.toNativeOnly headTyped contextLockFree)
        (DescTelescope.toNativeOnlyTelescope restTyped
          ((isLockFreeContext_cons context head).trans contextLockFree))

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
    (derivation : HasTypeDescPi profile context subject classifier)
    (contextLockFree : context.isLockFreeContext = true) :
    HasTypeUnionNativeOnly profile context subject classifier :=
  match derivation with
  | .ofFormation formationTyped => HasTypeDesc.toNativeOnly formationTyped contextLockFree
  | .conv levelExpr flag typed converts reclassifierTyped =>
      HasTypeUnionNativeOnly.conv levelExpr flag
        (HasTypeDescPi.toNativeOnly typed contextLockFree) converts
        (HasTypeDescPi.toNativeOnly reclassifierTyped contextLockFree)
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => by
      -- The λ-body binds the domain, so its obligations live one `cons` deeper; `cons` preserves
      -- lock-freeness, so the codomain / body recursions stay over a lock-free context.
      have extendedLockFree : (context.cons domainCode).isLockFreeContext = true :=
        (isLockFreeContext_cons context domainCode).trans contextLockFree
      refine HasTypeUnionNativeOnly.intro context .gen_lam lamIntroRule
        (.childCons domainCode (.childCons body .childNil))
        (.childCons codomainCode .childNil)
        domainLevel codomainLevel flag rfl (gradedBinderChecks_spectrum body).1 ?_
        (by
          intro obligation hmem
          cases hmem with
          | head => exact context.lockFreeImpliesSubjectFibrantlyUsable contextLockFree _
          | tail _ hmem => cases hmem with
            | head =>
                exact (context.cons domainCode).lockFreeImpliesSubjectFibrantlyUsable extendedLockFree _
            | tail _ hmem => cases hmem with
              | head =>
                  exact (context.cons domainCode).lockFreeImpliesSubjectFibrantlyUsable extendedLockFree _
              | tail _ hmem => cases hmem)
      intro obligation hmem
      cases hmem with
      | head => exact HasTypeDescPi.toNativeOnly domainTyped contextLockFree
      | tail _ hmem => cases hmem with
        | head => exact HasTypeDescPi.toNativeOnly codomainTyped extendedLockFree
        | tail _ hmem => cases hmem with
          | head => exact HasTypeDescPi.toNativeOnly bodyTyped extendedLockFree
          | tail _ hmem => cases hmem
  | @HasTypeDescPi.piElim _ _ _ functionTerm argument domainCode codomainCode
      functionTyped argumentTyped => by
      refine HasTypeUnionNativeOnly.elim context .gen_app appElimRule
        (.childCons functionTerm (.childCons argument .childNil))
        (.childCons domainCode (.childCons codomainCode .childNil))
        LevelExpr.lzero LevelExpr.lzero UniverseFlag.standard rfl ?_
        (by
          intro obligation hmem
          cases hmem with
          | head => exact context.lockFreeImpliesSubjectFibrantlyUsable contextLockFree _
          | tail _ hmem => cases hmem with
            | head => exact context.lockFreeImpliesSubjectFibrantlyUsable contextLockFree _
            | tail _ hmem => cases hmem)
      intro obligation hmem
      cases hmem with
      | head => exact HasTypeDescPi.toNativeOnly functionTyped contextLockFree
      | tail _ hmem => cases hmem with
        | head => exact HasTypeDescPi.toNativeOnly argumentTyped contextLockFree
        | tail _ hmem => cases hmem
  | .genFormationPi context generator payload children levels flag rule isFormation premises =>
      nativeOnlyCumulativeFormerCloses context generator payload children levels flag rule
        isFormation (DescTelescopePi.toNativeOnlyTelescope premises contextLockFree) contextLockFree

/-- Companion: reflect a GROWN premise spine into a native-only telescope.  The grown mirror of
`DescTelescope.toNativeOnlyTelescope`, head recursing the grown engine. -/
theorem DescTelescopePi.toNativeOnlyTelescope {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile context levels flag children)
    (contextLockFree : context.isLockFreeContext = true) :
    DescTelescopeNativeOnly profile context levels flag children :=
  match telescope with
  | .nil context flag => DescTelescopeNativeOnly.nil context flag
  | .cons context head headLevel restLevels flag rest headTyped restTyped =>
      DescTelescopeNativeOnly.cons context head headLevel restLevels flag rest
        (HasTypeDescPi.toNativeOnly headTyped contextLockFree)
        (DescTelescopePi.toNativeOnlyTelescope restTyped
          ((isLockFreeContext_cons context head).trans contextLockFree))

end

end FX1Poly.Typed

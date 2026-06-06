import FX1Poly.Typed.HasTypeDescPiContextConversion
import FX1Poly.Typed.HasTypeDescContextConversion

/-! # FX1Poly/Typed/HasTypeDescPiContextConversionConditional
    — the grown-engine context-conversion mutual pair, conditional on the lone `piElim` crux (GCC-1/2/3/4/6)

Context-conversion for the GROWN engine `HasTypeDescPi` (typing stable under a pointwise-`Conv`-replaced
context) is the brick the grown telescope SR — hence the master SR dispatcher's `genFormationPi` arm (SN-055,
`#558`) — needs.  `HasTypeDescPiContextConversion.lean` (#814 part 2a) shipped only the two validity-free
HELPERS (`convBackToUniverseCode`, `convContextOfFormation`) and recorded that the full version is the mutual
FUNDAMENTAL-METATHEORY bundle, because its `piElim` arm needs "typing a `Conv`-equal Π type" = type-Conv-closure
(circular with SR).

This file ships the rest: the full mutual pair `HasTypeDescPi.convContext ⋈ DescTelescopePi.convTelescope`
with EVERY validity-free arm discharged, isolating the `piElim` arm as a single explicit hypothesis
(`piElimArm`) — the SRD-1 conditional-package discipline (`#664`/`#844`) applied to GCC.  The five non-`piElim`
arms are all here:

  * **`ofFormation`** — delegate to `convContextOfFormation` (formation context-conversion, re-embedded).
  * **`conv`** — recurse on the premise; compose the conversions (`Conv.trans converts.sym …`).
  * **`piIntro`** — domain / codomain conv-back to universe codes via `convBackToUniverseCode` (no validity);
    body conv-backed via the RECURSIVELY-obtained codomain re-typing under the extended context
    (`convContextCondition_cons`).  Validity-FREE — the memory's key observation made concrete.
  * **`genFormationPi`** — recurse the premise spine through the mutual `convTelescope`; re-fire `genFormationPi`.
  * **`piElim`** — the hypothesis (the lone hard arm).
  * **telescope `nil`/`cons`** — `cons` re-types the head via the mutual `convContext`, conv-backed through
    `convBackToUniverseCode`, and recurses the tail under the extended context.

Discharging `piElimArm` (GCC-5, the mutual fundamental-metatheory bundle: type-correctness + context-conversion +
SR — Π/Σ-code injectivity is NOT a bundle member: it ships SEPARATELY as the unconditional raw-confluence
corollary `Conv.piTyCode_injective` / `Conv.sigmaTyCode_injective`, PI-1/PI-2/PI-3, `#864`–`#866`, an
independently-available INPUT the bundle may cite) yields unconditional grown context-conversion — and
`convTelescopeOfPiElimArm` is exactly the grown telescope
context-conversion (GCC-3) the grown telescope SR consumes for its tail re-typing, which in turn discharges the
SR dispatcher's `telescopeSR` hypothesis (SRD-2, `#845`) toward unconditional SN-055.

## Zero-axiom verification

Mutual structural recursion on the derivation / telescope + `convContextOfFormation` + `convBackToUniverseCode`
+ `convContextCondition_cons` + the `conv` / `piIntro` / `genFormationPi` constructors + `Conv.trans` / `.sym` /
`.refl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

mutual

/-- **Grown-engine context-conversion, conditional on the `piElim` arm.**  A `HasTypeDescPi` derivation survives
replacing the context by a pointwise-`Conv`-related one — at a `Conv`-equal classifier — given the `piElim` arm
`piElimArm` (the lone validity-entangled case).  All other arms are discharged: `ofFormation` via
`convContextOfFormation`, `conv` by recursion + conversion composition, `piIntro` validity-free (components
conv-backed to universe codes; body via the recursively-obtained codomain re-typing), `genFormationPi` via the
mutual `convTelescope`. -/
theorem HasTypeDescPi.convContextOfPiElimArm {profile : PolyProfile}
    (piElimArm : ∀ {armScope : Nat} {armSrc : TypingContext profile armScope}
        {fn arg armDomain : RawTerm armScope} {armCodomain : RawTerm (armScope + 1)},
        HasTypeDescPi profile armSrc fn (piTyCodeCell armDomain armCodomain) →
        HasTypeDescPi profile armSrc arg armDomain →
        ∀ armTgt : TypingContext profile armScope,
          (∀ index : Fin armScope, Conv (armSrc.lookup index) (armTgt.lookup index)) →
          ∃ classifier', Conv (RawTerm.subst0 armCodomain arg) classifier' ∧
            HasTypeDescPi profile armTgt (appCell fn arg) classifier')
    {scope : Nat} {sourceContext : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescPi profile sourceContext subject classifier) :
    ∀ (targetContext : TypingContext profile scope),
      (∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      ∃ classifier', Conv classifier classifier' ∧
        HasTypeDescPi profile targetContext subject classifier' :=
  match derivation with
  | .ofFormation formationTyped => fun targetContext contextConv =>
      HasTypeDescPi.convContextOfFormation formationTyped targetContext contextConv
  | .conv levelExpr flag typed converts _reclassifierTyped => fun targetContext contextConv => by
      obtain ⟨classifier', convClassifierToClassifier', typedAtClassifier'⟩ :=
        HasTypeDescPi.convContextOfPiElimArm piElimArm typed targetContext contextConv
      exact ⟨classifier', Conv.trans converts.sym convClassifierToClassifier', typedAtClassifier'⟩
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => fun targetContext contextConv => by
      obtain ⟨_clsD, convD, domainAtClsD⟩ :=
        HasTypeDescPi.convContextOfPiElimArm piElimArm domainTyped targetContext contextConv
      have domainTyped' : HasTypeDescPi profile targetContext domainCode
          (universeCodeCell domainLevel flag) := domainAtClsD.convBackToUniverseCode convD
      obtain ⟨_clsC, convC, codomainAtClsC⟩ :=
        HasTypeDescPi.convContextOfPiElimArm piElimArm codomainTyped (targetContext.cons domainCode)
          (convContextCondition_cons domainCode contextConv)
      have codomainTyped' : HasTypeDescPi profile (targetContext.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag) := codomainAtClsC.convBackToUniverseCode convC
      obtain ⟨_clsBody, convBody, bodyAtClsBody⟩ :=
        HasTypeDescPi.convContextOfPiElimArm piElimArm bodyTyped (targetContext.cons domainCode)
          (convContextCondition_cons domainCode contextConv)
      have bodyTyped' : HasTypeDescPi profile (targetContext.cons domainCode) body codomainCode :=
        HasTypeDescPi.conv codomainLevel flag bodyAtClsBody convBody.sym codomainTyped'
      exact ⟨piTyCodeCell domainCode codomainCode, Conv.refl _,
        HasTypeDescPi.piIntro domainLevel codomainLevel flag domainTyped' codomainTyped' bodyTyped'⟩
  | .piElim functionTyped argumentTyped => fun targetContext contextConv =>
      piElimArm functionTyped argumentTyped targetContext contextConv
  | .genFormationPi _formerContext generator payload children levels flag rule isFormation premises =>
      fun targetContext contextConv =>
      ⟨rule.outputType scope levels flag, Conv.refl _,
        HasTypeDescPi.genFormationPi targetContext generator payload children levels flag rule
          isFormation
          (DescTelescopePi.convTelescopeOfPiElimArm piElimArm premises targetContext contextConv)⟩

/-- **Grown premise-telescope context-conversion, conditional on the `piElim` arm** (the mutual companion).
Re-types each head via the mutual `convContextOfPiElimArm` (conv-backed to its universe code through
`convBackToUniverseCode`) and recurses the tail under the extended context (`convContextCondition_cons`).  This
is the grown telescope context-conversion (GCC-3) the grown telescope SR consumes for its tail re-typing. -/
theorem DescTelescopePi.convTelescopeOfPiElimArm {profile : PolyProfile}
    (piElimArm : ∀ {armScope : Nat} {armSrc : TypingContext profile armScope}
        {fn arg armDomain : RawTerm armScope} {armCodomain : RawTerm (armScope + 1)},
        HasTypeDescPi profile armSrc fn (piTyCodeCell armDomain armCodomain) →
        HasTypeDescPi profile armSrc arg armDomain →
        ∀ armTgt : TypingContext profile armScope,
          (∀ index : Fin armScope, Conv (armSrc.lookup index) (armTgt.lookup index)) →
          ∃ classifier', Conv (RawTerm.subst0 armCodomain arg) classifier' ∧
            HasTypeDescPi profile armTgt (appCell fn arg) classifier')
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile sourceContext levels flag children) :
    ∀ (targetContext : TypingContext profile (baseScope + currentDepth)),
      (∀ index : Fin (baseScope + currentDepth),
        Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      DescTelescopePi profile targetContext levels flag children :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _contextConv =>
      DescTelescopePi.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext contextConv => by
        obtain ⟨_headClassifier, headConv, headAtClassifier⟩ :=
          HasTypeDescPi.convContextOfPiElimArm piElimArm headTyped targetContext contextConv
        have headTyped' : HasTypeDescPi profile targetContext head (universeCodeCell headLevel flag) :=
          headAtClassifier.convBackToUniverseCode headConv
        refine DescTelescopePi.cons targetContext head headLevel restLevels flag rest headTyped' ?_
        exact DescTelescopePi.convTelescopeOfPiElimArm piElimArm restTyped (targetContext.cons head)
          (convContextCondition_cons head contextConv)

end

end FX1Poly.Typed

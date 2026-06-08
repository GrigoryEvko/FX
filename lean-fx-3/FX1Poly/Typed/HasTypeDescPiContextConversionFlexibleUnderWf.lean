import FX1Poly.Typed.HasTypeDescPiContextConversion
import FX1Poly.Typed.HasTypeDescContextConversion
import FX1Poly.Typed.HasTypeDescPiContextConversionPiElimUnderWf
import FX1Poly.Typed.HasTypeDescPiClassifierValidity

/-! # FX1Poly/Typed/HasTypeDescPiContextConversionFlexibleUnderWf
    — the GROWN context conversion, UNCONDITIONAL under target well-formedness (closes GrownCtxConv-5's piElim arm)

`HasTypeDescPiContextConversionConditional.lean` shipped the grown context-conversion mutual
`convContextOfPiElimArm ⋈ convTelescopeOfPiElimArm` with every arm discharged EXCEPT the `piElim` arm, which it
factored out as a hypothesis (GrownCtxConv-5, `#842`) — believed to need the intrinsic logical relation, because the
`var` arm of a wf-FREE arbitrary-`Conv` conversion needs "`IsType` respects `Conv`", which is FALSE
(`classifierRespectsConv`, refuted in `#1058`).

This file discharges that arm — at the cost of carrying the TARGET context's well-formedness `WfContextDescPi
targetContext` (a benign, decidable presupposition).  The two changes versus the conditional template:

  * the **`piElim` arm** uses `HasTypeDescPi.piElimArmUnderWfTarget` (the flexible, residual-free piElim arm):
    re-type the function and argument by the IH, derive the function's classifier-validity from its converted
    typing via `classifierIsTypeDescPi` (this is the only use of the target wf in the arm), and reform;
  * the **`var` arm needs no wf** — the var RULE types `var k` at `targetContext.lookup k` unconditionally, and
    the context `Conv` gives `classifier' = targetContext.lookup k`.

Target wf threads through and is EXTENDED at the two binder-crossing arms (`piIntro` and telescope `cons`) via
`WfContextDescPi.cons` with the recursively re-typed domain/head validity.

## Why target wf, not wf-free — the honest boundary

The wf-FREE arbitrary-`Conv` grown context conversion is genuinely logical-relation-bound: its `var`/`piElim`
arms need to transport a binding's or function-classifier's VALIDITY from source to target, and "validity
transports across a pointwise-`Conv` context" is itself the same obstruction (the source→target well-formedness
bridge `IsTypeDescPi src (src i) → Conv (src i) (tgt i) → IsTypeDescPi tgt (tgt i)` is circular with this very
theorem).  Carrying the TARGET wf cuts that knot: every needed target-context validity is read off
`WfContextDescPi.lookupIsType` / `classifierIsTypeDescPi` directly.  So "grown context conversion under target wf"
is the MAXIMAL structural closure of GrownCtxConv-5 — unconditional modulo a presupposition of exactly the same
benign character as SN-043's `WfContext` (`HasTypeDescPi → WfContextDesc` is itself refuted, `ContextValidityFails`).
The grown master subject reduction does NOT consume this (SR-U4 routed it through the EXACT directed conversion),
so the consumers are already served; this is the standalone GrownCtxConv-5 result.

## Zero-axiom verification

Mutual structural recursion on the derivation / telescope + `convContextOfFormation` + `convBackToUniverseCode`
+ `convContextCondition_cons` + `piElimArmUnderWfTarget` + `classifierIsTypeDescPi` + `WfContextDescPi.cons` +
`Conv.trans`/`.sym`/`.refl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

mutual

/-- **★ The grown-engine context conversion, UNCONDITIONAL under target well-formedness.**  A `HasTypeDescPi`
derivation survives replacing the context by a pointwise-`Conv`-related one — at a `Conv`-equal classifier —
given the TARGET context's well-formedness `WfContextDescPi targetContext`.  The `piElim` arm (the
GrownCtxConv-5 crux) is discharged via `piElimArmUnderWfTarget`; the `var`-style leaves are wf-free; target wf is
extended at the binder arms.  No `piElim` hypothesis, no logical relation. -/
theorem HasTypeDescPi.convContextUnderWf {profile : PolyProfile}
    {scope : Nat} {sourceContext : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescPi profile sourceContext subject classifier) :
    ∀ (targetContext : TypingContext profile scope),
      WfContextDescPi targetContext →
      (∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      ∃ classifier', Conv classifier classifier' ∧
        HasTypeDescPi profile targetContext subject classifier' :=
  match derivation with
  | .ofFormation formationTyped => fun targetContext _targetWf contextConv =>
      HasTypeDescPi.convContextOfFormation formationTyped targetContext contextConv
  | .conv levelExpr flag typed converts _reclassifierTyped =>
      fun targetContext targetWf contextConv => by
      obtain ⟨classifier', convClassifierToClassifier', typedAtClassifier'⟩ :=
        HasTypeDescPi.convContextUnderWf typed targetContext targetWf contextConv
      exact ⟨classifier', Conv.trans converts.sym convClassifierToClassifier', typedAtClassifier'⟩
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => fun targetContext targetWf contextConv => by
      obtain ⟨_clsD, convD, domainAtClsD⟩ :=
        HasTypeDescPi.convContextUnderWf domainTyped targetContext targetWf contextConv
      have domainTyped' : HasTypeDescPi profile targetContext domainCode
          (universeCodeCell domainLevel flag) := domainAtClsD.convBackToUniverseCode convD
      have extendedWf : WfContextDescPi (targetContext.cons domainCode) :=
        WfContextDescPi.cons targetWf ⟨domainLevel, flag, domainTyped'⟩
      obtain ⟨_clsC, convC, codomainAtClsC⟩ :=
        HasTypeDescPi.convContextUnderWf codomainTyped (targetContext.cons domainCode)
          extendedWf (convContextCondition_cons domainCode contextConv)
      have codomainTyped' : HasTypeDescPi profile (targetContext.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag) := codomainAtClsC.convBackToUniverseCode convC
      obtain ⟨_clsBody, convBody, bodyAtClsBody⟩ :=
        HasTypeDescPi.convContextUnderWf bodyTyped (targetContext.cons domainCode)
          extendedWf (convContextCondition_cons domainCode contextConv)
      have bodyTyped' : HasTypeDescPi profile (targetContext.cons domainCode) body codomainCode :=
        HasTypeDescPi.conv codomainLevel flag bodyAtClsBody convBody.sym codomainTyped'
      exact ⟨piTyCodeCell domainCode codomainCode, Conv.refl _,
        HasTypeDescPi.piIntro domainLevel codomainLevel flag domainTyped' codomainTyped' bodyTyped'⟩
  | .piElim functionTyped argumentTyped => fun targetContext targetWf contextConv => by
      obtain ⟨functionClassifier, convToFunctionClassifier, functionAtClassifier⟩ :=
        HasTypeDescPi.convContextUnderWf functionTyped targetContext targetWf contextConv
      exact HasTypeDescPi.piElimArmUnderWfTarget targetWf
        ⟨functionClassifier, convToFunctionClassifier,
          HasTypeDescPi.classifierIsTypeDescPi targetWf functionAtClassifier⟩
        ⟨functionClassifier, convToFunctionClassifier, functionAtClassifier⟩
        (HasTypeDescPi.convContextUnderWf argumentTyped targetContext targetWf contextConv)
  | .genFormationPi _formerContext generator payload children levels flag rule isFormation premises =>
      fun targetContext targetWf contextConv =>
      ⟨rule.outputType scope levels flag, Conv.refl _,
        HasTypeDescPi.genFormationPi targetContext generator payload children levels flag rule
          isFormation
          (DescTelescopePi.convTelescopeUnderWf premises targetContext targetWf contextConv)⟩

/-- **The grown premise-telescope context conversion under target well-formedness** (the mutual companion).
Re-types each head via the mutual `convContextUnderWf` (conv-backed to its universe code) and recurses the tail
under the extended context + extended target wf. -/
theorem DescTelescopePi.convTelescopeUnderWf {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile sourceContext levels flag children) :
    ∀ (targetContext : TypingContext profile (baseScope + currentDepth)),
      WfContextDescPi targetContext →
      (∀ index : Fin (baseScope + currentDepth),
        Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      DescTelescopePi profile targetContext levels flag children :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _targetWf _contextConv =>
      DescTelescopePi.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext targetWf contextConv => by
        obtain ⟨_headClassifier, headConv, headAtClassifier⟩ :=
          HasTypeDescPi.convContextUnderWf headTyped targetContext targetWf contextConv
        have headTyped' : HasTypeDescPi profile targetContext head (universeCodeCell headLevel flag) :=
          headAtClassifier.convBackToUniverseCode headConv
        have extendedWf : WfContextDescPi (targetContext.cons head) :=
          WfContextDescPi.cons targetWf ⟨headLevel, flag, headTyped'⟩
        refine DescTelescopePi.cons targetContext head headLevel restLevels flag rest headTyped' ?_
        exact DescTelescopePi.convTelescopeUnderWf restTyped (targetContext.cons head)
          extendedWf (convContextCondition_cons head contextConv)

end

end FX1Poly.Typed

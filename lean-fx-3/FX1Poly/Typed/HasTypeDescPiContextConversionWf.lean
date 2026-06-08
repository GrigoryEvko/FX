import FX1Poly.Typed.HasTypeDescPiContextConversionPiElimReduction
import FX1Poly.Typed.HasTypeDescPiContextConversionConditional
import FX1Poly.Typed.WfContextDescPi

/-! # FX1Poly/Typed/HasTypeDescPiContextConversionWf
    — WfContext-threaded grown context-conversion, conditional on the MINIMAL Pi-validity residual (GCC-5-WFTHREAD)

The conditional grown context-conversion (`HasTypeDescPi.convContextOfPiElimArm`, GCC-1..4/#838-841) is
conditional on the OPAQUE full `piElimArm` hypothesis — the entire elimination arm.  `#1092` (GCC-5-REASSEMBLY)
showed the piElim arm reduces to a SINGLE pure type-formation residual,
`ConvContextPreservesPiValidity` (a `Π`-type-code's validity is context-conversion-stable), modulo source
well-formedness `WfContextDescPi` and the convContext IH.  This file delivers the consequence: a grown
context-conversion mutual pair conditional on that MINIMAL residual instead of the opaque arm, threading
`WfContextDescPi` properly so the piElim arm can be INLINED.

This strictly improves on `convContextOfPiElimArm`:

  * **the residual shrinks** from the whole `piElimArm` (function + argument + reassembly) to the single
    type-formation fact `ConvContextPreservesPiValidity` — clearly what remains for GCC-5 (`#842`);
  * **`WfContextDescPi` is threaded**, which the master subject-reduction dispatcher already carries, so the
    result is directly consumable;
  * **the piElim arm is inlined** via `piElimArmFromPiValidityTransfer` (#1092) — using the threaded `wfSrc`
    (→ `classifierIsTypeDescPi`/WFG-3 source `Π`-validity), the residual (→ target `Π`-validity), and the
    recursive convContext IH on the function/argument children — confirming the reduction is real, not a
    restatement.

`WfContextDescPi` is a structural `def` (`WfContextDescPi (Γ.cons A) = WfContextDescPi Γ ∧ IsTypeDescPi Γ A`),
so at each binder (`piIntro` domain, telescope `cons` head) the extended well-formedness is built directly from
the SOURCE-side domain/head typing via `WfContextDescPi.cons` — every recursive call's well-formedness is
discharged from premises already present, no extra hypothesis.

## The arms

  * `ofFormation` — delegate to the unconditional formation context-conversion (`convContextOfFormation`).
  * `conv` — recurse on the premise; compose conversions.
  * `piIntro` — domain/codomain conv-backed to universe codes; body re-typed under the binder, with the
    extended `WfContextDescPi (Γ.cons domain)` built from the domain typing.
  * `piElim` — **INLINED** via `piElimArmFromPiValidityTransfer` (residual + threaded `wfSrc` + the two
    recursive convContext IHs).
  * `genFormationPi` — recurse the premise spine through the mutual `convTelescopeWfOfPiValidity`.
  * telescope `nil`/`cons` — `cons` re-types the head, threads the extended well-formedness, recurses the tail.

Discharging `ConvContextPreservesPiValidity` (the lone open obligation; genuinely the mutual
fundamental-metatheory bundle GTL-20 or the semantic/reflection route — see `#1092`) makes BOTH this pair and
`convContextOfPiElimArm` unconditional.

## Zero-axiom verification

Mutual structural recursion on the derivation / telescope + `convContextOfFormation` + `convBackToUniverseCode`
+ `convContextCondition_cons` + `WfContextDescPi.cons` + `piElimArmFromPiValidityTransfer` + the `conv` /
`piIntro` / `genFormationPi` constructors + `Conv.trans` / `.sym` / `.refl`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

mutual

/-- **WfContext-threaded grown context-conversion, conditional on the minimal `Π`-validity residual.**  A
`HasTypeDescPi` derivation in a grown-well-formed context survives replacing the context by a
pointwise-`Conv`-related one, at a `Conv`-equal classifier, given only `ConvContextPreservesPiValidity` (the
type-formation residual).  The piElim arm is inlined (no opaque `piElimArm` hypothesis); the well-formedness is
threaded and extended at each binder from the source-side premises. -/
theorem HasTypeDescPi.convContextWfOfPiValidity {profile : PolyProfile}
    (piValidityTransfers : ConvContextPreservesPiValidity profile)
    {scope : Nat} {sourceContext : TypingContext profile scope} {subject classifier : RawTerm scope}
    (sourceWellFormed : WfContextDescPi sourceContext)
    (derivation : HasTypeDescPi profile sourceContext subject classifier) :
    ∀ (targetContext : TypingContext profile scope),
      (∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      ∃ classifier', Conv classifier classifier' ∧
        HasTypeDescPi profile targetContext subject classifier' :=
  match derivation with
  | .ofFormation formationTyped => fun targetContext contextConv =>
      HasTypeDescPi.convContextOfFormation formationTyped targetContext contextConv
  | .conv _levelExpr _flag typed converts _reclassifierTyped => fun targetContext contextConv => by
      obtain ⟨classifier', convClassifierToClassifier', typedAtClassifier'⟩ :=
        HasTypeDescPi.convContextWfOfPiValidity piValidityTransfers sourceWellFormed typed
          targetContext contextConv
      exact ⟨classifier', Conv.trans converts.sym convClassifierToClassifier', typedAtClassifier'⟩
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => fun targetContext contextConv => by
      have wfExtended : WfContextDescPi (sourceContext.cons domainCode) :=
        WfContextDescPi.cons sourceWellFormed ⟨domainLevel, flag, domainTyped⟩
      obtain ⟨_clsD, convD, domainAtClsD⟩ :=
        HasTypeDescPi.convContextWfOfPiValidity piValidityTransfers sourceWellFormed domainTyped
          targetContext contextConv
      have domainTyped' : HasTypeDescPi profile targetContext domainCode
          (universeCodeCell domainLevel flag) := domainAtClsD.convBackToUniverseCode convD
      obtain ⟨_clsC, convC, codomainAtClsC⟩ :=
        HasTypeDescPi.convContextWfOfPiValidity piValidityTransfers wfExtended codomainTyped
          (targetContext.cons domainCode) (convContextCondition_cons domainCode contextConv)
      have codomainTyped' : HasTypeDescPi profile (targetContext.cons domainCode) codomainCode
          (universeCodeCell codomainLevel flag) := codomainAtClsC.convBackToUniverseCode convC
      obtain ⟨_clsBody, convBody, bodyAtClsBody⟩ :=
        HasTypeDescPi.convContextWfOfPiValidity piValidityTransfers wfExtended bodyTyped
          (targetContext.cons domainCode) (convContextCondition_cons domainCode contextConv)
      have bodyTyped' : HasTypeDescPi profile (targetContext.cons domainCode) body codomainCode :=
        HasTypeDescPi.conv codomainLevel flag bodyAtClsBody convBody.sym codomainTyped'
      exact ⟨piTyCodeCell domainCode codomainCode, Conv.refl _,
        HasTypeDescPi.piIntro domainLevel codomainLevel flag domainTyped' codomainTyped' bodyTyped'⟩
  | .piElim functionTyped argumentTyped => fun targetContext contextConv =>
      HasTypeDescPi.piElimArmFromPiValidityTransfer piValidityTransfers sourceWellFormed
        functionTyped contextConv
        (HasTypeDescPi.convContextWfOfPiValidity piValidityTransfers sourceWellFormed functionTyped
          targetContext contextConv)
        (HasTypeDescPi.convContextWfOfPiValidity piValidityTransfers sourceWellFormed argumentTyped
          targetContext contextConv)
  | .genFormationPi _formerContext generator payload children levels flag rule isFormation premises =>
      fun targetContext contextConv =>
      ⟨rule.outputType scope levels flag, Conv.refl _,
        HasTypeDescPi.genFormationPi targetContext generator payload children levels flag rule
          isFormation
          (DescTelescopePi.convTelescopeWfOfPiValidity piValidityTransfers premises sourceWellFormed
            targetContext contextConv)⟩

/-- **The mutual telescope companion.**  Re-types each premise head via the mutual
`convContextWfOfPiValidity` (conv-backed to its universe code) and recurses the tail under the extended context,
threading the extended well-formedness `WfContextDescPi (Γ.cons head)` built from the head typing.  The telescope
argument precedes the well-formedness so the `baseScope`/`currentDepth` split is pinned by the telescope's
children index before the (sum-only) well-formedness is checked. -/
theorem DescTelescopePi.convTelescopeWfOfPiValidity {profile : PolyProfile}
    (piValidityTransfers : ConvContextPreservesPiValidity profile)
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile sourceContext levels flag children)
    (sourceWellFormed : WfContextDescPi sourceContext) :
    ∀ (targetContext : TypingContext profile (baseScope + currentDepth)),
      (∀ index : Fin (baseScope + currentDepth),
        Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      DescTelescopePi profile targetContext levels flag children :=
  match telescope, sourceWellFormed with
  | .nil _telescopeContext flag, _wfMatched => fun targetContext _contextConv =>
      DescTelescopePi.nil targetContext flag
  | .cons _telescopeContext head headLevel restLevels flag rest headTyped restTyped, wfMatched =>
      fun targetContext contextConv => by
        have wfExtended : WfContextDescPi (_telescopeContext.cons head) :=
          WfContextDescPi.cons wfMatched ⟨headLevel, flag, headTyped⟩
        obtain ⟨_headClassifier, headConv, headAtClassifier⟩ :=
          HasTypeDescPi.convContextWfOfPiValidity piValidityTransfers wfMatched headTyped
            targetContext contextConv
        have headTyped' : HasTypeDescPi profile targetContext head (universeCodeCell headLevel flag) :=
          headAtClassifier.convBackToUniverseCode headConv
        refine DescTelescopePi.cons targetContext head headLevel restLevels flag rest headTyped' ?_
        exact DescTelescopePi.convTelescopeWfOfPiValidity piValidityTransfers restTyped wfExtended
          (targetContext.cons head) (convContextCondition_cons head contextConv)

end

end FX1Poly.Typed

import FX1Poly.Typed.TypedTypeValidityLeveledTransport
import FX1Poly.Typed.HasTypeDescPiContextConversionFlexibleUnderWf

/-! # FX1Poly/Typed/TypedTypeValidityLeveledTransportUnderWf
    — the leveled transport's `neutralRecon` hypothesis DISCHARGED under target well-formedness

`TypedTypeValidityLeveled.transport` (#1125) is conditional on ONE hypothesis: `neutralRecon`, the
Abel-reflection reconstruction of a NEUTRAL type code's exact universe-code typing across a pointwise-`Conv`
context conversion.  At the time it shipped, that was the genuine open core (the var-headed leaf #1119 plus
an open application-spine case, circular with the LR itself).

SR-U5 (#1133) then closed the grown context conversion UNCONDITIONALLY under target well-formedness:
`HasTypeDescPi.convContextUnderWf` re-types ANY grown subject across a pointwise-`Conv` conversion at a
`Conv`-equal classifier, given `WfContextDescPi targetContext`.  Composed with `convBackToUniverseCode`
(which pins a `Conv`-reached classifier back to its exact universe code, the universe code's own validity
being FREE via `universeFormation`), this discharges `neutralRecon` outright — the `IsNeutral` premise is
not even needed.  Nobody had walked back to the transport with this; this file does.

  * `HasTypeDescPi.universeClassifiedConvContextUnderWf` — the discharge: a subject typed at an EXACT
    universe code survives pointwise-`Conv` context conversion at that SAME exact universe code, given
    target wf.  `convContextUnderWf` + `convBackToUniverseCode`, two lines.
  * `TypedTypeValidityLeveled.transportUnderWf` — the leveled-LR transport re-run with the neutral arm
    discharged: conditional ONLY on `WfContextDescPi targetContext`.  The `piType` arm extends the target
    wf at the binder via the transported domain's own exact universe typing (`toHasTypeDescPi` wrapped as
    `IsTypeDescPi`) — the same wf-extension move as `convContextUnderWf`'s `piIntro` arm.  Crucially the
    CANDIDATE BOX is preserved: this transports the logical-relation STRUCTURE, not just the typing — the
    object the grown-strengthening campaign's LR-completeness leg works with.
  * `TypedTypeValidityLeveled.transportValidityUnderWf` — the validity payoff at the GrownCtxConv-5
    residual's shape, wf-conditional.

This converts the #1168 (grown strengthening) dependency chain's `neutralRecon` link from an OPEN research
hypothesis into the same benign `WfContextDescPi` presupposition that SN-043 / OSN-1 already carry.

## Zero-axiom verification

`induction` on the leveled relation: `neutral` → `universeClassifiedConvContextUnderWf`; `universeType` →
`universeFormation` rebuild; `piType` → two IHs (the codomain under `convContextCondition_cons` + wf
extended by `WfContextDescPi.cons`) + `piFormationViaGenArm` on the `toHasTypeDescPi` projections.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The `neutralRecon` discharge under target well-formedness.**  A subject typed at an EXACT universe
code survives pointwise-`Conv` context conversion at that same exact universe code, given
`WfContextDescPi targetContext`: `convContextUnderWf` (#1133) lands it at a `Conv`-equal classifier and
`convBackToUniverseCode` pins the classifier back (the universe code's validity is free via
`universeFormation`).  Subsumes the leveled transport's `neutralRecon` hypothesis — the `IsNeutral`
premise is not needed. -/
theorem HasTypeDescPi.universeClassifiedConvContextUnderWf {profile : PolyProfile} {scope : Nat}
    {sourceContext targetContext : TypingContext profile scope}
    {subject : RawTerm scope} {level : LevelExpr} {flag : UniverseFlag}
    (targetWf : WfContextDescPi targetContext)
    (typed : HasTypeDescPi profile sourceContext subject (universeCodeCell level flag))
    (contextConv : ∀ index : Fin scope,
      Conv (sourceContext.lookup index) (targetContext.lookup index)) :
    HasTypeDescPi profile targetContext subject (universeCodeCell level flag) := by
  obtain ⟨reachedCode, universeConvToReached, typedAtReached⟩ :=
    HasTypeDescPi.convContextUnderWf typed targetContext targetWf contextConv
  exact typedAtReached.convBackToUniverseCode universeConvToReached

/-- **★ The leveled-LR transport with the neutral arm DISCHARGED** — conditional only on target
well-formedness.  By induction on the leveled relation: `neutral` →
`universeClassifiedConvContextUnderWf`; `universeType` → free `universeFormation` rebuild; `piType` →
recurse (the codomain under the cons-lifted condition, with target wf extended at the binder via the
transported domain's exact universe typing) and rebuild via `piFormationViaGenArm`.  The candidate box is
preserved throughout — this transports the logical-relation STRUCTURE across context conversion. -/
theorem TypedTypeValidityLeveled.transportUnderWf {profile : PolyProfile}
    {scope : Nat} {sourceContext : TypingContext profile scope} {typeCode : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag} {box : KripkeCandBox scope}
    (relation : TypedTypeValidityLeveled profile sourceContext typeCode level flag box) :
    ∀ (targetContext : TypingContext profile scope),
      WfContextDescPi targetContext →
      (∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      TypedTypeValidityLeveled profile targetContext typeCode level flag box := by
  induction relation with
  | neutral neutralCode validity =>
      intro targetContext targetWf contextConv
      exact TypedTypeValidityLeveled.neutral neutralCode
        (HasTypeDescPi.universeClassifiedConvContextUnderWf targetWf validity contextConv)
  | @universeType _armScope _armContext levelExpr armFlag _validity =>
      intro targetContext _targetWf _contextConv
      exact TypedTypeValidityLeveled.universeType
        (HasTypeDescPi.ofFormation
          (HasTypeDesc.universeFormation targetContext levelExpr armFlag))
  | @piType _armScope _armContext domainCode _codomainCode domainLevel codomainLevel armFlag
      _domainBox _codomainBox codomainFamily _domainValid _codomainValid _validity
      domainIH codomainIH =>
      intro targetContext targetWf contextConv
      have domainValid' := domainIH targetContext targetWf contextConv
      have extendedWf : WfContextDescPi (targetContext.cons domainCode) :=
        WfContextDescPi.cons targetWf ⟨domainLevel, armFlag, domainValid'.toHasTypeDescPi⟩
      have codomainValid' :=
        codomainIH (targetContext.cons domainCode) extendedWf
          (convContextCondition_cons domainCode contextConv)
      exact TypedTypeValidityLeveled.piType codomainFamily domainValid' codomainValid'
        (HasTypeDescPi.piFormationViaGenArm targetContext domainCode _codomainCode
          domainLevel codomainLevel armFlag
          domainValid'.toHasTypeDescPi codomainValid'.toHasTypeDescPi)

/-- **The validity-transport payoff, wf-conditional**: a leveled-valid type code's EXACT universe-code
typing transports across pointwise-`Conv` context conversion given target well-formedness — the
GrownCtxConv-5 residual's shape with the LR's open `neutralRecon` hypothesis replaced by the benign
`WfContextDescPi` presupposition. -/
theorem TypedTypeValidityLeveled.transportValidityUnderWf {profile : PolyProfile}
    {scope : Nat} {sourceContext targetContext : TypingContext profile scope}
    {typeCode : RawTerm scope} {level : LevelExpr} {flag : UniverseFlag} {box : KripkeCandBox scope}
    (relation : TypedTypeValidityLeveled profile sourceContext typeCode level flag box)
    (targetWf : WfContextDescPi targetContext)
    (contextConv : ∀ index : Fin scope,
      Conv (sourceContext.lookup index) (targetContext.lookup index)) :
    HasTypeDescPi profile targetContext typeCode (universeCodeCell level flag) :=
  (relation.transportUnderWf targetContext targetWf contextConv).toHasTypeDescPi

end FX1Poly.Typed

import FX1Poly.Typed.TypedTypeValidityLeveled
import FX1Poly.Typed.HasTypeDescPiFormerCongruence
import FX1Poly.Typed.HasTypeDescContextConversion

/-! # FX1Poly/Typed/TypedTypeValidityLeveledTransport
    — the LEVELED transport across context conversion (GrownCtxConv-5 route B, the flag-matched payoff)

The universe-tracking refined LR `TypedTypeValidityLeveled` (`#1124`) carries the universe `(level, flag)` in
its index, so the `piType` arm forces its domain and codomain to share the flag.  This file harvests that:
the LR transports across a pointwise-`Conv` context conversion, by induction on the relation, with the
`piType` arm rebuilding the `Π`-validity via `piFormationViaGenArm` — and the rebuild's flag-matching, the
firing-34 obstacle, is now DISCHARGED by the leveled index (the transported domain and codomain still share
the flag, because the index is preserved).

## The three arms

  * `universeType` — FREE.  A universe code `Type@levelExpr` is context-independent: re-derive its validity
    `HasTypeDescPi targetContext (Type@levelExpr) (Type@(levelExpr.lsucc))` from scratch via `universeFormation`
    under the target.  No input from the source.
  * `piType` — RECURSE + REBUILD.  Transport the domain (under the target) and codomain (under the cons-lifted
    target context via `convContextCondition_cons`); the IHs give them back at `(domainLevel, flag)` and
    `(codomainLevel, flag)` — SAME `flag` (the leveled index).  `toHasTypeDescPi` exposes both at their exact
    universe codes, so `piFormationViaGenArm` (which needs the shared flag) rebuilds
    `HasTypeDescPi targetContext (Π D C) (Type@(lmax domainLevel codomainLevel))`, and `piType` re-fires.
  * `neutral` — the CONDITIONAL Abel-reflection reconstruction `neutralRecon` (a neutral type code valid in the
    source is valid at a `Conv`-converted target).  This is the lone open hypothesis — the genuine hard core
    (the var-headed leaf `#1119` extended to general neutral spines / the term-level mutual partner).

## The payoff for the residual

`transportValidity`: a leveled-valid type code's EXACT universe-code typing transports across context
conversion (conditional on `neutralRecon`).  Specialized to a `Π`-code, this is exactly the GrownCtxConv-5
residual `ConvContextPreservesPiValidity` shape — discharged for LEVELED-VALID `Π`-codes, conditional ONLY on
the neutral reconstruction.  The remaining route-B brick is COMPLETENESS (`HasTypeDescPi context T
(universeCodeCell level flag) → TypedTypeValidityLeveled …`), after which `soundness ∘ transport ∘
completeness` discharges the residual modulo `neutralRecon`.

## Zero-axiom verification

`induction` on the leveled relation: `neutral` → `neutralRecon`; `universeType` → `universeFormation` rebuild;
`piType` → two IHs (the codomain under `convContextCondition_cons`) + `piFormationViaGenArm` on the
`toHasTypeDescPi` projections (flag-matched).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The leveled transport across context conversion**, conditional on the neutral-arm reconstruction
`neutralRecon`.  By induction on the leveled relation: the `universeType` arm is FREE (universe codes are
context-independent, rebuilt via `universeFormation` under the target); the `piType` arm RECURSES on the domain
and codomain (the codomain under the cons-lifted condition `convContextCondition_cons`) and REBUILDS the
`Π`-validity via `piFormationViaGenArm` — the rebuild's flag-matching is discharged by the leveled index (domain
and codomain share the flag); the `neutral` arm is the lone conditional reconstruction hypothesis.  The
candidate box is preserved throughout. -/
theorem TypedTypeValidityLeveled.transport {profile : PolyProfile}
    (neutralRecon : ∀ {neutralScope : Nat}
        {neutralSource neutralTarget : TypingContext profile neutralScope}
        {neutralCode : RawTerm neutralScope} {neutralLevel : LevelExpr} {neutralFlag : UniverseFlag},
        IsNeutral neutralCode →
        HasTypeDescPi profile neutralSource neutralCode (universeCodeCell neutralLevel neutralFlag) →
        (∀ index : Fin neutralScope,
          Conv (neutralSource.lookup index) (neutralTarget.lookup index)) →
        HasTypeDescPi profile neutralTarget neutralCode (universeCodeCell neutralLevel neutralFlag))
    {scope : Nat} {sourceContext : TypingContext profile scope} {typeCode : RawTerm scope}
    {level : LevelExpr} {flag : UniverseFlag} {box : KripkeCandBox scope}
    (relation : TypedTypeValidityLeveled profile sourceContext typeCode level flag box) :
    ∀ (targetContext : TypingContext profile scope),
      (∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) →
      TypedTypeValidityLeveled profile targetContext typeCode level flag box := by
  induction relation with
  | neutral neutralCode validity =>
      intro targetContext contextConv
      exact TypedTypeValidityLeveled.neutral neutralCode
        (neutralRecon neutralCode validity contextConv)
  | @universeType _armScope _armContext levelExpr armFlag _validity =>
      intro targetContext _contextConv
      exact TypedTypeValidityLeveled.universeType
        (HasTypeDescPi.ofFormation
          (HasTypeDesc.universeFormation targetContext levelExpr armFlag))
  | @piType _armScope _armContext domainCode _codomainCode domainLevel codomainLevel armFlag
      _domainBox _codomainBox codomainFamily _domainValid _codomainValid _validity
      domainIH codomainIH =>
      intro targetContext contextConv
      have domainValid' := domainIH targetContext contextConv
      have codomainValid' :=
        codomainIH (targetContext.cons domainCode)
          (convContextCondition_cons domainCode contextConv)
      exact TypedTypeValidityLeveled.piType codomainFamily domainValid' codomainValid'
        (HasTypeDescPi.piFormationViaGenArm targetContext domainCode _codomainCode
          domainLevel codomainLevel armFlag
          domainValid'.toHasTypeDescPi codomainValid'.toHasTypeDescPi)

/-- **★ The validity-transport payoff (the residual's shape).**  A leveled-valid type code's EXACT
universe-code typing transports across a pointwise-`Conv` context conversion — conditional on the neutral
reconstruction `neutralRecon`.  Specialized to a `Π`-code (`typeCode = piTyCodeCell D C`,
`level = lmax …`), this is precisely the GrownCtxConv-5 residual `ConvContextPreservesPiValidity` shape,
discharged for LEVELED-VALID `Π`-codes, conditional ONLY on `neutralRecon`.  Completeness
(`IsTypeDescPi → TypedTypeValidityLeveled`) then yields the residual modulo `neutralRecon`. -/
theorem TypedTypeValidityLeveled.transportValidity {profile : PolyProfile}
    (neutralRecon : ∀ {neutralScope : Nat}
        {neutralSource neutralTarget : TypingContext profile neutralScope}
        {neutralCode : RawTerm neutralScope} {neutralLevel : LevelExpr} {neutralFlag : UniverseFlag},
        IsNeutral neutralCode →
        HasTypeDescPi profile neutralSource neutralCode (universeCodeCell neutralLevel neutralFlag) →
        (∀ index : Fin neutralScope,
          Conv (neutralSource.lookup index) (neutralTarget.lookup index)) →
        HasTypeDescPi profile neutralTarget neutralCode (universeCodeCell neutralLevel neutralFlag))
    {scope : Nat} {sourceContext targetContext : TypingContext profile scope}
    {typeCode : RawTerm scope} {level : LevelExpr} {flag : UniverseFlag} {box : KripkeCandBox scope}
    (relation : TypedTypeValidityLeveled profile sourceContext typeCode level flag box)
    (contextConv : ∀ index : Fin scope, Conv (sourceContext.lookup index) (targetContext.lookup index)) :
    HasTypeDescPi profile targetContext typeCode (universeCodeCell level flag) :=
  (relation.transport neutralRecon targetContext contextConv).toHasTypeDescPi

end FX1Poly.Typed

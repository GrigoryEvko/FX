import FX1Poly.Typed.Engine.Union.HasTypeUnionNativeOnly

/-! # FX1Poly/Typed/Engine/Union/HasTypeUnionNativeOnlyAdmissibility — the native-only equivalence capstone (TYTAB-2 ADMIT)

`HasTypeUnion` (the kernel judgment) and `HasTypeUnionNativeOnly` (the `ofGrown`-free judgment) classify
exactly the same triples.  With the `ofGrown` arm retired, the forward reflection `HasTypeUnion.toNativeOnly`
is the trivial six-arm structural map and the backward `HasTypeUnionNativeOnly.toUnion` re-embeds; every
consequence proved over one transports to the other along `iff_nativeOnly`.

The host-engine → native-only reflections that historically justified retiring `ofGrown` (over the grown
`HasTypeDescPi` and formation `HasTypeDesc` derivations) were relocated (B0-b) to
`FX1Poly.Typed.Metatheory.HostAdmissibility.HostEngineNativeOnlyReflection`, so this file no longer imports the
grown engine.

## Zero-axiom

`induction` over the union derivation + native-arm constructor applications.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/Typed/Engine/Union/HasTypeUnionNativeOnlyAdmissibility.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Axis.Syntax FX1Poly.Modal

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
  | var context index isAccessible => exact HasTypeUnionNativeOnly.var context index isAccessible
  | universeFormation context levelExpr flag =>
      exact HasTypeUnionNativeOnly.universeFormation context levelExpr flag
  | conv levelExpr flag _typed converts _reclassifierTyped typedIH reclassifierIH =>
      exact HasTypeUnionNativeOnly.conv levelExpr flag typedIH converts reclassifierIH
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      _premisesHold usabilityHolds ihPremises =>
      exact HasTypeUnionNativeOnly.formationRule context generator payload children rule levels carrier
        level flag isFormationRule ihPremises usabilityHolds
  | intro context generator rule args params level0 level1 flag isIntro sideHolds _premisesHold
      usabilityHolds ihPremises =>
      exact HasTypeUnionNativeOnly.intro context generator rule args params level0 level1 flag isIntro
        sideHolds ihPremises usabilityHolds
  | elim context generator rule args params level0 level1 flag isElim _premisesHold
      usabilityHolds ihPremises =>
      exact HasTypeUnionNativeOnly.elim context generator rule args params level0 level1 flag isElim
        ihPremises usabilityHolds

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

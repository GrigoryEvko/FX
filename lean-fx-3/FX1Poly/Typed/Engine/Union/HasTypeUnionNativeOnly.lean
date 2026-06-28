import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.Union.HasTypeUnionFormationObligations

/-! # FX1Poly/Typed/Engine/Union/HasTypeUnionNativeOnly — the OFGROWN-FREE union judgment (TYTAB-2 ADMIT)

The native-only typing relation: `HasTypeUnionOver` with the `ofGrown` host-embedding arm REMOVED.  Its six
arms are exactly the native ones — `var`, `universeFormation` (the two structural leaves, TYTAB-2 VAR/UNIV),
`formationRule` / `intro` / `elim` (the three table-driven keystone arms), and `conv` — each premise
referencing `HasTypeUnionNativeOnly` itself (so a native-only derivation has NO `ofGrown` anywhere in its
tree, not just at the root).  Pinned to the shipped tables (`formationRuleOf` / `introRuleOf` / `elimRuleOf`),
matching the `HasTypeUnion` constructor aliases.

This is the TARGET relation of host-engine admissibility (#1695 ADMIT): the goal is to prove
`WfContextUnion context → HasTypeDescPi profile context subject classifier →
HasTypeUnionNativeOnly profile context subject classifier`, i.e. every host derivation is reproducible from
the native arms alone, making `ofGrown` a provably-eliminable compatibility shim.

This file ships the relation + the EMBEDDING `toUnion` (every native-only derivation IS a union derivation —
the easy direction, witnessing that `HasTypeUnionNativeOnly` is a genuine sub-relation of the kernel).  The
admissibility reflection (the hard converse) is the substantial remaining work: a mutual induction over the
host `HasTypeDescPi` / `HasTypeDesc` engines mapping each host arm to its native counterpart (var → var,
universe → universe, conv → conv, piIntro → intro@gen_lam, piElim → elim@gen_app, genFormationPi →
formationRule), with the data-former / Π-formation obligation premises discharged native-only.

## Zero-axiom

The inductive is strictly positive (the relation appears positively under the `∀ obligation ∈ …`, exactly as
`HasTypeUnionOver`).  The embedding is a one-pass structural `induction` mapping each arm to its
`HasTypeUnion` constructor alias.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditHasTypeUnionNativeOnly.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ The OFGROWN-FREE native union judgment.**  `HasTypeUnionOver` minus the `ofGrown` arm: a subject is
native-only-typed iff it is built purely from the six native arms (`var` / `universeFormation` /
`formationRule` / `intro` / `elim` / `conv`), recursively — no host embedding anywhere in the derivation. -/
inductive HasTypeUnionNativeOnly (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  /-- The native variable leaf, carrying the Fitch fibrant-accessibility premise (A1-RESTRICT) — mirrors
  `HasTypeUnionOver.var`. -/
  | var {scope : Nat} (context : TypingContext profile scope) (index : Fin scope)
      (isAccessible : context.isFibrantlyAccessibleAt index = true) :
      HasTypeUnionNativeOnly profile context (variableCell index) (context.lookup index)
  /-- The native universe-formation leaf (`Type@L : Type@(L+1)`). -/
  | universeFormation {scope : Nat} (context : TypingContext profile scope)
      (levelExpr : LevelExpr) (flag : UniverseFlag) :
      HasTypeUnionNativeOnly profile context (universeCodeCell levelExpr flag)
        (universeCodeCell levelExpr.lsucc flag)
  /-- The native type-formation arm (base / flat / cumulative / term-indexed), premises native-only. -/
  | formationRule {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (payload : generator.payload scope)
      (children : RawTermChildren generator.binderShifts scope)
      (rule : FormationRule)
      (levels : List LevelExpr) (carrier : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag)
      (isFormationRule : formationRuleOf generator = some rule)
      (premisesHold : ∀ obligation ∈ rule.obligations profile context children levels carrier level flag,
        HasTypeUnionNativeOnly profile obligation.context obligation.subject obligation.classifier) :
      HasTypeUnionNativeOnly profile context (.mkGen generator payload children)
        (rule.outputType scope levels level flag)
  /-- The native introducer arm, premises native-only. -/
  | intro {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : IntroRule)
      (args : RawTermChildren rule.argShifts scope)
      (params : RawTermChildren rule.paramShifts scope)
      (level0 level1 : LevelExpr) (flag : UniverseFlag)
      (isIntro : introRuleOf generator = some rule)
      (sideHolds : rule.sideCondition scope args)
      (premisesHold : ∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
        HasTypeUnionNativeOnly profile obligation.context obligation.subject obligation.classifier) :
      HasTypeUnionNativeOnly profile context
        (rule.memberCell scope args) (rule.outputType scope args params)
  /-- The native eliminator arm, premises native-only. -/
  | elim {scope : Nat} (context : TypingContext profile scope)
      (generator : Generator) (rule : ElimRule)
      (args : RawTermChildren rule.argShifts scope)
      (params : RawTermChildren rule.paramShifts scope)
      (level0 level1 : LevelExpr) (flag : UniverseFlag)
      (isElim : elimRuleOf generator = some rule)
      (premisesHold : ∀ obligation ∈ rule.obligations scope context args params level0 level1 flag,
        HasTypeUnionNativeOnly profile obligation.context obligation.subject obligation.classifier) :
      HasTypeUnionNativeOnly profile context
        (rule.memberCell scope args) (rule.outputType scope args params)
  /-- The native conversion arm, premises native-only. -/
  | conv {scope : Nat} {context : TypingContext profile scope}
      {subject classifier reclassifier : RawTerm scope}
      (levelExpr : LevelExpr) (flag : UniverseFlag)
      (typed : HasTypeUnionNativeOnly profile context subject classifier)
      (converts : Conv classifier reclassifier)
      (reclassifierTyped :
        HasTypeUnionNativeOnly profile context reclassifier
          (universeCodeCell levelExpr flag)) :
      HasTypeUnionNativeOnly profile context subject reclassifier

/-- **★ The embedding `HasTypeUnionNativeOnly → HasTypeUnion`.**  Every native-only derivation IS a kernel
union derivation — the native-only relation is a genuine sub-relation of `HasTypeUnion` (forget that the
tree avoids `ofGrown`).  One-pass `induction`: each arm maps to its `HasTypeUnion` constructor alias, the
recursive-premise IH (`ihPremises` / `typedIH`) supplying the union obligations / sub-derivations. -/
theorem HasTypeUnionNativeOnly.toUnion {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeUnionNativeOnly profile context subject classifier) :
    HasTypeUnion profile context subject classifier := by
  induction derivation with
  | var context index isAccessible => exact HasTypeUnion.var context index isAccessible
  | universeFormation context levelExpr flag =>
      exact HasTypeUnion.universeFormation context levelExpr flag
  | formationRule context generator payload children rule levels carrier level flag isFormationRule
      _premisesHold ihPremises =>
      exact HasTypeUnion.formationRuleOfObligations context generator payload children rule levels carrier
        level flag isFormationRule ihPremises
  | intro context generator rule args params level0 level1 flag isIntro sideHolds _premisesHold
      ihPremises =>
      exact HasTypeUnion.intro context generator rule args params level0 level1 flag isIntro sideHolds
        ihPremises
  | elim context generator rule args params level0 level1 flag isElim _premisesHold
      ihPremises =>
      exact HasTypeUnion.elim context generator rule args params level0 level1 flag isElim ihPremises
  | conv levelExpr flag _typed converts _reclassifierTyped typedIH reclassifierIH =>
      exact HasTypeUnion.conv levelExpr flag typedIH converts reclassifierIH

end FX1Poly.Typed

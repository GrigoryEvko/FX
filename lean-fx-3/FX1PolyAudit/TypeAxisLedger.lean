import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.HasTypeDesc.HasTypeDesc

/-! # FX1PolyAudit/TypeAxisLedger — audit record for the type-axis rungs (type-1 .. type-8)

This file replaces the eight deleted `FX1Poly/Typed/Ledger/TypeAxis/Type{One..Eight}.lean` "ledger" modules
and their eight `AuditAxisType{One..Eight}.lean` gates.

Honest accounting.  Those ledgers were NOT new mathematics.  Each "backed flip" was a `Bool := true` marker
paired with a theorem `marker = true ∧ <conjunction of already-proven facts>`; the `= true` conjunct is `rfl`,
and every other conjunct re-cited a theorem already proven — and already zero-axiom-gated — in its home
module.  The genuine substrate lives, unchanged, where it always did:

  * type-1 (sum / initial algebra): `HasTypeDescPi.sigmaFormationViaGenArm`, `IsCarrierHomomorphism.unique`,
    `IsReducibleMemberAt.unitFormerInUniverse`.
  * type-2 (pi / classifier / Tarski): `HasTypeDescPi.piFormationViaGenArm`, `betaSubjectReduction`,
    `closedNormalFunctionIsLambda`, `etaExpansionPreservesTypingGrown`, `universeCodeClassifierIsSuccessor`,
    `universeCodeClassifierUnique`, `universeHierarchyHasNoTop`, `tarskiDecode` / `tarskiEncode` /
    `universeMembership_iff`.
  * type-3 (M-types / terminal coalgebra): `StreamCoalgebra.ana_isHom` / `ana_unique`,
    `FinalStream.bisim_observe`, `NuStream.corec_unique`, `nu_canBeUnbounded`.
  * type-4 (W / IR / II): `RawTermChildren.eq_childNil`, `IsTypeDesc.decidableOfWellFormedGeneric` /
    `decideTypeGeneric`, `wStyleRecursiveBinderDemoRule_interpretsTarget`, plus the two formation derivations
    BELOW — the only constructed terms the whole exercise produced.
  * type-5 (QIIT): `quotRecMkIotaRow_interpretsTarget` / `quotElimMkIotaRow_interpretsTarget`,
    `iotaRuleTable_isWf`, `Conv.equivalence`, `Generator.descriptor_toGenerator_roundTrip` /
    `descriptor_injective`, `rootFiringDeterministic`, quot-row `IsScopeUniform` / `HasSortPreservingTarget`.
  * type-6 (HIT / cubical): `pathBetaIotaRow_interpretsTarget`, `hasReductionRule_pathApp`, the
    interval/bridge `hasSomeTypingRule_*` rows, `termIndexedFormerDescOf_bridgeCode`,
    `gradedIntroRuleOf_pathLam`, `truncRecIntroIotaRow_interpretsTarget`, `generalElimRuleOf_pathApp`,
    `generalElimEngine_typesPathApp`, `gradedIntroEndpointIotaComputesTyped`.
  * type-7 (definitional univalence): `idJReflIotaRow_interpretsTarget` / `idStrictRecReflIotaRow_*`,
    `reflClosedReducesToValue`, `idJCanonicalWitnessReducesToBase`, `flatTypingRuleDescOf_equivCode`,
    `equivCode_isReducibleMemberOfUniverse` / `equivCode_isStronglyNormalizing_of_source_target`,
    `candidateUnivalenceTable_isWf` / `candidateUnivalenceTable_isConfluent`.
  * type-8 (structure identity principle): `samenessArity_reflexivity_eq_diagonal`,
    `identity_is_relational_at_Eq`, `identity_finest_reflexive`, `relational_not_reflexive`,
    `equalityCrispJ.transport_refl` / `equalityCrispJ.beta`, `identity_respects` / `id_respects` /
    `comp_respects`, `fxUsageSemiring_isLawful`, `effectIsLawfulBoundedJoinSemilattice`,
    `Migration.compose_assoc`, `migrateDropField_addField`, `migrateAddField_injective_inDefault`.

Each of those is gated zero-axiom in its own home-module audit; deleting the ledgers loses no coverage.

The genuine open frontier the ledgers recorded as deferred (NOT shipped — kept here for honesty, not behind
a flag): object-level sum-elimination / per-object inductive initiality (type-1); fibred-pi right adjoint /
display-map classifier / Tarski round-trip inverse (type-2); coinductive type former / container M-type /
coinductive reducibility (type-3); indexed W / induction-recursion / induction-induction OBJECT-level formers
(type-4); quotient type former / quotient equality / QIIT former (type-5); cubical Kan operations / HIT path
constructors / HIT canonicity (type-6); LIVE definitional univalence — the rule sits only in the
`candidateUnivalenceTable`, not the operational `iotaRuleTable` — plus equivalence eliminators and a univalent
universe in any model (type-7); structure-transport-along-an-equivalence / proof-relevant sameness /
dimension univalence (type-8).

Below: the only constructed terms from the whole exercise — two formation derivations through the live
`HasTypeDesc.genFormation` arm, kept as audit-side demonstrations.  The first shows the nullary unit former
typing through `genFormation` + `DescTelescope.nil`; the second shows a one-child former (`list(Unit)`) typing
through `genFormation` + `DescTelescope.cons`, exercising the inductive-inductive cross-reference (the
telescope constructor whose `headTyped` premise is itself a `HasTypeDesc` derivation) that the nullary case
never touches. -/

namespace FX1PolyAudit

open FX1Poly.Core
open FX1Poly.Typed
open FX1Poly.Universe

/-- Demonstration: the nullary unit type former types through the generic `HasTypeDesc.genFormation` arm,
consuming the flag-pinned `nullaryFormerOutput` row (`typingRuleDescOf_unitCode`) with an empty
`DescTelescope.nil` premise — yielding `Unit : Type@0(standard)`. -/
theorem typeAxisUnitFormerTypesViaGenArm {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (flag : UniverseFlag) :
    HasTypeDesc profile context (.mkGen .gen_unitCode () .childNil)
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  HasTypeDesc.genFormation context .gen_unitCode () .childNil [] flag
    { outputType := nullaryFormerOutput } typingRuleDescOf_unitCode
    (DescTelescope.nil (profile := profile) (baseScope := scope) (currentDepth := 0) context flag)

/-- Demonstration: the one-child former `list(Unit)` types through `HasTypeDesc.genFormation` consuming a
`DescTelescope.cons` whose `headTyped` premise is the unit former derivation itself — the in-engine
inductive-inductive cross-reference (the typing judgment is defined mutually with its premise telescope, and
the telescope constructor references `HasTypeDesc` in its premises). -/
theorem typeAxisListOverUnitTypesViaGenArm {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    HasTypeDesc profile context
      (.mkGen .gen_listCode () (.childCons (.mkGen .gen_unitCode () .childNil) .childNil))
      (universeCodeCell LevelExpr.lzero UniverseFlag.standard) :=
  HasTypeDesc.genFormation context .gen_listCode ()
    (.childCons (.mkGen .gen_unitCode () .childNil) .childNil)
    [LevelExpr.lzero] UniverseFlag.standard
    { outputType := universeFormerOutput } typingRuleDescOf_listCode
    (DescTelescope.cons (profile := profile) (baseScope := scope) (currentDepth := 0) context
      (.mkGen .gen_unitCode () .childNil)
      LevelExpr.lzero [] UniverseFlag.standard .childNil
      (HasTypeDesc.genFormation context .gen_unitCode () .childNil [] UniverseFlag.standard
        { outputType := nullaryFormerOutput } typingRuleDescOf_unitCode
        (DescTelescope.nil (profile := profile) (baseScope := scope) (currentDepth := 0) context
          UniverseFlag.standard))
      (DescTelescope.nil (profile := profile) (baseScope := scope) (currentDepth := 1)
        (context.cons (.mkGen .gen_unitCode () .childNil)) UniverseFlag.standard))

#assert_no_axioms FX1PolyAudit.typeAxisUnitFormerTypesViaGenArm
#assert_no_axioms FX1PolyAudit.typeAxisListOverUnitTypesViaGenArm

end FX1PolyAudit

import FX1Poly.Typed.HasTypeDescTermIndexedFormerWeakening
import FX1Poly.Typed.ConvUniverseClassificationUnique

/-! # FX1Poly/Typed/HasTypeDescTermIndexedFormerUniqueness — NATIVE-14: inversion + typing-uniqueness for the
    term-indexed former engine

`HasTypeDescTermIndexedFormer` (NATIVE-12) types `Id A a b` / `Bridge A a b` through ONE generic arm; NATIVE-13
gave its renaming/substitution. This file lands the inversion (a typed cell exposes its table membership +
the carrier/endpoints premise + a `Conv` to the carrier's universe) and the typing-uniqueness headline (two
derivations of the same subject have `Conv` classifiers — the determinism a type-checker rests on). The
term-indexed twin of the union's `flatFormation`-arm inversion and uniqueness metatheory.

## The uniqueness route is SHORTER than the flat one

The flat engine's output is `universeFormerOutput scope levels flag = universeCodeCell (lmaxAll levels) flag`,
so its uniqueness must agree the WHOLE level list via `FlatDescTelescope.uniquenessAgree`. The term-indexed
output is `termIndexedCarrierOutput scope level flag = universeCodeCell level flag` — a SINGLE level, the
CARRIER's. Two derivations of the same subject share the same children, hence the same carrier head; the two
carrier typings `HasTypeDescPi carrier (universeCodeCell levelᵢ flagᵢ)` feed the shipped grown
`HasTypeDescPi.convUniverseClassificationUnique` (a subject typed at two universe codes pins level + flag),
which settles `level₁ = level₂ ∧ flag₁ = flag₂` directly — no telescope-wide agreement substrate.

## The propext-free route

`cases` on the first derivation is clean (single `genFormation` constructor, free subject index — no impossible
arms, no equation lemmas → no propext). That exposes the concrete `.mkGen` cell, so the second derivation is
inverted by the propext-free `inversionFormerWithConv` (head-generator alignment via `congrArg headGenerator`
before any `injection`). Casing the two `TermIndexedFormerTelescope.mk` premises (each a single constructor)
aligns the shared carrier head (the children index unifies `carrier₂ = carrier₁`), and
`convUniverseClassificationUnique` closes it.

## Zero-axiom

`cases` on free-index single-constructor scrutinees; the second derivation via the propext-free inversion;
`convUniverseClassificationUnique` is itself zero-axiom; `Conv.sym` is the join-relation symmetry. No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`. Per-declaration audit-gated in
`FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **★ Term-indexed former inversion (with Conv).**  A `HasTypeDescTermIndexedFormer` derivation of a subject
that IS the table cell `mkGen generator payload children` exposes the carrier/level/flag and the children-indexed
telescope premise, plus a `Conv` from the reached classifier to the carrier's universe code.  The propext-free
second-derivation inverter (head-generator alignment before `injection`) — the term-indexed twin of
the union's `flatFormation`-arm former inversion. -/
theorem HasTypeDescTermIndexedFormer.inversionFormerWithConv {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject reachedClassifier : RawTerm scope}
    (derivation : HasTypeDescTermIndexedFormer profile context subject reachedClassifier)
    {generator : Generator} {rule : TermIndexedFormerDesc}
    (isTermIndexed : termIndexedFormerDescOf generator = some rule)
    {payload : generator.payload scope} {children : RawTermChildren generator.binderShifts scope}
    (subjectEq : subject = RawTerm.mkGen generator payload children) :
    ∃ (carrier : RawTerm scope) (level : LevelExpr) (flag : UniverseFlag),
      TermIndexedFormerTelescope profile context children carrier level flag ∧
      Conv reachedClassifier (universeCodeCell level flag) := by
  cases derivation with
  | genFormation armGenerator armPayload armChildren armCarrier armLevel armFlag
      armRule armIsTermIndexed armPremises =>
      have generatorAgree : armGenerator = generator :=
        congrArg RawTerm.headGenerator subjectEq
      subst generatorAgree
      obtain rfl : armRule = { outputType := termIndexedCarrierOutput } :=
        termIndexedFormerRuleIsCarrierOutput armIsTermIndexed
      injection subjectEq
      subst_vars
      exact ⟨armCarrier, armLevel, armFlag, armPremises, Conv.refl _⟩

/-- **Telescope level/flag agreement.**  Two term-indexed former telescopes over the SAME children agree on
their level and flag.  Both `mk` constructors expose the shared carrier head (the children index forces
`carrierA = carrierB`), so the two carrier-universe typings feed the grown `convUniverseClassificationUnique`.

Stated over a FREE-variable `shifts` index (not `generator.binderShifts`): the telescope `cases` must unify the
children index against the `mk` constructor's `childCons (shift := 0) carrier rest`, and that unification only
goes through when the shift list is a free variable Lean can substitute — an opaque `generator.binderShifts`
projection would leave dependent elimination stuck.  `uniquenessNative` applies this lemma at the concrete
`generator1.binderShifts` AFTER it has the two telescopes in hand, so the stuck-index `cases` never happens at
the call site. -/
theorem TermIndexedFormerTelescope.levelFlagAgree {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {shifts : List Nat}
    {children : RawTermChildren shifts scope}
    {carrierA : RawTerm scope} {levelA : LevelExpr} {flagA : UniverseFlag}
    {carrierB : RawTerm scope} {levelB : LevelExpr} {flagB : UniverseFlag}
    (telescopeA : TermIndexedFormerTelescope profile context children carrierA levelA flagA)
    (telescopeB : TermIndexedFormerTelescope profile context children carrierB levelB flagB)
    (wellFormed : WfContextDescPi context) :
    levelA = levelB ∧ flagA = flagB := by
  cases telescopeA with
  | mk headCarrierA restEndpointsA headLevelA headFlagA carrierTypedA endpointsTypedA =>
    cases telescopeB with
    | mk headCarrierB restEndpointsB headLevelB headFlagB carrierTypedB endpointsTypedB =>
      exact HasTypeDescPi.convUniverseClassificationUnique wellFormed
        (Conv.refl _) carrierTypedA carrierTypedB

/-- **★ Term-indexed former typing uniqueness.**  Two `HasTypeDescTermIndexedFormer` derivations of the SAME
subject under a grown-well-formed context have definitionally-`Conv` classifiers — the determinism property a
type-checker rests on.  The term-indexed analogue of the union's `flatFormation`-arm uniqueness: the carrier head is
shared, so the grown `convUniverseClassificationUnique` (via `TermIndexedFormerTelescope.levelFlagAgree`) settles
the two carrier-universe classifiers' level + flag, and the outputs (`universeCodeCell levelᵢ flagᵢ`) coincide. -/
theorem HasTypeDescTermIndexedFormer.uniquenessNative {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier1 classifier2 : RawTerm scope}
    (derivation1 : HasTypeDescTermIndexedFormer profile context subject classifier1)
    (derivation2 : HasTypeDescTermIndexedFormer profile context subject classifier2)
    (wellFormed : WfContextDescPi context) :
    Conv classifier1 classifier2 := by
  cases derivation1 with
  | genFormation generator1 payload1 children1 carrier1 level1 flag1 rule1 isTermIndexed1 premises1 =>
    obtain rfl : rule1 = { outputType := termIndexedCarrierOutput } :=
      termIndexedFormerRuleIsCarrierOutput isTermIndexed1
    show Conv (universeCodeCell level1 flag1) classifier2
    obtain ⟨carrier2, level2, flag2, premises2, conv2⟩ :=
      derivation2.inversionFormerWithConv isTermIndexed1 rfl
    obtain ⟨levelAgree, flagAgree⟩ :=
      TermIndexedFormerTelescope.levelFlagAgree premises1 premises2 wellFormed
    rw [levelAgree, flagAgree]
    exact Conv.sym conv2

end FX1Poly.Typed

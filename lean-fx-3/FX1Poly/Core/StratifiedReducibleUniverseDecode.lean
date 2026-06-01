import FX1Poly.Core.StratifiedReducibleMember

/-! # FX1Poly/Core/StratifiedReducibleUniverseDecode
    — the Tarski decode: a reducible member of the universe (at `level+1`) is a reducible type (at `level`)

The keystone of the level-threading the fundamental theorem over `HasTypeDescPi` rests on.  In the
stratified (Tarski-universe) construction, a universe code at `level+1` denotes the candidate
`universeReducibilityPredicate (ReducibleTypeAt level)` = `fun typeCode => SN typeCode ∧ ∃ candidate,
ReducibleTypeAt level typeCode candidate` (the `universeCode` arm of `ReducibleTypeStep`).  So a reducible
MEMBER of that universe — `IsReducibleMemberAt (level+1) (universeCode …) typeCode` — unfolds to
`SN typeCode ∧ ∃ candidate, ReducibleTypeAt level typeCode candidate`, whose second conjunct is exactly
`IsReducibleTypeAt level typeCode`.  This DECODE is the bridge by which the fundamental theorem turns a
typing premise `A : Type@e` (interpreted at `level+1`) into "A is a reducible type at `level`" — the form
the `conv` arm (`castAlongConv`'s target reducibility), the `piIntro` arm (`abstraction`'s domain/codomain
reducibility), and the formation arms all consume.  The level STRICTLY DECREASES through the universe
(`level+1 ↦ level`): the Tarski decode is where the stratification's fuel is spent.

## The two bricks

  * `ReducibleTypeStep.universeCodeInversion` — the sibling of `ReducibleTypeStep.piTypeInversion`: a
    universe-code-rooted reducible type came through the `universeCode` arm (the `whnfExpand` head-step is
    impossible — a universe code is a normal leaf, refuted by `rootIota` ∘ `iotaStep`; the `neutral` arm is
    root-refuted by `notUniverse`; the `piType` arm auto-drops on the `gen_universeCode ≠ gen_piTyCode`
    subject mismatch).  Recovers that the candidate IS `universeReducibilityPredicate lowerReducible`
    pointwise.
  * `IsReducibleMemberAt.tarskiDecode` — the decode itself: destructure the universe membership, invert the
    universe candidate via `universeCodeInversion` (at `level+1`, where `ReducibleTypeAt (level+1)` is
    definitionally `ReducibleTypeStep (ReducibleTypeAt level)`), and project the second conjunct.

## Zero-axiom verification

`universeCodeInversion` is `cases` on the derivation with the impossible arms root-refuted, byte-for-byte
the `universeCode` case of `ReducibleTypeStep.deterministic` (audited clean) and the structural twin of the
shipped `piTypeInversion`; `tarskiDecode` destructures the existential and the `And`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation FX1Poly.Universe StepStar

/-- **Universe-code inversion (parametric).**  A `gen_universeCode`-rooted type reducible at the step-functor
came through the `universeCode` arm: `whnfExpand` cannot fire (a universe code is weak-head normal, refuted
by `rootIota` ∘ `iotaStep`), and the `neutral` arm is refuted by its non-universe guard (`notUniverse`); the
`piType` arm auto-drops on the `gen_universeCode ≠ gen_piTyCode` subject mismatch.  Recovers that the
candidate is the universe predicate `universeReducibilityPredicate lowerReducible` pointwise.  The sibling of
`ReducibleTypeStep.piTypeInversion`. -/
theorem ReducibleTypeStep.universeCodeInversion {scope : Nat}
    {lowerReducible : RawTerm scope → (RawTerm scope → Prop) → Prop}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {candidate : RawTerm scope → Prop}
    (reducible : ReducibleTypeStep lowerReducible
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) candidate) :
    PointwiseIff candidate (universeReducibilityPredicate lowerReducible) := by
  cases reducible with
  | whnfExpand weakHeadStep _reductReducible =>
      cases weakHeadStep with | rootIota iotaStep => cases iotaStep
  | neutral _noWeakHeadStep _notPiType notUniverse => exact absurd rfl notUniverse
  | universeCode _levelExpr _flag => intro _term; exact Iff.rfl

/-- **The Tarski decode.**  A reducible member of the universe code at `level + 1` is a reducible type at
`level` — the universe at `level + 1` decodes to the reducible types at `level` (its second conjunct, after
`universeCodeInversion` exhibits the universe candidate as `SN ∧ ∃ candidate, ReducibleTypeAt level _
candidate`).  At `level + 1` the lower relation `ReducibleTypeAt (level + 1)` is definitionally
`ReducibleTypeStep (ReducibleTypeAt level)`, so the inversion's `lowerReducible` resolves to
`ReducibleTypeAt level`.  This is the type/term bridge the fundamental theorem invokes on every typing
premise of the form `A : Type@e` to obtain A's reducibility AS A TYPE at the level below. -/
theorem IsReducibleMemberAt.tarskiDecode {scope : Nat} {predLevel : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {typeCode : RawTerm scope}
    (member : IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) typeCode) :
    IsReducibleTypeAt predLevel typeCode := by
  obtain ⟨_universeCandidate, universeReducible, membership⟩ := member
  obtain ⟨_stronglyNormalizing, typeReducible⟩ :=
    (ReducibleTypeStep.universeCodeInversion universeReducible typeCode).mp membership
  exact typeReducible

/-- **The Tarski encode** — the dual of `tarskiDecode`.  A strongly-normalizing reducible type at `level` is
a reducible member of the universe code at `level + 1`: the universe at `level + 1` is INHABITED by exactly
the SN reducible types at `level`.  The universe candidate is `universeReducibilityPredicate
(ReducibleTypeAt level)` = `fun typeCode => SN typeCode ∧ ∃ candidate, ReducibleTypeAt level typeCode
candidate`, so the member is the triple ⟨that candidate, the universe code's own reducibility (the
`universeCode` arm), the membership ⟨SN witness, the type's candidate⟩⟩.  No inversion needed — encode just
applies the `universeCode` constructor.  The direction the formation arms consume to exhibit a type-former
(or a universe code) AS a universe member. -/
theorem IsReducibleMemberAt.tarskiEncode {scope : Nat} {predLevel : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {typeCode : RawTerm scope}
    (stronglyNormalizing : IsStronglyNormalizing typeCode)
    (typeReducible : IsReducibleTypeAt predLevel typeCode) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) typeCode :=
  ⟨universeReducibilityPredicate (ReducibleTypeAt predLevel),
   ReducibleTypeStep.universeCode levelExpr flag,
   ⟨stronglyNormalizing, typeReducible⟩⟩

/-- **The Tarski universe-membership characterization** (decode ∧ encode packaged into the defining iff).
A term is a reducible member of the universe code at `level + 1` IFF it is a strongly-normalizing reducible
type at `level`.  This is the definitive statement of the universe's Tarski semantics: the universe at
`level + 1` is PRECISELY the SN reducible types at `level`.  Forward is `universeCodeInversion` (keeping BOTH
conjuncts of the universe candidate — the inversion exhibits the candidate as `SN ∧ ∃ candidate,
ReducibleTypeAt level _ candidate`, definitionally `SN ∧ IsReducibleTypeAt level`); backward is
`tarskiEncode`. -/
theorem IsReducibleMemberAt.universeMembership_iff {scope : Nat} {predLevel : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {typeCode : RawTerm scope} :
    IsReducibleMemberAt (predLevel + 1)
        (.mkGen .gen_universeCode (levelExpr, flag) .childNil) typeCode ↔
      IsStronglyNormalizing typeCode ∧ IsReducibleTypeAt predLevel typeCode := by
  constructor
  · intro member
    obtain ⟨_universeCandidate, universeReducible, membership⟩ := member
    exact (ReducibleTypeStep.universeCodeInversion universeReducible typeCode).mp membership
  · intro stronglyNormalizingAndReducible
    exact IsReducibleMemberAt.tarskiEncode
      stronglyNormalizingAndReducible.1 stronglyNormalizingAndReducible.2

end FX1Poly.Core

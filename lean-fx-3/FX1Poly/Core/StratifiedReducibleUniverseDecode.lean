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
    PointwiseIff candidate (universeReducibilityPredicate lowerReducible) :=
  reducible.candidateIffUniverse rfl

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

/-- **Every kernel universe code is a reducible type, at EVERY reducibility level — independent of its
`LevelExpr` and `UniverseFlag`.**  The formal LINK between the Tarski-universe reducibility relation and the
kernel's `gen_universeCode (LevelExpr × UniverseFlag)` codes: the `universeCode` arm of `ReducibleTypeStep`
produces `universeReducibilityPredicate lower` for ANY `(levelExpr, flag)` payload, so the relation's `Nat`
fuel — the META-level stratification of the logical relation — is DECOUPLED from the kernel's `LevelExpr`
OBJECT-level universe levels.  This decoupling is sound because the no-Type-in-Type level discipline is
enforced by the TYPING rules (`HasTypeDesc` universe formation: `Type@e : Type@(lsucc e)`), NOT re-derived in
the reducibility model — the model is a permissive semantic interpretation whose job is "every well-typed
term is reducible", not "reject the ill-typed". -/
theorem IsReducibleTypeAt.universeCode {scope : Nat} (level : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsReducibleTypeAt level
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil : RawTerm scope) := by
  cases level with
  | zero => exact ⟨_, ReducibleTypeStep.universeCode levelExpr flag⟩
  | succ predLevel => exact ⟨_, ReducibleTypeStep.universeCode levelExpr flag⟩

/-- **The universe-formation arm of the fundamental theorem, semantically.**  `Type@e` is a reducible
member of `Type@(lsucc e)` at `predLevel + 1`: `tarskiEncode` the universe code `Type@e` as a member of the
universe `Type@(lsucc e)` from its strong normalization (a normal leaf — `noStep_universeCode`) and its
reducibility AS A TYPE at `predLevel` (`IsReducibleTypeAt.universeCode`).  This is the semantic discharge of
the embedded `HasTypeDesc` universe-formation rule — the formation arm of the fundamental theorem at a
universe classifier.

The reducibility fuel `predLevel + 1` is DECOUPLED from the syntactic level `e`: `tarskiEncode` accepts any
classifier universe code, the `lsucc`-level discipline being the typing rules' responsibility, not the
model's.  (The model would equally accept `Type@e : Type@e'` for any `e'` — it is the `HasTypeDesc` rule, not
the reducibility relation, that pins the classifier to `lsucc e`.) -/
theorem IsReducibleMemberAt.universeFormation {scope : Nat} (predLevel : Nat)
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (LevelExpr.lsucc levelExpr, flag) .childNil : RawTerm scope)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) :=
  IsReducibleMemberAt.tarskiEncode
    (isStronglyNormalizing_of_noStep (fun _ step => noStep_universeCode (levelExpr, flag) step))
    (IsReducibleTypeAt.universeCode predLevel levelExpr flag)

/-- **A strongly-normalizing data type former inhabits its universe** — the fundamental theorem's
`genFormationPi` arm for the non-Π non-universe formers, semantically.  Any weak-head-normal non-Π
non-universe type code (every DATA former — Σ / Nat / List / Option / Either / Id / product / sum) that is
strongly normalizing is a reducible member of any universe code `Type@levelExpr` at `predLevel + 1`:
`tarskiEncode` the former from its strong normalization (supplied from SN of its children at the call site)
and its reducibility AS A TYPE at `predLevel` (`reducibleOfWeakHeadNormalFormer` — the SN candidate, the
Tarski model classifying every data type by strong normalization).  The classifier universe level is
decoupled from the former's structure, the `lsucc`/level discipline being the typing rules' responsibility.
With the Π formers handled by `piTypeCanonical` and the universe code by `universeFormation`, this discharges
the remaining `genFormationPi` formers — no per-former reducibility candidate required. -/
theorem IsReducibleMemberAt.dataFormerInUniverse {scope : Nat} {predLevel : Nat}
    (levelExpr : LevelExpr) (flag : UniverseFlag) {former : RawTerm scope}
    (stronglyNormalizing : IsStronglyNormalizing former)
    (weakHeadNormal : ∀ reduct : RawTerm scope, ¬ WeakHeadStep former reduct)
    (notPiType : former.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : former.rootGenerator ≠ Generator.gen_universeCode) :
    IsReducibleMemberAt (predLevel + 1)
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) former :=
  IsReducibleMemberAt.tarskiEncode stronglyNormalizing
    (ReducibleTypeAt.reducibleOfWeakHeadNormalFormer weakHeadNormal notPiType notUniverse)

end FX1Poly.Core

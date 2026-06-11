import FX1Poly.Core.GeneratorAdmission
import FX1Poly.Typed.GeneratorSemanticTier

/-! # FX1Poly/Typed/GeneratorAdmissionSplit — syntactic vs semantic admission (M30-Z1)

The explicit split of generator admission into its two honest notions, with a decision
procedure for each:

  * **Syntactic admission** — the generator is a row of the 198-name table: it has an
    arity, binder shifts, child specs, and a `SupportedGenerator` witness, so the
    certified layer can BUILD cells on it.  Under the default `fxProfile` this is TOTAL
    (`syntacticallyAdmissible_total`) — every name in the enum is a legal cell head.

  * **Semantic admission** — the generator additionally MEANS something: some typing
    engine types cells built on it (`hasSomeTypingRule`, HON-1) or a `Step` fires at its
    root (`Generator.hasRedexHead`, HON-2).  This is exactly the `semanticTier = .live`
    verdict of the HON-3 ledger (`isSemanticallyAdmissible_iff_tierLive`).

The split is STRICT (`admissionSplit_isStrict`): `gen_hilbertSpace` is a perfectly legal
cell head (syntactically admissible) yet semantically dead — no engine types it, no rule
reduces it.  Conversely every semantically admissible generator is syntactically
admissible (`semanticallyAdmissible_implies_syntactically`), and its type-level admission
witness is computable (`admissionWitnessOfSemantic`).

Both notions are DECIDABLE: the `Bool` classifiers `isSyntacticallyAdmissible` /
`isSemanticallyAdmissible` compute by table lookup, and the `Prop` forms carry
`Decidable` instances via `Bool` equality — no choice, no excluded middle.

Soundness of the semantic verdict is NOT re-proven here — it is the shipped HON
stack: a semantically inadmissible (reserved) generator is untyped by every engine
(HON-5), operationally inert (HON-6), and both at once (HON-7,
`semanticTierReservedSound`).  This file only NAMES the split the soundness theorems
already defend, completing M30-Z1 now that the Z-arc shape migration (M27/M28) has
stabilized every admitted generator's child spec.

## Zero-axiom

The classifiers are table lookups; the totality/refinement/strictness theorems are
`rfl` / constructor applications; the tier bridge destructures the `||` Bool with
`if_neg` + `Bool.noConfusion` / `SemanticTier.noConfusion` (the SemanticTierSoundness
recipe).  The `Decidable` instances are `Bool.decEq` retypings.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration
audit-gated in `FX1PolyAudit/AuditTypedHonestyClassifiers.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- **Syntactic admission classifier.**  `true` iff the generator has a
`SupportedGenerator` witness — it is a legal cell head at the certified layer.  Under
the default `fxProfile` the admission lookup is total, so this computes `true` for every
generator; a restricted profile would return `false` on its excluded rows. -/
def isSyntacticallyAdmissible (generator : Generator) : Bool :=
  (supportedGenerator? generator).isSome

/-- **Semantic admission classifier.**  `true` iff the generator carries encoded
meaning on at least one axis: some typing engine types it (`hasSomeTypingRule`, HON-1)
or a reduction rule fires at its root (`Generator.hasRedexHead`, HON-2).  This is the
Bool form of the HON-3 `semanticTier = .live` verdict
(`isSemanticallyAdmissible_iff_tierLive`). -/
def isSemanticallyAdmissible (generator : Generator) : Bool :=
  hasSomeTypingRule generator || generator.hasRedexHead

/-- Proposition form of syntactic admission. -/
def SyntacticallyAdmissible (generator : Generator) : Prop :=
  isSyntacticallyAdmissible generator = true

/-- Proposition form of semantic admission. -/
def SemanticallyAdmissible (generator : Generator) : Prop :=
  isSemanticallyAdmissible generator = true

/-- Syntactic admission is decidable (Bool-equality decision, choice-free). -/
instance (generator : Generator) : Decidable (SyntacticallyAdmissible generator) :=
  inferInstanceAs (Decidable (isSyntacticallyAdmissible generator = true))

/-- Semantic admission is decidable (Bool-equality decision, choice-free). -/
instance (generator : Generator) : Decidable (SemanticallyAdmissible generator) :=
  inferInstanceAs (Decidable (isSemanticallyAdmissible generator = true))

/-- Under the default `fxProfile`, EVERY generator is syntactically admissible — the
admission lookup `supportedGenerator?` is total. -/
theorem syntacticallyAdmissible_total (generator : Generator) :
    SyntacticallyAdmissible generator :=
  supportedGenerator?_isSome generator

/-- Syntactic admission delivers the type-level admission witness the certified layer
consumes.  (Under `fxProfile` the hypothesis is free by `syntacticallyAdmissible_total`;
a restricted profile would make it load-bearing.) -/
def admissionWitnessOfSyntactic {generator : Generator}
    (_ : SyntacticallyAdmissible generator) : SupportedGenerator generator :=
  supportedGenerator generator

/-- **The refinement half of the split:** semantic admission implies syntactic
admission — a generator that means something is in particular a legal cell head. -/
theorem semanticallyAdmissible_implies_syntactically {generator : Generator}
    (_ : SemanticallyAdmissible generator) : SyntacticallyAdmissible generator :=
  syntacticallyAdmissible_total generator

/-- A semantically admissible generator's type-level admission witness. -/
def admissionWitnessOfSemantic {generator : Generator}
    (semanticAdmission : SemanticallyAdmissible generator) : SupportedGenerator generator :=
  admissionWitnessOfSyntactic
    (semanticallyAdmissible_implies_syntactically semanticAdmission)

/-- **The tier bridge:** the semantic-admission classifier decides exactly the HON-3
`semanticTier = .live` verdict.  Forward: rewrite the tier's `if` condition to `true`.
Backward: were the condition `false`, the tier would compute `.reserved ≠ .live`. -/
theorem isSemanticallyAdmissible_iff_tierLive (generator : Generator) :
    isSemanticallyAdmissible generator = true ↔ semanticTier generator = .live := by
  constructor
  · intro isAdmissible
    dsimp only [semanticTier]
    rw [show (hasSomeTypingRule generator || generator.hasRedexHead) = true
          from isAdmissible]
    rfl
  · intro tierLive
    cases admissionValue :
        (hasSomeTypingRule generator || generator.hasRedexHead) with
    | true => exact admissionValue
    | false =>
        dsimp only [semanticTier] at tierLive
        rw [admissionValue,
          if_neg (fun absurdTrue => Bool.noConfusion absurdTrue)] at tierLive
        exact SemanticTier.noConfusion tierLive

/-! ## Witnesses — the split is honest and strict -/

/-- `gen_app` is semantically admissible (typed AND a redex head). -/
theorem app_isSemanticallyAdmissible : SemanticallyAdmissible .gen_app := rfl

/-- `gen_natElim` is semantically admissible via the OPERATIONAL axis alone (it
reduces but no engine types it) — the axis-union genuinely matters. -/
theorem natElim_isSemanticallyAdmissible : SemanticallyAdmissible .gen_natElim := rfl

/-- `gen_idJ` is semantically admissible — the Z-arc's final migrated eliminator
(motive shape `[2,0,0]`) is live on both axes. -/
theorem idJ_isSemanticallyAdmissible : SemanticallyAdmissible .gen_idJ := rfl

/-- `gen_hilbertSpace` is NOT semantically admissible — a reserved name. -/
theorem hilbertSpace_isSemanticallyAdmissible_false :
    isSemanticallyAdmissible .gen_hilbertSpace = false := rfl

/-- **★ The split is STRICT:** `gen_hilbertSpace` is syntactically admissible (a legal
cell head with a `SupportedGenerator` witness) yet NOT semantically admissible (no
typing rule, no reduction rule).  Syntactic admission does not collapse into semantic
admission — the two notions are genuinely different, which is the honest content of the
M30 split. -/
theorem admissionSplit_isStrict :
    SyntacticallyAdmissible .gen_hilbertSpace
      ∧ ¬ SemanticallyAdmissible .gen_hilbertSpace :=
  ⟨syntacticallyAdmissible_total .gen_hilbertSpace,
   fun semanticAdmission =>
     Bool.noConfusion
       (hilbertSpace_isSemanticallyAdmissible_false.symm.trans semanticAdmission)⟩

end FX1Poly.Typed

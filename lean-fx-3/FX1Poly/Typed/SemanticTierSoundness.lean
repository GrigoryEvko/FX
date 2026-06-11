import FX1Poly.Typed.GeneratorSemanticTier
import FX1Poly.Typed.StaticTypingSoundness
import FX1Poly.Core.GeneratorRedexHeadSoundness

/-! # FX1Poly/Typed/SemanticTierSoundness — the unified tier verdict is TRUTHFUL (HON-7)

`GeneratorSemanticTier.semanticTier` partitions all 203 generators into `live` (carries static and/or
operational meaning) and `reserved`, by `if hasSomeTypingRule g || g.hasRedexHead then .live else .reserved`.
That file shipped the classifier, its complementarity (neither axis alone suffices), and a non-vacuity
discriminator.  It deferred the SOUNDNESS of the `reserved` verdict — the claim that makes `reserved` a TRUTHFUL
"semantically dead name" rather than a `Bool` that happens to compute.  This file ships that soundness, combining
the two soundness legs shipped beneath it:

  * **Static leg (HON-5, `StaticTypingSoundness`)** — `reservedHeadUntypedByEveryEngine` /
    `grownReservedUntyped`: a head reported `hasSomeTypingRule = false` is typed by NO engine.
  * **Operational leg (HON-6, `GeneratorRedexHeadSoundness`)** — `hasRedexHead_false_imp_no_root_redex`: a
    generator reported `hasRedexHead = false` fires no root redex (`hasRootStepSource = false`) on any cell.

The bridge `semanticTier_reserved_imp_both_false` decomposes the tier verdict into the two Bool falsities —
`semanticTier g = .reserved` forces the `||` condition false, hence each disjunct false — after which the two
legs apply directly.

  * **`semanticTier_reserved_imp_both_false`** — the decomposition (`reserved ⟹ hasSomeTypingRule = false ∧
    hasRedexHead = false`).
  * **`reservedTierOperationallyInert`** — operational half: a reserved generator fires no root redex on any cell.
  * **`reservedTierUntypedByGrownEngine`** — static half (grown representative): a reserved generator heads no
    grown-typed (`HasTypeDescPi`) cell.
  * **`reservedTierUntypedByEveryEngine`** — the COMPLETE static half: a reserved generator heads no cell typed
    by any of the 16 engines `hasSomeTypingRule` consults (the full HON-5 bundle, threaded through the head
    equation).
  * **`semanticTierReservedSound`** — ★ the headline: a reserved generator is semantically dead — its cells are
    grown-untyped AND operationally inert.  (Grown is the headline's static representative; the full-16
    completeness is `reservedTierUntypedByEveryEngine`.)

This is the honest answer to "does the 203-generator tier ledger lie?":  it does not — every name it brands
`reserved` is genuinely typed by no engine and reduces under no rule.

## Zero-axiom

The bridge is `cases` on the `||` Bool: the `true` branch reduces the tier `if` via `if_pos hCond` to
`SemanticTier.live`, refuted against `.reserved` by `SemanticTier.noConfusion`; the `false` branch projects the
two disjuncts with the propext-free `orEqFalse_leftFalse` / `orEqFalse_rightFalse` (from `StaticTypingSoundness`).
The legs are direct applications of the shipped HON-5 / HON-6 soundness.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The tier verdict decomposes into the two classifier falsities.**  `semanticTier g = .reserved` means the
`||` of the static (`hasSomeTypingRule`) and operational (`hasRedexHead`) classifiers is false — were it true the
tier `if` would yield `.live ≠ .reserved` — so each disjunct is individually `false`.  This is the propext-free
bridge that lets the tier soundness reuse the HON-5 static and HON-6 operational soundness legs verbatim. -/
theorem semanticTier_reserved_imp_both_false {g : Generator}
    (reserved : semanticTier g = .reserved) :
    hasSomeTypingRule g = false ∧ g.hasRedexHead = false := by
  dsimp only [semanticTier] at reserved
  cases hCond : (hasSomeTypingRule g || g.hasRedexHead) with
  | true =>
      rw [if_pos hCond] at reserved
      exact SemanticTier.noConfusion reserved
  | false =>
      exact ⟨orEqFalse_leftFalse hCond, orEqFalse_rightFalse hCond⟩

/-- **Operational half of the tier soundness.**  A `reserved` generator fires no root redex on ANY cell built on
it: `hasRootStepSource (mkGen g payload children) = false`.  Composes the bridge's `hasRedexHead = false` with the
HON-6 operational-inertness soundness. -/
theorem reservedTierOperationallyInert {g : Generator}
    (reserved : semanticTier g = .reserved) {scope : Nat}
    (payload : g.payload scope) (children : RawTermChildren g.binderShifts scope) :
    RawTerm.hasRootStepSource (RawTerm.mkGen g payload children) = false :=
  hasRedexHead_false_imp_no_root_redex
    (semanticTier_reserved_imp_both_false reserved).2 payload children

/-- **Static half of the tier soundness (grown representative).**  A `reserved` generator heads no grown-typed
(`HasTypeDescPi`) cell: any subject whose head is `g` has no `HasTypeDescPi` derivation.  Composes the bridge's
`hasSomeTypingRule = false` (rewritten along the head equation) with the HON-5 grown leg. -/
theorem reservedTierUntypedByGrownEngine {g : Generator}
    (reserved : semanticTier g = .reserved) {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (headEq : RawTerm.headGenerator subject = g)
    (typed : HasTypeDescPi profile context subject classifier) : False :=
  grownReservedUntyped (by rw [headEq]; exact (semanticTier_reserved_imp_both_false reserved).1) typed

/-- **The COMPLETE static half.**  A `reserved` generator heads no cell typed by ANY of the 16 engines the
classifier consults — the full HON-5 bundle, threaded through the head equation.  This is the exhaustive
"untyped by every engine" companion to the grown-representative headline. -/
theorem reservedTierUntypedByEveryEngine {g : Generator}
    (reserved : semanticTier g = .reserved) {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    (headEq : RawTerm.headGenerator subject = g) :
    (∀ classifier : RawTerm scope, ¬ HasTypeDescPi profile context subject classifier) ∧
    (∀ classifier : RawTerm scope, ¬ HasTypeDescFlat profile context subject classifier) ∧
    (∀ classifier : RawTerm scope, ¬ HasTypeDescBaseType profile context subject classifier) ∧
    (∀ classifier : RawTerm scope, ¬ HasTypeDescDataIntro profile context subject classifier) ∧
    (∀ classifier : RawTerm scope, ¬ HasTypeDescNatIntro profile context subject classifier) ∧
    (∀ classifier : RawTerm scope, ¬ HasTypeDescIdIntro profile context subject classifier) ∧
    (∀ classifier : RawTerm scope, ¬ HasTypeDescOptionIntro profile context subject classifier) ∧
    (∀ classifier : RawTerm scope, ¬ HasTypeDescEitherIntro profile context subject classifier) ∧
    (∀ classifier : RawTerm scope, ¬ HasTypeDescPairIntro profile context subject classifier) ∧
    (∀ classifier : RawTerm scope, ¬ HasTypeDescListIntro profile context subject classifier) ∧
    (∀ classifier : RawTerm scope, ¬ HasTypeDescBoolElim profile context subject classifier) ∧
    (∀ classifier : RawTerm scope, ¬ HasTypeDescIdElim profile context subject classifier) ∧
    (∀ classifier : RawTerm scope, ¬ HasTypeDescOptionMatch profile context subject classifier) ∧
    (∀ classifier : RawTerm scope, ¬ HasTypeDescEitherMatch profile context subject classifier) ∧
    (∀ classifier : RawTerm scope, ¬ HasTypeDescSigmaProjection profile context subject classifier) ∧
    (∀ classifier : RawTerm scope, ¬ HasTypeDescBridge profile context subject classifier) :=
  reservedHeadUntypedByEveryEngine (by rw [headEq]; exact (semanticTier_reserved_imp_both_false reserved).1)

/-- **★ The tier verdict is TRUTHFUL.**  A generator the semantic-tier ledger brands `reserved` is genuinely
semantically dead: every cell built on it is untyped by the grown engine AND fires no root redex.  The static
half is the grown representative (`reservedTierUntypedByGrownEngine`); the operational half is HON-6 inertness.
The full-16-engine static completeness is `reservedTierUntypedByEveryEngine`.  Together with the LIVE complementarity
and non-vacuity from `GeneratorSemanticTier`, this is the soundness that makes the honest 203-generator
live/reserved partition a verified ledger rather than an unchecked `Bool`. -/
theorem semanticTierReservedSound {g : Generator} (reserved : semanticTier g = .reserved) :
    (∀ {profile : PolyProfile} {scope : Nat} {context : TypingContext profile scope}
       {subject classifier : RawTerm scope},
       RawTerm.headGenerator subject = g → ¬ HasTypeDescPi profile context subject classifier) ∧
    (∀ {scope : Nat} (payload : g.payload scope) (children : RawTermChildren g.binderShifts scope),
       RawTerm.hasRootStepSource (RawTerm.mkGen g payload children) = false) :=
  ⟨fun headEq typed => reservedTierUntypedByGrownEngine reserved headEq typed,
   fun payload children => reservedTierOperationallyInert reserved payload children⟩

end FX1Poly.Typed

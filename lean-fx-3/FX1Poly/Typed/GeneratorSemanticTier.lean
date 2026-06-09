import FX1Poly.Typed.TypedBySomeEngine
import FX1Poly.Core.GeneratorRedexHead

/-! # FX1Poly/Typed/GeneratorSemanticTier — the unified live/reserved ledger (HON-3)

The honest semantic classification of every one of the 197 generators, combining the two axes shipped before
it: the STATIC-typing axis `hasSomeTypingRule` (HON-1 — typed by some of the 17 typing engines) and the
OPERATIONAL axis `Generator.hasRedexHead` (HON-2 — a `Step` fires at its root).  A generator is `live` iff it
carries meaning on EITHER axis, `reserved` otherwise.  This is the single predicate that answers, honestly, for
each generator: "does this name encode anything, or is it a bare reserved slot?"

The two axes are GENUINELY complementary — neither alone suffices, and the tier is exactly their union:

  * `natElim`/`natRec`/`listElim`/`idStrictRec` REDUCE (redex heads) but are statically RESERVED (no typing
    engine types them).  The static classifier `isUntypableHead`/`typingRoleOf` would mislabel them; the tier
    catches them via the operational axis (`natElim_reducesButUntyped_stillLive`).
  * The canonical value-formers (`boolTrue`, `pair`, `lam`, …) are statically TYPED (intro engines) but are NOT
    redex heads; the tier catches them via the static axis (`boolTrue_typedNotRedex_stillLive`).
  * `gen_hilbertSpace`, `gen_quantumGate`, `gen_unit`, `gen_idCode`, … are neither — genuinely RESERVED names.

`semanticTier_discriminates` is the non-vacuity guard (the classifier is non-constant), in the spirit of
`MetatheoryParityLedger.parity_discriminates_*`.  The SOUNDNESS of the `reserved` verdict — that a reserved
generator is genuinely untyped by all engines AND has no root `Step` — is HON-7 (combining the HON-5 static and
HON-6 operational soundness legs); this file ships the classifier and the complementarity/non-vacuity facts.

## Zero-axiom

`if`-over-`Bool` (the two classifiers' `||`), every witness `rfl` / `⟨rfl, rfl, rfl⟩`; the discriminator is
`rw` to the reduced tier values + `SemanticTier.noConfusion` (propext-free constructor disequality — NOT
`decide` on `Ne`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

/-- The honest semantic classification of a generator: `live` (carries static and/or operational meaning) vs
`reserved` (a bare syntactic name with no encoded semantics). -/
inductive SemanticTier where
  | live
  | reserved
  deriving DecidableEq

/-- **The unified semantic-tier classifier.**  `live` iff the generator is statically typed by some engine
(`hasSomeTypingRule`, HON-1) OR an operational redex head (`hasRedexHead`, HON-2); `reserved` otherwise.  The
honest live/reserved partition of all 197 generators. -/
def semanticTier (g : Generator) : SemanticTier :=
  if hasSomeTypingRule g || g.hasRedexHead then .live else .reserved

/-! ## LIVE witnesses -/

/-- Typed AND a redex head. -/
theorem semanticTier_app : semanticTier .gen_app = .live := rfl
/-- A typed value-former. -/
theorem semanticTier_boolTrue : semanticTier .gen_boolTrue = .live := rfl
/-- A redex head only (statically reserved, operationally live). -/
theorem semanticTier_natElim : semanticTier .gen_natElim = .live := rfl
/-- A typed former. -/
theorem semanticTier_piTyCode : semanticTier .gen_piTyCode = .live := rfl

/-! ## RESERVED witnesses — genuinely meaningless names -/

theorem semanticTier_hilbertSpace : semanticTier .gen_hilbertSpace = .reserved := rfl
theorem semanticTier_unit : semanticTier .gen_unit = .reserved := rfl
theorem semanticTier_idCode : semanticTier .gen_idCode = .reserved := rfl
theorem semanticTier_quantumGate : semanticTier .gen_quantumGate = .reserved := rfl

/-! ## ★ Axis-complementarity — why the tier needs BOTH axes -/

/-- **★ `natElim` reduces but is untyped, yet LIVE.**  A recursive eliminator: `hasRedexHead = true` (it
reduces) while `hasSomeTypingRule = false` (no engine types it) — yet `semanticTier = live`, caught by the
operational axis.  The static-only classifiers would wrongly bucket it with the reserved zoo. -/
theorem natElim_reducesButUntyped_stillLive :
    Generator.gen_natElim.hasRedexHead = true ∧ hasSomeTypingRule .gen_natElim = false
      ∧ semanticTier .gen_natElim = .live := ⟨rfl, rfl, rfl⟩

/-- **★ Dual: `boolTrue` is typed but not a redex head, still LIVE** — caught by the static axis.  Together with
the above this proves neither axis alone suffices; the tier is genuinely their union. -/
theorem boolTrue_typedNotRedex_stillLive :
    hasSomeTypingRule .gen_boolTrue = true ∧ Generator.gen_boolTrue.hasRedexHead = false
      ∧ semanticTier .gen_boolTrue = .live := ⟨rfl, rfl, rfl⟩

/-- Non-vacuity: the tier genuinely distinguishes generators (a live one from a reserved one), so the
classification is not a constant. -/
theorem semanticTier_discriminates :
    semanticTier .gen_app ≠ semanticTier .gen_hilbertSpace := by
  rw [semanticTier_app, semanticTier_hilbertSpace]
  exact fun h => SemanticTier.noConfusion h

end FX1Poly.Typed

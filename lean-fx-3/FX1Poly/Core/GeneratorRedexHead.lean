import FX1Poly.Core.GeneratorCore

/-! # FX1Poly/Core/GeneratorRedexHead — the operational-liveness (redex-head) classifier (HON-2)

The operational axis of the generator-honesty ledger.  `Generator.hasRedexHead` decides, for each of the 203
generators, whether a `Step` reduction fires at the ROOT of a cell headed by it — i.e. whether the generator is
an ELIMINATOR with a β/ι rule.  This is exactly the generator set of `RawTerm.hasRootStepSource`
(`RawTermNF.lean`): the eleven heads `gen_app` (β) and the ι-eliminators
`gen_boolElim`/`gen_fst`/`gen_snd`/`gen_natElim`/`gen_natRec`/`gen_listElim`/`gen_optionMatch`/`gen_eitherMatch`/
`gen_idJ`/`gen_idStrictRec`.

It is the complement the honest semantic tier needs ALONGSIDE the static-typing classifier `hasSomeTypingRule`
(HON-1).  The two axes are genuinely DIFFERENT:

  * Canonical value-formers (`gen_lam`, `gen_boolTrue`, `gen_pair`, `gen_refl`, …) are NOT redex heads — they do
    not reduce at their own root, they are CONSUMED by the eliminators — so they are operationally live as VALUES,
    captured by the STATIC axis (the intro engines type them), not here.
  * The recursive / strict eliminators (`gen_natElim`, `gen_natRec`, `gen_listElim`, `gen_idStrictRec`) REDUCE
    but are statically RESERVED (no typing engine types them — `hasSomeTypingRule` is `false` on them).  They are
    the operational axis's marginal contribution to the tier: live by reduction, invisible to typing.
  * A generator that is neither a redex head NOR statically typed (e.g. `gen_hilbertSpace`) is genuinely reserved.

`hasRedexHead` is the CLASSIFIER; its soundness — `hasRedexHead g = false → mkGen g _ _ has no root Step` — is
HON-6 (`GeneratorRedexHeadSoundness.lean`: a `dif_neg` chain against `hasRootStepSource`'s eleven-head dispatch
+ the `hasRootStepSource` ↔ `Step` pins).  η-extension heads (`gen_pathLam`/`gen_modIntro`/`gen_glueIntro` +
their unwraps) are a separate axis (HON-15), since `hasRootStepSource` is β+ι only by design.

## Zero-axiom

`decide` over `DecidableEq Generator`, `||`-combined — NO wildcard match (propext-clean); every witness `rfl`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated
in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- **The redex-head classifier.**  `true` iff a `Step` fires at the root of `mkGen g _ children` — the eleven
eliminator generators (β: `gen_app`; ι: boolElim/fst/snd/natElim/natRec/listElim/optionMatch/eitherMatch/idJ/
idStrictRec), exactly `RawTerm.hasRootStepSource`'s generator set.  The operational axis of the honesty tier. -/
def Generator.hasRedexHead (g : Generator) : Bool :=
  decide (g = .gen_app) || decide (g = .gen_boolElim) || decide (g = .gen_fst) || decide (g = .gen_snd)
  || decide (g = .gen_natElim) || decide (g = .gen_natRec) || decide (g = .gen_listElim)
  || decide (g = .gen_optionMatch) || decide (g = .gen_eitherMatch)
  || decide (g = .gen_idJ) || decide (g = .gen_idStrictRec)

/-! ## LIVE — the redex heads, by `rfl` -/

/-- β-elimination (application). -/
theorem hasRedexHead_app : Generator.gen_app.hasRedexHead = true := rfl
/-- Boolean elimination. -/
theorem hasRedexHead_boolElim : Generator.gen_boolElim.hasRedexHead = true := rfl
/-- Nat recursion (a RECURSIVE eliminator — reduces, yet statically reserved). -/
theorem hasRedexHead_natElim : Generator.gen_natElim.hasRedexHead = true := rfl
/-- Dependent Nat recursor. -/
theorem hasRedexHead_natRec : Generator.gen_natRec.hasRedexHead = true := rfl
/-- List recursion. -/
theorem hasRedexHead_listElim : Generator.gen_listElim.hasRedexHead = true := rfl
/-- Strict identity eliminator. -/
theorem hasRedexHead_idStrictRec : Generator.gen_idStrictRec.hasRedexHead = true := rfl

/-! ## NOT redex heads — canonical values / binders (operationally live as VALUES, via the static axis) -/

/-- A λ is a canonical value, not a redex head: `app(lam, a)` reduces (headed by `gen_app`), a bare `lam` does
not. -/
theorem hasRedexHead_lam : Generator.gen_lam.hasRedexHead = false := rfl
/-- `boolTrue` is a canonical value (the scrutinee `boolElim` consumes), not a redex head. -/
theorem hasRedexHead_boolTrue : Generator.gen_boolTrue.hasRedexHead = false := rfl
/-- A pair is a canonical value (projected by `fst`/`snd`), not a redex head. -/
theorem hasRedexHead_pair : Generator.gen_pair.hasRedexHead = false := rfl
/-- A Π type-code is a former, not a redex head. -/
theorem hasRedexHead_piTyCode : Generator.gen_piTyCode.hasRedexHead = false := rfl

/-! ## RESERVED — neither redex head nor statically typed -/

theorem hasRedexHead_hilbertSpace : Generator.gen_hilbertSpace.hasRedexHead = false := rfl
theorem hasRedexHead_quantumGate : Generator.gen_quantumGate.hasRedexHead = false := rfl

end FX1Poly.Core

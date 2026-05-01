import LeanFX.Syntax.Reduction.ParBi
import LeanFX.Syntax.Reduction.RawPar
import LeanFX.Syntax.ToRaw
import LeanFX.Syntax.ToRawCommute

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Step.par.toRawBridge` — typed parallel reduction lifts to raw.

For every typed `Step.par sourceTerm targetTerm` with a βι-witness
(`Step.par.isBi`), produce the corresponding raw step
`RawStep.par sourceTerm.toRaw targetTerm.toRaw`.

The bridge is the architecturally clean route to typed `parStar`
inversion: raw `parStar` enjoys clean Lean-elaborable inversion
lemmas (`RawStep.par.lam_inv`, `pair_inv`, `boolTrue_inv`, …),
while typed `parStar` does not because constructors like
`betaApp` carry target types involving non-injective `Ty.subst0`.

η is excluded by the `isBi` gate: `Step.par.isBi` has no
`etaArrow` / `etaSigma` ctors, so `induction biWitness` simply
omits those cases — no vacuous handling needed.

The four dependent β cases (`betaApp` / `betaAppPi` non-deep + deep)
require `Term.toRaw_subst0` to commute with `Term.subst0`'s
singleton-flavor target; this is blocked on Wave 6 β-surgery
(`Subst.singleton` → `Subst.termSingleton` migration).  We isolate
them with structured `sorry` markers and a precise TODO referencing
#1006-#1014. -/

/-- Forward bridge for βι parallel reduction: typed lifts to raw
via `Term.toRaw`.

Lean's `induction biWitness` binds only the recursive `isBi`
premises and their IHs in `case` syntax — explicit Term arguments
of each `isBi` constructor become anonymous hypotheses (visible
via `rename_i` if needed).  Where a raw rule needs an explicit
RawTerm argument, we pass `_` and let the elaborator unify
against the goal's source / target. -/
theorem Step.par.toRawBridge
    {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
    {sourceType : Ty level scope}
    {sourceTerm targetTerm : Term ctx sourceType}
    {parallelStep : Step.par sourceTerm targetTerm}
    (biWitness : Step.par.isBi parallelStep) :
    RawStep.par sourceTerm.toRaw targetTerm.toRaw := by
  induction biWitness
  -- Reflexivity.
  case refl term =>
    exact RawStep.par.refl term.toRaw
  -- Pure congruence cases (no contraction inside the rule).
  case lam bodyIH =>
    exact RawStep.par.lam bodyIH
  case lamPi bodyIH =>
    exact RawStep.par.lam bodyIH
  case app functionIH argumentIH =>
    exact RawStep.par.app functionIH argumentIH
  case appPi functionIH argumentIH =>
    exact RawStep.par.app functionIH argumentIH
  case pair firstIH secondIH =>
    exact RawStep.par.pair firstIH secondIH
  case fst pairIH =>
    exact RawStep.par.fst pairIH
  case snd pairIH =>
    exact RawStep.par.snd pairIH
  case boolElim scrutineeIH thenIH elseIH =>
    exact RawStep.par.boolElim scrutineeIH thenIH elseIH
  case natSucc predIH =>
    exact RawStep.par.natSucc predIH
  case natElim scrutineeIH zeroIH succIH =>
    exact RawStep.par.natElim scrutineeIH zeroIH succIH
  case natRec scrutineeIH zeroIH succIH =>
    exact RawStep.par.natRec scrutineeIH zeroIH succIH
  case listCons headIH tailIH =>
    exact RawStep.par.listCons headIH tailIH
  case listElim scrutineeIH nilIH consIH =>
    exact RawStep.par.listElim scrutineeIH nilIH consIH
  case optionSome valueIH =>
    exact RawStep.par.optionSome valueIH
  case optionMatch scrutineeIH noneIH someIH =>
    exact RawStep.par.optionMatch scrutineeIH noneIH someIH
  case eitherInl valueIH =>
    exact RawStep.par.eitherInl valueIH
  case eitherInr valueIH =>
    exact RawStep.par.eitherInr valueIH
  case eitherMatch scrutineeIH leftIH rightIH =>
    exact RawStep.par.eitherMatch scrutineeIH leftIH rightIH
  case idJ baseIH witnessIH =>
    exact RawStep.par.idJ baseIH witnessIH
  -- Shallow ι cases — explicit Term args become `_` in the raw
  -- rule and unify against the source's `toRaw`.
  case iotaBoolElimTrue thenIH =>
    exact RawStep.par.iotaBoolElimTrue _ thenIH
  case iotaBoolElimFalse elseIH =>
    exact RawStep.par.iotaBoolElimFalse _ elseIH
  case iotaNatElimZero zeroIH =>
    exact RawStep.par.iotaNatElimZero _ zeroIH
  case iotaNatElimSucc predIH succIH =>
    exact RawStep.par.iotaNatElimSucc _ predIH succIH
  case iotaNatRecZero zeroIH =>
    exact RawStep.par.iotaNatRecZero _ zeroIH
  case iotaNatRecSucc predIH zeroIH succIH =>
    exact RawStep.par.iotaNatRecSucc predIH zeroIH succIH
  case iotaListElimNil nilIH =>
    exact RawStep.par.iotaListElimNil _ nilIH
  case iotaListElimCons headIH tailIH consIH =>
    exact RawStep.par.iotaListElimCons _ headIH tailIH consIH
  case iotaOptionMatchNone noneIH =>
    exact RawStep.par.iotaOptionMatchNone _ noneIH
  case iotaOptionMatchSome valueIH someIH =>
    exact RawStep.par.iotaOptionMatchSome _ valueIH someIH
  case iotaEitherMatchInl valueIH leftIH =>
    exact RawStep.par.iotaEitherMatchInl _ valueIH leftIH
  case iotaEitherMatchInr valueIH rightIH =>
    exact RawStep.par.iotaEitherMatchInr _ valueIH rightIH
  case iotaIdJRefl baseIH =>
    exact RawStep.par.iotaIdJRefl _ baseIH
  -- Shallow σ-projection β cases.
  case betaFstPair firstIH =>
    exact RawStep.par.betaFstPair _ firstIH
  case betaSndPair secondIH =>
    exact RawStep.par.betaSndPair _ secondIH
  -- Deep σ-projection β cases.
  case betaFstPairDeep pairIH =>
    exact RawStep.par.betaFstPairDeep pairIH
  case betaSndPairDeep pairIH =>
    exact RawStep.par.betaSndPairDeep pairIH
  -- Deep ι cases (12).
  case iotaBoolElimTrueDeep scrutineeIH thenIH =>
    exact RawStep.par.iotaBoolElimTrueDeep _ scrutineeIH thenIH
  case iotaBoolElimFalseDeep scrutineeIH elseIH =>
    exact RawStep.par.iotaBoolElimFalseDeep _ scrutineeIH elseIH
  case iotaNatElimZeroDeep scrutineeIH zeroIH =>
    exact RawStep.par.iotaNatElimZeroDeep _ scrutineeIH zeroIH
  case iotaNatElimSuccDeep scrutineeIH succIH =>
    exact RawStep.par.iotaNatElimSuccDeep _ scrutineeIH succIH
  case iotaNatRecZeroDeep scrutineeIH zeroIH =>
    exact RawStep.par.iotaNatRecZeroDeep _ scrutineeIH zeroIH
  case iotaNatRecSuccDeep scrutineeIH zeroIH succIH =>
    exact RawStep.par.iotaNatRecSuccDeep scrutineeIH zeroIH succIH
  case iotaListElimNilDeep scrutineeIH nilIH =>
    exact RawStep.par.iotaListElimNilDeep _ scrutineeIH nilIH
  case iotaListElimConsDeep scrutineeIH consIH =>
    exact RawStep.par.iotaListElimConsDeep _ scrutineeIH consIH
  case iotaOptionMatchNoneDeep scrutineeIH noneIH =>
    exact RawStep.par.iotaOptionMatchNoneDeep _ scrutineeIH noneIH
  case iotaOptionMatchSomeDeep scrutineeIH someIH =>
    exact RawStep.par.iotaOptionMatchSomeDeep _ scrutineeIH someIH
  case iotaEitherMatchInlDeep scrutineeIH leftIH =>
    exact RawStep.par.iotaEitherMatchInlDeep _ scrutineeIH leftIH
  case iotaEitherMatchInrDeep scrutineeIH rightIH =>
    exact RawStep.par.iotaEitherMatchInrDeep _ scrutineeIH rightIH
  case iotaIdJReflDeep witnessIH baseIH =>
    exact RawStep.par.iotaIdJReflDeep witnessIH baseIH
  -- The four β cases below are architecturally blocked.  The blocker:
  -- typed `Step.par.betaApp` produces a target of shape
  --   `(Ty.weaken_subst_singleton ...) ▸ Term.subst0 body' arg'`
  -- whose raw projection is `(toRaw body').subst RawTermSubst.dropNewest`
  -- (because `Subst.singleton`'s `forRaw` field is `dropNewest`, which
  -- maps position 0 to `RawTerm.unit`).  The raw rule
  -- `RawStep.par.betaApp` instead produces `(toRaw body').subst0 (toRaw
  -- arg') = (toRaw body').subst (RawTermSubst.singleton (toRaw arg'))`
  -- (which maps position 0 to `toRaw arg'`).  When `body'` contains a
  -- `Term.refl r` referencing position 0 in `r`, the two raw projections
  -- DIFFER — and there is no chain of raw cong rules between them, since
  -- `toRaw arg' ⟶par* unit` doesn't hold for non-unit arguments.
  --
  -- This is NOT a soundness concern (both typed and raw reductions are
  -- sound on their own); it's a bridge concern.  The fix requires
  -- migrating the typed `betaApp` ctor to use `Term.subst0_term`
  -- instead of `Term.subst0` so the toRaw projection puts `toRaw arg'`
  -- (not `unit`) at position 0.
  --
  -- The required infrastructure is mostly landed: `Term.subst0_term`
  -- exists, `Term.toRaw_subst0_term` proves the unconditional bridge
  -- (`ToRawCommute.lean:266`), and `Term.subst0_term_subst_HEq`
  -- (Phase C1, `ToRawCommute.lean`) handles substitution-commute.
  -- What remains:
  --   * Phase C3 (#1008): change `Step.par.betaApp` ctor to produce
  --     `Term.subst0_term body' arg'` with cast through
  --     `Ty.weaken_subst_termSingleton`.
  --   * Phase C5 (#1010): update `Step.par.subst_compatible` β-arm
  --     to use `subst0_term_subst_HEq`.  Requires adding a
  --     `RawConsistent termSubstitution` hypothesis (or proving the
  --     β-arm's specific substitution is RawConsistent at the call
  --     site).
  --   * Phase C7-C8 (#1012-#1013): mechanical propagation through cd
  --     cascade and the parStarWithBi family.
  --   * Phase C9 (#1014): the 4 sorries below close trivially via
  --     `Term.toRaw_subst0_term` once the ctor change lands.
  --
  -- An alternative path (without kernel migration): restrict the
  -- bridge to terms whose `body'` has no `refl(var 0)` subterm — but
  -- this severely limits the bridge's usefulness for general
  -- dependent-type confluence work.
  --
  -- TODO(Phase C): close after `Step.par.betaApp` ctor migration to
  -- `subst0_term` form.  See WS.1-#1156 / WS.4-#1159 for details.
  case betaApp _ _ => sorry
  case betaAppPi _ _ => sorry
  case betaAppDeep _ _ => sorry
  case betaAppPiDeep _ _ => sorry

end LeanFX.Syntax

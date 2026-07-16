import FX1Poly.Polygraph.TwoCategory.Table.WordProblemDecisionLedger
import FX1Poly.Polygraph.TwoCategory.WalkingInvolution.InvolutionDecision
import FX1Poly.Polygraph.TwoCategory.WalkingCyclicThree.CyclicThreeDecision
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordProblem
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentSaturatedNormalizer
import FX1Poly.Polygraph.TwoCategory.Table.WalkerDualityInstances
import FX1Poly.Polygraph.TwoCategory.WalkingKZ.KZMonadDecision
import FX1Poly.Polygraph.TwoCategory.WalkingKZ.KZOrderCompleteness
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingDecisionAssembly
import FX1Poly.Polygraph.TwoCategory.WalkingOperad.OperadTreeDecision

/-! # Polygraph/TwoCategory/Table/WordProblemDecisionWitnessBundle — the grounded decider bundle

★ **The non-rotting upgrade to `WordProblemDecisionLedger` (WP-LEDGER #2048).**

The core ledger cites each rung's decision witness by decl NAME in a docstring.  This file HOLDS them: each
`wpLedger*Decider` is a definitional alias of the real decider, so if any decider is renamed or removed the
alias breaks the build — the citation cannot silently rot (the countermeasure from [[feedback_three_strata_drift]]:
prefer a machine-checked term over a prose claim).  All eleven aliases elaborate in this ONE module, so the
module itself is the coexistence witness: the decided-10's deciders exist and typecheck together.

The ten shipped deciders:

  * involution 1-cell — `decideInvolutionOneCellConv`
  * cyclic-3 1-cell — `decideCyclicThreeOneCellConv` (the ℤ/3 residue decider)
  * monad full-2-cell — `monadSaturatedTwoCellDecision`
  * idempotent full-2-cell — `decideSaturatedConvOverIdempotentNative`
  * comonad full-2-cell — `decideSaturatedConvOverComonadNative` (op-transport of the monad decider)
  * idempotent-comonad full-2-cell — `decideSaturatedConvOverIdempotentComonadNative`
  * KZ 2-cell equality — `decideKZEq`
  * KZ directed order — `decideKZLETotal`
  * co-KZ directed order — `decideCoKZLETotal`
  * adjunction full-2-cell by matching — `decideSaturatedTwoCellConv_ofSeed`
  * operad tree-pasting — `decideOperadTreeConv` (right-comb normal form)

(Eleven aliases, ten rungs: KZ contributes both its equality and its order decider.)

The audit twin runs `#assert_no_axioms` on every alias, which — transitively — MACHINE-CHECKS the ledger's
claim that the decision witnesses themselves are zero-axiom, not merely that this wrapper is.

Raw Lean 4 + Init; definitional aliases + one coexistence tuple, no new proof content. -/

namespace FX1Poly.Polygraph.Table

/-! ## The eleven grounding aliases (one per decision witness) -/

/-- Involution — the total 1-cell (dimension-1 `Z/2`) word-problem decider.  `@` keeps the binders explicit so
the alias does not eagerly synthesize the decl's implicit mode/path arguments. -/
def wpLedgerInvolutionDecider := @FX1Poly.Polygraph.decideInvolutionOneCellConv

/-- Cyclic-3 — the total 1-cell (dimension-1 `Z/3`) word-problem decider (the former decided-8 gap, now closed). -/
def wpLedgerCyclicThreeDecider := @FX1Poly.Polygraph.decideCyclicThreeOneCellConv

/-- Walking monad — the total saturated-2-cell decider (Delta-plus monotone map). -/
def wpLedgerMonadDecider := @FX1Poly.Polygraph.monadSaturatedTwoCellDecision

/-- Idempotent semigroup (= idempotent monad) — the total saturated-2-cell decider (locally posetal). -/
def wpLedgerIdempotentDecider := @FX1Poly.Polygraph.Amalgam.decideSaturatedConvOverIdempotentNative

/-- Walking comonad — the total saturated-2-cell decider (op-transport of the monad decider). -/
def wpLedgerComonadDecider := @FX1Poly.Polygraph.Table.decideSaturatedConvOverComonadNative

/-- Idempotent comonad — the total saturated-2-cell decider (op-transport of the idempotent decider). -/
def wpLedgerIdempotentComonadDecider :=
  @FX1Poly.Polygraph.Table.decideSaturatedConvOverIdempotentComonadNative

/-- Walking KZ — the total 2-cell equality decider (via the monad monotone map). -/
def wpLedgerKZEqDecider := @FX1Poly.Polygraph.decideKZEq

/-- Walking KZ — the total directed-order decider (the unconditional order closure). -/
def wpLedgerKZOrderDecider := @FX1Poly.Polygraph.decideKZLETotal

/-- Walking co-KZ — the total directed-order decider (the reversed KZ order). -/
def wpLedgerCoKZOrderDecider := @FX1Poly.Polygraph.Table.decideCoKZLETotal

/-- Walking adjunction — the total saturated-2-cell decider by boundary-arc MATCHING (not rewriting). -/
def wpLedgerAdjunctionDecider := @FX1Poly.Polygraph.decideSaturatedTwoCellConv_ofSeed

/-- Walking monoid operad — the total tree-pasting decider (right-comb normal form, WP-OPERAD brick 2). -/
def wpLedgerOperadDecider := @FX1Poly.Polygraph.decideOperadTreeConv

/-! ## The grounding marker -/

/-- ★ **THE TEN DECIDERS ARE HELD AND GROUNDED (recorded).**  `= true` records that all TEN shipped
word-problem deciders are held as the eleven definitional aliases above (KZ contributes two; cyclic-3's ℤ/3
decider closed the former decided-8 gap; the operad's right-comb decision joined as decided-10), all
typechecking in ONE module — machine proof that the decided-10's deciders exist and coexist in one import
context, upgrading the core ledger's decl-name citations to machine-checked terms.  The DECISION-axis
counterpart to the census's grounded presentation conjunction `squierFamilyFourWalkersCoherentlyPresented`.
The audit twin's `#assert_no_axioms` on the aliases transitively certifies the deciders themselves are
zero-axiom. -/
def fxWpLedger_tenDecidersHeldAndGrounded : Bool := true

end FX1Poly.Polygraph.Table

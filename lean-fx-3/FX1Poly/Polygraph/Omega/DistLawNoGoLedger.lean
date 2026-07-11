import FX1Poly.Polygraph.Omega.WalkingDistLawSortNF

/-! # Polygraph/Omega/DistLawNoGoLedger — the distributive-law no-go ledger and census feed
(WP-DISTLAW r1, B4 + B5)

★ **The free-theory / specific-monad boundary, stated exactly, as a proof-carrying LEDGER INTERFACE (not a
mechanized no-go).**  The recon adjudication: the no-go theorems for distributive laws (Zwart–Marsden, LICS
2019 / LMCS 2022; Klin–Salamanca, MFPS 2018 — no distributive law of the powerset monad over itself) are
MODEL-LEVEL facts about specific `Set`-monads, proved by small-carrier counting.  The WALKER decides the FREE
theory — a DIFFERENT animal.  So the honest r1 deliverable is a ledger interface recording the two INDEPENDENT
facts per monad-pair, with the model side populated by CITED WALLS (never a mechanized no-go this round).

## The exact boundary (B4)

For a pair of monads `(S, T)` there are two orthogonal questions:

  1. **Does the FREE distributive-law theory have a coherent presentation?**  ALWAYS YES — the walking
     distributive law's two-colour Squier presentation (`WalkingDistLawPresentation.lean`: seven generators,
     four Beck axioms + ten monad-internal rows, all resolved modulo strict) plus the decided 1-cell word
     problem (`WalkingDistLawSortNF.lean`) IS that presentation.  It is grounded here proof-carrying by
     `distLawWalkerFreeTheoryPresented`.

  2. **Does a distributive law `lambda : S.T => T.S` EXIST for the SPECIFIC monads `(S, T)` in `Set`?**  This
     is model-level and depends on `(S, T)`: it EXISTS for some (e.g. two reader monads distribute by swap —
     the sibling lane's shipped `TwoMonad.DistributiveLaw` / `readerReaderDistributiveLaw`, NAMED not
     imported), and provably does NOT exist for others (Zwart–Marsden's idempotent counterexamples;
     Klin–Salamanca's `P` over `P`).

These are INDEPENDENT: the free theory is always coherently presented (question 1), yet question 2 can go
either way.  A no-go theorem refutes question 2 for a specific `(S, T)`; it says NOTHING about question 1.
The ledger records both.

## Why NOT a mechanized no-go this round (the recon gate)

A finite-carrier refutation IS mechanizable in principle — enumerate all candidate `lambda` on a tiny carrier
(`|X| <= 2..3`) for two finitary `Set`-monads and `decide` that none satisfies all four Beck axioms.  But
WHICH specific pair has its obstruction at carrier `<= 3` is a literature question (Zwart–Marsden section 5's
idempotent counterexamples are the candidates; the powerset functor is not finitely enumerable at a fixed
tiny bound without care).  So the ledger CAN represent a `finiteRefutation` status, but NO entry is populated
with it this round — it is a follow-up gated on a literature (deep-research) stage to pin the smallest carrier
bound.  Model entries are `existsWitness` or `citedWall` only.

## The Amalgam caveat (NAMED)

The Amalgam lane's disjoint-signature word-problem combination is decidable (Pigozzi 1974; Baader–Tinelli
1998), but the distributive-law swap is a GENUINE interaction (a shared/interacting symbol), so that
unconditional decidability does NOT transfer — the mathematical reason the full 2-cell decision is hard.
Lack, *Composing PROPs* (TAC 13, 2004) and Zanasi's *Interacting Hopf Algebras* thesis (Prop. 2.30) frame the
distributive law as exactly how two PROP presentations compose; NAMED, not imported.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The model-law status and the ledger entry -/

/-- ★ The **model-level status** of a distributive law for a SPECIFIC monad pair: a concrete law exists, or
the law is refuted by a cited literature no-go, or (the follow-up shape, not populated this round) a
mechanized finite-carrier refutation at a named carrier bound. -/
inductive DistLawModelStatus where
  /-- A concrete distributive law `S.T => T.S` exists in `Set` (a witness is known). -/
  | existsWitness
  /-- No distributive law exists — a MODEL-level no-go, cited to the literature (author / theorem). -/
  | citedWall (source : String)
  /-- A mechanized finite-carrier refutation at carrier bound `carrierBound` (the follow-up SHAPE; NOT
  populated this round — the recon gate defers it to a literature stage pinning the smallest bound). -/
  | finiteRefutation (carrierBound : Nat)

/-- ★ A **distributive-law ledger entry** for one monad pair: whether the FREE theory has a coherent
presentation (the walker — ALWAYS true), and the MODEL-level status of the specific law (the two independent
facts of the boundary).  The `pairName` names the monad pair. -/
structure DistLawLedgerEntry where
  /-- The monad pair this entry is about (e.g. "reader over reader"). -/
  pairName : String
  /-- Does the FREE distributive-law theory have a coherent presentation?  Always `true` (the walker). -/
  freeTheoryPresented : Bool
  /-- The model-level status of the specific law `S.T => T.S`. -/
  modelLawStatus : DistLawModelStatus

/-! ## The populated entries (model side: cited walls + one exists-witness) -/

/-- Reader over reader: the free theory is presented (the walker); a concrete law EXISTS (two reader monads
distribute by swap — the sibling lane's shipped `TwoMonad.DistributiveLaw` / `readerReaderDistributiveLaw`,
NAMED not imported). -/
def distLawLedgerReaderReader : DistLawLedgerEntry where
  pairName := "reader over reader"
  freeTheoryPresented := true
  modelLawStatus := DistLawModelStatus.existsWitness

/-- Powerset over powerset: the free theory is presented (the walker); NO law exists (Klin–Salamanca, MFPS
2018 — iterated covariant powerset is not a monad / no distributive law of `P` over `P`). -/
def distLawLedgerPowersetPowerset : DistLawLedgerEntry where
  pairName := "powerset over powerset"
  freeTheoryPresented := true
  modelLawStatus := DistLawModelStatus.citedWall "Klin-Salamanca, MFPS 2018 (no distributive law of P over P)"

/-- An idempotent-monad counterexample: the free theory is presented (the walker); NO law exists
(Zwart–Marsden, LICS 2019 / LMCS 2022 — no-go theorems for distributive laws, the idempotent counterexamples
of section 5). -/
def distLawLedgerIdempotentCounterexample : DistLawLedgerEntry where
  pairName := "Zwart-Marsden idempotent counterexample"
  freeTheoryPresented := true
  modelLawStatus :=
    DistLawModelStatus.citedWall "Zwart-Marsden, LICS 2019 / LMCS 2022 (no-go theorems for distributive laws)"

/-- The ledger — the three populated entries (one exists-witness, two cited walls). -/
def distLawNoGoLedger : List DistLawLedgerEntry :=
  [distLawLedgerReaderReader, distLawLedgerPowersetPowerset, distLawLedgerIdempotentCounterexample]

/-- ★ **Every entry's free-theory side is `true`** — the walker presents the free theory of EVERY monad
pair, independent of the model-level status.  Kernel-checked over the ledger. -/
theorem distLawNoGoLedger_allFreeTheoryPresented :
    ∀ entry ∈ distLawNoGoLedger, entry.freeTheoryPresented = true
  | _, List.Mem.head _ => rfl
  | _, List.Mem.tail _ (List.Mem.head _) => rfl
  | _, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)) => rfl

/-- The ledger has exactly three populated entries. -/
theorem distLawNoGoLedger_countIsThree : distLawNoGoLedger.length = 3 := rfl

/-! ## The free-theory side, GROUNDED by the walker (proof-carrying)

The `freeTheoryPresented = true` flag is NOT a bare tally — it is grounded by the shipped walking-distributive-
law presentation and its decided 1-cell word problem. -/

/-- ★ **The walker's free-theory presentation statement** — the four Beck axioms coherently resolved modulo
strict AND the 1-cell word problem decided (convertibility equivalent to letter counts).  The proof-carrying
content behind `freeTheoryPresented = true`. -/
def DistLawWalkerFreeTheoryPresentedStatement : Prop :=
  DistLawFourBeckAxiomsResolvedStatement ∧
  (∀ w1 w2 : List DistLawColour, DistLawWordConv w1 w2 ↔ DistLawWordSameCount w1 w2)

/-- ★★ **THE FREE THEORY IS PRESENTED (grounded).**  The walking distributive law's free theory has a
coherent presentation: the four Beck axioms are resolved modulo strict (`distLawFourBeckAxiomsResolved`) and
the 1-cell word problem is decided (`distLawConv_iffSameCount`).  This grounds every ledger entry's
`freeTheoryPresented = true` — it is proof-carrying, not a marker. -/
theorem distLawWalkerFreeTheoryPresented : DistLawWalkerFreeTheoryPresentedStatement :=
  ⟨distLawFourBeckAxiomsResolved, distLawConv_iffSameCount⟩

/-! ## The census feed and the downstream inheritance (B5)

★ **What feeds the `SquierFamilyCensus` and what the downstream lanes inherit — recorded here, NOT by editing
the census** (the recon's namespace-hygiene directive: the walking distributive law is a genuinely NEW walker,
so touch the decided-9 tally only with a fresh entry, never silently renumber). -/

/-- ★ **THE CENSUS FEED (recorded, not applied).**  `= true` records that the walking distributive law is a
genuinely NEW single-object walker: two 1-generators `s`, `t`, five 2-generators, fourteen critical-pair rows.
It FITS the `OmegaComputad` single-mode (`modeCarrier := Unit`) family pattern — unlike Brauer / Frobenius,
which are walled multi-object.  So it would ADD a fresh entry to the `SquierFamilyCensus` decided-set (a tenth
walker, or a new two-generator family row), with status `shippedOmegaLane` for its four-Beck presentation.
This is NAMED here; the census's decided-9 tally and its exhaustiveness proof are NOT touched this round. -/
def fxDistLaw_censusFeedNewSingleObjectWalker : Bool := true

/-- ★ **THE DOWNSTREAM INHERITANCE (recorded).**  `= true` records what the downstream lanes (WP-STRONG,
WP-BANG) inherit from this round: (i) the two-colour signature scaffold `distLawOmegaComputad` (a
`DistLawGenLabel` seven-label family — the reusable multi-generator pattern); (ii) the four Beck-axiom rows +
ten monad-internal rows as a `SaturatedConvOverWithId` presentation; (iii) the 1-cell sort backbone
(inversion-count structural-fuel bubble sort) + the decided word problem.  The co-distributive-law
(`op(swap)`) is op-dual-reachable via the shipped generic op-transport (`opCriticalPairResolved` in
`PresentationOpDualityWithId.lean`), NAMED not re-derived. -/
def fxDistLaw_downstreamInheritanceRecorded : Bool := true

/-! ## The jam ledger — every wall the exact goal + a NAMED node (B5) -/

/-- ★ **JAM 1 — the full 2-cell decision (WALLED).**  Goal: decide EVERY parallel pair of free 2-cells (à la
`monadSaturatedTwoCellDecision`).  FALSE at this scope.  NAMED node: `monadPath_normalForm`
(`MonadSaturatedCanonReps.lean`) — "every 1-cell is a `t`-power" — is FALSE for two colours (`s.t` is not a
`t`-power), so the single-ordinal `List Nat` monotone-map model cannot encode an interleaved `{s,t}`-word plus
its shuffle data.  A genuine two-colour monotone-map model is a research object, not a mechanical retune. -/
def fxDistLaw_jamFullTwoCellDecisionAtMonadPathNormalForm : Bool := true

/-- ★ **JAM 2 — a mechanized finite no-go (DEFERRED, not walled).**  Goal: a machine-checked
`finiteRefutation` — enumerate all candidate `lambda` on a tiny carrier for a specific finitary monad pair and
`decide` no Beck-law-satisfying law exists.  NOT a wall (it is mechanizable in principle), but DEFERRED: the
NAMED node is "the smallest carrier bound for a specific pair", a literature question (Zwart–Marsden section 5
candidates) gated on a deep-research stage.  The ledger's `finiteRefutation` status is the target shape; no
entry is populated with it this round. -/
def fxDistLaw_jamMechanizedFiniteNoGoDeferredOnCarrierBound : Bool := true

/-- ★ **JAM 3 — the full homotopy basis (OMEGA-5 HANDOFF).**  Goal: every parallel 2-path pair
3-cell-homotopic, by a structural length-fuel 2-path normalizer one dimension up.  NAMED node: the 2-path
normalizer (the `conv_toParityNF`-analogue at the 2-path level) over the fourteen-generator homotopy basis —
the same OMEGA-5 remainder the walking monad deferred
(`fxOmega4_walkingMonadFullHomotopyBasisReached = false`). -/
def fxDistLaw_jamFullHomotopyBasisOmegaFiveHandoff : Bool := true

/-! ## The #2187 state marker -/

/-- ★★ **THE WP-DISTLAW r1 STATE (#2187).**  `= true` records the round's honest deliverable: the walking
distributive law opens as a two-colour Squier presentation (four Beck axioms resolved modulo strict + ten
monad-internal rows), its 1-cell word problem is DECIDED (sorted normal form `t^m s^n`, inversion-count
structural-fuel termination, both verdicts), and the no-go / free-theory boundary is recorded as a
proof-carrying ledger with cited walls (`distLawWalkerFreeTheoryPresented` grounds the free-theory side).
Three named jams remain: the full 2-cell decision (walled at `monadPath_normalForm`), a mechanized finite
no-go (deferred on the carrier bound), and the full homotopy basis (OMEGA-5 handoff).  NOT a close — an
opening, honestly bounded. -/
def fxDistLaw_wpDistLawR1StateRecorded : Bool := true

end FX1Poly.Polygraph.Omega

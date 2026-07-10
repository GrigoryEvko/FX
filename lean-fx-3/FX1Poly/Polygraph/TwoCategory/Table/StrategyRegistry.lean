import FX1Poly.Polygraph.TwoCategory.Table.TableArchitectureLock
import FX1Poly.Polygraph.TwoCategory.Amalgam.EndgameDemo

/-! # Polygraph/TwoCategory/Table/StrategyRegistry — the CERTIFIED strategy registry + one generic dispatch
soundness theorem (POLY-TAB r1, P2)

`Table/TableArchitectureLock.lean` (r0, decision 4) anchored the strategy table with the `DecisionMechanism` tag and DEFERRED
the dependent per-mechanism certificate.  This file ships the certified registry: entries pairing a fingerprint, a
`DecisionMechanism` tag, a certified decider, and an admissibility certificate; ONE generic dispatch-soundness
theorem; and the re-seat of the MODE-ADMIT row-aware registry ONTO it BY BRIDGE — the existing `admitByRowAware`
and its `EndgameDemo` consumers keep working (additive equalities, no break), and the `EndgameDemo` near-miss
negative control is still REFUSED through the new dispatch.

## The design (Nelson-Oppen routing + MirrorShard certified hints, Init-only)

The literature splits registries into loose-index-then-recheck (Lean simp / Isabelle simproc / Coq auto) and
certify-the-dispatch (Nelson-Oppen side-conditions / MirrorShard certified hints).  Init-only zero-axiom forces the
second track: there is no second kernel to catch a bad route, so the registry must be self-certifying.  Hence:

  * **The fingerprint is an EXACT `Bool` gate** (`isRowAwarePresentationMatch`), not a discr-tree over-approximation:
    a match is a SUFFICIENT hypothesis for the returned family to decide the candidate's intended relation (the NO
    purification/disjointness discipline, not the simp discr-tree discipline).
  * **The certified decider IS `entry.family.decider`** — a `DecidableSaturatedConvForRel` whose soundness is
    intrinsic to its `Decidable` type.  **The admissibility certificate IS `entry.family.walkerIffGeneric`** — the
    family's bridge, which certifies the decider decides exactly the intended walker relation (identified with the
    generic `SaturatedConvOver`).  Both are carried by the `family` field; the projections below expose them.
  * **Dispatch soundness is ONE generic theorem** (`dispatchStrategy_sound`): if dispatch returns an entry, the
    entry's fingerprint MATCHED the candidate — proved once by projecting `List.find?`'s found-element property, no
    per-entry meta-reasoning.  Adding a row cannot weaken it (contrast Isabelle/Coq, where soundness is
    re-established per tactic invocation by the kernel).

## The re-seat by bridge (existing consumers keep working)

`certifiedStrategyRegistry` mirrors `rowAwareRegistry` (`Amalgam/ModeAdmit.lean`) entry-for-entry (the walking
monad and the walking idempotent monad, both `deltaMonotone`), so `dispatchFamily` and `admitByRowAware` agree on
every fingerprint the consumers use — proved by `rfl` for the `EndgameDemo` staging dimension and its near-miss.
The re-seat is ADDITIVE (a new value plus equalities), not a rewrite: `admitByRowAware`, `rowAwareRegistry`, and
the `EndgameDemo` payoffs are untouched.

## The negative control, refused THROUGH the new dispatch (the §27.3 Layer-1 discipline)

`EndgameDemo`'s `partialStagingRowAware` (the monad computad with associativity DROPPED) is a near-miss whose
declared laws match NO registered doctrine.  `dispatchStrategy partialStagingRowAware = none` by `rfl` — the new
dispatch REFUSES it, exactly as `admitByRowAware` does (the bridge holds on the near-miss too).  This is the
load-bearing refusal-correctness property: a near-miss is never routed to a decider whose admissibility hypothesis
is unmet.  It is registered here as a permanent regression fact — the known-witness smoke test for the dispatch
layer.

Raw Lean 4 + Init; the `List.find?` soundness helper is a structural induction with a `Bool`-cases and `injection`
(no `simp` beyond the clean `List.find?` equation, no wildcard), every payoff is `rfl`, so every declaration is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Additive: nothing in `Amalgam/` is edited.
Per-declaration `#assert_no_axioms` in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph.Table

universe u

/-! ## The `List.find?` routing-soundness helper (structural, zero-axiom) -/

/-- **The found element satisfies the search predicate** — if `List.find? pred xs = some found`, then
`pred found = true`.  Structural induction on the list with a `Bool`-cases on `pred head` and `injection`; no
`propext` (the shipped `List.find?_some` leaks it, so this is re-derived cleanly).  The load-bearing fact under the
generic dispatch soundness. -/
theorem foundElement_satisfiesPredicate {alpha : Type u} (pred : alpha → Bool) :
    (xs : List alpha) → {found : alpha} → (xs.find? pred = some found) → pred found = true
  | [], _, h => nomatch h
  | head :: rest, found, h => by
      simp only [List.find?] at h
      cases hpredHead : pred head with
      | true =>
          rw [hpredHead] at h
          injection h with headEqFound
          exact headEqFound ▸ hpredHead
      | false =>
          rw [hpredHead] at h
          exact foundElement_satisfiesPredicate pred rest h

/-! ## The certified strategy entry — (fingerprint, mechanism, certified decider, admissibility certificate) -/

/-- ★ **A certified strategy entry** — one row of the strategy table: a display `name`, a `fingerprint`
(`RowAwarePresentationData`, the EXACT decidable registry key), a `mechanism` tag (`DecisionMechanism`, WHY the
decider is sound), and a decided `family` (`SaturatedRelationFamily`).  The `family` bundles BOTH the certified
decider (`family.decider`) and the admissibility certificate (`family.walkerIffGeneric`); the projections below
expose them as the entry's certified decider and admissibility certificate. -/
structure CertifiedStrategyEntry where
  /-- The walker's display / lookup name. -/
  name : String
  /-- The EXACT decidable registry key (mode count + generator renaming + reflected law rows). -/
  fingerprint : RowAwarePresentationData
  /-- The decision mechanism tag (`Table/TableArchitectureLock.lean`): WHY the decider is sound. -/
  mechanism : DecisionMechanism
  /-- The decided family, carrying the certified decider AND the admissibility certificate. -/
  family : SaturatedRelationFamily

/-- The entry's **certified decider** — its family's `DecidableSaturatedConvForRel`, sound by its `Decidable`
type. -/
def CertifiedStrategyEntry.certifiedDecider (entry : CertifiedStrategyEntry) :
    DecidableSaturatedConvForRel entry.family.signature entry.family.baseRel :=
  entry.family.decider

/-- ★ **The entry's admissibility certificate** — the family bridge `walkerIffGeneric`, certifying the certified
decider decides EXACTLY the intended walker relation (identified with the generic `SaturatedConvOver` at the
entry's law relation).  This is the per-entry `admissible` obligation the certify-the-dispatch discipline requires,
discharged by the family's own bridge field. -/
theorem CertifiedStrategyEntry.admissibilityCertificate (entry : CertifiedStrategyEntry)
    {sourceMode targetMode : entry.family.signature.graph.Mode}
    {sourcePath targetPath : ModalityPath entry.family.signature.graph sourceMode targetMode}
    (cellAlpha cellBeta : RawTwoCellExpr entry.family.signature sourcePath targetPath) :
    entry.family.walkerConv cellAlpha cellBeta
      ↔ SaturatedConvOver entry.family.signature entry.family.baseRel cellAlpha cellBeta :=
  entry.family.walkerIffGeneric cellAlpha cellBeta

/-! ## The registry (mirroring `rowAwareRegistry` with mechanism tags) -/

/-- ★ **The certified strategy registry** — the two row-aware decided walkers (the walking monad and the walking
idempotent monad), each keyed by its DISTINCT row-aware fingerprint, tagged with its decision mechanism
(`deltaMonotone` — the Delta simplicial model separates and reconstructs, per `DecisionMechanism`).  Mirrors
`rowAwareRegistry` entry-for-entry, so the dispatch re-seats `admitByRowAware` by bridge.  The `undecidableWall`
mechanism (`EncodedConv`) is DEFINITIONALLY EXCLUDED — a certified registry admits only entries carrying a
decider, and the honest undecidability wall has none. -/
def certifiedStrategyRegistry : List CertifiedStrategyEntry :=
  [ { name := "walking monad"
      fingerprint := monadRowAware
      mechanism := DecisionMechanism.deltaMonotone
      family := monadRelationFamily },
    { name := "walking idempotent monad"
      fingerprint := idempotentRowAware
      mechanism := DecisionMechanism.deltaMonotone
      family := idempotentRelationFamily } ]

/-- **Dispatch a candidate fingerprint** — scan the certified registry for the first entry whose exact fingerprint
gate matches the candidate. -/
def dispatchStrategy (candidate : RowAwarePresentationData) : Option CertifiedStrategyEntry :=
  certifiedStrategyRegistry.find? (fun entry => isRowAwarePresentationMatch candidate entry.fingerprint)

/-- The dispatched family (the certified decider carrier), or `none` if refused. -/
def dispatchFamily (candidate : RowAwarePresentationData) : Option SaturatedRelationFamily :=
  (dispatchStrategy candidate).map (fun entry => entry.family)

/-- The dispatched decision mechanism tag, or `none` if refused. -/
def dispatchMechanism (candidate : RowAwarePresentationData) : Option DecisionMechanism :=
  (dispatchStrategy candidate).map (fun entry => entry.mechanism)

/-! ## The ONE generic dispatch-soundness theorem -/

/-- ★★ **Generic dispatch soundness (ONE theorem, no per-entry reasoning).**  If dispatch returns an entry, the
entry's fingerprint MATCHED the candidate — so the candidate genuinely satisfies the entry's exact gate, and the
returned certified decider's admissibility hypothesis is met.  Proved once by `foundElement_satisfiesPredicate`;
adding a registry row cannot weaken it.  This is the certify-the-dispatch payoff: soundness of the ROUTING itself,
not merely of a re-checked output. -/
theorem dispatchStrategy_sound (candidate : RowAwarePresentationData) (entry : CertifiedStrategyEntry)
    (dispatched : dispatchStrategy candidate = some entry) :
    isRowAwarePresentationMatch candidate entry.fingerprint = true := by
  have found :
      certifiedStrategyRegistry.find?
          (fun registered => isRowAwarePresentationMatch candidate registered.fingerprint) = some entry :=
    dispatched
  exact @foundElement_satisfiesPredicate CertifiedStrategyEntry
    (fun registered => isRowAwarePresentationMatch candidate registered.fingerprint)
    certifiedStrategyRegistry entry found

/-! ## The re-seat by bridge — `admitByRowAware` consumers keep working -/

/-- ★ **Re-seat, staging dimension** — on `EndgameDemo`'s staging fingerprint the new dispatch and the shipped
`admitByRowAware` return the SAME family (`some monadRelationFamily`), by `rfl`.  The `EndgameDemo` consumer that
reads `admitByRowAware stagedRowAware` keeps working through the certified dispatch. -/
theorem dispatchFamily_staged_eq_admit :
    dispatchFamily stagedRowAware = admitByRowAware stagedRowAware := rfl

/-- ★ The dispatched staging family IS the separating walking monad (routed by its reflected law rows). -/
theorem dispatchFamily_staged_isMonad :
    dispatchFamily stagedRowAware = some monadRelationFamily := rfl

/-- ★ **The dispatch preserves the mechanism tag** — the staging dimension is dispatched with the `deltaMonotone`
tag (the Delta simplicial model), queryable at the call site. -/
theorem dispatchMechanism_staged_isDelta :
    dispatchMechanism stagedRowAware = some DecisionMechanism.deltaMonotone := rfl

/-- ★ **Re-seat, idempotent dimension** — the idempotent fingerprint routes to `idempotentRelationFamily` through
the new dispatch, agreeing with `admitByRowAware`, by `rfl`. -/
theorem dispatchFamily_idempotent_eq_admit :
    dispatchFamily idempotentRowAware = admitByRowAware idempotentRowAware := rfl

/-! ## The near-miss negative control, REFUSED through the new dispatch -/

/-- ★★ **The near-miss is REFUSED through the new dispatch.**  `EndgameDemo`'s `partialStagingRowAware` (the monad
computad with associativity DROPPED) matches NO registered doctrine, so `dispatchStrategy` returns `none` — the
load-bearing refusal-correctness fact: a near-miss is never routed to a decider whose admissibility hypothesis is
unmet.  `= none` by `rfl`. -/
theorem dispatchStrategy_refusesNearMiss :
    dispatchStrategy partialStagingRowAware = none := rfl

/-- ★ The refused near-miss yields NO family (nor mechanism). -/
theorem dispatchFamily_nearMiss_none :
    dispatchFamily partialStagingRowAware = none := rfl

/-- ★ **Re-seat, near-miss** — the certified dispatch and `admitByRowAware` AGREE on the near-miss too: both refuse
(`none`), so the bridge is total over the `EndgameDemo` consumers, by `rfl`. -/
theorem dispatchFamily_nearMiss_eq_admit :
    dispatchFamily partialStagingRowAware = admitByRowAware partialStagingRowAware := rfl

/-! ## The dispatched decider RUNS (the separating verdict, through the routed family) -/

/-- ★ **The dispatched family's decider SEPARATES.**  The staging dimension routes to `monadRelationFamily`
(`dispatchFamily_staged_isMonad`); that routed family's decider decides the two unit faces `t <| eta` vs `eta |> t`
as `isFalse` — the genuine separating behaviour delivered THROUGH the dispatch.  All four `Decidable`-outcome cases
enumerated (propext-free). -/
def dispatchedFamilySeparatesVerdict : Bool :=
  match monadRelationFamily.decider
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell) with
  | isTrue _ => true
  | isFalse _ => false

/-- ★ The dispatched separating verdict COMPUTES to `false` by `rfl` — the routed monad decider separates the unit
faces. -/
theorem dispatchedFamilySeparatesVerdict_holds : dispatchedFamilySeparatesVerdict = false := rfl

/-! ## Observability -/

-- The staging dimension is dispatched with the deltaMonotone mechanism: expect `some deltaMonotone`.
#eval match dispatchMechanism stagedRowAware with
  | some DecisionMechanism.deltaMonotone => "some deltaMonotone"
  | _ => "OTHER"
-- The near-miss is refused (dispatch returns none): expect `true`.
#eval (dispatchStrategy partialStagingRowAware).isNone
-- The dispatched (routed monad) family decider separates the unit faces: expect `false`.
#eval dispatchedFamilySeparatesVerdict

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the CERTIFIED strategy registry SHIPS with one generic dispatch-soundness theorem
(POLY-TAB r1, P2).**  The certified entry (`CertifiedStrategyEntry`: fingerprint + `DecisionMechanism` tag +
certified decider `entry.certifiedDecider` + admissibility certificate `entry.admissibilityCertificate`), the
registry (`certifiedStrategyRegistry`, mirroring `rowAwareRegistry`, both `deltaMonotone`; `undecidableWall`
definitionally excluded), the dispatch (`dispatchStrategy` / `dispatchFamily` / `dispatchMechanism`), and the ONE
generic soundness theorem (`dispatchStrategy_sound`: dispatch returns an entry ⟹ its exact fingerprint matched,
proved once).  The MODE-ADMIT row-aware registry is RE-SEATED BY BRIDGE: `dispatchFamily = admitByRowAware` on the
`EndgameDemo` staging dimension AND its near-miss (by `rfl`, consumers keep working), the mechanism tag is
preserved (`dispatchMechanism_staged_isDelta`), and the near-miss negative control is REFUSED through the new
dispatch (`dispatchStrategy_refusesNearMiss = none`), with the routed monad decider separating the unit faces
(`dispatchedFamilySeparatesVerdict_holds`).  Additive — `Amalgam/` untouched.  `= true`. -/
def fxTab_hasCertifiedStrategyRegistry : Bool := true

end FX1Poly.Polygraph.Amalgam

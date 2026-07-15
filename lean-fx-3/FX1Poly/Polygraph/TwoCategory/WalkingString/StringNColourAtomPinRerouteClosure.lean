import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericMidPureCupSortDriver
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringQuadrupleDeterminacyKeystone

/-! # WalkingString — the N-COLOUR ATOM-PIN REROUTE census bill CLOSED (FC-4 r7, the closure)

The FC-4 opener census (`StringKParameterizationCensus`) posted the OPEN road marker
`fxString_hasNColourAtomPinReroute := false` with the bill (verbatim):

> "The shipped determinacy brick's atom pin routes through `stringTwoCell_codPack_uniqueOfDom` ('dom
> determines cod'), which is FALSE at `k ≥ 3`: the units `η1` (dom `nil`, cod `L1·L2`) and `η3` (dom `nil`,
> cod `L3·L4`) share dom `nil` but differ in cod, so 'dom determines cod' is refuted.  The re-derivation
> re-routes the shared-cod pin through a cup-restricted COD pin (`stringTwoCell_domPack_uniqueOfCod_forCups`,
> 'among cups, cod word determines the generator', probed true) — that plus the `k = 3` seed and fresh `k = 3`
> sort fixtures is the r2+ determinacy bill; the connectivity spine ports for free."

and the r5/r6 rounds committed the BROADER reading: the bill is the FULL width-`0` quad SORT (the fueled
cup-sort driver + the generic snake-exclusion / LOCATE chain), not merely the pin swap.  This file adjudicates
that bill CLAUSE BY CLAUSE against delivered, kernel-checked vehicles, and closes it by the honest vehicle:
the frozen owner stays byte-intact `:= false` (ADDITIVE-ONLY law — the census file is FROZEN), and THIS file's
content marker `fxString_hasNColourAtomPinRerouteClosed := true` SUPERSEDES it (the same owner-frozen /
content-marker-supersedes vehicle the Omega lane uses).

## The bill, clause by clause

  1. **The cup-restricted COD pin ("among cups, cod word determines the generator")** — DELIVERED: the FC-4 r3
     keystone `stringQuadCupSpineAtom_eq_of_codWordReadOffs` (`StringQuadrupleDeterminacyKeystone`, routed
     through the r2 restricted pin) and its class-generic form `genericStringCupAtom_eq_of_sharedCod_sameWindow`
     (FC-4 r5 B2, a FIELD-derived consequence of `cupCodDeterminesGenerator`).  CONSUMED AT THE EXACT NODE the
     refuted dom→cod pin occupied: the generic fueled sort driver
     (`StringGenericMidPureCupSortDriver`) pins the located back-cup against the peeled last cup by
     `genericStringCupAtom_eq_of_sharedCod_sameWindow` — the shared-cod pin rerouted through COD, at every `k`.
  2. **The `k = 3` seed** — DELIVERED: `adjointQuadrupleModeSignature` (`StringQuadrupleSeed`, FC-4 r2), the
     free 2-computad of `L1 ⊣ L2 ⊣ L3 ⊣ L4` with the census HONESTY-LAW bridge
     (`quadCupCods_eq_carrierAtThree` — the seed IS the `k = 3` instance of the census carrier).
  3. **Fresh `k = 3` sort fixtures** — DELIVERED: the width-`0` distinct-generator two-order pair
     `quadSortOrderA/B` (`{η1, η3}`, equal matchings `[1,0,3,2]`), the mid-`2` distinct pair
     `quadSortMidOrderA/B` over the `L3·L4` survivors (equal matchings `[4,5,3,2,0,1,7,6]`), and the nested
     rainbow `quadNestedRainbow` (`[3,2,1,0]`) — each `by decide`-pinned, each RUN END-TO-END through the sort
     decision (`quadSortDecision_firesAtThreeWidthZero` / `_firesAtThreeMidTwo` /
     `quadSortDecision_runsOnNestedRainbow`).
  4. **The BROADER committed reading — the FULL width-`0` quad SORT** — DELIVERED as the r7 ANY-WIDTH generic
     chain over `AdjointStringConnectivity × midWidth`, each brick fired at `k = 2` AND `k = 3`:
     the arc census / perfect-matching fold + any-width involution
     (`genericMatchingPartner_isInvolution_anyWidth`, `StringGenericArcCensusInvolution`), the snake exclusion
     + fueled LOCATE (`genericMatchingForwardChordsNotAdjacent_mid` / `genericMatchingLocateAuxMid`,
     `StringGenericMidSnakeLocate`), and the fueled SORT DRIVER + determinacy
     (`genericMidPureCupDeterminacy_proof`, `StringGenericMidPureCupSortDriver`) — consuming the r5 B2/B3 and
     r6 readoff/drop tranches.  The width-`0` quad sort is the `midWidth := 0` face of
     `quadPureCupDeterminacyAtThree` below, and it FIRED on the fresh fixtures of clause 3.
  5. **The `k = 2` re-derivation check** — the generic chain recovers the NAMED shipped `k = 2` bricks on
     their LITERAL statements: `stringPositiveMidPureCupDeterminacy_proof` AND
     `stringWidthZeroPureCupDeterminacyShared_proof` (the `shippedInhabitant` / `viaGenericClassAtTwo` pairs,
     `StringGenericMidPureCupSortDriver`), plus the involution / locate recoveries in the sibling tranches —
     the flip demand "at BOTH instances" is discharged at `k = 2` by re-derivation and at `k = 3` by the
     quadruple decision.

## The graveyard stands

Nothing here resurrects the machine-refuted dom-only pin: `quadDomOnlySingletonBlock_refutedAtThree`
(`StringQuadrupleSingletonBlockCoChain`) is untouched, and the whole delivered chain consumes only the
`(dom, cod)`-pair-disciplined class fields (`cupCodDeterminesGenerator` / `generatorFullArity`).

## What this closure does NOT claim (honest residual, named)

The `k = 3` CONV-level word-problem decision (`decidableStringSaturatedConv`-at-three) — the analogue of the
`k = 2` `decidableStringSaturatedConv_holds` — additionally needs the CAP-side dual sort tower + the valley
cell reducer + the completeness masters at `k = 3` (the `_ofBrick` tower generic).  That is NOT part of this
census bill (whose clauses are 1–3 above, under the committed broader reading 4); it is the named successor
content for the ADJPOLY lane (`#2211`).

ADDITIVE ONLY: the frozen census owner is byte-intact; no shipped file is touched.  Raw Lean 4 + Init;
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin plus an INDEPENDENT `#print axioms` witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The two named instances of the any-width determinacy — the flip's "BOTH instances" -/

/-- ★ **The `k = 2` (walking adjoint-triple) any-width pure-cup determinacy, NAMED.**  The generic driver at
`adjointStringConnectivityAtTwo`: one statement covering the shipped width-`0` AND positive-mid `k = 2` bricks
(both recovered on their literal statements in `StringGenericMidPureCupSortDriver`). -/
theorem stringPureCupDeterminacyAtTwo :
    GenericMidPureCupDeterminacy adjointStringConnectivityAtTwo :=
  genericMidPureCupDeterminacy_proof adjointStringConnectivityAtTwo

/-- ★★ **THE QUADRUPLE DECISION — the `k = 3` (walking adjoint-quadruple) any-width pure-cup determinacy,
NAMED.**  The generic driver at `adjointStringConnectivityAtThree`: two boundary-chained, word-chained
pure-cup spines over ANY `midWidth` with shared top word and EQUAL boundary matching are `SpineTraceEquiv` —
at the six-generator adjoint-quadruple signature with the fresh letter `L4`.  Its `midWidth := 0` face is the
census bill's "full width-`0` quad sort"; fired on the fresh `k = 3` fixtures
(`quadSortDecision_firesAtThreeWidthZero` / `_firesAtThreeMidTwo`). -/
theorem quadPureCupDeterminacyAtThree :
    GenericMidPureCupDeterminacy adjointStringConnectivityAtThree :=
  genericMidPureCupDeterminacy_proof adjointStringConnectivityAtThree

/-! ## The superseding content marker -/

/-- **★★ CLOSED — the N-COLOUR ATOM-PIN REROUTE census bill is DISCHARGED; this content marker SUPERSEDES the
frozen owner `fxString_hasNColourAtomPinReroute := false` (`StringKParameterizationCensus`, byte-intact per
the ADDITIVE-ONLY law).**  Every clause of the owner's verbatim bill is delivered kernel-checked, zero-axiom:

  1. the cup-restricted COD pin ("among cups, cod word determines the generator") — the r3 keystone
     `stringQuadCupSpineAtom_eq_of_codWordReadOffs` + the r5 B2 class-generic
     `genericStringCupAtom_eq_of_sharedCod_sameWindow`, consumed by the generic fueled sort driver at the
     exact node the `k ≥ 3`-refuted `stringTwoCell_codPack_uniqueOfDom` occupied;
  2. the `k = 3` seed — `adjointQuadrupleModeSignature` with the census carrier bridge;
  3. fresh `k = 3` sort fixtures, RUN end-to-end — `quadSortOrderA/B` (width-`0`, matchings `[1,0,3,2]`),
     `quadSortMidOrderA/B` (mid-`2`, matchings `[4,5,3,2,0,1,7,6]`), `quadNestedRainbow` (`[3,2,1,0]`), fired
     through `quadPureCupDeterminacyAtThree` (`quadSortDecision_firesAtThreeWidthZero` / `_firesAtThreeMidTwo`
     / `quadSortDecision_runsOnNestedRainbow`), with window-projection + generator-identity negative controls;
  4. the broader committed reading (the FULL width-`0` quad SORT = the generic snake-exclusion via the
     positive involution / arc census tower + the fueled LOCATE + the fueled SORT DRIVER) — the r7 ANY-WIDTH
     chain `genericMatchingPartner_isInvolution_anyWidth` → `genericMatchingForwardChordsNotAdjacent_mid` →
     `genericMatchingLocateAuxMid` → `genericMidPureCupDeterminacy_proof`, ONE fueled fold over
     `AdjointStringConnectivity × midWidth` (never a per-cup-count rebuild), subsuming BOTH shipped `k = 2`
     drivers;
  5. the `k = 2` re-derivation — the generic chain inhabits the LITERAL shipped statements
     `StringPositiveMidPureCupDeterminacy` and `StringWidthZeroPureCupDeterminacyShared` at
     `adjointStringConnectivityAtTwo` (defeq signature), alongside the involution / locate recoveries.

  The graveyard stands (no dom-only pin resurrected; the chain consumes only the `(dom, cod)`-pair fields).
  The honest residual is NAMED, not hidden: the `k = 3` CONV-level decision (cap-side dual tower + valley
  reducer + completeness masters at `k = 3`) is the ADJPOLY (`#2211`) successor content, outside this bill.
  `= true`. -/
def fxString_hasNColourAtomPinRerouteClosed : Bool := true

end FX1Poly.Polygraph

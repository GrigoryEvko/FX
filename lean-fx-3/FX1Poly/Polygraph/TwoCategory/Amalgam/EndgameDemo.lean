import FX1Poly.Polygraph.TwoCategory.Amalgam.ModeAdmit
import FX1Poly.Polygraph.TwoCategory.WalkingInvolution.InvolutionDecision

/-! # Polygraph/TwoCategory/Amalgam/EndgameDemo — the Tier-A capstone (ENDGAME-DEMO r1, #2215)

This file is the CONSUMER-FACING capstone of the MODE-ADMIT stack.  Everything below it (`SaturatedRelationFamily`,
`ModeAdmit`, the three registered walkers) is the machine; this file shows the machine SERVING a freshly-declared
FX dimension.  A new dimension DECLARES its own presentation (fresh Lean names, real row-aware fingerprint data),
the admission gate MATCHES it from that data, and a decided 2-cell conversion comes back with ZERO new proof
bodies at this layer.  Nothing here proves a theorem the substrate did not already prove — every payoff is `rfl`
over the shipped machine.

## What the literature asks, and what this discharges

Gratzer's normalization for MTT (LICS'22, arXiv 2301.11842) reduces the decidability of an ENTIRE modal type
theory to a single obligation: "conversion in MTT is decidable when equality of modalities and 2-cells is
decidable", an obligation it calls "potentially nontrivial, e.g., the word problem for groups is known to be
undecidable", and then leaves to each instantiation to discharge by hand.  Licata-Shulman-Riley (FSCD'17) show the
standard mode-theoretic dimensions one wants to instantiate are exactly session-duality (an involution), linear /
affine, and (co)monad / staging.  The proof-assistant precedent (Coq `Decidable`, family-polymorphic metatheory)
delivers "decidability for free" only at the typeclass / term level, never at the mode-theory 2-cell level and
never as a data-recognition gate.  What ships here is that missing machine: a kernel-checked admission gate that
delivers mode-theory 2-cell decidability by DATA RECOGNITION, per dimension, with no new proof bodies.

## The two demo dimensions (both routed through the ONE shipped gate)

  * **demo-1 (dim-6 Protocol / session duality).**  A fresh dimension whose modality is `dual : P -> P` with
    `dual(dual(S)) = S` -- the session-type duality involution (Thiemann-Vasconcelos POPL'20: "duality is an
    involution on session types"; Gay-Thiemann-Vasconcelos EPTCS 314; nLab duality-involution; fx_design.md
    §11.2, Wadler dual-dual = identity).  Its presentation `protocolDualityComputad` is data-distinct in name but
    structurally the walking-involution computad (one object, one endo-generator, no generating 2-cells -- thin).
    Routed through the THIN gate `admitModeTheory`, which recognises it as a renaming of the registered involution
    and hands back a decider over the dimension's OWN signature (thin transport is sound natively).  Verdict at the
    2-cell level: total `isTrue` (a thin mode theory has no separating 2-cells).  The dimension's GENUINE
    separation lives one level down as the 1-cell parity fact `dual` is not `id` (odd vs even number of duals),
    exhibited by the sibling decider `decideInvolutionOneCellConv` -- stated honestly, not smuggled into the 2-cell
    tier.

  * **demo-2 (dim-17 Staged computation, `code(T)`).**  A fresh dimension whose modality is the quotation
    `code : T -> code(T)` of multi-stage metaprogramming (fx_design.md §17.2): `quote : id => code` is the monad
    unit, `splice : code . code => code` the multiplication, and unit + associativity the staging coherence laws
    -- a monad-shaped mode theory (LSR'17 catalogue "(co)monads and adjunctions").  Its presentation
    `stagedComputationComputad` + `stagedComputationLawRows` is data-distinct in name but structurally the walking
    monad's computad and its three law rows.  Routed through the ROW-AWARE gate `admitByRowAware`, which recognises
    it from the reflected law data and routes it to the SEPARATING `monadRelationFamily` -- NOT the walking
    IDEMPOTENT monad that shares its plain fingerprint.  The recognised family's decider exhibits BOTH verdicts:
    `isTrue` on associativity AND `isFalse` on the two unit faces `code <| quote` vs `quote |> code`.

## The precise tier this is verified at (the honesty crux -- read before citing)

The verified reality is RECOGNITION + REGISTERED-DECIDER, with cell-transport walled:

  * The gate MATCHES a data-distinct presentation and RETURNS the registered family (`admitByRowAware
    stagedRowAware = some monadRelationFamily`, by `rfl` -- the fresh data reduces to the same match verdict).
  * The family decider then decides the REGISTERED walker's conversion (over the bespoke `monadModeSignature`).
    Transporting that decision onto the new dimension's OWN freshly-named cells is the decider-REUSE leg that stays
    walled: `fxModeAdmit_hasRenamingDeciderTransport = false`, because no `ComputadMorphismTwo` exists into the
    bespoke `monadModeSignature` (`ModeAdmit.lean` P2).  So "a new dimension inherits a decided 2-cell conversion"
    means DATA-RECOGNITION routed to the registered decider, not cell-level transport of the decision.

  * demo-1 is the one exception whose decision runs on the dimension's OWN carrier -- but only because thinness is
    a STRUCTURAL property the renaming preserves, so the thin decider needs no transport.  Its 2-cell verdict is
    therefore total `isTrue`; the `isFalse` separation is the sibling 1-cell decider, at a DIFFERENT (seed)
    presentation, cited as such.

This is exactly the shape `ModeAdmit.lean` reached at r2 (`fxModeAdmit_hasRowAwareRecognizedSeparation = true`)
and the D4 audit below is LITERAL: every payoff at this layer is a `:= rfl` over the shipped machine; there are
NO tactic proof bodies at all -- the only `by decide` tokens are Fin / scope bounds inside DATA definitions, and
no declaration opens a tactic proof block.

## The #2045 / decide-21 architecture note

What EXISTS: the composable-fragment dispatch (`ComposableFragmentDispatch` / `SaturatedRelationFamily`) plus this
admission gate -- a per-dimension machine that discharges MTT's 2-cell-decidability obligation for the registered
doctrines (thin / idempotent / monad) and hands the decision to a freshly-declared dimension by data recognition.
What REMAINS for a fully-automatic, sound, data-keyed admission of an ARBITRARY presented dimension (the
`fxModeAdmit_hasCertifiedDataAdmission = false` scope): (1) certify the reflected law rows FAITHFUL to the Prop law
relation; (2) the bespoke-vs-reconstructed reseat's backward isTrue leg (`MonadReseat.lean`, cast labor, not a
wall); (3) Tietze-closure matching beyond bijective renaming.  This capstone ships the recognition tier and names
those three residuals precisely.

Raw Lean 4 + Init.  Structural, ASCII-only, additive.  Per-declaration `#assert_no_axioms` + independent
`#print axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## D1 -- the two demo-dimension presentations (fresh-named data)

Each presentation below is a genuinely new `def` with its own name and dimension story; its underlying `Nat` data
coincides with a registered walker's, so the name-blind fingerprint (the substrate stores no display name on
`ModeComputad` -- only `Nat` / `Fin` indices) recognises it.  The fresh Lean identifiers and docstrings are
invisible to the data key; that is the whole point. -/

/-- ★ **demo-1 dimension -- dim-6 Protocol / session duality.**  The presentation of a fresh FX dimension whose
single object is the protocol object `P` and whose single endo-modality is session-type DUALITY `dual : P -> P`,
subject to the involution law `dual(dual(S)) = S` (Thiemann-Vasconcelos POPL'20, "duality is an involution on
session types"; fx_design.md §11.2).  Structurally the walking-involution computad: one mode, one endo-1-generator,
NO generating 2-cells (the `dual . dual = id` law is 1-cell-level, so the 2-generator list is empty -- thin).
Fresh name; identical `Nat` data to `involutionComputad`. -/
def protocolDualityComputad : ModeComputad where
  modeCount := 1
  modalityGenerators := [(⟨0, by decide⟩, ⟨0, by decide⟩)]
  twoCellGenerators := []

/-- The `code(-)` modality's 1-cell word -- the single staging endo-generator, index `0`. -/
def stagedCodeWord : List Nat := [0]

/-- The reflected staging UNIT `quote : id => code` -- the 2-generator at index `0` (the monad unit `eta`). -/
def reflectedQuote : RawCellData := RawCellData.genAtom 0

/-- The reflected staging MULTIPLICATION `splice : code . code => code` -- the 2-generator at index `1` (the monad
multiplication `mu`). -/
def reflectedSplice : RawCellData := RawCellData.genAtom 1

/-- The reflected identity 2-cell on `code` (the RHS of both staging unit laws). -/
def reflectedIdCode : RawCellData := RawCellData.idCell stagedCodeWord

/-- ★ **demo-2 dimension -- dim-17 Staged computation `code(T)`.**  The presentation of a fresh FX dimension whose
single object is the value stage and whose single endo-modality is the quotation `code : T -> code(T)` of
multi-stage metaprogramming (fx_design.md §17.2).  Two generating 2-cells: `quote : id => code` (the unit) and
`splice : code . code => code` (the flatten / multiplication).  Structurally the walking-monad computad: one mode,
one endo-1-generator, two 2-generators with boundary words `[] => [code]` and `[code, code] => [code]`.  Fresh
name; identical `Nat` data to `monadComputad`. -/
def stagedComputationComputad : ModeComputad where
  modeCount := 1
  modalityGenerators := [(⟨0, by decide⟩, ⟨0, by decide⟩)]
  twoCellGenerators :=
    [ { src := ⟨0, by decide⟩, tgt := ⟨0, by decide⟩, lhs := [], rhs := [⟨0, by decide⟩] },
      { src := ⟨0, by decide⟩, tgt := ⟨0, by decide⟩,
        lhs := [⟨0, by decide⟩, ⟨0, by decide⟩], rhs := [⟨0, by decide⟩] } ]

/-- ★ **The staging coherence laws, reflected as data.**  Left unit `splice . (quote |> code) ~ id_code`, right
unit `splice . (code <| quote) ~ id_code`, associativity `splice . (splice |> code) ~ splice . (code <| splice)`.
Structurally identical `Nat` data to `monadLawRowsData` -- three rows -- but named for the staging story.  This is
the row-aware key the gate reads. -/
def stagedComputationLawRows : List (RawCellData × RawCellData) :=
  [ (RawCellData.vcomp (RawCellData.whiskerRight stagedCodeWord reflectedQuote) reflectedSplice, reflectedIdCode),
    (RawCellData.vcomp (RawCellData.whiskerLeft stagedCodeWord reflectedQuote) reflectedSplice, reflectedIdCode),
    (RawCellData.vcomp (RawCellData.whiskerRight stagedCodeWord reflectedSplice) reflectedSplice,
      RawCellData.vcomp (RawCellData.whiskerLeft stagedCodeWord reflectedSplice) reflectedSplice) ]

/-- The demo-2 dimension's row-aware fingerprint -- the plain base (mode count + generators) PLUS the reflected
staging coherence rows. -/
def stagedRowAware : RowAwarePresentationData :=
  stagedComputationComputad.toRowAwarePresentationData stagedComputationLawRows

/-- ★ **The NEGATIVE-CONTROL dimension -- a "partial staging" doctrine MISSING the associativity coherence.**  The
two unit rows only (no associativity), representing a dimension whose declared laws match NO registered doctrine
(neither the three-row monad nor the four-row idempotent monad).  A genuinely-different, unregistered law set: the
gate must REFUSE it. -/
def partialStagingLawRows : List (RawCellData × RawCellData) :=
  [ (RawCellData.vcomp (RawCellData.whiskerRight stagedCodeWord reflectedQuote) reflectedSplice, reflectedIdCode),
    (RawCellData.vcomp (RawCellData.whiskerLeft stagedCodeWord reflectedQuote) reflectedSplice, reflectedIdCode) ]

/-- The negative control's row-aware fingerprint -- same base as `stagedRowAware`, but the truncated (unregistered)
law rows. -/
def partialStagingRowAware : RowAwarePresentationData :=
  stagedComputationComputad.toRowAwarePresentationData partialStagingLawRows

/-! ## D2 -- the gate runs: recognition from DATA + a negative control

The gate reads only the fingerprint data (name-blind), so a fresh dimension whose data coincides with a registered
walker's is recognised; a fresh dimension whose data does not is rejected. -/

/-- ★ **demo-1 recognition.**  The registry recognises the protocol-duality presentation as a renaming of a
registered THIN walker (the walking involution) -- from data alone, the fresh name invisible. -/
theorem demoProtocol_recognizedByRegistry :
    isRegisteredThinRenaming protocolDualityComputad.toPresentationData = true := rfl

/-- ★ **demo-2 recognition.**  The row-aware matcher recognises the staging presentation as the walking monad's
row-aware fingerprint -- the reflected law rows agree despite the fresh names. -/
theorem demoStaging_matchesMonadData :
    isRowAwarePresentationMatch stagedRowAware monadRowAware = true := rfl

/-- ★ **demo-2 discrimination.**  The SAME staging presentation is NOT confused with the walking idempotent monad:
they share a plain fingerprint (same computad) but the reflected law rows differ (3 vs 4), so the row-aware matcher
separates them -- the precise conflation the plain data key could not resolve. -/
theorem demoStaging_distinctFromIdempotent :
    isRowAwarePresentationMatch stagedRowAware idempotentRowAware = false := rfl

/-- ★★ **NEGATIVE CONTROL.**  The partial-staging dimension (a near-miss: monad computad but only the two unit
laws) is REJECTED by the gate -- `admitByRowAware` returns `none` because the truncated law rows match neither the
three-row monad nor the four-row idempotent monad.  The row data is genuinely load-bearing: the gate is not fooled
by a doctrine missing a coherence law. -/
theorem demoUnregistered_rejected :
    (admitByRowAware partialStagingRowAware).isSome = false := rfl

/-! ## D3 -- the decisions through the registry families

demo-1 routes through the THIN gate onto its OWN carrier (thin transport sound); its 2-cell verdict is total
`isTrue`, and its genuine separation is the sibling 1-cell parity decider.  demo-2 routes through the ROW-AWARE
gate onto the REGISTERED monad carrier; its decider exhibits BOTH verdicts. -/

/-- ★ **demo-1 admission.**  The gate ADMITS the protocol-duality dimension: `admitModeTheory` returns `some
decider` -- a decision over the dimension's OWN signature (thin transport is native). -/
theorem demoProtocol_admitted :
    (admitModeTheory protocolDualityComputad).isSome = true := rfl

/-- The identity 2-cell on the empty 1-cell at the protocol object -- a genuine cell over the dimension's OWN
signature. -/
def protocolDualityNilCellA :
    RawTwoCellExpr protocolDualityComputad.toModeSignature
      (ModalityPath.nil (graph := protocolDualityComputad.toModeSignature.graph) ⟨0, by decide⟩)
      (ModalityPath.nil (graph := protocolDualityComputad.toModeSignature.graph) ⟨0, by decide⟩) :=
  RawTwoCellExpr.id (ModalityPath.nil (graph := protocolDualityComputad.toModeSignature.graph) ⟨0, by decide⟩)

/-- A SYNTACTICALLY DISTINCT parallel cell -- the vertical composite of two identities on the same empty 1-cell.
Parallel to `protocolDualityNilCellA` (same boundary), a different expression, so the thin decision is non-vacuous. -/
def protocolDualityNilCellB :
    RawTwoCellExpr protocolDualityComputad.toModeSignature
      (ModalityPath.nil (graph := protocolDualityComputad.toModeSignature.graph) ⟨0, by decide⟩)
      (ModalityPath.nil (graph := protocolDualityComputad.toModeSignature.graph) ⟨0, by decide⟩) :=
  RawTwoCellExpr.vcomp
    (RawTwoCellExpr.id (ModalityPath.nil (graph := protocolDualityComputad.toModeSignature.graph) ⟨0, by decide⟩))
    (RawTwoCellExpr.id (ModalityPath.nil (graph := protocolDualityComputad.toModeSignature.graph) ⟨0, by decide⟩))

/-- ★ **demo-1 thin verdict (through the gate).**  Feed the protocol-duality dimension to the gate; it is
recognised, admitted, and its returned decider decides the distinct parallel pair `id` vs `id . id` as `isTrue`
(thin: every parallel 2-cell pair is convertible).  `false` here would mean NOT admitted or decided `isFalse`. -/
def demoProtocolThinVerdict : Bool :=
  match admitModeTheory protocolDualityComputad with
  | none => false
  | some decider =>
      match decider protocolDualityNilCellA protocolDualityNilCellB with
      | isTrue _ => true
      | isFalse _ => false

/-- ★ demo-1 thin verdict COMPUTES to `true` -- recognition, admission, and the thin decision all reduce. -/
theorem demoProtocolThinVerdict_holds : demoProtocolThinVerdict = true := rfl

/-- ★ **demo-1 GENUINE separation (the honest, sibling-level fact).**  The 2-cell tier is total `isTrue` (thin), so
the dimension's real content -- that `dual` is NOT the identity protocol transform -- lives at the 1-CELL parity
level: an odd number of `dual`s is separated from an even number.  The sibling decider `decideInvolutionOneCellConv`
decides a single `dual` (`involutionS`) against the identity (`involutionNil`) as `isFalse`.  This is the
machine-checked `dual(dual(S)) = S` but `dual(S)` is not `S` (fx_design.md §11.2 / Wadler).  HONEST: this decider
lives over the involution SEED presentation, a DIFFERENT presentation from `protocolDualityComputad`, cited as a
sibling fact -- it is not transported onto the demo dimension's 2-cells. -/
theorem demoProtocolDualSeparates :
    decide (InvolutionOneCellConv involutionS involutionNil) = false := rfl

/-- ★★ **demo-2 admission + routing (from DATA, to the SEPARATING family).**  `admitByRowAware stagedRowAware`
returns EXACTLY `monadRelationFamily` by `rfl`: the reflected staging law rows route the fresh dimension to the
walking-monad family (the member that separates), NOT to the total idempotent monad that shares its plain
fingerprint.  This ONE `rfl` is the whole Tier-A bridge -- recognition of data-distinct presentation, retrieval of
the registered decided family. -/
theorem demoStaging_admitsMonad :
    admitByRowAware stagedRowAware = some monadRelationFamily := rfl

/-- ★★ **demo-2 BOTH verdicts (through the recognised family).**  The family the gate returns for the staging data
(`monadRelationFamily`, certified by `demoStaging_admitsMonad`) decides the associativity foldings as `isTrue`
(convertible) AND the two staging unit faces `code <| quote` (`whiskerRight`) vs `quote |> code` (`whiskerLeft`) as
`isFalse` (distinct monotone maps `[1]` vs `[0]`).  `true` requires the FIRST `isTrue` and the SECOND `isFalse` --
the genuine separating behaviour, inherited by data recognition.  All 2x2 `Decidable` outcomes enumerated (no
wildcard) to stay propext-free.  HONEST: the decider runs on the REGISTERED monad carrier (`monadModeSignature`);
transport onto the staging dimension's OWN cells is walled (`fxModeAdmit_hasRenamingDeciderTransport = false`). -/
def demoStagingBothVerdicts : Bool :=
  match monadRelationFamily.decider monadAssocLeftCell monadAssocRightCell,
        monadRelationFamily.decider
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
          (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell) with
  | isTrue _, isTrue _ => false
  | isTrue _, isFalse _ => true
  | isFalse _, isTrue _ => false
  | isFalse _, isFalse _ => false

/-- ★ demo-2 both-verdicts run COMPUTES to `true` -- associativity `isTrue`, staging unit faces `isFalse`, both
from the row-aware-recognised monad family. -/
theorem demoStagingBothVerdicts_holds : demoStagingBothVerdicts = true := rfl

/-! ## Observability -- one `#eval` mirroring each payoff -/

-- demo-1: the registry recognises the protocol-duality dimension: expect `true`.
#eval isRegisteredThinRenaming protocolDualityComputad.toPresentationData
-- demo-1: the gate admits it (returns `some`): expect `true`.
#eval (admitModeTheory protocolDualityComputad).isSome
-- demo-1: the thin decision on a real parallel pair: expect `true`.
#eval demoProtocolThinVerdict
-- demo-1: the sibling 1-cell parity separation `dual` vs `id`: expect `false`.
#eval decide (InvolutionOneCellConv involutionS involutionNil)
-- demo-2: the row-aware matcher recognises the staging data as the monad: expect `true`.
#eval isRowAwarePresentationMatch stagedRowAware monadRowAware
-- demo-2: the staging data is NOT confused with the idempotent monad: expect `false`.
#eval isRowAwarePresentationMatch stagedRowAware idempotentRowAware
-- demo-2: row-aware admission routes the staging data to a family: expect `true`.
#eval (admitByRowAware stagedRowAware).isSome
-- demo-2 NEGATIVE CONTROL: the partial-staging near-miss is rejected: expect `false`.
#eval (admitByRowAware partialStagingRowAware).isSome
-- demo-2: the recognised monad family decides assoc isTrue AND unit faces isFalse: expect `true`.
#eval demoStagingBothVerdicts

/-! ## D5 -- the Tier-A capstone marker -/

/-- ★★ **Honesty marker -- the Tier-A mode-theory admission DEMO SHIPS (ENDGAME-DEMO r1, #2215).**

Two freshly-declared FX dimensions -- dim-6 session-duality (`protocolDualityComputad`) and dim-17 staged
computation (`stagedComputationComputad` + `stagedComputationLawRows`) -- each with its own Lean names and
dimension story, are RECOGNISED from their fingerprint DATA by the ONE shipped admission gate and handed a decided
2-cell conversion with ZERO new proof bodies at this layer:

  * demo-1 through the THIN gate `admitModeTheory`: recognised (`demoProtocol_recognizedByRegistry`), admitted
    (`demoProtocol_admitted`), decided total `isTrue` on its OWN carrier (`demoProtocolThinVerdict_holds`).  Its
    genuine separation is the sibling 1-cell parity fact `dual` is not `id` (`demoProtocolDualSeparates`,
    `isFalse`), stated honestly at the seed presentation.

  * demo-2 through the ROW-AWARE gate `admitByRowAware`: recognised from law-row data
    (`demoStaging_matchesMonadData`), distinguished from the idempotent monad (`demoStaging_distinctFromIdempotent`),
    routed to the SEPARATING `monadRelationFamily` (`demoStaging_admitsMonad`, by `rfl`), whose decider exhibits
    BOTH verdicts -- associativity `isTrue` and staging unit faces `isFalse` (`demoStagingBothVerdicts_holds`).  A
    near-miss (partial-staging, associativity dropped) is REJECTED (`demoUnregistered_rejected`).

THE VERIFIED TIER (precise): RECOGNITION + REGISTERED-DECIDER.  The gate matches data-distinct presentations and
returns the registered family; the family decider decides the REGISTERED walker's conversion.  Transport of that
decision onto the new dimension's OWN freshly-named cells is WALLED
(`fxModeAdmit_hasRenamingDeciderTransport = false`: no `ComputadMorphismTwo` into the bespoke `monadModeSignature`;
demo-1's own-carrier decision is the sound exception, thinness being renaming-stable).  Fully-automatic sound
data-keyed admission of an ARBITRARY dimension (`fxModeAdmit_hasCertifiedDataAdmission = false`) additionally needs
(1) certified reflection faithfulness, (2) the reseat backward isTrue leg (cast labor, `MonadReseat.lean`), (3)
Tietze-closure matching -- the three named residuals.

D4 (zero new proofs at the demo layer) is LITERAL: the nine payoff theorems above are each `:= rfl`; there are NO
tactic proof bodies anywhere -- the only `by decide` tokens are Fin / scope bounds inside DATA definitions, and no
declaration opens a tactic proof block.  The decision content lives entirely in the shipped MODE-ADMIT machine.
`= true`. -/
def fxEndgame_hasTierADemo : Bool := true

end FX1Poly.Polygraph.Amalgam

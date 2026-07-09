import FX1Poly.Polygraph.TwoCategory.Amalgam.Pushout
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Model

/-! # Polygraph/TwoCategory/Amalgam/Dispatch — the categorical Nelson-Oppen dispatch STATEMENT (AMALG-2 target)

The payoff of the amalgam layer at scale: given DECIDED word problems for two component doctrines (each shipped
as a `DecidableTwoCellConvFor` — the §3.13 decidable-2-cell-equality interface, `FreeTwoCell/Model.lean`) over
DISJOINT generators sharing the mode set, the combined 2-cell convertibility of the pushout `comp1 +_M comp2`
is decidable.  This is the categorical analogue of the DISJOINT-SIGNATURE word-problem combination.

## This file ships the STATEMENT, not the proof

`DispatchDecidability` is the AMALG-2 TARGET — a structure recording exactly the Nelson-Oppen-style hypotheses
(two component deciders + the disjoint-generator condition) and the conclusion (a combined decider).  It is
STATED here; inhabiting the arrow `(dec1, dec2, disjoint) → combined` is the WP-AMALG-2 work
(`fxAmalg_hasDispatchTheorem = false`).  What ships alongside is the disjointness PREDICATE
(`computadGeneratorsDisjoint`, a computable `Bool`) that the pushout satisfies by construction (witnessed
concretely in `Witness.lean`).

## The interface analysis (why this is the RIGHT set of hypotheses)

Governing prior art: NOT the stably-infinite Nelson-Oppen SATISFIABILITY combination, but the DISJOINT-SIGNATURE
WORD-PROBLEM combination — first proved by Pigozzi (1974), re-derived by Baader-Tinelli ("Deciding the Word
Problem in the Union of Equational Theories", 1998).  Their SHARP caveat: combining across a SHARED function
symbol is undecidable in general (associativity + ground equations encodes an arbitrary finitely-presented
semigroup with undecidable word problem), which is precisely why the DISJOINT-generator condition
(`computadGeneratorsDisjoint`) is load-bearing — no combined relation may mention both components' generators.
The categorical framing is the pushout of PROPs via a distributive law (Zanasi, Prop. 2.30), with the
amalgamation property (automatic for disjoint generators over a shared mode set) replacing stable-infiniteness
(Ghilardi 2004).  At the mode-theory level the nearest published kin is MTT's monolithic transfer ("conversion
in MTT is decidable when equality of modalities and 2-cells is decidable", Gratzer et al.) — but no published
MODULAR (across-a-pushout) decidability-transfer theorem exists, so AMALG-2 is genuinely new territory.

## The expected proof shape (the componentComm hook)

Cross-component 2-cell interaction is EXACTLY the Godement interchange of DISJOINT-SUPPORT cells: since
different-component generators never co-occur in a relation, the only cross-terms are `hcomp` / whisker
exchanges of a component-1 cell past a component-2 cell.  That is precisely what the keystone
`matchingGodementInvariant_of_componentCommute` (+ `GodementIndependence`, the union-find join-order
independence of two horizontally-disjoint blocks, `FreeTwoCell/MatchingComponentGodement.lean`) discharges.
Expected proof: block-decompose each parallel cell along the 1-cell interleaving NF (`InterleavingNF.lean`),
dispatch each same-component block to its component decider, then interchange-normalise to a block-sorted form
via `componentComm` and compare.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

/-! ## The disjoint-generator condition -/

/-- Every letter of a word is in component 1 (`.val < splitPoint`) — recursive Bool, propext-free. -/
def wordBelow (splitPoint : Nat) {bound : Nat} : List (Fin bound) → Bool
  | [] => true
  | letter :: rest => Nat.blt letter.val splitPoint && wordBelow splitPoint rest

/-- Every letter of a word is in component 2 (`.val ≥ splitPoint`) — recursive Bool, propext-free. -/
def wordAtOrAbove (splitPoint : Nat) {bound : Nat} : List (Fin bound) → Bool
  | [] => true
  | letter :: rest => Nat.ble splitPoint letter.val && wordAtOrAbove splitPoint rest

/-- A 2-generator is **component-pure** — both its parallel words lie ENTIRELY in one component's letter range
(so the relation mentions only one component's generators). -/
def generatorIsComponentPure {modeCount : Nat} {generators : List (Fin modeCount × Fin modeCount)}
    (splitPoint : Nat) (generator : ComputadTwoGen modeCount generators) : Bool :=
  (wordBelow splitPoint generator.lhs && wordBelow splitPoint generator.rhs)
    || (wordAtOrAbove splitPoint generator.lhs && wordAtOrAbove splitPoint generator.rhs)

/-- ★ The **disjoint-generator condition** — every 2-generator of a computad is component-pure at `splitPoint`
(no relation mentions both components' generators).  Computable (`Bool`), so it decides on concrete pushouts. -/
def computadGeneratorsDisjoint (splitPoint : Nat) (computad : ModeComputad) : Bool :=
  computad.twoCellGenerators.all (generatorIsComponentPure splitPoint)

/-! ## The dispatch statement -/

/-- ★ **The categorical Nelson-Oppen dispatch statement (AMALG-2 target).**  Records the disjoint-signature
word-problem combination as a structure: two component deciders (the `DecidableTwoCellConvFor` §3.13
interfaces), the disjoint-generator condition, and the CONCLUSION — a decider for the pushout's combined 2-cell
convertibility.  STATED; the arrow producing `combinedDecider` from the hypotheses is WP-AMALG-2
(`fxAmalg_hasDispatchTheorem = false`).  The disjointness hypothesis is `computadGeneratorsDisjoint` at the
component-1 boundary `comp1.modalityGenerators.length`. -/
structure DispatchDecidability (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount) where
  /-- Component 1's word problem is decided (the DECIDED walker's `DecidableTwoCellConvFor`). -/
  componentOneDecider : DecidableTwoCellConvFor comp1.toModeSignature
  /-- Component 2's word problem is decided. -/
  componentTwoDecider : DecidableTwoCellConvFor comp2.toModeSignature
  /-- The disjoint-generator condition — the load-bearing hypothesis (shared symbols would be undecidable, per
  Baader-Tinelli). -/
  generatorsDisjoint :
    computadGeneratorsDisjoint comp1.modalityGenerators.length (pushoutShared comp1 comp2 sameModes) = true
  /-- The CONCLUSION — a decider for the pushout's combined 2-cell convertibility. -/
  combinedDecider : DecidableTwoCellConvFor (pushoutShared comp1 comp2 sameModes).toModeSignature

/-! ## Honesty marker -/

/-- **Honesty marker.**  The DISPATCH THEOREM — the arrow `(componentOneDecider, componentTwoDecider,
generatorsDisjoint) → combinedDecider` inhabiting `DispatchDecidability` for every pair of DECIDED disjoint
components — is WP-AMALG-2.  Its expected proof (block-wise dispatch over the interleaving NF + `componentComm`
interchange normalisation) is documented above; the arrow is NOT built here.  Nearest published kin: the
Pigozzi / Baader-Tinelli disjoint word-problem combination (equational) and MTT's monolithic (non-modular)
decidability transfer.  `= false`. -/
def fxAmalg_hasDispatchTheorem : Bool := false

end FX1Poly.Polygraph.Amalgam

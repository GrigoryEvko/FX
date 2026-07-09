import FX1Poly.Polygraph.TwoCategory.Amalgam.RealCoprojection
import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchSaturated
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordProblem

/-! # Polygraph/TwoCategory/Amalgam/DeciderReseat — the reconstruction bridge (P3, jam) and the discriminating
cross-component separation witness (P4) (WP-AMALG r6)

`RealCoprojection.lean` (r6 P2) shipped the genuine-generator right coprojection `inclusionRightTwoReal`, so the
pushout `involution +_M monad` now has a REAL 2-generator coprojection.  This file addresses the two remaining r6
targets.

## P3 — the reconstruction bridge (the machine-documented JAM, plus the easy graph half)

The only shipped REAL saturated decider, `monadSaturatedTwoCellDecision`, lives over the BESPOKE
`monadModeSignature` (carrier `MonadMode` / `MonadModality` / `MonadTwoCell`); the pushout's component-2 signature
is the RECONSTRUCTED `monadComputad.toModeSignature` (carrier `Fin 1` / an endpoint-matched `Fin`-subtype /
`ReconstructedTwoCell`).  These are DISTINCT carrier Types, so `Decidable (SaturatedConvOver
monadComputad.toModeSignature …)` cannot be `= monadSaturatedTwoCellDecision` literally — it requires a
signature-equivalence transport, exactly the `adjunctionComputad.toModeSignature ≠ adjunctionModeSignature`
situation the codebase already flags as impossible to state as `=`.  The 0/1-skeleton half of that equivalence IS
provable (`monadComputadGraphEquiv`, mirroring `adjunctionComputadGraphEquiv`); the 2-cell-inclusive half plus the
bidirectional `Decidable` transport is the fib-3-coupled multi-brick (`fxMode_hasDecidableTwoCellEquality`),
machine-documented below as INT-SIG-ALIGN data with the exact field discrepancy.

## P4 — the discriminating cross-component separation witness

The pushout monad unit `pushoutMonadUnit` (a REAL reconstructed 2-generator, index `0`) gives two pushout monad
FACES `t ⇒ t·t`: `pushoutFaceDeltaOne = whiskerRight t eta` (Δ-monotone map `[1]`) and `pushoutFaceDeltaZero =
whiskerLeft t eta` (map `[0]`).  Whiskered on the left by the component-1 letter `s`, they become a genuinely
INTERLEAVING pair `s·t ⇒ s·t·t` whose boundary words `blockDecompose` into `[(s),(t)]` and `[(s),(t,t)]` (each by
`rfl`).  Their monad blocks are the two faces, which the shipped bespoke decision SEPARATES
(`monadDecision_no_faces`: `[1] ≠ [0]`).  So the pair is genuinely non-convertible on its monad component.

A LIVE combined `isFalse` verdict — the pushout decider returning `isFalse` on this pair THROUGH `blockDecompose` +
the component decider — is NOT r6-reachable: it needs (i) the reconstruction transport (P3 jam) to feed the monad
decider into the pushout, and decisively (iii) the REFLECTING direction (a common `s`-whiskering of
non-convertible monad blocks stays non-convertible — the Nelson-Oppen / Baader-Tinelli purification completeness),
which `DispatchSaturated.lean` flags as broken precisely for the wire-creating unit/mult generators of the monad.
So P4 ships as a documented SEPARATION witness, not a live combined verdict — a genuine finding pinpointing why
`involution +_M monad` is strictly harder than the shipped thin `involution +_M semiring`.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## P4 — the concrete pushout monad unit and faces -/

/-- The single mode of the `involution +_M monad` pushout (`Fin 1`, both components' shared `point`). -/
def monadPushMode : Fin involutionMonadPushout.modeCount := ⟨0, by decide⟩

/-- The component-1 letter `s` as a `Modality` of the pushout (endpoints `(0, 0)` by `rfl`). -/
def monadPushSModality : involutionMonadPushout.Modality monadPushMode monadPushMode :=
  ⟨sLetter, rfl⟩

/-- The component-2 letter `t` as a `Modality` of the pushout (endpoints `(0, 0)` by `rfl`). -/
def monadPushTModality : involutionMonadPushout.Modality monadPushMode monadPushMode :=
  ⟨tLetter, rfl⟩

/-- The component-1 letter `s` as a length-1 path over the pushout. -/
def monadPushSPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode :=
  ModalityPath.cons monadPushSModality (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)

/-- The component-2 letter `t` as a length-1 path over the pushout. -/
def monadPushTPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode :=
  ModalityPath.cons monadPushTModality (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)

/-- ★ **The pushout monad unit** — the RECONSTRUCTED 2-generator index `0` (the monad's `eta`, retagged into the
pushout with `involutionComputad`'s empty 2-generator list, so the shift is `0`) inhabits the pushout's
`ReconstructedTwoCell` at the boundary `(id, t)`: the interpreter sends the retagged `lhs = []` to `id` and
`rhs = [t]` to `monadPushTPath`, both by `rfl` (the concrete pushout computes).  A GENUINE generating 2-cell over
the pushout signature. -/
def pushoutMonadUnit :
    involutionMonadPushout.ReconstructedTwoCell
      (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) monadPushTPath :=
  ⟨⟨0, by decide⟩, ⟨rfl, rfl⟩⟩

/-- The pushout monad unit as a free 2-cell `id ⇒ t`. -/
def pushoutEta :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode) monadPushTPath :=
  RawTwoCellExpr.gen pushoutMonadUnit

/-- ★ **Pushout monad face δ₁** — `eta` whiskered on the RIGHT by `t`: `t ⇒ t·t` (Δ-monotone map `[1]` on the
bespoke side).  `whiskerRight t eta`. -/
def pushoutFaceDeltaOne :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      monadPushTPath (composePath monadPushTPath monadPushTPath) :=
  RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature) monadPushTPath pushoutEta

/-- ★ **Pushout monad face δ₀** — `eta` whiskered on the LEFT by `t`: `t ⇒ t·t` (Δ-monotone map `[0]` on the
bespoke side).  `whiskerLeft t eta`. -/
def pushoutFaceDeltaZero :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (composePath monadPushTPath
        (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode))
      (composePath monadPushTPath monadPushTPath) :=
  RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature) monadPushTPath pushoutEta

/-! ## P4 — the genuinely interleaving cross-component pair -/

/-- ★ **The interleaving cell α** — the δ₁ monad face whiskered on the LEFT by the component-1 letter `s`:
`s·t ⇒ s·(t·t)`.  Its boundary genuinely mixes both components (an `s` prefix over a `t`-monad tail). -/
def crossPairAlpha :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (composePath monadPushSPath monadPushTPath)
      (composePath monadPushSPath (composePath monadPushTPath monadPushTPath)) :=
  RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature)
    monadPushSPath pushoutFaceDeltaOne

/-- ★ **The interleaving cell β** — the δ₀ monad face whiskered on the LEFT by `s`: `s·(t·id) ⇒ s·(t·t)` (the
domain `t·id` is propositionally `t`).  The δ₀/δ₁ counterpart of `crossPairAlpha` at the same monad tail. -/
def crossPairBeta :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (composePath monadPushSPath
        (composePath monadPushTPath
          (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)))
      (composePath monadPushSPath (composePath monadPushTPath monadPushTPath)) :=
  RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature)
    monadPushSPath pushoutFaceDeltaZero

/-! ## P4 — the boundary words and their block decompositions (each `rfl`) -/

/-- The domain word `s·t` of the interleaving pair — a genuine two-component alternation. -/
def crossPairDomainWord : List (Fin involutionMonadPushout.modalityGenerators.length) :=
  [sLetter, tLetter]

/-- The codomain word `s·t·t` of the interleaving pair. -/
def crossPairCodomainWord : List (Fin involutionMonadPushout.modalityGenerators.length) :=
  [sLetter, tLetter, tLetter]

/-- ★ **The domain word block-decomposes** into the two maximal same-component blocks `[(s), (t)]` (`rfl`, so it
COMPUTES): a component-1 `s` prefix and a component-2 `t` block — the interleaving is visible. -/
theorem crossPairDomainDecompose :
    blockDecompose involutionMonadSplit crossPairDomainWord
      = [(true, [sLetter]), (false, [tLetter])] := rfl

/-- ★ **The codomain word block-decomposes** into `[(s), (t t)]` (`rfl`): the `s` prefix, then the merged
component-2 `t·t` block.  The `s` block is a clean prefix, so the discrimination reduces to the pure monad blocks
— no interleaving relation fires mid-word (the disjoint-signature word-problem structure). -/
theorem crossPairCodomainDecompose :
    blockDecompose involutionMonadSplit crossPairCodomainWord
      = [(true, [sLetter]), (false, [tLetter, tLetter])] := rfl

/-- The alternation invariant at the domain word — the two blocks alternate `true false`. -/
theorem crossPairDomainAlternates :
    isAlternating (blockDecompose involutionMonadSplit crossPairDomainWord) = true :=
  blockDecompose_alternates involutionMonadSplit crossPairDomainWord

/-- The `s` block is a clean prefix of BOTH words: the two decompositions share their component-1 head block, so
the discrimination is carried entirely by the differing component-2 (monad) tails. -/
theorem crossPair_sharedPrefix :
    (blockDecompose involutionMonadSplit crossPairDomainWord).head?
      = (blockDecompose involutionMonadSplit crossPairCodomainWord).head? := rfl

/-! ## P4 — the monad-block separation (via the shipped bespoke decision) -/

/-- ★ **The monad blocks of the pair are NON-convertible.**  Stripped of the common `s`-prefix, the two component-2
blocks are the monad faces `whiskerRight t eta` (δ₁, Δ-map `[1]`) and `whiskerLeft t eta` (δ₀, Δ-map `[0]`), which
the shipped bespoke walking-monad decision SEPARATES: no `MonadSaturatedTwoCellConv` relates them.  This is the
discriminating content of P4 — the pair genuinely differs on its monad component, routed through the DECIDED
walking-monad word problem (`monadDecision_no_faces`), NOT asserted.  Restated here (over the bespoke
`monadModeSignature`, the carrier the decision lives on) to anchor the separation. -/
theorem crossPairMonadBlocksSeparate :
    ¬ MonadSaturatedTwoCellConv
        (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
        (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell) :=
  monadDecision_no_faces

/-! ## P4 — the isTrue counterpart: the disjoint-whisker exchange (FREE, cross-component) -/

/-- ★ **The isTrue counterpart — a genuinely CONVERTIBLE cross-component mixed pair.**  The `s`-left-whisker of a
`t`-right-whisker of the pushout unit is saturated-convertible to the reversed whisker order (up to the
associativity boundary cast), discharged FREE by `crossComponentWhiskerCommute` (`ofFull (whiskerExchange …)`).
The convertible counterpart to the non-convertible `crossPairMonadBlocksSeparate`: disjoint-component whiskers
commute, same-component monad faces do not.  Uses GENUINELY different-component whiskers (`s` in component 1, `t`
in component 2) AND the r6 P2 real coprojection `inclusionRightTwoReal` in its base relation. -/
def crossPairConvertibleCounterpart :=
  crossComponentWhiskerCommute
    (baseRel := SaturatedConvOverPushout involutionComputad monadComputad involutionMonadSameModes
      (inclusionLeftTwo involutionComputad monadComputad involutionMonadSameModes rfl)
      (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
      (emptyCellRel involutionComputad.toModeSignature)
      (emptyCellRel monadComputad.toModeSignature))
    monadPushSPath monadPushTPath pushoutEta

/-! ## P3 — the reconstruction bridge: the achievable 0/1-skeleton graph equivalence

The 0/1-skeleton of `monadComputad`'s reconstruction is faithful to the bespoke `monadGraph` underlying
`monadModeSignature` — a genuine `ModeGraphEquiv`, mirroring the shipped `adjunctionComputadGraphEquiv` but for one
mode / one endo-generator.  This is the EASY, PROVABLE half of the reconstruction bridge; the `twoCell`-inclusive
half (and the `Decidable` transport it enables) is the jam documented below. -/

/-- The forward mode map `Fin 1 → MonadMode` (the impossible `≥ 1` index discharged propext-free). -/
def monadFinToMode : Fin 1 → MonadMode
  | ⟨0, _⟩ => MonadMode.point
  | ⟨count + 1, isLt⟩ => False.elim (Nat.not_lt_zero count (Nat.lt_of_succ_lt_succ isLt))

/-- The backward mode map `MonadMode → Fin 1`. -/
def monadModeToFin : MonadMode → Fin 1
  | MonadMode.point => ⟨0, by decide⟩

/-- The **0-cell equivalence** `Fin 1 ≃ MonadMode` — both round-trips structural (the `Fin 1` side cased by
`Fin.mk` patterns, propext-free). -/
def monadComputadModeEquiv : TypeEquiv (Fin 1) MonadMode where
  toFun := monadFinToMode
  invFun := monadModeToFin
  leftInverse
    | ⟨0, _⟩ => rfl
    | ⟨count + 1, isLt⟩ => False.elim (Nat.not_lt_zero count (Nat.lt_of_succ_lt_succ isLt))
  rightInverse := fun mode => by cases mode; rfl

/-- Every `Fin 1` value is `⟨0, _⟩`, propext-free (`⟨val, isLt⟩` decomposition + `Nat.not_lt_zero`, NOT `Fin.cases`
which would pull `propext`). -/
theorem finOneEqZero (index : Fin 1) : (⟨0, by decide⟩ : Fin 1) = index :=
  match index with
  | ⟨0, _⟩ => rfl
  | ⟨count + 1, isLt⟩ => False.elim (Nat.not_lt_zero count (Nat.lt_of_succ_lt_succ isLt))

/-- The single `MonadModality point point` generator is `t`, drawn propext-free by explicit match (NOT `cases`,
which pulls `propext` on the indexed inductive). -/
theorem monadModalityEqT (modality : MonadModality MonadMode.point MonadMode.point) :
    MonadModality.t = modality :=
  match modality with
  | MonadModality.t => rfl

/-- Every `monadComputad` 1-generator index is `0` — the reconstructed hom `monadComputad.Modality point point`
carries exactly the one endo-generator `t`, drawn propext-free by casing the `Fin 1` index. -/
def monadComputadModalityEquiv : (src tgt : Fin 1) →
    TypeEquiv (monadComputad.Modality src tgt)
      (MonadModality (monadFinToMode src) (monadFinToMode tgt))
  | ⟨0, _⟩, ⟨0, _⟩ =>
    { toFun := fun _ => MonadModality.t
      invFun := fun _ => ⟨⟨0, by decide⟩, rfl⟩
      leftInverse := fun modality => Subtype.ext (finOneEqZero modality.val)
      rightInverse := fun modality => monadModalityEqT modality }
  | ⟨0, _⟩, ⟨count + 1, isLt⟩ =>
      False.elim (Nat.not_lt_zero count (Nat.lt_of_succ_lt_succ isLt))
  | ⟨count + 1, isLt⟩, _ =>
      False.elim (Nat.not_lt_zero count (Nat.lt_of_succ_lt_succ isLt))

/-- ★ **The 0/1-skeleton reconstruction bridge** — `monadComputad.toModeGraph` is a genuine `ModeGraphEquiv` to the
bespoke `monadGraph` underlying `monadModeSignature`.  The one-mode / one-endo-generator analogue of the shipped
`adjunctionComputadGraphEquiv`.  This is the PROVABLE half of the P3 reconstruction bridge. -/
def monadComputadGraphEquiv : ModeGraphEquiv monadComputad.toModeGraph monadGraph where
  modeEquiv := monadComputadModeEquiv
  modalityEquiv := monadComputadModalityEquiv

/-! ## P3 — the JAM: the field discrepancy between the bespoke and reconstructed monad signatures (INT-SIG-ALIGN)

The shipped real decider `monadSaturatedTwoCellDecision : MonadDecidableSaturatedTwoCellConvFor` decides
`MonadSaturatedTwoCellConv` over the BESPOKE `monadModeSignature`.  Feeding it as the component-2 decider of a
computad pushout needs `Decidable (SaturatedConvOver monadComputad.toModeSignature MonadLawRelReconstructed …)`,
over the RECONSTRUCTED `monadComputad.toModeSignature`.  These carriers are field-by-field DISTINCT Types — a
literal `=` is impossible (the `adjunctionComputad.toModeSignature ≠ adjunctionModeSignature` situation):

| carrier field | bespoke `monadModeSignature`         | reconstructed `monadComputad.toModeSignature`       |
| ------------- | ------------------------------------ | --------------------------------------------------- |
| `Mode`        | `MonadMode` (ctor `point`)           | `Fin 1`                                             |
| `Modality`    | `MonadModality` (ctor `t`)           | `{ i : Fin 1 // get i = (⟨0⟩,⟨0⟩) }`               |
| `twoCell`     | `MonadTwoCell` (ctors `eta`, `mu`)   | `ReconstructedTwoCell` (subtype of `Fin 2`)         |

`monadComputadGraphEquiv` bridges the first two rows (0/1-skeleton).  The `twoCell` row needs the FULL 2-cell
inclusive signature equivalence (`ReconstructedTwoCell ↔ MonadTwoCell` both ways, and that gens `0`/`1` are the
ONLY inhabitants), then a bidirectional `RawTwoCellExpr`-functor along that equivalence re-basing
`SaturatedConvOver` each way (the r3 `isTrue`/`isFalse` transport template).  That is coupled to
`fxMode_hasDecidableTwoCellEquality` (fib-3): the same wall `DispatchSaturated.lean` names as residual (ii).  It is
larger than one r6 round — the JAM, machine-documented here. -/

/-- ★ **Honesty marker — the P3 reconstruction bridge: 0/1-skeleton SHIPS, 2-cell transport is the JAM.**  The
graph-level equivalence `monadComputadGraphEquiv : ModeGraphEquiv monadComputad.toModeGraph monadGraph` is a
genuine iso (the achievable half).  The `twoCell`-inclusive equivalence plus the bidirectional `Decidable
(SaturatedConvOver …)` transport — the reseat of `monadSaturatedTwoCellDecision` onto the reconstructed signature —
is coupled to `fxMode_hasDecidableTwoCellEquality` (fib-3), the residual (ii) of `DispatchSaturated.lean`.  `=
true` (the graph half ships). -/
def fxAmalg_hasReconstructionGraphBridge : Bool := true

/-- **Honesty marker — the FULL decider reseat is the JAM.**  Transporting `monadSaturatedTwoCellDecision` from the
bespoke `monadModeSignature` onto the reconstructed `monadComputad.toModeSignature` (the field discrepancy tabled
above) needs the 2-cell-inclusive signature equivalence + the bidirectional cell re-basing functor, coupled to
`fxMode_hasDecidableTwoCellEquality` (fib-3).  Larger than one r6 round.  `= false`. -/
def fxAmalg_hasReconstructionDecoderReseat : Bool := false

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the discriminating cross-component SEPARATION witness SHIPS (r6 P4).**  The pushout monad
unit `pushoutEta` (a REAL reconstructed 2-generator), the two pushout monad faces (`pushoutFaceDeltaOne` /
`pushoutFaceDeltaZero`), the genuinely interleaving pair (`crossPairAlpha` / `crossPairBeta`, boundary `s·t ⇒
s·t·t`), its boundary block-decompositions computing by `rfl` (`crossPairDomainDecompose` /
`crossPairCodomainDecompose`, into `[(s),(t)]` and `[(s),(t,t)]` with a shared `s`-prefix), the monad-block
separation routed through the DECIDED bespoke walking-monad word problem (`crossPairMonadBlocksSeparate` =
`monadDecision_no_faces`), and the CONVERTIBLE isTrue counterpart via the free disjoint-whisker exchange
(`crossPairConvertibleCounterpart`, using the P2 real coprojection).  This is the FIRST concrete separation over a
real-relation pushout: disjoint-component whiskers commute (isTrue), same-component monad faces do not (isFalse on
the monad component).  `= true`. -/
def fxAmalg_hasCrossComponentSeparationWitness : Bool := true

/-- ★★★ **Honesty marker — the LIVE combined `isFalse` verdict SHIPS HYPOTHESIS-FREE (r8, the #2043 milestone).**
`crossPairAlpha ≁ crossPairBeta` is now a LIVE pushout non-convertibility verdict, discharged in
`Amalgam/PushoutBundle.lean` (`crossPairPushoutNonConvUnconditional`) — NOT via the `blockDecompose` + component
decider DISPATCH this marker originally scoped (that route needed the P3 reconstruction reseat + the broken
purification reflection for the wire-creating unit/mult regime), but via a DIFFERENT, direct route: the
signature-generic arity fold `arityMonotoneMapOf`, a SEMANTIC invariant that reflects blockwise monad inequality
straight off the ordinal fold (`[0, 2] ≠ [0, 1]`).  Its convertibility-soundness bundle
`ArityFoldConvSound involutionMonadPushout.toModeSignature` is inhabited unconditionally
(`pushoutArityFoldConvSound`) by re-homing the walking-monad Δ-fold soundness generic-over-a-face/degen arity
discipline that the pushout's two reconstructed generators satisfy (via `interpretWordFrom_length`).  With r6's
UNCONDITIONAL isTrue `crossPairConvertibleCounterpart` it is the COMPLETE discriminating pair over a real-relation
pushout.  The GENERAL saturated dispatch decision (arbitrary pairs, via the walled purification reflection /
reconstruction reseat) stays the r9+ residual (`Amalgam/PushoutBundle.lean` `fxAmalg_hasGeneralPushoutDispatch`,
`fxAmalg_hasSaturatedDispatchTheorem`).  `= true`. -/
def fxAmalg_hasLiveMonadPushoutIsFalse : Bool := true

end FX1Poly.Polygraph.Amalgam

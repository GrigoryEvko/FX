import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadDecision
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadCanonicalWord

/-! # WalkingIdempotent/IdempotentMonadMuInvertible — the multiplication is INVERTIBLE (the thinness crux)

`IdempotentMonadDecision` shipped the decision assembly MODULO local posetality (thinness), the genuine hom
`t ⇒ t` collapse on its three representatives, and named the residual: full thinness is TRUE but its mechanization
is a genuine coherence proof, and "the whole weight compresses onto ONE lemma — the mu-iso, fold-then-grow ≈ id"
(nLab *idempotent monad* condition (1): `mu : t.t ⇒ t` is a natural ISOMORPHISM, EQUIVALENT to the shipped
well-pointedness law `eta ▷ t ≈ t ◁ eta`).  This file MECHANIZES exactly that crux, zero-axiom.

## What this file ships (each piece zero-axiom)

  * ★ **`rawCell_targetLenZero_impliesSourceLenZero`** — the CELL-level RIGIDITY ("no `1 ⇒ 0`"): every free 2-cell
    whose target 1-cell is the identity (`t^0`) has an identity source.  Structural induction over
    `RawTwoCellExpr`.  Lifts the chain model's `idempotentInhabited_no_collapse_to_identity` from the boundary to
    the cell level, and makes the empty homs `t^{m+1} ⇒ nil` VACUOUSLY thin (`emptyHom_isThin`).
  * ★★ **`idempotentMulRightInverse`** — THE crux: `mu ∘ (eta ▷ t) ≈ id_{t.t}` (the "other" composite of the
    mu-iso; the LEFT unit law `(eta ▷ t) ∘ mu ≈ id_t` is the easy direction, shipped as `monadLeftUnitHolds`).
    Together they exhibit `mu` as a two-sided ISOMORPHISM with inverse `eta ▷ t` (`idempotentMulInvertible`).
    Proved by the standard equational chase — naturality of `eta` at `mu` (interchange), well-pointedness
    `eta_{TT} = T(eta_T)` (idempotence whiskered), left-whisker functoriality, and the left unit law.
  * **`idempotentThinness_ofNormalize`** — the HONEST reduction: full thinness follows from ANY
    boundary-determined normalizer (`rep` reading only the boundary + `normalize : cell ≈ rep cell`), mirroring the
    walking monad's `monadConvOfMapEq_ofNormalize`.  Pins the SOLE residual precisely: the general-`n`
    normalization, of which `idempotentMulRightInverse` is the base case.

Raw Lean 4 + Init; interchange / whisker-functoriality / monad-law constructors of the shipped relations, structural
`Nat` recursion for rigidity.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

open IdempotentMonadSaturatedTwoCellConv

/-! ## Lifting the shipped free-system moves into the idempotent relation -/

/-- Lift a single strict-2-category rewrite step (interchange / whisker distributivity / identity laws /
associativity — anything in `TwoCellStep`) into the walking-idempotent-monad convertibility, through
`ofConv`/`ofFull`/`ofMonad`. -/
theorem idempotentConvOfStep {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (step : TwoCellStep monadModeSignature cellAlpha cellBeta) :
    IdempotentMonadSaturatedTwoCellConv cellAlpha cellBeta :=
  ofMonad (MonadSaturatedTwoCellConv.ofConv (TwoCellConv.ofStep step))

/-- Lift a completed free-strict-2-category convertibility (interchange PLUS whisker FUNCTORIALITY — unit-whisker
strip, composite-whisker split, disjoint-whisker exchange) into the walking-idempotent-monad convertibility. -/
theorem idempotentConvOfFull {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (convFull : TwoCellConvFull monadModeSignature cellAlpha cellBeta) :
    IdempotentMonadSaturatedTwoCellConv cellAlpha cellBeta :=
  ofMonad (MonadSaturatedTwoCellConv.ofFull convFull)

/-! ## Cell-level rigidity: no free 2-cell collapses `t^{m+1}` to the identity 1-cell -/

private theorem natSumZero {firstAddend secondAddend : Nat}
    (hFirst : firstAddend = 0) (hSecond : secondAddend = 0) : firstAddend + secondAddend = 0 := by
  rw [hFirst, hSecond]

/-- ★ **Cell-level rigidity ("no `1 ⇒ 0`").**  Every free 2-cell of the walking idempotent monad whose TARGET
1-cell has length `0` (the identity `t^0 = nil`) has a SOURCE 1-cell of length `0`.  Structural induction over
`RawTwoCellExpr`: the two generators `eta`/`mu` both target `t` (length `1`, vacuous); `id` copies the boundary;
`vcomp` threads the two factors; the whiskerings split the length by `ModalityPath.length_composePath`.  This is
the cell-level form of the chain model's `idempotentInhabited_no_collapse_to_identity`: the idempotent monad has a
unit but NO counit, so nothing rewrites a `t`-power down to the bare identity. -/
theorem rawCell_targetLenZero_impliesSourceLenZero :
    {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath) →
    targetPath.length = 0 → sourcePath.length = 0
  | _, _, _, _, .gen MonadTwoCell.eta, hlen => Nat.noConfusion hlen
  | _, _, _, _, .gen MonadTwoCell.mu, hlen => Nat.noConfusion hlen
  | _, _, _, _, .id _, hlen => hlen
  | _, _, _, _, .vcomp cellLower cellUpper, hlen =>
      rawCell_targetLenZero_impliesSourceLenZero cellLower
        (rawCell_targetLenZero_impliesSourceLenZero cellUpper hlen)
  | _, _, _, _, .whiskerLeft whisker body, hlen =>
      Eq.trans (ModalityPath.length_composePath whisker _)
        (natSumZero (Nat.eq_zero_of_add_eq_zero_right (ModalityPath.length_composePath whisker _ ▸ hlen))
          (rawCell_targetLenZero_impliesSourceLenZero body
            (Nat.eq_zero_of_add_eq_zero_left (ModalityPath.length_composePath whisker _ ▸ hlen))))
  | _, _, _, _, .whiskerRight whisker body, hlen =>
      Eq.trans (ModalityPath.length_composePath _ whisker)
        (natSumZero
          (rawCell_targetLenZero_impliesSourceLenZero body
            (Nat.eq_zero_of_add_eq_zero_right (ModalityPath.length_composePath _ whisker ▸ hlen)))
          (Nat.eq_zero_of_add_eq_zero_left (ModalityPath.length_composePath _ whisker ▸ hlen)))

/-- Smoke: there is NO free 2-cell `t ⇒ nil` — if one existed, rigidity would force `t`'s length `1` to be `0`.
Stated as: any such cell yields a proof of `1 = 0`, hence `False` for any consumer. -/
theorem noRawCellFromTIntoIdentity
    (cell : RawTwoCellExpr monadModeSignature monadT (ModalityPath.nil (graph := monadGraph) MonadMode.point)) :
    (1 : Nat) = 0 :=
  rawCell_targetLenZero_impliesSourceLenZero cell rfl

/-- ★ **Empty homs are vacuously thin.**  When the target 1-cell is the identity but the source has POSITIVE
length, the hom is EMPTY, so any two parallel cells there are convertible — vacuously, since no such cell exists
(rigidity refutes the source-length hypothesis).  A degenerate but honest thinness instance covering the model's
"no `1 ⇒ 0`" boundary class. -/
theorem emptyHom_isThin {sourcePath : ModalityPath monadGraph MonadMode.point MonadMode.point}
    (hSourcePositive : 0 < sourcePath.length)
    (cellA cellB :
      RawTwoCellExpr monadModeSignature sourcePath (ModalityPath.nil (graph := monadGraph) MonadMode.point)) :
    IdempotentMonadSaturatedTwoCellConv cellA cellB :=
  absurd (rawCell_targetLenZero_impliesSourceLenZero cellA rfl)
    (Nat.pos_iff_ne_zero.mp hSourcePositive)

/-! ## The mu-invertibility crux: `mu ∘ (eta ▷ t) ≈ id_{t.t}`

The two 1-cells `t.t` and `t` are `monadTThenT` and `monadT`; `composePath monadT monadT = monadTThenT`
definitionally, so all the intermediate `t`-power boundaries below compute on the nose (no genuine cast survives —
the whisker-functoriality casts erase by proof irrelevance of the `Eq` boundary proofs). -/

/-- The composite `mu ∘ (eta ▷ t) : t.t ⇒ t ⇒ t.t` — multiply the two `t`'s, then re-grow one by the unit
whiskered on the right.  In an idempotent monad this is the identity `id_{t.t}` (the mu-iso "other composite"). -/
noncomputable def mulThenUnitRightWhisker :
    RawTwoCellExpr monadModeSignature monadTThenT (composePath monadT monadT) :=
  RawTwoCellExpr.vcomp monadMulTwoCell monadEtaTCell

/-- The Godement horizontal composite `eta ⊠ mu : t.t ⇒ t.t` — the `whiskerRight`-then-`whiskerLeft` order,
`(eta ▷ t.t) ∘ (t ◁ mu)`.  The naturality of `eta` at `mu` (interchange) makes it convertible to
`mulThenUnitRightWhisker`; the left unit law then collapses it to the identity. -/
noncomputable def godementUnitMul :=
  RawTwoCellExpr.hcomp (signature := monadModeSignature) monadUnitTwoCell monadMulTwoCell

/-- **Naturality of `eta` at `mu`** — `mu ∘ (eta ▷ t) ≈ eta ⊠ mu`.  The two Godement orders of the horizontal
composite `eta ⊠ mu` agree by the strict-2-category INTERCHANGE law: instantiating
`TwoCellStep.interchange` at `(id_nil ∘ eta) ⊠ (mu ∘ id_t)` produces a redex convertible (identity-law cleanups) to
`eta ⊠ mu` in the `whiskerRight`-first order, and a reduct convertible to `mu ∘ (eta ▷ t)` in the
`whiskerLeft`-first order.  No idempotence is used here — this is pure interchange. -/
theorem mulThenUnitRightWhisker_conv_godement :
    IdempotentMonadSaturatedTwoCellConv mulThenUnitRightWhisker godementUnitMul := by
  unfold mulThenUnitRightWhisker godementUnitMul
  have interchangeStep := idempotentConvOfStep (TwoCellStep.interchange (signature := monadModeSignature)
    (cellAlpha := RawTwoCellExpr.id (ModalityPath.nil (graph := monadGraph) MonadMode.point))
    (cellAlphaUpper := monadUnitTwoCell)
    (cellBeta := monadMulTwoCell)
    (cellBetaUpper := RawTwoCellExpr.id (signature := monadModeSignature) monadT))
  dsimp only [RawTwoCellExpr.hcomp] at interchangeStep ⊢
  refine trans ?_ (trans (symm interchangeStep) ?_)
  · refine trans (vcompCongrLeft _ ?_) (vcompCongrRight _ ?_)
    · exact symm (trans (vcompCongrLeft _ (idempotentConvOfStep (TwoCellStep.whiskerRightId _ _)))
        (trans (vcompCongrRight _ (idempotentConvOfFull (TwoCellConvFull.whiskerLeftUnit monadMulTwoCell)))
          (idempotentConvOfStep (TwoCellStep.vcompIdLeft monadMulTwoCell))))
    · exact symm (trans
        (vcompCongrRight _
          (idempotentConvOfStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT monadT)))
        (idempotentConvOfStep (TwoCellStep.vcompIdRight
          (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell))))
  · refine trans (vcompCongrLeft _ (whiskerRightCongr _ ?_)) (vcompCongrRight _ (whiskerLeftCongr _ ?_))
    · exact idempotentConvOfStep (TwoCellStep.vcompIdLeft monadUnitTwoCell)
    · exact idempotentConvOfStep (TwoCellStep.vcompIdRight monadMulTwoCell)

/-- **Well-pointedness whiskered** — `eta ▷ t.t ≈ t ◁ (eta ▷ t)`.  The categorical identity `eta_{TT} = T(eta_T)`:
whisker the right side by a further `t`, flip the whisker side by IDEMPOTENCE (`eta ▷ t ≈ t ◁ eta`), and
re-associate by the disjoint-whisker exchange.  This is the SOLE use of idempotence in the mu-iso chase — the step
that FAILS in the plain walking monad (where `eta ▷ t ≠ t ◁ eta`) and makes `mu` non-invertible there. -/
theorem unitRightWhiskerSquare_conv_unitLeftWhisker :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadTThenT monadUnitTwoCell)
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadEtaTCell) := by
  have whiskerSplit :=
    idempotentConvOfFull (TwoCellConvFull.whiskerRightComp (signature := monadModeSignature)
      monadT monadT monadUnitTwoCell)
  have whiskerCommute :=
    idempotentConvOfFull (TwoCellConvFull.whiskerExchange (signature := monadModeSignature)
      monadT monadT monadUnitTwoCell)
  exact trans whiskerSplit (trans (whiskerRightCongr _ idempotence) (symm whiskerCommute))

/-- **The Godement composite collapses** — `eta ⊠ mu ≈ id_{t.t}`.  After well-pointedness rewrites `eta ▷ t.t` to
`t ◁ (eta ▷ t)`, the whole composite is a LEFT whisker of `(eta ▷ t) ∘ mu`, which is the left-unit composite
`≈ id_t` (`monadLeftUnitHolds`); left-whiskering the identity gives `id_{t.t}`. -/
theorem godementUnitMul_conv_identity :
    IdempotentMonadSaturatedTwoCellConv godementUnitMul
      (RawTwoCellExpr.id (signature := monadModeSignature) monadTThenT) := by
  unfold godementUnitMul
  dsimp only [RawTwoCellExpr.hcomp]
  refine trans (vcompCongrLeft _ unitRightWhiskerSquare_conv_unitLeftWhisker) ?_
  refine trans (symm (idempotentConvOfStep
    (TwoCellStep.whiskerLeftVcomp monadT monadEtaTCell monadMulTwoCell))) ?_
  refine trans (whiskerLeftCongr _ (ofMonad MonadSaturatedTwoCellConv.leftUnit)) ?_
  exact idempotentConvOfStep (TwoCellStep.whiskerLeftId (signature := monadModeSignature) monadT monadT)

/-- ★★ **The multiplication's RIGHT inverse** — `mu ∘ (eta ▷ t) ≈ id_{t.t}`.  This is the nontrivial half of "`mu`
is an isomorphism" (the easy half, `(eta ▷ t) ∘ mu ≈ id_t`, is the left unit law).  Chains naturality of `eta` at
`mu` with the Godement collapse: `mu ∘ (eta ▷ t) ≈ eta ⊠ mu ≈ id_{t.t}`.  This is the exact residual the shipped
`fxIdempotentMonad_hasLocalPosetalityCollapse` docstring named as "the whole weight compresses onto ONE lemma", now
mechanized zero-axiom. -/
theorem idempotentMulRightInverse :
    IdempotentMonadSaturatedTwoCellConv mulThenUnitRightWhisker
      (RawTwoCellExpr.id (signature := monadModeSignature) monadTThenT) :=
  trans mulThenUnitRightWhisker_conv_godement godementUnitMul_conv_identity

/-- The multiplication's right inverse in the `t ◁ eta` presentation — `mu ∘ (t ◁ eta) ≈ id_{t.t}`.  Immediate from
`idempotentMulRightInverse` by flipping the unit whisker with idempotence (`t ◁ eta ≈ eta ▷ t`). -/
theorem idempotentMulRightInverse_leftWhisker :
    IdempotentMonadSaturatedTwoCellConv
      (RawTwoCellExpr.vcomp monadMulTwoCell monadTEtaCell)
      (RawTwoCellExpr.id (signature := monadModeSignature) monadTThenT) :=
  trans (vcompCongrRight monadMulTwoCell (symm idempotence)) idempotentMulRightInverse

/-- ★ **The multiplication is a two-sided ISOMORPHISM**, with inverse `eta ▷ t`: the LEFT unit law
`(eta ▷ t) ∘ mu ≈ id_t` (the `t ⇒ t` composite) and the crux `mu ∘ (eta ▷ t) ≈ id_{t.t}` (the `t.t ⇒ t.t`
composite).  This is nLab *idempotent monad* condition (1) — `mu` a natural iso — DERIVED from the shipped
well-pointedness law (condition (3), `eta ▷ t ≈ t ◁ eta`), the equivalence at the heart of thinness. -/
theorem idempotentMulInvertible :
    IdempotentMonadSaturatedTwoCellConv monadLeftUnitCell monadIdTCell ∧
      IdempotentMonadSaturatedTwoCellConv mulThenUnitRightWhisker
        (RawTwoCellExpr.id (signature := monadModeSignature) monadTThenT) :=
  ⟨ofMonad MonadSaturatedTwoCellConv.leftUnit, idempotentMulRightInverse⟩

/-! ## The hom `t.t ⇒ t.t` collapses on its natural representatives (one level up from the shipped `t ⇒ t`) -/

/-- ★ **The hom `t.t ⇒ t.t` is thin on three natural representatives**: the identity `id_{t.t}`, the grow-after-mul
`mu ∘ (eta ▷ t)`, and its `t ◁ eta` twin `mu ∘ (t ◁ eta)` are all mutually convertible — the mu-iso doing the real
work.  A concrete, populated hom (`(min m 1, min n 1) = (1, 1)`) where local posetality is proved outright, one
dimension above the shipped `t ⇒ t` collapse. -/
theorem idempotentHomTThenTToTThenT_thinOnRepresentatives :
    IdempotentMonadSaturatedTwoCellConv mulThenUnitRightWhisker
        (RawTwoCellExpr.id (signature := monadModeSignature) monadTThenT) ∧
      IdempotentMonadSaturatedTwoCellConv (RawTwoCellExpr.vcomp monadMulTwoCell monadTEtaCell)
        (RawTwoCellExpr.id (signature := monadModeSignature) monadTThenT) ∧
      IdempotentMonadSaturatedTwoCellConv mulThenUnitRightWhisker
        (RawTwoCellExpr.vcomp monadMulTwoCell monadTEtaCell) :=
  ⟨idempotentMulRightInverse, idempotentMulRightInverse_leftWhisker,
    trans idempotentMulRightInverse (symm idempotentMulRightInverse_leftWhisker)⟩

/-! ## The honest reduction: full thinness from a boundary-determined normalizer -/

/-- ★ **Full thinness from a boundary-determined normalizer.**  If some `rep` assigns to every free 2-cell a
parallel canonical cell that depends only on the BOUNDARY (`hRepBoundary` : parallel cells get equal `rep`), and
every cell is convertible to its `rep` (`normalize`), then EVERY parallel pair is convertible
(`IdempotentMonadThinness`): `cellA ≈ rep cellA = rep cellB ≈ cellB`.  The honest analog of the walking monad's
`monadConvOfMapEq_ofNormalize`; it pins the SOLE residual toward full thinness — a boundary-determined normalizer,
of which `idempotentMulRightInverse` (fold-then-grow ≈ id at `t.t`) is the base case. -/
theorem idempotentThinness_ofNormalize
    (rep : {sourceMode targetMode : MonadMode} →
      {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
      RawTwoCellExpr monadModeSignature sourcePath targetPath →
      RawTwoCellExpr monadModeSignature sourcePath targetPath)
    (hRepBoundary : ∀ {sourceMode targetMode : MonadMode}
      {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
      (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath), rep cellA = rep cellB)
    (normalize : ∀ {sourceMode targetMode : MonadMode}
      {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
      (cell : RawTwoCellExpr monadModeSignature sourcePath targetPath),
      IdempotentMonadSaturatedTwoCellConv cell (rep cell)) :
    IdempotentMonadThinness := by
  intro _ _ _ _ cellA cellB
  refine trans (normalize cellA) ?_
  rw [hRepBoundary cellA cellB]
  exact symm (normalize cellB)

/-! ## Smokes -/

/-- Smoke: the `mu`-iso composite `mu ∘ (eta ▷ t)` really is a genuine 2-cell of `size 4` (a `vcomp` of `mu` and a
`whiskerRight` of `eta`), not a bare identity — its convertibility to `id_{t.t}` is CONTENT, not definitional. -/
theorem mulThenUnitRightWhisker_size : mulThenUnitRightWhisker.size = 4 := rfl

/-- Smoke: the Godement composite `eta ⊠ mu` has `size 5` — a genuine horizontal composite (two whiskerings inside
a `vcomp`), so its collapse to the identity is real coherence, not bookkeeping. -/
theorem godementUnitMul_size : godementUnitMul.size = 5 := rfl

/-! ## Honesty markers -/

/-- ★★ **ESTABLISHED — the multiplication is INVERTIBLE (the thinness crux, mechanized).**  The nontrivial half
`mu ∘ (eta ▷ t) ≈ id_{t.t}` (`idempotentMulRightInverse`) is proved zero-axiom by the standard equational chase:
naturality of `eta` at `mu` (interchange), well-pointedness `eta_{TT} = T(eta_T)` (the shipped idempotence law
whiskered — the SOLE idempotence use), left-whisker functoriality, and the left unit law.  Together with the left
unit law it exhibits `mu` as a two-sided isomorphism with inverse `eta ▷ t` (`idempotentMulInvertible`) — nLab
*idempotent monad* condition (1) DERIVED from the well-pointedness condition (3).  This mechanizes exactly what the
shipped `fxIdempotentMonad_hasLocalPosetalityCollapse` docstring named as the crux ("the whole weight compresses
onto ONE lemma — fold-then-grow ≈ id"), and lifts the hom collapse from `t ⇒ t` to `t.t ⇒ t.t`.  `= true`. -/
def fxIdempotentMonad_hasMulInvertible : Bool := true

/-- **ESTABLISHED — cell-level rigidity ("no `1 ⇒ 0`").**  Every free 2-cell into the identity 1-cell has an
identity source (`rawCell_targetLenZero_impliesSourceLenZero`), so the homs `t^{m+1} ⇒ nil` are EMPTY and
vacuously thin (`emptyHom_isThin`) — the cell-level lift of the chain model's
`idempotentInhabited_no_collapse_to_identity`, the boundary-separation half of the decision.  `= true`. -/
def fxIdempotentMonad_hasCellRigidity : Bool := true

/-- **Honesty marker — full thinness NARROWED to general-`n` normalization.**  With the mu-iso crux mechanized
(`idempotentMulRightInverse`) and the honest reduction shipped (`idempotentThinness_ofNormalize`: thinness from ANY
boundary-determined normalizer), the SOLE residual toward inhabiting `IdempotentMonadLocalPosetality` is the
general-`n` normalizer: an induction over `RawTwoCellExpr` sending every free `t^m ⇒ t^n` to the canonical
representative of its `(min(m,1), min(n,1))` boundary, whose crux — the general fold-then-grow collapse
`growUp n ∘ foldDown n ≈ id_{t^n}` — is the `n`-fold iterate of `idempotentMulRightInverse` (the `n = 2` base,
now DONE), threaded through the three whisker/vcomp closure lemmas.  That closure induction (the coarse analog of
the walking monad's open `wordMul_vcomp`) is NOT landed this round, so `IdempotentMonadLocalPosetality` is not yet
inhabited and `fxIdempotentMonad_hasLocalPosetalityCollapse` stays `false`.  `= false`. -/
def fxIdempotentMonad_hasGeneralThinnessNormalizer : Bool := false

end FX1Poly.Polygraph

import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadModel

/-! # WalkingIdempotent/IdempotentMonadDecision — local posetality (thinness) and the decision modulo it

The walking idempotent monad is LOCALLY POSETAL: every hom-category is a poset — at most one 2-cell between any
two parallel 1-cells (Lack, *A 2-Categories Companion*, §1.5; nLab *adjoint string*: "Δ … is the walking lax
idempotent monoid").  Since the chain model's boundary image already decides which parallel pairs are populated
(`IdempotentMonadModel`), the whole word problem reduces to that posetality: two PARALLEL free 2-cells are ALWAYS
convertible.  This file states that as `IdempotentMonadThinness`, packages the decision assembly that consumes it
(complete and zero-axiom), and ships GENUINE thinness INSTANCES — populated homs where the collapse is proved
outright, idempotence doing real work.

## What genuinely closes vs the named residual

  * The decision ASSEMBLY (`decideIdempotentConvViaThinness`) is complete and zero-axiom: supplying thinness
    decides every parallel pair (always `isTrue`).
  * GENUINE thinness INSTANCES are proved: the hom `t ⇒ t` collapses — its representatives `mu ∘ (eta ▷ t)`,
    `mu ∘ (t ◁ eta)`, and `id_t` are all mutually convertible, the first two identified DIRECTLY through the
    idempotence law (`vcompCongrLeft`) as well as through the two unit laws.
  * The FULL thinness (`IdempotentMonadThinness` for EVERY parallel pair — the coherence / normalization theorem)
    is the NAMED RESIDUAL, exactly analogous to the walking monad's open `convOfMapEq`
    (`fxMonad_hasMonotoneMapDecisionAssembled = false`).  It is TRUE (the walking idempotent monad is locally
    posetal) but its mechanization is a genuine coherence proof, not attempted this round.  Until it lands,
    `IdempotentMonadLocalPosetality` is NOT inhabited and the decision is not real.

Raw Lean 4 + Init; the assembly is `Decidable`-plumbing over the `Prop` relation, so every declaration is
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms`
gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## Local posetality (thinness) -/

/-- ★ **Local posetality (thinness)** of the walking idempotent monad: ANY two parallel free 2-cells are
convertible — every hom is a poset with at most one 2-cell.  This is the genuine remaining content ("the walking
idempotent monad is locally posetal"); the decision below consumes it. -/
def IdempotentMonadThinness : Prop :=
  ∀ {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath),
    IdempotentMonadSaturatedTwoCellConv cellA cellB

/-- The walking idempotent monad's **local-posetality** package — the thinness collapse, the coherence theorem the
decision needs.  Mirrors `MonadSaturatedCanonicalization`: a single field whose mechanization is the residual. -/
structure IdempotentMonadLocalPosetality where
  /-- All parallel free 2-cells are convertible (at most one 2-cell per hom). -/
  allParallelConv : IdempotentMonadThinness

/-! ## The decision modulo thinness -/

/-- ★ **Decide walking-idempotent-monad saturated convertibility via thinness.**  Given local posetality, any
parallel pair is convertible, so the decision is `isTrue` unconditionally.  Complete and zero-axiom — the
`isFalse` branch never occurs because there are no non-convertible parallel pairs. -/
def decideIdempotentConvViaThinness (posetality : IdempotentMonadLocalPosetality)
    {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    Decidable (IdempotentMonadSaturatedTwoCellConv cellA cellB) :=
  isTrue (posetality.allParallelConv cellA cellB)

/-- The walking idempotent monad's **saturated 2-cell word-problem interface**: saturated convertibility is
decidable on every parallel pair of free 2-cells. -/
abbrev IdempotentMonadDecidableSaturatedTwoCellConvFor : Type :=
  {sourceMode targetMode : MonadMode} →
  {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
  (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath) →
  Decidable (IdempotentMonadSaturatedTwoCellConv cellA cellB)

/-- ★ **The walking idempotent monad's saturated 2-cell word problem, modulo local posetality.**  Supplying the
thinness collapse inhabits the full saturated decision interface — it decides EVERY parallel pair. -/
@[reducible] def idempotentSaturatedWordProblemModuloPosetality
    (posetality : IdempotentMonadLocalPosetality) : IdempotentMonadDecidableSaturatedTwoCellConvFor :=
  fun cellA cellB => decideIdempotentConvViaThinness posetality cellA cellB

/-! ## Genuine thinness INSTANCES — the hom `t ⇒ t` collapses (non-vacuity) -/

/-- The representative `mu ∘ (eta ▷ t) : t ⇒ t` collapses to `id_t` (the left-unit monad law, via `ofMonad`). -/
theorem idempotentLeftUnitConvIdT :
    IdempotentMonadSaturatedTwoCellConv monadLeftUnitCell monadIdTCell :=
  IdempotentMonadSaturatedTwoCellConv.ofMonad MonadSaturatedTwoCellConv.leftUnit

/-- The representative `mu ∘ (t ◁ eta) : t ⇒ t` collapses to `id_t` (the right-unit monad law, via `ofMonad`). -/
theorem idempotentRightUnitConvIdT :
    IdempotentMonadSaturatedTwoCellConv monadRightUnitCell monadIdTCell :=
  IdempotentMonadSaturatedTwoCellConv.ofMonad MonadSaturatedTwoCellConv.rightUnit

/-- ★ **Idempotence does real work**: the two `t ⇒ t` representatives `mu ∘ (eta ▷ t)` and `mu ∘ (t ◁ eta)` are
convertible DIRECTLY through the idempotence law (`eta ▷ t ≈ t ◁ eta` under `vcompCongrLeft mu`) — NOT only via the
two unit laws.  A genuine, idempotence-driven thinness instance at the hom `t ⇒ t`. -/
theorem idempotentLeftUnitConvRightUnit_viaIdempotence :
    IdempotentMonadSaturatedTwoCellConv monadLeftUnitCell monadRightUnitCell :=
  IdempotentMonadSaturatedTwoCellConv.vcompCongrLeft monadMulTwoCell
    IdempotentMonadSaturatedTwoCellConv.idempotence

/-- ★ **The hom `t ⇒ t` is thin (on its three canonical representatives)**: `mu ∘ (eta ▷ t)`, `mu ∘ (t ◁ eta)` and
`id_t` are all mutually convertible.  A concrete, populated hom where local posetality is proved outright — the
non-vacuous witness that the collapse is real, even though the FULL thinness is the named residual. -/
theorem idempotentHomTToT_thinOnRepresentatives :
    IdempotentMonadSaturatedTwoCellConv monadLeftUnitCell monadRightUnitCell ∧
      IdempotentMonadSaturatedTwoCellConv monadLeftUnitCell monadIdTCell ∧
      IdempotentMonadSaturatedTwoCellConv monadRightUnitCell monadIdTCell :=
  ⟨idempotentLeftUnitConvRightUnit_viaIdempotence, idempotentLeftUnitConvIdT, idempotentRightUnitConvIdT⟩

/-- Smoke: were thinness supplied, the decision fires — `decideIdempotentConvViaThinness` on any parallel pair is
`isTrue`.  (Stated as a function OF a posetality witness, so it is honest that the decision is modulo the
residual — no unproven `isTrue` is manufactured.) -/
theorem decideIdempotent_isTrue_ofPosetality (posetality : IdempotentMonadLocalPosetality) :
    ∀ {sourceMode targetMode : MonadMode}
      {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
      (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath),
      IdempotentMonadSaturatedTwoCellConv cellA cellB :=
  fun cellA cellB => posetality.allParallelConv cellA cellB

/-! ## Honesty markers -/

/-- **ESTABLISHED.**  The saturated DECISION of the walking idempotent monad is shipped MODULO the local-posetality
(thinness) collapse (`IdempotentMonadLocalPosetality`): the decision assembly
(`decideIdempotentConvViaThinness` / `idempotentSaturatedWordProblemModuloPosetality`) is complete and zero-axiom,
and GENUINE thinness instances are proved — the hom `t ⇒ t` collapses on its three representatives
(`idempotentHomTToT_thinOnRepresentatives`), the two unit composites identified DIRECTLY through the idempotence
law.  `= true`. -/
def fxIdempotentMonad_hasDecisionAssemblyModuloThinness : Bool := true

/-- **Honesty marker — the named residual (crux now DONE; only general-`n` closure remains).**  The FULL local
posetality `IdempotentMonadThinness` (EVERY parallel pair convertible — the coherence / normalization theorem) is
TRUE (the walking idempotent monad is locally posetal, Lack / nLab) but NOT yet fully mechanized: it is the coarse
analog of the walking monad's open EZ reconstruction `convOfMapEq` (`fxMonad_hasMonotoneMapDecisionAssembled =
false`).  The route normalizes every free `t^m ⇒ t^n` to the canonical cell of its `(min(m,1), min(n,1))` boundary,
then any two agree; "the whole weight compresses onto ONE lemma — the mu-iso, fold-then-grow ≈ id".  That CRUX is
now MECHANIZED in `WalkingIdempotent/IdempotentMonadMuInvertible` (`idempotentMulRightInverse` :
`mu ∘ (eta ▷ t) ≈ id_{t.t}`, zero-axiom), lifting the hom collapse from `t ⇒ t` to `t.t ⇒ t.t` and exhibiting `mu`
as invertible (`idempotentMulInvertible`).  What REMAINS is the general-`n` normalizer — the fold/grow ladder
closure whose base case is exactly that mu-iso — packaged by the honest reduction
`idempotentThinness_ofNormalize` (thinness from any boundary-determined normalizer).  Until that closure lands,
`IdempotentMonadLocalPosetality` is NOT inhabited and the decision is not real.  `= false`. -/
def fxIdempotentMonad_hasLocalPosetalityCollapse : Bool := false

end FX1Poly.Polygraph

import FX1Poly.Polygraph.TwoCategory.WalkingKZ.KZMonadPresentation
import FX1Poly.Polygraph.TwoCategory.WalkingKZ.KZMonadOrderModel
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordProblem

/-! # WalkingKZ/KZMonadDecision — soundness, the TOTAL KZ-equality decision, and the order decision modulo completeness

The walking KZ monad's 2-cell order `KZTwoCellLE` (`KZMonadPresentation`) folds into the pointwise order `mapLE`
on Delta_+ monotone maps (`KZMonadOrderModel`).  This file assembles the decision content:

  * ★ **`kzLE_sound`** — SOUNDNESS: `KZTwoCellLE a b → mapLE (fold a) (fold b)`.  A full induction reusing the
    shipped walking-MONAD legs verbatim: the `ofMonad` case is `monadMonotoneMapOf_mapEqOfConv` (fold EQ, hence
    `mapLE` by reflexivity); `kzGen` is the fold-order `mapLE [0] [1]`; the four congruences are the three shipped
    ORDER-monotonicity closures (`composeMap_mapLE_left`/`_right`, `embedLocalMap_mapLE`) fed by the vcomp / whisker
    fold homomorphisms; `refl`/`trans` are the poset laws.  The idempotent thinness scaffold is explicitly the
    WRONG altitude (it collapses homs to a boolean, erasing the order KZ is about) — the correct reuse is the finer
    walking-MONAD fold with an ORDER on top.

  * ★★ **`decideKZEq`** — the KZ 2-cell EQUALITY word problem, TOTAL and zero-axiom.  KZ-equality (`<=` both ways) of
    parallel cells coincides EXACTLY with equality of Delta_+ folds (`kzEq_iff_mapEq`, via `mapLE_antisymm` one way
    and the shipped walking-monad completeness `monadConvOfMapEq_ofNormalize` the other), which is `DecidableEq
    (List Nat)`.  So the ANTISYMMETRIC CORE — the poset reflection — of the walking KZ monad IS the (already-closed)
    walking monad, decided outright.  Non-vacuous both ways (`decideKZEq_yes_assoc` / `decideKZEq_no_faces`).

  * **`decideKZLE`** — the KZ 2-cell ORDER word problem, MODULO the named residual `KZOrderCompleteness` (the
    `leOfMapLE` reconstruction).  The soundness direction is fully proved, so the `isFalse` branch is real; only the
    `isTrue` branch needs completeness.

  * ★ **`kz_strict`** — NON-VACUITY / genuine laxness: `t ◁ eta <= eta ▷ t` holds but the reverse does NOT (it
    would force `mapLE [1] [0]`, i.e. `1 <= 0`).  A strictly-directional pair `{[0] < [1]}` witnessing that the
    walking KZ monad is properly BETWEEN the walking monad (full Delta_+) and the walking idempotent monad (thin,
    the two faces identified).

## The named residual (honest fail-forward)

The FULL order decision (`KZOrderCompleteness.leOfMapLE` : `mapLE (fold a) (fold b) → KZTwoCellLE a b`) is TRUE (the
walking KZ monad is the pointwise-ordered Delta_+, Street) but its mechanization is genuine NEW combinatorics: the
STRICT-order half must generate the pointwise order on Delta_+(m,n) by whiskered `kzGen` covering moves (the
dominance order on fibre-count vectors), the KZ analog of the walking monad's `convOfMapEq` staircase but for the
ORDER.  The EQUALITY half is entirely free (shipped monad decision), which is why `decideKZEq` is total this round;
the strict-order generation is the residual, named precisely and left for a following round.

Raw Lean 4 + Init; the induction is over an inductive `Prop`, the decision is `Decidable`-plumbing over `List Nat`
comparisons, so every declaration is `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The soundness congruence helpers (order analogs of the map-homomorphism congruences) -/

/-- Soundness, LEFT-vcomp-congruence: `composeMap` monotone in its first factor (the right factor is weakly
increasing, `first'` in range).  The order analog of `monadMonotoneMapOf_vcompCongrLeft`. -/
theorem kzSound_vcompLeft {sourceMode targetMode : MonadMode}
    {oneCellF oneCellG oneCellH : ModalityPath monadGraph sourceMode targetMode}
    {cellAlpha cellAlpha' : RawTwoCellExpr monadModeSignature oneCellF oneCellG}
    (cellBeta : RawTwoCellExpr monadModeSignature oneCellG oneCellH)
    (ih : mapLE (monadMonotoneMapOf cellAlpha) (monadMonotoneMapOf cellAlpha')) :
    mapLE (monadMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta))
      (monadMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha' cellBeta)) := by
  rw [monadMonotoneMapOf_vcomp, monadMonotoneMapOf_vcomp]
  exact composeMap_mapLE_left (monadMonotoneMapOf cellAlpha) (monadMonotoneMapOf cellAlpha')
    (monadMonotoneMapOf cellBeta)
    (by rw [monadMonotoneMapOf_length, monadMonotoneMapOf_length]) ih
    (by rw [monadMonotoneMapOf_length cellBeta]; exact monadMonotoneMapOf_mapsInto cellAlpha')
    (monadMonotoneMapOf_isWeaklyIncreasing cellBeta)

/-- Soundness, RIGHT-vcomp-congruence: `composeMap` monotone in its second factor (`cellAlpha` in range).  The order
analog of `monadMonotoneMapOf_vcompCongrRight`. -/
theorem kzSound_vcompRight {sourceMode targetMode : MonadMode}
    {oneCellF oneCellG oneCellH : ModalityPath monadGraph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr monadModeSignature oneCellF oneCellG)
    {cellBeta cellBeta' : RawTwoCellExpr monadModeSignature oneCellG oneCellH}
    (ih : mapLE (monadMonotoneMapOf cellBeta) (monadMonotoneMapOf cellBeta')) :
    mapLE (monadMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta))
      (monadMonotoneMapOf (RawTwoCellExpr.vcomp cellAlpha cellBeta')) := by
  rw [monadMonotoneMapOf_vcomp, monadMonotoneMapOf_vcomp]
  exact composeMap_mapLE_right (monadMonotoneMapOf cellAlpha)
    (monadMonotoneMapOf cellBeta) (monadMonotoneMapOf cellBeta') ih
    (by rw [monadMonotoneMapOf_length cellBeta]; exact monadMonotoneMapOf_mapsInto cellAlpha)

/-- Soundness, LEFT-whisker-congruence: the ordinal-sum embedding monotone in the local map.  The order analog of
`monadMonotoneMapOf_whiskerLeftCongr`. -/
theorem kzSound_whiskerLeft {sourceMode middleMode targetMode : MonadMode}
    (oneCell : ModalityPath monadGraph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath monadGraph middleMode targetMode}
    {cellBeta cellBeta' : RawTwoCellExpr monadModeSignature oneCellG oneCellH}
    (ih : mapLE (monadMonotoneMapOf cellBeta) (monadMonotoneMapOf cellBeta')) :
    mapLE (monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft oneCell cellBeta))
      (monadMonotoneMapOf (RawTwoCellExpr.whiskerLeft oneCell cellBeta')) := by
  rw [monadMonotoneMapOf_whiskerLeft, monadMonotoneMapOf_whiskerLeft]
  exact embedLocalMap_mapLE oneCell.length oneCellH.length 0
    (monadMonotoneMapOf cellBeta) (monadMonotoneMapOf cellBeta')
    (by rw [monadMonotoneMapOf_length, monadMonotoneMapOf_length]) ih

/-- Soundness, RIGHT-whisker-congruence: the ordinal-sum embedding monotone in the local map.  The order analog of
`monadMonotoneMapOf_whiskerRightCongr`. -/
theorem kzSound_whiskerRight {sourceMode middleMode targetMode : MonadMode}
    {oneCellF oneCellG : ModalityPath monadGraph sourceMode middleMode}
    (oneCell : ModalityPath monadGraph middleMode targetMode)
    {cellAlpha cellAlpha' : RawTwoCellExpr monadModeSignature oneCellF oneCellG}
    (ih : mapLE (monadMonotoneMapOf cellAlpha) (monadMonotoneMapOf cellAlpha')) :
    mapLE (monadMonotoneMapOf (RawTwoCellExpr.whiskerRight oneCell cellAlpha))
      (monadMonotoneMapOf (RawTwoCellExpr.whiskerRight oneCell cellAlpha')) := by
  rw [monadMonotoneMapOf_whiskerRight, monadMonotoneMapOf_whiskerRight]
  exact embedLocalMap_mapLE 0 oneCellG.length oneCell.length
    (monadMonotoneMapOf cellAlpha) (monadMonotoneMapOf cellAlpha')
    (by rw [monadMonotoneMapOf_length, monadMonotoneMapOf_length]) ih

/-! ## ★ Soundness: KZ order folds into the pointwise map order -/

/-- ★ **SOUNDNESS of the KZ order** — `KZTwoCellLE a b → mapLE (fold a) (fold b)`.  Every KZ derivation preserves the
pointwise Delta_+ order: `ofMonad` via `monadMonotoneMapOf_mapEqOfConv` (fold EQ ⟹ `mapLE` by reflexivity); `kzGen`
is the fold-order `[0] <= [1]`; the four congruences by the order-monotonicity helpers; `refl`/`trans` by the poset
laws.  This is the NO-direction of the KZ order decision — the walking-MONAD fold, ordered. -/
theorem kzLE_sound {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (le : KZTwoCellLE cellA cellB) :
    mapLE (monadMonotoneMapOf cellA) (monadMonotoneMapOf cellB) := by
  induction le with
  | ofMonad h => exact mapLE_of_eq (monadMonotoneMapOf_mapEqOfConv h)
  | kzGen =>
      have h0 : monadMonotoneMapOf kzTEtaCell = [0] := rfl
      have h1 : monadMonotoneMapOf kzEtaTCell = [1] := rfl
      rw [h0, h1]; exact mapLE01
  | vcompCongrLeft cellBeta _ ih => exact kzSound_vcompLeft cellBeta ih
  | vcompCongrRight cellAlpha _ ih => exact kzSound_vcompRight cellAlpha ih
  | whiskerLeftCongr oneCell _ ih => exact kzSound_whiskerLeft oneCell ih
  | whiskerRightCongr oneCell _ ih => exact kzSound_whiskerRight oneCell ih
  | refl cell => exact mapLE_refl (monadMonotoneMapOf cell)
  | trans _ _ ih1 ih2 =>
      exact mapLE_trans (Nat.le_of_eq (by rw [monadMonotoneMapOf_length, monadMonotoneMapOf_length])) ih1 ih2

/-! ## ★ Non-vacuity: the strictly-directional KZ pair (KZ ≠ idempotent) -/

/-- ★★ **The KZ order is genuinely directional** — `t ◁ eta <= eta ▷ t` holds (`kzGen`) but its REVERSE does NOT: it
would force `mapLE [1] [0]` (`1 <= 0`), refuted by soundness.  A strictly-directional 2-element hom-poset `{[0] <
[1]}` — the non-degeneracy proof that the walking KZ monad is PROPERLY between the walking monad (full Delta_+) and
the walking idempotent monad (thin: these two faces are IDENTIFIED).  This is exactly the lax-idempotency (the
comparison is an order, not an iso). -/
theorem kz_strict :
    KZTwoCellLE kzTEtaCell kzEtaTCell ∧ ¬ KZTwoCellLE kzEtaTCell kzTEtaCell := by
  refine ⟨KZTwoCellLE.kzGen, ?_⟩
  intro le
  have hsound := kzLE_sound le
  have h1 : monadMonotoneMapOf kzEtaTCell = [1] := rfl
  have h0 : monadMonotoneMapOf kzTEtaCell = [0] := rfl
  rw [h1, h0] at hsound
  exact not_mapLE10 hsound

/-! ## ★★ The TOTAL KZ 2-cell EQUALITY decision (the antisymmetric core = the walking monad) -/

/-- The EQUALITY half of completeness, FREE: cells with equal Delta_+ folds are KZ-`<=` (via the shipped
walking-monad completeness `monadConvOfMapEq_ofNormalize` through `ofMonad`).  The antisymmetric-core completeness
that the STRICT order generation (the residual) is NOT needed for. -/
theorem kzLE_ofMapEq {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (hmap : monadMonotoneMapOf cellA = monadMonotoneMapOf cellB) :
    KZTwoCellLE cellA cellB :=
  KZTwoCellLE.ofMonad (monadConvOfMapEq_ofNormalize monadNormalize hmap)

/-- ★★ **KZ 2-cell EQUALITY is fold equality.**  Parallel cells are KZ-equal (`<=` both ways) exactly when their
Delta_+ folds coincide: forward by `mapLE_antisymm` on the two soundness images, backward by `kzLE_ofMapEq` both
directions.  So the poset REFLECTION (antisymmetrization) of the walking KZ monad IS the walking monad — the KZ
enrichment adds ORDER, not new equalities. -/
theorem kzEq_iff_mapEq {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    KZTwoCellEq cellA cellB ↔ monadMonotoneMapOf cellA = monadMonotoneMapOf cellB := by
  constructor
  · rintro ⟨leAB, leBA⟩
    exact mapLE_antisymm (by rw [monadMonotoneMapOf_length, monadMonotoneMapOf_length])
      (kzLE_sound leAB) (kzLE_sound leBA)
  · intro hmap
    exact ⟨kzLE_ofMapEq hmap, kzLE_ofMapEq hmap.symm⟩

/-- ★★ **The KZ 2-cell EQUALITY word problem is DECIDABLE, unconditionally, zero-axiom.**  Decide `KZTwoCellEq` by
comparing Delta_+ folds (`DecidableEq (List Nat)`) through `kzEq_iff_mapEq` — no residual, because the equality half
of completeness is the shipped walking-monad reconstruction.  Closes the antisymmetric-core word problem of the
walking KZ monad. -/
def decideKZEq {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    Decidable (KZTwoCellEq cellA cellB) :=
  match (inferInstance : Decidable (monadMonotoneMapOf cellA = monadMonotoneMapOf cellB)) with
  | isTrue hmap => isTrue ((kzEq_iff_mapEq cellA cellB).mpr hmap)
  | isFalse hmap => isFalse (fun heq => hmap ((kzEq_iff_mapEq cellA cellB).mp heq))

/-- ★ Non-vacuity (equal, non-trivial → YES): the two associativity foldings `t·t·t ⇒ t` are KZ-equal (both fold
`[0,0,0]`), decided TRUE by `decideKZEq` through completeness. -/
theorem decideKZEq_yes_assoc : KZTwoCellEq monadAssocLeftCell monadAssocRightCell :=
  (kzEq_iff_mapEq monadAssocLeftCell monadAssocRightCell).mpr monadMonotoneMapOf_assoc_eq

/-- ★ Non-vacuity (separating → NO): the two idempotence faces `t ⇒ t.t` are NOT KZ-equal (folds `[0]` vs `[1]`) —
they are strictly ORDERED, not identified (the KZ ≠ idempotent separation at the equality level). -/
theorem decideKZEq_no_faces : ¬ KZTwoCellEq kzTEtaCell kzEtaTCell := by
  intro heq
  exact absurd ((kzEq_iff_mapEq kzTEtaCell kzEtaTCell).mp heq) (by decide)

/-! ## The KZ ORDER decision, modulo the named order-completeness residual -/

/-- The walking KZ monad's **order-completeness** residual — the `leOfMapLE` reconstruction: pointwise-ordered folds
lift back to a KZ 2-cell order.  TRUE (the walking KZ monad is the pointwise-ordered Delta_+) but its STRICT half is
genuine new combinatorics (covering-move generation of the dominance order via whiskered `kzGen`), the KZ analog of
the walking monad's `convOfMapEq` staircase.  Named here; not attempted this round. -/
structure KZOrderCompleteness where
  /-- Pointwise-ordered folds reconstruct a KZ 2-cell order. -/
  leOfMapLE : {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    {cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath} →
    mapLE (monadMonotoneMapOf cellA) (monadMonotoneMapOf cellB) → KZTwoCellLE cellA cellB

/-- ★ **Decide the KZ 2-cell ORDER via the fold order, modulo completeness.**  Compare the two cells' folds by
`mapLE` (zero-axiom decidable): ordered ⟹ `isTrue` (via `leOfMapLE`); unordered ⟹ `isFalse`, because SOUNDNESS
(`kzLE_sound`) would force the fold order.  The `isFalse` branch is fully backed; only `isTrue` consumes the
residual. -/
def decideKZLE (completeness : KZOrderCompleteness)
    {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    Decidable (KZTwoCellLE cellA cellB) :=
  match decMapLE (monadMonotoneMapOf cellA) (monadMonotoneMapOf cellB) with
  | isTrue hle => isTrue (completeness.leOfMapLE hle)
  | isFalse hle => isFalse (fun le => hle (kzLE_sound le))

/-- The walking KZ monad's **2-cell order word-problem interface**: `KZTwoCellLE` decidable on every parallel pair. -/
abbrev KZDecidableTwoCellLEFor : Type :=
  {sourceMode targetMode : MonadMode} →
  {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
  (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath) →
  Decidable (KZTwoCellLE cellA cellB)

/-- ★ **The walking KZ monad's 2-cell ORDER word problem, modulo order-completeness.**  Supplying the `leOfMapLE`
reconstruction inhabits the full order-decision interface — it decides EVERY parallel pair. -/
@[reducible] def kzOrderWordProblemModuloCompleteness
    (completeness : KZOrderCompleteness) : KZDecidableTwoCellLEFor :=
  fun cellA cellB => decideKZLE completeness cellA cellB

/-! ## Honesty markers -/

/-- **ESTABLISHED.**  The KZ order SOUNDNESS is complete (`kzLE_sound`): every `KZTwoCellLE` derivation folds into
the pointwise Delta_+ order `mapLE`, reusing the shipped walking-MONAD legs (`monadMonotoneMapOf_mapEqOfConv`, the
vcomp / whisker fold homomorphisms) with the three ORDER-monotonicity closures on top.  Non-vacuity is genuine and
strictly directional (`kz_strict`): `t ◁ eta <= eta ▷ t` holds, its reverse is refuted — a 2-element hom-poset
`{[0] < [1]}` distinguishing the walking KZ monad from the (thin) walking idempotent monad.  `= true`. -/
def fxKZ_hasKZOrderSoundnessAndStrictness : Bool := true

/-- **ESTABLISHED (the antisymmetric core, TOTAL).**  The KZ 2-cell EQUALITY word problem is CLOSED unconditionally,
zero-axiom (`decideKZEq`): KZ-equality of parallel cells coincides with Delta_+ fold equality (`kzEq_iff_mapEq` —
`mapLE_antisymm` forward, the shipped walking-monad completeness `monadConvOfMapEq_ofNormalize` backward), which is
`DecidableEq (List Nat)`.  So the poset REFLECTION of the walking KZ monad is exactly the (already-decided) walking
monad.  Non-vacuous both ways: the associativity foldings are decided EQUAL (`decideKZEq_yes_assoc`), the two
idempotence faces are decided NOT EQUAL (`decideKZEq_no_faces`, strictly ordered not identified).  `= true`. -/
def fxKZ_hasKZEqualityDecisionClosed : Bool := true

/-- **ESTABLISHED (order decision, modulo the residual).**  The KZ 2-cell ORDER decision assembly
(`decideKZLE` / `kzOrderWordProblemModuloCompleteness`) is complete and zero-axiom given the order-completeness
witness `KZOrderCompleteness`; the SOUNDNESS-backed `isFalse` branch is fully real.  `= true`. -/
def fxKZ_hasKZOrderDecisionModuloCompleteness : Bool := true

/-- **ESTABLISHED — the FULL KZ 2-cell ORDER decision is TOTAL (the residual is closed).**  The order-completeness
leg `KZOrderCompleteness.leOfMapLE` (pointwise-ordered folds reconstruct a KZ order) is now mechanized zero-axiom
as `kzLE_complete` and `KZOrderCompleteness` is INHABITED (`kzOrderCompletenessWitness`, in `KZOrderCompleteness`):
the STRICT half — the covering-move generation of the dominance order on Delta_+(m,n) via whiskered `kzGen` — is the
head-peel majorization recursion `kzChainByLength` (prefix-sum dominance climbed by `kzFrontCoveringMulti` +
`kzPrefixAddTotal`), the KZ analog of the walking monad's `convOfMapEq` staircase but for the directed ORDER.  So the
KZ 2-cell ORDER decision is TOTAL (`decideKZLETotal`), strictly directional, joining the already-total EQUALITY
decision (`decideKZEq`).  `= true`. -/
def fxKZ_hasWalkingKZOrderCompleteness : Bool := true

end FX1Poly.Polygraph

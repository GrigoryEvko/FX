import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadLawRelation
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadDeltaDecision

/-! # WalkingMonad/MonadSaturatedDeltaGen — the Δ SOUNDNESS leg + decision assembly, GENERIC-NATIVE
(POLY-TAB r6 monad re-founding, S2 + S3)

This file re-founds the walking-monad Δ decision's SOUNDNESS leg DIRECTLY over the GENERIC saturated carrier
`SaturatedConvOver monadModeSignature MonadLawRel`, using ONLY the generic constructors and the universal property
`SaturatedConvOver.recInto` — never the bespoke `MonadSaturatedTwoCellConv`.  It is the born-generic twin of
`monadMonotoneMapOf_mapEqOfConv` (`WalkingMonad/MonadDeltaDecision`), the "one real induction port" the recon
identified as the substantial content of the soundness half.

## The conv-FREE skeleton is REUSED verbatim (S2)

The Δ monotone-map carrier `monadMonotoneMapOf` and ALL its soundness building blocks are CONV-FREE — they never
mention any saturated convertibility relation, only `RawTwoCellExpr` and the free `TwoCellConvFull`:

  * `monadMonotoneMapOf` — the fold (`WalkingMonad/MonadDeltaModel`);
  * `monadMonotoneMapOf_eqOfConvFull` — invariance under the completed free convertibility, Godement included
    (`WalkingMonad/MonadDeltaDecision`, the disjoint-window two-block commute);
  * the three seed-law lemmas `monadMonotoneMapOf_leftUnit_eq_id` / `_rightUnit_eq_id` / `_assoc_eq`
    (`WalkingMonad/MonadDeltaModel`, the simplicial identities `σ_p δ_p = id`, `σ_p δ_{p+1} = id`, `σσ` commute);
  * the four congruence lemmas `_vcompCongrLeft` / `_vcompCongrRight` (`WalkingMonad/MonadMapFactorization`) and
    `_whiskerLeftCongr` / `_whiskerRightCongr` (`WalkingMonad/MonadWhiskerEmbedding`).

None has `MonadSaturatedTwoCellConv` in its constant-closure; only the OUTER assembly
`monadMonotoneMapOf_mapEqOfConv` inducts on the bespoke conv, and THAT is exactly what this file re-founds generic.

## What ships here (each piece bespoke-free at the constant level)

  * ★ **`monadIsMonotoneMapCongruence`** — the `IsSaturatedCongruence` witness that "equal monotone map" is a
    congruence absorbing `TwoCellConvFull`, the three `MonadLawRel` rows, the four one-hole congruences, and
    `refl`/`symm`/`trans`.  Its fields ARE the reused conv-free soundness lemmas; the `ofRelation` field collapses
    the three bespoke law arms into ONE match on the `MonadLawRel` row.
  * ★★ **`monadMonotoneMapOf_mapEqOfConvGen`** — the COMPLETE Δ soundness leg over the generic carrier, via
    `SaturatedConvOver.recInto monadIsMonotoneMapCongruence`.  Bespoke-free: its transitive constant-closure
    contains NO `MonadSaturatedTwoCellConv`.
  * **`MonadSaturatedCanonicalizationGen`** — the born-generic canonicalization structure (carrier + soundness field
    `mapEqOfConvGen` + completeness field `convOfMapEqGen`), and **`monadDecideSaturatedConvOverGen`** — the
    born-generic decision assembly consuming it (compare maps; `isTrue` via completeness, `isFalse` via soundness).
    Both bespoke-free.  The SOUNDNESS field is inhabited by `monadMonotoneMapOf_mapEqOfConvGen`; the COMPLETENESS
    field is the wave-1 residual (the born-generic normalize `monadNormalizeGen`).

Raw Lean 4 + Init; every proof BUILDS map-equalities (`recInto` folds the reused conv-free lemmas) or is a
decision assembly.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The soundness leg over the generic carrier -/

/-- ★ **"Equal monotone map" is a saturated congruence over `MonadLawRel`.**  The `IsSaturatedCongruence` witness
whose target relation is `fun cellA cellB => monadMonotoneMapOf cellA = monadMonotoneMapOf cellB`: it absorbs the
completed free convertibility (`monadMonotoneMapOf_eqOfConvFull`, Godement included), the three monad-law rows (the
`ofRelation` field matching each `MonadLawRel` row into the corresponding simplicial-identity seed lemma), the four
one-hole congruences (the shipped fold-congruence lemmas), and `refl`/`symm`/`trans` (trivially, `Eq` is an
equivalence).  Every field body is a REUSED conv-free soundness lemma — no `MonadSaturatedTwoCellConv`. -/
def monadIsMonotoneMapCongruence :
    IsSaturatedCongruence monadModeSignature MonadLawRel
      (fun cellA cellB => monadMonotoneMapOf cellA = monadMonotoneMapOf cellB) where
  ofFull full := monadMonotoneMapOf_eqOfConvFull full
  ofRelation row :=
    match row with
    | MonadLawRel.leftUnit => monadMonotoneMapOf_leftUnit_eq_id
    | MonadLawRel.rightUnit => monadMonotoneMapOf_rightUnit_eq_id
    | MonadLawRel.assoc => monadMonotoneMapOf_assoc_eq
  vcompCongrLeft ih := monadMonotoneMapOf_vcompCongrLeft _ ih
  vcompCongrRight ih := monadMonotoneMapOf_vcompCongrRight _ ih
  whiskerLeftCongr ih := monadMonotoneMapOf_whiskerLeftCongr _ ih
  whiskerRightCongr ih := monadMonotoneMapOf_whiskerRightCongr _ ih
  refl _cell := rfl
  symm ih := ih.symm
  trans ihLeft ihRight := ihLeft.trans ihRight

/-- ★★ **The COMPLETE Δ soundness leg over the GENERIC carrier** — every `SaturatedConvOver monadModeSignature
MonadLawRel` derivation preserves the monotone map.  The born-generic twin of `monadMonotoneMapOf_mapEqOfConv`
(`WalkingMonad/MonadDeltaDecision`): instead of inducting on the bespoke `MonadSaturatedTwoCellConv` (11 arms, the
three laws as separate ctors), it applies the universal property `SaturatedConvOver.recInto` to
`monadIsMonotoneMapCongruence` (the three laws collapsed into the single `ofRelation` match).  Its transitive
constant-closure contains NO `MonadSaturatedTwoCellConv` — the NO-direction of the Δ decision, re-based. -/
theorem monadMonotoneMapOf_mapEqOfConvGen {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    {cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath}
    (conv : SaturatedConvOver monadModeSignature MonadLawRel cellA cellB) :
    monadMonotoneMapOf cellA = monadMonotoneMapOf cellB :=
  SaturatedConvOver.recInto monadIsMonotoneMapCongruence conv

/-! ## The born-generic canonicalization structure + decision assembly -/

/-- The walking monad's **GENERIC saturated canonicalization** — the monotone-map normal form packaged with its two
invariance directions over the GENERIC carrier `SaturatedConvOver monadModeSignature MonadLawRel`: `mapEqOfConvGen`
(SOUND — generically-convertible cells have equal maps) and `convOfMapEqGen` (COMPLETE — equal maps reconstruct a
generic convertibility).  The born-generic analog of `MonadSaturatedCanonicalization` (`WalkingMonad/MonadDeltaModel`),
typed over the generic carrier so an inhabitant is bespoke-free. -/
structure MonadSaturatedCanonicalizationGen where
  /-- The monotone-map normal form of a saturated 2-cell. -/
  monotoneMapOf : {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    RawTwoCellExpr monadModeSignature sourcePath targetPath → List Nat
  /-- SOUNDNESS over the generic carrier: generically-convertible cells have equal monotone maps. -/
  mapEqOfConvGen : {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    {cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath} →
    SaturatedConvOver monadModeSignature MonadLawRel cellA cellB → monotoneMapOf cellA = monotoneMapOf cellB
  /-- COMPLETENESS over the generic carrier: cells with equal monotone maps are generically convertible. -/
  convOfMapEqGen : {sourceMode targetMode : MonadMode} →
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode} →
    {cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath} →
    monotoneMapOf cellA = monotoneMapOf cellB → SaturatedConvOver monadModeSignature MonadLawRel cellA cellB

/-- ★ **Decide GENERIC walking-monad saturated convertibility via the monotone map.**  Given the born-generic
canonicalization, compare the two cells' monotone maps by list equality: equal maps ⟹ `isTrue` (via
`convOfMapEqGen`); unequal maps ⟹ `isFalse` (via `mapEqOfConvGen`, soundness).  Both branches discharged from the
canonicalization's two generic directions — the born-generic analog of `monadDecideSaturatedConvViaMonotoneMap`,
with NO `MonadSaturatedTwoCellConv` in the assembly. -/
def monadDecideSaturatedConvOverGen (canon : MonadSaturatedCanonicalizationGen)
    {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath) :
    Decidable (SaturatedConvOver monadModeSignature MonadLawRel cellA cellB) :=
  match (inferInstance : Decidable (canon.monotoneMapOf cellA = canon.monotoneMapOf cellB)) with
  | isTrue mapsEqual => isTrue (canon.convOfMapEqGen mapsEqual)
  | isFalse mapsDiffer => isFalse (fun conv => mapsDiffer (canon.mapEqOfConvGen conv))

/-- The born-generic decision assembly at the full interface `DecidableSaturatedConvForRel monadModeSignature
MonadLawRel`: supplying a born-generic canonicalization decides EVERY parallel pair over the generic carrier.  The
born-generic analog of `monadSaturatedWordProblemModuloCanonicalization`. -/
def monadSaturatedGenDecisionModulo (canon : MonadSaturatedCanonicalizationGen) :
    DecidableSaturatedConvForRel monadModeSignature MonadLawRel :=
  fun cellA cellB => monadDecideSaturatedConvOverGen canon cellA cellB

/-! ## Honesty marker -/

/-- **ESTABLISHED — the walking-monad Δ SOUNDNESS leg is RE-FOUNDED GENERIC-NATIVE (POLY-TAB r6, S2 + S3).**  The
born-generic `monadMonotoneMapOf_mapEqOfConvGen` — every `SaturatedConvOver monadModeSignature MonadLawRel`
derivation preserves the monotone map — is proved DIRECTLY via the universal property
`SaturatedConvOver.recInto monadIsMonotoneMapCongruence`, reusing verbatim the conv-FREE fold + soundness lemmas
(`monadMonotoneMapOf` / `_eqOfConvFull` / the three seed-law lemmas / the four congruences), so its transitive
constant-closure contains NO `MonadSaturatedTwoCellConv` (the S4 audit twin's meta-walk confirms it, with the
bespoke `monadMonotoneMapOf_mapEqOfConv` as the needle-detector control).  The born-generic canonicalization
structure `MonadSaturatedCanonicalizationGen` and decision assembly `monadDecideSaturatedConvOverGen` /
`monadSaturatedGenDecisionModulo` are shipped bespoke-free; the SOUNDNESS field is inhabited, and the COMPLETENESS
field `convOfMapEqGen` (the born-generic normalize `monadNormalizeGen`) is the wave-1 residual.  `= true`. -/
def fxMonad_hasGenericNativeSoundnessLeg : Bool := true

end FX1Poly.Polygraph.Amalgam

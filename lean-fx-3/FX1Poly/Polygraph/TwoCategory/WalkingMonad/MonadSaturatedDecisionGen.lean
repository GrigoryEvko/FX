import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaGen
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordProblem

/-! # WalkingMonad/MonadSaturatedDecisionGen — the GENERIC decider: soundness born-generic, completeness INTERIM
(POLY-TAB r6 monad re-founding, S4 — HONEST PARTIAL)

The born-generic decision assembly `monadDecideSaturatedConvOverGen` (`WalkingMonad/MonadSaturatedDeltaGen`) decides
`SaturatedConvOver monadModeSignature MonadLawRel` GIVEN a born-generic canonicalization
`MonadSaturatedCanonicalizationGen` (carrier + `mapEqOfConvGen` + `convOfMapEqGen`).  Its SOUNDNESS field is inhabited
BESPOKE-FREE (`monadMonotoneMapOf_mapEqOfConvGen`, S3).  Its COMPLETENESS field `convOfMapEqGen` — the born-generic
normalize `monadNormalizeGen : cell → SaturatedConvOver monadModeSignature MonadLawRel cell (canon cell)` — is the
wave-1 RESIDUAL: unlike the trivially-thin idempotent lane, the walking monad is NOT locally posetal, so completeness
is the full Eilenberg–Zilber word-multiplicativity chain (`wordMul_vcomp` / `wordMul_hcomp` / the vcomp-multiplicativity
`MonadVcompMult` + `MonadHcompMult` + `MonadWordMultiplicativity`, ~2000 conv-producing lines) re-founded ctor-for-ctor
over the generic carrier.  That born-generic port is wave-2.

## What ships here (honest partial)

  * **`monadSaturatedCanonicalizationGenViaBridge`** — an INTERIM inhabitant of `MonadSaturatedCanonicalizationGen`:
    its SOUNDNESS field is the BESPOKE-FREE `monadMonotoneMapOf_mapEqOfConvGen`; its COMPLETENESS field transports the
    bespoke `monadConvOfMapEq_ofNormalize monadNormalize` through `monadSaturated_to_generic` (INT-SIG-ALIGN #2079's
    forward iso).  So this canonicalization's completeness STILL references `MonadSaturatedTwoCellConv` — it is NOT
    bespoke-free, and the constant META-WALK below records exactly that (the residual is the completeness field).
  * **`decideSaturatedConvOverMonadInterim`** — the working GENERIC decider built from it.  It decides EVERY parallel
    pair over the generic carrier; the SOUNDNESS half of its verdict is born-generic, the COMPLETENESS half rides the
    bridge.  The name `decideSaturatedConvOverMonadNative` is RESERVED for the wave-2 bespoke-free decider (the moment
    `monadNormalizeGen` lands, the interim canonicalization is swapped and the marker flips).
  * **Regression continuity** — the interim generic decider AGREES with the shipped bespoke
    `monadSaturatedTwoCellDecision` on the lane regression pairs: the size-3 associativity pair `t.t.t ⇒ t`
    (CONVERTIBLE, both fold `[0,0,0]`, `isTrue`) and the separating size-1 faces pair `t ⇒ t.t` (NON-convertible,
    maps `[1]` vs `[0]`, `isFalse`).  Both deciders match on the SAME `monadMonotoneMapOf` comparison, so they agree
    by `rfl`, including the separating `isFalse` pair.

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin; the interim canonicalization's non-bespoke-freeness (the completeness
residual) is recorded by the constant meta-walk. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The INTERIM canonicalization: born-generic soundness + bespoke-transported completeness -/

/-- **INTERIM** inhabitant of the born-generic canonicalization.  SOUNDNESS is the bespoke-free
`monadMonotoneMapOf_mapEqOfConvGen` (S3); COMPLETENESS transports the bespoke normalize
`monadConvOfMapEq_ofNormalize monadNormalize` through the INT-SIG-ALIGN forward iso `monadSaturated_to_generic`.  The
completeness field therefore still contains `MonadSaturatedTwoCellConv` in its constant-closure — the exact wave-1
residual (the born-generic `monadNormalizeGen` port).  Swapping this field for the born-generic normalize yields the
bespoke-free canonicalization (wave-2). -/
def monadSaturatedCanonicalizationGenViaBridge : MonadSaturatedCanonicalizationGen where
  monotoneMapOf := monadMonotoneMapOf
  mapEqOfConvGen := monadMonotoneMapOf_mapEqOfConvGen
  convOfMapEqGen := fun hmap => monadSaturated_to_generic (monadConvOfMapEq_ofNormalize monadNormalize hmap)

/-- ★ **The working GENERIC decider (INTERIM)** — decides `SaturatedConvOver monadModeSignature MonadLawRel` on
every parallel pair via the born-generic assembly `monadDecideSaturatedConvOverGen`.  Its SOUNDNESS branch is
born-generic; its COMPLETENESS branch rides the bespoke normalize through the interim canonicalization.  The
bespoke-free target `decideSaturatedConvOverMonadNative` is blocked ONLY on the born-generic `monadNormalizeGen`. -/
def decideSaturatedConvOverMonadInterim :
    DecidableSaturatedConvForRel monadModeSignature MonadLawRel :=
  monadSaturatedGenDecisionModulo monadSaturatedCanonicalizationGenViaBridge

/-! ## Regression continuity: interim generic decider = old bespoke decider on the lane pairs -/

/-- The interim generic decider decides the size-3 associativity pair `mu . (mu |> t)` vs `mu . (t <| mu)` (both
fold the width-3 degeneracy `[0,0,0]`) to `true` (CONVERTIBLE). -/
def monadGenDecidesTrue_assoc : Bool :=
  match decideSaturatedConvOverMonadInterim monadAssocLeftCell monadAssocRightCell with
  | isTrue _ => true
  | isFalse _ => false

/-- The interim generic decider decides the separating size-1 faces pair `whiskerRight t eta` (`δ₁`, map `[1]`) vs
`whiskerLeft t eta` (`δ₀`, map `[0]`) to `false` (NON-convertible) — the separating `isFalse` verdict. -/
def monadGenDecidesFalse_faces : Bool :=
  match decideSaturatedConvOverMonadInterim
      (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
      (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell) with
  | isTrue _ => true
  | isFalse _ => false

/-- The interim generic decider returns `true` on the associativity pair (by `rfl`). -/
theorem monadGenDecidesTrue_assoc_holds : monadGenDecidesTrue_assoc = true := rfl

/-- The interim generic decider returns `false` on the separating faces pair (by `rfl`). -/
theorem monadGenDecidesFalse_faces_holds : monadGenDecidesFalse_faces = false := rfl

/-- Map the old bespoke decision to a `Bool` verdict, for the regression comparison. -/
def monadOldVerdict {sourceMode targetMode : MonadMode}
    {sourcePath targetPath : ModalityPath monadGraph sourceMode targetMode}
    (cellA cellB : RawTwoCellExpr monadModeSignature sourcePath targetPath) : Bool :=
  match monadSaturatedTwoCellDecision cellA cellB with
  | isTrue _ => true
  | isFalse _ => false

/-- ★ **Regression: interim generic = old bespoke on BOTH lane pairs.**  Both deciders branch on the same
`monadMonotoneMapOf cellA = monadMonotoneMapOf cellB` comparison, so the interim generic verdict equals the old
bespoke verdict on the associativity pair (both `true`) and the separating faces pair (both `false`), including the
`isFalse` separating pair — by `rfl`. -/
def monadGenAgreesOldOnRegression : Bool :=
  (monadGenDecidesTrue_assoc == monadOldVerdict monadAssocLeftCell monadAssocRightCell)
    && (monadGenDecidesFalse_faces
        == monadOldVerdict
            (RawTwoCellExpr.whiskerRight (signature := monadModeSignature) monadT monadUnitTwoCell)
            (RawTwoCellExpr.whiskerLeft (signature := monadModeSignature) monadT monadUnitTwoCell))

/-- Regression value: the interim generic decider agrees with the old bespoke decider on both lane pairs (by `rfl`). -/
theorem monadGenAgreesOldOnRegression_holds : monadGenAgreesOldOnRegression = true := rfl

/-! ## Honesty markers -/

/-- **ESTABLISHED (INTERIM) — the GENERIC walking-monad decider is WORKING with born-generic SOUNDNESS (POLY-TAB r6,
S4 partial).**  `decideSaturatedConvOverMonadInterim` decides `SaturatedConvOver monadModeSignature MonadLawRel` on
every parallel pair; its SOUNDNESS half is the bespoke-free `monadMonotoneMapOf_mapEqOfConvGen`, its COMPLETENESS half
rides the bespoke normalize through `monadSaturated_to_generic` (the interim canonicalization
`monadSaturatedCanonicalizationGenViaBridge`).  It reproduces the shipped bespoke decider's verdicts on both lane
regression pairs (`monadGenAgreesOldOnRegression_holds`, incl. the separating `isFalse` faces pair).  `= true`. -/
def fxMonad_hasGenericNativeDeciderInterim : Bool := true

/-- **RESIDUAL (honest) — the fully BESPOKE-FREE monad decider is NOT yet complete.**  The completeness field of the
interim canonicalization transports the bespoke `monadConvOfMapEq_ofNormalize monadNormalize`, so
`monadSaturatedCanonicalizationGenViaBridge` and `decideSaturatedConvOverMonadInterim` STILL contain
`MonadSaturatedTwoCellConv` in their constant-closure (the constant meta-walk records this).  The wave-1 residual is
the born-generic normalize `monadNormalizeGen` — the Eilenberg–Zilber word-multiplicativity chain (`wordMul_vcomp`,
the vcomp/hcomp/word-multiplicativity conv-producing files) re-founded ctor-for-ctor over the generic carrier, which
is the substantial wave-2 port.  Once it lands, `convOfMapEqGen` is swapped born-generic, the bespoke-free
`decideSaturatedConvOverMonadNative` is assembled, and this marker flips.  `= false` (honestly). -/
def fxMonad_hasGenericNativeDecider : Bool := false

end FX1Poly.Polygraph.Amalgam

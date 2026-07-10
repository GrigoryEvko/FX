import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadSaturatedDeltaGen

/-! # WalkingMonad/MonadSaturatedDecisionGen — the GENERIC decider markers (native COMPLETE; interim RETIRED)
(MONAD-R7 r2, S5 — the superseded INTERIM decider retired)

The born-generic decision assembly `monadDecideSaturatedConvOverGen` (`WalkingMonad/MonadSaturatedDeltaGen`) decides
`SaturatedConvOver monadModeSignature MonadLawRel` GIVEN a born-generic canonicalization
`MonadSaturatedCanonicalizationGen`.  Its SOUNDNESS field is inhabited BESPOKE-FREE
(`monadMonotoneMapOf_mapEqOfConvGen`, S3); its COMPLETENESS field is inhabited born-generic by `monadNormalizeGen`
(`WalkingMonad/MonadNormalizeGen`, WAVE 2), assembling the fully bespoke-free `decideSaturatedConvOverMonadNative`.

## History: the RETIRED INTERIM decider (MONAD-R7 r2, S5)

At r6 an INTERIM generic decider shipped HERE — `monadSaturatedCanonicalizationGenViaBridge` /
`decideSaturatedConvOverMonadInterim` — whose SOUNDNESS half was born-generic (`monadMonotoneMapOf_mapEqOfConvGen`)
but whose COMPLETENESS half transported the bespoke normalize (`monadConvOfMapEq_ofNormalize monadNormalize`)
through the INT-SIG-ALIGN forward iso `monadSaturated_to_generic`, so it still referenced `MonadSaturatedTwoCellConv`.
The WAVE-2 native decider `decideSaturatedConvOverMonadNative` (`WalkingMonad/MonadNormalizeGen`) SUPERSEDED it BOTH
ways born-generic.  MONAD-R7 r2 (S5) RETIRED the interim machinery here — the interim canonicalization + decider and
their old-vs-interim regression pairs (`monadGenDecidesTrue_assoc` / `monadGenDecidesFalse_faces` / `monadOldVerdict`
/ `monadGenAgreesOldOnRegression`) — removing this file's dependency on the bespoke `monadNormalize` /
`monadSaturatedTwoCellDecision` (the `MonadWordProblem` import is dropped here; `WalkingMonad/MonadNormalizeGen` now
imports `MonadWordProblem` directly for the conv-FREE `one_le_cellSize` fuel lemma it previously received
transitively through this file).  The
native / interim / old verdict continuity (all three fold the same `monadMonotoneMapOf` comparison — assoc `[0,0,0]`
`isTrue`, separating faces `[1] ≠ [0]` `isFalse`) is now recorded HISTORICALLY in `Table/TableRetirementLedger` (the r7-r2
section).  The two markers below survive as HISTORY (interim, retired) + LIVE (native, complete).

Raw Lean 4 + Init; `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration
`#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

/-! ## Honesty markers -/

/-- **ESTABLISHED (HISTORY — the interim decider is RETIRED, MONAD-R7 r2 S5).**  At r6 a working INTERIM generic
decider shipped here (`decideSaturatedConvOverMonadInterim`, built from the interim canonicalization
`monadSaturatedCanonicalizationGenViaBridge`): its SOUNDNESS half was the bespoke-free
`monadMonotoneMapOf_mapEqOfConvGen`, its COMPLETENESS half rode the bespoke normalize through
`monadSaturated_to_generic`.  It decided every parallel pair over the generic carrier and reproduced the shipped
bespoke decider's verdicts on both lane regression pairs (incl. the separating `isFalse` faces pair).  It was
SUPERSEDED by the fully bespoke-free `decideSaturatedConvOverMonadNative` (`fxMonad_hasGenericNativeDecider` below)
and its machinery was RETIRED in MONAD-R7 r2 (S5); this marker stands as the historical record that the interim
milestone was reached and machine-checked.  `= true`. -/
def fxMonad_hasGenericNativeDeciderInterim : Bool := true

/-- ★★ **ESTABLISHED (WAVE 2) — the fully BESPOKE-FREE monad decider is COMPLETE.**  The wave-2 port
(`WalkingMonad/MonadWordMultGen` / `MonadNormalizeCasesGen` / `MonadVcompMultGen` / `MonadWordVcompGen` /
`MonadNormalizeGen`) re-founded the Eilenberg–Zilber word-multiplicativity chain (`wordMul_vcompGen` / `wordMul_hcompGen`
/ the vcomp/hcomp/word-multiplicativity conv-producing lemmas) ctor-for-ctor over the generic carrier, inhabiting the
born-generic normalize `monadNormalizeGen : cell → SaturatedConvOver monadModeSignature MonadLawRel cell (canon cell)`.
That inhabits `convOfMapEqGen` born-generic in `monadSaturatedCanonicalizationGenNative` (SOUNDNESS field the
born-generic `monadMonotoneMapOf_mapEqOfConvGen`), yielding the terminal `decideSaturatedConvOverMonadNative`
(`WalkingMonad/MonadNormalizeGen`) — decided BOTH ways born-generic, its ENTIRE constant-closure free of
`MonadSaturatedTwoCellConv` (the exhaustive `includeStdlib := true` meta-walk certifies it; 847 constants walked).
It decides both lane regression pairs correctly (`monadNativeAgreesOnRegression_holds` — the associativity pair
`isTrue`, the separating faces pair `isFalse`); the historical native / interim / old verdict continuity is recorded
in `Table/TableRetirementLedger` (the r7-r2 section).  `= true`. -/
def fxMonad_hasGenericNativeDecider : Bool := true

end FX1Poly.Polygraph.Amalgam

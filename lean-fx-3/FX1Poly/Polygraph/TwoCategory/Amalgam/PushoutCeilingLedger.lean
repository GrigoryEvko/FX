import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutPayloadZipProbeVerdict

/-! # Polygraph/TwoCategory/Amalgam/PushoutCeilingLedger — the #2043 CEILING ADJUDICATION: the four masters mapped
verbatim to DONE / MECHANICAL / JAM-A, the total-reader gated form, and the close criterion re-derived (WP-AMALG-2
r20, Bricks B3 + B4)

Twenty rounds in, this file lands the DEFINITIVE #2043 state after the r20 payload-zip probe.  The verdict
(`PushoutPayloadZipProbeVerdict.lean`, B1): the payload arm is NOT an independent wall — it IS the JAM A per-gap
descent composed with the WalkingMonad reconstructed word problem (fib-3-coupled).  On top of the r20 B2 arm (a)
(`fxAmalg_hasIdCanonicalCollapse`) this file re-scopes the four masters and the total-canonical reader IN NEW DECLS
ONLY — every master `Prop` stays byte-intact at its walled value.

## The five-arm completion plan (the PROVABLE branch)

  1. **id-collapse** — ✅ DONE (r20 B2 arm (a), `fxAmalg_hasIdCanonicalCollapse`).
  2. **whiskerLeft junction merge** — MECHANICAL, r21 (`fxAmalg_whiskerJunctionMergeStaysWalled`, JAM-B only).
  3. **whiskerRight junction merge** — MECHANICAL, r21 (same node, `whiskerRight` dual).
  4. **vcomp common-refinement zip** — JAM-A + fib-3 HOSTAGE (`fxAmalg_vcompCommonRefinementZipStaysWalled` =
     `fxAmalg_hasSaturatedDispatchTheorem`, cross-lane, cannot author in Amalgam).
  5. **top assembly + decider wiring** — gated on 1–4 (`fxAmalg_topFactorizationInductionStaysWalled`).

Arms 1–3 flip at most master conjunct (iii) (COMPLETENESS descent for the wall-free / whisker frames); arms 4–5 gate
(i)/(ii) on JAM A.  NO master flips until arm 4, which is fib-3-hostage.

## The four masters, mapped verbatim (each `Prop` byte-intact)

  * **`fxAmalg_hasFullSaturatedPushoutDispatch`** (`DispatchSaturated.lean:351`, `false`) — the skeleton fragment is
    DONE (r16 ALIGNABLE, `fxAmalg_alignmentVerdictAlignableAtSkeleton`); the payload fragment is exactly conjunct
    (iii) COMPLETENESS = the JAM A descent, NOT a separate payload wall.
  * **`fxAmalg_hasGeneralPushoutDispatch`** (`PushoutBundle.lean:1081`, `false`) — needs (i) the reconstruction decider
    reseat (fib-3) OR (ii) purification-reflection completeness; the payload comparison IS the reconstruction decider
    per-gap, so the payload arm needs BOTH — doubly-hostage.
  * **`fxAmalg_hasSaturatedDispatchTheorem`** (`SaturatedDispatch.lean:143`, `false`) — the JAM A named node; the
    payload zip = the descent = THIS node (`fxAmalg_vcompZipIsJamADescent`).
  * **`fxAmalg_topFactorizationInductionStaysWalled`** (`PushoutVcompInterchangeSplice.lean:273`, `true`) — the reader
    is buildable at SKELETON granularity (existence + skeleton-canonical decision + gen/id arms SHIPPED); its
    payload-canonical form is the JAM A hostage; a complete reader flips at most (iii), leaving (i)/(ii) gated on the
    descent it never supplies.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The ceiling status of each reader arm -/

/-- The **ceiling status** of a canonical-reader arm after the r20 probe: `done` (shipped this round or earlier),
`mechanicalR21` (JAM-B-only engineering, authorable next round, no JAM A), or `jamAHostage` (blocked on the JAM A
per-gap descent + the fib-3 WalkingMonad reconstruction iso, cross-lane, cannot author in the Amalgam lane). -/
inductive CeilingStatus : Type where
  | done
  | mechanicalR21
  | jamAHostage
deriving DecidableEq

/-- The five canonical-reader arms and their r20 ceiling status.  Arm (a) id-collapse is DONE (r20 B2); arms (b)/(b')
whisker junction merge are MECHANICAL (r21, JAM-B); arm (c) the vcomp common-refinement zip is the JAM-A hostage; the
top assembly is gated on all four (hostage while arm (c) is). -/
def pushoutReaderArmStatus : List (String × CeilingStatus) :=
  [ ("id-collapse (arm a)", CeilingStatus.done),
    ("whiskerLeft junction merge (arm b)", CeilingStatus.mechanicalR21),
    ("whiskerRight junction merge (arm b')", CeilingStatus.mechanicalR21),
    ("vcomp common-refinement zip (arm c)", CeilingStatus.jamAHostage),
    ("top assembly + decider wiring", CeilingStatus.jamAHostage) ]

/-- ★★ **The reader-arm ledger reads exactly one DONE, two MECHANICAL, two JAM-A (`rfl`).**  Machine-checks the r20
scoreboard: arm (a) shipped, arms (b)/(b') are next-round mechanical, arm (c) and the top assembly are the JAM A +
fib-3 hostage. -/
theorem pushoutReaderArmStatus_scoreboard :
    (pushoutReaderArmStatus.filter (fun entry => entry.2 == CeilingStatus.done)).length = 1
      ∧ (pushoutReaderArmStatus.filter (fun entry => entry.2 == CeilingStatus.mechanicalR21)).length = 2
      ∧ (pushoutReaderArmStatus.filter (fun entry => entry.2 == CeilingStatus.jamAHostage)).length = 2 :=
  ⟨rfl, rfl, rfl⟩

/-! ## The total-reader gated form -/

/-- The **total canonical reader gated state** — the DONE fragments (the factorization motive + arms, the id-collapse,
the skeleton alignment, the coarse producer) all `true`, conjoined with every master + top-reader marker held at its
walled value.  This is the r20 definitive shape: the reader is TOTAL at skeleton granularity, its payload-canonical
form is the JAM A hostage. -/
def pushoutTotalReaderGatedState : Bool :=
  fxAmalg_hasCanonicalFactorizationArms
    && fxAmalg_hasIdCanonicalCollapse
    && fxAmalg_hasFiringBlockProducer
    && fxAmalg_alignmentVerdictAlignableAtSkeleton
    && fxAmalg_hasVcompGapInterchangeSplice
    && fxAmalg_totalCanonicalReaderStaysGated
    && fxAmalg_whiskerJunctionMergeStaysWalled
    && fxAmalg_vcompCommonRefinementZipStaysWalled
    && fxAmalg_topFactorizationInductionStaysWalled

/-- The total-reader gated state holds (`rfl`): every DONE fragment ships and every walled marker holds. -/
theorem pushoutTotalReaderGatedState_true : pushoutTotalReaderGatedState = true := rfl

/-! ## The close criterion, re-derived -/

/-- The **#2043 close criterion** — the conjunction that would close #2043: all four masters flipped to their closing
values (`fxAmalg_hasFullSaturatedPushoutDispatch`, `fxAmalg_hasGeneralPushoutDispatch`,
`fxAmalg_hasSaturatedDispatchTheorem` all `true`, the top-factorization wall `false`).  Re-derived here as the single
Boolean gate the definitive state is measured against. -/
def pushoutDispatchCloseCriterion : Bool :=
  fxAmalg_hasFullSaturatedPushoutDispatch
    && fxAmalg_hasGeneralPushoutDispatch
    && fxAmalg_hasSaturatedDispatchTheorem
    && (!fxAmalg_topFactorizationInductionStaysWalled)

/-- ★★★ **#2043 does NOT close (`rfl`).**  The close criterion is `false`: no master has flipped.  By the ceiling
ledger the criterion flips only when arm (c) — the vcomp zip = the JAM A descent = `fxAmalg_hasSaturatedDispatchTheorem`
— flips, which is fib-3-hostage (cross-lane).  So `#2043` is walled on ONE residual, definitively. -/
theorem pushoutDispatchCloseCriterion_false : pushoutDispatchCloseCriterion = false := rfl

/-! ## The definitive-state markers -/

/-- ★★★ **Honesty marker — the #2043 DEFINITIVE STATE after twenty rounds: ONE residual, the payload arm IS JAM A
(WP-AMALG-2 r20, B3 + B4).**  `= true`.  The r20 probe DECIDED the residual COUNT: #2043's true residual is ONE wall
— the JAM A per-gap DESCENT composed with the WalkingMonad reconstructed word problem (fib-3-coupled) — NOT two.  The
r13 payload-zip "wall" is DISSOLVED: r16 aligned the SKELETON (`fxAmalg_alignmentVerdictAlignableAtSkeleton`); r20's
probe reduced the PAYLOAD arm to JAM A (`fxAmalg_vcompZipIsJamADescent`: no independent refutation
(`fxAmalg_payloadZipProbeNotRefutable`), no independent proof).  The dispatch theorem = the skeleton fragment (DONE) +
the payload hostage (= JAM A).  The five-arm plan: arm (a) id-collapse DONE (r20 B2); arms (b)/(b') whisker junction
merge MECHANICAL (r21, JAM-B); arm (c) vcomp zip + arm (5) top assembly JAM-A + fib-3 HOSTAGE.  The total canonical
reader is TOTAL at skeleton granularity (`pushoutTotalReaderGatedState`), payload-canonical form the hostage.  The
close criterion is `false` (`pushoutDispatchCloseCriterion_false`); it flips only when arm (c) flips (fib-3).  The four
masters + every walled marker STAY byte-intact at their values; #2043 does NOT close.  `= true`. -/
def fxAmalg_pushout2043DefinitiveState : Bool := true

/-- ★★★ **The ceiling ledger leaves the four masters walled and the close criterion false (`rfl`).**  Machine-checks
the definitive state: the two `false` masters + `fxAmalg_hasSaturatedDispatchTheorem` false + the top-factorization
wall true, the id-collapse shipped, and the close criterion false — every master `Prop` byte-intact, the re-scope in
NEW decls only. -/
theorem ceilingLedgerMastersStayWalled :
    fxAmalg_hasFullSaturatedPushoutDispatch = false
      ∧ fxAmalg_hasGeneralPushoutDispatch = false
      ∧ fxAmalg_hasSaturatedDispatchTheorem = false
      ∧ fxAmalg_topFactorizationInductionStaysWalled = true
      ∧ fxAmalg_hasIdCanonicalCollapse = true
      ∧ pushoutDispatchCloseCriterion = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph.Amalgam

# Roadmap — lean-fx-2

Phasing from skeleton → working kernel → full engine.  Status reflects
**actual** progress as of 2026-05-07; do NOT mark a phase ✅ COMPLETE
unless every sub-task ships zero-axiom AND its strict harness gate
passes inline.  Premature COMPLETE marks are explicitly forbidden per
CLAUDE.md "no half-measures".

## Status legend

* `[x]` — shipped, zero-axiom verified, strict gate passes inline
* `[~]` — partial: foundation shipped, some sub-tasks still open
* `[ ]` — not started
* `(blocked)` — implementation possible but blocked on prerequisite

## Phase 0 — Skeleton ✅ DONE

* [x] Directory layout
* [x] Build configs (lakefile, lean-toolchain, .gitignore)
* [x] Documentation: AXIOMS.md, README.md, ARCHITECTURE.md, ROADMAP.md, MIGRATION.md
* [x] Stub files for all layers with substantial docstrings
* [x] Build green (empty namespace declarations + import wiring)

## Phase 1 — Foundation (Layer 0) ✅ DONE

* [x] `Foundation/Mode.lean` — 10-ctor 2-axis enum (#1297, #1512 advisory)
* [x] `Foundation/RawTerm.lean` — 67 ctors (#1299 D1.6)
* [x] `Foundation/RawSubst.lean` — 67-ctor cascade (#1300 D1.7, no dropNewest)
* [x] `Foundation/Ty.lean` — 25 ctors incl. cubical/HOTT/refine/record/codata/session/effect/modal (#1298 D1.5)
* [x] `Foundation/Subst.lean` — unified singleton (#1301 D1.8)
* [x] `Foundation/Context.lean`
* [x] `Foundation/Action.lean` — typeclass framework (#1471 MEGA-Z1.A)

Acceptance: ✅ build green, AuditAll passes, 7780 audited decls clean.

## Phase 2 — Term (Layer 1) ✅ DONE

* [x] `Term.lean` — 75-ctor raw-aware Term inductive (#1302 D1.9)
* [x] `Term/Rename.lean` (#1303 D1.10)
* [x] `Term/Subst.lean` (#1303 D1.10)
* [x] `Term/Pointwise.lean` (#1304 D1.11)
* [x] `Term/ToRaw.lean` — 75/75 toRaw_X = rfl
* [x] `Term/SubjectReduction.lean` — preserves_isClosedTy (#1307 D2.2, #1308 D2.3)

Acceptance: ✅ Term.toRaw_X = rfl for all 75 ctors; specialized SR for parametric types (#1276 M07).

## Phase 3 — Reduction (Layer 2) — PARTIAL [~]

* [x] `Reduction/Step.lean` — 105 ctors incl. cubical/HOTT/modal (#1310 D2.6, #1311 D2.7)
* [x] `Reduction/StepStar.lean` — RT closure + mapStep
* [x] `Reduction/Conv.lean` — Conv as ∃-StepStar (W10 design baked in)
* [x] `Reduction/ParRed.lean` — 109 ctors (#1312 D2.8)
* [x] `Reduction/RawPar.lean` (#1313 D2.9)
* [x] `Reduction/Compat.lean` — D2.10 (#1314) ✅ COMPLETE (commit 4d15f98, 2026-05-07): all 14 typed cong-rule rename+subst compat lemmas shipped at zero axioms; budget ratcheted 14 → 0.  Compositional pattern (10 rules) + cast-surfacing pattern (oeqFunextCong via `oeqFunextPointwiseType_rename`/`_subst`; pathLamCong via `Ty.weaken_rename_commute`/`_subst`).
* [~] D2.5 cubical β rules (#1309): typed β cascade across 9 sub-tickets, mixed status as of 2026-05-15.
  * ✅ **Shipped**: D2.5.1 `Step.transpBeta` (#1527), D2.5.2 `Step.hcompBeta` (#1528), D2.5.3 `Step.betaGlueElimIntro` IS the typed glueBeta (#1529 verified), D2.5.4 `Step.transpReflBeta` (#1555 — Phase G activation commit cd77f91, full cd cascade arm shipped), D2.5.8 `Step.betaPathReflApp` (#1559).
  * ⏳ **Pending — foundation ready, cascade BLOCKED on #1951 eta-bottleneck**: D2.5.5 `Step.transpPiBeta` (#1556).  All 8 foundation primitives shipped 2026-05-15 across commits b042fde / 4836f0c / 37fd585 / e93efd6 / f54aea8 / e02db5e: `RawRenaming.swap01` + involution + `_lift_lift_commute`; `RawTerm.swap01_rename_lift_lift_commute` + `_subst_lift_lift_commute`; `RawTerm.transpPiBetaContractum` `@[reducible] def` + `_rename` + `_subst`.  Plus Blocker-A (#1945) `UnweakenSubstCommute.lean` ✅, Blocker-C (#1947) subst-compat dispatch ✅.  **Cascade Phases G/H/I rolled back 2026-05-15 (commit 5e57bcf)** after Phase C step 2a dispatcher delegation surfaced a structural eta-bottleneck: `cd_lemma`'s transpPiBeta arm requires discharging `par contractum (cd source)` in the case where cd's `unweaken?` succeeds (slot-1 beta-erased).  The contractum reduces to `lam (app source.weaken (var 0))`, an eta-redex of `source`; without `Step.eta` in the kernel this collapse is impossible.  Per CLAUDE.md warrior-mentality deferral criterion 1 (structurally impossible at current kernel state), shipping requires `Step.eta` first — multi-day cascade adjacent to K18.7 #1891 but on typed LeanFX2 layer.  Foundation lemmas + recognizer (`matchTranspPiBetaShape?` + `_rename`) + `cdTranspPiCase` helper + `transpPiBetaContractum_par_cong` Phase F prep are all KEPT (par-ctor-independent) for future re-attempt.
  * ⏳ **Pending — blocked on kernel ctor**: D2.5.6 `Step.transpSigmaBeta` (#1557) blocked on Blocker-A (#1948 `Term.transpFill` ctor) or Blocker-B (#1949 `Term.transp` redesign), plus Σ-specific Blocker-C (#1950 `RawTerm.fst (RawTerm.pair x y) ⟶ x` at subst0 layer).
  * ⏳ **Pending**: D2.5.7 closed-type transps (#1558).  D2.5.7.1 `RawStep.par.transpListBeta` (#1669) Phase A (~210 LoC: raw ctor + cong + rename + subst compat + transp_inv extension + `rename_eq_listCode_imp` helper) STASHED at `stash@{0}` ("lane-b-transpListBeta-D2.5.7.1-phase-A-raw-cascade").  Phase A is NOT atomic per the original plan — the new ctor forces a `cd_lemma` arm whose discharge requires extending `RawTerm.cdTranspCase` (`Confluence/RawCd/CubicalAndEquiv.lean:36`) with a 75-arm source-dispatch helper (`cdTranspListBetaCase`) so `cd source` reaches a `listCons (transp ...) (transp ...)` reduct.  Total scope ~500-600 LoC.  Diamond closes WITHOUT `Step.eta` because the contractum introduces no fresh binder (unlike D2.5.5).  See `feedback_d257_cd_cascade_blocker.md` memory.  D2.5.7.2-4 (option/either/record) follow same shape, each ~500 LoC.  D2.5.9 `Step.glueAtFace` (#1560 — needs face-system predicate).
  * 🔄 **Original-shared blocker, now scoped to #1556 only**: #1951 cd_lemma dispatch ambiguity from commit 067ed74.  Path 2 split-ctor (recommended on RFC, shipped as commit e64db8f) wires `matchTranspPiBetaShape?` into `cdTranspCase`'s `unweaken? = none` branch with disjoint premises (`unweaken? pathBody = some _` ⇒ `transpReflBeta` priority; `matchTranspPiBetaShape? pathBody = some _` ⇒ `transpPiBeta`).  Phase A/B/C cascade implemented; rolled back as commit 5e57bcf because cd_lemma's transpPiBeta arm has an η-bottleneck (Case I): when `cd` reduces `codomainSource` to interval-independent form, the contractum `λx. transp ... (sourceTarget.weaken @ x)` cannot par-step to `cd source` without `Step.eta`.  Path 2 is therefore **necessary but not sufficient** — it eliminates the dispatch ambiguity but does NOT discharge the contractum's η-redex.  Closure requires `Step.eta` kernel ctor first (multi-day cascade, adjacent to K18.7 #1891).  D2.5.6 (#1557) and D2.5.7.1 (#1669) do NOT share this η-bottleneck (their contractums have no binder); their independent blockers are Term.transpFill #1948 and the `cdTranspListBetaCase` ~500-LoC dispatcher respectively.

Acceptance: rename/subst preserves Step ✅ (raw and typed levels); typed `Step.par.<X>Cong.{rename,subst}_compatible` 14 of 14 done (100%).  Outstanding: D2.5.5-7/9 typed cubical β-rules pending Phase E-K cascade work + shared cd_lemma blocker (#1951).  Not blocking M06 SR or PHASE7-CONV-TRANS since those are cong-rule consumers, not β-rule consumers.

## Phase 4 — Confluence (Layer 3) ✅ DONE (raw-level)

* [x] `Confluence/Cd.lean` (#1316 D3.1)
* [x] `Confluence/CdLemma.lean` (#1317 D3.2)
* [x] `Confluence/Diamond.lean` (#1318 D3.3)
* [x] `Confluence/ChurchRosser.lean` — `RawStep.parStar.confluence` shipped
* [x] `Confluence/CanonicalForm.lean` — `Conv.canonicalRaw` shipped (#1319 D3.4)

Acceptance: ✅ raw-level Tait-Martin-Löf chain ships zero-axiom.  **Partial**: typed `Conv.trans` (#1504 PHASE7-CONV-TRANS) — Phase 1 (chain composition) ✅ shipped 2026-05-08 as `Conv.transChains` / `Conv.trans_via_chains` (`Reduction/Conv.lean` + `Confluence/ConvTrans.lean`).  Full `Conv.trans` (where each Conv brings its own midpoint) still blocked on **strong subject reduction** (term construction via raw-step inversion at typed sources) — M06/M07 ship the type-EQUALITY part of SR but not term construction (~100+ inversion cases).  See `Confluence/ConvTrans.lean`'s docstring for the detailed shipping plan. M06 SR ✅ shipped (`Step.preserves_ty_arrow` at `Term/SubjectReductionGeneral.lean:754` via closed-isClosedTy chain); D2.10 ✅ closed 2026-05-07; typed Cong (#1502 WEAK-FX2-03) requires the same Phase 7 strong SR.

## Phase 5 — Bridge (Layer 4) ✅ DONE

* [x] `Bridge.lean` — `Step.par.toRawBridge` total, no sorries (load-bearing for confluence corollaries)
* [x] Cross-theory bridges: `Bridge/{PathToId,IdToPath,PathIdInverse,IdEqType,PathEqType,PathIdMeta,BoxObservational,BoxCubical}.lean`

Acceptance: ✅ `Step.par.toRawBridge` total; cross-theory bridges ship rfl-fragment claims with explicit scope advisories (#1515).

## Phase 6 — HoTT (Layer 5) ✅ DONE

* [x] `HoTT/Identity.lean`, `HoTT/J.lean` — full dep motive J
* [x] `HoTT/Path/{Composition,Inverse,Groupoid}.lean` (#1325 D3.10)
* [x] `HoTT/Transport.lean`
* [x] `HoTT/Equivalence.lean`, `HoTT/NTypes.lean` (#1320 D3.5)
* [x] `HoTT/Univalence.lean` — Univalence via `Conv.fromStep Step.eqType` (#1321 D3.6, #1437 CUMUL-8.6)
* [x] `HoTT/Funext.lean` — funext via `Conv.fromStep Step.eqArrow` (#1322 D3.7, #1438 CUMUL-8.7)
* [x] `HoTT/HIT/{Spec,Setoid,Eliminator,Examples}.lean` — 7 concrete HITs (#1323, #1324)
* [x] D3.12-ROOT-LABELS (#1576) — every HoTT/HIT/Cubical/Modal/Bridge module now exposes a `## Root status` docstring subsection (Layer / Load-bearing for / Axiom budget); 47 modules labelled across 6 commits 2026-05-08
* [x] D3.6 univalence-β step-rule chain (#1682–#1687) — six sub-phases shipped 2026-05-08/09 covering raw-layer kernel-internal univalence-β rules: S1 (`uaBeta` / `uaBetaDeep`, #1682), S2 (`transpReflId` no-op vs #1555, #1683), S3 (`transpCompose{,Deep}`, #1684), S4 (`idToEquivRefl{,Deep}`, #1685), S5 (`idToEquivCompose{,Deep}`, #1686), S6 (`uaReflEquivApply{,Deep}`, #1687).  Comprehensive rollup audit at `Smoke/AuditD36All.lean` (#1688).
* [x] D3.6-S6 uaToEquiv-of-oeqRefl round-trip (#1687) — shipped 2026-05-09 via `RawStep.par.uaReflEquivApply{,Deep}`: redesigned the rule target to `equivApply (uaToEquiv (oeqRefl X)) arg ⟶ arg` (the identity-equivalence-via-univalence applied to a value yields the value unchanged).  This shape composes cleanly with `uaBetaDeep` because both reductions converge on the argument — the diamond holds.  Cascade through 8 files: RawPar (`uaReflEquivApply{,Deep}` ctors), RawParInversion / RawParRename / RawParCompatible / RawParWeakenInv (cascade arms), RawCd (`cdEquivApplyCase` + `cdUaToEquivApplyCase` 67-arm full enumeration), RawCdDominates / RawCdRename, RawCdLemma (cd_lemma extension via `uaToEquiv_inv` + `oeqRefl_inv`).  Three commits: `2cd91f3` (RawPar+cascade) + `91ddd9a` (cd cascade) + closeout commit (cd_lemma + smoke + audit gates).

Acceptance: ✅ Univalence + funext are real theorems (zero-axiom verified per #1439 CUMUL-8.8); HIT eliminators land via parallel `Step` reductions; D3.6 step-rule chain S1–S6 ships zero-axiom — round-trip-β closure complete.

## Phase 7 — Modal (Layer 6) — NOT STARTED [ ]

* [ ] D4.1 `Modal/TwoLevel.lean` (#1328) — 2LTT structure + Modality + box/diamond
* [ ] D4.2 `Modal/Adjunction.lean` (#1329) — ◇ ⊣ □ basic adjunction
* [ ] D4.3 `Modal/BoxPath.lean` (#1330) — □ commutes with Path/Id
* [ ] D4.4 `Modal/Cohesive.lean` (#1331) — ♭ / ♯ flat + sharp modalities
* [ ] D4.5 full ♭ ⊣ ◇ ⊣ □ ⊣ ♯ adjoint chain (#1332)
* [ ] D4.6 `Modal/Bridge.lean` (#1333) — strict ↔ observational ↔ univalent transfer
* [ ] D4.7 `Modal/{Ghost,Cap,Later,Clock}.lean` (#1334) — 4 FX-application modalities
* [ ] D4.8 `Modal/2LTT.lean` integration tests (#1335)

Acceptance: pending — modal computation rules fire, free theorems extract, 2LTT layering works.

## Phase 8 — Graded (Layer 7) ✅ DONE

* [x] `Graded/Semiring.lean` (#1337 D5.1)
* [x] `Graded/GradeVector.lean` — 21-dim (#1338 D5.2)
* [x] `Graded/Ctx.lean` + `Graded/Rules.lean` — Wood/Atkey 2022 corrected Lam (#1339 D5.3)
* [x] `Graded/AtkeyAttack.lean` — Atkey 2018 attack term REJECTED (#1341 D5.5)
* [x] `Graded/Instances/{Usage,Effect,Security,Lifetime,Provenance,Trust,Repr,Observability,ClockDomain,Complexity,Precision,Space,Overflow,FPOrder,Mutation,Reentrancy,Size,Version,NatResource}.lean` (#1340 D5.4)

Acceptance: ✅ Atkey-2018 witness rejected by corrected Lam rule.

## Phase 9 — Refine (Layer 8) — PARTIAL [~]

* [x] `Refine/Decidable.lean` (#1343 D5.7)
* [ ] `Refine/Ty.lean` + `Refine/Term.lean` extension (#1342 D5.6)
* [ ] `Refine/SMTCert.lean` + `Refine/SMTRecheck.lean` (#1344 D5.8)

## Phase 10 — Algo (Layer 9) — PARTIAL [~]

* [x] `Algo/RawWHNF.lean`, `Algo/RawWHNFCorrect.lean`, `Algo/WHNF.lean`, `Algo/DecConv.lean`
* [x] `Algo/Infer.lean`, `Algo/Check.lean`, `Algo/Synth.lean`, `Algo/Eval.lean`, `Algo/Soundness.lean`, `Algo/Completeness.lean`
* [ ] M03 `Term.eval` reaches WHNF (#1272), M04 strong normalization (#1273), M05 progress (#1274)
* [x] M06 SR at arrow types (#1275) — `Step.preserves_ty_arrow` ships at `Term/SubjectReductionGeneral.lean:754` via the closed-isClosedTy preservation chain (#1276 M07 also done at lines 787, 818); unblocks #1504 PHASE7-CONV-TRANS
* [~] M08 `Term.headStep?` ι coverage (#1277) — 12 per-case ι-rule soundness theorems shipped at `Algo/Soundness.lean` (boolElim×2 lines 70-105, natElimZero/Succ lines 108-122 + 251-267, natRecZero/Succ lines 125-140 + 270-288, listElimNil/Cons lines 190-206 + 291-311, optionMatchNone/Some lines 209-223 + 314-330, eitherMatchInl/Inr lines 333-370) plus the closure theorem `Term.headStep?_sound` (line 395+) covering all canonical-with-payload firings AND `betaFstPair` inline (line 483-504), and the multi-step closure `Term.eval_sound` (line 976+).  Audit-clean per `Smoke/AuditPhase12A3HeadStepPayloadSound.lean` and `Smoke/AuditPhase12A3M08Composition.lean`.  Architectural deferrals (`betaApp` / `betaAppPi` / `betaSndPair` / `pathApp` β) remain blocked on Phase 7.D dep-pattern matching propext-clean infrastructure (per `Algo/Eval.lean` docstring §38-46); a dedicated `Term.headStep?_sound_betaFstPair` per-case theorem is also deferred — adding `Term.headCtor_pair_raw` to `Algo/WHNF.lean` (parallel to the other 11 headCtor-raw bridges) tripped four AuditAll budget gates (GatesShape 1259>1258, GatesAxiomAdj 707>706, GatesBroad 1177>1176, GatesNumOps 847>846) and the project discipline forbids loosening budgets.
* [x] M10 `Algo/Completeness.lean` infer/check completeness (#1279) — full bidirectional surface shipped 2026-05-07: 15 zero-axiom inferable theorems (5 atomic + 5 single-recurse + 5 multi-recurse via `dsimp only + dif_pos rfl` recipe, commits 053dc0e + 6afd940 + 35b7840) plus 15 zero-axiom check-mode counterparts (5 atomic + 2 parametric leaves + 4 single-recurse + 1 multi-recurse + 3 binder via term-mode `dif_pos rfl` and `simp only [Term.check]` recipes, commit a140694); 30 theorems total close the canonical RawTerm fragment that `Algo/Infer` + `Algo/Check` handle deterministically.  Eliminator and HoTT/cubical/modal-primitive check arms remain deferred.

## Phase 11 — Surface (Layer 10) — PARTIAL [~]

* [x] `Surface/{Token,GrammarToken,TokenSchema,TokenInvariants,Lex,SchemaAudit,StdNames,KernelBridge,KernelBridgeReduction,KernelEnv,KernelEnvCorrespondence,Semantics,HostLex}.lean` — token/lex/AST/bridge skeleton
* [x] B01-B07, B11 + B12 partial (#1241-#1247, #1251, #1252 partial)
* [x] L08, L03, L07, L04, C02-C08 (Surface audits) #1206, #1201, #1205, #1202, #1218-#1224
* [x] L04 (#1202) — `Lex.run_offsets_monotonic` ships zero-axiom 2026-05-07 via `lexLoop_token_offsets_bounded` + `lexLoop_preserves_monotonic_offsets` (mirror of L07.5/L07.6 chain) extending through the appended `Token.eof` sentinel via `Array.isMonotonicByOffset_push` (L04.2)
* [ ] L01, L05, L06 (#1199, #1203, #1204)
* [ ] T01-T10 (#1207-#1216)
* [ ] A01-A15 (#1226-#1240) — AST extensions for §3-§18 fx_design coverage
* [ ] H01-H05 (#1289-#1293) — higher-rank
* [ ] P01-P04 (#1281-#1284) — position validity
* [ ] D6.4-6.6 Parse/Print/Roundtrip (#1354-#1356)
* [ ] D6.7-6.9 Elab/ElabSoundness/ElabCompleteness (#1357-#1359)

## Phase 12 — Pipeline (Layer 11) — NOT STARTED [ ]

* [ ] `Pipeline.lean` — D6.12 (#1362) end-to-end String → Tokens → AST → Term → Reduced value

## Day 5 — Sessions / Codata layer ✅ PARTIAL

* [x] D5.11 `Sessions/Foundation.lean` — `SessionProtocol` 5-ctor inductive
  factored out (#1347)
* [x] D5.12 `Sessions/Duality.lean` — dual involution + four named
  dual_cancels_* lemmas (commit 7f6ebca, 2026-05-08)
* [x] `Sessions/Step.lean` — binary protocol-step relation with 6 ctors,
  preserves_isFinite, dual, target_deterministic, of_dual, dual_iff
* [x] `Sessions/Global.lean` — top-down global protocol + projection
  relation
* [ ] D5.x v1.1 — typed-session-step rule lifting protocol advance to the
  Term level (requires graded-mode Ctx tracking + typed Term.sessionSend
  protocol-position update); deferred
* [ ] D5.x v1.1 — bridge `SessionProtocol PayloadType` ↔ `Ty.session
  protocolStep : RawTerm scope` requires fixing PayloadType := RawTerm
  scope or shipping a custom encoding; deferred

Acceptance: ✅ binary session protocol grammar + duality + protocol-step
relation + global projection all ship at zero axioms; AuditSessions.lean
ratchet 30 #assert_no_axioms gates.  Linear-typing claim deferred.

## Day 8 / FX1.Core — minimal lambda-Pi trust anchor ✅ B0 milestone

The minimal lambda-Pi kernel that anchors trust for the FX1/LeanKernel
extension (Day 8 proper).  Ships zero-axiom under
`FX1.check_sound : ∀ env ctx expr ty, Expr.check? env ctx expr ty = true →
HasType env ctx expr ty` at `FX1/Core/Soundness.lean:28-37`.  Coverage:
de Bruijn variables, universes (Sort), Π, lambda, application, constants
(via proved executable environment lookup), bounded weak-head common-reduct
conversion over β + δ.

Sub-items:

* [x] K17.2 `FX1.Name` — hierarchical name inductive (anonymous / str / num)
* [x] K17.3 `FX1.Level` — 5-ctor universe level (zero/succ/max/imax/param)
* [x] K17.4 `FX1.Expr` — 6-ctor minimal expression syntax (bvar/sort/const/pi/lam/app)
* [x] K17.5 `FX1.Declaration` — axiom/def/theorem with release-policy gate
* [x] K17.6 `FX1.Environment` — checked declarations + lookup + well-formedness
* [x] K17.7 `FX1.Context` — de Bruijn-indexed local context
* [x] K17.8 FX1 scope checking — every bvar within context length
* [x] K17.9 FX1 weakening — shift past a cutoff
* [x] K17.10 FX1 renaming — shift / lift / parallel composition correctness
* [x] K17.11 FX1 substitution — `Expr.instantiate` β substitution
* [x] K17.12 FX1 subst identity lemma — `subst id = id`
* [x] K17.13 FX1 subst composition lemma — `(e.subst s1).subst s2 = e.subst (s1 ∘ s2)`
* [x] K17.14 FX1 rename/subst interaction commute
* [x] K17.15 FX1 β substitution lemma — instantiate respects type via context lookup
* [x] K17.16 `FX1.Step` — β + δ reduction relations
* [x] K17.17 `FX1.HasType` — ~12 typing rules for 6-ctor Expr
* [x] K17.18 FX1 environment well-formedness — every declaration typechecks
* [x] K17.19 FX1 context well-formedness — every binding type is a Sort
* [x] K17.20 FX1 β + δ preservation — typing preserved under reduction
* [x] K17.21 `FX1.WHNF` — weak head normal form via β + δ
* [x] K17.22 `FX1.Conv` — definitional equality via β + δ + structural recursion
* [x] K17.23 `FX1.check` — executable proof-carrying type checker
* [x] K17.24 `FX1.check_sound` — HEADLINE soundness theorem zero-axiom
* [x] K17.25 FX1/Core close-out (this section) — B0 bootstrap milestone declared

Acceptance: ✅ `lake build LeanFX2.FX1.Core` green (21 jobs); per-decl
strict harness gates pass under `AuditFX1Core.lean`; `FX1.check_sound` +
`FX1.checkCore_sound` both ship zero-axiom (per `FX1/Core/Soundness.lean`).
B0 trust anchor operational — the FX1/LeanKernel extension (Day 8 proper
below) builds on this foundation.

## Day 8 — Lean kernel modeling (FX1.LeanKernel) ✅ Outcome B (partial scope, zero axioms)

* [x] D8.1 base HasType arms — sort, bvar, const, forallE, lam (#1318
  initial slice)
* [x] D8.6 HasType.app + Expr.instantiate codomain reduction (#1521)
* [x] D8.7-EXTEND HasType.{letE, mdata, litNat, litStrAtom} +
  Expr.{natTypeName, stringTypeName, natType, stringType} primitive name
  helpers (#1524, commits ee3cac8 → 1f4f11b)
* [x] D8.8-EXTEND `Term.check` arms covering all ten HasType arms (#1524)
* [x] D8.9 `check_sound` composition: every check-accepted expression is
  witnessed by HasType (proof composes per-arm soundness)
* [x] D8.10 `FX1/LeanKernel/Audit.lean` reviewer-facing comprehensive
  axiom cone over the 25 load-bearing decls (HasType + 10 arms, Context +
  6 helpers, Environment HasConstant{InList,}, 4 primitive-name helpers,
  check + check_sound) — strict harness gates already cover via
  `AuditFX1LeanKernel_Other.lean` (74 #assert_no_axioms checks)
* [ ] proj — needs Inductive-spec lookup + parameter-substituted field
  type computation; deferred (Outcome B forward path)
* [ ] fvar — needs separate fvar-context + free-variable reindexing;
  deferred (Outcome B forward path)
* [ ] mvar — Lean kernel rejects mvars in fully-elaborated terms; mirror
  policy is "executable checker returns Option.none, no HasType arm";
  deferred unless mvar typing semantics change

Acceptance: ✅ Outcome B — 10 of 13 Expr constructors have HasType arms;
all ship zero-axiom; relational typing remains conservative (missing arms
are monotone, can only enlarge trusted set).  `check_sound` connects
executable Option-valued bidirectional checker to relational HasType for
every accepted shape.  Strict harness gates fail-fast inline on any
axiom regression.

## Phase 13 — Tools (Layer 12) ✅ DONE

* [x] `Tools/AuditGen.lean` — auto-generation tactic (#1365 D7.2)
* [x] `Tools/AuditAll.lean` — generated gates + ~64 sibling files
* [x] `Tools/StrictHarness.lean` — 8 STRICT gates (#1494-#1501)
* [x] `Tools/AuditAll/AuditSurface.lean` — 49 strict gates added (#1531)
* [x] `Tools/AuditAll/AuditConfluence.lean` — RawStep.parStar.confluence (#1508)
* [ ] `Tools/Tactics/{Cast,HEq,SimpStrip}.lean` — D7.3 (#1366)

Acceptance: ✅ 7780 audited decls clean inline; AuditAll auto-extends via namespace sweep.

## Phase 14 — Smoke + Documentation (cross-cutting) — PARTIAL [~]

* [x] Per-layer `Smoke/Audit*.lean` files with concrete examples
* [x] AXIOMS.md zero-axiom commitment (#1367 D7.4)
* [x] ROADMAP.md (this) — accurate status, no premature COMPLETE
* [ ] D7.6 MIGRATION.md final
* [ ] D7.7 README.md final v1.0 release notes (#1370)
* [ ] D7.8 fx_design.md cross-reference (#1371)
* [ ] D7.9 Smoke comprehensive (#1372)
* [ ] D7.10 final integration tests (#1373)

## Phase 15 — Cutover (deferred) [ ]

* [ ] Verify lean-fx-2 has feature parity with lean-fx
* [ ] Move `lean-fx/` → `lean-fx.deprecated/` (#1369 D7.6)
* [ ] Move `lean-fx-2/` → `lean-fx/`
* [ ] Update parent project imports
* [ ] D7.11 v1.0 git tag (#1374)

**Cutover gating**: Phase 15 NOT to fire until Phases 7 (modal),
Phase 9-12 debt is closed AND M06 SR / typed Conv.trans / Phase 7
SR work is shipped.  D2.10 Compat (14 typed cong rename+subst
lemmas) ✅ closed 2026-05-07 — no longer a cutover blocker.
Premature cutover would orphan the lean-fx codebase before
lean-fx-2 reaches feature parity.

## unblock-E Family — kernel-extension matrix (CONVTRANS-C universal chain)

CONVTRANS-C Phase A1 (#1734) ships `lift_full_term` as a
`DispatchAtom`-gated dispatcher over Term ctors.  5 leaves remain
structurally blocked on missing typed `Step.par` β kernel rules
(unblock-A.leaf.{equivApply, appPi, transp, hcomp, hcompPath} =
#2013–#2017).  Family E ships those kernel extensions, then closes
the leaves and drops the `DispatchAtom` gate.

### Leaf-by-leaf coverage

| Leaf | Blocker | TypedCtor | Cascade | Close | LoC |
|------|---------|-----------|---------|-------|-----|
| #2013 equivApply | typed `Step.par.uaReflEquivApply{,Deep}` | #2057 | #2058 | #2059 | ~600 |
| #2014 appPi | typed `Step.par.piEta` η bridge | #2060 | #2061 | #2062 | ~1100 |
| #2015 transp | 5 typed deep+ua+compose β arms | #2063 | #2064 | #2065 | ~1300 |
| #2016 hcomp | vacuity via TermPathLamExcludes + path-typed extension | (vac) #2066 ✅ | #2067 ← #2069 | (vac) | ~350 |
| #2017 hcompPath | relax `Step.par.hcompBeta` + add `hcompBetaDeep` | #2068 | (folded) | #2069 | ~600 |

#2066 unblock-E.hcomp.ClosedCarrier shipped 2026-05-22 at commit
`cf43720b` via Term.pathLam_excludes_closedTy vacuity (no new
kernel β ctor required).  Path-typed carrier (#2067) routes
through Term.hcompPath once #2068/#2069 ship.

### Close-out chain

After all 5 leaves close: drop the `DispatchAtom` restriction
(#2070, parallels #2018), ship `Step.parStar.invertRaw` chain
induction headline (#2072, parallels #2019), final CONVTRANS-C
audit + downstream migration (#2073, parallels #2020).

### Parallelization

#2057/#2060/#2063/#2068 are independent kernel extensions with no
inter-family cascade dependencies — perfectly parallelizable
across sibling sessions.  #2067 hcomp.PathCarrier waits on #2069
hcompPath.Close since path-typed hcomp routes through the new
hcompPath β rules.

### Downstream consumers unblocked

* CONVTRANS-C #1734 → #1735 typed `Conv.trans` → #1736 audit
* strength-T5 #1961 (par-back form #2022) ← already shipped raw
  injectivity headline #2021 (`RawStep.par.rename_inj_inv`)
* strength-T6 #1962 / T7 #1963 → K12.27 SN, K12.28 β-η-CR
* D2.5 cubical cascade (D2.5.5–9) ← shares Step.eta blocker
  with the broader Geuvers 1992 lift in unblock-D.geuvers (#2038)

## Critical-path summary (v1.0 requirements)

The v1.0 milestone ("100% proven kernel") gates on:

1. **D2.10 #1314** ✅ DONE 2026-05-07 — typed Step.par cong rename+subst compat (14 of 14 shipped, budget ratcheted to 0)
2. **M06 #1275** ✅ DONE — Phase 7 subject reduction at arrow types (`Step.preserves_ty_arrow` at `Term/SubjectReductionGeneral.lean:754`)
3. **PHASE7-CONV-TRANS #1504** — typed `Conv.trans`: Phase 1 ✅ shipped 2026-05-08 (`Conv.transChains` / `Conv.trans_via_chains` zero-axiom, chain-composition flavor); full unrestricted `Conv.trans` still requires Phase 7 strong subject reduction (term construction via raw-step inversion at typed sources, ~100+ ctor-by-ctor cases — see `Confluence/ConvTrans.lean`)
4. **K07.1-8 #1516-1523** — dep-motive eliminator refactors (8 ctors)
5. **D2.5 typed cubical β cascade** — D2.5.1 #1527 ✅, D2.5.2 #1528 ✅, D2.5.3 #1529 ✅ verified, D2.5.4 #1555 ✅ (Phase G activation), D2.5.8 #1559 ✅.  Pending: D2.5.5 #1556 (foundation + Path 2 dispatch infrastructure shipped 2026-05-15; cascade rolled back 2026-05-15 on cd_lemma Case I η-blocker — see #1951; resolution requires `Step.eta` kernel ctor, multi-day cascade), D2.5.6 #1557 (blocked on Term.transpFill #1948, INDEPENDENT of #1951's η-blocker — Σ contractum has no binder), D2.5.7 #1558 (D2.5.7.1's contractum has no binder either; blocker is a separate ~500-LoC `cdTranspListBetaCase` dispatcher extension), D2.5.9 #1560.
6. **WEAK-FX2-03 #1502** — retire 121 manufactured-witness wrappers
7. **D4 modal layer** — full ♭⊣◇⊣□⊣♯ adjoint chain

Each item has its own task in the tracker; the dashboard
(`#audit_debt_dashboard`) reports load-bearing debt counts.

## Estimated agent budget (revised)

* Phase 0-3 (kernel + skeletal Reduction): ✅ done (lean-fx D-series)
* Phase 4-6 + 8 (Confluence, Bridge, HoTT, Graded): ✅ done
* Phase 9-13 (partial): ~3-4 agent runs to close
* Phase 7 modal: ~2-3 agent runs
* D2.10 completion: ✅ done 2026-05-07 (14/14 cong-rules shipped at zero axioms in 7 batched commits ending at 4d15f98)
* Phase 11/12 surface + pipeline: ~5-7 agent runs
* Cutover: ~1-2 agent runs

This is comparable to the lean-fx Wave 8 confluence project's effort
(~25 commits) but delivers a *complete* engine instead of just the
typed Church-Rosser chain.

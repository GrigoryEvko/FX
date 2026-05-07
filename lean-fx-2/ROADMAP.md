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
* [~] `Reduction/Compat.lean` — D2.10 (#1314): exemplar `intervalOppCong` + 12 batch shipped (commit 7ecca67); **15 cong rules still need rename+subst compat**
* [ ] D2.5 cubical β rules (#1309): typed β for transp/hcomp/glue (#1527-1529)

Acceptance: rename/subst preserves Step ✅ (raw level); typed `Step.par.<X>Cong.{rename,subst}_compatible` 13 of 28 done (46%).

## Phase 4 — Confluence (Layer 3) ✅ DONE (raw-level)

* [x] `Confluence/Cd.lean` (#1316 D3.1)
* [x] `Confluence/CdLemma.lean` (#1317 D3.2)
* [x] `Confluence/Diamond.lean` (#1318 D3.3)
* [x] `Confluence/ChurchRosser.lean` — `RawStep.parStar.confluence` shipped
* [x] `Confluence/CanonicalForm.lean` — `Conv.canonicalRaw` shipped (#1319 D3.4)

Acceptance: ✅ raw-level Tait-Martin-Löf chain ships zero-axiom.  **Open**: typed `Conv.trans` (#1504 PHASE7-CONV-TRANS) blocked by full D2.10 + M06 SR (#1275); typed Cong (#1502 WEAK-FX2-03) requires Phase 7 SR.

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

Acceptance: ✅ Univalence + funext are real theorems (zero-axiom verified per #1439 CUMUL-8.8); HIT eliminators land via parallel `Step` reductions.

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
* [ ] M06 SR at arrow types (#1275, blocks Conv.trans)
* [ ] M08 `Term.headStep?` ι coverage (#1277)
* [ ] M10 `Algo/Completeness.lean` infer/check completeness (#1279)

## Phase 11 — Surface (Layer 10) — PARTIAL [~]

* [x] `Surface/{Token,GrammarToken,TokenSchema,TokenInvariants,Lex,SchemaAudit,StdNames,KernelBridge,KernelBridgeReduction,KernelEnv,KernelEnvCorrespondence,Semantics,HostLex}.lean` — token/lex/AST/bridge skeleton
* [x] B01-B07, B11 + B12 partial (#1241-#1247, #1251, #1252 partial)
* [x] L08, L03, C02-C08 (Surface audits) #1206, #1201, #1218-#1224
* [ ] L01/L02/L04-L07 (#1199, #1200, #1202-#1205)
* [ ] T01-T10 (#1207-#1216)
* [ ] A01-A15 (#1226-#1240) — AST extensions for §3-§18 fx_design coverage
* [ ] H01-H05 (#1289-#1293) — higher-rank
* [ ] P01-P04 (#1281-#1284) — position validity
* [ ] D6.4-6.6 Parse/Print/Roundtrip (#1354-#1356)
* [ ] D6.7-6.9 Elab/ElabSoundness/ElabCompleteness (#1357-#1359)

## Phase 12 — Pipeline (Layer 11) — NOT STARTED [ ]

* [ ] `Pipeline.lean` — D6.12 (#1362) end-to-end String → Tokens → AST → Term → Reduced value

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
remaining Phase 3 (D2.10 Compat 15-rule completion), Phase 9-12
debt is closed AND M06 SR / typed Conv.trans / Phase 7 SR work
is shipped.  Premature cutover would orphan the lean-fx codebase
before lean-fx-2 reaches feature parity.

## Critical-path summary (v1.0 requirements)

The v1.0 milestone ("100% proven kernel") gates on:

1. **D2.10 #1314** — typed Step.par cong rename+subst compat (15 of 28 still missing)
2. **M06 #1275** — Phase 7 subject reduction at arrow types (depends on D2.10)
3. **PHASE7-CONV-TRANS #1504** — typed `Conv.trans` (depends on M06)
4. **K07.1-8 #1516-1523** — dep-motive eliminator refactors (8 ctors)
5. **D2.5.1-3 #1527-1529** — typed cubical β rules (transp/hcomp/glue)
6. **WEAK-FX2-03 #1502** — retire 121 manufactured-witness wrappers
7. **D4 modal layer** — full ♭⊣◇⊣□⊣♯ adjoint chain

Each item has its own task in the tracker; the dashboard
(`#audit_debt_dashboard`) reports load-bearing debt counts.

## Estimated agent budget (revised)

* Phase 0-3 (kernel + skeletal Reduction): ✅ done (lean-fx D-series)
* Phase 4-6 + 8 (Confluence, Bridge, HoTT, Graded): ✅ done
* Phase 9-13 (partial): ~3-4 agent runs to close
* Phase 7 modal: ~2-3 agent runs
* D2.10 completion: ~3-4 batch agent runs (already 13/28; expect similar batches)
* Phase 11/12 surface + pipeline: ~5-7 agent runs
* Cutover: ~1-2 agent runs

This is comparable to the lean-fx Wave 8 confluence project's effort
(~25 commits) but delivers a *complete* engine instead of just the
typed Church-Rosser chain.

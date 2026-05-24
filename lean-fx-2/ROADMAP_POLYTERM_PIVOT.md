# Roadmap — Accelerate Path Rethought Under PolyTerm Pivot

> **Status:** active.  Created 2026-05-23 as the operational
> reconfiguration of the accelerate-* roadmap under the PolyTerm
> architectural pivot.  Replaces the per-phase task structure in
> `ROADMAP.md` for everything past commits `7d6758a9` (P2.3 substrate)
> and `ca101887` (polycell.md design doc).  Pre-pivot roadmap kept
> in `ROADMAP.md` for historical reference.
>
> **Design reference:** `polycell.md` (2259 lines, ten-axis substrate).
> **Literature reference:** `reference_loubaton_papers.md` memory.
>
> **Pivot decision posture:** SOFT pivot — start POLY-α immediately as
> parallel work, do NOT tear down current FX kernel.  POLY-α
> deliverables ship as atomic increments; each can be reverted if
> a wall hits.  Full pivot commits only when POLY-α validates the
> approach (~month 3-6).

---

## The decision

### What we are doing

1.  **Pivot the substrate.**  Long-term destination is the
    ten-axis `PolyTerm π dim source target` per polycell.md.
    FX kernel becomes one profile instance.  Cascade tax disappears.
    Conv decidable via ωcE.  Univalence structural.
2.  **Start POLY-α immediately**, as atomic shippable Lean files,
    NOT as a 6-month design phase.  Every commit lands zero-axiom
    and independently useful.
3.  **De-risk in this order**: CellShape → Stratification → ωcE
    → bridge to existing Conv.  Each step makes the next more
    confident.  If any step hits a wall, abandon the pivot
    gracefully and stay on current substrate.
4.  **Keep the current kernel running** in parallel.  No tearing
    down, no big-bang migration.  Tier-1 unblockers continue to
    ship under the current substrate as they're needed.
5.  **Cancel ~30 of the 50 accelerate-* tasks** with explicit
    "subsumed by PolyTerm POLY-X" annotations.  Don't waste
    effort on tasks the pivot makes obsolete.

### What we are NOT doing

1.  **NOT** a big-bang substrate replacement.  The migration
    in POLY-η is a 6-month staged rollout, not a single commit.
2.  **NOT** a 6-month design phase before any code ships.
    POLY-α has shippable atomic increments starting week 1.
3.  **NOT** delaying MILESTONE A.  POLY-α delivers decidable Conv
    in ~3 weeks via ωcE morphism search, faster than the
    NbE-based path (#2132 P3.12).
4.  **NOT** building all ten axes upfront.  POLY-α ships only
    axes 1+3+9 (the minimum for decidable Conv).  Axes 2+4-8+10
    ship in POLY-β through POLY-ε over months 6-24.
5.  **NOT** committing to the full 36-month rollout before
    POLY-α validates the approach.  Real go/no-go decision point
    is end of POLY-α, ~month 3.

---

## Tier 0 — POLY-α immediate ship (weeks 1-3, ~6K LoC, 6 commits)

These six commits land POLY-α MVP.  Each is independently useful
and zero-axiom.  Each ships its own smoke audit.

### Commit 1: `Foundation/Polygraph/CellShape.lean`

**Week:** 1, days 1-2.  **LoC:** ~800.  **Audit:** 10 `#assert_no_axioms`.

The shape catalogue inductive: `globular`, `cubical`, `simplicial`,
`opetopic`, `theta`, `steiner`, `reedy`, `hda`, `prod`, `wreath`.
Each has its own boundary/parallelism combinatorics encoded
as separate inductives (`Opetope`, `ThetaCell`, `ParityComplex`,
`HDACube`, `GenReedy`).  `deriving DecidableEq` clean per
per-shape ctor enumeration.

**Acceptance:** `lake build LeanFX2.Foundation.Polygraph.CellShape`
zero-axiom + `Smoke/AuditCellShape.lean` green.

**Dependencies:** none (greenfield foundation).

**Risk:** none — pure data, no propext exposure.

### Commit 2: `Foundation/Polygraph/Stratification.lean`

**Week:** 1, days 3-4.  **LoC:** ~600.  **Audit:** 6 `#assert_no_axioms`.

The `Stratification` structure per Henry-Loubaton 2301.11424 §2.2:
per-cell per-dim thinness predicate with closure axioms
(`identitiesAreThin`, `closedUnderComp`, `closedSrcTgt`).
Decidability instance field.  Minimal Saturation enum
(`minimal`, `oneTrivial`, `nTrivial`, `omegaSat`).

**Acceptance:** structure compiles zero-axiom; example
instantiations for identity-only and all-thin saturations.

**Dependencies:** CellShape (commit 1).

**Risk:** medium — the closure axioms must be propext-clean per
the recipe in `feedback_lean_zero_axiom_match`.  Mitigation:
encode each axiom as explicit Prop with `nomatch`-style
discharge for impossible cases.

### Commit 3: `Foundation/Polygraph/OmegacE/Construction.lean`

**Week:** 1 day 5 + week 2 days 1-3.  **LoC:** ~1.5K.  **Audit:** 8 `#assert_no_axioms`.

The HLOR 2404.14509 Construction 1.22 build of `ωcE^(k)`:

```lean
inductive OmegacE_at : Nat → Type where
  | atom0     : Vertex 0 → OmegacE_at 0
  | q1cell    : OmegacE_at 1
  | extend    : OmegacE_at k → OmegacE_at (k+1)
  | alphaCell : OmegacE_at k → OmegacE_at (k+1)
  | betaCell  : OmegacE_at k → OmegacE_at (k+1)
```

Plus colim-over-Nat for `OmegacE` itself, plus the suspension
operator `Σ : OmegacE_at k → OmegacE_at (k+1)`, plus the
pushout-via-explicit-construction (no Lean colim machinery
because that pulls propext).

**Acceptance:** all ctors typecheck zero-axiom; explicit
truncation `truncate (k : Nat) : OmegacE → OmegacE_at k`
ships zero-axiom; smoke audit shows each `OmegacE_at k` is
finite-type for `k ≤ 5` (extends to all k by induction).

**Dependencies:** CellShape, Stratification.

**Risk:** medium-high — Construction 1.22's "ω-step colimit"
requires careful encoding.  Mitigation: avoid Lean's
`Quotient` / `Quot.mk` machinery (propext); use explicit
`Nat`-indexed sequence + structural recursion.

### Commit 4: `Foundation/Polygraph/OmegacE/UniversalProperty.lean`

**Week:** 2, days 4-5 + week 3 day 1.  **LoC:** ~1K.  **Audit:** 4 `#assert_no_axioms`.

HLOR Proposition 1.26 in Lean:

```lean
def IsCoherentEquiv (π : PolyProfile) (dim : Nat)
    (a : PolyTermStub π dim) : Prop :=
  ∃ (φ : PolygraphMor (suspendIter (dim-1) OmegacE) (PolyTermStub π)),
    a = φ.factorThrough (suspendIter (dim-1) .f)
```

Plus the decidability instance via polygraph-morphism search
(finite-type because ωcE_at k is finite-type at each k).

**Acceptance:** `IsCoherentEquiv` typechecks zero-axiom;
`Decidable (IsCoherentEquiv π dim a)` instance ships
zero-axiom for any `a` of bounded depth.

**Dependencies:** Stratification, OmegacE/Construction.

**Risk:** medium — search performance may be exponential in
worst case.  Mitigation: bounded search depth + timeout
fallback, plus the pragmatic observation that FX kernel
terms are bounded depth in practice.

**Note:** `PolyTermStub π` is a temporary placeholder type — the
full PolyTerm ships in POLY-ζ.  For POLY-α we use a thin
shim that wraps existing `Term` / `Step` types, demonstrating
the universal property holds on the current kernel.

### Commit 5: `Reduction/ConvViaOmegacE.lean`

**Week:** 3, days 2-4.  **LoC:** ~1.5K.  **Audit:** 6 `#assert_no_axioms`.

The new Conv definition wired through ωcE:

```lean
def ConvViaOmegacE {mode level scope} {ctx : Ctx mode level scope}
    {ty : Ty level scope} (a b : Term ctx ty _) : Prop :=
  IsCoherentEquiv fxStubProfile 1 (Step.bundle a b)

instance ConvViaOmegacE.decide : Decidable (ConvViaOmegacE a b) := ...
```

Plus the bridge theorem:

```lean
theorem ConvViaOmegacE.iff_existing :
    ConvViaOmegacE a b ↔ Conv a b := ...
```

The bridge is non-trivial (~600 LoC of Lean) because it must
show: a polygraph morphism from `Σ^0(ωcE)` factoring `(a, b)`
exists iff there's a `StepStar` zigzag.  This is essentially
the HLOR Theorem 1.33 contractibility result applied to FX
specifically.

**Acceptance:** the iff lemma ships zero-axiom; existing FX tests
that use `Conv` keep passing with `ConvViaOmegacE` as a
drop-in replacement.

**Dependencies:** OmegacE/UniversalProperty, existing Conv.

**Risk:** high — this is the load-bearing soundness theorem.
If it fails to discharge zero-axiom, POLY-α has not succeeded
and we re-evaluate.  Mitigation: prove the easy direction
first (`ConvViaOmegacE → Conv` via explicit witness
extraction); the hard direction (`Conv → ConvViaOmegacE`)
follows from finite-type polygraph completeness.

### Commit 6: POLY-α audit milestone

**Week:** 3, day 5.  **LoC:** ~500 (mostly smoke + docs).

Aggregate smoke audit verifying all five POLY-α files ship
zero-axiom under `LeanFX2Audit`.  Documentation update in
`ROADMAP.md` marking POLY-α complete.  Update memory entry
`project_polyterm_pivot_α_complete.md`.

**Acceptance:** **★ MILESTONE A reached** — FX has decidable
typecheck via ωcE-based Conv.

---

## Tier 1 — critical unblockers under current substrate (parallel, ~1 week)

These ship under the current Step/Term substrate because they unblock
immediate downstream work AND are too atomic to wait for POLY-α
migration.  Each is ~1 day.

### #2110 P0.11 — `Step.iotaOeqJRefl`

**LoC:** ~80.  **Cascade:** none (template `iotaIdJRefl` already exists at `Step/Inductive.lean:742`).

Add the ι-rule `oeqJ baseCase (oeqRefl _) ⟶ baseCase` to the typed
Step inductive.  Pattern after `Step.iotaIdJRefl` at line 742.

**Unblocks:** #1632 `Term.oeqJ_oeqRefl_steps`.

**Pivot fit:** STAYS as Step ctor under current substrate; becomes
Generator value at dim 1 under PolyTerm migration.  No cascade
work needed.

### #2109 P0.12 — `Term.emptyElim`

**LoC:** ~60.  **Cascade:** ~200 (added to Term, RawTerm, Subst).

Add bottom-type eliminator (absurd / exFalso) to typed Term.
Reasonable but cascading addition.

**Pivot fit:** STAYS as Term ctor; becomes Generator value at
dim 0 under PolyTerm migration.

**Decision:** SKIP unless explicitly demanded — under PolyTerm,
`emptyElim` becomes one Generator entry without cascade.
Adding it now then deleting cascade entries during migration
is wasted work.

### Delete K11.8/K11.9 fake mirrors

**LoC:** ~960 deleted (256 `RawPolyTerm.lean` + ~700 `PolyTerm.lean`).

User-approved earlier (Path A "delete the fake mirrors").  Also
delete:
- `Foundation/Polygraph/PolyTermAction.lean` + `PolyTermAction/`
- `Foundation/Polygraph/PolyTermRoundtrip.lean`
- `Foundation/Polygraph/RawPolyTermFlatToLegacy.lean` (today's
  commit 936fa7d4 — bridges to fake target)
- `Smoke/AuditPolyTerm*.lean` + matching smoke audits

**Acceptance:** `lake build LeanFX2` still green after deletion;
no downstream imports break (verified by grep).

**Pivot fit:** Required cleanup before POLY-α work depends
on substrate.

### Update task tracker

Close #2125 P2.4, #2126 P2.5, #2127 P2.8, #2128 P3.1,
#2129 P3.2, #2130 P3.4, #2131 P3.5 as **CANCELLED — subsumed by
PolyTerm POLY-X** with explicit pointer to polycell.md section.

Close #2132 P3.12 as **REDIRECTED** to POLY-α commit 5 (decidable
Conv via ωcE).

Mark task #2124 P2.3 as **COMPLETE** (substrate shipped at
commit 7d6758a9; bridge is now in scope of POLY-α not P2.5).

---

## Tier 2 — CANCELLED tasks (29 tasks)

Marked CANCELLED-by-PolyTerm with explicit subsumption pointer.

### Phase P2 polygraph (5 cancelled)

| Task | Cancelled because |
|---|---|
| #2125 P2.4 PolyTerm intrinsic mirror | polycell.md §5: FXTerm is a view definition on FXCell, no separate inductive |
| #2126 P2.5 PolyTerm.toRawPoly_rfl | Subsumed by POLY-α commit 4 + commit 5 (the bridge IS the erasure) |
| #2127 P2.8 PolyTerm rename/subst | Subsumed by POLY-β AXIS 2 (polynomial monad multiplication) |
| (K11.8 RawPolyTerm) | Already CANCELLED (fake mirror) — deleted in Tier 1 |
| (K11.9 PolyTerm) | Already CANCELLED (fake mirror) — deleted in Tier 1 |

### Phase P3 metatheory (8 cancelled)

| Task | Cancelled because |
|---|---|
| #2128 P3.1 PolyTerm.subject_reduction | polycell.md §6: SR is profile-level theorem under saturation discipline |
| #2129 P3.2 PolyTerm.strong_normalization | polycell.md §6: SN is profile-level theorem |
| #2130 P3.4 PolyStep dim-1 generators | polycell.md §3.2: dim-1 cells of PolyTerm via AXIS 2 |
| #2131 P3.5 PolyStep.cd/cd_lemma generic | polycell.md §3.4: subsumed by AXIS 4 saturation closure |
| #1788 P3.6 RawValueTerm | polycell.md §6: values are NF predicates on PolyTerm |
| #1789 P3.7 ValueTerm typed mirror | polycell.md §6: ditto |
| #1793 P3.8 PolyTerm.eval | polycell.md §3.6: eval = polygraph fold via AXIS 6 |
| #1804 P3.9 ValueTerm.quote | polycell.md §3.6: quote = inverse fold |
| #1805 P3.10 nbe roundtrip | polycell.md §3.6: roundtrip from fold/unfold |
| #1807 P3.11 Conv.decide via NF | polycell.md §3.9: subsumed by POLY-α ωcE morphism search |
| #2132 P3.12 typecheck_decidable | **REDIRECTED** to POLY-α commit 5 (faster path) |

### Phase D2.5.x cubical β cascade (10 cancelled)

| Task | Cancelled because |
|---|---|
| #1651-1657 D2.5.5 transpPi (E/F/G/H/I/J/K) | polycell.md §3.1: cubical β is topos op on cubical-shape cells (AXIS 7) |
| #1658-1668 D2.5.6 transpSigma (A-K) | Same |
| #1669-1673 D2.5.7 transp{List,Option,Either,Record} | Same |
| #1675 D2.5.9 glueAtFace | Same |
| #1561 D2.5-CASCADE per-rule extension | Same |

### Phase CUMUL-7 modal cross cascade (8 cancelled)

| Task | Cancelled because |
|---|---|
| #1427-1430, 1689-1698 CUMUL-7.x | polycell.md §3.7: modal topos handles cumul + cross-mode definitionally |

### Phase K20 self-hosting (deferred not cancelled)

K20.x FX-in-FX tasks are NOT cancelled but DEFERRED to post-POLY-η.
Self-hosting works better against a stable PolyTerm-based kernel
than against the current cascading substrate.

---

## Tier 3 — KEEP as POLY-X subwork (months 1-36)

These tasks stay in scope but get redirected to be PolyTerm-axis
deliverables.

### Phase 0 SN chain (10 keep)

These STAY because PolyTerm needs SN proven for the fxProfile.  But
the proof migrates from per-ctor (current) to generic over Generator
(POLY-β onwards).

| Task | New scope |
|---|---|
| #1963 P0.3 Reducible.rename_equivariant | Becomes per-axis-2 polynomial-monad equivariance theorem |
| #1926 P0.4 Reducible.cr3 + U2 | Becomes profile-level CR3 theorem (one per saturation) |
| #1927 P0.5 ReducibleSubst.lift | Becomes axis-2 multiplication-respects-saturation |
| #1928 P0.6 fundamental_lam | Wood/Atkey 2022 — applies at AXIS 2 algebra (Lam case) |
| #1778 P0.7 fundamental_betaRedex | Per-Generator dispatch (axis 2 + axis 4 closure) |
| #1779 P0.8 fundamental_iota | Per-Generator dispatch |
| #1781 P0.9 fundamental_cubical_modal_advanced | AXIS 1 (cubical shapes) + AXIS 7 (modal topos) |
| #1782 K12.25 modal cases | AXIS 7 (modal topos handles 8-modality dispatch) |
| #1783 K12.26 cumulUp/refine/type-code/session/effect | AXIS 7 + AXIS 10 (universe cells) |
| #1784 P0.10 strong_normalization (M04) | Profile-level theorem; one proof per profile |

### Phase 1 Allais kit (2 keep, 4 deferred)

| Task | Status |
|---|---|
| #2117 P1.3 SubstHet Action | KEEP as axis-8 fibration field |
| #2118 P1.4 Term.act / Term.fold | KEEP as axis-2 polygraph fold |
| #2119 P1.5 act_id / act_comp | KEEP — polynomial-monad laws |
| #2120 P1.6 strength-cleanup | DEFER until POLY-β ships axis 2; then deletes ~5-8K LoC of commute ladders |
| #1745 P1.1 Renaming Action | ✅ SHIPPED |
| #2116 P1.2 Subst Action | ✅ SHIPPED |

### Phase 2 Generator-coded polygraph (8 shipped/redirected)

| Task | Status |
|---|---|
| #2121 P2.0 outputType spike | ✅ SHIPPED (commit 2eb49d31) |
| #2122 P2.1 Generator enum + arity | ✅ SHIPPED (commit bb2e7e2d) |
| #2123 P2.2 outputType shape-function | ✅ SHIPPED (commits 51011e51..36d592e9) |
| #2124 P2.3 RawPolyTermFlat substrate | ✅ SHIPPED today (commit 7d6758a9) |
| P2.4-P2.8 | CANCELLED (Tier 2) |

### Phase 4 math layer (DEFERRED to post-POLY-ζ)

| Task | Decision |
|---|---|
| #1263 P4.3 quotMk/quotRec | DEFER — needs AXIS 3 stratification stable first |
| #2133 P4.4 push HIT | DEFER |
| #2134 P4.5 trunc HIT | DEFER |
| #2135 P4.6 polyMu/polyNu | DEFER until AXIS 2 polynomial monad ships |
| #2136 P4.7 measure theory | DEFER |
| #2137 P4.8 SDG | DEFER |
| #2138 P4.9 cgef_obligation_bundle | DEFER (the "engine keystone" is now PolyTerm itself) |

### Phase 5 distribution (DEFERRED)

| Task | Decision |
|---|---|
| #2139 P5.1 evalDistributed_sound | DEFER until POLY-γ ships axis 6 Gray module |
| #1808-1822 P5.2/K14.x EGraph | DEFER until POLY-α ships and substrate stabilizes |

### Reducibility (K12.x) — keep, restructure

| Task | New scope |
|---|---|
| K12.20.U1-U5 (CR3 / Reducible internals) | KEEP under POLY-β; become axis-2 + axis-4 per-profile theorems |
| K12.27 (strong_normalization headline) | KEEP — same as P0.10 |
| K12.28 (β-η critical pair joinability) | KEEP via Geuvers 1992 — applies at axis-4 saturation |
| K12.29 (Tait audit + Era S close) | KEEP — becomes the per-profile SN closure proof |
| K12.30 (Atkey 2018 attack regression) | KEEP — security test against the Lam-rule corruption |

### CONVTRANS chain — REDIRECTED

| Task | Status |
|---|---|
| #1734 P3.3 Step.parStar.confluent | DEFER until POLY-α ships; then becomes axis-4 closure corollary |
| #1735 CONVTRANS-D Conv.trans typed headline | **REDIRECTED**: under POLY-α, Conv.trans is composition of polygraph morphisms (definitional, ~50 LoC) |
| #1736 CONVTRANS-Audit | REDIRECTED to POLY-α audit milestone (commit 6) |

### strength-T chain — keep most, redirect cascades

| Task | Status |
|---|---|
| T1, T2, T3 ✅ SHIPPED | — |
| T4-{closed,binder,parametric,id,cubical,advanced} ✅ SHIPPED | — |
| #1961 T5 Step.par.preserves_rename_image | KEEP — becomes axis-2 polynomial multiplication preserves shape |
| #1962 T6 Conv.rename_equivariant | REDIRECTED — under POLY-α, Conv-via-ωcE is equivariant by construction (axis 9) |
| #1964 T8 subst0_rename_commute ✅ SHIPPED | — |
| T9-T12 series (η-image recognizers) ✅ SHIPPED | — |
| T13-T17 (K13/K14/K15/K17-19 future bridges) | KEEP but become POLY-ζ migration tasks |
| #1977 T18 Conv.decide via NF | **REDIRECTED** to POLY-α commit 4-5 (ωcE-based) |

### unblock-* chains — keep ongoing, integrate with POLY-α

| Task family | Status |
|---|---|
| unblock-A.* dispatch arms (16 shipped) | ✅ COMPLETE |
| unblock-A.universal (#2018) | KEEP — small atomic ship |
| unblock-A.chain (#2019), audit (#2020) | KEEP — close before POLY-α migration |
| unblock-B.t5.* (#2022-2026) | KEEP — directly feed axis-2 polynomial monad |
| unblock-C.t6.* (#2029-2034) | KEEP — feed axis-9 (Conv.rename_equivariant becomes free under POLY-α) |
| unblock-D.* (#2035-2044) | KEEP — feed POLY-α Conv bridge |
| unblock-E.* (#2070-2073) | KEEP — small atomic shps |

---

## Tier 4 — explicit ABANDON (not now)

Per polycell.md §12 risk register, these are flagged as
research-frontier-with-no-mitigation if hit head-on.  We do
NOT attempt them until POLY-δ stabilizes.

| Idea | Why abandoned now |
|---|---|
| Per-cell polynomial monad parameters (one monad per Generator) | Loubaton frame doesn't support; would require novel research |
| Multi-axis stratification (thinness varying by shape + by sortFamily) | Verity Theorem 2.4 only handles per-cell; per-(shape, sort) is open |
| Profile-of-profiles depth > ω | Cisinski ω-loc is the limit; beyond needs un-published research |
| (∞,∞) directed all the way (per Riehl-Shulman / Weaver-Licata) | (∞,1) directed mechanized; (∞,ω) directed is open |
| Mathlib full-import polygraph translation | Possible per polycell.md §6 but ~50K LoC; defer to v4 |

---

## Risk register (focused on pivot, subset of polycell.md §12)

### POLY-α-specific risks

| Risk | Probability | Impact | Mitigation |
|---|---|---|---|
| ωcE Construction 1.22 hits propext via Quot machinery | Medium | High (POLY-α stuck) | Avoid Lean Quot; use explicit Nat-indexed structural build |
| ωcE morphism search exponential on FX terms | Low | Medium (perf, not correctness) | Bounded depth + memoization + fallback to existing Conv path |
| Stratification closure axioms hit propext via partial pattern match | Medium | High | Per `feedback_lean_zero_axiom_match` recipes — full enum, no wildcard |
| Bridge theorem (Conv ↔ ConvViaOmegacE) fails in one direction | Medium | High (cancels POLY-α) | Prove easy direction first; iff is the contractibility theorem from HLOR 1.33 |
| Lean elaborator slow on profile structure with 10 fields | Low | Medium (compile time) | `@[reducible]` field accessors; consider Lean 5 if released |

### Pivot-level risks

| Risk | Probability | Impact | Mitigation |
|---|---|---|---|
| Axis 6 complicial Gray module hits ∞-cat mechanization wall in POLY-γ | Medium | Critical (drops Gray tensor, lose interchange-as-frame-rule) | Fallback: ship simpler Gray tensor without full complicial conditions; lose univalence-as-theorem but keep decidable Conv |
| Axis 7 ∞-topos base too heavy for Lean | High | Critical | Fallback: encode topos as a list of modal adjunctions without full topos structure; lose math automation but keep modal layer |
| Axis 8 Cisinski ω-loc doesn't mechanize | Medium | Medium (lose self-referential profiles) | Fallback: hardcode depth-3 profile tower |
| Loubaton paper has subtle gap when Lean-mechanized | Medium | High | Email Loubaton at end of POLY-α (~month 3) for design review |
| 36-month timeline slips to 48+ months | High | Medium | Each POLY-X is independently useful; can stop after any of α/β/γ/δ |

### Project-level risks

| Risk | Probability | Impact | Mitigation |
|---|---|---|---|
| Existing FX kernel breaks during pivot (regression) | Low | High | Tier 1 unblockers shipped under current substrate; POLY-α adds new files without modifying old |
| User loses interest mid-pivot | Medium | Critical | Each POLY-α commit is independently useful; even if pivot stops at month 3, ωcE-based Conv decidability is a shipped win |
| Cron-driven loops misalign with POLY-α phase boundaries | Low | Low | Just keep shipping atomic increments; loops continue saying "real progress with unblocker tasks" which matches |

---

## Concrete next-3-weeks plan

| Day | Deliverable | LoC | Status |
|---|---|---|---|
| Week 1 day 1-2 | `Foundation/Polygraph/CellShape.lean` | 800 | Tier 0 commit 1 |
| Week 1 day 3 | `Foundation/Polygraph/Stratification.lean` (structure + axioms) | 400 | Tier 0 commit 2 part 1 |
| Week 1 day 4 | `Foundation/Polygraph/Stratification.lean` (decidability + example instances) | 200 | Tier 0 commit 2 part 2 |
| Week 1 day 5 | `Foundation/Polygraph/OmegacE/Construction.lean` skeleton | 400 | Tier 0 commit 3 part 1 |
| **Week 1 milestone** | CellShape + Stratification shipped, ωcE skeleton in place | 1.8K | Commits 1+2 + ωcE start |
| Week 2 day 1-2 | `OmegacE/Construction.lean` complete with α/β/extend ctors | 700 | Tier 0 commit 3 part 2 |
| Week 2 day 3 | `OmegacE/Construction.lean` colim-over-Nat + truncations | 400 | Tier 0 commit 3 part 3 |
| Week 2 day 4-5 | `OmegacE/UniversalProperty.lean` IsCoherentEquiv def | 500 | Tier 0 commit 4 part 1 |
| **Week 2 milestone** | Full ωcE polygraph shipped with decidability instance | 3.4K | Commit 3 complete, commit 4 in flight |
| Week 3 day 1 | `OmegacE/UniversalProperty.lean` decidability + search | 500 | Tier 0 commit 4 part 2 |
| Week 3 day 2 | `Reduction/ConvViaOmegacE.lean` definition | 300 | Tier 0 commit 5 part 1 |
| Week 3 day 3 | `ConvViaOmegacE.lean` bridge theorem (easy direction) | 400 | Tier 0 commit 5 part 2 |
| Week 3 day 4 | `ConvViaOmegacE.lean` bridge theorem (hard direction) | 800 | Tier 0 commit 5 part 3 |
| Week 3 day 5 | POLY-α audit milestone + memory entry + ROADMAP update | 500 | Tier 0 commit 6 |
| **Week 3 milestone** | **★ MILESTONE A reached** via ωcE-based decidable Conv | 5.9K total | POLY-α complete |

In parallel (during normal cron firings):

| Day | Tier 1 deliverable | LoC | Status |
|---|---|---|---|
| Any free hour | #2110 Step.iotaOeqJRefl | 80 | atomic |
| Any free 2 days | Delete K11.8/K11.9 fake mirrors | -960 | cleanup |
| Any free day | Update task tracker (close cancelled tasks) | 0 (admin) | bookkeeping |

---

## Email Loubaton timeline

| Trigger | Action |
|---|---|
| End of week 1 (CellShape + Stratification shipped) | Pre-draft email; don't send yet |
| End of week 2 (ωcE construction shipped) | Send: "We're mechanizing the framework from your 2207.08504 + HLOR + thesis §6.1. Here's POLY-α status. Would feedback help?" |
| End of week 3 (POLY-α MVP) | Follow up with concrete code repo link + ConvViaOmegacE.lean |
| Month 2 onwards | Maintain quarterly check-ins as POLY-β/γ ships |

Loubaton's email: `loubaton@mpim-bonn.mpg.de` (MPIM Bonn).

---

## Open decisions for user

These need explicit user input before being acted on.

1.  **Do we ship Tier 1 `Step.iotaOeqJRefl` (#2110) in parallel with
    POLY-α?**  Pro: small atomic unblocker for #1632.  Con: adds work
    that gets thrown away during PolyTerm migration.  **Recommendation:**
    YES — 80 LoC, 1 day, useful regardless.

2.  **Do we ship Tier 1 `Term.emptyElim` (#2109)?**  Pro: simple.  Con:
    cascading addition that PolyTerm subsumes.  **Recommendation:** NO
    — defer until POLY-β ships axis 2, then it's one Generator entry.

3.  **Do we delete K11.8 RawPolyTerm + K11.9 PolyTerm now?**  User
    previously said yes ("Confirmed — delete the fake mirrors").
    **Recommendation:** YES, do it in week 1 alongside POLY-α.

4.  **Do we update the existing `ROADMAP.md` or keep this as a
    supplement?**  **Recommendation:** Keep this as supplement.
    `ROADMAP.md` stays historical; this doc is the active plan.
    After POLY-η completes (month 36), merge.

5.  **Do we revoke task tracker entries we marked CANCELLED, or
    keep them with `[deleted]` status?**  **Recommendation:** Keep
    with explicit "CANCELLED — subsumed by PolyTerm POLY-X" annotation.
    Don't delete; future engineers benefit from the audit trail.

6.  **Should we email Loubaton during POLY-α or wait for POLY-β?**
    **Recommendation:** End of week 2 (after ωcE construction
    shipped) — concrete enough to be credible, early enough to get
    useful design feedback.

7.  **What happens if POLY-α commit 5 (the bridge theorem) doesn't
    work zero-axiom?**  **Recommendation:** Drop POLY-α pivot, stay
    on current substrate, continue accelerate-* roadmap as planned.
    The 4 commits already shipped (CellShape, Stratification, ωcE,
    UniversalProperty) become abandoned-but-documented archaeology.

---

## Status as of 2026-05-23

**Shipped:**
- Polyterm design doc: `polycell.md` (2259 lines) at commit ca101887
- Reference memory: `reference_loubaton_papers.md`
- This pivot roadmap doc (you are reading it)

**In progress:**
- Tier 0 POLY-α (week 1 starts on user go-ahead)
- Tier 1 quick-ship unblockers (Step.iotaOeqJRefl + K11.8/9 deletion)

**Awaiting user decision:**
- Open decisions 1-7 above
- Final go/no-go on starting POLY-α commit 1 (CellShape.lean)

**Default if user doesn't reply by next cron firing:**
- Start Tier 0 commit 1 (CellShape.lean)
- Concurrently ship Tier 1 cleanups (K11.8/9 deletion + Step.iotaOeqJRefl)
- Continue per the week-by-week plan above until next user input

**Critical-path-shortened version:**
- If MILESTONE A is the only goal: POLY-α (3 weeks) + done
- Stop after POLY-α and resume accelerate-* roadmap from a position
  of much stronger Conv infrastructure
- The other axes (β through ε) can wait indefinitely; what they
  buy (univalence-as-theorem, concurrency, modal cohesion, math
  automation) are all nice-to-have, not blockers

**Maximalist version (per polycell.md):**
- 36 months, ~187K LoC, full ten-axis substrate, FX becomes the
  first proof assistant with (∞,ω)-categories internalized

The choice between these is the user's, but the **decision needed
THIS WEEK** is just: start POLY-α commit 1 yes/no.  Everything else
can be re-evaluated at week 3 milestone.

---

*Document version 1.0 — 2026-05-23.  Pivot rethink under PolyTerm.
Replaces the pre-pivot accelerate-* roadmap structure for forward
planning while keeping the old `ROADMAP.md` as historical reference.*

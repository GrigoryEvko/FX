# T2 closure plan — Phases α / β / γ

**Status**: design document for Codex handoff
**Headline goal**: ship `Term.rename_injective` (T2) at 78/78 strict-propositional-equality cases, then update consumers (HeadlineRenameInjInv #1985, the 78 `isAggregatorTotal_*` wrappers #1986, T4/T5/T7 corollaries, K19 encoding bridges).
**Audience**: Codex (or any single Lean engineer with kernel context).

---

## 0. Background — what is T2 and why are 9 arms unshipped?

T2 statement:
```
theorem Term.rename_injective {ρ : RawRenaming srcScope tgtScope}
    (rhoInjective : RawRenamingInjective ρ) :
    ∀ {ctx ty raw} (termA termB : Term ctx ty raw),
      Term.rename rho termA = Term.rename rho termB → termA = termB
```

The kernel has shipped 69 of 78 per-arm theorems
(`Term.rename_injective_arm_<ctor>`) zero-axiom in
`LeanFX2/Term/RenameInjective/InductiveArms.lean`. The 9 unshipped arms are:

```
equivReflId       funextRefl         equivReflIdAtId   funextReflAtId
equivIntroHet     uaIntroHet         funextIntroHet
universeCode      effectPerform
```

The wall analysis (committed in
`LeanFX2/Smoke/AuditRenameInjectivityWalls.lean`) classified them as
"kernel-design walls". On re-examination via parallel explore agents, the
walls split into **three categories with distinct fixes**:

| Category | Ctors | Wall mechanism | Fix |
|----------|-------|----------------|-----|
| **Discharged by existing infrastructure** | `funextRefl` (1) | Cross-ctor collision with `Term.lamPi (Term.refl ...)`; kernel already proves `renamedLamPi_ne_renamedFunextReflCast` in `BinderInversions.lean:98-150` | **Phase α** (1 hour, ~50 LoC) — use the ne-lemma |
| **Vacuous walls — proof technique workaround** | `equivReflId`, `funextReflAtId`, `equivIntroHet`, `funextIntroHet` (4) | `cases termB` blocks on multi-ctor raw collisions; the supposed cross-ctor inhabitants require uninhabitable proof obligations (e.g. `equivIntroHet`'s leftInv/rightInv at colliding shape) | **Phase β** (1-2 days, ~600 LoC) — deep PSum inversion via custom `_raw_inv` lemmas |
| **Free-data walls — kernel raw enrichment** | `equivReflIdAtId`, `uaIntroHet`, `universeCode`, `effectPerform` (4) | Ctor carries typed data the raw projection forgets (`UniverseLevel.toNat` collapses, `effectRow` absent, `Ty` carriers projected only as raws) | **Phase γ** (3-5 days, ~50 files) — enrich RawTerm to carry the forgotten data |

The three phases are **strictly independent** — each can ship without the others. Combined: T2 = 78/78.

The natural shipping order is α → β → γ (cheapest first, biggest cascade last), but Codex can interleave if convenient.

---

## 1. Phase α — funextRefl via existing infrastructure (~50 LoC, 1 hour)

### 1.1 What's available

The kernel ships `renamedLamPi_ne_renamedFunextReflCast` at
`/root/iprit/FX/lean-fx-2/LeanFX2/Term/RenameInjective/BinderInversions.lean:98-150`.
Signature:

```lean
theorem renamedLamPi_ne_renamedFunextReflCast
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    {domainType : Ty level sourceScope}
    {codomainType : Ty level (sourceScope + 1)}
    {bodyRaw : RawTerm (sourceScope + 1)}
    (bodyTerm : Term (sourceCtx.cons domainType) codomainType bodyRaw)
    (baseCodomain : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (bodyRawEq : bodyRaw = RawTerm.refl applyRaw)
    (codomainEq : codomainType = Ty.id baseCodomain.weaken applyRaw applyRaw) :
    HEq (Term.rename termRenaming (Term.lamPi bodyTerm))
        (Term.rename termRenaming
          (Term.funextRefl (context := sourceCtx) domainType baseCodomain applyRaw)) →
      False
```

This lemma proves that the renamed `Term.lamPi (Term.refl ...)` and renamed
`Term.funextRefl ...` are NEVER HEq, at the typed level. The lamPi arm
of T2 already uses this lemma at `InductiveArms.lean:898-939` to handle
the lamPi-vs-funextRefl branch.

The kernel also ships `Term.lam_pi_inv` at `BinderInversions.lean:256-306`
which inverts a typed term whose outer Ty is `Ty.piTy` and raw is
`RawTerm.lam bodyRaw` into a 2-way PSum `{lamPi, funextRefl}`.

### 1.2 The proof template

`funextRefl`'s outer Ty is `funextReflType domainType codomainType applyRaw`
which `@[reducible]` unfolds to
`Ty.piTy domainType (Ty.id codomainType.weaken applyRaw applyRaw)`. So
`Term.lam_pi_inv` directly applies to termB.

```lean
theorem Term.rename_injective_arm_funextRefl
    (rhoInjective : RawRenamingInjective rho)
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (termB : Term sourceCtx (funextReflType domainType codomainType applyRaw)
                            (RawTerm.lam (RawTerm.refl applyRaw))) :
    Term.rename termRenaming
        (Term.funextRefl (context := sourceCtx) domainType codomainType applyRaw) =
      Term.rename termRenaming termB →
    Term.funextRefl (context := sourceCtx) domainType codomainType applyRaw = termB := by
  intro renameEq
  -- funextReflType unfolds to Ty.piTy domainType (Ty.id codomainType.weaken applyRaw applyRaw)
  cases Term.lam_pi_inv (codomainType := Ty.id codomainType.weaken applyRaw applyRaw)
    (bodyRaw := RawTerm.refl applyRaw) termB with
  | inl piView =>
    -- termB = Term.lamPi bodyTerm with bodyTerm : Term _ (Ty.id _ applyRaw applyRaw) (RawTerm.refl applyRaw)
    -- The renameEq becomes Term.lamPi-shaped vs Term.funextRefl-shaped after rewriting.
    -- Discharge via renamedLamPi_ne_renamedFunextReflCast (symmetric to the lamPi arm's use)
    obtain ⟨bodyTerm, termHEqB⟩ := piView
    cases termHEqB
    exact False.elim
      (renamedLamPi_ne_renamedFunextReflCast termRenaming bodyTerm
        codomainType applyRaw rfl rfl
        (heq_of_eq renameEq.symm))
  | inr reflView =>
    -- termB = Term.funextRefl domainType baseCodomainB applyRawB with eqs
    -- After cases on the equality witnesses, termB collapses to Term.funextRefl ...
    obtain ⟨baseCodomainB, applyRawB, bodyRawEqB, codomainEqB, termHEqB⟩ := reflView
    cases bodyRawEqB         -- applyRawB := applyRaw
    -- codomainEqB : Ty.id codomainType.weaken applyRaw applyRaw 
    --             = Ty.id baseCodomainB.weaken applyRaw applyRaw
    -- Inject: codomainType.weaken = baseCodomainB.weaken
    -- Use Ty.weaken_inj_on_freshVar (or similar; verify the kernel ships it; if not, ship as ~20 LoC helper)
    injection codomainEqB with carrierEq _ _
    -- carrierEq : codomainType.weaken = baseCodomainB.weaken
    have codomainEq : codomainType = baseCodomainB := by
      -- TODO: check if Ty.weaken_injective is shipped; if not, ship it as a structural induction
      sorry  -- placeholder; the actual proof uses Ty.weaken injectivity
    cases codomainEq
    cases termHEqB
    rfl
```

### 1.3 Open questions for Phase α

1. **Is `Ty.weaken_injective` shipped?** Codex should grep
   `Ty.weaken_injective` / `Ty.weaken.*inj` in `Foundation/Ty.lean` and
   `Foundation/RawPartialRename/`. If not shipped, add it as a structural
   induction over Ty (~50 LoC; mostly mechanical since weakening is
   structural). This would be a one-time helper that benefits multiple
   downstream theorems.

2. **Does `cases bodyRawEqB` work cleanly?** `bodyRawEqB : RawTerm.refl applyRaw = RawTerm.refl applyRawB`
   should subst applyRawB := applyRaw via `cases bodyRawEqB` followed by
   another `cases` on the inner equation. Or use `injection bodyRawEqB`.
   Codex should verify.

3. **Does the `cases termHEqB` close the goal directly?** After all the
   substitutions, termHEqB : HEq termB (Term.funextRefl domainType codomainType applyRaw).
   `cases termHEqB` should give termB = Term.funextRefl domainType codomainType applyRaw,
   which closes the goal by rfl.

### 1.4 Phase α deliverable

- **File modified**: `LeanFX2/Term/RenameInjective/InductiveArms.lean` (replace the docstring at lines 2286-2330 with the funextRefl arm proof; ~50 LoC).
- **File modified**: `LeanFX2/Smoke/AuditCumulUpEquivApplyArms.lean` (add `#print axioms Term.rename_injective_arm_funextRefl`).
- **File possibly modified**: `LeanFX2/Foundation/Ty.lean` (if `Ty.weaken_injective` needs to be shipped; ~50 LoC).
- **Audit gate**: `lake build LeanFX2 LeanFX2Audit` green; `#print axioms` reports zero axioms.
- **T2 count after Phase α**: 70/78.

---

## 2. Phase β — 4 vacuous walls via deep PSum inversion (~600 LoC, 1-2 days)

### 2.1 The 4 vacuous walls

Per Agent 1's analysis (the explore agent that audited the 9 walls in
detail), the following 4 arms are "vacuous walls" — the supposed
counterexample inhabitants require uninhabitable proof obligations:

| Arm | Why vacuous |
|-----|-------------|
| `equivReflId` | Cross-ctor collision with `equivIntroHet` requires `leftInv : Term ctx (Ty.piTy carrier (Ty.id carrier.weaken (app id.weaken (app id.weaken (var 0))) (var 0))) leftInvRaw` — the inner `Ty.id` has syntactically distinct endpoints, and no Term ctor produces `Ty.id A a b` with `a ≠ b` at arbitrary carrier. Hence the supposed cross-ctor inhabitant is uninhabitable. |
| `funextReflAtId` | All ctor inputs are pinned by outer Ty + raw; cross-ctor collisions with `funextIntroHet` are ruled out by `rawTerm_ne_refl_self` (already shipped). |
| `equivIntroHet` | Own internal proof witnesses (leftInv/rightInv) are uninhabitable at the colliding `forwardRaw = backwardRaw = lam (var 0)` shape, so the "wall" multi-inhabitancy is hypothetical. |
| `funextIntroHet` | All inputs pinned by outer Ty + raw; cross-ctor collisions structurally ruled out (same family as `funextReflAtId`). |

For each of these, the T2 arm is provable via the standard
`cases termB`/`suffices key` pattern, EXTENDED with deep cases inversion
to handle the multi-ctor PSum branches.

### 2.2 The proof template (equivReflId as canonical)

```lean
theorem Term.rename_injective_arm_equivReflId
    (rhoInjective : RawRenamingInjective rho)
    (carrier : Ty level sourceScope)
    (termB : Term sourceCtx (Ty.equiv carrier carrier)
              (RawTerm.equivIntro
                (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩))
                (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ sourceScope⟩)))) :
    Term.rename termRenaming (Term.equivReflId carrier) =
      Term.rename termRenaming termB →
    Term.equivReflId carrier = termB := by
  intro renameEq
  -- termB inhabits Term ctx (Ty.equiv carrier carrier) (RawTerm.equivIntro id id)
  -- Ctors producing this outer-Ty + raw: equivReflId, equivIntroHet (under conditions)
  -- equivReflIdAtId / uaIntroHet produce different outer Ty (Ty.id ..., not Ty.equiv ...)
  -- Cases on termB:
  cases termB with
  | equivReflId carrierB =>
    -- Both terms are Term.equivReflId; just need carrier = carrierB
    -- From renameEq: Term.equivReflId (carrier.rename rho) = Term.equivReflId (carrierB.rename rho)
    -- → carrier.rename = carrierB.rename → carrier = carrierB via Ty.rename_injective
    -- Then rfl
    sorry -- mechanical
  | equivIntroHet forward backward leftInv rightInv =>
    -- This is the supposed wall branch.
    -- leftInv has type Ty.piTy carrier (Ty.id carrier.weaken (app backward.weaken (app forward.weaken (var 0))) (var 0))
    -- Apply Term.lam_pi_inv on leftInv (since its raw must be RawTerm.lam <bodyRaw>):
    --   → either lamPi-shaped or funextRefl-shaped
    -- BUT the inner Ty.id has syntactically distinct endpoints — the funextRefl branch fails its rawEq constraint
    --   (funextRefl requires bodyRaw = RawTerm.refl applyRaw AND codomainType = Ty.id base.weaken applyRaw applyRaw)
    --   The codomainType here is Ty.id carrier.weaken (app backward (app forward (var 0))) (var 0) — endpoints differ
    -- And the lamPi-shaped body must have type Ty.id ... — for which we need Term.refl (endpoints must match) or some other ctor
    -- For arbitrary `carrier`, no constructive Ty.id-inhabitant exists.
    -- → deep cases on leftInv eventually hits a no-confusion contradiction
    sorry -- the actual proof writes the leftInv inversion chain to expose the uninhabitability
  -- ... (and any other ctor that could produce Ty.equiv carrier carrier + raw equivIntro id id; verify there are none beyond these two)
```

### 2.3 Architecture for the deep PSum chain

The proof technique:
1. Use the standard `cases termB` to enumerate the candidate ctors producing the shared outer Ty + raw shape
2. For each non-target ctor branch:
   - Identify which subterm has an "uninhabitable" type (the inner proof witness with syntactically-distinct Id endpoints)
   - Use `cases` or a custom `_raw_inv` lemma to invert that subterm
   - Drill down via more `cases` until a `Term.noConfusion` or `RawTerm.noConfusion` discharges via raw-shape mismatch

This is the SAME PATTERN used by the kernel's existing `_raw_inv` lemmas
(`Term.snd_raw_inv`, `Term.boolElim_raw_inv`, `Term.appPi_raw_inv`) in
`LeanFX2/Term/RenameInjective/CastInversions.lean`. Codex should
generalize this pattern to a reusable infrastructure.

### 2.4 Phase β files to modify

- **NEW file**: `LeanFX2/Term/RenameInjective/EtaFamilyInversions.lean` (~300 LoC)
  - Custom `_raw_inv` lemmas for `equivReflId`, `funextReflAtId`, `equivIntroHet`, `funextIntroHet`
  - The "uninhabitable inner subterm" inversion helpers
- **MODIFY**: `LeanFX2/Term/RenameInjective/InductiveArms.lean` (~200 LoC across 4 arms)
  - Replace the η-family wall docstring block at lines 2286-2330 with the 4 arm proofs
- **MODIFY**: `LeanFX2/Smoke/AuditCumulUpEquivApplyArms.lean`
  - Add `#print axioms` for the 4 new arms
- **MODIFY**: `LeanFX2/Smoke/AuditRenameInjectivityWalls.lean`
  - Remove the `equivReflIdInhabitant`/`equivIntroHetInhabitant` pair (their multi-inhabitancy is preserved but vacuous from a rename-injectivity perspective; document this as a note)
- **Audit gate**: `lake build LeanFX2 LeanFX2Audit` green; all 4 new arms zero-axiom.
- **T2 count after Phase β**: 74/78.

### 2.5 Risk for Phase β

- **R-β1**: The `cases termB` might still fail propext-clean for `equivReflId` because dep-elim on `Ty.equiv carrier carrier` (where both indices are equal `carrier`) is fragile. Mitigation: use a `suffices key` wrapper that frees the outer Ty index, then case-analyze the freed type via `subst` after Ty injection.
- **R-β2**: The deep cases chain for `equivIntroHet`'s leftInv inversion may bottom out at a `Ty.id` ctor where Lean's match generates propext-leaking equations. Mitigation: write the deep cases chain in term-mode using `match ... with` matchers explicitly (avoid `cases` tactic propext leak).

---

## 3. Phase γ — RawTerm enrichment for the 4 free-data walls (~50 files, 3-5 days)

### 3.1 The 4 free-data walls

A `Term` constructor's parameter is **free data** iff it satisfies all four:
1. The parameter is in `Type`, not `Prop` (so proof-irrelevance doesn't apply)
2. The parameter does NOT appear in the constructor's output `Ty` index
3. The parameter does NOT appear in the constructor's output `RawTerm` index
4. The parameter is NOT existentially-recoverable from an inner subterm's outer type

The 4 free-data instances in the current kernel:

| Term ctor | Free-data param | Currently in raw as | Issue |
|-----------|-----------------|---------------------|-------|
| `universeCode` | `innerLevel : UniverseLevel` | `innerLevel.toNat : Nat` | `toNat` non-injective (`max 0 0` ≡ `imax 0 0` → 0) |
| `effectPerform` | `effectRow : Effects.EffectRow` and `operationSignature.{effectLabel}` | absent | row + label completely forgotten by raw |
| `equivReflIdAtId` | `carrier : Ty level scope` | `carrierRaw : RawTerm scope` only | typed `Ty` carrier forgotten; only its raw projection appears |
| `uaIntroHet` | `carrierA, carrierB : Ty level scope` | `carrierARaw, carrierBRaw : RawTerm scope` only | typed `Ty` carriers forgotten |

### 3.2 Pre-flight check for Phase γ — DO BEFORE STARTING THE REFACTOR (~2 hours)

**The 4 free-data walls may ALSO be proof-technique walls, not structural walls.**

The actual T2 hypothesis is `rename ρ termA = rename ρ termB → termA = termB` — and for the supposed counterexample pairs:

- `Term.universeCode (max 0 0) ...` vs `Term.universeCode (imax 0 0) ...`
- `Term.effectPerform _ [read] _ cpA op arg` vs `Term.effectPerform _ [write] _ cpB op arg`
- `Term.equivReflIdAtId _ _ Ty.unit raw` vs `Term.equivReflIdAtId _ _ Ty.bool raw`
- `Term.uaIntroHet _ _ Ty.unit Ty.unit ... witnessUnit` vs `Term.uaIntroHet _ _ Ty.bool Ty.bool ... witnessBool`

In every case, the renamed outputs `rename ρ A` and `rename ρ B` are **propositionally distinct** in Lean 4's freely-generated inductive (different ctor implicit-arg tuples — `Term.universeCode max ...` and `Term.universeCode imax ...` are distinct ctor applications since `max ≠ imax` as `UniverseLevel` values). So the T2 hypothesis `rename A = rename B` is FALSE on these pairs, and the implication holds vacuously.

The "wall" is actually that Lean's `cases termB` tactic fails to dep-eliminate on the toNat-collapsed raw constraint (`innerLevelB.toNat = innerLevel.toNat` doesn't determine `innerLevelB` since `UniverseLevel.toNat` is non-injective). This is a tactic limitation, not a falsehood.

### 3.3 Pre-flight tasks

1. **Pick the universeCode arm** as the simplest test. Write the arm proof using one of:
   - **Approach A**: `match termB, hRaw : RawTerm.universeCode k = RawTerm.universeCode innerLevel.toNat with ...` — Lean 4 supports refined match that can bypass the index-unification heuristics
   - **Approach B**: A custom `Term.universeCode_raw_inv` lemma that returns `Σ' (innerLevelB : UniverseLevel) (cumulOkB ...) (levelLeB ...), innerLevelB.toNat = innerLevel.toNat ∧ HEq termB (Term.universeCode innerLevelB ...)`. Then in the arm, take the existential, use `rename(A) = rename(B)` + `Term.universeCode.injEq` (Lean auto-generates this) to extract `innerLevel = innerLevelB` propositionally, close by `cases innerLevelEq + rfl`.

2. **If Approach A or B succeeds** on universeCode, repeat the same pattern for `effectPerform`, `equivReflIdAtId`, `uaIntroHet`. Each is ~30–50 LoC.

3. **If all 4 arms ship via this pattern**, T2 = 78/78 with ZERO kernel refactor required. Phase γ becomes UNNECESSARY. Update `Smoke/AuditRenameInjectivityWalls.lean` (the constructive "counterexample" witnesses there are vacuous from a rename-injectivity perspective — they show multi-inhabitancy at the same indexed Term type, but not rename-injectivity failure).

4. **Only if the pre-flight fails** on at least one arm (e.g., the auto-generated `Term.<ctor>.injEq` doesn't fire propositionally because of Prop-irrelevance issues on the implicit `cumulOk`/`levelLe` fields, OR the `_raw_inv` lemma itself can't be written without leaking propext) — proceed to the full Phase γ refactor below.

**Expected outcome of pre-flight**: ~80% probability the walls dissolve via Approach B alone, ~20% probability that at least one needs the structural kernel refactor below.

### 3.4 Architectural problem statement (if Phase γ is needed)

Even if the pre-flight succeeds for T2 specifically, the underlying architectural issue is real: **4 `RawTerm` constructors store strictly less information than their `Term` counterparts carry as typed data**. This asymmetry causes friction for any future theorem that needs to recover typed data from raw — not just T2. Phase γ closes this asymmetry permanently.

Multi-inhabitancy at the same indexed type `Term ctx outerTy outerRaw` is itself FINE — Lean freely allows distinct ctor applications to inhabit the same indexed type. The actual problem is downstream: any function or theorem that tries to **extract** the typed `innerLevel`/`effectRow`/`carrier` from the raw projection fails, because the raw doesn't carry that data. This affects:

- T2's standard `cases`-based proof technique (Lean's dep-elim heuristics)
- Future bridges from raw representation back to typed (encode_term_sound, K19.x)
- Term reconstruction from raw + outer Ty (any "decode" function)
- E-graph canonicalization (K14) — equivalent typed terms have equal raw projections

Phase γ closes this universally by ensuring every `Term` parameter is either raw-determined, outer-Ty-determined, sub-Ty-existential, or Prop-irrelevant. After Phase γ, the architectural law "raw uniquely determines all non-Prop ctor args modulo outer-Ty existentials" holds for all 78 ctors.

### 3.5 Per-ctor refactor design

Each refactor enriches the `RawTerm` constructor to carry the forgotten data, then updates the corresponding `Term` constructor's raw output to reference the new shape, then cascades through every consumer.

#### 3.5.1 `RawTerm.universeCode` enrichment

**Current** (`LeanFX2/Foundation/RawTerm.lean`):
```lean
| universeCode (universeIndex : Nat) : RawTerm scope
```

**Enriched**:
```lean
| universeCode (innerLevel : UniverseLevel) : RawTerm scope
```

The `Nat` is replaced by the full `UniverseLevel`. (Alternative: keep the `Nat` for backwards compat AND add the `UniverseLevel` as a separate field — but that creates redundancy. Replace cleanly.)

**Term ctor update** (`LeanFX2/Term.lean:593-599`):
```lean
| universeCode {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Term context (Ty.universe outerLevel levelLe)
                 (RawTerm.universeCode innerLevel)  -- was: innerLevel.toNat
```

**Foundation/Universe.lean update**: Keep `UniverseLevel.toNat` as a derived projection (used by `Ty.universeLe`); add `UniverseLevel.DecidableEq` (already shipped at line 92), `UniverseLevel.Repr` (line 92) — no new infrastructure needed for the enrichment itself.

#### 3.5.2 `RawTerm.effectPerform` enrichment

**Current**:
```lean
| effectPerform (operationRaw argumentsRaw : RawTerm scope) : RawTerm scope
```

**Enriched** (option A — full enrichment, preferred):
```lean
| effectPerform 
    (effectRow : Effects.EffectRow)
    (effectLabel : Effects.EffectLabel)
    (operationRaw argumentsRaw : RawTerm scope) : RawTerm scope
```

The two missing pieces are `effectRow` (the row witnessing CanPerform) and `effectLabel` (the operation's label, from `operationSignature.effectLabel`). The `argumentCarrier` and `resultCarrier` are typed `Ty` values that are existentially recoverable (argumentCarrier from `operationTag`'s inner type; resultCarrier from outer `Ty.effect resultCarrier effectTag`), so they don't need to be in raw.

**Term ctor update** (`LeanFX2/Term.lean:567-582`):
```lean
| effectPerform {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation : Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    (operationTag : Term context
        (Ty.effect operationSignature.argumentCarrier effectTag) operationRaw)
    (arguments : Term context operationSignature.argumentCarrier argumentsRaw) :
    Term context (Ty.effect operationSignature.resultCarrier effectTag)
      (RawTerm.effectPerform 
        effectRow 
        operationSignature.effectLabel 
        operationRaw 
        argumentsRaw)  -- was: just (operationRaw, argumentsRaw)
```

#### 3.5.3 `RawTerm.equivReflIdAtId` enrichment

**Current**: `equivReflIdAtId` shares the raw shape `RawTerm.equivIntro (RawTerm.lam (RawTerm.var 0)) (RawTerm.lam (RawTerm.var 0))` with `equivReflId`, `equivIntroHet`, `uaIntroHet`. The shared raw is what creates the η-family collision.

**Option A** — add a dedicated `RawTerm.equivReflIdAtIdMarker` ctor:
```lean
| equivReflIdAtIdMarker 
    (innerLevel : UniverseLevel)  -- adds the level data
    (carrierRaw : RawTerm scope) : RawTerm scope
```

This breaks the 4-way collision: only `Term.equivReflIdAtId` produces this raw, distinct from the equivIntro-shape raws.

**Term ctor update** (`LeanFX2/Term.lean:704-714`):
```lean
| equivReflIdAtId {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope) :
    Term context
      (Ty.id (Ty.universe innerLevel innerLevelLt) carrierRaw carrierRaw)
      (RawTerm.equivReflIdAtIdMarker innerLevel carrierRaw)  -- new dedicated marker
```

Note: the typed `carrier : Ty level scope` parameter remains free data even after this enrichment (it's used semantically but not in raw). **This is acceptable** because the carrier's role in the kernel is semantic-only — it doesn't affect rename injectivity or raw bijection. If a future theorem needs to recover carrier from raw, it would need additional infrastructure; but T2 specifically only needs the rename to distinguish equivReflIdAtId from other ctors, which the marker achieves.

**Alternative — remove the `carrier` parameter entirely**: if `carrier` is never used as data downstream (only as a phantom type-class argument), remove it from the ctor. This is the cleanest fix. Investigate consumers (`grep -rn "Term.equivReflIdAtId" /root/iprit/FX/lean-fx-2/` to see if anyone destructs and uses `carrier`).

#### 3.5.4 `RawTerm.uaIntroHet` enrichment

Same approach as `equivReflIdAtId`. The η-family collision on raw `RawTerm.equivIntro fw bw` is shared with `Term.uaIntroHet`. Add a dedicated marker.

**Option A** — dedicated `RawTerm.uaIntroHetMarker`:
```lean
| uaIntroHetMarker 
    (innerLevel : UniverseLevel)
    (carrierARaw carrierBRaw : RawTerm scope)
    (forwardRaw backwardRaw : RawTerm scope) : RawTerm scope
```

**Term ctor update** (`LeanFX2/Term.lean:843-854`):
```lean
| uaIntroHet {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    (equivWitness : Term context (Ty.equiv carrierA carrierB)
                                 (RawTerm.equivIntro forwardRaw backwardRaw)) :
    Term context (Ty.id (Ty.universe innerLevel innerLevelLt)
                        carrierARaw carrierBRaw)
                 (RawTerm.uaIntroHetMarker 
                    innerLevel carrierARaw carrierBRaw 
                    forwardRaw backwardRaw)  -- was: RawTerm.equivIntro fw bw
```

#### 3.5.5 Summary table

| Raw ctor change | Term ctor change | New raw enrichment |
|-----------------|------------------|--------------------|
| `universeCode (k : Nat)` → `universeCode (innerLevel : UniverseLevel)` | output `RawTerm.universeCode innerLevel` | full UniverseLevel |
| `effectPerform (op, arg)` → `effectPerform (row, label, op, arg)` | output adds row + label | EffectRow + EffectLabel |
| `equivReflIdAtIdMarker` — NEW ctor | output `RawTerm.equivReflIdAtIdMarker innerLevel carrierRaw` | dedicated ctor + level |
| `uaIntroHetMarker` — NEW ctor | output `RawTerm.uaIntroHetMarker innerLevel cARaw cBRaw fwRaw bwRaw` | dedicated ctor + level |

### 3.6 The Phase γ cascade — ~50 files, mechanical

After bumping the 4 `RawTerm` ctors and the 4 `Term` ctors, every consumer that pattern-matches on or constructs these raw shapes must be updated.

#### 3.6.1 Foundation/RawTerm.lean changes

- `RawTerm.universeCode`/`effectPerform`: signature change
- Add `RawTerm.equivReflIdAtIdMarker` + `uaIntroHetMarker` constructors
- Update `RawTerm.rename` (4 arms)
- Update `RawTerm.subst` / `RawTerm.partialStrengthen?` (4 arms each)
- Update `RawTerm.decEq` (4 arms — should auto-derive)
- Update `RawTerm.rename_injective_under_injective_renaming` (4 arms)

#### 3.6.2 Foundation/Ty.lean — unaffected

`Ty.universe` already carries `UniverseLevel` structurally; only the RawTerm projection forgot it. No Ty changes needed.

#### 3.6.3 Term.lean — the 4 Term ctors

Update output raw expressions in the 4 ctors. ~10 LoC each.

#### 3.6.4 Term/Rename.lean

Rename function pattern-matches on Term ctors. The 4 affected ctors need their pattern-match arms updated.

#### 3.6.5 Term/Subst.lean, Term/PartialStrengthen/Dispatcher.lean

Similar: each pattern-matches on Term ctors; the 4 affected ctors' arms need re-checking. Should be no-ops at the typed level (substitution acts on subterms, doesn't touch the new free-data fields).

#### 3.6.6 Term/Pointwise.lean, Term/PolyRename.lean

Heteromorphic-rename / Poly-equivalence chains. The 4 affected ctors need their arms updated to match the new ctor signatures.

#### 3.6.7 Foundation/Polygraph/*.lean

`RawPolyTerm` mirror of RawTerm. Add the same 4 ctor changes:
- `RawPolyTerm.universeCode (innerLevel : UniverseLevel)`
- `RawPolyTerm.effectPerform (row, label, op, arg)`
- `RawPolyTerm.equivReflIdAtIdMarker (innerLevel, carrierRaw)`
- `RawPolyTerm.uaIntroHetMarker (innerLevel, cARaw, cBRaw, fwRaw, bwRaw)`

Update `RawPolyTerm.toRawTerm` / `RawTerm.toPoly` bijection (K11.12).

#### 3.6.8 Reduction layer (~10 files)

`RawStep.par`, `Step.par.cd`, `cd_lemma`, `RawParRename`, `RawParCompatible`, `RawParInversion`, `Compat/*`, `ConvBridge` — every file that has a per-ctor dispatch on `RawTerm.universeCode`/`effectPerform`/`equivReflIdAtIdMarker`/`uaIntroHetMarker` needs the new arms.

For non-RawStep arms (where the 4 ctors are "frozen" / non-reducing), the arms are trivial: refl / no-op.

#### 3.6.9 Term/RenameInjective/InductiveArms.lean

The 4 free-data T2 arms can now ship via the standard cases-based pattern, since their raw shapes now uniquely determine all explicit ctor args. ~30 LoC per arm.

Update the docstrings that previously documented the walls — they're now provable.

#### 3.6.10 Smoke/AuditRenameInjectivityWalls.lean

After Phase γ ships, the wall counterexamples in this file ARE STILL CONSTRUCTIVE — but the universeCode max/imax pair NO LONGER share a raw shape (because raw now carries the full UniverseLevel). Update this file to:
- DELETE the universeCodeMax/Imax inhabitants (they no longer share a raw shape)
- DELETE the equivReflId/equivIntroHet pair (their multi-inhabitancy at the same raw was vacuous; document this as a separate "harmless multi-inhabitancy" note)
- Repurpose the file as a documentation note: "Phase γ closed all 4 free-data walls; remaining multi-inhabitancy patterns are rename-injectivity-preserving by ctor-injection on implicit args".

#### 3.6.11 FX1Bridge/ encoders (~5 files)

`FX1Bridge/Universe.lean`, `FX1Bridge/Effect.lean`, etc. — the encoders from LeanFX2 to FX1 may need updates if they pattern-match on the changed raw ctors. Mostly trivial.

#### 3.6.12 Tools/AuditAll.lean

Add `#assert_no_axioms` gates for the 4 newly-provable T2 arms.

### 3.7 Phase γ file inventory (estimated)

Based on `grep -rln "RawTerm.universeCode\|RawTerm.effectPerform" /root/iprit/FX/lean-fx-2/`:

| Domain | File count | Notes |
|--------|------------|-------|
| Foundation (RawTerm, Ty, Polygraph) | ~5 | Core ctor signature changes |
| Term/ (Rename, Subst, Pointwise, PolyRename) | ~10 | Pattern-match arms |
| Reduction/ (RawStep, Step, ParRed, Compat, ConvBridge, RawCdLemma) | ~15 | Per-ctor arms |
| Term/RenameInjective/ + Term/StrengtheningImage/ | ~10 | Arm proofs + smoke updates |
| FX1Bridge/ | ~5 | Encoder updates |
| Tools/AuditAll, Smoke/* | ~5 | Audit gates + reviewer logs |

**Total**: ~50 files. Realistic estimate.

---

## 4. Combined shipping order (α → β → γ)

Each phase is INDEPENDENT — Codex can ship them in any order. The recommended order minimises risk:

### Day 0: Phase α (1 hour, ~50 LoC)

1. Verify `Ty.weaken_injective` is shipped or add it (~50 LoC)
2. Write `Term.rename_injective_arm_funextRefl` using `Term.lam_pi_inv` + `renamedLamPi_ne_renamedFunextReflCast`
3. Add to smoke audit
4. `lake build LeanFX2 LeanFX2Audit` green
5. Commit: "Phase α: ship funextRefl T2 arm via existing ne-lemma; T2 = 70/78"

### Day 1-2: Phase β (~600 LoC)

1. Audit each of the 4 vacuous walls to confirm they're proof-technique-only
2. Write the deep PSum inversion infrastructure in a new file `EtaFamilyInversions.lean`
3. Ship `Term.rename_injective_arm_{equivReflId, funextReflAtId, equivIntroHet, funextIntroHet}` arms one at a time
4. Each arm: write proof, build green, add to smoke audit, commit
5. After all 4: commit aggregate "Phase β: ship 4 vacuous-wall T2 arms via deep PSum inversion; T2 = 74/78"

### Day 3-7: Phase γ (4-8 hours pre-flight + 3-5 days cascade)

1. **Pre-flight (§3.2-3.3)**: spend 2 hours attempting `Approach B` on `universeCode`. If successful, repeat for the other 3 free-data ctors. Total: ~4-8 hours.
2. **If pre-flight succeeds**: skip the full Phase γ refactor. Document the proof-technique fix. Commit: "Phase γ resolved via proof-technique inversion; no kernel refactor needed; T2 = 78/78".
3. **If pre-flight fails on any arm**: proceed to the full cascade refactor (§3.5-3.7). Ship one ctor per day:
   - Day 3: universeCode enrichment + cascade
   - Day 4: effectPerform enrichment + cascade
   - Day 5: equivReflIdAtIdMarker + uaIntroHetMarker (combined since structurally similar)
   - Day 6: final audit + Smoke updates + task #1953 closure
4. Final commit: "Phase γ: T2 = 78/78 zero-axiom; closes #1953"

---

## 5. Verification plan

### After each commit (per phase)

```bash
cd /root/iprit/FX/lean-fx-2
lake build LeanFX2 LeanFX2Audit
# Must report: Build completed successfully (XXX jobs).
# No new axioms in any shipped theorem.
```

### After each phase

```bash
cd /root/iprit/FX/lean-fx-2
lake env lean -c '
import LeanFX2.Term.RenameInjective.InductiveArms
-- Phase α:
#print axioms LeanFX2.Term.rename_injective_arm_funextRefl
-- Phase β (after Phase β):
#print axioms LeanFX2.Term.rename_injective_arm_equivReflId
#print axioms LeanFX2.Term.rename_injective_arm_funextReflAtId
#print axioms LeanFX2.Term.rename_injective_arm_equivIntroHet
#print axioms LeanFX2.Term.rename_injective_arm_funextIntroHet
-- Phase γ (after Phase γ):
#print axioms LeanFX2.Term.rename_injective_arm_universeCode
#print axioms LeanFX2.Term.rename_injective_arm_effectPerform
#print axioms LeanFX2.Term.rename_injective_arm_equivReflIdAtId
#print axioms LeanFX2.Term.rename_injective_arm_uaIntroHet
'
# All must report: "does not depend on any axioms"
```

### Final headline check (after all 3 phases)

T2 = 78/78. The `Term.rename_injective` universal headline composition (#1985 HeadlineRenameInjInv) becomes possible. The 250-LoC manual blocker collapses to a single dispatch.

---

## 6. Risk register

| ID | Risk | Severity | Mitigation |
|----|------|----------|------------|
| **R-α1** | `Ty.weaken_injective` not shipped — Phase α needs it | low | Ship as ~50 LoC structural induction; one-time helper |
| **R-α2** | `cases bodyRawEqB` produces propext leak in Phase α | low | Use `injection` instead of `cases` for raw equations |
| **R-β1** | `cases termB` propext-leaks at `Ty.equiv carrier carrier` outer Ty | medium | Use `suffices key` pattern with freed genericType + outer Ty injection |
| **R-β2** | Deep cases chain hits propext-leaky `match` over Ty.id | medium | Write inversion in term-mode (`match ... with`) to avoid tactic propext |
| **R-β3** | Some vacuous walls are NOT actually vacuous on closer inspection | medium | Pre-audit each arm before writing the proof; if found genuine, escalate to Phase γ |
| **R-γ1** | UniverseLevel changes cascade unpredictably | medium | Pre-commit grep for Nat-typed usages of `RawTerm.universeCode` |
| **R-γ2** | Effects.EffectRow ordering issue (`[read, write]` vs `[write, read]`) | medium | Defer row-quotient handling to K15; document the row-ordering assumption |
| **R-γ3** | `RawTerm.equivReflIdAtIdMarker` vs `RawTerm.equivIntro` runtime collision | low | Grep `equivIntro.*lam.*var` to find dispatchers; update to new markers |
| **R-γ4** | Pre-flight succeeds, refactor unnecessary | high (positive) | Do pre-flight BEFORE committing to Phase γ |
| **R-γ5** | Cascade size underestimated (real count 60-80 files) | medium | Initial `git grep -l` to get actual file list |

---

## 7. Hand-off context for Codex

### Key invariants Codex must preserve

1. **Zero-axiom discipline**: every theorem in `LeanFX2/*` must report "does not depend on any axioms" via `#print axioms`. No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical.choice` allowed.

2. **ASCII-only identifiers, ≥4 char names**: per `WORKING_RULES.md`.

3. **`simp only` / `dsimp only`, not bare `simp`/`unfold`** in any case split over Term/RawTerm — per the performance discipline in `lean-fx-2/CLAUDE.md`.

4. **Every commit must build green** with `lake build LeanFX2`. Audit (`LeanFX2Audit`) at end of each phase.

5. **`@[reducible]` markers** on substitution-shape helpers if Codex introduces new helpers.

### Critical files to read before starting

1. `/root/iprit/FX/lean-fx-2/CLAUDE.md` — kernel discipline
2. `/root/iprit/FX/lean-fx-2/AXIOMS.md` — zero-axiom policy
3. `/root/iprit/FX/lean-fx-2/WORKING_RULES.md` — naming + style
4. `/root/iprit/FX/lean-fx-2/LeanFX2/Foundation/RawTerm.lean` — the data layer being enriched
5. `/root/iprit/FX/lean-fx-2/LeanFX2/Foundation/Universe.lean` — UniverseLevel structure
6. `/root/iprit/FX/lean-fx-2/LeanFX2/Foundation/Effect.lean` — EffectRow + CanPerform
7. `/root/iprit/FX/lean-fx-2/LeanFX2/Term/RenameInjective/InductiveArms.lean` — the T2 per-arm proofs
8. `/root/iprit/FX/lean-fx-2/LeanFX2/Term/RenameInjective/BinderInversions.lean` — the lam_pi_inv + renamedLamPi_ne_renamedFunextReflCast infrastructure for Phase α
9. `/root/iprit/FX/lean-fx-2/LeanFX2/Term/RenameInjective/CastInversions.lean` — the `_raw_inv` PSum pattern for Phase β
10. `/root/iprit/FX/lean-fx-2/LeanFX2/Smoke/AuditRenameInjectivityWalls.lean` — the wall counterexamples (to be updated)

### Decision points where Codex should ask

1. **Phase α — `Ty.weaken_injective`**: if not shipped, ask whether to ship as a standalone lemma or inline into the funextRefl arm.

2. **Phase β — vacuous wall audit**: for each of the 4 arms, before writing the proof, verify the supposed counterexample is truly uninhabitable (use the constructive probe in `Smoke/AuditRenameInjectivityWalls.lean` as a template). If any wall is actually genuine, escalate to Phase γ for that ctor.

3. **Phase γ pre-flight outcome**: if pre-flight succeeds for all 4 walls, abort the cascade refactor. Document the proof-technique fix and update task #1953 to closed.

4. **Phase γ — `equivReflIdAtId` carrier removal**: if the typed `carrier` parameter has no downstream consumers, prefer removing it over the marker-ctor approach. This is the cleanest fix architecturally.

5. **Phase γ — `equivReflId` and `equivIntroHet` collision**: these two stay on `RawTerm.equivIntro (lam var0) (lam var0)`. Document why they're harmless (vacuous multi-inhabitancy per Agent 1's analysis) rather than forcing them onto markers too.

---

## 8. Expected outcome (all phases combined)

After Phases α + β + γ ship:

- **T2 = 78/78**: every `Term.rename_injective_arm_*` ships zero-axiom
- **HeadlineRenameInjInv** (#1985): the 250-LoC manual blocker can be replaced with a 78-case T2 dispatch (now feasible)
- **78 `isAggregatorTotal_*` wrappers** (#1986): can be deleted (replaced by T2 + dispatch)
- **K19.x bridges**: encoders from LeanFX2 to FX1 become cleaner — raw projection now uniquely encodes typed structure
- **K14 e-graph canonicalization**: typed terms equivalent under raw projection are now distinguishable, simplifying canonical-form analysis
- **η pipeline** (#1979-#1981): mostly independent of T2; T9/T10/T11/T12 use T1 (not T2) for the η-unblock chain
- **`Smoke/AuditRenameInjectivityWalls.lean`**: deleted or repurposed as a historical note

**Net code change**: estimate +200 LoC (new ctor signatures + 4 enriched arms + Phase β inversions), -3500 LoC (deleted `_with_*` wrappers + simplified inversion code) = -3300 LoC net.

**Wall-clock**: ~1 week for one engineer, mostly mechanical cascade work after the design spikes.

---

## 9. Sign-off checklist

### Phase α

- [ ] `Ty.weaken_injective` available (shipped existing or added)
- [ ] `Term.rename_injective_arm_funextRefl` ships zero-axiom
- [ ] `Smoke/AuditCumulUpEquivApplyArms.lean` updated with `#print axioms`
- [ ] `lake build LeanFX2 LeanFX2Audit` green
- [ ] T2 = 70/78 confirmed

### Phase β

- [ ] Each of 4 vacuous walls audited to confirm uninhabitable counterexample
- [ ] `LeanFX2/Term/RenameInjective/EtaFamilyInversions.lean` shipped
- [ ] All 4 arms (`equivReflId`, `funextReflAtId`, `equivIntroHet`, `funextIntroHet`) ship zero-axiom
- [ ] `Smoke/AuditCumulUpEquivApplyArms.lean` updated
- [ ] `Smoke/AuditRenameInjectivityWalls.lean` updated to remove vacuous walls
- [ ] `lake build LeanFX2 LeanFX2Audit` green
- [ ] T2 = 74/78 confirmed

### Phase γ

- [ ] Pre-flight (§3.2-3.3) executed; outcome documented
- [ ] **If pre-flight succeeds**: all 4 free-data walls ship via proof-technique fix; no kernel refactor
- [ ] **If pre-flight fails**: all 4 RawTerm ctors enriched per §3.5
- [ ] All ~50 consumer files updated and audited green
- [ ] All 4 free-data T2 arms ship zero-axiom
- [ ] T2 = 78/78 confirmed via `#print axioms` on all 78 arms
- [ ] `Smoke/AuditRenameInjectivityWalls.lean` deleted or repurposed
- [ ] `InductiveArms.lean` wall docstrings deleted
- [ ] Task #1953 closed with link to final commit
- [ ] `lake build LeanFX2 LeanFX2Audit` green
- [ ] No new axioms in any shipped theorem (verify via `Tools/StrictHarness`)

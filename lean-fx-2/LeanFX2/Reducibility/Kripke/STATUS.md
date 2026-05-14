# Kripke Refactor — Honest Status

Worktree: `/root/iprit/FX-kripke` on branch `kripke-refactor`.

## What ships in this branch (zero-axiom verified)

13 declarations, all pinned in `LeanFX2/Smoke/AuditKripke.lean`:

| Decl | LoC | Description |
| --- | --- | --- |
| `ReducibleKBody` | ~40 | per-Ty arm dispatcher (25 ctors enumerated) |
| `ReducibleK` | ~12 | step-indexed Kripke Tait predicate |
| `ReducibleK.zero_eq_true` | 5 | step-0 unfold |
| `ReducibleK.succ_{unit,bool,nat,empty,interval}_iff_sn` | 5 × 8 | closed-leaf unfold |
| `ReducibleK.weaken_{unit,bool,nat,empty,interval}` | 5 × ~16 | closed-leaf world weakening |

All 13 verified `does not depend on any axioms`.

## Architectural decisions

1. **Step-indexed encoding** (Ahmed 2006, Iris-style) chosen after direct Ty-recursive encoding rejected by Lean 4 v4.29.1 structural-recursion checker (renamed Ty not structural sub-term; `termination_by` banned by GatesCore line 51).

2. **Nat-Ty match split** via `ReducibleKBody` helper avoids the multi-arity match propext leak (memory `feedback_lean_match_arity_axioms`).

3. **Full ctor enumeration** (no wildcards) in `ReducibleKBody` per memory `feedback_lean_zero_axiom_match` rule 1.

4. **Closed leaves** use plain SN; arrow uses Kripke closure quantifying over `TermRenaming` into any future context; remaining 17 ctors ship SN-only fallback for PoC.

## What's NOT yet shipped (the rest of the refactor)

In realistic order of next implementation:

### Phase A — predicate completion (~2-3 days)
- Port remaining 17 Ty arms from SN-fallback to their full Kripke closures (sigmaTy, piTy, id-family, listType/optionType/eitherType, path/glue, oeq/idStrict, equiv, refine, record/codata/session/effect, modal)

### Phase B — CR2/CR3 (~3-5 days)
- `ReducibleK.cr2` — forward step closure (analogous to single-world but with step-decrease + renaming threading)
- `ReducibleK.cr3` — neutral SN closure
- Per-Ty CR2/CR3 instances (25 arms each)

### Phase C — arrow + binder weakening (~1-2 weeks)
- `ReducibleK.weaken_arrow` — the HEADLINE win. Direct from Kripke quantification, no bypass needed.
- Same for piTy and other binder-quantifying arms
- This is where the bypass route (3000 LoC of IsIdentityLike infrastructure on master) is replaced by a few hundred LoC

### Phase D — ReducibleSubstK (~3-5 days)
- `ReducibleSubstK` — substitution-reducibility predicate
- `ReducibleSubstK.singleton`, `.identity` — base cases (trivial)
- `ReducibleSubstK.lift` — the LOAD-BEARING successor case. Now direct via Kripke weakening rather than blocked at `ReducibleSubst.lift` on master.

### Phase E — fundamental theorem (~1-2 weeks)
- Re-state fundamental theorem against `ReducibleK` instead of `Reducible`
- Port ~25 Term-ctor cases (var/unit/lam/app/lamPi/appPi/pair/fst/snd/recordIntro/recordProj/refineIntro/refineElim/boolElim/natElim/natRec/listElim/optionMatch/eitherMatch/idJ/oeqJ/idStrictRec/equivApply/codataDest/modIntro/modElim/subsume + cubical cases)

### Phase F — headline + cleanup (~1 week)
- `Term.strong_normalization` via Kripke fundamental at identity Kripke substitution at any step
- Retire bypass infrastructure: delete `IsIdentityLike`-related ~3000 LoC + 57 `fundamental_identity_X` helpers
- Migrate downstream consumers (217 generic `fundamental_X` + 728 total Reducibility theorems)

## Realistic completion timeline

**At the pace of recent Codex K12.20.U commits (~80/day)**: 4-6 weeks of focused single-stream work.

The PoC commits in this branch (3 atomic commits totaling ~350 LoC of zero-axiom Lean) prove the architectural decision (step-indexed Kripke) is viable. Lean 4 v4.29.1's restrictions don't kill it. The propext+match traps were the real obstacles and are navigated.

## Compare to bypass route (Codex on master)

| Metric | Bypass (master) | Kripke (this branch) |
| --- | --- | --- |
| Closed-leaf weakening | shipped via `IsIdentityLike` invariant across 77 ctors | shipped in 5 × ~16 LoC theorems |
| Arrow weakening | FAILS — fundamental architectural blocker | direct from predicate (Phase C) |
| `ReducibleSubst.lift` successor | FAILS — the K12.20.U3.monotone in_progress (#1944) | direct from arrow weakening (Phase D) |
| `fundamental_lam` | identity-only bypass route (~3000 LoC plumbing) | substitution-parametric direct (Phase E) |
| `Term.strong_normalization` | shippable for identity substitution only | full general after Phase F |
| Total LoC delta vs current Reducibility/ | ~+5000 (bypass plumbing) | ~+3000 / ~-3000 (replaces bypass, no net add) |

## Commits in this branch

* `ada4487` Kripke refactor PoC — step-indexed ReducibleK predicate (zero-axiom)
* `7cde127` Kripke refactor — ReducibleK extraction lemmas (closed leaves)
* `b43d21c` Kripke refactor — closed-leaf world weakening (zero-axiom)

All build clean: `lake build LeanFX2.Reducibility.Kripke.Predicate LeanFX2.Reducibility.Kripke.Basic LeanFX2.Reducibility.Kripke.Weaken LeanFX2.Smoke.AuditKripke`.

# Kripke Refactor — Honest Status

Now on master under `LeanFX2/Reducibility/Kripke/`.

## What ships today (zero-axiom verified)

138 declarations under `LeanFX2.Reducibility.Kripke.*` + `LeanFX2.Term.X_strong_normalization_via_kripke` user-facing headlines, all pinned in `LeanFX2/Smoke/AuditKripke.lean`.

| File                | Decls | Description                                                            |
| ------------------- | ----- | ---------------------------------------------------------------------- |
| `Predicate.lean`    | 2     | `ReducibleKBody` + `ReducibleK` (25-Ty enumerated arms)               |
| `Basic.lean`        | 6     | step-0/succ unfold lemmas for closed leaves                            |
| `Project.lean`      | 5     | `sn_of_{unit,bool,nat,empty,interval}` SN projection                  |
| `Weaken.lean`       | 5     | closed-leaf world weakening                                            |
| `Monotone.lean`     | 5     | step-index monotonicity                                                |
| `SNClosure.lean`    | 7     | CR2 forward closure + raw/typed `step_closure`                         |
| `Arrow.lean`        | 2     | `arrow_sn` + `arrow_apply` (Kripke closure-application combinator)     |
| `Fundamental.lean`  | 55    | per-ctor `fundamental_X` + `fundamental_X_sn` preservation wrappers    |
| `Headline.lean`     | 51    | user-facing `Term.X_strong_normalization_via_kripke` per Term ctor     |

All 138 audit gates report `does not depend on any axioms`.

## Coverage matrix (per Term ctor)

| Term ctor                          | Fundamental    | Headline       |
| ---------------------------------- | -------------- | -------------- |
| unit / boolTrue / boolFalse        | yes            | yes            |
| natZero / natSucc                  | yes            | yes            |
| var (5 closed types)               | yes            | yes            |
| pair / fst / snd                   | yes (SN-only)  | yes            |
| lam / lamPi                        | yes (SN-only)  | yes            |
| modIntro / subsume                 | yes (SN-only)  | yes            |
| recordIntro / recordProj           | yes (SN-only)  | yes            |
| refineIntro / refineElim           | yes (SN-only)  | yes            |
| codataUnfold                       | yes (SN-only)  | yes            |
| sessionRecv / sessionSend          | yes (SN-only)  | yes            |
| intervalOpp / Meet / Join          | yes            | yes            |
| listNil / optionNone               | yes            | yes            |
| listCons / optionSome / either(In) | yes (SN-only)  | yes            |
| refl / oeqRefl / idStrictRefl      | yes (SN-only)  | yes            |
| cumulUp                            | yes (SN-only)  | yes            |
| equivReflId / uaToEquiv            | yes (SN-only)  | yes            |
| 6 type-codes                       | yes (SN-only)  | yes            |
| pathLam / glueIntro / glueElim     | yes (SN-only)  | yes            |
| equivIntroHet                      | yes (SN-only)  | yes            |
| funextRefl / funextReflAtId        | yes (SN-only)  | yes            |
| oeqFunext                          | yes (SN-only)  | yes            |
| effectPerform                      | yes (SN-only)  | yes            |
| uaIntroHet / equivReflIdAtId       | yes (SN-only)  | yes            |
| **app / appPi (Π-elim)**           | NO             | NO             |
| **boolElim / natElim / natRec**    | NO             | NO             |
| **listElim / optionMatch**         | NO             | NO             |
| **eitherMatch**                    | NO             | NO             |
| **idJ / oeqJ / idStrictRec**       | NO             | NO             |
| **equivApply / pathApp**           | NO             | NO             |
| **transp / hcomp (cubical β)**     | NO             | NO             |
| **modElim**                        | NO             | NO             |

## Architectural decisions

1. **Step-indexed encoding** (Ahmed 2006, Iris-style) chosen after direct Ty-recursive encoding rejected by Lean 4 v4.29.1 structural-recursion checker.

2. **Nat-Ty match split** via `ReducibleKBody` helper avoids the multi-arity match propext leak.

3. **Full ctor enumeration** (no wildcards) per `feedback_lean_zero_axiom_match` rule 1.

4. **Closed leaves** use plain SN; arrow uses Kripke closure quantifying over `TermRenaming` into any future context; remaining 17 ctors ship SN-only fallback for PoC compatibility.

5. **`fundamental_X_sn` wrapper pattern**: per-ctor SN-preservation helpers that delegate to existing `Term.X_isStronglyNormalizing` (sourced from `Reducibility/Foundation.lean` and friends).  Provides Kripke-namespace SN-headlines without inflight rewrites of the underlying SN proofs.

## What's NOT yet shipped

### Phase A — predicate completion (~2-3 days)
- Port remaining 17 Ty arms from SN-fallback to full Kripke closures (sigmaTy, piTy, id-family, listType/optionType/eitherType, path/glue, oeq/idStrict, equiv, refine, record/codata/session/effect, modal)

### Phase B — eliminator fundamentals (~1-2 weeks)
- `ReducibleK.fundamental_app` / `fundamental_appPi` via `arrow_apply` at identity renaming
- `fundamental_boolElim` / `natElim` / `natRec` / `listElim` / `optionMatch` / `eitherMatch` — ι-elim with Kripke motive
- `fundamental_idJ` / `oeqJ` / `idStrictRec` — J family
- `fundamental_equivApply` / `pathApp` — HoTT eliminators
- `fundamental_transp` / `hcomp` — cubical β rules
- `fundamental_modElim` — modal elim

### Phase C — ReducibleSubstK (~3-5 days)
- `ReducibleSubstK.{singleton,identity,lift}` substitution-reducibility carrier
- Generic Kripke version that uses the step-indexed predicate uniformly

### Phase D — bypass extraction (~1 week)
- Move `Term.X_isStronglyNormalizing` SN-helper family from `Reducibility/Foundation.lean` into a new `Term/SN/` module (or similar) that does NOT depend on `Reducible`/`ReducibleSubst`
- This unblocks bypass deletion: once Kripke fundamentals reference `Term/SN/` not `Reducibility/Foundation`, the legacy `Reducible`-predicate infrastructure is genuinely unused

### Phase E — bypass deletion (~1 day)
- Delete `Reducibility/{Basic,Classifier,Foundation,Predicate,StableBase,Neutral,NeutralSN*,TypedCR2*,Fundamental*}.lean` (~77 files)
- Delete `Smoke/AuditReducibility/` (11 files)
- Rewrite `Reducibility.lean` to only re-export `Kripke/`

### Phase F — strong normalization headline (~1 week)
- `Term.strong_normalization` via Kripke fundamental at identity Kripke substitution at any step count
- Closes M04 (#1273) zero-axiom

## Honest blockers

* **Bypass deletion is NOT a one-step operation.**  The SN-helper family in `Foundation.lean` is shared between Kripke and the legacy `Reducible`/`ReducibleSubst` infrastructure.  Phase D extraction is the prerequisite.
* Eliminator fundamentals (Phase B) need the full Kripke chain via `arrow_apply` — not just SN-preservation wrappers like the intro family.
* `K12.20.U3.monotone` blocker (#1944) still applies on the bypass side; Kripke route sidesteps it but doesn't unblock the legacy path.

## Verification

```bash
lake build LeanFX2.Reducibility.Kripke LeanFX2.Smoke.AuditKripke
```

Reports all 138 audit gates as `does not depend on any axioms`.

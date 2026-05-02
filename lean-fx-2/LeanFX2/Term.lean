import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.Subst
import LeanFX2.Foundation.Context

/-! # Term — the raw-aware typed term inductive

The kernel's load-bearing inductive.  Every Term value carries its
raw form as a **type-level index**:

```lean
Term : (ctx : Ctx mode level scope) → (ty : Ty level scope) →
       (raw : RawTerm scope) → Type
```

Each constructor pins the raw form structurally:

| Ctor | Raw form (type index) |
|---|---|
| `var i` | `RawTerm.var i` |
| `unit` | `RawTerm.unit` |
| `lam body` | `RawTerm.lam body.raw` |
| `app fn arg` | `RawTerm.app fn.raw arg.raw` |
| `lamPi body` | `RawTerm.lam body.raw` |
| `appPi fn arg` | `RawTerm.app fn.raw arg.raw`, type = `cod.subst (Subst.singleton dom arg.raw)` |
| `pair fv sv` | `RawTerm.pair fv.raw sv.raw` |
| `fst p` | `RawTerm.fst p.raw` |
| `snd p` | `RawTerm.snd p.raw`, type = `secondType.subst (Subst.singleton firstType (RawTerm.fst p.raw))` |
| `boolTrue/False` | `RawTerm.boolTrue/False` |
| `boolElim s t e` | `RawTerm.boolElim s.raw t.raw e.raw` |
| `natZero/Succ` | `RawTerm.natZero / RawTerm.natSucc p.raw` |
| `natElim/natRec` | matching `RawTerm.<elim>` |
| `listNil/Cons/Elim` | matching |
| `optionNone/Some/Match` | matching |
| `eitherInl/Inr/Match` | matching |
| `refl rt` | `RawTerm.refl rt`, type = `Ty.id carrier rt rt` |
| `idJ b w` | `RawTerm.idJ b.raw w.raw` |
| `modIntro / modElim / subsume` | Layer 6 — see `Modal/Foundation.lean` |

## Why this shape

The current lean-fx kernel has `Term : Ctx → Ty → Type` with
`Term.toRaw` defined separately by structural recursion.  This
loses the raw form at every typed substitution (because
`Subst.singleton.forRaw = dropNewest` placeholder), making the
typed↔raw bridge unprovable for refl-bearing β-redexes.

Carrying the raw form as a type index makes:
* `Term.toRaw t = t.raw` is **rfl** (the projection IS the index)
* `Term.toRaw_rename`, `Term.toRaw_subst` etc. all become rfl
* The bridge β cases close with one line: `RawStep.par.<ctor> witnesses`
* No `RawConsistent` threading required (every TermSubst is
  raw-consistent because forRaw is constrained by Term values' raws)

## TermRenaming

A `TermRenaming Γ Δ ρ` is a position-equality witness: for every
`i : Fin scope`, `varType Δ (ρ i) = (varType Γ i).rename ρ`.  Used by
`Term.rename` to lift the renaming under a binder via
`TermRenaming.lift`.

## Decidable equality

DecidableEq via hand-written instance (no `deriving` — match-compiler
propext risk per `feedback_lean_zero_axiom_match.md`).

## Diff from lean-fx

* lean-fx's Term lacks the raw index.  This file adds it.
* lean-fx's `Term.toRaw` is a 60-line structural recursion + many
  bridge lemmas.  lean-fx-2 collapses to `Term.toRaw t = raw` (Layer 1
  in `Term/ToRaw.lean`).
* W9.B1.1 added `resultEq` parameter to `Term.appPi`; W9.B1.2 added
  to `Term.snd`.  These are SCAFFOLDING for inline migration —
  lean-fx-2 doesn't have them.  Type index supersedes.

## Zero-axiom commitment

Term inductive is well-formed under Lean 4's positivity check (verified
in `LeanFX/Sketch/Wave9.lean` prototype).  Decidable equality
hand-written.  No propext, no Quot.sound.
-/

namespace LeanFX2

-- TODO Phase 2: `Term : Ctx → Ty → RawTerm → Type` inductive per
--   the table above.  Mirror `LeanFX/Sketch/Wave9.lean`'s blueprint
--   but extend to all 28 constructors.
-- TODO Phase 2: TermRenaming structure + lift + identity + weaken
-- TODO Phase 2: smart constructors (e.g., Term.var without explicit raw
--   since elaboration auto-fills)
-- TODO Phase 2: DecidableEq Term via hand-written instance

end LeanFX2

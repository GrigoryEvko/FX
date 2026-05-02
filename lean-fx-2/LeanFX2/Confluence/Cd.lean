import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.Compat

/-! # Confluence/Cd — complete development

`Term.cd : Term ctx ty raw → Term ctx ty (raw.cd)` — fires every
visible redex in one structural pass.  The Tait-Martin-Löf vehicle
for proving the diamond property.

## Contents

```lean
def Term.cd : {ctx : Ctx ...} → {ty : Ty ...} → {raw : RawTerm scope} →
    Term ctx ty raw → Term ctx ty raw.cd
```

Match arms by Term constructor:

* `var i` → `var i` (no redex)
* `unit` → `unit`
* `lam body` → `lam body.cd`
* `app fn arg` → if `fn.cd = Term.lam body'`, fire β: `subst0 body' arg.cd`; else `app fn.cd arg.cd`
* `lamPi body` → `lamPi body.cd`
* `appPi fn arg` → if `fn.cd = Term.lamPi body'`, fire β; else `appPi fn.cd arg.cd`
* `pair fv sv` → `pair fv.cd sv.cd`
* `fst pairTerm` → if `pairTerm.cd = Term.pair fv' _`, fire β: `fv'`; else `fst pairTerm.cd`
* `snd pairTerm` → analogous
* `boolElim scrutinee thenBr elseBr` → fire ι if scrutinee.cd is boolTrue/False; else cong
* `natElim/natRec/listElim/optionMatch/eitherMatch` → analogous ι firing
* `refl r` → `refl r`
* `idJ baseCase witness` → if `witness.cd = refl _`, fire ι: `baseCase.cd`; else cong

The "if" matches in the redex-firing arms use `Term.toRaw`-projection
matching (since toRaw is rfl, this is a clean match on the type
index).  Per lean-fx's `feedback_lean_zero_axiom_match.md` empirical
recipe, full enumeration on the toRaw-shape avoids propext leaks.

## raw.cd

The raw side of cd:

```lean
def RawTerm.cd : RawTerm scope → RawTerm scope
```

For each typed cd arm, the raw side mirrors structurally.  Critical
property: `(Term.cd t).toRaw = t.toRaw.cd` is **rfl** (raw index
propagates through Term.cd's match by construction).

## Dependencies

* `Reduction/ParRed.lean` — Term.cd's β/ι arms produce values used
  by Step.par
* `Reduction/Compat.lean` — Term.cd's substitution machinery uses
  subst-compat lemmas

## Downstream consumers

* `Confluence/CdLemma.lean` — `Step.par t t' → Step.par t' (Term.cd t)`
* `Confluence/Diamond.lean` — diamond proof uses Term.cd

## Diff from lean-fx

* Inline cd_<head>_redex helpers (lean-fx had separate
  `CompleteDevelopmentRedex.lean` with one helper per head).  In
  lean-fx-2 we inline; the constructor-shape match avoids the
  propext-leak that motivated the helper extraction in lean-fx.
* Drop W9.B1.1/B1.2 `resultEq` parameter scaffolding
* Verify β-firing arms produce the right Ty type (no cast needed
  because subst0 in lean-fx-2 produces the right type by index)

Target: ~500 lines.

## Implementation plan (Phase 4)

1. Define `RawTerm.cd` first (no typing, just structural reduction)
2. Define `Term.cd` mirroring RawTerm.cd
3. Verify `(Term.cd t).toRaw = t.toRaw.cd` by `rfl` smoke test
4. Match arm casts use only `Ty.weaken_subst_singleton` (β-app)
-/

namespace LeanFX2

end LeanFX2

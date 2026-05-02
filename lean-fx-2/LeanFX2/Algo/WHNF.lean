import LeanFX2.Reduction.Step

/-! # Algo/WHNF — weak head normal form classifier

```lean
def Term.isWHNF : Term ctx ty raw → Bool
```

Decides whether a term is in **weak head normal form** — that is,
whether the head constructor is a value-form (`Term.lam`, `Term.pair`,
`Term.refl`, etc.) rather than an eliminator applied to a non-value
(`Term.app (Term.lam _) _` is NOT in WHNF — it's a β-redex).

## WHNF classifications

| Term head | WHNF? |
|---|---|
| `var` | yes (head reduction stops at variables) |
| `unit`, `boolTrue`, `boolFalse`, `natZero` | yes (canonical) |
| `lam`, `lamPi`, `pair`, `refl` | yes (value introductions) |
| `natSucc t` | yes (canonical succ form) |
| `listNil`, `listCons _ _`, `optionNone`, `optionSome _`, etc. | yes |
| `app fn arg` where `fn` is `Term.lam` | NO (β-redex) |
| `app fn arg` where `fn` is var/app | yes (neutral) |
| `appPi`, `fst`, `snd`, `boolElim`, `natElim`, etc. on values | NO (ι-redex) |
| `idJ base (refl _)` | NO (ι-redex) |
| `modIntro/modElim` similar pattern | NO if eliminating intro |

## Why WHNF, not full NF

Decidable conversion (Layer 9 `DecConv`) reduces both sides to WHNF,
compares heads, recurses on sub-terms.  This is faster than reducing
to full normal form.  For the kernel's correctness, WHNF + structural
recursion gives complete decidable conversion (per the Church-Rosser
theorem from Layer 3).

## Dependencies

* `Reduction/Step.lean` — for the redex classification

## Downstream

* `Algo/DecConv.lean` — decidable conversion runs WHNF on both sides
* `Algo/Eval.lean` — fuel-bounded eval steps to WHNF then dispatches

## Implementation plan (Layer 9)

1. Define `isWHNF` by Term ctor enumeration
2. Provide `Term.whnf : Term → Term` that reduces to WHNF (uses Step
   in a fuel loop or via direct β/ι firing)
3. Smoke: identity terms, β-redexes reduce one step

Target: ~150 lines.
-/

namespace LeanFX2.Algo

-- TODO Layer 9: isWHNF predicate
-- TODO Layer 9: whnf reduction
-- TODO Layer 9: smoke tests

end LeanFX2.Algo

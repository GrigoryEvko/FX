import LeanFX2.Foundation.Mode

/-! # RawTerm — untyped well-scoped terms.

`RawTerm scope` is a de Bruijn–indexed term family with `Fin scope`
positions.  No type annotations, no scope-shifting helpers — just the
syntactic skeleton.

## Architectural role

RawTerm is the **type-level index** that makes lean-fx-2's Term
`Term : Ctx → Ty → RawTerm scope → Type` raw-aware.  In lean-fx, RawTerm
existed as a separate inductive with `Term.toRaw : Term Γ T → RawTerm`
as a function — leading to ~30 bridge lemmas needed to commute toRaw
through every operation.  In lean-fx-2, raw form IS the type index,
so `Term.toRaw t` is `t`'s third index — recovered by `rfl`.

## Constructor list

Mirrors the typed `Term`'s constructors (sans type annotations):

* `var (i : Fin scope)`
* `unit`
* `lam (body : RawTerm (scope+1))`
* `app (fn arg : RawTerm scope)`  (covers both arrow and Π apps)
* `pair (first second : RawTerm scope)`
* `fst (pair : RawTerm scope)`
* `snd (pair : RawTerm scope)`
* `boolTrue`, `boolFalse`
* `boolElim (scrut then else : RawTerm scope)`
* `natZero`
* `natSucc (predecessor : RawTerm scope)`
* `natElim (scrut zero succ : RawTerm scope)`
* `natRec (scrut zero succ : RawTerm scope)`
* `listNil`, `listCons (head tail : RawTerm scope)`
* `listElim (scrut nil cons : RawTerm scope)`
* `optionNone`, `optionSome (value : RawTerm scope)`
* `optionMatch (scrut none some : RawTerm scope)`
* `eitherInl (value : RawTerm scope)`, `eitherInr (value : RawTerm scope)`
* `eitherMatch (scrut left right : RawTerm scope)`
* `refl (rawWitness : RawTerm scope)` — Identity-type intro
* `idJ (base witness : RawTerm scope)` — J eliminator
* `modIntro (raw : RawTerm scope)`, `modElim (raw : RawTerm scope)`,
  `subsume (raw : RawTerm scope)` — Modal (Layer 6 references)

## Decidable equality

`deriving DecidableEq` — the recursors-based decision procedure is
propext-free (Lean 4 v4.29.1's auto-derivation works for `Inductive`
families with a single Nat index, per `feedback_lean_zero_axiom_match.md`).

## Dependencies

* `Foundation/Mode.lean` — for `modIntro`/`modElim`/`subsume` to refer
  to a `Modality` (via `Mode` reference; the actual modality is at the
  `Ty` layer, RawTerm just records that this is a modal-flavored ctor).

Note: lean-fx had RawTerm depend ONLY on Mode.Defn.  lean-fx-2 keeps
that minimal-dependency story.

## Downstream

* `Foundation/RawSubst.lean` — substitution algebra on RawTerm
* `Foundation/Subst.lean` — joint substitution carries a `forRaw : RawTermSubst src tgt`
* `Term.lean` — RawTerm is the third type index
* `Reduction/RawPar.lean` — raw parallel reduction (porting from lean-fx)

## Diff from lean-fx

* No changes to constructor list.
* Same `deriving DecidableEq` strategy.
* Same `Fin scope` discipline for variables.

This is one of the few files that ports nearly verbatim from lean-fx.
-/

namespace LeanFX2

-- TODO: RawTerm inductive (per constructor list above)
-- TODO: deriving DecidableEq

end LeanFX2

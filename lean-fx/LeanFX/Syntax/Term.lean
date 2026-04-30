import LeanFX.Syntax.RawTerm
import LeanFX.Syntax.Ty
import LeanFX.Syntax.RawSubst
import LeanFX.Syntax.Subst
import LeanFX.Syntax.Context
import LeanFX.Syntax.TypedTerm
import LeanFX.Syntax.TermSubst
import LeanFX.Syntax.ToRaw
import LeanFX.Syntax.Reduction
import LeanFX.Syntax.Identity
import LeanFX.Syntax.Strengthen
import LeanFX.Syntax.TermStrengthen
import LeanFX.Syntax.CompleteDevelopment
import LeanFX.Syntax.CdDominates
import LeanFX.Syntax.RawCompleteDevelopment
import LeanFX.Syntax.RawCdDominates
import LeanFX.Syntax.ToRawCommute
import LeanFX.Syntax.Smoke

/-! # Syntax umbrella module.

Single-import gateway to the entire `LeanFX.Syntax` layer.
Importing this file pulls in raw and typed terms, types,
substitution, contexts, the reduction relation, complete
development, and the raw/typed bridge.

Dependency order (matches imports above):

  * `RawTerm` — untyped term skeleton (`RawTerm`), de Bruijn
    indices, no Ty index.  The "safety net" layer: when typed
    proofs hit dep-elim walls, the raw counterpart plus
    `toRawBridge` discharges them.
  * `Ty` — kernel types (`Ty`), level + scope indices,
    `Ty.weaken` / `Ty.subst` / `Ty.subst0`.
  * `RawSubst` — `RawSubst`, `RawRenaming` algebra at the
    raw level (composition, identity, lift).
  * `Subst` — typed `Subst` and `Renaming`, the typed
    counterpart of `RawSubst`.
  * `Context` — typing contexts `Ctx mode level scope`,
    `Ctx.cons`, `Ctx.lookup`.
  * `TypedTerm` — the intrinsic `Term ctx ty` inductive with
    its constructor zoo (lam/app/pair/fst/snd/idJ/eliminators
    /etc.).
  * `TermSubst` — the term substitution / renaming algebra
    (compose, pointwise, congruence, weaken, subst0).
  * `ToRaw` — the `Term.toRaw : Term ctx ty -> RawTerm` bridge.
  * `Reduction` — `Step`, `StepStar`, `Conv`, `Step.par`,
    `Step.parStar`, plus the raw counterparts (`RawPar`,
    `RawCdLemma`, `RawConfluence`).
  * `Identity` — `Eq`-on-`Term` smart constructors and
    coherence helpers.
  * `Strengthen` / `TermStrengthen` — context strengthening
    (removing unused binders) at type and term level.
  * `CompleteDevelopment` / `CdDominates` — the typed `Term.cd`
    development function and its domination lemma
    (every `Step.par` lands in `Term.cd`).
  * `RawCompleteDevelopment` / `RawCdDominates` — raw
    counterparts that bypass typed dep-elim walls.
  * `ToRawCommute` — coherence: typed reduction commutes with
    `Term.toRaw` into raw reduction.
  * `Smoke` — sanity smoke tests on the syntax layer (kept in
    the source tree so they recompile with kernel changes).

Convention: zero axioms across the entire syntax layer
(verified per file by `Tools.AuditAll.lean`'s
`#assert_no_axioms` gates).  See `feedback_typed_inversion_breakthrough.md`
in agent memory for the discharge pattern that keeps the
typed Step inversions axiom-free. -/

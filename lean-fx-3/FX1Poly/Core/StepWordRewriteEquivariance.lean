import FX1Poly.Core.StepWordRewriteSoundness
import FX1Poly.Core.StepRename
import FX1Poly.Core.StepSubst

/-! # FX1Poly/Core/StepWordRewriteEquivariance
    — rename/subst-equivariance of the Step→word bridge + system-level inversion

The forward soundness `Step a b ⟹ FxWordRewritesOneStep fxStepSystem a.toCode b.toCode` lives in
`StepWordRewriteSoundness`.  This file gives its two complementary halves:

* **rename/subst-equivariance** — the soundness bridge commutes with the term renaming and substitution actions,
  realized via the shipped `Step.rename` / `Step.subst` / `StepStar.rename` closures; and the generated system
  `fxStepSystem` is closed under both actions.  This is the substantive metatheory: the word-rewriting image of a
  reduction is stable under renaming and substitution of the reduction's terms.
* **inversion** — every rule of `fxStepSystem` comes from an actual FX reduction (`fxStepSystem_imp_step`), and
  every such rule is non-degenerate (non-empty sides, from `toCode_ne_nil`).

## The honest scope of "completeness"

Full word→Step completeness — `FxWordRewritesOneStep fxStepSystem w1 w2 ⟹` (decode w1, w2 are terms related by
`Step`) — is NOT proved here, and is genuinely BLOCKED at this layer for two reasons:

1. The free word monoid `List Nat` is more permissive than the term algebra: a `underLeftContext` / `underRightContext`
   rewrite splits a word at an arbitrary position `prefixWord ++ sourceWord`, which need not correspond to any
   term sub-context (the term-code words are not closed under arbitrary concatenation splits).
2. `RawTerm.toCode` is NOT injective: `payloadToNat` collapses every non-`Nat`/`Fin` payload to `0` (e.g. all
   `gen_universeCode` payloads — `LevelExpr × UniverseFlag` — map to `0`), so distinct universe codes share a
   word.  Decoding a word back to a unique term therefore fails on the universe-code fragment.

So completeness is restricted to the SYSTEM level (a rule of `fxStepSystem` IS a Step code-pair, proved here) and
the full word→term inversion is deferred to the typed-SN critical path (it needs a decode on the rigid fragment,
per `core_raw_sn_false_natrec`).  Stating this honestly rather than proving a false full-completeness theorem.

## Zero-axiom verification

The equivariance lemmas are direct applications of the shipped `Step.rename` / `Step.subst` / `StepStar.rename`
followed by the word-rewrite soundness / the rule-map membership; the inversion is the definitional projection of
`fxStepSystem`; the non-degeneracy is `obtain` + `rw` + `toCode_ne_nil`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- **rename-equivariance (single step)**: renaming the redex/reduct and encoding gives a one-step word rewrite,
via the renamed reduction `Step.rename`. -/
theorem Step.toWordRewrite_rename {sourceScope targetScope : Nat}
    {redex reduct : RawTerm sourceScope}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (step : Step redex reduct) :
    FxWordRewritesOneStep fxStepSystem
      (RawTerm.rename rawRenaming redex).toCode
      (RawTerm.rename rawRenaming reduct).toCode :=
  (Step.rename rawRenaming step).toWordRewrite

/-- **rename-equivariance (many step)**: renaming a reduction sequence and encoding gives a word-rewrite
sequence, via `StepStar.rename`. -/
theorem StepStar.toWordRewrites_rename {sourceScope targetScope : Nat}
    {startTerm finalTerm : RawTerm sourceScope}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (steps : StepStar startTerm finalTerm) :
    FxWordRewritesMany fxStepSystem
      (RawTerm.rename rawRenaming startTerm).toCode
      (RawTerm.rename rawRenaming finalTerm).toCode :=
  (StepStar.rename rawRenaming steps).toWordRewrites

/-- **subst-equivariance (single step)**: substituting in the redex/reduct and encoding gives a one-step word
rewrite, via the substituted reduction `Step.subst`. -/
theorem Step.toWordRewrite_subst {sourceScope targetScope : Nat}
    {redex reduct : RawTerm sourceScope}
    (sigma : RawTermSubst sourceScope targetScope)
    (step : Step redex reduct) :
    FxWordRewritesOneStep fxStepSystem
      (RawTerm.subst sigma redex).toCode
      (RawTerm.subst sigma reduct).toCode :=
  (Step.subst sigma step).toWordRewrite

/-- The generated system is **closed under the term-rename action**: the renamed reduction's code pair is again a
system rule. -/
theorem fxStepSystem_rename_mem {sourceScope targetScope : Nat}
    {redex reduct : RawTerm sourceScope}
    (rawRenaming : RawRenaming sourceScope targetScope)
    (step : Step redex reduct) :
    fxStepSystem ⟨(RawTerm.rename rawRenaming redex).toCode,
      (RawTerm.rename rawRenaming reduct).toCode⟩ :=
  (Step.rename rawRenaming step).inducedRewriteRule_mem_fxStepSystem

/-- The generated system is **closed under the term-subst action**: the substituted reduction's code pair is
again a system rule. -/
theorem fxStepSystem_subst_mem {sourceScope targetScope : Nat}
    {redex reduct : RawTerm sourceScope}
    (sigma : RawTermSubst sourceScope targetScope)
    (step : Step redex reduct) :
    fxStepSystem ⟨(RawTerm.subst sigma redex).toCode,
      (RawTerm.subst sigma reduct).toCode⟩ :=
  (Step.subst sigma step).inducedRewriteRule_mem_fxStepSystem

/-- **System-level inversion**: every rule of the generated system comes from an actual FX reduction (the rule's
two sides are the codes of the reduction's redex and reduct).  The system-level completeness — full word→term
inversion is blocked by `toCode` payload-collapse and the free word monoid (see the module docstring). -/
theorem fxStepSystem_imp_step {rule : FxTermRewriteRule} (mem : fxStepSystem rule) :
    ∃ (scope : Nat) (redex reduct : RawTerm scope),
      Step redex reduct
        ∧ rule.leftHandSide = redex.toCode
        ∧ rule.rightHandSide = reduct.toCode :=
  mem

/-- Every system rule has a **non-empty left side** (derived from the inversion + `toCode_ne_nil`) — the system
contains no degenerate rules. -/
theorem fxStepSystem_leftHandSide_ne_nil {rule : FxTermRewriteRule}
    (mem : fxStepSystem rule) : rule.leftHandSide ≠ [] := by
  obtain ⟨_scope, redex, _reduct, _step, lhsEq, _rhsEq⟩ := mem
  rw [lhsEq]
  exact toCode_ne_nil redex

/-- Every system rule has a **non-empty right side**. -/
theorem fxStepSystem_rightHandSide_ne_nil {rule : FxTermRewriteRule}
    (mem : fxStepSystem rule) : rule.rightHandSide ≠ [] := by
  obtain ⟨_scope, _redex, reduct, _step, _lhsEq, rhsEq⟩ := mem
  rw [rhsEq]
  exact toCode_ne_nil reduct

end FX1Poly.Core

import LeanFX2.Confluence.Cd
import LeanFX2.Confluence.CdLemma
import LeanFX2.Confluence.Diamond
import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Confluence.CanonicalForm
import LeanFX2.HoTT.Univalence
import LeanFX2.HoTT.Funext

/-! # Smoke/AuditPhase12AB8Cascade — confluence cascade for eqType/eqArrow.

Phase 12.A.B8.5 (CUMUL-8.5).  Audits the typed-input/raw-output
confluence pipeline at `Step.eqType` / `Step.eqArrow` (the
Univalence and Funext rfl-fragment Step ctors), demonstrating that
the Phase 4 base infrastructure (commit `b4087c6b`) auto-handles
the new ctors WITHOUT any per-ctor extension — same architectural
payoff as `Step.cumulUpInner` (audited in
`AuditPhase12AB18CumulConfluence`).

## Why no per-ctor extension is needed

The Phase 4 base ships the typed-input/raw-output confluence
pipeline as a **uniform** projection through `Step.par.toRawBridge`:

* `Term.cdRaw` — body is `RawTerm.cd rawForm`, polymorphic over
  the typed Term's raw projection.
  - `Term.equivReflIdAtId` projects to
    `RawTerm.equivIntro (lam (var 0)) (lam (var 0))`.  Its `cd`
    develops both subterms: `equivIntro (cd (lam (var 0))) (cd
    (lam (var 0)))` = `equivIntro (lam (var 0)) (lam (var 0))`
    (since `cd (lam body) = lam (cd body)` and `cd (var 0) =
    var 0`).  Hence the `cd` is equal to the input — an `rfl`
    smoke property.
  - Similarly, `Term.equivReflId carrier`'s raw projection has
    the same constant form, so `cdRaw = RawTerm.equivIntro id id`
    — also `rfl`.
  - `Term.funextReflAtId`/`Term.funextRefl` project to
    `RawTerm.lam (RawTerm.refl applyRaw)`.  `cd` develops:
    `lam (cd (refl applyRaw))` = `lam (refl (cd applyRaw))`.
    The shape is `lam (refl _)` — also definitional.

* `Step.par.cdLemmaRaw` — body is
  `RawStep.par.cd_lemma (Step.par.toRawBridge parallelStep)`.
  The `toRawBridge` arms for `eqType` / `eqArrow` collapse the
  typed parallel step to a `RawStep.par.refl _` on the raw form
  (Bridge.lean:201 / 206), since both source and target raw
  projections are the SAME.  The raw cd_lemma at refl produces
  `RawStep.par someRaw (RawTerm.cd someRaw)` directly.

* `Step.par.diamondRaw` — composes two `toRawBridge` projections
  through `RawStep.par.diamond`.  Each `eqType` / `eqArrow`
  reduces to `RawStep.par.refl _` on the constant raw form, and
  the diamond at refl yields the trivial join
  `RawTerm.cd source` (computed structurally).

* `Step.parStar.churchRosserRaw` / `StepStar.churchRosserRaw` /
  `Conv.canonicalRaw` / `Conv.canonicalForm` — all chain through
  `Step.parStar.toRawBridge` (multi-step lift of toRawBridge),
  so `eqType` / `eqArrow` cascade transparently to a multi-step
  raw refl chain.

## What this audit ships

Six smoke theorems (three for eqType, three for eqArrow):

* **eqType (Univalence) cascade:**
  1. `Step.par.cdLemmaRaw_eqType` (CUMUL-8.5/eqType #1) — applying
     `cdLemmaRaw` to a `Step.par.eqType` produces an explicit raw
     witness.
  2. `Step.par.diamondRaw_eqType_pair` (CUMUL-8.5/eqType #2) —
     diamond at two `eqType` reductions produces a raw join.
  3. `Conv.canonicalForm_Univalence` (CUMUL-8.5/eqType #3) — the
     Univalence theorem's content projects to a raw join through
     `canonicalForm`.

* **eqArrow (Funext) cascade:**
  4. `Step.par.cdLemmaRaw_eqArrow` (CUMUL-8.5/eqArrow #1) —
     same shape, for the funext rfl reduction.
  5. `Step.par.diamondRaw_eqArrow_pair` (CUMUL-8.5/eqArrow #2) —
     diamond at two `eqArrow` reductions produces a raw join.
  6. `Conv.canonicalForm_funext` (CUMUL-8.5/eqArrow #3) — the
     funext theorem's content projects to a raw join through
     `canonicalForm`.

## Audit gates

Every shipped declaration is gated by `#print axioms` reporting
"does not depend on any axioms" under strict policy.

## Honest discipline

Per CLAUDE.md zero-axiom rule: every smoke theorem has a real body.
No `sorry`.  No hypothesis-as-postulate.  The Phase 4 base IS
load-bearing and does the actual work; this audit re-confirms that
load-bearing is uniform across `Step.eqType` / `Step.eqArrow`
without per-ctor extension to Cd / CdLemma / Diamond / ChurchRosser
/ CanonicalForm. -/

namespace LeanFX2

/-! ## Confluence audit gates re-shown for context. -/

#print axioms Term.cdRaw
#print axioms Step.par.cdLemmaRaw
#print axioms Step.par.diamondRaw
#print axioms Step.parStar.churchRosserRaw
#print axioms StepStar.churchRosserRaw
#print axioms Conv.canonicalRaw
#print axioms Conv.canonicalForm

/-! ## CUMUL-8.5 / eqType #1 — `cdLemmaRaw` on `Step.par.eqType`.

The typed parallel step `Step.par.eqType` reduces
`Term.equivReflIdAtId ...` to `Term.equivReflId ...`; both project
to the raw form `RawTerm.equivIntro (lam (var 0)) (lam (var 0))`.
The `toRawBridge` arm gives `RawStep.par.refl _` on this raw form
(Bridge.lean:201).  The raw cd_lemma at refl produces a step from
that raw form to `RawTerm.cd` of itself. -/

/-- `cdLemmaRaw` applied to `Step.par.eqType` produces a raw step
from the (constant) target raw form to `RawTerm.cd source`. -/
theorem Step.par.cdLemmaRaw_eqType
    {mode : Mode} {level scope : Nat}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {context : Ctx mode level scope}
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope) :
    RawStep.par
      (RawTerm.equivIntro
        (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
        (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)))
      (RawTerm.cd
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)))) :=
  Step.par.cdLemmaRaw
    (Step.par.eqType (context := context) innerLevel innerLevelLt
                     carrier carrierRaw)

#print axioms Step.par.cdLemmaRaw_eqType

/-! ## CUMUL-8.5 / eqType #2 — `diamondRaw` on a pair of `eqType` steps.

Two parallel `Step.par.eqType` reductions from the same source
project (via `toRawBridge`) to two `RawStep.par.refl` on the same
constant raw form.  The diamond at this pair returns the cd as
the common raw reduct. -/

/-- Diamond at two parallel `eqType` reductions yields a raw join. -/
theorem Step.par.diamondRaw_eqType_pair
    {mode : Mode} {level scope : Nat}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {context : Ctx mode level scope}
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope) :
    ∃ commonRaw : RawTerm scope,
      RawStep.par
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)))
        commonRaw ∧
      RawStep.par
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)))
        commonRaw :=
  Step.par.diamondRaw
    (Step.par.eqType (context := context) innerLevel innerLevelLt
                     carrier carrierRaw)
    (Step.par.eqType (context := context) innerLevel innerLevelLt
                     carrier carrierRaw)

#print axioms Step.par.diamondRaw_eqType_pair

/-! ## CUMUL-8.5 / eqType #3 — `Conv.canonicalForm` on `Univalence`.

The Univalence theorem's content (`Conv.fromStep Step.eqType`)
projects to a raw join through `canonicalForm`.  The join is the
same constant raw form on both sides — a trivial multi-step
witness anchored on the `equivIntro id id` raw form. -/

/-- Univalence's content yields a raw common reduct via canonicalForm. -/
theorem Conv.canonicalForm_Univalence
    {mode : Mode} {level scope : Nat}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {context : Ctx mode level scope}
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope) :
    ∃ commonRaw : RawTerm scope,
      RawStep.parStar
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)))
        commonRaw ∧
      RawStep.parStar
        (RawTerm.equivIntro
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩)))
        commonRaw :=
  Conv.canonicalForm
    (LeanFX2.Univalence (context := context) innerLevel innerLevelLt
                        carrier carrierRaw)

#print axioms Conv.canonicalForm_Univalence

/-! ## CUMUL-8.5 / eqArrow #1 — `cdLemmaRaw` on `Step.par.eqArrow`.

Mirrors the eqType audit at the funext rfl-fragment.  The raw form
of both source `Term.funextReflAtId` and target `Term.funextRefl`
is `RawTerm.lam (RawTerm.refl applyRaw)`. -/

/-- `cdLemmaRaw` applied to `Step.par.eqArrow` produces a raw step
from the (constant) target raw form to `RawTerm.cd source`. -/
theorem Step.par.cdLemmaRaw_eqArrow
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    RawStep.par
      (RawTerm.lam (RawTerm.refl applyRaw))
      (RawTerm.cd (RawTerm.lam (RawTerm.refl applyRaw))) :=
  Step.par.cdLemmaRaw
    (Step.par.eqArrow (context := context) domainType codomainType applyRaw)

#print axioms Step.par.cdLemmaRaw_eqArrow

/-! ## CUMUL-8.5 / eqArrow #2 — `diamondRaw` on a pair of `eqArrow` steps. -/

/-- Diamond at two parallel `eqArrow` reductions yields a raw join. -/
theorem Step.par.diamondRaw_eqArrow_pair
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    ∃ commonRaw : RawTerm scope,
      RawStep.par
        (RawTerm.lam (RawTerm.refl applyRaw)) commonRaw ∧
      RawStep.par
        (RawTerm.lam (RawTerm.refl applyRaw)) commonRaw :=
  Step.par.diamondRaw
    (Step.par.eqArrow (context := context) domainType codomainType applyRaw)
    (Step.par.eqArrow (context := context) domainType codomainType applyRaw)

#print axioms Step.par.diamondRaw_eqArrow_pair

/-! ## CUMUL-8.5 / eqArrow #3 — `Conv.canonicalForm` on `funext`. -/

/-- funext's content yields a raw common reduct via canonicalForm. -/
theorem Conv.canonicalForm_funext
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (applyRaw : RawTerm (scope + 1)) :
    ∃ commonRaw : RawTerm scope,
      RawStep.parStar
        (RawTerm.lam (RawTerm.refl applyRaw)) commonRaw ∧
      RawStep.parStar
        (RawTerm.lam (RawTerm.refl applyRaw)) commonRaw :=
  Conv.canonicalForm
    (LeanFX2.funext (context := context) domainType codomainType applyRaw)

#print axioms Conv.canonicalForm_funext

/-! ## Architectural confirmation — Phase 4 base auto-handles the cascade.

The six smoke theorems above are each one-liners (the bodies are
direct applications of Phase 4 base theorems).  This confirms that
the Phase 4 base infrastructure handles `Step.eqType` and
`Step.eqArrow` UNIFORMLY through the existing `toRawBridge`
pipeline — no per-ctor case-splitting needed in Cd, CdLemma,
Diamond, ChurchRosser, or CanonicalForm.

The only load-bearing pieces are the `eqType` and `eqArrow` arms
of `Step.par.toRawBridge` (Bridge.lean:201, 206), which collapse
the outer typed step to a raw `RawStep.par.refl _` on the
canonical raw form.  Everything downstream is parametric in the
bridge and inherits the new ctors for free.

This is the same architectural payoff as `Step.cumulUpInnerCong`
(audited in AuditPhase12AB18CumulConfluence): pre-aligning the
source/target raw forms means the bridge arm is `RawStep.par.refl
_`, and Phase 4 base machinery is already polymorphic enough to
cascade through. -/

end LeanFX2

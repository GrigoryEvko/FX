import FX1Poly.Tier0.Context.ExplicitSubstitution

/-! # context-12 — Gratzer MTT normalization: multimodal NbE over the modal base

`context-12` is the NORMALIZATION-BY-EVALUATION rung (Gratzer 2022, "Normalization for Multimodal Type
Theory", LICS; the Gratzer–Sterling–Birkedal MTT line; arXiv 2301.11842).  NbE = `normalize = reify ∘ eval`:
`eval` interprets syntax into a semantic (value) domain, `reify` reads values back into normal forms, and the
two exhibit the values as a RETRACT of the syntax — so `normalize` is the induced idempotent, sound and
complete for the equational theory.  Gratzer's MTT normalization runs this relative to a MODE THEORY, with
the proof itself a Synthetic-Tait-Computability / gluing argument (`context-11`).

## The context-side residue, in full

The full MTT-NbE normalizes TYPED TERMS and TYPES over the mode theory (`×type+term+mode`).  The strictly
CONTEXT-SIDE residue is NbE for the SUBSTITUTION calculus — the morphisms of the context base
`fxBaseSubstCategory`.  And it lands cleanly because `context-8` already shipped the `eval` half:

  * `eval = SubstExpr.denote` — `context-8`'s interpretation of the λσ explicit-substitution SYNTAX
    (`SubstExpr`) into the semantic substitution category (`SubstVec`).  This IS NbE's `eval`.
  * `reify = SubstVec.reify` — read a semantic substitution back to its CANONICAL `consSub`-chain syntax
    (added here; the base case is the unique map out of the empty context, `SubstExpr.emptyToScope`).
  * `SubstExpr.denote_reify` — ★ the SECTION law `denote ∘ reify = id` (every value is the denotation of
    its reification), by induction on the scope with `SubstVec`'s definitional product-eta.

From the retraction, the generic NbE package: `normalize = reify ∘ denote`, with SOUNDNESS
(`denote ∘ normalize = denote`), IDEMPOTENCE, COMPLETENESS (`denote`-equal terms have equal normal forms),
and the conversion characterization `normalize a = normalize b ↔ denote a = denote b` — i.e. conversion of
substitutions is decided by their semantic value (decidable once `SubstVec` has `DecidableEq`, which
`SubstVec.ext` + `RawTerm.decEq` support — noted, the mechanical corollary).

## The two normalization routes agree (Path-A NbE vs Path-rewriting)

`context-8` shipped the OTHER route — the σ-rewriting (the seven λσ rules) with denotational Church–Rosser
and strong normalization.  `context-12` ships the DENOTATIONAL (NbE) route, and the bridge
`fxSubstNormalize_substStep_invariant` proves they agree: the NbE normal form is a σ-REWRITING INVARIANT
(`SubstStep a b → normalize a = normalize b`), because each σ-rule preserves the denotation
(`context-8`'s `SubstStep.denote_eq`) and `normalize` is `denote`-complete.  So NbE-normalize is exactly the
value the σ-rewriting converges to, up to denotation.

## What lands here (all zero-axiom)

  * `NbeRetraction` + `normalize` + `eval_normalize` / `normalize_idempotent` / `normalize_complete` /
    `eval_eq_of_normalize_eq` / `normalize_eq_iff_eval_eq` — the generic NbE-as-retraction package;
  * `SubstExpr.emptyToScope` / `SubstVec.reify` / `SubstExpr.denote_reify` — reify for the substitution
    calculus + the ★ section law;
  * `fxSubstNbe` / `fxSubstNormalize` / `fxSubstNormalize_denote` / `fxSubstConv_iff` — the concrete
    substitution-calculus NbE, its normalizer, soundness, and the conversion characterization;
  * `fxSubstNormalize_substStep_invariant` / `fxSubstNormalize_substStepStar_invariant` — ★ the bridge to
    `context-8`'s σ-rewriting (NbE NF is a rewriting invariant);
  * `FxMultimodalNbe` / `fxMultimodalNbe` — the assembled witness;
  * `fxMultimodalNbe_hasTypedTermReification` / `fxMultimodalNbe_hasModalLockThreading` — the honesty
    markers (`= false`); see the deferral note;
  * `fxMultimodalNbe_normalize_idempotent_smoke`.

## SHIPPED vs DEFERRED

SHIPPED (context-side, zero-axiom): NbE for the base's morphisms (substitutions) — eval (`context-8`) +
reify + the section + the normalizer + soundness/idempotence/completeness + the conversion characterization
+ the σ-rewriting agreement.

DEFERRED (honestly NOT here, recorded by the `= false` markers):
  * `hasTypedTermReification` — reifying TYPED TERMS/TYPES (the full MTT-NbE: a value domain with the
    type-former semantics, reify to βη-normal terms, the fundamental theorem) needs the type formers and
    typing — `×type+term`, the joint normalization of `fib-6`.
  * `hasModalLockThreading` — the MULTIMODAL part proper: threading the mode theory's locks `◐_μ`
    (`context-4`) through eval/reify (Gratzer's mode-relative NbE; the lock acts on contexts) — `×mode`,
    deferred to `fib-3`.

AXIS HYGIENE: `SubstExpr` / `SubstVec` are the SUBSTITUTION calculus = the base's morphisms (context-side,
as `context-8` established); the `RawTerm` heads inside `consSub` are term-axis VALUES carried opaquely
(`reify` transports them; `denote` substitutes via the term axis) — same stance as `context-8`/`context-11`.

Zero external dependencies.  Raw Lean 4 + Init only.  No `funext` (`SubstVec`'s product-eta does the work).
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-! ## The generic NbE retraction -/

/-- **An NbE-as-retraction structure.**  An `eval` from syntax to a semantic value domain and a `reify`
back, such that every value is the denotation of its reification (`evalReify`: `eval ∘ reify = id`).  This
exhibits `Value` as a RETRACT of `Syntax`; the induced idempotent `normalize = reify ∘ eval` is the
normalizer, sound and complete for the equational theory `eval` denotes. -/
structure NbeRetraction (Syntax : Type) (Value : Type) where
  /-- Interpret syntax into the semantic value domain. -/
  eval : Syntax → Value
  /-- Read a value back into (canonical, normal-form) syntax. -/
  reify : Value → Syntax
  /-- Every value is the denotation of its reification — `reify` is a section of `eval`. -/
  evalReify : ∀ (value : Value), eval (reify value) = value

/-- The normalizer induced by the retraction: evaluate, then reify. -/
def NbeRetraction.normalize {Syntax Value : Type} (nbe : NbeRetraction Syntax Value)
    (syntaxTerm : Syntax) : Syntax :=
  nbe.reify (nbe.eval syntaxTerm)

/-- **Soundness** — `normalize` preserves the denotation: `eval (normalize s) = eval s`. -/
theorem NbeRetraction.eval_normalize {Syntax Value : Type} (nbe : NbeRetraction Syntax Value)
    (syntaxTerm : Syntax) : nbe.eval (nbe.normalize syntaxTerm) = nbe.eval syntaxTerm := by
  show nbe.eval (nbe.reify (nbe.eval syntaxTerm)) = nbe.eval syntaxTerm
  rw [nbe.evalReify]

/-- **Idempotence** — normal forms are stable: `normalize (normalize s) = normalize s`. -/
theorem NbeRetraction.normalize_idempotent {Syntax Value : Type} (nbe : NbeRetraction Syntax Value)
    (syntaxTerm : Syntax) : nbe.normalize (nbe.normalize syntaxTerm) = nbe.normalize syntaxTerm := by
  show nbe.reify (nbe.eval (nbe.reify (nbe.eval syntaxTerm))) = nbe.reify (nbe.eval syntaxTerm)
  rw [nbe.evalReify]

/-- **Completeness** — `eval`-equal terms have equal normal forms (the easy direction of NbE conversion). -/
theorem NbeRetraction.normalize_complete {Syntax Value : Type} (nbe : NbeRetraction Syntax Value)
    {firstTerm secondTerm : Syntax} (hValueEq : nbe.eval firstTerm = nbe.eval secondTerm) :
    nbe.normalize firstTerm = nbe.normalize secondTerm := by
  show nbe.reify (nbe.eval firstTerm) = nbe.reify (nbe.eval secondTerm)
  rw [hValueEq]

/-- Equal normal forms force equal denotations (the converse direction), via soundness. -/
theorem NbeRetraction.eval_eq_of_normalize_eq {Syntax Value : Type} (nbe : NbeRetraction Syntax Value)
    {firstTerm secondTerm : Syntax} (hNormEq : nbe.normalize firstTerm = nbe.normalize secondTerm) :
    nbe.eval firstTerm = nbe.eval secondTerm := by
  rw [← nbe.eval_normalize firstTerm, ← nbe.eval_normalize secondTerm, hNormEq]

/-- ★ **The conversion characterization** — two terms have equal normal forms IFF equal denotations.  This
reduces conversion to semantic equality (decidable when `Value` has `DecidableEq`). -/
theorem NbeRetraction.normalize_eq_iff_eval_eq {Syntax Value : Type} (nbe : NbeRetraction Syntax Value)
    (firstTerm secondTerm : Syntax) :
    nbe.normalize firstTerm = nbe.normalize secondTerm ↔ nbe.eval firstTerm = nbe.eval secondTerm :=
  ⟨fun hNormEq => nbe.eval_eq_of_normalize_eq hNormEq, fun hValueEq => nbe.normalize_complete hValueEq⟩

/-! ## reify for the substitution calculus + the section law -/

/-- **The unique substitution out of the empty context** — `SubstExpr target 0`.  The reify base case: a
semantic substitution `SubstVec target 0` is the unique (empty) one, so its reification is this canonical
empty-context map (`id` at scope `0`, then a `shift`-tower up to `target`). -/
def SubstExpr.emptyToScope : (target : Nat) → SubstExpr target 0
  | 0 => SubstExpr.identitySub
  | target + 1 => SubstExpr.composeSub (SubstExpr.emptyToScope target) SubstExpr.shiftSub

/-- **reify** — read a semantic substitution back to its CANONICAL `consSub`-chain syntax.  By recursion on
the source scope: the empty substitution reifies to `emptyToScope`; an extended one to `consSub` of the head
image and the reification of the tail.  This is NbE's read-back for the substitution calculus. -/
def SubstVec.reify {target : Nat} :
    {source : Nat} → SubstVec target source → SubstExpr target source
  | 0, _vec => SubstExpr.emptyToScope target
  | _source + 1, vec => SubstExpr.consSub vec.1 (SubstVec.reify vec.2)

/-- ★ **The section law** — `denote ∘ reify = id`.  Every semantic substitution is the denotation of its
reification.  By induction on the source scope: the base case is `SubstVec`-extensionality over the vacuous
`Fin 0`; the step rewrites through `denote_consSub` and the inductive hypothesis, then closes by the
definitional product-eta of `SubstVec.cons` (`cons vec.1 vec.2 = vec`).  Zero-axiom (no `funext`). -/
theorem SubstExpr.denote_reify {target : Nat} :
    {source : Nat} → (vec : SubstVec target source) → (SubstVec.reify vec).denote = vec
  | 0, _vec => SubstVec.ext _ _ (fun index => index.elim0)
  | _source + 1, vec => by
      show (SubstExpr.consSub vec.1 (SubstVec.reify vec.2)).denote = vec
      rw [SubstExpr.denote_consSub, SubstExpr.denote_reify vec.2]
      rfl

/-! ## The concrete substitution-calculus NbE + the σ-rewriting bridge -/

/-- **The substitution calculus is an NbE retraction** — `eval = denote` (`context-8`), `reify = reify`,
section = `denote_reify`.  So the λσ substitution syntax normalizes by evaluation into `SubstVec`. -/
def fxSubstNbe (target source : Nat) :
    NbeRetraction (SubstExpr target source) (SubstVec target source) where
  eval := SubstExpr.denote
  reify := SubstVec.reify
  evalReify := fun vec => SubstExpr.denote_reify vec

/-- The NbE normalizer for substitution expressions: `reify ∘ denote`. -/
def fxSubstNormalize {target source : Nat} (subExpr : SubstExpr target source) :
    SubstExpr target source :=
  (fxSubstNbe target source).normalize subExpr

/-- **Soundness** — the NbE normal form denotes the same substitution as its input. -/
theorem fxSubstNormalize_denote {target source : Nat} (subExpr : SubstExpr target source) :
    (fxSubstNormalize subExpr).denote = subExpr.denote :=
  (fxSubstNbe target source).eval_normalize subExpr

/-- ★ **Conversion characterization** — two substitution expressions have equal NbE normal forms IFF equal
denotations.  Conversion of substitutions is decided by their semantic value (`SubstVec`). -/
theorem fxSubstConv_iff {target source : Nat} (firstExpr secondExpr : SubstExpr target source) :
    fxSubstNormalize firstExpr = fxSubstNormalize secondExpr ↔ firstExpr.denote = secondExpr.denote :=
  (fxSubstNbe target source).normalize_eq_iff_eval_eq firstExpr secondExpr

/-- ★ **The NbE normal form is a σ-rewriting invariant** — `SubstStep a b → normalize a = normalize b`.  The
bridge to `context-8`'s rewriting route: each σ-rule preserves the denotation (`SubstStep.denote_eq`) and
`normalize` is `denote`-complete, so both normalization routes agree (Path-A NbE vs Path-rewriting). -/
theorem fxSubstNormalize_substStep_invariant {target source : Nat}
    {firstExpr secondExpr : SubstExpr target source} (step : SubstStep firstExpr secondExpr) :
    fxSubstNormalize firstExpr = fxSubstNormalize secondExpr :=
  (fxSubstNbe target source).normalize_complete (SubstStep.denote_eq step)

/-- The σ-rewriting invariance, extended to multi-step reduction (`SubstStepStar`). -/
theorem fxSubstNormalize_substStepStar_invariant {target source : Nat}
    {firstExpr secondExpr : SubstExpr target source} (steps : SubstStepStar firstExpr secondExpr) :
    fxSubstNormalize firstExpr = fxSubstNormalize secondExpr :=
  (fxSubstNbe target source).normalize_complete (SubstStepStar.denote_eq steps)

/-! ## The assembled witness + honesty markers -/

/-- **The FX modal context base HAS a normalization-by-evaluation** for its morphisms, gathered as one
citable object: the per-scope NbE retraction on the substitution calculus and the σ-rewriting invariance of
its normal form. -/
structure FxMultimodalNbe where
  /-- The NbE retraction at each pair of scopes (eval = `context-8`'s denote, reify added here). -/
  retraction : (target source : Nat) →
    NbeRetraction (SubstExpr target source) (SubstVec target source)
  /-- The normal form is a σ-rewriting invariant (the bridge to `context-8`'s rewriting route). -/
  normalizeStepInvariant : ∀ {target source : Nat} {firstExpr secondExpr : SubstExpr target source},
    SubstStep firstExpr secondExpr →
    (retraction target source).normalize firstExpr = (retraction target source).normalize secondExpr

/-- ★ The assembled `context-12` witness over the FX modal context base. -/
def fxMultimodalNbe : FxMultimodalNbe where
  retraction := fxSubstNbe
  normalizeStepInvariant := fun step => fxSubstNormalize_substStep_invariant step

/-- **Honesty marker.**  This NbE reifies SUBSTITUTIONS (the base's morphisms).  Reifying TYPED TERMS and
TYPES — the full MTT-NbE: a value domain with the type-former semantics, read-back to βη-normal terms, and
the fundamental theorem — needs the type formers and typing (`×type+term`, the joint normalization of
`fib-6`).  `= false` records that typed-term reification is not shipped here. -/
def fxMultimodalNbe_hasTypedTermReification : Bool := false

/-- **Honesty marker.**  The MULTIMODAL part proper — threading the mode theory's locks `◐_μ` (`context-4`)
through eval/reify (Gratzer's mode-relative NbE; the lock acts on contexts) — is `×mode`, deferred to
`fib-3`.  This rung fixes NbE over the substitution base; the modal-lock action is not threaded here.
`= false` records that. -/
def fxMultimodalNbe_hasModalLockThreading : Bool := false

/-! ## Smoke: NbE normal forms are idempotent -/

/-- Smoke: normalizing a substitution expression twice equals normalizing it once (normal forms are
stable). -/
theorem fxMultimodalNbe_normalize_idempotent_smoke {target source : Nat}
    (subExpr : SubstExpr target source) :
    fxSubstNormalize (fxSubstNormalize subExpr) = fxSubstNormalize subExpr :=
  (fxSubstNbe target source).normalize_idempotent subExpr

end FX1Poly.Tier0

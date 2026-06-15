import FX1Poly.Tier0.Context.ComprehensionSigma
import FX1Poly.Tier0.Context.Strictification
import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstSingleton
import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstDisplayMap
import FX1Poly.Tier0.Context.RenamingInclusion
import FX1Poly.Tier0.Context.MultimodalNormalization

/-! # context-9 — SFMTT: the substitution-free structural algorithm (context-side residue)

`context-9` is the SUBSTITUTION-FREE rung (SFMTT — Gratzer's substitution-free formulation of multimodal
type theory; cf. the implementation in `mitten`).  Where `context-8` reified substitution as an explicit
first-order calculus (λσ), SFMTT goes the OTHER way: it presents the type theory with NO general
substitution operation at all.  The structural algorithm (typing / normalization) uses only

  * **renamings** (variable-to-variable maps — structural, finite, decidable), for weakening and the
    Kripke/presheaf structure, and
  * **single substitution** (`singleton`, plugging ONE term for variable 0), at β-redexes,

and GENERAL substitution is then ADMISSIBLE — recovered as a meta-theorem, never a primitive.  "Sound +
complete" is exactly that admissibility: the substitution-free presentation derives the same judgments as
the substitution-ful one (sound = derives no more; complete = substitution is admissible, so nothing is
lost).

## THE SPLIT (`⊟SPLIT · core=lock-soundness×mode→fib-3`)

The full SFMTT theorem is about the typing/normalization algorithm under the MODAL LOCK `◐_μ`
(`context-4`): that the substitution-free structural algorithm is sound and complete RELATIVE TO the modal
lock semantics.  That `lock-soundness × mode` core is the cross-axis content and is deferred to `fib-3`
(`#1581 ★ [everything ⊣ mode]`).  This file ships the strictly CONTEXT-SIDE residue: the
substitution-ADMISSIBILITY laws on the plain (non-modal) de Bruijn substitution base — the equalities that
make the structural algorithm work without a general-substitution primitive.

## What lands here (all zero-axiom): substitution is admissible

The structural algorithm's β-engine never forms `SubstVec.compose σ τ` for general `σ, τ`.  It needs only:

  * **`SubstVec.lift_compose_singleton`** — ★ the β-substitution law: substituting under a binder and then
    plugging the argument IS extension — `(σ⁺) ∘ ⟨arg⟩ = arg · σ`.  This is exactly the substitution the
    β-rule `(λ b) a ↝ b[a]` runs, expressed with only `lift` (a renaming-built operation) and `singleton`
    (single substitution) — no general composition.
  * **`SubstVec.singleton_compose`** — pushing a substitution past a single-substitution: `⟨arg⟩ ∘ σ =
    (arg[σ]) · σ`.
  * **`SubstVec.singleton_naturality`** — ★ the SUBSTITUTION LEMMA in substitution-free form: single
    substitution commutes with substitution, `⟨arg⟩ ∘ σ = (σ⁺) ∘ ⟨arg[σ]⟩`.  This is the law that lets the
    structural algorithm move a single substitution through a substitution it never had to form.
  * **`SubstVec.cons_eq_lift_compose_singleton`** — the comprehension extension is admissible from the
    structural ops: `head · tail = (tail⁺) ∘ ⟨head⟩` (so even `cons` is not needed primitively).
  * **`SubstVec.factor_lift_singleton`** — ★ COMPLETENESS: every substitution into an extended context
    FACTORS as `lift` ∘ single-substitution, `vec = ((p ∘ vec)⁺) ∘ ⟨vec 0⟩`.  This is "substitution is
    admissible" made precise — the structural algorithm needs NO general substitution composition as a
    primitive; the zeroth image (a single substitution) plus a weaken-and-recurse tail plus `lift` rebuild
    any substitution.
  * **`SubstVec.weakening_is_renaming`** / **`SubstVec.identity_is_renaming`** — the non-`singleton`
    structural maps are RENAMINGS: both `weakening` (`= ι(↑)`) and `identity` (`= ι(id)`) carry no term
    content, so among `{id, ↑, singleton}` the ONLY term-carrying primitive is the single substitution
    `singleton`.
  * **`SubstitutionFreeStructure` / `fxSubstitutionFree`** — the seven substitution-free laws (β,
    single-substitution stability, the substitution lemma, the display section `↑ ∘ ⟨arg⟩ = id`, extension
    admissibility, the factorization/completeness, and weakening-is-a-renaming) gathered as ONE object:
    "the substitution-free structural algorithm", realized on the FX context base.
  * **`SubstExpr.IsStructural` / `fxSubstitutionFreeNormalForm`** — the ALGORITHMIC form.  The laws above
    say substitution is admissible as EQUATIONS; this says the structural algorithm OUTPUTS
    substitution-free syntax.  `IsStructural` is the substitution-free SUB-GRAMMAR of `context-8`'s
    explicit-substitution calculus (`composeSub` allowed ONLY as a weakening `_ ∘ ↑`, never between two
    genuine substitutions — a PROPER subclass), and `fxSubstNormalize_isStructural` proves `context-12`'s
    NbE normalizer (`reify ∘ denote`) ALWAYS lands in it.  This is the SFMTT headline — "the structural
    algorithm needs no general substitution" — tying `context-9` to the shipped `context-12` normalizer.
  * **`SubstVec.hasSubstitutionFreePresentation`** — the SOUND + COMPLETE statement the premise names, as
    ONE proposition: every base morphism `vec` has a substitution-free `SubstExpr` (`IsStructural`) with
    `denote = vec` — COMPLETE (such a presentation exists for every substitution) and SOUND (it denotes the
    morphism it presents).  The modal-lock-relative version is the `×mode` core deferred to `fib-3`.

The bundle `fxSubstitutionFree` is the precise CONTEXT-SIDE deliverable: every field is an equality between
MORPHISMS of the substitution/renaming category (the CwF comprehension structure).  Terms appear only as the
DATA those morphisms carry and as the action `compose` is implemented by — never as the subject.

CONTEXT→TERM BRIDGE (`⟦×term → term-2 / term-26 (#1622)⟧`, NOT counted as context-side): the single
operational corollary `RawTerm.subst_cons_eq_singleton_after_lift` — `body[arg · σ] = body[σ⁺][⟨arg⟩]` — is a
statement about the TERM action `RawTerm.subst`, so its home is the TERM axis (term-2's dim-1 rewriting / the
β-on-terms, and term-26's RawTerm single-substitution algebra).  It is surfaced here ONLY to demonstrate that
the context β-law has operational teeth through the action functor (`compose_subst_apply`); it is a one-line
corollary and is deliberately EXCLUDED from `fxSubstitutionFree`.  When term-26 lands it is re-derived there.

SOUNDNESS of the substitution-free maps: renamings include into substitutions FUNCTORIALLY — this is
`context-1`'s `renamingInclusion : RawFunctor fxBaseRenamingVecCategory fxBaseSubstCategory` (with
`RenamingVec.toSubstVec_identity` / `_compose`), already shipped.  The β bridge to the kernel's `Step`
relation is `SubstVec.subst_singleton_eq_subst0` (also shipped): the categorical single substitution acts
as the de Bruijn `subst0` the β-rule references.

DEFERRED to `fib-3` (`×mode`, honestly NOT shipped): the modal lock `◐_μ`'s interaction with the
structural algorithm, and the lock-relative soundness/completeness of substitution-free typing/NbE.

Zero external dependencies.  Raw Lean 4 + Init only.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-! ## Substitution is admissible: the β-substitution law -/

/-- ★ **The β-substitution law, substitution-free.**  Lifting a substitution under a binder and then
plugging an argument equals extending the substitution by that argument:
`(σ⁺) ∘ ⟨arg⟩ = arg · σ`.  This is the substitution the β-rule `(λ b) a ↝ b[a]` performs — and it is built
from ONLY `SubstVec.lift` (the under-binder operation) and `SubstVec.singleton` (single substitution), with
NO general substitution composition as a primitive.  Proof: unfold `lift = ⟨q, σ ∘ ↑⟩`, distribute the
composition through `cons` (`cons_compose`); the head is `arg` (`subst_varCell` + `singleton_lookup_zero`)
and the tail reassociates `σ ∘ (↑ ∘ ⟨arg⟩) = σ ∘ id = σ` (`compose_assoc` + the display-section law
`weakening_compose_singleton` + `compose_identity`). -/
theorem SubstVec.lift_compose_singleton {targetScope sourceScope : Nat}
    (sigma : SubstVec targetScope sourceScope) (arg : RawTerm targetScope) :
    sigma.lift.compose (SubstVec.singleton arg) = SubstVec.cons arg sigma := by
  show (SubstVec.cons (SubstVec.varCell ⟨0, Nat.succ_pos targetScope⟩)
        (sigma.compose (SubstVec.weakening targetScope))).compose (SubstVec.singleton arg)
      = SubstVec.cons arg sigma
  rw [SubstVec.cons_compose, SubstVec.subst_varCell, SubstVec.singleton_lookup_zero,
      SubstVec.compose_assoc, SubstVec.weakening_compose_singleton, SubstVec.compose_identity]

/-- **Single substitution under a substitution.**  Composing a single-substitution with `σ` substitutes
the argument and re-extends: `⟨arg⟩ ∘ σ = (arg[σ]) · σ`.  Proof: `singleton = arg · id`, so `cons_compose`
gives the head `arg[σ]` and the tail `id ∘ σ = σ` (`identity_compose`). -/
theorem SubstVec.singleton_compose {targetScope sourceScope : Nat}
    (arg : RawTerm sourceScope) (sigma : SubstVec targetScope sourceScope) :
    (SubstVec.singleton arg).compose sigma
      = SubstVec.cons (RawTerm.subst sigma.toRawTermSubst arg) sigma := by
  show (SubstVec.cons arg (SubstVec.identity sourceScope)).compose sigma
      = SubstVec.cons (RawTerm.subst sigma.toRawTermSubst arg) sigma
  rw [SubstVec.cons_compose, SubstVec.identity_compose]

/-- ★ **The substitution lemma, substitution-free.**  Single substitution COMMUTES with substitution:
`⟨arg⟩ ∘ σ = (σ⁺) ∘ ⟨arg[σ]⟩`.  This is the law (`a[b][σ] = a[σ⁺][b[σ]]` at the substitution level) that the
substitution-free structural algorithm uses to push a single substitution through a substitution it never
formed — the crux of why general substitution is admissible.  Both sides equal `(arg[σ]) · σ`
(`singleton_compose` on the left, `lift_compose_singleton` on the right). -/
theorem SubstVec.singleton_naturality {targetScope sourceScope : Nat}
    (arg : RawTerm sourceScope) (sigma : SubstVec targetScope sourceScope) :
    (SubstVec.singleton arg).compose sigma
      = sigma.lift.compose (SubstVec.singleton (RawTerm.subst sigma.toRawTermSubst arg)) :=
  (SubstVec.singleton_compose arg sigma).trans
    (SubstVec.lift_compose_singleton sigma (RawTerm.subst sigma.toRawTermSubst arg)).symm

/-! ## COMPLETENESS — substitution is generated by the structural operations -/

/-- **The comprehension extension is admissible from the structural operations.**  Every `cons head tail`
(the generator of the substitution category) IS a `lift` composed with a single substitution:
`head · tail = (tail⁺) ∘ ⟨head⟩`.  So the extension primitive is not needed either — `lift` + `singleton`
build it.  (The β-law `lift_compose_singleton`, read right-to-left.) -/
theorem SubstVec.cons_eq_lift_compose_singleton {target source : Nat} (head : RawTerm target)
    (tail : SubstVec target source) :
    SubstVec.cons head tail = tail.lift.compose (SubstVec.singleton head) :=
  (SubstVec.lift_compose_singleton tail head).symm

/-- ★ **Every substitution into an extended context FACTORS through `lift` and a single substitution** —
the substitution-free completeness.  For any `vec : Γ ⟶ Δ.A`,
`vec = ((p ∘ vec)⁺) ∘ ⟨vec 0⟩`, where `p = weakening` and `vec 0 = vec.lookup 0`.  Read as an algorithm:
to apply an arbitrary substitution it suffices to (i) take its zeroth image (a single substitution), (ii)
weaken-and-recurse on the tail, (iii) `lift`.  No general substitution composition is ever a primitive —
this is precisely "substitution is admissible".  Proof: the comprehension η-law `cons_unique` rewrites
`vec = (vec 0) · (p ∘ vec)`, then `lift_compose_singleton` recognizes the right-hand side as the factored
form. -/
theorem SubstVec.factor_lift_singleton {target source : Nat} (vec : SubstVec target (source + 1)) :
    vec = ((SubstVec.weakening source).compose vec).lift.compose
            (SubstVec.singleton (vec.lookup ⟨0, Nat.succ_pos source⟩)) := by
  rw [SubstVec.lift_compose_singleton]
  exact SubstVec.cons_unique _ _ vec rfl rfl

/-! ## The substitution-free maps are renamings -/

/-- **Weakening is a RENAMING** — `weakening = ι(↑)`, the image under `renamingInclusion` of the renaming
shift.  This makes "the structural algorithm weakens substitution-free" concrete: weakening carries no term
content (every image is a variable), so it lives in the renaming sub-category, not the genuine substitution
part.  Together with `cons_eq_lift_compose_singleton`/`factor_lift_singleton`, the ONLY term-carrying
primitive the structural algorithm uses is the single substitution `singleton`.  Proof: pointwise, both send
`index ↦ var (index+1)` (`RenamingVec.shiftImage` is `Fin.succ` definitionally). -/
theorem SubstVec.weakening_is_renaming (scope : Nat) :
    (RenamingVec.weakening scope).toSubstVec = SubstVec.weakening scope :=
  SubstVec.ext _ _ (fun index => by
    rw [RenamingVec.toSubstVec_lookup, RenamingVec.weakening_lookup, SubstVec.weakening_lookup,
        show RenamingVec.shiftImage index = index.succ from Fin.ext rfl])

/-- **Identity is a renaming** — `id = ι(id_ren)`; the structural identity carries no term content.  (The
`renamingInclusion` identity law `RenamingVec.toSubstVec_identity`, read right-to-left.) -/
theorem SubstVec.identity_is_renaming (scope : Nat) :
    (RenamingVec.identity scope).toSubstVec = SubstVec.identity scope :=
  RenamingVec.toSubstVec_identity scope

/-! ## CONTEXT→TERM BRIDGE (`⟦×term → term-2 / term-26⟧`, NOT context-side)

The one declaration below is TERM-axis content — a statement about the action `RawTerm.subst` on a term,
not about a morphism of the context category.  Its home is term-2 (β-on-terms, the dim-1 rewriting layer)
and term-26 (#1622, the RawTerm single-substitution algebra).  It is surfaced here only as the operational
shadow of the context β-law and is excluded from the `fxSubstitutionFree` bundle. -/

/-- ★ **(`×term` bridge — term-axis, surfaced here) The substitution-free β-reduction on terms.**
Substituting `arg · σ` into a term IS: lift `σ`,
substitute, then plug `arg` — `body[arg · σ] = body[σ⁺][⟨arg⟩]`.  This is exactly what the structural
algorithm computes for `(λ body) arg` under a pending substitution `σ`: it NEVER forms the composite
substitution `arg · σ`; it weakens-and-lifts `σ`, applies it, and finally single-substitutes `arg`.  Proof:
the β-law `lift_compose_singleton` rewrites `arg · σ = σ⁺ ∘ ⟨arg⟩`, then `compose_subst_apply` distributes
the substitution action over the composition.  (At `σ = id`, `arg · id = ⟨arg⟩` recovers ordinary β.) -/
theorem RawTerm.subst_cons_eq_singleton_after_lift {targetScope sourceScope : Nat}
    (arg : RawTerm targetScope) (sigma : SubstVec targetScope sourceScope)
    (body : RawTerm (sourceScope + 1)) :
    RawTerm.subst (SubstVec.cons arg sigma).toRawTermSubst body
      = RawTerm.subst (SubstVec.singleton arg).toRawTermSubst
          (RawTerm.subst sigma.lift.toRawTermSubst body) := by
  rw [← SubstVec.lift_compose_singleton sigma arg, SubstVec.compose_subst_apply]

/-! ## The substitution-free structural algorithm, as one object -/

/-- **The substitution-free structural algorithm** of the FX context base, gathered as one citable object:
the β-substitution law, single-substitution stability, the substitution lemma, and the display section
(`↑ ∘ ⟨arg⟩ = id`).  Together these are the laws the structural (substitution-free) β-engine runs on — it
forms NO general substitution composition, only `lift`, `singleton`, and `weakening`.  The renaming
soundness leg (renamings ⊂ substitutions, functorially) is `context-1`'s `renamingInclusion`; the modal
lock interaction is `fib-3`. -/
structure SubstitutionFreeStructure where
  /-- β-substitution: substitute under a binder then plug = extend. -/
  betaLaw : ∀ {targetScope sourceScope : Nat} (sigma : SubstVec targetScope sourceScope)
              (arg : RawTerm targetScope),
            sigma.lift.compose (SubstVec.singleton arg) = SubstVec.cons arg sigma
  /-- Single substitution under a substitution. -/
  singletonStable : ∀ {targetScope sourceScope : Nat} (arg : RawTerm sourceScope)
                      (sigma : SubstVec targetScope sourceScope),
            (SubstVec.singleton arg).compose sigma
              = SubstVec.cons (RawTerm.subst sigma.toRawTermSubst arg) sigma
  /-- The substitution lemma: single substitution commutes with substitution. -/
  substitutionLemma : ∀ {targetScope sourceScope : Nat} (arg : RawTerm sourceScope)
                        (sigma : SubstVec targetScope sourceScope),
            (SubstVec.singleton arg).compose sigma
              = sigma.lift.compose (SubstVec.singleton (RawTerm.subst sigma.toRawTermSubst arg))
  /-- The display section: weakening cancels single substitution (`↑ ∘ ⟨arg⟩ = id`). -/
  displaySection : ∀ {scope : Nat} (arg : RawTerm scope),
            (SubstVec.weakening scope).compose (SubstVec.singleton arg) = SubstVec.identity scope
  /-- Comprehension extension is admissible: `head · tail = (tail⁺) ∘ ⟨head⟩`. -/
  extensionAdmissible : ∀ {target source : Nat} (head : RawTerm target)
                          (tail : SubstVec target source),
            SubstVec.cons head tail = tail.lift.compose (SubstVec.singleton head)
  /-- ★ COMPLETENESS: every substitution into an extended context factors through `lift` + a single
  substitution — no general composition is ever a primitive (substitution is admissible). -/
  factorization : ∀ {target source : Nat} (vec : SubstVec target (source + 1)),
            vec = ((SubstVec.weakening source).compose vec).lift.compose
                    (SubstVec.singleton (vec.lookup ⟨0, Nat.succ_pos source⟩))
  /-- The non-`singleton` structural maps are RENAMINGS: weakening carries no term content. -/
  weakeningIsRenaming : ∀ (scope : Nat),
            (RenamingVec.weakening scope).toSubstVec = SubstVec.weakening scope

/-- ★ The FX context base HAS a substitution-free structural algorithm — the witness, wiring the four laws
above (the first three new here, the display section being the shipped `weakening_compose_singleton`).  This
is `context-9`'s "substitution-free structural algorithm" delivered as one object; the modal-lock-relative
soundness/completeness is `fib-3`. -/
def fxSubstitutionFree : SubstitutionFreeStructure where
  betaLaw := fun sigma arg => SubstVec.lift_compose_singleton sigma arg
  singletonStable := fun arg sigma => SubstVec.singleton_compose arg sigma
  substitutionLemma := fun arg sigma => SubstVec.singleton_naturality arg sigma
  displaySection := fun arg => SubstVec.weakening_compose_singleton arg
  extensionAdmissible := fun head tail => SubstVec.cons_eq_lift_compose_singleton head tail
  factorization := fun vec => SubstVec.factor_lift_singleton vec
  weakeningIsRenaming := fun scope => SubstVec.weakening_is_renaming scope

/-! ## Smoke: the β-substitution at the identity substitution -/

/-- Smoke: at `σ = id`, the β-law reads `id⁺ ∘ ⟨arg⟩ = arg · id = ⟨arg⟩` — substituting under a binder over
the identity then plugging is exactly the single substitution. -/
theorem SubstVec.lift_identity_compose_singleton_smoke {scope : Nat} (arg : RawTerm scope) :
    (SubstVec.identity scope).lift.compose (SubstVec.singleton arg) = SubstVec.singleton arg :=
  SubstVec.lift_compose_singleton (SubstVec.identity scope) arg

/-! ## The ALGORITHMIC form — the structural normal form is substitution-free

The laws above say substitution is admissible as EQUATIONS.  SFMTT's headline is ALGORITHMIC: the
structural algorithm OUTPUTS substitution-free syntax.  `context-8` reified substitutions as the
explicit-substitution calculus `SubstExpr`, and `context-12` shipped its NbE normalizer
`fxSubstNormalize = reify ∘ denote`.  Here "substitution-free" is pinned down as a PROPER sub-grammar of
`SubstExpr`, and the normalizer is proved to always land in it: every NbE normal form uses general
composition NOWHERE — `composeSub` survives only as a weakening `_ ∘ ↑` (a renaming), never between two
genuine substitutions.  This is the formal content of "the structural algorithm needs no general
substitution". -/

/-- **The substitution-free sub-grammar of the explicit-substitution calculus** (SFMTT).  A `SubstExpr`
is STRUCTURAL when general composition never appears: the only constructors are the identity, the shift,
single-extension `consSub` (over a structural tail), and `composeSub` USED ONLY AS A WEAKENING
`inner ∘ ↑` (the renaming `shiftSub` on the right).  This is a PROPER subclass — a genuine composition
`first ∘ second` whose right operand `second` is not a shift has NO `IsStructural` proof — so "the
normalizer lands in it" is real content, not a tautology. -/
inductive SubstExpr.IsStructural : {target source : Nat} → SubstExpr target source → Prop where
  /-- The identity substitution is substitution-free. -/
  | identity {scope : Nat} :
      SubstExpr.IsStructural (SubstExpr.identitySub : SubstExpr scope scope)
  /-- The shift/display substitution is substitution-free (a renaming). -/
  | shift {scope : Nat} :
      SubstExpr.IsStructural (SubstExpr.shiftSub : SubstExpr (scope + 1) scope)
  /-- Single-extension over a substitution-free tail is substitution-free (`singleton`/`consSub` is the
  only term-carrying primitive). -/
  | cons {target source : Nat} (head : RawTerm target) {tail : SubstExpr target source}
      (tailStructural : SubstExpr.IsStructural tail) :
      SubstExpr.IsStructural (SubstExpr.consSub head tail)
  /-- Composition USED ONLY AS A WEAKENING — `inner ∘ ↑` — is substitution-free (the right operand is the
  renaming `shiftSub`, not a genuine substitution). -/
  | weaken {mid source : Nat} {inner : SubstExpr mid source}
      (innerStructural : SubstExpr.IsStructural inner) :
      SubstExpr.IsStructural
        (SubstExpr.composeSub inner (SubstExpr.shiftSub : SubstExpr (mid + 1) mid))

/-- The empty-context map `emptyToScope` is substitution-free — it is the identity (at `scope 0`) or a
tower of weakenings `id ∘ ↑ ∘ … ∘ ↑`.  By structural recursion on the target scope. -/
theorem SubstExpr.isStructural_emptyToScope :
    (target : Nat) → (SubstExpr.emptyToScope target).IsStructural
  | 0 => SubstExpr.IsStructural.identity
  | target + 1 => SubstExpr.IsStructural.weaken (SubstExpr.isStructural_emptyToScope target)

/-- ★ **Every reified substitution is substitution-free.**  `SubstVec.reify` (`context-12`'s read-back)
always produces a `consSub`-chain over the empty-context map — never a genuine composition.  By structural
recursion on the source scope (mirroring `reify`): the empty case is `isStructural_emptyToScope`, the
extension case is `IsStructural.cons` over the reified tail. -/
theorem SubstVec.isStructural_reify {target : Nat} :
    {source : Nat} → (vec : SubstVec target source) → (SubstVec.reify vec).IsStructural
  | 0, _vec => SubstExpr.isStructural_emptyToScope target
  | _source + 1, vec => SubstExpr.IsStructural.cons vec.1 (SubstVec.isStructural_reify vec.2)

/-- ★ **The NbE normal form of ANY substitution expression is substitution-free** — `context-12`'s
normalizer `fxSubstNormalize = reify ∘ denote` ALWAYS lands in the substitution-free sub-grammar.  This is
the SFMTT headline in algorithmic form: the structural algorithm eliminates every genuine composition,
leaving only identity/shift/single-extension/weakening syntax.  (`fxSubstNormalize subExpr` reduces
definitionally to `SubstVec.reify subExpr.denote`, so this is `isStructural_reify` at the denotation.) -/
theorem fxSubstNormalize_isStructural {target source : Nat} (subExpr : SubstExpr target source) :
    (fxSubstNormalize subExpr).IsStructural :=
  SubstVec.isStructural_reify subExpr.denote

/-- ★ **The substitution-free structural algorithm is SOUND + COMPLETE** (context-side, the morphism
form) — the headline the task premise names.  Every morphism of the substitution category has a
substitution-free presentation: for every `vec : SubstVec target source` there is a substitution-free
`SubstExpr` (`IsStructural`) whose denotation IS `vec`.

  * **COMPLETE** — such a presentation EXISTS for every substitution: general substitution is admissible,
    nothing is lost by dropping the general-composition primitive.
  * **SOUND** — the presentation DENOTES the very morphism it presents (`structuralForm.denote = vec`): the
    substitution-free syntax derives nothing different from the substitution-ful one.

The witness is the canonical `reify` form, so the presentation is moreover COMPUTABLE and unique up to
denotation (`context-12`'s `fxSubstConv_iff`).  The MODAL-LOCK-relative sound + completeness — the `×mode`
core (`◐_μ` threaded through the structural algorithm) — is `fib-3` (`#1581`), per the `⊟SPLIT` marker. -/
theorem SubstVec.hasSubstitutionFreePresentation {target source : Nat}
    (vec : SubstVec target source) :
    ∃ structuralForm : SubstExpr target source,
      structuralForm.IsStructural ∧ structuralForm.denote = vec :=
  ⟨SubstVec.reify vec, SubstVec.isStructural_reify vec, SubstExpr.denote_reify vec⟩

/-- **The substitution-free structural algorithm, as one object** (the ALGORITHMIC companion to
`fxSubstitutionFree`): the empty-context map, every reified substitution, and the NbE normal form of every
substitution expression all lie in the substitution-free sub-grammar.  Where `fxSubstitutionFree` says
substitution is admissible as equations, this says the structural algorithm OUTPUTS substitution-free
syntax. -/
structure SubstitutionFreeNormalForm where
  /-- The empty-context map is substitution-free. -/
  emptyToScopeIsStructural : ∀ (target : Nat), (SubstExpr.emptyToScope target).IsStructural
  /-- Every reified substitution is substitution-free. -/
  reifyIsStructural : ∀ {target source : Nat} (vec : SubstVec target source),
    (SubstVec.reify vec).IsStructural
  /-- ★ The NbE normal form of every substitution expression is substitution-free. -/
  normalizeIsStructural : ∀ {target source : Nat} (subExpr : SubstExpr target source),
    (fxSubstNormalize subExpr).IsStructural
  /-- ★ SOUND + COMPLETE: every base morphism has a substitution-free presentation denoting it (the
  premise's headline). -/
  soundCompletePresentation : ∀ {target source : Nat} (vec : SubstVec target source),
    ∃ structuralForm : SubstExpr target source,
      structuralForm.IsStructural ∧ structuralForm.denote = vec

/-- ★ The FX context base's NbE normalizer realizes the substitution-free presentation — the witness,
wiring `isStructural_emptyToScope` / `isStructural_reify` / `fxSubstNormalize_isStructural` and the
sound + complete headline `hasSubstitutionFreePresentation`. -/
def fxSubstitutionFreeNormalForm : SubstitutionFreeNormalForm where
  emptyToScopeIsStructural := SubstExpr.isStructural_emptyToScope
  reifyIsStructural := fun vec => SubstVec.isStructural_reify vec
  normalizeIsStructural := fun subExpr => fxSubstNormalize_isStructural subExpr
  soundCompletePresentation := fun vec => SubstVec.hasSubstitutionFreePresentation vec

/-- Smoke: the NbE normal form of the identity substitution is substitution-free. -/
theorem fxSubstNormalize_isStructural_identity_smoke (scope : Nat) :
    (fxSubstNormalize (SubstExpr.identitySub : SubstExpr scope scope)).IsStructural :=
  fxSubstNormalize_isStructural SubstExpr.identitySub

end FX1Poly.Tier0

import FX1Poly.Typed.UnitCollapseBinderFence

/-! # FX1Poly/Typed/UnitVariableCollapseDeep
   — the BINDER-CROSSING unit collapse: the type-directed traversal skeleton (ULC-4 brick B)

The binder-fence refutation (`UnitCollapseBinderFence`) proved no binder-fenced canonicalizer can
be complete: β relocates unit-variable differences under binders.  This module crosses the fence.

## The binder-domain discipline: the preceding sibling

The per-generator "binder-domain table" the re-scope called for turns out to be a UNIFORM
discipline already enforced by the kernel's telescopes (TELESCOPE-REACH): for every current
binder generator, a shift-1 child's binder domain IS its immediately preceding sibling —
`gen_lam`'s body is bound by the T2 domain child before it, `gen_piTyCode`/`gen_sigmaTyCode`'s
codomain by the domain child before it.  So the traversal needs no generator table at all: it
THREADS the previous (original, un-collapsed) sibling through the children spine and pushes it as
the context extension when it meets a shift-1 child.  Honest fences that remain: a shift-1 child
with NO preceding sibling, and shift ≥ 2 children, are left untouched (none exist in the current
generator population's live rows; the Z0 eliminator-motive migration will revisit).

## What this module ships

  * `collapseUnitVariablesDeep` / `collapseUnitVariablesDeepChildren` — the binder-crossing
    traversal (mutual, structural, cast-free).
  * ★ `deepCollapse_crossesBinderFence` — the architecture's proof-of-life: the deep collapse
    sends the binder-fence witness's normal form `λ(b:Unit). x↑` to `λ(b:Unit). unitCell` — BY
    `rfl` — erasing exactly the difference every fenced canonicalizer provably cannot reach.
  * ★ `deepCollapse_identifiesKonstNormalForms` — the two βη normal forms that refuted
    normalize-first are IDENTIFIED by the deep collapse (syntactic comparison succeeds where the
    fenced procedure provably answers NO).
  * `deepCollapse_computesGapPair` — the deep collapse agrees with the fenced one on the original
    gap pair (binder-free terms are treated identically).

## Honest boundaries

(1) SOUNDNESS is the next brick: relating a term to its deep collapse needs the binder-crossing
congruence arm in the spec (`DefEqUnitEtaCong` currently fences binder children via `consEqual`);
the planned arm relates bodies in `context.cons domainSibling` with the SAME original domain on
both sides, and composes with `congGen` + `trans` to cover collapsed domains.  (2) The pushed
domain is the ORIGINAL previous sibling (the left-side convention) — the body is collapsed
against the un-collapsed domain's lookup, matching the planned spec arm.  (3) Completeness of the
deep canonicalizer re-poses AFTER soundness; the congGen/normalization commutation concern
stands.

## Zero-axiom verification

Mutual structural recursion threading an `Option` accumulator — no casts, no measure; the
computations are `rfl`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core

mutual

/-- **The binder-crossing unit-variable collapse**: like `collapseUnitVariables`, but binder
children are traversed under the context extended by their preceding sibling (the telescope
discipline), so unit-typed variables UNDER binders collapse too. -/
def collapseUnitVariablesDeep {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) : RawTerm scope → RawTerm scope
  | .mkGen generator payload children =>
      if isVariable : generator = Generator.gen_var then
        if (context.lookup
            (Eq.rec (motive := fun targetGenerator _ => targetGenerator.payload scope)
              payload isVariable)) = unitTypeCell then
          unitCell
        else
          .mkGen generator payload children
      else
        .mkGen generator payload (collapseUnitVariablesDeepChildren context none children)

/-- Children traversal threading the previous (ORIGINAL) sibling: shift-0 heads collapse in the
ambient context and become the next sibling's candidate domain; a shift-1 head with an available
preceding sibling collapses under the EXTENDED context; binder heads without a preceding sibling
and shift ≥ 2 heads stay fenced (none live in the current generator population). -/
def collapseUnitVariablesDeepChildren {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) :
    Option (RawTerm scope) → {shifts : List Nat} →
      RawTermChildren shifts scope → RawTermChildren shifts scope
  | _, _, .childNil => .childNil
  | _, _, @RawTermChildren.childCons _ 0 _ headChild restChildren =>
      .childCons (collapseUnitVariablesDeep context headChild)
        (collapseUnitVariablesDeepChildren context (some headChild) restChildren)
  | some domainSibling, _, @RawTermChildren.childCons _ 1 _ bodyChild restChildren =>
      .childCons (collapseUnitVariablesDeep (context.cons domainSibling) bodyChild)
        (collapseUnitVariablesDeepChildren context none restChildren)
  | none, _, @RawTermChildren.childCons _ 1 _ headChild restChildren =>
      .childCons headChild (collapseUnitVariablesDeepChildren context none restChildren)
  | _, _, @RawTermChildren.childCons _ (_ + 2) _ headChild restChildren =>
      .childCons headChild (collapseUnitVariablesDeepChildren context none restChildren)

end

/-- **★ The fence is crossed — proof of life**: the deep collapse sends the binder-fence
witness's normal form `λ(b:Unit). x↑` to `λ(b:Unit). unitCell` BY `rfl` — the body's weakened
unit variable is found through the extended-context lookup, the exact rewrite
`UnitCollapseBinderFence` proves NO fenced canonicalizer can perform. -/
theorem deepCollapse_crossesBinderFence (profile : PolyProfile) :
    collapseUnitVariablesDeep (unitVariableContext profile) konstAppliedToVariableNormalForm
      = konstAppliedToUnitNormalForm := rfl

/-- **★ The deep collapse IDENTIFIES the normal forms that refuted normalize-first**: syntactic
comparison after the deep collapse succeeds exactly where `normalizeFirstCanonicalizer_isIncomplete`
proves the fenced comparison answers NO. -/
theorem deepCollapse_identifiesKonstNormalForms (profile : PolyProfile) :
    collapseUnitVariablesDeep (unitVariableContext profile) konstAppliedToVariableNormalForm
      = collapseUnitVariablesDeep (unitVariableContext profile)
          konstAppliedToUnitNormalForm := rfl

/-- The deep collapse agrees with the fenced collapse on the original (binder-free) gap pair. -/
theorem deepCollapse_computesGapPair (profile : PolyProfile) :
    collapseUnitVariablesDeep (unitVariableContext profile) pairOfUnitVariables
      = pairOfUnitValues := rfl

end FX1Poly.Typed

import FX1Poly.Tier0.FxBaseSubstCategory

/-! # Tier0/ContextOmega/Colimits — finite coproducts of contexts (context-3, the colimit half)

The RIGHT/colimit content of the context ω-category: the category of contexts-and-substitutions
`fxBaseSubstCategory` (objects = scopes, `Hom(X, Y) = SubstVec Y X`) has **finite coproducts** —
context concatenation — and an **initial object** (the empty context).  This is the "+ pushouts /
colimits of contexts" half of context-3, realized concretely and zero-axiom over the shipped
`SubstVec`.

## The coproduct = context concatenation

The coproduct of contexts `firstScope` and `secondScope` is the object `firstScope + secondScope`,
witnessed by the hom-set bijection

    Hom(firstScope + secondScope, Y)  ≅  Hom(firstScope, Y) × Hom(secondScope, Y)

i.e. `SubstVec Y (firstScope + secondScope) ≅ SubstVec Y firstScope × SubstVec Y secondScope`.
Because `SubstVec Y n` is the product-recursive `n`-tuple of `RawTerm Y`, and `Nat.add` recurses on
its second argument (`firstScope + (secondScope + 1) = (firstScope + secondScope) + 1`
DEFINITIONALLY), the split/append legs are total structural recursions on `secondScope` with NO `Fin`
arithmetic:

  * `coproductCopair` — the copairing `[f, g]`: append `f`'s and `g`'s images (`g` at the front).
  * `coproductSplit` — its inverse: peel the `secondScope` front entries back off.
  * `coproductSplit_coproductCopair` / `coproductCopair_coproductSplit` — the two round-trips (the
    bijection), each by `secondScope`-induction closing on product-eta + `PUnit` eta.

## The initial object = the empty context

`Hom(0, Y) = SubstVec Y 0 = PUnit` is a subsingleton, so the empty context `0` is initial: there is
exactly one substitution out of it (`emptyContextMorphism`), and it is unique
(`emptyContextInitial_unique`).

## Honest boundaries

  * **Naturality of the coproduct bijection in the target `Y`** (which upgrades the hom-set bijection
    to the fully-coherent categorical coproduct) is a straightforward but separate `secondScope`
    -induction through a `compose`-`cons` distribution lemma; it is deferred, not claimed here.  The
    hom-set bijection delivered IS the coproduct universal property pointwise.
  * **The dimensional adjoint quadruple `Ⅎ ⊣ Σ ⊣ Ω ⊣ Π ⊣ ◊` and the transpension `◊`** — the other,
    genuinely harder half of context-3 — are NOT mechanized here.  The transpension is the rightmost
    adjoint and does NOT commute with substitution (Nuyts–Devriese 2008.08533 §2.1.7), so its
    categorical realization needs the affine/fresh-substitution layer; the shipped
    `Core/TranspensionAffineContractionEquivariance` (TRANSP-DSL GO) handles the SYNTACTIC gel-β
    contraction and `gen_transpension` (TRANSP-1 #1418) is its operational build-out.  This file
    delivers the cleanly-provable colimit half.

## Zero-axiom verification

The copair/split legs are structural recursion on `secondScope` (defeq-clean via `Nat.add`'s
second-argument recursion); the round-trips are `secondScope`-induction with product-eta + `PUnit`
eta (the closing `rfl` after the IH rewrite); the initial object is `PUnit` eta.  No `Fin.cases`, no
`funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.
Per-declaration gated in `FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-! ## The coproduct of contexts = context concatenation -/

/-- **The copairing `[f, g]` of the coproduct `firstScope + secondScope`.**  Appends the right part
`g` (at the front) onto the left part `f`: a substitution into each summand assembles into one
substitution out of the concatenated context.  Structural recursion on `secondScope` — at `0` it is
`f` (since `firstScope + 0 = firstScope` definitionally), at a successor it conses `g`'s head. -/
def coproductCopair {ambientScope firstScope : Nat} :
    {secondScope : Nat} →
      SubstVec ambientScope firstScope → SubstVec ambientScope secondScope →
      SubstVec ambientScope (firstScope + secondScope)
  | 0, leftPart, _rightPart => leftPart
  | _ + 1, leftPart, rightPart => (rightPart.1, coproductCopair leftPart rightPart.2)

/-- **The inverse of the copairing.**  Splits a substitution out of `firstScope + secondScope` into
its left and right restrictions — peeling the `secondScope` front entries back off.  Structural
recursion on `secondScope`. -/
def coproductSplit {ambientScope firstScope : Nat} :
    {secondScope : Nat} →
      SubstVec ambientScope (firstScope + secondScope) →
      SubstVec ambientScope firstScope × SubstVec ambientScope secondScope
  | 0, combinedVec => (combinedVec, PUnit.unit)
  | _ + 1, combinedVec =>
      ((coproductSplit combinedVec.2).1, (combinedVec.1, (coproductSplit combinedVec.2).2))

/-- **Round-trip (split ∘ copair = id).**  Splitting a freshly copaired substitution recovers both
summand restrictions — by `secondScope`-induction (the base is `PUnit` eta; the step is the IH on the
tail closed by product-eta). -/
theorem coproductSplit_coproductCopair {ambientScope firstScope : Nat} :
    {secondScope : Nat} → (leftPart : SubstVec ambientScope firstScope) →
      (rightPart : SubstVec ambientScope secondScope) →
      coproductSplit (coproductCopair leftPart rightPart) = (leftPart, rightPart)
  | 0, _leftPart, _rightPart => rfl
  | _ + 1, leftPart, rightPart => by
      show ((coproductSplit (coproductCopair leftPart rightPart.2)).1,
            (rightPart.1, (coproductSplit (coproductCopair leftPart rightPart.2)).2)) = (leftPart, rightPart)
      rw [coproductSplit_coproductCopair leftPart rightPart.2]
      rfl

/-- **Round-trip (copair ∘ split = id).**  Re-appending a substitution's split restrictions recovers
it — `secondScope`-induction, product-eta. -/
theorem coproductCopair_coproductSplit {ambientScope firstScope : Nat} :
    {secondScope : Nat} → (combinedVec : SubstVec ambientScope (firstScope + secondScope)) →
      coproductCopair (coproductSplit combinedVec).1 (coproductSplit combinedVec).2 = combinedVec
  | 0, _combinedVec => rfl
  | _ + 1, combinedVec => by
      show (combinedVec.1,
            coproductCopair (coproductSplit combinedVec.2).1 (coproductSplit combinedVec.2).2) = combinedVec
      rw [coproductCopair_coproductSplit combinedVec.2]
      rfl

/-- **The coproduct hom-set bijection.**  `coproductSplit` and `coproductCopair` are mutually inverse,
so `Hom(firstScope + secondScope, Y) ≅ Hom(firstScope, Y) × Hom(secondScope, Y)` — the universal
property that exhibits `firstScope + secondScope` as the coproduct of `firstScope` and `secondScope`
in the context category (naturality in `Y` deferred — see the module header). -/
theorem coproductHomBijection {ambientScope firstScope secondScope : Nat} :
    (∀ leftPart : SubstVec ambientScope firstScope,
      ∀ rightPart : SubstVec ambientScope secondScope,
        coproductSplit (coproductCopair leftPart rightPart) = (leftPart, rightPart)) ∧
    (∀ combinedVec : SubstVec ambientScope (firstScope + secondScope),
        coproductCopair (coproductSplit combinedVec).1 (coproductSplit combinedVec).2 = combinedVec) :=
  ⟨fun leftPart rightPart => coproductSplit_coproductCopair leftPart rightPart,
   fun combinedVec => coproductCopair_coproductSplit combinedVec⟩

/-! ## The initial object = the empty context -/

/-- **The unique substitution out of the empty context.**  `Hom(0, Y) = SubstVec Y 0 = PUnit`. -/
def emptyContextMorphism (ambientScope : Nat) : SubstVec ambientScope 0 := PUnit.unit

/-- **The empty context is initial.**  Any two substitutions out of the empty context are equal
(`SubstVec _ 0` is `PUnit`, a subsingleton) — so `0` is the initial object of the context category. -/
theorem emptyContextInitial_unique {ambientScope : Nat}
    (firstMorphism secondMorphism : SubstVec ambientScope 0) :
    firstMorphism = secondMorphism :=
  rfl

end FX1Poly.Tier0.ContextOmega

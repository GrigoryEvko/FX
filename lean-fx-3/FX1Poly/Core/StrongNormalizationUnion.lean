/-! # FX1Poly/Core/StrongNormalizationUnion
    — the abstract Geser strong-normalization-of-union criterion (the βη-SN crux)

Strong normalization is NOT generally preserved by taking the union of two SN relations (β and η
INTERLEAVE; no single measure decreases on both — β can grow term size, η shrinks it but need not lower
the β-reduction rank).  The classical fix (Bachmair-Dershowitz / Geser) is QUASI-COMMUTATION: if the
second relation quasi-commutes over the first, the union is SN.  This file proves that criterion
constructively, Init-only, over arbitrary relations:

  `reduceLeft` SN at `a`  ∧  `reduceRight` SN everywhere  ∧  `reduceRight` quasi-commutes over
  `reduceLeft`   ⇒   `reduceLeft ∪ reduceRight` SN at `a`.

For FX this is instantiated with `reduceLeft := Step` (β/ι), `reduceRight := Step.eta` (η) — β-SN
for well-typed terms is open βη-SN's β half, η-SN is unconditional (`Step.etaStar.isStronglyNormalizing`,
every term, since η strictly shrinks `RawTerm.size`), and the η-postponement-over-β quasi-commutation is the
per-η-constructor critical-pair work — yielding open βη-SN.  It is equally the
reusable substrate for SN-robustness under future extensions (cubical, HITs).

## The proof shape (why it goes through)

`accUnion` inducts on the β-accessibility of `a` (outer).  The body builds `Acc UnionSuccessor a` by an INNER
induction (`accUnionInner`) on the η-accessibility of `a`, whose motive carries the outer β-induction
hypothesis AS THE GOAL'S ANTECEDENT — so the η-descent keeps it.  A β-step forwards that hypothesis directly;
an η-step uses the inner IH and reconstructs the η-descendant's β-predecessor obligations via
QUASI-COMMUTATION (`reduceRight a b → reduceLeft b c ⇒ ∃ d, reduceLeft a d ∧ (d →* c)`) plus downward
closure of accessibility along union-star reduction.  The naive lex(β-Acc, size) fails precisely because a
β-predecessor of an η-descendant is neither β-smaller nor size-smaller; quasi-commutation is what supplies it.

## Zero-axiom verification

Structural `Acc.rec` / `Acc.inv`, `Or`/`Exists`/`And` elimination, and an induction on the minimal
`UnionStar` closure.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

/-- Reflexive-transitive closure of the union of two relations (Init-only, minimal). -/
inductive UnionStar {Alpha : Type} (reduceLeft reduceRight : Alpha → Alpha → Prop) :
    Alpha → Alpha → Prop
  | refl (a : Alpha) : UnionStar reduceLeft reduceRight a a
  | tailLeft {a b c : Alpha} :
      UnionStar reduceLeft reduceRight a b → reduceLeft b c → UnionStar reduceLeft reduceRight a c
  | tailRight {a b c : Alpha} :
      UnionStar reduceLeft reduceRight a b → reduceRight b c → UnionStar reduceLeft reduceRight a c

/-- The one-step-successor relation for `reduceLeft ∪ reduceRight` accessibility (strong
normalization): `later` is below `earlier` when `earlier` reduces to `later` by either relation. -/
def UnionSuccessor {Alpha : Type} (reduceLeft reduceRight : Alpha → Alpha → Prop)
    (later earlier : Alpha) : Prop :=
  reduceLeft earlier later ∨ reduceRight earlier later

/-- Accessibility for the union is closed downward along union-star reduction: if `a` is union-SN and
`a` union-reduces to `b`, then `b` is union-SN. -/
theorem accDownwardUnionStar {Alpha : Type} {reduceLeft reduceRight : Alpha → Alpha → Prop}
    {a b : Alpha}
    (accStart : Acc (UnionSuccessor reduceLeft reduceRight) a)
    (star : UnionStar reduceLeft reduceRight a b) :
    Acc (UnionSuccessor reduceLeft reduceRight) b := by
  induction star with
  | refl => exact accStart
  | tailLeft _ stepToReduct ih => exact ih.inv (Or.inl stepToReduct)
  | tailRight _ stepToReduct ih => exact ih.inv (Or.inr stepToReduct)

/-- `reduceRight` quasi-commutes over `reduceLeft`: a `reduceRight`-step followed by a `reduceLeft`-step
can be reordered into a `reduceLeft`-step followed by a union-star reduction (for βη: η-postponement over
β — η-then-β becomes β-then-βη*). -/
def QuasiCommutesRightOverLeft {Alpha : Type} (reduceLeft reduceRight : Alpha → Alpha → Prop) : Prop :=
  ∀ a b c : Alpha,
    reduceRight a b → reduceLeft b c → ∃ d, reduceLeft a d ∧ UnionStar reduceLeft reduceRight d c

/-- Inner step of the Geser criterion: by induction on the `reduceRight`-accessibility of `a`, with the
`reduceLeft`-induction-hypothesis carried as the goal's antecedent (so the right-descent keeps it).  A
left-step forwards `leftIH`; a right-step uses the inner IH and reconstructs the right-descendant's
left-predecessor obligations via quasi-commutation + downward closure. -/
theorem accUnionInner {Alpha : Type} {reduceLeft reduceRight : Alpha → Alpha → Prop}
    (quasiCommutes : QuasiCommutesRightOverLeft reduceLeft reduceRight) {a : Alpha}
    (accRight : Acc (fun later earlier => reduceRight earlier later) a) :
    (∀ predecessor, reduceLeft a predecessor →
        Acc (UnionSuccessor reduceLeft reduceRight) predecessor) →
      Acc (UnionSuccessor reduceLeft reduceRight) a := by
  induction accRight with
  | intro a _accRightInv innerIH =>
    intro leftIH
    refine Acc.intro a (fun reduct unionStep => ?_)
    rcases unionStep with leftStep | rightStep
    · exact leftIH reduct leftStep
    · refine innerIH reduct rightStep (fun deepPredecessor deepLeftStep => ?_)
      obtain ⟨detour, leftToDetour, detourStar⟩ :=
        quasiCommutes a reduct deepPredecessor rightStep deepLeftStep
      exact accDownwardUnionStar (leftIH detour leftToDetour) detourStar

/-- **Geser strong-normalization-of-union.**  If `reduceLeft` is strongly normalizing at `a`,
`reduceRight` is strongly normalizing everywhere, and `reduceRight` quasi-commutes over `reduceLeft`, then
the union is strongly normalizing at `a`.  The Bachmair-Dershowitz criterion, constructive and zero-axiom —
the make-or-break crux for open βη strong normalization. -/
theorem accUnion {Alpha : Type} {reduceLeft reduceRight : Alpha → Alpha → Prop}
    (rightStronglyNormalizing :
      ∀ x, Acc (fun later earlier => reduceRight earlier later) x)
    (quasiCommutes : QuasiCommutesRightOverLeft reduceLeft reduceRight) {a : Alpha}
    (accLeft : Acc (fun later earlier => reduceLeft earlier later) a) :
    Acc (UnionSuccessor reduceLeft reduceRight) a := by
  induction accLeft with
  | intro a _accLeftInv outerIH =>
    exact accUnionInner quasiCommutes (rightStronglyNormalizing a) outerIH

end FX1Poly.Core

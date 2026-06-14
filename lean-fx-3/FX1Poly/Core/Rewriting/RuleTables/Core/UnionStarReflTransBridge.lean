import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationUnion
import FX1Poly.Core.Rewriting.Confluence.Newman

/-! # FX1Poly/Core/UnionStarReflTransBridge
    — the snoc-form union closure `UnionStar` and the head-form generic
      `ReflTransClosure` of the pointwise union are the same closure.

`UnionStar reduceLeft reduceRight` (`StrongNormalizationUnion`) is the
reflexive-transitive closure of `reduceLeft ∪ reduceRight` in SNOC form —
its `tailLeft` / `tailRight` constructors append a single left/right step
at the END of a chain.  `ReflTransClosure rel` (`Newman`) is the generic
HEAD-form closure of a single relation `rel`.  At the pointwise union
`rel := fun source target => reduceLeft source target ∨ reduceRight source target`
the two closures coincide.

This is the vocabulary bridge the guarded-Newman confluence assembly
needs: the canonical beta-eta union's strong-normalization witness and its
reduction chains are stated in the `UnionStar` / `UnionSuccessor`
vocabulary, while the relation-generic `newmanGuarded` consumes
`ReflTransClosure` and `Acc (flip rel)`.  The accessibility side already
matches up to a definitional unfold (`UnionSuccessor reduceLeft reduceRight`
is `flip` of the pointwise union); only the snoc-vs-head closures need this
explicit bridge.

## Zero-axiom verification

`UnionStar.head` prepends a step by structural recursion on the tail (the
chain's START stays fixed, so the prepended step stays well-typed
throughout); the two transports are structural inductions composing
`ReflTransClosure.trans` / `ReflTransClosure.single` and `UnionStar.head`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
`omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCoreTerminationOrders.lean`. -/

namespace FX1Poly.Core

variable {Carrier : Type}

/-- A single union step **prepends** to a `UnionStar` chain.  `UnionStar`'s
constructors only append at the tail, but recursion on the tail keeps the
chain's START (and hence the prepended `firstStep`) fixed, so the head
extension goes through — the snoc closure is also a head closure. -/
theorem UnionStar.head {reduceLeft reduceRight : Carrier → Carrier → Prop}
    {source middle target : Carrier}
    (firstStep : reduceLeft source middle ∨ reduceRight source middle)
    (rest : UnionStar reduceLeft reduceRight middle target) :
    UnionStar reduceLeft reduceRight source target := by
  induction rest with
  | refl =>
      cases firstStep with
      | inl leftStep => exact .tailLeft (.refl source) leftStep
      | inr rightStep => exact .tailRight (.refl source) rightStep
  | tailLeft _prefixChain leftStep prefixIsHeaded =>
      exact .tailLeft prefixIsHeaded leftStep
  | tailRight _prefixChain rightStep prefixIsHeaded =>
      exact .tailRight prefixIsHeaded rightStep

/-- **Forward**: a snoc-form union chain is a head-form reflexive-transitive
closure of the pointwise union.  Each tail step appends a single union step
to the head-form prefix. -/
theorem UnionStar.toReflTransClosure
    {reduceLeft reduceRight : Carrier → Carrier → Prop}
    {source target : Carrier}
    (chain : UnionStar reduceLeft reduceRight source target) :
    ReflTransClosure
      (fun stepSource stepTarget =>
        reduceLeft stepSource stepTarget ∨ reduceRight stepSource stepTarget)
      source target := by
  induction chain with
  | refl => exact .refl _
  | tailLeft _prefixChain leftStep prefixIsHeaded =>
      exact prefixIsHeaded.trans (.single (Or.inl leftStep))
  | tailRight _prefixChain rightStep prefixIsHeaded =>
      exact prefixIsHeaded.trans (.single (Or.inr rightStep))

/-- **Backward**: a head-form reflexive-transitive closure of the pointwise
union is a snoc-form union chain.  Each head step prepends via
`UnionStar.head`. -/
theorem ReflTransClosure.toUnionStar
    {reduceLeft reduceRight : Carrier → Carrier → Prop}
    {source target : Carrier}
    (chain : ReflTransClosure
      (fun stepSource stepTarget =>
        reduceLeft stepSource stepTarget ∨ reduceRight stepSource stepTarget)
      source target) :
    UnionStar reduceLeft reduceRight source target := by
  induction chain with
  | refl => exact .refl _
  | head firstStep _restChain restIsSnoc =>
      exact UnionStar.head firstStep restIsSnoc

end FX1Poly.Core

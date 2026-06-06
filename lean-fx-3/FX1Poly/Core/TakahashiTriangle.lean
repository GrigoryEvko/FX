import FX1Poly.Core.DiamondConfluence

/-! # FX1Poly/Core/TakahashiTriangle
    — the Takahashi triangle lemma: a complete-development function with the triangle property ⟹ the diamond

`DiamondConfluence.lean` proves the Tait/Martin-Löf/Takahashi confluence core — a relation with the
`DiamondProperty` has confluent reflexive-transitive closure, with NO termination needed — and
`StepParallelConfluence.lean` reduces FX raw confluence to exhibiting a parallel reduction sandwiched
`Step ⊆ ParStep ⊆ StepStar` whose `DiamondProperty` holds.  The remaining obligation is that diamond.

Proving the diamond of a parallel reduction DIRECTLY (joining two arbitrary diverging parallel steps) is
a quadratic case analysis.  Takahashi 1995 (*Parallel reductions in λ-calculus*) replaces it by a LINEAR
argument: define a `completeDevelopment` function that contracts ALL the redexes of a term at once, and
prove the one-sided TRIANGLE property — every parallel reduct of `source` parallel-reduces further to
`completeDevelopment source`.  The diamond falls out immediately: two diverging reducts both reduce to
the single complete development, which is therefore their common reduct.

This file ships that abstract reduction — `TriangleProperty`, `DiamondProperty.ofTriangle`,
`Confluent.ofTriangle` — over an arbitrary relation, so the eventual concrete FX parallel-reduction
diamond (the unconditional raw-confluence prize that strong normalization cannot supply
because raw β+ι is not SN) reduces to the single linear obligation "exhibit `completeDevelopment` and
prove its triangle", rather than the quadratic direct diamond.  It composes with the shipped
`diamondConfluence` and `StepStar.hasConfluence_of_parallelDiamond` to complete the pipeline.

## Zero-axiom verification

`DiamondProperty.ofTriangle` is `intro` + an anonymous-constructor `exact` (the common reduct is
`completeDevelopment source`, reached from both sides by the triangle); `Confluent.ofTriangle` composes
it with the shipped `diamondConfluence`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

universe carrierUniverse
variable {Carrier : Type carrierUniverse}

/-- **The triangle property of a complete-development function.**  `completeDevelopment` maps each point
to its maximal one-shot reduct, and EVERY single `rel`-step out of `source` reduces further, in a single
`rel`-step, to `completeDevelopment source`.  This is Takahashi's one-sided replacement for the diamond:
the complete development is a common target reachable from every reduct. -/
def TriangleProperty (rel : Carrier → Carrier → Prop) (completeDevelopment : Carrier → Carrier) : Prop :=
  ∀ {source target : Carrier}, rel source target → rel target (completeDevelopment source)

/-- **Takahashi triangle lemma: triangle property ⟹ diamond property.**  Given a complete-development
function with the triangle property, two diverging single steps `rel source leftStep` and
`rel source rightStep` reconverge at `completeDevelopment source`: the triangle sends each reduct there
in one further step.  This is the linear route to the diamond — no quadratic redex-pair case split. -/
theorem DiamondProperty.ofTriangle {rel : Carrier → Carrier → Prop}
    {completeDevelopment : Carrier → Carrier}
    (triangle : TriangleProperty rel completeDevelopment) : DiamondProperty rel := by
  intro source leftStep rightStep leftReduction rightReduction
  exact ⟨completeDevelopment source, triangle leftReduction, triangle rightReduction⟩

/-- **Triangle property ⟹ confluence.**  Composing `DiamondProperty.ofTriangle` with the shipped
`diamondConfluence`: a relation admitting a complete-development function with the triangle property has
confluent reflexive-transitive closure, with no termination assumption.  This is the headline Takahashi
result, the form the concrete FX parallel reduction will instantiate to discharge raw confluence. -/
theorem Confluent.ofTriangle {rel : Carrier → Carrier → Prop}
    {completeDevelopment : Carrier → Carrier}
    (triangle : TriangleProperty rel completeDevelopment) : Confluent rel :=
  diamondConfluence (DiamondProperty.ofTriangle triangle)

/-- **A relation has maximal reducts** when every point has a reduct to which every other single-step
reduct further reduces.  This is the EXISTENTIAL, per-source form of Takahashi's complete development:
instead of a separately-defined total `completeDevelopment` function (which over `RawTerm` would need a
full structural-recursion definition plus a termination argument), the maximal reduct is exhibited
per-source — the form a concrete FX parallel-reduction diamond proof discharges by induction on the
source term. -/
def HasMaximalReduct (rel : Carrier → Carrier → Prop) : Prop :=
  ∀ source : Carrier, ∃ maximalReduct : Carrier,
    ∀ target : Carrier, rel source target → rel target maximalReduct

/-- A complete-development function with the triangle property yields maximal reducts: its value at each
source is the witness, and the triangle property is exactly the "every reduct reaches it" clause.  So the
existential `HasMaximalReduct` form generalizes the function-based `TriangleProperty`. -/
theorem HasMaximalReduct.ofTriangle {rel : Carrier → Carrier → Prop}
    {completeDevelopment : Carrier → Carrier}
    (triangle : TriangleProperty rel completeDevelopment) : HasMaximalReduct rel :=
  fun source => ⟨completeDevelopment source, fun _target reduction => triangle reduction⟩

/-- **Maximal reducts ⟹ diamond property.**  The per-source form of the Takahashi triangle argument: two
diverging single steps `rel source leftStep` and `rel source rightStep` reconverge at the maximal reduct
of `source`, since by definition every reduct of `source` reaches it in one further step.  Linear, no
quadratic redex-pair split. -/
theorem DiamondProperty.ofMaximalReduct {rel : Carrier → Carrier → Prop}
    (hasMaximalReduct : HasMaximalReduct rel) : DiamondProperty rel := by
  intro source leftStep rightStep leftReduction rightReduction
  obtain ⟨maximalReduct, reductsReachMaximal⟩ := hasMaximalReduct source
  exact ⟨maximalReduct,
    reductsReachMaximal leftStep leftReduction, reductsReachMaximal rightStep rightReduction⟩

/-- **Maximal reducts ⟹ confluence.**  Composing `DiamondProperty.ofMaximalReduct` with the shipped
`diamondConfluence`.  This is the form the concrete FX parallel reduction will instantiate: prove that
every term has a maximal parallel reduct (by structural recursion), and raw confluence follows with no
termination assumption. -/
theorem Confluent.ofMaximalReduct {rel : Carrier → Carrier → Prop}
    (hasMaximalReduct : HasMaximalReduct rel) : Confluent rel :=
  diamondConfluence (DiamondProperty.ofMaximalReduct hasMaximalReduct)

end FX1Poly.Core

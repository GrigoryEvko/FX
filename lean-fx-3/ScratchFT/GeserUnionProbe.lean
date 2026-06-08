/-! Probe (NEVER committed): OSN-B2 — abstract Geser SN-of-union, Init-only constructive Acc.
    R SN at a ∧ S SN everywhere ∧ S quasi-commutes over R  ⇒  (R∪S) SN at a.
    The make-or-break for OSN-1 (βη-SN). Nested Acc: outer on R-Acc (β), inner on S-Acc (η) with the
    inner motive carrying the outer R-IH; quasi-commutation supplies the η-descendant's R-predecessors. -/

namespace FX1Poly.Core.Spike

/-- Reflexive-transitive closure of the union of two relations (Init-only, minimal). -/
inductive UnionStar {Alpha : Type} (reduceLeft reduceRight : Alpha → Alpha → Prop) :
    Alpha → Alpha → Prop
  | refl (a : Alpha) : UnionStar reduceLeft reduceRight a a
  | tailLeft {a b c : Alpha} :
      UnionStar reduceLeft reduceRight a b → reduceLeft b c → UnionStar reduceLeft reduceRight a c
  | tailRight {a b c : Alpha} :
      UnionStar reduceLeft reduceRight a b → reduceRight b c → UnionStar reduceLeft reduceRight a c

/-- The successor relation for `R∪S` accessibility (SN): `later` is below `earlier` when `earlier`
reduces to `later` by either relation. -/
def UnionSuccessor {Alpha : Type} (reduceLeft reduceRight : Alpha → Alpha → Prop)
    (later earlier : Alpha) : Prop :=
  reduceLeft earlier later ∨ reduceRight earlier later

/-- Accessibility for the union is closed downward along union-star reduction. -/
theorem accDownwardUnionStar {Alpha : Type} {reduceLeft reduceRight : Alpha → Alpha → Prop}
    {a b : Alpha}
    (accStart : Acc (UnionSuccessor reduceLeft reduceRight) a)
    (star : UnionStar reduceLeft reduceRight a b) :
    Acc (UnionSuccessor reduceLeft reduceRight) b := by
  induction star with
  | refl => exact accStart
  | tailLeft _ stepToC ih => exact ih.inv (Or.inl stepToC)
  | tailRight _ stepToC ih => exact ih.inv (Or.inr stepToC)

/-- S quasi-commutes over R: an S-step then an R-step can be reordered to an R-step then a
union-star reduction (η-postponement over β). -/
def QuasiCommutesRightOverLeft {Alpha : Type} (reduceLeft reduceRight : Alpha → Alpha → Prop) : Prop :=
  ∀ a b c : Alpha,
    reduceRight a b → reduceLeft b c → ∃ d, reduceLeft a d ∧ UnionStar reduceLeft reduceRight d c

/-- Inner step: by induction on the S-accessibility of `a`, carrying the R-induction-hypothesis in
the motive.  The R-step case forwards `leftIH`; the S-step case reconstructs the descendant's
`leftIH` via quasi-commutation. -/
theorem accUnionInner {Alpha : Type} {reduceLeft reduceRight : Alpha → Alpha → Prop}
    (quasiComm : QuasiCommutesRightOverLeft reduceLeft reduceRight) {a : Alpha}
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
    · refine innerIH reduct rightStep (fun deepPred deepLeftStep => ?_)
      obtain ⟨detour, leftToDetour, detourStar⟩ := quasiComm a reduct deepPred rightStep deepLeftStep
      exact accDownwardUnionStar (leftIH detour leftToDetour) detourStar

/-- **Geser SN-of-union.**  If `reduceLeft` (β) is strongly normalizing at `a`, `reduceRight` (η) is
strongly normalizing everywhere, and η quasi-commutes over β, then the union is strongly normalizing
at `a`. -/
theorem accUnion {Alpha : Type} {reduceLeft reduceRight : Alpha → Alpha → Prop}
    (rightStronglyNormalizing :
      ∀ x, Acc (fun later earlier => reduceRight earlier later) x)
    (quasiComm : QuasiCommutesRightOverLeft reduceLeft reduceRight) {a : Alpha}
    (accLeft : Acc (fun later earlier => reduceLeft earlier later) a) :
    Acc (UnionSuccessor reduceLeft reduceRight) a := by
  induction accLeft with
  | intro a _accLeftInv outerIH =>
    exact accUnionInner quasiComm (rightStronglyNormalizing a) outerIH

end FX1Poly.Core.Spike

#print axioms FX1Poly.Core.Spike.accDownwardUnionStar
#print axioms FX1Poly.Core.Spike.accUnionInner
#print axioms FX1Poly.Core.Spike.accUnion

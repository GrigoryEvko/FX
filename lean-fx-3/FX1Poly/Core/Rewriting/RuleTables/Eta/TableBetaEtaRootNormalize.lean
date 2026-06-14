import FX1Poly.Core.Rewriting.RuleTables.Eta.TableBetaEtaRootReduce
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationUnion

/-! # TableBetaEtaRootNormalize — the union normalizer for the canonical
table beta-eta-root relation

The second computable brick of the TABLE-NATIVE union beta-eta decider:
the normalizer FUNCTION for the canonical union
`StepTableBetaEtaRootUnion = StepTable ∨ StepEtaRootTable`, driven by
PIECE 1's `reduceOnceTableBetaEtaRoot?` along a
`UnionSuccessor StepTable StepEtaRootTable` accessibility witness.

The descent shrinks the accessibility PROOF, not the term (β/ι grow
terms), so the recursion is `Acc.rec` — NOT `WellFounded.fix` (which
leaks `propext` + `Quot.sound` and would not reduce).  The single seam
to PIECE 1 is that the reducer's soundness
(`reduceOnceTableBetaEtaRoot?_sound`) produces a `StepTableBetaEtaRootUnion`
step, which IS the `UnionSuccessor` predecessor obligation
DEFINITIONALLY (both unfold to the same `StepTable ∨ StepEtaRootTable`),
so it feeds the accessibility inverse with no transport.

* `RawTerm.normalizeTableBetaEtaRoot` — iterate the reducer to a union
  normal form;
* `normalizeTableBetaEtaRoot_reachesNormalForm` — the output is reached
  by a `UnionStar` chain;
* `normalizeTableBetaEtaRoot_isNormalForm` — the output admits no
  `StepTableBetaEtaRootUnion` step (PIECE 1's blocking lemma at the
  halt).

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTableBetaEtaRootConvDecidable.lean`. -/

namespace FX1Poly.Core

/-- Prepend a left step to a union star (the head-extension brick the
normalizer's chain needs; structural recursion on the tail). -/
theorem unionStarPrependLeft {Alpha : Type}
    {reduceLeft reduceRight : Alpha → Alpha → Prop} {a b c : Alpha}
    (firstStep : reduceLeft a b)
    (restStar : UnionStar reduceLeft reduceRight b c) :
    UnionStar reduceLeft reduceRight a c := by
  induction restStar with
  | refl => exact .tailLeft (.refl _) firstStep
  | tailLeft _ stepToReduct ih => exact .tailLeft ih stepToReduct
  | tailRight _ stepToReduct ih => exact .tailRight ih stepToReduct

/-- Prepend a right step to a union star (mirror of
`unionStarPrependLeft`). -/
theorem unionStarPrependRight {Alpha : Type}
    {reduceLeft reduceRight : Alpha → Alpha → Prop} {a b c : Alpha}
    (firstStep : reduceRight a b)
    (restStar : UnionStar reduceLeft reduceRight b c) :
    UnionStar reduceLeft reduceRight a c := by
  induction restStar with
  | refl => exact .tailRight (.refl _) firstStep
  | tailLeft _ stepToReduct ih => exact .tailLeft ih stepToReduct
  | tailRight _ stepToReduct ih => exact .tailRight ih stepToReduct

/-- The reducer's soundness produces exactly the `UnionSuccessor`
predecessor obligation: `reduceOnceTableBetaEtaRoot? term = some reduct`
forces `reduct` below `term` for `StepTable ∪ StepEtaRootTable`.  The
bridge is definitional (both `Or`-unfold to the same disjunction). -/
theorem reduceOnceTableBetaEtaRoot?_unionSuccessor {scope : Nat}
    {term reduct : RawTerm scope}
    (reduced : term.reduceOnceTableBetaEtaRoot? = some reduct) :
    UnionSuccessor (StepTable (scope := scope)) StepEtaRootTable reduct term :=
  RawTerm.reduceOnceTableBetaEtaRoot?_sound reduced

/-! ## The normalizer -/

/-- **The union beta-eta-root normalizer.**  Iterate
`reduceOnceTableBetaEtaRoot?` along the accessibility witness until the
reducer halts; the result is a union normal form reached by a genuine
union step chain.  Written with `Acc.rec` because the descent shrinks
the accessibility proof, not the term.  The table twin of
`normalizeOverTable`. -/
def RawTerm.normalizeTableBetaEtaRoot {scope : Nat} (term : RawTerm scope)
    (accessible :
      Acc (UnionSuccessor (StepTable (scope := scope)) StepEtaRootTable)
        term) :
    RawTerm scope :=
  Acc.rec
    (motive := fun _currentTerm _acc => RawTerm scope)
    (fun currentTerm _accStep normalizeRec =>
      match reduceEq : currentTerm.reduceOnceTableBetaEtaRoot? with
      | none => currentTerm
      | some reduct =>
          normalizeRec reduct
            (reduceOnceTableBetaEtaRoot?_unionSuccessor reduceEq))
    accessible

/-- One-step unfolding of `normalizeTableBetaEtaRoot` at an `Acc.intro`
witness (holds by `rfl`; the proof handle for the correctness
theorems). -/
theorem RawTerm.normalizeTableBetaEtaRoot_unfold {scope : Nat}
    (term : RawTerm scope)
    (accStep :
      ∀ later,
        UnionSuccessor (StepTable (scope := scope)) StepEtaRootTable later
          term →
        Acc (UnionSuccessor (StepTable (scope := scope)) StepEtaRootTable)
          later) :
    RawTerm.normalizeTableBetaEtaRoot term (.intro term accStep) =
      (match reduceEq : term.reduceOnceTableBetaEtaRoot? with
        | none => term
        | some reduct =>
            RawTerm.normalizeTableBetaEtaRoot reduct
              (accStep reduct
                (reduceOnceTableBetaEtaRoot?_unionSuccessor reduceEq))) :=
  rfl

/-- **The normalizer reaches its output by a union step chain.** -/
theorem RawTerm.normalizeTableBetaEtaRoot_reachesNormalForm {scope : Nat}
    (term : RawTerm scope)
    (accessible :
      Acc (UnionSuccessor (StepTable (scope := scope)) StepEtaRootTable)
        term) :
    UnionStar (StepTable (scope := scope)) StepEtaRootTable term
      (RawTerm.normalizeTableBetaEtaRoot term accessible) := by
  induction accessible with
  | intro currentTerm accStep ih =>
      rw [RawTerm.normalizeTableBetaEtaRoot_unfold currentTerm accStep]
      split
      · exact UnionStar.refl _
      · next reduct reduceEq =>
          have headStep :=
            RawTerm.reduceOnceTableBetaEtaRoot?_sound reduceEq
          cases headStep with
          | inl iotaStep =>
              exact unionStarPrependLeft iotaStep
                (ih reduct
                  (reduceOnceTableBetaEtaRoot?_unionSuccessor reduceEq))
          | inr etaStep =>
              exact unionStarPrependRight etaStep
                (ih reduct
                  (reduceOnceTableBetaEtaRoot?_unionSuccessor reduceEq))

/-- **The normalizer's output is a union normal form.**  At the halt the
reducer returned `none`, so PIECE 1's blocking lemma refutes every union
step. -/
theorem RawTerm.normalizeTableBetaEtaRoot_isNormalForm {scope : Nat}
    (term : RawTerm scope)
    (accessible :
      Acc (UnionSuccessor (StepTable (scope := scope)) StepEtaRootTable)
        term) :
    ∀ next : RawTerm scope,
      ¬ StepTableBetaEtaRootUnion
          (RawTerm.normalizeTableBetaEtaRoot term accessible) next := by
  induction accessible with
  | intro currentTerm accStep ih =>
      rw [RawTerm.normalizeTableBetaEtaRoot_unfold currentTerm accStep]
      split
      · next reduceEq =>
          intro next unionStep
          exact RawTerm.reduceOnceTableBetaEtaRoot?_blocksStep reduceEq
            unionStep
      · next reduct reduceEq =>
          exact ih reduct
            (reduceOnceTableBetaEtaRoot?_unionSuccessor reduceEq)

end FX1Poly.Core

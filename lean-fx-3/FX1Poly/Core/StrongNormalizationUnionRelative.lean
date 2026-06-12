import FX1Poly.Core.StrongNormalizationUnion

/-! # StrongNormalizationUnionRelative — ETA-T6 increment 4: the
class-relativized Geser engine

The global Geser criterion (`accUnion`) demands quasi-commutation at
EVERY term — and ETA-T5 proved that demand unsatisfiable for raw
table eta over table iota (the cross-pair counterexamples).  On the
TYPED fragment the offending configurations are untypable, so the
right engine for typed union SN is the criterion RELATIVIZED to a
class of terms closed under both relations (subject reduction is
exactly that closure): quasi-commutation is demanded only AT class
members, and accessibility is concluded only FOR class members.

The proofs mirror `accUnionInner`/`accUnion` with the class threaded
as an antecedent alongside the left induction hypothesis — the
right-descent and the left-descent both stay inside the class by the
closure hypotheses, so every quasi-commutation call happens at a
class member.

Fully abstract (any `Alpha`, any two relations, any class) — the
typed instantiation (class := well-typed, closure := the two subject
reductions, quasi-commutation := the T5 mutual with the duality
oracle discharged by untypability) is downstream work; this engine is
the load-bearing missing piece it plugs into.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditStrongNormalizationUnionRelative.lean`. -/

namespace FX1Poly.Core

/-- Quasi-commutation demanded only at members of a class. -/
def QuasiCommutesRightOverLeftOn {Alpha : Type} (klass : Alpha → Prop)
    (reduceLeft reduceRight : Alpha → Alpha → Prop) : Prop :=
  ∀ a b c : Alpha, klass a →
    reduceRight a b → reduceLeft b c →
    ∃ d, reduceLeft a d ∧ UnionStar reduceLeft reduceRight d c

/-- The global criterion implies the relativized one at any class. -/
theorem QuasiCommutesRightOverLeftOn.ofGlobal {Alpha : Type}
    (klass : Alpha → Prop)
    {reduceLeft reduceRight : Alpha → Alpha → Prop}
    (quasiCommutes : QuasiCommutesRightOverLeft reduceLeft reduceRight) :
    QuasiCommutesRightOverLeftOn klass reduceLeft reduceRight :=
  fun a b c _isMember rightStep leftStep =>
    quasiCommutes a b c rightStep leftStep

/-- Inner step of the relativized criterion: induction on the
right-accessibility of `a`, with BOTH the class membership and the
left induction hypothesis carried as antecedents — the right-descent
keeps the membership by right-closure, so every quasi-commutation
call happens at a class member. -/
theorem accUnionInnerOn {Alpha : Type} {klass : Alpha → Prop}
    {reduceLeft reduceRight : Alpha → Alpha → Prop}
    (quasiCommutesOn :
      QuasiCommutesRightOverLeftOn klass reduceLeft reduceRight)
    (rightPreservesClass : ∀ {a b : Alpha}, klass a →
      reduceRight a b → klass b)
    {a : Alpha}
    (accRight : Acc (fun later earlier => reduceRight earlier later) a) :
    klass a →
    (∀ predecessor, reduceLeft a predecessor →
        Acc (UnionSuccessor reduceLeft reduceRight) predecessor) →
      Acc (UnionSuccessor reduceLeft reduceRight) a := by
  induction accRight with
  | intro a _accRightInv innerIH =>
    intro isMember leftIH
    refine Acc.intro a (fun reduct unionStep => ?_)
    rcases unionStep with leftStep | rightStep
    · exact leftIH reduct leftStep
    · refine innerIH reduct rightStep
        (rightPreservesClass isMember rightStep)
        (fun deepPredecessor deepLeftStep => ?_)
      obtain ⟨detour, leftToDetour, detourStar⟩ :=
        quasiCommutesOn a reduct deepPredecessor isMember rightStep
          deepLeftStep
      exact accDownwardUnionStar (leftIH detour leftToDetour) detourStar

/-- ★ **The relativized Geser criterion**: on a class closed under
both relations, left SN at a member plus global right SN plus
quasi-commutation AT CLASS MEMBERS gives union SN at the member.
The typed union-SN engine: typing supplies the class closure (subject
reduction) and refutes the quasi-commutation counterexamples. -/
theorem accUnionOn {Alpha : Type} {klass : Alpha → Prop}
    {reduceLeft reduceRight : Alpha → Alpha → Prop}
    (rightStronglyNormalizing :
      ∀ x, Acc (fun later earlier => reduceRight earlier later) x)
    (quasiCommutesOn :
      QuasiCommutesRightOverLeftOn klass reduceLeft reduceRight)
    (leftPreservesClass : ∀ {a b : Alpha}, klass a →
      reduceLeft a b → klass b)
    (rightPreservesClass : ∀ {a b : Alpha}, klass a →
      reduceRight a b → klass b)
    {a : Alpha}
    (accLeft : Acc (fun later earlier => reduceLeft earlier later) a)
    (isMember : klass a) :
    Acc (UnionSuccessor reduceLeft reduceRight) a := by
  induction accLeft with
  | intro a _accLeftInv outerIH =>
    exact accUnionInnerOn quasiCommutesOn rightPreservesClass
      (rightStronglyNormalizing a) isMember
      (fun predecessor leftStep =>
        outerIH predecessor leftStep
          (leftPreservesClass isMember leftStep))

end FX1Poly.Core

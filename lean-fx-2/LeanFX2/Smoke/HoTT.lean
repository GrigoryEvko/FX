import LeanFX2.HoTT.Identity
import LeanFX2.HoTT.J
import LeanFX2.HoTT.Transport
import LeanFX2.HoTT.HIT.Eliminator
import LeanFX2.HoTT.HIT.PropTrunc
import LeanFX2.HoTT.HIT.Quot
import LeanFX2.HoTT.HIT.S1
import LeanFX2.Tools.DependencyAudit

/-! # Smoke/HoTT — Identity types, J, transport, HIT examples.

```lean
-- J on refl reduces to base
example (baseCase : Term ctx P (RawTerm.var ⟨0, _⟩)) :
    Step (Term.idJ baseCase (Term.refl ...)) baseCase :=
  Step.iotaIdJRefl baseCase

-- Transport along refl is identity
example (P : ...) (a : ...) (witness : ...) :
    transport P (refl a) witness = witness := by simp ...
```

## Dependencies

* `HoTT/Identity.lean`, `HoTT/J.lean`, `HoTT/Transport.lean`

## Implementation plan (Layer 14)

1. J on refl
2. transport along refl
3. Path composition + groupoid laws
4. S¹ via setoid encoding (small example)
-/

namespace LeanFX2.Smoke

/-- A discrete HIT specification has no path labels. -/
theorem hitSpec_discrete_noPath_smoke :
    ¬ (HoTT.HIT.HITSpec.discrete Unit).hasPathBetween () () :=
  HoTT.HIT.HITSpec.discrete_hasNoPath Unit () ()

/-- The indiscrete HIT setoid relates any two representatives. -/
theorem hitSetoid_indiscrete_relation_smoke :
    (HoTT.HIT.HITSetoid.indiscrete Unit).relation () () :=
  True.intro

/-- Constant HIT recursors compute by reflexive reduction. -/
theorem hitRecursor_constant_run_smoke :
    (HoTT.HIT.HITRecursor.constant
      (encodedHit := HoTT.HIT.HITSetoid.indiscrete Unit)
      Bool true).run () = true :=
  HoTT.HIT.HITRecursor.constant_run
    (encodedHit := HoTT.HIT.HITSetoid.indiscrete Unit)
    Bool true ()

/-- Propositional truncation relates any two introduced witnesses. -/
theorem propTrunc_squash_smoke :
    (HoTT.HIT.PropTrunc Unit).relation
      (HoTT.HIT.PropTrunc.intro ())
      (HoTT.HIT.PropTrunc.intro ()) :=
  HoTT.HIT.PropTrunc.squash
    (HoTT.HIT.PropTrunc.intro ())
    (HoTT.HIT.PropTrunc.intro ())

/-- Propositional truncation recursion computes on introduced values. -/
theorem propTrunc_rec_intro_smoke :
    (HoTT.HIT.PropTrunc.rec
      (sourceType := Unit)
      Bool
      (fun _ => true)
      (fun _ _ => rfl)).run
      (HoTT.HIT.PropTrunc.intro ()) =
      true :=
  HoTT.HIT.PropTrunc.rec_intro
    (sourceType := Unit)
    Bool
    (fun _ => true)
    (fun _ _ => rfl)
    ()

/-- The equality quotient presentation keeps equality as its relation. -/
theorem quotientHIT_equality_relation_smoke :
    (HoTT.HIT.QuotientHIT.equality Unit).relation () () :=
  rfl

/-- Quotient recursion computes on introduced representatives. -/
theorem quotientHIT_rec_intro_smoke :
    (HoTT.HIT.QuotientHIT.rec
      (sourceType := Unit)
      (relation := Eq)
      (isRefl := fun sourceValue => Eq.refl sourceValue)
      (isSymm := fun relationWitness => Eq.symm relationWitness)
      (isTrans := fun firstWitness secondWitness =>
        Eq.trans firstWitness secondWitness)
      Bool
      (fun _ => true)
      (fun relationWitness => by
        cases relationWitness
        rfl)).run
      (HoTT.HIT.QuotientHIT.intro ()) =
      true :=
  HoTT.HIT.QuotientHIT.rec_intro
    (sourceType := Unit)
    (relation := Eq)
    (isRefl := fun sourceValue => Eq.refl sourceValue)
    (isSymm := fun relationWitness => Eq.symm relationWitness)
    (isTrans := fun firstWitness secondWitness =>
      Eq.trans firstWitness secondWitness)
    Bool
    (fun _ => true)
    (fun relationWitness => by
      cases relationWitness
      rfl)
    ()

/-- The S1 spec contains the loop path from base to base. -/
theorem s1_loop_spec_smoke :
    HoTT.HIT.S1Spec.hasPathBetween
      HoTT.HIT.S1PointLabel.base
      HoTT.HIT.S1PointLabel.base :=
  HoTT.HIT.S1.loopSpec

/-- Setoid-level S1 recursion computes at base. -/
theorem s1_rec_base_smoke :
    (HoTT.HIT.S1.rec Bool true).run HoTT.HIT.S1.base = true :=
  HoTT.HIT.S1.rec_base Bool true

#assert_no_axioms LeanFX2.Smoke.hitSpec_discrete_noPath_smoke
#assert_no_axioms LeanFX2.Smoke.hitSetoid_indiscrete_relation_smoke
#assert_no_axioms LeanFX2.Smoke.hitRecursor_constant_run_smoke
#assert_no_axioms LeanFX2.Smoke.propTrunc_squash_smoke
#assert_no_axioms LeanFX2.Smoke.propTrunc_rec_intro_smoke
#assert_no_axioms LeanFX2.Smoke.quotientHIT_equality_relation_smoke
#assert_no_axioms LeanFX2.Smoke.quotientHIT_rec_intro_smoke
#assert_no_axioms LeanFX2.Smoke.s1_loop_spec_smoke
#assert_no_axioms LeanFX2.Smoke.s1_rec_base_smoke

end LeanFX2.Smoke

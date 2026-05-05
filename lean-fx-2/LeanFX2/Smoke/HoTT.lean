import LeanFX2.HoTT.Identity
import LeanFX2.HoTT.J
import LeanFX2.HoTT.Transport
import LeanFX2.HoTT.HIT.Eliminator
import LeanFX2.HoTT.HIT.PropTrunc
import LeanFX2.HoTT.HIT.SetTrunc
import LeanFX2.HoTT.HIT.Quot
import LeanFX2.HoTT.HIT.S1
import LeanFX2.HoTT.HIT.Suspension
import LeanFX2.HoTT.HIT.Pushout
import LeanFX2.HoTT.HIT.Coequalizer
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

/-- Constant dependent HIT inductors compute by reflexive reduction. -/
theorem hitInductor_constant_run_smoke :
    (HoTT.HIT.HITInductor.constant
      (encodedHit := HoTT.HIT.HITSetoid.indiscrete Unit)
      Bool true).run () = true :=
  HoTT.HIT.HITInductor.constant_run
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

/-- Propositional truncation relates distinct Bool witnesses through
the named squash relation. -/
theorem propTrunc_bool_squash_smoke :
    (HoTT.HIT.PropTrunc Bool).relation
      (HoTT.HIT.PropTrunc.intro false)
      (HoTT.HIT.PropTrunc.intro true) :=
  HoTT.HIT.PropTrunc.squash false true

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

/-- Propositional truncation recursion respects the squash path between
distinct Bool representatives when the eliminator is constant. -/
theorem propTrunc_bool_rec_squash_smoke :
    (HoTT.HIT.PropTrunc.rec
      (sourceType := Bool)
      Bool
      (fun _ => true)
      (fun _ _ => rfl)).run
      (HoTT.HIT.PropTrunc.intro false) =
      (HoTT.HIT.PropTrunc.rec
        (sourceType := Bool)
        Bool
        (fun _ => true)
        (fun _ _ => rfl)).run
        (HoTT.HIT.PropTrunc.intro true) :=
  HoTT.HIT.PropTrunc.rec_squash
    (sourceType := Bool)
    Bool
    (fun _ => true)
    (fun _ _ => rfl)
    false
    true

/-- Propositional truncation dependent induction computes on introduced
values. -/
theorem propTrunc_dependentInductor_intro_smoke :
    (HoTT.HIT.PropTrunc.dependentInductor
      (sourceType := Unit)
      (fun _ => Bool)
      (fun _ => true)
      (fun _ _ => HEq.rfl)).run
      (HoTT.HIT.PropTrunc.intro ()) =
      true :=
  HoTT.HIT.PropTrunc.dependentInductor_intro
    (sourceType := Unit)
    (fun _ => Bool)
    (fun _ => true)
    (fun _ _ => HEq.rfl)
    ()

/-- Set truncation relates equal introduced representatives. -/
theorem setTrunc_path_smoke :
    (HoTT.HIT.SetTrunc Unit).relation
      (HoTT.HIT.SetTrunc.intro ())
      (HoTT.HIT.SetTrunc.intro ()) :=
  HoTT.HIT.SetTrunc.path rfl

/-- Set truncation keeps distinct Bool representatives separate at the
current setoid layer; only reflexive representatives get a path. -/
theorem setTrunc_bool_reflPath_smoke :
    (HoTT.HIT.SetTrunc Bool).relation
      (HoTT.HIT.SetTrunc.intro false)
      (HoTT.HIT.SetTrunc.intro false) :=
  HoTT.HIT.SetTrunc.path rfl

/-- Set-truncation recursion computes on introduced representatives. -/
theorem setTrunc_rec_intro_smoke :
    (HoTT.HIT.SetTrunc.rec
      (sourceType := Unit)
      Bool
      (fun _ => true)).run
      (HoTT.HIT.SetTrunc.intro ()) =
      true :=
  HoTT.HIT.SetTrunc.rec_intro
    (sourceType := Unit)
    Bool
    (fun _ => true)
    ()

/-- Set-truncation dependent induction computes on introduced
representatives. -/
theorem setTrunc_dependentInductor_intro_smoke :
    (HoTT.HIT.SetTrunc.dependentInductor
      (sourceType := Unit)
      (fun _ => Bool)
      (fun _ => true)).run
      (HoTT.HIT.SetTrunc.intro ()) =
      true :=
  HoTT.HIT.SetTrunc.dependentInductor_intro
    (sourceType := Unit)
    (fun _ => Bool)
    (fun _ => true)
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

/-- Quotient dependent induction computes on introduced representatives. -/
theorem quotientHIT_dependentInductor_intro_smoke :
    (HoTT.HIT.QuotientHIT.dependentInductor
      (sourceType := Unit)
      (relation := Eq)
      (isRefl := fun sourceValue => Eq.refl sourceValue)
      (isSymm := fun relationWitness => Eq.symm relationWitness)
      (isTrans := fun firstWitness secondWitness =>
        Eq.trans firstWitness secondWitness)
      (fun _ => Bool)
      (fun _ => true)
      (fun relationWitness => by
        cases relationWitness
        exact HEq.rfl)).run
      (HoTT.HIT.QuotientHIT.intro ()) =
      true :=
  HoTT.HIT.QuotientHIT.dependentInductor_intro
    (sourceType := Unit)
    (relation := Eq)
    (isRefl := fun sourceValue => Eq.refl sourceValue)
    (isSymm := fun relationWitness => Eq.symm relationWitness)
    (isTrans := fun firstWitness secondWitness =>
      Eq.trans firstWitness secondWitness)
    (fun _ => Bool)
    (fun _ => true)
    (fun relationWitness => by
      cases relationWitness
      exact HEq.rfl)
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

/-- Setoid-level S1 dependent induction computes at base. -/
theorem s1_dependentInductor_base_smoke :
    (HoTT.HIT.S1.dependentInductor
      (fun _ => Bool)
      (fun _ => true)
      (fun _ _ => HEq.rfl)).run
      HoTT.HIT.S1.base = true :=
  HoTT.HIT.S1.dependentInductor_base
    (fun _ => Bool)
    (fun _ => true)
    (fun _ _ => HEq.rfl)

/-- Setoid-level S1 now has non-base winding representatives connected
to base. -/
theorem s1_forwardLoop_relation_smoke :
    HoTT.HIT.S1.setoid.relation
      HoTT.HIT.S1.base
      (HoTT.HIT.S1.forwardLoop 0) :=
  HoTT.HIT.S1.loopForward 0

/-- S1 dependent induction must respect distinct winding representatives. -/
theorem s1_dependentInductor_loopBetween_smoke :
    HEq
      ((HoTT.HIT.S1.dependentInductor
        (fun _ => Bool)
        (fun _ => true)
        (fun _ _ => HEq.rfl)).run HoTT.HIT.S1.base)
      ((HoTT.HIT.S1.dependentInductor
        (fun _ => Bool)
        (fun _ => true)
        (fun _ _ => HEq.rfl)).run (HoTT.HIT.S1.forwardLoop 0)) :=
  HoTT.HIT.S1.dependentInductor_loopBetween
    (fun _ => Bool)
    (fun _ => true)
    (fun _ _ => HEq.rfl)
    HoTT.HIT.S1.base
    (HoTT.HIT.S1.forwardLoop 0)

/-- A suspension meridian relates north and south when a source witness exists. -/
theorem suspension_meridian_smoke :
    (HoTT.HIT.Suspension.setoid Unit).relation
      (HoTT.HIT.Suspension.north (sourceType := Unit))
      (HoTT.HIT.Suspension.south (sourceType := Unit)) :=
  HoTT.HIT.Suspension.meridian ()

/-- Suspension recursion computes at north. -/
theorem suspension_rec_north_smoke :
    (HoTT.HIT.Suspension.rec
      (sourceType := Unit)
      Bool true true
      (fun _ => rfl)).run
      (HoTT.HIT.Suspension.north (sourceType := Unit)) =
      true :=
  HoTT.HIT.Suspension.rec_north
    (sourceType := Unit)
    Bool true true
    (fun _ => rfl)

/-- Suspension dependent induction computes at north. -/
theorem suspension_dependentInductor_north_smoke :
    (HoTT.HIT.Suspension.dependentInductor
      (sourceType := Unit)
      (fun _ => Bool)
      true true
      (fun _ => HEq.rfl)).run
      (HoTT.HIT.Suspension.north (sourceType := Unit)) =
      true :=
  HoTT.HIT.Suspension.dependentInductor_north
    (sourceType := Unit)
    (fun _ => Bool)
    true true
    (fun _ => HEq.rfl)

/-- A pushout glue witness relates the left and right images. -/
theorem pushout_glue_smoke :
    (HoTT.HIT.PushoutHIT
      Unit Unit Unit
      (fun sourceValue => sourceValue)
      (fun sourceValue => sourceValue)
      (fun _ _ => True)
      (fun _ => True.intro)
      (fun _ => True.intro)
      (fun _ _ => True.intro)
      (fun _ => True.intro)).relation
      (HoTT.HIT.PushoutHIT.left ())
      (HoTT.HIT.PushoutHIT.right ()) :=
  HoTT.HIT.PushoutHIT.glue ()

/-- Pushout recursion computes on left representatives. -/
theorem pushout_rec_left_smoke :
    (HoTT.HIT.PushoutHIT.rec
      (sourceType := Unit)
      (leftMap := fun sourceValue => sourceValue)
      (rightMap := fun sourceValue => sourceValue)
      (relation := fun _ _ => True)
      (isRefl := fun _ => True.intro)
      (isSymm := fun _ => True.intro)
      (isTrans := fun _ _ => True.intro)
      (glueRespects := fun _ => True.intro)
      Bool
      (fun _ => true)
      (fun _ => true)
      (fun {leftValue} {rightValue} _ => by
        cases leftValue <;> cases rightValue <;> rfl)).run
      (Sum.inl ()) =
      true :=
  HoTT.HIT.PushoutHIT.rec_left
    (sourceType := Unit)
    (leftMap := fun sourceValue => sourceValue)
    (rightMap := fun sourceValue => sourceValue)
    (relation := fun _ _ => True)
    (isRefl := fun _ => True.intro)
    (isSymm := fun _ => True.intro)
    (isTrans := fun _ _ => True.intro)
    (glueRespects := fun _ => True.intro)
    Bool
    (fun _ => true)
    (fun _ => true)
    (fun {leftValue} {rightValue} _ => by
      cases leftValue <;> cases rightValue <;> rfl)
    ()

/-- Pushout dependent induction computes on left representatives. -/
theorem pushout_dependentInductor_left_smoke :
    (HoTT.HIT.PushoutHIT.dependentInductor
      (sourceType := Unit)
      (leftMap := fun sourceValue => sourceValue)
      (rightMap := fun sourceValue => sourceValue)
      (relation := fun _ _ => True)
      (isRefl := fun _ => True.intro)
      (isSymm := fun _ => True.intro)
      (isTrans := fun _ _ => True.intro)
      (glueRespects := fun _ => True.intro)
      (fun _ => Bool)
      (fun _ => true)
      (fun _ => true)
      (fun {leftValue} {rightValue} _ => by
        cases leftValue <;> cases rightValue <;> exact HEq.rfl)).run
      (Sum.inl ()) =
      true :=
  HoTT.HIT.PushoutHIT.dependentInductor_left
    (sourceType := Unit)
    (leftMap := fun sourceValue => sourceValue)
    (rightMap := fun sourceValue => sourceValue)
    (relation := fun _ _ => True)
    (isRefl := fun _ => True.intro)
    (isSymm := fun _ => True.intro)
    (isTrans := fun _ _ => True.intro)
    (glueRespects := fun _ => True.intro)
    (fun _ => Bool)
    (fun _ => true)
    (fun _ => true)
    (fun {leftValue} {rightValue} _ => by
      cases leftValue <;> cases rightValue <;> exact HEq.rfl)
    ()

/-- A coequalizer path witness relates the two map images. -/
theorem coequalizer_equalize_smoke :
    (HoTT.HIT.CoequalizerHIT
      Unit Unit
      (fun sourceValue => sourceValue)
      (fun sourceValue => sourceValue)
      (fun _ _ => True)
      (fun _ => True.intro)
      (fun _ => True.intro)
      (fun _ _ => True.intro)
      (fun _ => True.intro)).relation
      (HoTT.HIT.CoequalizerHIT.point ())
      (HoTT.HIT.CoequalizerHIT.point ()) :=
  HoTT.HIT.CoequalizerHIT.equalize ()

/-- Coequalizer recursion computes on point representatives. -/
theorem coequalizer_rec_point_smoke :
    (HoTT.HIT.CoequalizerHIT.rec
      (sourceType := Unit)
      (leftMap := fun sourceValue => sourceValue)
      (rightMap := fun sourceValue => sourceValue)
      (relation := fun _ _ => True)
      (isRefl := fun _ => True.intro)
      (isSymm := fun _ => True.intro)
      (isTrans := fun _ _ => True.intro)
      (equalizeRespects := fun _ => True.intro)
      Bool
      (fun _ => true)
      (fun _ => rfl)).run
      (HoTT.HIT.CoequalizerHIT.point ()) =
      true :=
  HoTT.HIT.CoequalizerHIT.rec_point
    (sourceType := Unit)
    (leftMap := fun sourceValue => sourceValue)
    (rightMap := fun sourceValue => sourceValue)
    (relation := fun _ _ => True)
    (isRefl := fun _ => True.intro)
    (isSymm := fun _ => True.intro)
    (isTrans := fun _ _ => True.intro)
    (equalizeRespects := fun _ => True.intro)
    Bool
    (fun _ => true)
    (fun _ => rfl)
    ()

/-- Coequalizer dependent induction computes on point representatives. -/
theorem coequalizer_dependentInductor_point_smoke :
    (HoTT.HIT.CoequalizerHIT.dependentInductor
      (sourceType := Unit)
      (leftMap := fun sourceValue => sourceValue)
      (rightMap := fun sourceValue => sourceValue)
      (relation := fun _ _ => True)
      (isRefl := fun _ => True.intro)
      (isSymm := fun _ => True.intro)
      (isTrans := fun _ _ => True.intro)
      (equalizeRespects := fun _ => True.intro)
      (fun _ => Bool)
      (fun _ => true)
      (fun _ => HEq.rfl)).run
      (HoTT.HIT.CoequalizerHIT.point ()) =
      true :=
  HoTT.HIT.CoequalizerHIT.dependentInductor_point
    (sourceType := Unit)
    (leftMap := fun sourceValue => sourceValue)
    (rightMap := fun sourceValue => sourceValue)
    (relation := fun _ _ => True)
    (isRefl := fun _ => True.intro)
    (isSymm := fun _ => True.intro)
    (isTrans := fun _ _ => True.intro)
    (equalizeRespects := fun _ => True.intro)
    (fun _ => Bool)
    (fun _ => true)
    (fun _ => HEq.rfl)
    ()

#assert_no_axioms LeanFX2.Smoke.hitSpec_discrete_noPath_smoke
#assert_no_axioms LeanFX2.Smoke.hitSetoid_indiscrete_relation_smoke
#assert_no_axioms LeanFX2.Smoke.hitRecursor_constant_run_smoke
#assert_no_axioms LeanFX2.Smoke.hitInductor_constant_run_smoke
#assert_no_axioms LeanFX2.Smoke.propTrunc_squash_smoke
#assert_no_axioms LeanFX2.Smoke.propTrunc_bool_squash_smoke
#assert_no_axioms LeanFX2.Smoke.propTrunc_rec_intro_smoke
#assert_no_axioms LeanFX2.Smoke.propTrunc_bool_rec_squash_smoke
#assert_no_axioms LeanFX2.Smoke.propTrunc_dependentInductor_intro_smoke
#assert_no_axioms LeanFX2.Smoke.setTrunc_path_smoke
#assert_no_axioms LeanFX2.Smoke.setTrunc_bool_reflPath_smoke
#assert_no_axioms LeanFX2.Smoke.setTrunc_rec_intro_smoke
#assert_no_axioms LeanFX2.Smoke.setTrunc_dependentInductor_intro_smoke
#assert_no_axioms LeanFX2.Smoke.quotientHIT_equality_relation_smoke
#assert_no_axioms LeanFX2.Smoke.quotientHIT_rec_intro_smoke
#assert_no_axioms LeanFX2.Smoke.quotientHIT_dependentInductor_intro_smoke
#assert_no_axioms LeanFX2.Smoke.s1_loop_spec_smoke
#assert_no_axioms LeanFX2.Smoke.s1_rec_base_smoke
#assert_no_axioms LeanFX2.Smoke.s1_dependentInductor_base_smoke
#assert_no_axioms LeanFX2.Smoke.s1_forwardLoop_relation_smoke
#assert_no_axioms LeanFX2.Smoke.s1_dependentInductor_loopBetween_smoke
#assert_no_axioms LeanFX2.Smoke.suspension_meridian_smoke
#assert_no_axioms LeanFX2.Smoke.suspension_rec_north_smoke
#assert_no_axioms LeanFX2.Smoke.suspension_dependentInductor_north_smoke
#assert_no_axioms LeanFX2.Smoke.pushout_glue_smoke
#assert_no_axioms LeanFX2.Smoke.pushout_rec_left_smoke
#assert_no_axioms LeanFX2.Smoke.pushout_dependentInductor_left_smoke
#assert_no_axioms LeanFX2.Smoke.coequalizer_equalize_smoke
#assert_no_axioms LeanFX2.Smoke.coequalizer_rec_point_smoke
#assert_no_axioms LeanFX2.Smoke.coequalizer_dependentInductor_point_smoke

end LeanFX2.Smoke

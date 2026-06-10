import FX1Poly.Typed.TypedNbeNormalizer

/-! # FX1Poly/Typed/TypedNbeConvDecision
   — ★ #364: the typed NbE conversion check — sound everywhere, sound AND complete at unit

The #364 artifact over the composed typed NbE normalizer (#480 eval ∘ #481 quote): a computable
normalize-and-compare CHECK for the full typed judgmental equality `DefEqUnitEtaCong`
(β + ι + η + type-directed unit-η + congruence), with its honest 0/0 ledger:

  * **`checkNbeEqual`** — compute both NbE normal forms, compare by the kernel's decidable
    syntactic equality.  Executable; keyed on the typing derivations (the termination and
    classifier data ride along).
  * **Soundness, unconditional** (`checkNbeEqual_sound`): a passing check certifies
    `DefEqUnitEtaCong` — `ofNbeEqual` behind `of_decide_eq_true`.
  * **Completeness AT THE UNIT CLASSIFIER, total** (`nbeComplete_atUnit` /
    `checkNbeEqual_iff_atUnit`): the readback is CONSTANT at `unitTypeCell` — every NbE form at
    positive fuel is `unitCell`, symbolically (`rfl`!), so any two unit-typed subjects check
    equal.  Combined with soundness this is a genuine 0-false-positive / 0-false-negative cell:
    `checkNbeEqual = true ↔ DefEqUnitEtaCong`, decidably (`decidableAtUnit`).

## The honest completeness ledger (per-fragment, per the #484 discipline)

  * β/ι leg: COMPLETE — eval computes THE unique normal form (`conv_iff_normalForm_eq`), so
    `Conv`-related subjects always check equal after eval.
  * unit-η leg: COMPLETE at the unit classifier (this module — the readback constancy).
  * η leg at Π and the congruent closure: completeness holds on every machine-checked boundary
    witness (the #481 campaign's ten verdicts — η pair, mixed η+unit, spines, annotations, all
    decided through this one procedure) and is UNPROVEN in general — the joint
    Cong-completeness statement is the O-NORM research item, not claimed here.

## Zero-axiom verification

The check is `decide` over the kernel's manual `DecidableEq RawTerm`; soundness composes
`of_decide_eq_true` with `ofNbeEqual`; unit constancy is `rfl` (the readback's unit arm fires
on a SYMBOLIC subject); the unit decidability is `isTrue` of the `unitEta` axiom-free witness.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The typed NbE conversion check (#364)**: compute both NbE normal forms and compare
syntactically.  Sound everywhere (below); complete at the unit classifier (below) and on every
machine-checked #481 boundary pair. -/
def HasTypeDescPi.checkNbeEqual {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier leftTerm rightTerm : RawTerm scope}
    (leftFuel rightFuel : Nat)
    (contextWellFormed : WfContextDesc context)
    (leftTyped : HasTypeDescPi profile context leftTerm classifier)
    (rightTyped : HasTypeDescPi profile context rightTerm classifier) : Bool :=
  decide (HasTypeDescPi.nbeNormalForm leftFuel contextWellFormed leftTyped
    = HasTypeDescPi.nbeNormalForm rightFuel contextWellFormed rightTyped)

/-- **★ The check is sound, unconditionally**: a passing check certifies the full typed
judgmental equality. -/
theorem HasTypeDescPi.checkNbeEqual_sound {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier leftTerm rightTerm : RawTerm scope}
    {leftFuel rightFuel : Nat}
    {contextWellFormed : WfContextDesc context}
    {leftTyped : HasTypeDescPi profile context leftTerm classifier}
    {rightTyped : HasTypeDescPi profile context rightTerm classifier}
    {classifierLevel : LevelExpr} {classifierFlag : UniverseFlag}
    (classifierTyped : HasTypeDesc profile context classifier
      (universeCodeCell classifierLevel classifierFlag))
    (checkPasses : HasTypeDescPi.checkNbeEqual leftFuel rightFuel
      contextWellFormed leftTyped rightTyped = true) :
    DefEqUnitEtaCong profile context leftTerm rightTerm :=
  DefEqUnitEtaCong.ofNbeEqual contextWellFormed leftTyped rightTyped classifierTyped
    (of_decide_eq_true checkPasses)

/-- **The readback is CONSTANT at the unit classifier** — for a SYMBOLIC subject, by `rfl`:
the unit arm fires before any subject inspection. -/
theorem readbackAtClassifier_constantAtUnit {profile : PolyProfile} (fuel : Nat) {scope : Nat}
    (context : TypingContext profile scope) (term : RawTerm scope) :
    readbackAtClassifier (fuel + 1) context unitTypeCell term = unitCell := rfl

/-- **The NbE form of EVERY unit-typed subject is `unitCell`** at positive fuel — the readback
constancy composed through eval, still `rfl` (the eval output stays symbolic). -/
theorem HasTypeDescPi.nbeNormalForm_constantAtUnit {profile : PolyProfile}
    (fuel : Nat) {scope : Nat} {context : TypingContext profile scope}
    {subject : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject unitTypeCell) :
    HasTypeDescPi.nbeNormalForm (fuel + 1) contextWellFormed typed = unitCell := rfl

/-- **★ NbE completeness at the unit classifier, TOTAL**: any two unit-typed subjects have
EQUAL NbE forms at positive fuel — both are `unitCell`. -/
theorem HasTypeDescPi.nbeComplete_atUnit {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {leftTerm rightTerm : RawTerm scope}
    (leftFuel rightFuel : Nat)
    (contextWellFormed : WfContextDesc context)
    (leftTyped : HasTypeDescPi profile context leftTerm unitTypeCell)
    (rightTyped : HasTypeDescPi profile context rightTerm unitTypeCell) :
    HasTypeDescPi.nbeNormalForm (leftFuel + 1) contextWellFormed leftTyped
      = HasTypeDescPi.nbeNormalForm (rightFuel + 1) contextWellFormed rightTyped :=
  (HasTypeDescPi.nbeNormalForm_constantAtUnit leftFuel contextWellFormed leftTyped).trans
    (HasTypeDescPi.nbeNormalForm_constantAtUnit rightFuel contextWellFormed
      rightTyped).symm

/-- **★ The 0/0 cell — the check is sound AND complete at the unit classifier**: at positive
fuel, `checkNbeEqual = true ↔ DefEqUnitEtaCong`, for every pair of unit-typed subjects in a wf
context. -/
theorem HasTypeDescPi.checkNbeEqual_iff_atUnit {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {leftTerm rightTerm : RawTerm scope}
    (leftFuel rightFuel : Nat)
    (contextWellFormed : WfContextDesc context)
    (leftTyped : HasTypeDescPi profile context leftTerm unitTypeCell)
    (rightTyped : HasTypeDescPi profile context rightTerm unitTypeCell) :
    HasTypeDescPi.checkNbeEqual (leftFuel + 1) (rightFuel + 1)
        contextWellFormed leftTyped rightTyped = true
      ↔ DefEqUnitEtaCong profile context leftTerm rightTerm :=
  ⟨HasTypeDescPi.checkNbeEqual_sound (unitTypeCellFormationTyped context),
   fun _ => decide_eq_true
     (HasTypeDescPi.nbeComplete_atUnit leftFuel rightFuel contextWellFormed
       leftTyped rightTyped)⟩

/-- **★ Decidable typed judgmental equality at the unit classifier** — the relation is TOTAL
there (`unitEta`), so the decision is `isTrue`; the NbE check coincides
(`checkNbeEqual_iff_atUnit`). -/
def DefEqUnitEtaCong.decidableAtUnit {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {leftTerm rightTerm : RawTerm scope}
    (leftTyped : HasTypeDescPi profile context leftTerm unitTypeCell)
    (rightTyped : HasTypeDescPi profile context rightTerm unitTypeCell) :
    Decidable (DefEqUnitEtaCong profile context leftTerm rightTerm) :=
  isTrue (.ofDefEq (.unitEta (Or.inr leftTyped) (Or.inr rightTyped)))

end FX1Poly.Typed

import LeanFX2.Reducibility.Predicate

/-! # LeanFX2.Reducibility.Classifier — SN-direct Reducible arms

Some Ty constructors specialize `Reducible` to plain strong
normalization (no closure beyond SN).  This module classifies
those arms and ships the supporting infrastructure:

* `Reducible.IsSNDirect` — Prop predicate over `Ty level scope`
  marking the 9 admitting types (`unit`, `bool`, `nat`, `empty`,
  `interval`, `universe`, `session`, `effect`, `modal`).  Full
  enumeration of all 25 Ty ctors keeps the match propext-clean
  (per `feedback_lean_match_propext_recipe.md` recipe 1:
  "wildcard `_ =>` always leaks propext").
* `Reducible.IsSNDirect.rename` — typed renaming preserves the
  SN-direct property because every admitting outer ctor survives
  `Ty.rename` unchanged.
* `Reducible.of_isStronglyNormalizing_when_SNDirect` — on
  SN-direct arms, strong normalization is full reducibility.
* K12.20.U4 SN-direct codomain recovery — companions for
  `Reducible.IsSNDirect` consumers in the stable-fundamental
  cascade.

The classifier intentionally excludes `Ty.tyVar` (after
substitution it can become any type, breaking the invariant at
the fundamental-call boundary).

## Root status

Layer 3 metatheory leaf.  Used by `Reducibility.StableBase`,
`Reducibility.NeutralSN*`, and the entire K12.20.U4 cascade. -/

namespace LeanFX2


/-! ## K12.20.U4 SN-direct codomain recovery

The lambda SN-codomain route needs a codomain-specific bridge from
strong normalization back to `Reducible`.  This bridge is valid exactly
for the candidate arms whose `Reducible` body is definitionally plain
`Term.isStronglyNormalizing`: the closed leaves plus the current Layer-1
session/effect/modal fallback arms.  Function-like and projection-like
compound candidates are deliberately absent because they require their
own closure fields, not just SN.
-/

/-- Unit reducibility is exactly strong normalization. -/
theorem Reducible.unit_of_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {raw : RawTerm scope}
    {term : Term context Ty.unit raw}
    (termIsSN : Term.isStronglyNormalizing term) :
    Reducible Ty.unit term :=
  termIsSN

/-- Boolean reducibility is exactly strong normalization. -/
theorem Reducible.bool_of_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {raw : RawTerm scope}
    {term : Term context Ty.bool raw}
    (termIsSN : Term.isStronglyNormalizing term) :
    Reducible Ty.bool term :=
  termIsSN

/-- Natural-number reducibility is exactly strong normalization. -/
theorem Reducible.nat_of_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {raw : RawTerm scope}
    {term : Term context Ty.nat raw}
    (termIsSN : Term.isStronglyNormalizing term) :
    Reducible Ty.nat term :=
  termIsSN

/-- Empty-type reducibility is exactly strong normalization. -/
theorem Reducible.empty_of_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {raw : RawTerm scope}
    {term : Term context Ty.empty raw}
    (termIsSN : Term.isStronglyNormalizing term) :
    Reducible Ty.empty term :=
  termIsSN

/-- Interval reducibility is exactly strong normalization. -/
theorem Reducible.interval_of_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {raw : RawTerm scope}
    {term : Term context Ty.interval raw}
    (termIsSN : Term.isStronglyNormalizing term) :
    Reducible Ty.interval term :=
  termIsSN

/-- Universe-code reducibility is exactly strong normalization. -/
theorem Reducible.universe_of_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {universeLevel : UniverseLevel}
    {levelLe : universeLevel.toNat + 1 ≤ level}
    {raw : RawTerm scope}
    {term : Term context (Ty.universe universeLevel levelLe) raw}
    (termIsSN : Term.isStronglyNormalizing term) :
    Reducible (Ty.universe universeLevel levelLe) term :=
  termIsSN

/-- Type-variable fallback reducibility is exactly strong normalization. -/
theorem Reducible.tyVar_of_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {position : Fin scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.tyVar position) raw}
    (termIsSN : Term.isStronglyNormalizing term) :
    Reducible (Ty.tyVar position) term :=
  termIsSN

/-- Layer-1 session reducibility is exactly strong normalization. -/
theorem Reducible.session_of_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.session protocolStep) raw}
    (termIsSN : Term.isStronglyNormalizing term) :
    Reducible (Ty.session protocolStep) term :=
  termIsSN

/-- Layer-1 effect reducibility is exactly strong normalization. -/
theorem Reducible.effect_of_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.effect carrierType effectTag) raw}
    (termIsSN : Term.isStronglyNormalizing term) :
    Reducible (Ty.effect carrierType effectTag) term :=
  termIsSN

/-- Layer-1 modal reducibility is exactly strong normalization. -/
theorem Reducible.modal_of_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {modalityTag : Nat}
    {carrierType : Ty level scope}
    {raw : RawTerm scope}
    {term : Term context (Ty.modal modalityTag carrierType) raw}
    (termIsSN : Term.isStronglyNormalizing term) :
    Reducible (Ty.modal modalityTag carrierType) term :=
  termIsSN

/-! ## K12.20.U4 SN-direct reducibility classifier

The stable fundamental cases for type-preserving wrappers (`subsume`,
`modIntro`, `modElim`) should not be sliced once per closed type.
They only need the invariant that the current `Reducible` arm is
definitionally just `Term.isStronglyNormalizing`.  `Ty.tyVar` is
intentionally excluded: after substitution it can become any type, so
it does not preserve this invariant at the fundamental-call boundary.
-/

/-- Types whose current `Reducible` candidate is plain strong
normalization.

The match enumerates all 25 Ty constructors explicitly because the
wildcard form leaks propext through the auto-generated equation
lemmas (see `feedback_lean_match_propext_recipe.md` recipe 1:
"wildcard `_ =>` always leaks propext"). The admitting nine return
`True`; the remaining sixteen return `False` explicitly. -/
def Reducible.IsSNDirect {level scope : Nat} : Ty level scope → Prop
  | Ty.unit => True
  | Ty.bool => True
  | Ty.nat => True
  | Ty.empty => True
  | Ty.interval => True
  | Ty.universe _ _ => True
  | Ty.session _ => True
  | Ty.effect _ _ => True
  | Ty.modal _ _ => True
  | Ty.arrow _ _ => False
  | Ty.piTy _ _ => False
  | Ty.sigmaTy _ _ => False
  | Ty.tyVar _ => False
  | Ty.id _ _ _ => False
  | Ty.listType _ => False
  | Ty.optionType _ => False
  | Ty.eitherType _ _ => False
  | Ty.path _ _ _ => False
  | Ty.glue _ _ => False
  | Ty.oeq _ _ _ => False
  | Ty.idStrict _ _ _ => False
  | Ty.equiv _ _ => False
  | Ty.refine _ _ => False
  | Ty.record _ => False
  | Ty.codata _ _ => False

/-- SN-directness is preserved by typed renaming because every admitted
arm keeps the same outer type constructor under `Ty.rename`. -/
theorem Reducible.IsSNDirect.rename
    {level sourceScope targetScope : Nat}
    {sourceType : Ty level sourceScope}
    {rho : RawRenaming sourceScope targetScope}
    (sourceTypeIsSNDirect : Reducible.IsSNDirect sourceType) :
    Reducible.IsSNDirect (sourceType.rename rho) := by
  cases sourceType <;>
    first
    | exact trivial
    | change False at sourceTypeIsSNDirect
      cases sourceTypeIsSNDirect

/-- On SN-direct candidate arms, strong normalization recovers the full
`Reducible` witness. -/
theorem Reducible.of_isStronglyNormalizing_when_SNDirect
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType : Ty level scope}
    {raw : RawTerm scope}
    {term : Term context sourceType raw}
    (sourceTypeIsSNDirect : Reducible.IsSNDirect sourceType)
    (termIsSN : Term.isStronglyNormalizing term) :
    Reducible sourceType term := by
  cases sourceType <;>
    first
    | exact termIsSN
    | change False at sourceTypeIsSNDirect
      cases sourceTypeIsSNDirect


end LeanFX2

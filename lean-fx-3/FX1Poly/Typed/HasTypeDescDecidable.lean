import FX1Poly.Typed.HasTypeDescSound
import FX1Poly.Typed.HasTypeDecidable

/-! # FX1Poly/Typed/HasTypeDescDecidable — the description engine is DECIDABLE
    (the P11 "0-FN" payoff of the `HasTypeDesc ⟺ HasType` equivalence)

The moonshot description-driven generic engine `HasTypeDesc` (§11.8.5 / §5.2: the
Natural-Model display map as a data-driven cascade-free `gen` arm) is proven
EQUIVALENT to the trusted bespoke `HasType` on the formation fragment, both
directions:
* `HasType.toHasTypeDesc` — completeness (the generic engine is at least as strong);
* `HasTypeDesc.toHasType` — soundness (it derives nothing the trusted kernel wouldn't).

Decidability TRANSPORTS across that equivalence.  The bespoke engine already has a
decision procedure (`HasType.decidableOfWellFormed`, #461/#302); this file lifts it
to the description engine in a few lines — `Decidable (HasTypeDesc Γ t T)` — the
generic engine's P11 "0 false negatives" property (every typing question is
decidable), WITHOUT redoing the decider from scratch.  This is the concrete payoff
of the equivalence: the cascade-free description-driven `gen` arm is not just sound
+ complete but a genuine, decidable typechecker on the native pi/sigma-formation HasType core.

## Why hand-built, not `decidable_of_iff`

`decidable_of_iff` transports a `Decidable` along an `Iff`, but routing through an
`Iff` (a `Prop`-level bi-implication) risks pulling `propext` in some elaborations.
The decision here is built DIRECTLY by `match`ing the bespoke decision and mapping
each branch through the appropriate equivalence direction: `isTrue` via completeness
(`toHasTypeDesc`), `isFalse` via soundness (`toHasType`, supplying the
contradiction).  No `Iff`, no `propext`.

## Zero-axiom verification

A `match` on the `HasType.decidableOfWellFormed` decision + the two
zero-axiom equivalence maps.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, `omega`.  Audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The description engine is decidable: `Decidable (HasTypeDesc Γ subject classifier)`,
lifted from the bespoke `HasType.decidableOfWellFormed` through the proven
`HasTypeDesc ⟺ HasType` equivalence.  `isTrue` maps the bespoke derivation forward
via completeness (`HasType.toHasTypeDesc`); `isFalse` refutes by mapping a
hypothetical `HasTypeDesc` derivation back via soundness (`HasTypeDesc.toHasType`)
into the bespoke contradiction.  The P11 "0-FN" deliverable for the cascade-free
engine. -/
def HasTypeDesc.decidableOfWellFormed {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (wellFormed : WfContext context)
    (subject classifier : RawTerm scope) :
    Decidable (HasTypeDesc profile context subject classifier) :=
  match HasType.decidableOfWellFormed wellFormed subject classifier with
  | isTrue bespokeDerivation => isTrue (HasType.toHasTypeDesc bespokeDerivation)
  | isFalse bespokeRefutation =>
      isFalse (fun descDerivation =>
        bespokeRefutation (HasTypeDesc.toHasType descDerivation))

end FX1Poly.Typed

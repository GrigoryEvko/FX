import FX1Poly.Typed.DenoteKeyedReducibleEnv
import FX1Poly.Typed.DenoteKeyedFundamentalMotive
import FX1Poly.Typed.HasTypeSubstitution
import FX1Poly.Typed.HasTypeDescPi

/-! # FX1Poly/Typed/DenoteKeyedCodomainMemberWiring
    — the SN-040-FREE codomain-member wiring for the genFormationPi arms (SN-D5d; toward SN-043/#750)

The genFormationPi Σ/Π fundamental-theorem arms (`DenoteKeyedGenFormationSigmaArm.lean` /
`DenoteKeyedGenFormationPiArm.lean`) carry the codomain's under-binder strong normalization as a deferred
premise.  The earlier ledger analysis (ticks #18/#19) claimed that PRODUCING that codomain SN from the
telescope IH needs the denote reducibility relation's renaming-closure (SN-040), which is Kripke-obstructed.

**That claim was WRONG, and this file corrects it.**  The codomain's universe membership is needed at the
substitution `RawTermSubst.cons headTerm substitution` — variable 0 mapped to a domain member `headTerm`, the
ORIGINAL `substitution` kept as the tail.  `ReducibleEnvAtDenote.cons` extends the environment with EXACTLY this
shape (`DenoteKeyedReducibleEnv.lean:84` — the `position+1` case applies `tailReducible` to the UN-RENAMED
`substitution`-image, never a `rename shift (...)`).  So the codomain member at `cons headTerm substitution`
comes straight from the codomain IH applied to `ReducibleEnvAtDenote.cons envReducible headMember` — NO
renaming-closure, NO SN-040.  The binder-discharge uses `cons` (prepend), not `lift` (weaken-and-rename), and
that is the whole difference.

CONSEQUENCE for the residual: with SN-040 off the table, the genFormationPi codomain SN reduces (via the shipped
`openBodyOfConsSubst` + CR1 over this membership) to producing the domain member `headTerm` — for which the only
universal choice is `var 0` (a neutral, in every reducibility candidate by `containsVariable`), requiring the
domain reducible AT THE AMBIENT LEVEL.  That ambient-level reducibility routes through the A2 bridge
`universeMemberReducibleAtLevel`, which itself consumes the #752 `piArm`.  So the genFormationPi residual
UNIFIES to #752 alone (the Π output-level threshold) — there is no separate SN-040 Kripke wall.

## The declaration

`codomainMemberFromIH` — from the codomain IH (its `FundamentalConclusionAtDenote` in the cons-extended
context), a denote-reducible environment for `context` at `substitution`, and a domain member `headTerm`, the
codomain is a denote-reducible member of its universe code at `cons headTerm substitution`.  This is exactly the
`codomainMemberAtFreshVar` hypothesis the Σ assembly `sigmaFormationFromChildMembersAtDenote` consumes — now
PRODUCED from the IH with no SN-040.  General over the member `headTerm` (the caller picks `var 0`).

## Zero-axiom verification

`codomainIH` applied to `RawTermSubst.cons headTerm substitution` and `ReducibleEnvAtDenote.cons envReducible
headMember`, then `rwa [subst_universeCodeCell]` to cancel the substitution on the closed universe classifier.
No induction, no `funext`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or
`omega` (checked: depends on no axioms).  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The SN-040-free codomain-member wiring.**  The codomain's universe membership at the cons-extended
substitution `cons headTerm substitution` comes directly from the codomain IH (`FundamentalConclusionAtDenote`
in the cons-extended context) applied to `ReducibleEnvAtDenote.cons envReducible headMember`.  The env extension
uses `cons` (un-renamed tail), so NO renaming-closure (SN-040) is needed — only a domain member `headTerm`.
This produces the `codomainMemberAtFreshVar` hypothesis the Σ assembly consumes. -/
theorem codomainMemberFromIH {profile : PolyProfile} {scope targetScope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    {domain : RawTerm scope} {codomain : RawTerm (scope + 1)} (codomainLevel : LevelExpr)
    (flag : UniverseFlag) (substitution : RawTermSubst scope targetScope)
    (headTerm : RawTerm targetScope)
    (envReducible : ReducibleEnvAtDenote env level context substitution)
    (headMember : IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution domain) headTerm)
    (codomainIH : FundamentalConclusionAtDenote env level (context.cons domain) codomain
      (universeCodeCell codomainLevel flag)) :
    IsReducibleMemberAtDenote env level (universeCodeCell codomainLevel flag)
      (RawTerm.subst (RawTermSubst.cons headTerm substitution) codomain) := by
  have member := codomainIH (RawTermSubst.cons headTerm substitution)
    (ReducibleEnvAtDenote.cons envReducible headMember)
  rwa [subst_universeCodeCell] at member

end FX1Poly.Typed

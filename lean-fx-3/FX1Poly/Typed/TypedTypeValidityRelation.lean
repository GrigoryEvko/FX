import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Core.KripkeCandidateRenameClosure
import FX1Poly.Core.NeutralTerm

/-! # FX1Poly/Typed/TypedTypeValidityRelation
    — the typed type-validity logical relation (the open-context model object for GrownCtxConv-5 #842)

## What this file is

The single open release blocker is the residual `ConvContextPreservesPiValidity` (#1092): a `Π`-type code's
GROWN validity (`IsTypeDescPi`) is stable under pointwise context conversion.  Both GrownCtxConv-5 (grown
context-conversion, #842) and SRD-2 (master subject reduction, #845) reduce to it (#1098).  Its
genuinely-open core (#1099) is the type-level NEUTRAL applications `(var f) (var a)` typed via `piElim` at a
universe; discharging it needs an OPEN-CONTEXT typed logical relation pairing a reducibility candidate with a
typing witness (the bounded reducibility model is closed-substitution-based and structurally unfit).

Firings 13-18 banked the full Kripke/model SUBSTRATE — `Step.reflectRename` (#1104), the Kripke arrow CR
bundle CR1/CR2/CR3 (#1105), semantic neutral-type context-freeness (#1106), and the SN Kripke candidate
`snKripkeCand` (#1108) — but the RELATION OBJECT itself was undefined.  **This file defines it**: the typed
type-validity logical relation `TypedTypeValidity`, the Kripke-model interpretation of a valid type code,
PAIRING (a) a reducibility candidate (the `KripkeCand` semantic interpretation) with (b) the `IsTypeDescPi`
typing witness.

## The neutral arm (this firing)

`TypedTypeValidity.neutral`: a NEUTRAL type code (a variable, or a neutral elimination form used as a type) is
typed-valid, carrying the SN Kripke candidate (`snKripkeCand`, #1108) as its semantic interpretation together
with its `IsTypeDescPi` typing witness.  This is the base case of the open type-level neutral reflection (the
variable / neutral-application leaf at which the residual bottoms out).  The candidate's rename-invariance
(`snKripkeCand_transport_pointwise`, #1108) is the semantic reason context conversion is FREE on this arm — so
the eventual transport-across-context-conversion theorem is structural here.

## ★ Design finding (durable): `KripkeCand` cannot be a dependent INDEX of the relation

`KripkeCand scope := ∀ {targetScope}, RawRenaming scope targetScope → RawTerm targetScope → Prop` is
FUNCTION-valued.  Indexing the relation by the candidate (`TypedTypeValidity … typeCode candidate`) makes the
index a function; Lean's dependent eliminator then fails to unify the eta-expanded implicit-lambda form
`(fun {targetScope} => candidate) =?= fun {targetScope} => snKripkeCand` (`Dependent elimination failed`), so
`cases`/`induction` on the relation cannot fire — and EVERY downstream consumer (soundness, transport, the
fundamental theorem) needs to eliminate it.  The resolution shipped here: keep `(context, typeCode)` as the
only INDICES and carry the candidate as a stored ARGUMENT of the constructor, recoverable by `cases`
(`carriesSnCandidate`).  The candidate is thus PAIRED with the typing (the firing-18 mandate) without being a
function-valued index.

## Honest boundary (the next spike)

This is the relation SKELETON + the NEUTRAL arm.  The Π-FORMER arm (a `Π` type code is typed-valid, with
interpretation `kripkeArrowDep (domain candidate) (codomain family)` built from the sub-codes' candidates) is
the genuine crux: with the candidate stored as an argument rather than an index, the Π-former cannot read its
sub-derivations' candidates inside a constructor declaration.  Threading sub-candidates needs either a
first-order boxed-candidate index, a relational candidate-membership, or a well-founded interpretation
function — a deliberate DESIGN SPIKE for the next firing, NOT another substrate closure.

## Zero-axiom verification

The relation is a plain inductive; soundness / candidate-recovery are single-arm `cases`; non-vacuity is one
constructor application with `Iff.rfl` for the SN-pointwise field.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **Pointwise agreement of two Kripke candidates.**  They accept the same terms at every renaming index —
the up-to-pointwise-iff equivalence at which reducibility candidates are used (mirroring the shipped
`IsReducibilityCandidate` respecting `PointwiseIff`, #489).  The `neutral` arm below records that the carried
candidate agrees pointwise with the SN Kripke candidate `snKripkeCand` (#1108). -/
def KripkeCandPointwiseIff {scope : Nat} (first second : KripkeCand scope) : Prop :=
  ∀ {targetScope : Nat} (indexRenaming : RawRenaming scope targetScope) (term : RawTerm targetScope),
    first indexRenaming term ↔ second indexRenaming term

/-- **The typed type-validity logical relation** — the Kripke-model interpretation of a valid type code,
pairing a reducibility candidate with the grown typing witness.  Indexed by `(context, typeCode)` ONLY (the
candidate is a stored ARGUMENT, not an index — see the file header's design finding on why a function-valued
`KripkeCand` index breaks dependent elimination).  The neutral arm is the base case of the open type-level
neutral reflection on which the GrownCtxConv-5 (#842) residual `ConvContextPreservesPiValidity` bottoms out. -/
inductive TypedTypeValidity (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → Prop where
  /-- A NEUTRAL type code (variable / neutral elimination form used as a type) is typed-valid, carrying the
  SN Kripke candidate as its semantic interpretation (`interpIsSn`: the carried candidate agrees pointwise
  with `snKripkeCand`, #1108) together with its `IsTypeDescPi` typing witness.  The base case of the open
  neutral reflection; context conversion is free here because `snKripkeCand` is rename-invariant (#1108). -/
  | neutral {scope : Nat} {context : TypingContext profile scope} {typeCode : RawTerm scope}
      (candidate : KripkeCand scope)
      (neutralCode : IsNeutral typeCode)
      (interpIsSn : KripkeCandPointwiseIff candidate snKripkeCand)
      (validity : IsTypeDescPi profile context typeCode) :
      TypedTypeValidity profile context typeCode

/-- **Soundness: the relation carries the grown type validity.**  A typed-valid type code inhabits some
universe in the grown engine (`IsTypeDescPi`).  This is the half that feeds the GrownCtxConv-5 residual: once transport
across context conversion is proved ON the relation, `IsTypeDescPi sourceCtx (Π D C)` → (completeness) the
relation → (transport) the relation at the target → (this soundness) `IsTypeDescPi targetCtx (Π D C)`.
Single-arm `cases`; the candidate being a stored argument (not a function index) is exactly what lets `cases`
fire. -/
theorem TypedTypeValidity.toIsTypeDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope}
    (relation : TypedTypeValidity profile context typeCode) :
    IsTypeDescPi profile context typeCode := by
  cases relation with
  | neutral _ _ _ validity => exact validity

/-- **Candidate pairing: a typed-valid type carries an SN-pointwise Kripke candidate.**  Recovers the stored
semantic interpretation (pointwise-equal to `snKripkeCand`, #1108) from the relation — the "pairs a candidate
with the typing" content of the model object, made explicit.  For the neutral arm the candidate is morally the
SN candidate; recovering it by `cases` (rather than reading a function-valued index) is the workaround for the
dependent-elimination constraint recorded in the file header. -/
theorem TypedTypeValidity.carriesSnCandidate {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {typeCode : RawTerm scope}
    (relation : TypedTypeValidity profile context typeCode) :
    ∃ candidate : KripkeCand scope, KripkeCandPointwiseIff candidate snKripkeCand := by
  cases relation with
  | neutral candidate _ interpIsSn _ => exact ⟨candidate, interpIsSn⟩

/-- **Non-vacuity: a variable type code with a validity witness is typed-valid.**  The simplest neutral type
code — a bare de Bruijn variable used as a type — is in the relation, carrying `snKripkeCand` (with the
pointwise field by `Iff.rfl`).  The base leaf of the open type-level neutral reflection: under context
conversion a variable's typing transfers by the var rule + the pointwise `Conv` on the looked-up classifier
(the non-circular leaf), whereas the neutral APPLICATION `(var f)(var a)` re-assembles the type-level `piElim`
(the genuinely-open residual = GrownCtxConv-5).  Demonstrates the relation is inhabited (not a vacuous definition). -/
theorem smoke_variableTypeIsTypedValid {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} (index : Fin scope)
    (validity : IsTypeDescPi profile context (.mkGen .gen_var index .childNil)) :
    TypedTypeValidity profile context (.mkGen .gen_var index .childNil) :=
  TypedTypeValidity.neutral snKripkeCand (IsNeutral.var index) (fun _ _ => Iff.rfl) validity

end FX1Poly.Typed

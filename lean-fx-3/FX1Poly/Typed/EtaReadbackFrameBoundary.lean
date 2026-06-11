import FX1Poly.Typed.TypeDirectedUnitReadback
import FX1Poly.Typed.UntypableHeadDecision
/-! # FX1Poly/Typed/EtaReadbackFrameBoundary
   — Σ / modal / cubical η-long readback is FRAME-BLOCKED (the #361/#363 verdict)

The type-directed η-long readback (`readbackAtClassifier`) was specced
to grow Σ (surjective pairing), modal, cubical-path, and Glue arms.
This file PROVES those arms cannot exist within the current soundness
frame, and pins the readback's honest behavior at those classifiers.

## The frame-block

The readback's soundness statement (`readbackAtClassifier_congruent`)
lives in `DefEqUnitEtaCong` with GROWN-typing presuppositions, and its
η-expansion legs route through `DefEqUnitEta.ofBetaEtaConv`, which
requires BOTH the subject AND its η-expansion grown-typed.  But the
grown engine (`HasTypeDescPi`) has NO rules for the advanced η-source
heads:

  * `gen_pair` / `gen_fst` / `gen_snd` — the pair story lives in the
    STANDALONE engines (`HasTypeDescPairIntro` / Σ-projection) by
    design: the grown `IntroRuleDesc` schema is binder-intro-shaped
    (`scope → RawTerm scope → RawTerm (scope+1) → RawTerm scope`, the
    λ shape), and a dependent pair intro (second premise classified by
    a TERM-substituted codomain) does not fit it.
  * `gen_modIntro` / `gen_pathLam` / `gen_glueIntro` — modal/cubical
    intros have reducibility and raw-η semantics but no grown typing
    rule (the HasType-era modal rules were deleted with that engine).

So each advanced η-EXPANSION (`pair (fst t) (snd t)`,
`modIntro (modElim t)`, `pathLam (pathApp (weaken t) v₀)`,
`glueIntro (glueElim t) t`) is grown-UNTYPABLE — proved below via
`isUntypableHead_sound` (the head has no row in any grown table) —
and the `ofBetaEtaConv` obligation is therefore UNINHABITED.  An
η-expanding arm at these classifiers would be an arm whose soundness
leg is unprovable; the module discipline (soundness mirrors the
function) forbids it.

## The honest positive content

At a Σ classifier the shipped readback ALREADY does the right thing:
`sigmaTyCodeCell` fails the Π-code match and DELEGATES to the
neutral-spine readback (`readbackAtClassifier_sigmaDelegatesToSpine`,
proved by reduction) — covered by the existing spine soundness.
Degrade, never break.

## The unlock (named, not claimed)

Either (a) grown pair/fst/snd + modal rules — requiring a NEW
intro-row schema beyond the binder shape (a costed design decision,
the next consumer of the cascade-free table mechanism), or (b) a
COMBINED-engine readback soundness frame (grown + standalone
intro/elim), the direction the canonicity arc (CANON-1/CAN-5) already
took.  Until one lands, the Σ/modal/cubical η DECISION content remains
covered by the βη-reducer route (the `BetaEtaConv` decider consumes
`Step.eta.etaPair` / `.etaModIntro` / `.etaPathLam` / `.etaGlueIntro`
directly), and the readback artifact is honestly absent.

Clock/param η formers are further out still: their generators are not
in the enum (Phase Z7/Z8), so even the raw `Step.eta` constructors do
not exist for them.

Zero-axiom; gated in `FX1PolyAudit/AuditTypedUnitEtaReadback.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## The advanced η-source heads have no grown row (rfl pins) -/

/-- `gen_pair` is grown-untypable (no row in any grown rule table). -/
theorem isUntypableHead_pair : isUntypableHead .gen_pair = true := rfl

/-- `gen_modIntro` is grown-untypable. -/
theorem isUntypableHead_modIntro : isUntypableHead .gen_modIntro = true := rfl

/-- `gen_pathLam` is grown-untypable. -/
theorem isUntypableHead_pathLam : isUntypableHead .gen_pathLam = true := rfl

/-- `gen_glueIntro` is grown-untypable. -/
theorem isUntypableHead_glueIntro : isUntypableHead .gen_glueIntro = true := rfl

/-! ## ★ The four advanced η-EXPANSIONS are grown-untypable

Each is the exact term an η-expanding readback arm would emit; none
can satisfy the `ofBetaEtaConv` both-sides-grown-typed obligation. -/

/-- The Σ-η expansion `pair (fst t) (snd t)` has no grown typing. -/
theorem etaPairSource_notGrownTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {pairTerm classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context
      (RawTerm.etaPairSource pairTerm) classifier) : False :=
  isUntypableHead_sound isUntypableHead_pair typed

/-- The modal-η expansion `modIntro (modElim t)` has no grown typing. -/
theorem etaModIntroSource_notGrownTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {modalTerm classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context
      (RawTerm.etaModIntroSource modalTerm) classifier) : False :=
  isUntypableHead_sound isUntypableHead_modIntro typed

/-- The path-η expansion `pathLam (pathApp (weaken t) v₀)` has no
grown typing. -/
theorem etaPathLamSource_notGrownTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {innerPath classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context
      (RawTerm.etaPathLamSource innerPath) classifier) : False :=
  isUntypableHead_sound isUntypableHead_pathLam typed

/-- The Glue-η expansion `glueIntro (glueElim t) t` has no grown
typing. -/
theorem etaGlueIntroSource_notGrownTyped {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {gluedTerm classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context
      (RawTerm.etaGlueIntroSource gluedTerm) classifier) : False :=
  isUntypableHead_sound isUntypableHead_glueIntro typed

/-! ## The honest positive content at Σ classifiers -/

/-- A Σ code is never the unit code (head discrimination). -/
theorem sigmaTyCodeCell_ne_unitTypeCell {scope : Nat}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)} :
    sigmaTyCodeCell domainCode codomainCode ≠ unitTypeCell :=
  fun headsEqual => nomatch (congrArg RawTerm.headGenerator headsEqual)

/-- A Σ code is not a Π code (the readback's Π-detector rejects it). -/
theorem asPiCode?_sigma_isNone {scope : Nat}
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    asPiCode? (sigmaTyCodeCell domainCode codomainCode) = none := by
  dsimp only [asPiCode?, sigmaTyCodeCell]
  rw [dif_neg (fun sigmaIsPi => nomatch sigmaIsPi :
    ¬(Generator.gen_sigmaTyCode = Generator.gen_piTyCode))]

/-- **The shipped readback's behavior at a Σ classifier is the
neutral-spine delegation** — the degrade-never-break discipline.  An
η-EXPANDING Σ arm would be unsound-in-frame (the expansion is
grown-untypable, `etaPairSource_notGrownTyped`); the delegation is the
honest arm, covered by the existing spine soundness. -/
theorem readbackAtClassifier_sigmaDelegatesToSpine
    {profile : PolyProfile} {scope : Nat}
    (fuel : Nat) (context : TypingContext profile scope)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1))
    (term : RawTerm scope) :
    readbackAtClassifier (fuel + 1) context
        (sigmaTyCodeCell domainCode codomainCode) term
      = readbackSpine fuel context term := by
  dsimp only [readbackAtClassifier]
  rw [if_neg sigmaTyCodeCell_ne_unitTypeCell,
    asPiCode?_sigma_isNone domainCode codomainCode]

end FX1Poly.Typed

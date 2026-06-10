import FX1Poly.Typed.GrownCheckContextConversion
import FX1Poly.Typed.CurryFixpointDivergence
import FX1Poly.Typed.TypedFragmentAcyclicity

/-! # FX1Poly/Typed/GrownCheckSoundnessRefutation — the RAW relation is UNSOUND even at a typed target

The strengthening campaign's second load-bearing refutation (after `GrownStrengtheningRefutation`):
SOUNDNESS of the raw `GrownCheck` relation — "a check at a typed target in a well-formed context
yields a typing" — is FALSE.  The raw relation was designed with NO typehood premises so that its
rename-reflection stays structural; the price is that the app arm's floating Π-code admits
ILL-FOUNDED types, and recursive types make untypable terms checkable:

  * `recursivePiType` — `X := curryOmega (λT. Π T. Type@0)`, the Curry fix-point TYPE, with
    `X ~Conv~ Π X. Type@0` (`recursivePiType_convPi`: the curry unfolding step + one β, the subst0
    computing definitionally).
  * `selfApplicationBodyChecks` / `selfApplicationChecksAtPi` / `selfApplicationChecksAtRecursiveType`
    — `λx. x x` checks BOTH at `Π X. Type@0` and at `X` itself (the unfolding read through the
    λ-arm's `Conv` leaf), its body's var leaves absorbing the weakened unfolding.
  * `omegaChecksAtTypeZero` — ★ Ω = `(λx.xx)(λx.xx)` CHECKS at `Type@0`: the app arm routes its
    floating Π-code through `X`, and the output leaf computes to `Type@0` because the codomain is
    constant.  The target is TYPED and the context well-formed — yet Ω is untypable
    (`omegaCombinator_notClosedWellTyped`, an SN-043 corollary).
  * `grownCheckRawSoundness_isFalse` — ★★ the refutation of the STR-5 statement.

## Consequence for the campaign

The completeness ∘ rename-reflection ∘ soundness pipeline CANNOT run over the raw relation: the
soundness leg needs typehood, and (per the STR-3/STR-2 analyses) typehood premises break either
the reflection (engine premises at non-subterm subjects = circular strengthening) or completeness
(relation-check premises = non-subderivation recursion).  Note the exploit needs a NON-SN type code
(`X` diverges), but SN side conditions do NOT rescue soundness — ill-typed NORMAL junk (e.g.
`app boolTrue boolTrue`) threads the same hole via universe-anchored argument chains.  The
surviving routes (recorded in the campaign log): NF-annotated ENGINE derivations with an
image-pinned-classifier premise (open core: pinning the function's Π at `piElim`), and the
both-pinned target's η-SR instance where the `(var 0)` argument pins the domain through
`inversionVariable`.  The shipped `GrownCheck` bricks (absorption, context conversion, exposure,
reassembly) remain the toolbox for whichever annotated judgment lands. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Core.StepStar FX1Poly.Universe FX1Poly.Foundation

/-- The Π-former body `Π (var 0). Type@0` — the recursive-type generator's body. -/
def piFormerBody : RawTerm 1 :=
  piTyCodeCell (variableCell ⟨0, Nat.succ_pos 0⟩) (typeZeroCode 2)

/-- The Π-former generator `λT. Π T. Type@0`.  Church-annotated with the recursive type `X` itself
(`recursiveSelfApplicationLambda`'s domain): under T2 the checker reads the λ-domain from the
syntactic annotation, so the exploit that routes the floating Π-code through `X` must pin the
annotation to `X` (the universe-anchored domain the body's var leaves absorb). -/
def piFormerLambda : RawTerm 0 :=
  lamCell (typeZeroCode 0) piFormerBody

/-- The recursive Π-type `X := curryOmega (λT. Π T. Type@0)` — the ill-founded type code with
`X ~Conv~ Π X. Type@0`. -/
def recursivePiType : RawTerm 0 :=
  curryOmega piFormerLambda

/-- The self-applicator `λx. x x` Church-annotated with the recursive type `X` as its domain — the
T2 form of the refutation's witness.  Under Church-style binders the checker reads the λ-domain from
the annotation, so the exploit pins the annotation to `X` (rather than letting the old Curry checker
choose it freely); the `unitCell`-annotated `selfApplicationLambda` from the SN corpus would pin the
domain to `unit`, which does not route the floating Π-code through `X`. -/
def recursiveSelfApplicationLambda : RawTerm 0 :=
  lamCell recursivePiType
    (appCell (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1))
      (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))

/-- `Ω` over the `X`-annotated self-applicator — the same divergent self-application, untypable for
the same SN-043 reason (its β-self-step is `Step.beta`, annotation discarded). -/
def recursiveOmega : RawTerm 0 :=
  appCell recursiveSelfApplicationLambda recursiveSelfApplicationLambda

/-- `X` reduces to `Π X. Type@0` in two steps: the curry unfolding, then β (the subst0 of the
Π-former body at `X` computes definitionally to `Π X. Type@0`). -/
theorem recursivePiType_reducesToPi :
    StepStar recursivePiType (piTyCodeCell recursivePiType (typeZeroCode 1)) :=
  have betaStep : Step (appCell piFormerLambda recursivePiType)
      (piTyCodeCell recursivePiType (typeZeroCode 1)) :=
    Step.beta
  StepStar.trans (curryOmega_step piFormerLambda) (StepStar.single betaStep)

/-- `X ~Conv~ Π X. Type@0` — the recursive-type unfolding as a conversion. -/
theorem recursivePiType_convPi :
    Conv recursivePiType (piTyCodeCell recursivePiType (typeZeroCode 1)) :=
  Conv.fromStepStar recursivePiType_reducesToPi

/-- The self-application body `(var 0)(var 0)` CHECKS at `Type@0` under the context `[X]` — the
var-arm leaves absorb the recursive unfolding (weakened). -/
theorem selfApplicationBodyChecks (profile : PolyProfile) :
    GrownCheck profile
      ((TypingContext.empty (profile := profile)).cons recursivePiType)
      (appCell (variableCell ⟨0, Nat.succ_pos 0⟩) (variableCell ⟨0, Nat.succ_pos 0⟩))
      (typeZeroCode 1) :=
  have lookupConvPi : Conv (RawTerm.weaken recursivePiType)
      (piTyCodeCell (RawTerm.weaken recursivePiType) (typeZeroCode 2)) :=
    Conv.rename RawRenaming.weaken recursivePiType_convPi
  GrownCheck.app (RawTerm.weaken recursivePiType) (typeZeroCode 2)
    (GrownCheck.var ⟨0, Nat.succ_pos 0⟩ lookupConvPi)
    (GrownCheck.var ⟨0, Nat.succ_pos 0⟩ (Conv.refl _))
    (Conv.refl _)

/-- The `X`-annotated self-applicator CHECKS at the honest-looking Π-code `Π X. Type@0` — under T2
the lam arm reads the domain from the annotation, which is exactly `X`. -/
theorem selfApplicationChecksAtPi (profile : PolyProfile) :
    GrownCheck profile (TypingContext.empty (profile := profile))
      recursiveSelfApplicationLambda
      (piTyCodeCell recursivePiType (typeZeroCode 1)) :=
  GrownCheck.lam recursivePiType (typeZeroCode 1)
    (Conv.refl _)
    (selfApplicationBodyChecks profile)

/-- The `X`-annotated self-applicator ALSO checks at the recursive type `X` itself (the unfolding read
backwards through the λ-arm's `Conv` leaf). -/
theorem selfApplicationChecksAtRecursiveType (profile : PolyProfile) :
    GrownCheck profile (TypingContext.empty (profile := profile))
      recursiveSelfApplicationLambda
      recursivePiType :=
  GrownCheck.lam recursivePiType (typeZeroCode 1)
    recursivePiType_convPi.sym
    (selfApplicationBodyChecks profile)

/-- ★ **`recursiveOmega` CHECKS at `Type@0`** — the untypable diverging combinator passes the raw
relation at a TYPED target, by routing the app arm's floating Π-code through the recursive type `X`
(the function and argument are the SAME `X`-annotated self-applicator). -/
theorem omegaChecksAtTypeZero (profile : PolyProfile) :
    GrownCheck profile (TypingContext.empty (profile := profile))
      recursiveOmega
      (typeZeroCode 0) :=
  GrownCheck.app recursivePiType (typeZeroCode 1)
    (selfApplicationChecksAtPi profile)
    (selfApplicationChecksAtRecursiveType profile)
    (Conv.refl _)

/-- `recursiveOmega` β-self-steps (the annotation is discarded by β, the body `(var 0)(var 0)`
substituted by the self-applicator recopies it), so it diverges and is NOT strongly normalizing. -/
theorem recursiveOmega_betaSelfStep : Step recursiveOmega recursiveOmega :=
  Step.beta

/-- `recursiveOmega` is NOT strongly normalizing — it self-loops under `Step`. -/
theorem recursiveOmega_notStronglyNormalizing :
    ¬ IsStronglyNormalizing recursiveOmega :=
  fun stronglyNormalizing =>
    accessibleElementNotSelfRelated stronglyNormalizing recursiveOmega_betaSelfStep

/-- `recursiveOmega` has NO closed type — were it typed, SN-043 would force it strongly normalizing,
contradicting its self-loop. -/
theorem recursiveOmega_notClosedWellTyped {profile : PolyProfile} :
    ¬ ∃ classifier : RawTerm 0,
      HasTypeDescPi profile TypingContext.empty recursiveOmega classifier :=
  fun ⟨_classifier, typing⟩ =>
    recursiveOmega_notStronglyNormalizing
      (HasTypeDescPi.closedStronglyNormalizing typing)

/-- ★★ **Raw-relation soundness is FALSE, even with a typed target and a well-formed context**:
were every `GrownCheck` at a typed target sound, `recursiveOmega` would be well-typed — contradicting
`recursiveOmega_notClosedWellTyped` (SN-043). -/
theorem grownCheckRawSoundness_isFalse (profile : PolyProfile) :
    ¬ (∀ (subject target : RawTerm 0) (targetLevel : LevelExpr) (targetFlag : UniverseFlag),
        WfContextDescPi (TypingContext.empty (profile := profile)) →
        HasTypeDescPi profile TypingContext.empty target
          (universeCodeCell targetLevel targetFlag) →
        GrownCheck profile TypingContext.empty subject target →
        HasTypeDescPi profile TypingContext.empty subject target) := by
  intro soundnessClaim
  exact recursiveOmega_notClosedWellTyped
    ⟨typeZeroCode 0,
      soundnessClaim recursiveOmega (typeZeroCode 0) LevelExpr.lzero.lsucc
        UniverseFlag.standard
        WfContextDescPi.emptyIsWellFormed
        (HasTypeDescPi.ofFormation
          (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero
            UniverseFlag.standard))
        (omegaChecksAtTypeZero profile)⟩

end FX1Poly.Typed

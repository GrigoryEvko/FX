import FX1Poly.Typed.FormationClassifierRigidity
import FX1Poly.Typed.GrownWfOpenStronglyNormalizing
import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional
import FX1Poly.Typed.TypedLambdaDerivations
import FX1Poly.Core.Normalize

/-! # FX1Poly/Typed/TypedNbeNormalizer
   — ★ #480: the typed NbE EVAL half + the eval∘quote composition (the typed normalizer)

The typed normalizer's two halves, composed:

  * **eval** (`evalNormalForm`, THIS module's #480 core): β/ι-normalization of a well-typed OPEN
    term — `RawTerm.normalize` with the open SN witness
    (`stronglyNormalizingOfWfContextDesc`, OB-5) as the termination certificate.  TOTAL on the
    wf typed fragment, NO fuel.  Its typed metatheory: the output is reached by a reduction
    chain, is structurally normal, converts to the input, and — the #480 headline — is TYPED AT
    THE SAME CLASSIFIER (`evalNormalForm_typed`, via the unconditional master
    `subjectReductionStar`).
  * **quote** (`readbackAtClassifier`, the #481 campaign): type-directed η-long/unit
    canonicalization of the β-normal output.

`nbeNormalForm = quote ∘ eval` is the composed typed NbE normalizer;
`nbeNormalForm_congruent` is its soundness (the input is congruently unit-η-equal to its NbE
form), and `DefEqUnitEtaCong.ofNbeEqual` the #364-shaped semi-decision: equal NbE forms ⟹
congruently equal.

## Each half is load-bearing

  * EVAL is load-bearing: the β-redex `(λ(x:Type@(e+1)).x)(Type@e)` and its reduct `Type@e`
    (both typed at `Type@(e+1)`) are decided by the composition
    (`identityApplicationPair_decidedByNbe` — eval collapses the redex), while quote ALONE
    fixes the unevaluated redex (`readbackAlone_keepsBetaRedex` — the readback never
    β-reduces).
  * QUOTE is load-bearing: the η pair and the mixed η+unit pairs (the #481 modules) are
    invisible to β/ι-normalization — both sides are already β-normal — and are decided only by
    the type-directed readback.

## Zero-axiom verification

`evalNormalForm` composes the shipped `RawTerm.normalize` (Acc-recursion, propext-free) with
the shipped open-SN witness; the typed metatheory is `subjectReductionStar` + the `normalize`
lemma family; eval identifications use `normalize_eq_iff_conv` + `StepStar.eq_of_noStep`; the
composition soundness chains `ofBetaEtaConv` with the readback soundness.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The typed NbE EVAL half (#480)**: β/ι-normalize a well-typed open term, with the open SN
witness as the termination certificate.  Total, fuel-free. -/
def HasTypeDescPi.evalNormalForm {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) : RawTerm scope :=
  RawTerm.normalize subject
    (HasTypeDescPi.stronglyNormalizingOfWfContextDesc contextWellFormed typed)

/-- The subject reaches its eval normal form by a reduction chain. -/
theorem HasTypeDescPi.evalNormalForm_reducesTo {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) :
    StepStar subject (HasTypeDescPi.evalNormalForm contextWellFormed typed) :=
  RawTerm.normalize_reducesTo subject _

/-- The eval normal form is structurally normal — no β/ι step applies. -/
theorem HasTypeDescPi.evalNormalForm_isStepNormalForm {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) :
    RawTerm.isStepNormalForm (HasTypeDescPi.evalNormalForm contextWellFormed typed) :=
  RawTerm.normalize_isStepNormalForm subject _

/-- The subject converts to its eval normal form. -/
theorem HasTypeDescPi.evalNormalForm_conv {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) :
    Conv subject (HasTypeDescPi.evalNormalForm contextWellFormed typed) :=
  RawTerm.conv_normalize subject _

/-- **★ Eval preserves typing (#480 headline)**: the eval normal form is grown-typed at the SAME
classifier — the unconditional master `subjectReductionStar` along the normalization chain. -/
theorem HasTypeDescPi.evalNormalForm_typed {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) :
    HasTypeDescPi profile context
      (HasTypeDescPi.evalNormalForm contextWellFormed typed) classifier :=
  HasTypeDescPi.subjectReductionStar (WfContextDescPi.ofWfContextDesc contextWellFormed)
    typed (HasTypeDescPi.evalNormalForm_reducesTo contextWellFormed typed)

/-- **The composed typed NbE normalizer**: eval (β/ι, total) then quote (type-directed η-long
unit canonicalization, fuel-structural). -/
def HasTypeDescPi.nbeNormalForm {profile : PolyProfile} (fuel : Nat) {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier) : RawTerm scope :=
  readbackAtClassifier fuel context classifier
    (HasTypeDescPi.evalNormalForm contextWellFormed typed)

/-- **★ Composed soundness**: a well-typed subject is congruently unit-η-equal to its NbE
normal form — the eval leg by `ofBetaEtaConv` over the normalization chain (eval preserves
typing supplies the right endpoint), the quote leg by the readback soundness on the typed
eval output. -/
theorem HasTypeDescPi.nbeNormalForm_congruent {profile : PolyProfile}
    (fuel : Nat) {scope : Nat} {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (contextWellFormed : WfContextDesc context)
    (typed : HasTypeDescPi profile context subject classifier)
    {classifierLevel : LevelExpr} {classifierFlag : UniverseFlag}
    (classifierTyped : HasTypeDesc profile context classifier
      (universeCodeCell classifierLevel classifierFlag)) :
    DefEqUnitEtaCong profile context subject
      (HasTypeDescPi.nbeNormalForm fuel contextWellFormed typed) :=
  DefEqUnitEtaCong.trans
    (.ofDefEq (.ofBetaEtaConv contextWellFormed typed
      (HasTypeDescPi.evalNormalForm_typed contextWellFormed typed)
      (BetaEtaConv.ofConv
        (HasTypeDescPi.evalNormalForm_conv contextWellFormed typed))))
    (readbackAtClassifier_congruent fuel context classifier
      (HasTypeDescPi.evalNormalForm contextWellFormed typed)
      contextWellFormed
      (HasTypeDescPi.evalNormalForm_typed contextWellFormed typed)
      classifierTyped)

/-- **★ The composed semi-decision (the #364 shape)**: two subjects grown-typed at the same
formation-typed classifier in a wf context, with EQUAL NbE normal forms, are congruently
unit-η-equal. -/
theorem DefEqUnitEtaCong.ofNbeEqual {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {classifier leftTerm rightTerm : RawTerm scope}
    {leftFuel rightFuel : Nat}
    {classifierLevel : LevelExpr} {classifierFlag : UniverseFlag}
    (contextWellFormed : WfContextDesc context)
    (leftTyped : HasTypeDescPi profile context leftTerm classifier)
    (rightTyped : HasTypeDescPi profile context rightTerm classifier)
    (classifierTyped : HasTypeDesc profile context classifier
      (universeCodeCell classifierLevel classifierFlag))
    (nbeEqual : HasTypeDescPi.nbeNormalForm leftFuel contextWellFormed leftTyped
      = HasTypeDescPi.nbeNormalForm rightFuel contextWellFormed rightTyped) :
    DefEqUnitEtaCong profile context leftTerm rightTerm :=
  .trans
    (HasTypeDescPi.nbeNormalForm_congruent leftFuel contextWellFormed leftTyped
      classifierTyped)
    (nbeEqual ▸
      (HasTypeDescPi.nbeNormalForm_congruent rightFuel contextWellFormed rightTyped
        classifierTyped).sym)

/-- Universe codes are eval fixed points — they admit no step, so the normalization chain
collapses. -/
theorem universeCode_evalNormalForm_eq {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    HasTypeDescPi.evalNormalForm WfContextDesc.emptyIsWellFormed
        (HasTypeDescPi.ofFormation
          (HasTypeDesc.universeFormation (TypingContext.empty : TypingContext profile 0)
            levelExpr flag))
      = universeCodeCell levelExpr flag :=
  StepStar.eq_of_noStep (fun _reduct step => Step.no_step_from_universeCode step)
    (HasTypeDescPi.evalNormalForm_reducesTo _ _)

/-- **Eval contracts the typed β-redex**: `(λ(x:Type@(e+1)).x)(Type@e)` evaluates to `Type@e` —
the redex converts to its reduct (one β step), so `normalize_eq_iff_conv` identifies the two
eval forms, and the reduct is an eval fixed point. -/
theorem identityApplication_evalNormalForm_eq {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    HasTypeDescPi.evalNormalForm WfContextDesc.emptyIsWellFormed
        (identityApplicationOnUniverseCode_hasTypeDescPi (profile := profile) levelExpr flag)
      = universeCodeCell levelExpr flag := by
  have redexConvertsToReduct :
      Conv
        (appCell (lamCell (universeCodeCell levelExpr.lsucc flag)
            (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
          (universeCodeCell levelExpr flag))
        (universeCodeCell levelExpr flag) :=
    ⟨universeCodeCell levelExpr flag,
      StepStar.trans
        (identityApplicationOnUniverseCode_betaReducesToArgument levelExpr flag)
        (StepStar.refl _),
      StepStar.refl _⟩
  have normalizersAgree :=
    (RawTerm.normalize_eq_iff_conv _ _
      (HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed
        (identityApplicationOnUniverseCode_hasTypeDescPi (profile := profile)
          levelExpr flag))
      (HasTypeDescPi.stronglyNormalizingOfWfContextDesc WfContextDesc.emptyIsWellFormed
        (HasTypeDescPi.ofFormation
          (HasTypeDesc.universeFormation (TypingContext.empty : TypingContext profile 0)
            levelExpr flag)))).mp redexConvertsToReduct
  have universeIsEvalFixed :=
    universeCode_evalNormalForm_eq (profile := profile) levelExpr flag
  dsimp only [HasTypeDescPi.evalNormalForm] at universeIsEvalFixed ⊢
  exact normalizersAgree.trans universeIsEvalFixed

/-- **Quote alone never β-reduces**: the readback FIXES the unevaluated β-redex (the spine arm
deep-collapses an app with a λ head, and there are no unit-typed variables to rewrite) — eval
is load-bearing in the composition. -/
theorem readbackAlone_keepsBetaRedex {profile : PolyProfile} :
    readbackAtClassifier 1 (TypingContext.empty : TypingContext profile 0)
        (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)
        (appCell (lamCell (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)
            (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
          (universeCodeCell LevelExpr.lzero UniverseFlag.standard))
      = appCell (lamCell (universeCodeCell LevelExpr.lzero.lsucc UniverseFlag.standard)
            (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
          (universeCodeCell LevelExpr.lzero UniverseFlag.standard) := rfl

/-- **★ The β-redex pair, decided by the COMPOSED normalizer**: the typed redex and its reduct
(both at `Type@(e+1)`) have equal NbE forms at fuel 1 — eval contracts the redex, quote agrees
on the shared eval output.  Quote alone provably fixes the redex
(`readbackAlone_keepsBetaRedex`), so this pair certifies eval's place in the pipeline. -/
theorem identityApplicationPair_decidedByNbe {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    DefEqUnitEtaCong profile (TypingContext.empty : TypingContext profile 0)
      (appCell (lamCell (universeCodeCell levelExpr.lsucc flag)
          (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1)))
        (universeCodeCell levelExpr flag))
      (universeCodeCell levelExpr flag) :=
  DefEqUnitEtaCong.ofNbeEqual (leftFuel := 1) (rightFuel := 1)
    WfContextDesc.emptyIsWellFormed
    (identityApplicationOnUniverseCode_hasTypeDescPi levelExpr flag)
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty levelExpr flag))
    (HasTypeDesc.universeFormation TypingContext.empty levelExpr.lsucc flag)
    (by
      dsimp only [HasTypeDescPi.nbeNormalForm]
      rw [identityApplication_evalNormalForm_eq, universeCode_evalNormalForm_eq])

end FX1Poly.Typed

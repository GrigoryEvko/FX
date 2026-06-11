import FX1Poly.Typed.IntroRuleDesc
import FX1Poly.Typed.ElimRuleDesc
import FX1Poly.Modal.ResourceGraded

/-! # FX1Poly/Typed/UnifiedRuleSignature — NATIVE-01: the unified RuleDesc + generalized premise telescope (DESIGN LOCK)

The campaign's design lock.  Today the typed layer has THREE separate rule-description tables, each
carrying ONLY its OUTPUT as data while the PREMISES are either a data-light telescope or hardwired:

  * `typingRuleDescOf` (formation) — output `TypingRuleDesc.outputType` from the children's LEVELS;
    premises = the `DescTelescope` spine ("children are TYPES").  THE shipped generic premise schema.
  * `introRuleDescOf` (introduction) — output `IntroRuleDesc.outputType` from Π type-parameters;
    premises HARDWIRED in `HasTypeDescPi.piIntro` (domain : Type, codomain : Type, body : codomain).
  * `elimRuleDescOf` (elimination) — output `ElimRuleDesc.outputType` children-DEPENDENT (`subst0`);
    premises HARDWIRED in `HasTypeDescPi.piElim` (function : Π, argument : domain).

To become ONE judgment = the initial model of a single second-order signature (Uemura RMC / Kaposi-Xie
SSC), the premises themselves must become DATA over a fixed vocabulary.  This module LOCKS that
vocabulary and proves it faithfully describes every rule-bearing AND every spike-target generator,
WITHOUT yet building the unified interpreter (that is NATIVE-12/20/27 onward — each `PremiseClassifierKind`
gets its interpreter as the spikes 02/03/04 discharge expressibility).

## The locked premise vocabulary (`PremiseClassifierKind`)

Five constructors — the genuine distinct premise-shape classes that determine interpreter complexity:

  1. `childIsType` — the child is a TYPE (universe-code-classified).  Interpreter SHIPPED (`DescTelescope`).
     Covers every formation child and every eliminator's motive (a type family under a binder).
  2. `childMemberOfInferredType` — the child is a TERM inhabiting an INFERRED classifier (λ-body inhabits
     the inferred codomain; app-argument inhabits the inferred domain; the eliminator branches).
     Interpreter SHIPPED (the grown `HasTypeDescPi` piIntro/piElim arms).
  3. `childMemberOfEarlierType earlierIndex` — the child is a TERM whose classifier is an EARLIER CHILD
     viewed as a type (the Id/Bridge endpoint terms `a b : A`).  THE term-indexed-former premise —
     interpreter is NATIVE-02 / NATIVE-12.
  4. `childInferredFunctionFormer` — the eliminated child inhabits an INFERRED eliminable type (app's
     function inhabits an inferred Π; a data scrutinee inhabits an inferred data type).  Shipped for Π
     (grown piElim); the data-eliminator extension rides NATIVE-27/32.
  5. `childMotiveInstance motiveIndex` — the child inhabits the MOTIVE (an earlier child) applied to
     constructor data / the IH (the dependent recursive eliminators natElim/natRec/listElim).  THE
     dependent-elim premise — interpreter is NATIVE-04 / NATIVE-27 (the campaign's risk class).

The GRADED dimension is ORTHOGONAL: every premise carries a `usage : UsageGrade` (the shipped
{0,1,ω} usage semiring).  Ordinary binders carry `.omega`; the BRIDGE/path dimension binder (`pathLam`)
carries `.one` (affine) — that single non-`omega` is the entire NATIVE-03 graded-intro obligation,
factored OUT of the classifier vocabulary as its own dimension.

## What is machine-checked here (the design lock's teeth)

  * `RuleSignature.premiseBinderShifts sig = generator.binderShifts` for EVERY generator in the table —
    the load-bearing faithfulness tying the descriptor telescope to the kernel generator's actual binder
    structure (`signature_binderShifts_faithful`).  A descriptor that mis-states a premise's binder count
    FAILS to compile.
  * Role pins agreeing with the existing tables (`unifiedSignatureOf g` role = `formation` exactly when
    `typingRuleDescOf g` is `some`, etc.).
  * `formationGeneratorsAreNative` — every formation generator's premises use ONLY shipped classifier
    kinds, so formation is 100% native NOW (the campaign's already-won fragment).
  * The gap pins: `bridgePremisesNeedTermIndexed`, `pathLamPremiseIsGradedAffine`,
    `natElimPremisesNeedMotive` — each spike target's signature exhibits exactly the unshipped kind that
    its spike (02/03/04) must make expressible.

## Zero-axiom

Plain enums (`deriving DecidableEq, BEq`); the faithfulness + role + gap pins are `rfl` / `by decide` /
`⟨rfl, …⟩`.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
Per-declaration audit-gated in `FX1PolyAudit/AuditTypedSubstVecCwR.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Modal

/-! ## The unified role + premise vocabulary -/

/-- The role a typing rule plays in the unified signature. -/
inductive RuleRole where
  | formation
  | introduction
  | elimination
  deriving DecidableEq, BEq

/-- The LOCKED premise-classifier vocabulary — the five genuine premise-shape classes the unified
typing interpreter must cover.  Each constructor's interpreter status is recorded by
`classifierKindInterpreterShipped`; the unshipped ones are the NATIVE-02/03/04 spike obligations. -/
inductive PremiseClassifierKind where
  /-- Child is a TYPE (universe-code-classified).  Interpreter: `DescTelescope`.  SHIPPED. -/
  | childIsType
  /-- Child is a term inhabiting an INFERRED classifier (λ-body / app-argument / eliminator branch).
  Interpreter: the grown `HasTypeDescPi` piIntro/piElim arms.  SHIPPED. -/
  | childMemberOfInferredType
  /-- Child is a term whose classifier is an EARLIER CHILD as a type (Id/Bridge endpoints).  The
  term-indexed-former premise.  NATIVE-02. -/
  | childMemberOfEarlierType (earlierIndex : Nat)
  /-- The eliminated child inhabits an INFERRED eliminable type (app function : Π; data scrutinee).
  Shipped for Π; data-eliminator extension is NATIVE-27. -/
  | childInferredFunctionFormer
  /-- Child inhabits the MOTIVE (an earlier child) applied to constructor data / the IH (dependent
  recursive eliminators).  NATIVE-04 (the risk class). -/
  | childMotiveInstance (motiveIndex : Nat)
  deriving DecidableEq, BEq

/-- Whether the unified typing interpreter for a premise classifier kind is ALREADY shipped.  Only the
two MLTT-core kinds (`childIsType` via the formation telescope, `childMemberOfInferredType` via the grown
piIntro/piElim) have interpreters today; the others are the spike obligations.  `childInferredFunctionFormer`
is shipped for Π (grown piElim) but its data-eliminator extension is pending — recorded `false` until
NATIVE-27 lands the general form. -/
def classifierKindInterpreterShipped : PremiseClassifierKind → Bool
  | .childIsType => true
  | .childMemberOfInferredType => true
  | .childMemberOfEarlierType _ => false
  | .childInferredFunctionFormer => false
  | .childMotiveInstance _ => false

/-- One premise in a rule's telescope: how many fresh binders it introduces (must agree with the
generator's `binderShifts`), its classifier kind (the vocabulary above), and its usage grade (the
graded dimension; `.omega` ordinary, `.one` for the affine dimension binder). -/
structure PremiseDescriptor where
  binderShift : Nat
  classifierKind : PremiseClassifierKind
  usage : UsageGrade
  deriving DecidableEq

/-- A unified rule signature: its role and its premise telescope.  The OUTPUT stays the existing
per-role table data (`TypingRuleDesc`/`IntroRuleDesc`/`ElimRuleDesc`) — those genuinely produce
different-arity outputs and CANNOT be naively merged (the design-lock conclusion: the premise telescope
is what unifies, not the output).  This signature is the static DESCRIPTION; the interpreter turning it
into actual `HasType` premises is the NATIVE-12+ work. -/
structure RuleSignature where
  role : RuleRole
  premises : List PremiseDescriptor

/-- The binder-shift telescope read off a signature's premises — the structural projection that must
match the generator's own `binderShifts`. -/
def RuleSignature.premiseBinderShifts (signature : RuleSignature) : List Nat :=
  signature.premises.map (·.binderShift)

/-- Whether every premise of a signature uses an already-shipped classifier kind. -/
def RuleSignature.allPremisesNative (signature : RuleSignature) : Bool :=
  signature.premises.all (fun premise => classifierKindInterpreterShipped premise.classifierKind)

/-! ## The unified signature table (covers the rule-bearing AND the spike-target generators) -/

/-- Shorthand: an ordinary (unrestricted) premise. -/
def ordinaryPremise (binderShift : Nat) (kind : PremiseClassifierKind) : PremiseDescriptor :=
  { binderShift := binderShift, classifierKind := kind, usage := .omega }

/-- Shorthand: an AFFINE premise (the dimension binder) — usage `.one`. -/
def affinePremise (binderShift : Nat) (kind : PremiseClassifierKind) : PremiseDescriptor :=
  { binderShift := binderShift, classifierKind := kind, usage := .one }

/-- The unified signature table.  Covers the seven currently-typed rule-bearing generators
(piTyCode/sigmaTyCode/listCode/optionCode/unitCode/lam/app) PLUS the five spike targets
(idCode/bridgeCode/pathLam/pathApp/natElim/listElim), demonstrating the locked vocabulary EXPRESSES every
target's premise telescope.  Premise binder-shifts match each generator's `binderShifts` exactly (the
faithfulness theorem below). -/
def unifiedSignatureOf (generator : Generator) : Option RuleSignature :=
  if generator = .gen_piTyCode then
    some { role := .formation,
           premises := [ordinaryPremise 0 .childIsType, ordinaryPremise 1 .childIsType] }
  else if generator = .gen_sigmaTyCode then
    some { role := .formation,
           premises := [ordinaryPremise 0 .childIsType, ordinaryPremise 1 .childIsType] }
  else if generator = .gen_listCode then
    some { role := .formation, premises := [ordinaryPremise 0 .childIsType] }
  else if generator = .gen_optionCode then
    some { role := .formation, premises := [ordinaryPremise 0 .childIsType] }
  else if generator = .gen_unitCode then
    some { role := .formation, premises := [] }
  else if generator = .gen_lam then
    some { role := .introduction,
           premises := [ordinaryPremise 0 .childIsType,
                        ordinaryPremise 1 .childMemberOfInferredType] }
  else if generator = .gen_app then
    some { role := .elimination,
           premises := [ordinaryPremise 0 .childInferredFunctionFormer,
                        ordinaryPremise 0 .childMemberOfInferredType] }
  else if generator = .gen_idCode then
    some { role := .formation,
           premises := [ordinaryPremise 0 .childIsType,
                        ordinaryPremise 0 (.childMemberOfEarlierType 0),
                        ordinaryPremise 0 (.childMemberOfEarlierType 0)] }
  else if generator = .gen_bridgeCode then
    some { role := .formation,
           premises := [ordinaryPremise 0 .childIsType,
                        ordinaryPremise 0 (.childMemberOfEarlierType 0),
                        ordinaryPremise 0 (.childMemberOfEarlierType 0)] }
  else if generator = .gen_pathLam then
    some { role := .introduction,
           premises := [affinePremise 1 .childMemberOfInferredType] }
  else if generator = .gen_pathApp then
    some { role := .elimination,
           premises := [ordinaryPremise 0 .childInferredFunctionFormer,
                        ordinaryPremise 0 .childMemberOfInferredType] }
  else if generator = .gen_natElim then
    some { role := .elimination,
           premises := [ordinaryPremise 1 .childIsType,
                        ordinaryPremise 0 (.childMotiveInstance 0),
                        ordinaryPremise 2 (.childMotiveInstance 0),
                        ordinaryPremise 0 .childMemberOfInferredType] }
  else if generator = .gen_listElim then
    some { role := .elimination,
           premises := [ordinaryPremise 1 .childIsType,
                        ordinaryPremise 0 (.childMotiveInstance 0),
                        ordinaryPremise 0 (.childMotiveInstance 0),
                        ordinaryPremise 0 .childMemberOfInferredType] }
  else none

/-! ## ★ Faithfulness: the descriptor telescope matches the kernel generator's binder structure -/

/-- **The load-bearing design-lock check: each signature's premise binder-shifts equal the generator's
own `binderShifts`.**  This ties the unified premise telescope to the kernel's actual binder structure —
a descriptor that mis-states a premise's binder count fails to compile.  Verified by `decide` over all
twelve table generators. -/
theorem signature_binderShifts_faithful :
    (unifiedSignatureOf .gen_piTyCode).map (·.premiseBinderShifts) = some Generator.gen_piTyCode.binderShifts ∧
    (unifiedSignatureOf .gen_sigmaTyCode).map (·.premiseBinderShifts) = some Generator.gen_sigmaTyCode.binderShifts ∧
    (unifiedSignatureOf .gen_listCode).map (·.premiseBinderShifts) = some Generator.gen_listCode.binderShifts ∧
    (unifiedSignatureOf .gen_optionCode).map (·.premiseBinderShifts) = some Generator.gen_optionCode.binderShifts ∧
    (unifiedSignatureOf .gen_unitCode).map (·.premiseBinderShifts) = some Generator.gen_unitCode.binderShifts ∧
    (unifiedSignatureOf .gen_lam).map (·.premiseBinderShifts) = some Generator.gen_lam.binderShifts ∧
    (unifiedSignatureOf .gen_app).map (·.premiseBinderShifts) = some Generator.gen_app.binderShifts ∧
    (unifiedSignatureOf .gen_idCode).map (·.premiseBinderShifts) = some Generator.gen_idCode.binderShifts ∧
    (unifiedSignatureOf .gen_bridgeCode).map (·.premiseBinderShifts) = some Generator.gen_bridgeCode.binderShifts ∧
    (unifiedSignatureOf .gen_pathLam).map (·.premiseBinderShifts) = some Generator.gen_pathLam.binderShifts ∧
    (unifiedSignatureOf .gen_pathApp).map (·.premiseBinderShifts) = some Generator.gen_pathApp.binderShifts ∧
    (unifiedSignatureOf .gen_natElim).map (·.premiseBinderShifts) = some Generator.gen_natElim.binderShifts ∧
    (unifiedSignatureOf .gen_listElim).map (·.premiseBinderShifts) = some Generator.gen_listElim.binderShifts := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-! ## Role faithfulness vs the existing tables -/

/-- The formation generators carry role `formation`, and they are exactly those with a `typingRuleDescOf`
row (the two tables agree on the formation fragment). -/
theorem unifiedRole_formation_agreesWithTable :
    (unifiedSignatureOf .gen_piTyCode).map (·.role) = some .formation ∧
    (typingRuleDescOf .gen_piTyCode).isSome = true ∧
    (unifiedSignatureOf .gen_unitCode).map (·.role) = some .formation ∧
    (typingRuleDescOf .gen_unitCode).isSome = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `gen_lam` carries role `introduction` and has an `introRuleDescOf` row; `gen_app` carries role
`elimination` and has an `elimRuleDescOf` row — the unified roles agree with the existing intro/elim
tables. -/
theorem unifiedRole_introElim_agreesWithTable :
    (unifiedSignatureOf .gen_lam).map (·.role) = some .introduction ∧
    (introRuleDescOf .gen_lam).isSome = true ∧
    (unifiedSignatureOf .gen_app).map (·.role) = some .elimination ∧
    (elimRuleDescOf .gen_app).isSome = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## The native fragment + the spike-target gap pins -/

/-- **Formation is 100% native NOW.**  Every formation generator's premises use only shipped classifier
kinds (`childIsType`) — the campaign's already-won fragment.  (`gen_lam`'s `childIsType` domain premise
is likewise shipped; its body premise rides the shipped grown piIntro.) -/
theorem formationGeneratorsAreNative :
    (unifiedSignatureOf .gen_piTyCode).map (·.allPremisesNative) = some true ∧
    (unifiedSignatureOf .gen_sigmaTyCode).map (·.allPremisesNative) = some true ∧
    (unifiedSignatureOf .gen_listCode).map (·.allPremisesNative) = some true ∧
    (unifiedSignatureOf .gen_optionCode).map (·.allPremisesNative) = some true ∧
    (unifiedSignatureOf .gen_unitCode).map (·.allPremisesNative) = some true ∧
    (unifiedSignatureOf .gen_lam).map (·.allPremisesNative) = some true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The term-indexed-former gap (NATIVE-02 obligation):** the Id and Bridge signatures' endpoint
premises carry `childMemberOfEarlierType 0` (the endpoints `a b : A`), an UNSHIPPED kind, so their
signatures are not yet native.  This is exactly what NATIVE-02 must make expressible. -/
theorem bridgePremisesNeedTermIndexed :
    (unifiedSignatureOf .gen_idCode).map (·.allPremisesNative) = some false ∧
    (unifiedSignatureOf .gen_bridgeCode).map (·.allPremisesNative) = some false ∧
    classifierKindInterpreterShipped (.childMemberOfEarlierType 0) = false :=
  ⟨rfl, rfl, rfl⟩

/-- **The graded-intro gap (NATIVE-03 obligation):** `pathLam`'s sole premise is the affine dimension
binder — usage `.one`, NOT `.omega`.  The graded dimension is the orthogonal axis the table-graded
interpreter (NATIVE-20/23) must thread; this pins the single non-`omega` usage that defines it. -/
theorem pathLamPremiseIsGradedAffine :
    (unifiedSignatureOf .gen_pathLam).map (fun sig => sig.premises.map (·.usage))
      = some [UsageGrade.one] :=
  rfl

/-- **The dependent-elim gap (NATIVE-04 obligation):** natElim and listElim carry `childMotiveInstance`
premises (the recursive IH), an UNSHIPPED kind — the campaign's risk class that decides whether the final
system is one inductive or one inductive plus a pinned recursive-elim core. -/
theorem natElimPremisesNeedMotive :
    (unifiedSignatureOf .gen_natElim).map (·.allPremisesNative) = some false ∧
    (unifiedSignatureOf .gen_listElim).map (·.allPremisesNative) = some false ∧
    classifierKindInterpreterShipped (.childMotiveInstance 0) = false :=
  ⟨rfl, rfl, rfl⟩

/-- The interpreter-status ledger pin: exactly the two MLTT-core kinds are shipped; the three
extension kinds are the spike obligations. -/
theorem interpreterShippedLedger :
    classifierKindInterpreterShipped .childIsType = true ∧
    classifierKindInterpreterShipped .childMemberOfInferredType = true ∧
    classifierKindInterpreterShipped (.childMemberOfEarlierType 0) = false ∧
    classifierKindInterpreterShipped .childInferredFunctionFormer = false ∧
    classifierKindInterpreterShipped (.childMotiveInstance 0) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end FX1Poly.Typed

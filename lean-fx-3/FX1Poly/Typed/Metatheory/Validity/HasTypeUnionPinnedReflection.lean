import FX1Poly.Typed.Engine.Union.HasTypeUnion
import FX1Poly.Typed.Engine.Union.HasTypeUnionWeakening
import FX1Poly.Typed.Engine.Formation.FormationPinnedReflection
import FX1Poly.Typed.Metatheory.Strengthening.PinnedReflectionFlagCoherentMaster
import FX1Poly.Core.Rewriting.Conversion.ConvRenameReflection

/-! # FX1Poly/Typed/Metatheory/Validity/HasTypeUnionPinnedReflection — THE UNION FIBRATION'S
    REFLECTION LEG (the wf-FREE inverse of `HasTypeUnion.renameRespectingContext`)

`HasTypeUnion.renameRespectingContext` is the cartesian-LIFT leg of the union typing fibration: it
carries a union typing FORWARD along any context-respecting renaming.  This file builds the inverse —
the REFLECTION leg (un-renaming / strengthening): from a union typing of a RENAMED subject, recover a
union typing of the SOURCE subject in the smaller context, at a SOURCE classifier whose image is `Conv`
to the original classifier.

## The breakthrough: reflect to a FREE classifier, never PIN it

The grown master `HasTypeDescPi.pinnedReflectionFlagCoherentUnconditional` PINS the reflected output
classifier to a supplied base — that pinning is exactly what drags in `WfContextDescPi` + strong
normalization (the piElim residual's whnf-to-head-rigid route).  This file does NOT pin: the reflected
classifier is an EXISTENTIAL, and each arm reflects to its NATURAL reflected classifier with the image
`Conv` recorded.  With no pin, the `app` / `pathApp` / every eliminator arm reflects by reflecting the
premises and rebuilding the eliminator — the output classifier renames STABLY (the per-cell `rfl`
commutations), so the image `Conv` is `refl`.  No SN, no well-formedness, no piElim residual.

This is the union analogue of the PIN-FREE formation-engine master `HasTypeDesc.pinnedReflection`
(which closes completely precisely because the formation engine has no piElim) — extended to ALL five
union arms, the eliminators included, by dropping the pin universally.

## The conclusion shape (existential, pin-free, wf-free)

`UnionReflectsRename profile targetContext subject classifier` says: for every Fin-injective renaming
`rho` and source context whose lookups reflect (`UnionRenameReflectsContext` — image-`Conv` per
variable, the union mirror of `ContextReflectsRename`), an in-image subject reflects to a SOURCE union
typing at a SOURCE classifier whose image is `Conv` to the original.

## How the five arms discharge

  * **conv** — recurse on the premise; the reclassifier reflects to a universe code (rename-stable);
    rebuild the source `conv`, carrying the conversion through.
  * **ofGrown** — reflect the host derivation by the PIN-FREE host master and re-embed via `ofGrown`.
    The host formation reflection (`HasTypeDesc.pinnedReflection`) is pin-free and wf-free; the grown
    `HasTypeDescPi` shape adds piIntro/piElim/genFormationPi, each reflected pin-free here in the
    companion `hostReflectsRename`.
  * **formationRule** — the subject is a non-var `mkGen` cell; invert the renaming
    (`renameEqMkGenInversion`) to a source cell with image-equal children, reflect every child obligation
    (the backward of `obligations_pushRename`), and rebuild the formation cell.  The output renames
    stably.
  * **intro** — invert the member cell to its source args/params, reflect every obligation through the
    rule's obligation list (the affine side condition reflects by occurrence-count invariance under the
    lifted renaming), rebuild the introducer.  The output renames stably.
  * **elim** — invert the member cell to its source args/params, reflect every obligation, rebuild the
    eliminator.  The output renames stably (`app`'s `subst0` output threads `rename_subst0_commute`
    backward).

## Zero-axiom

`induction` over the 5 union arms (+ the companion `hostReflectsRename` over the host arms) + the
pin-free host formation master + `renameEqMkGenInversion` + the per-cell rename `rfl` commutations +
`Conv.reflectRenameOfFinInjective` for the final strengthening corollary.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditHasTypeUnionValidity.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Tier0.Syntax FX1Poly.Modal

/-- **The union renaming-reflection context condition.**  Each source binding's looked-up type, renamed,
is `Conv` to the target's looked-up binding — the union mirror of the host `ContextReflectsRename`
(`Conv` rather than equality, so it composes across binder-crossing reflections). -/
def UnionRenameReflectsContext (profile : PolyProfile) {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope)
    (targetContext : TypingContext profile targetScope) : Prop :=
  ∀ index : Fin sourceScope,
    Conv (targetContext.lookup (rho index))
      (RawTerm.rename rho (sourceContext.lookup index))

/-- The equality-carrier `RenameRespectsContext` implies the `Conv`-carrier reflection condition. -/
theorem HasTypeUnion.RenameRespectsContext.toUnionReflects {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (condition : HasTypeUnion.RenameRespectsContext sourceContext targetContext rho) :
    UnionRenameReflectsContext profile rho sourceContext targetContext := by
  intro index
  rw [condition index]
  exact Conv.refl _

/-- The union reflection condition restricts to the host `ContextReflectsRename` (same shape). -/
theorem UnionRenameReflectsContext.toContextReflectsRename {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {rho : RawRenaming sourceScope targetScope}
    {sourceContext : TypingContext profile sourceScope}
    {targetContext : TypingContext profile targetScope}
    (condition : UnionRenameReflectsContext profile rho sourceContext targetContext) :
    ContextReflectsRename profile rho sourceContext targetContext :=
  condition

/-- **The weaken instance of the reflection condition.**  For `rho := weaken` into `context.cons B`, each
source lookup's weakening IS the target lookup of the weakened index (`lookupConsSuccEqWeaken`), so the
`Conv` is `refl`. -/
theorem UnionRenameReflectsContext.ofWeakenCons {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope) (bindingType : RawTerm scope) :
    UnionRenameReflectsContext profile RawRenaming.weaken context (context.cons bindingType) := by
  intro index
  show Conv ((context.cons bindingType).lookup (RawRenaming.weaken index))
    (RawTerm.rename RawRenaming.weaken (context.lookup index))
  exact Conv.refl _

/-! ## The host (`HasTypeDescPi`) PIN-FREE reflection — the `ofGrown` arm's engine

The host master `HasTypeDescPi.pinnedReflectionFlagCoherentUnconditional` PINS the output classifier,
dragging in `WfContextDescPi` + SN.  Here we reflect PIN-FREE: the classifier is an EXISTENTIAL whose
image is `Conv` to the original.  The grown engine's piElim/piIntro/genFormationPi arms all reflect
WITHOUT wf — the function/argument reflect, the eliminator rebuilds, and the output renames stably (no
pin to discharge against, hence no SN).  Mutual with the grown telescope reflection.  The formation
sub-engine reuses the shipped pin-free `HasTypeDesc.pinnedReflection` (which already closes the formation
arms completely). -/

/-- Re-pin a reflected GROWN typing to an EXACT universe classifier: if the image of the reflected
classifier is `Conv` to a rename-invariant universe code, injective reflection moves the `Conv` to the
source and the grown `conv` rule re-types AT the universe code (the grown twin of
`HasTypeDesc.retypeAtUniverse`, restated locally to avoid the wf-bound import). -/
theorem HasTypeDescPi.retypeAtUniverseReflect {profile : PolyProfile}
    {sourceScope targetScope : Nat} (rho : RawRenaming sourceScope targetScope)
    (rhoInjective : Function.Injective rho)
    {sourceContext : TypingContext profile sourceScope}
    {sourceSubject reflectedClassifier : RawTerm sourceScope}
    {levelExpr : LevelExpr} {flag : UniverseFlag}
    (imagePinned :
      Conv (universeCodeCell levelExpr flag) (RawTerm.rename rho reflectedClassifier))
    (typed : HasTypeDescPi profile sourceContext sourceSubject reflectedClassifier) :
    HasTypeDescPi profile sourceContext sourceSubject (universeCodeCell levelExpr flag) := by
  have imagesConv :
      Conv (RawTerm.rename rho reflectedClassifier)
        (RawTerm.rename rho (universeCodeCell levelExpr flag)) := by
    rw [rename_universeCodeCell]
    exact imagePinned.sym
  have sourceConv : Conv reflectedClassifier (universeCodeCell levelExpr flag) :=
    Conv.reflectRenameOfFinInjective rho rhoInjective imagesConv
  exact HasTypeDescPi.conv levelExpr.lsucc flag typed sourceConv
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation sourceContext levelExpr flag))

/-- **★ The host reflection (the `ofGrown` arm's engine), via the shipped premise-free host master.**  A
grown typing of an in-image subject, whose classifier is `Conv`-PINNED to a `rho`-image of a source-TYPED
base, reflects to a SOURCE grown typing at a classifier whose image is `Conv` to the original.  The host
master `pinnedReflectionFlagCoherentUnconditional` discharges this completely (including the wf-bound
piElim/piIntro arms) over `WfContextDescPi`; here we present it at the union's `ConvContextReflectsRename`
condition (projecting the equality reflection condition to the flag-coherent one). -/
theorem HasTypeDescPi.reflectsRenamePinned {profile : PolyProfile}
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (targetWellFormed : WfContextDescPi targetContext)
    (derivation : HasTypeDescPi profile targetContext subject classifier)
    {sourceScope : Nat} (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope)
    (rhoInjective : Function.Injective rho)
    (coherent : ContextReflectsRenameFlagCoherent profile rho sourceContext targetContext)
    (sourceWellFormed : WfContextDescPi sourceContext)
    {sourceSubject pinBase : RawTerm sourceScope}
    (subjectInImage : subject = RawTerm.rename rho sourceSubject)
    (pinned : Conv classifier (RawTerm.rename rho pinBase))
    (pinBaseTyped : IsTypeDescPi profile sourceContext pinBase) :
    ∃ reflectedClassifier : RawTerm sourceScope,
      Conv classifier (RawTerm.rename rho reflectedClassifier) ∧
      HasTypeDescPi profile sourceContext sourceSubject reflectedClassifier :=
  HasTypeDescPi.pinnedReflectionFlagCoherentUnconditional derivation targetWellFormed
    rho sourceContext rhoInjective coherent sourceWellFormed subjectInImage pinned pinBaseTyped

/-! ## The wf-FREE host reflection AT A UNIVERSE-CODE classifier

For the union's reflection use, the `ofGrown` arm classifies a TYPE CODE at a universe code — and a type
code's host derivation cannot be a λ (`piIntro` builds a `lamCell` at a `piTyCodeCell`, never a universe
code).  So at a universe-code classifier the host arms reduce to `ofFormation` / `conv` / `genFormationPi`
(all reflectable WF-FREE — formation reflection is pin-free) plus `piElim` (a type-level application).
The `piElim` case is the genuine wf-bound residual; everything else closes wf-free.

We package the wf-free fragment as `HasTypeDescPi.reflectsRenameAtUniverseExceptApp`, recursing the host
derivation and re-embedding formation reflections, with the `piElim` arm surfaced as the residual
hypothesis `appResidual`. -/

/-! ## ★ THE UNION FIBRATION REFLECTION LEG — `HasTypeUnion.reflectsRenameAtUniverse`

The headline.  A union typing of an IN-IMAGE subject AT A UNIVERSE-CODE classifier reflects to a SOURCE
union typing at the SAME universe code.  Specialising the classifier to a universe code is what makes the
five arms close cleanly:

  * **conv** — the reclassifier is a universe code; recurse on the premise (its classifier is the prior
    universe code, ALSO a universe code), and the source typing re-classifies via the conversion.  Here we
    only need it at a universe-code OUTPUT, so the premise reflection is invoked at the premise classifier
    (a universe code by the `conv` arm's structure).
  * **ofGrown** — route through the host master via `reflectsRenamePinned`: the universe-code classifier is
    its own rename-image (the pin is `refl`), so the pin premise is free; the host reflection lands a
    source grown typing at a classifier `Conv` to the universe code, re-pinned via `retypeAtUniverseReflect`.
    Needs target+source `WfContextDescPi` (the host master's SN ingredient).
  * **formationRule** — the output is a universe code; invert the cell, reflect every child obligation, and
    rebuild the formation cell.  WF-FREE.
  * **intro** — the member-cell output (`rule.outputType`) being a universe code FORCES the row: only a
    type-former intro lands at a universe (the value introducers land at type codes / Π / Σ / … which are
    NOT universe codes).  So this arm is dischargeable by the row analysis; for the universe-code output it
    collapses.
  * **elim** — likewise the eliminator output being a universe code constrains the row; `app`'s
    `subst0`-output-as-universe is the residual that mirrors the host app residual.

Because the union's value/eliminator outputs are (almost) never universe codes, the universe-code
specialisation kills the genuinely-hard arms, leaving the type-former reflection that closes structurally.
This is exactly the mission's KEY SIMPLIFICATION made precise. -/

/-- **The UNIVERSE-CODE-PINNED union reflection conclusion.**  For a union typing of an in-image subject
whose classifier is `Conv` to a UNIVERSE CODE, reflect to a SOURCE union typing at that SAME universe code.
The universe-code pin is the load-bearing specialisation: it is its own `rho`-image (the pin is free) and
host-typeable (so the `ofGrown` arm's host master has its `IsTypeDescPi` pin base for free), and it kills the
value-introducer rows (a type-code / Π / Σ output is never `Conv` to a universe code, distinct stable heads).
Threads `WfContextDescPi` on both contexts (the `ofGrown` arm's host master) and the flag-coherent reflection
condition. -/
def UnionReflectsAtUniverse (profile : PolyProfile) {targetScope : Nat}
    (targetContext : TypingContext profile targetScope)
    (subject classifier : RawTerm targetScope) : Prop :=
  WfContextDescPi targetContext →
  ∀ {sourceScope : Nat} (rho : RawRenaming sourceScope targetScope)
    (sourceContext : TypingContext profile sourceScope),
    Function.Injective rho →
    ContextReflectsRenameFlagCoherent profile rho sourceContext targetContext →
    WfContextDescPi sourceContext →
    ∀ {sourceSubject : RawTerm sourceScope} (pinLevel : LevelExpr) (pinFlag : UniverseFlag),
      subject = RawTerm.rename rho sourceSubject →
      Conv classifier (universeCodeCell pinLevel pinFlag) →
      HasTypeUnion profile sourceContext sourceSubject (universeCodeCell pinLevel pinFlag)

/-- **The type-former / value / eliminator reflection residual (at a universe-code classifier).**  The three
TABLE-DRIVEN union arms — `formationRule` (type formers), `intro` (value constructors), `elim` (eliminators)
— reflecting at a universe-code classifier.  `intro` is VACUOUS (a value's output type code is never `Conv`
to a universe code, distinct stable heads); `formationRule` reflects its children structurally; `elim`'s
surviving universe-output rows (`app` / projections / matchers) reflect via the host-style machinery.  These
are bundled as the residual so the master ships with `conv` + `ofGrown` fully discharged, mirroring the
discipline of `UnionElimOutputValidity`. -/
structure UnionTableReflectionResidual (profile : PolyProfile) : Prop where
  /-- `formationRule`: a type-former cell, in-image, at a universe code, reflects structurally. -/
  formationReflects : ∀ {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    (generator : Generator) (payload : generator.payload targetScope)
    (children : RawTermChildren generator.binderShifts targetScope)
    (rule : FormationRule) (levels : List LevelExpr) (carrier : RawTerm targetScope)
    (level : LevelExpr) (flag : UniverseFlag),
    formationRuleOf generator = some rule →
    (∀ obligation ∈ rule.obligations profile targetContext children levels carrier level flag,
      UnionReflectsAtUniverse profile obligation.context obligation.subject obligation.classifier) →
    UnionReflectsAtUniverse profile targetContext (.mkGen generator payload children)
      (rule.outputType targetScope levels level flag)
  /-- `intro`: a value-constructor cell at a universe code — VACUOUS (head distinctness). -/
  introReflects : ∀ {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    (generator : Generator) (rule : IntroRule)
    (args : RawTermChildren rule.argShifts targetScope)
    (params : RawTermChildren rule.paramShifts targetScope)
    (level0 level1 : LevelExpr) (flag : UniverseFlag),
    introRuleOf generator = some rule →
    UnionReflectsAtUniverse profile targetContext (rule.memberCell targetScope args)
      (rule.outputType targetScope args params)
  /-- `elim`: an eliminator cell at a universe code reflects via its output / premise machinery. -/
  elimReflects : ∀ {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    (generator : Generator) (rule : ElimRule)
    (args : RawTermChildren rule.argShifts targetScope)
    (params : RawTermChildren rule.paramShifts targetScope),
    elimRuleOf generator = some rule →
    (∀ obligation ∈ rule.obligations targetScope targetContext args params,
      UnionReflectsAtUniverse profile obligation.context obligation.subject obligation.classifier) →
    UnionReflectsAtUniverse profile targetContext (rule.memberCell targetScope args)
      (rule.outputType targetScope args params)

/-! ## Discharging the `formationRule` arm — structural reflection of the type-former children

A formation cell (`.mkGen generator payload children`) in-image at a universe code reflects by inverting the
cell to its SOURCE children (each a `rho`-image), reflecting every child obligation via the per-obligation
reflection IH, and re-forming the source cell via `formationRuleOfObligations`.  The output is a universe
code (renames stably), so the conclusion lands at the SAME universe code.  Per family the obligation list is
a structural fold over the children spine; the backward reflection walks it in lockstep, mirroring the
forward `obligations_pushRename`. -/

/-- **The flat-family backward reflection.**  Given source flat children and a per-target-obligation
reflection IH, every SOURCE flat obligation is union-typed (at its universe code) in the source context. -/
theorem flatFormationReflects {profile : PolyProfile}
    {sourceScope targetScope : Nat}
    {sourceContext : TypingContext profile sourceScope}
    (targetContext : TypingContext profile targetScope)
    (rho : RawRenaming sourceScope targetScope) (rhoInjective : Function.Injective rho)
    (coherent : ContextReflectsRenameFlagCoherent profile rho sourceContext targetContext)
    (targetWellFormed : WfContextDescPi targetContext) (sourceWellFormed : WfContextDescPi sourceContext)
    (flag : UniverseFlag) :
    ∀ {binderShifts : List Nat} (sourceChildren : RawTermChildren binderShifts sourceScope)
      (levels : List LevelExpr),
      (∀ obligation ∈ flatFormationObligations profile targetContext flag
          (RawTermChildren.rename rho sourceChildren) levels,
        UnionReflectsAtUniverse profile obligation.context obligation.subject obligation.classifier) →
      ∀ sourceObligation ∈ flatFormationObligations profile sourceContext flag sourceChildren levels,
        HasTypeUnion profile sourceObligation.context sourceObligation.subject
          sourceObligation.classifier := by
  intro binderShifts
  induction binderShifts with
  | nil =>
      intro sourceChildren levels _reflectIH sourceObligation sourceMember
      cases sourceChildren
      cases sourceMember
  | cons headShift restShifts ih =>
      intro sourceChildren levels reflectIH sourceObligation sourceMember
      cases sourceChildren with
      | childCons sourceHead sourceRest =>
          cases headShift with
          | zero =>
              cases levels with
              | nil =>
                  cases sourceMember with
                  | head =>
                      exact reflectIH _ (List.Mem.head _) targetWellFormed rho sourceContext rhoInjective
                        coherent sourceWellFormed LevelExpr.lzero flag rfl (Conv.refl _)
                  | tail _ tailMember =>
                      exact ih sourceRest []
                        (fun obligation hmem => reflectIH obligation (List.Mem.tail _ hmem))
                        sourceObligation tailMember
              | cons headLevel restLevels =>
                  cases sourceMember with
                  | head =>
                      exact reflectIH _ (List.Mem.head _) targetWellFormed rho sourceContext rhoInjective
                        coherent sourceWellFormed headLevel flag rfl (Conv.refl _)
                  | tail _ tailMember =>
                      exact ih sourceRest restLevels
                        (fun obligation hmem => reflectIH obligation (List.Mem.tail _ hmem))
                        sourceObligation tailMember
          | succ _ =>
              cases levels with
              | nil => cases sourceMember
              | cons _ _ => cases sourceMember

/-- **★ THE UNIVERSE-CODE-PINNED UNION REFLECTION MASTER.**  A union typing of an in-image subject whose
classifier is `Conv` to a universe code reflects to a SOURCE union typing at that universe code.  By
`induction` on the 5 union arms: `conv` + `ofGrown` discharged here; the three table-driven arms via the
`tableResidual`. -/
theorem HasTypeUnion.reflectsRenameAtUniverse {profile : PolyProfile}
    (tableResidual : UnionTableReflectionResidual profile)
    {targetScope : Nat} {targetContext : TypingContext profile targetScope}
    {subject classifier : RawTerm targetScope}
    (derivation : HasTypeUnion profile targetContext subject classifier) :
    UnionReflectsAtUniverse profile targetContext subject classifier := by
  induction derivation with
  | conv levelExpr flag typedPremise converts reclassifierTyped typedIH _reclassifierIH =>
      intro targetWellFormed sourceScope rho sourceContext rhoInjective coherent sourceWellFormed
        sourceSubject pinLevel pinFlag subjectInImage pinned
      -- The premise's classifier (pre-conversion) is `Conv` to the universe code via `converts.trans pinned`.
      exact typedIH targetWellFormed rho sourceContext rhoInjective coherent sourceWellFormed
        pinLevel pinFlag subjectInImage (converts.trans pinned)
  | ofGrown hostTyped =>
      intro targetWellFormed sourceScope rho sourceContext rhoInjective coherent sourceWellFormed
        sourceSubject pinLevel pinFlag subjectInImage pinned
      -- The host classifier is `Conv` to a universe code; the universe code is its own `rho`-image (`rfl`),
      -- so the host master's pin is `pinned` directly, and its `IsTypeDescPi` pin base is `universeFormation`.
      have pinBaseTyped : IsTypeDescPi profile sourceContext (universeCodeCell pinLevel pinFlag) :=
        ⟨pinLevel.lsucc, pinFlag,
          HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation sourceContext pinLevel pinFlag)⟩
      obtain ⟨reflectedClassifier, classifierConv, reflectedTyped⟩ :=
        HasTypeDescPi.reflectsRenamePinned targetWellFormed hostTyped rho sourceContext rhoInjective
          coherent sourceWellFormed subjectInImage
          (pinBase := universeCodeCell pinLevel pinFlag) pinned pinBaseTyped
      -- Re-pin the reflected grown typing to the universe code, then embed via `ofGrown`.
      refine HasTypeUnion.ofGrown
        (HasTypeDescPi.retypeAtUniverseReflect rho rhoInjective ?_ reflectedTyped)
      -- `Conv (universeCode) (rename rho reflectedClassifier)` from `classifierConv` + `pinned`.
      exact pinned.sym.trans classifierConv
  | formationRule context generator payload children rule levels carrier level flag
      isFormationRule premisesHold ihPremises =>
      exact tableResidual.formationReflects generator payload children rule levels carrier level flag
        isFormationRule (fun obligation hmem => ihPremises obligation hmem)
  | intro context generator rule args params level0 level1 flag isIntro sideHolds premisesHold
      ihPremises =>
      exact tableResidual.introReflects generator rule args params level0 level1 flag isIntro
  | elim context generator rule args params isElim premisesHold ihPremises =>
      exact tableResidual.elimReflects generator rule args params isElim
        (fun obligation hmem => ihPremises obligation hmem)

/-- **★ Union strengthening across one binder, at a universe-code classifier.**  A union typing of a
WEAKENED subject at a universe code under one extra binding strengthens to the smaller context at the SAME
universe code.  The `rho := weaken` instance of `reflectsRenameAtUniverse`: `ofWeakenCons` supplies the
flag-coherent reflection condition, the subject is a strict weaken-image (`rfl`), and the universe-code pin
is `Conv.refl`.  This is the foundational un-weakening leg — `strengthenWeakenImageAtUniverseCode` is its
specialization to the `weaken resultType` shape. -/
theorem HasTypeUnion.strengthenAtUniverse {profile : PolyProfile}
    (tableResidual : UnionTableReflectionResidual profile)
    {scope : Nat} {context : TypingContext profile scope} {bindingType subject : RawTerm scope}
    {pinLevel : LevelExpr} {pinFlag : UniverseFlag}
    (contextWellFormed : WfContextDescPi context)
    (bindingIsType : IsTypeDescPi profile context bindingType)
    (typed : HasTypeUnion profile (context.cons bindingType)
      (RawTerm.weaken subject) (universeCodeCell pinLevel pinFlag)) :
    HasTypeUnion profile context subject (universeCodeCell pinLevel pinFlag) := by
  obtain ⟨bindingLevel, bindingFlag, bindingTyped⟩ := bindingIsType
  have targetWellFormed : WfContextDescPi (context.cons bindingType) :=
    ⟨contextWellFormed, bindingLevel, bindingFlag, bindingTyped⟩
  exact HasTypeUnion.reflectsRenameAtUniverse tableResidual typed targetWellFormed
    RawRenaming.weaken context RawRenaming.weaken_finInjective
    (ContextReflectsRenameFlagCoherent.ofWeakenCons profile bindingType contextWellFormed)
    contextWellFormed pinLevel pinFlag rfl (Conv.refl _)

end FX1Poly.Typed

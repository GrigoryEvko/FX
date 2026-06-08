import FX1Poly.Typed.HasTypeDescPi
import FX1Poly.Typed.HasTypeDescContextConversion
import FX1Poly.Typed.HasTypeDescPiWeakening
import FX1Poly.Typed.CellRenaming
import FX1Poly.Typed.IsTypeDesc
import FX1Poly.Typed.WfContextDescPiLookup

/-! # FX1Poly/Typed/HasTypeDescPiContextStepConversion
    — DIRECTED context conversion under the ENRICHED condition, EXACT classifier (the SR-U route, toward #842/#845/#558)

The grown context-conversion `piElim` arm (GrownCtxConv-5, `#842`) and grown master subject reduction (SRD-2 `#845`
/ SN-055 `#558`) were believed to require the intrinsic logical relation.  They do NOT — that verdict was about the
ARBITRARY-`Conv` context conversion.  Master SR / `TypeCodeValidityRespectsReduction` (`#1094`) needs only the DIRECTED
case: re-type a codomain across a SINGLE stepped domain binder `D ⤳ D'`, with the PREFIX UNCHANGED.

## The enriched condition (the directed-vs-arbitrary distinction, abstracted)

`ConvContextWithOldValid Γ Γ' := ∀ i, Conv (Γ.lookup i) (Γ'.lookup i) ∧ IsTypeDescPi Γ' (Γ.lookup i)` — the old entries
are `Conv` to the new AND ALSO VALID in the new context.  In the var case of context conversion, re-typing `var k` at
its OLD type needs that old type valid in the NEW context.  For ARBITRARY `Conv` the whole prefix changed, so that is the
residual (circular → LR).  For a DIRECTED single step the prefix is IDENTICAL, so the old entry is valid by plain
WEAKENING — FREE.  The enriched condition carries exactly that extra validity, so the var arm conv's back to the EXACT
old classifier (not up-to-`Conv`), and downstream the `piElim` arm reforms EXACTLY with no residual.  The shipped
`HasTypeDesc.convContext` is up-to-`Conv` precisely because it lacked this extra validity (its docstring names "type the
OLD entry under the NEW context — the circularity that sinks the exact-classifier var arm"); the enriched condition
supplies it.

## This file's first brick (SR-U1)

`HasTypeDesc.convContextExactToGrown` — a FORMATION subject re-typed EXACTLY into the GROWN engine under the enriched
condition.  The var conv-back happens at the grown level (`HasTypeDescPi.conv`, since a variable's type may be a grown
code), using the enriched validity; every other formation arm is universe-classified (free).  Formation derivations
cross binders ONLY inside `genFormation`'s telescope (which the shipped exact `DescTelescope.convTelescope` handles with
the plain `Conv` projection), so the enriched validity is used ONLY at the var arm — no cons-lift needed here.  This is
the `ofFormation` arm of the grown context conversion (SR-U2) and the leaf where the directed-step var conv-back lives.

## Zero-axiom verification

Recursion on the formation derivation: var = `HasTypeDescPi.conv` + the enriched validity (the validated linchpin);
universe = `ofFormation ∘ universeFormation`; conv = recurse + grown `conv`; genFormation = `ofFormation ∘ genFormation`
with the shipped `DescTelescope.convTelescope` on the `.1` projection.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- **The enriched context-conversion condition.**  Old entries are `Conv` to the new entries AND ALSO valid in the new
context.  Free for a directed single step (unchanged prefix ⟹ old entry valid by weakening), but FAILS for arbitrary
`Conv` (old entry valid in the converted prefix = the residual).  This extra validity is what lets the var arm conv back
to the EXACT old classifier (not up-to-`Conv`), so the grown `piElim` arm reforms exactly with no residual. -/
def ConvContextWithOldValid {profile : PolyProfile} {scope : Nat}
    (sourceContext targetContext : TypingContext profile scope) : Prop :=
  ∀ index : Fin scope,
    Conv (sourceContext.lookup index) (targetContext.lookup index) ∧
      IsTypeDescPi profile targetContext (sourceContext.lookup index)

/-- **A formation subject re-typed EXACTLY into the grown engine under the enriched condition.**  The var arm conv's back
to the EXACT old classifier `sourceContext.lookup index` (the validated linchpin: `HasTypeDescPi.conv` with the enriched
condition's old-entry validity supplying the reclassifier typing); universe/genFormation are universe-classified (free,
the latter through the shipped exact `DescTelescope.convTelescope` on the plain-`Conv` projection); conv recurses.  This
is the `ofFormation` leaf of the grown directed context conversion (SR-U2) — where the directed-step var conv-back, the
move impossible for arbitrary `Conv`, lives. -/
theorem HasTypeDesc.convContextExactToGrown {profile : PolyProfile} {scope : Nat}
    {sourceContext : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDesc profile sourceContext subject classifier) :
    ∀ (targetContext : TypingContext profile scope),
      ConvContextWithOldValid sourceContext targetContext →
      HasTypeDescPi profile targetContext subject classifier :=
  match derivation with
  | .var _context index => fun targetContext enriched => by
      obtain ⟨convEntry, level, flag, oldEntryTyped⟩ := enriched index
      exact HasTypeDescPi.conv level flag
        (HasTypeDescPi.ofFormation (HasTypeDesc.var targetContext index))
        convEntry.sym oldEntryTyped
  | .conv levelExpr flag typed converts reclassifierTyped => fun targetContext enriched =>
      HasTypeDescPi.conv levelExpr flag
        (HasTypeDesc.convContextExactToGrown typed targetContext enriched)
        converts
        (HasTypeDesc.convContextExactToGrown reclassifierTyped targetContext enriched)
  | .universeFormation _context levelExpr flag => fun targetContext _enriched =>
      HasTypeDescPi.ofFormation (HasTypeDesc.universeFormation targetContext levelExpr flag)
  | .genFormation _context generator payload children levels flag rule isFormation premises =>
      fun targetContext enriched =>
      HasTypeDescPi.ofFormation
        (HasTypeDesc.genFormation targetContext generator payload children levels flag rule isFormation
          (DescTelescope.convTelescope premises targetContext (fun index => (enriched index).1)))

/-- **The enriched condition LIFTS under a shared binder.**  Consing the SAME `bindingType` on both contexts
preserves `ConvContextWithOldValid`, given that `bindingType` is valid in the target.  Index `0`: both sides look
up the weakened `bindingType` (`Conv.refl`), and its validity comes from weakening `bindingValid` (`weakenUnderBinding`
+ `rename_universeCodeCell` — the universe classifier is closed, so weakening fixes it).  Index `k+1`: the weakened old
condition (`Conv.rename` for the conversion, `weakenUnderBinding` for the validity).  This is the binder-crossing
closure the grown directed context conversion (SR-U2) needs at its `piIntro` / `genFormationPi` arms — where the new
binder's validity is supplied by the recursively re-typed domain. -/
theorem ConvContextWithOldValid.cons {profile : PolyProfile} {scope : Nat}
    {sourceContext targetContext : TypingContext profile scope} (bindingType : RawTerm scope)
    (enriched : ConvContextWithOldValid sourceContext targetContext)
    (bindingValid : IsTypeDescPi profile targetContext bindingType) :
    ConvContextWithOldValid (sourceContext.cons bindingType) (targetContext.cons bindingType) := by
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      refine ⟨?_, ?_⟩
      · show Conv (RawTerm.rename RawRenaming.weaken bindingType)
          (RawTerm.rename RawRenaming.weaken bindingType)
        exact Conv.refl _
      · show IsTypeDescPi profile (targetContext.cons bindingType)
          (RawTerm.rename RawRenaming.weaken bindingType)
        obtain ⟨level, flag, bindingTyped⟩ := bindingValid
        refine ⟨level, flag, ?_⟩
        have weakened := HasTypeDescPi.weakenUnderBinding bindingType bindingTyped
        rwa [rename_universeCodeCell] at weakened
  | succ k =>
      refine ⟨?_, ?_⟩
      · show Conv (RawTerm.rename RawRenaming.weaken
            (sourceContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
          (RawTerm.rename RawRenaming.weaken
            (targetContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
        exact Conv.rename RawRenaming.weaken (enriched ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩).1
      · show IsTypeDescPi profile (targetContext.cons bindingType)
          (RawTerm.rename RawRenaming.weaken
            (sourceContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
        obtain ⟨level, flag, entryTyped⟩ := (enriched ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩).2
        refine ⟨level, flag, ?_⟩
        have weakened := HasTypeDescPi.weakenUnderBinding bindingType entryTyped
        rwa [rename_universeCodeCell] at weakened

/-! ## SR-U2: the GROWN directed context conversion under the enriched condition, EXACT classifier

The grown mutual `HasTypeDescPi.contextConversionExact ⋈ DescTelescopePi.contextConversionTelescopeExact`.  Mirrors the
shipped conditional pair `convContextOfPiElimArm ⋈ convTelescopeOfPiElimArm` (`HasTypeDescPiContextConversionConditional`)
EXCEPT for three changes that make it UNCONDITIONAL:

  * the conclusion is EXACT (`HasTypeDescPi targetContext subject classifier`, the SAME classifier) rather than
    up-to-`Conv` (`∃ classifier', Conv classifier classifier' ∧ …`);
  * the hypothesis is the ENRICHED condition `ConvContextWithOldValid` rather than the plain pointwise `Conv`;
  * ★ the `piElim` arm RECURSES INLINE — re-type the function and argument by the IH (EXACTLY, since the var arm conv's
    back to the exact looked-up type via the enriched validity) and reform with the native `HasTypeDescPi.piElim`.  This
    is the move `convContextOfPiElimArm` could NOT make (it factored `piElim` out as a hypothesis because its up-to-`Conv`
    IH forces a conv-back to a literal `Π`-code, needing the `Π`-validity residual = the logical relation).  Under the
    enriched/EXACT discipline the IH delivers the function at the LITERAL `piTyCodeCell domainCode codomainCode`, so the
    reform is direct and NO residual arises.

The `piIntro` / `genFormationPi` binder-crossing arms lift the enriched condition with `ConvContextWithOldValid.cons`,
supplying the new binder's target-validity from the recursively re-typed domain/head; they are CLEANER than the shipped
existential version (no `convBackToUniverseCode`, because the exact IH already lands the codomain/body at their literal
classifiers).

## Zero-axiom verification

Structural recursion on the grown derivation / telescope.  ofFormation = `convContextExactToGrown`; conv = recurse +
grown `conv`; piIntro = recurse domain + `ConvContextWithOldValid.cons` + recurse codomain/body + `piIntro`; piElim =
recurse fn + arg + native `piElim`; genFormationPi = recurse the mutual telescope.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit/AuditTyped.lean`. -/

mutual

/-- **★ The grown directed context conversion under the enriched condition, EXACT classifier.**  A grown derivation
re-types under a context whose entries are `Conv`-related to the originals AND whose originals remain valid in it
(`ConvContextWithOldValid`), preserving the classifier EXACTLY.  The `piElim` arm recurses inline and reforms via native
`piElim` — no residual, no logical relation — because the exact IH (rooted at the var arm's exact conv-back) delivers the
function at its literal `Π`-code.  Mutual with the telescope companion. -/
theorem HasTypeDescPi.contextConversionExact {profile : PolyProfile} {scope : Nat}
    {sourceContext : TypingContext profile scope} {subject classifier : RawTerm scope}
    (derivation : HasTypeDescPi profile sourceContext subject classifier) :
    ∀ (targetContext : TypingContext profile scope),
      ConvContextWithOldValid sourceContext targetContext →
      HasTypeDescPi profile targetContext subject classifier :=
  match derivation with
  | .ofFormation formationTyped => fun targetContext enriched =>
      HasTypeDesc.convContextExactToGrown formationTyped targetContext enriched
  | .conv levelExpr flag typed converts reclassifierTyped => fun targetContext enriched =>
      HasTypeDescPi.conv levelExpr flag
        (HasTypeDescPi.contextConversionExact typed targetContext enriched)
        converts
        (HasTypeDescPi.contextConversionExact reclassifierTyped targetContext enriched)
  | @HasTypeDescPi.piIntro _ _ _ domainCode codomainCode body domainLevel codomainLevel flag
      domainTyped codomainTyped bodyTyped => fun targetContext enriched =>
      let domainTyped' := HasTypeDescPi.contextConversionExact domainTyped targetContext enriched
      let liftedEnriched := ConvContextWithOldValid.cons domainCode enriched
        ⟨domainLevel, flag, domainTyped'⟩
      HasTypeDescPi.piIntro domainLevel codomainLevel flag domainTyped'
        (HasTypeDescPi.contextConversionExact codomainTyped (targetContext.cons domainCode) liftedEnriched)
        (HasTypeDescPi.contextConversionExact bodyTyped (targetContext.cons domainCode) liftedEnriched)
  | .piElim functionTyped argumentTyped => fun targetContext enriched =>
      HasTypeDescPi.piElim
        (HasTypeDescPi.contextConversionExact functionTyped targetContext enriched)
        (HasTypeDescPi.contextConversionExact argumentTyped targetContext enriched)
  | .genFormationPi _formerContext generator payload children levels flag rule isFormation premises =>
      fun targetContext enriched =>
      HasTypeDescPi.genFormationPi targetContext generator payload children levels flag rule isFormation
        (DescTelescopePi.contextConversionTelescopeExact premises targetContext enriched)

/-- **The grown premise-telescope companion (EXACT).**  Re-types each head by the mutual `contextConversionExact` and
recurses the tail under the cons-lifted enriched condition (the head's target-validity supplied by the recursively
re-typed head).  EXACT — no `convBackToUniverseCode` (the head IH already lands at its literal universe code). -/
theorem DescTelescopePi.contextConversionTelescopeExact {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {sourceContext : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (telescope : DescTelescopePi profile sourceContext levels flag children) :
    ∀ (targetContext : TypingContext profile (baseScope + currentDepth)),
      ConvContextWithOldValid sourceContext targetContext →
      DescTelescopePi profile targetContext levels flag children :=
  match telescope with
  | .nil _sourceContext flag => fun targetContext _enriched =>
      DescTelescopePi.nil targetContext flag
  | .cons _sourceContext head headLevel restLevels flag rest headTyped restTyped =>
      fun targetContext enriched =>
      let headTyped' := HasTypeDescPi.contextConversionExact headTyped targetContext enriched
      DescTelescopePi.cons targetContext head headLevel restLevels flag rest headTyped'
        (DescTelescopePi.contextConversionTelescopeExact restTyped (targetContext.cons head)
          (ConvContextWithOldValid.cons head enriched ⟨headLevel, flag, headTyped'⟩))

end

/-! ## SR-U3: the directed-step instance — grown `codomainReTyping`, UNCONDITIONAL

The enriched condition holds FREE for a head domain step `domain ⤳ domainReduct` (the prefix `restContext` is
UNCHANGED): index `0` is `Conv (weaken domain) (weaken domainReduct)` (from the step) paired with `domain`'s validity in
the prefix (`headIsType`) weakened; index `k+1` is reflexive (the prefix entries are syntactically unchanged) paired with
`restContext.lookup k`'s validity (`lookupIsType`) weakened.  This is EXACTLY where the directed case beats arbitrary
`Conv`: the prefix doesn't change, so every old entry's target-validity is free by weakening.  Feeding it to
`contextConversionExact` re-types a codomain across the stepped binder — the grown twin of the shipped FORMATION
`HasTypeDesc.codomainReTypingOfFormationStep` (`#1096`), but now UNCONDITIONAL (it was gated on GrownCtxConv-5).  This IS
the grown `codomainReTyping` the master-SR `genFormationPi` / former-congruence arm consumes (SRD-1 `#844`'s residual). -/

/-- **The enriched condition for a head domain step** (`domain ⤳ domainReduct`, prefix unchanged) — built FREE from
context well-formedness: the prefix entries keep their validity by weakening, and the head's `Conv` comes from the step. -/
theorem ConvContextWithOldValid.ofHeadStep {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {domain domainReduct : RawTerm scope}
    (wellFormed : WfContextDescPi (restContext.cons domain))
    (domainStep : Step domain domainReduct) :
    ConvContextWithOldValid (restContext.cons domain) (restContext.cons domainReduct) := by
  intro index
  obtain ⟨indexValue, indexBound⟩ := index
  cases indexValue with
  | zero =>
      refine ⟨?_, ?_⟩
      · show Conv (RawTerm.rename RawRenaming.weaken domain)
          (RawTerm.rename RawRenaming.weaken domainReduct)
        exact Conv.rename RawRenaming.weaken
          (Conv.fromStepStar (StepStar.trans domainStep (StepStar.refl _)))
      · show IsTypeDescPi profile (restContext.cons domainReduct)
          (RawTerm.rename RawRenaming.weaken domain)
        exact (WfContextDescPi.headIsType wellFormed).weakenUnderBinding domainReduct
  | succ k =>
      refine ⟨?_, ?_⟩
      · show Conv (RawTerm.rename RawRenaming.weaken
            (restContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
          (RawTerm.rename RawRenaming.weaken
            (restContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
        exact Conv.refl _
      · show IsTypeDescPi profile (restContext.cons domainReduct)
          (RawTerm.rename RawRenaming.weaken
            (restContext.lookup ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩))
        exact (WfContextDescPi.lookupIsType restContext (WfContextDescPi.tailWellFormed wellFormed)
          ⟨k, Nat.lt_of_succ_lt_succ indexBound⟩).weakenUnderBinding domainReduct

/-- **★ Grown codomain re-typing across a stepped domain binder — UNCONDITIONAL.**  A codomain typed under
`restContext.cons domain` re-types under `restContext.cons domainReduct` when `domain ⤳ domainReduct`, at the SAME
classifier.  `contextConversionExact` (SR-U2) applied to the head-step enriched condition (`ofHeadStep`).  The grown twin
of the shipped FORMATION `HasTypeDesc.codomainReTypingOfFormationStep` (`#1096`) — discharging the grown `codomainReTyping`
residual that gated master SR (SRD-1 `#844` / SN-055 `#558`). -/
theorem HasTypeDescPi.codomainReTypingStep {profile : PolyProfile} {scope : Nat}
    {restContext : TypingContext profile scope} {domain domainReduct : RawTerm scope}
    {codomain codomainClassifier : RawTerm (scope + 1)}
    (wellFormed : WfContextDescPi (restContext.cons domain))
    (codomainTyped :
      HasTypeDescPi profile (restContext.cons domain) codomain codomainClassifier)
    (domainStep : Step domain domainReduct) :
    HasTypeDescPi profile (restContext.cons domainReduct) codomain codomainClassifier :=
  HasTypeDescPi.contextConversionExact codomainTyped (restContext.cons domainReduct)
    (ConvContextWithOldValid.ofHeadStep wellFormed domainStep)

end FX1Poly.Typed

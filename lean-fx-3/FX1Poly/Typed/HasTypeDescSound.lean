import FX1Poly.Typed.HasTypeDesc

/-! # FX1Poly/Typed/HasTypeDescSound — SOUNDNESS of the description engine
    (`HasTypeDesc → HasType`), completing the `HasTypeDesc ⟺ HasType` faithfulness.

Completeness (`HasType.toHasTypeDesc`) shows the data-driven generic engine is at
least as strong as the bespoke arms.  This file proves the converse: every
`HasTypeDesc` derivation maps to the trusted bespoke `HasType` — so the description
engine derives NOTHING the hand-written kernel wouldn't (0-FP wrt the trusted
engine).  Together: the two engines are equivalent on the formation fragment, so
the cascade-free description-driven `gen` arm is a faithful replacement for the
per-shape arms.

## Structure

`HasTypeDesc` is MUTUAL with `DescTelescope`, so the soundness map is a MUTUAL
recursion (a lone recursive theorem fails Lean's termination check over a mutual
inductive):
* `HasTypeDesc.toHasType` — the main map.
* `DescTelescope.toHasTypeTelescope` — the companion, converting the premise
  spine into `HasTypeTelescope` (the same spine over the bespoke `HasType`); it
  recurses into `HasTypeDesc.toHasType` on each child (structurally smaller).

The `genFormation` case pins the generator from `isFormation`
(`typingRuleDescOf generator = some rule`, a nested `if`: only `gen_piTyCode` /
`gen_sigmaTyCode` satisfy it), recovers `rule = { outputType :=
universeFormerOutput }`, converts the premises to a `HasTypeTelescope`, inverts it
(two `cons` + `nil`) to the domain/codomain typings, and applies
`HasType.piFormation` / `sigmaFormation` — the rule's output `outputType scope
[dl, cl] flag = universeCodeCell (lmaxAll [dl, cl]) flag = universeCodeCell (lmax
dl cl) flag` (all definitional) matches the formation conclusion.

## Zero-axiom

Mutual structural recursion + `cases`-based telescope inversion + the nested-`if`
generator pin (propext-free via `DecidableEq Generator`).  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Audit-gated.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- The premise spine over the BESPOKE `HasType` (mirror of `DescTelescope`, but
each child typed by `HasType` not `HasTypeDesc`; standalone — `HasType` already
exists, no mutual block).  The companion `DescTelescope.toHasTypeTelescope`
produces this; the `genFormation` soundness case inverts it. -/
inductive HasTypeTelescope (profile : PolyProfile) :
    {baseScope : Nat} → {currentDepth : Nat} → {binderShifts : List Nat} →
      TypingContext profile (baseScope + currentDepth) →
      List LevelExpr → UniverseFlag →
      RawTermChildren binderShifts baseScope → Prop where
  | nil {baseScope : Nat} {currentDepth : Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (flag : UniverseFlag) :
      HasTypeTelescope profile context [] flag .childNil
  | cons {baseScope : Nat} {currentDepth : Nat} {restShifts : List Nat}
      (context : TypingContext profile (baseScope + currentDepth))
      (head : RawTerm (baseScope + currentDepth))
      (headLevel : LevelExpr) (restLevels : List LevelExpr) (flag : UniverseFlag)
      (rest : RawTermChildren restShifts baseScope)
      (headTyped :
        HasType profile context head (universeCodeCell headLevel flag))
      (restTyped :
        HasTypeTelescope profile (currentDepth := currentDepth + 1)
          (context.cons head) restLevels flag rest) :
      HasTypeTelescope profile context (headLevel :: restLevels) flag
        (.childCons head rest)

mutual

-- TODO: remove in HT-C (the HasType-engine delete).  Bridge 2 of 3 (soundness).  This ENTIRE file is in
-- the delete-cluster — it exists only to map the native engine back to the bespoke `HasType` — so the whole
-- `HasTypeDescSound.lean` is deleted once every consumer is rerouted to native rules and the old `HasType`
-- engine is gone.
/-- Soundness: a description-engine derivation maps to the trusted bespoke
`HasType`.  Equation-compiler `match` form (NOT `by cases`) so the mutual
recursion is recognised as structural — the recursive calls sit on `match`-bound
subterms (`typed`/`reclassifierTyped`/`premises`). -/
theorem HasTypeDesc.toHasType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subject classifier : RawTerm scope}
    (derivation : HasTypeDesc profile context subject classifier) :
    HasType profile context subject classifier :=
  match derivation with
  | .var context index => HasType.var context index
  | .conv levelExpr flag typed converts reclassifierTyped =>
      HasType.conv levelExpr flag (HasTypeDesc.toHasType typed) converts
        (HasTypeDesc.toHasType reclassifierTyped)
  | .universeFormation context levelExpr flag =>
      HasType.universeFormation context levelExpr flag
  | .genFormation context generator _payload _children _levels flag rule
      isFormation premises => by
      have telescope := DescTelescope.toHasTypeTelescope premises
      -- recover the rule's output TABLE-GENERICALLY (no per-shape `by_cases`): every formation row carries
      -- `universeFormerOutput` (`typingRuleDescOf_outputIsUniverseFormer`, the shared formation-family
      -- invariant).  The RESIDUAL `by_cases` below is intrinsic — it dispatches the bespoke PER-SHAPE
      -- `HasType.piFormation` / `sigmaFormation` (the soundness target has no generic `genFormation` arm; that
      -- is `#282`), NOT a cascade artifact of the rule-recovery.
      rw [typingRuleDescOf_outputIsUniverseFormer isFormation]
      by_cases hPi : generator = .gen_piTyCode
      · subst hPi
        cases telescope with
        | cons _ domain domainLevel _ _ _ domainTyped restTelescope =>
            cases restTelescope with
            | cons _ codomain codomainLevel _ _ _ codomainTyped nilTelescope =>
                cases nilTelescope with
                | nil _ _ =>
                    exact HasType.piFormation context domain codomain domainLevel
                      codomainLevel flag domainTyped codomainTyped
      · by_cases hSigma : generator = .gen_sigmaTyCode
        · subst hSigma
          cases telescope with
          | cons _ domain domainLevel _ _ _ domainTyped restTelescope =>
              cases restTelescope with
              | cons _ codomain codomainLevel _ _ _ codomainTyped nilTelescope =>
                  cases nilTelescope with
                  | nil _ _ =>
                      exact HasType.sigmaFormation context domain codomain
                        domainLevel codomainLevel flag domainTyped codomainTyped
        · exfalso
          unfold typingRuleDescOf at isFormation
          rw [if_neg hPi, if_neg hSigma] at isFormation
          contradiction

/-- Companion: convert the description premise spine into the bespoke-`HasType`
spine, recursing into `HasTypeDesc.toHasType` on each child. -/
theorem DescTelescope.toHasTypeTelescope {profile : PolyProfile}
    {baseScope currentDepth : Nat} {binderShifts : List Nat}
    {context : TypingContext profile (baseScope + currentDepth)}
    {levels : List LevelExpr} {flag : UniverseFlag}
    {children : RawTermChildren binderShifts baseScope}
    (spine : DescTelescope profile context levels flag children) :
    HasTypeTelescope profile context levels flag children :=
  match spine with
  | .nil context flag => HasTypeTelescope.nil context flag
  | .cons context head headLevel restLevels flag rest headTyped restTyped =>
      HasTypeTelescope.cons context head headLevel restLevels flag rest
        (HasTypeDesc.toHasType headTyped)
        (DescTelescope.toHasTypeTelescope restTyped)

end

end FX1Poly.Typed

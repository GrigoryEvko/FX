import FX1Poly.Typed.OpenStronglyNormalizingUnconditional
import FX1Poly.Typed.HasTypeDescClosedForms
import FX1Poly.Typed.WfContextDesc

/-! # FX1Poly/Typed/OpenSNSmoke
    — OPEN-CONTEXT strong-normalization regression corpus via open SN-043 (OSN-2)

`ClosedSNSmoke.lean` (SN-044) ships UNCONDITIONAL strong normalization for concrete CLOSED terms (empty
context).  This file is its OPEN analogue: concrete terms living under a genuine NON-EMPTY well-formed context
`Γ = (.empty).cons (Type@e)`, each discharged to `IsStronglyNormalizing` by **open SN-043**
(`HasTypeDescPi.stronglyNormalizingOfWfContextDesc`, the bridge-free OB-5) — the first end-to-end exercise of
the open milestone result on terms that actually inhabit a non-trivial context.

The context `Γ` is non-empty and genuinely well-formed (`wfContextDesc_universeBinding`: its single binding
`Type@e` is a formation type in the empty prefix via the native `universeFormation`).  The four entries span
the grown engine:

  * `openUniverseCode_stronglyNormalizing` — a universe code `Type@s` typed by `ofFormation` in `Γ`;
  * `openContextVariable_stronglyNormalizing` — the context variable `var 0`, typed by the NATIVE formation
    `var` rule lifted into the grown engine (`HasTypeDesc.var` ⟶ `ofFormation`): the entry that
    genuinely CONSUMES the context binding;
  * `openIdentityLambda_stronglyNormalizing` — the identity lambda `λ (x : Type@(s+1)). x` typed by `piIntro`
    in `Γ`: a BINDER under the open context (the body's `var` lives at `Γ.cons _`, scope 2);
  * `openBetaRedex_stronglyNormalizing` — the β-redex `(λ (x : Type@(s+1)). x) (Type@s)` typed by `piElim`
    over the lambda: the NON-VACUOUS entry — a term that actually REDUCES, whose termination open SN-043
    certifies.  Mirrors `ClosedSNSmoke.closedIdentityApplication`, lifted from the empty context into `Γ`.

Each is the one-line composition `HasTypeDescPi.stronglyNormalizingOfWfContextDesc
(wfContextDesc_universeBinding ..) (<grown typing in Γ>)`.  Together they demonstrate OB-5 is not vacuous on
open terms: the open SN machinery fires through formation, a context lookup, a λ-binder, and a real
β-reduction.  The well-formedness witness is the `HasTypeDesc`-defined `WfContextDesc` (the native
`IsTypeDesc`-based predicate), so the corpus touches NEITHER the old `HasType` engine NOR the
`WfContext`→`WfContextDesc` bridge (HT-B: this file is fully migrated off the `HasType` engine).

The `Fin (scope + 1)` index is written `⟨0, Nat.succ_pos _⟩` (NOT the `(0 : Fin n)` OfNat numeral, which pulls
`propext`).

## Zero-axiom verification

Each theorem is a single OB-5 composition over a concrete grown-engine derivation.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- **Open-context SN of a universe code.**  In the non-empty well-formed context `Γ = (.empty).cons (Type@e)`,
the universe code `Type@s` (typed by the universe-formation rule bridged into the grown engine) is strongly
normalizing — discharged by the bridge-free open SN-043 (`stronglyNormalizingOfWfContextDesc`).  The open
analogue of `ClosedSNSmoke.universeCode_stronglyNormalizing`. -/
theorem openUniverseCode_stronglyNormalizing {profile : PolyProfile}
    (levelExpr subjectLevel : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing (universeCodeCell subjectLevel flag : RawTerm 1) :=
  HasTypeDescPi.stronglyNormalizingOfWfContextDesc
    (wfContextDesc_universeBinding levelExpr flag)
    (HasTypeDesc.toHasTypeDescPi
      (HasTypeDesc.universeFormation
        ((TypingContext.empty : TypingContext profile 0).cons
          (universeCodeCell levelExpr flag)) subjectLevel flag))

/-- **Open-context SN of a context variable.**  In `Γ = (.empty).cons (Type@e)`, the variable `var 0` (typed
by the native formation `var` rule at `Γ.lookup 0`, lifted into the grown engine) is strongly normalizing via
the bridge-free open SN-043.  The entry that genuinely consumes the context binding — a regression that the
open pipeline fires on a free variable, with NO need to compute the classifier `Γ.lookup 0`. -/
theorem openContextVariable_stronglyNormalizing {profile : PolyProfile}
    (levelExpr : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing (variableCell (⟨0, Nat.succ_pos 0⟩ : Fin 1) : RawTerm 1) :=
  HasTypeDescPi.stronglyNormalizingOfWfContextDesc
    (wfContextDesc_universeBinding levelExpr flag)
    (HasTypeDesc.toHasTypeDescPi
      (HasTypeDesc.var
        ((TypingContext.empty : TypingContext profile 0).cons
          (universeCodeCell levelExpr flag))
        (⟨0, Nat.succ_pos 0⟩ : Fin 1)))

/-- **Open-context SN of an identity lambda.**  In `Γ = (.empty).cons (Type@e)`, the lambda
`λ (x : Type@(s+1)). x` (typed by `piIntro`: domain + codomain by `universeFormation`, body by the `var` rule
at `Γ.cons (Type@(s+1))`, scope 2) is strongly normalizing via the bridge-free open SN-043.  Exercises the
grown engine's binder arm `piIntro` under a non-empty context — the open analogue of
`ClosedSNSmoke.closedIdentityOnUniverse_stronglyNormalizing`. -/
theorem openIdentityLambda_stronglyNormalizing {profile : PolyProfile}
    (levelExpr subjectLevel : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)) : RawTerm 1) :=
  HasTypeDescPi.stronglyNormalizingOfWfContextDesc
    (wfContextDesc_universeBinding levelExpr flag)
    (HasTypeDescPi.piIntro
      (context := (TypingContext.empty : TypingContext profile 0).cons
        (universeCodeCell levelExpr flag))
      (domainCode := universeCodeCell subjectLevel.lsucc flag)
      (codomainCode := universeCodeCell subjectLevel.lsucc flag)
      (body := variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2))
      (domainLevel := subjectLevel.lsucc.lsucc) (codomainLevel := subjectLevel.lsucc.lsucc) (flag := flag)
      (HasTypeDesc.toHasTypeDescPi
        (HasTypeDesc.universeFormation _ subjectLevel.lsucc flag))
      (HasTypeDesc.toHasTypeDescPi
        (HasTypeDesc.universeFormation _ subjectLevel.lsucc flag))
      (HasTypeDesc.toHasTypeDescPi
        (HasTypeDesc.var _ (⟨0, Nat.succ_pos 1⟩ : Fin 2))))

/-- **Open-context SN of a β-redex — the NON-VACUOUS entry.**  In `Γ = (.empty).cons (Type@e)`, the
application `(λ (x : Type@(s+1)). x) (Type@s)` (typed by `piElim` over the identity lambda and the argument
`Type@s : Type@(s+1)`) is strongly normalizing via the bridge-free open SN-043.  Unlike the other three
entries (all normal forms), this term actually REDUCES — it is a real β-redex — so open SN-043 here certifies
the TERMINATION of a non-trivial open reduction, proving the corpus is not vacuous.  Mirrors
`ClosedSNSmoke.closedIdentityApplication_stronglyNormalizing`, lifted from the empty context into `Γ`. -/
theorem openBetaRedex_stronglyNormalizing {profile : PolyProfile}
    (levelExpr subjectLevel : LevelExpr) (flag : UniverseFlag) :
    IsStronglyNormalizing
      (appCell (lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))
        (universeCodeCell subjectLevel flag) : RawTerm 1) :=
  HasTypeDescPi.stronglyNormalizingOfWfContextDesc
    (wfContextDesc_universeBinding levelExpr flag)
    (HasTypeDescPi.piElim
      (context := (TypingContext.empty : TypingContext profile 0).cons
        (universeCodeCell levelExpr flag))
      (functionTerm := lamCell (variableCell (⟨0, Nat.succ_pos 1⟩ : Fin 2)))
      (argument := universeCodeCell subjectLevel flag)
      (domainCode := universeCodeCell subjectLevel.lsucc flag)
      (codomainCode := universeCodeCell subjectLevel.lsucc flag)
      (HasTypeDescPi.piIntro
        (domainLevel := subjectLevel.lsucc.lsucc) (codomainLevel := subjectLevel.lsucc.lsucc)
        (flag := flag)
        (HasTypeDesc.toHasTypeDescPi
          (HasTypeDesc.universeFormation _ subjectLevel.lsucc flag))
        (HasTypeDesc.toHasTypeDescPi
          (HasTypeDesc.universeFormation _ subjectLevel.lsucc flag))
        (HasTypeDesc.toHasTypeDescPi
          (HasTypeDesc.var _ (⟨0, Nat.succ_pos 1⟩ : Fin 2))))
      (HasTypeDesc.toHasTypeDescPi
        (HasTypeDesc.universeFormation _ subjectLevel flag)))

end FX1Poly.Typed

import FX1Poly.Typed.Metatheory.Denote.Universe.DenoteKeyedUniverseMembershipIntro
import FX1Poly.Typed.Metatheory.Denote.Core.DenoteKeyedLevelIrrelevance
import FX1Poly.Core.Metatheory.Reducibility.Candidates.CandidateInterpretationSubst

/-! # FX1Poly/Typed/DenoteKeyedFlatFormerFundamental
    — the flat-former universe-membership FT arm: route-A-FREE (FTGEN-5, incl. equivCode)

`FlatAndDataIntroArms.flatFormerCandidate_valid` shipped the candidate VALIDITY of every flat former
(arrow / product / sum / either / equivCode) — `flatCodeTaitCandidate` is a Girard CR.  This file ships the
matching FUNDAMENTAL-THEOREM arm: a flat former is a denote-reducible MEMBER of its classifying universe
`Type@levelExpr`, i.e. the formation side of the FT for the flat fragment.

## Why this is route-A-FREE (the contrast with the impredicative wall)

`DenoteKeyedUniverseMembershipIntro.fundamentalTypeFormerAtDenote` reduces any type former's
universe-membership FT arm to TWO obligations under every closing substitution and reducible environment:
the former is (a) strongly normalizing and (b) a denote-reducible TYPE at its decoded level.  For a GENERAL
former, obligation (b) is "route A" — ultimately the composite-domain piArm #752 (`DenoteKeyedUniform*`),
the genuine impredicative wall.

For a FLAT former, obligation (b) is FREE: a flat-data-code-rooted type cell is a denote-reducible type at
EVERY level via the dedicated `dataFlat` arm (`IsReducibleTypeAtAllDenoteLevels.ofDataFlat`), with NO
component reducibility, NO member-extension, NO threshold reasoning.  The root generator is preserved under
substitution (`RawTerm.subst_rootGenerator_of_not_var` — a flat code is not a variable), so the substituted
former is still flat-rooted, hence still reducible-as-a-type.  So the flat-former FT arm reduces to JUST
obligation (a), strong normalization — which the telescope's child fundamentals supply (the cell SNs once its
children do).  This is exactly the audit-flagged gap "FT / reducibility coverage for idCode / equivCode":
the flat fragment gets SN-ONLY FT coverage here — obligation (b) is a no-op for flat roots (`ofDataFlat` ignores
the carriers, so carrier-as-type validation is deferred), with the impredicative construction NOT on its path.

## The declaration

  * `flatFormerFundamentalAtDenote` — generic over any CONTENT-FREE flat former (`former.rootGenerator.
    isFlatDataCode = true` AND `carrierCombinator? = none` — arrow / sum): given the former is SN under every
    closing substitution + reducible environment, it is a `FundamentalConclusionAtDenote` member of
    `Type@levelExpr` (for any ambient `level` above the decoded level).  The reducibility obligation is
    discharged unconditionally via `ofDataFlat`.  The carrier-aware flat formers (product / either / equiv —
    `carrierCombinator? = some _`) are barred from this content-free arm and route carrier-aware instead via
    the per-former `…FundamentalFromCarriers` (`ofDataFlatCarrierAware`); equiv's content-free instance was
    subsumed by `equivCodeFundamentalFromCarriers` at FTGEN-5.5 when equivCode became a carrier-aware capability.

## Zero-axiom verification

`flatFormerFundamentalAtDenote` is `fundamentalTypeFormerAtDenote` fed the SN premise and the `ofDataFlat`
reducibility (the flat-pinned-after-subst from `subst_rootGenerator_of_not_var` + the original pin + the
content-free gate `carrierCombinator? = none`).  No `induction`, no `funext`.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in `FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **★ FTGEN-5 — the flat-former universe-membership FT arm, route-A-FREE.**  A CONTENT-FREE flat former (any
type code whose root generator satisfies `isFlatDataCode = true` AND `carrierCombinator? = none` — arrow / sum;
the carrier-aware product / either / equiv route through `ofDataFlatCarrierAware` instead) that is
strongly normalizing under every closing substitution and denote-reducible environment is a
`FundamentalConclusionAtDenote` member of its classifying universe `Type@levelExpr`, at any ambient `level`
strictly above the decoded level.  The denote-reducible-TYPE obligation of `fundamentalTypeFormerAtDenote` is
discharged unconditionally by `IsReducibleTypeAtAllDenoteLevels.ofDataFlat` on the substituted former (whose
root generator is preserved by `subst_rootGenerator_of_not_var`, the flat code being a non-variable) — so NO
route-A composite-domain piArm is needed, only the former's strong normalization (the telescope's
contribution). -/
theorem flatFormerFundamentalAtDenote {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope) (former : RawTerm scope)
    (flatPinned : former.rootGenerator.isFlatDataCode = true)
    (notCarrierAware : former.rootGenerator.carrierCombinator? = none)
    (notTermIndexed : former.rootGenerator.isTermIndexedCode = false)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (formerStronglyNormalizing : ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution former)) :
    FundamentalConclusionAtDenote env level context former (universeCodeCell levelExpr flag) := by
  have notVariable : former.rootGenerator ≠ Generator.gen_var := by
    intro rootIsVar
    rw [rootIsVar] at flatPinned
    exact absurd flatPinned (by decide)
  intro targetScope substitution envReducible
  exact fundamentalTypeFormerAtDenote env level context former levelExpr flag levelAbove
    (fun {_innerScope} innerSubst innerEnv =>
      ⟨formerStronglyNormalizing innerSubst innerEnv,
        (IsReducibleTypeAtAllDenoteLevels.ofDataFlat
            (by rw [RawTerm.subst_rootGenerator_of_not_var innerSubst notVariable]; exact flatPinned)
            (by rw [RawTerm.subst_rootGenerator_of_not_var innerSubst notVariable]; exact notCarrierAware)
            (by rw [RawTerm.subst_rootGenerator_of_not_var innerSubst notVariable]; exact notTermIndexed))
          (LevelExpr.denote levelExpr env)⟩)
    substitution envReducible

end FX1Poly.Typed

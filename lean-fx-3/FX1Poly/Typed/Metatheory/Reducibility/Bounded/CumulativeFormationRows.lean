import FX1Poly.Typed.Metatheory.Reducibility.Bounded.CumulativeBinderFormationMember
import FX1Poly.Typed.Metatheory.Reducibility.Bounded.CumulativeFreeLevelsSupport
import FX1Poly.Typed.Engine.RuleTables.FormationRuleTable

/-! # FX1Poly/Typed/CumulativeFormationRows
    — the Π / Σ cumulative formation FT rows over the native obligation list + FREE levels (TYTAB-4 step 4)

`CumulativeBinderFormationMember.lean` discharged the binder-crossing Π/Σ formation members at fixed component
levels.  This file lifts them to the shape the native `formationFundamental` premise demands: the subject is the
generic `mkGen generator payload children` (children the Π/Σ binder spine), the obligation hypotheses come as the
single `∀ obligation ∈ cumulativeFormationObligations …` list, and the level list is FREE (so the output universe is
`universeFormerOutput scope levels flag = Type@(lmaxAll levels)`).

## The free-`levels` dispatch

After the binder spine `childCons domain (childCons codomain childNil)`, `cumulativeFormationObligations` reduces — on
`levels` — to `cumulativeBinderObligations … domain codomain OBL_DL OBL_CL` for one of three obligation-level pairs:

  * `levels = domainLevel :: codomainLevel :: _` → `(domainLevel, codomainLevel)` (the real Π/Σ row);
  * `levels = [_]` → `(Type@0, Type@0)` (the forced-`lzero` short-list case);
  * `levels = []` → `(Type@0, Type@0)` (the forced-`lzero` empty case).

In each, the two obligations are the domain (`.head`) and binder-crossing codomain (`.tail.head`) IHs (each `have`
is type-annotated to reduce the obligation-record projections to the clean `domain` / `codomain` subjects), fed to
`fundamentalCumulative{Pi,Sigma}MemberAtBoundedSucc` to land the member at `Type@(lmaxAll [OBL_DL, OBL_CL])`, then
lifted to the free output `Type@(lmaxAll levels)` by `fundamentalConclusion_universeCumulative` — the obligation-level
max never exceeds the free-levels max (`denote_le_lmaxFold` for the real case; `0 ≤ _` for the forced-`lzero` cases),
and the free-levels max stays below the bound (`denote_lmaxFold_lt` from the per-level gate, or `boundPositive` for the
empty list).  The conclusion's `∀ targetScope substitution envReducible` are `intro`'d up front so the lift's
per-substitution member is applied directly (sidestepping the folded-`FundamentalConclusionAtBoundedSucc` unifier).

## Zero-axiom verification

`match` on the spine + a three-way `match` on `levels`, each branch a member application + the cumulativity lift with
elementary `lmaxFold`/`levelMax` bounds.  No induction (the inductions live in the support layer), no `funext`.  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-- **The Π cumulative formation FT row (TYTAB-4 step 4).**  From the native obligation-list IHs over
`cumulativeFormationObligations` (the domain at its level, the binder-crossing codomain at its level) under a FREE
`levels`, the cell `mkGen gen_piTyCode payload children` is a bound-reducible member of the free output universe
`universeFormerOutput scope levels flag = Type@(lmaxAll levels)`.  Dispatches the three obligation-level shapes,
lands the binder-crossing member, and lifts to the free output universe. -/
theorem fundamentalCumulativePiRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {payload : Generator.gen_piTyCode.payload scope}
    {children : RawTermChildren Generator.gen_piTyCode.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag}
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ cumulativeFormationObligations profile context flag children levels →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context
      (RawTerm.mkGen Generator.gen_piTyCode payload children)
      (universeFormerOutput scope levels flag) := by
  match children with
  | .childCons domain (.childCons codomain .childNil) =>
    show FundamentalConclusionAtBoundedSucc env bound context (piTyCodeCell domain codomain)
      (universeCodeCell (lmaxAll levels) flag)
    intro targetScope substitution envReducible
    match levels with
    | domainLevel :: codomainLevel :: restLevels =>
      have domainIH : FundamentalConclusionAtBoundedSucc env bound context domain
          (universeCodeCell domainLevel flag) :=
        obligationsFundamental
          { scope := scope, context := context, subject := domain,
            classifier := universeCodeCell domainLevel flag } (List.Mem.head _)
      have codomainIH : FundamentalConclusionAtBoundedSucc env bound (context.cons domain) codomain
          (universeCodeCell codomainLevel flag) :=
        obligationsFundamental
          { scope := scope + 1, context := context.cons domain, subject := codomain,
            classifier := universeCodeCell codomainLevel flag } (List.Mem.tail _ (List.Mem.head _))
      exact fundamentalConclusion_universeCumulative env bound context
        (lmaxAll [domainLevel, codomainLevel])
        (lmaxAll (domainLevel :: codomainLevel :: restLevels)) flag
        (fundamentalCumulativePiMemberAtBoundedSucc env bound context domainLevel codomainLevel flag
          domainIH codomainIH)
        (denote_le_lmaxFold env restLevels (LevelExpr.lmax domainLevel codomainLevel))
        (denote_lmaxFold_lt env bound restLevels (LevelExpr.lmax domainLevel codomainLevel)
          (by
            rw [LevelExpr.denote_lmax]
            exact levelMax_lt (levelsBelowBound domainLevel (List.Mem.head _))
              (levelsBelowBound codomainLevel (List.Mem.tail _ (List.Mem.head _))))
          (fun levelExpr levelMem =>
            levelsBelowBound levelExpr (List.Mem.tail _ (List.Mem.tail _ levelMem))))
        substitution envReducible
    | [singleLevel] =>
      have domainIH : FundamentalConclusionAtBoundedSucc env bound context domain
          (universeCodeCell LevelExpr.lzero flag) :=
        obligationsFundamental
          { scope := scope, context := context, subject := domain,
            classifier := universeCodeCell LevelExpr.lzero flag } (List.Mem.head _)
      have codomainIH : FundamentalConclusionAtBoundedSucc env bound (context.cons domain) codomain
          (universeCodeCell LevelExpr.lzero flag) :=
        obligationsFundamental
          { scope := scope + 1, context := context.cons domain, subject := codomain,
            classifier := universeCodeCell LevelExpr.lzero flag } (List.Mem.tail _ (List.Mem.head _))
      exact fundamentalConclusion_universeCumulative env bound context
        (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) (lmaxAll [singleLevel]) flag
        (fundamentalCumulativePiMemberAtBoundedSucc env bound context LevelExpr.lzero LevelExpr.lzero
          flag domainIH codomainIH)
        (by rw [lmaxAll_pair, LevelExpr.denote_lmax, LevelExpr.denote_lzero]; exact Nat.zero_le _)
        (levelsBelowBound singleLevel (List.Mem.head _))
        substitution envReducible
    | [] =>
      have domainIH : FundamentalConclusionAtBoundedSucc env bound context domain
          (universeCodeCell LevelExpr.lzero flag) :=
        obligationsFundamental
          { scope := scope, context := context, subject := domain,
            classifier := universeCodeCell LevelExpr.lzero flag } (List.Mem.head _)
      have codomainIH : FundamentalConclusionAtBoundedSucc env bound (context.cons domain) codomain
          (universeCodeCell LevelExpr.lzero flag) :=
        obligationsFundamental
          { scope := scope + 1, context := context.cons domain, subject := codomain,
            classifier := universeCodeCell LevelExpr.lzero flag } (List.Mem.tail _ (List.Mem.head _))
      exact fundamentalConclusion_universeCumulative env bound context
        (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) (lmaxAll []) flag
        (fundamentalCumulativePiMemberAtBoundedSucc env bound context LevelExpr.lzero LevelExpr.lzero
          flag domainIH codomainIH)
        (by rw [lmaxAll_pair, LevelExpr.denote_lmax, LevelExpr.denote_lzero]; exact Nat.zero_le _)
        boundPositive
        substitution envReducible

/-- **The Σ cumulative formation FT row (TYTAB-4 step 4).**  The Σ twin of
`fundamentalCumulativePiRowAtBoundedSucc`: identical free-`levels` dispatch, landing
`fundamentalCumulativeSigmaMemberAtBoundedSucc` and lifting to `Type@(lmaxAll levels)`. -/
theorem fundamentalCumulativeSigmaRowAtBoundedSucc {profile : PolyProfile} (env : Nat → Nat) (bound : Nat)
    {scope : Nat} (context : TypingContext profile scope)
    {payload : Generator.gen_sigmaTyCode.payload scope}
    {children : RawTermChildren Generator.gen_sigmaTyCode.binderShifts scope}
    {levels : List LevelExpr} {flag : UniverseFlag}
    (levelsBelowBound : ∀ levelExpr, levelExpr ∈ levels → LevelExpr.denote levelExpr env < bound)
    (boundPositive : 0 < bound)
    (obligationsFundamental : ∀ obligation,
        obligation ∈ cumulativeFormationObligations profile context flag children levels →
        FundamentalConclusionAtBoundedSucc env bound obligation.context obligation.subject
          obligation.classifier) :
    FundamentalConclusionAtBoundedSucc env bound context
      (RawTerm.mkGen Generator.gen_sigmaTyCode payload children)
      (universeFormerOutput scope levels flag) := by
  match children with
  | .childCons domain (.childCons codomain .childNil) =>
    show FundamentalConclusionAtBoundedSucc env bound context (sigmaTyCodeCell domain codomain)
      (universeCodeCell (lmaxAll levels) flag)
    intro targetScope substitution envReducible
    match levels with
    | domainLevel :: codomainLevel :: restLevels =>
      have domainIH : FundamentalConclusionAtBoundedSucc env bound context domain
          (universeCodeCell domainLevel flag) :=
        obligationsFundamental
          { scope := scope, context := context, subject := domain,
            classifier := universeCodeCell domainLevel flag } (List.Mem.head _)
      have codomainIH : FundamentalConclusionAtBoundedSucc env bound (context.cons domain) codomain
          (universeCodeCell codomainLevel flag) :=
        obligationsFundamental
          { scope := scope + 1, context := context.cons domain, subject := codomain,
            classifier := universeCodeCell codomainLevel flag } (List.Mem.tail _ (List.Mem.head _))
      exact fundamentalConclusion_universeCumulative env bound context
        (lmaxAll [domainLevel, codomainLevel])
        (lmaxAll (domainLevel :: codomainLevel :: restLevels)) flag
        (fundamentalCumulativeSigmaMemberAtBoundedSucc env bound context domainLevel codomainLevel flag
          domainIH codomainIH)
        (denote_le_lmaxFold env restLevels (LevelExpr.lmax domainLevel codomainLevel))
        (denote_lmaxFold_lt env bound restLevels (LevelExpr.lmax domainLevel codomainLevel)
          (by
            rw [LevelExpr.denote_lmax]
            exact levelMax_lt (levelsBelowBound domainLevel (List.Mem.head _))
              (levelsBelowBound codomainLevel (List.Mem.tail _ (List.Mem.head _))))
          (fun levelExpr levelMem =>
            levelsBelowBound levelExpr (List.Mem.tail _ (List.Mem.tail _ levelMem))))
        substitution envReducible
    | [singleLevel] =>
      have domainIH : FundamentalConclusionAtBoundedSucc env bound context domain
          (universeCodeCell LevelExpr.lzero flag) :=
        obligationsFundamental
          { scope := scope, context := context, subject := domain,
            classifier := universeCodeCell LevelExpr.lzero flag } (List.Mem.head _)
      have codomainIH : FundamentalConclusionAtBoundedSucc env bound (context.cons domain) codomain
          (universeCodeCell LevelExpr.lzero flag) :=
        obligationsFundamental
          { scope := scope + 1, context := context.cons domain, subject := codomain,
            classifier := universeCodeCell LevelExpr.lzero flag } (List.Mem.tail _ (List.Mem.head _))
      exact fundamentalConclusion_universeCumulative env bound context
        (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) (lmaxAll [singleLevel]) flag
        (fundamentalCumulativeSigmaMemberAtBoundedSucc env bound context LevelExpr.lzero LevelExpr.lzero
          flag domainIH codomainIH)
        (by rw [lmaxAll_pair, LevelExpr.denote_lmax, LevelExpr.denote_lzero]; exact Nat.zero_le _)
        (levelsBelowBound singleLevel (List.Mem.head _))
        substitution envReducible
    | [] =>
      have domainIH : FundamentalConclusionAtBoundedSucc env bound context domain
          (universeCodeCell LevelExpr.lzero flag) :=
        obligationsFundamental
          { scope := scope, context := context, subject := domain,
            classifier := universeCodeCell LevelExpr.lzero flag } (List.Mem.head _)
      have codomainIH : FundamentalConclusionAtBoundedSucc env bound (context.cons domain) codomain
          (universeCodeCell LevelExpr.lzero flag) :=
        obligationsFundamental
          { scope := scope + 1, context := context.cons domain, subject := codomain,
            classifier := universeCodeCell LevelExpr.lzero flag } (List.Mem.tail _ (List.Mem.head _))
      exact fundamentalConclusion_universeCumulative env bound context
        (lmaxAll [LevelExpr.lzero, LevelExpr.lzero]) (lmaxAll []) flag
        (fundamentalCumulativeSigmaMemberAtBoundedSucc env bound context LevelExpr.lzero LevelExpr.lzero
          flag domainIH codomainIH)
        (by rw [lmaxAll_pair, LevelExpr.denote_lmax, LevelExpr.denote_lzero]; exact Nat.zero_le _)
        boundPositive
        substitution envReducible

end FX1Poly.Typed

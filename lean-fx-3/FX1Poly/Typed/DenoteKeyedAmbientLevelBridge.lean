import FX1Poly.Typed.DenoteKeyedLevelIrrelevance

/-! # FX1Poly/Typed/DenoteKeyedAmbientLevelBridge
    — the A2 ambient-level reducibility bridge (SN-D5-A2bridge; the shared conv+piIntro residual, toward SN-043/#672)

The single shared deep ingredient the denote fundamental theorem's formation/intro/conv arms all consume —
identified in the SN-D5a conv-arm analysis.  `universeMemberReducibleAtLevel` turns a type's UNIVERSE
MEMBERSHIP at the ambient level into the type's REDUCIBILITY at the ambient level:

  `IsReducibleMemberAtDenote env level (Type@levelExpr) X` + `denote levelExpr env < level`
    ⟹ `IsReducibleTypeAtDenote env level X`.

WHY THIS IS THE CRUX.  The single-level denote motive (`FundamentalConclusionAtDenote`, one uniform ambient
`level`) makes the elimination arm (`fundamentalPiElimAtDenote`) trivial — it threads candidates already at the
ambient level — but it pushes ALL the difficulty here: the `conv` arm's reclassifier and the `piIntro` arm's
domain both arrive (via their FT IHs) as members of a universe code, and universe membership decodes
reducibility at the FIXED DECODED level `denote levelExpr env`, NOT at the ambient `level`.  Bridging
decoded-level reducibility to ambient-level reducibility for an arbitrary type code is the general denote
type-level LEVEL-IRRELEVANCE (= the A2 residual = the denote restatement of #672).  No conv-transport produces
it directly: reducibility candidates are NOT backward-closed under arbitrary `Step` (only weak-head), confirmed
by `convInvariant` being determinism-only at both the denote and fuel layers.

THE CONSTRUCTION (real content, not a deferral).  Unpack the universe membership: its candidate is
`universeDenotePredicate` (aligned via `candidateIffUniverse`), whose `∃` conjunct gives X reducible in
`denoteBelowFamily env level (denote levelExpr env)`; the `levelAbove` bound `denote levelExpr env < level`
turns that into `ReducibleTypeAtDenote env (denote levelExpr env) X` (via `denoteBelowFamily_eq_reducible`);
then the shipped level-irrelevance backbone `IsReducibleTypeAtAllDenoteLevels.ofReducibleTypeStepDenote` lifts
to ALL denote levels, and we project to the target `level`.

THE ONE RESIDUAL.  `ofReducibleTypeStepDenote` is itself parametric over its `piType` arm (the composite-
dependent-domain level-irrelevance — the genuine A2 residual; the {uniform, neutral, universe}-domain instances
are shipped in the from-existence family, the composite-domain case is open).  This bridge is therefore
parametric over EXACTLY that one `piArm` (instantiated at the decoded level's below-family) — the established
`ofReducibleTypeStepDenote` discipline.  So the CONSOLIDATION this file delivers: the denote FT's conv arm
(SN-D5a) and piIntro arm (SN-D5c, pending) both reduce — through this single bridge — to the ONE composite-domain
piArm, which is the lone deep obligation gating the entire denote SN-043 route.

## Zero-axiom verification

`obtain` the universe member, `candidateIffUniverse` to expose `universeDenotePredicate`, `obtain` its `∃`
conjunct, `denoteBelowFamily_eq_reducible` rewrite at the decoded index, then `ofReducibleTypeStepDenote`
(parametric piArm) projected at `level`.  No induction here (the induction is inside the backbone), no `funext`.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated
in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **The A2 ambient-level reducibility bridge.**  A type that is a denote-reducible MEMBER of `Type@levelExpr`
at the ambient `level` (with the decoded classifier level below the ambient level) is itself denote-reducible AT
the ambient `level`.  The universe membership decodes reducibility at the decoded level `denote levelExpr env`;
`ofReducibleTypeStepDenote` lifts that to all levels, projected to `level`.  Parametric over EXACTLY the
`ofReducibleTypeStepDenote` composite-domain `piArm` (at the decoded level's below-family) — the single shared
residual of the conv and piIntro fundamental-theorem arms. -/
theorem universeMemberReducibleAtLevel {scope : Nat} {env : Nat → Nat} {level : Nat}
    {levelExpr : LevelExpr} {flag : UniverseFlag} {X : RawTerm scope}
    (piArm : ∀ {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
        {domainCandidate : RawTerm scope → Prop}
        (codomainCandidate : RawTerm scope → (RawTerm scope → Prop)),
        ReducibleTypeStepDenote env (denoteBelowFamily env (LevelExpr.denote levelExpr env))
          domainCode domainCandidate →
        (∀ argument : RawTerm scope, domainCandidate argument →
          ReducibleTypeStepDenote env (denoteBelowFamily env (LevelExpr.denote levelExpr env))
            (RawTerm.subst0 codomainCode argument) (codomainCandidate argument)) →
        IsReducibleTypeAtAllDenoteLevels env domainCode →
        (∀ argument : RawTerm scope, domainCandidate argument →
          IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst0 codomainCode argument)) →
        IsReducibleTypeAtAllDenoteLevels env
          (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
    (memberOfUniverse : IsReducibleMemberAtDenote env level
      (.mkGen .gen_universeCode (levelExpr, flag) .childNil) X)
    (levelAbove : LevelExpr.denote levelExpr env < level) :
    IsReducibleTypeAtDenote env level X := by
  obtain ⟨cand, reducibleUniv, candX⟩ := memberOfUniverse
  have candIff := ReducibleTypeStepDenote.candidateIffUniverse reducibleUniv
    (levelExpr := levelExpr) (flag := flag) rfl
  have univX := (candIff X).mp candX
  obtain ⟨_snX, _decodeCandidate, denoteReducibleX⟩ := univX
  rw [denoteBelowFamily_eq_reducible env level (LevelExpr.denote levelExpr env) levelAbove]
    at denoteReducibleX
  exact IsReducibleTypeAtAllDenoteLevels.ofReducibleTypeStepDenote piArm denoteReducibleX level

end FX1Poly.Typed

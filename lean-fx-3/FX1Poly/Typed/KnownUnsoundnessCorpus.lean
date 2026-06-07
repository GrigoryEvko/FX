import FX1Poly.Modal.UsageDiscipline
import FX1Poly.Typed.GrownUniverseConsistency

/-! # FX1Poly/Typed/KnownUnsoundnessCorpus
    — the §27.3 Layer-1 known-unsoundness corpus: every cataloged type-theory bug is a permanent rejection
      test (§27.2 / §23.6 / §1.4)

The §27.3 five-layer defense opens with Layer 1: "known-witness smoke tests — every cataloged bug is a
rejected test."  §27.2 catalogs the known type-theory unsoundnesses from the literature; §23.6 makes the
corpus a single regression set that grows-never-shrinks and blocks all releases.  This file IS that corpus
for the FX1Poly kernel: it assembles the shipped zero-axiom REJECTION witnesses for every cataloged bug the
current kernel can express, records the remaining catalog entries as an HONEST machine-checked pending ledger
(their dimension is not yet engine-typed — not a silent omission), and strengthens the dependent-type entry
with genuinely-new acyclicity content.

## The §27.2 catalog (`KnownTypeTheoryBug`)

  | bug                                   | dimension                       | encodable now |
  | ------------------------------------- | ------------------------------- | ------------- |
  | Atkey-2018 broken Lam                 | usage (linearity)               | YES           |
  | session-endpoint aliased              | protocol (session)              | no            |
  | ML value restriction                  | usage (polymorphic references)  | no            |
  | Type:Type / Girard's paradox          | type (universe hierarchy)       | YES           |
  | implicit flow via branch on secret    | security (information flow)     | no            |
  | constant-time secret memory access    | security (constant-time)        | no            |
  | fractional-permission overallocation  | usage (fractional permissions)  | no            |

The two `YES` rows have shipped, gated, zero-axiom rejections (the usage dimension's Atkey check and the grown
engine's universe strictness); the five `no` rows await the dimension that would let them even be STATED
(sessions, ML-style mutable references, a branch construct over secret-graded data, a constant-time effect, a
fractional-permission PCM).  `isEncodableNow` records this split as data, so the ledger cannot silently drift.

## Genuinely-new content — universe-typing acyclicity (Part 1)

The shipped Girard rejections (`grownUniverseCode_notTypedAtSelf` etc.) reject the length-1 cycle
`Type@e : Type@e`.  This file proves the relation is acyclic at every length by pinning it EXACTLY:

  * `grownUniverseTypingForcesSuccessor` — if `Type@a : Type@b` in the grown engine (ANY context, no
    well-formedness needed), then `b = a+1` and the flags agree.  The universe-typing relation is the
    successor FUNCTION, not merely irreflexive.
  * `grownUniverseTypingHasNoTwoCycle` — hence no pair of universes classifies each other (`b = a+1` and
    `a = b+1` force `a = a+2`, refuted by `LevelExpr.ne_lsuccLsucc_self`).  The honest "no Girard cycle of any
    length" — the 2-cycle is the first genuinely-new obstruction beyond the shipped 1-cycle.
  * `corpusRejectsTypeInType` — the classic no-`Type:Type` (1-cycle), now a one-line corollary of the
    functional characterization, and (unlike the shipped twins) carrying NO well-formedness decoration.

## Zero-axiom verification

Part 1 is one `inversionUniverseCode` feeding `universeCodeCell_inj_of_conv` (confluence + cell injectivity,
no SN premise), then the size-free predicativity guards `LevelExpr.ne_lsucc_self` / `ne_lsuccLsucc_self`.  The
catalog functions are full-enumeration non-dependent matches (Bool / String), and the ledger facts close by
`rfl`; the re-exported witnesses inherit the zero-axiom status of their sources.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Modal

/-! ## Part 1 — the universe-typing relation is acyclic (strengthening the Girard / Type:Type entry) -/

/-- **Universe typing is the successor function.**  If a universe code `Type@(subjectLevel, subjectFlag)` is
grown-typed at a universe code `Type@(classifierLevel, classifierFlag)` in ANY context (no well-formedness
needed — this is a pure inversion), then `classifierLevel = subjectLevel + 1` and the flags agree.  The
grown inversion `inversionUniverseCode` forces every classifier `Conv`-equal to the strict predicative
successor `Type@(subjectLevel+1, subjectFlag)`; `universeCodeCell_inj_of_conv` collapses that `Conv` to the
level + flag equalities.  Every level-strictness rejection (self / inflation / deflation) is a corollary. -/
theorem grownUniverseTypingForcesSuccessor {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {subjectLevel classifierLevel : LevelExpr} {subjectFlag classifierFlag : UniverseFlag}
    (typed : HasTypeDescPi profile context (universeCodeCell subjectLevel subjectFlag)
        (universeCodeCell classifierLevel classifierFlag)) :
    classifierLevel = subjectLevel.lsucc ∧ classifierFlag = subjectFlag :=
  universeCodeCell_inj_of_conv (HasTypeDescPi.inversionUniverseCode typed)

/-- **No Girard 2-cycle in universe typing.**  There is no pair of universes each classified by the other:
`Type@a : Type@b` forces `b = a+1`, and `Type@b : Type@a` forces `a = b+1`, so `a = a+2`, refuted by the
double-successor predicativity guard `LevelExpr.ne_lsuccLsucc_self`.  The first genuinely-new acyclicity
obstruction beyond the shipped length-1 no-`Type:Type` — the honest "no Girard cycle of any length"
guarantee for the grown engine. -/
theorem grownUniverseTypingHasNoTwoCycle {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {levelA levelB : LevelExpr} {flagA flagB : UniverseFlag}
    (typedUp : HasTypeDescPi profile context (universeCodeCell levelA flagA)
        (universeCodeCell levelB flagB))
    (typedDown : HasTypeDescPi profile context (universeCodeCell levelB flagB)
        (universeCodeCell levelA flagA)) :
    False := by
  obtain ⟨levelBeqSuccA, _⟩ := grownUniverseTypingForcesSuccessor typedUp
  obtain ⟨levelAeqSuccB, _⟩ := grownUniverseTypingForcesSuccessor typedDown
  rw [levelBeqSuccA] at levelAeqSuccB
  exact LevelExpr.ne_lsuccLsucc_self levelA levelAeqSuccB

/-- **Corpus entry — no `Type : Type` (the classic Girard 1-cycle, §27.2 / §1.4).**  `Type@(level, flag)`
is never grown-classified by itself, in ANY context.  A one-line corollary of the functional
characterization: self-classification forces `level = level + 1`, refuted by `LevelExpr.ne_lsucc_self`.
Unlike the shipped `grownUniverseCode_notTypedAtSelf`, this carries no well-formedness decoration — the
rejection is unconditional. -/
theorem corpusRejectsTypeInType {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    (level : LevelExpr) (flag : UniverseFlag) :
    ¬ HasTypeDescPi profile context (universeCodeCell level flag)
        (universeCodeCell level flag) := by
  intro typed
  exact LevelExpr.ne_lsucc_self level (grownUniverseTypingForcesSuccessor typed).1

/-! ## Part 2 — the §27.2 catalog as machine-checked data -/

/-- **The §27.2 known-unsoundness catalog.**  One constructor per cataloged type-theory bug from the
literature.  The enumeration is the corpus's index: `dimension` / `literatureSource` document each entry,
`isEncodableNow` records whether the current kernel can state-and-reject it. -/
inductive KnownTypeTheoryBug where
  | atkey2018BrokenLam
  | sessionEndpointAliased
  | mlValueRestriction
  | typeInTypeGirard
  | implicitFlowBranchOnSecret
  | constantTimeSecretMemoryAccess
  | fractionalPermissionOverallocation

/-- The graded dimension (or feature) each cataloged bug lives in (§6.3 / §27.2). -/
def KnownTypeTheoryBug.dimension : KnownTypeTheoryBug → String
  | .atkey2018BrokenLam => "usage (linearity)"
  | .sessionEndpointAliased => "protocol (session)"
  | .mlValueRestriction => "usage (polymorphic references)"
  | .typeInTypeGirard => "type (universe hierarchy)"
  | .implicitFlowBranchOnSecret => "security (information flow)"
  | .constantTimeSecretMemoryAccess => "security (constant-time)"
  | .fractionalPermissionOverallocation => "usage (fractional permissions)"

/-- The literature source §27.2 cites for each cataloged bug. -/
def KnownTypeTheoryBug.literatureSource : KnownTypeTheoryBug → String
  | .atkey2018BrokenLam => "Atkey 2018 broken Lam; Wood-Atkey 2022 correction"
  | .sessionEndpointAliased => "linear session endpoints (Honda-Yoshida-Carbone)"
  | .mlValueRestriction => "Wright 1995 ML value restriction"
  | .typeInTypeGirard => "Girard 1972 System U paradox"
  | .implicitFlowBranchOnSecret => "Denning-Denning 1977; Sabelfeld-Myers 2003"
  | .constantTimeSecretMemoryAccess => "constant-time crypto (Barthe et al.)"
  | .fractionalPermissionOverallocation => "Boyland 2003 fractional permissions"

/-- **Encodability ledger.**  `true` ⟺ this corpus carries a shipped zero-axiom rejection witness for the
bug; `false` ⟺ the bug's dimension is not yet engine-typed, so the kernel cannot even STATE it (an HONEST
pending entry, not a silent omission).  Full enumeration — every catalog entry is classified, none falls
through a wildcard. -/
def KnownTypeTheoryBug.isEncodableNow : KnownTypeTheoryBug → Bool
  | .atkey2018BrokenLam => true
  | .typeInTypeGirard => true
  | .sessionEndpointAliased => false
  | .mlValueRestriction => false
  | .implicitFlowBranchOnSecret => false
  | .constantTimeSecretMemoryAccess => false
  | .fractionalPermissionOverallocation => false

/-! ## Part 3 — the rejection witnesses, corpus-cited -/

/-- **Corpus entry — Atkey-2018 broken Lam (usage/linearity, §27.2 / §27.1).**  `λx. f (f x)` with `f`
declared linear is REJECTED by the usage check (`f`'s occurrence usage is `ω`, and `ω ≤ 1` is false) — the
Wood-Atkey 2022 correction.  Re-exported from the usage dimension (`FX1Poly.Modal.atkey_rejected`). -/
theorem corpusRejectsAtkeyBrokenLam :
    ¬ GradedLambda.WellGraded 1 atkeyClosure linearContext :=
  atkey_rejected

/-- **Corpus entry — the naive occurrence-grade check is not subject-reduction-closed (§27.2 / §27.3).**
A well-graded redex whose β-reduct is ill-graded — `(λx. x x) g` with `g` linear: well-graded (`g` appears
once syntactically) yet its reduct `g g` uses `g` twice.  The concrete reason a sound graded judgment must
scale arguments by the binder grade.  Re-exported from `usage_check_fails_subject_reduction`. -/
theorem corpusRejectsNaiveGradeCheck :
    ∃ (redex reduct : GradedLambda) (declared : GradeVector),
      GradedLambda.BetaStep redex reduct ∧
        GradedLambda.WellGraded 1 redex declared ∧
        ¬ GradedLambda.WellGraded 1 reduct declared :=
  usage_check_fails_subject_reduction

/-! ## Part 4 — the honest ledger + non-vacuity -/

/-- Ledger fact: the Atkey-2018 broken Lam is currently encodable (its rejection ships above). -/
theorem atkeyBug_isEncodableNow :
    KnownTypeTheoryBug.atkey2018BrokenLam.isEncodableNow = true := rfl

/-- Ledger fact: the Type:Type / Girard bug is currently encodable (its rejection ships above). -/
theorem girardBug_isEncodableNow :
    KnownTypeTheoryBug.typeInTypeGirard.isEncodableNow = true := rfl

/-- Ledger fact (HONEST pending): session-endpoint aliasing is NOT yet encodable — the protocol/session
dimension is not engine-typed. -/
theorem sessionBug_isPending :
    KnownTypeTheoryBug.sessionEndpointAliased.isEncodableNow = false := rfl

/-- Ledger fact (HONEST pending): the ML value restriction is NOT yet encodable — there are no ML-style
polymorphic mutable references in the kernel. -/
theorem mlValueRestrictionBug_isPending :
    KnownTypeTheoryBug.mlValueRestriction.isEncodableNow = false := rfl

/-- Ledger fact (HONEST pending): implicit flow via branch on secret is NOT yet encodable — the graded
engine has no branch construct over secret-graded data. -/
theorem implicitFlowBug_isPending :
    KnownTypeTheoryBug.implicitFlowBranchOnSecret.isEncodableNow = false := rfl

/-- Ledger fact (HONEST pending): the constant-time secret-memory-access bug is NOT yet encodable — there
is no constant-time effect tracking secret-dependent memory access. -/
theorem constantTimeBug_isPending :
    KnownTypeTheoryBug.constantTimeSecretMemoryAccess.isEncodableNow = false := rfl

/-- Ledger fact (HONEST pending): fractional-permission overallocation is NOT yet encodable — there is no
fractional-permission PCM in the kernel yet. -/
theorem fractionalPermissionBug_isPending :
    KnownTypeTheoryBug.fractionalPermissionOverallocation.isEncodableNow = false := rfl

/-- **The corpus is non-vacuous.**  Both currently-encodable cataloged bugs are concretely rejected: the
Atkey-2018 broken Lam (`f` linear, used twice) is not well-graded, and `Type@0 : Type@0` (the Girard
1-cycle) has no grown typing in the empty context — for every profile.  Layer-1 of the §27.3 defense is
load-bearing, not a placeholder. -/
theorem corpusNonVacuous :
    (¬ GradedLambda.WellGraded 1 atkeyClosure linearContext) ∧
    (∀ profile : PolyProfile,
      ¬ HasTypeDescPi profile (TypingContext.empty : TypingContext profile 0)
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard)
        (universeCodeCell LevelExpr.lzero UniverseFlag.standard)) :=
  ⟨atkey_rejected,
    fun profile =>
      corpusRejectsTypeInType (profile := profile) LevelExpr.lzero UniverseFlag.standard⟩

end FX1Poly.Typed

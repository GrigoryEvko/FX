import FX1Poly.Modal.UsageDiscipline
import FX1Poly.Modal.GradedTypingGeneric
import FX1Poly.Modal.FractionalPermission
import FX1Poly.Typed.GrownUniverseConsistency

/-! # FX1Poly/Typed/KnownUnsoundnessCorpus
    — the §27.3 Layer-1 known-unsoundness corpus: every cataloged type-theory bug is a permanent rejection
      test (§27.2 / §23.6 / §1.4)

The §27.3 five-layer defense opens with Layer 1: "known-witness smoke tests — every cataloged bug is a
rejected test."  §27.2 catalogs the known type-theory unsoundnesses from the literature; §23.6 makes the
corpus a single regression set that grows-never-shrinks and blocks all releases.  This file IS that corpus
for the FX1Poly kernel: it assembles the shipped zero-axiom REJECTION witnesses for every cataloged bug the
current kernel can express, records the remaining catalog entries as an HONEST machine-checked pending ledger
(their dimension is not yet engine-typed — not a silent omission), strengthens the dependent-type entry
with genuinely-new acyclicity content (Part 1), and — now that the security graded judgment ships
(`FX1Poly.Modal.HasGradeOver` over `fxSecuritySemiring`) — adds the FIRST security-dimension noninterference
witnesses (Part 5): the explicit-flow rejection (no laundering a secret to public by direct use) and the
application-form implicit-flow rejection (a secret selector's secrecy cannot be laundered through a
selection).  The native-`if` surface of the cataloged implicit-flow bug stays honestly pending.  And —
now that the §6.4 fractional-permission algebra ships (`FX1Poly.Modal.Permission`) — it adds the
fractional-permission OVERALLOCATION rejection (Part 6): the guarded add never produces an over-full
share (Boyland 2003), flipping that catalog entry to encodable.

## The §27.2 catalog (`KnownTypeTheoryBug`)

  | bug                                   | dimension                       | encodable now |
  | ------------------------------------- | ------------------------------- | ------------- |
  | Atkey-2018 broken Lam                 | usage (linearity)               | YES           |
  | session-endpoint aliased              | protocol (session)              | no            |
  | ML value restriction                  | usage (polymorphic references)  | no            |
  | Type:Type / Girard's paradox          | type (universe hierarchy)       | YES           |
  | implicit flow via branch on secret    | security (information flow)     | no            |
  | constant-time secret memory access    | security (constant-time)        | no            |
  | fractional-permission overallocation  | usage (fractional permissions)  | YES           |

The three `YES` rows have shipped, gated, zero-axiom rejections (the usage dimension's Atkey check, the grown
engine's universe strictness, and the §6.4 fractional-permission overallocation guard); the four `no` rows
await the dimension that would let them even be STATED (sessions, ML-style mutable references, a native branch
construct over secret-graded data, a constant-time effect).  `isEncodableNow` records this split as data, so
the ledger cannot silently drift.

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
  | .fractionalPermissionOverallocation => true

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

/-- Ledger fact (HONEST pending): implicit flow via branch on secret is NOT yet encodable AS THE
CATALOGED NATIVE-BRANCH BUG — the graded engine has no native `if` construct whose grade rule joins the
scrutinee's security grade into the branches.  (The implicit-flow MECHANISM — a secret SELECTOR
controlling the result — IS already defended in its application form: see Part 5's
`securitySelectorAppCannotLaunderSelector`, where the App-scaling rule propagates a classified selector's
grade into the result so it cannot be laundered to public.  The pending surface is specifically the
native `if`.) -/
theorem implicitFlowBug_isPending :
    KnownTypeTheoryBug.implicitFlowBranchOnSecret.isEncodableNow = false := rfl

/-- Ledger fact (HONEST pending): the constant-time secret-memory-access bug is NOT yet encodable — there
is no constant-time effect tracking secret-dependent memory access. -/
theorem constantTimeBug_isPending :
    KnownTypeTheoryBug.constantTimeSecretMemoryAccess.isEncodableNow = false := rfl

/-- Ledger fact: fractional-permission overallocation is NOW encodable — the §6.4 permission algebra
(`FX1Poly.Modal.Permission`) ships, and its guarded add rejects over-the-whole combines (Part 6). -/
theorem fractionalPermissionBug_isEncodableNow :
    KnownTypeTheoryBug.fractionalPermissionOverallocation.isEncodableNow = true := rfl

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

/-! ## Part 5 — security-dimension noninterference witnesses (the first §27.2 security entries)

Until now the §27.2 corpus carried witnesses only for the usage and type dimensions; the three security
rows (`implicitFlowBranchOnSecret`, `constantTimeSecretMemoryAccess`) stayed pending for lack of a
dimension that could even STATE them.  With the security graded judgment shipped
(`FX1Poly.Modal.HasGradeOver` over `fxSecuritySemiring`, `unclassified < classified`), the
NONINTERFERENCE core IS now witnessable — these are the first security-dimension rejections in the
corpus.  They are positive metatheory content (like Part 1's universe acyclicity), not new catalog
constructors.

The security grade vector records the secrecy level at which each binding is used; the var rule fixes a
used variable's grade to `R.one = classified` (no subsumption can lower it), and the App-scaling rule
`functionGrades + binderGrade · argumentGrades` adds the function's grades directly — so a classified
SELECTOR's secrecy `+`-poisons the result (`classified + a = classified`).  Together: a secret cannot be
laundered to public, neither by direct use (explicit flow) nor by controlling a selection (the
application form of implicit flow).

  * `securityVarUsedIsClassified` — baseline: a directly-used variable IS graded `classified` (the var
    rule at `fxSecuritySemiring`).
  * **`securityDirectUseCannotBePublic`** — the EXPLICIT-flow rejection (Denning-Denning's direct case):
    that same used variable canNOT be graded `unclassified`; `invertVar` forces the grade to `R.one =
    classified` and `unclassified ≠ classified`.  No laundering a secret to public by direct use.
  * `securitySelectorAppResultIsClassified` — the IMPLICIT-flow mechanism, positive: applying a
    classified selector `s` (a Church-style chooser at function type) to a public value grades the
    result `classified` at the selector position — the App-scaling rule propagates the selector's
    secrecy into the result.
  * **`securitySelectorAppCannotLaunderSelector`** — the IMPLICIT-flow rejection: that application
    canNOT be graded with the selector position `unclassified`; the App-scaled position-1 grade is
    `one + binderGrade · zero = classified` (poisoned), so the secret that controlled the selection
    cannot be laundered to public.  This is the application form of "implicit flow via branch on secret"
    (`if` is Church-encoded as application); the native-`if` catalog surface stays pending
    (`implicitFlowBug_isPending`).
-/

/-- Baseline: a directly-used variable IS graded `classified` (`= R.one`) at `fxSecuritySemiring` — the
var rule with the security semiring's unit. -/
theorem securityVarUsedIsClassified :
    HasGradeOver fxSecuritySemiring [GTypeOver.base]
        (GradeVectorOver.single fxSecuritySemiring 1 0 SecurityGrade.classified)
        (GradedLambda.var 0) GTypeOver.base :=
  HasGradeOver.var (R := fxSecuritySemiring) [GTypeOver.base] 0 GTypeOver.base rfl

/-- **Corpus entry — explicit information-flow leak rejected (security, §27.2 / §12.2; Denning-Denning
1977).**  A directly-used secret variable canNOT be graded `unclassified` (public): the var rule fixes
its grade to `R.one = classified` and there is no subsumption to lower it, so `unclassified =
classified` — refuted by `SecurityGrade.noConfusion`.  The grade-level noninterference baseline: a
secret cannot be laundered to public by direct use (only an explicit `declassify`, absent from this
calculus, could). -/
theorem securityDirectUseCannotBePublic :
    ¬ HasGradeOver fxSecuritySemiring [GTypeOver.base]
        (GradeVectorOver.single fxSecuritySemiring 1 0 SecurityGrade.unclassified)
        (GradedLambda.var 0) GTypeOver.base := by
  intro typed
  obtain ⟨_lookupOk, gradesEq⟩ := HasGradeOver.invertVar typed
  have headEq : SecurityGrade.unclassified = fxSecuritySemiring.one := by
    have reduced :
        GradeVectorOver.cons SecurityGrade.unclassified GradeVectorOver.nil =
          GradeVectorOver.cons fxSecuritySemiring.one GradeVectorOver.nil := gradesEq
    exact (GradeVectorOver.cons.inj reduced).1
  exact SecurityGrade.noConfusion headEq

/-- The implicit-flow MECHANISM, positive: applying a classified selector `s` (index 1, a chooser at
function type) to a public base value `a` (index 0) grades the result `classified` at the selector
position — the App-scaling rule `functionGrades + binderGrade · argumentGrades` carries the selector's
secrecy into the result.  `s a` grades both positions `classified`. -/
theorem securitySelectorAppResultIsClassified :
    HasGradeOver fxSecuritySemiring
        [GTypeOver.base, GTypeOver.arrow SecurityGrade.classified GTypeOver.base GTypeOver.base]
        (GradeVectorOver.cons SecurityGrade.classified
          (GradeVectorOver.cons SecurityGrade.classified GradeVectorOver.nil))
        (GradedLambda.app (GradedLambda.var 1) (GradedLambda.var 0)) GTypeOver.base :=
  HasGradeOver.app (R := fxSecuritySemiring)
    [GTypeOver.base, GTypeOver.arrow SecurityGrade.classified GTypeOver.base GTypeOver.base]
    SecurityGrade.classified GTypeOver.base GTypeOver.base
    (GradeVectorOver.single fxSecuritySemiring 2 1 fxSecuritySemiring.one)
    (GradeVectorOver.single fxSecuritySemiring 2 0 fxSecuritySemiring.one)
    (GradedLambda.var 1) (GradedLambda.var 0)
    (HasGradeOver.var (R := fxSecuritySemiring) _ 1
      (GTypeOver.arrow SecurityGrade.classified GTypeOver.base GTypeOver.base) rfl)
    (HasGradeOver.var (R := fxSecuritySemiring) _ 0 GTypeOver.base rfl)

/-- **Corpus entry — implicit information-flow leak rejected (security, §27.2 / §12.2; the application
form of "implicit flow via branch on secret").**  The selector-application `s a` canNOT be graded with
the selector position `unclassified`: `invertApp` + `invertVar` fix the App-scaled position-1 grade to
`one + binderGrade · zero`, which `classified`-poisons to `classified` for EVERY binder grade — so the
claimed `unclassified` forces `unclassified = classified`, refuted by `SecurityGrade.noConfusion`.  A
secret that CONTROLS a selection (Church-encoded branching is application) cannot be laundered to public
through the result.  The native-`if` catalog surface remains pending (`implicitFlowBug_isPending`); this
is the application-form defense the App-scaling rule already provides. -/
theorem securitySelectorAppCannotLaunderSelector :
    ¬ HasGradeOver fxSecuritySemiring
        [GTypeOver.base, GTypeOver.arrow SecurityGrade.classified GTypeOver.base GTypeOver.base]
        (GradeVectorOver.cons SecurityGrade.classified
          (GradeVectorOver.cons SecurityGrade.unclassified GradeVectorOver.nil))
        (GradedLambda.app (GradedLambda.var 1) (GradedLambda.var 0)) GTypeOver.base := by
  intro typed
  obtain ⟨binderGrade, _domain, _functionGrades, _argumentGrades, functionTyped, argumentTyped,
    gradesEq⟩ := HasGradeOver.invertApp typed
  obtain ⟨_fnLookup, fnGradesEq⟩ := HasGradeOver.invertVar functionTyped
  obtain ⟨_argLookup, argGradesEq⟩ := HasGradeOver.invertVar argumentTyped
  subst fnGradesEq argGradesEq
  -- casing the abstract binder grade makes scale/add concrete; injection exposes the position-1
  -- equality `unclassified = classified` (the selector is `+`-poisoned), refuted by noConfusion
  cases binderGrade <;>
    · injection gradesEq with _headEq tailEq
      injection tailEq with selectorEq _
      exact SecurityGrade.noConfusion selectorEq

/-- **The security noninterference witnesses are non-vacuous.**  The classified selector genuinely types
(positive), and BOTH laundering attempts — direct-use-to-public and selector-to-public — are concretely
rejected.  The first security-dimension entries in the §27.2 corpus are load-bearing, not placeholders. -/
theorem securityNoninterferenceWitnessed :
    HasGradeOver fxSecuritySemiring
        [GTypeOver.base, GTypeOver.arrow SecurityGrade.classified GTypeOver.base GTypeOver.base]
        (GradeVectorOver.cons SecurityGrade.classified
          (GradeVectorOver.cons SecurityGrade.classified GradeVectorOver.nil))
        (GradedLambda.app (GradedLambda.var 1) (GradedLambda.var 0)) GTypeOver.base ∧
    (¬ HasGradeOver fxSecuritySemiring [GTypeOver.base]
        (GradeVectorOver.single fxSecuritySemiring 1 0 SecurityGrade.unclassified)
        (GradedLambda.var 0) GTypeOver.base) ∧
    (¬ HasGradeOver fxSecuritySemiring
        [GTypeOver.base, GTypeOver.arrow SecurityGrade.classified GTypeOver.base GTypeOver.base]
        (GradeVectorOver.cons SecurityGrade.classified
          (GradeVectorOver.cons SecurityGrade.unclassified GradeVectorOver.nil))
        (GradedLambda.app (GradedLambda.var 1) (GradedLambda.var 0)) GTypeOver.base) :=
  ⟨securitySelectorAppResultIsClassified, securityDirectUseCannotBePublic,
    securitySelectorAppCannotLaunderSelector⟩

/-! ## Part 6 — the fractional-permission overallocation rejection (the §27.2 usage/fractional entry)

The last `no` usage row — fractional-permission overallocation (Boyland 2003) — flips to encodable now
that the §6.4 separation-logic permission algebra ships (`FX1Poly.Modal.Permission`).  The bug: combining
two fractional ownership shares whose total exceeds the whole (`2/3 + 2/3 = 4/3 > 1`) and treating the
result as a valid share — overallocating, so two parties both believe they hold more than the whole.  The
sound algebra's guarded `add` rejects it (→ `conflict`), and its soundness theorem
(`Permission.add_neverOverallocates`) guarantees a fitting combine never yields an over-full share.  These
re-export the shipped witnesses, corpus-cited.

  * `corpusRejectsFractionalOverallocation` — the REJECTION: the sound `add` of `2/3 + 2/3` is
    `conflict`, not an over-full share.
  * `corpusNaiveFractionalOverallocates` — the BUG: the unguarded `naiveAdd` of `2/3 + 2/3` produces an
    over-full share (`frac 12 9`) that does NOT fit the whole.
-/

/-- **Corpus entry — fractional-permission overallocation rejected (usage/fractional, §27.2 / §6.4;
Boyland 2003).**  The sound guarded `add` of `2/3 + 2/3` (a total exceeding the whole) yields `conflict`,
not an over-full share.  Re-exported from `FX1Poly.Modal.Permission.soundAddRejectsOverallocation`; backed
by `Permission.add_neverOverallocates` (a fitting combine never overallocates). -/
theorem corpusRejectsFractionalOverallocation :
    Permission.add (.frac 2 3) (.frac 2 3) = .conflict :=
  Permission.soundAddRejectsOverallocation

/-- The unsound NAIVE combine (the bug) over-allocates: `naiveAdd (2/3) (2/3) = frac 12 9` (= 4/3 > 1), an
over-full share that does NOT fit the whole.  The contrast that makes the guard load-bearing. -/
theorem corpusNaiveFractionalOverallocates :
    Permission.naiveAdd (.frac 2 3) (.frac 2 3) = .frac 12 9 ∧
    (Permission.naiveAdd (.frac 2 3) (.frac 2 3)).fitsWhole = false :=
  ⟨Permission.naiveAddOverallocates, Permission.naiveOverallocationDoesNotFit⟩

end FX1Poly.Typed

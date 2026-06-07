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
share (Boyland 2003), flipping that catalog entry to encodable.  Finally — since a session endpoint IS
a linear resource and aliasing it IS using it twice — it adds the linearity-MECHANISM defense of
session-endpoint aliasing (Part 7): the self-application `g g` (occurrence usage `ω = 1 + 1`) is
rejected at a linear AND an erased declaration and accepted only at an unrestricted one, so the usage
discipline permits endpoint aliasing iff the endpoint is declared unrestricted.  The native
session-typed surface (send/recv protocol state) stays honestly pending, exactly as Part 5 keeps the
native `if` pending.

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
obstruction beyond the shipped length-1 no-`Type:Type`.  (The FULL "no Girard cycle of any length" guarantee —
length-3 and beyond — is `grownUniverseTypingHasNoCycleOfAnyLength` in `UniverseClassificationAcyclic.lean`,
which generalizes this finite obstruction via the transitive closure + a strictly-increasing size measure;
that file's `grownUniverseTypingHasNoTwoCycleViaChain` re-derives this 2-cycle as its length-2 instance.) -/
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

/-- Ledger fact (HONEST pending): session-endpoint aliasing is NOT yet encodable AS THE CATALOGED
NATIVE-SESSION BUG — the protocol/session dimension (send/recv endpoints carrying protocol state) is
not engine-typed.  (The aliasing MECHANISM — a linear endpoint used twice — IS already defended in its
linearity form: see Part 7's `corpusRejectsLinearEndpointAliasing`, where the usage discipline rejects
the self-application `g g` at a linear declaration.  The pending surface is specifically the native
session type, exactly as `implicitFlowBug_isPending`'s pending surface is the native `if`.) -/
theorem sessionBug_isPending :
    KnownTypeTheoryBug.sessionEndpointAliased.isEncodableNow = false := rfl

/-- Ledger fact (HONEST pending): the ML value restriction is NOT yet encodable AS THE CATALOGED
NATIVE-ML-REFERENCE BUG — there are no ML-style polymorphic mutable references with let-generalization in
the kernel.  (The value-restriction MECHANISM — generalizing a NON-VALUE (a `ref` allocation) is unsound,
because the cell's write-at-`a` and read-at-`b` compose to a universal coercion — IS now defended in Part 9:
`refAllocationIsNotGeneralizableUnderValueRestriction` rejects generalizing the allocation, and
`naivePolyRefCoercionIsUnsound` / `valueRestrictionSeparatesSoundFromUnsound` show the naive generalization's
`∀ a b, a → b` is uninhabited while the value-restricted `∀ a, a → a` is inhabited.  The pending surface is
specifically the native ML-style mutable reference, exactly as Parts 5/7/8 keep their native surfaces
pending.) -/
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

/-- Ledger fact (HONEST pending): the constant-time secret-memory-access bug is NOT yet encodable AS THE
CATALOGED NATIVE-CT BUG — there is no `with CT` effect tracking secret-dependent memory access.  (The
constant-time MECHANISM — a secret-dependent memory ADDRESS leaking through the access TRACE — IS now
defended in its trace form: see Part 8's `secretIndexAccessViolatesConstantTime` and
`constantTimeStrictlyStrongerThanNoninterference`, where the address-trace noninterference property is
violated by a secret index EVEN WHEN value-noninterference holds.  The pending surface is specifically the
native `with CT` effect, exactly as Part 5 keeps the native `if` and Part 7 the native session type pending.) -/
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

/-! ## Part 7 — the linearity mechanism of session-endpoint aliasing (the first protocol-adjacent entry)

The `sessionEndpointAliased` row stays pending for the NATIVE session-typed surface (send/recv endpoints
carrying protocol state — a dimension the kernel does not yet type).  But the bug's MECHANISM is pure
linearity: a session endpoint is a linear resource, and "aliasing" it is using it twice — exactly the
violation the usage dimension already rejects.  So, mirroring Part 5 (which defends the implicit-flow
MECHANISM in application form while the native `if` stays pending), this part adds the linearity-form
defense of endpoint aliasing, re-using the shipped usage substrate (`FX1Poly.Modal.dupReduct` = `g g`,
the §27.2 self-application whose β-reduct uses its argument twice).

The witnessed term `g g` is the usage-calculus image of the body of `δ = λx. x x` — the very
self-application whose application to itself is the Ω combinator (`UntypedOmegaNotStronglyNormalizing`).
The SAME syntactic shape that breaks strong normalization in the TYPE dimension breaks linearity in the
USAGE dimension: `δ` admits no linear function type because its binder is used twice.  The two
pathologies — non-termination and resource-aliasing — share one syntactic root.

  * `aliasedLinearEndpointUsageIsOmega` — the endpoint's occurrence multiplicity from two uses is `ω`
    (`= 1 + 1`), computed.
  * **`corpusRejectsLinearEndpointAliasing`** — a LINEAR endpoint used twice is rejected (`ω ≰ 1`).  The
    linearity core of session-endpoint aliasing (re-exported from `dupReduct_illGraded`).
  * `corpusRejectsErasedEndpointAliasing` — even an ERASED (ghost, grade-`0`) endpoint cannot be aliased
    (`ω ≰ 0`).
  * `unrestrictedEndpointAliasingAccepted` — an UNRESTRICTED (grade-`ω`) resource CAN be aliased
    (`ω ≤ ω`): the discipline does not over-reject.
  * **`endpointAliasingPermittedIffUnrestricted`** — the line is drawn EXACTLY at `ω`: aliasing rejected
    at grades `0` and `1`, accepted only at `ω`.  The usage discipline permits endpoint aliasing iff the
    endpoint is declared unrestricted — the precise linearity content of "a linear channel cannot be
    aliased".
-/

/-- An ERASED (ghost, grade-`0`) declared context for a single endpoint resource. -/
def erasedEndpointContext : GradeVector := GradeVector.cons UsageGrade.zero GradeVector.nil

/-- An UNRESTRICTED (grade-`ω`) declared context for a single endpoint resource. -/
def unrestrictedEndpointContext : GradeVector := GradeVector.cons UsageGrade.omega GradeVector.nil

/-- The endpoint's occurrence multiplicity from being used twice (`g g`) is `ω` (`= 1 + 1`, the §6.1
usage semiring) — computed by `rfl`.  The quantitative reason aliasing a linear endpoint is unsound. -/
theorem aliasedLinearEndpointUsageIsOmega :
    GradedLambda.usage 1 dupReduct = GradeVector.cons UsageGrade.omega GradeVector.nil :=
  rfl

/-- **Corpus entry — linear session-endpoint aliasing rejected (usage/linearity, §27.2 / §11; the
linearity mechanism of "session endpoint aliased").**  A LINEAR endpoint used twice (`g g`) is NOT
well-graded: its occurrence usage is `ω` and `ω ≤ 1` is false.  This is the linearity core of
session-endpoint aliasing (a session channel is a linear resource; aliasing = double use).  Re-exported
from the usage dimension's `dupReduct_illGraded`; the native session-typed surface stays pending
(`sessionBug_isPending`). -/
theorem corpusRejectsLinearEndpointAliasing :
    ¬ GradedLambda.WellGraded 1 dupReduct linearG :=
  dupReduct_illGraded

/-- Even an ERASED (ghost, grade-`0`) endpoint cannot be aliased: `g g` uses it `ω` times and `ω ≤ 0`
is false.  Aliasing escapes every sub-unrestricted declaration, not just the linear one. -/
theorem corpusRejectsErasedEndpointAliasing :
    ¬ GradedLambda.WellGraded 1 dupReduct erasedEndpointContext := by
  intro wellGraded
  obtain ⟨headBelow, _⟩ := wellGraded
  exact Bool.noConfusion headBelow

/-- An UNRESTRICTED (grade-`ω`) resource CAN be aliased: `g g` uses it `ω` times and `ω ≤ ω`.  The
discipline does not over-reject — duplication is exactly what the unrestricted grade grants. -/
theorem unrestrictedEndpointAliasingAccepted :
    GradedLambda.WellGraded 1 dupReduct unrestrictedEndpointContext :=
  ⟨rfl, True.intro⟩

/-- **The usage discipline permits endpoint aliasing iff the endpoint is unrestricted.**  Aliasing
(`g g`) is rejected at the erased (`0`) and linear (`1`) declarations and accepted only at the
unrestricted (`ω`) one — the line is drawn EXACTLY at `ω`.  This is the precise linearity content of
"a linear session channel cannot be aliased", and it is non-vacuous: both rejections and the acceptance
are concrete.  (The native session-typed surface — send/recv protocol state — stays pending; this is
the linearity-mechanism defense the usage dimension already provides.) -/
theorem endpointAliasingPermittedIffUnrestricted :
    (¬ GradedLambda.WellGraded 1 dupReduct erasedEndpointContext) ∧
    (¬ GradedLambda.WellGraded 1 dupReduct linearG) ∧
    GradedLambda.WellGraded 1 dupReduct unrestrictedEndpointContext :=
  ⟨corpusRejectsErasedEndpointAliasing, corpusRejectsLinearEndpointAliasing,
    unrestrictedEndpointAliasingAccepted⟩

/-! ## Part 8 — the constant-time mechanism: address-trace noninterference (constant-time strictly
       stronger than value noninterference)

The `constantTimeSecretMemoryAccess` row (§12.5; Barthe et al. constant-time crypto) stays pending for the
NATIVE constant-time surface — a `with CT` effect tracking secret-dependent memory access — which the kernel
does not yet have.  But the bug's MECHANISM is witnessable now, and it is genuinely DISTINCT from the Part-5
information-flow witnesses: constant-time constrains the execution TRACE (which memory ADDRESS is touched —
the timing/access-pattern channel), not the output VALUE.  A secret-dependent ADDRESS leaks even when no
secret-dependent VALUE ever reaches an output — so constant-time is STRICTLY STRONGER than value
noninterference.

This part models a memory access by its two observables — the ADDRESS it touches (`addressTrace`, the index)
and the VALUE it reads (`valueObservable`) — each as a function of the secret input.  Constant-time is
address-trace noninterference (`isConstantTime`: the address is secret-independent); value noninterference
(`isValueNoninterfering`: the value is secret-independent) is the Part-5-style property.  Mirroring Parts 5
and 7 (which defend the implicit-flow and session-aliasing MECHANISMS in their encodable forms while the
native surfaces stay pending), this defends the constant-time mechanism in its trace form.

  * `publicConstantIndexAccessIsConstantTime` — the GOOD case: a public constant index (address `0`
    regardless of the secret) is constant-time.  The discipline does not over-reject.
  * **`secretIndexAccessViolatesConstantTime`** — the BUG: indexing AT the secret makes the address trace
    BE the secret (`addressTrace s = s`), so two secrets `0 ≠ 1` give different traces — not constant-time.
  * `secretIndexConstantArrayIsValueNoninterfering` — the secret-indexed read of a CONSTANT (public) array
    is value-noninterference-CLEAN: the array ignores the index, so the secret cannot affect the VALUE read.
  * **`constantTimeStrictlyStrongerThanNoninterference`** — ★ the headline: that very access is
    value-noninterference-clean YET violates constant-time — a term that leaks the secret through the address
    channel while leaking nothing through the value channel.  Exactly the timing/access-pattern leak the
    §27.2 / §12.5 entry warns about.  (The secret index is also `classified`-graded by Part 5's security
    semiring, so a native `with CT` discipline forbidding classified indices would reject it; the trace-level
    strictness is what makes constant-time a distinct, stronger property than value noninterference.)
  * `corpusConstantTimeMechanismWitnessed` — non-vacuity: the good case IS constant-time, the bug is NOT, and
    the bug is value-noninterference-clean.  Layer-1 carries the constant-time mechanism, not a placeholder.
-/

/-- A memory address (an index into memory). -/
abbrev MemoryAddress := Nat

/-- A memory access, modeled by its two observables as functions of the secret input: `indexOf` is the
ADDRESS it touches (the index, the constant-time-relevant channel) and `arrayContents` is the (public)
memory whose cell it reads.  Pure data (no kernel term) — strictly positive, like the session/permission
algebras. -/
structure SecretDependentAccess where
  indexOf : Nat → MemoryAddress
  arrayContents : MemoryAddress → Nat

/-- The ADDRESS-TRACE observable: which memory address the access touches, as a function of the secret —
the constant-time channel (§12.5: the access pattern must not depend on secret inputs). -/
def SecretDependentAccess.addressTrace (access : SecretDependentAccess) (secret : Nat) : MemoryAddress :=
  access.indexOf secret

/-- The VALUE observable: the contents read at the touched address, as a function of the secret — the
information-flow channel that value noninterference (Part 5) constrains. -/
def SecretDependentAccess.valueObservable (access : SecretDependentAccess) (secret : Nat) : Nat :=
  access.arrayContents (access.indexOf secret)

/-- **Constant-time = address-trace noninterference (§12.5).**  The access is constant-time iff the address
it touches does not depend on the secret — the execution trace (which memory location) is secret-independent. -/
def SecretDependentAccess.isConstantTime (access : SecretDependentAccess) : Prop :=
  ∀ firstSecret secondSecret : Nat, access.addressTrace firstSecret = access.addressTrace secondSecret

/-- **Value noninterference (§12.2).**  The access is value-noninterfering iff the value it reads does not
depend on the secret — the Part-5-style information-flow property on the VALUE channel. -/
def SecretDependentAccess.isValueNoninterfering (access : SecretDependentAccess) : Prop :=
  ∀ firstSecret secondSecret : Nat,
    access.valueObservable firstSecret = access.valueObservable secondSecret

/-- A constant public index: touch address `0` regardless of the secret (the constant-time-clean access). -/
def publicConstantIndexAccess (contents : MemoryAddress → Nat) : SecretDependentAccess :=
  { indexOf := fun _ => 0, arrayContents := contents }

/-- A secret-dependent index: touch the address that IS the secret (the constant-time-violating access). -/
def secretIndexAccess (contents : MemoryAddress → Nat) : SecretDependentAccess :=
  { indexOf := fun secret => secret, arrayContents := contents }

/-- **The good case is constant-time (no over-rejection).**  A public constant index touches address `0`
for every secret, so its address trace is secret-independent — constant-time. -/
theorem publicConstantIndexAccessIsConstantTime (contents : MemoryAddress → Nat) :
    (publicConstantIndexAccess contents).isConstantTime :=
  fun _ _ => rfl

/-- **Corpus entry — secret-dependent memory access violates constant-time (security/constant-time, §27.2 /
§12.5; Barthe et al.).**  Indexing AT the secret makes the address trace BE the secret
(`addressTrace s = s`), so secrets `0` and `1` touch different addresses — the access pattern leaks the
secret.  Not constant-time. -/
theorem secretIndexAccessViolatesConstantTime (contents : MemoryAddress → Nat) :
    ¬ (secretIndexAccess contents).isConstantTime := by
  intro isCT
  exact Nat.noConfusion (isCT 0 1)

/-- The secret-indexed read of a CONSTANT (public) array is value-noninterference-CLEAN: the array ignores
the index (every cell holds `fixedValue`), so the secret cannot affect the VALUE read — no information flows
through the value channel. -/
theorem secretIndexConstantArrayIsValueNoninterfering (fixedValue : Nat) :
    (secretIndexAccess (fun _ => fixedValue)).isValueNoninterfering :=
  fun _ _ => rfl

/-- ★ **Constant-time is STRICTLY STRONGER than value noninterference (§27.2 / §12.5).**  The secret-indexed
read of a constant public array is value-noninterference-CLEAN (the value never changes with the secret) yet
VIOLATES constant-time (the ADDRESS it touches IS the secret) — a term that leaks the secret through the
access-pattern/timing channel while leaking nothing through the value channel.  This is precisely why
constant-time is a distinct, stronger discipline than information-flow noninterference: noninterference would
accept this access (the output is secret-independent), but constant-time rejects it (the address is not). -/
theorem constantTimeStrictlyStrongerThanNoninterference (fixedValue : Nat) :
    (secretIndexAccess (fun _ => fixedValue)).isValueNoninterfering ∧
    ¬ (secretIndexAccess (fun _ => fixedValue)).isConstantTime :=
  ⟨secretIndexConstantArrayIsValueNoninterfering fixedValue,
    secretIndexAccessViolatesConstantTime (fun _ => fixedValue)⟩

/-- **The constant-time mechanism witness is non-vacuous.**  The public constant-index access IS
constant-time, the secret-index access is NOT, and that secret-index access is value-noninterference-clean —
all concrete.  Layer-1 of the §27.3 defense carries the constant-time mechanism, not a placeholder; the
native `with CT` surface stays pending (`constantTimeBug_isPending`). -/
theorem corpusConstantTimeMechanismWitnessed (fixedValue : Nat) :
    (publicConstantIndexAccess (fun _ => fixedValue)).isConstantTime ∧
    ¬ (secretIndexAccess (fun _ => fixedValue)).isConstantTime ∧
    (secretIndexAccess (fun _ => fixedValue)).isValueNoninterfering :=
  ⟨publicConstantIndexAccessIsConstantTime (fun _ => fixedValue),
    secretIndexAccessViolatesConstantTime (fun _ => fixedValue),
    secretIndexConstantArrayIsValueNoninterfering fixedValue⟩

/-! ## Part 9 — the ML value restriction: generalizing a non-value is unsound (the last §27.2 mechanism)

The `mlValueRestriction` row (Wright 1995) is the LAST §27.2 pending entry without a mechanism defense.  Its
native surface — ML-style polymorphic mutable references with let-generalization — is not in the kernel, but
the bug's MECHANISM is witnessable: generalizing the type of a NON-VALUE (a `ref` allocation) is unsound,
because the resulting polymorphic cell can be WRITTEN at one type and READ at another, composing into a
universal coercion.  The value restriction is the syntactic discipline that fixes it: generalize only
SYNTACTIC VALUES (lambdas, variables), never computations.

This part models both halves.  The SYNTACTIC half: a tiny ML expression (`MLExpr`), the value predicate
(`isSyntacticValue` — lambdas and variables are values; applications and `ref` allocations are not, since a
`ref` allocates — an effect), and the restriction (`isGeneralizableUnderValueRestriction := isSyntacticValue`)
versus naive "generalize everything" (`isGeneralizableNaively`).  The SEMANTIC half: the TYPE that naive
generalization would assign to write-then-read on a polymorphic reference — a universal coercion
`∀ a b, a → b` (`NaivePolyRefCoercion`) — is proved UNINHABITED (it yields a closed inhabitant of `Empty`),
while the value-restricted type `∀ a, a → a` (`ValueRestrictedRefCoercion`, write and read at the single
allocation type) is INHABITED by the identity.  This completes the §27.2 corpus's mechanism coverage: all
four pending rows now carry a mechanism defense.

  * `lambdaIsGeneralizableUnderValueRestriction` / `variableIsGeneralizableUnderValueRestriction` — the GOOD
    cases: syntactic values ARE generalizable (no over-restriction).
  * **`refAllocationIsNotGeneralizableUnderValueRestriction`** — the BUG SOURCE rejected: a `ref` allocation
    is not a syntactic value, so the value restriction refuses to generalize it.
  * `applicationIsNotGeneralizableUnderValueRestriction` — applications (general computations) are likewise
    not generalized.
  * `valueRestrictionRejectsRefThatNaiveAccepts` — the restriction is STRICTLY tighter than naive
    generalization on exactly the dangerous case: naive accepts the `ref` allocation, the restriction rejects it.
  * **`naivePolyRefCoercionIsUnsound`** — the SEMANTIC unsoundness: the universal coercion `∀ a b, a → b` that
    naive generalization permits is uninhabited (instantiate at `Unit → Empty`, apply to `Unit.unit`, derive
    a closed `Empty`).  Generalizing the non-value really is catastrophic.
  * `valueRestrictedRefCoercionIsInhabited` — by contrast `∀ a, a → a` (the value-restricted read/write at the
    single allocation type) is inhabited by the identity — sound.
  * **`valueRestrictionSeparatesSoundFromUnsound`** — ★ the bundle: the naive coercion is uninhabited and the
    value-restricted one is inhabited.  The value restriction is exactly the line between the unsound universal
    coercion and the sound identity coercion.
-/

/-- A tiny ML-style expression: variables and lambdas (the syntactic VALUES), applications and `ref`
allocations (the non-values — an application may diverge or effect, a `ref` allocates mutable state).  Pure
data — strictly positive. -/
inductive MLExpr where
  | var (index : Nat)
  | lam (body : MLExpr)
  | app (function : MLExpr) (argument : MLExpr)
  | refAlloc (initial : MLExpr)

/-- The syntactic-VALUE predicate (Wright 1995): lambdas and variables are values; applications and `ref`
allocations are not.  Full enumeration, no wildcard — propext-free. -/
def MLExpr.isSyntacticValue : MLExpr → Bool
  | .var _ => true
  | .lam _ => true
  | .app _ _ => false
  | .refAlloc _ => false

/-- **The value restriction**: a let-bound expression's type may be generalized iff the expression is a
SYNTACTIC VALUE.  This is the whole fix — generalizing only values, never computations. -/
def MLExpr.isGeneralizableUnderValueRestriction (expr : MLExpr) : Bool := expr.isSyntacticValue

/-- The NAIVE (unsound) rule the value restriction replaces: generalize EVERY let-bound expression,
value or not.  The rule that admits the ML mutable-reference unsoundness. -/
def MLExpr.isGeneralizableNaively (_expr : MLExpr) : Bool := true

/-- The GOOD case: a lambda IS a syntactic value, so the value restriction generalizes it (no
over-restriction — polymorphism is retained for values). -/
theorem lambdaIsGeneralizableUnderValueRestriction (body : MLExpr) :
    (MLExpr.lam body).isGeneralizableUnderValueRestriction = true := rfl

/-- The GOOD case: a variable IS a syntactic value, so it is generalizable under the value restriction. -/
theorem variableIsGeneralizableUnderValueRestriction (index : Nat) :
    (MLExpr.var index).isGeneralizableUnderValueRestriction = true := rfl

/-- **Corpus entry — the value restriction rejects generalizing a `ref` allocation (usage/polymorphic
references, §27.2; Wright 1995).**  A `ref` allocation is not a syntactic value, so its type is NOT
generalized — the cell stays monomorphic at its allocation type, preventing the write-at-`a`/read-at-`b`
universal coercion.  The syntactic core of the ML value restriction. -/
theorem refAllocationIsNotGeneralizableUnderValueRestriction (initial : MLExpr) :
    (MLExpr.refAlloc initial).isGeneralizableUnderValueRestriction = false := rfl

/-- Applications (general computations) are likewise not syntactic values, so not generalized — the value
restriction confines polymorphism to values across the board, not only `ref`. -/
theorem applicationIsNotGeneralizableUnderValueRestriction (function argument : MLExpr) :
    (MLExpr.app function argument).isGeneralizableUnderValueRestriction = false := rfl

/-- **The value restriction is STRICTLY tighter than naive generalization on exactly the dangerous case.**
The naive rule generalizes the `ref` allocation (`= true`); the value restriction rejects it (`= false`).
The discipline difference is precisely on the bug source. -/
theorem valueRestrictionRejectsRefThatNaiveAccepts (initial : MLExpr) :
    (MLExpr.refAlloc initial).isGeneralizableNaively = true ∧
    (MLExpr.refAlloc initial).isGeneralizableUnderValueRestriction = false :=
  ⟨rfl, rfl⟩

/-- The TYPE naive generalization assigns to write-then-read on a polymorphic reference: write at an
arbitrary type, read at an arbitrary type — a UNIVERSAL COERCION `∀ a b, a → b`.  The unsound consequence
the value restriction prevents. -/
abbrev NaivePolyRefCoercion := ∀ firstType secondType : Type, firstType → secondType

/-- The TYPE under the value restriction: the reference is monomorphic at its ALLOCATION type, so write and
read share one type — only identity coercions `∀ a, a → a` arise. -/
abbrev ValueRestrictedRefCoercion := ∀ allocationType : Type, allocationType → allocationType

/-- **Corpus entry — naive generalization of a polymorphic reference is unsound (§27.2; Wright 1995).**  The
universal coercion `∀ a b, a → b` that naive generalization permits is UNINHABITED: instantiate at
`Unit → Empty`, apply to `Unit.unit`, and obtain a closed inhabitant of `Empty` (hence `False`).  Generalizing
the non-value `ref` allocation really does collapse the type system. -/
theorem naivePolyRefCoercionIsUnsound : NaivePolyRefCoercion → False :=
  fun coerce => nomatch (coerce Unit Empty Unit.unit)

/-- By contrast the value-restricted read/write type `∀ a, a → a` (write and read at the single allocation
type) is INHABITED — by the identity.  The value restriction keeps the reference sound. -/
theorem valueRestrictedRefCoercionIsInhabited : Nonempty ValueRestrictedRefCoercion :=
  ⟨fun _allocationType value => value⟩

/-- ★ **The value restriction separates the sound coercion from the unsound one.**  The naive universal
coercion `∀ a b, a → b` is uninhabited; the value-restricted identity coercion `∀ a, a → a` is inhabited.
The value restriction is exactly the line between them — generalizing the `ref` non-value would land on the
uninhabited side, which is why the restriction forbids it.  Completes the §27.2 corpus mechanism coverage. -/
theorem valueRestrictionSeparatesSoundFromUnsound :
    (NaivePolyRefCoercion → False) ∧ Nonempty ValueRestrictedRefCoercion :=
  ⟨naivePolyRefCoercionIsUnsound, valueRestrictedRefCoercionIsInhabited⟩

end FX1Poly.Typed

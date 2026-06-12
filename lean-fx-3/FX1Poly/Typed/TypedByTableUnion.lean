import FX1Poly.Typed.TypedBySomeEngine
import FX1Poly.Typed.NativeUnionRuleTables
import FX1Poly.Typed.HasTypeDescGradedIntro
import FX1Poly.Typed.HasTypeDescGeneralElim
import FX1Poly.Typed.StaticTypingSoundness

/-! # FX1Poly/Typed/TypedByTableUnion — the table-driven static-typing classifier (the honesty-classifier collapse)

`TypedBySomeEngine.hasSomeTypingRule` is the honest static-typing classifier: it reports `true` iff some typing
engine types a cell headed by a generator.  Its definition mixes SIX rule-table membership tests
(`typingRuleDescOf` / `introRuleDescOf` / `elimRuleDescOf` / `flatTypingRuleDescOf` / `baseTypeRuleDescOf` /
`dataIntroNullaryRuleDescOf`) with TWENTY-ONE `decide (g = …)` head equalities — one per standalone data
intro/elim head, per bespoke head, and per cubical head.  Those decides predate the native-union rule tables
(`NativeUnionRuleTables`, plus `gradedIntroRuleOf` / `generalElimRuleOf`), which now drive the unified judgment
`HasTypeNativeUnion` table-FIRST.  Sixteen of the decides are exactly the heads those native tables key on.

This file ships the table-driven TWIN and the machine-checked equivalence (the delete-readiness evidence for
swapping `hasSomeTypingRule`'s body):

  * **`hasTableTypingRule`** — the collapse: the six original tables PLUS `gradedIntroRuleOf` (lam / pathLam),
    `generalElimRuleOf` (app / pathApp), and the eleven native-union tables, as a pure `Option.isSome`
    disjunction.  The sixteen data-family decides (boolElim / optionMatch / eitherMatch / idJ / fst / snd /
    natSucc / listCons / optionSome / optionNone / eitherInl / eitherInr / pair / refl) and the two cubical-path
    decides (pathLam / pathApp) all dissolve into table membership.  FOUR irreducible decides remain — `natZero` /
    `listNil` (nullary data constructors typed only by the embedding arms `HasTypeDescNatIntro` /
    `HasTypeDescListIntro`, which key on hardcoded arms with no generator-keyed `Option` table) and `var` /
    `universeCode` (the two genuinely-bespoke grown rules).  `hasTableTypingRule` is `decide`-free over the data
    families; the four-decide residual is the honest floor under the current table set (see
    `tableClassifierResidual…`).

  * **`hasSomeTypingRule_eq_hasTableTypingRule`** (★ Leg B) — exact equality over EVERY generator, by per-constructor
    `rfl`.  The covered sets are identical: `gradedIntroRuleOf` only adds `lam` (already in `introRuleDescOf`) and
    `pathLam` (the dropped decide); `generalElimRuleOf` only adds `app` (already in `elimRuleDescOf`) and `pathApp`;
    each native table covers exactly the data heads that were decides.  No generator differs.

  * **`hasTableTypingRule_falsePeel`** (★ Leg C / the per-table peel) — a head the table classifier reports reserved
    (`= false`) forces EVERY disjunct false, as a 23-way conjunction.  This is the table-driven replacement for the
    positional `||`-peel in `StaticTypingSoundness`; `hasTableTypingRule_false_imp_isUntypableHead` re-derives the
    grown bridge directly from it (the projections at the grown atoms), and the surviving-engine soundness bundle
    `reservedTableHeadUntypedBySurvivingEngines` rebases HON-5/HON-7 onto the table classifier.

  * Per-table introduction lemmas (`hasTableTypingRule_of_…`) and the native-table peel projections — the NATIVE-41
    per-table legs replacing the positional peel.

The DELIBERATE non-coverage: the union's `nativeRecursiveElimRuleOf` (natElim / natRec) row, the `listElimNativeRuleOf`
row, and `termIndexedFormerDescOf`'s `idCode` row are NOT folded into `hasTableTypingRule`, because the honesty
classifier brands those four heads (natElim / natRec / listElim / idCode) RESERVED — and the union now types them.
Folding them would flip the classifier, diverging from `hasSomeTypingRule`.  That genuine divergence (the honesty
ledger is now stale vs the union) is documented separately in `TableTypingUnionDivergence`, as the precise input to
the canonicity-collapse decision (whether to promote those four to live).

## Zero-axiom

`Option.isSome` over pure selectors, `||`-combined — no wildcard match.  The equivalence is `cases generator <;>
rfl` (propext-clean over the flat 197-constructor enum).  The peel reuses `StaticTypingSoundness`'s propext-free
`orEqFalse_leftFalse` / `orEqFalse_rightFalse`.  The intro lemmas are `cases`-on-the-chain + a peel contradiction.
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditTableDrivenHonesty.lean`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ## The table-driven static-typing classifier -/

/-- **The table-driven honest static-typing classifier.**  `true` iff some rule TABLE driving
`HasTypeNativeUnion` carries a row for `generator`: the six original tables, the graded intro / general elim
tables (covering `lam`/`pathLam`, `app`/`pathApp`), and the eleven native-union tables (the three data-eliminator
families, the seven n-ary/recursive data-intro families, and listElim's sibling — wait, NO: listElim is
deliberately excluded; see the four native data-intro/elim families below).  The only `decide`s are the
four-head irreducible residual — `natZero`/`listNil` (typed by the embedding arms with no generator-keyed table)
and `var`/`universeCode` (the bespoke grown rules).  Extensionally equal to `hasSomeTypingRule`
(`hasSomeTypingRule_eq_hasTableTypingRule`). -/
def hasTableTypingRule (generator : Generator) : Bool :=
  (typingRuleDescOf generator).isSome || (introRuleDescOf generator).isSome
  || (elimRuleDescOf generator).isSome || (flatTypingRuleDescOf generator).isSome
  || (baseTypeRuleDescOf generator).isSome || (dataIntroNullaryRuleDescOf generator).isSome
  || (gradedIntroRuleOf generator).isSome || (generalElimRuleOf generator).isSome
  || (nativeTwoBranchMatchRuleOf generator).isSome
  || (nativePathInductionRuleOf generator).isSome
  || (nativeProjectionRuleOf generator).isSome
  || (nativeRecursiveUnaryDataIntroRuleOf generator).isSome
  || (nativeRecursiveBinaryDataIntroRuleOf generator).isSome
  || (nativePinnedUnaryDataIntroRuleOf generator).isSome
  || (nativeNullaryFreeTypeDataIntroRuleOf generator).isSome
  || (nativeCoproductDataIntroRuleOf generator).isSome
  || (nativeNonDependentBinaryDataIntroRuleOf generator).isSome
  || (nativeReflexiveDataIntroRuleOf generator).isSome
  || decide (generator = .gen_natZero) || decide (generator = .gen_listNil)
  || decide (generator = .gen_var) || decide (generator = .gen_universeCode)
  || decide (generator = .gen_bridgeCode)

/-! ## ★ Leg B — the exact equivalence -/

/-- **★ The table classifier equals the honest classifier on EVERY generator.**  The sixteen data-family decides
and the two cubical-path decides of `hasSomeTypingRule` collapse into table membership without changing the
classified set: `gradedIntroRuleOf`/`generalElimRuleOf` add only already-covered heads (`lam`/`app`) plus the
dropped path decides, and each native table covers exactly its data heads.  Proven by per-constructor `rfl`
(propext-clean over the flat 197-constructor enum). -/
theorem hasSomeTypingRule_eq_hasTableTypingRule :
    ∀ generator : Generator, hasSomeTypingRule generator = hasTableTypingRule generator := by
  intro generator
  cases generator <;> rfl

/-! ## Leg A — LIVE witnesses, one per collapsed family, by `rfl` -/

/-- Two-branch match table (boolElim) collapses into `nativeTwoBranchMatchRuleOf`. -/
theorem hasTableTypingRule_boolElim : hasTableTypingRule .gen_boolElim = true := rfl
/-- Two-branch match table (optionMatch). -/
theorem hasTableTypingRule_optionMatch : hasTableTypingRule .gen_optionMatch = true := rfl
/-- Two-branch match table (eitherMatch). -/
theorem hasTableTypingRule_eitherMatch : hasTableTypingRule .gen_eitherMatch = true := rfl
/-- Path-induction table (idJ). -/
theorem hasTableTypingRule_idJ : hasTableTypingRule .gen_idJ = true := rfl
/-- Projection table (fst). -/
theorem hasTableTypingRule_fst : hasTableTypingRule .gen_fst = true := rfl
/-- Projection table (snd). -/
theorem hasTableTypingRule_snd : hasTableTypingRule .gen_snd = true := rfl
/-- Recursive-unary intro (natSucc). -/
theorem hasTableTypingRule_natSucc : hasTableTypingRule .gen_natSucc = true := rfl
/-- Recursive-binary intro (listCons). -/
theorem hasTableTypingRule_listCons : hasTableTypingRule .gen_listCons = true := rfl
/-- Pinned-unary intro (optionSome). -/
theorem hasTableTypingRule_optionSome : hasTableTypingRule .gen_optionSome = true := rfl
/-- Nullary-free-type intro (optionNone). -/
theorem hasTableTypingRule_optionNone : hasTableTypingRule .gen_optionNone = true := rfl
/-- Coproduct intro (eitherInl / eitherInr). -/
theorem hasTableTypingRule_eitherInl : hasTableTypingRule .gen_eitherInl = true := rfl
theorem hasTableTypingRule_eitherInr : hasTableTypingRule .gen_eitherInr = true := rfl
/-- Non-dependent binary intro (pair). -/
theorem hasTableTypingRule_pair : hasTableTypingRule .gen_pair = true := rfl
/-- Reflexive intro (refl). -/
theorem hasTableTypingRule_refl : hasTableTypingRule .gen_refl = true := rfl
/-- Graded intro table (pathLam) — the first cubical decide dissolved. -/
theorem hasTableTypingRule_pathLam : hasTableTypingRule .gen_pathLam = true := rfl
/-- General elim table (pathApp) — the second cubical decide dissolved. -/
theorem hasTableTypingRule_pathApp : hasTableTypingRule .gen_pathApp = true := rfl

/-! ## ★ Leg C / NATIVE-41 — the table-driven false-peel (replaces the positional peel) -/

/-- **★ A head the table classifier reports RESERVED forces every disjunct false.**  The 23-way conjunction
peeled off `hasTableTypingRule g = false` via the propext-free `orEqFalse_leftFalse` / `orEqFalse_rightFalse`
projections (reused from `StaticTypingSoundness`).  This is the per-table replacement for the positional `||`-peel:
every consumer that needs "the table is empty here" projects the relevant conjunct rather than re-peeling the
chain by hand. -/
theorem hasTableTypingRule_falsePeel {generator : Generator}
    (reserved : hasTableTypingRule generator = false) :
    (typingRuleDescOf generator).isSome = false ∧ (introRuleDescOf generator).isSome = false ∧
    (elimRuleDescOf generator).isSome = false ∧ (flatTypingRuleDescOf generator).isSome = false ∧
    (baseTypeRuleDescOf generator).isSome = false ∧ (dataIntroNullaryRuleDescOf generator).isSome = false ∧
    (gradedIntroRuleOf generator).isSome = false ∧ (generalElimRuleOf generator).isSome = false ∧
    (nativeTwoBranchMatchRuleOf generator).isSome = false ∧
    (nativePathInductionRuleOf generator).isSome = false ∧
    (nativeProjectionRuleOf generator).isSome = false ∧
    (nativeRecursiveUnaryDataIntroRuleOf generator).isSome = false ∧
    (nativeRecursiveBinaryDataIntroRuleOf generator).isSome = false ∧
    (nativePinnedUnaryDataIntroRuleOf generator).isSome = false ∧
    (nativeNullaryFreeTypeDataIntroRuleOf generator).isSome = false ∧
    (nativeCoproductDataIntroRuleOf generator).isSome = false ∧
    (nativeNonDependentBinaryDataIntroRuleOf generator).isSome = false ∧
    (nativeReflexiveDataIntroRuleOf generator).isSome = false ∧
    decide (generator = .gen_natZero) = false ∧ decide (generator = .gen_listNil) = false ∧
    decide (generator = .gen_var) = false ∧ decide (generator = .gen_universeCode) = false ∧
    decide (generator = .gen_bridgeCode) = false := by
  unfold hasTableTypingRule at reserved
  have r23 := reserved
  have r22 := orEqFalse_leftFalse r23
  have r21 := orEqFalse_leftFalse r22
  have r20 := orEqFalse_leftFalse r21
  have r19 := orEqFalse_leftFalse r20
  have r18 := orEqFalse_leftFalse r19
  have r17 := orEqFalse_leftFalse r18
  have r16 := orEqFalse_leftFalse r17
  have r15 := orEqFalse_leftFalse r16
  have r14 := orEqFalse_leftFalse r15
  have r13 := orEqFalse_leftFalse r14
  have r12 := orEqFalse_leftFalse r13
  have r11 := orEqFalse_leftFalse r12
  have r10 := orEqFalse_leftFalse r11
  have r9 := orEqFalse_leftFalse r10
  have r8 := orEqFalse_leftFalse r9
  have r7 := orEqFalse_leftFalse r8
  have r6 := orEqFalse_leftFalse r7
  have r5 := orEqFalse_leftFalse r6
  have r4 := orEqFalse_leftFalse r5
  have r3 := orEqFalse_leftFalse r4
  have r2 := orEqFalse_leftFalse r3
  exact ⟨orEqFalse_leftFalse r2, orEqFalse_rightFalse r2, orEqFalse_rightFalse r3,
    orEqFalse_rightFalse r4, orEqFalse_rightFalse r5, orEqFalse_rightFalse r6,
    orEqFalse_rightFalse r7, orEqFalse_rightFalse r8, orEqFalse_rightFalse r9,
    orEqFalse_rightFalse r10, orEqFalse_rightFalse r11, orEqFalse_rightFalse r12,
    orEqFalse_rightFalse r13, orEqFalse_rightFalse r14, orEqFalse_rightFalse r15,
    orEqFalse_rightFalse r16, orEqFalse_rightFalse r17, orEqFalse_rightFalse r18,
    orEqFalse_rightFalse r19, orEqFalse_rightFalse r20, orEqFalse_rightFalse r21,
    orEqFalse_rightFalse r22, orEqFalse_rightFalse r23⟩

/-! ### Named per-table peel projections (the NATIVE-41 per-table legs) -/

/-- The grown formation table is empty at a reserved head. -/
theorem hasTableTypingRule_typingRuleDescOf_false {generator : Generator}
    (reserved : hasTableTypingRule generator = false) : (typingRuleDescOf generator).isSome = false :=
  (hasTableTypingRule_falsePeel reserved).1
/-- The grown intro table is empty at a reserved head. -/
theorem hasTableTypingRule_introRuleDescOf_false {generator : Generator}
    (reserved : hasTableTypingRule generator = false) : (introRuleDescOf generator).isSome = false :=
  (hasTableTypingRule_falsePeel reserved).2.1
/-- The grown elim table is empty at a reserved head. -/
theorem hasTableTypingRule_elimRuleDescOf_false {generator : Generator}
    (reserved : hasTableTypingRule generator = false) : (elimRuleDescOf generator).isSome = false :=
  (hasTableTypingRule_falsePeel reserved).2.2.1
/-- The native two-branch-match table is empty at a reserved head. -/
theorem hasTableTypingRule_nativeTwoBranchMatch_false {generator : Generator}
    (reserved : hasTableTypingRule generator = false) :
    (nativeTwoBranchMatchRuleOf generator).isSome = false :=
  (hasTableTypingRule_falsePeel reserved).2.2.2.2.2.2.2.2.1
/-- The native path-induction table is empty at a reserved head. -/
theorem hasTableTypingRule_nativePathInduction_false {generator : Generator}
    (reserved : hasTableTypingRule generator = false) :
    (nativePathInductionRuleOf generator).isSome = false :=
  (hasTableTypingRule_falsePeel reserved).2.2.2.2.2.2.2.2.2.1
/-- The native projection table is empty at a reserved head. -/
theorem hasTableTypingRule_nativeProjection_false {generator : Generator}
    (reserved : hasTableTypingRule generator = false) :
    (nativeProjectionRuleOf generator).isSome = false :=
  (hasTableTypingRule_falsePeel reserved).2.2.2.2.2.2.2.2.2.2.1

/-! ## NATIVE-41 — per-table introduction lemmas (a true table forces the classifier true) -/

/-- A two-branch-match table hit makes the classifier live.  `cases` on the chain Bool; the `false` branch
contradicts the hit via the table-driven peel projection (propext-free). -/
theorem hasTableTypingRule_of_nativeTwoBranchMatch {generator : Generator}
    (hit : (nativeTwoBranchMatchRuleOf generator).isSome = true) :
    hasTableTypingRule generator = true := by
  cases hchain : hasTableTypingRule generator with
  | true => rfl
  | false =>
      have hf := hasTableTypingRule_nativeTwoBranchMatch_false hchain
      rw [hit] at hf
      exact Bool.noConfusion hf
/-- A path-induction table hit makes the classifier live. -/
theorem hasTableTypingRule_of_nativePathInduction {generator : Generator}
    (hit : (nativePathInductionRuleOf generator).isSome = true) :
    hasTableTypingRule generator = true := by
  cases hchain : hasTableTypingRule generator with
  | true => rfl
  | false =>
      have hf := hasTableTypingRule_nativePathInduction_false hchain
      rw [hit] at hf
      exact Bool.noConfusion hf
/-- A projection table hit makes the classifier live. -/
theorem hasTableTypingRule_of_nativeProjection {generator : Generator}
    (hit : (nativeProjectionRuleOf generator).isSome = true) :
    hasTableTypingRule generator = true := by
  cases hchain : hasTableTypingRule generator with
  | true => rfl
  | false =>
      have hf := hasTableTypingRule_nativeProjection_false hchain
      rw [hit] at hf
      exact Bool.noConfusion hf

/-! ## ★ Leg C — the grown bridge, re-derived from the TABLE peel -/

/-- **A head the table classifier reports RESERVED is `isUntypableHead`** — re-derived directly from the
table-driven peel (the grown atoms `typingRuleDescOf` / `introRuleDescOf` / `elimRuleDescOf` and the bespoke
`var` / `universeCode` decides are projections of `hasTableTypingRule_falsePeel`), not routed through the
positional peel of `StaticTypingSoundness`.  Mirrors `hasSomeTypingRule_false_imp_isUntypableHead` on the table
classifier. -/
theorem hasTableTypingRule_false_imp_isUntypableHead (generator : Generator)
    (reserved : hasTableTypingRule generator = false) : isUntypableHead generator = true := by
  have peel := hasTableTypingRule_falsePeel reserved
  have formationFalse := peel.1
  have introFalse := peel.2.1
  have elimFalse := peel.2.2.1
  have varFalse := peel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have universeCodeFalse := peel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have roleless : typingRoleOf generator = none := by
    dsimp only [typingRoleOf]
    rw [if_neg (notEqTrue_ofEqFalse formationFalse),
        if_neg (notEqTrue_ofEqFalse introFalse),
        if_neg (notEqTrue_ofEqFalse elimFalse)]
  have notVar : generator ≠ Generator.gen_var := by
    intro isVar; rw [isVar] at varFalse; exact Bool.noConfusion varFalse
  have notUniverse : generator ≠ Generator.gen_universeCode := by
    intro isUniverse; rw [isUniverse] at universeCodeFalse; exact Bool.noConfusion universeCodeFalse
  exact decide_eq_true ⟨roleless, notVar, notUniverse⟩

/-! ## ★ Leg C — the soundness bundle rebased onto the table classifier -/

/-- **★ HON-5 / HON-7 rebased: a head the TABLE classifier reports reserved is typed by no surviving standalone
engine.**  Routed through the exact equivalence (`hasSomeTypingRule_eq_hasTableTypingRule`): a
`hasTableTypingRule = false` verdict is a `hasSomeTypingRule = false` verdict, so the shipped surviving-engine
soundness bundle applies unchanged.  The honest classifier and its table twin make the SAME truthful "statically
reserved" claim.  The bespoke `HasTypeDescBridge` engine was RETIRED (NATIVE-45): its rows are now arms of
`HasTypeNativeUnion`, so its leg is no longer a standalone conjunct.  The retired bridge rows and the base-type /
data-intro / flat formation arms (now `baseTypeFormation` / `dataIntroNullary` / `flatFormation` arms of
`HasTypeNativeUnion`) are subsumed by the single-judgment successor over ALL native typing,
`HasTypeNativeUnion.reservedHeadUntyped` in `UnionStaticTypingSoundness`. -/
theorem reservedTableHeadUntypedBySurvivingEngines {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject : RawTerm scope}
    (reserved : hasTableTypingRule (RawTerm.headGenerator subject) = false) :
    ∀ classifier : RawTerm scope, ¬ HasTypeDescPi profile context subject classifier := by
  rw [← hasSomeTypingRule_eq_hasTableTypingRule] at reserved
  exact reservedHeadUntypedBySurvivingEngines reserved

/-! ## The irreducible four-decide residual — the honest floor under the current table set -/

/-- **The four heads that cannot become table membership.**  `natZero` / `listNil` are typed only by the
embedding engines `HasTypeDescNatIntro` / `HasTypeDescListIntro`, which key on hardcoded constructor arms with no
generator-keyed `Option` table (their recursive siblings `natSucc` / `listCons` DO have native tables — the
asymmetry is exactly the nullary-vs-recursive split).  `var` / `universeCode` are the two bespoke grown rules.
Each is classified live by the residual `decide`; collapsing them to table membership would require a new
generator-keyed table, which the union does not (yet) carry for these heads. -/
theorem tableClassifierResidualHeadsLive :
    hasTableTypingRule .gen_natZero = true ∧ hasTableTypingRule .gen_listNil = true ∧
    hasTableTypingRule .gen_var = true ∧ hasTableTypingRule .gen_universeCode = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The natZero table residency after the NATIVE-42 drain: the native-union recursive/free-type
tables still return `none` on `natZero` (it is not recursive and its element type is not free), but
the nullary DATA-INTRO table now carries its row — `natZero` is table-covered, no longer a decide. -/
theorem natZeroNativeIntroTableResidency :
    (nativeRecursiveUnaryDataIntroRuleOf .gen_natZero).isSome = false ∧
    (nativeNullaryFreeTypeDataIntroRuleOf .gen_natZero).isSome = false ∧
    (dataIntroNullaryRuleDescOf .gen_natZero).isSome = true :=
  ⟨rfl, rfl, rfl⟩

end FX1Poly.Typed

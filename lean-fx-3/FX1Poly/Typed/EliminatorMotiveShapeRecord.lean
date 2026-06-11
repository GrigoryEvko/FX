import FX1Poly.Typed.HasTypeDescBoolElim

/-! # FX1Poly/Typed/EliminatorMotiveShapeRecord — the Phase-Z₀ motive-migration spike (Z0-DECIDE)

The mandated pre-construction spike for the Phase-Z₀ eliminator-motive migration (the gateway
to revised-MILESTONE-A coverage breadth per §11.8.12.1; tracker series M24-Z2…M30-Z1).  Census,
machine-checked current-shape pins, a feasibility witness for the cascade-free alternative, and
the costed decision record.

## The census (2026-06, Phase-Z eliminator migration COMPLETE — all eight stages SHIPPED)

ALL EIGHT eliminator generators now carry their Phase-Z motive shape.  `gen_boolElim`,
`gen_listElim`, `gen_optionMatch` and `gen_eitherMatch` sit at arity 4 binderShifts `[1,0,0,0]`;
`gen_natElim` / `gen_natRec` at arity 4 binderShifts `[1,0,2,0]` (the recursors' succ-branch sits
under TWO binders — predecessor + induction hypothesis — and the succ-ι SUBSTITUTES into it); and
`gen_idJ` / `gen_idStrictRec` at arity 3 binderShifts `[2,0,0]` (the identity-eliminator motive
binds the endpoint and the path, so it sits under TWO binders, and its ι DISCARDS the motive —
pure base-case projection).  The data/list/bool/match families carry children
`(motive, …branches…, scrutinee)` with the motive a term under one binder and the scrutinee LAST;
the identity eliminators carry `(motive, baseCase, witness)` with the motive a term under two
binders and the witness LAST (all pinned as `rfl` theorems below).  The Z₀ eliminator migration is
COMPLETE — every eliminator stores its motive.  The binder-shift MECHANISM is live and proven
(`gen_lam` at `[0,1]`, `gen_boolElim`/`gen_listElim`/`gen_optionMatch`/`gen_eitherMatch` at
`[1,0,0,0]`, `gen_natElim`/`gen_natRec` at `[1,0,2,0]`, `gen_idJ`/`gen_idStrictRec` at `[2,0,0]`).

BLAST RADIUS of changing arity+binderShifts for the 8 generators: 1406 files in
FX1Poly/FX0Poly/FX1PolyAudit mention at least one eliminator generator (262 for `gen_natElim`
alone); `RawTermChildren` is INDEXED by `binderShifts`, so every `.mkGen .gen_natElim …` term
in every fixture changes TYPE, every `Step.iota*` rule restates, every SR/reducibility/
canonicity/candidate arm re-proves, the certifier/serializer/FX0 encoding re-derive, and the
Church-iota faithfulness corpus rebuilds.  This is the per-constructor cascade wall multiplied
by eight — months of mechanical migration.

## The feasibility finding: dependent elimination over the motive-carrying shape

What Z₀ buys semantically is DEPENDENT elimination (induction): branches at `motive(true)` /
`motive(false)`, result at `motive(scrutinee)`.  With the Phase-Z boolElim shape SHIPPED the motive
is now STORED in the cell (the head child under one binder); the dependent RULE reads that stored
motive and applies it by `subst0`:

  * `HasTypeDescBoolElimDependent` — the dependent boolean eliminator: the cell's stored
    `motive : RawTerm (scope+1)` types the branches at `subst0 motive boolTrue/boolFalse` and the
    `boolElim(motive, s, t, e)` cell at `subst0 motive s`.  (Pre-Phase-Z this spike carried the
    motive EXTRINSICALLY over the flat substrate to witness feasibility without the cascade; the
    motive is now in the term, so checking the dependent rule is decidable — read the motive child.)
  * `subsumesSimpleShape` — the constant motive (`weaken resultType`) collapses every premise
    and the conclusion to the shipped non-dependent rule's shape (`weaken_subst_singleton`), so
    the dependent rule strictly generalizes `HasTypeDescBoolElim`.
  * `dependentIotaComputesTyped_true` — ι-coherence at value scrutinees is BY CONSTRUCTION: at
    `scrutinee = boolTrue` the conclusion classifier is literally the then-branch's premise
    type, so the ι-reduct is typed at the conclusion classifier verbatim (no SR needed) while
    `Step.iotaBoolTrue` fires.

## The costed decision record (substrate changes are user decisions — T2 precedent)

**Route A — the full Z₀ substrate migration (spec §11.8 as written; M24-Z2…M30-Z1):** change
arity+binderShifts for 8 generators to the motive-carrying shapes.  Cost: the 1406-file blast
radius above; every shipped eliminator theorem re-lands.  Buys: the motive is STORED in the
term, so dependent-elimination CHECKING is decidable (read the motive child, check premises),
uniqueness of typing survives, and the kernel calculus matches fx_design's dependent
eliminators.  This is the spec-committed END STATE for revised-A breadth; the open question is
WHEN, and whether to stage it per-eliminator.

**Route B — extrinsic-motive standalone judgments over the FLAT substrate (this spike's
witness):** dependent rules with the motive as a premise.  Cost per eliminator family: ~1
firing on the established standalone-engine template; ZERO substrate cascade.  Named LIMITS
(the honest boundary, both classical reasons real kernels store motives):
  (1) NO decidable checking — the motive is not in the term, so checking requires motive
      INFERENCE (higher-order unification, undecidable in general);
  (2) typing is NOT unique at neutral scrutinees — distinct motives agreeing on the
      constructors but differing elsewhere give the same term distinct classifiers.
Route B delivers the dependent-elimination RELATION (enough for canonicity/SR-style
metatheory and for stating induction principles) but NOT the revised-A decidable-checking
criterion on the dependent fragment.

**Route C — defer Z₀ until the ProfileExtension calculus absorbs it:** rejected — the
extension calculus (V2-L5) is itself unbuilt, so this inverts the dependency.

**RECOMMENDATION:** Route B bricks now where dependent elimination unblocks metatheory (per
eliminator family, cascade-free, spec-by-addition), and Route A as the user-scheduled substrate
commitment — staged ONE eliminator at a time (boolElim first: smallest corpus, validated the
migration playbook; listElim second, exercising the recursive cons-ι motive threading; natElim +
natRec next, the FIRST shift-2 succ-branch and the FIRST SUBSTITUTING ι, the recursors' 262-file
footprint; optionMatch + eitherMatch next, the non-recursive function-branch matches whose ι DISCARDS
the motive; idJ + idStrictRec last, the identity eliminators at arity 3 shift `[2,0,0]` whose
two-binder motive is DISCARDED by the refl-ι — pure base-case projection), each stage an atomic
green commit.  The `rfl` pins below are the regression tripwires: each Route-A stage breaks exactly
its own generator's two pins, by design.  The Z₀ eliminator migration is COMPLETE — all eight
generators store their motive.

## Zero-axiom verification

The 16 pins are `rfl` on the `Generator.arity`/`Generator.binderShifts` tables; the dependent
judgment is a single positive arm; the subsumption is `weaken_subst_singleton` rewriting; the
ι-coherence is constructor-side (premises in, `Step.iotaBoolTrue`, premise out).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe

/-! ### The shape pins — Route A's regression tripwires.

All eight eliminator generators have LANDED their Phase-Z motive shape; their pins record the SHIPPED
motive-carrying shape.  Two naming conventions coexist by necessity.  SIX legacy-named pins keep the
`…isFlat` suffix (a historical artifact, kept stable so the per-declaration audit references survive)
while asserting the new shipped shape: boolElim / listElim / natElim / natRec.  TEN `…hasMotive` pins
carry the descriptive name: the FOUR optionMatch/eitherMatch pins (renamed when their migration landed)
plus the FOUR NEW idJ/idStrictRec pins (the `…isFlat` name would assert the literal opposite of the new
`[2,0,0]` body, so the descriptive name was used from the start).  The Z₀ migration is COMPLETE — no pin
remains to flip. -/

theorem boolElim_arity_isFlat : Generator.gen_boolElim.arity = 4 := rfl
theorem boolElim_binderShifts_isFlat :
    Generator.gen_boolElim.binderShifts = [1, 0, 0, 0] := rfl
theorem natElim_arity_isFlat : Generator.gen_natElim.arity = 4 := rfl
theorem natElim_binderShifts_isFlat : Generator.gen_natElim.binderShifts = [1, 0, 2, 0] := rfl
theorem natRec_arity_isFlat : Generator.gen_natRec.arity = 4 := rfl
theorem natRec_binderShifts_isFlat : Generator.gen_natRec.binderShifts = [1, 0, 2, 0] := rfl
theorem listElim_arity_isFlat : Generator.gen_listElim.arity = 4 := rfl
theorem listElim_binderShifts_isFlat : Generator.gen_listElim.binderShifts = [1, 0, 0, 0] := rfl
theorem optionMatch_arity_hasMotive : Generator.gen_optionMatch.arity = 4 := rfl
theorem optionMatch_binderShifts_hasMotive :
    Generator.gen_optionMatch.binderShifts = [1, 0, 0, 0] := rfl
theorem eitherMatch_arity_hasMotive : Generator.gen_eitherMatch.arity = 4 := rfl
theorem eitherMatch_binderShifts_hasMotive :
    Generator.gen_eitherMatch.binderShifts = [1, 0, 0, 0] := rfl
theorem idJ_arity_hasMotive : Generator.gen_idJ.arity = 3 := rfl
theorem idJ_binderShifts_hasMotive : Generator.gen_idJ.binderShifts = [2, 0, 0] := rfl
theorem idStrictRec_arity_hasMotive : Generator.gen_idStrictRec.arity = 3 := rfl
theorem idStrictRec_binderShifts_hasMotive :
    Generator.gen_idStrictRec.binderShifts = [2, 0, 0] := rfl

/-- **The DEPENDENT boolean eliminator over the motive-carrying shape.**
A standalone judgment over the Phase-Z `boolElimCell`: the motive is the cell's STORED head child (a
term under one binder), applied by `subst0`.  Branches are typed at the motive instantiated at the
matching constructor; the eliminator is typed at the motive instantiated at the scrutinee — genuine
dependent elimination, the motive now in the term (so checking is decidable: read the motive child). -/
inductive HasTypeDescBoolElimDependent (profile : PolyProfile) :
    {scope : Nat} → TypingContext profile scope → RawTerm scope → RawTerm scope → Prop where
  | boolElimDependentIntro {scope : Nat} (context : TypingContext profile scope)
      (motive : RawTerm (scope + 1)) (scrutinee thenBranch elseBranch : RawTerm scope)
      (scrutineeTyped : HasTypeDescDataIntro profile context scrutinee boolTypeCell)
      (thenTyped : HasTypeDescPi profile context thenBranch
        (RawTerm.subst0 motive boolTrueCell))
      (elseTyped : HasTypeDescPi profile context elseBranch
        (RawTerm.subst0 motive boolFalseCell)) :
      HasTypeDescBoolElimDependent profile context
        (boolElimCell motive scrutinee thenBranch elseBranch) (RawTerm.subst0 motive scrutinee)

/-- **★ The dependent rule subsumes the simple one.**  With the CONSTANT motive
(`weaken resultType`), every `subst0` instance collapses to `resultType`
(`weaken_subst_singleton`), recovering exactly the shipped `HasTypeDescBoolElim.boolElimIntro`
premise/conclusion shape — the extrinsic dependent rule is a strict generalization. -/
theorem HasTypeDescBoolElimDependent.subsumesSimpleShape {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (scrutinee thenBranch elseBranch resultType : RawTerm scope)
    (scrutineeTyped : HasTypeDescDataIntro profile context scrutinee boolTypeCell)
    (thenTyped : HasTypeDescPi profile context thenBranch resultType)
    (elseTyped : HasTypeDescPi profile context elseBranch resultType) :
    HasTypeDescBoolElimDependent profile context
      (boolElimCell (RawTerm.weaken resultType) scrutinee thenBranch elseBranch) resultType := by
  have collapseAtTrue :
      RawTerm.subst0 (RawTerm.weaken resultType) boolTrueCell = resultType :=
    RawTerm.weaken_subst_singleton resultType boolTrueCell
  have collapseAtFalse :
      RawTerm.subst0 (RawTerm.weaken resultType) boolFalseCell = resultType :=
    RawTerm.weaken_subst_singleton resultType boolFalseCell
  have collapseAtScrutinee :
      RawTerm.subst0 (RawTerm.weaken resultType) scrutinee = resultType :=
    RawTerm.weaken_subst_singleton resultType scrutinee
  have thenAtMotive : HasTypeDescPi profile context thenBranch
      (RawTerm.subst0 (RawTerm.weaken resultType) boolTrueCell) := by
    rw [collapseAtTrue]; exact thenTyped
  have elseAtMotive : HasTypeDescPi profile context elseBranch
      (RawTerm.subst0 (RawTerm.weaken resultType) boolFalseCell) := by
    rw [collapseAtFalse]; exact elseTyped
  have dependentTyped :=
    HasTypeDescBoolElimDependent.boolElimDependentIntro context
      (RawTerm.weaken resultType) scrutinee thenBranch elseBranch
      scrutineeTyped thenAtMotive elseAtMotive
  rwa [collapseAtScrutinee] at dependentTyped

/-- **★ A dependent eliminator is typed (non-vacuous smoke).**  The constant-motive
instantiation of the shipped simple smoke: `boolElim(boolTrue, Type@0, Type@0) : Type@1`
through the DEPENDENT rule. -/
theorem HasTypeDescBoolElimDependent.ofUniverseCodesTyped {profile : PolyProfile}
    (flag : UniverseFlag) :
    HasTypeDescBoolElimDependent profile (TypingContext.empty : TypingContext profile 0)
      (boolElimCell (RawTerm.weaken (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag))
        boolTrueCell (universeCodeCell LevelExpr.lzero flag)
        (universeCodeCell LevelExpr.lzero flag))
      (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag) :=
  HasTypeDescBoolElimDependent.subsumesSimpleShape TypingContext.empty boolTrueCell
    (universeCodeCell LevelExpr.lzero flag) (universeCodeCell LevelExpr.lzero flag)
    (universeCodeCell (LevelExpr.lsucc LevelExpr.lzero) flag)
    (HasTypeDescDataIntro.boolTrueTyped TypingContext.empty)
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))
    (HasTypeDescPi.ofFormation
      (HasTypeDesc.universeFormation TypingContext.empty LevelExpr.lzero flag))

/-- **★ Dependent ι-coherence at the value scrutinee, BY CONSTRUCTION.**  At
`scrutinee = boolTrue` the dependent conclusion classifier `subst0 motive boolTrue` is
LITERALLY the then-branch's premise type: the eliminator is typed there, `Step.iotaBoolTrue`
fires, and the reduct (the then branch) is typed at the same classifier verbatim — the
extrinsic-motive rule computes without any subject-reduction machinery. -/
theorem dependentBoolElimIotaComputesTyped_true {profile : PolyProfile} {scope : Nat}
    (context : TypingContext profile scope)
    (thenBranch elseBranch : RawTerm scope) (motive : RawTerm (scope + 1))
    (thenTyped : HasTypeDescPi profile context thenBranch
      (RawTerm.subst0 motive boolTrueCell))
    (elseTyped : HasTypeDescPi profile context elseBranch
      (RawTerm.subst0 motive boolFalseCell)) :
    HasTypeDescBoolElimDependent profile context
      (boolElimCell motive boolTrueCell thenBranch elseBranch)
      (RawTerm.subst0 motive boolTrueCell) ∧
    Step (boolElimCell motive boolTrueCell thenBranch elseBranch) thenBranch ∧
    HasTypeDescPi profile context thenBranch (RawTerm.subst0 motive boolTrueCell) :=
  ⟨HasTypeDescBoolElimDependent.boolElimDependentIntro context motive boolTrueCell thenBranch
      elseBranch (HasTypeDescDataIntro.boolTrueTyped context) thenTyped elseTyped,
   Step.iotaBoolTrue, thenTyped⟩

end FX1Poly.Typed

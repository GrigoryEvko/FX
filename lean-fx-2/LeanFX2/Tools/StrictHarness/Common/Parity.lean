import LeanFX2.Tools.StrictHarness.Common.AuditCounts

namespace LeanFX2.Tools

open Lean Elab Command

/-- Get the constructor names of an inductive type. -/
def getInductiveConstructorNames
    (environment : Environment) (inductiveName : Name) :
    Array Name :=
  match environment.find? inductiveName with
  | some (.inductInfo inductiveInfo) => inductiveInfo.ctors.toArray
  | _ => #[]

/-- Strip a namespace prefix off a name and return just the final
component as a string.  Used for matching raw / typed ctor suffixes. -/
def Name.lastSegmentString (someName : Name) : String :=
  match someName with
  | .anonymous => ""
  | .str _ part => part
  | .num _ index => toString index

/-- Documented raw-only constructors that intentionally have no typed
counterpart in the current snapshot.  The remaining entries are
structural raw rules whose typed layer intentionally represents the same
operation through a different constructor family.  Tracking them as
documented exceptions means the parity gate still catches NEW raw-only
ctors going forward, while the remaining gaps are recorded explicitly
rather than being silently allowed.

Discipline for moving an entry OUT of this list: add the matching
`Step.par.X` constructor in `Reduction/ParRed.lean`, mirror the
`Confluence/RawCd.lean` and `Confluence/RawCdLemma.lean` entries to
`Confluence/Cd.lean` and `Confluence/CdLemma.lean`, then delete the
entry below. -/
def isDocumentedRawOnlyParity (rawCtorName : Name) : Bool :=
  let suffix := Name.lastSegmentString rawCtorName
  -- Section A: parametric type-code cong rules (CUMUL-2 cumulativity
  -- type-codes ship raw-only; typed cumulativity uses cumulUp directly).
  suffix == "arrowCodeCong" ||
  suffix == "piTyCodeCong" ||
  suffix == "sigmaTyCodeCong" ||
  suffix == "productCodeCong" ||
  suffix == "sumCodeCong" ||
  suffix == "listCodeCong" ||
  suffix == "optionCodeCong" ||
  suffix == "eitherCodeCong" ||
  suffix == "idCodeCong" ||
  suffix == "equivCodeCong" ||
  suffix == "cumulUpMarkerCong" ||
  -- (D3.6-P1 `uaToEquivCong` entry removed in P3 — typed mirror
  -- `Step.par.uaToEquivCong` now ships as part of the
  -- `Term.uaToEquiv` typed cascade.)
  -- (D3.6-P2 `equivApplyCong` entry removed in P4 — typed mirror
  -- `Step.par.equivApplyCong` now ships as part of the
  -- `Term.equivApply` typed cascade.)
  -- Section B: refl cong rule (typed Term.refl uses different reduction
  -- shape; raw reflCong is structural-only).
  suffix == "reflCong" ||
  -- Section C: deep cubical β rule for transp-at-constant-path.  The typed
  -- mirror would require Step.par.transpReflBetaDeep with a path-reduction
  -- premise across heterogeneous `pathRawSource` raw shape; this is a
  -- raw-only confluence-closure mechanism (D2.5.4-G).  Typed transp β is
  -- already covered through `Step.par.transpReflBeta` (shallow form,
  -- shipped) for the typed bridge target #1555 — which is itself a
  -- confluence-only mechanism when combined with cd's `cdTranspCase`
  -- β-firing.  The deep par ctor exists purely to close the cd cascade
  -- via `RawStep.par.weaken_inv` (Phase G.0).
  suffix == "transpReflBetaDeep" ||
  -- D2.5.5 transpPi β (CCHM transport through Π type).  Shallow
  -- (`transpPiBeta`) and deep (`transpPiBetaDeep`) variants ship
  -- raw-only; typed `Step.transpPi` mirror is deferred to ticket
  -- D2.5.5-J (#1656).  Confluence-only mechanism activated through
  -- `cdTranspCase`'s extended pathLam-non-weaken arm dispatching to
  -- `cdTranspPiCase` when `matchTranspPiBetaShape?` fires.
  suffix == "transpPiBeta" ||
  suffix == "transpPiBetaDeep" ||
  -- Section D: D3.6-S1 univalence-β raw rules.  Typed `Term.transp` requires
  -- its path argument at type `Ty.path ...`, but typed `Term.uaToEquiv`
  -- produces type `Ty.equiv ...` (NOT `Ty.path`).  Therefore no typed
  -- `Term.transp` can have a path-raw of `RawTerm.uaToEquiv proofRaw`,
  -- making both `uaBeta` (shallow, `transp (uaToEquiv proof) source ⟶
  -- equivApply (uaToEquiv proof) source`) and `uaBetaDeep` (path develops
  -- to uaToEquiv via parallel reduction) structurally raw-only
  -- confluence-closure mechanisms — kernel-internal univalence-β at the
  -- raw level.  Activated through `cdTranspCase`'s `uaToEquiv` arm in
  -- `Confluence/RawCd.lean`.
  suffix == "uaBeta" ||
  suffix == "uaBetaDeep" ||
  -- Section E: D3.6-S3 compose-β raw rules.  `RawTerm.pathCompose` ships at
  -- the raw layer (binary ctor, `pathCompose left right`), enabling the
  -- headline rule `transp (pathCompose left right) source ⟶ transp right
  -- (transp left source)` to fire syntactically through the cd cascade.
  -- Typed `Term.pathCompose` is the v1.1 D3.10 follow-up; until then,
  -- `pathComposeCong` (cong), `transpCompose` (shallow β), and
  -- `transpComposeDeep` (path-developed β) all ship raw-only.  Activated
  -- through `cdTranspCase`'s `pathCompose` arm in `Confluence/RawCd.lean`.
  suffix == "pathComposeCong" ||
  suffix == "transpCompose" ||
  suffix == "transpComposeDeep" ||
  -- Section F: D3.6-S4 univalence-refl-β raw rules.  `RawTerm.idToEquiv`
  -- ships at the raw layer (unary ctor, `idToEquiv proofRaw`), enabling
  -- the headline rule `idToEquiv (refl _) ⟶ equivIntro (lam (var 0))
  -- (lam (var 0))` to fire syntactically through the cd cascade via
  -- `cdIdToEquivCase`.  Typed `Term.idToEquiv` is the v1.1 follow-up;
  -- until then, `idToEquivCong` (cong), `idToEquivRefl` (shallow β),
  -- and `idToEquivReflDeep` (proof-developed β) all ship raw-only.
  suffix == "idToEquivCong" ||
  suffix == "idToEquivRefl" ||
  suffix == "idToEquivReflDeep" ||
  -- Section G: D3.6-S5 univalence-compose-β raw rules.
  -- `RawTerm.oeqTrans` (binary observational-equality transitivity)
  -- and `RawTerm.equivCompose` (binary equivalence composition) ship
  -- at the raw layer, enabling the headline rule
  -- `idToEquiv (oeqTrans first second) ⟶ equivCompose (idToEquiv
  -- first) (idToEquiv second)` to fire syntactically through the cd
  -- cascade via `cdIdToEquivCase`'s `oeqTrans` arm.  Typed mirrors
  -- (`Term.oeqTrans`, `Term.equivCompose`) are the v1.1 follow-up;
  -- until then, `oeqTransCong` / `equivComposeCong` (cong rules),
  -- `idToEquivCompose` (shallow compose-β), and
  -- `idToEquivComposeDeep` (proof-developed compose-β) all ship
  -- raw-only.
  suffix == "oeqTransCong" ||
  suffix == "equivComposeCong" ||
  suffix == "idToEquivCompose" ||
  suffix == "idToEquivComposeDeep" ||
  -- Section H: D3.6-S6 univalence-refl round-trip-β raw rules.
  -- Headline rule: `equivApply (uaToEquiv (oeqRefl witness)) source
  -- ⟶ source` — applying the identity-equivalence-via-univalence to
  -- a value yields the value unchanged.  Mounted on existing
  -- `RawTerm.equivApply` + `RawTerm.uaToEquiv` + `RawTerm.oeqRefl`
  -- ctors; no new vocabulary.  Both shallow (`uaReflEquivApply`,
  -- equiv-raw is syntactically `uaToEquiv (oeqRefl _)`) and deep
  -- (`uaReflEquivApplyDeep`, equiv-raw develops to `uaToEquiv
  -- (oeqRefl _)` via parallel reduction) ship raw-only.  Typed
  -- `Term.equivApply` cannot have an equiv-raw of `RawTerm.uaToEquiv
  -- (RawTerm.oeqRefl _)` because typed `Term.uaToEquiv proofTerm`
  -- requires `proofTerm : Term ctx (Ty.id ...) ...` while typed
  -- `Term.oeqRefl` produces `Term ctx (Ty.oeqType ...) ...` —
  -- different typed-Ty heads, no typed bridge until v1.1's D3.10
  -- unifies `Ty.id` and `Ty.oeqType`.  Activated through
  -- `cdEquivApplyCase`'s `uaToEquiv` arm (firing the inner
  -- `cdUaToEquivApplyCase`'s `oeqRefl` headline arm) in
  -- `Confluence/RawCd.lean`.
  suffix == "uaReflEquivApply" ||
  suffix == "uaReflEquivApplyDeep" ||
  -- Section I: D2.5.2 cubical hcomp-β raw-only deep variant.
  -- Headline rule: `hcomp (pathLam X.weaken) cap ⟶ cap` —
  -- homogeneous composition with constant-path sides reduces to the
  -- cap (the boundary box is trivially filled).  The shallow form
  -- `hcompBeta` ships its typed mirror `Step.par.hcompBeta` in
  -- Phase B (Reduction/Step.lean + ParRed/ParInductive.lean +
  -- ParStepLift.lean + ConvBridge.lean), so the shallow form is NO
  -- LONGER listed as documented raw-only.  The deep variant
  -- `hcompBetaDeep` (sides develops to `pathLam X.weaken` via
  -- parallel reduction) remains raw-only: its typed mirror would
  -- need `Step.par.hcompBetaDeep` with a path-reduction premise
  -- across a heterogeneous `sidesRawSource` raw shape, which is a
  -- pure confluence-closure mechanism (parallels
  -- `transpReflBetaDeep`).  Activated through `cdHcompCase`'s
  -- `pathLam` arm in `Confluence/RawCd.lean` and discharged in
  -- cd_lemma / cd_dominates via `RawStep.par.weaken_inv`.
  suffix == "hcompBetaDeep" ||
  -- Section J: D2.5.6-Blocker-A `transpFillCong` raw-only cong rule.
  -- `RawTerm.transpFill pathTy currentInterval source` is the CCHM
  -- cubical fill ctor — a raw-only vocabulary that exists to give
  -- the transpPi β rule's contractum a stable boundary substituent
  -- without needing typed `Term.transpFill` (whose typing rule is
  -- the D2.5.6-Blocker-B redesign track #1949).  The structural
  -- cong `transpFillCong` discharges 3-argument pointwise reduction
  -- through `Step.par.transp_inv` and the rename/subst compat
  -- cascade.  Typed mirror is the D2.5.6 follow-up; the raw cong is
  -- enough to land the kernel ctor + cascade while the typing rule
  -- design is settled separately.
  suffix == "transpFillCong"

/-- Build-failing parity gate.  For every constructor of
`LeanFX2.RawStep.par` whose suffix is not in the documented raw-only
list, the constructor with the same suffix must exist in
`LeanFX2.Step.par`. -/
elab "#assert_raw_typed_parity" : command => do
  let environment ← getEnv
  let rawCtors := getInductiveConstructorNames environment `LeanFX2.RawStep.par
  let typedCtors := getInductiveConstructorNames environment `LeanFX2.Step.par
  let typedSuffixes : Std.HashSet String :=
    typedCtors.foldl (init := {}) fun acc ctorName =>
      acc.insert (Name.lastSegmentString ctorName)
  let mut missing : Array Name := #[]
  for rawCtorName in rawCtors do
    let suffix := Name.lastSegmentString rawCtorName
    if !typedSuffixes.contains suffix && !isDocumentedRawOnlyParity rawCtorName then
      missing := missing.push rawCtorName
  if missing.isEmpty then
    logInfo s!"raw/typed parity ok: {rawCtors.size} raw ctors have typed mirror ({typedCtors.size} typed ctors)"
  else
    let perCtorLines := missing.toList.map fun rawCtorName =>
      s!"  - {rawCtorName} -> expected LeanFX2.Step.par.{Name.lastSegmentString rawCtorName} (missing)"
    let header :=
      s!"raw/typed parity FAILED: {missing.size} raw ctors lack typed counterpart"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

/-- Documented typed-only constructors that intentionally have no
raw counterpart in the current snapshot.  STRICT-9 reverse parity:
this is the dual of `isDocumentedRawOnlyParity`.  The typed layer
runs at finer granularity than raw — the same operation is split
across multiple typed cong/sub-step rules whose RawStep.par
counterpart is one umbrella cong rule.  Plus a smaller set of
typed-only β/eq rules that exist only at the typed level by design.

Discipline for moving an entry OUT of this list: add the matching
`RawStep.par.X` constructor in `Reduction/RawPar.lean`, mirror the
`Confluence/Cd.lean` and `Confluence/CdLemma.lean` typed entries to
`Confluence/RawCd.lean` and `Confluence/RawCdLemma.lean`, then delete
the entry below.

Discipline for ADDING entries: every new typed-only Step.par ctor
must come with a docstring justifying why it has no raw mirror
(typically: typed-level type information that doesn't survive raw
projection).  Without justification, the ctor should land with a
RawStep.par mirror first. -/
def isDocumentedTypedOnlyParity (typedCtorName : Name) : Bool :=
  let suffix := Name.lastSegmentString typedCtorName
  -- Section A: fine-grained per-position cong rules (typed has separate
  -- ctors for each subterm; raw uses one umbrella cong per RawTerm
  -- ctor).  Maps to the same operation at raw level.
  suffix == "appLeft" || suffix == "appRight" ||
  suffix == "boolElimScrutinee" || suffix == "boolElimThen" ||
  suffix == "boolElimElse" ||
  suffix == "natElimScrutinee" || suffix == "natElimZero" ||
  suffix == "natElimSucc" ||
  suffix == "natRecScrutinee" || suffix == "natRecZero" ||
  suffix == "natRecSucc" ||
  suffix == "natSuccPred" ||
  suffix == "listConsHead" || suffix == "listConsTail" ||
  suffix == "listElimScrutinee" || suffix == "listElimNil" ||
  suffix == "listElimCons" ||
  suffix == "optionMatchScrutinee" || suffix == "optionMatchNone" ||
  suffix == "optionMatchSome" ||
  suffix == "optionSomeValue" ||
  suffix == "eitherInlValue" || suffix == "eitherInrValue" ||
  suffix == "eitherMatchScrutinee" || suffix == "eitherMatchLeft" ||
  suffix == "eitherMatchRight" ||
  suffix == "fstCong" || suffix == "sndCong" ||
  suffix == "pairRight" ||
  suffix == "lamBody" ||
  suffix == "modIntroInner" || suffix == "modElimInner" ||
  suffix == "subsumeInner" ||
  suffix == "intervalOppInner" ||
  suffix == "intervalMeetLeft" || suffix == "intervalMeetRight" ||
  suffix == "intervalJoinLeft" || suffix == "intervalJoinRight" ||
  suffix == "pathLamBody" ||
  suffix == "pathAppPath" || suffix == "pathAppInterval" ||
  suffix == "transpPath" || suffix == "transpSource" ||
  suffix == "hcompSides" || suffix == "hcompCap" ||
  suffix == "glueIntroBase" || suffix == "glueIntroPartial" ||
  suffix == "glueElimValue" ||
  suffix == "oeqJBase" || suffix == "oeqJWitness" ||
  suffix == "oeqFunextPointwise" ||
  suffix == "idStrictRecBase" || suffix == "idStrictRecWitness" ||
  suffix == "idJBase" || suffix == "idJWitness" ||
  suffix == "equivAppEquiv" || suffix == "equivAppArgument" ||
  suffix == "refineIntroValue" || suffix == "refineIntroProof" ||
  suffix == "refineElimValue" ||
  suffix == "recordIntroField" || suffix == "recordProjRecord" ||
  suffix == "codataUnfoldState" || suffix == "codataUnfoldTransition" ||
  suffix == "codataDestValue" ||
  suffix == "sessionSendChannel" || suffix == "sessionSendPayload" ||
  suffix == "sessionRecvChannel" ||
  suffix == "effectPerformOperation" || suffix == "effectPerformArguments" ||
  -- Section B: typed-Pi-flavored cong rules (raw treats arrow and
  -- Pi uniformly via `app`; typed splits Pi-flavored arms separately
  -- because typed Pi carries a binder type and shifts subst indices).
  suffix == "appPi" || suffix == "appPiLeft" || suffix == "appPiRight" ||
  suffix == "lamPi" || suffix == "lamPiBody" ||
  suffix == "betaAppPi" || suffix == "betaAppPiDeep" ||
  -- Section C: typed-only β/cong for HOTT eq* rules and cumulativity
  -- (D2.6 / CUMUL series — these encode typed-level definitional
  -- equalities that the raw projection collapses).
  suffix == "eqType" || suffix == "eqArrow" ||
  suffix == "eqTypeHet" || suffix == "eqArrowHet" ||
  suffix == "cumulUpInner" || suffix == "cumulUpInnerCong" ||
  -- Section D: heterogeneous equiv/UA intro (MEGA-Z8 — typed-level
  -- heterogeneous variants needed for cross-type observational
  -- reasoning; raw doesn't track types).
  suffix == "equivIntroHetForward" || suffix == "equivIntroHetBackward" ||
  suffix == "equivIntroHetCong" ||
  suffix == "uaIntroHetWitness" || suffix == "uaIntroHetCong" ||
  -- Section E: glue/hcomp/transp/pathApp/pathLam/glueIntro/glueElim/
  -- transp short-form aliases (the raw layer uses a single suffix for
  -- the umbrella; typed splits the same op across multiple ctors).
  suffix == "glueIntro" || suffix == "glueElim" ||
  suffix == "hcomp" || suffix == "hcompPathCong" || suffix == "transp" ||
  suffix == "pathApp" || suffix == "pathLam"

/-- Build-failing reverse parity gate (STRICT-9).  For every
constructor of `LeanFX2.Step.par` whose suffix is not in the
documented typed-only list, the constructor with the same suffix
must exist in `LeanFX2.RawStep.par`.

Catches the failure mode complementary to STRICT-3: a typed β rule
(or fine-grained cong rule) that lands without a documented
justification or a raw mirror, breaking the discipline that every
typed reduction projects to a raw reduction. -/
elab "#assert_typed_raw_parity" : command => do
  let environment ← getEnv
  let rawCtors := getInductiveConstructorNames environment `LeanFX2.RawStep.par
  let typedCtors := getInductiveConstructorNames environment `LeanFX2.Step.par
  let rawSuffixes : Std.HashSet String :=
    rawCtors.foldl (init := {}) fun acc ctorName =>
      acc.insert (Name.lastSegmentString ctorName)
  let mut missing : Array Name := #[]
  for typedCtorName in typedCtors do
    let suffix := Name.lastSegmentString typedCtorName
    if !rawSuffixes.contains suffix && !isDocumentedTypedOnlyParity typedCtorName then
      missing := missing.push typedCtorName
  if missing.isEmpty then
    logInfo s!"typed/raw parity ok: {typedCtors.size} typed ctors have raw mirror or documented typed-only ({rawCtors.size} raw ctors)"
  else
    let perCtorLines := missing.toList.map fun typedCtorName =>
      s!"  - {typedCtorName} -> expected LeanFX2.RawStep.par.{Name.lastSegmentString typedCtorName} (missing) or add to isDocumentedTypedOnlyParity"
    let header :=
      s!"typed/raw parity FAILED: {missing.size} typed ctors lack raw counterpart and are not documented typed-only"
    throwError (header ++ "\n" ++ String.intercalate "\n" perCtorLines)

end LeanFX2.Tools

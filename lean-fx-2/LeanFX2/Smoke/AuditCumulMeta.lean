import LeanFX2.Term
import LeanFX2.Term.Rename
import LeanFX2.Term.Subst
import LeanFX2.Term.SubstHet
import LeanFX2.Term.Pointwise
import LeanFX2.Term.Act
import LeanFX2.Term.SubjectReductionUniverse
import LeanFX2.Foundation.Action
import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.Ty
import LeanFX2.Foundation.TyAct
import LeanFX2.Foundation.SubstActsOnTy
import LeanFX2.Reduction.Step
import LeanFX2.Reduction.ParRed
import LeanFX2.Reduction.Cumul
import LeanFX2.Reduction.CumulSubstCompat
import LeanFX2.Reduction.CumulPairedEnv
import LeanFX2.Reduction.CumulAllais
import LeanFX2.Reduction.ConvCumulHomo
import LeanFX2.Reduction.ConvBridge
import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawDiamond
import LeanFX2.Confluence.CdLemma
import LeanFX2.Confluence.Diamond
import LeanFX2.Confluence.ChurchRosser
import LeanFX2.Confluence.CanonicalForm
import LeanFX2.Bridge
import LeanFX2.HoTT.Univalence
import LeanFX2.HoTT.Funext

/-! # AuditCumulMeta — CUMUL chapter v1.0 integration audit.

Final certification that CUMUL-1 through CUMUL-8 ship as a unified
zero-axiom milestone for lean-fx-2's MLTT + observational HoTT layer.

CUMUL-7 (modal cumul) is DEFERRED — gated on D4 Modal Layer.  The
remaining chapters constitute the load-bearing universe-cumulativity
story for pure MLTT + observational HoTT.

## Lineage summary

* **CUMUL-1**: `Term.cumulUp` ctor + `ConvCumul` relation +
  `ConvCumul.subst_compatible_outer` foundation.  Shipped early-CUMUL
  chain (`Reduction/Cumul.lean` core inductive).

* **CUMUL-1.7**: Pattern 3 paired-env (Allais ICFP'18) — full
  `ConvCumulHomo.subst_compatible_paired_allais` headline.  Shipped
  across commits `8518c90` (PointwiseCompatHomo + lift), `e4e5e49`
  (fundamental lemma + identity-simulation headline), `c076a3f` (FULL
  Pattern 3 homogeneous headline), and `a38ae5c` (wire-in: replace
  cosmetic stub with Pattern 3).  Cascade refactor at commit
  `61f416b` (split CumulSubstCompat 2777 → 328 LoC across 5 files).

* **CUMUL-2**: Per-shape cumul — 10 type-code ctors (arrowCode /
  piTyCode / sigmaTyCode / productCode / sumCode / listCode /
  optionCode / eitherCode / idCode / equivCode) plus the
  architectural breakthrough `RawTerm.cumulUpMarker` (commit
  `8e62c13` Phase A; raw cascade).  Typed Term ctors at commit
  `5fa652a` (CUMUL-2.4+2.5).  Design D unification: `Term.cumulUp`
  Phase B+C+D at commit `43992a5`; ConvCumul + ConvCumulHomo
  Phase E at `b1ba455`; Pattern 2 + 3 cumulUp arms at `ae351fa`;
  audits + per-shape smokes at `842e5b2`.

* **CUMUL-3**: `Step.cumulUpInner` + `Step.par.cumulUpInnerCong`
  reduction rule (commit `ec34407`); raw-layer compat suffices
  finding at commit `5a0c29a` (CUMUL-3.3).

* **CUMUL-4**: `Term.cdRaw` + `Step.par.cdLemmaRaw` + Diamond +
  ChurchRosser through cumulUp (commits `7c4596d`, `298560b`).

* **CUMUL-5**: `Conv` ↔ `ConvCumul` bridges — `Step.toConvCumul`,
  `Conv.toConvCumul`, refl-only inverses (commits `0029ce6` refl
  fragment; `e1158fe` kernel extension; `0ed7896` backward fragment +
  inverse).

* **CUMUL-6**: Subject reduction at `Ty.universe` types
  (`Step.preserves_ty_universe`, `StepStar.preserves_ty_universe`)
  via `IsClosedTy` framework (commit `aae1556`).

* **CUMUL-7**: Modal cumul.  DEFERRED — gated on D4 Modal Layer.

* **CUMUL-8**: Observational HoTT integration — `Step.eqType`,
  `Step.eqArrow`, `Step.eqTypeHet`, `Step.eqArrowHet` reduction
  rules → Univalence + UnivalenceHet + funext + FunextHet zero-
  axiom theorems (commits `08b125e`, `a9bdf68`, `0ce0fd5`,
  `07a7176`, `69a3d27`, `055b40e`, `8a64629`, `6c31a9f`, `436835b`).

## Tier 3 Action framework

Sister sprint (MEGA-Z) ships the unified Action typeclass:

* MEGA-Z1.A: `Action` typeclass foundation (commit `9b39090`)
* MEGA-Z1.B: `RawRenaming` / `RawTermSubst` / `Subst` instances
  (commit `69275e6`)
* MEGA-Z2.A: `Ty.act` recursion engine (commit `dc1716e`)
* MEGA-Z2.6: native `Ty.act_pointwise` / `Ty.act_compose` /
  `Ty.act_identity` (commit `86f12d9`)
* MEGA-Z4.A: `RawTerm.act` recursion engine over all 56 ctors
  (commit `211c2db`)
* MEGA-Z5.A: `Term.act` via `TermActCompat` typeclass + thin-wrapper
  engines (commit `060a9c8`)

## v1.0 milestone

After this audit ships, lean-fx-2 has:
* complete universe hierarchy (Type 0 : Type 1 : Type 2 : ...)
* cumulativity for ALL type codes via `cumulUpMarker`
* subject reduction + confluence + Church-Rosser through cumul
* Univalence + funext (homogeneous + heterogeneous) as zero-axiom
  theorems
* Pattern 3 paired-env Allais simulation framework
* Tier 3 Action framework for future ctor additions

This is the "v1.0 release-quality" mark for the MLTT + observational
HoTT cumulativity story.  Every `#print axioms` below MUST report
"does not depend on any axioms".  Any axiom leak — `propext`,
`Quot.sound`, `Classical.choice`, or any user-declared axiom — is a
REGRESSION in the chain and blocks v1.0. -/

namespace LeanFX2

/-! ## §1. CUMUL-1 — Foundation.

`Term.cumulUp` constructor + `ConvCumul` core inductive +
`ConvCumul.subst_compatible_outer` (the original "outer" Allais arm
predating Pattern 3).  Ships the load-bearing relation that lifts a
Term at a lower universe level to one at a higher level. -/

#print axioms Term.cumulUp
#print axioms ConvCumul
#print axioms ConvCumul.refl
#print axioms ConvCumul.viaUp
#print axioms ConvCumul.trans
#print axioms ConvCumul.subst_compatible_outer

/-! ## §2. CUMUL-1.7 — Pattern 3 paired-env (Allais ICFP'18).

The full Allais paired-env framework: `PointwiseCompat` predicate +
its homogeneous-typed companion `PointwiseCompatHomo` + the
fundamental lemma `Term.subst_compatible_pointwise_allais` (per-arm
dispatch over Term induction) + the identity-simulation headline
`ConvCumul.subst_compatible_paired_allais` + the FULL homogeneous
headline `ConvCumulHomo.subst_compatible_paired_allais` + the
unified entry point `ConvCumul.subst_compatible`.

Forty-plus per-Term-ctor Allais arms (closed-payload, single-subterm
cong, multi-subterm cong, binder, eliminator) live in
`Reduction/CumulSubstCompat.lean`; this audit covers the load-
bearing combinators and the headline. -/

-- PointwiseCompat predicate + combinators (Allais 𝓥ᴿ relation)
#print axioms TermSubstHet.PointwiseCompat
#print axioms TermSubstHet.PointwiseCompat.refl
#print axioms TermSubstHet.PointwiseCompat.sym
#print axioms TermSubstHet.PointwiseCompat.trans

-- Pattern 3 homogeneous lift companion
#print axioms TermSubstHet.PointwiseCompatHomo.refl
#print axioms TermSubstHet.PointwiseCompatHomo.sym
#print axioms TermSubstHet.PointwiseCompatHomo.trans
#print axioms TermSubstHet.PointwiseCompatHomo.toPointwiseCompat
#print axioms TermSubstHet.PointwiseCompatHomo.lift

-- Pattern 3 fundamental lemma (Term-induction with per-arm dispatch)
#print axioms Term.subst_compatible_pointwise_allais

-- Pattern 3 identity-simulation headline
#print axioms ConvCumul.subst_compatible_paired_allais

-- Pattern 3 FULL HEADLINE at homogeneous level
#print axioms ConvCumulHomo.subst_compatible_paired_allais

-- CUMUL-1.7 unified entry point
#print axioms ConvCumul.subst_compatible

/-! ## §3. CUMUL-2 — Per-shape cumul + cumulUpMarker.

The architectural breakthrough: 10 type-code ctors (one per Ty
shape) on both `RawTerm` (CUMUL-2.1) and `Term` (CUMUL-2.4) plus
the `RawTerm.cumulUpMarker` ctor (CUMUL-2.6 Phase A) that encodes
"this is a cumul-lifted code, distinguishable structurally from the
unlifted form".

The marker breaks Lean 4 v4.29.1's match-compiler propext leak: with
the marker present, match arms over `Term.cases` discharge cumulUp
branches via raw-ctor mismatch (cumulUpMarker vs .universeCode/
.unit/etc.) — no propositional index equation, no propext leak. -/

-- The marker (architectural keystone)
#print axioms RawTerm.cumulUpMarker
#print axioms RawStep.par.cumulUpMarkerCong

-- 10 typed Term type-code ctors (CUMUL-2.4)
#print axioms Term.arrowCode
#print axioms Term.piTyCode
#print axioms Term.sigmaTyCode
#print axioms Term.productCode
#print axioms Term.sumCode
#print axioms Term.listCode
#print axioms Term.optionCode
#print axioms Term.eitherCode
#print axioms Term.idCode
#print axioms Term.equivCode

-- 10 RawTerm type-code ctors (CUMUL-2.1)
#print axioms RawTerm.arrowCode
#print axioms RawTerm.piTyCode
#print axioms RawTerm.sigmaTyCode
#print axioms RawTerm.productCode
#print axioms RawTerm.sumCode
#print axioms RawTerm.listCode
#print axioms RawTerm.optionCode
#print axioms RawTerm.eitherCode
#print axioms RawTerm.idCode
#print axioms RawTerm.equivCode

-- 10 RawStep.par cong rules over the type-code ctors
#print axioms RawStep.par.arrowCodeCong
#print axioms RawStep.par.piTyCodeCong
#print axioms RawStep.par.sigmaTyCodeCong
#print axioms RawStep.par.productCodeCong
#print axioms RawStep.par.sumCodeCong
#print axioms RawStep.par.listCodeCong
#print axioms RawStep.par.optionCodeCong
#print axioms RawStep.par.eitherCodeCong
#print axioms RawStep.par.idCodeCong
#print axioms RawStep.par.equivCodeCong

/-! ## §4. CUMUL-3 — Step.cumulUpInner reduction.

Step rule that reduces inside `Term.cumulUp`'s typeCode payload
(single context, schematic codeRaw).  Plus the parallel-reduction
analog `Step.par.cumulUpInnerCong`.  Architectural finding (CUMUL-
3.3): typed-layer compatibility cascades through the raw layer
without new theorems — the `Step.par.toRawBridge` extension lifts
the inner step's bridge result via `RawStep.par.cumulUpMarkerCong`
and the marker arm of `RawTerm.{rename,subst}` recurses on the inner
code raw, matching the typed `Term.{rename,subst}` cumulUp arm
structurally. -/

#print axioms Step.cumulUpInner
#print axioms Step.par.cumulUpInnerCong
#print axioms Step.par.toRawBridge

/-! ## §5. CUMUL-4 — Cd / Diamond / ChurchRosser through cumul.

The Tait-Martin-Löf typed→raw confluence chain.  Phase 4 base
shipped the typed-input/raw-output confluence pipeline (commit
`b08e62e`); CUMUL-4 demonstrated that the cumulUp / cumulUpMarker
arms cascade through Phase 4 base WITHOUT per-ctor extensions —
the `toRawBridge` arms collapse via the marker's structural
distinction. -/

-- Raw-layer Tait-Martin-Löf confluence chain (load-bearing for W8)
#print axioms RawTerm.cd
#print axioms RawStep.par.cd_lemma
#print axioms RawStep.par.diamond
#print axioms RawStep.parStar.confluence

-- Typed-layer Cd / CdLemma / Diamond / ChurchRosser (Phase 4 base)
#print axioms Term.cdRaw
#print axioms Step.par.cdLemmaRaw
#print axioms Step.par.cdDominatesRaw
#print axioms Step.par.diamondRaw
#print axioms Step.par.diamondRawCd
#print axioms Step.parStar.churchRosserRaw
#print axioms StepStar.churchRosserRaw

-- Conv canonical form (typed-input/raw-output corollary)
#print axioms Conv.canonicalRaw
#print axioms Conv.canonicalForm
#print axioms Conv.canonicalForm_self
#print axioms Conv.canonicalForm_fromStepStar

/-! ## §6. CUMUL-5 — Conv ↔ ConvCumul bridges.

Forward direction (`Conv → ConvCumul`) via every Step ctor's
`Step.toConvCumul` arm + the chain lifts `StepStar.toConvCumul` and
`Conv.toConvCumul`.  Backward direction restricted to the refl-
homogeneous fragment (full backward requires Conv.trans which needs
Church-Rosser — Layer 3, available now via §5 above but the
ConvCumul.viaUp / cumulUpCong cross-context limits remain). -/

#print axioms Step.toConvCumul
#print axioms StepStar.toConvCumul
#print axioms Conv.toConvCumul

-- Refl-fragment backward bridges
#print axioms Conv.refl_toConvCumul
#print axioms ConvCumul.refl_toConv
#print axioms Conv.toConvCumul_toConv_refl
#print axioms ConvCumul.toConv_toConvCumul_refl

-- β/ι homogeneous-fragment backward lifts (17 total)
#print axioms ConvCumul.betaAppCumul_toConv
#print axioms ConvCumul.betaAppPiCumul_toConv
#print axioms ConvCumul.betaFstPairCumul_toConv
#print axioms ConvCumul.betaSndPairCumul_toConv
#print axioms ConvCumul.iotaBoolElimTrueCumul_toConv
#print axioms ConvCumul.iotaBoolElimFalseCumul_toConv
#print axioms ConvCumul.iotaNatElimZeroCumul_toConv
#print axioms ConvCumul.iotaNatElimSuccCumul_toConv
#print axioms ConvCumul.iotaNatRecZeroCumul_toConv
#print axioms ConvCumul.iotaNatRecSuccCumul_toConv
#print axioms ConvCumul.iotaListElimNilCumul_toConv
#print axioms ConvCumul.iotaListElimConsCumul_toConv
#print axioms ConvCumul.iotaOptionMatchNoneCumul_toConv
#print axioms ConvCumul.iotaOptionMatchSomeCumul_toConv
#print axioms ConvCumul.iotaEitherMatchInlCumul_toConv
#print axioms ConvCumul.iotaEitherMatchInrCumul_toConv
#print axioms ConvCumul.iotaIdJReflCumul_toConv

/-! ## §7. CUMUL-6 — Subject reduction at `Ty.universe`.

Step / StepStar preserve closedness of `Ty.universe` (the type that
hosts cumulativity).  One-line corollaries of the generic
`IsClosedTy`-preservation theorems instantiated at the closed-leaf
universe witness. -/

#print axioms Step.preserves_ty_universe
#print axioms StepStar.preserves_ty_universe

-- Underlying generic IsClosedTy-preservation theorems
#print axioms Step.preserves_isClosedTy
#print axioms StepStar.preserves_isClosedTy

/-! ## §8. CUMUL-7 — Modal cumul (DEFERRED).

Modal cumulativity is gated on the D4 Modal Layer (♭ ⊣ ◇ ⊣ □ ⊣ ♯
adjoint chain).  Not part of the v1.0 milestone — will be its own
sub-sprint when D4 lands.  No theorems audited in this section. -/

/-! ## §9. CUMUL-8 — Observational HoTT integration.

The headline: Univalence + funext (homogeneous and heterogeneous)
SHIP AS ZERO-AXIOM THEOREMS in lean-fx-2.

* `Step.eqType` reduces `Term.equivReflIdAtId → Term.equivReflId`
  (the rfl-fragment of Univalence, made definitional in the kernel
  reduction relation).
* `Step.eqArrow` reduces `Term.funextReflAtId → Term.funextRefl`
  (the rfl-fragment of funext, made definitional).
* `Step.eqTypeHet` extends `Step.eqType` to ANY two type endpoints
  (heterogeneous Univalence).
* `Step.eqArrowHet` extends `Step.eqArrow` to ANY two function
  endpoints (heterogeneous funext).

Lifted via `Conv.fromStep` to the four headline theorems:
`Univalence`, `UnivalenceHet`, `funext`, `FunextHet`.

Vanilla MLTT cannot derive even the rfl-fragment of Univalence
without an axiom; lean-fx-2 derives the FULL heterogeneous form via
the `Step.eqType*` / `Step.eqArrow*` reduction rules.  The four
headlines below — gated by `#print axioms` — establish the v1.0
HoTT-integration milestone. -/

-- Step constructors (kernel reductions)
#print axioms Step.eqType
#print axioms Step.eqArrow
#print axioms Step.eqTypeHet
#print axioms Step.eqArrowHet

-- Step.par parallel-reduction analogs
#print axioms Step.par.eqType
#print axioms Step.par.eqArrow

-- HoTT source/target Term ctors
#print axioms Term.equivReflId
#print axioms Term.equivReflIdAtId
#print axioms Term.funextRefl
#print axioms Term.funextReflAtId
#print axioms Term.equivIntroHet
#print axioms Term.uaIntroHet
#print axioms Term.funextIntroHet

-- THE FOUR HEADLINE THEOREMS — load-bearing v1.0 milestone
#print axioms Univalence
#print axioms UnivalenceHet
#print axioms funext
#print axioms FunextHet

/-! ## §10. Tier 3 Action framework foundation.

The unified Action typeclass + native Ty.act / RawTerm.act / Term.act
recursion engines.  Shipped across the MEGA-Z sprint as the
infrastructure for future ctor additions without per-engine cascade
duplication. -/

-- Action typeclass core
#print axioms Action

-- Ty.act native infrastructure (MEGA-Z2.6)
#print axioms Ty.act
#print axioms Ty.act_pointwise
#print axioms Ty.act_compose
#print axioms Ty.act_identity

-- Z2.B bridge equivalence (MEGA-Z2.B)
#print axioms Ty.act_eq_rename
#print axioms Ty.act_eq_subst
#print axioms Ty.act_eq_weaken

-- RawTerm.act (MEGA-Z4.A) + Z2.A.1 bridge
#print axioms RawTerm.act
#print axioms RawTerm.act_eq_rename
#print axioms RawTerm.act_eq_subst_forRaw

-- Term.act (MEGA-Z5.A) — typeclass + thin wrappers
#print axioms TermActCompat
#print axioms Term.actRenaming
#print axioms Term.actSubst

/-! ## §11. Subst infrastructure — load-bearing for cumul.

The unified `Term.subst` / `Term.rename` / `Term.substHet` family
underpins the entire ConvCumul.subst_compatible chain.  Per the
ARCHITECTURE.md commitment: ONE `Subst.singleton`, NO
`dropNewest`, NO `termSingleton` variant. -/

#print axioms Term.rename
#print axioms Term.subst
#print axioms Term.substHet
#print axioms Term.subst_pointwise

end LeanFX2

/-! ## v1.0 milestone declaration.

If every `#print axioms` line above reports "does not depend on any
axioms", the CUMUL chapter is RELEASE-QUALITY:

* CUMUL-1 (foundation): SHIPPED zero-axiom
* CUMUL-1.7 (Pattern 3 paired-env): SHIPPED zero-axiom
* CUMUL-2 (per-shape + cumulUpMarker): SHIPPED zero-axiom
* CUMUL-3 (Step.cumulUpInner): SHIPPED zero-axiom
* CUMUL-4 (Cd / Diamond / ChurchRosser): SHIPPED zero-axiom
* CUMUL-5 (Conv ↔ ConvCumul bridges): SHIPPED zero-axiom (forward
  + refl-homogeneous backward)
* CUMUL-6 (SR at universe): SHIPPED zero-axiom
* CUMUL-7 (modal cumul): DEFERRED (gated on D4 Modal Layer)
* CUMUL-8 (HoTT integration): SHIPPED zero-axiom (4 headlines)

The MLTT + observational HoTT cumulativity story is closed.

Future work (not blocking v1.0):
* CUMUL-7 modal cumul (post-D4)
* Full ConvCumul → Conv backward direction (cross-context fragment)
* Iso-cumul / definitional univalence (Cubical Layer)
-/

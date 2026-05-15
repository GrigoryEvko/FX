import LeanFX2.Foundation.RawSubst
import LeanFX2.Foundation.RawPartialRename
import LeanFX2.Foundation.RawPartialRename.TranspPiContractum
import LeanFX2.Foundation.RawPartialRename.TranspPiPathRecognizer

/-! # LeanFX2.Confluence.RawCd.CubicalAndEquiv

Per-redex helpers for cubical transport and equivalence redexes:
`cdTranspCase` (cubical transport at a syntactically constant type path),
`cdIdToEquivCase` (D3.6-S4 `idToEquiv (refl _) → equivIntro id ...`),
`cdUaToEquivApplyCase` (D3.6-S6 `uaToEquiv (oeqRefl _)` inner dispatch),
`cdEquivApplyCase` (D3.6-S6 outer `equivApply` dispatch — calls
`cdUaToEquivApplyCase` on the `uaToEquiv` arm).

Every inner `match` enumerates all 55 `RawTerm` constructors
explicitly to satisfy AXIOMS.md Layer M strict-zero-axiom policy.

## Root status

Layer 2 confluence helper.  Consumed by `Confluence.RawCd` shim and
downstream `Confluence.RawCdLemma`. -/

namespace LeanFX2

/-- Cubical transport at a syntactically constant type path:
`transp (pathLam typeRaw.weaken) source ⟶ source` (the cubical
analog of `transp refl x ⟶ x`).  When the developed path is
`pathLam pathBody` and `RawTerm.unweaken? pathBody` succeeds (i.e.
`pathBody` is a weakened type code with no interval-binder
dependence), fire the β reduction.  Otherwise rebuild as a
`transp` cong.

The 67-arm outer match keeps the match compiler propext-clean per
`feedback_lean_zero_axiom_match.md`; the inner `Option (RawTerm
scope)` match enumerates `some _` / `none` explicitly. -/
def RawTerm.cdTranspCase {scope : Nat}
    (developedPath developedSource : RawTerm scope) : RawTerm scope :=
  match developedPath with
  | RawTerm.pathLam pathBody =>
    match RawTerm.unweaken? pathBody with
    | some _ => developedSource
    | none =>
        RawTerm.transp (RawTerm.pathLam pathBody) developedSource
  | RawTerm.var _ => RawTerm.transp developedPath developedSource
  | RawTerm.unit => RawTerm.transp developedPath developedSource
  | RawTerm.lam _ => RawTerm.transp developedPath developedSource
  | RawTerm.app _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.pair _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.fst _ => RawTerm.transp developedPath developedSource
  | RawTerm.snd _ => RawTerm.transp developedPath developedSource
  | RawTerm.boolTrue => RawTerm.transp developedPath developedSource
  | RawTerm.boolFalse => RawTerm.transp developedPath developedSource
  | RawTerm.boolElim _ _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.natZero => RawTerm.transp developedPath developedSource
  | RawTerm.natSucc _ => RawTerm.transp developedPath developedSource
  | RawTerm.natElim _ _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.natRec _ _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.listNil => RawTerm.transp developedPath developedSource
  | RawTerm.listCons _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.listElim _ _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.optionNone => RawTerm.transp developedPath developedSource
  | RawTerm.optionSome _ => RawTerm.transp developedPath developedSource
  | RawTerm.optionMatch _ _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.eitherInl _ => RawTerm.transp developedPath developedSource
  | RawTerm.eitherInr _ => RawTerm.transp developedPath developedSource
  | RawTerm.eitherMatch _ _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.refl _ => RawTerm.transp developedPath developedSource
  | RawTerm.idJ _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.modIntro _ => RawTerm.transp developedPath developedSource
  | RawTerm.modElim _ => RawTerm.transp developedPath developedSource
  | RawTerm.subsume _ => RawTerm.transp developedPath developedSource
  | RawTerm.interval0 => RawTerm.transp developedPath developedSource
  | RawTerm.interval1 => RawTerm.transp developedPath developedSource
  | RawTerm.intervalOpp _ => RawTerm.transp developedPath developedSource
  | RawTerm.intervalMeet _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.intervalJoin _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.pathApp _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.glueIntro _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.glueElim _ => RawTerm.transp developedPath developedSource
  | RawTerm.transp _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.hcomp _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.oeqRefl _ => RawTerm.transp developedPath developedSource
  | RawTerm.oeqJ _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.oeqFunext _ => RawTerm.transp developedPath developedSource
  | RawTerm.idStrictRefl _ => RawTerm.transp developedPath developedSource
  | RawTerm.idStrictRec _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.equivIntro _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.equivApp _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.refineIntro _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.refineElim _ => RawTerm.transp developedPath developedSource
  | RawTerm.recordIntro _ => RawTerm.transp developedPath developedSource
  | RawTerm.recordProj _ => RawTerm.transp developedPath developedSource
  | RawTerm.codataUnfold _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.codataDest _ => RawTerm.transp developedPath developedSource
  | RawTerm.sessionSend _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.sessionRecv _ => RawTerm.transp developedPath developedSource
  | RawTerm.effectPerform _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.universeCode _ => RawTerm.transp developedPath developedSource
  | RawTerm.arrowCode _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.piTyCode _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.sigmaTyCode _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.productCode _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.sumCode _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.listCode _ => RawTerm.transp developedPath developedSource
  | RawTerm.optionCode _ => RawTerm.transp developedPath developedSource
  | RawTerm.eitherCode _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.idCode _ _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.equivCode _ _ => RawTerm.transp developedPath developedSource
  | RawTerm.cumulUpMarker _ => RawTerm.transp developedPath developedSource
  -- D3.6-S1: univalence-β fires when developed path is `uaToEquiv proof`.
  -- Reduce to `equivApply (uaToEquiv proof) developedSource` (the ua β
  -- contractum).
  | RawTerm.uaToEquiv proof =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedSource
  | RawTerm.equivApply _ _ => RawTerm.transp developedPath developedSource
  -- D3.6-S3: compose-β fires when developed path is
  -- `pathCompose left right`.  Reduce to
  -- `transp right (transp left developedSource)` — the compose-β
  -- contractum.  This is the cubical analog of the meta-level rule
  -- `Path.transport_compose` shipped in `HoTT/TranspCompose.lean`.
  | RawTerm.pathCompose left right =>
    RawTerm.transp right (RawTerm.transp left developedSource)
  -- D3.6-S4: idToEquiv as a path argument to transp does not fire a
  -- transp β rule (idToEquiv is not a path; the β rule for idToEquiv
  -- fires through `cdIdToEquivCase` not here).  Default rebuild.
  | RawTerm.idToEquiv _ => RawTerm.transp developedPath developedSource
  -- D3.6-S5: oeqTrans as a path argument to transp does not fire a
  -- transp β rule (oeqTrans is not a path; the β rule for oeqTrans
  -- fires through `cdIdToEquivCase`'s oeqTrans arm, not here).
  -- Default rebuild.
  | RawTerm.oeqTrans _ _ => RawTerm.transp developedPath developedSource
  -- D3.6-S5: equivCompose as a path argument to transp does not fire a
  -- transp β rule.  Default rebuild.
  | RawTerm.equivCompose _ _ => RawTerm.transp developedPath developedSource

/-- D2.5.5 transpPi β-rule dispatch helper.  Called from the `none`
branch of `cdTranspCase`'s `unweaken? pathBody` dispatch — i.e. after
the constant-path / `transpReflBeta` rule failed to fire.  Decides
whether the developed path-body has the CCHM transpPi shape:

  `pathBody = piTyCode (innerDomain.weaken) codomainCode`

(with `innerDomain` not using the interval-binder slot), and if so
fires the transpPi β reduction returning
`transpPiBetaContractum codomainCode developedSource`; otherwise
rebuilds the original transp cong.

The disjoint-premise design (#1951) is enforced at the caller side
by checking `unweaken? pathBody` first — when `cdTranspPiCase` is
invoked, `unweaken? pathBody` is already known to be `none`, so the
`matchTranspPiBetaShape?`-success path here cannot collide with
`transpReflBeta`.  Even so the helper itself is total: it dispatches
on the recognizer alone, leaving the caller to enforce ordering.

Consumed by future atomic Phase F+G+I cascade landing
(`cdTranspCase` extension + `RawStep.par.transpPiBeta` ctor +
`cd_lemma` transpPi arm).  Shipped standalone in Phase F so the
foundation primitive set is verified before the cascade integrates. -/
def RawTerm.cdTranspPiCase {scope : Nat}
    (pathBody : RawTerm (scope + 1))
    (developedSource : RawTerm scope) : RawTerm scope :=
  match RawTerm.matchTranspPiBetaShape? pathBody with
  | some (_, codomainCode) =>
      RawTerm.transpPiBetaContractum codomainCode developedSource
  | none =>
      RawTerm.transp (RawTerm.pathLam pathBody) developedSource

/-- D2.5.2 cubical hcomp at a syntactically constant sides-path:
`hcomp (pathLam X.weaken) cap ⟶ cap` (the cubical analog of
"trivial-box hcomp returns the cap" — the constant-path sides
provide trivial filler so the box reduces to its cap).

When the developed sides is `pathLam sidesBody` and
`RawTerm.unweaken? sidesBody` succeeds (i.e. `sidesBody` is a
weakened term with no interval-binder dependence), fire the β
reduction returning `developedCap`.  Otherwise rebuild as a plain
`hcomp` cong.

The β rule is independent of `developedCap`'s value — any
constant-path sides triggers the reduction.  This matches
`RawStep.par.hcompBeta` whose `pathBodyRawSource` and
`capRawSource` are independent witnesses (the raw confluence rule
does not enforce the cubical boundary condition that the path body
equals the cap; that is a typing concern, deferred to Phase B).

Structurally mirrors `cdTranspCase`: 67-arm outer match keeps the
match compiler propext-clean per `feedback_lean_zero_axiom_match.md`;
the inner `Option (RawTerm scope)` match enumerates `some _` / `none`
explicitly. -/
def RawTerm.cdHcompCase {scope : Nat}
    (developedSides developedCap : RawTerm scope) : RawTerm scope :=
  match developedSides with
  | RawTerm.pathLam sidesBody =>
    match RawTerm.unweaken? sidesBody with
    | some _ => developedCap
    | none =>
        RawTerm.hcomp (RawTerm.pathLam sidesBody) developedCap
  | RawTerm.var _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.unit => RawTerm.hcomp developedSides developedCap
  | RawTerm.lam _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.app _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.pair _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.fst _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.snd _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.boolTrue => RawTerm.hcomp developedSides developedCap
  | RawTerm.boolFalse => RawTerm.hcomp developedSides developedCap
  | RawTerm.boolElim _ _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.natZero => RawTerm.hcomp developedSides developedCap
  | RawTerm.natSucc _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.natElim _ _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.natRec _ _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.listNil => RawTerm.hcomp developedSides developedCap
  | RawTerm.listCons _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.listElim _ _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.optionNone => RawTerm.hcomp developedSides developedCap
  | RawTerm.optionSome _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.optionMatch _ _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.eitherInl _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.eitherInr _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.eitherMatch _ _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.refl _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.idJ _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.modIntro _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.modElim _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.subsume _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.interval0 => RawTerm.hcomp developedSides developedCap
  | RawTerm.interval1 => RawTerm.hcomp developedSides developedCap
  | RawTerm.intervalOpp _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.intervalMeet _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.intervalJoin _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.pathApp _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.glueIntro _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.glueElim _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.transp _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.hcomp _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.oeqRefl _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.oeqJ _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.oeqFunext _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.idStrictRefl _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.idStrictRec _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.equivIntro _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.equivApp _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.refineIntro _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.refineElim _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.recordIntro _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.recordProj _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.codataUnfold _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.codataDest _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.sessionSend _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.sessionRecv _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.effectPerform _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.universeCode _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.arrowCode _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.piTyCode _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.sigmaTyCode _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.productCode _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.sumCode _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.listCode _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.optionCode _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.eitherCode _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.idCode _ _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.equivCode _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.cumulUpMarker _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.uaToEquiv _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.equivApply _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.pathCompose _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.idToEquiv _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.oeqTrans _ _ => RawTerm.hcomp developedSides developedCap
  | RawTerm.equivCompose _ _ => RawTerm.hcomp developedSides developedCap

/-- D3.6-S4 idToEquiv-refl redex: `idToEquiv (refl _) → equivIntro id
id`; otherwise rebuild `idToEquiv developedProof`.

The β rule fires when the developed proof is a syntactic `refl _`.
The contractum is the kernel encoding of the identity equivalence:
forward and backward functions are both `lam (var 0)` (the identity
on the bound variable). -/
def RawTerm.cdIdToEquivCase {scope : Nat}
    (developedProof : RawTerm scope) : RawTerm scope :=
  match developedProof with
  -- HEADLINE: idToEquiv (refl _) ⟶ equivIntro (lam id) (lam id)
  | RawTerm.refl _ =>
      RawTerm.equivIntro
        (RawTerm.lam (RawTerm.var (Fin.mk 0 (Nat.zero_lt_succ _))))
        (RawTerm.lam (RawTerm.var (Fin.mk 0 (Nat.zero_lt_succ _))))
  | RawTerm.var _ => RawTerm.idToEquiv developedProof
  | RawTerm.unit => RawTerm.idToEquiv developedProof
  | RawTerm.lam _ => RawTerm.idToEquiv developedProof
  | RawTerm.app _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.pair _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.fst _ => RawTerm.idToEquiv developedProof
  | RawTerm.snd _ => RawTerm.idToEquiv developedProof
  | RawTerm.boolTrue => RawTerm.idToEquiv developedProof
  | RawTerm.boolFalse => RawTerm.idToEquiv developedProof
  | RawTerm.boolElim _ _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.natZero => RawTerm.idToEquiv developedProof
  | RawTerm.natSucc _ => RawTerm.idToEquiv developedProof
  | RawTerm.natElim _ _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.natRec _ _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.listNil => RawTerm.idToEquiv developedProof
  | RawTerm.listCons _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.listElim _ _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.optionNone => RawTerm.idToEquiv developedProof
  | RawTerm.optionSome _ => RawTerm.idToEquiv developedProof
  | RawTerm.optionMatch _ _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.eitherInl _ => RawTerm.idToEquiv developedProof
  | RawTerm.eitherInr _ => RawTerm.idToEquiv developedProof
  | RawTerm.eitherMatch _ _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.idJ _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.modIntro _ => RawTerm.idToEquiv developedProof
  | RawTerm.modElim _ => RawTerm.idToEquiv developedProof
  | RawTerm.subsume _ => RawTerm.idToEquiv developedProof
  | RawTerm.interval0 => RawTerm.idToEquiv developedProof
  | RawTerm.interval1 => RawTerm.idToEquiv developedProof
  | RawTerm.intervalOpp _ => RawTerm.idToEquiv developedProof
  | RawTerm.intervalMeet _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.intervalJoin _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.pathLam _ => RawTerm.idToEquiv developedProof
  | RawTerm.pathApp _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.glueIntro _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.glueElim _ => RawTerm.idToEquiv developedProof
  | RawTerm.transp _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.hcomp _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.oeqRefl _ => RawTerm.idToEquiv developedProof
  | RawTerm.oeqJ _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.oeqFunext _ => RawTerm.idToEquiv developedProof
  | RawTerm.idStrictRefl _ => RawTerm.idToEquiv developedProof
  | RawTerm.idStrictRec _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.equivIntro _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.equivApp _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.refineIntro _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.refineElim _ => RawTerm.idToEquiv developedProof
  | RawTerm.recordIntro _ => RawTerm.idToEquiv developedProof
  | RawTerm.recordProj _ => RawTerm.idToEquiv developedProof
  | RawTerm.codataUnfold _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.codataDest _ => RawTerm.idToEquiv developedProof
  | RawTerm.sessionSend _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.sessionRecv _ => RawTerm.idToEquiv developedProof
  | RawTerm.effectPerform _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.universeCode _ => RawTerm.idToEquiv developedProof
  | RawTerm.arrowCode _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.piTyCode _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.sigmaTyCode _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.productCode _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.sumCode _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.listCode _ => RawTerm.idToEquiv developedProof
  | RawTerm.optionCode _ => RawTerm.idToEquiv developedProof
  | RawTerm.eitherCode _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.idCode _ _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.equivCode _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.cumulUpMarker _ => RawTerm.idToEquiv developedProof
  | RawTerm.uaToEquiv _ => RawTerm.idToEquiv developedProof
  | RawTerm.equivApply _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.pathCompose _ _ => RawTerm.idToEquiv developedProof
  | RawTerm.idToEquiv _ => RawTerm.idToEquiv developedProof
  -- HEADLINE D3.6-S5: idToEquiv (oeqTrans first second) ⟶
  -- equivCompose (idToEquiv first) (idToEquiv second).  This is the
  -- compose-β contractum target.
  | RawTerm.oeqTrans firstProof secondProof =>
      RawTerm.equivCompose
        (RawTerm.idToEquiv firstProof)
        (RawTerm.idToEquiv secondProof)
  | RawTerm.equivCompose _ _ => RawTerm.idToEquiv developedProof

/-- D3.6-S6 uaToEquiv-of-witness redex (inner dispatch under
`cdEquivApplyCase`'s `uaToEquiv` arm): `uaToEquiv (oeqRefl _)` is the
identity-equivalence-via-univalence; applying it to a value yields
the value unchanged.  When the inner `proof` is syntactically
`oeqRefl witness`, the contractum is `developedArg` directly.
Otherwise rebuild `equivApply (uaToEquiv proof) developedArg`.
67-arm full enumeration keeps the match propext-clean. -/
def RawTerm.cdUaToEquivApplyCase {scope : Nat}
    (proof developedArg : RawTerm scope) : RawTerm scope :=
  match proof with
  -- HEADLINE: equivApply (uaToEquiv (oeqRefl _)) developedArg ⟶ developedArg
  | RawTerm.oeqRefl _ => developedArg
  | RawTerm.var _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.unit =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.lam _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.app _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.pair _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.fst _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.snd _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.boolTrue =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.boolFalse =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.boolElim _ _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.natZero =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.natSucc _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.natElim _ _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.natRec _ _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.listNil =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.listCons _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.listElim _ _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.optionNone =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.optionSome _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.optionMatch _ _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.eitherInl _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.eitherInr _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.eitherMatch _ _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.refl _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.idJ _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.modIntro _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.modElim _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.subsume _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.interval0 =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.interval1 =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.intervalOpp _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.intervalMeet _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.intervalJoin _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.pathLam _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.pathApp _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.glueIntro _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.glueElim _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.transp _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.hcomp _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.oeqJ _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.oeqFunext _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.idStrictRefl _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.idStrictRec _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.equivIntro _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.equivApp _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.refineIntro _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.refineElim _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.recordIntro _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.recordProj _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.codataUnfold _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.codataDest _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.sessionSend _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.sessionRecv _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.effectPerform _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.universeCode _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.arrowCode _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.piTyCode _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.sigmaTyCode _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.productCode _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.sumCode _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.listCode _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.optionCode _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.eitherCode _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.idCode _ _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.equivCode _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.cumulUpMarker _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.uaToEquiv _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.equivApply _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.pathCompose _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.idToEquiv _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.oeqTrans _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg
  | RawTerm.equivCompose _ _ =>
    RawTerm.equivApply (RawTerm.uaToEquiv proof) developedArg

/-- D3.6-S6 outer dispatch: `equivApply` reduces directly when the
developed equiv is `uaToEquiv (oeqRefl _)` (the
identity-equivalence-via-univalence shape).  Dispatches through
`cdUaToEquivApplyCase` for the `uaToEquiv` arm; all other 66 ctors
rebuild as plain cong `equivApply developedEquiv developedArg`.
67-arm full enumeration keeps the match propext-clean. -/
def RawTerm.cdEquivApplyCase {scope : Nat}
    (developedEquiv developedArg : RawTerm scope) : RawTerm scope :=
  match developedEquiv with
  -- HEADLINE: dispatch the round-trip-β rule when developed equiv has
  -- shape uaToEquiv (oeqRefl _).
  | RawTerm.uaToEquiv proof =>
    RawTerm.cdUaToEquivApplyCase proof developedArg
  | RawTerm.var _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.unit => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.lam _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.app _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.pair _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.fst _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.snd _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.boolTrue => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.boolFalse => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.boolElim _ _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.natZero => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.natSucc _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.natElim _ _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.natRec _ _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.listNil => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.listCons _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.listElim _ _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.optionNone => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.optionSome _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.optionMatch _ _ _ =>
    RawTerm.equivApply developedEquiv developedArg
  | RawTerm.eitherInl _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.eitherInr _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.eitherMatch _ _ _ =>
    RawTerm.equivApply developedEquiv developedArg
  | RawTerm.refl _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.idJ _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.modIntro _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.modElim _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.subsume _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.interval0 => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.interval1 => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.intervalOpp _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.intervalMeet _ _ =>
    RawTerm.equivApply developedEquiv developedArg
  | RawTerm.intervalJoin _ _ =>
    RawTerm.equivApply developedEquiv developedArg
  | RawTerm.pathLam _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.pathApp _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.glueIntro _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.glueElim _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.transp _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.hcomp _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.oeqRefl _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.oeqJ _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.oeqFunext _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.idStrictRefl _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.idStrictRec _ _ =>
    RawTerm.equivApply developedEquiv developedArg
  | RawTerm.equivIntro _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.equivApp _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.refineIntro _ _ =>
    RawTerm.equivApply developedEquiv developedArg
  | RawTerm.refineElim _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.recordIntro _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.recordProj _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.codataUnfold _ _ =>
    RawTerm.equivApply developedEquiv developedArg
  | RawTerm.codataDest _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.sessionSend _ _ =>
    RawTerm.equivApply developedEquiv developedArg
  | RawTerm.sessionRecv _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.effectPerform _ _ =>
    RawTerm.equivApply developedEquiv developedArg
  | RawTerm.universeCode _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.arrowCode _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.piTyCode _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.sigmaTyCode _ _ =>
    RawTerm.equivApply developedEquiv developedArg
  | RawTerm.productCode _ _ =>
    RawTerm.equivApply developedEquiv developedArg
  | RawTerm.sumCode _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.listCode _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.optionCode _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.eitherCode _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.idCode _ _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.equivCode _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.cumulUpMarker _ =>
    RawTerm.equivApply developedEquiv developedArg
  | RawTerm.equivApply _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.pathCompose _ _ =>
    RawTerm.equivApply developedEquiv developedArg
  | RawTerm.idToEquiv _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.oeqTrans _ _ => RawTerm.equivApply developedEquiv developedArg
  | RawTerm.equivCompose _ _ =>
    RawTerm.equivApply developedEquiv developedArg

end LeanFX2

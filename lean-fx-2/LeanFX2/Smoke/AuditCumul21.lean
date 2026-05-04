import LeanFX2.Foundation.RawTerm
import LeanFX2.Foundation.RawSubst
import LeanFX2.Foundation.RenameIdentity
import LeanFX2.Foundation.SubstActsOnTy
import LeanFX2.Reduction.RawPar
import LeanFX2.Reduction.RawParCompatible
import LeanFX2.Reduction.RawParRename
import LeanFX2.Confluence.RawCd
import LeanFX2.Confluence.RawCdLemma
import LeanFX2.Confluence.RawCdDominates
import LeanFX2.Algo.RawWHNF
import LeanFX2.Algo.RawWHNFCorrect

/-! # Smoke/AuditCumul21 — CUMUL-2.1 zero-axiom audit gate.

Phase CUMUL-2.1 (the first phase of the CUMUL-2 chain) extends
`RawTerm` with ten new per-shape type-code constructors:

* Atom-shape (no binder): `arrowCode`, `productCode`, `sumCode`,
  `listCode`, `optionCode`, `eitherCode`, `idCode`, `equivCode`.
* Binder-shape (codomain at `scope + 1`): `piTyCode`, `sigmaTyCode`.

These ctors model: each type former in lean-fx-2's `Ty` (arrow,
piTy, sigmaTy, product, sum, list, option, either, id, equiv)
has a corresponding type CODE at the RawTerm level.  The code
represents "I am a value whose Ty is `Ty.universe N`, and I
encode the type former `<X>`".

CUMUL-2.1 unblocks per-shape cumulativity: lifting `Term ctxLow
(Ty.universe lower _) raw` for ANY type-code raw, not just
`RawTerm.universeCode N`.

## Cascade scope

Path B (cascade folded into this gladiator) ships:
* RawTerm.lean: 10 new ctors + 10 arms in `RawTerm.act`
* RawSubst.lean: 10 arms each in `rename`, `subst`, `act` and
  60 arms across the 7 pointwise / compose / identity / cross-
  direction commute lemmas
* RenameIdentity.lean: 10 arms in `RawTerm.rename_identity`
* SubstActsOnTy.lean: 20 arms across `act_eq_rename` and
  `act_eq_subst_forRaw`
* RawPar.lean: 10 new `*CodeCong` constructors on `RawStep.par`
* RawParRename.lean: 10 arms in `RawStep.par.rename`
* RawParCompatible.lean: 20 arms across `subst_par_pointwise`
  and `subst_par`
* RawCd.lean: 10 arms in each of 11 case helpers + 10 arms in
  `RawTerm.cd`
* RawCdLemma.lean: 10 arms in `cd_lemma`
* RawCdDominates.lean: 10 arms in `cd_dominates`
* RawWHNF.lean: 10 enum entries in `RawTerm.HeadCtor` + 10 arms
  in `headCtor` projection + 80 arms across the 7 `?`-projection
  helpers and `isRefl` + 10 arms in WHNF body
* RawWHNFCorrect.lean: 70 nomatch arms across 7 inversion lemmas
  + 10 refl arms in headline theorem + ext to compound `|`
  patterns
* Algo/Infer.lean and Algo/Check.lean: 10 `none` arms each (no
  typed `Term` counterparts yet — CUMUL-2.4 ships those)

## Zero-axiom gate

Every shipped declaration MUST report
`'Foo' does not depend on any axioms` per
`feedback_lean_zero_axiom_match.md` and `CLAUDE.md`'s zero-axiom
commitment. -/

namespace LeanFX2

/-! ## Smoke: every new ctor elaborates as RawTerm scope. -/

private def cumul21_arrowCode_smoke : RawTerm 0 :=
  RawTerm.arrowCode (RawTerm.universeCode 0) (RawTerm.universeCode 0)

private def cumul21_piTyCode_smoke : RawTerm 0 :=
  RawTerm.piTyCode (RawTerm.universeCode 0) (RawTerm.universeCode 1)

private def cumul21_sigmaTyCode_smoke : RawTerm 0 :=
  RawTerm.sigmaTyCode (RawTerm.universeCode 0) (RawTerm.universeCode 1)

private def cumul21_productCode_smoke : RawTerm 0 :=
  RawTerm.productCode (RawTerm.universeCode 0) (RawTerm.universeCode 0)

private def cumul21_sumCode_smoke : RawTerm 0 :=
  RawTerm.sumCode (RawTerm.universeCode 0) (RawTerm.universeCode 0)

private def cumul21_listCode_smoke : RawTerm 0 :=
  RawTerm.listCode (RawTerm.universeCode 0)

private def cumul21_optionCode_smoke : RawTerm 0 :=
  RawTerm.optionCode (RawTerm.universeCode 0)

private def cumul21_eitherCode_smoke : RawTerm 0 :=
  RawTerm.eitherCode (RawTerm.universeCode 0) (RawTerm.universeCode 0)

private def cumul21_idCode_smoke : RawTerm 0 :=
  RawTerm.idCode (RawTerm.universeCode 0)
                 (RawTerm.universeCode 0)
                 (RawTerm.universeCode 0)

private def cumul21_equivCode_smoke : RawTerm 0 :=
  RawTerm.equivCode (RawTerm.universeCode 0) (RawTerm.universeCode 0)

/-! ## rfl-bodied smokes for the cascade. -/

/-- arrowCode renames pointwise on subterms. -/
private theorem cumul21_arrowCode_rename_smoke {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (domainCode codomainCode : RawTerm sourceScope) :
    (RawTerm.arrowCode domainCode codomainCode).rename rho =
      RawTerm.arrowCode (domainCode.rename rho) (codomainCode.rename rho) := rfl

/-- piTyCode renames with `lift` on codomain. -/
private theorem cumul21_piTyCode_rename_smoke {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (domainCode : RawTerm sourceScope)
    (codomainCode : RawTerm (sourceScope + 1)) :
    (RawTerm.piTyCode domainCode codomainCode).rename rho =
      RawTerm.piTyCode (domainCode.rename rho) (codomainCode.rename rho.lift) := rfl

/-- sigmaTyCode renames with `lift` on codomain. -/
private theorem cumul21_sigmaTyCode_rename_smoke {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (domainCode : RawTerm sourceScope)
    (codomainCode : RawTerm (sourceScope + 1)) :
    (RawTerm.sigmaTyCode domainCode codomainCode).rename rho =
      RawTerm.sigmaTyCode (domainCode.rename rho) (codomainCode.rename rho.lift) := rfl

/-- arrowCode substitutes pointwise on subterms. -/
private theorem cumul21_arrowCode_subst_smoke {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope)
    (domainCode codomainCode : RawTerm sourceScope) :
    (RawTerm.arrowCode domainCode codomainCode).subst sigma =
      RawTerm.arrowCode (domainCode.subst sigma) (codomainCode.subst sigma) := rfl

/-- piTyCode substitutes with `lift` on codomain. -/
private theorem cumul21_piTyCode_subst_smoke {sourceScope targetScope : Nat}
    (sigma : RawTermSubst sourceScope targetScope)
    (domainCode : RawTerm sourceScope)
    (codomainCode : RawTerm (sourceScope + 1)) :
    (RawTerm.piTyCode domainCode codomainCode).subst sigma =
      RawTerm.piTyCode (domainCode.subst sigma) (codomainCode.subst sigma.lift) := rfl

/-- listCode renames recursively. -/
private theorem cumul21_listCode_rename_smoke {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (elementCode : RawTerm sourceScope) :
    (RawTerm.listCode elementCode).rename rho =
      RawTerm.listCode (elementCode.rename rho) := rfl

/-- idCode renames pointwise on all three subterms. -/
private theorem cumul21_idCode_rename_smoke {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (typeCode leftRaw rightRaw : RawTerm sourceScope) :
    (RawTerm.idCode typeCode leftRaw rightRaw).rename rho =
      RawTerm.idCode (typeCode.rename rho)
                     (leftRaw.rename rho)
                     (rightRaw.rename rho) := rfl

/-! ## RawTerm.act smokes. -/

/-- `arrowCode.act` matches `arrowCode.rename` shape over a renaming. -/
private theorem cumul21_arrowCode_act_smoke {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (domainCode codomainCode : RawTerm sourceScope) :
    (RawTerm.arrowCode domainCode codomainCode).act rho =
      RawTerm.arrowCode (domainCode.act rho) (codomainCode.act rho) := rfl

/-- `piTyCode.act` threads `Action.liftForRaw` on codomain. -/
private theorem cumul21_piTyCode_act_smoke {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (domainCode : RawTerm sourceScope)
    (codomainCode : RawTerm (sourceScope + 1)) :
    (RawTerm.piTyCode domainCode codomainCode).act rho =
      RawTerm.piTyCode (domainCode.act rho)
                       (codomainCode.act (Action.liftForRaw rho)) := rfl

/-! ## RawStep.par cong smokes. -/

private theorem cumul21_arrowCodeCong_smoke {scope : Nat}
    (domainCode codomainCode : RawTerm scope) :
    RawStep.par (RawTerm.arrowCode domainCode codomainCode)
                (RawTerm.arrowCode domainCode codomainCode) :=
  RawStep.par.arrowCodeCong (RawStep.par.refl _) (RawStep.par.refl _)

private theorem cumul21_piTyCodeCong_smoke {scope : Nat}
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    RawStep.par (RawTerm.piTyCode domainCode codomainCode)
                (RawTerm.piTyCode domainCode codomainCode) :=
  RawStep.par.piTyCodeCong (RawStep.par.refl _) (RawStep.par.refl _)

private theorem cumul21_idCodeCong_smoke {scope : Nat}
    (typeCode leftRaw rightRaw : RawTerm scope) :
    RawStep.par (RawTerm.idCode typeCode leftRaw rightRaw)
                (RawTerm.idCode typeCode leftRaw rightRaw) :=
  RawStep.par.idCodeCong (RawStep.par.refl _) (RawStep.par.refl _) (RawStep.par.refl _)

end LeanFX2

/-! ## Zero-axiom audit gate

Every CUMUL-2.1 declaration MUST be axiom-free.  This includes:
* The 10 new `RawTerm` ctors (proved via the smoke values above).
* The 10 new `RawStep.par.*CodeCong` rules.
* The cascade arms in `RawTerm.act`, `RawTerm.rename`,
  `RawTerm.subst`, `RawTerm.cd`, the 7 `*_pointwise` /
  `*_compose` / `*_identity` / cross-direction commute lemmas,
  `RawStep.par.rename`, `RawStep.par.subst_par`,
  `RawStep.par.cd_lemma`, `RawStep.par.cd_dominates`,
  `RawTerm.headCtor` and the 7 `?`-projection helpers,
  `RawTerm.whnf`, the 7 inversion lemmas in RawWHNFCorrect,
  `RawTerm.whnf_reaches`, `Term.infer`, `Term.check`.
-/

#print axioms LeanFX2.cumul21_arrowCode_smoke
#print axioms LeanFX2.cumul21_piTyCode_smoke
#print axioms LeanFX2.cumul21_sigmaTyCode_smoke
#print axioms LeanFX2.cumul21_productCode_smoke
#print axioms LeanFX2.cumul21_sumCode_smoke
#print axioms LeanFX2.cumul21_listCode_smoke
#print axioms LeanFX2.cumul21_optionCode_smoke
#print axioms LeanFX2.cumul21_eitherCode_smoke
#print axioms LeanFX2.cumul21_idCode_smoke
#print axioms LeanFX2.cumul21_equivCode_smoke

#print axioms LeanFX2.cumul21_arrowCode_rename_smoke
#print axioms LeanFX2.cumul21_piTyCode_rename_smoke
#print axioms LeanFX2.cumul21_sigmaTyCode_rename_smoke
#print axioms LeanFX2.cumul21_arrowCode_subst_smoke
#print axioms LeanFX2.cumul21_piTyCode_subst_smoke
#print axioms LeanFX2.cumul21_listCode_rename_smoke
#print axioms LeanFX2.cumul21_idCode_rename_smoke

#print axioms LeanFX2.cumul21_arrowCode_act_smoke
#print axioms LeanFX2.cumul21_piTyCode_act_smoke

#print axioms LeanFX2.cumul21_arrowCodeCong_smoke
#print axioms LeanFX2.cumul21_piTyCodeCong_smoke
#print axioms LeanFX2.cumul21_idCodeCong_smoke

/-! ## Cascade regression — load-bearing decls in cascaded files
must remain zero-axiom. -/

#print axioms LeanFX2.RawTerm.rename
#print axioms LeanFX2.RawTerm.subst
#print axioms LeanFX2.RawTerm.act
#print axioms LeanFX2.RawTerm.subst_pointwise
#print axioms LeanFX2.RawTerm.subst_compose
#print axioms LeanFX2.RawTerm.subst_identity
#print axioms LeanFX2.RawTerm.rename_pointwise
#print axioms LeanFX2.RawTerm.rename_compose
#print axioms LeanFX2.RawTerm.rename_identity
#print axioms LeanFX2.RawTerm.rename_subst_commute
#print axioms LeanFX2.RawTerm.subst_rename_commute
#print axioms LeanFX2.RawStep.par.rename
#print axioms LeanFX2.RawStep.par.subst_par
#print axioms LeanFX2.RawTerm.subst_par_pointwise
#print axioms LeanFX2.RawStep.par.cd_dominates
#print axioms LeanFX2.RawStep.par.cd_lemma
#print axioms LeanFX2.RawTerm.cd
#print axioms LeanFX2.RawTerm.headCtor
#print axioms LeanFX2.RawTerm.whnf
#print axioms LeanFX2.RawTerm.whnf_reaches

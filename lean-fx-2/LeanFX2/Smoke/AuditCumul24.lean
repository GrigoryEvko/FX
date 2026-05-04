import LeanFX2.Term
import LeanFX2.Term.Rename
import LeanFX2.Term.Subst
import LeanFX2.Term.SubstHet
import LeanFX2.Term.Pointwise
import LeanFX2.Algo.WHNF
import LeanFX2.Algo.Eval
import LeanFX2.Algo.Soundness
import LeanFX2.Reduction.CumulSubstCompat
import LeanFX2.Smoke.AuditCumul21

/-! # Smoke/AuditCumul24 — CUMUL-2.4 zero-axiom audit gate.

Phase CUMUL-2.4 (the second big phase of the CUMUL-2 chain) ships
ten new TYPED `Term` constructors mirroring the RawTerm type-code
ctors landed in CUMUL-2.1 (commit 686d7dc).

Each typed ctor is VALUE-shaped (schematic `RawTerm scope` payloads,
no recursive typed `Term` children) — mirror of the
`Term.funextIntroHet` / `Term.equivReflIdAtId` precedent.  The
schematic-payload design keeps the cascade machinery
(`Term.rename`, `Term.subst`, `Term.substHet`, `Term.pointwise`,
`ConvCumul.subst_compatible_*_allais`) structural and refl-
discharging, avoiding the need for new `*Cong` rules in `ConvCumul`
(which would cascade through every ConvCumul induction).

A future CUMUL-2.5 may upgrade these ctors to recursive typed
subterms once the matching cong infrastructure (and ConvCumul
induction-arm extensions) lands; CUMUL-2.4 ships the schematic-
payload variant to keep cascade arms zero-axiom and the gladiator
atomic.

## Cascade scope (Path B — folded into this gladiator)

* `Term.lean`: 10 new typed ctors (after `Term.funextIntroHet`)
* `Term/Rename.lean`: 10 new arms in `Term.rename`
* `Term/Subst.lean`: 10 new arms in `Term.subst`
* `Term/SubstHet.lean`: 10 new arms in `Term.substHet` (each
  composing `Nat.le_trans levelLe sigma.cumulOk` for the lifted
  universe-level proof)
* `Term/Pointwise.lean`: 10 rfl arms in `Term.subst_pointwise`
* `Algo/WHNF.lean`: 10 enum entries in `Term.HeadCtor` + 10 arms
  in `Term.headCtor` projection + 10 arms in `Term.isWHNF` (all
  `true` — VALUE) + 110 nomatch arms across 11 inversion lemmas
* `Algo/Eval.lean`: 10 `none` arms in `Term.headStep?`
* `Algo/Soundness.lean`: 10 nomatch arms in `Term.headStep?_sound`
  + 50 dispatch arms across 5 dispatch theorems
* `Reduction/CumulSubstCompat.lean`: 10 new Allais helpers (mirror
  of `subst_compatible_funextIntroHet_allais`) + 10 dispatch arms
  in `Term.subst_compatible_pointwise_allais`

## Zero-axiom gate

Every shipped declaration MUST report
`'Foo' does not depend on any axioms` per
`feedback_lean_zero_axiom_match.md` and `CLAUDE.md`'s zero-axiom
commitment.  ALL existing audits (Pattern 3, W8, Univalence,
UnivalenceHet, funext, FunextHet, all CUMUL chain) must remain
zero-axiom. -/

namespace LeanFX2

open Term

/-! ## Per-ctor existence + Term.toRaw = rfl invariant per ctor.

The raw projection of every typed ctor MUST agree definitionally
with the matching `RawTerm.{X}Code ...` term.  This is what makes
the typed↔raw bridge `rfl`-driven for downstream subject-reduction
and ParRed work.  Each smoke is `rfl` ⇒ invariant holds.  Every
ctor's existence is implicit in its toRaw_rfl smoke (the term
inhabits the typed Term type by construction). -/

private theorem cumul24_arrowCode_toRaw_rfl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm scope) :
    (Term.arrowCode (context := context) outerLevel levelLe
                    domainCodeRaw codomainCodeRaw).toRaw =
      RawTerm.arrowCode domainCodeRaw codomainCodeRaw := rfl

private theorem cumul24_piTyCode_toRaw_rfl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    (Term.piTyCode (context := context) outerLevel levelLe
                   domainCodeRaw codomainCodeRaw).toRaw =
      RawTerm.piTyCode domainCodeRaw codomainCodeRaw := rfl

private theorem cumul24_sigmaTyCode_toRaw_rfl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm scope)
    (codomainCodeRaw : RawTerm (scope + 1)) :
    (Term.sigmaTyCode (context := context) outerLevel levelLe
                      domainCodeRaw codomainCodeRaw).toRaw =
      RawTerm.sigmaTyCode domainCodeRaw codomainCodeRaw := rfl

private theorem cumul24_productCode_toRaw_rfl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm scope) :
    (Term.productCode (context := context) outerLevel levelLe
                      firstCodeRaw secondCodeRaw).toRaw =
      RawTerm.productCode firstCodeRaw secondCodeRaw := rfl

private theorem cumul24_sumCode_toRaw_rfl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    (Term.sumCode (context := context) outerLevel levelLe
                  leftCodeRaw rightCodeRaw).toRaw =
      RawTerm.sumCode leftCodeRaw rightCodeRaw := rfl

private theorem cumul24_listCode_toRaw_rfl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    (Term.listCode (context := context) outerLevel levelLe elementCodeRaw).toRaw =
      RawTerm.listCode elementCodeRaw := rfl

private theorem cumul24_optionCode_toRaw_rfl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm scope) :
    (Term.optionCode (context := context) outerLevel levelLe elementCodeRaw).toRaw =
      RawTerm.optionCode elementCodeRaw := rfl

private theorem cumul24_eitherCode_toRaw_rfl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm scope) :
    (Term.eitherCode (context := context) outerLevel levelLe
                     leftCodeRaw rightCodeRaw).toRaw =
      RawTerm.eitherCode leftCodeRaw rightCodeRaw := rfl

private theorem cumul24_idCode_toRaw_rfl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm scope) :
    (Term.idCode (context := context) outerLevel levelLe
                 typeCodeRaw leftRaw rightRaw).toRaw =
      RawTerm.idCode typeCodeRaw leftRaw rightRaw := rfl

private theorem cumul24_equivCode_toRaw_rfl
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope) :
    (Term.equivCode (context := context) outerLevel levelLe
                    leftTypeCodeRaw rightTypeCodeRaw).toRaw =
      RawTerm.equivCode leftTypeCodeRaw rightTypeCodeRaw := rfl

#print axioms cumul24_arrowCode_toRaw_rfl
#print axioms cumul24_piTyCode_toRaw_rfl
#print axioms cumul24_sigmaTyCode_toRaw_rfl
#print axioms cumul24_productCode_toRaw_rfl
#print axioms cumul24_sumCode_toRaw_rfl
#print axioms cumul24_listCode_toRaw_rfl
#print axioms cumul24_optionCode_toRaw_rfl
#print axioms cumul24_eitherCode_toRaw_rfl
#print axioms cumul24_idCode_toRaw_rfl
#print axioms cumul24_equivCode_toRaw_rfl

/-! ## Cascade audits — every Allais helper, every cascaded operation
must remain zero-axiom. -/

#print axioms LeanFX2.ConvCumul.subst_compatible_arrowCode_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_piTyCode_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_sigmaTyCode_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_productCode_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_sumCode_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_listCode_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_optionCode_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_eitherCode_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_idCode_allais
#print axioms LeanFX2.ConvCumul.subst_compatible_equivCode_allais

#print axioms LeanFX2.Term.rename
#print axioms LeanFX2.Term.subst
#print axioms LeanFX2.Term.substHet
#print axioms LeanFX2.Term.subst_pointwise
#print axioms LeanFX2.Term.headCtor
#print axioms LeanFX2.Term.isWHNF
#print axioms LeanFX2.Term.headStep?
#print axioms LeanFX2.Term.headStep?_sound
#print axioms LeanFX2.Term.subst_compatible_pointwise_allais

/-! ## Inversion-lemma regression — load-bearing for Algo/Soundness.

Every headCtor inversion lemma extended with 10 new nomatch arms
must remain zero-axiom.  These lemmas underpin
`Term.headStep?_sound` (Phase 9.G). -/

#print axioms LeanFX2.Term.headCtor_boolTrue_raw
#print axioms LeanFX2.Term.headCtor_boolFalse_raw
#print axioms LeanFX2.Term.headCtor_natZero_raw
#print axioms LeanFX2.Term.headCtor_listNil_raw
#print axioms LeanFX2.Term.headCtor_optionNone_raw
#print axioms LeanFX2.Term.headCtor_natSucc_raw
#print axioms LeanFX2.Term.headCtor_listCons_raw
#print axioms LeanFX2.Term.headCtor_optionSome_raw
#print axioms LeanFX2.Term.headCtor_eitherInl_raw
#print axioms LeanFX2.Term.headCtor_eitherInr_raw
#print axioms LeanFX2.Term.headCtor_unit_raw

end LeanFX2

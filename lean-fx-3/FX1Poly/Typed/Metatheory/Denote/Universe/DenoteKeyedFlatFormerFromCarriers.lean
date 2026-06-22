import FX1Poly.Typed.Metatheory.Denote.Universe.DenoteKeyedFlatFormerFundamental
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationConstructors

/-! # FX1Poly/Typed/DenoteKeyedFlatFormerFromCarriers
    — flat-former SN-membership in the flat-pinned denote relation, closed to the carriers' SN (leaf-closed family)

`DenoteKeyedFlatFormerFundamental.flatFormerFundamentalAtDenote` proved a flat former is a
`FundamentalConclusionAtDenote` member of its universe MODULO the former's own strong normalization (the
honest telescope residual).  This file DISCHARGES that residual for the two-carrier flat formers
(equivCode / productCode / sumCode / eitherCode / arrowCode): each former's SN follows structurally from its
two carriers' SN (the shipped congruence-only `*_isStronglyNormalizing_of_*` lemmas — a flat code has no root
redex, so its only steps are congruence through the carriers), and the carriers' SN under every closing
substitution is exactly what their own formation fundamentals supply.

So the flat-former universe-membership is now a pure FUNCTION of its carriers' SN-under-substitution — no
former-SN premise, no route-A composite-domain piArm (#752).  This is the leaf-closed shape the FT telescope
feeds: a flat type former applied to reducible carriers is itself a member of its classifying universe.

SCOPE LEDGER (FTGEN-5.1/5.2, per-former, post the table-driven carrier-aware arm):
  * `productCodeFundamentalFromCarriers` / `eitherCodeFundamentalFromCarriers` — CARRIER-AWARE: their
    type-reducibility conjunct routes through the table-driven `ofDataFlatCarrierAware` (denoting
    `carrierAwarePairCandidate` / `carrierAwareEitherCandidate` per the combinator), so they GENUINELY validate
    both carriers as denote-reducible types — taking their all-level reducibility as a premise, not merely their
    SN.  The product AND coproduct slices of FTGEN-5.2 (the formation FT recursing into the carriers) are
    complete.
  * `equivCode / sumCode / arrowCode` — STILL CONTENT-FREE: their type-reducibility conjunct is discharged by
    the gated `ofDataFlat` (which ignores the carriers, supplied `carrierCombinator? = none` by `rfl` on the
    concrete non-carrier-aware generator), so "member of its classifying universe" here tests SN +
    flat-rootedness only.  Carrier-aware type-reducibility for these (a function/equiv carrier-aware candidate,
    the typed formation rule, and the equiv-as-sigma semantics) is the genuine completion still pending; these
    remain SN-membership leaves only.

`equivCodeFundamentalFromCarriers` is the headline instance — the equivalence-code former — with its
SN-membership closed down to its two carrier types' strong normalization.

## Zero-axiom verification

Each is `flatFormerFundamentalAtDenote` (flat pin `rfl` — `Generator.isFlatDataCode` computes `true` on the
concrete flat generator) fed the per-former congruence-SN lemma applied to the carriers' SN; the substituted
former's SN matches the per-former lemma's conclusion by raw definitional reduction of `subst` on a concrete
generator head (the proof rides defeq directly; it does NOT invoke `RawTerm.subst_mkGen_of_ne_var`).  No
`induction`, no `funext`.  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **★ The GENERIC carrier-aware formation FT — one theorem keyed on the `CarrierCombinator` table (FTGEN-13
slice).**  For ANY carrier-aware binary flat former `combinator.cell firstCarrier secondCarrier`
(`pairLike` ↦ product, `coproductLike` ↦ either, `equivLike` ↦ equiv): given both carriers are SN AND
reducible-as-types at every denote level under every closing substitution, the former is a
`FundamentalConclusionAtDenote` member of its universe.  Both obligations are read off the table — SN via the
generic `CarrierCombinator.cell_isStronglyNormalizing_of_carriers`, reducibility-as-type via the generic
`IsReducibleTypeAtAllDenoteLevels.ofDataFlatCarrierAware` (denoting `combinator.assemble` on the carrier
candidates) — bridged across the closing substitution by `CarrierCombinator.cell_subst` (subst commutes with the
cell).  The three per-former `…FundamentalFromCarriers` theorems below are now one-line instances; adding a new
carrier-aware former costs exactly a `CarrierCombinator` row, with NO new formation-FT proof. -/
theorem carrierAwareFormerFundamentalFromCarriers {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    (combinator : CarrierCombinator)
    (firstCarrier secondCarrier : RawTerm scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (firstStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution firstCarrier))
    (secondStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution secondCarrier))
    (firstReducibleAllLevels :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst substitution firstCarrier))
    (secondReducibleAllLevels :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst substitution secondCarrier)) :
    FundamentalConclusionAtDenote env level context
      (combinator.cell firstCarrier secondCarrier)
      (universeCodeCell levelExpr flag) :=
  fundamentalTypeFormerAtDenote env level context
    (combinator.cell firstCarrier secondCarrier) levelExpr flag levelAbove
    (fun substitution envReducible => by
      rw [CarrierCombinator.cell_subst]
      exact ⟨CarrierCombinator.cell_isStronglyNormalizing_of_carriers combinator
                (firstStronglyNormalizing substitution envReducible)
                (secondStronglyNormalizing substitution envReducible),
             (IsReducibleTypeAtAllDenoteLevels.ofDataFlatCarrierAware (combinator := combinator)
                 (firstReducibleAllLevels substitution envReducible)
                 (secondReducibleAllLevels substitution envReducible))
               (LevelExpr.denote levelExpr env)⟩)

/-- **★ Equivalence type code CARRIER-AWARE formation FT (FTGEN-5.4/5.5 equivalence slice).**  `equivCode(source,
target)` is a `FundamentalConclusionAtDenote` member of its universe given both carriers are SN AND
reducible-as-types at every denote level under every closing substitution.  Post FTGEN-5.5 the equiv is barred
from the content-free `ofDataFlat` (its `carrierCombinator? = some equivLike`) and routes through the
CARRIER-AWARE arm `ofDataFlatCarrierAware (combinator := .equivLike)`: the substituted equivalence's
reducibility-as-type is genuinely built from the substituted carriers' all-level reducibility, denoting
`carrierAwareEquivCandidate` — the `(f, isEquiv f)` Σ-unfold whose components are reducible functions between the
carriers (FTGEN-5.4).  The former's own SN still rides `equivCode_isStronglyNormalizing_of_source_target`; both
obligations match the closed-generator `subst`-reduct by defeq.  This is the equivalence instance where the
formation FT actually RECURSES into the carriers — the equiv-as-capability the definitional-univalence frontier
(FTGEN-5.6, `Id_U ↝ equivCode`) consumes. -/
theorem equivCodeFundamentalFromCarriers {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    (sourceCarrier targetCarrier : RawTerm scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (sourceCarrierStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution sourceCarrier))
    (targetCarrierStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution targetCarrier))
    (sourceReducibleAllLevels :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst substitution sourceCarrier))
    (targetReducibleAllLevels :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst substitution targetCarrier)) :
    FundamentalConclusionAtDenote env level context
      (.mkGen .gen_equivCode () (.childCons sourceCarrier (.childCons targetCarrier .childNil)))
      (universeCodeCell levelExpr flag) :=
  carrierAwareFormerFundamentalFromCarriers env level context .equivLike sourceCarrier targetCarrier
    levelExpr flag levelAbove
    sourceCarrierStronglyNormalizing targetCarrierStronglyNormalizing
    sourceReducibleAllLevels targetReducibleAllLevels

/-- **★ Product type code CARRIER-AWARE formation FT (FTGEN-5.1/5.2 product slice).**  `productCode(left, right)`
is a `FundamentalConclusionAtDenote` member of its universe given both components are SN AND reducible-as-types at
every denote level under every closing substitution.  Unlike the three non-carrier-aware flat formers — which
discharge their type-reducibility obligation content-free via `ofDataFlat` — the product is barred from
`ofDataFlat` (the gate `carrierCombinator? = none` is false for it) and routes through the CARRIER-AWARE arm
`ofDataFlatCarrierAware (.pairLike)`: the substituted product's reducibility-as-type is genuinely built from the
substituted carriers' all-level reducibility (denoting `carrierAwarePairCandidate`).  The former's own SN still
rides `productCode_isStronglyNormalizing_of_left_right`;
both obligations match the closed-generator `subst`-reduct by defeq.  This is the product instance where the
formation FT actually RECURSES into the carriers — the FTGEN-5.1 payoff. -/
theorem productCodeFundamentalFromCarriers {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    (leftType rightType : RawTerm scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (leftStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution leftType))
    (rightStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution rightType))
    (leftReducibleAllLevels :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst substitution leftType))
    (rightReducibleAllLevels :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst substitution rightType)) :
    FundamentalConclusionAtDenote env level context
      (.mkGen .gen_productCode () (.childCons leftType (.childCons rightType .childNil)))
      (universeCodeCell levelExpr flag) :=
  carrierAwareFormerFundamentalFromCarriers env level context .pairLike leftType rightType
    levelExpr flag levelAbove
    leftStronglyNormalizing rightStronglyNormalizing
    leftReducibleAllLevels rightReducibleAllLevels

/-- **Sum type code formation FT closed to its summands' SN.**  `sumCode(left, right)`, SN via
`sumCode_isStronglyNormalizing_of_left_right`. -/
theorem sumCodeFundamentalFromCarriers {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    (leftType rightType : RawTerm scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (leftStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution leftType))
    (rightStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution rightType)) :
    FundamentalConclusionAtDenote env level context
      (.mkGen .gen_sumCode () (.childCons leftType (.childCons rightType .childNil)))
      (universeCodeCell levelExpr flag) :=
  flatFormerFundamentalAtDenote env level context
    (.mkGen .gen_sumCode () (.childCons leftType (.childCons rightType .childNil)))
    rfl (rfl : Generator.gen_sumCode.carrierCombinator? = none) levelExpr flag levelAbove
    (fun substitution envReducible =>
      sumCode_isStronglyNormalizing_of_left_right
        (leftStronglyNormalizing substitution envReducible)
        (rightStronglyNormalizing substitution envReducible))

/-- **★ Either type code CARRIER-AWARE formation FT (FTGEN-5.2 coproduct slice).**  `eitherCode(left, right)`
is a `FundamentalConclusionAtDenote` member of its universe given both sides are SN AND reducible-as-types at
every denote level under every closing substitution.  Like the product former, the either is barred from the
content-free `ofDataFlat` (its `carrierCombinator? = some coproductLike`) and routes through the CARRIER-AWARE
arm `ofDataFlatCarrierAware (combinator := .coproductLike)`: the substituted coproduct's reducibility-as-type is
genuinely built from the substituted sides' all-level reducibility (denoting `carrierAwareEitherCandidate`).  The
former's own SN rides `eitherCode_isStronglyNormalizing_of_left_right`.  The coproduct instance where the
formation FT actually RECURSES into the carriers — the FTGEN-5.2 coproduct payoff. -/
theorem eitherCodeFundamentalFromCarriers {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    (leftType rightType : RawTerm scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (leftStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution leftType))
    (rightStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution rightType))
    (leftReducibleAllLevels :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst substitution leftType))
    (rightReducibleAllLevels :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsReducibleTypeAtAllDenoteLevels env (RawTerm.subst substitution rightType)) :
    FundamentalConclusionAtDenote env level context
      (.mkGen .gen_eitherCode () (.childCons leftType (.childCons rightType .childNil)))
      (universeCodeCell levelExpr flag) :=
  carrierAwareFormerFundamentalFromCarriers env level context .coproductLike leftType rightType
    levelExpr flag levelAbove
    leftStronglyNormalizing rightStronglyNormalizing
    leftReducibleAllLevels rightReducibleAllLevels

/-- **Arrow type code formation FT closed to its endpoints' SN.**  `arrowCode(domain, codomain)` (the
non-dependent function code), SN via `arrowCode_isStronglyNormalizing_of_domain_codomain`. -/
theorem arrowCodeFundamentalFromCarriers {profile : PolyProfile} {scope : Nat} (env : Nat → Nat)
    (level : Nat) (context : TypingContext profile scope)
    (domainType codomainType : RawTerm scope)
    (levelExpr : LevelExpr) (flag : UniverseFlag)
    (levelAbove : LevelExpr.denote levelExpr env < level)
    (domainStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution domainType))
    (codomainStronglyNormalizing :
      ∀ {targetScope : Nat} (substitution : RawTermSubst scope targetScope),
        ReducibleEnvAtDenote env level context substitution →
        IsStronglyNormalizing (RawTerm.subst substitution codomainType)) :
    FundamentalConclusionAtDenote env level context
      (.mkGen .gen_arrowCode () (.childCons domainType (.childCons codomainType .childNil)))
      (universeCodeCell levelExpr flag) :=
  flatFormerFundamentalAtDenote env level context
    (.mkGen .gen_arrowCode () (.childCons domainType (.childCons codomainType .childNil)))
    rfl (rfl : Generator.gen_arrowCode.carrierCombinator? = none) levelExpr flag levelAbove
    (fun substitution envReducible =>
      arrowCode_isStronglyNormalizing_of_domain_codomain
        (domainStronglyNormalizing substitution envReducible)
        (codomainStronglyNormalizing substitution envReducible))

end FX1Poly.Typed

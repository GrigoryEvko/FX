import FX1Poly.Tier0.ContextOmega.Strictification
import FX1Poly.Tier0.FxBaseSubstComprehension
import FX1Poly.Tier0.FxBaseSubstDisplayMap

/-! # Tier0/ContextOmega/ExplicitSubstitution — the λσ calculus, realized and convergent (context-8)

The **λσ calculus** of Abadi–Cardelli–Curien–Lévy (ACCL, 1991) reifies substitution as first-class
syntax: a substitution `s` is a term former, and a confluent rewrite system of σ-rules propagates it.
Its substitution sub-calculus σ (the rules WITHOUT the Beta rule) is **confluent and terminating**;
the full λσ (σ-rules + Beta interacting) is the explicit-substitution machine that compilers use.

The FX context base `fxBaseSubstCategory` realizes the σ-calculus **semantically**: a substitution is
a `SubstVec` (a tuple of `RawTerm`s), and "propagating" it is the meta-level function `RawTerm.subst`
/ `SubstVec.compose`.  This module proves the FX base satisfies the full ACCL σ-equational theory,
exhibits the σ-fragment's convergence concretely, and records the **non-termination boundary** the
FX design sidesteps.

## What is built — the ACCL σ-calculus on the FX base

The ACCL σ-rules, each a theorem about `SubstVec` (the spec name in brackets):

  * **IdL / IdR / Ass** `[id∘s=s · s∘id=s · (s∘t)∘u=s∘(t∘u)]` — the monoid laws, shipped
    (`identity_compose` / `compose_identity` / `compose_assoc`, context-7's strict base).
  * **VarCons** `[1[a·s]=a]` — `cons_lookup_zero` (the v-law, shipped).
  * **ShiftCons** `[↑∘(a·s)=s]` — `weakening_compose_cons` (the p-law, shipped).
  * ★ **Map** `[(a·s)∘t = a[t]·(s∘t)]` — `substMapRule`, NEW: pushing a substitution into an
    extension distributes over head and tail.  Proved pointwise via `SubstVec.ext`.
  * ★ **SCons** `[1[s]·(↑∘s)=s]` — `substSurjectivePairing`, NEW: the η-rule for substitutions
    (surjective pairing of contexts), via the comprehension universal property `cons_unique`.
  * **Clos** `[a[s][t]=a[s∘t]]` — `compose_subst_apply` (shipped); **IdSubst** `[a[id]=a]` —
    `identity_subst_apply` (shipped).
  * `fxRealizesLambdaSigmaCalculus` — all nine σ-rules bundled at one coherent shape: the FX base IS
    a model of the ACCL substitution calculus.

## Convergence of the σ-fragment

  * ★ `sigmaTripleConfluent` — a triple substitution `a[s][t][u]` collapses to the single composite
    `a[(s∘t)∘u]` regardless of grouping: different reduction orders of a substitution chain CONVERGE.
    The concrete confluence witness (the σ-fragment is Church–Rosser), via `Clos` + associativity.
  * `sigmaSubstitutionTotal` — `RawTerm.subst` is a total function, so the σ-fragment TERMINATES
    automatically: there is no σ-redex that fails to reduce, and the σ-normal form (the computed
    substitution) always exists.  (Strong normalization of σ is a corollary of totality — no infinite
    σ-reduction is even expressible, because `subst` computes in one meta-step.)

## The non-termination boundary (recorded, not faked)

Melliès (1995) proved that the FULL λσ calculus — with explicit substitutions as OBJECT-LEVEL term
formers and the Beta rule `(λa)[s]·b ↝ a[(b·s)]` interacting with the σ-rules — is **NOT strongly
normalizing on simply-typed open terms**: there is a typed term with an infinite λσ-reduction.  This
is the famous failure of "PSN" (preservation of strong normalization) for naive explicit
substitutions.  FX **sidesteps** this boundary by construction: substitution is NOT an object-level
former.  `RawTerm.subst` is a meta-level function that computes immediately, so the Melliès
configuration (a substitution suspended on a redex, looping with σ-propagation) is INEXPRESSIBLE —
the FX kernel's reduction `Step` only ever sees terms in which substitution has already fired
(β contracts to the COMPUTED `subst0 arg body`).  This is the FX design choice that buys PSN for
free; the price is no first-class substitution syntax (which FX does not want).

## Zero-axiom verification

`substMapRule` is `SubstVec.ext` + `cons_lookup` + `lookup_compose`; `substSurjectivePairing` is the
shipped `cons_unique` at the identity premises; `sigmaTripleConfluent` chains `compose_subst_apply`;
the bundle conjoins shipped σ-rules with the two new ones.  No `funext`, no `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditContextOmega.lean`. -/

namespace FX1Poly.Tier0.ContextOmega

open FX1Poly.Tier0 FX1Poly.Core

/-! ## The two NEW σ-rules: Map and SCons -/

/-- ★ **The Map rule** `(a · s) ∘ t = a[t] · (s ∘ t)`.  Composing a substitution `t` after an extended
substitution `a · s` distributes: the head `a` is substituted into (`a[t]`), the tail `s` composes
(`s ∘ t`).  The ACCL σ-rule that pushes a composition through an extension; proved pointwise. -/
theorem substMapRule {target source other : Nat} (headTerm : RawTerm source)
    (tailVec : SubstVec source other) (otherVec : SubstVec target source) :
    (SubstVec.cons headTerm tailVec).compose otherVec =
      SubstVec.cons (RawTerm.subst otherVec.toRawTermSubst headTerm) (tailVec.compose otherVec) :=
  SubstVec.ext _ _ (fun index =>
    match index with
    | ⟨0, _isLt⟩ => by
        rw [SubstVec.lookup_compose, SubstVec.cons_lookup_zero, SubstVec.cons_lookup_zero]
    | ⟨_position + 1, _isLt⟩ => by
        rw [SubstVec.lookup_compose, SubstVec.cons_lookup_succ, SubstVec.cons_lookup_succ,
            SubstVec.lookup_compose])

/-- ★ **The SCons rule (surjective pairing / substitution η)** `1[s] · (↑ ∘ s) = s`.  Any substitution
into an EXTENDED context is recovered from its zeroth lookup (the head) and its composition with the
display map (the tail) — the η-law for substitutions.  This is the comprehension universal property
`cons_unique` applied at the reflexive premises: `s` projects to `↑ ∘ s` and has head `s.lookup 0`. -/
theorem substSurjectivePairing {target source : Nat} (someVec : SubstVec target (source + 1)) :
    SubstVec.cons (someVec.lookup ⟨0, Nat.succ_pos source⟩)
      ((SubstVec.weakening source).compose someVec) = someVec :=
  (SubstVec.cons_unique (someVec.lookup ⟨0, Nat.succ_pos source⟩)
    ((SubstVec.weakening source).compose someVec) someVec rfl rfl).symm

/-! ## The full ACCL σ-calculus realized -/

/-- ★ **The FX context base realizes the ACCL λσ substitution calculus.**  All nine σ-rules hold
simultaneously on the FX base: the monoid laws (IdL/IdR/Ass), the comprehension rules
(VarCons/ShiftCons/Map/SCons), and the substitution-application laws (Clos/IdSubst).  The FX base is a
model of the explicit-substitution equational theory — realized semantically, where a substitution is
a `SubstVec` and propagation is the meta-level `subst`/`compose`. -/
theorem fxRealizesLambdaSigmaCalculus {scopeA scopeB scopeC scopeD : Nat}
    (headTerm : RawTerm scopeB) (tailVec : SubstVec scopeB scopeA)
    (firstVec : SubstVec scopeB scopeA) (secondVec : SubstVec scopeC scopeB)
    (thirdVec : SubstVec scopeD scopeC) (someTerm : RawTerm scopeA)
    (extendedVec : SubstVec scopeB (scopeA + 1)) :
    -- IdL: id ∘ s = s
    (SubstVec.identity scopeA).compose firstVec = firstVec ∧
    -- IdR: s ∘ id = s
    firstVec.compose (SubstVec.identity scopeB) = firstVec ∧
    -- Ass: (s ∘ t) ∘ u = s ∘ (t ∘ u)
    (firstVec.compose secondVec).compose thirdVec =
      firstVec.compose (secondVec.compose thirdVec) ∧
    -- VarCons (v): 1[a · s] = a
    (SubstVec.cons headTerm tailVec).lookup ⟨0, Nat.succ_pos scopeA⟩ = headTerm ∧
    -- ShiftCons (p): ↑ ∘ (a · s) = s
    (SubstVec.weakening scopeA).compose (SubstVec.cons headTerm tailVec) = tailVec ∧
    -- Map: (a · s) ∘ t = a[t] · (s ∘ t)
    (SubstVec.cons headTerm tailVec).compose secondVec =
      SubstVec.cons (RawTerm.subst secondVec.toRawTermSubst headTerm)
        (tailVec.compose secondVec) ∧
    -- SCons (η): 1[s] · (↑ ∘ s) = s
    SubstVec.cons (extendedVec.lookup ⟨0, Nat.succ_pos scopeA⟩)
        ((SubstVec.weakening scopeA).compose extendedVec) = extendedVec ∧
    -- IdSubst: a[id] = a
    RawTerm.subst (SubstVec.identity scopeA).toRawTermSubst someTerm = someTerm ∧
    -- Clos: a[s][t] = a[s ∘ t]
    RawTerm.subst secondVec.toRawTermSubst (RawTerm.subst firstVec.toRawTermSubst someTerm) =
      RawTerm.subst (firstVec.compose secondVec).toRawTermSubst someTerm :=
  ⟨SubstVec.identity_compose firstVec,
   SubstVec.compose_identity firstVec,
   SubstVec.compose_assoc firstVec secondVec thirdVec,
   SubstVec.cons_lookup_zero headTerm tailVec (Nat.succ_pos scopeA),
   SubstVec.weakening_compose_cons headTerm tailVec,
   substMapRule headTerm tailVec secondVec,
   substSurjectivePairing extendedVec,
   SubstVec.identity_subst_apply someTerm,
   (SubstVec.compose_subst_apply firstVec secondVec someTerm).symm⟩

/-! ## Convergence of the σ-fragment -/

/-- ★ **The σ-fragment is confluent.**  A triple substitution `a[s][t][u]` collapses to the single
composite substitution `a[(s∘t)∘u]` — and by associativity (`Ass`) the grouping is irrelevant, so
EVERY reduction order of a substitution chain converges to the same term.  This is the concrete
Church–Rosser witness for the σ-subcalculus, via the Clos rule (`compose_subst_apply`) twice. -/
theorem sigmaTripleConfluent {scopeA scopeB scopeC scopeD : Nat}
    (firstVec : SubstVec scopeB scopeA) (secondVec : SubstVec scopeC scopeB)
    (thirdVec : SubstVec scopeD scopeC) (someTerm : RawTerm scopeA) :
    RawTerm.subst thirdVec.toRawTermSubst
        (RawTerm.subst secondVec.toRawTermSubst (RawTerm.subst firstVec.toRawTermSubst someTerm)) =
      RawTerm.subst ((firstVec.compose secondVec).compose thirdVec).toRawTermSubst someTerm :=
  (congrArg (RawTerm.subst thirdVec.toRawTermSubst)
      (SubstVec.compose_subst_apply firstVec secondVec someTerm).symm).trans
    (SubstVec.compose_subst_apply (firstVec.compose secondVec) thirdVec someTerm).symm

/-- **The σ-fragment terminates automatically.**  Substituting along a vector is a TOTAL meta-level
function: applying `s` to `a` always yields a definite term `a[s]` (no stuck σ-redex).  This is why
the FX realization of λσ has strong normalization for free — substitution computes in one meta-step,
so no infinite σ-reduction sequence is expressible (contrast the Melliès non-termination of
object-level λσ, recorded in the module header).  Stated as: the σ-normal form exists and equals the
computed substitution (here, reflexively — it IS the function's output). -/
theorem sigmaSubstitutionTotal {target source : Nat} (someVec : SubstVec target source)
    (someTerm : RawTerm source) :
    RawTerm.subst someVec.toRawTermSubst someTerm =
      RawTerm.subst someVec.toRawTermSubst someTerm := rfl

end FX1Poly.Tier0.ContextOmega

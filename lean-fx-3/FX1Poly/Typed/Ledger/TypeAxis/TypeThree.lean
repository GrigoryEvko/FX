import FX1Poly.Tier0.Term.Codata.TerminalCoalgebra
import FX1Poly.Tier0.Term.Codata.MixedFixpoint

/-! # type-3 — the RIGHT rung: M-types, the terminal coalgebra of a container

The RIGHT / coinductive rung of the type axis — the exact dual of `type-1`'s LEFT/Σ-initial-algebra.  Where
`type-1` cited `term-1`'s initial-algebra universal property (`IsCarrierHomomorphism.unique`), `type-3` cites
`term-3`'s TERMINAL-coalgebra universal property (`StreamCoalgebra.ana_unique`) and the coinduction principle
(`FinalStream.bisim_observe`), plus the μ/ν parity's GREATEST-fixpoint half (`term-14`).  Like `type-1`/
`type-2`, this is a NON-DUPLICATIVE cross-layer ledger ABOVE Typed: marker + `_isBacked` referencing named
shipped theorems.

## What this rung backs (each `= true`, conjoined with named shipped theorems)

  * **`fxType_hasTerminalCoalgebra`** — the TERMINAL COALGEBRA universal property (FINALITY): the anamorphism
    `ana` is a coalgebra homomorphism (`StreamCoalgebra.ana_isHom`, existence) and is the UNIQUE one up to
    bisimulation (`StreamCoalgebra.ana_unique`, terminality) — the op-dual of `type-1`'s
    `IsCarrierHomomorphism.unique`.  Corecursion = the final coalgebra.
  * **`fxType_hasCoinduction`** — the COINDUCTION principle: bisimilar streams are observationally equal
    (`FinalStream.bisim_observe`).  The proof method for coinductive equality, the dual of induction.
  * **`fxType_hasGreatestFixpoint`** — the ν / greatest-fixpoint content (`term-14`): the ν-corecursor is
    unique (`NuStream.corec_unique`) and a coinductive element can be genuinely UNBOUNDED
    (`nu_canBeUnbounded` — the `0,1,2,…` stream strictly increases forever), the greatest-fixpoint side of the
    μ/ν parity / the W↔M backdrop.

## What is deferred (the genuine type-level RIGHT frontier)

  * `fxType_hasCoinductiveTypeFormer` — a TYPE-LEVEL coinductive / M-type / ν FORMER with real semantics.  The
    generator tags `gen_polyNu` / `gen_codataUnfold` / `gen_codataDest` are RESERVED (Unit payload, NOT redex
    heads, no iota rule, no typing rule, no reducibility member) — only `productiveClass` classifier metadata.
    The shipped finality is the canonical-stream / signature level (`term-3`), the co-dual of `SIG-5`.
    `= false`.
  * `fxType_hasContainerMType` — the CONTAINER presentation (shape `S` + position family `P : S → Type`) and
    INDEXED M-types.  No container record / polynomial-functor calculus exists; `gen_polyMu` / `gen_polyNu` /
    `gen_containerDeriv` are reserved tags.  The W↔M (initial-algebra ↔ terminal-coalgebra of a container)
    duality is `type-16` (polynomial-functor calculus); indexed M-types are `type-4`.  `= false`.
  * `fxType_hasCoinductiveReducibility` — SN / canonicity for coinductive (ν) members.  The stratified
    reducibility model has NO greatest-fixpoint / ν member set (only Π / Σ / universe / data-former arms) —
    the asymmetry with `type-1` (whose data-former reducibility IS shipped).  `= false`.

## Zero-axiom verification

Three `Bool` markers `:= true` (each `_isBacked` conjunction closed by `rfl` + named shipped theorems:
`ana_isHom` / `ana_unique`, `bisim_observe`, `corec_unique` / `nu_canBeUnbounded`) and three `:= false`
deferral markers.  All cited substrate is `term-3` / `term-14` (`FX1Poly.Core`), funext-free (equality is
observational / bisimulation).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`,
or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTier0TypeThree.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-! ## The terminal coalgebra (finality) -/

/-- **Honesty marker** — `type-3` (terminal coalgebra).  The anamorphism is the unique coalgebra
homomorphism into the final coalgebra — FINALITY, the op-dual of `type-1`'s initial algebra.  Backed in
`fxType_terminalCoalgebra_isBacked`.  `= true`. -/
def fxType_hasTerminalCoalgebra : Bool := true

/-- ★ **Backed flip (terminal coalgebra).**  The marker is `true` AND (i) the anamorphism is a coalgebra
homomorphism (`StreamCoalgebra.ana_isHom`, existence); (ii) any coalgebra homomorphism agrees with the
anamorphism at every observation (`StreamCoalgebra.ana_unique`, terminality). -/
theorem fxType_terminalCoalgebra_isBacked :
    fxType_hasTerminalCoalgebra = true
      ∧ (∀ {Carrier A : Type} (coalgebra : StreamCoalgebra Carrier A),
          IsStreamCoalgebraHom coalgebra coalgebra.ana)
      ∧ (∀ {Carrier A : Type} (coalgebra : StreamCoalgebra Carrier A)
          {candidate : Carrier → FinalStream A} (_isHom : IsStreamCoalgebraHom coalgebra candidate)
          (index : Nat) (state : Carrier),
          (candidate state).observe index = (coalgebra.ana state).observe index) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro Carrier A coalgebra
    exact coalgebra.ana_isHom
  · intro Carrier A coalgebra candidate isHom index state
    exact coalgebra.ana_unique isHom index state

/-! ## Coinduction -/

/-- **Honesty marker** — `type-3` (coinduction).  Bisimilar streams are observationally equal — the
coinduction proof principle (dual of induction).  Backed in `fxType_coinduction_isBacked`.  `= true`. -/
def fxType_hasCoinduction : Bool := true

/-- ★ **Backed flip (coinduction).**  The marker is `true` AND a bisimulation entails observational equality
at every index (`FinalStream.bisim_observe`). -/
theorem fxType_coinduction_isBacked :
    fxType_hasCoinduction = true
      ∧ (∀ {A : Type} {related : FinalStream A → FinalStream A → Prop}
          (_isBisimulation : IsBisimulation related) (index : Nat)
          {first second : FinalStream A},
          related first second → first.observe index = second.observe index) := by
  refine ⟨rfl, ?_⟩
  intro A related isBisimulation index first second relatedFirstSecond
  exact FinalStream.bisim_observe isBisimulation index relatedFirstSecond

/-! ## The greatest fixpoint (ν) — the μ/ν parity -/

/-- **Honesty marker** — `type-3` (greatest fixpoint).  The ν-corecursor is unique, and a coinductive element
can be genuinely unbounded (the greatest-fixpoint side of the μ/ν parity / the W↔M backdrop).  Backed in
`fxType_greatestFixpoint_isBacked`.  `= true`. -/
def fxType_hasGreatestFixpoint : Bool := true

/-- ★ **Backed flip (greatest fixpoint).**  The marker is `true` AND (i) the ν-corecursor is unique
(`NuStream.corec_unique`); (ii) a ν element can be unbounded — the `0,1,2,…` stream strictly increases
forever (`nu_canBeUnbounded`), the separation from the finite μ side. -/
theorem fxType_greatestFixpoint_isBacked :
    fxType_hasGreatestFixpoint = true
      ∧ (∀ {A Seed : Type} (observe : Seed → A) (advance : Seed → Seed)
          (candidate : Seed → NuStream A),
          (∀ seed, (candidate seed).head = observe seed) →
          (∀ seed position, (candidate seed).tail position = candidate (advance seed) position) →
          ∀ (seed : Seed) (position : Nat),
            candidate seed position = NuStream.corec observe advance seed position)
      ∧ (∃ stream : NuStream Nat, ∀ position, stream position < stream (position + 1)) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro A Seed observe advance candidate candidateHead candidateTail seed position
    exact NuStream.corec_unique observe advance candidate candidateHead candidateTail seed position
  · exact nu_canBeUnbounded

/-! ## Honesty markers (the deferred type-level RIGHT frontier) -/

/-- **Honesty marker.**  A TYPE-LEVEL coinductive / M-type / ν FORMER with real semantics — `gen_polyNu` /
`gen_codataUnfold` / `gen_codataDest` are RESERVED tags (Unit payload, no iota / typing / reducibility), only
classifier metadata; the shipped finality is the canonical-stream / signature level (`term-3`), the co-dual
of `SIG-5`.  Deferred.  `= false`. -/
def fxType_hasCoinductiveTypeFormer : Bool := false

/-- **Honesty marker.**  The CONTAINER presentation (shape + position family) and INDEXED M-types — no
container record / polynomial-functor calculus exists (`gen_polyMu` / `gen_polyNu` / `gen_containerDeriv` are
reserved); the W↔M duality is `type-16`, indexed M-types are `type-4`.  Deferred.  `= false`. -/
def fxType_hasContainerMType : Bool := false

/-- **Honesty marker.**  SN / canonicity for coinductive (ν) members — the stratified reducibility model has
no greatest-fixpoint / ν member set (only Π / Σ / universe / data-former arms), the asymmetry with `type-1`'s
shipped data-former reducibility.  Deferred.  `= false`. -/
def fxType_hasCoinductiveReducibility : Bool := false

end FX1Poly.Tier0

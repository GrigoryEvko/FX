import FX1Poly.Tier0.FxBaseSubstCategory
import FX1Poly.Core.RawTermRenameSubstCommute

/-! # FX1Poly/Tier0/FxBaseSubstWeakening
    — the display / weakening substitution (brick 3 of the term-carrying CwR base)

`FxBaseSubstVec.lean` (SUBSTVEC-1) shipped the extensional substitution vector `SubstVec`; `FxBaseSubstCategory.lean`
(SUBSTVEC-2) assembled `fxBaseSubstCategory : RawCategory` (objects = scopes, morphisms `source ⟶ target` =
substitution vectors `SubstVec target source`).  This file adds the FIRST distinguished morphism the comprehension
structure needs: the **display / weakening substitution** `scope ⟶ scope + 1`, which embeds the `scope`-context's
variables into the extended `scope + 1` context by shifting each past the freshly-bound variable `0`.  It is the
term-carrying analogue of the renaming base's `RenamingVec.weakening`, and the representable-map candidate toward
`fxBaseSubstRMC`.

## What lands here (all zero-axiom)

  * `SubstVec.weakening scope : SubstVec (scope + 1) scope` — the display substitution, sending each variable `i`
    to the term `var (i + 1)`.  As a `fxBaseSubstCategory` morphism it is exactly `scope ⟶ scope + 1`
    (`fxBaseSubstCategory.Morphism scope (scope + 1)` unfolds to `SubstVec (scope + 1) scope` definitionally).
  * `SubstVec.weakening_lookup` — its lookup is the shifted-variable term (`lookup_tabulate`).
  * `SubstVec.weakening_lookup_eq_rename` — the lookup AGREES with the weakening RENAMING on a variable.
  * `SubstVec.weakening_unique` — the display map is uniquely characterized by its action (via `ext`).
  * **`SubstVec.weakening_subst_eq_rename`** — the DEEP coherence: the weakening SUBSTITUTION acts on EVERY term
    exactly as the weakening RENAMING (`subst weakening.toRawTermSubst t = rename weaken t`), not merely agreeing
    on variable lookups.  This is the substitution/renaming coherence specialized to weakening — the genuine
    content of the brick (the lookup-level agreement is only its variable-arm shadow).

## Honest scope boundary

This lands the display map ITSELF + its coherence with renaming.  It is NOT yet the comprehension structure: the
`cons` extension `(someSubst, headTerm)` and the display map's UNIVERSAL property (the β/weakening-cancellation
pullback square — `RawTerm.weaken_subst_cons` is the term-level cancellation it will rest on) are the next brick.
The representable-map class + the three CwR axioms over `fxBaseSubstCategory` (yielding `fxBaseSubstRMC`), and the
`GlobalSections` / `SconingPreservation` / extraction instances over the term-carrying base, are the later bricks
of this arc.

## Zero-axiom verification

`weakening` is `tabulate` of the shifted-variable function; `weakening_lookup` / `_eq_rename` are `lookup_tabulate`;
`weakening_unique` is `ext`.  The deep coherence routes `rename weaken t` back through `subst_identity_apply`
(undoing the identity substitution), `rename_subst_commute` (folding the rename into the substitution
`weaken.thenSubst identity`), then `subst_pointwise` against `weakening_lookup` — the two substitutions agree
pointwise, both sending variable `i` to `var (i + 1)`.  No `funext` (the whole point of `SubstVec`).  No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core FX1Poly.Foundation

/-- The **display / weakening substitution** `scope ⟶ scope + 1`: every variable `i` maps to the term `var (i + 1)`,
embedding the `scope`-context's variables into the extended context past the freshly-bound variable `0`.  The
term-carrying analogue of `RenamingVec.weakening`. -/
def SubstVec.weakening (scope : Nat) : SubstVec (scope + 1) scope :=
  SubstVec.tabulate (fun index => RawTerm.mkGen .gen_var (Fin.succ index) .childNil)

/-- The weakening substitution's lookup is the shifted-variable term. -/
theorem SubstVec.weakening_lookup (scope : Nat) (index : Fin scope) :
    (SubstVec.weakening scope).lookup index =
      RawTerm.mkGen .gen_var (Fin.succ index) .childNil :=
  SubstVec.lookup_tabulate _ index

/-- The weakening substitution's lookup AGREES with the weakening RENAMING's action on a variable. -/
theorem SubstVec.weakening_lookup_eq_rename (scope : Nat) (index : Fin scope) :
    (SubstVec.weakening scope).lookup index =
      RawTerm.rename RawRenaming.weaken (RawTerm.mkGen .gen_var index .childNil) :=
  SubstVec.lookup_tabulate _ index

/-- The display map is uniquely characterized by its action (every variable to its shifted self) — via `ext`. -/
theorem SubstVec.weakening_unique (scope : Nat) (candidate : SubstVec (scope + 1) scope)
    (actsAsWeaken : ∀ index : Fin scope,
      candidate.lookup index = RawTerm.mkGen .gen_var (Fin.succ index) .childNil) :
    candidate = SubstVec.weakening scope :=
  SubstVec.ext candidate (SubstVec.weakening scope)
    (fun index => (actsAsWeaken index).trans (SubstVec.weakening_lookup scope index).symm)

/-- **Deep coherence: the weakening SUBSTITUTION acts on EVERY term as the weakening RENAMING.**  Not merely
agreeing on variable lookups (`weakening_lookup_eq_rename`): substituting via the weakening substitution equals
renaming via the weakening renaming on the WHOLE term algebra.  Routes `rename weaken t` back through the identity
substitution (`subst_identity_apply`), folds the rename into `weaken.thenSubst identity` (`rename_subst_commute`),
then bridges to the weakening substitution pointwise (`subst_pointwise` against `weakening_lookup` — both send
variable `i` to `var (i + 1)`). -/
theorem SubstVec.weakening_subst_eq_rename {scope : Nat} (sourceTerm : RawTerm scope) :
    RawTerm.subst (SubstVec.weakening scope).toRawTermSubst sourceTerm =
      RawTerm.rename RawRenaming.weaken sourceTerm := by
  rw [← RawTerm.subst_identity_apply (RawTerm.rename RawRenaming.weaken sourceTerm)]
  rw [RawTerm.rename_subst_commute RawRenaming.weaken RawTermSubst.identity sourceTerm]
  exact RawTerm.subst_pointwise
    (fun position => SubstVec.weakening_lookup scope position) sourceTerm

end FX1Poly.Tier0

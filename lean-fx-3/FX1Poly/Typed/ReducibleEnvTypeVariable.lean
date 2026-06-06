import FX1Poly.Typed.ReducibleEnvAt
import FX1Poly.Core.StratifiedReducibleUniverseDecode
import FX1Poly.Typed.CellSubstitution

/-! # FX1Poly/Typed/ReducibleEnvTypeVariable
    — type-variable domains get their reducibility from the environment (the FT crux that sidesteps the wall)

The fundamental theorem's λ-introduction arm needs the abstraction's DOMAIN to be a reducible TYPE under the
closing substitution.  For a domain that is a TYPE VARIABLE `α` (a context binding `α : Type@levelExpr+flag`),
this is supplied directly by the reducible environment — NO appeal to the open universe wall:

  * `ReducibleEnvAt` makes `substitution index` a reducible MEMBER of the substituted binding type.
  * The binding type is a universe code `Type@levelExpr+flag`, which substitution fixes
    (`subst_universeCodeCell` — universe codes carry no `RawTerm` children, so they are closed).
  * A member of a universe code at fuel `predLevel + 1` decodes (`IsReducibleMemberAt.universeMembership_iff`)
    to `IsStronglyNormalizing ∧ IsReducibleTypeAt predLevel` — its second conjunct is exactly the domain
    reducibility the λ arm consumes.

**Why this sidesteps the universe wall.**  The wall (`ReducibleTypeStep.existsCongr`'s fuel-`0` degeneracy)
blocks TYPE ABSTRACTION — a Π whose DOMAIN is the universe `Type@e` itself (`λA : Type@e. …`, genuine type
polymorphism / System F).  But a SIMPLY-TYPED term abstracts over TERMS, never over types: its domain is a
type VARIABLE `α` (or an arrow of such), never the universe `Type@e`.  A type variable's reducibility is read
off the environment by the decode above; the wall is never invoked.  So the simply-typed fundamental theorem
is NOT wall-blocked — its remaining cost is the term-judgment + environment assembly, not a research wall.

This is the `ReducibleEnvAt` (fixed-level closing-substitution) analogue of the existing
`ReducibleEnvVec.typeVariableReducible` (the vector-environment version the dependent formation FT uses); it
is the form an `ReducibleEnvAt`-based simply-typed term FT — built on `ReducibleEnvAt.lookupReducible` /
`.cons` / `.empty` — consumes in its λ arm.

## Zero-axiom verification

`envReducible index` (a projection), `rw [lookupIsUniverse, subst_universeCodeCell]`, then the forward decode
`IsReducibleMemberAt.universeMembership_iff.mp … |>.2`.  No `axiom`, `sorry`, `propext`, `Quot.sound`,
`Classical`, `native_decide`, or `omega`.  Gated per declaration in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe
open StepStar

/-- **A type-variable domain is reducible under a reducible environment.**  When a context binds `index` at a
universe code `Type@levelExpr+flag`, a reducible environment (at fuel `predLevel + 1`) sends `index` to a
reducible TYPE at `predLevel` — the λ-introduction arm's domain-reducibility obligation, discharged from the
environment with NO appeal to the universe wall (which blocks type abstraction, not term abstraction over type
variables).  The crux that makes the simply-typed fundamental theorem achievable over contexts carrying type
variables. -/
theorem ReducibleEnvAt.typeVariableReducible {profile : PolyProfile} {scope targetScope : Nat}
    {predLevel : Nat} {context : TypingContext profile scope}
    {substitution : RawTermSubst scope targetScope}
    {levelExpr : LevelExpr} {flag : UniverseFlag} (index : Fin scope)
    (envReducible : ReducibleEnvAt (predLevel + 1) context substitution)
    (lookupIsUniverse : context.lookup index = universeCodeCell levelExpr flag) :
    IsReducibleTypeAt predLevel (substitution index) := by
  have member := envReducible index
  rw [lookupIsUniverse, subst_universeCodeCell] at member
  exact (IsReducibleMemberAt.universeMembership_iff.mp member).2

end FX1Poly.Typed

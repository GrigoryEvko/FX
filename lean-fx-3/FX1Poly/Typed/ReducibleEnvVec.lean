import FX1Poly.Core.StratifiedReducibleMember
import FX1Poly.Core.RawTermSubstConsCommute
import FX1Poly.Typed.TypingContext

/-! # FX1Poly/Typed/ReducibleEnvVec
    — the PER-VARIABLE-LEVEL reducible closing-substitution environment for the dependent fundamental theorem

`ReducibleEnvAt level` (the level-UNIFORM environment) carries a SINGLE fuel `level` for every context
variable.  That is sufficient for the simply-typed / single-tower-rung fragment, but NOT for the full
dependent fundamental theorem: in the typing tower `t : T : Type@k : Type@(k+1) : …` each RUNG sits at fuel
one higher (`tarskiDecode`: `IsReducibleMemberAt L universeCode ⟺ IsReducibleTypeAt (L-1)`), so a CONTEXT
that mixes variables at DIFFERENT tower positions (`x : A : Type@j` and `y : B : Type@k` with `j ≠ k`) cannot
be served by any single global level — and upward level-cumulativity (`IsReducibleTypeAt L → IsReducibleTypeAt
(L+1)`) is FALSE (Π-domain contravariance), so the uniform environment cannot be bumped.

The fix is the standard device for predicative universe towers (Abel et al.'s decidability-of-conversion;
the Agda/Coq MLTT logical-relation models): a Kripke-style environment indexed by a PER-VARIABLE LEVEL
ASSIGNMENT.  `ReducibleEnvVec levels context substitution` says the substitution sends EACH context variable
to a reducible member at THAT VARIABLE'S OWN level `levels index` of its looked-up (closed) type:

  `∀ index, IsReducibleMemberAt (levels index)
      (subst substitution (context.lookup index)) (substitution index)`.

The `levels : Fin scope → Nat` vector lets each variable live at the fuel its own type's tower position
demands.  The two environment operations mirror `ReducibleEnvAt` exactly, modulo the level now being read
per-position from the vector (which is inert through the cons rewrites — they touch only the looked-up TYPE
and the SUBSTITUTED TERM, never the membership predicate's level).

## Zero-axiom verification

A `∀`-quantified `def`; `levelCons` is the propext-free `⟨0,_⟩`/`⟨k+1,_⟩` structure match (NOT `Fin.cons`,
which pulls propext via `Fin.cases`); `empty` is `Fin.elim0`; `cons` is the same `Fin`-position split whose
lookups are rewritten by `TypingContext.lookup_cons_zero` / `lookup_cons_succ` and the weakening cancellation
`RawTerm.weaken_subst_cons` — the per-position level rides along untouched.  No `axiom`, `sorry`, `propext`,
`Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation

/-- Cons a fresh head level onto a tail level vector — the propext-free `Fin`-position structure match
(position 0 takes the head level; position `k + 1` reads the tail at `k`).  Avoids `Fin.cons` (which pulls
propext through `Fin.cases`). -/
def levelCons {scope : Nat} (headLevel : Nat) (tailLevels : Fin scope → Nat) :
    Fin (scope + 1) → Nat :=
  fun position =>
    match position with
    | ⟨0, _⟩ => headLevel
    | ⟨priorValue + 1, isLtSucc⟩ => tailLevels ⟨priorValue, Nat.lt_of_succ_lt_succ isLtSucc⟩

/-- The per-variable-level reducible closing-substitution environment: `substitution` sends each context
variable to a reducible member — at THAT VARIABLE'S level `levels index` — of that variable's looked-up type,
itself closed by the same substitution.  The Kripke (per-tower-rung) refinement of `ReducibleEnvAt` that the
dependent fundamental theorem's heterogeneous contexts demand. -/
def ReducibleEnvVec {profile : PolyProfile} {scope targetScope : Nat}
    (levels : Fin scope → Nat)
    (context : TypingContext profile scope)
    (substitution : RawTermSubst scope targetScope) : Prop :=
  ∀ index : Fin scope,
    IsReducibleMemberAt (levels index)
      (RawTerm.subst substitution (context.lookup index)) (substitution index)

/-- The `var` case of the dependent fundamental theorem: a per-variable-level reducible environment sends
each variable to a reducible member — at its own level `levels index` — of its looked-up (closed) type. -/
theorem ReducibleEnvVec.lookupReducible {profile : PolyProfile} {scope targetScope : Nat}
    {levels : Fin scope → Nat}
    {context : TypingContext profile scope} {substitution : RawTermSubst scope targetScope}
    (envReducible : ReducibleEnvVec levels context substitution) (index : Fin scope) :
    IsReducibleMemberAt (levels index)
      (RawTerm.subst substitution (context.lookup index)) (substitution index) :=
  envReducible index

/-- Every substitution is reducible for the empty context at any level vector — the base environment
(vacuous: `Fin 0` is uninhabited), turning the dependent fundamental theorem into the closed-term
reducibility corollary. -/
theorem ReducibleEnvVec.empty {profile : PolyProfile} {targetScope : Nat}
    (levels : Fin 0 → Nat) (substitution : RawTermSubst 0 targetScope) :
    ReducibleEnvVec levels (TypingContext.empty : TypingContext profile 0) substitution :=
  fun index => index.elim0

/-- Extend a per-variable-level reducible environment at a binder (the dependent Π-introduction step): given
a reducible environment for `context` at `tailLevels` and a reducible member — at the fresh `headLevel` — of
the new binding's closed type, the `cons`-extended substitution is reducible for `context.cons bindingType`
at the `levelCons headLevel tailLevels` vector.  Variable 0 lands on `headTerm` at `headLevel` (its weakened
lookup of `bindingType` cancels to `subst tailSubst bindingType`); variable `k + 1` recurses into the tail
environment at `tailLevels k` (its weakened lookup cancels likewise) — each variable keeps its own tower
level. -/
theorem ReducibleEnvVec.cons {profile : PolyProfile} {scope targetScope : Nat}
    {tailLevels : Fin scope → Nat} {headLevel : Nat}
    {context : TypingContext profile scope} {bindingType : RawTerm scope}
    {tailSubst : RawTermSubst scope targetScope} {headTerm : RawTerm targetScope}
    (tailReducible : ReducibleEnvVec tailLevels context tailSubst)
    (headReducible :
      IsReducibleMemberAt headLevel (RawTerm.subst tailSubst bindingType) headTerm) :
    ReducibleEnvVec (levelCons headLevel tailLevels) (context.cons bindingType)
      (RawTermSubst.cons headTerm tailSubst) := by
  intro index
  match index with
  | ⟨0, isLt⟩ =>
      show IsReducibleMemberAt headLevel _ _
      rw [TypingContext.lookup_cons_zero context bindingType isLt,
        RawTerm.weaken_subst_cons bindingType headTerm tailSubst]
      exact headReducible
  | ⟨position + 1, isLtSucc⟩ =>
      show IsReducibleMemberAt (tailLevels ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩) _ _
      rw [TypingContext.lookup_cons_succ context bindingType position isLtSucc,
        RawTerm.weaken_subst_cons
          (context.lookup ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩) headTerm tailSubst]
      exact tailReducible ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩

end FX1Poly.Typed

import FX1Poly.Core.ReducibleMember
import FX1Poly.Core.RawTermSubstConsCommute
import FX1Poly.Typed.TypingContext

/-! # FX1Poly/Typed/ReducibleEnv
    — the reducible closing-substitution environment for the fundamental theorem (#425)

The Girard-Tait fundamental theorem over `HasTypeDescPi` will read

  `HasTypeDescPi profile context subject classifier → ReducibleEnv context γ →
     IsReducibleMember (classifier.subst γ) (subject.subst γ)`

— every well-typed term, closed by a REDUCIBLE substitution, is a reducible member of its (closed)
classifier.  This file ships that environment.

`ReducibleEnv context substitution` says the substitution sends EACH context variable to a reducible
member of that variable's looked-up type (itself closed by the same substitution):

  `∀ index, IsReducibleMember (subst substitution (context.lookup index)) (substitution index)`.

The ∀-form (rather than a telescopic inductive over `RawTermSubst.cons`) makes the fundamental theorem's
`var` case IMMEDIATE — it is literally `envReducible index` (`lookupReducible`) — while avoiding any
function-extensionality on the substitution (no `funext`/`Quot.sound`).  The DEPENDENT membership
`IsReducibleMember` (rather than a fixed per-variable candidate) is what a term-indexed type family needs:
each variable's type is re-substituted, not transported as a frozen candidate.

The two operations the fundamental theorem performs:

  * **`empty`** — every substitution is reducible for the empty context (vacuously: `Fin 0` is empty).
    The base case turning the theorem into the closed-term corollary.
  * **`cons`** — extend a reducible environment at a binder: given a reducible environment for `context`
    and a reducible member of the new binding's (closed) type, the `cons`-extended substitution is
    reducible for `context.cons bindingType`.  This is the Π-introduction binder step.  Each variable's
    lookup weakens by one (`TypingContext.lookup`), which the `cons` substitution cancels
    (`RawTerm.weaken_subst_cons`): variable 0 hits the fresh head, variable `k+1` recurses into the tail.

## Zero-axiom verification

A `∀`-quantified `def`; `empty` is `Fin.elim0`; `cons` is a `Fin`-position split (`⟨0,_⟩` / `⟨k+1,_⟩`,
the propext-free structure match) whose lookups are rewritten by `TypingContext.lookup_cons_zero` /
`lookup_cons_succ` and the weakening cancellation `RawTerm.weaken_subst_cons`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Foundation

/-- The reducible closing-substitution environment: `substitution` sends each context variable to a
reducible member of that variable's looked-up type, itself closed by the same substitution. -/
def ReducibleEnv {profile : PolyProfile} {scope targetScope : Nat}
    (context : TypingContext profile scope)
    (substitution : RawTermSubst scope targetScope) : Prop :=
  ∀ index : Fin scope,
    IsReducibleMember (RawTerm.subst substitution (context.lookup index)) (substitution index)

/-- The `var` case of the fundamental theorem: a reducible environment sends each variable to a
reducible member of its looked-up (closed) type. -/
theorem ReducibleEnv.lookupReducible {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {substitution : RawTermSubst scope targetScope}
    (envReducible : ReducibleEnv context substitution) (index : Fin scope) :
    IsReducibleMember (RawTerm.subst substitution (context.lookup index)) (substitution index) :=
  envReducible index

/-- Every substitution is reducible for the empty context — the base environment (vacuous: `Fin 0` is
uninhabited), turning the fundamental theorem into the closed-term reducibility corollary. -/
theorem ReducibleEnv.empty {profile : PolyProfile} {targetScope : Nat}
    (substitution : RawTermSubst 0 targetScope) :
    ReducibleEnv (TypingContext.empty : TypingContext profile 0) substitution :=
  fun index => index.elim0

/-- Extend a reducible environment at a binder (the Π-introduction step): given a reducible environment
for `context` and a reducible member `headTerm` of the new binding's closed type, the `cons`-extended
substitution is reducible for `context.cons bindingType`.  Variable 0 lands on `headTerm` (its weakened
lookup of `bindingType` cancels to `subst tailSubst bindingType`); variable `k+1` recurses into the tail
environment (its weakened lookup cancels likewise). -/
theorem ReducibleEnv.cons {profile : PolyProfile} {scope targetScope : Nat}
    {context : TypingContext profile scope} {bindingType : RawTerm scope}
    {tailSubst : RawTermSubst scope targetScope} {headTerm : RawTerm targetScope}
    (tailReducible : ReducibleEnv context tailSubst)
    (headReducible : IsReducibleMember (RawTerm.subst tailSubst bindingType) headTerm) :
    ReducibleEnv (context.cons bindingType) (RawTermSubst.cons headTerm tailSubst) := by
  intro index
  match index with
  | ⟨0, isLt⟩ =>
      rw [TypingContext.lookup_cons_zero context bindingType isLt,
        RawTerm.weaken_subst_cons bindingType headTerm tailSubst]
      exact headReducible
  | ⟨position + 1, isLtSucc⟩ =>
      rw [TypingContext.lookup_cons_succ context bindingType position isLtSucc,
        RawTerm.weaken_subst_cons
          (context.lookup ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩) headTerm tailSubst]
      exact tailReducible ⟨position, Nat.lt_of_succ_lt_succ isLtSucc⟩

end FX1Poly.Typed

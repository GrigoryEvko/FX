import FX1Poly.Core.EtaRuleTable
import FX1Poly.Core.RawTermSubstRenameCommute
import FX1Poly.Core.RawTermRenameSubstCommute

/-! # EtaStrengthenEquivariance — ETA-T2: strengthening commutes with
binder-lifted substitution and renaming

The crux bricks of the eta equivariance arc: the un-weakening engine
`strengthenBy?` is NATURAL in the term — a term that strengthens keeps
strengthening after any binder-lifted substitution or renaming, to the
substituted/renamed core.  The fresh variables stay unused because the
lifted action maps the fresh block to itself and weakens everything
else.

The single-depth square is the `strengthen_commutes_rename` technique
re-run for substitutions: a successful strengthening rewrites the body
to `weaken extracted` (soundness), the weakening pulls through the
lifted substitution by the two fold-commutation theorems and one
pointwise identity (`σ.lift ∘ weaken ≡ weaken ∘ σ` — the Allais
extensionality discharges it), and `strengthen_weaken` closes.  The
multi-depth engines then stack the squares along the
`iterateLiftRaw`/`strengthenBy?` recursions, which peel binders in the
SAME newest-first order.

Zero-axiom: no `sorry`, no `propext`, no `Quot.sound`, no `Classical`,
`native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditEtaStrengthenEquivariance.lean`. -/

namespace FX1Poly.Core

open FX1Poly.Foundation (RawRenaming)

/-! ## The single-depth substitution square -/

/-- **Strengthening commutes with a lifted substitution**: a body whose
newest variable is unused keeps it unused after `σ.lift` (the lift maps
`var 0` to `var 0` and weakens every substituent), and the extracted
core substitutes by `σ`. -/
theorem RawTerm.strengthen_subst {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope)
    (body : RawTerm (sourceScope + 1)) (extracted : RawTerm sourceScope)
    (success : RawTerm.strengthen body = some extracted) :
    RawTerm.strengthen
        (RawTerm.subst someSubstitution.lift body)
      = some (RawTerm.subst someSubstitution extracted) := by
  have weakenedBody := RawTerm.strengthen_sound body extracted success
  rw [← weakenedBody]
  dsimp only [RawTerm.weaken]
  rw [RawTerm.rename_subst_commute RawRenaming.weaken
    someSubstitution.lift extracted]
  have substAgree :
      RawTermSubst.PointwiseEq
        (RawRenaming.thenSubst RawRenaming.weaken someSubstitution.lift)
        (RawTermSubst.postRename someSubstitution RawRenaming.weaken) := by
    intro position
    cases position with
    | mk positionValue positionBound => rfl
  rw [RawTerm.subst_pointwise substAgree extracted]
  rw [← RawTerm.subst_rename_commute someSubstitution
    RawRenaming.weaken extracted]
  exact RawTerm.strengthen_weaken
    (RawTerm.subst someSubstitution extracted)

/-! ## The multi-depth engines -/

/-- **`strengthenBy?` is natural in binder-lifted substitutions** — the
ETA-T2 crux: the multi-depth un-weakening commutes with
`iterateLiftRaw σ depth`, stacking the single-depth square along the
shared newest-first recursion. -/
theorem RawTerm.strengthenBy?_subst {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope) :
    (depth : Nat) → (body : RawTerm (sourceScope + depth)) →
    (core : RawTerm sourceScope) →
    RawTerm.strengthenBy? depth body = some core →
    RawTerm.strengthenBy? depth
        (RawTerm.subst (iterateLiftRaw someSubstitution depth) body)
      = some (RawTerm.subst someSubstitution core)
  | 0, body, core, success => by
      have bodyIsCore : core = body := (Option.some.inj success).symm
      subst bodyIsCore
      rfl
  | depth + 1, body, core, success => by
      have peeled :
          (RawTerm.strengthen body).bind
            (fun stripped => RawTerm.strengthenBy? depth stripped)
          = some core := success
      match strippedEq : RawTerm.strengthen body with
      | none =>
          rw [strippedEq] at peeled
          exact nomatch peeled
      | some stripped =>
          rw [strippedEq] at peeled
          have strippedSuccess :
              RawTerm.strengthenBy? depth stripped = some core := peeled
          have stepSquare :=
            RawTerm.strengthen_subst (iterateLiftRaw someSubstitution depth)
              body stripped strippedEq
          show (RawTerm.strengthen
              (RawTerm.subst
                (RawTermSubst.lift (iterateLiftRaw someSubstitution depth))
                body)).bind
              (fun strippedTerm => RawTerm.strengthenBy? depth strippedTerm)
            = some (RawTerm.subst someSubstitution core)
          rw [stepSquare]
          exact RawTerm.strengthenBy?_subst someSubstitution depth stripped
            core strippedSuccess

/-- **`strengthenBy?` is natural in binder-lifted renamings** — the
companion engine, stacking the shipped `strengthen_commutes_rename`
square. -/
theorem RawTerm.strengthenBy?_rename {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope) :
    (depth : Nat) → (body : RawTerm (sourceScope + depth)) →
    (core : RawTerm sourceScope) →
    RawTerm.strengthenBy? depth body = some core →
    RawTerm.strengthenBy? depth
        (RawTerm.rename (iterateLiftRaw rawRenaming depth) body)
      = some (RawTerm.rename rawRenaming core)
  | 0, body, core, success => by
      have bodyIsCore : core = body := (Option.some.inj success).symm
      subst bodyIsCore
      rfl
  | depth + 1, body, core, success => by
      have peeled :
          (RawTerm.strengthen body).bind
            (fun stripped => RawTerm.strengthenBy? depth stripped)
          = some core := success
      match strippedEq : RawTerm.strengthen body with
      | none =>
          rw [strippedEq] at peeled
          exact nomatch peeled
      | some stripped =>
          rw [strippedEq] at peeled
          have strippedSuccess :
              RawTerm.strengthenBy? depth stripped = some core := peeled
          have stepSquare :=
            RawTerm.strengthen_commutes_rename
              (iterateLiftRaw rawRenaming depth) body stripped strippedEq
          show (RawTerm.strengthen
              (RawTerm.rename
                (RawRenaming.lift (iterateLiftRaw rawRenaming depth))
                body)).bind
              (fun strippedTerm => RawTerm.strengthenBy? depth strippedTerm)
            = some (RawTerm.rename rawRenaming core)
          rw [stepSquare]
          exact RawTerm.strengthenBy?_rename rawRenaming depth stripped
            core strippedSuccess

/-! ## The lifted action fixes the fresh block -/

/-- A binder-lifted substitution maps each fresh variable to itself —
the reason eta's fresh-variable patterns persist under substitution. -/
theorem iterateLiftRaw_RawTermSubst_fixesFreshVar {sourceScope targetScope : Nat}
    (someSubstitution : RawTermSubst sourceScope targetScope) :
    (depth : Nat) → (varIndex : Nat) →
    (sourceBound : varIndex < sourceScope + depth) →
    (targetBound : varIndex < targetScope + depth) →
    varIndex < depth →
    iterateLiftRaw someSubstitution depth ⟨varIndex, sourceBound⟩
      = .mkGen .gen_var ⟨varIndex, targetBound⟩ .childNil
  | 0, _varIndex, _sourceBound, _targetBound, isFresh =>
      absurd isFresh (Nat.not_lt_zero _)
  | depth + 1, 0, _sourceBound, _targetBound, _isFresh => rfl
  | depth + 1, varIndex + 1, sourceBound, targetBound, isFresh => by
      show RawTerm.weaken
          (iterateLiftRaw someSubstitution depth
            ⟨varIndex, Nat.lt_of_succ_lt_succ sourceBound⟩)
        = .mkGen .gen_var ⟨varIndex + 1, targetBound⟩ .childNil
      rw [iterateLiftRaw_RawTermSubst_fixesFreshVar someSubstitution depth
        varIndex (Nat.lt_of_succ_lt_succ sourceBound)
        (Nat.lt_of_succ_lt_succ targetBound)
        (Nat.lt_of_succ_lt_succ isFresh)]
      rfl

end FX1Poly.Core

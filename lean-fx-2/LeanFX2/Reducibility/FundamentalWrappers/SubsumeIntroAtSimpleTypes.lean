import LeanFX2.Reducibility.FundamentalWrappers.ModalDestructorBase

/-! # LeanFX2.Reducibility.FundamentalWrappers.SubsumeIntroAtSimpleTypes

Fundamental cases for `Term.subsume` and `Term.modIntro` at the
simple closed-leaf types: `Ty.bool`, `Ty.nat`, `Ty.empty`,
`Ty.interval`, and `Ty.effect`.  Each ships an SN-direct case
plus a renaming-stable companion.

## Root status

Layer 3 metatheory leaf.  Fourth slice of `FundamentalWrappers`. -/

namespace LeanFX2


/-! ## K12.20.BE Remaining SN-direct fundamental cases — subsume / modIntro

Five additional SN-direct arms covering the closed-leaf and
raw-payload-carrying types not in K12.20.BC/BD's
representative quartet: `Ty.bool`, `Ty.nat`, `Ty.empty`,
`Ty.interval`, and `Ty.effect`.  All five preserve their outer
Ty constructor under substitution (`Foundation/Subst.lean:103,
104, 126, 127, 152-153` respectively), keeping the SN-direct
invariant per `Reducibility.lean:326-329, 602-603`.

Ten total cases (5 subsume + 5 modIntro) closing the SN-direct
fragment of `Reducible.fundamental_subsume` and
`fundamental_modIntro` at Layer 1.  Same single-line composition
pattern as K12.20.BC/BD: `RawTerm.{subsume,modIntro}_isStronglyNormalizing
innerIH`.

After K12.20.BE, the full SN-direct coverage matrix is:

| Ty           | subsume | modIntro |
| ------------ | ------- | -------- |
| unit         | BC.1    | BD.1     |
| bool         | BE.1    | BE.6     |
| nat          | BE.2    | BE.7     |
| empty        | BE.3    | BE.8     |
| interval     | BE.4    | BE.9     |
| universe     | BC.2    | BD.2     |
| session      | BC.3    | BD.3     |
| effect       | BE.5    | BE.10    |
| modal        | BC.4    | BD.4     |

`Ty.tyVar` is intentionally excluded: substitution maps
`tyVar position → sigma.forTy position` (`Foundation/Subst.lean:111-112`)
to an arbitrary Ty, breaking the SN-direct invariant.  The
tyVar case ships at K12.25 alongside the compound-Ty machinery.

Compound-Ty innerType arms (arrow / sigmaTy / listType /
optionType / eitherType / id / oeq / idStrict / path / glue /
equiv / refine / record / codata / piTy) require the full
`Reducible.subsume_intro` / `Reducible.modIntro_intro`
framework with case analysis on the substituted Ty and step-
closure under elimination forms — those ship at K12.25. -/

/-- **K12.20.BE.1 subsume at `Ty.bool`** — SN-direct closed-leaf.
`(Ty.bool).subst sigma = .bool` (`Foundation/Subst.lean:103`). -/
theorem Reducible.fundamental_subsume_at_bool
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.bool innerRaw}
    (innerIH : Reducible ((Ty.bool : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.bool : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- Boolean subsumption preserves fundamental stability. -/
theorem Reducible.fundamental_subsume_at_bool_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.bool innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.bool : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.bool : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.subsume innerTerm)) := by
  exact Reducible.fundamental_subsume_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.2 subsume at `Ty.nat`** — SN-direct closed-leaf.
`(Ty.nat).subst sigma = .nat` (`Foundation/Subst.lean:104`). -/
theorem Reducible.fundamental_subsume_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.nat innerRaw}
    (innerIH : Reducible ((Ty.nat : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.nat : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- Natural subsumption preserves fundamental stability. -/
theorem Reducible.fundamental_subsume_at_nat_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.nat innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.nat : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.nat : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.subsume innerTerm)) := by
  exact Reducible.fundamental_subsume_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.3 subsume at `Ty.empty`** — SN-direct closed-leaf.
`(Ty.empty).subst sigma = .empty` (`Foundation/Subst.lean:126`). -/
theorem Reducible.fundamental_subsume_at_empty
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.empty innerRaw}
    (innerIH : Reducible ((Ty.empty : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.empty : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- Empty-type subsumption preserves fundamental stability. -/
theorem Reducible.fundamental_subsume_at_empty_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.empty innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.empty : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.empty : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.subsume innerTerm)) := by
  exact Reducible.fundamental_subsume_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.4 subsume at `Ty.interval`** — SN-direct cubical
closed-leaf.  `(Ty.interval).subst sigma = .interval`
(`Foundation/Subst.lean:127`). -/
theorem Reducible.fundamental_subsume_at_interval
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.interval innerRaw}
    (innerIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- Interval subsumption preserves fundamental stability. -/
theorem Reducible.fundamental_subsume_at_interval_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.interval innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.subsume innerTerm)) := by
  exact Reducible.fundamental_subsume_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.5 subsume at `Ty.effect`** — SN-direct
raw-payload-carrying.  `(Ty.effect carrier tag).subst sigma =
.effect (carrier.subst sigma) (tag.subst sigma.forRaw)`
(`Foundation/Subst.lean:152-153`) — the outer `Ty.effect`
constructor is preserved.  Sister to K12.20.BC.3 session. -/
theorem Reducible.fundamental_subsume_at_effect
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.effect carrierType effectTag) innerRaw}
    (innerIH :
        Reducible ((Ty.effect carrierType effectTag).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.effect carrierType effectTag).subst sigma)
              (Term.subst termSubst (Term.subsume innerTerm)) :=
  RawTerm.subsume_isStronglyNormalizing innerIH

/-- Effect subsumption preserves fundamental stability. -/
theorem Reducible.fundamental_subsume_at_effect_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.effect carrierType effectTag) innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.effect carrierType effectTag).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.effect carrierType effectTag).subst sigma)
      (Term.subst termSubst (Term.subsume innerTerm)) := by
  exact Reducible.fundamental_subsume_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.6 modIntro at `Ty.bool`** — sister to BE.1 via
K12.20.Y `RawTerm.modIntro_isStronglyNormalizing`. -/
theorem Reducible.fundamental_modIntro_at_bool
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.bool innerRaw}
    (innerIH : Reducible ((Ty.bool : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.bool : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- Boolean modal introduction preserves fundamental stability. -/
theorem Reducible.fundamental_modIntro_at_bool_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.bool innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.bool : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.bool : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.modIntro innerTerm)) := by
  exact Reducible.fundamental_modIntro_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.7 modIntro at `Ty.nat`** — sister to BE.2. -/
theorem Reducible.fundamental_modIntro_at_nat
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.nat innerRaw}
    (innerIH : Reducible ((Ty.nat : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.nat : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- Natural modal introduction preserves fundamental stability. -/
theorem Reducible.fundamental_modIntro_at_nat_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.nat innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.nat : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.nat : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.modIntro innerTerm)) := by
  exact Reducible.fundamental_modIntro_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.8 modIntro at `Ty.empty`** — sister to BE.3. -/
theorem Reducible.fundamental_modIntro_at_empty
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.empty innerRaw}
    (innerIH : Reducible ((Ty.empty : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.empty : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- Empty-type modal introduction preserves fundamental stability. -/
theorem Reducible.fundamental_modIntro_at_empty_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.empty innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.empty : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.empty : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.modIntro innerTerm)) := by
  exact Reducible.fundamental_modIntro_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.9 modIntro at `Ty.interval`** — sister to BE.4. -/
theorem Reducible.fundamental_modIntro_at_interval
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.interval innerRaw}
    (innerIH : Reducible ((Ty.interval : Ty level scope).subst sigma)
                         (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.interval : Ty level scope).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- Interval modal introduction preserves fundamental stability. -/
theorem Reducible.fundamental_modIntro_at_interval_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx Ty.interval innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.interval : Ty level scope).subst sigma)
      (Term.subst termSubst (Term.modIntro innerTerm)) := by
  exact Reducible.fundamental_modIntro_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

/-- **K12.20.BE.10 modIntro at `Ty.effect`** — sister to BE.5. -/
theorem Reducible.fundamental_modIntro_at_effect
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.effect carrierType effectTag) innerRaw}
    (innerIH :
        Reducible ((Ty.effect carrierType effectTag).subst sigma)
                  (Term.subst termSubst innerTerm)) :
    Reducible ((Ty.effect carrierType effectTag).subst sigma)
              (Term.subst termSubst (Term.modIntro innerTerm)) :=
  RawTerm.modIntro_isStronglyNormalizing innerIH

/-- Effect modal introduction preserves fundamental stability. -/
theorem Reducible.fundamental_modIntro_at_effect_stable
    {mode : Mode} {level scope targetScope : Nat}
    {sourceCtx : Ctx mode level scope}
    {targetCtx : Ctx mode level targetScope}
    {sigma : Subst level scope targetScope}
    {termSubst : TermSubst sourceCtx targetCtx sigma}
    {carrierType : Ty level scope}
    {effectTag : RawTerm scope}
    {innerRaw : RawTerm scope}
    {innerTerm :
        Term sourceCtx (Ty.effect carrierType effectTag) innerRaw}
    (innerIsStable :
      IsRenamingStableReducible ((Ty.effect carrierType effectTag).subst sigma)
        (Term.subst termSubst innerTerm)) :
    IsRenamingStableReducible ((Ty.effect carrierType effectTag).subst sigma)
      (Term.subst termSubst (Term.modIntro innerTerm)) := by
  exact Reducible.fundamental_modIntro_stable
    (by simp [Reducible.IsSNDirect, Ty.subst]) innerIsStable

end LeanFX2

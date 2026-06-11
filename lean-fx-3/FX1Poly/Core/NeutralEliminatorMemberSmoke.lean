import FX1Poly.Core.NatElimNeutralScrutineeMember
import FX1Poly.Core.ListElimNeutralScrutineeMember
import FX1Poly.Core.DirectIotaEliminatorNeutralScrutineeMember
import FX1Poly.Core.MatchEliminatorNeutralScrutineeMember
import FX1Poly.Core.StrongNormalizationLeaves

/-! # FX1Poly/Core/NeutralEliminatorMemberSmoke
    — non-vacuous regression corpus for the completed eliminator-neutral-coverage arc

The four-file arc (`NatElimNeutralScrutineeMember`, `ListElimNeutralScrutineeMember`,
`DirectIotaEliminatorNeutralScrutineeMember`, `MatchEliminatorNeutralScrutineeMember`) proved that every one of
the ten non-leaf `IsNeutral` eliminators (`natElim`, `natRec`, `listElim`, `boolElim`, `optionMatch`,
`eitherMatch`, `fst`, `snd`, `idJ`, `idStrictRec`) over a neutral principal child is a member of ANY reducibility
candidate.  Those theorems are universally quantified over the candidate and over the (abstractly SN) children,
so a reader cannot tell at a glance that they are NON-VACUOUS — that the hypotheses are actually inhabited by a
real stuck term.

This file is the regression witness: each shipped neutral member, instantiated at the concrete SN candidate
(`isStronglyNormalizing_isReducibilityCandidate`, where "member" unfolds to "strongly normalizing") with the
variable `var index` as the genuinely-neutral principal child (`IsNeutral.var` + `var_isStronglyNormalizing`),
yields a CONCRETE strong-normalization fact: the stuck eliminator `elim (var index) …` is strongly normalizing.
Each is a closed instantiation — if any neutral member regressed (e.g. silently became vacuous, or lost its
zero-axiom status), one of these would fail to typecheck.  Spelled at an arbitrary `Fin scope` index so the
corpus is parametric, not pinned to a single scope.

## Zero-axiom verification

Each smoke is a single application of a shipped neutral member to `var_isStronglyNormalizing` + `IsNeutral.var`,
so it inherits their zero-axiom status.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open StepStar

/-- **`natElim` over a variable scrutinee is strongly normalizing** — the concrete non-vacuous witness of
`natElimNeutralScrutineeMember` at the SN candidate.  Phase-Z motive shape: a `var 0` under-binder throwaway
motive (SN), zero-branch / scrutinee the same outer variable, and a `var 0` two-binder throwaway succ-branch
(SN at `scope + 2`). -/
theorem natElimNeutralVarSmoke {scope : Nat} (index : Fin scope) :
    IsStronglyNormalizing (natElimCellSpine (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil)
      (.mkGen .gen_var index .childNil) (.mkGen .gen_var index .childNil)
      (.mkGen .gen_var ⟨0, Nat.zero_lt_succ (scope + 1)⟩ .childNil)) :=
  natElimNeutralScrutineeMember IsStronglyNormalizing isStronglyNormalizing_isReducibilityCandidate
    (var_isStronglyNormalizing ⟨0, Nat.zero_lt_succ scope⟩)
    (var_isStronglyNormalizing index) (IsNeutral.var index)
    (var_isStronglyNormalizing index) (var_isStronglyNormalizing ⟨0, Nat.zero_lt_succ (scope + 1)⟩)

/-- **`natRec` over a variable scrutinee is strongly normalizing** (dependent-recursor twin). -/
theorem natRecNeutralVarSmoke {scope : Nat} (index : Fin scope) :
    IsStronglyNormalizing (natRecCellSpine (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil)
      (.mkGen .gen_var index .childNil) (.mkGen .gen_var index .childNil)
      (.mkGen .gen_var ⟨0, Nat.zero_lt_succ (scope + 1)⟩ .childNil)) :=
  natRecNeutralScrutineeMember IsStronglyNormalizing isStronglyNormalizing_isReducibilityCandidate
    (var_isStronglyNormalizing ⟨0, Nat.zero_lt_succ scope⟩)
    (var_isStronglyNormalizing index) (IsNeutral.var index)
    (var_isStronglyNormalizing index) (var_isStronglyNormalizing ⟨0, Nat.zero_lt_succ (scope + 1)⟩)

/-- **`listElim` over a variable scrutinee is strongly normalizing.**  Phase-Z motive shape: a `var 0`
under-binder throwaway motive (SN), then nil/cons/scrutinee all the same outer variable. -/
theorem listElimNeutralVarSmoke {scope : Nat} (index : Fin scope) :
    IsStronglyNormalizing (listElimCellSpine (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil)
      (.mkGen .gen_var index .childNil)
      (.mkGen .gen_var index .childNil) (.mkGen .gen_var index .childNil)) :=
  listElimNeutralScrutineeMember IsStronglyNormalizing isStronglyNormalizing_isReducibilityCandidate
    (var_isStronglyNormalizing ⟨0, Nat.zero_lt_succ scope⟩)
    (var_isStronglyNormalizing index) (IsNeutral.var index)
    (var_isStronglyNormalizing index) (var_isStronglyNormalizing index)

/-- **`optionMatch` over a variable scrutinee is strongly normalizing.**  Phase-Z motive shape: a `var 0`
under-binder throwaway motive (SN), scrutinee/none/some all the same outer variable. -/
theorem optionMatchNeutralVarSmoke {scope : Nat} (index : Fin scope) :
    IsStronglyNormalizing (optionMatchCellSpine (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil)
      (.mkGen .gen_var index .childNil)
      (.mkGen .gen_var index .childNil) (.mkGen .gen_var index .childNil)) :=
  optionMatchNeutralScrutineeMember IsStronglyNormalizing isStronglyNormalizing_isReducibilityCandidate
    (var_isStronglyNormalizing ⟨0, Nat.zero_lt_succ scope⟩)
    (var_isStronglyNormalizing index) (IsNeutral.var index)
    (var_isStronglyNormalizing index) (var_isStronglyNormalizing index)

/-- **`eitherMatch` over a variable scrutinee is strongly normalizing.**  Phase-Z motive shape: a `var 0`
under-binder throwaway motive (SN), scrutinee/left/right all the same outer variable. -/
theorem eitherMatchNeutralVarSmoke {scope : Nat} (index : Fin scope) :
    IsStronglyNormalizing (eitherMatchCellSpine (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil)
      (.mkGen .gen_var index .childNil)
      (.mkGen .gen_var index .childNil) (.mkGen .gen_var index .childNil)) :=
  eitherMatchNeutralScrutineeMember IsStronglyNormalizing isStronglyNormalizing_isReducibilityCandidate
    (var_isStronglyNormalizing ⟨0, Nat.zero_lt_succ scope⟩)
    (var_isStronglyNormalizing index) (IsNeutral.var index)
    (var_isStronglyNormalizing index) (var_isStronglyNormalizing index)

/-- **`boolElim` over a variable scrutinee is strongly normalizing.**  Phase-Z motive shape: a `var 0`
under-binder throwaway motive (SN), then/else/scrutinee all the same outer variable. -/
theorem boolElimNeutralVarSmoke {scope : Nat} (index : Fin scope) :
    IsStronglyNormalizing (.mkGen .gen_boolElim ()
      (.childCons (.mkGen .gen_var ⟨0, Nat.zero_lt_succ scope⟩ .childNil)
        (.childCons (.mkGen .gen_var index .childNil)
          (.childCons (.mkGen .gen_var index .childNil)
            (.childCons (.mkGen .gen_var index .childNil) .childNil))))) :=
  boolElimNeutralScrutineeMember IsStronglyNormalizing isStronglyNormalizing_isReducibilityCandidate
    (var_isStronglyNormalizing ⟨0, Nat.zero_lt_succ scope⟩)
    (var_isStronglyNormalizing index) (IsNeutral.var index)
    (var_isStronglyNormalizing index) (var_isStronglyNormalizing index)

/-- **`fst` over a variable argument is strongly normalizing.** -/
theorem fstNeutralVarSmoke {scope : Nat} (index : Fin scope) :
    IsStronglyNormalizing (.mkGen .gen_fst () (.childCons (.mkGen .gen_var index .childNil) .childNil)) :=
  fstNeutralArgumentMember IsStronglyNormalizing isStronglyNormalizing_isReducibilityCandidate
    (var_isStronglyNormalizing index) (IsNeutral.var index)

/-- **`snd` over a variable argument is strongly normalizing.** -/
theorem sndNeutralVarSmoke {scope : Nat} (index : Fin scope) :
    IsStronglyNormalizing (.mkGen .gen_snd () (.childCons (.mkGen .gen_var index .childNil) .childNil)) :=
  sndNeutralArgumentMember IsStronglyNormalizing isStronglyNormalizing_isReducibilityCandidate
    (var_isStronglyNormalizing index) (IsNeutral.var index)

/-- **`idJ` over a variable witness is strongly normalizing** (the neutral child is the WITNESS; the base case
is also a variable here). -/
theorem idJNeutralVarSmoke {scope : Nat} (index : Fin scope) :
    IsStronglyNormalizing (.mkGen .gen_idJ ()
      (.childCons (.mkGen .gen_var index .childNil)
        (.childCons (.mkGen .gen_var index .childNil) .childNil))) :=
  idJNeutralWitnessMember IsStronglyNormalizing isStronglyNormalizing_isReducibilityCandidate
    (var_isStronglyNormalizing index) (var_isStronglyNormalizing index) (IsNeutral.var index)

/-- **`idStrictRec` over a variable witness is strongly normalizing.** -/
theorem idStrictRecNeutralVarSmoke {scope : Nat} (index : Fin scope) :
    IsStronglyNormalizing (.mkGen .gen_idStrictRec ()
      (.childCons (.mkGen .gen_var index .childNil)
        (.childCons (.mkGen .gen_var index .childNil) .childNil))) :=
  idStrictRecNeutralWitnessMember IsStronglyNormalizing isStronglyNormalizing_isReducibilityCandidate
    (var_isStronglyNormalizing index) (var_isStronglyNormalizing index) (IsNeutral.var index)

end FX1Poly.Core

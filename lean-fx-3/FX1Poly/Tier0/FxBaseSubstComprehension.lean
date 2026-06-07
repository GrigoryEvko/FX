import FX1Poly.Tier0.FxBaseSubstWeakening
import FX1Poly.Core.CandidateReducibleSubst

/-! # FX1Poly/Tier0/FxBaseSubstComprehension
    — the context-extension (comprehension) structure (brick 4 of the term-carrying CwR base)

`FxBaseSubstWeakening.lean` (SUBSTVEC-3) shipped the display map `SubstVec.weakening`.  A category with
representable maps needs the dual operation: **context extension / comprehension**.  Given a substitution
`tailVec : SubstVec target source` (a morphism `source ⟶ target`) and a head term `headTerm : RawTerm target`,
form the extended substitution `SubstVec.cons headTerm tailVec : SubstVec target (source + 1)` (a morphism
`source + 1 ⟶ target`).  This is the substitution that sends the freshly-bound variable `0` to `headTerm` and
every other variable `i + 1` to `tailVec`'s image of `i` — exactly the de Bruijn binder-extension the β-rule
runs (`RawTermSubst.cons`, of which this is the extensional `SubstVec` analogue).

## What lands here (all zero-axiom)

  * `SubstVec.cons headTerm tailVec` — the extension morphism (literally the product pair `(headTerm, tailVec)`,
    since `SubstVec target (source + 1) = RawTerm target × SubstVec target source`).
  * `SubstVec.cons_lookup_zero` / `cons_lookup_succ` — the **v-law** (the zeroth variable recovers the head) and
    the tail recovery; both `rfl`.
  * **`SubstVec.weakening_compose_cons`** — the **p-law / comprehension β-cancellation**: composing the display
    map `weakening` after the extension recovers the tail (`weakening.compose (cons head tail) = tail`).  The
    genuine de Bruijn content — the display map projects an extended context back onto its base.
  * **`SubstVec.cons_unique`** — the **comprehension UNIVERSAL PROPERTY**: the extension is the UNIQUE morphism
    whose display-projection is the tail and whose zeroth lookup is the head.  Together with `cons` (existence) +
    the p/v laws (computation) this is the CwR comprehension structure.
  * `SubstVec.cons_toRawTermSubst` — the bridge: `SubstVec.cons` IS `RawTermSubst.cons` (pointwise), so the
    extensional comprehension agrees with the function-level binder-extension the β-engine already uses.

## Honest scope boundary

This lands the comprehension morphism + its universal property over the term-carrying base.  It is NOT yet the
full `RepresentableMapCategory`: the representable-map class (the display maps as a distinguished morphism class)
and the three CwR axioms over `fxBaseSubstCategory` (yielding `fxBaseSubstRMC`) are the next brick; the
`GlobalSections` / `SconingPreservation` / extraction instances over the term base are the later bricks of this
arc.

## Zero-axiom verification

`cons` is the product constructor; `cons_lookup_zero/succ` are `rfl` (the `SubstVec.lookup` match arms); the
p-law and uniqueness go through `ext` pointwise, reducing each variable arm to `lookup_compose` +
`weakening_lookup` + subst-of-a-variable (`rfl`) + `lookup_succ`; the `RawTermSubst.cons` bridge is a per-position
match.  No `funext` (the whole point of `SubstVec`).  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`,
`native_decide`, or `omega`.  Per-declaration gated in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core FX1Poly.Foundation

/-- **Context extension / comprehension.**  Extend a substitution `tailVec : SubstVec target source` with a head
term `headTerm`, forming `SubstVec target (source + 1)` — the morphism `source + 1 ⟶ target` sending the fresh
variable `0` to `headTerm` and each `i + 1` to `tailVec`'s image of `i`.  Literally the product pair (since
`SubstVec target (source + 1) = RawTerm target × SubstVec target source`); the extensional analogue of
`RawTermSubst.cons`. -/
def SubstVec.cons {target source : Nat} (headTerm : RawTerm target)
    (tailVec : SubstVec target source) : SubstVec target (source + 1) :=
  (headTerm, tailVec)

/-- **v-law.**  The zeroth variable recovers the head term. -/
theorem SubstVec.cons_lookup_zero {target source : Nat} (headTerm : RawTerm target)
    (tailVec : SubstVec target source) (isLt : 0 < source + 1) :
    (SubstVec.cons headTerm tailVec).lookup ⟨0, isLt⟩ = headTerm := rfl

/-- A successor variable recurses into the tail. -/
theorem SubstVec.cons_lookup_succ {target source : Nat} (headTerm : RawTerm target)
    (tailVec : SubstVec target source) (position : Nat) (isLt : position + 1 < source + 1) :
    (SubstVec.cons headTerm tailVec).lookup ⟨position + 1, isLt⟩ =
      tailVec.lookup ⟨position, Nat.lt_of_succ_lt_succ isLt⟩ := rfl

/-- **p-law / comprehension β-cancellation.**  Composing the display map `weakening` after the extension recovers
the tail: the display map projects the extended context back onto its base.  The de Bruijn step at the heart of
the comprehension structure. -/
theorem SubstVec.weakening_compose_cons {target source : Nat} (headTerm : RawTerm target)
    (tailVec : SubstVec target source) :
    (SubstVec.weakening source).compose (SubstVec.cons headTerm tailVec) = tailVec :=
  SubstVec.ext _ _ (fun index => by
    rw [SubstVec.lookup_compose, SubstVec.weakening_lookup]; rfl)

/-- **The bridge: `SubstVec.cons` IS `RawTermSubst.cons`** (pointwise).  The extensional comprehension agrees with
the function-level binder-extension the β-engine already uses (`RawTermSubst.cons`, the substitution `subst0`
rests on). -/
theorem SubstVec.cons_toRawTermSubst {target source : Nat} (headTerm : RawTerm target)
    (tailVec : SubstVec target source) (index : Fin (source + 1)) :
    (SubstVec.cons headTerm tailVec).toRawTermSubst index =
      RawTermSubst.cons headTerm tailVec.toRawTermSubst index := by
  match index with
  | ⟨0, _⟩ => rfl
  | ⟨_position + 1, _⟩ => rfl

/-- **Comprehension universal property.**  The extension `cons headTerm tailVec` is the UNIQUE morphism whose
display-projection (`weakening` composed after it) is `tailVec` and whose zeroth lookup is `headTerm`.  Together
with `cons` (existence) and the p/v laws (computation), this is the full CwR comprehension structure over the
term-carrying base. -/
theorem SubstVec.cons_unique {target source : Nat} (headTerm : RawTerm target)
    (tailVec : SubstVec target source) (candidate : SubstVec target (source + 1))
    (projectsToTail : (SubstVec.weakening source).compose candidate = tailVec)
    (zerothIsHead : candidate.lookup ⟨0, Nat.succ_pos source⟩ = headTerm) :
    candidate = SubstVec.cons headTerm tailVec :=
  SubstVec.ext candidate (SubstVec.cons headTerm tailVec) (fun index =>
    match index with
    | ⟨0, _⟩ => zerothIsHead
    | ⟨position + 1, isLt⟩ => by
        -- project `projectsToTail` at this position: the display composite's lookup is the tail's
        have tailAgrees :
            ((SubstVec.weakening source).compose candidate).lookup
                ⟨position, Nat.lt_of_succ_lt_succ isLt⟩ =
              tailVec.lookup ⟨position, Nat.lt_of_succ_lt_succ isLt⟩ := by
          rw [projectsToTail]
        rw [SubstVec.lookup_compose, SubstVec.weakening_lookup] at tailAgrees
        -- tailAgrees : candidate.lookup (succ position) = tailVec.lookup position (subst-of-var rfl); the goal's
        -- RHS (cons head tail).lookup (position+1) reduces to tailVec.lookup position (cons_lookup_succ)
        exact tailAgrees)

end FX1Poly.Tier0
